import Lax3Proofs.SolveBlocks
import Lax3Proofs.ImplScatter

/-!
# F6c/1 — `greedyScatter` as an IMP+ program, discharged

`Impl.greedyScatter G r X t` (`ImplScatter`, §6.5) is the guarded
early-stop sweep: return `0` outright at `t = 0`, otherwise scan the
vertices in ascending order, pick each unmarked member of `X`, stop at
the `t`-th pick, and mark `ball_r` of every non-final pick. This file
compiles it by the direct `Spec`-kit route and discharges the `Spec`:
**`scatterCom` leaves exactly `Impl.greedyScatter G r X t` in its
count cell** (`scatterCom_spec`), from a state holding the graph in
CSR form (`Lib.Csr` + the head file's adjacency semantics), the
predicate `X` and the (clean) mark set as bit arrays, and a length-`N`
distance scratch.

## The marking BFS, inlined

The one non-obvious ingredient is the per-pick test "`v` unmarked",
which the abstract routine spells `∀ u ∈ acc, ¬ WithinDist G r u v`.
The machine maintains the mark bit array `ma = ⋃_{u picked} ball_r(u)`
and pays for it per pick: `markCom` is a depth-`r` BFS **by rounds**
from the pick — reset the distance scratch to the sentinel `r+1`
(`gsReset`), then `r` rounds, each one full pass over the vertices
relaxing the CSR rows of the current frontier (`D s = round`), setting
the mark bit alongside every distance write. Correctness rides on
four carried clauses (`DSt` + the relaxation clause): the source is at
`0`, every discovered entry is *sound* (`D w ≤ r → WithinDist G (D w)
v₀ w`), every entry is at most the sentinel, and every vertex below
the round counter has relaxed its row; *completeness* (`WithinDist G r
v₀ w → D w ≤ r`) is **derived** from those by induction on the radius
(`d_complete`) rather than carried — the frontier of round `p` is
fixed during the round (writes are `p+1`), which is what makes the
carried form stable.

## The budget, in the landed charge's terms

`scatterK N ns r t = 30·N + (markK N ns r + 30)·t + 14`, with
`markK N ns r = 13·N + (25·N + 26·ns + 14)·r + 18` the per-pick
marking charge. This is `Impl.greedyScatterCost`'s shape at
`W := markK` — one scan unit per vertex plus `W` per non-final pick
(`greedyScatterCost_le : … ≤ t·(n + W)`); the machine's `W` is
`O((r+1)·(N + ns))` (`markK_le`) — one carrier-plus-slots sweep per
round, §6.5's `W := ‖A‖` instantiation at the schedule constant
`r ≤ 2R`. The two amortized loops (the frontier pass pays per row out
of `26·(ns − off u)`, the sweep pays each non-final pick out of
`(markK + 30)·(t − cnt)`) are `Run.while_potential`'s potential form,
which is why the guard (`t = 0` scans nothing) and the early stop
(the `t`-th pick skips both the rest of the scan and its own marking)
cost what §6.5 says they cost.

Stored values: distances `≤ r + 1`, marks and predicate bits `≤ 1`,
counters `≤ N`, slot pointers `≤ ns`, the count `≤ t` — the explicit
`< B` hypotheses of the theorems, all below `mcB` at a schedule
constant (head file's stored-value paragraph).

The scratch cells are the fixed list `gsScalars`; the five arrays are
name parameters (the caller points them at a level's CSR and its own
mark/scratch/predicate regions — distinctness hypotheses are stated
where used, dischargeable by `decide` at F7's concrete names).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (arrOf_getD)
open Lax3.ColoredGraphs (WithinDist)
open Lax3Proofs.WalkDistance

/-! ## §1 Two facts about `WithinDist` -/

theorem withinDist_zero_iff {V : Type*} {G : SimpleGraph V} {u v : V} :
    WithinDist G 0 u v ↔ u = v := by
  constructor
  · rintro ⟨w, hw⟩
    exact SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.mp hw)
  · rintro rfl
    exact withinDist_refl G 0 u

/-- The BFS step: within `p+1` is within `p`, or one edge past
within `p`. -/
theorem withinDist_succ_iff {V : Type*} {G : SimpleGraph V} (p : ℕ) (v w : V) :
    WithinDist G (p + 1) v w ↔
      WithinDist G p v w ∨ ∃ s, WithinDist G p v s ∧ G.Adj s w := by
  constructor
  · rintro ⟨wk, hlen⟩
    by_cases h : wk.length ≤ p
    · exact Or.inl ⟨wk, h⟩
    · right
      have hr : wk.reverse.length = p + 1 := by
        rw [SimpleGraph.Walk.length_reverse]; omega
      cases hwk : wk.reverse with
      | nil => rw [hwk] at hr; simp at hr
      | cons hadj tail =>
        rw [hwk] at hr
        simp only [SimpleGraph.Walk.length_cons] at hr
        exact ⟨_, ⟨tail.reverse, by rw [SimpleGraph.Walk.length_reverse]; omega⟩,
          hadj.symm⟩
  · rintro (h | ⟨s, ⟨wk, hlen⟩, hadj⟩)
    · exact withinDist_mono_radius (by omega) h
    · exact ⟨wk.concat hadj, by rw [SimpleGraph.Walk.length_concat]; omega⟩

/-- **Completeness, derived**: a `0`-anchored distance table whose
sub-`r` entries have all relaxed their rows dominates the true
distances up to `r`. -/
theorem d_complete {N : ℕ} {G : SimpleGraph (Fin N)} {v₀ : Fin N}
    {D : ℕ → ℕ} {r : ℕ} (h0 : D (v₀ : ℕ) = 0)
    (hrel : ∀ s w : Fin N, D (s : ℕ) < r → G.Adj s w → D (w : ℕ) ≤ D (s : ℕ) + 1) :
    ∀ q, q ≤ r → ∀ w : Fin N, WithinDist G q v₀ w → D (w : ℕ) ≤ q := by
  intro q
  induction q with
  | zero =>
    intro _ w hw
    obtain rfl := withinDist_zero_iff.mp hw
    omega
  | succ q ih =>
    intro hq w hw
    rcases (withinDist_succ_iff q v₀ w).mp hw with h | ⟨s, hs, hadj⟩
    · have := ih (by omega) w h
      omega
    · have hDs := ih (by omega) s hs
      have := hrel s w (by omega) hadj
      omega

/-! ## §2 The marked set of a pick list -/

/-- The set the mark array realizes: everything within `r` of a pick. -/
def marks {N : ℕ} (G : SimpleGraph (Fin N)) (r : ℕ) (acc : List (Fin N)) :
    Set (Fin N) :=
  {w | ∃ u ∈ acc, WithinDist G r u w}

@[simp] theorem marks_nil {N : ℕ} (G : SimpleGraph (Fin N)) (r : ℕ) :
    marks G r [] = ∅ := by
  ext w; simp [marks]

theorem marks_append {N : ℕ} (G : SimpleGraph (Fin N)) (r : ℕ)
    (acc : List (Fin N)) (v : Fin N) :
    marks G r (acc ++ [v]) = marks G r acc ∪ {w | WithinDist G r v w} := by
  ext w
  simp only [marks, Set.mem_setOf_eq, Set.mem_union, List.mem_append,
    List.mem_singleton]
  constructor
  · rintro ⟨u, hu | rfl, hw⟩
    · exact Or.inl ⟨u, hu, hw⟩
    · exact Or.inr hw
  · rintro (⟨u, hu, hw⟩ | hw)
    · exact ⟨u, Or.inl hu, hw⟩
    · exact ⟨v, Or.inr rfl, hw⟩

theorem not_mem_marks_iff {N : ℕ} {G : SimpleGraph (Fin N)} {r : ℕ}
    {acc : List (Fin N)} {w : Fin N} :
    w ∉ marks G r acc ↔ ∀ u ∈ acc, ¬ WithinDist G r u w := by
  simp [marks]

/-! ## §3 The program -/

/-- The routine's scratch cells (fixed names; the arrays are
parameters). In scan order: pick counter, sweep index, stop bound,
the three inputs `N`/`r`/`t`, the round counter, the frontier index,
the two row pointers, the slot value, the reset index. -/
def gsScalars : List String :=
  ["gs.c", "gs.v", "gs.s", "gs.n", "gs.r", "gs.t",
    "gs.p", "gs.u", "gs.j", "gs.e", "gs.w", "gs.i"]

/-- Reset the distance scratch to the sentinel `r + 1`. -/
def gsReset (da : String) : Com :=
  .seq (.assign "gs.i" (.lit 0))
    (.while (.lt (.var "gs.i") (.var "gs.n"))
      (.seq (.store da (.var "gs.i") (.add (.var "gs.r") (.lit 1)))
        (.assign "gs.i" (.add (.var "gs.i") (.lit 1)))))

/-- One slot of a frontier row: read the target, relax it (write
distance `round+1` and the mark bit if that improves), advance. -/
def gsSlotBody (t ma da : String) : Com :=
  .seq (Csr.slot t "gs.j" "gs.w")
    (.seq
      (.ite (.lt (.add (.var "gs.p") (.lit 1)) (.get da (.var "gs.w")))
        (.seq (.store da (.var "gs.w") (.add (.var "gs.p") (.lit 1)))
          (.store ma (.var "gs.w") (.lit 1)))
        .skip)
      (.assign "gs.j" (.add (.var "gs.j") (.lit 1))))

/-- One vertex of a round's pass: scan its row iff it is on the
frontier (`D u = round`), advance. -/
def gsUBody (o t ma da : String) : Com :=
  .seq
    (.ite (.eq (.get da (.var "gs.u")) (.var "gs.p"))
      (.seq (Csr.loadRow o "gs.u" "gs.j" "gs.e")
        (Csr.scan "gs.j" "gs.e" (gsSlotBody t ma da)))
      .skip)
    (.assign "gs.u" (.add (.var "gs.u") (.lit 1)))

/-- One round: a full pass over the vertices. -/
def gsRoundBody (o t ma da : String) : Com :=
  .seq (.assign "gs.u" (.lit 0))
    (.seq (.while (.lt (.var "gs.u") (.var "gs.n")) (gsUBody o t ma da))
      (.assign "gs.p" (.add (.var "gs.p") (.lit 1))))

/-- **The marking BFS**: reset, seed the pick (`D := 0`, mark it),
run `r` rounds. Marks accumulate — the mark array is never cleared,
which is the sweep's union-of-balls discipline. -/
def markCom (o t ma da : String) : Com :=
  .seq (gsReset da)
    (.seq (.store da (.var "gs.v") (.lit 0))
      (.seq (.store ma (.var "gs.v") (.lit 1))
        (.seq (.assign "gs.p" (.lit 0))
          (.while (.lt (.var "gs.p") (.var "gs.r")) (gsRoundBody o t ma da)))))

/-- One vertex of the sweep: if it satisfies the predicate and is
unmarked, pick it — the `t`-th pick stops the scan (`stop := 0`), any
earlier pick marks its ball; then advance. -/
def gsSweepBody (o t pa ma da : String) : Com :=
  .seq
    (.ite (.eq (.get pa (.var "gs.v")) (.lit 1))
      (.ite (.lt (.get ma (.var "gs.v")) (.lit 1))
        (.seq (.assign "gs.c" (.add (.var "gs.c") (.lit 1)))
          (.ite (.eq (.var "gs.c") (.var "gs.t"))
            (.assign "gs.s" (.lit 0))
            (markCom o t ma da)))
        .skip)
      .skip)
    (.assign "gs.v" (.add (.var "gs.v") (.lit 1)))

/-- The unguarded sweep: counter and index to `0`, stop bound to `N`,
scan. -/
def gsSweep (o t pa ma da : String) : Com :=
  .seq (.assign "gs.c" (.lit 0))
    (.seq (.assign "gs.v" (.lit 0))
      (.seq (.assign "gs.s" (.var "gs.n"))
        (.while (.lt (.var "gs.v") (.var "gs.s")) (gsSweepBody o t pa ma da))))

/-- **`greedyScatter`, as IMP+**: the `t = 0` guard explicit in the
program text (§6.5 — the guard is a cost statement), else the sweep. -/
def scatterCom (o t pa ma da : String) : Com :=
  .ite (.eq (.var "gs.t") (.lit 0))
    (.assign "gs.c" (.lit 0))
    (gsSweep o t pa ma da)

/-! ## §4 The budgets -/

/-- The per-pick marking charge: the reset, the seed, `r` rounds of
one full carrier-plus-slots pass each. -/
def markK (N ns r : ℕ) : ℕ := 13 * N + (25 * N + 26 * ns + 14) * r + 18

/-- **The routine's budget**: one scan unit per vertex, `markK` per
non-final pick — `Impl.greedyScatterCost`'s `t·(n + W)` shape at
`W := markK`. -/
def scatterK (N ns r t : ℕ) : ℕ := 30 * N + (markK N ns r + 30) * t + 14

/-- The marking charge is §6.5's `W := ‖A‖` at a schedule constant:
linear in carrier plus slots, `r+1` sweeps. -/
theorem markK_le (N ns r : ℕ) : markK N ns r ≤ 65 * (r + 1) * (N + ns + 1) := by
  have h1 : 13 * N + 18 ≤ 31 * (N + ns + 1) := by omega
  have h2 : 25 * N + 26 * ns + 14 ≤ 34 * (N + ns + 1) := by omega
  have h3 : (25 * N + 26 * ns + 14) * r ≤ 34 * (N + ns + 1) * r :=
    Nat.mul_le_mul_right r h2
  have h4 : 31 * (N + ns + 1) + 34 * ((N + ns + 1) * r)
      ≤ 65 * ((r + 1) * (N + ns + 1)) := by
    have : (r + 1) * (N + ns + 1) = (N + ns + 1) * r + (N + ns + 1) := by ring
    rw [this]
    omega
  calc markK N ns r = 13 * N + 18 + (25 * N + 26 * ns + 14) * r := by
        rw [markK]; ring
    _ ≤ 31 * (N + ns + 1) + 34 * (N + ns + 1) * r := by omega
    _ = 31 * (N + ns + 1) + 34 * ((N + ns + 1) * r) := by ring
    _ ≤ 65 * ((r + 1) * (N + ns + 1)) := h4
    _ = 65 * (r + 1) * (N + ns + 1) := by ring

/-! ## §5 The reset -/

/-- The reset's specification: the distance scratch becomes the
constant sentinel array. -/
theorem gsReset_spec (B N r : ℕ) (da : String) (hNB : N < B) (hrB : r + 2 < B) :
    Spec B
      (fun σ => (σ.arrs da).length = N ∧ σ.vars "gs.n" = N ∧ σ.vars "gs.r" = r)
      (gsReset da)
      (fun _ σ' => σ'.arrs da = arrOf N fun _ => r + 1)
      (13 * N + 6) := by
  classical
  -- the loop invariant: a prefix of sentinels
  set I : Env → Prop := fun σ =>
    σ.vars "gs.n" = N ∧ σ.vars "gs.r" = r ∧ σ.vars "gs.i" ≤ N ∧
      ∃ f, σ.arrs da = arrOf N f ∧ ∀ p < σ.vars "gs.i", f p = r + 1 with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "gs.i" < N)
      (.seq (.store da (.var "gs.i") (.add (.var "gs.r") (.lit 1)))
        (.assign "gs.i" (.add (.var "gs.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "gs.i" = σ.vars "gs.i" + 1) 9 := by
    intro σ hσ
    obtain ⟨⟨hn, hr, hiN, f, hf, hpre⟩, hlt⟩ := hσ
    have hiB : σ.vars "gs.i" < B := by omega
    have hidx : σ.vars "gs.i" < (σ.arrs da).length := by
      rw [hf, length_arrOf]; omega
    have hstore : Run B (.store da (.var "gs.i") (.add (.var "gs.r") (.lit 1)))
        σ (σ.setArr da (σ.vars "gs.i") (r + 1)) 5 := by
      refine (Run.store (evalB_var hiB) ?_ hidx).mono (by simp)
      have := evalB_bin (B := B) (op := .add) (e := .var "gs.r") (f := .lit 1)
        (σ := σ) (evalB_var (by omega)) (evalB_lit (by omega)) (by rw [hr]; show r + 1 < B; omega)
      rw [hr] at this
      exact this
    have hassign : Run B (.assign "gs.i" (.add (.var "gs.i") (.lit 1)))
        (σ.setArr da (σ.vars "gs.i") (r + 1))
        ((σ.setArr da (σ.vars "gs.i") (r + 1)).setVar "gs.i" (σ.vars "gs.i" + 1)) 4 := by
      refine (Run.assign ?_).mono (by simp)
      exact evalB_bin (op := .add) (evalB_var (by simpa using hiB)) (evalB_lit (by omega))
        (by simpa using by omega : Bop.add.apply ((σ.setArr da (σ.vars "gs.i") (r+1)).vars "gs.i") 1 < B)
    refine ⟨_, (hstore.seq hassign).mono (by omega), ⟨by simp [hn], by simp [hr],
      by simp; omega, ?_⟩, by simp⟩
    refine ⟨fun p => if p = σ.vars "gs.i" then r + 1 else f p, ?_, ?_⟩
    · simp only [arrs_setVar, arrs_setArr, if_pos rfl, hf, set_arrOf]
    · intro p hp
      simp only [vars_setVar, if_pos rfl] at hp
      by_cases hpe : p = σ.vars "gs.i"
      · rw [if_pos hpe]
      · rw [if_neg hpe]
        exact hpre p (by omega)
  have hmain := Spec.forRangeZero (B := B) "gs.i" "gs.n" I N 9 hNB
    (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.1) hbody
  refine ((hmain.pre ?_).post ?_).mono (by omega)
  · rintro σ ⟨hlen, hn, hr⟩
    refine ⟨by simp [hn], by simp [hr], by simp, ?_⟩
    refine ⟨fun p => (σ.arrs da).getD p 0, ?_, by simp⟩
    simp only [arrs_setVar]
    rw [← hlen]
    exact (arrOf_getD (σ.arrs da)).symm
  · rintro σ σ' hσ ⟨⟨-, -, -, f, hf, hall⟩, hiN⟩
    rw [hf]
    exact arrOf_congr fun p hp => hall p (by omega)

/-! ## §6 The marking BFS -/

section Mark

variable {N ns r : ℕ} {G : SimpleGraph (Fin N)} (off tgt : ℕ → ℕ)

open Classical in
/-- The coupled BFS state of one marking call: the distance scratch
reads `D`, the mark array is `Mset` plus everything discovered
(`D ≤ r`), the source is at `0`, entries are bounded by the sentinel,
and every discovered entry is sound. -/
structure DSt (ma da : String) (G : SimpleGraph (Fin N)) (r : ℕ)
    (v₀ : Fin N) (Mset : Set (Fin N)) (D : ℕ → ℕ) (σ : Env) : Prop where
  dArr : σ.arrs da = arrOf N D
  mArr : σ.arrs ma = arrOf N fun w =>
    if (∃ hw : w < N, (⟨w, hw⟩ : Fin N) ∈ Mset) ∨ D w ≤ r then 1 else 0
  anchor : D (v₀ : ℕ) = 0
  bound : ∀ w, w < N → D w ≤ r + 1
  sound : ∀ w, ∀ hw : w < N, D w ≤ r → WithinDist G (D w) v₀ ⟨w, hw⟩

/-- The rows already relaxed: every vertex strictly below the level. -/
def Relaxed (G : SimpleGraph (Fin N)) (D : ℕ → ℕ) (p : ℕ) : Prop :=
  ∀ s w : Fin N, D (s : ℕ) < p → G.Adj s w → D (w : ℕ) ≤ D (s : ℕ) + 1

variable {off tgt}

/-- The invariant between rounds (`IR` at the round counter). -/
def RoundInv (o t ma da : String) (ns r : ℕ) (off tgt : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) (v₀ : Fin N) (Mset : Set (Fin N)) (σ : Env) : Prop :=
  Csr o t N ns N off tgt σ ∧
    σ.vars "gs.n" = N ∧ σ.vars "gs.r" = r ∧ σ.vars "gs.p" ≤ r ∧
    ∃ D, DSt ma da G r v₀ Mset D σ ∧ Relaxed G D (σ.vars "gs.p")

/-- The invariant inside one round's pass, at round `p`, frontier
progress up to the pass index. -/
def PassInv (o t ma da : String) (ns r : ℕ) (off tgt : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) (v₀ : Fin N) (Mset : Set (Fin N)) (p : ℕ)
    (σ : Env) : Prop :=
  Csr o t N ns N off tgt σ ∧
    σ.vars "gs.n" = N ∧ σ.vars "gs.r" = r ∧ σ.vars "gs.p" = p ∧
    σ.vars "gs.u" ≤ N ∧
    ∃ D, DSt ma da G r v₀ Mset D σ ∧ Relaxed G D p ∧
      ∀ s : Fin N, (s : ℕ) < σ.vars "gs.u" → D (s : ℕ) = p →
        ∀ w : Fin N, G.Adj s w → D (w : ℕ) ≤ p + 1

/-- The invariant inside one frontier row's scan: the vertex `u` is on
the frontier, the pointer walks its row, everything up to the pointer
is relaxed. -/
def RowInv (o t ma da : String) (ns r : ℕ) (off tgt : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) (v₀ : Fin N) (Mset : Set (Fin N)) (p u : ℕ)
    (σ : Env) : Prop :=
  Csr o t N ns N off tgt σ ∧
    σ.vars "gs.n" = N ∧ σ.vars "gs.r" = r ∧ σ.vars "gs.p" = p ∧
    σ.vars "gs.u" = u ∧ σ.vars "gs.e" = off (u + 1) ∧
    off u ≤ σ.vars "gs.j" ∧ σ.vars "gs.j" ≤ off (u + 1) ∧
    ∃ D, DSt ma da G r v₀ Mset D σ ∧ Relaxed G D p ∧ D u = p ∧
      (∀ s : Fin N, (s : ℕ) < u → D (s : ℕ) = p →
        ∀ w : Fin N, G.Adj s w → D (w : ℕ) ≤ p + 1) ∧
      ∀ q, off u ≤ q → q < σ.vars "gs.j" → D (tgt q) ≤ p + 1

variable
  (hadj : ∀ (v : Fin N) (w : ℕ),
    w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)

section RowScan

variable {B : ℕ} {o t ma da : String}
  (hNB : N < B) (hnsB : ns < B) (hrB : r + 2 < B)
  (hda_ma : da ≠ ma)

open Classical in
/-- One slot of a frontier row, as a `Run` step: read the target,
relax, advance. -/
theorem gsSlot_run {v₀ : Fin N} {Mset : Set (Fin N)} {p u : ℕ}
    (hpr : p < r) (huN : u < N) {σ : Env}
    (hσ : RowInv o t ma da ns r off tgt G v₀ Mset p u σ)
    (hj : σ.vars "gs.j" < off (u + 1)) :
    ∃ σ', Run B (gsSlotBody t ma da) σ σ' 22 ∧
      RowInv o t ma da ns r off tgt G v₀ Mset p u σ' ∧
      σ'.vars "gs.j" = σ.vars "gs.j" + 1 := by
  obtain ⟨hc, hn, hr, hp, hu, he, hjlo, hjhi, D, hD, hrel, hDu, hprog, hpart⟩ := hσ
  set j := σ.vars "gs.j" with hjdef
  have hjns : j < ns := lt_of_lt_of_le hj (hc.row_le huN)
  have hjB : j < B := by omega
  -- the target read
  have hw : tgt j < N := hc.target hjns
  have hwB : tgt j < B := by omega
  have hread : Run B (Csr.slot t "gs.j" "gs.w") σ (σ.setVar "gs.w" (tgt j)) 3 := by
    refine (Run.assign ?_).mono (by simp [Csr.slot])
    exact evalB_get (evalB_var hjB) (by rw [hc.tgtArr, getElem?_arrOf tgt hjns]) hwB
  set σ₁ := σ.setVar "gs.w" (tgt j) with hσ₁
  -- the target is a graph neighbour of `u`
  have hmem : tgt j ∈ Csr.row off tgt u := by
    rw [mem_row_iff]
    exact ⟨j, hjlo, hj, rfl⟩
  obtain ⟨hwN, hAdj⟩ := (hadj ⟨u, huN⟩ (tgt j)).mp hmem
  -- the relax condition
  have hDw : D (tgt j) ≤ r + 1 := hD.bound _ hw
  have hcond : (Cond.lt (.add (.var "gs.p") (.lit 1)) (.get da (.var "gs.w"))).evalB
      B σ₁ = some (decide (p + 1 < D (tgt j))) := by
    refine evalB_condLt ?_ ?_
    · have : σ₁.vars "gs.p" = p := by rw [hσ₁, vars_setVar, if_neg (by decide), hp]
      have hev := evalB_bin (B := B) (op := .add) (e := .var "gs.p") (f := .lit 1)
        (σ := σ₁) (evalB_var (by rw [this]; omega)) (evalB_lit (by omega))
        (by rw [this]; show p + 1 < B; omega)
      rw [this] at hev
      exact hev
    · refine evalB_get (evalB_var ?_) ?_ (by omega)
      · rw [hσ₁, vars_setVar, if_pos rfl]; omega
      · rw [hσ₁, arrs_setVar, hD.dArr, vars_setVar, if_pos rfl,
          getElem?_arrOf D hw]
  by_cases hless : p + 1 < D (tgt j)
  · -- relax: two stores
    have hlenD : (tgt j) < (σ₁.arrs da).length := by
      rw [hσ₁, arrs_setVar, hD.dArr, length_arrOf]; exact hw
    have hst1 : Run B (.store da (.var "gs.w") (.add (.var "gs.p") (.lit 1)))
        σ₁ (σ₁.setArr da (tgt j) (p + 1)) 5 := by
      refine (Run.store (evalB_var (by rw [hσ₁, vars_setVar, if_pos rfl]; omega)) ?_ ?_).mono
        (by simp)
      · have hp1 : σ₁.vars "gs.p" = p := by rw [hσ₁, vars_setVar, if_neg (by decide), hp]
        have hev := evalB_bin (B := B) (op := .add) (e := .var "gs.p") (f := .lit 1)
          (σ := σ₁) (evalB_var (by rw [hp1]; omega)) (evalB_lit (by omega))
          (by rw [hp1]; show p + 1 < B; omega)
        rw [hp1] at hev
        have : σ₁.vars "gs.w" = tgt j := by rw [hσ₁, vars_setVar, if_pos rfl]
        rw [this] at hev ⊢
        exact hev
      · have : σ₁.vars "gs.w" = tgt j := by rw [hσ₁, vars_setVar, if_pos rfl]
        rw [this]
        exact hlenD
    sorry
  · sorry

end RowScan

end Mark

end Lax3Proofs.Prog
