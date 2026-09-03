import Lax3Proofs.SolveBlocks
import Lax3Proofs.ImplScatter

/-!
# F6c/1 — `greedyScatter` as an IMP+ program, discharged

`Impl.greedyScatter G r X t` (`ImplScatter`, §6.5) is the guarded
early-stop sweep: return `0` outright at `t = 0`, otherwise scan the
vertices in ascending order, pick each unmarked member of `X`, stop at
the `t`-th pick, and mark `ball_r` of every non-final pick. This file
compiles it by the direct `Spec`-kit route and discharges the `Spec`:
**`scatterCom` leaves exactly `Impl.greedyScatter G r X t` in its count
cell** (`scatterCom_spec`, and `scatterCom_spec_graphCsr` at the head
file's seam predicate), from a state holding the graph in CSR form,
the predicate `X` as a bit array, and length-`N` mark and distance
scratch regions (dirty is fine: each call cleans its own mark slate,
inside the guard — a `t = 0` call never scans, so it never owes a
cleanup either).

## The marking BFS, inlined

The abstract routine's per-vertex test is `∀ u ∈ acc, ¬ WithinDist G r
u v`; the machine maintains the mark array `ma = ⋃_{u picked}
ball_r(u)` (`marks`) and pays for it per pick. `markCom` is a
depth-`r` BFS **by rounds** from the pick: reset the distance scratch
to the sentinel `r+1` (`gsReset`), seed the source, then `r` rounds;
each round is one owner-advancing pass over the whole slot array
(`Lib.Csr.ownerScan_spec`, `gsTurn` its turn) relaxing every slot
whose *owner* is on the frontier (`D u = round`), the mark bit written
alongside every distance write.

Correctness rides on the carried state `DSt` — source at `0`, mark
array coupled to the distances (`Mset` plus everything with `D ≤ r`),
entries bounded by the sentinel, every discovered entry *sound*
(`D w ≤ r → WithinDist G (D w) v₀ w`) — plus the relaxation clause
`Relaxed` (every vertex strictly below the round counter has relaxed
its row). *Completeness* (`WithinDist G r v₀ w → D w ≤ r`) is
**derived** from anchor + `Relaxed` by induction on the radius
(`d_complete`), not carried: the frontier of round `p` is fixed during
the round (all writes are `p+1`), which is what keeps the carried form
stable through a pass.

## The budget, in the landed charge's terms

`scatterK N ns r t = 41·N + (markK N ns r + 30)·t + 24`, with
`markK N ns r = 13·N + (15·N + 38·ns + 16)·r + 18` the per-pick
marking charge. This is `Impl.greedyScatterCost`'s shape at
`W := markK` — one scan unit per vertex plus `W` per non-final pick
(`greedyScatterCost_le : … ≤ t·(n + W)`, the `41·N` covering the
mark cleanup and the scan); the machine's `W` is
`O((r+1)·(N + ns))` (`markK_le`) — one carrier-plus-slots pass per
round — §6.5's `W := ‖A‖` instantiation at the schedule constant
`r ≤ 2R`. The guard (`t = 0` scans nothing) and the early stop (the
`t`-th pick skips the rest of the scan and its own marking) are in the
program text, exactly as `ImplScatter` demands; the sweep's potential
(`markK + 30` per pick left, `30` per vertex left) prices them.

Stored values: distances `≤ r+1`, bits `≤ 1`, counters `≤ N`, slot
pointers `≤ ns`, the count `≤ t` — the explicit `< B` hypotheses, all
below `mcB` at a schedule constant (head file's stored-value
paragraph). The scratch cells are the fixed list `gsScalars`; the five
arrays are name parameters, so one theorem serves every level's
regions (distinctness hypotheses are `decide`-dischargeable at F7's
concrete names).
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax67Proofs.Reasoning.Lib
open Lax62Proofs.Codegen (arrOf_getD getD_eq_getElem)
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

/-- The BFS step: within `p+1` is within `p`, or one edge past within
`p`. -/
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
      | cons hAdj tail =>
        rw [hwk] at hr
        simp only [SimpleGraph.Walk.length_cons] at hr
        exact ⟨_, ⟨tail.reverse, by rw [SimpleGraph.Walk.length_reverse]; omega⟩,
          hAdj.symm⟩
  · rintro (h | ⟨s, ⟨wk, hlen⟩, hAdj⟩)
    · exact withinDist_mono_radius (by omega) h
    · exact ⟨wk.concat hAdj, by rw [SimpleGraph.Walk.length_concat]; omega⟩

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
    rcases (withinDist_succ_iff q v₀ w).mp hw with h | ⟨s, hs, hAdj⟩
    · have := ih (by omega) w h
      omega
    · have hDs := ih (by omega) s hs
      have := hrel s w (by omega) hAdj
      omega

/-! ## §2 The marked set of a pick list, and small helpers -/

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

/-- Dropping the sweep's remainder, one vertex at a time. -/
theorem finRange_drop_eq {N v : ℕ} (hv : v < N) :
    (List.finRange N).drop v = ⟨v, hv⟩ :: (List.finRange N).drop (v + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hv)]
  simp

private theorem getElem?_eq_getD {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getElem?_eq_getElem h, getD_eq_getElem h]

private theorem evalB_incr {B : ℕ} {x : String} {σ : Env}
    (hx : σ.vars x + 1 < B) :
    (Expr.add (.var x) (.lit 1)).evalB B σ = some (σ.vars x + 1) := by
  have h := evalB_bin (B := B) (op := .add) (e := .var x) (f := .lit 1) (σ := σ)
    (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hx)
  simpa using h

open Classical in
/-- The abstract sweep, stepped over a picked vertex. -/
theorem scatterAux_cons_pos {N : ℕ} {G : SimpleGraph (Fin N)} {r t : ℕ}
    {X : Set (Fin N)} (acc : List (Fin N)) (v : Fin N) (vs : List (Fin N))
    (h : v ∈ X ∧ ∀ u ∈ acc, ¬ WithinDist G r u v) :
    Lax3Proofs.Impl.scatterAux G r X t acc (v :: vs)
      = if acc.length + 1 = t then t
        else Lax3Proofs.Impl.scatterAux G r X t (acc ++ [v]) vs := by
  simp only [Lax3Proofs.Impl.scatterAux]
  rw [if_pos h]

open Classical in
/-- The abstract sweep, stepped over a skipped vertex. -/
theorem scatterAux_cons_neg {N : ℕ} {G : SimpleGraph (Fin N)} {r t : ℕ}
    {X : Set (Fin N)} (acc : List (Fin N)) (v : Fin N) (vs : List (Fin N))
    (h : ¬ (v ∈ X ∧ ∀ u ∈ acc, ¬ WithinDist G r u v)) :
    Lax3Proofs.Impl.scatterAux G r X t acc (v :: vs)
      = Lax3Proofs.Impl.scatterAux G r X t acc vs := by
  simp only [Lax3Proofs.Impl.scatterAux]
  rw [if_neg h]

/-! ## §3 The program -/

/-- The routine's scratch cells (fixed names; the arrays are
parameters): pick counter, sweep index, stop bound, the four inputs
`N`/`ns`/`r`/`t`, the round counter, the owner, the slot pointer, the
slot value, the reset index. -/
def gsScalars : List String :=
  ["gs.c", "gs.v", "gs.s", "gs.n", "gs.m", "gs.r", "gs.t",
    "gs.p", "gs.u", "gs.j", "gs.w", "gs.i"]

/-- Reset the distance scratch to the sentinel `r + 1`. -/
def gsReset (da : String) : Com :=
  .seq (.assign "gs.i" (.lit 0))
    (.while (.lt (.var "gs.i") (.var "gs.n"))
      (.seq (.store da (.var "gs.i") (.add (.var "gs.r") (.lit 1)))
        (.assign "gs.i" (.add (.var "gs.i") (.lit 1)))))

/-- Zero an array's first `N` entries (the mark region, at the start
of a sweep — each call cleans its own slate, so a `t = 0` call, which
never scans, never owes a cleanup either). -/
def gsZero (a : String) : Com :=
  .seq (.assign "gs.i" (.lit 0))
    (.while (.lt (.var "gs.i") (.var "gs.n"))
      (.seq (.store a (.var "gs.i") (.lit 0))
        (.assign "gs.i" (.add (.var "gs.i") (.lit 1)))))

/-- One slot of a round's pass: read the target; if the slot's owner is
on the frontier and the target improves, relax it (distance and mark
bit together); advance the slot pointer. -/
def gsRelaxStep (ta ma da : String) : Com :=
  .seq (Csr.slot ta "gs.j" "gs.w")
    (.seq
      (.ite (.eq (.get da (.var "gs.u")) (.var "gs.p"))
        (.ite (.lt (.add (.var "gs.p") (.lit 1)) (.get da (.var "gs.w")))
          (.seq (.store da (.var "gs.w") (.add (.var "gs.p") (.lit 1)))
            (.store ma (.var "gs.w") (.lit 1)))
          .skip)
        .skip)
      (.assign "gs.j" (.add (.var "gs.j") (.lit 1))))

/-- One turn of the owner-advancing pass: inside the owner's row, take
the slot; at its end, move the owner on (`Lib.Csr`'s `ownerStep`
shape). -/
def gsTurn (oa ta ma da : String) : Com :=
  .ite (.lt (.var "gs.j") (.get oa (.add (.var "gs.u") (.lit 1))))
    (gsRelaxStep ta ma da)
    (.assign "gs.u" (.add (.var "gs.u") (.lit 1)))

/-- One round: reset the two pointers, one full owner-advancing pass,
advance the round counter. -/
def gsRound (oa ta ma da : String) : Com :=
  .seq (.assign "gs.u" (.lit 0))
    (.seq (.assign "gs.j" (.lit 0))
      (.seq (Csr.scan "gs.j" "gs.m" (gsTurn oa ta ma da))
        (.assign "gs.p" (.add (.var "gs.p") (.lit 1)))))

/-- **The marking BFS**: reset the scratch, seed the pick (distance
`0`, mark bit set), run `r` rounds. Marks accumulate — the mark array
is never cleared, which is the sweep's union-of-balls discipline. -/
def markCom (oa ta ma da : String) : Com :=
  .seq (gsReset da)
    (.seq (.store da (.var "gs.v") (.lit 0))
      (.seq (.store ma (.var "gs.v") (.lit 1))
        (.seq (.assign "gs.p" (.lit 0))
          (.while (.lt (.var "gs.p") (.var "gs.r")) (gsRound oa ta ma da)))))

/-- One vertex of the sweep: if it satisfies the predicate and is
unmarked, pick it — the `t`-th pick stops the scan (`stop := 0`,
skipping its own marking), any earlier pick marks its ball; then
advance. -/
def gsSweepBody (oa ta pa ma da : String) : Com :=
  .seq
    (.ite (.eq (.get pa (.var "gs.v")) (.lit 1))
      (.ite (.lt (.get ma (.var "gs.v")) (.lit 1))
        (.seq (.assign "gs.c" (.add (.var "gs.c") (.lit 1)))
          (.ite (.eq (.var "gs.c") (.var "gs.t"))
            (.assign "gs.s" (.lit 0))
            (markCom oa ta ma da)))
        .skip)
      .skip)
    (.assign "gs.v" (.add (.var "gs.v") (.lit 1)))

/-- The unguarded sweep: clean the mark region, counter and index to
`0`, stop bound to `N`, scan. -/
def gsSweep (oa ta pa ma da : String) : Com :=
  .seq (gsZero ma)
    (.seq (.assign "gs.c" (.lit 0))
      (.seq (.assign "gs.v" (.lit 0))
        (.seq (.assign "gs.s" (.var "gs.n"))
          (.while (.lt (.var "gs.v") (.var "gs.s")) (gsSweepBody oa ta pa ma da)))))

/-- **`greedyScatter`, as IMP+**: the `t = 0` guard explicit in the
program text (§6.5 — the guard is a cost statement), else the sweep. -/
def scatterCom (oa ta pa ma da : String) : Com :=
  .ite (.eq (.var "gs.t") (.lit 0))
    (.assign "gs.c" (.lit 0))
    (gsSweep oa ta pa ma da)

/-! The frame data of the marking call, computed once (the sweep steps
over `markCom` and reads them off). -/

theorem wvars_markCom (oa ta ma da : String) :
    (markCom oa ta ma da).wvars =
      ["gs.i", "gs.i", "gs.p", "gs.u", "gs.j", "gs.w", "gs.j", "gs.u", "gs.p"] := rfl

theorem warrs_markCom (oa ta ma da : String) :
    (markCom oa ta ma da).warrs = [da, da, ma, da, ma] := rfl

theorem noWrite_markCom (oa ta ma da : String) : (markCom oa ta ma da).NoWrite := by
  simp [markCom, gsReset, gsRound, gsTurn, gsRelaxStep, Csr.scan, Csr.slot,
    Com.NoWrite]

theorem not_reads_markCom (oa ta ma da : String) : ¬ (markCom oa ta ma da).reads := by
  simp [markCom, gsReset, gsRound, gsTurn, gsRelaxStep, Csr.scan, Csr.slot,
    Com.reads]

/-! The frame data of the whole routine — consumers apply
`(scatterCom_spec …).frame` and read the untouched state off these. -/

theorem wvars_scatterCom (oa ta pa ma da : String) :
    (scatterCom oa ta pa ma da).wvars =
      ["gs.c", "gs.i", "gs.i", "gs.c", "gs.v", "gs.s",
        "gs.c", "gs.s", "gs.i", "gs.i", "gs.p", "gs.u", "gs.j", "gs.w",
        "gs.j", "gs.u", "gs.p", "gs.v"] := rfl

/-- Every cell the routine writes is scratch. -/
theorem wvars_scatterCom_subset (oa ta pa ma da : String) :
    ∀ y ∈ (scatterCom oa ta pa ma da).wvars, y ∈ gsScalars := by
  rw [wvars_scatterCom]
  decide

theorem warrs_scatterCom (oa ta pa ma da : String) :
    (scatterCom oa ta pa ma da).warrs = [ma, da, da, ma, da, ma] := rfl

theorem noWrite_scatterCom (oa ta pa ma da : String) :
    (scatterCom oa ta pa ma da).NoWrite := by
  simp [scatterCom, gsSweep, gsSweepBody, gsZero, markCom, gsReset, gsRound,
    gsTurn, gsRelaxStep, Csr.scan, Csr.slot, Com.NoWrite]

theorem not_reads_scatterCom (oa ta pa ma da : String) :
    ¬ (scatterCom oa ta pa ma da).reads := by
  simp [scatterCom, gsSweep, gsSweepBody, gsZero, markCom, gsReset, gsRound,
    gsTurn, gsRelaxStep, Csr.scan, Csr.slot, Com.reads]

/-! ## §4 The budgets -/

/-- The per-pick marking charge: the reset, the seed, `r` rounds of one
owner-advancing pass each (`34` a slot, `11` a row). -/
def markK (N ns r : ℕ) : ℕ := 13 * N + (15 * N + 38 * ns + 16) * r + 18

/-- **The routine's budget**: `Impl.greedyScatterCost`'s `t·(n + W)`
shape at `W := markK` — the mark region's cleanup and one scan unit
per vertex (`41·N`), `markK + 30` per pick. -/
def scatterK (N ns r t : ℕ) : ℕ := 41 * N + (markK N ns r + 30) * t + 24

/-- The marking charge is §6.5's `W := ‖A‖` at a schedule constant:
linear in carrier plus slots, one pass per round. -/
theorem markK_le (N ns r : ℕ) : markK N ns r ≤ 69 * (r + 1) * (N + ns + 1) := by
  have h2 : 15 * N + 38 * ns + 16 ≤ 38 * (N + ns + 1) := by omega
  have h3 : (15 * N + 38 * ns + 16) * r ≤ 38 * (N + ns + 1) * r :=
    Nat.mul_le_mul_right r h2
  have he : 69 * (r + 1) * (N + ns + 1)
      = 38 * (N + ns + 1) * r + (31 * (N + ns + 1) * r + 69 * (N + ns + 1)) := by
    ring
  have h1 : 13 * N + 18 ≤ 69 * (N + ns + 1) := by omega
  simp only [markK]
  rw [he]
  omega

/-- **The whole routine's envelope**, for F7's reconciliation: one
schedule constant times `(t+1)·(r+1)·‖CSR‖` — `greedyScatterCost`'s
`t·(n + W)` closed under the machine's `W`. -/
theorem scatterK_le (N ns r t : ℕ) :
    scatterK N ns r t ≤ 130 * ((t + 1) * ((r + 1) * (N + ns + 1))) := by
  have hmk := markK_le N ns r
  have hP0 : 0 < (r + 1) * (N + ns + 1) := by positivity
  set P := (r + 1) * (N + ns + 1) with hP
  have hmk' : markK N ns r ≤ 69 * P := by
    rw [hP, ← Nat.mul_assoc]
    exact hmk
  have hNP : N + ns + 1 ≤ P := by
    rw [hP]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have htP : t ≤ P * t := Nat.le_mul_of_pos_left t hP0
  have hstep : (markK N ns r + 30) * t ≤ 69 * (P * t) + 30 * (P * t) := by
    calc (markK N ns r + 30) * t ≤ (69 * P + 30) * t :=
          Nat.mul_le_mul_right t (by omega)
      _ = 69 * (P * t) + 30 * t := by ring
      _ ≤ 69 * (P * t) + 30 * (P * t) := by omega
  have hexp : 130 * ((t + 1) * P) = 130 * P + 130 * (P * t) := by ring
  have hfin : scatterK N ns r t = 41 * N + (markK N ns r + 30) * t + 24 := rfl
  omega

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
    have hval : (Expr.add (.var "gs.r") (.lit 1)).evalB B σ = some (r + 1) := by
      have h := evalB_bin (B := B) (op := .add) (e := .var "gs.r") (f := .lit 1)
        (σ := σ) (evalB_var (by omega)) (evalB_lit (by omega))
        (by rw [hr]; show r + 1 < B; omega)
      rw [hr] at h
      simpa using h
    have hstore : Run B (.store da (.var "gs.i") (.add (.var "gs.r") (.lit 1)))
        σ (σ.setArr da (σ.vars "gs.i") (r + 1)) 5 :=
      (Run.store (evalB_var hiB) hval hidx).mono (by simp)
    set σ₁ := σ.setArr da (σ.vars "gs.i") (r + 1) with hσ₁
    have hassign : Run B (.assign "gs.i" (.add (.var "gs.i") (.lit 1)))
        σ₁ (σ₁.setVar "gs.i" (σ.vars "gs.i" + 1)) 4 := by
      have hev : (Expr.add (.var "gs.i") (.lit 1)).evalB B σ₁
          = some (σ.vars "gs.i" + 1) := by
        have h := evalB_incr (B := B) (x := "gs.i") (σ := σ₁)
          (by rw [hσ₁, vars_setArr]; omega)
        rw [hσ₁] at h ⊢
        simpa using h
      exact (Run.assign hev).mono (by simp)
    refine ⟨_, (hstore.seq hassign).mono (by omega),
      ⟨by simp [hσ₁, hn], by simp [hσ₁, hr], by simp [hσ₁]; omega, ?_⟩,
      by simp [hσ₁]⟩
    refine ⟨fun p => if p = σ.vars "gs.i" then r + 1 else f p, ?_, ?_⟩
    · simp [hσ₁, hf, set_arrOf]
    · intro p hp
      simp [hσ₁] at hp
      show (if p = σ.vars "gs.i" then r + 1 else f p) = r + 1
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

/-- The zeroing pass's specification. -/
theorem gsZero_spec (B N : ℕ) (a : String) (hNB : N < B) (h0B : 0 < B) :
    Spec B
      (fun σ => (σ.arrs a).length = N ∧ σ.vars "gs.n" = N)
      (gsZero a)
      (fun _ σ' => σ'.arrs a = arrOf N fun _ => 0)
      (11 * N + 6) := by
  classical
  set I : Env → Prop := fun σ =>
    σ.vars "gs.n" = N ∧ σ.vars "gs.i" ≤ N ∧
      ∃ f, σ.arrs a = arrOf N f ∧ ∀ p < σ.vars "gs.i", f p = 0 with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "gs.i" < N)
      (.seq (.store a (.var "gs.i") (.lit 0))
        (.assign "gs.i" (.add (.var "gs.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "gs.i" = σ.vars "gs.i" + 1) 7 := by
    intro σ hσ
    obtain ⟨⟨hn, hiN, f, hf, hpre⟩, hlt⟩ := hσ
    have hiB : σ.vars "gs.i" < B := by omega
    have hidx : σ.vars "gs.i" < (σ.arrs a).length := by
      rw [hf, length_arrOf]; omega
    have hstore : Run B (.store a (.var "gs.i") (.lit 0))
        σ (σ.setArr a (σ.vars "gs.i") 0) 3 :=
      (Run.store (evalB_var hiB) (evalB_lit h0B) hidx).mono (by simp)
    set σ₁ := σ.setArr a (σ.vars "gs.i") 0 with hσ₁
    have hassign : Run B (.assign "gs.i" (.add (.var "gs.i") (.lit 1)))
        σ₁ (σ₁.setVar "gs.i" (σ.vars "gs.i" + 1)) 4 := by
      have hev : (Expr.add (.var "gs.i") (.lit 1)).evalB B σ₁
          = some (σ.vars "gs.i" + 1) := by
        have h := evalB_incr (B := B) (x := "gs.i") (σ := σ₁)
          (by rw [hσ₁, vars_setArr]; omega)
        rw [hσ₁] at h ⊢
        simpa using h
      exact (Run.assign hev).mono (by simp)
    refine ⟨_, (hstore.seq hassign).mono (by omega),
      ⟨by simp [hσ₁, hn], by simp [hσ₁]; omega, ?_⟩, by simp [hσ₁]⟩
    refine ⟨fun p => if p = σ.vars "gs.i" then 0 else f p, ?_, ?_⟩
    · simp [hσ₁, hf, set_arrOf]
    · intro p hp
      simp [hσ₁] at hp
      show (if p = σ.vars "gs.i" then 0 else f p) = 0
      by_cases hpe : p = σ.vars "gs.i"
      · rw [if_pos hpe]
      · rw [if_neg hpe]
        exact hpre p (by omega)
  have hmain := Spec.forRangeZero (B := B) "gs.i" "gs.n" I N 7 hNB
    (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) hbody
  refine ((hmain.pre ?_).post ?_).mono (by omega)
  · rintro σ ⟨hlen, hn⟩
    refine ⟨by simp [hn], by simp, ?_⟩
    refine ⟨fun p => (σ.arrs a).getD p 0, ?_, by simp⟩
    simp only [arrs_setVar]
    rw [← hlen]
    exact (arrOf_getD (σ.arrs a)).symm
  · rintro σ σ' hσ ⟨⟨-, -, f, hf, hall⟩, hiN⟩
    rw [hf]
    exact arrOf_congr fun p hp => hall p (by omega)

/-! ## §6 The marking BFS -/

section Mark

variable {B N ns r : ℕ} {G : SimpleGraph (Fin N)}
  {oa ta ma da : String} {off tgt : ℕ → ℕ}

open Classical in
/-- The coupled BFS state of one marking call: the distance scratch
reads `D`, the mark array is `Mset` plus everything discovered
(`D ≤ r`), the source is at `0`, entries are bounded by the sentinel,
every discovered entry is sound. -/
structure DSt (ma da : String) (G : SimpleGraph (Fin N)) (r : ℕ)
    (v₀ : Fin N) (Mset : Set (Fin N)) (D : ℕ → ℕ) (σ : Env) : Prop where
  dArr : σ.arrs da = arrOf N D
  mArr : σ.arrs ma = arrOf N fun w =>
    if (∃ hw : w < N, (⟨w, hw⟩ : Fin N) ∈ Mset) ∨ D w ≤ r then 1 else 0
  anchor : D (v₀ : ℕ) = 0
  bound : ∀ w, w < N → D w ≤ r + 1
  sound : ∀ w, ∀ hw : w < N, D w ≤ r → WithinDist G (D w) v₀ ⟨w, hw⟩

/-- Every vertex strictly below the level has relaxed its row. -/
def Relaxed (G : SimpleGraph (Fin N)) (D : ℕ → ℕ) (p : ℕ) : Prop :=
  ∀ s w : Fin N, D (s : ℕ) < p → G.Adj s w → D (w : ℕ) ≤ D (s : ℕ) + 1

/-- The invariant of one round's pass at level `p`: the CSR, the
cells, the owner discipline, the coupled BFS state, `Relaxed` below
`p`, and partial progress — every slot below the pointer whose owner
is on the frontier has been relaxed. -/
def PassInv (oa ta ma da : String) (ns r : ℕ) (off tgt : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) (v₀ : Fin N) (Mset : Set (Fin N)) (p : ℕ)
    (σ : Env) : Prop :=
  Csr oa ta N ns N off tgt σ ∧
    σ.vars "gs.n" = N ∧ σ.vars "gs.m" = ns ∧ σ.vars "gs.r" = r ∧
    σ.vars "gs.p" = p ∧
    σ.vars "gs.u" ≤ N ∧ σ.vars "gs.j" ≤ ns ∧
    off (σ.vars "gs.u") ≤ σ.vars "gs.j" ∧
    ∃ D, DSt ma da G r v₀ Mset D σ ∧ Relaxed G D p ∧
      ∀ (s : Fin N) (q : ℕ), D (s : ℕ) = p → off (s : ℕ) ≤ q →
        q < off ((s : ℕ) + 1) → q < σ.vars "gs.j" → D (tgt q) ≤ p + 1

/-- The invariant between rounds: `Relaxed` at the round counter. -/
def RoundInv (oa ta ma da : String) (ns r : ℕ) (off tgt : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) (v₀ : Fin N) (Mset : Set (Fin N)) (σ : Env) : Prop :=
  Csr oa ta N ns N off tgt σ ∧
    σ.vars "gs.n" = N ∧ σ.vars "gs.m" = ns ∧ σ.vars "gs.r" = r ∧
    σ.vars "gs.p" ≤ r ∧
    ∃ D, DSt ma da G r v₀ Mset D σ ∧ Relaxed G D (σ.vars "gs.p")

variable
  (hadj : ∀ (v : Fin N) (w : ℕ),
    w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
  (hoff0 : off 0 = 0)
  (hNB : N < B) (hnsB : ns < B) (hrB : r + 2 < B)
  (hda_oa : da ≠ oa) (hda_ta : da ≠ ta) (hda_ma : da ≠ ma)
  (hma_oa : ma ≠ oa) (hma_ta : ma ≠ ta)

section Turn

variable {v₀ : Fin N} {Mset : Set (Fin N)} {p : ℕ}

include hadj hNB hnsB hrB hda_oa hda_ta hda_ma hma_oa hma_ta in
open Classical in
/-- **One turn of the pass**, in `ownerScan_spec`'s step form: it
either relaxes a slot or moves the owner on, keeps the invariant, and
costs `34` per slot moved, `11` per row moved. -/
theorem gsTurn_step (hpr : p < r) :
    ∀ σ, PassInv oa ta ma da ns r off tgt G v₀ Mset p σ → σ.vars "gs.j" < ns →
      ∃ σ' K', Run B (gsTurn oa ta ma da) σ σ' K' ∧
        PassInv oa ta ma da ns r off tgt G v₀ Mset p σ' ∧
        σ.vars "gs.j" ≤ σ'.vars "gs.j" ∧ σ.vars "gs.u" ≤ σ'.vars "gs.u" ∧
        (σ.vars "gs.j" < σ'.vars "gs.j" ∨ σ.vars "gs.u" < σ'.vars "gs.u") ∧
        K' ≤ 34 * (σ'.vars "gs.j" - σ.vars "gs.j")
          + 11 * (σ'.vars "gs.u" - σ.vars "gs.u") := by
  rintro σ ⟨hc, hn, hm, hr, hp, hu, hj, hlo, D, hD, hrel, hpart⟩ hjns
  have huN : σ.vars "gs.u" < N := hc.owner_lt hu hlo hjns
  set u := σ.vars "gs.u" with hu_def
  set j := σ.vars "gs.j" with hj_def
  -- the turn's test: `j < off (u+1)`
  have hoffval : (Expr.get oa (.add (.var "gs.u") (.lit 1))).evalB B σ
      = some (off (u + 1)) := by
    refine evalB_get (k := u + 1) (evalB_incr (by omega)) ?_
      (hc.off_lt hnsB (by omega))
    rw [hc.offArr, getElem?_arrOf off (by omega)]
  have hcond := evalB_condLt (evalB_var (x := "gs.j") (σ := σ) (by omega)) hoffval
  by_cases hslot : j < off (u + 1)
  · -- inside the row: take the slot
    have hcondT : (Cond.lt (.var "gs.j")
        (.get oa (.add (.var "gs.u") (.lit 1)))).evalB B σ = some true := by
      rw [hcond]
      congr 1
      simpa using hslot
    set w := tgt j with hw_def
    have hwN : w < N := hc.target hjns
    -- slot read
    have hread : Run B (Csr.slot ta "gs.j" "gs.w") σ (σ.setVar "gs.w" w) 3 := by
      refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono
        (by simp)
      rw [hc.tgtArr, getElem?_arrOf tgt hjns]
    set σ₁ := σ.setVar "gs.w" w with hσ₁
    have h1u : σ₁.vars "gs.u" = u := by rw [hσ₁]; simp [hu_def]
    have h1p : σ₁.vars "gs.p" = p := by rw [hσ₁]; simp [← hp]
    have h1w : σ₁.vars "gs.w" = w := by rw [hσ₁]; simp
    have h1j : σ₁.vars "gs.j" = j := by rw [hσ₁]; simp [hj_def]
    have h1da : σ₁.arrs da = arrOf N D := by rw [hσ₁]; simpa using hD.dArr
    -- the frontier test
    have hfrontEv : (Cond.eq (.get da (.var "gs.u")) (.var "gs.p")).evalB B σ₁
        = some (D u == p) := by
      have hDuB : D u ≤ r + 1 := hD.bound u huN
      have hval : (Expr.get da (.var "gs.u")).evalB B σ₁ = some (D u) := by
        refine evalB_get (evalB_var (by rw [h1u]; omega)) ?_ (by omega)
        rw [h1da, h1u, getElem?_arrOf D huN]
      have hpev : (Expr.var "gs.p").evalB B σ₁ = some p := by
        rw [← h1p]
        exact evalB_var (by rw [h1p]; omega)
      exact evalB_condEq hval hpev
    -- the slot is a graph edge out of `u`
    have hAdj : G.Adj ⟨u, huN⟩ ⟨w, hwN⟩ := by
      have hmem : w ∈ Csr.row off tgt u := by
        rw [mem_row_iff]
        exact ⟨j, hlo, hslot, rfl⟩
      obtain ⟨hw', hA⟩ := (hadj ⟨u, huN⟩ w).mp hmem
      exact hA
    by_cases hfront : D u = p
    · have hfrontT : (Cond.eq (.get da (.var "gs.u")) (.var "gs.p")).evalB B σ₁
          = some true := by
        rw [hfrontEv]
        congr 1
        simpa using hfront
      have hDwB : D w ≤ r + 1 := hD.bound w hwN
      have hrelEv : (Cond.lt (.add (.var "gs.p") (.lit 1))
          (.get da (.var "gs.w"))).evalB B σ₁ = some (decide (p + 1 < D w)) := by
        refine evalB_condLt ?_
          (evalB_get (evalB_var (by rw [h1w]; omega)) ?_ (by omega))
        · have h := evalB_incr (B := B) (x := "gs.p") (σ := σ₁) (by rw [h1p]; omega)
          rwa [h1p] at h
        · rw [h1da, h1w, getElem?_arrOf D hwN]
      by_cases himp : p + 1 < D w
      · -- relax: the two stores
        have hrelT : (Cond.lt (.add (.var "gs.p") (.lit 1))
            (.get da (.var "gs.w"))).evalB B σ₁ = some true := by
          rw [hrelEv]
          congr 1
          simpa using himp
        have hpev : (Expr.add (.var "gs.p") (.lit 1)).evalB B σ₁ = some (p + 1) := by
          have h := evalB_incr (B := B) (x := "gs.p") (σ := σ₁) (by rw [h1p]; omega)
          rwa [h1p] at h
        have hst1 : Run B (.store da (.var "gs.w") (.add (.var "gs.p") (.lit 1)))
            σ₁ (σ₁.setArr da w (p + 1)) 5 := by
          have hwev : (Expr.var "gs.w").evalB B σ₁ = some w := by
            rw [← h1w]
            exact evalB_var (by rw [h1w]; omega)
          refine (Run.store hwev hpev ?_).mono (by simp)
          rw [h1da, length_arrOf]
          exact hwN
        set σ₂ := σ₁.setArr da w (p + 1) with hσ₂
        have hst2 : Run B (.store ma (.var "gs.w") (.lit 1))
            σ₂ (σ₂.setArr ma w 1) 3 := by
          have h2w : σ₂.vars "gs.w" = w := by rw [hσ₂]; simpa using h1w
          have hwev : (Expr.var "gs.w").evalB B σ₂ = some w := by
            rw [← h2w]
            exact evalB_var (by rw [h2w]; omega)
          refine (Run.store hwev (evalB_lit (by omega)) ?_).mono (by simp)
          rw [hσ₂, hσ₁]
          simp [Ne.symm hda_ma, hD.mArr, hwN]
        set σ₃ := σ₂.setArr ma w 1 with hσ₃
        have hinc : Run B (.assign "gs.j" (.add (.var "gs.j") (.lit 1)))
            σ₃ (σ₃.setVar "gs.j" (j + 1)) 4 := by
          have h3j : σ₃.vars "gs.j" = j := by rw [hσ₃, hσ₂]; simpa using h1j
          have hev := evalB_incr (B := B) (x := "gs.j") (σ := σ₃)
            (by rw [h3j]; omega)
          rw [h3j] at hev
          exact (Run.assign hev).mono (by simp)
        set σ' := σ₃.setVar "gs.j" (j + 1) with hσ'
        have hrun : Run B (gsTurn oa ta ma da) σ σ' 34 := by
          have hInner : Run B (.ite (.lt (.add (.var "gs.p") (.lit 1))
              (.get da (.var "gs.w")))
              (.seq (.store da (.var "gs.w") (.add (.var "gs.p") (.lit 1)))
                (.store ma (.var "gs.w") (.lit 1))) .skip) σ₁ σ₃ 15 :=
            (Run.ite_true hrelT (hst1.seq hst2)).mono (by simp)
          have hOuter : Run B (.ite (.eq (.get da (.var "gs.u")) (.var "gs.p"))
              (.ite (.lt (.add (.var "gs.p") (.lit 1)) (.get da (.var "gs.w")))
                (.seq (.store da (.var "gs.w") (.add (.var "gs.p") (.lit 1)))
                  (.store ma (.var "gs.w") (.lit 1)))
                .skip)
              .skip) σ₁ σ₃ 20 :=
            (Run.ite_true hfrontT hInner).mono (by simp)
          have hRel : Run B (gsRelaxStep ta ma da) σ σ' 27 :=
            (hread.seq (hOuter.seq hinc)).mono (by simp)
          exact (Run.ite_true hcondT hRel).mono (by simp)
        -- the projections of the final environment
        have h'j : σ'.vars "gs.j" = j + 1 := by rw [hσ']; simp
        have h'u : σ'.vars "gs.u" = u := by
          rw [hσ', hσ₃, hσ₂, hσ₁]; simp [hu_def]
        have h'vars : ∀ y, y ≠ "gs.j" → y ≠ "gs.w" → σ'.vars y = σ.vars y := by
          intro y hy1 hy2
          rw [hσ', hσ₃, hσ₂, hσ₁]
          simp [hy1, hy2]
        have h'da : σ'.arrs da = (arrOf N D).set w (p + 1) := by
          rw [hσ', hσ₃, hσ₂, hσ₁]
          simp [hda_ma, hD.dArr]
        have h'ma : σ'.arrs ma = ((arrOf N fun q =>
            if (∃ hq : q < N, (⟨q, hq⟩ : Fin N) ∈ Mset) ∨ D q ≤ r then 1 else 0).set
              w 1) := by
          rw [hσ', hσ₃, hσ₂, hσ₁]
          simp [Ne.symm hda_ma, hD.mArr]
        have h'other : ∀ b, b ≠ da → b ≠ ma → σ'.arrs b = σ.arrs b := by
          intro b hb1 hb2
          rw [hσ', hσ₃, hσ₂, hσ₁]
          simp [hb1, hb2]
        -- the new table
        set D' : ℕ → ℕ := fun q => if q = w then p + 1 else D q with hD'_def
        have hD'w : D' w = p + 1 := by
          show (if w = w then p + 1 else D w) = p + 1
          rw [if_pos rfl]
        have hD'ne : ∀ q, q ≠ w → D' q = D q := by
          intro q hq
          show (if q = w then p + 1 else D q) = D q
          rw [if_neg hq]
        have hD'le : ∀ q, D' q ≤ D q := by
          intro q
          by_cases hq : q = w
          · rw [hq, hD'w]; omega
          · exact le_of_eq (hD'ne q hq)
        have hwd : WithinDist G (p + 1) v₀ ⟨w, hwN⟩ := by
          have h₁ : WithinDist G p v₀ ⟨u, huN⟩ := by
            have := hD.sound u huN (by omega)
            rwa [hfront] at this
          have := withinDist_trans h₁ (withinDist_of_adj hAdj)
          simpa using this
        refine ⟨σ', 34, hrun,
          ⟨hc.of_eq (h'other oa (Ne.symm hda_oa) (Ne.symm hma_oa))
            (h'other ta (Ne.symm hda_ta) (Ne.symm hma_ta)),
            by rw [h'vars _ (by decide) (by decide)]; exact hn,
            by rw [h'vars _ (by decide) (by decide)]; exact hm,
            by rw [h'vars _ (by decide) (by decide)]; exact hr,
            by rw [h'vars _ (by decide) (by decide)]; exact hp,
            by rw [h'u]; exact hu,
            by rw [h'j]; omega,
            by rw [h'u, h'j]; omega,
            D', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩,
          by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
          by rw [h'j, h'u]; omega⟩
        · -- dArr
          rw [h'da, set_arrOf, hD'_def]
        · -- mArr
          rw [h'ma, set_arrOf]
          refine arrOf_congr fun q hqN => ?_
          show (if q = w then 1
              else if (∃ hq : q < N, (⟨q, hq⟩ : Fin N) ∈ Mset) ∨ D q ≤ r then 1 else 0)
            = (if (∃ hq : q < N, (⟨q, hq⟩ : Fin N) ∈ Mset) ∨ D' q ≤ r then 1 else 0)
          by_cases hq : q = w
          · rw [if_pos hq, hq, if_pos (Or.inr (by rw [hD'w]; omega))]
          · rw [if_neg hq, hD'ne q hq]
        · -- anchor
          show (if (v₀ : ℕ) = w then p + 1 else D (v₀ : ℕ)) = 0
          by_cases hq : (v₀ : ℕ) = w
          · exfalso
            have := hD.anchor
            rw [hq] at this
            omega
          · rw [if_neg hq]
            exact hD.anchor
        · -- bound
          intro q hqN
          by_cases hq : q = w
          · rw [hq, hD'w]; omega
          · rw [hD'ne q hq]
            exact hD.bound q hqN
        · -- sound
          intro q hqN hle
          by_cases hq : q = w
          · subst hq
            rw [hD'w]
            exact hwd
          · rw [hD'ne q hq] at hle ⊢
            exact hD.sound q hqN hle
        · -- Relaxed
          intro s w' hs hA
          have hsw : (s : ℕ) ≠ w := by
            intro hcon
            rw [hcon, hD'w] at hs
            omega
          rw [hD'ne _ hsw] at hs ⊢
          calc D' (w' : ℕ) ≤ D (w' : ℕ) := hD'le _
            _ ≤ D (s : ℕ) + 1 := hrel s w' hs hA
        · -- partial progress
          intro s q hsD hq1 hq2 hq3
          rw [h'j] at hq3
          have hsw : (s : ℕ) ≠ w := by
            intro hcon
            rw [hcon, hD'w] at hsD
            omega
          rw [hD'ne _ hsw] at hsD
          rcases Nat.lt_or_ge q j with hqj | hqj
          · exact le_trans (hD'le _) (hpart s q hsD hq1 hq2 hqj)
          · have hqeq : q = j := by omega
            subst hqeq
            have hsu : (s : ℕ) = u :=
              hc.owner_unique (by omega) (by omega) hq1 hq2 hlo hslot
            rw [← hw_def]
            rw [hD'w]
        -- no-relax and off-frontier branches share their environment
      · have hrelF : (Cond.lt (.add (.var "gs.p") (.lit 1))
            (.get da (.var "gs.w"))).evalB B σ₁ = some false := by
          rw [hrelEv]
          congr 1
          simpa using himp
        set σ' := σ₁.setVar "gs.j" (j + 1) with hσ'
        have hinc : Run B (.assign "gs.j" (.add (.var "gs.j") (.lit 1)))
            σ₁ σ' 4 := by
          have hev := evalB_incr (B := B) (x := "gs.j") (σ := σ₁)
            (by rw [h1j]; omega)
          rw [h1j] at hev
          exact (Run.assign hev).mono (by simp)
        have hrun : Run B (gsTurn oa ta ma da) σ σ' 34 := by
          refine (Run.ite_true hcondT (hread.seq
            ((Run.ite_true hfrontT (Run.ite_false hrelF Run.skip)).seq hinc))).mono ?_
          simp
        have h'j : σ'.vars "gs.j" = j + 1 := by rw [hσ']; simp
        have h'u : σ'.vars "gs.u" = u := by rw [hσ', hσ₁]; simp [hu_def]
        have h'vars : ∀ y, y ≠ "gs.j" → y ≠ "gs.w" → σ'.vars y = σ.vars y := by
          intro y hy1 hy2
          rw [hσ', hσ₁]
          simp [hy1, hy2]
        have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := by
          intro b
          rw [hσ', hσ₁]
          simp
        refine ⟨σ', 34, hrun,
          ⟨hc.of_eq (h'arrs oa) (h'arrs ta),
            by rw [h'vars _ (by decide) (by decide)]; exact hn,
            by rw [h'vars _ (by decide) (by decide)]; exact hm,
            by rw [h'vars _ (by decide) (by decide)]; exact hr,
            by rw [h'vars _ (by decide) (by decide)]; exact hp,
            by rw [h'u]; exact hu,
            by rw [h'j]; omega,
            by rw [h'u, h'j]; omega,
            D, ⟨by rw [h'arrs]; exact hD.dArr, by rw [h'arrs]; exact hD.mArr,
              hD.anchor, hD.bound, hD.sound⟩, hrel, ?_⟩,
          by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
          by rw [h'j, h'u]; omega⟩
        intro s q hsD hq1 hq2 hq3
        rw [h'j] at hq3
        rcases Nat.lt_or_ge q j with hqj | hqj
        · exact hpart s q hsD hq1 hq2 hqj
        · have hqeq : q = j := by omega
          subst hqeq
          have hsu : (s : ℕ) = u :=
            hc.owner_unique (by omega) (by omega) hq1 hq2 hlo hslot
          rw [← hw_def]
          omega
    · -- the owner is off the frontier: skip the slot
      have hfrontF : (Cond.eq (.get da (.var "gs.u")) (.var "gs.p")).evalB B σ₁
          = some false := by
        rw [hfrontEv]
        congr 1
        simpa using hfront
      set σ' := σ₁.setVar "gs.j" (j + 1) with hσ'
      have hinc : Run B (.assign "gs.j" (.add (.var "gs.j") (.lit 1)))
          σ₁ σ' 4 := by
        have hev := evalB_incr (B := B) (x := "gs.j") (σ := σ₁)
          (by rw [h1j]; omega)
        rw [h1j] at hev
        exact (Run.assign hev).mono (by simp)
      have hrun : Run B (gsTurn oa ta ma da) σ σ' 34 := by
        have hOuter : Run B (.ite (.eq (.get da (.var "gs.u")) (.var "gs.p"))
            (.ite (.lt (.add (.var "gs.p") (.lit 1)) (.get da (.var "gs.w")))
              (.seq (.store da (.var "gs.w") (.add (.var "gs.p") (.lit 1)))
                (.store ma (.var "gs.w") (.lit 1)))
              .skip)
            .skip) σ₁ σ₁ 20 :=
          (Run.ite_false hfrontF Run.skip).mono (by simp)
        have hRel : Run B (gsRelaxStep ta ma da) σ σ' 27 :=
          (hread.seq (hOuter.seq hinc)).mono (by simp)
        exact (Run.ite_true hcondT hRel).mono (by simp)
      have h'j : σ'.vars "gs.j" = j + 1 := by rw [hσ']; simp
      have h'u : σ'.vars "gs.u" = u := by rw [hσ', hσ₁]; simp [hu_def]
      have h'vars : ∀ y, y ≠ "gs.j" → y ≠ "gs.w" → σ'.vars y = σ.vars y := by
        intro y hy1 hy2
        rw [hσ', hσ₁]
        simp [hy1, hy2]
      have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := by
        intro b
        rw [hσ', hσ₁]
        simp
      refine ⟨σ', 34, hrun,
        ⟨hc.of_eq (h'arrs oa) (h'arrs ta),
          by rw [h'vars _ (by decide) (by decide)]; exact hn,
          by rw [h'vars _ (by decide) (by decide)]; exact hm,
          by rw [h'vars _ (by decide) (by decide)]; exact hr,
          by rw [h'vars _ (by decide) (by decide)]; exact hp,
          by rw [h'u]; exact hu,
          by rw [h'j]; omega,
          by rw [h'u, h'j]; omega,
          D, ⟨by rw [h'arrs]; exact hD.dArr, by rw [h'arrs]; exact hD.mArr,
            hD.anchor, hD.bound, hD.sound⟩, hrel, ?_⟩,
        by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
        by rw [h'j, h'u]; omega⟩
      intro s q hsD hq1 hq2 hq3
      rw [h'j] at hq3
      rcases Nat.lt_or_ge q j with hqj | hqj
      · exact hpart s q hsD hq1 hq2 hqj
      · have hqeq : q = j := by omega
        subst hqeq
        have hsu : (s : ℕ) = u :=
          hc.owner_unique (by omega) (by omega) hq1 hq2 hlo hslot
        exfalso
        apply hfront
        rw [← hsu]
        exact hsD
  · -- at the row's end: move the owner on
    have hcondF : (Cond.lt (.var "gs.j")
        (.get oa (.add (.var "gs.u") (.lit 1)))).evalB B σ = some false := by
      rw [hcond]
      congr 1
      simpa using hslot
    set σ' := σ.setVar "gs.u" (u + 1) with hσ'
    have hrun : Run B (gsTurn oa ta ma da) σ σ' 11 := by
      have hass : Run B (.assign "gs.u" (.add (.var "gs.u") (.lit 1))) σ σ' 4 := by
        have hev := evalB_incr (B := B) (x := "gs.u") (σ := σ) (by omega)
        exact (Run.assign hev).mono (by simp)
      exact (Run.ite_false hcondF hass).mono (by simp)
    have h'u : σ'.vars "gs.u" = u + 1 := by rw [hσ']; simp
    have h'vars : ∀ y, y ≠ "gs.u" → σ'.vars y = σ.vars y := by
      intro y hy
      rw [hσ']
      simp [hy]
    have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := fun b => by rw [hσ']; simp
    refine ⟨σ', 11, hrun,
      ⟨hc.of_eq (h'arrs oa) (h'arrs ta),
        by rw [h'vars _ (by decide)]; exact hn,
        by rw [h'vars _ (by decide)]; exact hm,
        by rw [h'vars _ (by decide)]; exact hr,
        by rw [h'vars _ (by decide)]; exact hp,
        by rw [h'u]; omega,
        by rw [h'vars _ (by decide)]; exact hj,
        by rw [h'u, h'vars _ (by decide)]; omega,
        D, ⟨by rw [h'arrs]; exact hD.dArr, by rw [h'arrs]; exact hD.mArr,
          hD.anchor, hD.bound, hD.sound⟩, hrel, ?_⟩,
      by rw [h'vars _ (by decide)], by rw [h'u]; omega,
      by rw [h'u]; omega,
      by rw [h'u, h'vars _ (by decide)]; omega⟩
    intro s q hsD hq1 hq2 hq3
    rw [h'vars _ (by decide)] at hq3
    exact hpart s q hsD hq1 hq2 hq3

end Turn

include hadj hoff0 hNB hnsB hrB hda_oa hda_ta hda_ma hma_oa hma_ta in
/-- **One round**: from the between-rounds invariant below the radius,
one pass re-establishes it one level up. -/
theorem gsRound_spec {v₀ : Fin N} {Mset : Set (Fin N)} :
    Spec B
      (fun σ => RoundInv oa ta ma da ns r off tgt G v₀ Mset σ ∧
        σ.vars "gs.p" < r)
      (gsRound oa ta ma da)
      (fun σ σ' => RoundInv oa ta ma da ns r off tgt G v₀ Mset σ' ∧
        σ'.vars "gs.p" = σ.vars "gs.p" + 1)
      (38 * ns + 15 * N + 12) := by
  intro σ₀ hσ₀
  obtain ⟨⟨hc, hn, hm, hr, hpr', D, hD, hrel⟩, hplt⟩ := hσ₀
  set p := σ₀.vars "gs.p" with hp_def
  -- the two pointer resets
  set σa := σ₀.setVar "gs.u" 0 with hσa
  set σb := σa.setVar "gs.j" 0 with hσb
  have hra : Run B (.assign "gs.u" (.lit 0)) σ₀ σa 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hrb : Run B (.assign "gs.j" (.lit 0)) σa σb 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hbvars : ∀ y, y ≠ "gs.u" → y ≠ "gs.j" → σb.vars y = σ₀.vars y := by
    intro y hy1 hy2
    rw [hσb, hσa]
    simp [hy1, hy2]
  have hbarrs : ∀ b, σb.arrs b = σ₀.arrs b := by
    intro b
    rw [hσb, hσa]
    simp
  -- the pass
  have hpass := Csr.ownerScan_spec (B := B) (38 * ns + 15 * N + 4) N ns 34 11
    "gs.j" "gs.m" "gs.u" (gsTurn oa ta ma da)
    (P := fun σ => σ = σb)
    (I := PassInv oa ta ma da ns r off tgt G v₀ Mset p)
    hnsB
    (fun σ hI => ⟨hI.2.2.1, hI.2.2.2.2.2.2.1, hI.2.2.2.2.2.1⟩)
    (gsTurn_step hadj hNB hnsB hrB hda_oa hda_ta hda_ma hma_oa hma_ta
      (by omega))
    (fun σ hσ => by
      subst hσ
      refine ⟨hc.of_eq (hbarrs oa) (hbarrs ta),
        by rw [hbvars _ (by decide) (by decide)]; exact hn,
        by rw [hbvars _ (by decide) (by decide)]; exact hm,
        by rw [hbvars _ (by decide) (by decide)]; exact hr,
        by rw [hbvars _ (by decide) (by decide)],
        by rw [hσb, hσa]; simp,
        by rw [hσb]; simp,
        by rw [hσb, hσa]; simp [hoff0],
        D, ⟨by rw [hbarrs]; exact hD.dArr, by rw [hbarrs]; exact hD.mArr,
          hD.anchor, hD.bound, hD.sound⟩, hrel, ?_⟩
      intro s q _ _ _ hq3
      rw [hσb] at hq3
      simp at hq3)
    (fun σ hσ => by
      subst hσ
      have h1 : (34 + 4) * (ns - σb.vars "gs.j") ≤ 38 * ns :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : (11 + 4) * (N - σb.vars "gs.u") ≤ 15 * N :=
        Nat.mul_le_mul_left _ (by omega)
      omega)
  obtain ⟨σc, hrc, hIcj⟩ := hpass.run rfl
  obtain ⟨hIc, hjc⟩ := hIcj
  obtain ⟨hcc, hnc, hmc, hrcr, hpc, huc, hjc', hloc, Dc, hDc, hrelc, hpartc⟩ := hIc
  -- the pass leaves the level relaxed
  have hrelc' : Relaxed G Dc (p + 1) := by
    intro s w hs hA
    rcases Nat.lt_or_ge (Dc (s : ℕ)) p with h | h
    · exact hrelc s w h hA
    · have hsp : Dc (s : ℕ) = p := by omega
      have hmem : (w : ℕ) ∈ Csr.row off tgt s := by
        refine (hadj s (w : ℕ)).mpr ⟨w.2, ?_⟩
        simpa using hA
      obtain ⟨q, hq1, hq2, hq3⟩ := mem_row_iff.mp hmem
      have hqns : q < ns := lt_of_lt_of_le hq2 (hcc.le_ns (by omega))
      have hres := hpartc s q hsp hq1 hq2 (by omega)
      rw [hq3] at hres
      omega
  -- advance the round counter
  set σd := σc.setVar "gs.p" (p + 1) with hσd
  have hrd : Run B (.assign "gs.p" (.add (.var "gs.p") (.lit 1))) σc σd 4 := by
    have hev := evalB_incr (B := B) (x := "gs.p") (σ := σc) (by rw [hpc]; omega)
    have h : Run B (.assign "gs.p" (.add (.var "gs.p") (.lit 1))) σc
        (σc.setVar "gs.p" (σc.vars "gs.p" + 1)) 4 :=
      (Run.assign hev).mono (by simp)
    rw [hpc] at h
    rwa [hσd]
  refine ⟨σd, ?_, ⟨?_, ?_, ?_, ?_, ?_, Dc, ?_, ?_⟩, ?_⟩
  · -- the assembled run at the announced cost
    have h := hra.seq (hrb.seq (hrc.seq hrd))
    exact h.mono (by omega)
  · exact hcc.setVar _ _
  · rw [hσd]; simpa using hnc
  · rw [hσd]; simpa using hmc
  · rw [hσd]; simpa using hrcr
  · rw [hσd]; simp; omega
  · exact ⟨by rw [hσd]; simpa using hDc.dArr, by rw [hσd]; simpa using hDc.mArr,
      hDc.anchor, hDc.bound, hDc.sound⟩
  · rw [hσd]
    simpa using hrelc'
  · rw [hσd]
    simp [← hp_def]

include hadj hoff0 hNB hnsB hrB hda_oa hda_ta hda_ma hma_oa hma_ta in
open Classical in
/-- **The marking call, discharged**: from the CSR, the input cells,
the pick in `"gs.v"` and the current mark set, `markCom` unions the
pick's `r`-ball into the marks, at cost `markK`. Everything else it
leaves alone (`Spec.frame` off `wvars_markCom`/`warrs_markCom`). -/
theorem markCom_spec (v₀ : Fin N) (Mset : Set (Fin N)) :
    Spec B
      (fun σ => Csr oa ta N ns N off tgt σ ∧
        σ.vars "gs.n" = N ∧ σ.vars "gs.m" = ns ∧ σ.vars "gs.r" = r ∧
        σ.vars "gs.v" = (v₀ : ℕ) ∧
        (σ.arrs da).length = N ∧ FinBits ma Mset σ)
      (markCom oa ta ma da)
      (fun _ σ' => Csr oa ta N ns N off tgt σ' ∧
        (σ'.arrs da).length = N ∧
        FinBits ma (Mset ∪ {w | WithinDist G r v₀ w}) σ')
      (markK N ns r) := by
  intro σ hσ
  obtain ⟨hc, hn, hm, hr, hv, hdl, hFB⟩ := hσ
  have hv₀N : (v₀ : ℕ) < N := v₀.2
  -- 1. the reset
  obtain ⟨σ₁, hr1, hpost1⟩ := ((gsReset_spec B N r da hNB hrB).frame).run ⟨hdl, hn, hr⟩
  obtain ⟨hd1, hfv1, hfa1, -, -⟩ := hpost1
  have h1vars : ∀ y, y ≠ "gs.i" → σ₁.vars y = σ.vars y := fun y hy =>
    hfv1 y (by show y ∉ (gsReset da).wvars; show y ∉ ["gs.i", "gs.i"]; simp [hy])
  have h1arrs : ∀ b, b ≠ da → σ₁.arrs b = σ.arrs b := fun b hb =>
    hfa1 b (by show b ∉ (gsReset da).warrs; show b ∉ [da]; simp [hb])
  -- 2. the seed
  have h1v : σ₁.vars "gs.v" = (v₀ : ℕ) := by rw [h1vars _ (by decide)]; exact hv
  have hst1 : Run B (.store da (.var "gs.v") (.lit 0)) σ₁
      (σ₁.setArr da (v₀ : ℕ) 0) 3 := by
    have hvev : (Expr.var "gs.v").evalB B σ₁ = some ((v₀ : ℕ)) := by
      rw [← h1v]
      exact evalB_var (by rw [h1v]; omega)
    refine (Run.store hvev (evalB_lit (by omega)) ?_).mono (by simp)
    rw [hd1, length_arrOf]
    exact hv₀N
  set σ₂ := σ₁.setArr da (v₀ : ℕ) 0 with hσ₂
  have hst2 : Run B (.store ma (.var "gs.v") (.lit 1)) σ₂
      (σ₂.setArr ma (v₀ : ℕ) 1) 3 := by
    have h2v : σ₂.vars "gs.v" = (v₀ : ℕ) := by rw [hσ₂]; simpa using h1v
    have hvev : (Expr.var "gs.v").evalB B σ₂ = some ((v₀ : ℕ)) := by
      rw [← h2v]
      exact evalB_var (by rw [h2v]; omega)
    refine (Run.store hvev (evalB_lit (by omega)) ?_).mono (by simp)
    rw [hσ₂]
    simp only [arrs_setArr]
    rw [if_neg (Ne.symm hda_ma), h1arrs ma (Ne.symm hda_ma), hFB.1]
    exact hv₀N
  set σ₃ := σ₂.setArr ma (v₀ : ℕ) 1 with hσ₃
  have h3vars : ∀ y, y ≠ "gs.i" → σ₃.vars y = σ.vars y := by
    intro y hy
    rw [hσ₃, hσ₂]
    simpa using h1vars y hy
  have h3da : σ₃.arrs da = (arrOf N fun _ => r + 1).set (v₀ : ℕ) 0 := by
    rw [hσ₃, hσ₂]
    simp [hda_ma, hd1]
  have h3ma : σ₃.arrs ma = (σ.arrs ma).set (v₀ : ℕ) 1 := by
    rw [hσ₃, hσ₂]
    simp [Ne.symm hda_ma, h1arrs ma (Ne.symm hda_ma)]
  have h3other : ∀ b, b ≠ da → b ≠ ma → σ₃.arrs b = σ.arrs b := by
    intro b hb1 hb2
    rw [hσ₃, hσ₂]
    simp only [arrs_setArr]
    rw [if_neg hb2, if_neg hb1, h1arrs b hb1]
  -- 3. the rounds
  set D₁ : ℕ → ℕ := fun q => if q = (v₀ : ℕ) then 0 else r + 1 with hD₁
  have hrounds := Spec.forRangeZero (B := B) "gs.p" "gs.r"
    (RoundInv oa ta ma da ns r off tgt G v₀ Mset) r
    (38 * ns + 15 * N + 12) (by omega)
    (fun σ' hσ' => hσ'.2.2.2.2.1)
    (fun σ' hσ' => hσ'.2.2.2.1)
    (gsRound_spec hadj hoff0 hNB hnsB hrB hda_oa hda_ta hda_ma hma_oa hma_ta)
  have hpre3 : RoundInv oa ta ma da ns r off tgt G v₀ Mset
      (σ₃.setVar "gs.p" 0) := by
    refine ⟨(hc.of_eq (h3other oa (Ne.symm hda_oa) (Ne.symm hma_oa))
        (h3other ta (Ne.symm hda_ta) (Ne.symm hma_ta))).setVar _ _,
      by rw [vars_setVar, if_neg (show ¬("gs.n" = "gs.p") by decide),
        h3vars "gs.n" (by decide)]; exact hn,
      by rw [vars_setVar, if_neg (show ¬("gs.m" = "gs.p") by decide),
        h3vars "gs.m" (by decide)]; exact hm,
      by rw [vars_setVar, if_neg (show ¬("gs.r" = "gs.p") by decide),
        h3vars "gs.r" (by decide)]; exact hr,
      by simp,
      D₁, ⟨?_, ?_, by simp [hD₁], ?_, ?_⟩, ?_⟩
    · rw [arrs_setVar, h3da, set_arrOf]
    · rw [arrs_setVar, h3ma]
      have hσma : σ.arrs ma = arrOf N fun q => (σ.arrs ma).getD q 0 := by
        conv_lhs => rw [← arrOf_getD (σ.arrs ma)]
        rw [hFB.1]
      rw [hσma, set_arrOf]
      refine arrOf_congr fun q hqN => ?_
      show (if q = (v₀ : ℕ) then 1 else (σ.arrs ma).getD q 0)
          = (if (∃ hw : q < N, (⟨q, hw⟩ : Fin N) ∈ Mset) ∨ D₁ q ≤ r then 1 else 0)
      by_cases hq : q = (v₀ : ℕ)
      · rw [if_pos hq,
          if_pos (Or.inr (show D₁ q ≤ r by rw [hq]; simp [hD₁]))]
      · rw [if_neg hq]
        have hbit : (σ.arrs ma).getD q 0
            = if (⟨q, hqN⟩ : Fin N) ∈ Mset then 1 else 0 := by
          simpa using hFB.2 ⟨q, hqN⟩
        rw [hbit]
        have hD₁q : D₁ q = r + 1 := by simp [hD₁, hq]
        rw [hD₁q]
        refine if_congr ?_ rfl rfl
        constructor
        · intro hmem
          exact Or.inl ⟨hqN, hmem⟩
        · rintro (⟨hw, hmem⟩ | hle)
          · exact hmem
          · omega
    · intro q hqN
      simp only [hD₁]
      by_cases hq : q = (v₀ : ℕ) <;> simp [hq]
    · intro q hqN hle
      have hq : q = (v₀ : ℕ) := by
        by_contra hne
        have : D₁ q = r + 1 := by rw [hD₁]; simp [hne]
        omega
      subst hq
      have h0 : D₁ (v₀ : ℕ) = 0 := by rw [hD₁]; simp
      rw [h0]
      exact withinDist_of_eq G 0 (Fin.ext rfl)
    · intro s w hs hA
      rw [vars_setVar, if_pos rfl] at hs
      omega
  obtain ⟨σ₄, hr4, hI4, hp4⟩ := hrounds.run hpre3
  obtain ⟨hc4, hn4, hm4, hr4c, hpr4, D4, hD4, hrel4⟩ := hI4
  have hrelr : Relaxed G D4 r := by rw [← hp4]; exact hrel4
  -- assemble
  refine ⟨σ₄, ?_, hc4, by rw [hD4.dArr, length_arrOf], ?_, ?_⟩
  · have h := hr1.seq (hst1.seq (hst2.seq hr4))
    refine h.mono ?_
    simp only [markK]
    have heq : (38 * ns + 15 * N + 12 + 4) * r
        = (15 * N + 38 * ns + 16) * r := by ring
    omega
  · rw [hD4.mArr, length_arrOf]
  · intro v
    rw [hD4.mArr, getD_arrOf _ v.2]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro (⟨hw, hmem⟩ | hle)
      · exact Or.inl (by simpa using hmem)
      · refine Or.inr ?_
        have hsnd := hD4.sound (v : ℕ) v.2 hle
        have h' := withinDist_mono_radius hle hsnd
        simpa using h'
    · rintro (hmem | hwd)
      · exact Or.inl ⟨v.2, by simpa using hmem⟩
      · exact Or.inr (d_complete hD4.anchor hrelr r le_rfl v hwd)

end Mark

/-! ## §7 The guarded early-stop sweep -/

section Sweep

variable {B N ns r t : ℕ} {G : SimpleGraph (Fin N)} {X : Set (Fin N)}
  {oa ta pa ma da : String} {off tgt : ℕ → ℕ}

open Classical in
/-- The sweep loop's invariant. Either the scan is still running —
some pick list `acc` accounts for the count, the marks and the
*continuation identity* (finishing the abstract sweep from here yields
the total) — or the early stop has fired and the count already holds
the total. -/
def SweepInv (oa ta pa ma da : String) (ns r t : ℕ) (off tgt : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) (X : Set (Fin N)) (σ : Env) : Prop :=
  Csr oa ta N ns N off tgt σ ∧
    σ.vars "gs.n" = N ∧ σ.vars "gs.m" = ns ∧ σ.vars "gs.r" = r ∧
    σ.vars "gs.t" = t ∧
    FinBits pa X σ ∧ (σ.arrs da).length = N ∧ σ.vars "gs.v" ≤ N ∧
    ((∃ acc : List (Fin N),
        σ.vars "gs.s" = N ∧ σ.vars "gs.c" = acc.length ∧ acc.length < t ∧
        FinBits ma (marks G r acc) σ ∧
        Lax3Proofs.Impl.scatterAux G r X t acc
            ((List.finRange N).drop (σ.vars "gs.v"))
          = Lax3Proofs.Impl.scatterAux G r X t [] (List.finRange N))
      ∨ (σ.vars "gs.s" = 0 ∧
          σ.vars "gs.c" = Lax3Proofs.Impl.scatterAux G r X t [] (List.finRange N) ∧
          (σ.arrs ma).length = N))

/-- The sweep's potential: `30` per vertex left before the stop bound,
the marking charge plus `30` per pick left. -/
def sweepPot (N ns r t : ℕ) (σ : Env) : ℕ :=
  30 * (σ.vars "gs.s" - σ.vars "gs.v")
    + (markK N ns r + 30) * (t - σ.vars "gs.c")

variable
  (hadj : ∀ (v : Fin N) (w : ℕ),
    w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
  (hoff0 : off 0 = 0)
  (hNB : N < B) (hnsB : ns < B) (hrB : r + 2 < B) (htB : t < B)
  (hda_oa : da ≠ oa) (hda_ta : da ≠ ta) (hda_ma : da ≠ ma) (hda_pa : da ≠ pa)
  (hma_oa : ma ≠ oa) (hma_ta : ma ≠ ta) (hma_pa : ma ≠ pa)

include hadj hoff0 hNB hnsB hrB htB hda_oa hda_ta hda_ma hda_pa hma_oa hma_ta
  hma_pa in
open Classical in
/-- **One step of the sweep**, in `Run.while_potential`'s form. -/
theorem gsSweepBody_step :
    ∀ σ, SweepInv oa ta pa ma da ns r t off tgt G X σ →
      (Cond.lt (.var "gs.v") (.var "gs.s")).evalB B σ = some true →
      ∃ σ' K, Run B (gsSweepBody oa ta pa ma da) σ σ' K ∧
        SweepInv oa ta pa ma da ns r t off tgt G X σ' ∧
        1 + (Cond.lt (.var "gs.v") (.var "gs.s")).size + K
            + sweepPot N ns r t σ' ≤ sweepPot N ns r t σ := by
  rintro σ ⟨hc, hn, hm, hr, ht, hP, hdl, hvN, hrun⟩ hcond
  have hvs : σ.vars "gs.v" < σ.vars "gs.s" := lt_of_condLt_true hcond
  rcases hrun with ⟨acc, hs, hcnt, hlt, hM, hcont⟩ | ⟨hs, -, -⟩
  swap
  · exact absurd hvs (by omega)
  set v := σ.vars "gs.v" with hv_def
  have hvNlt : v < N := by omega
  set vf : Fin N := ⟨v, hvNlt⟩ with hvf
  -- the predicate bit
  have hPbit : (σ.arrs pa).getD v 0 = if vf ∈ X then 1 else 0 := by
    have := hP.2 vf
    simpa [hvf] using this
  have hPread : (Expr.get pa (.var "gs.v")).evalB B σ
      = some (if vf ∈ X then 1 else 0) := by
    refine evalB_get (evalB_var (by omega)) ?_ (by split <;> omega)
    rw [getElem?_eq_getD (by rw [hP.1]; omega), hPbit]
  have hPev : (Cond.eq (.get pa (.var "gs.v")) (.lit 1)).evalB B σ
      = some ((if vf ∈ X then 1 else 0) == 1) :=
    evalB_condEq hPread (evalB_lit (by omega))
  -- the continuation identity, stepped to this vertex
  rw [finRange_drop_eq hvNlt] at hcont
  by_cases hX : vf ∈ X
  · -- the predicate holds: test the marks
    have hPevT : (Cond.eq (.get pa (.var "gs.v")) (.lit 1)).evalB B σ
        = some true := by
      rw [hPev]
      congr 1
      simp [hX]
    have hMbit : (σ.arrs ma).getD v 0 = if vf ∈ marks G r acc then 1 else 0 := by
      have := hM.2 vf
      simpa [hvf] using this
    have hMread : (Expr.get ma (.var "gs.v")).evalB B σ
        = some (if vf ∈ marks G r acc then 1 else 0) := by
      refine evalB_get (evalB_var (by omega)) ?_ (by split <;> omega)
      rw [getElem?_eq_getD (by rw [hM.1]; omega), hMbit]
    have hMev : (Cond.lt (.get ma (.var "gs.v")) (.lit 1)).evalB B σ
        = some (decide ((if vf ∈ marks G r acc then 1 else 0) < 1)) :=
      evalB_condLt hMread (evalB_lit (by omega))
    by_cases hMk : vf ∈ marks G r acc
    · -- marked: skip
      have hMevF : (Cond.lt (.get ma (.var "gs.v")) (.lit 1)).evalB B σ
          = some false := by
        rw [hMev]
        congr 1
        simp [hMk]
      set σ' := σ.setVar "gs.v" (v + 1) with hσ'
      have hinc : Run B (.assign "gs.v" (.add (.var "gs.v") (.lit 1))) σ σ' 4 := by
        have hev := evalB_incr (B := B) (x := "gs.v") (σ := σ) (by omega)
        exact (Run.assign hev).mono (by simp)
      have hrun : Run B (gsSweepBody oa ta pa ma da) σ σ' 15 := by
        refine ((Run.ite_true hPevT (Run.ite_false hMevF Run.skip)).seq hinc).mono ?_
        simp
      have h'vars : ∀ y, y ≠ "gs.v" → σ'.vars y = σ.vars y := by
        intro y hy
        rw [hσ']
        simp [hy]
      have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := fun b => by rw [hσ']; simp
      have hstep : Lax3Proofs.Impl.scatterAux G r X t acc
          ((List.finRange N).drop (v + 1))
          = Lax3Proofs.Impl.scatterAux G r X t [] (List.finRange N) := by
        rw [← hcont, scatterAux_cons_neg]
        rintro ⟨-, hfar⟩
        obtain ⟨u, hu, hwd⟩ := hMk
        exact hfar u hu hwd
      refine ⟨σ', 15, hrun,
        ⟨hc.of_eq (h'arrs oa) (h'arrs ta),
          by rw [h'vars _ (by decide)]; exact hn,
          by rw [h'vars _ (by decide)]; exact hm,
          by rw [h'vars _ (by decide)]; exact hr,
          by rw [h'vars _ (by decide)]; exact ht,
          ⟨by rw [h'arrs]; exact hP.1, fun w => by rw [h'arrs]; exact hP.2 w⟩,
          by rw [h'arrs]; exact hdl,
          by rw [hσ']; simp; omega,
          Or.inl ⟨acc,
            by rw [h'vars _ (by decide)]; exact hs,
            by rw [h'vars _ (by decide)]; exact hcnt,
            hlt,
            ⟨by rw [h'arrs]; exact hM.1, fun w => by rw [h'arrs]; exact hM.2 w⟩,
            by rw [hσ']; simpa using hstep⟩⟩, ?_⟩
      have h's : σ'.vars "gs.s" = σ.vars "gs.s" := h'vars _ (by decide)
      have h'c : σ'.vars "gs.c" = σ.vars "gs.c" := h'vars _ (by decide)
      have h'v : σ'.vars "gs.v" = v + 1 := by rw [hσ']; simp
      simp only [sweepPot]
      rw [h's, h'c, h'v]
      simp only [size_condLt, size_var]
      omega
    · -- unmarked: pick
      have hMevT : (Cond.lt (.get ma (.var "gs.v")) (.lit 1)).evalB B σ
          = some true := by
        rw [hMev]
        congr 1
        simp [hMk]
      have hfar : ∀ u ∈ acc, ¬ WithinDist G r u vf := not_mem_marks_iff.mp hMk
      -- the counter bump
      have hcntB : σ.vars "gs.c" + 1 < B := by
        rw [hcnt]; omega
      set σ₁ := σ.setVar "gs.c" (acc.length + 1) with hσ₁
      have hbump : Run B (.assign "gs.c" (.add (.var "gs.c") (.lit 1))) σ σ₁ 4 := by
        have hev := evalB_incr (B := B) (x := "gs.c") (σ := σ) hcntB
        rw [hcnt] at hev
        have h : Run B (.assign "gs.c" (.add (.var "gs.c") (.lit 1))) σ
            (σ.setVar "gs.c" (acc.length + 1)) 4 :=
          (Run.assign hev).mono (by simp)
        rwa [hσ₁]
      have h1c : σ₁.vars "gs.c" = acc.length + 1 := by rw [hσ₁]; simp
      have h1t : σ₁.vars "gs.t" = t := by rw [hσ₁]; simpa using ht
      have hfinEv : (Cond.eq (.var "gs.c") (.var "gs.t")).evalB B σ₁
          = some ((acc.length + 1) == t) := by
        have h1 : (Expr.var "gs.c").evalB B σ₁ = some (acc.length + 1) := by
          rw [← h1c]
          exact evalB_var (by rw [h1c]; omega)
        have h2 : (Expr.var "gs.t").evalB B σ₁ = some t := by
          rw [← h1t]
          exact evalB_var (by rw [h1t]; omega)
        exact evalB_condEq h1 h2
      -- the abstract step at a pick
      have hpick := scatterAux_cons_pos (G := G) (r := r) (t := t) (X := X)
        acc vf ((List.finRange N).drop (v + 1)) ⟨hX, hfar⟩
      by_cases hFin : acc.length + 1 = t
      · -- the final pick: stop
        have hfinT : (Cond.eq (.var "gs.c") (.var "gs.t")).evalB B σ₁
            = some true := by
          rw [hfinEv]
          congr 1
          simp [hFin]
        set σ₂ := σ₁.setVar "gs.s" 0 with hσ₂
        have hstop : Run B (.assign "gs.s" (.lit 0)) σ₁ σ₂ 2 :=
          (Run.assign (evalB_lit (by omega))).mono (by simp)
        set σ' := σ₂.setVar "gs.v" (v + 1) with hσ'
        have hinc : Run B (.assign "gs.v" (.add (.var "gs.v") (.lit 1))) σ₂ σ' 4 := by
          have h2v : σ₂.vars "gs.v" = v := by rw [hσ₂, hσ₁]; simpa using hv_def.symm
          have hev := evalB_incr (B := B) (x := "gs.v") (σ := σ₂)
            (by rw [h2v]; omega)
          rw [h2v] at hev
          exact (Run.assign hev).mono (by simp)
        have hrun : Run B (gsSweepBody oa ta pa ma da) σ σ' 24 := by
          refine ((Run.ite_true hPevT (Run.ite_true hMevT
            (hbump.seq (Run.ite_true hfinT hstop)))).seq hinc).mono ?_
          simp
        have h'vars : ∀ y, y ≠ "gs.v" → y ≠ "gs.s" → y ≠ "gs.c" →
            σ'.vars y = σ.vars y := by
          intro y hy1 hy2 hy3
          rw [hσ', hσ₂, hσ₁]
          simp [hy1, hy2, hy3]
        have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := fun b => by
          rw [hσ', hσ₂, hσ₁]; simp
        have htotal : t = Lax3Proofs.Impl.scatterAux G r X t [] (List.finRange N) := by
          rw [← hcont, hpick, if_pos hFin]
        refine ⟨σ', 24, hrun,
          ⟨hc.of_eq (h'arrs oa) (h'arrs ta),
            by rw [h'vars _ (by decide) (by decide) (by decide)]; exact hn,
            by rw [h'vars _ (by decide) (by decide) (by decide)]; exact hm,
            by rw [h'vars _ (by decide) (by decide) (by decide)]; exact hr,
            by rw [h'vars _ (by decide) (by decide) (by decide)]; exact ht,
            ⟨by rw [h'arrs]; exact hP.1, fun w => by rw [h'arrs]; exact hP.2 w⟩,
            by rw [h'arrs]; exact hdl,
            by rw [hσ', hσ₂, hσ₁]; simp; omega,
            Or.inr ⟨by rw [hσ', hσ₂]; simp,
              ?_,
              by rw [h'arrs]; exact hM.1⟩⟩, ?_⟩
        · have h'c : σ'.vars "gs.c" = acc.length + 1 := by
            rw [hσ', hσ₂, hσ₁]; simp
          rw [h'c, hFin]
          exact htotal
        · have h's : σ'.vars "gs.s" = 0 := by rw [hσ', hσ₂]; simp
          have h'c : σ'.vars "gs.c" = acc.length + 1 := by
            rw [hσ', hσ₂, hσ₁]; simp
          have h'v : σ'.vars "gs.v" = v + 1 := by rw [hσ']; simp
          simp only [sweepPot]
          rw [h's, h'c, h'v, hcnt]
          simp only [size_condLt, size_var]
          have hle : (markK N ns r + 30) * (t - (acc.length + 1))
              ≤ (markK N ns r + 30) * (t - acc.length) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
      · -- a non-final pick: mark its ball
        have hfinF : (Cond.eq (.var "gs.c") (.var "gs.t")).evalB B σ₁
            = some false := by
          rw [hfinEv]
          congr 1
          simp [hFin]
        have h1vars : ∀ y, y ≠ "gs.c" → σ₁.vars y = σ.vars y := by
          intro y hy
          rw [hσ₁]
          simp [hy]
        have h1arrs : ∀ b, σ₁.arrs b = σ.arrs b := fun b => by rw [hσ₁]; simp
        -- the marking call
        obtain ⟨σ₂, hmrun, hmpost⟩ :=
          ((markCom_spec hadj hoff0 hNB hnsB hrB hda_oa hda_ta hda_ma hma_oa
            hma_ta vf (marks G r acc)).frame).run
            (σ := σ₁)
            ⟨(hc.of_eq (h1arrs oa) (h1arrs ta)),
              by rw [h1vars _ (by decide)]; exact hn,
              by rw [h1vars _ (by decide)]; exact hm,
              by rw [h1vars _ (by decide)]; exact hr,
              by rw [h1vars _ (by decide)],
              by rw [h1arrs]; exact hdl,
              ⟨by rw [h1arrs]; exact hM.1, fun w => by rw [h1arrs]; exact hM.2 w⟩⟩
        obtain ⟨⟨hc2, hdl2, hM2⟩, hfv2, hfa2, -, -⟩ := hmpost
        have h2vars : ∀ y, y ∈ (["gs.c", "gs.v", "gs.s", "gs.t", "gs.n", "gs.m",
            "gs.r"] : List String) → σ₂.vars y = σ₁.vars y := by
          intro y hy
          refine hfv2 y ?_
          rw [wvars_markCom]
          fin_cases hy <;> decide
        have h2pa : σ₂.arrs pa = σ₁.arrs pa := by
          refine hfa2 pa ?_
          rw [warrs_markCom]
          simp [Ne.symm hda_pa, Ne.symm hma_pa]
        set σ' := σ₂.setVar "gs.v" (v + 1) with hσ'
        have hinc : Run B (.assign "gs.v" (.add (.var "gs.v") (.lit 1))) σ₂ σ' 4 := by
          have h2v : σ₂.vars "gs.v" = v := by
            rw [h2vars "gs.v" (by simp), h1vars _ (by decide)]
          have hev := evalB_incr (B := B) (x := "gs.v") (σ := σ₂)
            (by rw [h2v]; omega)
          rw [h2v] at hev
          exact (Run.assign hev).mono (by simp)
        have hrun : Run B (gsSweepBody oa ta pa ma da) σ σ'
            (22 + markK N ns r) := by
          refine ((Run.ite_true hPevT (Run.ite_true hMevT
            (hbump.seq (Run.ite_false hfinF hmrun)))).seq hinc).mono ?_
          simp only [size_condEq, size_condLt, size_get, size_var, size_lit]
          omega
        have h'cells : ∀ y, y ∈ (["gs.s", "gs.t", "gs.n", "gs.m", "gs.r"] :
            List String) → σ'.vars y = σ.vars y := by
          intro y hy
          have hyv : y ≠ "gs.v" := by fin_cases hy <;> decide
          have hyc : y ≠ "gs.c" := by fin_cases hy <;> decide
          rw [hσ', vars_setVar, if_neg hyv, h2vars y (by fin_cases hy <;> simp),
            h1vars y hyc]
        have h'pa : σ'.arrs pa = σ.arrs pa := by
          rw [hσ', arrs_setVar, h2pa, h1arrs]
        have hstep : Lax3Proofs.Impl.scatterAux G r X t (acc ++ [vf])
            ((List.finRange N).drop (v + 1))
            = Lax3Proofs.Impl.scatterAux G r X t [] (List.finRange N) := by
          rw [← hcont, hpick, if_neg hFin]
        refine ⟨σ', 22 + markK N ns r, hrun,
          ⟨hc2.setVar _ _,
            h'cells "gs.n" (by simp) ▸ hn,
            h'cells "gs.m" (by simp) ▸ hm,
            h'cells "gs.r" (by simp) ▸ hr,
            h'cells "gs.t" (by simp) ▸ ht,
            ⟨by rw [h'pa]; exact hP.1, fun w => by rw [h'pa]; exact hP.2 w⟩,
            by rw [hσ', arrs_setVar]; exact hdl2,
            by rw [hσ']; simp; omega,
            Or.inl ⟨acc ++ [vf],
              h'cells "gs.s" (by simp) ▸ hs,
              by rw [hσ', vars_setVar, if_neg (by decide),
                h2vars "gs.c" (by simp), h1c]; simp,
              by simp; omega,
              ?_,
              by rw [hσ']; simpa using hstep⟩⟩, ?_⟩
        · -- the marks after the pick
          rw [marks_append]
          exact ⟨by rw [hσ', arrs_setVar]; exact hM2.1,
            fun w => by rw [hσ', arrs_setVar]; exact hM2.2 w⟩
        · have h's : σ'.vars "gs.s" = σ.vars "gs.s" := h'cells "gs.s" (by simp)
          have h'v : σ'.vars "gs.v" = v + 1 := by rw [hσ']; simp
          have h'c : σ'.vars "gs.c" = acc.length + 1 := by
            rw [hσ', vars_setVar, if_neg (by decide), h2vars "gs.c" (by simp), h1c]
          simp only [sweepPot]
          rw [h's, h'v, h'c, hcnt]
          simp only [size_condLt, size_var]
          have hta : acc.length + 1 ≤ t := by omega
          have hexp : (markK N ns r + 30) * (t - acc.length)
              = (markK N ns r + 30) * (t - (acc.length + 1))
                + (markK N ns r + 30) := by
            rw [← Nat.mul_succ]
            congr 1
            omega
          omega
  · -- the predicate fails: skip
    have hPevF : (Cond.eq (.get pa (.var "gs.v")) (.lit 1)).evalB B σ
        = some false := by
      rw [hPev]
      congr 1
      simp [hX]
    set σ' := σ.setVar "gs.v" (v + 1) with hσ'
    have hinc : Run B (.assign "gs.v" (.add (.var "gs.v") (.lit 1))) σ σ' 4 := by
      have hev := evalB_incr (B := B) (x := "gs.v") (σ := σ) (by omega)
      exact (Run.assign hev).mono (by simp)
    have hrun : Run B (gsSweepBody oa ta pa ma da) σ σ' 15 := by
      refine ((Run.ite_false hPevF Run.skip).seq hinc).mono ?_
      simp
    have h'vars : ∀ y, y ≠ "gs.v" → σ'.vars y = σ.vars y := by
      intro y hy
      rw [hσ']
      simp [hy]
    have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := fun b => by rw [hσ']; simp
    have hstep : Lax3Proofs.Impl.scatterAux G r X t acc
        ((List.finRange N).drop (v + 1))
        = Lax3Proofs.Impl.scatterAux G r X t [] (List.finRange N) := by
      rw [← hcont, scatterAux_cons_neg]
      rintro ⟨hX', -⟩
      exact hX hX'
    refine ⟨σ', 15, hrun,
      ⟨hc.of_eq (h'arrs oa) (h'arrs ta),
        by rw [h'vars _ (by decide)]; exact hn,
        by rw [h'vars _ (by decide)]; exact hm,
        by rw [h'vars _ (by decide)]; exact hr,
        by rw [h'vars _ (by decide)]; exact ht,
        ⟨by rw [h'arrs]; exact hP.1, fun w => by rw [h'arrs]; exact hP.2 w⟩,
        by rw [h'arrs]; exact hdl,
        by rw [hσ']; simp; omega,
        Or.inl ⟨acc,
          by rw [h'vars _ (by decide)]; exact hs,
          by rw [h'vars _ (by decide)]; exact hcnt,
          hlt,
          ⟨by rw [h'arrs]; exact hM.1, fun w => by rw [h'arrs]; exact hM.2 w⟩,
          by rw [hσ']; simpa using hstep⟩⟩, ?_⟩
    have h's : σ'.vars "gs.s" = σ.vars "gs.s" := h'vars _ (by decide)
    have h'c : σ'.vars "gs.c" = σ.vars "gs.c" := h'vars _ (by decide)
    have h'v : σ'.vars "gs.v" = v + 1 := by rw [hσ']; simp
    simp only [sweepPot]
    rw [h's, h'c, h'v]
    simp only [size_condLt, size_var]
    omega

include hadj hoff0 hNB hnsB hrB htB hda_oa hda_ta hda_ma hda_pa hma_oa hma_ta
  hma_pa in
open Classical in
/-- **The unguarded sweep, discharged** (`1 ≤ t`): the count cell ends
at the abstract sweep's total. -/
theorem gsSweep_spec (ht1 : 1 ≤ t) :
    Spec B
      (fun σ => Csr oa ta N ns N off tgt σ ∧
        σ.vars "gs.n" = N ∧ σ.vars "gs.m" = ns ∧ σ.vars "gs.r" = r ∧
        σ.vars "gs.t" = t ∧
        FinBits pa X σ ∧ (σ.arrs ma).length = N ∧
        (σ.arrs da).length = N)
      (gsSweep oa ta pa ma da)
      (fun _ σ' =>
        σ'.vars "gs.c" = Lax3Proofs.Impl.scatterAux G r X t [] (List.finRange N) ∧
        Csr oa ta N ns N off tgt σ' ∧ FinBits pa X σ' ∧
        (σ'.arrs ma).length = N ∧ (σ'.arrs da).length = N)
      (41 * N + (markK N ns r + 30) * t + 20) := by
  intro σz hσz
  obtain ⟨hcz, hnz, hmz, hrz, htz, hPz, hMz, hdlz⟩ := hσz
  -- the mark region's cleanup
  obtain ⟨σ₀, hrz0, hz0⟩ := ((gsZero_spec B N ma hNB (by omega)).frame).run
    ⟨hMz, hnz⟩
  obtain ⟨hzeroed, hfvz, hfaz, -, -⟩ := hz0
  have hzvars : ∀ y, y ≠ "gs.i" → σ₀.vars y = σz.vars y := fun y hy =>
    hfvz y (by show y ∉ (gsZero ma).wvars; show y ∉ ["gs.i", "gs.i"]; simp [hy])
  have hzarrs : ∀ b, b ≠ ma → σ₀.arrs b = σz.arrs b := fun b hb =>
    hfaz b (by show b ∉ (gsZero ma).warrs; show b ∉ [ma]; simp [hb])
  have hc : Csr oa ta N ns N off tgt σ₀ :=
    hcz.of_eq (hzarrs oa (Ne.symm hma_oa)) (hzarrs ta (Ne.symm hma_ta))
  have hn : σ₀.vars "gs.n" = N := by rw [hzvars _ (by decide)]; exact hnz
  have hm : σ₀.vars "gs.m" = ns := by rw [hzvars _ (by decide)]; exact hmz
  have hr : σ₀.vars "gs.r" = r := by rw [hzvars _ (by decide)]; exact hrz
  have ht : σ₀.vars "gs.t" = t := by rw [hzvars _ (by decide)]; exact htz
  have hP : FinBits pa X σ₀ :=
    ⟨by rw [hzarrs pa (Ne.symm hma_pa)]; exact hPz.1,
      fun w => by rw [hzarrs pa (Ne.symm hma_pa)]; exact hPz.2 w⟩
  have hM0 : FinBits ma (∅ : Set (Fin N)) σ₀ := by
    refine ⟨by rw [hzeroed, length_arrOf], fun w => ?_⟩
    rw [hzeroed, getD_arrOf _ w.2]
    simp
  have hdl : (σ₀.arrs da).length = N := by
    rw [hzarrs da hda_ma]; exact hdlz
  -- the three initializations
  set σa := σ₀.setVar "gs.c" 0 with hσa
  set σb := σa.setVar "gs.v" 0 with hσb
  set σi := σb.setVar "gs.s" N with hσi
  have hra : Run B (.assign "gs.c" (.lit 0)) σ₀ σa 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hrb : Run B (.assign "gs.v" (.lit 0)) σa σb 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hri : Run B (.assign "gs.s" (.var "gs.n")) σb σi 2 := by
    have hbn : σb.vars "gs.n" = N := by rw [hσb, hσa]; simpa using hn
    have hev : (Expr.var "gs.n").evalB B σb = some N := by
      rw [← hbn]
      exact evalB_var (by rw [hbn]; omega)
    have h : Run B (.assign "gs.s" (.var "gs.n")) σb (σb.setVar "gs.s" N) 2 :=
      (Run.assign hev).mono (by simp)
    rwa [hσi]
  have hivars : ∀ y, y ≠ "gs.c" → y ≠ "gs.v" → y ≠ "gs.s" →
      σi.vars y = σ₀.vars y := by
    intro y h1 h2 h3
    rw [hσi, hσb, hσa]
    simp [h1, h2, h3]
  have hiarrs : ∀ b, σi.arrs b = σ₀.arrs b := fun b => by
    rw [hσi, hσb, hσa]; simp
  -- the loop
  have hIi : SweepInv oa ta pa ma da ns r t off tgt G X σi := by
    refine ⟨hc.of_eq (hiarrs oa) (hiarrs ta),
      by rw [hivars _ (by decide) (by decide) (by decide)]; exact hn,
      by rw [hivars _ (by decide) (by decide) (by decide)]; exact hm,
      by rw [hivars _ (by decide) (by decide) (by decide)]; exact hr,
      by rw [hivars _ (by decide) (by decide) (by decide)]; exact ht,
      ⟨by rw [hiarrs]; exact hP.1, fun w => by rw [hiarrs]; exact hP.2 w⟩,
      by rw [hiarrs]; exact hdl,
      by rw [hσi, hσb]; simp,
      Or.inl ⟨[], by rw [hσi]; simp,
        by rw [hσi, hσb, hσa]; simp,
        by simpa using ht1,
        ?_,
        by rw [hσi, hσb]; simp⟩⟩
    rw [marks_nil]
    exact ⟨by rw [hiarrs]; exact hM0.1, fun w => by rw [hiarrs]; exact hM0.2 w⟩
  have hloop := Spec.while_potential
    (b := Cond.lt (.var "gs.v") (.var "gs.s"))
    (c := gsSweepBody oa ta pa ma da)
    (B := B)
    (P := fun σ => σ = σi)
    (K := 30 * N + (markK N ns r + 30) * t + 4)
    (SweepInv oa ta pa ma da ns r t off tgt G X)
    (sweepPot N ns r t)
    (fun σ hI => by
      obtain ⟨-, -, -, -, -, -, -, hvN, hrun⟩ := hI
      have hsB : σ.vars "gs.s" < B := by
        rcases hrun with ⟨acc, hs, -⟩ | ⟨hs, -⟩ <;> rw [hs] <;> omega
      exact evalB_condLt_vars (by omega) hsB)
    (fun σ hI hcond =>
      gsSweepBody_step hadj hoff0 hNB hnsB hrB htB hda_oa hda_ta hda_ma hda_pa
        hma_oa hma_ta hma_pa σ hI hcond)
    (fun σ hσ => hσ ▸ hIi)
    (fun σ hσ => by
      subst hσ
      have his : σi.vars "gs.s" = N := by rw [hσi]; simp
      have hiv : σi.vars "gs.v" = 0 := by rw [hσi, hσb]; simp
      have hic : σi.vars "gs.c" = 0 := by
        rw [hσi, hσb, hσa]; simp
      simp only [sweepPot]
      rw [his, hiv, hic]
      simp only [size_condLt, size_var]
      have h1 : 30 * (N - 0) ≤ 30 * N := by omega
      have h2 : (markK N ns r + 30) * (t - 0) = (markK N ns r + 30) * t := by
        rw [Nat.sub_zero]
      omega)
  obtain ⟨σf, hrl, hIf, hcf⟩ := hloop.run rfl
  obtain ⟨hcF, hnF, hmF, hrF, htF, hPF, hdlF, hvNF, hrunF⟩ := hIf
  have hvsF := le_of_condLt_false hcf
  have hval : σf.vars "gs.c"
      = Lax3Proofs.Impl.scatterAux G r X t [] (List.finRange N) := by
    rcases hrunF with ⟨acc, hsF, hcntF, -, -, hcontF⟩ | ⟨-, hcF', -⟩
    · have hvF : σf.vars "gs.v" = N := by omega
      rw [hvF] at hcontF
      rw [List.drop_eq_nil_of_le (by simp)] at hcontF
      rw [hcntF, ← hcontF]
      simp only [Lax3Proofs.Impl.scatterAux]
    · exact hcF'
  have hmaF : (σf.arrs ma).length = N := by
    rcases hrunF with ⟨acc, -, -, -, hMF, -⟩ | ⟨-, -, hl⟩
    · exact hMF.1
    · exact hl
  refine ⟨σf, ?_, hval, hcF, hPF, hmaF, hdlF⟩
  have h := hrz0.seq (hra.seq (hrb.seq (hri.seq hrl)))
  refine h.mono ?_
  omega

end Sweep

/-! ## §8 The routine, guarded — the discharged `Spec` -/

section Scatter

variable {B N ns r t : ℕ} {G : SimpleGraph (Fin N)} {X : Set (Fin N)}
  {oa ta pa ma da : String} {off tgt : ℕ → ℕ}

variable
  (hadj : ∀ (v : Fin N) (w : ℕ),
    w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
  (hoff0 : off 0 = 0)
  (hNB : N < B) (hnsB : ns < B) (hrB : r + 2 < B) (htB : t < B)
  (hda_oa : da ≠ oa) (hda_ta : da ≠ ta) (hda_ma : da ≠ ma) (hda_pa : da ≠ pa)
  (hma_oa : ma ≠ oa) (hma_ta : ma ≠ ta) (hma_pa : ma ≠ pa)

include hadj hoff0 hNB hnsB hrB htB hda_oa hda_ta hda_ma hda_pa hma_oa hma_ta
  hma_pa in
open Classical in
/-- **`greedyScatter`, discharged end to end**: from the CSR, the four
input cells, the predicate bits, a clean mark region and a length-`N`
distance scratch, `scatterCom` leaves **exactly
`Impl.greedyScatter G r X t`** in the count cell, within `scatterK`.
Everything not named in the postcondition is frame
(`Spec.frame`: the command writes only `gsScalars` cells and the
`ma`/`da` regions, reads no tape, writes no tape). -/
theorem scatterCom_spec :
    Spec B
      (fun σ => Csr oa ta N ns N off tgt σ ∧
        σ.vars "gs.n" = N ∧ σ.vars "gs.m" = ns ∧ σ.vars "gs.r" = r ∧
        σ.vars "gs.t" = t ∧
        FinBits pa X σ ∧ (σ.arrs ma).length = N ∧
        (σ.arrs da).length = N)
      (scatterCom oa ta pa ma da)
      (fun _ σ' =>
        σ'.vars "gs.c" = Lax3Proofs.Impl.greedyScatter G r X t ∧
        Csr oa ta N ns N off tgt σ' ∧ FinBits pa X σ' ∧
        (σ'.arrs ma).length = N ∧ (σ'.arrs da).length = N)
      (scatterK N ns r t) := by
  intro σ hσ
  obtain ⟨hc, hn, hm, hr, ht, hP, hM, hdl⟩ := hσ
  have hguard : (Cond.eq (.var "gs.t") (.lit 0)).evalB B σ = some (t == 0) := by
    have h1 : (Expr.var "gs.t").evalB B σ = some t := by
      rw [← ht]
      exact evalB_var (by rw [ht]; omega)
    exact evalB_condEq h1 (evalB_lit (by omega))
  by_cases ht0 : t = 0
  · -- the guard: no scan at all
    have hguardT : (Cond.eq (.var "gs.t") (.lit 0)).evalB B σ = some true := by
      rw [hguard]
      congr 1
      simp [ht0]
    set σ' := σ.setVar "gs.c" 0 with hσ'
    have hass : Run B (.assign "gs.c" (.lit 0)) σ σ' 2 :=
      (Run.assign (evalB_lit (by omega))).mono (by simp)
    refine ⟨σ', (Run.ite_true hguardT hass).mono
      (by simp only [scatterK, size_condEq, size_var, size_lit]; omega),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ']
      simp only [Lax3Proofs.Impl.greedyScatter]
      rw [if_pos ht0]
      simp
    · exact hc.setVar _ _
    · exact ⟨by rw [hσ']; simpa using hP.1,
        fun w => by rw [hσ']; simpa using hP.2 w⟩
    · rw [hσ']
      simpa using hM
    · rw [hσ']
      simpa using hdl
  · -- the live route: the sweep
    have hguardF : (Cond.eq (.var "gs.t") (.lit 0)).evalB B σ = some false := by
      rw [hguard]
      congr 1
      simp [ht0]
    obtain ⟨σ', hrun, hval, hc', hP', hma', hda'⟩ :=
      (gsSweep_spec hadj hoff0 hNB hnsB hrB htB hda_oa hda_ta hda_ma hda_pa
        hma_oa hma_ta hma_pa (by omega)).run ⟨hc, hn, hm, hr, ht, hP, hM, hdl⟩
    refine ⟨σ', (Run.ite_false hguardF hrun).mono
      (by simp only [scatterK, size_condEq, size_var, size_lit]; omega),
      ?_, hc', hP', hma', hda'⟩
    rw [hval]
    simp only [Lax3Proofs.Impl.greedyScatter]
    rw [if_neg ht0]

end Scatter

section Seam

variable {B N ns r t : ℕ} {G : SimpleGraph (Fin N)} {X : Set (Fin N)}
  {oa ta pa ma da : String}

open Classical in
/-- **The routine at the head file's seam**: the same discharge stated
against `GraphCsr` — the form a frame block holds its arena in. -/
theorem scatterCom_spec_graphCsr
    (hNB : N < B) (hnsB : ns < B) (hrB : r + 2 < B) (htB : t < B)
    (hda_oa : da ≠ oa) (hda_ta : da ≠ ta) (hda_ma : da ≠ ma) (hda_pa : da ≠ pa)
    (hma_oa : ma ≠ oa) (hma_ta : ma ≠ ta) (hma_pa : ma ≠ pa) :
    Spec B
      (fun σ => GraphCsr oa ta G ns σ ∧
        σ.vars "gs.n" = N ∧ σ.vars "gs.m" = ns ∧ σ.vars "gs.r" = r ∧
        σ.vars "gs.t" = t ∧
        FinBits pa X σ ∧ (σ.arrs ma).length = N ∧
        (σ.arrs da).length = N)
      (scatterCom oa ta pa ma da)
      (fun _ σ' =>
        σ'.vars "gs.c" = Lax3Proofs.Impl.greedyScatter G r X t ∧
        GraphCsr oa ta G ns σ' ∧ FinBits pa X σ' ∧
        (σ'.arrs ma).length = N ∧ (σ'.arrs da).length = N)
      (scatterK N ns r t) := by
  intro σ hσ
  obtain ⟨⟨off, tgt, hc, hoff0, hnd, hadj'⟩, hcells⟩ := hσ
  have hadj : ∀ (v : Fin N) (w : ℕ),
      w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩ := hadj'
  obtain ⟨σ', hrun, hval, hc', hP', hma', hda'⟩ :=
    (scatterCom_spec hadj hoff0 hNB hnsB hrB htB hda_oa hda_ta hda_ma hda_pa
      hma_oa hma_ta hma_pa).run ⟨hc, hcells⟩
  exact ⟨σ', hrun, hval, ⟨off, tgt, hc', hoff0, hnd, hadj'⟩, hP', hma', hda'⟩

end Seam

end Lax3Proofs.Prog
