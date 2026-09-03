import Lax3Proofs.SolveBlocksScatter
import Lax3Proofs.ImplBfs

/-!
# F6d — the shared bounded-BFS command: the exact truncated distance table

`SolveBlocksScatter`'s `markCom` runs a depth-`r` BFS by rounds from a
pick, but its deliverable is the mark bits — the distances are scratch.
Three later stages need the distances themselves: the supports stage
reads the BFS tree off the table (`Impl.descend`/`Impl.bfsSupports`),
the profilesMS stage runs the same BFS on the virtual-source graph, and
the cover sweep takes a slot. This file is the shared routine they all
consume: **`bfsCom` leaves the exact truncated distance table of one
source in the distance region** — `bfsCom_spec`'s postcondition is
`Impl.BallTable G s d` at the region's contents, verbatim the seam
predicate every consumer composes against (`ImplBfs`: the tower's
`bfsAlg_computes_ball` spec in ND-MC vocabulary), together with the
sentinel bound `≤ d + 1` on every entry that routes the stored values
below `mcB`.

## Design

The program is `markCom` minus the mark array: reset the distance
region to the sentinel `d + 1` (`bfReset` — the region may be DIRTY on
entry; the routine cleans the scratch it uses, the caller never pays a
wipe), seed the source at `0`, then `d` rounds, each one
owner-advancing pass over the whole CSR slot array
(`Lib.Csr.ownerScan_spec`) relaxing every slot whose *owner* is on the
frontier (`D u = round`). The frontier of round `p` is fixed during
the round — every write is `p + 1` — which is what keeps the carried
invariant stable through a pass.

Correctness rides on the carried state `BSt` — source at `0`, entries
bounded by the sentinel, every discovered entry *sound*
(`D w ≤ d → WithinDist G (D w) s w`: the distance is achieved) — plus
the relaxation clause `Relaxed` (reused from the scatter file).
*Completeness* (`WithinDist G k s w → D w ≤ k` for `k ≤ d`) is
**derived** from anchor + `Relaxed` by `d_complete`, not carried.
Soundness and completeness together force the table exact at every
radius `k ≤ d` — `BallTable` is an iff at every `k ≤ d`, not mere
reachability at `k = d`, and that is what the readout discharges.

The three CSR arrays and the distance region are name parameters
(`oa`, `ta`, `da`), so one theorem serves every level's regions; the
scratch scalars are the fixed list `bfScalars` with fresh prefix
`"bf."`, so the command composes next to the `gs.`-routines without a
frame fight. `wvars_bfsCom`/`warrs_bfsCom` (only `da` among arrays) /
`noWrite_bfsCom`/`not_reads_bfsCom` are the frame data consumers apply
`Spec.frame` against.

## The budget

`bfsK N ns d = 13·N + (15·N + 38·ns + 16)·d + 15` — `markK`'s shape
minus the mark writes: the reset (`13·N`), the seed, and `d` rounds of
one owner-advancing pass each (`34` a slot, `11` a row — the slot
charge is kept at the scatter's constant, the dropped mark store is
slack). Envelope `bfsK_le : bfsK N ns d ≤ 69·(d+1)·(N+ns+1)` — one
carrier-plus-slots pass per round, §6.5's `W := ‖A‖` shape at a
schedule constant.

## What consumers read off it

The postcondition of `bfsCom_spec` (and `bfsCom_spec_graphCsr` at the
head file's `GraphCsr` seam): the CSR untouched, the region length-`N`
with every entry `≤ d + 1` (unreached entries hold the sentinel and
fail every `≤ k ≤ d` test), and
`BallTable G s d (fun v => (σ'.arrs da).getD v 0)`. Readers test
`D v ≤ d` for membership (`Impl.reached`), `descend` walks the
gradient, and every stored value is `≤ d + 1 < B` by the explicit
bound clause.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax67Proofs.Reasoning.Lib
open Lax62Proofs.Codegen (arrOf_getD getD_eq_getElem)
open Lax3.ColoredGraphs (WithinDist ball)
open Lax3Proofs.WalkDistance

/-! ## §1 The program -/

/-- The routine's scratch cells (fixed names; the arrays are
parameters): the source, the four inputs `N`/`ns`/`d`, the round
counter, the owner, the slot pointer, the slot value, the reset
index. -/
def bfScalars : List String :=
  ["bf.v", "bf.n", "bf.m", "bf.r", "bf.p", "bf.u", "bf.j", "bf.w", "bf.i"]

/-- Reset the distance region to the sentinel `d + 1`: the region may
be dirty on entry, the routine cleans the scratch it uses. -/
def bfReset (da : String) : Com :=
  .seq (.assign "bf.i" (.lit 0))
    (.while (.lt (.var "bf.i") (.var "bf.n"))
      (.seq (.store da (.var "bf.i") (.add (.var "bf.r") (.lit 1)))
        (.assign "bf.i" (.add (.var "bf.i") (.lit 1)))))

/-- One slot of a round's pass: read the target; if the slot's owner is
on the frontier and the target improves, relax it; advance the slot
pointer. -/
def bfRelaxStep (ta da : String) : Com :=
  .seq (Csr.slot ta "bf.j" "bf.w")
    (.seq
      (.ite (.eq (.get da (.var "bf.u")) (.var "bf.p"))
        (.ite (.lt (.add (.var "bf.p") (.lit 1)) (.get da (.var "bf.w")))
          (.store da (.var "bf.w") (.add (.var "bf.p") (.lit 1)))
          .skip)
        .skip)
      (.assign "bf.j" (.add (.var "bf.j") (.lit 1))))

/-- One turn of the owner-advancing pass: inside the owner's row, take
the slot; at its end, move the owner on (`Lib.Csr`'s `ownerStep`
shape). -/
def bfTurn (oa ta da : String) : Com :=
  .ite (.lt (.var "bf.j") (.get oa (.add (.var "bf.u") (.lit 1))))
    (bfRelaxStep ta da)
    (.assign "bf.u" (.add (.var "bf.u") (.lit 1)))

/-- One round: reset the two pointers, one full owner-advancing pass,
advance the round counter. -/
def bfRound (oa ta da : String) : Com :=
  .seq (.assign "bf.u" (.lit 0))
    (.seq (.assign "bf.j" (.lit 0))
      (.seq (Csr.scan "bf.j" "bf.m" (bfTurn oa ta da))
        (.assign "bf.p" (.add (.var "bf.p") (.lit 1)))))

/-- **The bounded BFS**: reset the region to the sentinel, seed the
source (distance `0`), run `d` rounds. No mark array — the deliverable
is the distance table itself; readers test `D v ≤ d`. -/
def bfsCom (oa ta da : String) : Com :=
  .seq (bfReset da)
    (.seq (.store da (.var "bf.v") (.lit 0))
      (.seq (.assign "bf.p" (.lit 0))
        (.while (.lt (.var "bf.p") (.var "bf.r")) (bfRound oa ta da))))

/-! The frame data, computed once — consumers apply
`(bfsCom_spec …).frame` and read the untouched state off these. -/

theorem wvars_bfsCom (oa ta da : String) :
    (bfsCom oa ta da).wvars =
      ["bf.i", "bf.i", "bf.p", "bf.u", "bf.j", "bf.w", "bf.j", "bf.u", "bf.p"] := rfl

/-- Every cell the routine writes is scratch. -/
theorem wvars_bfsCom_subset (oa ta da : String) :
    ∀ y ∈ (bfsCom oa ta da).wvars, y ∈ bfScalars := by
  rw [wvars_bfsCom]
  decide

theorem warrs_bfsCom (oa ta da : String) :
    (bfsCom oa ta da).warrs = [da, da, da] := rfl

theorem noWrite_bfsCom (oa ta da : String) : (bfsCom oa ta da).NoWrite := by
  simp [bfsCom, bfReset, bfRound, bfTurn, bfRelaxStep, Csr.scan, Csr.slot,
    Com.NoWrite]

theorem not_reads_bfsCom (oa ta da : String) : ¬ (bfsCom oa ta da).reads := by
  simp [bfsCom, bfReset, bfRound, bfTurn, bfRelaxStep, Csr.scan, Csr.slot,
    Com.reads]

/-! ## §2 The budget -/

/-- **The routine's budget**, `markK`'s shape minus the mark writes:
the reset, the seed, `d` rounds of one owner-advancing pass each. -/
def bfsK (N ns d : ℕ) : ℕ := 13 * N + (15 * N + 38 * ns + 16) * d + 15

/-- The envelope: linear in carrier plus slots, one pass per round. -/
theorem bfsK_le (N ns d : ℕ) : bfsK N ns d ≤ 69 * (d + 1) * (N + ns + 1) := by
  have h2 : 15 * N + 38 * ns + 16 ≤ 38 * (N + ns + 1) := by omega
  have h3 : (15 * N + 38 * ns + 16) * d ≤ 38 * (N + ns + 1) * d :=
    Nat.mul_le_mul_right d h2
  have he : 69 * (d + 1) * (N + ns + 1)
      = 38 * (N + ns + 1) * d + (31 * (N + ns + 1) * d + 69 * (N + ns + 1)) := by
    ring
  have h1 : 13 * N + 15 ≤ 69 * (N + ns + 1) := by omega
  simp only [bfsK]
  rw [he]
  omega

/-! ## §3 The reset -/

private theorem evalB_incr {B : ℕ} {x : String} {σ : Env}
    (hx : σ.vars x + 1 < B) :
    (Expr.add (.var x) (.lit 1)).evalB B σ = some (σ.vars x + 1) := by
  have h := evalB_bin (B := B) (op := .add) (e := .var x) (f := .lit 1) (σ := σ)
    (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hx)
  simpa using h

/-- The reset's specification: the distance region becomes the
constant sentinel array. -/
theorem bfReset_spec (B N d : ℕ) (da : String) (hNB : N < B) (hdB : d + 2 < B) :
    Spec B
      (fun σ => (σ.arrs da).length = N ∧ σ.vars "bf.n" = N ∧ σ.vars "bf.r" = d)
      (bfReset da)
      (fun _ σ' => σ'.arrs da = arrOf N fun _ => d + 1)
      (13 * N + 6) := by
  classical
  set I : Env → Prop := fun σ =>
    σ.vars "bf.n" = N ∧ σ.vars "bf.r" = d ∧ σ.vars "bf.i" ≤ N ∧
      ∃ f, σ.arrs da = arrOf N f ∧ ∀ p < σ.vars "bf.i", f p = d + 1 with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "bf.i" < N)
      (.seq (.store da (.var "bf.i") (.add (.var "bf.r") (.lit 1)))
        (.assign "bf.i" (.add (.var "bf.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "bf.i" = σ.vars "bf.i" + 1) 9 := by
    intro σ hσ
    obtain ⟨⟨hn, hr, hiN, f, hf, hpre⟩, hlt⟩ := hσ
    have hiB : σ.vars "bf.i" < B := by omega
    have hidx : σ.vars "bf.i" < (σ.arrs da).length := by
      rw [hf, length_arrOf]; omega
    have hval : (Expr.add (.var "bf.r") (.lit 1)).evalB B σ = some (d + 1) := by
      have h := evalB_bin (B := B) (op := .add) (e := .var "bf.r") (f := .lit 1)
        (σ := σ) (evalB_var (by omega)) (evalB_lit (by omega))
        (by rw [hr]; show d + 1 < B; omega)
      rw [hr] at h
      simpa using h
    have hstore : Run B (.store da (.var "bf.i") (.add (.var "bf.r") (.lit 1)))
        σ (σ.setArr da (σ.vars "bf.i") (d + 1)) 5 :=
      (Run.store (evalB_var hiB) hval hidx).mono (by simp)
    set σ₁ := σ.setArr da (σ.vars "bf.i") (d + 1) with hσ₁
    have hassign : Run B (.assign "bf.i" (.add (.var "bf.i") (.lit 1)))
        σ₁ (σ₁.setVar "bf.i" (σ.vars "bf.i" + 1)) 4 := by
      have hev : (Expr.add (.var "bf.i") (.lit 1)).evalB B σ₁
          = some (σ.vars "bf.i" + 1) := by
        have h := evalB_incr (B := B) (x := "bf.i") (σ := σ₁)
          (by rw [hσ₁, vars_setArr]; omega)
        rw [hσ₁] at h ⊢
        simpa using h
      exact (Run.assign hev).mono (by simp)
    refine ⟨_, (hstore.seq hassign).mono (by omega),
      ⟨by simp [hσ₁, hn], by simp [hσ₁, hr], by simp [hσ₁]; omega, ?_⟩,
      by simp [hσ₁]⟩
    refine ⟨fun p => if p = σ.vars "bf.i" then d + 1 else f p, ?_, ?_⟩
    · simp [hσ₁, hf, set_arrOf]
    · intro p hp
      simp [hσ₁] at hp
      show (if p = σ.vars "bf.i" then d + 1 else f p) = d + 1
      by_cases hpe : p = σ.vars "bf.i"
      · rw [if_pos hpe]
      · rw [if_neg hpe]
        exact hpre p (by omega)
  have hmain := Spec.forRangeZero (B := B) "bf.i" "bf.n" I N 9 hNB
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

/-! ## §4 The rounds -/

section Bfs

variable {B N ns d : ℕ} {G : SimpleGraph (Fin N)}
  {oa ta da : String} {off tgt : ℕ → ℕ}

/-- The carried BFS state of one call: the distance region reads `D`,
the source is at `0`, entries are bounded by the sentinel, every
discovered entry is sound — its distance is *achieved* by a walk, not
merely an upper bound. -/
structure BSt (da : String) (G : SimpleGraph (Fin N)) (d : ℕ)
    (v₀ : Fin N) (D : ℕ → ℕ) (σ : Env) : Prop where
  dArr : σ.arrs da = arrOf N D
  anchor : D (v₀ : ℕ) = 0
  bound : ∀ w, w < N → D w ≤ d + 1
  sound : ∀ w, ∀ hw : w < N, D w ≤ d → WithinDist G (D w) v₀ ⟨w, hw⟩

/-- The invariant of one round's pass at level `p`: the CSR, the
cells, the owner discipline, the carried BFS state, `Relaxed` below
`p`, and partial progress — every slot below the pointer whose owner
is on the frontier has been relaxed. -/
def BPassInv (oa ta da : String) (ns d : ℕ) (off tgt : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) (v₀ : Fin N) (p : ℕ) (σ : Env) : Prop :=
  Csr oa ta N ns N off tgt σ ∧
    σ.vars "bf.n" = N ∧ σ.vars "bf.m" = ns ∧ σ.vars "bf.r" = d ∧
    σ.vars "bf.p" = p ∧
    σ.vars "bf.u" ≤ N ∧ σ.vars "bf.j" ≤ ns ∧
    off (σ.vars "bf.u") ≤ σ.vars "bf.j" ∧
    ∃ D, BSt da G d v₀ D σ ∧ Relaxed G D p ∧
      ∀ (x : Fin N) (q : ℕ), D (x : ℕ) = p → off (x : ℕ) ≤ q →
        q < off ((x : ℕ) + 1) → q < σ.vars "bf.j" → D (tgt q) ≤ p + 1

/-- The invariant between rounds: `Relaxed` at the round counter. -/
def BRoundInv (oa ta da : String) (ns d : ℕ) (off tgt : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) (v₀ : Fin N) (σ : Env) : Prop :=
  Csr oa ta N ns N off tgt σ ∧
    σ.vars "bf.n" = N ∧ σ.vars "bf.m" = ns ∧ σ.vars "bf.r" = d ∧
    σ.vars "bf.p" ≤ d ∧
    ∃ D, BSt da G d v₀ D σ ∧ Relaxed G D (σ.vars "bf.p")

variable
  (hadj : ∀ (v : Fin N) (w : ℕ),
    w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
  (hoff0 : off 0 = 0)
  (hNB : N < B) (hnsB : ns < B) (hdB : d + 2 < B)
  (hda_oa : da ≠ oa) (hda_ta : da ≠ ta)

section Turn

variable {v₀ : Fin N} {p : ℕ}

include hadj hNB hnsB hdB hda_oa hda_ta in
/-- **One turn of the pass**, in `ownerScan_spec`'s step form: it
either relaxes a slot or moves the owner on, keeps the invariant, and
costs `34` per slot moved, `11` per row moved. -/
theorem bfTurn_step (hpd : p < d) :
    ∀ σ, BPassInv oa ta da ns d off tgt G v₀ p σ → σ.vars "bf.j" < ns →
      ∃ σ' K', Run B (bfTurn oa ta da) σ σ' K' ∧
        BPassInv oa ta da ns d off tgt G v₀ p σ' ∧
        σ.vars "bf.j" ≤ σ'.vars "bf.j" ∧ σ.vars "bf.u" ≤ σ'.vars "bf.u" ∧
        (σ.vars "bf.j" < σ'.vars "bf.j" ∨ σ.vars "bf.u" < σ'.vars "bf.u") ∧
        K' ≤ 34 * (σ'.vars "bf.j" - σ.vars "bf.j")
          + 11 * (σ'.vars "bf.u" - σ.vars "bf.u") := by
  rintro σ ⟨hc, hn, hm, hr, hp, hu, hj, hlo, D, hD, hrel, hpart⟩ hjns
  have huN : σ.vars "bf.u" < N := hc.owner_lt hu hlo hjns
  set u := σ.vars "bf.u" with hu_def
  set j := σ.vars "bf.j" with hj_def
  -- the turn's test: `j < off (u+1)`
  have hoffval : (Expr.get oa (.add (.var "bf.u") (.lit 1))).evalB B σ
      = some (off (u + 1)) := by
    refine evalB_get (k := u + 1) (evalB_incr (by omega)) ?_
      (hc.off_lt hnsB (by omega))
    rw [hc.offArr, getElem?_arrOf off (by omega)]
  have hcond := evalB_condLt (evalB_var (x := "bf.j") (σ := σ) (by omega)) hoffval
  by_cases hslot : j < off (u + 1)
  · -- inside the row: take the slot
    have hcondT : (Cond.lt (.var "bf.j")
        (.get oa (.add (.var "bf.u") (.lit 1)))).evalB B σ = some true := by
      rw [hcond]
      congr 1
      simpa using hslot
    set w := tgt j with hw_def
    have hwN : w < N := hc.target hjns
    -- slot read
    have hread : Run B (Csr.slot ta "bf.j" "bf.w") σ (σ.setVar "bf.w" w) 3 := by
      refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono
        (by simp)
      rw [hc.tgtArr, getElem?_arrOf tgt hjns]
    set σ₁ := σ.setVar "bf.w" w with hσ₁
    have h1u : σ₁.vars "bf.u" = u := by rw [hσ₁]; simp [hu_def]
    have h1p : σ₁.vars "bf.p" = p := by rw [hσ₁]; simp [← hp]
    have h1w : σ₁.vars "bf.w" = w := by rw [hσ₁]; simp
    have h1j : σ₁.vars "bf.j" = j := by rw [hσ₁]; simp [hj_def]
    have h1da : σ₁.arrs da = arrOf N D := by rw [hσ₁]; simpa using hD.dArr
    -- the frontier test
    have hfrontEv : (Cond.eq (.get da (.var "bf.u")) (.var "bf.p")).evalB B σ₁
        = some (D u == p) := by
      have hDuB : D u ≤ d + 1 := hD.bound u huN
      have hval : (Expr.get da (.var "bf.u")).evalB B σ₁ = some (D u) := by
        refine evalB_get (evalB_var (by rw [h1u]; omega)) ?_ (by omega)
        rw [h1da, h1u, getElem?_arrOf D huN]
      have hpev : (Expr.var "bf.p").evalB B σ₁ = some p := by
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
    · have hfrontT : (Cond.eq (.get da (.var "bf.u")) (.var "bf.p")).evalB B σ₁
          = some true := by
        rw [hfrontEv]
        congr 1
        simpa using hfront
      have hDwB : D w ≤ d + 1 := hD.bound w hwN
      have hrelEv : (Cond.lt (.add (.var "bf.p") (.lit 1))
          (.get da (.var "bf.w"))).evalB B σ₁ = some (decide (p + 1 < D w)) := by
        refine evalB_condLt ?_
          (evalB_get (evalB_var (by rw [h1w]; omega)) ?_ (by omega))
        · have h := evalB_incr (B := B) (x := "bf.p") (σ := σ₁) (by rw [h1p]; omega)
          rwa [h1p] at h
        · rw [h1da, h1w, getElem?_arrOf D hwN]
      by_cases himp : p + 1 < D w
      · -- relax: the store
        have hrelT : (Cond.lt (.add (.var "bf.p") (.lit 1))
            (.get da (.var "bf.w"))).evalB B σ₁ = some true := by
          rw [hrelEv]
          congr 1
          simpa using himp
        have hpev : (Expr.add (.var "bf.p") (.lit 1)).evalB B σ₁ = some (p + 1) := by
          have h := evalB_incr (B := B) (x := "bf.p") (σ := σ₁) (by rw [h1p]; omega)
          rwa [h1p] at h
        have hst1 : Run B (.store da (.var "bf.w") (.add (.var "bf.p") (.lit 1)))
            σ₁ (σ₁.setArr da w (p + 1)) 5 := by
          have hwev : (Expr.var "bf.w").evalB B σ₁ = some w := by
            rw [← h1w]
            exact evalB_var (by rw [h1w]; omega)
          refine (Run.store hwev hpev ?_).mono (by simp)
          rw [h1da, length_arrOf]
          exact hwN
        set σ₂ := σ₁.setArr da w (p + 1) with hσ₂
        have hinc : Run B (.assign "bf.j" (.add (.var "bf.j") (.lit 1)))
            σ₂ (σ₂.setVar "bf.j" (j + 1)) 4 := by
          have h2j : σ₂.vars "bf.j" = j := by rw [hσ₂]; simpa using h1j
          have hev := evalB_incr (B := B) (x := "bf.j") (σ := σ₂)
            (by rw [h2j]; omega)
          rw [h2j] at hev
          exact (Run.assign hev).mono (by simp)
        set σ' := σ₂.setVar "bf.j" (j + 1) with hσ'
        have hrun : Run B (bfTurn oa ta da) σ σ' 34 := by
          have hInner : Run B (.ite (.lt (.add (.var "bf.p") (.lit 1))
              (.get da (.var "bf.w")))
              (.store da (.var "bf.w") (.add (.var "bf.p") (.lit 1)))
              .skip) σ₁ σ₂ 15 :=
            (Run.ite_true hrelT hst1).mono (by simp)
          have hOuter : Run B (.ite (.eq (.get da (.var "bf.u")) (.var "bf.p"))
              (.ite (.lt (.add (.var "bf.p") (.lit 1)) (.get da (.var "bf.w")))
                (.store da (.var "bf.w") (.add (.var "bf.p") (.lit 1)))
                .skip)
              .skip) σ₁ σ₂ 20 :=
            (Run.ite_true hfrontT hInner).mono (by simp)
          have hRel : Run B (bfRelaxStep ta da) σ σ' 27 :=
            (hread.seq (hOuter.seq hinc)).mono (by simp)
          exact (Run.ite_true hcondT hRel).mono (by simp)
        -- the projections of the final environment
        have h'j : σ'.vars "bf.j" = j + 1 := by rw [hσ']; simp
        have h'u : σ'.vars "bf.u" = u := by
          rw [hσ', hσ₂, hσ₁]; simp [hu_def]
        have h'vars : ∀ y, y ≠ "bf.j" → y ≠ "bf.w" → σ'.vars y = σ.vars y := by
          intro y hy1 hy2
          rw [hσ', hσ₂, hσ₁]
          simp [hy1, hy2]
        have h'da : σ'.arrs da = (arrOf N D).set w (p + 1) := by
          rw [hσ', hσ₂, hσ₁]
          simp [hD.dArr]
        have h'other : ∀ b, b ≠ da → σ'.arrs b = σ.arrs b := by
          intro b hb
          rw [hσ', hσ₂, hσ₁]
          simp [hb]
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
          ⟨hc.of_eq (h'other oa (Ne.symm hda_oa)) (h'other ta (Ne.symm hda_ta)),
            by rw [h'vars _ (by decide) (by decide)]; exact hn,
            by rw [h'vars _ (by decide) (by decide)]; exact hm,
            by rw [h'vars _ (by decide) (by decide)]; exact hr,
            by rw [h'vars _ (by decide) (by decide)]; exact hp,
            by rw [h'u]; exact hu,
            by rw [h'j]; omega,
            by rw [h'u, h'j]; omega,
            D', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩,
          by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
          by rw [h'j, h'u]; omega⟩
        · -- dArr
          rw [h'da, set_arrOf, hD'_def]
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
          intro x q hsD hq1 hq2 hq3
          rw [h'j] at hq3
          have hsw : (x : ℕ) ≠ w := by
            intro hcon
            rw [hcon, hD'w] at hsD
            omega
          rw [hD'ne _ hsw] at hsD
          rcases Nat.lt_or_ge q j with hqj | hqj
          · exact le_trans (hD'le _) (hpart x q hsD hq1 hq2 hqj)
          · have hqeq : q = j := by omega
            subst hqeq
            have hsu : (x : ℕ) = u :=
              hc.owner_unique (by omega) (by omega) hq1 hq2 hlo hslot
            rw [← hw_def]
            rw [hD'w]
        -- no-relax and off-frontier branches share their environment
      · have hrelF : (Cond.lt (.add (.var "bf.p") (.lit 1))
            (.get da (.var "bf.w"))).evalB B σ₁ = some false := by
          rw [hrelEv]
          congr 1
          simpa using himp
        set σ' := σ₁.setVar "bf.j" (j + 1) with hσ'
        have hinc : Run B (.assign "bf.j" (.add (.var "bf.j") (.lit 1)))
            σ₁ σ' 4 := by
          have hev := evalB_incr (B := B) (x := "bf.j") (σ := σ₁)
            (by rw [h1j]; omega)
          rw [h1j] at hev
          exact (Run.assign hev).mono (by simp)
        have hrun : Run B (bfTurn oa ta da) σ σ' 34 := by
          refine (Run.ite_true hcondT (hread.seq
            ((Run.ite_true hfrontT (Run.ite_false hrelF Run.skip)).seq hinc))).mono ?_
          simp
        have h'j : σ'.vars "bf.j" = j + 1 := by rw [hσ']; simp
        have h'u : σ'.vars "bf.u" = u := by rw [hσ', hσ₁]; simp [hu_def]
        have h'vars : ∀ y, y ≠ "bf.j" → y ≠ "bf.w" → σ'.vars y = σ.vars y := by
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
            D, ⟨by rw [h'arrs]; exact hD.dArr, hD.anchor, hD.bound, hD.sound⟩,
            hrel, ?_⟩,
          by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
          by rw [h'j, h'u]; omega⟩
        intro x q hsD hq1 hq2 hq3
        rw [h'j] at hq3
        rcases Nat.lt_or_ge q j with hqj | hqj
        · exact hpart x q hsD hq1 hq2 hqj
        · have hqeq : q = j := by omega
          subst hqeq
          have hsu : (x : ℕ) = u :=
            hc.owner_unique (by omega) (by omega) hq1 hq2 hlo hslot
          rw [← hw_def]
          omega
    · -- the owner is off the frontier: skip the slot
      have hfrontF : (Cond.eq (.get da (.var "bf.u")) (.var "bf.p")).evalB B σ₁
          = some false := by
        rw [hfrontEv]
        congr 1
        simpa using hfront
      set σ' := σ₁.setVar "bf.j" (j + 1) with hσ'
      have hinc : Run B (.assign "bf.j" (.add (.var "bf.j") (.lit 1)))
          σ₁ σ' 4 := by
        have hev := evalB_incr (B := B) (x := "bf.j") (σ := σ₁)
          (by rw [h1j]; omega)
        rw [h1j] at hev
        exact (Run.assign hev).mono (by simp)
      have hrun : Run B (bfTurn oa ta da) σ σ' 34 := by
        have hOuter : Run B (.ite (.eq (.get da (.var "bf.u")) (.var "bf.p"))
            (.ite (.lt (.add (.var "bf.p") (.lit 1)) (.get da (.var "bf.w")))
              (.store da (.var "bf.w") (.add (.var "bf.p") (.lit 1)))
              .skip)
            .skip) σ₁ σ₁ 20 :=
          (Run.ite_false hfrontF Run.skip).mono (by simp)
        have hRel : Run B (bfRelaxStep ta da) σ σ' 27 :=
          (hread.seq (hOuter.seq hinc)).mono (by simp)
        exact (Run.ite_true hcondT hRel).mono (by simp)
      have h'j : σ'.vars "bf.j" = j + 1 := by rw [hσ']; simp
      have h'u : σ'.vars "bf.u" = u := by rw [hσ', hσ₁]; simp [hu_def]
      have h'vars : ∀ y, y ≠ "bf.j" → y ≠ "bf.w" → σ'.vars y = σ.vars y := by
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
          D, ⟨by rw [h'arrs]; exact hD.dArr, hD.anchor, hD.bound, hD.sound⟩,
          hrel, ?_⟩,
        by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
        by rw [h'j, h'u]; omega⟩
      intro x q hsD hq1 hq2 hq3
      rw [h'j] at hq3
      rcases Nat.lt_or_ge q j with hqj | hqj
      · exact hpart x q hsD hq1 hq2 hqj
      · have hqeq : q = j := by omega
        subst hqeq
        have hsu : (x : ℕ) = u :=
          hc.owner_unique (by omega) (by omega) hq1 hq2 hlo hslot
        exfalso
        apply hfront
        rw [← hsu]
        exact hsD
  · -- at the row's end: move the owner on
    have hcondF : (Cond.lt (.var "bf.j")
        (.get oa (.add (.var "bf.u") (.lit 1)))).evalB B σ = some false := by
      rw [hcond]
      congr 1
      simpa using hslot
    set σ' := σ.setVar "bf.u" (u + 1) with hσ'
    have hrun : Run B (bfTurn oa ta da) σ σ' 11 := by
      have hass : Run B (.assign "bf.u" (.add (.var "bf.u") (.lit 1))) σ σ' 4 := by
        have hev := evalB_incr (B := B) (x := "bf.u") (σ := σ) (by omega)
        exact (Run.assign hev).mono (by simp)
      exact (Run.ite_false hcondF hass).mono (by simp)
    have h'u : σ'.vars "bf.u" = u + 1 := by rw [hσ']; simp
    have h'vars : ∀ y, y ≠ "bf.u" → σ'.vars y = σ.vars y := by
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
        D, ⟨by rw [h'arrs]; exact hD.dArr, hD.anchor, hD.bound, hD.sound⟩,
        hrel, ?_⟩,
      by rw [h'vars _ (by decide)], by rw [h'u]; omega,
      by rw [h'u]; omega,
      by rw [h'u, h'vars _ (by decide)]; omega⟩
    intro x q hsD hq1 hq2 hq3
    rw [h'vars _ (by decide)] at hq3
    exact hpart x q hsD hq1 hq2 hq3

end Turn

include hadj hoff0 hNB hnsB hdB hda_oa hda_ta in
/-- **One round**: from the between-rounds invariant below the depth,
one pass re-establishes it one level up. -/
theorem bfRound_spec {v₀ : Fin N} :
    Spec B
      (fun σ => BRoundInv oa ta da ns d off tgt G v₀ σ ∧
        σ.vars "bf.p" < d)
      (bfRound oa ta da)
      (fun σ σ' => BRoundInv oa ta da ns d off tgt G v₀ σ' ∧
        σ'.vars "bf.p" = σ.vars "bf.p" + 1)
      (38 * ns + 15 * N + 12) := by
  intro σ₀ hσ₀
  obtain ⟨⟨hc, hn, hm, hr, hpr', D, hD, hrel⟩, hplt⟩ := hσ₀
  set p := σ₀.vars "bf.p" with hp_def
  -- the two pointer resets
  set σa := σ₀.setVar "bf.u" 0 with hσa
  set σb := σa.setVar "bf.j" 0 with hσb
  have hra : Run B (.assign "bf.u" (.lit 0)) σ₀ σa 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hrb : Run B (.assign "bf.j" (.lit 0)) σa σb 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hbvars : ∀ y, y ≠ "bf.u" → y ≠ "bf.j" → σb.vars y = σ₀.vars y := by
    intro y hy1 hy2
    rw [hσb, hσa]
    simp [hy1, hy2]
  have hbarrs : ∀ b, σb.arrs b = σ₀.arrs b := by
    intro b
    rw [hσb, hσa]
    simp
  -- the pass
  have hpass := Csr.ownerScan_spec (B := B) (38 * ns + 15 * N + 4) N ns 34 11
    "bf.j" "bf.m" "bf.u" (bfTurn oa ta da)
    (P := fun σ => σ = σb)
    (I := BPassInv oa ta da ns d off tgt G v₀ p)
    hnsB
    (fun σ hI => ⟨hI.2.2.1, hI.2.2.2.2.2.2.1, hI.2.2.2.2.2.1⟩)
    (bfTurn_step hadj hNB hnsB hdB hda_oa hda_ta (by omega))
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
        D, ⟨by rw [hbarrs]; exact hD.dArr, hD.anchor, hD.bound, hD.sound⟩,
        hrel, ?_⟩
      intro x q _ _ _ hq3
      rw [hσb] at hq3
      simp at hq3)
    (fun σ hσ => by
      subst hσ
      have h1 : (34 + 4) * (ns - σb.vars "bf.j") ≤ 38 * ns :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : (11 + 4) * (N - σb.vars "bf.u") ≤ 15 * N :=
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
  set σd := σc.setVar "bf.p" (p + 1) with hσd
  have hrd : Run B (.assign "bf.p" (.add (.var "bf.p") (.lit 1))) σc σd 4 := by
    have hev := evalB_incr (B := B) (x := "bf.p") (σ := σc) (by rw [hpc]; omega)
    have h : Run B (.assign "bf.p" (.add (.var "bf.p") (.lit 1))) σc
        (σc.setVar "bf.p" (σc.vars "bf.p" + 1)) 4 :=
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
  · exact ⟨by rw [hσd]; simpa using hDc.dArr, hDc.anchor, hDc.bound, hDc.sound⟩
  · rw [hσd]
    simpa using hrelc'
  · rw [hσd]
    simp [← hp_def]

/-! ## §5 The headline -/

include hadj hoff0 hNB hnsB hdB hda_oa hda_ta in
/-- **The bounded BFS, discharged**: from the CSR, the input cells and
a length-`N` distance region (dirty is fine — the command resets it),
`bfsCom` leaves **the exact truncated distance table of the source** in
the region: every entry `≤ d + 1`, and `BallTable` at the contents —
the iff at every radius `k ≤ d`, the seam the supports, profilesMS and
sweep stages compose against. Cost `bfsK N ns d`. Everything else is
frame (`Spec.frame` off `wvars_bfsCom`/`warrs_bfsCom`). -/
theorem bfsCom_spec (s : Fin N) :
    Spec B
      (fun σ => Csr oa ta N ns N off tgt σ ∧
        σ.vars "bf.n" = N ∧ σ.vars "bf.m" = ns ∧ σ.vars "bf.r" = d ∧
        σ.vars "bf.v" = (s : ℕ) ∧
        (σ.arrs da).length = N)
      (bfsCom oa ta da)
      (fun _ σ' => Csr oa ta N ns N off tgt σ' ∧
        (σ'.arrs da).length = N ∧
        (∀ v : Fin N, (σ'.arrs da).getD v 0 ≤ d + 1) ∧
        Lax3Proofs.Impl.BallTable G s d (fun v => (σ'.arrs da).getD v 0))
      (bfsK N ns d) := by
  intro σ hσ
  obtain ⟨hc, hn, hm, hr, hv, hdl⟩ := hσ
  have hsN : (s : ℕ) < N := s.2
  -- 1. the reset
  obtain ⟨σ₁, hr1, hpost1⟩ := ((bfReset_spec B N d da hNB hdB).frame).run ⟨hdl, hn, hr⟩
  obtain ⟨hd1, hfv1, hfa1, -, -⟩ := hpost1
  have h1vars : ∀ y, y ≠ "bf.i" → σ₁.vars y = σ.vars y := fun y hy =>
    hfv1 y (by show y ∉ (bfReset da).wvars; show y ∉ ["bf.i", "bf.i"]; simp [hy])
  have h1arrs : ∀ b, b ≠ da → σ₁.arrs b = σ.arrs b := fun b hb =>
    hfa1 b (by show b ∉ (bfReset da).warrs; show b ∉ [da]; simp [hb])
  -- 2. the seed
  have h1v : σ₁.vars "bf.v" = (s : ℕ) := by rw [h1vars _ (by decide)]; exact hv
  have hst1 : Run B (.store da (.var "bf.v") (.lit 0)) σ₁
      (σ₁.setArr da (s : ℕ) 0) 3 := by
    have hvev : (Expr.var "bf.v").evalB B σ₁ = some ((s : ℕ)) := by
      rw [← h1v]
      exact evalB_var (by rw [h1v]; omega)
    refine (Run.store hvev (evalB_lit (by omega)) ?_).mono (by simp)
    rw [hd1, length_arrOf]
    exact hsN
  set σ₂ := σ₁.setArr da (s : ℕ) 0 with hσ₂
  have h2vars : ∀ y, y ≠ "bf.i" → σ₂.vars y = σ.vars y := by
    intro y hy
    rw [hσ₂, vars_setArr]
    exact h1vars y hy
  have h2da : σ₂.arrs da = (arrOf N fun _ => d + 1).set (s : ℕ) 0 := by
    rw [hσ₂]
    simp [hd1]
  have h2other : ∀ b, b ≠ da → σ₂.arrs b = σ.arrs b := by
    intro b hb
    rw [hσ₂]
    simp only [arrs_setArr]
    rw [if_neg hb, h1arrs b hb]
  -- 3. the rounds
  set D₁ : ℕ → ℕ := fun q => if q = (s : ℕ) then 0 else d + 1 with hD₁
  have hrounds := Spec.forRangeZero (B := B) "bf.p" "bf.r"
    (BRoundInv oa ta da ns d off tgt G s) d
    (38 * ns + 15 * N + 12) (by omega)
    (fun σ' hσ' => hσ'.2.2.2.2.1)
    (fun σ' hσ' => hσ'.2.2.2.1)
    (bfRound_spec hadj hoff0 hNB hnsB hdB hda_oa hda_ta)
  have hpre2 : BRoundInv oa ta da ns d off tgt G s
      (σ₂.setVar "bf.p" 0) := by
    refine ⟨(hc.of_eq (h2other oa (Ne.symm hda_oa))
        (h2other ta (Ne.symm hda_ta))).setVar _ _,
      by rw [vars_setVar, if_neg (show ¬("bf.n" = "bf.p") by decide),
        h2vars "bf.n" (by decide)]; exact hn,
      by rw [vars_setVar, if_neg (show ¬("bf.m" = "bf.p") by decide),
        h2vars "bf.m" (by decide)]; exact hm,
      by rw [vars_setVar, if_neg (show ¬("bf.r" = "bf.p") by decide),
        h2vars "bf.r" (by decide)]; exact hr,
      by simp,
      D₁, ⟨?_, by simp [hD₁], ?_, ?_⟩, ?_⟩
    · rw [arrs_setVar, h2da, set_arrOf]
    · intro q hqN
      simp only [hD₁]
      by_cases hq : q = (s : ℕ) <;> simp [hq]
    · intro q hqN hle
      have hq : q = (s : ℕ) := by
        by_contra hne
        have : D₁ q = d + 1 := by rw [hD₁]; simp [hne]
        omega
      subst hq
      have h0 : D₁ (s : ℕ) = 0 := by rw [hD₁]; simp
      rw [h0]
      exact withinDist_of_eq G 0 (Fin.ext rfl)
    · intro x w hs hA
      rw [vars_setVar, if_pos rfl] at hs
      omega
  obtain ⟨σ₄, hr4, hI4, hp4⟩ := hrounds.run hpre2
  obtain ⟨hc4, hn4, hm4, hr4c, hpr4, D4, hD4, hrel4⟩ := hI4
  have hrelr : Relaxed G D4 d := by rw [← hp4]; exact hrel4
  -- assemble
  refine ⟨σ₄, ?_, hc4, by rw [hD4.dArr, length_arrOf], ?_, ?_⟩
  · have h := hr1.seq (hst1.seq hr4)
    refine h.mono ?_
    simp only [bfsK]
    have heq : (38 * ns + 15 * N + 12 + 4) * d
        = (15 * N + 38 * ns + 16) * d := by ring
    omega
  · -- every entry bounded by the sentinel
    intro v
    rw [hD4.dArr, getD_arrOf _ v.2]
    exact hD4.bound (v : ℕ) v.2
  · -- the exact truncated distance table
    intro v k hk
    show (σ₄.arrs da).getD (v : ℕ) 0 ≤ k ↔ v ∈ ball G k s
    rw [hD4.dArr, getD_arrOf _ v.2]
    constructor
    · intro hDk
      have hsnd := hD4.sound (v : ℕ) v.2 (le_trans hDk hk)
      have hmono := withinDist_mono_radius hDk hsnd
      exact mem_ball.mpr (by simpa using hmono)
    · intro hmem
      exact d_complete hD4.anchor hrelr k hk v (mem_ball.mp hmem)

end Bfs

section Seam

variable {B N ns d : ℕ} {G : SimpleGraph (Fin N)} {oa ta da : String}

/-- **The routine at the head file's seam**: the same discharge stated
against `GraphCsr` — the form a frame block holds its arena in. -/
theorem bfsCom_spec_graphCsr (s : Fin N)
    (hNB : N < B) (hnsB : ns < B) (hdB : d + 2 < B)
    (hda_oa : da ≠ oa) (hda_ta : da ≠ ta) :
    Spec B
      (fun σ => GraphCsr oa ta G ns σ ∧
        σ.vars "bf.n" = N ∧ σ.vars "bf.m" = ns ∧ σ.vars "bf.r" = d ∧
        σ.vars "bf.v" = (s : ℕ) ∧
        (σ.arrs da).length = N)
      (bfsCom oa ta da)
      (fun _ σ' => GraphCsr oa ta G ns σ' ∧
        (σ'.arrs da).length = N ∧
        (∀ v : Fin N, (σ'.arrs da).getD v 0 ≤ d + 1) ∧
        Lax3Proofs.Impl.BallTable G s d (fun v => (σ'.arrs da).getD v 0))
      (bfsK N ns d) := by
  intro σ hσ
  obtain ⟨⟨off, tgt, hc, hoff0, hnd, hadj'⟩, hcells⟩ := hσ
  obtain ⟨σ', hrun, hc', hlen, hbd, hbt⟩ :=
    (bfsCom_spec hadj' hoff0 hNB hnsB hdB hda_oa hda_ta s).run ⟨hc, hcells⟩
  exact ⟨σ', hrun, ⟨off, tgt, hc', hoff0, hnd, hadj'⟩, hlen, hbd, hbt⟩

end Seam

end Lax3Proofs.Prog
