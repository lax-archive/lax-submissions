import Lax3Proofs.SolveGlueStep

/-!
# F6c10b (residual 1) — `CoverAllIn`, split at its one real seam

`SolveGlueStep` §4 names `CoverAllIn`: the GKS peeling sweep per
admissible level arena, delivering `CtrArr` at `Driver.centre` and
`ClusterCsr` at `Driver.cluster`, both at `(ord A.N A.G).order`. This
file does **not** discharge it; it splits it — at the seam the
statement itself draws — into two named residuals and proves the
verbatim residual from them (`coverAllIn_of_order_sweep`). The split
is forced by three findings, recorded here because they shape any
future discharge.

## Finding 1 — the ordering must be computed inside `covC`

`CoverStageSpec`'s precondition offers the discharger only the arena,
the two output allocations and its own scratch descriptor `Scv`; and
the frame seam (`frameElse_of_cover_loop`'s `hscrCov`/`hscrLen`) makes
`Scv` derivable from a *length-only* level descriptor. No ordering
data can enter through the precondition, so the cover program owes an
**ordering pass** before the sweep: `covC j = ordC j ; swC j`, the
pass leaving the rank array of `(ord A.N A.G).order` (`RankArr`) in a
scratch region. That is the seam of the split.

## Finding 2 — `ord := timedGreedyRoutine R` is not machine-matchable

`timedGreedyRoutine`'s order is `elimPerm (greedyChain G R).toGraph`,
and `elimPerm` is built from `elimRank := Exists.choose …`
(`CoverRoutine.lean`): a **choice-picked** ranking among all valid
greedy eliminations. No concrete `Com` can be *proved* to output an
`Exists.choose`-picked permutation, so `CovOrderIn` — hence
`CoverAllIn` — is undischargeable at `ord := timedGreedyRoutine R`.
This is not a statement gap in `CoverAllIn` itself: the headline
(`Headline.lean`) binds the routine existentially (`∃ ord`), so F7 is
free to instantiate `ord` with a *machine-defined* routine — a
deterministic min-degree peel (deterministic tie-break) attains the
minimal bound `elimBound` (`LowDegreeVertices`' defining property
applied to each remaining set), so `AugChainData`'s two sInf-
minimality clauses are provable for it; that re-derivation is E12's
priced obligation, not this leaf's. Both residuals below are
parametric in `ord`, so they survive the repin unchanged.

## Finding 3 — the landed `bfsCom` cannot carry the sweep's budget

The route question for the peeled BFS (mask / restrict-then-BFS /
peel-monotonicity):

* **(c) is unavailable**: no peel-monotonicity identity exists —
  `fiber_eq_peeledBall` is *about* the peeled graph; full-graph
  distances genuinely differ on it.
* **(b) and any per-centre use of `bfsCom` bust the account**:
  `bfsK N ns d = 13N + (15N + 38ns + 16)d + 15` — every round is a
  full pass over the whole slot array, so one call costs
  `Θ((N + ns)·R)` and `N` centres cost `Θ(N·(N + ns))`, against the
  abstract target `sweepCharge ≤ 2·D²·N` (`ImplCover` §4, the
  `‖A‖^{1+2δ}` shape the driver's cost recurrence consumes). The same
  holds for a masked *variant* of `bfsCom`'s round structure: the
  full-array pass, not the missing mask, is what breaks the budget.
* **(a), strengthened, is the route**: a **frontier-queue BFS over a
  mutable adjacency structure with peeling** — GKS's own routine
  (tex:1459-1520). `sweepCharge`'s two summands *are* this machine's
  account: `|X_v|·D` prices the queue BFS at its edge budget, and
  `Σ_{w ∈ N_>(v)} d_<(w)` prices deleting `v` from its surviving
  neighbours' lists. `Lib.Queue` supplies the frontier; the new
  machinery a discharge owes is the deletable adjacency region
  (doubly-indexed CSR or mark-and-skip with *peeled-degree* charging)
  and its invariant against `deleteVerts` — the arena mutation
  `ImplCover`'s header already announces. `CovSweepIn` below is that
  obligation, stated at the seam.

## What this file proves

`coverAllIn_of_order_sweep`: from `CovOrderIn` (the ordering pass,
per admissible arena, leaving `RankArr` and preserving the arena, the
allocations and the sweep's scratch) and `CovSweepIn` (the sweep, from
the rank array, leaving `CoverStageSpec`'s exact postcondition), the
verbatim residual

    CoverAllIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm
      (fun j σ => Sov j σ ∧ Ssw j σ)
      (fun j => .seq (ordC j) (swC j))
      (fun j A => Kord j A + Ksw j A)

holds — `Scv` the conjunction of the two passes' scratch descriptors,
`covC` their sequence, `Kcov` their sum, all F7-compatible shapes.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The rank region -/

/-- **The rank region**: entry `v` holds the position of `v` in the
ordering — the one datum of `π` the sweep reads (the peel order; the
peel ranks *are* the order). Windowed convention, like every chain
region. -/
def RankArr (ra : String) {N : ℕ} (π : Equiv.Perm (Fin N)) (σ : Env) : Prop :=
  N ≤ (σ.arrs ra).length ∧
    ∀ v : Fin N, (σ.arrs ra).getD (v : ℕ) 0 = (π v : ℕ)

/-! ## §2 The two named residuals -/

/-- **Named residual (1a): the ordering pass** — per admissible level
arena at the word bound of every admissible input, from
`CoverStageSpec`'s exact precondition (the arena, the two output
allocations, the two passes' scratch `Sov`/`Ssw`), leave the rank
array of the routine's ordering in `ra j`, preserving the arena, the
allocations' lengths and the sweep's scratch.

Per Finding 2 (module docstring): dischargeable only for a
machine-defined `ord` — F7 instantiates the headline's `∃ ord`
accordingly; `timedGreedyRoutine`'s choice-picked `elimPerm` is not a
machine-matchable target. -/
def CovOrderIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (Sov Ssw : ℕ → Env → Prop)
    (ordC : ℕ → Com)
    (Kord : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Sov j σ ∧ Ssw j σ)
        (ordC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          RankArr (ra j) ((ord A.N A.G).order) σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Ssw j σ')
        (Kord j A)

/-- **Named residual (1b): the peeling sweep** — per admissible level
arena at the word bound of every admissible input, from the arena,
the rank array the ordering pass left, the two allocations and its
own scratch, leave `CoverStageSpec`'s exact postcondition: the arena
intact, `CtrArr` at `Driver.centre`, `ClusterCsr` at `Driver.cluster`,
both at the routine's ordering — the abstract sweep's contents,
through `Impl.sweepCluster_eq_cluster` / `Impl.sweepCtr_eq_centre`.

Per Finding 3 (module docstring): the route is GKS's own — a
frontier-queue BFS over a deletable adjacency structure, at
`Impl.sweepCharge`'s per-vertex account; per-centre `bfsCom` passes
(route (b), and any full-pass mask variant) cannot meet the
`2·D²·N` target. -/
def CovSweepIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm : ℕ → String) (ra : ℕ → String) (Ssw : ℕ → Env → Prop)
    (swC : ℕ → Com)
    (Ksw : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          RankArr (ra j) ((ord A.N A.G).order) σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Ssw j σ)
        (swC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          CtrArr (ca j) (centre (Headline.headlineSetup C hC φ) A
            ((ord A.N A.G).order)) σ' ∧
          ClusterCsr (co j) (cm j) (cluster (Headline.headlineSetup C hC φ) A
            ((ord A.N A.G).order)) σ')
        (Ksw j A)

/-! ## §3 The glue: the verbatim residual from the two passes -/

open Classical in
/-- **Residual 1 of the cover leaf, reduced to its two passes**:
`CoverAllIn` holds — verbatim — of the sequenced program
`ordC j ; swC j` at the summed budget, with the stage scratch
descriptor the conjunction of the passes', from the two named
residuals `CovOrderIn` and `CovSweepIn`. The composition is exactly
`CoverStageSpec`'s `Spec.seq`: the ordering pass's postcondition is
the sweep's precondition, and the sweep's postcondition is the
stage's. -/
theorem coverAllIn_of_order_sweep (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm : ℕ → String) (ra : ℕ → String) (Sov Ssw : ℕ → Env → Prop)
    (ordC swC : ℕ → Com)
    (Kord Ksw : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (hord : CovOrderIn C hC φ ord G c w q ℓp htabF hbf Adm ca co ra Sov Ssw
      ordC Kord)
    (hsw : CovSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra Ssw
      swC Ksw) :
    CoverAllIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm
      (fun j σ => Sov j σ ∧ Ssw j σ)
      (fun j => .seq (ordC j) (swC j))
      (fun j A => Kord j A + Ksw j A) := by
  intro x hx j hj A hAdm hbot
  refine Spec.seq
    ((hord x hx j hj A hAdm hbot).pre ?_)
    (hsw x hx j hj A hAdm hbot) ?_ ?_
  · -- the stage precondition (`Scv` one conjunct) is the pass's
    rintro σ ⟨hA, hca, hco, hSov, hSsw⟩
    exact ⟨hA, hca, hco, hSov, hSsw⟩
  · -- the ordering pass lands in the sweep's precondition
    rintro σ σ' - ⟨hA', hra, hca', hco', hSsw'⟩
    exact ⟨hA', hra, hca', hco', hSsw'⟩
  · -- the sweep's postcondition is the stage's
    rintro σ σ' σ'' - - hq
    exact hq

end Lax3Proofs.Prog
