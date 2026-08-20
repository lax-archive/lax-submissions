import Lax3Proofs.SolveSweepAdj

/-!
# F6c11b (part 2) — `CovSweepIn`, split at the structure's seam

`SolveCovStep` names `CovSweepIn`: the GKS peeling sweep per admissible
level arena — from the rank array, deliver `CoverStageSpec`'s exact
postcondition (`CtrArr` at `Driver.centre`, `ClusterCsr` at
`Driver.cluster`). Finding 3 there pins the route: a frontier-queue BFS
over a **deletable adjacency structure** at `Impl.sweepCharge`'s
account. This file splits `CovSweepIn` at the seam that structure
draws — the `DelAdjSt` region of `SolveSweepAdj` — into two named
residuals, and proves the verbatim residual from them
(`covSweepIn_of_build_peel`).

## The seam

* **`CovAdjBuildIn` — the build pass**: from `CovSweepIn`'s exact
  precondition, materialize the deletable adjacency region of the
  arena's graph at the empty deleted set, and invert the rank array
  into the order region `OrdArr` (the ascending peel reads ranks
  inverse-first: entry `i` is the vertex of rank `i`), preserving the
  arena, the rank array, the two output allocations and the peel's
  scratch. The arena's own CSR is the source; the pass is `O(N + ns)`
  (the mate pass is the standard counting trick). Its budget `Kbd` is
  the discharger's.

* **`CovPeelIn` — the peel run**: from the built region, run GKS's
  sweep — in ascending order (`OrdArr`), per centre one frontier-queue
  BFS at radius `2R` inside the current structure (`Lib.Queue` the
  frontier, the live prefixes of `DelAdjSt` the adjacency reads), emit
  the row and the first-hit `ctr` marks, then delete the centre
  (`AdjDeleteIn`'s account: `O(1)` per removed edge copy) — landing
  `CoverStageSpec`'s exact postcondition. The abstract identities it
  closes against are `SolveSweepAdj` §4: `cluster_eq_ball_peelSet`
  (the emitted ball IS the cluster), `centre_eq_of_hit_first` (the
  first-assignment `ctr` IS the centre), `peelSet_zero`/`peelSet_succ`
  (the deleted set walks the rank prefixes). Empty current-balls still
  produce their (empty) row: `ClusterCsr`'s offsets are anchored per
  centre, not per nonempty centre.

Both residuals stay **parametric in `ord`** (Finding 2: the headline
binds the routine existentially, so the repin to a machine-defined
routine — `SolveSweepOrder`'s `mdOrderingRoutine` — passes through them
unchanged).

## What this file proves

`covSweepIn_of_build_peel`: from the two residuals, the verbatim

    CovSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra
      (fun j σ => Sbd j σ ∧ Spl j σ)
      (fun j => .seq (bldC j) (plC j))
      (fun j A => Kbd j A + Kpl j A)

— the sweep's scratch descriptor the conjunction of the two passes',
its program their sequence, its budget their sum, all F7-compatible
shapes (the same composition pattern as the landed
`coverAllIn_of_order_sweep`).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The two named residuals -/

/-- **Named residual (1b-i): the build pass** — per admissible level
arena at the word bound of every admissible input, from `CovSweepIn`'s
exact precondition (the arena, the rank array, the two output
allocations, the two passes' scratch `Sbd`/`Spl`), materialize the
deletable adjacency region of `A.G` at the empty deleted set and the
order region (the rank array's inverse), preserving the arena, the
rank array, the allocations' lengths and the peel's scratch. -/
def CovAdjBuildIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od : ℕ → String) (Sbd Spl : ℕ → Env → Prop)
    (bldC : ℕ → Com)
    (Kbd : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
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
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Sbd j σ ∧ Spl j σ)
        (bldC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          RankArr (ra j) ((ord A.N A.G).order) σ' ∧
          OrdArr (od j) ((ord A.N A.G).order) σ' ∧
          DelAdjSt (ao j) (aj j) (dg j) (mt j) A.G ∅ σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Spl j σ')
        (Kbd j A)

/-- **Named residual (1b-ii): the peel run** — per admissible level
arena at the word bound of every admissible input, from the built
region, the order and rank regions, the two allocations and its own
scratch, run the ascending peel — per centre one frontier-queue BFS at
radius `2R` in the current structure, row emission, first-hit `ctr`
marks, then the centre's deletion — and leave `CoverStageSpec`'s exact
postcondition: the arena intact, `CtrArr` at `Driver.centre`,
`ClusterCsr` at `Driver.cluster`.

Its budget target is `Impl.sweepCharge`'s account (`ImplCover` §4):
the BFS at the live-prefix edge budget (`|X_v| · D`), the deletions at
`O(1)` per removed copy — never a full pass per centre. -/
def CovPeelIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od : ℕ → String) (Spl : ℕ → Env → Prop)
    (plC : ℕ → Com)
    (Kpl : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          RankArr (ra j) ((ord A.N A.G).order) σ ∧
          OrdArr (od j) ((ord A.N A.G).order) σ ∧
          DelAdjSt (ao j) (aj j) (dg j) (mt j) A.G ∅ σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Spl j σ)
        (plC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          CtrArr (ca j) (centre (Headline.headlineSetup C hC φ) A
            ((ord A.N A.G).order)) σ' ∧
          ClusterCsr (co j) (cm j) (cluster (Headline.headlineSetup C hC φ) A
            ((ord A.N A.G).order)) σ')
        (Kpl j A)

/-! ## §2 The glue: the verbatim residual from the two passes -/

open Classical in
/-- **Residual (1b) of the cover leaf, reduced to its two passes**:
`CovSweepIn` holds — verbatim — of the sequenced program
`bldC j ; plC j` at the summed budget, with the sweep's scratch
descriptor the conjunction of the passes', from the two named
residuals `CovAdjBuildIn` and `CovPeelIn`. The composition is
`Spec.seq`: the build lands in the peel's precondition, and the peel's
postcondition is the sweep's. -/
theorem covSweepIn_of_build_peel (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od : ℕ → String) (Sbd Spl : ℕ → Env → Prop)
    (bldC plC : ℕ → Com)
    (Kbd Kpl : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (hbld : CovAdjBuildIn C hC φ ord G c w q ℓp htabF hbf Adm ca co ra
      ao aj dg mt od Sbd Spl bldC Kbd)
    (hpl : CovPeelIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra
      ao aj dg mt od Spl plC Kpl) :
    CovSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra
      (fun j σ => Sbd j σ ∧ Spl j σ)
      (fun j => .seq (bldC j) (plC j))
      (fun j A => Kbd j A + Kpl j A) := by
  intro x hx j hj A hAdm hbot
  refine Spec.seq
    ((hbld x hx j hj A hAdm hbot).pre ?_)
    (hpl x hx j hj A hAdm hbot) ?_ ?_
  · -- the sweep precondition is the build's
    rintro σ ⟨hA, hra, hca, hco, hSbd, hSpl⟩
    exact ⟨hA, hra, hca, hco, hSbd, hSpl⟩
  · -- the build lands in the peel's precondition
    rintro σ σ' - ⟨hA', hra', hod', hadj', hca', hco', hSpl'⟩
    exact ⟨hA', hra', hod', hadj', hca', hco', hSpl'⟩
  · -- the peel's postcondition is the sweep's
    rintro σ σ' σ'' - - hq
    exact hq

end Lax3Proofs.Prog
