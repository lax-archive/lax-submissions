import Lax3Proofs.SolveSweepBfsRun
import Lax3Proofs.SolveSweepGroup
import Lax3Proofs.SolveSweepBuild
import Lax3Proofs.ProgCoverChargeDeg
import Lax3Proofs.SolveChainWin

/-!
# F6c12 — closing `CovPeelIn`, and the cover sweep above it

Both halves of the peel landed in the same tree and nobody had put
them together.  This file is the composition, the budget arithmetic,
and the honest account of what the composition does **not** reach.

## The chain

    peelBfsIn_bfsTurnCom      PeelBfsIn   at (12·R+44, 39, 76)
      ↓ peelSweepIn_of_bfs
    PeelSweepIn               at (12·R+86, 93, 76)
      ↓ covPeelIn_of_sweep_group  (with peelGroupIn_grCom at (153, 61, 0))
    CovPeelIn                 at peelK (12·R+239) 154 76
      ↓ covSweepIn_of_build_peel  (with covAdjBuildIn_bldCom)
    CovSweepIn                at peelK (12·R+362) 154 192

Every arrow is a landed theorem; this file supplies only the two
plumbing lemmas the seam needed (§2, §3), the two scratch descriptors
(§1), and the arithmetic (§5, §7).

## The seam the composition had to cross

`peelSweepIn_of_bfs` fixes the sweep's post-descriptor to its own
pre-descriptor, and `peelGroupIn_grCom` fixes the grouping's
pre-descriptor to four *allocation* clauses about `cm`, `sb`, `cnt`,
`cur`.  Neither mentions the other, so `covPeelIn_of_sweep_group` —
which needs the two to be the *same* predicate — does not apply
directly.

The fix is not to weaken either: it is that the four clauses are
**length-only**, and `run_arrs_length_eq` says an IMP+ run never
changes an array's length.  `sweepClose_peelSweepIn_conj` (§2)
therefore conjoins any length-stable predicate onto both ends of a
`PeelSweepIn` for free — through `specArrsLength`, not through a new
program analysis — and `sweepClose_peelGroupIn_pre` (§3) is the
(contravariant) precondition monotonicity `PeelGroupIn` enjoys because
its `Sgr` occurs only in the precondition.  The peel's scratch
descriptor is then the honest conjunction of the two passes'
(§1, `sweepClosePeelSc`), and §8 exhibits a state satisfying it.

## The cost envelope

`peelK_le_coverCFSel_total` closes the summed budget against the cover
ledger vector of the same node at

    peelK (12·R+239) 154 76 ≤ (12·R + 469) · chargeTotal (coverCFSel …)

(§5) and, for the whole sweep,

    peelK (12·R+362) 154 192 ≤ (12·R + 708) · chargeTotal (coverCFSel …)

(§7).  Nothing is quadratic in `A.N`: the three figures multiply
`A.N`, `clusterMass` and `peelEdgeWork`, and the build pass's own
`58·ns` — the one term stated in the arena's degree sum rather than in
the peel's currency — is folded into `peelEdgeWork` by
`sweepClose_ns_le_peelEdgeWork` (§7), which is
`sum_induced_deg_le_two_sum_dlt` at `s = univ` together with
`self_mem_cluster`.  That step is the reason the build does not
reintroduce the `86·N²` shape an earlier peel had.

## What this file does not reach

`coverAllIn_of_order_sweep` wants `CovOrderIn` beside `CovSweepIn`,
and `covOrderIn_bucketPeel` supplies it only from the named residual
`CovAugAdjSelIn` (`SolveSweepBucketRound.lean:3249`) — the augmented
adjacency build behind the bucket ordering.  That residual is *not*
discharged anywhere in this tree, so the cover stage stops one
residual short of `CoverAllIn`.  See §9.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax12.ColoringNumbers
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.CoverRoutine

variable {L n₀ : ℕ}

/-! ## §1 The three scratch descriptors, all concrete

Nothing here is a parameter constrained only through implications:
each is a closed formula about array lengths and array contents, and
§8 exhibits one state satisfying all three at once. -/

/-- **The grouping's allocation clauses** — `peelGroupIn_grCom`'s own
`Sgr`, named.  The two counting sorts need a membership row and a
sorted-centre row as long as the log, and a counter and a cursor row
as long as the offsets. -/
def sweepCloseGrpSc (co cm cnt cur lm sb : ℕ → String) (j : ℕ) (σ : Env) : Prop :=
  (σ.arrs (lm j)).length ≤ (σ.arrs (cm j)).length ∧
    (σ.arrs (lm j)).length ≤ (σ.arrs (sb j)).length ∧
    (σ.arrs (co j)).length ≤ (σ.arrs (cnt j)).length ∧
    (σ.arrs (co j)).length ≤ (σ.arrs (cur j)).length

/-- **The peel's scratch descriptor**: the sweep's own two log
allocations and its clean visited flags (`peelSweepIn_of_bfs`'s
descriptor at `Ssc = BfsClean`), conjoined with the grouping's four
allocation clauses.  The conjunction is what lets the sweep hand the
grouping its precondition; §2 is why it costs nothing. -/
def sweepClosePeelSc (co cm cnt cur lo lm sb : ℕ → String) (n : ℕ)
    (j : ℕ) (σ : Env) : Prop :=
  (n + 1 ≤ (σ.arrs (lo j)).length ∧ n * n ≤ (σ.arrs (lm j)).length ∧
      BfsClean (co j) n σ) ∧ sweepCloseGrpSc co cm cnt cur lm sb j σ

/-- **The build pass's scratch descriptor** — `covAdjBuildIn_bldCom`'s
`hSbd` duty, stated as the descriptor itself so that the duty is
`id`: the five regions the build materializes must already be
allocated. -/
def sweepCloseBldSc (ao aj dg mt od : ℕ → String) (j : ℕ) (σ : Env) : Prop :=
  σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (ao j)).length ∧
    σ.vars (arenaNames j).nS ≤ (σ.arrs (aj j)).length ∧
    σ.vars (arenaNames j).nN ≤ (σ.arrs (dg j)).length ∧
    σ.vars (arenaNames j).nS ≤ (σ.arrs (mt j)).length ∧
    σ.vars (arenaNames j).nN ≤ (σ.arrs (od j)).length

/-- The grouping's clauses are length-only, hence stable under any
IMP+ run. -/
theorem sweepCloseGrpSc_of_len {co cm cnt cur lm sb : ℕ → String} {j : ℕ}
    {σ σ' : Env} (hlen : ∀ b : String, (σ'.arrs b).length = (σ.arrs b).length)
    (h : sweepCloseGrpSc co cm cnt cur lm sb j σ) :
    sweepCloseGrpSc co cm cnt cur lm sb j σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hlen, hlen]; exact h1, by rw [hlen, hlen]; exact h2,
    by rw [hlen, hlen]; exact h3, by rw [hlen, hlen]; exact h4⟩

/-! ## §2 Conjoining a length-stable invariant to the sweep

The sweep's `Spec` says nothing about the four grouping allocations,
and it does not have to: `specArrsLength` (`SolveChainWin`) hands
every `Spec` the fact that no array's length moved, because IMP+ has
no allocation.  So any predicate that only reads lengths rides
through the sweep untouched, and the composition never has to
re-derive a frame. -/

open Classical in
/-- **The sweep carries any length-stable invariant.**  From
`PeelSweepIn` at `(Spl, Sgr)` and a predicate `F` stable under array
length equality, `PeelSweepIn` at `(Spl ∧ F, Sgr ∧ F)` — same program,
same budget.  This is the seam between `peelSweepIn_of_bfs`'s
descriptor and `peelGroupIn_grCom`'s. -/
theorem sweepClose_peelSweepIn_conj (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od lo lm : ℕ → String) (Spl Sgr F : ℕ → Env → Prop)
    (swC : ℕ → Com) (asw bsw csw : ℕ)
    (hF : ∀ (j : ℕ) (σ σ' : Env),
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) → F j σ → F j σ')
    (h : PeelSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co ra
      ao aj dg mt od lo lm Spl Sgr swC asw bsw csw) :
    PeelSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co ra
      ao aj dg mt od lo lm (fun j σ => Spl j σ ∧ F j σ)
      (fun j σ => Sgr j σ ∧ F j σ) swC asw bsw csw := by
  intro x hx j hj A hAdm hbot
  refine (specArrsLength (h x hx j hj A hAdm hbot)).conseq ?_ ?_ le_rfl
  · rintro σ ⟨hA, hra, hod, hdel, hca, hco, hSpl, -⟩
    exact ⟨hA, hra, hod, hdel, hca, hco, hSpl⟩
  · rintro σ σ' ⟨-, -, -, -, -, -, -, hFσ⟩ ⟨⟨hA, hctr, hod, hlog, hco, hSgr⟩, hlen⟩
    exact ⟨hA, hctr, hod, hlog, hco, hSgr, hF j σ σ' hlen hFσ⟩

/-! ## §3 The grouping's precondition is monotone

`PeelGroupIn`'s scratch parameter occurs only in the precondition of
its `Spec`, so it strengthens freely — this is `Spec.pre` and nothing
more. -/

open Classical in
/-- **Strengthening the grouping's scratch descriptor.** -/
theorem sweepClose_peelGroupIn_pre (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm : ℕ → String) (od lo lm : ℕ → String) (Sgr Sgr' : ℕ → Env → Prop)
    (grC : ℕ → Com) (agr bgr : ℕ)
    (himp : ∀ (j : ℕ) (σ : Env), Sgr' j σ → Sgr j σ)
    (h : PeelGroupIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm od lo lm
      Sgr grC agr bgr) :
    PeelGroupIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm od lo lm
      Sgr' grC agr bgr := by
  intro x hx j hj A hAdm hbot
  refine (h x hx j hj A hAdm hbot).pre ?_
  rintro σ ⟨hA, hctr, hod, hlog, hco, hS⟩
  exact ⟨hA, hctr, hod, hlog, hco, himp j σ hS⟩

/-! ## §4 `CovPeelIn`, discharged

Three landed theorems and the two lemmas above.  The program is
concrete everywhere: the sentinel pass, `A.N` turns of
`bfsTurnCom ; delAdjCom`, then the grouping's six passes. -/

open Classical in
/-- **The sweep half of `CovPeelIn`**: `PeelSweepIn` at the concrete
program and the concrete descriptor, from `peelBfsIn_bfsTurnCom` and
`peelSweepIn_of_bfs`.  `Ssc` is carried concretely at
`BfsClean (co j) n` — the landed chain fixes it there and this file
does not re-abstract it. -/
theorem sweepClose_peelSweepIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm cnt cur sb : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od lo lm : ℕ → String)
    (hq : 1 ≤ q)
    (hnmB : ∀ j, BfsNames (ca j) (co j) (ao j) (aj j) (dg j) (lo j) (lm j))
    (hfrB : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = mt j →
      b ≠ ca j ∧ b ≠ co j ∧ b ≠ lo j ∧ b ≠ lm j)
    (hnd : ∀ j, ao j ≠ aj j ∧ ao j ≠ mt j ∧ ao j ≠ dg j ∧
      aj j ≠ mt j ∧ aj j ≠ dg j ∧ mt j ≠ dg j ∧ ca j ≠ lo j)
    (hkeep : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = co j ∨ b = lm j ∨ b = ca j ∨
      b = lo j → b ≠ aj j ∧ b ≠ dg j ∧ b ≠ mt j)
    (hfresh : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = co j ∨ b = lm j ∨ b = ao j ∨
      b = aj j ∨ b = dg j ∨ b = mt j → b ≠ ca j ∧ b ≠ lo j)
    (hcoNe : ∀ j, co j ≠ ca j ∧ co j ≠ lo j ∧ co j ≠ lm j ∧ co j ≠ aj j ∧
      co j ≠ dg j ∧ co j ≠ mt j) :
    PeelSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co ra
      ao aj dg mt od lo lm
      (sweepClosePeelSc co cm cnt cur lo lm sb n)
      (sweepClosePeelSc co cm cnt cur lo lm sb n)
      (fun j => sweepCom
        (bfsTurnCom (Headline.headlineSetup C hC φ).R (ca j) (co j) (ao j)
          (aj j) (dg j) (lo j) (lm j) (arenaNames j).nN)
        (ca j) (lo j) (ao j) (aj j) (dg j) (mt j) (od j) (arenaNames j).nN)
      (12 * (Headline.headlineSetup C hC φ).R + 44 + 42) (39 + 54) 76 :=
  sweepClose_peelSweepIn_conj C hC φ ord G c w q ℓp htabF hbf Adm ca co ra
    ao aj dg mt od lo lm _ _ (sweepCloseGrpSc co cm cnt cur lm sb) _ _ _ _
    (fun _ _ _ hlen h => sweepCloseGrpSc_of_len hlen h)
    (peelSweepIn_of_bfs C hC φ ord G c w q ℓp htabF hbf Adm ca co ra
      ao aj dg mt od lo lm (fun j σ => BfsClean (co j) n σ) _ _ _ _ hq
      (Headline.headlineSetup C hC φ).one_le_R hnd hkeep hfresh
      (bfsClean_hSsc hcoNe)
      (peelBfsIn_bfsTurnCom C hC φ ord G c w q ℓp htabF hbf Adm ca co
        ao aj dg mt od lo lm hq (Headline.headlineSetup C hC φ).one_le_R
        hnmB hfrB))

open Classical in
/-- **`CovPeelIn`, discharged.**  The peel run of the cover sweep —
the sentinel pass, `A.N` turns of frontier BFS and swap-delete, then
the two counting sorts — meets `SolveSweepStep`'s residual verbatim,
at

    peelK (12·R + 239) 154 76,

from hypotheses only of the F7-suppliable kinds: `1 ≤ q` and name
hygiene.  `1 ≤ R` is *not* a hypothesis: it is `Setup.one_le_R`.
The scratch descriptor is `sweepClosePeelSc`, a closed formula about
allocation lengths and the visited flags — §8 exhibits a state
satisfying it. -/
theorem sweepClose_covPeelIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm cnt cur sb : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od lo lm : ℕ → String)
    (hq : 1 ≤ q)
    (hnmB : ∀ j, BfsNames (ca j) (co j) (ao j) (aj j) (dg j) (lo j) (lm j))
    (hfrB : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = mt j →
      b ≠ ca j ∧ b ≠ co j ∧ b ≠ lo j ∧ b ≠ lm j)
    (hnd : ∀ j, ao j ≠ aj j ∧ ao j ≠ mt j ∧ ao j ≠ dg j ∧
      aj j ≠ mt j ∧ aj j ≠ dg j ∧ mt j ≠ dg j ∧ ca j ≠ lo j)
    (hkeep : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = co j ∨ b = lm j ∨ b = ca j ∨
      b = lo j → b ≠ aj j ∧ b ≠ dg j ∧ b ≠ mt j)
    (hfresh : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = co j ∨ b = lm j ∨ b = ao j ∨
      b = aj j ∨ b = dg j ∨ b = mt j → b ≠ ca j ∧ b ≠ lo j)
    (hcoNe : ∀ j, co j ≠ ca j ∧ co j ≠ lo j ∧ co j ≠ lm j ∧ co j ≠ aj j ∧
      co j ≠ dg j ∧ co j ≠ mt j)
    (hnmG : ∀ j, GrpNames (lo j) (lm j) (od j) (ca j) (co j) (cm j) (cnt j)
      (cur j) (sb j))
    (hnNg : ∀ j, (arenaNames j).nN ∉ grScalars)
    (hnSg : ∀ j, (arenaNames j).nS ∉ grScalars)
    (harenaG : ∀ j, ∀ b ∈ [co j, cm j, cnt j, cur j, sb j],
      b ≠ (arenaNames j).off ∧ b ≠ (arenaNames j).tgt ∧ b ≠ (arenaNames j).col ∧
      b ≠ (arenaNames j).up ∧ b ≠ (arenaNames j).hist) :
    CovPeelIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra
      ao aj dg mt od
      (sweepClosePeelSc co cm cnt cur lo lm sb n)
      (fun j => .seq
        (sweepCom
          (bfsTurnCom (Headline.headlineSetup C hC φ).R (ca j) (co j) (ao j)
            (aj j) (dg j) (lo j) (lm j) (arenaNames j).nN)
          (ca j) (lo j) (ao j) (aj j) (dg j) (mt j) (od j) (arenaNames j).nN)
        (grCom (arenaNames j).nN (lo j) (lm j) (od j) (co j) (cm j) (cnt j)
          (cur j) (sb j)))
      (fun _ A => peelK (12 * (Headline.headlineSetup C hC φ).R + 239) 154 76
        (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)) := by
  have h := covPeelIn_of_sweep_group C hC φ ord G c w q ℓp htabF hbf Adm
    ca co cm ra ao aj dg mt od lo lm _ _ _ _ _ _ _ _ _
    (sweepClose_peelSweepIn C hC φ ord G c w q ℓp htabF hbf Adm
      ca co cm cnt cur sb ra ao aj dg mt od lo lm hq hnmB hfrB hnd hkeep
      hfresh hcoNe)
    (sweepClose_peelGroupIn_pre C hC φ ord G c w q ℓp htabF hbf Adm
      ca co cm od lo lm _ (sweepClosePeelSc co cm cnt cur lo lm sb n) _ _ _
      (fun _ _ h => h.2)
      (peelGroupIn_grCom C hC φ ord G c w q ℓp htabF hbf Adm
        ca co cm cnt cur sb od lo lm hq hnmG hnNg hnSg harenaG))
  have e1 : 12 * (Headline.headlineSetup C hC φ).R + 44 + 42 + 153
      = 12 * (Headline.headlineSetup C hC φ).R + 239 := by omega
  have e2 : 39 + 54 + 61 = 154 := by norm_num
  rw [e1, e2] at h
  exact h

/-! ## §5 The cost envelope at the peel

`peelK_le_coverCFSel_total` is the column bound: at a node whose
degree parameter the ledger names, a budget affine in the peel's three
figures is at most `(a+b+c)` times that node's **own** cover ledger
vector.  Feeding it `(12·R + 239, 154, 76)` is the check this leaf
exists to make.

Note what this does *not* claim.  It closes **per node**.  The step
from the node to the root is not a monotonicity step, because
`driverChargeMS` places the cover vector inside `frameChargeMS` only
on the `A.G ≠ ⊥` branch; that seam is elsewhere. -/

open Classical in
/-- **The summed peel budget, inside §7's envelope.**  At the
machine's own selection ordering, the discharged budget of
`sweepClose_covPeelIn` is at most

    (12·R + 469) · chargeTotal (coverCFSel sel S cf δ j A)

— a constant times the node's cover ledger vector.  No figure is
quadratic in `A.N`: `peelK`'s three summands are `A.N`, the cluster
mass and the `d_<` edge work, and the ledger vector dominates each
(`le_chargeTotal_coverCFSel` for the first, the `"cover.sweep"` column
for the other two). -/
theorem sweepClose_covPeelIn_budget_le (sel : ∀ m : ℕ, MinDegSel m) (S : Setup L)
    {cf δ : ℝ} (hcf : 1 ≤ cf) (hδ : 0 ≤ δ) (j : ℕ) (A : Arena (S.pal j) n₀)
    (hdeg : ∀ v : Fin A.N,
      (wreach A.G ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order
        (2 * S.R) v).ncard ≤ ⌈cf * (A.N : ℝ) ^ δ⌉₊) :
    peelK (12 * S.R + 239) 154 76 S A
        ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order
      ≤ (12 * S.R + 469) * chargeTotal (coverCFSel sel S cf δ j A) := by
  have h := peelK_le_coverCFSel_total sel S hcf hδ (12 * S.R + 239) 154 76 j A hdeg
  have e : 12 * S.R + 239 + 154 + 76 = 12 * S.R + 469 := by omega
  rwa [e] at h

/-! ## §6 The build pass's budget, in the peel's currency

`covAdjBuildIn_bldCom` prices the build at `bldK A.N ns` with `ns` the
arena's degree sum — the one figure in the whole cover sweep that is
not already one of `peelK`'s three.  Left as it stands, `ns` is
`Θ(A.N²)` on a dense arena, which is exactly the shape that broke the
headline once before.  It does not have to be left as it stands:
`sum_induced_deg_le_two_sum_dlt` at `s = univ`, `H = G` is GKS's own
`Σ_v deg(v) ≤ 2·Σ_v d_<(v)`, and every vertex lies in its own cluster,
so `Σ_v d_<(v) ≤ peelEdgeWork`.  The build therefore folds into the
peel's third figure with no new currency. -/

open Classical in
/-- **The degree sum is twice the `d_<` sum** — `sum_induced_deg_le_two_sum_dlt`
at the full carrier and the graph itself. -/
theorem sweepClose_sum_deg_le_two_sum_dlt {N : ℕ} (Gr : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) :
    ∑ v : Fin N, (Gr.neighborSet v).ncard ≤ 2 * ∑ v : Fin N, Impl.dlt Gr π v := by
  have h := sum_induced_deg_le_two_sum_dlt (le_refl Gr) π Finset.univ
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ncard_eq_card_univ_filter]
  congr 1

open Classical in
/-- **The `d_<` sum is at most the peel's edge work**: `u` lies in its
own cluster (`self_mem_cluster`), so `d_<(u)` is one summand of the
inner sum at `u`. -/
theorem sweepClose_sum_dlt_le_peelEdgeWork (S : Setup L) {Λ : ℕ}
    (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N)) :
    ∑ v : Fin A.N, Impl.dlt A.G π v ≤ peelEdgeWork S A π := by
  refine Finset.sum_le_sum fun u _ => ?_
  refine Finset.single_le_sum (f := fun w => Impl.dlt A.G π w)
    (fun _ _ => Nat.zero_le _) ?_
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, self_mem_cluster S A π u⟩

open Classical in
/-- **The build pass in `peelK` shape**: `bldK A.N ns ≤ peelK 123 0 116`.
The `93·N + 30` becomes `123·N` against `1 ≤ A.N` (a graph on an empty
carrier is `⊥`), and `58·ns` becomes `116·peelEdgeWork`. -/
theorem sweepClose_bldK_le_peelK (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (hN : 1 ≤ A.N) :
    bldK A.N (∑ v : Fin A.N, (A.G.neighborSet v).ncard) ≤ peelK 123 0 116 S A π := by
  have h1 : ∑ v : Fin A.N, (A.G.neighborSet v).ncard ≤ 2 * peelEdgeWork S A π :=
    le_trans (sweepClose_sum_deg_le_two_sum_dlt A.G π)
      (Nat.mul_le_mul_left 2 (sweepClose_sum_dlt_le_peelEdgeWork S A π))
  simp only [bldK, peelK]
  have h2 : 58 * (∑ v : Fin A.N, (A.G.neighborSet v).ncard)
      ≤ 116 * peelEdgeWork S A π := by
    calc 58 * (∑ v : Fin A.N, (A.G.neighborSet v).ncard)
        ≤ 58 * (2 * peelEdgeWork S A π) := Nat.mul_le_mul_left 58 h1
      _ = 116 * peelEdgeWork S A π := by ring
  have h3 : 93 * A.N + 30 ≤ 123 * A.N := by omega
  omega

/-! ## §7 `CovSweepIn`

The build pass is landed (`covAdjBuildIn_bldCom`) and `CovPeelIn` is
now landed too, so `covSweepIn_of_build_peel` closes the whole sweep.
The build's scratch descriptor is `sweepCloseBldSc`, which *is* its
allocation duty, so that hypothesis is `id`; its transport duty on the
peel's descriptor is the name-hygiene clause `hbldFresh`. -/

open Classical in
/-- `CovSweepIn` relaxes upward in its budget. -/
theorem sweepClose_covSweepIn_mono (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm : ℕ → String) (ra : ℕ → String) (Ssw : ℕ → Env → Prop)
    (swC : ℕ → Com)
    (Ksw Ksw' : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (hK : ∀ (j : ℕ) (A : Arena ((Headline.headlineSetup C hC φ).pal j) n),
      Adm j A → ¬ A.G = ⊥ → Ksw j A ≤ Ksw' j A)
    (h : CovSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra Ssw swC Ksw) :
    CovSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra Ssw swC Ksw' :=
  fun x hx j hj A hAdm hbot =>
    (h x hx j hj A hAdm hbot).mono (hK j A hAdm hbot)

open Classical in
/-- **The cover sweep, discharged.**  From the rank array the ordering
pass leaves, the build materializes the deletable adjacency structure
and the order region, and the peel run of §4 delivers
`CoverStageSpec`'s exact postcondition — `CtrArr` at `Driver.centre`,
`ClusterCsr` at `Driver.cluster`.  The whole sweep at

    peelK (12·R + 362) 154 192,

one affine budget in the peel's own three figures: nothing quadratic
in `A.N` survives the build's degree-sum term (§6). -/
theorem sweepClose_covSweepIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co cm cnt cur sb : ℕ → String) (ra : ℕ → String)
    (ao aj dg mt od lo lm : ℕ → String)
    (hq : 1 ≤ q)
    (hnmB : ∀ j, BfsNames (ca j) (co j) (ao j) (aj j) (dg j) (lo j) (lm j))
    (hfrB : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = mt j →
      b ≠ ca j ∧ b ≠ co j ∧ b ≠ lo j ∧ b ≠ lm j)
    (hnd : ∀ j, ao j ≠ aj j ∧ ao j ≠ mt j ∧ ao j ≠ dg j ∧
      aj j ≠ mt j ∧ aj j ≠ dg j ∧ mt j ≠ dg j ∧ ca j ≠ lo j)
    (hkeep : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = co j ∨ b = lm j ∨ b = ca j ∨
      b = lo j → b ≠ aj j ∧ b ≠ dg j ∧ b ≠ mt j)
    (hfresh : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = od j ∨ b = co j ∨ b = lm j ∨ b = ao j ∨
      b = aj j ∨ b = dg j ∨ b = mt j → b ≠ ca j ∧ b ≠ lo j)
    (hcoNe : ∀ j, co j ≠ ca j ∧ co j ≠ lo j ∧ co j ≠ lm j ∧ co j ≠ aj j ∧
      co j ≠ dg j ∧ co j ≠ mt j)
    (hnmG : ∀ j, GrpNames (lo j) (lm j) (od j) (ca j) (co j) (cm j) (cnt j)
      (cur j) (sb j))
    (hnNg : ∀ j, (arenaNames j).nN ∉ grScalars)
    (hnSg : ∀ j, (arenaNames j).nS ∉ grScalars)
    (harenaG : ∀ j, ∀ b ∈ [co j, cm j, cnt j, cur j, sb j],
      b ≠ (arenaNames j).off ∧ b ≠ (arenaNames j).tgt ∧ b ≠ (arenaNames j).col ∧
      b ≠ (arenaNames j).up ∧ b ≠ (arenaNames j).hist)
    (hnmBld : ∀ j, BldNames (arenaNames j).off (arenaNames j).tgt (ra j)
      (ao j) (aj j) (dg j) (mt j) (od j))
    (hcolBld : ∀ j, ∀ b ∈ [ao j, aj j, dg j, mt j, od j],
      b ≠ (arenaNames j).col ∧ b ≠ (arenaNames j).up ∧ b ≠ (arenaNames j).hist)
    (hbldFresh : ∀ (j : ℕ) (b : String), b = lo j ∨ b = lm j ∨ b = co j ∨
      b = cm j ∨ b = sb j ∨ b = cnt j ∨ b = cur j →
      b ≠ ao j ∧ b ≠ aj j ∧ b ≠ dg j ∧ b ≠ mt j ∧ b ≠ od j) :
    CovSweepIn C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra
      (fun j σ => sweepCloseBldSc ao aj dg mt od j σ ∧
        sweepClosePeelSc co cm cnt cur lo lm sb n j σ)
      (fun j => .seq
        (bldCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
          (arenaNames j).tgt (ra j) (ao j) (aj j) (dg j) (mt j) (od j))
        (.seq
          (sweepCom
            (bfsTurnCom (Headline.headlineSetup C hC φ).R (ca j) (co j) (ao j)
              (aj j) (dg j) (lo j) (lm j) (arenaNames j).nN)
            (ca j) (lo j) (ao j) (aj j) (dg j) (mt j) (od j) (arenaNames j).nN)
          (grCom (arenaNames j).nN (lo j) (lm j) (od j) (co j) (cm j) (cnt j)
            (cur j) (sb j))))
      (fun _ A => peelK (12 * (Headline.headlineSetup C hC φ).R + 362) 154 192
        (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)) := by
  refine sweepClose_covSweepIn_mono C hC φ ord G c w q ℓp htabF hbf Adm
    ca co cm ra _ _ _ _ ?_
    (covSweepIn_of_build_peel C hC φ ord G c w q ℓp htabF hbf Adm ca co cm ra
      ao aj dg mt od _ _ _ _ _ _
      (covAdjBuildIn_bldCom C hC φ ord G c w q ℓp htabF hbf Adm ca co ra
        ao aj dg mt od (sweepCloseBldSc ao aj dg mt od)
        (sweepClosePeelSc co cm cnt cur lo lm sb n) hq hnmBld hcolBld
        (fun _ _ h => h) ?_)
      (sweepClose_covPeelIn C hC φ ord G c w q ℓp htabF hbf Adm
        ca co cm cnt cur sb ra ao aj dg mt od lo lm hq hnmB hfrB hnd hkeep
        hfresh hcoNe hnmG hnNg hnSg harenaG))
  · -- the two budgets sum inside one affine budget
    intro j A _ hbot
    have hN : 1 ≤ A.N := by
      by_contra hcc
      exact hbot (by ext a b; exact absurd a.isLt (by omega))
    have hb := sweepClose_bldK_le_peelK (Headline.headlineSetup C hC φ) A
      ((ord A.N A.G).order) hN
    have hadd := peelK_add 123 0 116
      (12 * (Headline.headlineSetup C hC φ).R + 239) 154 76
      (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)
    have e1 : 123 + (12 * (Headline.headlineSetup C hC φ).R + 239)
        = 12 * (Headline.headlineSetup C hC φ).R + 362 := by omega
    have e2 : (0 : ℕ) + 154 = 154 := by norm_num
    have e3 : 116 + 76 = 192 := by norm_num
    rw [e1, e2, e3] at hadd
    omega
  · -- the peel's scratch descriptor survives the build's five writes
    rintro j σ σ' ⟨⟨hlo, hlm, hcl⟩, hgr⟩ harr -
    have hlo' : σ'.arrs (lo j) = σ.arrs (lo j) := by
      obtain ⟨k1, k2, k3, k4, k5⟩ := hbldFresh j (lo j) (Or.inl rfl)
      exact harr _ k1 k2 k3 k4 k5
    have hlm' : σ'.arrs (lm j) = σ.arrs (lm j) := by
      obtain ⟨k1, k2, k3, k4, k5⟩ := hbldFresh j (lm j) (Or.inr (Or.inl rfl))
      exact harr _ k1 k2 k3 k4 k5
    have hco' : σ'.arrs (co j) = σ.arrs (co j) := by
      obtain ⟨k1, k2, k3, k4, k5⟩ := hbldFresh j (co j) (Or.inr (Or.inr (Or.inl rfl)))
      exact harr _ k1 k2 k3 k4 k5
    have hcm' : σ'.arrs (cm j) = σ.arrs (cm j) := by
      obtain ⟨k1, k2, k3, k4, k5⟩ :=
        hbldFresh j (cm j) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      exact harr _ k1 k2 k3 k4 k5
    have hsb' : σ'.arrs (sb j) = σ.arrs (sb j) := by
      obtain ⟨k1, k2, k3, k4, k5⟩ :=
        hbldFresh j (sb j) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      exact harr _ k1 k2 k3 k4 k5
    have hcnt' : σ'.arrs (cnt j) = σ.arrs (cnt j) := by
      obtain ⟨k1, k2, k3, k4, k5⟩ :=
        hbldFresh j (cnt j) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      exact harr _ k1 k2 k3 k4 k5
    have hcur' : σ'.arrs (cur j) = σ.arrs (cur j) := by
      obtain ⟨k1, k2, k3, k4, k5⟩ :=
        hbldFresh j (cur j)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      exact harr _ k1 k2 k3 k4 k5
    obtain ⟨g1, g2, g3, g4⟩ := hgr
    exact ⟨⟨by rw [hlo']; exact hlo, by rw [hlm']; exact hlm,
      bfsClean_of_eq hcl hco'⟩,
      by rw [hlm', hcm']; exact g1, by rw [hlm', hsb']; exact g2,
      by rw [hco', hcnt']; exact g3, by rw [hco', hcur']; exact g4⟩

/-! ## §8 Anti-vacuity

Every descriptor in §1 is a closed formula, and nothing above
constrains any of them only through an implication.  Still, "closed"
is not "satisfiable": here is one state that satisfies all three at
once, for any names and any `n`.  `Ssc` itself was never re-abstracted
— the landed chain fixes it at `BfsClean (co j) n` and this file
carries that instance through. -/

/-- **The three scratch descriptors are simultaneously inhabited.** -/
theorem sweepClose_sc_inhabited (co cm cnt cur lo lm sb : ℕ → String)
    (ao aj dg mt od : ℕ → String) (n j : ℕ) :
    ∃ σ : Env, sweepClosePeelSc co cm cnt cur lo lm sb n j σ ∧
      sweepCloseGrpSc co cm cnt cur lm sb j σ ∧
      sweepCloseBldSc ao aj dg mt od j σ := by
  classical
  have hz : ∀ m v : ℕ, (List.replicate m (0 : ℕ)).getD v 0 = 0 := by
    intro m v
    simp
  refine ⟨⟨fun _ => 0, fun _ => List.replicate (n * n + n + 1) 0, [], []⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_replicate]; omega
    · simp only [List.length_replicate]; omega
    · intro v _; exact hz _ _
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
  · exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [List.length_replicate] <;> omega

open Classical in
/-- **The whole sweep's budget, inside §7's envelope.**  The same
column bound at the summed figures of §7: at the machine's own
selection ordering,

    peelK (12·R + 362) 154 192 ≤ (12·R + 708) · chargeTotal (coverCFSel …).

The build pass contributes `123` to the linear figure and `116` to the
edge figure and *nothing* to a fourth; there is no `A.N²` term
anywhere in the cover sweep's account. -/
theorem sweepClose_covSweepIn_budget_le (sel : ∀ m : ℕ, MinDegSel m) (S : Setup L)
    {cf δ : ℝ} (hcf : 1 ≤ cf) (hδ : 0 ≤ δ) (j : ℕ) (A : Arena (S.pal j) n₀)
    (hdeg : ∀ v : Fin A.N,
      (wreach A.G ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order
        (2 * S.R) v).ncard ≤ ⌈cf * (A.N : ℝ) ^ δ⌉₊) :
    peelK (12 * S.R + 362) 154 192 S A
        ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order
      ≤ (12 * S.R + 708) * chargeTotal (coverCFSel sel S cf δ j A) := by
  have h := peelK_le_coverCFSel_total sel S hcf hδ (12 * S.R + 362) 154 192 j A hdeg
  have e : 12 * S.R + 362 + 154 + 192 = 12 * S.R + 708 := by omega
  rwa [e] at h

/-! ## §9 Anti-vacuity, at the names

Every hypothesis §4 and §7 leave open is a disequality between region
names — the shape F7 supplies.  A bundle of disequalities is only as
good as its consistency, so this section exhibits one family that
supplies **all** of them at once: fourteen four-character bases under
`lv`, pairwise distinct and distinct from the arena's own eight, at
every level.  `sweepClose_covSweepIn_names` is `sweepClose_covSweepIn`
with every name hypothesis discharged — no name hypothesis survives,
and the discharge is therefore not vacuous. -/

/-- Two distinct four-character bases stay distinct at every level. -/
theorem sweepCloseNe4 {s t : String} (hs : s.length = 4) (ht : t.length = 4)
    (hst : s ≠ t) (j : ℕ) : lv s j ≠ lv t j :=
  lv_ne_of_base_ne (by rw [hs, ht]) hst j j

/-- The assignment (`ctr`) region. -/
def sweepCloseCa : ℕ → String := lv "sc.a"
/-- The cluster-offset region. -/
def sweepCloseCo : ℕ → String := lv "sc.o"
/-- The cluster-membership region. -/
def sweepCloseCm : ℕ → String := lv "sc.m"
/-- The first counting sort's counters. -/
def sweepCloseCnt : ℕ → String := lv "sc.n"
/-- The second counting sort's cursor. -/
def sweepCloseCur : ℕ → String := lv "sc.u"
/-- The sorted centres. -/
def sweepCloseSb : ℕ → String := lv "sc.b"
/-- The rank array. -/
def sweepCloseRa : ℕ → String := lv "sc.r"
/-- The deletable structure's offsets. -/
def sweepCloseAo : ℕ → String := lv "sc.p"
/-- The deletable structure's targets. -/
def sweepCloseAj : ℕ → String := lv "sc.j"
/-- The live degrees. -/
def sweepCloseDg : ℕ → String := lv "sc.d"
/-- The mate pointers. -/
def sweepCloseMt : ℕ → String := lv "sc.t"
/-- The order region (the rank array's inverse). -/
def sweepCloseOd : ℕ → String := lv "sc.q"
/-- The peel log's offsets. -/
def sweepCloseLo : ℕ → String := lv "sc.l"
/-- The peel log's members. -/
def sweepCloseLm : ℕ → String := lv "sc.g"

section Names

variable (j : ℕ)

theorem sweepClose_bfsNames :
    BfsNames (sweepCloseCa j) (sweepCloseCo j) (sweepCloseAo j) (sweepCloseAj j)
      (sweepCloseDg j) (sweepCloseLo j) (sweepCloseLm j) := by
  repeat' apply And.intro
  all_goals exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_hfrB (b : String) (hb : b = (arenaNames j).off ∨
    b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
    b = (arenaNames j).hist ∨ b = sweepCloseOd j ∨ b = sweepCloseMt j) :
    b ≠ sweepCloseCa j ∧ b ≠ sweepCloseCo j ∧ b ≠ sweepCloseLo j ∧
      b ≠ sweepCloseLm j := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_hnd :
    sweepCloseAo j ≠ sweepCloseAj j ∧ sweepCloseAo j ≠ sweepCloseMt j ∧
      sweepCloseAo j ≠ sweepCloseDg j ∧ sweepCloseAj j ≠ sweepCloseMt j ∧
      sweepCloseAj j ≠ sweepCloseDg j ∧ sweepCloseMt j ≠ sweepCloseDg j ∧
      sweepCloseCa j ≠ sweepCloseLo j := by
  repeat' apply And.intro
  all_goals exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_hkeep (b : String) (hb : b = (arenaNames j).off ∨
    b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
    b = (arenaNames j).hist ∨ b = sweepCloseOd j ∨ b = sweepCloseCo j ∨
    b = sweepCloseLm j ∨ b = sweepCloseCa j ∨ b = sweepCloseLo j) :
    b ≠ sweepCloseAj j ∧ b ≠ sweepCloseDg j ∧ b ≠ sweepCloseMt j := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩ <;>
      exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_hfresh (b : String) (hb : b = (arenaNames j).off ∨
    b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
    b = (arenaNames j).hist ∨ b = sweepCloseOd j ∨ b = sweepCloseCo j ∨
    b = sweepCloseLm j ∨ b = sweepCloseAo j ∨ b = sweepCloseAj j ∨
    b = sweepCloseDg j ∨ b = sweepCloseMt j) :
    b ≠ sweepCloseCa j ∧ b ≠ sweepCloseLo j := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_⟩ <;>
      exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_hcoNe :
    sweepCloseCo j ≠ sweepCloseCa j ∧ sweepCloseCo j ≠ sweepCloseLo j ∧
      sweepCloseCo j ≠ sweepCloseLm j ∧ sweepCloseCo j ≠ sweepCloseAj j ∧
      sweepCloseCo j ≠ sweepCloseDg j ∧ sweepCloseCo j ≠ sweepCloseMt j := by
  repeat' apply And.intro
  all_goals exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_grpNames :
    GrpNames (sweepCloseLo j) (sweepCloseLm j) (sweepCloseOd j) (sweepCloseCa j)
      (sweepCloseCo j) (sweepCloseCm j) (sweepCloseCnt j) (sweepCloseCur j)
      (sweepCloseSb j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        exact sweepCloseNe4 (by decide) (by decide) (by decide) j
  all_goals exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_nN_grScalars : (arenaNames j).nN ∉ grScalars := by
  simp only [grScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_len4 (by decide) (by decide) (by decide) j

theorem sweepClose_nS_grScalars : (arenaNames j).nS ∉ grScalars := by
  simp only [grScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_len4 (by decide) (by decide) (by decide) j

theorem sweepClose_harenaG (b : String)
    (hb : b ∈ [sweepCloseCo j, sweepCloseCm j, sweepCloseCnt j, sweepCloseCur j,
      sweepCloseSb j]) :
    b ≠ (arenaNames j).off ∧ b ≠ (arenaNames j).tgt ∧ b ≠ (arenaNames j).col ∧
      b ≠ (arenaNames j).up ∧ b ≠ (arenaNames j).hist := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_bldNames :
    BldNames (arenaNames j).off (arenaNames j).tgt (sweepCloseRa j)
      (sweepCloseAo j) (sweepCloseAj j) (sweepCloseDg j) (sweepCloseMt j)
      (sweepCloseOd j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_hcolBld (b : String)
    (hb : b ∈ [sweepCloseAo j, sweepCloseAj j, sweepCloseDg j, sweepCloseMt j,
      sweepCloseOd j]) :
    b ≠ (arenaNames j).col ∧ b ≠ (arenaNames j).up ∧ b ≠ (arenaNames j).hist := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩ <;>
      exact sweepCloseNe4 (by decide) (by decide) (by decide) j

theorem sweepClose_hbldFresh (b : String) (hb : b = sweepCloseLo j ∨
    b = sweepCloseLm j ∨ b = sweepCloseCo j ∨ b = sweepCloseCm j ∨
    b = sweepCloseSb j ∨ b = sweepCloseCnt j ∨ b = sweepCloseCur j) :
    b ≠ sweepCloseAo j ∧ b ≠ sweepCloseAj j ∧ b ≠ sweepCloseDg j ∧
      b ≠ sweepCloseMt j ∧ b ≠ sweepCloseOd j := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      exact sweepCloseNe4 (by decide) (by decide) (by decide) j

end Names

open Classical in
/-- **`CovSweepIn` at a concrete name family, with no name hypothesis
left.**  Only `1 ≤ q` survives — the schedule constant's positivity,
which F7 supplies from the schedule itself.  This is the anti-vacuity
statement for §4 and §7: the disequality bundles those theorems leave
open are jointly satisfiable, and here is the family that satisfies
them. -/
theorem sweepClose_covSweepIn_names (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (hq : 1 ≤ q) :
    CovSweepIn C hC φ ord G c w q ℓp htabF hbf Adm
      sweepCloseCa sweepCloseCo sweepCloseCm sweepCloseRa
      (fun j σ => sweepCloseBldSc sweepCloseAo sweepCloseAj sweepCloseDg
          sweepCloseMt sweepCloseOd j σ ∧
        sweepClosePeelSc sweepCloseCo sweepCloseCm sweepCloseCnt sweepCloseCur
          sweepCloseLo sweepCloseLm sweepCloseSb n j σ)
      (fun j => .seq
        (bldCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
          (arenaNames j).tgt (sweepCloseRa j) (sweepCloseAo j) (sweepCloseAj j)
          (sweepCloseDg j) (sweepCloseMt j) (sweepCloseOd j))
        (.seq
          (sweepCom
            (bfsTurnCom (Headline.headlineSetup C hC φ).R (sweepCloseCa j)
              (sweepCloseCo j) (sweepCloseAo j) (sweepCloseAj j)
              (sweepCloseDg j) (sweepCloseLo j) (sweepCloseLm j)
              (arenaNames j).nN)
            (sweepCloseCa j) (sweepCloseLo j) (sweepCloseAo j) (sweepCloseAj j)
            (sweepCloseDg j) (sweepCloseMt j) (sweepCloseOd j) (arenaNames j).nN)
          (grCom (arenaNames j).nN (sweepCloseLo j) (sweepCloseLm j)
            (sweepCloseOd j) (sweepCloseCo j) (sweepCloseCm j) (sweepCloseCnt j)
            (sweepCloseCur j) (sweepCloseSb j))))
      (fun _ A => peelK (12 * (Headline.headlineSetup C hC φ).R + 362) 154 192
        (Headline.headlineSetup C hC φ) A ((ord A.N A.G).order)) :=
  sweepClose_covSweepIn C hC φ ord G c w q ℓp htabF hbf Adm
    sweepCloseCa sweepCloseCo sweepCloseCm sweepCloseCnt sweepCloseCur
    sweepCloseSb sweepCloseRa sweepCloseAo sweepCloseAj sweepCloseDg
    sweepCloseMt sweepCloseOd sweepCloseLo sweepCloseLm hq
    sweepClose_bfsNames sweepClose_hfrB sweepClose_hnd sweepClose_hkeep
    sweepClose_hfresh sweepClose_hcoNe sweepClose_grpNames
    sweepClose_nN_grScalars sweepClose_nS_grScalars sweepClose_harenaG
    sweepClose_bldNames sweepClose_hcolBld sweepClose_hbldFresh

/-! ## §10 What is left, named exactly

`coverAllIn_of_order_sweep` (`SolveCovStep.lean:207`) takes
`CovOrderIn` and `CovSweepIn` to `CoverAllIn`.  §7 supplies the second.
The first is *not* available: `covOrderIn_bucketPeel`
(`SolveSweepBucketRound.lean:3223`) concludes `CovOrderIn` at
`selOrderingRoutine bucketSel R` — unconditionally on the *peel* side,
which is the half it proves — but from a named residual

    hag : CovAugAdjSelIn C hC φ (fun m => bucketSel m) R G c w q ℓp
            htabF hbf Adm ca co aoO ajO dgO mtO Sag … Ssw agC Kag

(line 3249).  `CovAugAdjSelIn` is the *augmented* adjacency build: the
sorted, augmentation-aware adjacency structure the bucket ordering
pops from, which is a different region from the `DelAdjSt` structure
`CovAdjBuildIn` materializes and cannot be supplied by it.

`CovAugAdjSelIn` is not discharged, but it *is* reduced, so the gap is
smaller and more precisely placed than "one residual":

* `covAugAdjSelIn_of_base_rounds_sym` (`SolveAugCompose.lean:493`)
  takes `AugBaseIn`, `AugRoundIn` and `AugSymIn` to it;
* `augBaseIn_of_adj_peel_orient` (`SolveAugCompose.lean:885`) takes
  `AugBaseAdjIn`, `AugBasePeelIn`, `AugBaseOrientIn` to `AugBaseIn`,
  and all three of those **are** discharged —
  `augBaseAdjIn_bldAdjCom` (`SolveAugFrameProg.lean:275`),
  `augBasePeelIn_bucketPeelBuild` (`SolveAugBaseFrame.lean:205`),
  `augBaseOrientIn_orCom` (`SolveAugOrient.lean:1993`);
* `augSymIn_of_symCsr_build` (`SolveAugCompose.lean:657`) takes
  `AugSymCsrIn` to `AugSymIn`.

That leaves exactly **two** predicates on the whole path from
`CovSweepIn` to `CoverAllIn` that occur only as hypotheses and are
concluded by no theorem in the tree:

1. **`AugRoundIn`** (`SolveAugCompose.lean:508`) — one augmentation
   round: the fraternal/transitive edge emission at
   `selChain (sel A.N) A.G i → selChain … (i+1)`.
2. **`AugSymCsrIn`** (`SolveAugCompose.lean:685`) — the
   symmetrization's CSR transpose, the input to the landed
   `bldAdjCom` that finishes `AugSymIn`.

Both are on the **ordering** side.  The peel side is closed.

One further seam, mechanical but not attempted here because it is
blocked by the two above: `coverAllIn_of_order_sweep` wants
`CovOrderIn` and `CovSweepIn` at the *same* `Ssw`, and
`covOrderIn_bucketPeel` carries an `hSsw` transport clause for it.
`sweepCloseBldSc` and `sweepClosePeelSc` meet that clause — array
lengths are preserved outright, `(arenaNames j).nN`/`nS` are
level-tagged four-character names and so are none of the `"bk.*"`
scratch scalars, and `BfsClean` rides on `co ∉ {ra, mtO, dgO, tpO,
skO}` — but the seam is only worth writing once there is a
`CovOrderIn` to attach it to.

Two further seams, recorded because they are load-bearing and are
*not* closed here:

* The budget bound of §5 is **per node**.  `driverChargeMS` places the
  cover vector inside `frameChargeMS` only on the `A.G ≠ ⊥` branch, so
  the node→root step is not monotonicity and is not attempted.
* §5 needs the degree hypothesis `hdeg` at the ledger's own `cf`;
  `exists_mcChargeMS_T_bucket_coverColumn` is where that constant and
  that hypothesis are produced together.
-/

#print axioms sweepClose_peelSweepIn_conj

#print axioms sweepClose_peelGroupIn_pre

#print axioms sweepClose_peelSweepIn

#print axioms sweepClose_covPeelIn

#print axioms sweepClose_covPeelIn_budget_le

#print axioms sweepClose_bldK_le_peelK

#print axioms sweepClose_covSweepIn

#print axioms sweepClose_covSweepIn_budget_le

#print axioms sweepClose_sc_inhabited

#print axioms sweepClose_covSweepIn_names

end Lax3Proofs.Prog
