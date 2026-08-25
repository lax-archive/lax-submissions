import Lax3Proofs.SolveSweepBucketProg
import Lax3Proofs.SolveSweepBuild
import Lax3Proofs.ProgCoverChargeSel
import Lax3Proofs.SolveAugFrat
import Lax3Proofs.SolveAugTrans

/-!
# F6c12-5a — the augmentation's frame: base, rounds, symmetrization

`CovAugAdjIn` (`SolveSweepOrder.lean:413`) asks for a program that runs
the `R` rounds of the deterministic tight transitive–fraternal
augmentation and leaves `(mdChain A.G R).toGraph` as a `DelAdjSt`
region. This file is **everything of that pass except the two
enumerations and the round's emit** — the frame the siblings' passes
hang in:

1. **`AugBaseIn` (§3)** — round `0`. `selChain sel G 0` is
   `baseOr G (selPerm sel G)` (§0 `selChain_zero`, read off the
   definition, not assumed): peel `G`, then orient every edge from its
   `selPerm`-smaller to its `selPerm`-larger end. §6 splits it into
   three named passes — the region build, the peel *at its linear
   contract*, the orientation — and composes them
   (`augBaseIn_of_adj_peel_orient`). **None of the three is discharged
   here**: the build is `covAdjBuildIn_bldCom`'s content minus the rank
   inversion (`bldAdjCom` behind the arena's window), and writing that
   out is left to whoever programs the other two.

2. **The `R`-round loop (§1, §4)** — the unrolled program `comIter`,
   its `Spec` rule `spec_comIter`, and the induction that identifies
   the loop's `i`-th state with `selChain sel A.G i`. The step identity
   `selChain sel G (i+1) = greedyStep (selRank sel (fratGraph …)) …`
   is §0's `selChain_succ`, again read off the definition.

3. **`AugSymIn` (§3, §5)** — symmetrize the final orientation into a
   `DelAdjSt` at `(selChain sel A.G R).toGraph`. §5 splits it into the
   transpose-and-merge residual `AugSymCsrIn` and `bldAdjCom`, and here
   `adjBuildAt_bldAdjCom` applies **directly** — the CSR the transpose
   leaves is in fresh arrays, not behind the arena's window — so
   `augSymIn_of_symCsr_build` is the file's one real composition with a
   landed program: the build half is proved, not assumed.

§4's `covAugAdjSelIn_of_base_rounds_sym` concludes `CovAugAdjSelIn`
(wave 25) verbatim, and `covAugAdjIn_of_base_rounds_sym` concludes the
landed `CovAugAdjIn` verbatim at `sel = mdSel`, both from the three
residuals and nothing else.

## The state predicate is a parameter

The rounds are stated at an abstract per-level *orientation region*

    AugSt : (j : ℕ) → (A : Arena … ) → Orientation A.N → Env → Prop

rather than at a fixed one. That is deliberate: the round body is
F6c12-5b/5c's (`FratCsrAt`, `TransCsrIn`, and the emit), and the
region it carries the current orientation in is theirs to choose.
`InNCsr` (`SolveAugFrat.lean:144`) is what both enumerations consume
and what the emit rebuilds, so §7 records `augStInN` — the canonical
instance, with `augStInN_ns` for the fact that the region determines
its own width — and every statement below holds at it. Nothing in
§1–§6 depends on the choice.

`greedyStep`'s output is an `Orientation` by construction, so
`not_mem_self` and `asymm` (NOdM permits a 2-cycle; Lean's
`Orientation` does not) travel with the round's postcondition and are
never separately assumed.

## The budget — pinned shapes, free constants

No new cost function is invented. Every residual's budget is a fixed
shape in the landed counts of `ProgCoverCharge`, with only the
constants free (w24's `peelK`, w26's `linearPeelBudget`):

    augBaseBudget  bn ba bc N D = bn·N + ba·arcCount D + bc
    augRoundBudget kn ka kf kt kc D
        = kn·n + ka·arcCount D + kf·fratPairCount D + kt·transPairCount D + kc
    augSymBudget   sn sa sc N D = sn·N + sa·arcCount D + sc

`augRoundBudget`'s shape is `levelCharge`'s (`ProgCoverCharge.lean:150`)
term for term, `augBaseBudget`'s is `selBaseCharge`'s and
`augSymBudget`'s is `finalCharge`'s. §2's `augChainCost_le_selChainCharge`
proves the composed total is `k·selChainCharge (sel m) G R + O(R)` once
the constants are bounded by the corresponding multiples of `k`, and
`exists_augChainCost_le` pushes that through wave 25's
`exists_selChainCharge_le` to `f·m^{1+δ} + O(R)` on a nowhere dense
class — **one δ inside** §7's envelope, the pre-verified target.

The trap the split is drawn around: the augmentation runs a peel
`R + 1` times (once on `G` for the base, once per round on the
fraternal graph), so a *quadratic* peel multiplies by `R + 1`. §5's
`AugBasePeelIn` therefore takes the peel at the **linear** contract
F6c13c (`SolveSweepBucketProg`) is built for — `a·N + b·slotCount + c`,
no `N²` — and never at the landed quadratic `peelCom`.

## What remains named-but-unproved, and to whom it belongs

* `AugRoundIn` — the round body: the fraternal CSR (F6c12-5b-ii), the
  transitive region (F6c12-5c-i, **landed**: `transCsrIn_trCom`), the
  peel of `fratGraph D` and the emit (F6c12-5c-ii). Siblings'.
* `AugBaseAdjIn`, `AugBasePeelIn`, `AugBaseOrientIn`, `AugSymCsrIn` —
  this leaf's own four small passes; **stated, not programmed**.
* The only program discharged here is the symmetrization's build half,
  inside `augSymIn_of_symCsr_build`, from the landed
  `adjBuildAt_bldAdjCom`.
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.Augmentation (Orientation fratGraph baseOr)
open Lax3Proofs.CoverRoutine (MinDegSel mdSel greedyStep selRank selPerm
  selChain mdChain mdPerm)

/-! ## §0 The chain, read off its definition

Hazard 1 of the packet: `selChain`'s round `0` is checked against the
definition, not assumed. Both equations below are `rfl` — they are the
equation compiler's own, and the point of naming them is that every
statement in §3–§5 quotes one of them. -/

/-- **Round `0` of the chain is the base orientation.** The peel of `G`
along the selection, with every edge pointing from its `selPerm`-smaller
to its `selPerm`-larger end. -/
theorem selChain_zero {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m)) :
    selChain sel G 0 = baseOr G (selPerm sel G) := rfl

/-- **Round `i + 1` is one greedy step along the peel of the current
fraternity graph.** The ranking the step arbitrates with is
`selRank sel (fratGraph (selChain sel G i))` — the peel of the
*fraternity* graph of the current orientation, not of `G` and not of
the augmented graph. -/
theorem selChain_succ {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m))
    (i : ℕ) :
    selChain sel G (i + 1)
      = greedyStep (selRank sel (fratGraph (selChain sel G i))) (selChain sel G i) :=
  rfl

/-! ## §1 The unrolled round program, and its `Spec` rule

`R` is a constant of the construction (the augmentation depth, fixed
with the class and the sentence before any graph is seen), so the
rounds are *unrolled* rather than run under a `while`: the program is a
literal `R`-fold sequence and there is no loop counter to maintain, no
guard to evaluate and no word bound to check on it. -/

/-- The `R`-fold sequence of a command, left-nested: `comIter c 0` is
`skip` and `comIter c (i+1)` runs the first `i` copies and then one
more. -/
def comIter (c : Com) : ℕ → Com
  | 0 => .skip
  | i + 1 => .seq (comIter c i) c

@[simp] theorem comIter_zero (c : Com) : comIter c 0 = .skip := rfl

@[simp] theorem comIter_succ (c : Com) (i : ℕ) :
    comIter c (i + 1) = .seq (comIter c i) c := rfl

/-- **The rule for an unrolled loop**: a command that carries the
indexed predicate `P i` to `P (i+1)` at cost `K i`, for every `i < R`,
carries `P 0` to `P R` in `R` copies at cost `1 + ∑_{i<R} K i`. The
`1` is `skip`'s own step at `R = 0`.

Nothing here is specific to the augmentation; it is the counterpart of
`Spec.forRange` for a count fixed at construction time. -/
theorem spec_comIter {B : ℕ} {c : Com} {P : ℕ → Env → Prop} {K : ℕ → ℕ} :
    ∀ R : ℕ, (∀ i, i < R → Spec B (P i) c (fun _ σ' => P (i + 1) σ') (K i)) →
      Spec B (P 0) (comIter c R) (fun _ σ' => P R σ')
        (1 + ∑ i ∈ Finset.range R, K i) := by
  intro R
  induction R with
  | zero =>
      intro _
      refine (Spec.skip (B := B) (P := P 0)).post ?_ |>.mono ?_
      · rintro σ σ' hσ rfl; exact hσ
      · rw [Finset.sum_range_zero]
        omega
  | succ R ih =>
      intro h
      refine (Spec.seq (ih (fun i hi => h i (by omega))) (h R (by omega))
        (fun _ σ' _ hq => hq) (fun _ _ _ _ _ hq' => hq')).mono ?_
      rw [Finset.sum_range_succ]
      omega

/-! ## §2 The budget: the shapes, and the envelope they close in

Three shapes, each the corresponding term of the landed
`selChainCharge` (`ProgCoverChargeSel.lean:147`) with free constants.
No new cost function is introduced anywhere in this file. -/

/-- **The base pass's budget shape** — `selBaseCharge`'s: one scan of
the carrier and a constant per arc of round `0` (whose arcs are exactly
the edges of `G`, `baseOr_orients`). -/
def augBaseBudget (bn ba bc : ℕ) {N : ℕ} (D : Orientation N) : ℕ :=
  bn * N + ba * arcCount D + bc

/-- **One round's budget shape** — `levelCharge`'s, term for term: the
per-vertex loop headers, the old-arc carry and the transitive
enumeration's middle loop, the fraternal candidate pairs, the
transitive candidate paths. This is the shape `FratCsrAt`'s `fratK` and
`TransCsrIn`'s `trK` already have (`fratK_le`, `trK_le`), so a round
built from them meets it with constants and nothing else. -/
def augRoundBudget (kn ka kf kt kc : ℕ) {N : ℕ} (D : Orientation N) : ℕ :=
  kn * N + ka * arcCount D + kf * fratPairCount D + kt * transPairCount D + kc

/-- **The symmetrization's budget shape** — `finalCharge`'s: a scan of
the carrier and a constant per arc of the final orientation (each arc
becomes two adjacency entries). -/
def augSymBudget (sn sa sc : ℕ) {N : ℕ} (D : Orientation N) : ℕ :=
  sn * N + sa * arcCount D + sc

/-- **The whole augmentation pass's budget**: base, the `R` rounds
(with `comIter`'s own `skip` step), symmetrization — each at its own
shape, read at the chain's own orientations. This is the `Kag` of §4's
conclusion, and §2's two theorems are the whole of its cost claim. -/
noncomputable def augChainCost (bn ba bc kn ka kf kt kc sn sa sc : ℕ)
    {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m)) (R : ℕ) : ℕ :=
  augBaseBudget bn ba bc (selChain sel G 0)
    + (1 + ∑ i ∈ Finset.range R, augRoundBudget kn ka kf kt kc (selChain sel G i))
    + augSymBudget sn sa sc (selChain sel G R)

/-- **The composed budget is `selChainCharge`, up to constants.** Once
every constant is bounded by `k` times the coefficient `levelCharge`
(resp. `selBaseCharge`, `finalCharge`) already gives that count, the
whole pass costs at most `k` times the landed charge plus `O(R)`.

This is the sense in which the split invents no cost: the only figures
that appear are `arcCount`, `fratPairCount` and `transPairCount`, at
the chain's own orientations, and `exists_selChainCharge_le` already
closes their total inside `f·m^{1+δ}`. -/
theorem augChainCost_le_selChainCharge (bn ba bc kn ka kf kt kc sn sa sc k : ℕ)
    {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m)) (R : ℕ)
    (hbn : bn ≤ k) (hba : ba ≤ 3 * k) (hkn : kn ≤ 3 * k) (hka : ka ≤ 2 * k)
    (hkf : kf ≤ 4 * k) (hkt : kt ≤ 2 * k) (hsn : sn ≤ 3 * k) (hsa : sa ≤ 5 * k) :
    augChainCost bn ba bc kn ka kf kt kc sn sa sc sel G R
      ≤ k * selChainCharge sel G R + (bc + sc + 1 + R * kc) := by
  have hround : ∀ i, augRoundBudget kn ka kf kt kc (selChain sel G i)
      ≤ k * levelCharge (selChain sel G i) + kc := by
    intro i
    have h1 : kn * m ≤ (3 * k) * m := Nat.mul_le_mul_right m hkn
    have h2 : ka * arcCount (selChain sel G i) ≤ (2 * k) * arcCount (selChain sel G i) :=
      Nat.mul_le_mul_right _ hka
    have h3 : kf * fratPairCount (selChain sel G i)
        ≤ (4 * k) * fratPairCount (selChain sel G i) := Nat.mul_le_mul_right _ hkf
    have h4 : kt * transPairCount (selChain sel G i)
        ≤ (2 * k) * transPairCount (selChain sel G i) := Nat.mul_le_mul_right _ hkt
    have hlev : k * levelCharge (selChain sel G i)
        = (3 * k) * m + (2 * k) * arcCount (selChain sel G i)
          + (4 * k) * fratPairCount (selChain sel G i)
          + (2 * k) * transPairCount (selChain sel G i) := by
      rw [levelCharge]; ring
    rw [augRoundBudget, hlev]
    omega
  have hsum : (∑ i ∈ Finset.range R, augRoundBudget kn ka kf kt kc (selChain sel G i))
      ≤ ∑ i ∈ Finset.range R, (k * levelCharge (selChain sel G i) + kc) :=
    Finset.sum_le_sum fun i _ => hround i
  have hsplit : (∑ i ∈ Finset.range R, (k * levelCharge (selChain sel G i) + kc))
      = k * (∑ i ∈ Finset.range R, levelCharge (selChain sel G i)) + R * kc := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range,
      smul_eq_mul]
  have hbase : augBaseBudget bn ba bc (selChain sel G 0)
      ≤ k * selBaseCharge sel G + bc := by
    have h1 : bn * m ≤ k * m := Nat.mul_le_mul_right m hbn
    have h2 : ba * arcCount (selChain sel G 0) ≤ (3 * k) * arcCount (selChain sel G 0) :=
      Nat.mul_le_mul_right _ hba
    have hb : k * selBaseCharge sel G
        = k * m + (3 * k) * arcCount (selChain sel G 0) := by
      rw [selBaseCharge]; ring
    rw [augBaseBudget, hb]
    omega
  have hsym : augSymBudget sn sa sc (selChain sel G R)
      ≤ k * finalCharge (selChain sel G R) + sc := by
    have h1 : sn * m ≤ (3 * k) * m := Nat.mul_le_mul_right m hsn
    have h2 : sa * arcCount (selChain sel G R) ≤ (5 * k) * arcCount (selChain sel G R) :=
      Nat.mul_le_mul_right _ hsa
    have hf : k * finalCharge (selChain sel G R)
        = (3 * k) * m + (5 * k) * arcCount (selChain sel G R) := by
      rw [finalCharge]; ring
    rw [augSymBudget, hf]
    omega
  have hchg : k * selChainCharge sel G R
      = k * selBaseCharge sel G
        + k * (∑ i ∈ Finset.range R, levelCharge (selChain sel G i))
        + k * finalCharge (selChain sel G R) := by
    rw [selChainCharge]; ring
  rw [augChainCost, hchg]
  omega

/-- **The composed budget closes inside §7's envelope, one δ to
spare.** On a nowhere dense class the whole augmentation pass —
base, `R` rounds, symmetrization, at the shapes above — costs at most
`f·m^{1+δ} + O(R)` on every subgraph copy of every member, with `f`
fixed before the graph. The interface asks for `m^{1+2δ}`.

Nothing is proved here that was not proved in wave 25: this is
`exists_selChainCharge_le` composed with the previous theorem, and it
is stated so that the shapes of §2 are visibly *consumers* of the
landed charge rather than a second cost account. -/
theorem exists_augChainCost_le (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (R : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (bn ba bc kn ka kf kt kc sn sa sc k : ℕ)
    (hbn : bn ≤ k) (hba : ba ≤ 3 * k) (hkn : kn ≤ 3 * k) (hka : ka ≤ 2 * k)
    (hkf : kf ≤ 4 * k) (hkt : kt ≤ 2 * k) (hsn : sn ≤ 3 * k) (hsa : sa ≤ 5 * k) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        (augChainCost bn ba bc kn ka kf kt kc sn sa sc (sel m) G R : ℝ)
          ≤ f * (m : ℝ) ^ (1 + δ) + (bc + sc + 1 + R * kc : ℕ) := by
  obtain ⟨f, hf0, hf⟩ := exists_selChainCharge_le sel C hC R δ hδ
  refine ⟨(k : ℝ) * f, by positivity, fun n Gn hGn m G hsub => ?_⟩
  have hN := augChainCost_le_selChainCharge bn ba bc kn ka kf kt kc sn sa sc k
    (sel m) G R hbn hba hkn hka hkf hkt hsn hsa
  have hR : ((augChainCost bn ba bc kn ka kf kt kc sn sa sc (sel m) G R : ℕ) : ℝ)
      ≤ ((k * selChainCharge (sel m) G R + (bc + sc + 1 + R * kc) : ℕ) : ℝ) := by
    exact_mod_cast hN
  refine hR.trans ?_
  have hcharge := hf n Gn hGn m G hsub
  push_cast
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [hcharge, hk0]

/-! ## §3 The three named residuals

All three are stated at `CovAugAdjSelIn`'s own parameters, clause for
clause, so that §4's composition is a `Spec.seq` and nothing else. The
orientation the machine currently holds is the abstract region
`AugSt j A D`; the working allocations the rounds need are `Srd j`,
established by the base pass, preserved by every round, consumed by the
symmetrization. `Smp` (the final peel's scratch) and `Ssw` (the sweep's)
are preserved throughout, exactly as `CovAugAdjSelIn` demands. -/

/-- **Residual (5a-i): the base pass.** From `CovAugAdjSelIn`'s exact
precondition, leave the machine holding round `0` of the chain —
`selChain (sel A.N) A.G 0`, which is `baseOr A.G (selPerm (sel A.N) A.G)`
(§0) — together with the rounds' working allocations `Srd`.

§5 splits it: build the deletable region of `A.G` from the arena's own
CSR (`AugBaseAdjIn`, **discharged** at `bldAdjCom`), peel that region
into the rank array at the *linear* contract (`AugBasePeelIn`), orient
along the ranks (`AugBaseOrientIn`). -/
def AugBaseIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String)
    (AugSt : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Orientation A.N → Env → Prop)
    (Sag Srd Smp Ssw : ℕ → Env → Prop) (bsC : ℕ → Com) (bn ba bc : ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Sag j σ ∧ Smp j σ ∧ Ssw j σ)
        (bsC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          AugSt j A (selChain (sel A.N) A.G 0) σ' ∧ Srd j σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
        (augBaseBudget bn ba bc (selChain (sel A.N) A.G 0))

/-- **Residual (5a-ii): one augmentation round** — the siblings' pass
(F6c12-5b's fraternal CSR, 5c-i's transitive region, 5c-ii's emit).
From the machine holding `selChain (sel A.N) A.G i`, leave it holding
`greedyStep (selRank (sel A.N) (fratGraph …)) …` — written out rather
than as `selChain … (i + 1)`, because that is the identity the emit
proves (`§0 selChain_succ` is what makes the two the same). The round's
own allocations `Srd` are preserved, so the next round can run.

Indexed by `i < R` rather than universally quantified over
orientations: a round pass needs its candidate counts to be words, and
that is available for the chain's own orientations (from admissibility
and `x ∈ mcD n G c w`) and for no others.

The budget is `augRoundBudget`'s pinned shape at the *current* round's
counts — the trap the split exists for: a peel of `fratGraph D` inside
the round must be linear, or the `R + 1` peels of the pass multiply. -/
def AugRoundIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String)
    (AugSt : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Orientation A.N → Env → Prop)
    (Srd Smp Ssw : ℕ → Env → Prop) (rdC : ℕ → Com) (kn ka kf kt kc : ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      ∀ i, i < R →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          AugSt j A (selChain (sel A.N) A.G i) σ ∧ Srd j σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
        (rdC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          AugSt j A (greedyStep
            (selRank (sel A.N) (fratGraph (selChain (sel A.N) A.G i)))
            (selChain (sel A.N) A.G i)) σ' ∧ Srd j σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
        (augRoundBudget kn ka kf kt kc (selChain (sel A.N) A.G i))

/-- **Residual (5a-iii): the symmetrization.** From the machine holding
the final orientation `selChain (sel A.N) A.G R`, leave
`CovAugAdjSelIn`'s own postcondition: the deletable adjacency region of
the *symmetrized* augmented graph `(selChain (sel A.N) A.G R).toGraph`
at the empty deleted set, in the four output names, with the arena, the
two allocations and both scratch descriptors intact.

§5 splits it into the transpose-and-merge residual `AugSymCsrIn` and the
landed build `bldAdjCom` (`augSymIn_of_symCsr_build`). -/
def AugSymIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (AugSt : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Orientation A.N → Env → Prop)
    (Srd Smp Ssw : ℕ → Env → Prop) (syC : ℕ → Com) (sn sa sc : ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          AugSt j A (selChain (sel A.N) A.G R) σ ∧ Srd j σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
        (syC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          DelAdjSt (aoO j) (ajO j) (dgO j) (mtO j)
            (selChain (sel A.N) A.G R).toGraph ∅ σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
        (augSymBudget sn sa sc (selChain (sel A.N) A.G R))

/-! ## §4 The augmentation pass, composed

The `R`-round induction. `spec_comIter` carries the indexed predicate
"the machine holds `selChain (sel A.N) A.G i`, and the rounds' working
allocations, and everything `CovAugAdjSelIn` preserves" from `i = 0`
to `i = R`; the base pass establishes it at `0` and the symmetrization
consumes it at `R`. -/

open Classical in
/-- **The augmentation pass** — `CovAugAdjSelIn` (wave 25) concluded
**verbatim** from the three residuals, at

* the program `bsC j ; (rdC j)^R ; syC j` (`comIter` unrolls the rounds,
  `R` being a constant of the construction),
* the augmentation's scratch descriptor `Sag` (the base's; the rounds'
  `Srd` is produced and consumed inside the pass, so it does not
  appear),
* the budget `augChainCost` — the three pinned shapes summed at the
  chain's own orientations, which §2 bounds by `k·selChainCharge + O(R)`
  and hence by `f·m^{1+δ} + O(R)` on a nowhere dense class.

The proof is `Spec.seq` twice around `spec_comIter`; the only step with
content is the round's, where the emit's postcondition
`greedyStep (selRank … (fratGraph …)) …` is recognised as
`selChain (sel A.N) A.G (i+1)` by §0's `selChain_succ`. -/
theorem covAugAdjSelIn_of_base_rounds_sym (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (AugSt : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Orientation A.N → Env → Prop)
    (Sag Srd Smp Ssw : ℕ → Env → Prop) (bsC rdC syC : ℕ → Com)
    (bn ba bc kn ka kf kt kc sn sa sc : ℕ)
    (hbs : AugBaseIn C hC φ sel G c w q ℓp htabF hbf Adm ca co AugSt
      Sag Srd Smp Ssw bsC bn ba bc)
    (hrd : AugRoundIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co AugSt
      Srd Smp Ssw rdC kn ka kf kt kc)
    (hsy : AugSymIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      aoO ajO dgO mtO AugSt Srd Smp Ssw syC sn sa sc) :
    CovAugAdjSelIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      aoO ajO dgO mtO Sag Smp Ssw
      (fun j => .seq (.seq (bsC j) (comIter (rdC j) R)) (syC j))
      (fun _j A => augChainCost bn ba bc kn ka kf kt kc sn sa sc
        (sel A.N) A.G R) := by
  intro x hx j hj A hAdm hbot
  -- the loop's indexed predicate is `AugBaseIn`'s postcondition, `AugRoundIn`'s
  -- pre- and postcondition and `AugSymIn`'s precondition, all at once, so the
  -- two `Spec.seq`s below need no reshaping at either seam
  have hrounds : Spec (mcB q x)
      (fun σ => ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A)) σ ∧
        AugSt j A (selChain (sel A.N) A.G 0) σ ∧ Srd j σ ∧
        A.N ≤ (σ.arrs (ca j)).length ∧
        A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
      (comIter (rdC j) R)
      (fun _ σ' => ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A)) σ' ∧
        AugSt j A (selChain (sel A.N) A.G R) σ' ∧ Srd j σ' ∧
        A.N ≤ (σ'.arrs (ca j)).length ∧
        A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
      (1 + ∑ i ∈ Finset.range R,
        augRoundBudget kn ka kf kt kc (selChain (sel A.N) A.G i)) := by
    refine spec_comIter
      (P := fun i σ =>
        ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A)) σ ∧
          AugSt j A (selChain (sel A.N) A.G i) σ ∧ Srd j σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
      (K := fun i => augRoundBudget kn ka kf kt kc (selChain (sel A.N) A.G i))
      R (fun i hi => ?_)
    refine (hrd x hx j hj A hAdm hbot i hi).post ?_
    rintro σ σ' - hq
    simp only [selChain_succ]
    exact hq
  exact Spec.seq
    (Spec.seq (hbs x hx j hj A hAdm hbot) hrounds
      (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq' => hq'))
    (hsy x hx j hj A hAdm hbot) (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq' => hq')

/-- **The landed residual, verbatim.** At the pinned selection the
composition concludes `CovAugAdjIn` (`SolveSweepOrder.lean:413`) itself,
through wave 25's `covAugAdjSelIn_mdSel` — the two `Prop`s coincide at
`sel = mdSel`, clause for clause, so nothing is weakened by stating the
frame at a freed tie-break. -/
theorem covAugAdjIn_of_base_rounds_sym (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (AugSt : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Orientation A.N → Env → Prop)
    (Sag Srd Smp Ssw : ℕ → Env → Prop) (bsC rdC syC : ℕ → Com)
    (bn ba bc kn ka kf kt kc sn sa sc : ℕ)
    (hbs : AugBaseIn C hC φ (fun m => mdSel m) G c w q ℓp htabF hbf Adm ca co
      AugSt Sag Srd Smp Ssw bsC bn ba bc)
    (hrd : AugRoundIn C hC φ (fun m => mdSel m) R G c w q ℓp htabF hbf Adm ca co
      AugSt Srd Smp Ssw rdC kn ka kf kt kc)
    (hsy : AugSymIn C hC φ (fun m => mdSel m) R G c w q ℓp htabF hbf Adm ca co
      aoO ajO dgO mtO AugSt Srd Smp Ssw syC sn sa sc) :
    CovAugAdjIn C hC φ R G c w q ℓp htabF hbf Adm ca co
      aoO ajO dgO mtO Sag Smp Ssw
      (fun j => .seq (.seq (bsC j) (comIter (rdC j) R)) (syC j))
      (fun _j A => augChainCost bn ba bc kn ka kf kt kc sn sa sc
        (mdSel A.N) A.G R) :=
  (covAugAdjSelIn_mdSel C hC φ R G c w q ℓp htabF hbf Adm ca co
    aoO ajO dgO mtO Sag Smp Ssw _ _).mp
    (covAugAdjSelIn_of_base_rounds_sym C hC φ (fun m => mdSel m) R G c w q ℓp
      htabF hbf Adm ca co aoO ajO dgO mtO AugSt Sag Srd Smp Ssw bsC rdC syC
      bn ba bc kn ka kf kt kc sn sa sc hbs hrd hsy)

/-! ## §5 The symmetrization, opened up: a transpose and the landed build

`AugSymIn` is a transpose-and-merge followed by `bldAdjCom`. The second
half is a **landed program** and applies here *directly*: the CSR the
transpose leaves is in fresh arrays, so `adjBuildAt_bldAdjCom`'s
`GraphCsr` precondition is met on the nose — none of the windowed-arena
plumbing `covAdjBuildIn_bldCom` needs is required. What is left named is
the transpose. -/

/-- **The transpose-and-merge residual.** From the machine holding the
final orientation, leave an ordinary `GraphCsr` of its symmetrization
`(selChain (sel A.N) A.G R).toGraph` in the fresh pair `(soO j, stO j)`,
its two figures in the fresh cells `(nNy j, nSy j)` and inside the word
bound, and the four output regions allocated for the build that follows.

The slot count is asked for only as `≤ 2·arcCount` — the windowed
convention — which is all the budget needs: the symmetrization of an
orientation has exactly two adjacency slots per arc, and a discharger
proving equality proves this a fortiori. -/
def AugSymCsrIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (nNy nSy soO stO : ℕ → String)
    (aoO ajO dgO mtO : ℕ → String)
    (AugSt : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Orientation A.N → Env → Prop)
    (Srd Smp Ssw : ℕ → Env → Prop) (tpC : ℕ → Com) (tn ta tc : ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          AugSt j A (selChain (sel A.N) A.G R) σ ∧ Srd j σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
        (tpC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          (∃ ns : ℕ,
            GraphCsr (soO j) (stO j) (selChain (sel A.N) A.G R).toGraph ns σ' ∧
            σ'.vars (nNy j) = A.N ∧ σ'.vars (nSy j) = ns ∧
            A.N < mcB q x ∧ ns < mcB q x ∧
            ns ≤ 2 * arcCount (selChain (sel A.N) A.G R) ∧
            A.N + 1 ≤ (σ'.arrs (aoO j)).length ∧
            ns ≤ (σ'.arrs (ajO j)).length ∧
            A.N ≤ (σ'.arrs (dgO j)).length ∧
            ns ≤ (σ'.arrs (mtO j)).length) ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
        (tn * A.N + ta * arcCount (selChain (sel A.N) A.G R) + tc)

open Classical in
/-- **`AugSymIn`, from the transpose and the landed build.** The pass is
`tpC j ; bldAdjCom …`, and its budget is `augSymBudget`'s shape at
`(tn + 81, ta + 116, tc + 24)`: `adjBuildAt_bldAdjCom` charges
`81·N + 58·ns + 24`, and `ns ≤ 2·arcCount` turns the slot term into
`116·arcCount`. No `N²` anywhere.

Everything asked of the caller is of the F7-suppliable kind: the build
pass's own region discipline (`BldNames`, `BldCells` — the same
hypotheses `covAdjBuildIn_bldCom` takes), that the four output regions
are not the arena's five arrays, and the two scratch descriptors'
transport across the build's writes. -/
theorem augSymIn_of_symCsr_build (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (nNy nSy soO stO raY odY : ℕ → String)
    (aoO ajO dgO mtO : ℕ → String)
    (AugSt : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Orientation A.N → Env → Prop)
    (Srd Smp Ssw : ℕ → Env → Prop) (tpC : ℕ → Com) (tn ta tc : ℕ)
    (hnm : ∀ j, BldNames (soO j) (stO j) (raY j) (aoO j) (ajO j) (dgO j)
      (mtO j) (odY j))
    (hcl : ∀ j, BldCells (nNy j) (nSy j))
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ aoO j ∧ b ≠ ajO j ∧ b ≠ dgO j ∧ b ≠ mtO j)
    (hSmp : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b, b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ bldScalars → σ'.vars y = σ.vars y) → Smp j σ')
    (hSsw : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b, b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ bldScalars → σ'.vars y = σ.vars y) → Ssw j σ')
    (htp : AugSymCsrIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      nNy nSy soO stO aoO ajO dgO mtO AugSt Srd Smp Ssw tpC tn ta tc) :
    AugSymIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co aoO ajO dgO mtO
      AugSt Srd Smp Ssw
      (fun j => .seq (tpC j)
        (bldAdjCom (nNy j) (nSy j) (soO j) (stO j)
          (aoO j) (ajO j) (dgO j) (mtO j)))
      (tn + 81) (ta + 116) (tc + 24) := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨σ₁, hrun1, hA1, ⟨ns, hcsr1, hnN1, hnS1, hNB, hnsB, hnsle,
    haoL, hajL, hdgL, hmtL⟩, hca1, hco1, hSmp1, hSsw1⟩ :=
    (htp x hx j hj A hAdm hbot) σ hσ
  -- the landed build, framed
  obtain ⟨σ₂, hrun2, ⟨⟨-, hdel2⟩, hfv, hfa, -, -⟩, hlen⟩ :=
    (specArrsLength
      (adjBuildAt_bldAdjCom (nN := nNy j) (nS := nSy j) (o := soO j) (t := stO j)
        (ra := raY j) (ao := aoO j) (aj := ajO j) (dg := dgO j) (mt := mtO j)
        (od := odY j) (B := mcB q x) (hnm j) (hcl j)
        ((selChain (sel A.N) A.G R).toGraph) ns).frame).run
      ⟨hcsr1, hnN1, hnS1, hNB, hnsB, haoL, hajL, hdgL, hmtL⟩
  -- the frame, in the two shapes the transports consume
  have hfa' : ∀ b, b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
      σ₂.arrs b = σ₁.arrs b :=
    fun b h1 h2 h3 h4 => hfa b (not_mem_warrs_bldAdjCom h1 h2 h3 h4)
  have hfv' : ∀ y, y ∉ bldScalars → σ₂.vars y = σ₁.vars y := by
    intro y hy
    simp only [bldScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hy
    exact hfv y (not_mem_wvars_bldAdjCom h0 h1 h2 h3 h4 h5)
  have hclj := bldCells_arenaNames j
  have hvN : σ₂.vars (arenaNames j).nN = σ₁.vars (arenaNames j).nN :=
    hfv' _ hclj.nN_notMem
  have hvS : σ₂.vars (arenaNames j).nS = σ₁.vars (arenaNames j).nS :=
    hfv' _ hclj.nS_notMem
  obtain ⟨ho1, ho2, ho3, ho4⟩ := harn j (arenaNames j).off (Or.inl rfl)
  obtain ⟨ht1, ht2, ht3, ht4⟩ := harn j (arenaNames j).tgt (Or.inr (Or.inl rfl))
  obtain ⟨hc1, hc2, hc3, hc4⟩ :=
    harn j (arenaNames j).col (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨hu1, hu2, hu3, hu4⟩ :=
    harn j (arenaNames j).up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨hh1, hh2, hh3, hh4⟩ :=
    harn j (arenaNames j).hist (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  refine ⟨σ₂, (hrun1.seq hrun2).mono ?_, ?_, hdel2, ?_, ?_, ?_, ?_⟩
  · -- the budget: `58·ns ≤ 116·arcCount`
    have h58 : 58 * ns ≤ 116 * arcCount (selChain (sel A.N) A.G R) := by
      calc 58 * ns ≤ 58 * (2 * arcCount (selChain (sel A.N) A.G R)) :=
            Nat.mul_le_mul_left _ hnsle
        _ = 116 * arcCount (selChain (sel A.N) A.G R) := by ring
    simp only [augSymBudget, add_mul]
    omega
  · exact arenaStW_of_eq hA1 hvN hvS (hfa' _ ho1 ho2 ho3 ho4)
      (hfa' _ ht1 ht2 ht3 ht4) (hfa' _ hc1 hc2 hc3 hc4)
      (hfa' _ hu1 hu2 hu3 hu4) (hfa' _ hh1 hh2 hh3 hh4)
  · rw [hlen (ca j)]; exact hca1
  · rw [hlen (co j)]; exact hco1
  · exact hSmp j σ₁ σ₂ hSmp1 hfa' hfv'
  · exact hSsw j σ₁ σ₂ hSsw1 hfa' hfv'

/-! ## §6 The base pass, opened up: build, peel, orient

Round `0` is `baseOr A.G (selPerm (sel A.N) A.G)` (§0), so the base pass
is three: materialize `A.G`'s deletable region from the arena's own CSR,
peel that region into the rank array, then orient each edge from its
rank-smaller to its rank-larger end and hand the result to the rounds.

All three budgets are stated at `arcCount (selChain (sel A.N) A.G 0)`,
which is the **edge count of `A.G`** — round `0` orients `A.G`
(`baseOr_orients`), so its arcs are exactly `A.G`'s edges. A pass
walking the CSR does `2·arcCount (selChain (sel A.N) A.G 0)` slot turns;
that factor of two is inside the free constant.

The middle one is the campaign's known trap. The augmentation runs a
peel `R + 1` times — once here on `A.G`, once per round on
`fratGraph (selChain …)` — so a peel charged `Θ(N²)` multiplies by
`R + 1` and breaks §7's envelope at the root. `AugBasePeelIn` is
therefore stated at the **linear** shape only, the one F6c13c
(`SolveSweepBucketProg`) is built for; the landed quadratic `peelCom`
(`covSelPeelIn_peelCom_mdSel`, `86·N² + 43·N + 14`) does *not* meet it,
and that is deliberate. -/

/-- **The base's region build** — the arena's CSR of `A.G` into a
deletable adjacency region at the empty deleted set, plus the base's own
scratch `Sbd`. This is `covAdjBuildIn_bldCom`'s content minus the rank
inversion (the rank array does not exist yet at this point of the pass),
i.e. `bldAdjCom` read through the arena's window. -/
def AugBaseAdjIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (bao baj bdg bmt : ℕ → String)
    (Sag Sbd Smp Ssw : ℕ → Env → Prop) (adjC : ℕ → Com) (b₁n b₁a b₁c : ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Sag j σ ∧ Smp j σ ∧ Ssw j σ)
        (adjC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          DelAdjSt (bao j) (baj j) (bdg j) (bmt j) A.G ∅ σ' ∧ Sbd j σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
        (b₁n * A.N + b₁a * arcCount (selChain (sel A.N) A.G 0) + b₁c)

/-- **The base's peel, at the linear contract.** From the region of
`A.G`, leave `RankArr` at `selPerm (sel A.N) A.G` — the selection's
elimination ranking of `A.G` itself, which is what round `0`'s
orientation is taken along — **without writing the adjacency arrays**,
so the region survives for the orientation pass to read.

The budget carries no `A.N * A.N` term. That is the whole point: this
peel runs once per augmentation and the round's peel of
`fratGraph (selChain …)` runs `R` more times. -/
def AugBasePeelIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (bao baj bdg bmt bra : ℕ → String)
    (Sbd Smp Ssw : ℕ → Env → Prop) (plC : ℕ → Com) (b₂n b₂a b₂c : ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          DelAdjSt (bao j) (baj j) (bdg j) (bmt j) A.G ∅ σ ∧ Sbd j σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
        (plC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          DelAdjSt (bao j) (baj j) (bdg j) (bmt j) A.G ∅ σ' ∧
          RankArr (bra j) (selPerm (sel A.N) A.G) σ' ∧ Sbd j σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
        (b₂n * A.N + b₂a * arcCount (selChain (sel A.N) A.G 0) + b₂c)

/-- **The base's orientation.** From the region of `A.G` and its rank
array, leave the machine holding `baseOr A.G (selPerm (sel A.N) A.G)` —
each edge oriented from its rank-smaller to its rank-larger end — in
whatever region the rounds read (`AugSt`), together with the rounds'
working allocations `Srd`. One pass over the slot space. -/
def AugBaseOrientIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (bao baj bdg bmt bra : ℕ → String)
    (AugSt : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Orientation A.N → Env → Prop)
    (Sbd Srd Smp Ssw : ℕ → Env → Prop) (orC : ℕ → Com) (b₃n b₃a b₃c : ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          DelAdjSt (bao j) (baj j) (bdg j) (bmt j) A.G ∅ σ ∧
          RankArr (bra j) (selPerm (sel A.N) A.G) σ ∧ Sbd j σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
        (orC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          AugSt j A (baseOr A.G (selPerm (sel A.N) A.G)) σ' ∧ Srd j σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
        (b₃n * A.N + b₃a * arcCount (selChain (sel A.N) A.G 0) + b₃c)

open Classical in
/-- **`AugBaseIn`, from its three passes.** The program is
`adjC j ; plC j ; orC j`, the budget the sum of the three shapes — which
is again `augBaseBudget`'s shape, since the shape is closed under
addition of its constants. The only step with content is the last:
`AugBaseOrientIn` leaves `baseOr A.G (selPerm (sel A.N) A.G)` and
`AugBaseIn` asks for `selChain (sel A.N) A.G 0`, and §0's
`selChain_zero` says these are the same orientation. -/
theorem augBaseIn_of_adj_peel_orient (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (bao baj bdg bmt bra : ℕ → String)
    (AugSt : (j : ℕ) → (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Orientation A.N → Env → Prop)
    (Sag Sbd Srd Smp Ssw : ℕ → Env → Prop) (adjC plC orC : ℕ → Com)
    (b₁n b₁a b₁c b₂n b₂a b₂c b₃n b₃a b₃c : ℕ)
    (hadj : AugBaseAdjIn C hC φ sel G c w q ℓp htabF hbf Adm ca co
      bao baj bdg bmt Sag Sbd Smp Ssw adjC b₁n b₁a b₁c)
    (hpl : AugBasePeelIn C hC φ sel G c w q ℓp htabF hbf Adm ca co
      bao baj bdg bmt bra Sbd Smp Ssw plC b₂n b₂a b₂c)
    (hor : AugBaseOrientIn C hC φ sel G c w q ℓp htabF hbf Adm ca co
      bao baj bdg bmt bra AugSt Sbd Srd Smp Ssw orC b₃n b₃a b₃c) :
    AugBaseIn C hC φ sel G c w q ℓp htabF hbf Adm ca co AugSt
      Sag Srd Smp Ssw
      (fun j => .seq (.seq (adjC j) (plC j)) (orC j))
      (b₁n + b₂n + b₃n) (b₁a + b₂a + b₃a) (b₁c + b₂c + b₃c) := by
  intro x hx j hj A hAdm hbot
  have hlast : Spec (mcB q x)
      (fun σ => ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A)) σ ∧
        DelAdjSt (bao j) (baj j) (bdg j) (bmt j) A.G ∅ σ ∧
        RankArr (bra j) (selPerm (sel A.N) A.G) σ ∧ Sbd j σ ∧
        A.N ≤ (σ.arrs (ca j)).length ∧
        A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
      (orC j)
      (fun _ σ' => ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A)) σ' ∧
        AugSt j A (selChain (sel A.N) A.G 0) σ' ∧ Srd j σ' ∧
        A.N ≤ (σ'.arrs (ca j)).length ∧
        A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
      (b₃n * A.N + b₃a * arcCount (selChain (sel A.N) A.G 0) + b₃c) := by
    refine (hor x hx j hj A hAdm hbot).post ?_
    rintro σ σ' - hq
    simp only [selChain_zero]
    exact hq
  refine (Spec.seq
    (Spec.seq (hadj x hx j hj A hAdm hbot) (hpl x hx j hj A hAdm hbot)
      (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq' => hq'))
    hlast (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq' => hq')).mono ?_
  simp only [augBaseBudget, add_mul]
  omega

/-! ## §7 The canonical orientation region

Nothing above depends on how the machine carries the current
orientation — `AugSt` is a parameter throughout. This section records
the instance the siblings' passes actually work at, so that the
parameter is visibly inhabited by the region the round body consumes
and rebuilds rather than by an arbitrary predicate. -/

/-- **The in-neighbour CSR as an orientation region.** `InNCsr`
(`SolveAugFrat.lean:144`) is the precondition of *both* enumerations —
`FratCsrAt` and `TransCsrIn` read a CSR of `D`'s in-neighbourhoods — and
the emit rebuilds one, so it is the natural instantiation of `AugSt`.
Its slot count is not a free parameter: `InNCsr.ns_eq` forces it to be
`arcCount D`, which is exactly the figure `augRoundBudget`'s second term
is stated at, so the round's `ka·arcCount D` really is "a constant per
slot of the region it is handed". The scalar `nA j` carries that count
for the pass to read. -/
def augStInN (io it nA : ℕ → String) (j : ℕ) {Λ n₀ : ℕ} (A : Arena Λ n₀)
    (D : Orientation A.N) (σ : Env) : Prop :=
  InNCsr (io j) (it j) D (arcCount D) σ ∧ σ.vars (nA j) = arcCount D

/-- The region determines its own width: any slot count an `InNCsr` of
`D` is stated at is `arcCount D`, so `augStInN` loses nothing by pinning
it. -/
theorem augStInN_ns {io it nA : ℕ → String} {j : ℕ} {Λ n₀ : ℕ}
    {A : Arena Λ n₀} {D : Orientation A.N} {ns : ℕ} {σ : Env}
    (h : InNCsr (io j) (it j) D ns σ) (hn : σ.vars (nA j) = ns) :
    augStInN io it nA j A D σ := by
  obtain rfl := h.ns_eq
  exact ⟨h, hn⟩

/-! ## §8 Axiom audit

Everything in §0–§2 and §5–§6 rests on the three standard axioms alone.
§4's two composition theorems quote `Headline.headlineSetup` in their
statements and therefore — exactly like the landed
`covOrderIn_of_aug_selPeel` and `covOrderIn_bucket` they feed —
additionally carry Lax12's endorsed
`uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms selChain_zero

#print axioms selChain_succ

#print axioms spec_comIter

#print axioms augChainCost_le_selChainCharge

#print axioms exists_augChainCost_le

#print axioms covAugAdjSelIn_of_base_rounds_sym

#print axioms covAugAdjIn_of_base_rounds_sym

#print axioms augSymIn_of_symCsr_build

#print axioms augBaseIn_of_adj_peel_orient

#print axioms augStInN_ns

end Lax3Proofs.Prog
