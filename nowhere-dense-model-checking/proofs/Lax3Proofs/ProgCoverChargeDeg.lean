import Lax3Proofs.ProgCoverChargeSel
import Lax3Proofs.SolveSweepPeel
import Lax3Proofs.SolveSweepBucketProg

/-!
# F5b, degree-export fix — the cover cost constant, tied to its degree property

## The gap this leaf closes

`SolveChain.KsChargeBridge` (`SolveChain.lean:705`) prices the solve
budget against `chargeTotal (mcChargeMS S ord ℓp htabF covC G …)`.  Its
**cover-sweep column** is a `peelK`-shaped budget, and the only landed
route from a `peelK` to a ledger entry is
`peelBudget_le_sweepCharge` (`SolveSweepPeel.lean:667`), whose
hypotheses are

* `1 ≤ S.R` — supplied by `Setup.one_le_R`;
* `1 ≤ D`;
* `hD : ∀ x, (wreach A.G π (2·S.R) x).ncard ≤ D`,

at `D := ⌈cf·A.N^δ⌉₊`, the very degree parameter the cover family
`coverCFSel` names.

The landed export `exists_mcChargeMS_T_selOrdering`
(`ProgCoverChargeSel.lean:911`) hands the consumer that `cf` behind an
`∃` carrying **only `0 ≤ cf`**.  The degree fact is nowhere in the
statement.  Reading the proofs rather than the docstrings:

* `exists_mcChargeMS_chargeTotal_le_sel` (`:697`) obtains `cdeg` from
  `exists_wreach_degree_selOrderingRoutine` (`:713`) and `cs` from
  `exists_coverChargeSel_le` (`:715`), and returns `cs`.  As *stated*,
  the two are unrelated opaque constants.
* `Impl.sweepCharge G π r D = ∑ v (|X_v|·D + ∑_{w ∈ N_>(v)} d_<(w))`
  (`ImplCover.lean:470`) is **monotone increasing in `D`**, so a charge
  bound proved at one `D` never transfers up to a larger one.  No
  monotonicity argument can recover the missing hypothesis, and no
  `max`-style repair is free: enlarging the constant to cover the
  degree side re-opens the charge side.

So the consumer is stuck with a `cf` it cannot feed to
`peelBudget_le_sweepCharge`.  This is exactly the `exists_fratCsr`
failure mode of this campaign — a true `∃` that drops the property of
its witness the consumer needs.

## Which of the three shapes, and why

The audit named three: take `cf` as an **input** satisfying the degree
bound; **export the degree clause at the same `cf`**; or restate at
`max cdeg cs`.  This file takes the **second**, and the reason is a
fact about the landed proof rather than a preference:
`exists_coverChargeSel_le`'s witness *already is* the degree constant —
its proof opens with `obtain ⟨c, hc0, hdeg⟩ :=
exists_wreach_degree_selOrderingRoutine …` and then `refine ⟨c, …⟩`
(`ProgCoverChargeSel.lean:599-602`).  The theorem is true with the
degree clause attached; it simply does not say so.  Shape 2 therefore
costs one restatement and no new mathematics, and it is the strongest
of the three: shape 1 only relocates the existential onto a consumer
who has no other producer of `cf`, and shape 3 pays a strictly larger
constant while — because of the monotonicity direction above — still
having to re-run the whole charge estimate at `max cdeg cs`.

The engine is nevertheless stated in shape-1 form
(`coverChargeSel_le_of_degree`, `mcChargeMS_chargeTotal_le_sel_of`):
constants in, bound out, no existential.  Shape 2 is then the corollary
that chooses them.  That keeps the witness's identity visible at every
level instead of re-hiding it one layer up.

One extra clause is exported beyond the audit's ask: **`1 ≤ cf`**, not
`0 ≤ cf`.  `peelBudget_le_sweepCharge` also wants `1 ≤ D`, and
`⌈cf·m^δ⌉₊` is `0` when `cf = 0` — which `0 ≤ cf` permits and
`exists_wreach_degree_selOrderingRoutine`'s `max c 0` really can be.
Raising the constant to `max cdeg 1` is sound in both directions here
because the charge estimate is re-run at the raised constant rather
than inherited.

## What closes, and where the exponent stays

`exists_selChainCharge_le`'s true exponent `1+δ` is untouched: the
`1+2δ` used below is `exists_selChainCharge_le_double`, exactly where
the interface already asks for it (the sweep's `2·D·(m·D)` is what
forces it), never in the ordering phase's own bound.

`1 ≤ S.R` (`(★)`'s closing estimate is false at `r = 0`) is taken from
`Setup.one_le_R`, not assumed.

**Vacuity.** `CoverOrderingTime` is cheaply true at `steps := 0`, so
the column below is stated against the *witness*: the ledger vector
`coverCFSel`, whose `"cover.order"` entry is `le_selChainCharge`-bounded
below by the carrier size (`le_chargeTotal_coverCFSel` here) and equals
`timedSelRoutine`'s `steps` (`coverCSel_order_eq_steps`).  The final
column bound `peelK ≤ (a+b+c)·chargeTotal (coverCFSel …)` uses that
lower bound as a load-bearing step, so it cannot be satisfied by a
placeholder charge.

## The routine is the machine's

`covOrderIn_bucketPeel` (`SolveSweepBucketRound.lean:3223`) concludes at
`selOrderingRoutine (fun m => bucketSel m) R` with `R` free, and
`coverCFSel sel S cf δ j A` runs `coverCSel` at `3 * S.R`
(`ProgCoverChargeSel.lean:669`).  At `R := 3 * (headlineSetup C hC φ).R`
and `sel := fun m => bucketSel m` — the selection is *forced* to
`bucketSel` by `augBasePeelIn_bucketPeelBuild` / `covSelPeelIn_bucketPeelCom`,
not chosen — both sides are literally the same routine.  §6 states the
capstone there.

## What this leaf does not do

The column is stated **per node**, like every sibling column of
`KsChargeBridge` (`restrictK_le_childCharge`, `isolateK_le_isolateCharge`,
`profilesK_le`, `scatterK_le`, `botComK_le`).  Getting from a node's
vector to the root total `chargeTotal (mcChargeMS …)` is the bridge's
own bookkeeping over `driverChargeMS`, and it is *not* a monotonicity
step: `driverChargeMS` puts `covC j A` inside `frameChargeMS` only on
the branch `A.G ≠ ⊥` (`ProgCharge.lean:199-212`), while a `⊥` node pays
`botC` and carries no cover vector at all.  So `chargeTotal (covC j A) ≤
chargeTotal (mcChargeMS …)` is false as a blanket statement and has to
follow the recursion's own admissibility, not a `le_add` — which is why
this leaf stops at the node.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Refine
open Lax3.ColoredGraphs
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ShallowMinorDensity
open Lax12.ColoringNumbers
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.AugmentedDensity
open Lax3Proofs.CoverDegree
open Lax3Proofs.CoverRoutine
open Lax3Proofs.CoverEdgeSum
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §0 The finding the fix rests on, as a theorem

The audit's claim that no monotonicity argument recovers the missing
hypothesis, checked rather than asserted. -/

/-- **`Impl.sweepCharge` is monotone *increasing* in the degree
parameter.**  Immediate from `ImplCover.lean:470` — `D` occurs only in
the summand `|X_v| · D`, positively.

This is why the gap cannot be patched downstream.  A cover charge bound
proved at `D = ⌈cs·m^δ⌉₊` says nothing about the charge at
`⌈max cdeg cs · m^δ⌉₊`, so restating at a larger constant obliges one to
re-run the whole charge estimate there (which is what §1 does, at
`max cdeg 1`) — it is never a free consequence of the landed bound. The
degree clause, by contrast, *does* travel upward (`Nat.ceil_mono`),
which is the asymmetry shape 2 exploits. -/
theorem sweepCharge_mono_deg {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (π : Equiv.Perm (Fin m)) (r : ℕ) {D D' : ℕ} (h : D ≤ D') :
    Impl.sweepCharge G π r D ≤ Impl.sweepCharge G π r D' := by
  rw [Impl.sweepCharge, Impl.sweepCharge]
  exact Finset.sum_le_sum fun v _ =>
    Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

/-! ## §1 The engine: the cover charge at a *given* degree constant

`exists_coverChargeSel_le` with both existentials opened.  Constants in,
bound out — so the identity of the constant the sweep is priced at is
visible in the statement, not buried in a witness. -/

open Classical in
/-- **The cover pipeline's charge at a supplied degree constant.**  On
one graph: if `c` bounds every wreach set of the selection routine's
ordering through `⌈c·m^δ⌉₊`, and `f₁` bounds the ordering phase, then
the whole cover charge — ordering plus sweep *at that same `c`* — is at
most `(f₁ + 2(c+1)²)·m^{1+2δ}`.

This is the body of `ProgCoverChargeSel.exists_coverChargeSel_le`
verbatim, with its two `obtain`s turned into hypotheses.  The sweep
enters through `Impl.sweepCharge_le`, whose `2·D·(m·D)` is the term
that forces the `1+2δ`; the ordering phase's own exponent is not
touched. -/
theorem coverChargeSel_le_of_degree (sel : ∀ m : ℕ, MinDegSel m)
    (rc R : ℕ) (hrc : 1 ≤ rc) {δ c f₁ : ℝ} (hδ : 0 < δ) (hc0 : 0 ≤ c)
    {m : ℕ} {G : SimpleGraph (Fin m)}
    (hdeg : ∀ v : Fin m,
      (wreach G ((selOrderingRoutine sel R) m G).order (2 * rc) v).ncard
        ≤ ⌈c * (m : ℝ) ^ δ⌉₊)
    (hchain : (selChainCharge (sel m) G R : ℝ) ≤ f₁ * (m : ℝ) ^ (1 + 2 * δ)) :
    ((selChainCharge (sel m) G R
      + Impl.sweepCharge G ((selOrderingRoutine sel R) m G).order rc
          ⌈c * (m : ℝ) ^ δ⌉₊ : ℕ) : ℝ)
      ≤ (f₁ + 2 * (c + 1) * (c + 1)) * (m : ℝ) ^ (1 + 2 * δ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [selChainCharge_zero, Impl.sweepCharge,
      Real.zero_rpow (show (1 : ℝ) + 2 * δ ≠ 0 by positivity)]
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set Dd : ℕ := ⌈c * (m : ℝ) ^ δ⌉₊ with hDddef
  have hsw : Impl.sweepCharge G ((selOrderingRoutine sel R) m G).order rc Dd
      ≤ 2 * Dd * (m * Dd) := Impl.sweepCharge_le hrc hdeg
  have hX1 : (1 : ℝ) ≤ (m : ℝ) ^ δ := one_le_rpow hm hδ.le
  have hceil : ((Dd : ℕ) : ℝ) ≤ (c + 1) * (m : ℝ) ^ δ := by
    calc ((Dd : ℕ) : ℝ) ≤ c * (m : ℝ) ^ δ + 1 :=
          (Nat.ceil_lt_add_one
            (mul_nonneg hc0 (Real.rpow_nonneg (Nat.cast_nonneg m) δ))).le
      _ ≤ (c + 1) * (m : ℝ) ^ δ := by nlinarith [hX1, hc0]
  have hpow : (m : ℝ) ^ (1 + 2 * δ) = (m : ℝ) * ((m : ℝ) ^ δ * (m : ℝ) ^ δ) := by
    rw [show (1 : ℝ) + 2 * δ = 1 + (δ + δ) by ring, Real.rpow_add hm0, Real.rpow_one,
      Real.rpow_add hm0]
  calc ((selChainCharge (sel m) G R
        + Impl.sweepCharge G ((selOrderingRoutine sel R) m G).order rc Dd : ℕ) : ℝ)
      = (selChainCharge (sel m) G R : ℝ)
        + ((Impl.sweepCharge G ((selOrderingRoutine sel R) m G).order rc Dd : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ f₁ * (m : ℝ) ^ (1 + 2 * δ)
        + 2 * ((c + 1) * (m : ℝ) ^ δ) * ((m : ℝ) * ((c + 1) * (m : ℝ) ^ δ)) := by
        refine add_le_add hchain ?_
        calc ((Impl.sweepCharge G ((selOrderingRoutine sel R) m G).order rc Dd : ℕ) : ℝ)
            ≤ ((2 * Dd * (m * Dd) : ℕ) : ℝ) := by exact_mod_cast hsw
          _ = 2 * ((Dd : ℕ) : ℝ) * ((m : ℝ) * ((Dd : ℕ) : ℝ)) := by push_cast; ring
          _ ≤ 2 * ((c + 1) * (m : ℝ) ^ δ) * ((m : ℝ) * ((c + 1) * (m : ℝ) ^ δ)) := by
              gcongr
    _ = (f₁ + 2 * (c + 1) * (c + 1)) * (m : ℝ) ^ (1 + 2 * δ) := by rw [hpow]; ring

/-! ## §2 Shape 2: the cover charge and the degree clause, at one constant

`exists_coverChargeSel_le` restated so that the constant it exports
carries the wreach-degree bound it was built from — plus `1 ≤ c`, which
`peelBudget_le_sweepCharge`'s `1 ≤ D` needs and `0 ≤ c` does not
give. -/

open Classical in
/-- **The degree-carrying cover charge bound** (the fix, at the cover
level).  On a nowhere dense class, with the radius arithmetic, there
are `c ≥ 1` and `f ≥ 0` — both fixed before any graph — such that on
every subgraph copy of every member, at `D := ⌈c·m^δ⌉₊`,

* every wreach set of the selection routine's ordering has size `≤ D`, **and**
* the whole cover charge, ordering plus sweep at that same `D`, is `≤ f·m^{1+2δ}`.

Compare `exists_coverChargeSel_le`, which proves the same two facts and
exports only the second.  The constant is `max cdeg 1`; the charge half
is re-derived at that constant (§1) rather than inherited, because
`Impl.sweepCharge` grows with `D`. -/
theorem exists_coverChargeSel_le_deg (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (hrc : 1 ≤ rc)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c f : ℝ, 1 ≤ c ∧ 0 ≤ f ∧
      (∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
        ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
          ∀ v : Fin m,
            (wreach G ((selOrderingRoutine sel R) m G).order (2 * rc) v).ncard
              ≤ ⌈c * (m : ℝ) ^ δ⌉₊) ∧
      (∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
        ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
          ((selChainCharge (sel m) G R
            + Impl.sweepCharge G ((selOrderingRoutine sel R) m G).order rc
                ⌈c * (m : ℝ) ^ δ⌉₊ : ℕ) : ℝ)
            ≤ f * (m : ℝ) ^ (1 + 2 * δ)) := by
  obtain ⟨cd, _hcd0, hdeg⟩ :=
    exists_wreach_degree_selOrderingRoutine sel C hC rc R t ht hrt δ hδ
  obtain ⟨f₁, hf₁0, hf₁⟩ := exists_selChainCharge_le_double sel C hC R δ hδ
  set c : ℝ := max cd 1 with hcdef
  have hc1 : (1 : ℝ) ≤ c := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hdeg' : ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ v : Fin m,
          (wreach G ((selOrderingRoutine sel R) m G).order (2 * rc) v).ncard
            ≤ ⌈c * (m : ℝ) ^ δ⌉₊ := by
    intro n Gn hGn m G hsub v
    refine (hdeg n Gn hGn m G hsub v).trans (Nat.ceil_mono ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg m) δ)
  refine ⟨c, f₁ + 2 * (c + 1) * (c + 1), hc1, by nlinarith, hdeg', ?_⟩
  intro n Gn hGn m G hsub
  exact coverChargeSel_le_of_degree sel rc R hrc hδ hc0
    (hdeg' n Gn hGn m G hsub) (hf₁ n Gn hGn m G hsub)

/-! ## §3 The ledger capstone at a supplied constant

`exists_mcChargeMS_chargeTotal_le_sel`'s body, with the two `obtain`s
replaced by hypotheses at **one** constant `cf`.  That single constant
is what `mcChargeMS_chargeTotal_le` already wants (its `c` is the
degree constant and its `f` the cover constant), so nothing is lost by
identifying them. -/

open Classical in
/-- **The root budget at a supplied pair of constants.**  Given a degree
bound and a cover-charge bound at the *same* `cf`, the whole root
ledger of the program — at any ordering routine whose order is the
selection's — is at most `κ·(‖G‖+1)^{1+ε}` with
`κ = KP S ℓp cf fs ^ (depth+1) + 2·topBudget S`.

This is `exists_mcChargeMS_chargeTotal_le_sel` with its existential
opened; §4 closes it again, but at a constant that keeps its degree
clause. -/
theorem mcChargeMS_chargeTotal_le_sel_of (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (S : Setup L) {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ)
    (ord : CoverSpec.OrderingRoutine)
    (hord : ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
      (ord m H).order = ((selOrderingRoutine sel (3 * S.R)) m H).order)
    {cf fs : ℝ} (hcf0 : 0 ≤ cf) (hfs0 : 0 ≤ fs)
    (hdegAll : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G → ∀ v : Fin m,
        (wreach H ((selOrderingRoutine sel (3 * S.R)) m H).order (2 * S.R) v).ncard
          ≤ ⌈cf * (m : ℝ) ^ headlineδ S ε⌉₊)
    (hcovAll : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
        ((selChainCharge (sel m) H (3 * S.R)
          + Impl.sweepCharge H ((selOrderingRoutine sel (3 * S.R)) m H).order S.R
              ⌈cf * (m : ℝ) ^ headlineδ S ε⌉₊ : ℕ) : ℝ)
          ≤ fs * (m : ℝ) ^ (1 + 2 * headlineδ S ε)) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ (col : Coloring n L)
        (htabF : (j : ℕ) → (A : Arena (S.pal j) n) →
          Fin A.N → Fin (ℓp j) → List (Fin A.N)),
        (chargeTotal (mcChargeMS S ord ℓp htabF
            (coverCFSel sel S cf (headlineδ S ε)) G col) : ℝ)
          ≤ (KP S ℓp cf fs ^ (S.depth + 1) + 2 * (topBudget S : ℝ))
            * ((graphWeight G : ℝ) + 1) ^ (1 + ε) := by
  have hδ : 0 < headlineδ S ε := by
    unfold headlineδ
    positivity
  have hK1 : (1 : ℝ) ≤ KP S ℓp cf fs := one_le_KP S ℓp hcf0 hfs0
  have hκ0 : (0 : ℝ) ≤ KP S ℓp cf fs ^ (S.depth + 1) + 2 * (topBudget S : ℝ) := by
    have h1 : (0 : ℝ) ≤ KP S ℓp cf fs ^ (S.depth + 1) := pow_nonneg (by linarith) _
    have h2 : (0 : ℝ) ≤ (topBudget S : ℝ) := Nat.cast_nonneg _
    linarith
  intro n G hG col htabF
  by_cases hW : 1 ≤ graphWeight G
  · have hcovG : ∀ (j : ℕ) (A : Arena (S.pal j) n), A.G ⊑ G →
        (chargeTotal (coverCFSel sel S cf (headlineδ S ε) j A) : ℝ)
          ≤ fs * (A.N : ℝ) ^ (1 + 2 * headlineδ S ε) := by
      intro j A hsub
      have hCF : chargeTotal (coverCFSel sel S cf (headlineδ S ε) j A)
          = selChainCharge (sel A.N) A.G (3 * S.R)
            + Impl.sweepCharge A.G
                ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order S.R
                ⌈cf * (A.N : ℝ) ^ headlineδ S ε⌉₊ :=
        chargeTotal_coverCSel (sel A.N) A.G S.R (3 * S.R) _
      rw [hCF]
      exact_mod_cast hcovAll n G hG A.N A.G hsub
    have hdegG : ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
        ∀ v : Fin m,
          (wreach H ((ord m H).order) (2 * S.R) v).ncard
            ≤ ⌈cf * (m : ℝ) ^ headlineδ S ε⌉₊ := by
      intro m H hsub v
      rw [hord m H]
      exact hdegAll n G hG m H hsub v
    have hmc := mcChargeMS_chargeTotal_le S ord ℓp
      htabF (coverCFSel sel S cf (headlineδ S ε)) hcf0 hfs0 hδ.le G col hcovG hdegG hW
    have hexp : 1 + ((S.depth : ℝ) + 2) * (2 * headlineδ S ε) = 1 + ε := by
      rw [headlineδ]
      have h2 : 2 * ((S.depth : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      try ring
    rw [hexp] at hmc
    refine hmc.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hκ0
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
  · -- the degenerate input: `‖G‖ = 0`, so the whole ledger is `0`
    have hgw : graphWeight G = 0 := by omega
    have hn : n = 0 := by
      have h : n ≤ graphWeight G := Nat.le_add_right _ _
      omega
    have hdz : chargeTotal (driverChargeMS S ord ℓp
        htabF (coverCFSel sel S cf (headlineδ S ε)) S.depth 0 (rootArena G col)) = 0 :=
      chargeTotal_driverChargeMS_of_N_eq_zero S ord
        ℓp htabF _ S.depth 0 (rootArena G col) hn
    have htopz : topScatterCost S G col
        (tables S ord 0 (rootArena G col)) = 0 := by
      have h := topScatterCost_le S G col
        (tables S ord 0 (rootArena G col))
      rw [hgw] at h
      omega
    have hmcz : chargeTotal (mcChargeMS S ord ℓp htabF
        (coverCFSel sel S cf (headlineδ S ε)) G col) = 0 := by
      rw [mcChargeMS, chargeTotal_add, chargeTotal_cost (by decide), hdz, htopz]
    rw [hmcz, hgw]
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    exact hκ0

/-! ## §4 Shape 2 at the ledger: the capstone that keeps its degree clause -/

open Classical in
/-- **The degree-carrying charge capstone.**  `exists_mcChargeMS_chargeTotal_le_sel`
with the exported constant tied to its property: there are `cf ≥ 1` and
`κ ≥ 0`, fixed before any graph, such that on every member

* every wreach set of the ordering the routine outputs, at radius
  `2·S.R`, on every subgraph copy, has size `≤ ⌈cf·m^δ⌉₊`, **and**
* the whole root ledger at the cover family `coverCFSel … cf …` is at
  most `κ·(‖G‖+1)^{1+ε}`.

The first clause is what `peelBudget_le_sweepCharge` consumes; the
second is the landed bound, unweakened. -/
theorem exists_mcChargeMS_chargeTotal_le_sel_deg (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (S : Setup L) {ε : ℝ} (hε : 0 < ε)
    (ℓp : ℕ → ℕ) (ord : CoverSpec.OrderingRoutine)
    (hord : ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
      (ord m H).order = ((selOrderingRoutine sel (3 * S.R)) m H).order) :
    ∃ cf κ : ℝ, 1 ≤ cf ∧ 0 ≤ κ ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G → ∀ v : Fin m,
          (wreach H ((ord m H).order) (2 * S.R) v).ncard
            ≤ ⌈cf * (m : ℝ) ^ headlineδ S ε⌉₊) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n L)
          (htabF : (j : ℕ) → (A : Arena (S.pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N)),
          (chargeTotal (mcChargeMS S ord ℓp htabF
              (coverCFSel sel S cf (headlineδ S ε)) G col) : ℝ)
            ≤ κ * ((graphWeight G : ℝ) + 1) ^ (1 + ε)) := by
  have hδ : 0 < headlineδ S ε := by
    unfold headlineδ
    positivity
  obtain ⟨cf, fs, hcf1, hfs0, hdegAll, hcovAll⟩ :=
    exists_coverChargeSel_le_deg sel C hC S.R (3 * S.R) S.R le_rfl
      (two_mul_le_two_pow S.one_le_R) S.one_le_R (headlineδ S ε) hδ
  have hcf0 : (0 : ℝ) ≤ cf := by linarith
  refine ⟨cf, KP S ℓp cf fs ^ (S.depth + 1) + 2 * (topBudget S : ℝ), hcf1, ?_, ?_, ?_⟩
  · have hK1 : (1 : ℝ) ≤ KP S ℓp cf fs := one_le_KP S ℓp hcf0 hfs0
    have h1 : (0 : ℝ) ≤ KP S ℓp cf fs ^ (S.depth + 1) := pow_nonneg (by linarith) _
    have h2 : (0 : ℝ) ≤ (topBudget S : ℝ) := Nat.cast_nonneg _
    linarith
  · intro n G hG m H hsub v
    rw [hord m H]
    exact hdegAll n G hG m H hsub v
  · exact mcChargeMS_chargeTotal_le_sel_of sel C S hε ℓp ord hord hcf0 hfs0
      hdegAll hcovAll

open Classical in
/-- The degree-carrying charge capstone at the **untimed** selection
routine — the one `SolveSweepBucketRound`'s machine
pass concludes at, so `KsChargeBridge` can carry this `ord` on both
sides. -/
theorem exists_mcChargeMS_chargeTotal_le_selOrdering_deg (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (S : Setup L) {ε : ℝ} (hε : 0 < ε)
    (ℓp : ℕ → ℕ) :
    ∃ cf κ : ℝ, 1 ≤ cf ∧ 0 ≤ κ ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G → ∀ v : Fin m,
          (wreach H (((selOrderingRoutine sel (3 * S.R)) m H).order) (2 * S.R) v).ncard
            ≤ ⌈cf * (m : ℝ) ^ headlineδ S ε⌉₊) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n L)
          (htabF : (j : ℕ) → (A : Arena (S.pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N)),
          (chargeTotal (mcChargeMS S (selOrderingRoutine sel (3 * S.R)) ℓp htabF
              (coverCFSel sel S cf (headlineδ S ε)) G col) : ℝ)
            ≤ κ * ((graphWeight G : ℝ) + 1) ^ (1 + ε)) :=
  exists_mcChargeMS_chargeTotal_le_sel_deg sel C hC S hε ℓp _ fun _ _ => rfl

open Lax11.GraphEncoding in
open Classical in
/-- **The degree-carrying `T` capstone** — `exists_mcChargeMS_T_sel`
with the degree clause attached to the exported `cf`.  This is the
statement F7 consumes: the `T` clause of the endorsed axiom *and* the
hypothesis its cover-sweep column needs, at one constant and one
routine. -/
theorem exists_mcChargeMS_T_sel_deg (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (φ : Lax3.FirstOrder.FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) (ord : CoverSpec.OrderingRoutine)
    (hord : ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
      (ord m H).order
        = ((selOrderingRoutine sel (3 * (Headline.headlineSetup C hC φ).R)) m H).order) :
    ∃ (cf c' : ℝ) (T : List ℕ → ℕ), 1 ≤ cf ∧ 0 ≤ c' ∧
      (∀ x : List ℕ, (T x : ℝ) ≤ c' * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G → ∀ v : Fin m,
          (wreach H ((ord m H).order) (2 * (Headline.headlineSetup C hC φ).R) v).ncard
            ≤ ⌈cf * (m : ℝ) ^ headlineδ (Headline.headlineSetup C hC φ) ε⌉₊) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n 0)
          (htabF : (j : ℕ) →
            (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N))
          (x : List ℕ), EncodesGraph x n G →
          chargeTotal (mcChargeMS (Headline.headlineSetup C hC φ) ord ℓp htabF
              (coverCFSel sel (Headline.headlineSetup C hC φ) cf
                (headlineδ (Headline.headlineSetup C hC φ) ε))
              G col) ≤ T x := by
  obtain ⟨cf, κ, hcf1, hκ0, hdeg, hmain⟩ :=
    exists_mcChargeMS_chargeTotal_le_sel_deg sel C hC (Headline.headlineSetup C hC φ)
      hε ℓp ord hord
  refine ⟨cf, κ + 1, fun x => ⌈κ * ((x.length : ℝ) + 1) ^ (1 + ε)⌉₊, hcf1,
    by linarith, ?_, hdeg, ?_⟩
  · -- the `T` bound, for every word
    intro x
    have h1 : (1 : ℝ) ≤ (x.length : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) x.length
      linarith
    have hle1 : (1 : ℝ) ≤ ((x.length : ℝ) + 1) ^ (1 + ε) := by
      calc (1 : ℝ) = 1 ^ ((1 : ℝ) + ε) := (Real.one_rpow _).symm
        _ ≤ ((x.length : ℝ) + 1) ^ (1 + ε) :=
          Real.rpow_le_rpow (by norm_num) h1 (by linarith)
    have hy : (0 : ℝ) ≤ κ * ((x.length : ℝ) + 1) ^ (1 + ε) :=
      mul_nonneg hκ0 (by linarith)
    calc ((⌈κ * ((x.length : ℝ) + 1) ^ (1 + ε)⌉₊ : ℕ) : ℝ)
        ≤ κ * ((x.length : ℝ) + 1) ^ (1 + ε) + 1 := (Nat.ceil_lt_add_one hy).le
      _ ≤ (κ + 1) * ((x.length : ℝ) + 1) ^ (1 + ε) := by nlinarith [hle1, hκ0]
  · -- the budget against the axiom's measure, on members
    intro n G hG col htabF x hx
    have hb := hmain n G hG col htabF
    have hlen : (graphWeight G : ℝ) ≤ (x.length : ℝ) :=
      Nat.cast_le.mpr (Headline.graphWeight_le_length hx)
    have h2 : (chargeTotal (mcChargeMS (Headline.headlineSetup C hC φ) ord ℓp htabF
        (coverCFSel sel (Headline.headlineSetup C hC φ) cf
          (headlineδ (Headline.headlineSetup C hC φ) ε)) G col) : ℝ)
        ≤ κ * ((x.length : ℝ) + 1) ^ (1 + ε) := by
      refine hb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hκ0
      refine Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have h3 := h2.trans (Nat.le_ceil _)
    exact_mod_cast h3

open Lax11.GraphEncoding in
open Classical in
/-- The degree-carrying `T` capstone at the untimed selection routine —
`exists_mcChargeMS_T_selOrdering`, repaired. -/
theorem exists_mcChargeMS_T_selOrdering_deg (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (φ : Lax3.FirstOrder.FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) :
    ∃ (cf c' : ℝ) (T : List ℕ → ℕ), 1 ≤ cf ∧ 0 ≤ c' ∧
      (∀ x : List ℕ, (T x : ℝ) ≤ c' * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G → ∀ v : Fin m,
          (wreach H
              (((selOrderingRoutine sel
                  (3 * (Headline.headlineSetup C hC φ).R)) m H).order)
              (2 * (Headline.headlineSetup C hC φ).R) v).ncard
            ≤ ⌈cf * (m : ℝ) ^ headlineδ (Headline.headlineSetup C hC φ) ε⌉₊) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n 0)
          (htabF : (j : ℕ) →
            (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N))
          (x : List ℕ), EncodesGraph x n G →
          chargeTotal (mcChargeMS (Headline.headlineSetup C hC φ)
              (selOrderingRoutine sel (3 * (Headline.headlineSetup C hC φ).R))
              ℓp htabF
              (coverCFSel sel (Headline.headlineSetup C hC φ) cf
                (headlineδ (Headline.headlineSetup C hC φ) ε))
              G col) ≤ T x :=
  exists_mcChargeMS_T_sel_deg sel C hC φ hε ℓp _ fun _ _ => rfl

/-! ## §5 The cover-sweep column

What `KsChargeBridge` actually consumes: the machine's peel budget at
one node, against that node's cover ledger vector.  `peelBudget_le_sweepCharge`
supplies it, once its three hypotheses are met — and the degree clause
of §4 is the third. -/

/-- `1 ≤ ⌈cf·m^δ⌉₊` on a nonempty carrier, at `1 ≤ cf` — the second
hypothesis of `peelBudget_le_sweepCharge`, and the reason §2 exports
`1 ≤ cf` rather than `0 ≤ cf`. -/
theorem one_le_ceil_deg {cf δ : ℝ} (hcf : 1 ≤ cf) (hδ : 0 ≤ δ) {m : ℕ} (hm : 0 < m) :
    1 ≤ ⌈cf * (m : ℝ) ^ δ⌉₊ := by
  refine Nat.ceil_pos.mpr ?_
  have h1 : (1 : ℝ) ≤ (m : ℝ) ^ δ := one_le_rpow hm hδ
  nlinarith

open Classical in
/-- The ledger entry the column is charged against: `coverCFSel`'s
`"cover.sweep"` slot **is** `Impl.sweepCharge` at the selection
routine's ordering and the family's own degree parameter. -/
theorem coverCFSel_toFun_sweep_eq (sel : ∀ m : ℕ, MinDegSel m) (S : Setup L)
    (cf δ : ℝ) (j : ℕ) (A : Arena (S.pal j) n₀) :
    (coverCFSel sel S cf δ j A).toFun "cover.sweep"
      = Impl.sweepCharge A.G ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order
          S.R ⌈cf * (A.N : ℝ) ^ δ⌉₊ :=
  coverCSel_toFun_sweep (sel A.N) A.G S.R (3 * S.R) _

open Classical in
/-- **The cover-sweep column, proved.**  For every budget affine in the
peel's three figures, at the machine's own ordering and at the degree
parameter the ledger names:

    peelK a b c ≤ a·A.N + (b+c) · (coverCFSel … cf δ j A).toFun "cover.sweep"

`peelBudget_le_sweepCharge`'s three hypotheses are met by `Setup.one_le_R`
(hazard 2: `(★)` is false at `R = 0`), `one_le_ceil_deg`, and the
degree clause `hdeg` — which is precisely what §4's capstone exports and
the landed `exists_mcChargeMS_T_selOrdering` does not.  The empty
carrier is handled separately: there `1 ≤ D` genuinely fails, and every
figure is an empty sum. -/
theorem peelK_le_coverCFSel_sweep (sel : ∀ m : ℕ, MinDegSel m) (S : Setup L)
    {cf δ : ℝ} (hcf : 1 ≤ cf) (hδ : 0 ≤ δ) (a b c : ℕ)
    (j : ℕ) (A : Arena (S.pal j) n₀)
    (hdeg : ∀ v : Fin A.N,
      (wreach A.G ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order (2 * S.R) v).ncard
        ≤ ⌈cf * (A.N : ℝ) ^ δ⌉₊) :
    peelK a b c S A ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order
      ≤ a * A.N + (b + c) * (coverCFSel sel S cf δ j A).toFun "cover.sweep" := by
  rw [coverCFSel_toFun_sweep_eq]
  rcases Nat.eq_zero_or_pos A.N with hN | hN
  · have hu : (Finset.univ : Finset (Fin A.N)) = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_univ, Fintype.card_fin, hN]
    simp [peelK, clusterMass, peelEdgeWork, hu]
  · exact peelBudget_le_sweepCharge S A _ a b c S.one_le_R
      (one_le_ceil_deg hcf hδ hN) hdeg

open Classical in
/-- **Anti-vacuity, at the node**: the cover ledger vector of a node is
at least that node's carrier size — the `"cover.order"` entry is
`selChainCharge`, and `le_selChainCharge` pins it above `A.N`.  So the
column below cannot be discharged by a placeholder charge. -/
theorem le_chargeTotal_coverCFSel (sel : ∀ m : ℕ, MinDegSel m) (S : Setup L)
    (cf δ : ℝ) (j : ℕ) (A : Arena (S.pal j) n₀) :
    A.N ≤ chargeTotal (coverCFSel sel S cf δ j A) := by
  rw [coverCFSel, chargeTotal_coverCSel]
  exact le_trans (le_selChainCharge (sel A.N) A.G (3 * S.R)) (Nat.le_add_right _ _)

open Classical in
/-- **The ledger–routine seam at a node**: the `"cover.order"` entry the
column is charged against is exactly the *priced* routine's abstract
`steps` field.  Together with `le_chargeTotal_coverCFSel` this is what
rules out the `steps := 0` reading of `CoverOrderingTime`: the charge
the column rides inside is the routine's own, and it is at least the
carrier size. -/
theorem coverCFSel_order_eq_timedSelRoutine_steps (sel : ∀ m : ℕ, MinDegSel m)
    (S : Setup L) (cf δ : ℝ) (j : ℕ) (A : Arena (S.pal j) n₀) :
    (((coverCFSel sel S cf δ j A).toFun "cover.order" : ℕ) : ℝ)
      = ((timedSelRoutine sel (3 * S.R)) A.N A.G).steps :=
  coverCSel_order_eq_steps sel A.N A.G S.R (3 * S.R) _

open Classical in
/-- **The column in `KsChargeBridge`'s own shape**: the peel budget of a
node is at most a constant times that node's ledger vector,

    peelK a b c ≤ (a+b+c) · chargeTotal (coverCFSel … cf δ j A).

The linear term `a·A.N` is absorbed through `le_chargeTotal_coverCFSel`
— i.e. through `le_selChainCharge` — so this is a bound against the
*witness*, not against a charge that could be `0`. -/
theorem peelK_le_coverCFSel_total (sel : ∀ m : ℕ, MinDegSel m) (S : Setup L)
    {cf δ : ℝ} (hcf : 1 ≤ cf) (hδ : 0 ≤ δ) (a b c : ℕ)
    (j : ℕ) (A : Arena (S.pal j) n₀)
    (hdeg : ∀ v : Fin A.N,
      (wreach A.G ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order (2 * S.R) v).ncard
        ≤ ⌈cf * (A.N : ℝ) ^ δ⌉₊) :
    peelK a b c S A ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order
      ≤ (a + b + c) * chargeTotal (coverCFSel sel S cf δ j A) := by
  have hcol := peelK_le_coverCFSel_sweep sel S hcf hδ a b c j A hdeg
  have hN : A.N ≤ chargeTotal (coverCFSel sel S cf δ j A) :=
    le_chargeTotal_coverCFSel sel S cf δ j A
  have hsw : (coverCFSel sel S cf δ j A).toFun "cover.sweep"
      ≤ chargeTotal (coverCFSel sel S cf δ j A) := by
    rw [coverCFSel, chargeTotal_coverCSel, coverCSel_toFun_sweep]
    exact Nat.le_add_left _ _
  calc peelK a b c S A ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order
      ≤ a * A.N + (b + c) * (coverCFSel sel S cf δ j A).toFun "cover.sweep" := hcol
    _ ≤ a * chargeTotal (coverCFSel sel S cf δ j A)
        + (b + c) * chargeTotal (coverCFSel sel S cf δ j A) :=
        Nat.add_le_add (Nat.mul_le_mul_left a hN) (Nat.mul_le_mul_left (b + c) hsw)
    _ = (a + b + c) * chargeTotal (coverCFSel sel S cf δ j A) := by ring

/-! ## §6 The capstone, at the machine's routine

`covOrderIn_bucketPeel` concludes at `selOrderingRoutine (fun m =>
bucketSel m) R` with `R` free; `coverCFSel` runs at `3 * S.R`.  At
`R := 3 * (headlineSetup C hC φ).R` the two are literally the same
routine, and `bucketSel` is the selection the machine passes force. -/

open Lax11.GraphEncoding in
open Classical in
/-- **The deliverable**: one constant `cf ≥ 1`, one `T`, one routine —
`selOrderingRoutine (fun m => bucketSel m) (3·S.R)`, the routine
`covOrderIn_bucketPeel` proves the machine's ordering pass against —
carrying at once

1. `T x ≤ c'·(|x|+1)^{1+ε}` for every word (the axiom's time clause);
2. the ledger bound `chargeTotal (mcChargeMS … ) ≤ T x` on members; and
3. the **cover-sweep column**: at every node of the recursion whose
   arena embeds in the input, the machine's peel budget is at most
   `(a+b+c)` times that node's cover ledger vector.

Clause 3 is what `SolveChain.KsChargeBridge`'s cover column consumes,
and it is dischargeable here — at the *same* `cf` as clause 2 — only
because the degree property travels with the constant.  With the landed
`exists_mcChargeMS_T_selOrdering` it is not: its `cf` carries `0 ≤ cf`
and nothing else. -/
theorem exists_mcChargeMS_T_bucket_coverColumn
    (C : GraphClass) (hC : NowhereDense C) (φ : Lax3.FirstOrder.FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) :
    ∃ (cf c' : ℝ) (T : List ℕ → ℕ), 1 ≤ cf ∧ 0 ≤ c' ∧
      (∀ x : List ℕ, (T x : ℝ) ≤ c' * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n 0)
          (htabF : (j : ℕ) →
            (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N))
          (x : List ℕ), EncodesGraph x n G →
          chargeTotal (mcChargeMS (Headline.headlineSetup C hC φ)
              (selOrderingRoutine (fun m => bucketSel m)
                (3 * (Headline.headlineSetup C hC φ).R))
              ℓp htabF
              (coverCFSel (fun m => bucketSel m) (Headline.headlineSetup C hC φ) cf
                (headlineδ (Headline.headlineSetup C hC φ) ε))
              G col) ≤ T x) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (j : ℕ) (A : Arena ((Headline.headlineSetup C hC φ).pal j) n),
          A.G ⊑ G → ∀ a b c : ℕ,
            peelK a b c (Headline.headlineSetup C hC φ) A
                ((selOrderingRoutine (fun m => bucketSel m)
                  (3 * (Headline.headlineSetup C hC φ).R)) A.N A.G).order
              ≤ (a + b + c) * chargeTotal
                  (coverCFSel (fun m => bucketSel m) (Headline.headlineSetup C hC φ) cf
                    (headlineδ (Headline.headlineSetup C hC φ) ε) j A)) := by
  have hδ : 0 < headlineδ (Headline.headlineSetup C hC φ) ε := by
    unfold headlineδ
    positivity
  obtain ⟨cf, c', T, hcf1, hc'0, hT, hdeg, hledger⟩ :=
    exists_mcChargeMS_T_selOrdering_deg (fun m => bucketSel m) C hC φ hε ℓp
  refine ⟨cf, c', T, hcf1, hc'0, hT, hledger, ?_⟩
  intro n G hG j A hsub a b c
  exact peelK_le_coverCFSel_total (fun m => bucketSel m) (Headline.headlineSetup C hC φ)
    hcf1 hδ.le a b c j A (hdeg n G hG A.N A.G hsub)

/-! ## §7 The leaf's axiom profile

Compared against the landed exports this leaf repairs, in matched pairs
— cover level and `T` level.  If each pair agrees, the degree clause
costs nothing beyond what F5b already paid.  (The cover-level pair
carries only the three of the ambient logic; the `T`-level pair
additionally carries Lax12's endorsed
`uniformlyQuasiWide_of_nowhereDense`, which enters through
`Headline.headlineSetup`, exactly as it does for the landed
`covSweepIn_of_build_peel`.) -/

#print axioms exists_coverChargeSel_le

#print axioms exists_coverChargeSel_le_deg

#print axioms exists_mcChargeMS_T_selOrdering

#print axioms exists_mcChargeMS_T_selOrdering_deg

#print axioms peelK_le_coverCFSel_total

#print axioms exists_mcChargeMS_T_bucket_coverColumn

end Lax3Proofs.Prog
