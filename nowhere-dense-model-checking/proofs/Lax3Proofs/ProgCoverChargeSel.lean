import Lax3Proofs.SolveSweepBucket

/-!
# F5b — the cover cost column, transferred off `timedGreedyRoutine`

F5 priced the ordering phase and closed the cover slot's cost at the
routine it had then: `timedGreedyRoutine`, whose chain is `greedyChain`
and whose order is `elimPerm (greedyChain G R).toGraph` — both built
from `elimRank = Exists.choose …`.  Wave 22 found (`SolveCovStep`'s
Finding 2) that no concrete program can be *proved* to output a
choice-picked ranking, and repinned the machine ordering to
`mdOrderingRoutine`; wave 24 (`SolveSweepBucket` §5) freed the
tie-break, generalising to `selOrderingRoutine sel` at any attaining
min-degree selection.  **The cost column did not move with either.**

This file moves it.  Everything F5 proved about `chainCharge` and
`coverC` is reproved at `selChain sel` / `selOrderingRoutine sel`, the
two capstones (`exists_mcChargeMS_chargeTotal_le`,
`exists_mcChargeMS_T`) are re-instantiated there, and §8 carries the
slot's *program* (`ProgCover.coverProg`, which names the routine in the
value it returns) across with them.

## Why the transfer, and not a corollary of F5

`CoverSpec.CoverOrderingTime C` is a bare `∃ A, …` — no routine can be
*extracted* from it, so F7 cannot read F5's witness out of the landed
headline.  F7 must exhibit its own routine (the one its `CovOrderIn`
pass is proved against) and its own cost, and the whole landed cost
column names `timedGreedyRoutine` literally: `chainCharge` is
`greedyChain G i` summand by summand, `coverC` reads
`((timedGreedyRoutine R) m G).order`, and `coverCF`/`exists_mcChargeMS_T`
carry both.

## Why the proof transfers verbatim

`AugmentedDensity.greedy_chain_joint_inDegLE` is stated for an
**arbitrary** chain: `IsAugChain G D r`, `∀ i < r, GreedyFratRound (D i)
(D (i+1))`, `(D 0).InDegLE d`, and a depth-`chainDepth r 1` density
bound on `G`.  Wave 24 landed all three at the selection —
`isAugChain_selChain`, `greedyFratRound_selChain`,
`inDegLE_baseOr_selPerm` — and `selChain sel G 0` is `baseOr G (selPerm
sel G)` definitionally, with `inDeg := elimBound G` in both routines, so
`inDeg_zero_le`/`elimBound_le` fire unchanged.  The per-level counts
(`arcCount`, `fratPairCount`, `transPairCount`, `levelCharge`) were
already stated at an arbitrary `Orientation`, so they are reused, not
restated; only `baseCharge` (which named `greedyChain G 0`) needed an
analogue, `selBaseCharge`.

## Stated at the selection, not at one tie-break

Every result below is at an arbitrary `sel : ∀ m, MinDegSel m`.
`mdOrderingRoutine` is the special case `sel := fun m => mdSel m`
(`selOrderingRoutine_mdSel`), and each headline is also given at it
explicitly, so a consumer may use either and a future re-pin of the
tie-break costs this column nothing.

## The exponent

`exists_selChainCharge_le` lands the ordering phase at
`f·m^{1+δ}` — the exponent F5 landed (`exists_chainCharge_le`), reached
the same way: run the in-degree recursion at inner exponent
`δ/(2·16^R)`, so the uniform bound is `d ≤ (3c₀+5)^{16^R}·m^{δ/2}` and
the per-round `N·d²` is `N^{1+δ}`.  `exists_selChainCharge_le_double`
weakens to the interface's `1+2δ` (the sweep's exponent, which
dominates) — the weakening is where the interface asks for it, never
in the phase's own bound.

## Vacuity, and the routine that carries the charge

`CoverOrderingTime` is cheaply true at `steps := 0`, so a bound with no
witness is worth nothing: `le_selChainCharge` (`m ≤ selChainCharge`) is
the control that the charge is not a disguised placeholder, and
`coverCSel_order_eq_steps` pins the ledger's `"cover.order"` entry to
the timed routine's abstract `steps` field.

**Which routine the ledger runs at.**  Every use of the
`OrderingRoutine` argument inside `Prog.mcChargeMS` is through its
`.order` field — `frameChargeMS` (`ProgCharge.lean:208`),
`Unroll.unrollAux` (`:228-229`), `DriverArena.tablesAux` (`:319`) — the
ordering phase's *charge* entering instead through the cover family
`covC`.  (`.steps` is read by `Unroll.frameCost`, the **abstract** cost
recursion, which `mcChargeMS` does not call.)  `timedSelRoutine sel R`
and `selOrderingRoutine sel R` have the same `.order` (definitionally —
the update touches `steps` alone), so the capstones below are proved
once, for **any** routine whose order is the selection's (`hord`), and
instantiated at all three: `selOrderingRoutine sel (3R)` — the routine
`SolveSweepOrder`'s machine pass is proved against, so
`SolveChain.KsChargeBridge`'s two sides can end at the same `ord` — at
`timedSelRoutine sel (3R)`, and at `mdOrderingRoutine (3R)`.

## Findings

* `ProgCoverCharge.dmax_cast_le` and `rpow_div_pow` are `private`, so
  the two numeric steps of `exists_chainCharge_le` had to be restated
  here (`selDmax_cast_le`, `sel_rpow_div_pow`); they are the landed
  proofs verbatim, not new mathematics.
* No landed statement was found to be false in the material this leaf
  reads.  One docstring is imprecise: `ProgCover`'s says the order half
  "enters at its true exponent `m^{1+δ}` (`exists_chainCharge_le`)",
  while the proof of `exists_coverCharge_le` in fact consumes the
  weakened `exists_chainCharge_le_double`.  The sum's bound is the same
  either way, so nothing is wrong — but `exists_chainCharge_le` is not
  what that proof uses.  The analogue here (`exists_coverChargeSel_le`)
  does the same and says so.
-/

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

/-! ## §1 The chain's charge, at a selection

`arcCount`, `fratPairCount`, `transPairCount`, `levelCharge` and
`finalCharge` are already stated at an arbitrary `Orientation`
(`ProgCoverCharge.lean:129-216`), so only the base level — which named
`greedyChain G 0` — needs an analogue. -/

/-- The charge of the base level at a selection: peel `G` with the
selection and orient along the peel (`baseOr G (selPerm sel G)`, which
*is* `selChain sel G 0`).  The peel is `O(n + |E(G)|)` and the arcs of
round `0` are exactly the edges of `G` (`baseOr_orients`), so
`m + 3·arcs` covers the peel's vertex scan, its edge work and the
orientation build — `baseCharge`'s allocation, at the freed
tie-break. -/
noncomputable def selBaseCharge {m : ℕ} (sel : MinDegSel m)
    (G : SimpleGraph (Fin m)) : ℕ :=
  m + 3 * arcCount (selChain sel G 0)

/-- **The charge of the whole ordering phase at a selection**: the base
peel, the `R` greedy rounds, and the final elimination of the
symmetrized augmented graph.  This is the `steps` value of
`timedSelRoutine` and the `"cover.order"` entry of `coverCSel` — the
mirror of `chainCharge`, at `selChain` instead of `greedyChain`. -/
noncomputable def selChainCharge {m : ℕ} (sel : MinDegSel m)
    (G : SimpleGraph (Fin m)) (R : ℕ) : ℕ :=
  selBaseCharge sel G + (∑ i ∈ Finset.range R, levelCharge (selChain sel G i))
    + finalCharge (selChain sel G R)

/-- On the empty carrier every count is an empty sum: the charge is
`0`.  (The `m = 0` case of every bound below.) -/
theorem selChainCharge_zero (sel : MinDegSel 0) (G : SimpleGraph (Fin 0)) (R : ℕ) :
    selChainCharge sel G R = 0 := by
  simp [selChainCharge, selBaseCharge, finalCharge, levelCharge, arcCount,
    fratPairCount, transPairCount]

/-- **Control: the charge is not a disguised placeholder.**  It is at
least the carrier size — the routine reads its input — so the timed
discharge below is not the vacuous `steps := 0` one the interface would
also accept.  This is `le_chainCharge` at the selection, and it is what
makes the bounds below worth stating. -/
theorem le_selChainCharge {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m))
    (R : ℕ) : m ≤ selChainCharge sel G R := by
  have h1 : m ≤ selBaseCharge sel G := Nat.le_add_right m _
  have h2 : selBaseCharge sel G ≤ selChainCharge sel G R :=
    le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  exact h1.trans h2

/-- **The chain total at a uniform in-degree bound**: `R` levels, the
base and the final elimination, all priced by one `d`, total
`(6R + 8)·m·(d+1)²`.  Pure counting — the class enters only through
`d`, and the selection only through the chain the counts are read
at. -/
theorem selChainCharge_le_of_uniform {m : ℕ} {sel : MinDegSel m}
    {G : SimpleGraph (Fin m)} {R d : ℕ}
    (hd : ∀ i ≤ R, (selChain sel G i).InDegLE d) :
    selChainCharge sel G R ≤ (6 * R + 8) * (m * ((d + 1) * (d + 1))) := by
  have hbase : selBaseCharge sel G ≤ 3 * (m * ((d + 1) * (d + 1))) := by
    have h := arcCount_le (hd 0 (Nat.zero_le R))
    have : selBaseCharge sel G = m + 3 * arcCount (selChain sel G 0) := rfl
    nlinarith [h]
  have hfin : finalCharge (selChain sel G R) ≤ 5 * (m * ((d + 1) * (d + 1))) := by
    have h := arcCount_le (hd R le_rfl)
    have : finalCharge (selChain sel G R) = 3 * m + 5 * arcCount (selChain sel G R) := rfl
    nlinarith [h]
  have hsum : (∑ i ∈ Finset.range R, levelCharge (selChain sel G i))
      ≤ R * (6 * (m * ((d + 1) * (d + 1)))) := by
    calc (∑ i ∈ Finset.range R, levelCharge (selChain sel G i))
        ≤ ∑ _i ∈ Finset.range R, 6 * (m * ((d + 1) * (d + 1))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h := levelCharge_le (hd i (le_of_lt (Finset.mem_range.mp hi)))
          nlinarith [h]
      _ = R * (6 * (m * ((d + 1) * (d + 1)))) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_range]
  calc selChainCharge sel G R
      = selBaseCharge sel G + (∑ i ∈ Finset.range R, levelCharge (selChain sel G i))
        + finalCharge (selChain sel G R) := rfl
    _ ≤ 3 * (m * ((d + 1) * (d + 1))) + R * (6 * (m * ((d + 1) * (d + 1))))
        + 5 * (m * ((d + 1) * (d + 1))) := by omega
    _ = (6 * R + 8) * (m * ((d + 1) * (d + 1))) := by ring

/-! ## §2 The selection chain's in-degree on a class

`greedy_chain_joint_inDegLE` (`AugmentedDensity.lean:966`) is stated for
an arbitrary chain; wave 24 landed its three hypotheses at the
selection.  Nothing in this section is new mathematics — it is
`exists_greedyChain_inDegLE_pow`'s proof with `greedyChain` replaced. -/

/-- **The selection chain's rounds, uniformly bounded on a class** (raw
form): for every round count and inner exponent there is a `c₀` such
that on every subgraph copy of a member all rounds `i ≤ R` of the
chain at *any* attaining selection have in-degree at most
`(3·⌈c₀·m^δ'⌉₊ + 2) ^ 16 ^ R`. -/
theorem exists_selChain_inDegLE_pow (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (R : ℕ) (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ i ≤ R, (selChain (sel m) G i).InDegLE
          ((3 * ⌈c₀ * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ R) := by
  obtain ⟨c₀, hc₀⟩ := exists_densityAtMost_of_nowhereDense C hC (chainDepth R 1) δ' hδ'
  refine ⟨max c₀ 0, le_max_right _ _, fun n Gn hGn m G hsub => ?_⟩
  have hXnn : (0 : ℝ) ≤ (m : ℝ) ^ δ' := Real.rpow_nonneg (Nat.cast_nonneg m) δ'
  have hdensR : HasDensityAtMost G (chainDepth R 1) ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ :=
    hasDensityAtMost_mono
      (Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn))
      (hc₀ n Gn hGn m G hsub)
  have hdens1 : HasDensityAtMost G 1 ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ :=
    hasDensityAtMost_mono_depth
      (show (1 : ℕ) ≤ chainDepth R 1 from chainDepth_mono_round 1 (Nat.zero_le R)) hdensR
  have hd0 : (selChain (sel m) G 0).InDegLE (elimBound G) :=
    inDegLE_baseOr_selPerm (sel m) G
  have hd0le : elimBound G ≤ 2 * ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ :=
    inDeg_zero_le hdens1 fun _k' hk' => elimBound_le hk'
  have hjoint := greedy_chain_joint_inDegLE (isAugChain_selChain (sel m) G R)
    (fun i _ => greedyFratRound_selChain (sel m) G i) hd0 hdensR
  intro i hi v
  refine (hjoint i hi v).trans ?_
  calc (joint (elimBound G) ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ i).1
      ≤ (elimBound G + ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ i := joint_fst_le _ _ _
    _ ≤ (3 * ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ i :=
        Nat.pow_le_pow_left (by omega) _
    _ ≤ (3 * ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ R :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hi)

/-- The cast of the raw bound: `(3·⌈c₀·X⌉₊ + 2)^P ≤ ((3c₀+5)·X)^P` for
`X ≥ 1`.  `ProgCoverCharge.dmax_cast_le` is `private`, so this is that
proof restated — not new content. -/
private theorem selDmax_cast_le {c₀ X : ℝ} (hc₀ : 0 ≤ c₀) (hX : 1 ≤ X) (P : ℕ) :
    (((3 * ⌈c₀ * X⌉₊ + 2) ^ P : ℕ) : ℝ) ≤ ((3 * c₀ + 5) * X) ^ P := by
  have hXnn : (0 : ℝ) ≤ X := zero_le_one.trans hX
  have hceil : ((⌈c₀ * X⌉₊ : ℕ) : ℝ) ≤ c₀ * X + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hc₀ hXnn)).le
  have hbase : ((3 * ⌈c₀ * X⌉₊ + 2 : ℕ) : ℝ) ≤ (3 * c₀ + 5) * X := by
    push_cast
    nlinarith [hceil, hX, hc₀]
  calc (((3 * ⌈c₀ * X⌉₊ + 2) ^ P : ℕ) : ℝ)
      = (((3 * ⌈c₀ * X⌉₊ + 2 : ℕ) : ℝ)) ^ P := by push_cast; ring
    _ ≤ ((3 * c₀ + 5) * X) ^ P := by gcongr

/-- `(m^(δ/P))^P = m^δ`: the inner exponent, undone.  (Restated:
`ProgCoverCharge.rpow_div_pow` is `private`.) -/
private theorem sel_rpow_div_pow (m P : ℕ) (hP : 0 < P) (δ : ℝ) :
    ((m : ℝ) ^ (δ / (P : ℝ))) ^ (P : ℕ) = (m : ℝ) ^ δ := by
  have hP0 : ((P : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  rw [← Real.rpow_natCast ((m : ℝ) ^ (δ / (P : ℝ))) P,
    ← Real.rpow_mul (Nat.cast_nonneg m), div_mul_cancel₀ _ hP0]

/-- **The selection chain's in-degree bound, on a class** — the
`⌈c·m^δ⌉₊` form: one constant, fixed before the graph, bounding the
in-degree of *every* round `i ≤ R` on every subgraph copy of every
member.  The uniformization `exists_greedyChain_inDegLE` at the freed
tie-break. -/
theorem exists_selChain_inDegLE (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ i ≤ R, (selChain (sel m) G i).InDegLE ⌈c * (m : ℝ) ^ δ⌉₊ := by
  have hPpos : 0 < (16 ^ R : ℕ) := by positivity
  have hδ' : 0 < δ / ((16 ^ R : ℕ) : ℝ) := div_pos hδ (by exact_mod_cast hPpos)
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_selChain_inDegLE_pow sel C hC R _ hδ'
  refine ⟨(3 * c₀ + 5) ^ (16 ^ R : ℕ), fun n Gn hGn m G hsub i hi v => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact v.elim0
  have h := hc₀ n Gn hGn m G hsub i hi v
  refine h.trans ?_
  have hX1 : (1 : ℝ) ≤ (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ)) := one_le_rpow hm hδ'.le
  have hcast := selDmax_cast_le hc₀0 hX1 (16 ^ R)
  have hXP := sel_rpow_div_pow m (16 ^ R) hPpos δ
  have hfin : (((3 * ⌈c₀ * (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))⌉₊ + 2) ^ 16 ^ R : ℕ) : ℝ)
      ≤ (3 * c₀ + 5) ^ (16 ^ R : ℕ) * (m : ℝ) ^ δ := by
    calc (((3 * ⌈c₀ * (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))⌉₊ + 2) ^ 16 ^ R : ℕ) : ℝ)
        ≤ ((3 * c₀ + 5) * (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))) ^ (16 ^ R : ℕ) := hcast
      _ = (3 * c₀ + 5) ^ (16 ^ R : ℕ)
            * ((m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))) ^ (16 ^ R : ℕ) := mul_pow _ _ _
      _ = (3 * c₀ + 5) ^ (16 ^ R : ℕ) * (m : ℝ) ^ δ := by rw [hXP]
  exact_mod_cast hfin.trans (Nat.le_ceil _)

/-! ## §3 The priced chain, on a class -/

/-- **The ordering phase's charge at a selection, bounded** — at the
exponent it truly has: on a nowhere dense class,
`selChainCharge ≤ f·m^{1+δ}`, with `f` fixed before the graph.  This is
the exponent F5 landed for `chainCharge` (`exists_chainCharge_le`), not
the interface's weaker `1 + 2δ`; the weakening is
`exists_selChainCharge_le_double`. -/
theorem exists_selChainCharge_le (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        (selChainCharge (sel m) G R : ℝ) ≤ f * (m : ℝ) ^ (1 + δ) := by
  have hPpos : 0 < (2 * 16 ^ R : ℕ) := by positivity
  have hδ' : 0 < δ / ((2 * 16 ^ R : ℕ) : ℝ) := div_pos hδ (by exact_mod_cast hPpos)
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_selChain_inDegLE_pow sel C hC R _ hδ'
  refine ⟨(4 * (6 * R + 8) : ℝ) * (3 * c₀ + 5) ^ (2 * 16 ^ R : ℕ), by positivity, ?_⟩
  intro n Gn hGn m G hsub
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [selChainCharge_zero, Nat.cast_zero,
      Real.zero_rpow (by positivity : (1 : ℝ) + δ ≠ 0), mul_zero]
  -- the uniform in-degree bound of every round
  have huni := hc₀ n Gn hGn m G hsub
  set D₁ : ℕ := ⌈c₀ * (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))⌉₊ with hD₁def
  -- the ℕ-side total at that bound
  have hN := selChainCharge_le_of_uniform huni
  set dmax : ℕ := (3 * D₁ + 2) ^ 16 ^ R with hdmaxdef
  have hd1 : 1 ≤ dmax := Nat.one_le_pow _ _ (by omega)
  have hsq : (dmax + 1) * (dmax + 1) ≤ 4 * ((3 * D₁ + 2) ^ (2 * 16 ^ R)) := by
    have h4 : (dmax + 1) * (dmax + 1) ≤ 4 * (dmax * dmax) := by nlinarith [hd1]
    have hdd : dmax * dmax = (3 * D₁ + 2) ^ (2 * 16 ^ R) := by
      rw [hdmaxdef, ← pow_add, two_mul]
    rwa [hdd] at h4
  have hN2 : selChainCharge (sel m) G R
      ≤ 4 * (6 * R + 8) * (m * (3 * D₁ + 2) ^ (2 * 16 ^ R)) := by
    calc selChainCharge (sel m) G R ≤ (6 * R + 8) * (m * ((dmax + 1) * (dmax + 1))) := hN
      _ ≤ (6 * R + 8) * (m * (4 * ((3 * D₁ + 2) ^ (2 * 16 ^ R)))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsq)
      _ = 4 * (6 * R + 8) * (m * (3 * D₁ + 2) ^ (2 * 16 ^ R)) := by ring
  -- the ℝ-side massage
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hX1 : (1 : ℝ) ≤ (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ)) := one_le_rpow hm hδ'.le
  have hcast := selDmax_cast_le hc₀0 hX1 (2 * 16 ^ R)
  have hXP := sel_rpow_div_pow m (2 * 16 ^ R) hPpos δ
  calc (selChainCharge (sel m) G R : ℝ)
      ≤ ((4 * (6 * R + 8) * (m * (3 * D₁ + 2) ^ (2 * 16 ^ R)) : ℕ) : ℝ) := by
        exact_mod_cast hN2
    _ = (4 * (6 * R + 8) : ℝ) * ((m : ℝ) * (((3 * D₁ + 2) ^ (2 * 16 ^ R) : ℕ) : ℝ)) := by
        push_cast; ring
    _ ≤ (4 * (6 * R + 8) : ℝ) * ((m : ℝ)
          * ((3 * c₀ + 5) * (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))) ^ (2 * 16 ^ R : ℕ)) := by
        rw [hD₁def]
        gcongr
    _ = (4 * (6 * R + 8) : ℝ) * (3 * c₀ + 5) ^ (2 * 16 ^ R : ℕ)
          * ((m : ℝ) * ((m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))) ^ (2 * 16 ^ R : ℕ)) := by
        rw [mul_pow]; ring
    _ = (4 * (6 * R + 8) : ℝ) * (3 * c₀ + 5) ^ (2 * 16 ^ R : ℕ) * (m : ℝ) ^ (1 + δ) := by
        rw [hXP, Real.rpow_add hm0, Real.rpow_one]

/-- The charge bound in the interface's exponent:
`selChainCharge ≤ f·m^{1+2δ}` — `exists_selChainCharge_le` weakened
along `m^{1+δ} ≤ m^{1+2δ}`.  This is the exact shape of
`CoverSpec.IsCoverOrdering.time`. -/
theorem exists_selChainCharge_le_double (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        (selChainCharge (sel m) G R : ℝ) ≤ f * (m : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨f, hf0, hf⟩ := exists_selChainCharge_le sel C hC R δ hδ
  refine ⟨f, hf0, fun n Gn hGn m G hsub => (hf n Gn hGn m G hsub).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hf0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero, Real.zero_rpow (by positivity : (1 : ℝ) + δ ≠ 0),
      Real.zero_rpow (by positivity : (1 : ℝ) + 2 * δ ≠ 0)]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)

/-! ## §4 The timed routine at a selection

`OrderingOutput.steps` is data, so the honest discharge is a *second*
routine, equal to wave 24's `selOrderingRoutine` in every field except
`steps` — which now carries `selChainCharge` instead of the placeholder
`0`.  The four congruence identities are definitional, so the `data`
theorem is inherited rather than re-proved. -/

/-- **The selection ordering routine, priced**: wave 24's routine with
the placeholder `steps := 0` replaced by the honest charge of the
phase.  Chain, order and the two elimination bounds are *unchanged*. -/
noncomputable def timedSelRoutine (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) :
    CoverSpec.OrderingRoutine :=
  fun m G => { selOrderingRoutine sel R m G with
    steps := (selChainCharge (sel m) G R : ℝ) }

/-- **The congruence with wave 24's routine**: every field except
`steps` is the placeholder routine's, definitionally.  This is what
lets `data` transfer without re-proof, and what lets the ledger below
be read at either routine. -/
theorem timedSelRoutine_congr (sel : ∀ m : ℕ, MinDegSel m) (R m : ℕ)
    (G : SimpleGraph (Fin m)) :
    ((timedSelRoutine sel R) m G).chain = ((selOrderingRoutine sel R) m G).chain ∧
    ((timedSelRoutine sel R) m G).order = ((selOrderingRoutine sel R) m G).order ∧
    ((timedSelRoutine sel R) m G).inDeg = ((selOrderingRoutine sel R) m G).inDeg ∧
    ((timedSelRoutine sel R) m G).backDeg = ((selOrderingRoutine sel R) m G).backDeg :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem timedSelRoutine_steps (sel : ∀ m : ℕ, MinDegSel m) (R m : ℕ)
    (G : SimpleGraph (Fin m)) :
    ((timedSelRoutine sel R) m G).steps = (selChainCharge (sel m) G R : ℝ) := rfl

@[simp] theorem timedSelRoutine_order (sel : ∀ m : ℕ, MinDegSel m) (R m : ℕ)
    (G : SimpleGraph (Fin m)) :
    ((timedSelRoutine sel R) m G).order
      = selPerm (sel m) (selChain (sel m) G R).toGraph := rfl

/-- The timed routine's order is the untimed routine's, definitionally
— the identity that lets a ledger stated at one be read at the
other. -/
theorem timedSelRoutine_order_eq (sel : ∀ m : ℕ, MinDegSel m) (R m : ℕ)
    (G : SimpleGraph (Fin m)) :
    ((timedSelRoutine sel R) m G).order = ((selOrderingRoutine sel R) m G).order := rfl

/-- The `data` half, inherited across the congruence: the timed
routine's output satisfies the six-clause `AugChainData` postcondition
for every graph on every carrier, with no hypothesis on the class — the
same proof term as wave 24's, since every field it speaks about is
unchanged. -/
theorem timedSelRoutine_data (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) :
    ∀ (m : ℕ) (G : SimpleGraph (Fin m)),
      AugChainData G ((timedSelRoutine sel R) m G).chain
        ((timedSelRoutine sel R) m G).order R
        ((timedSelRoutine sel R) m G).inDeg
        ((timedSelRoutine sel R) m G).backDeg :=
  fun m G => selOrderingRoutine_data sel R m G

/-- **Both halves of `IsCoverOrdering`, proved, for the priced
selection routine**: on a nowhere dense class, for every round count
and every `δ > 0` there is an `f` — fixed before the graph — such that
the timed selection routine is a correct ordering phase (`data`,
hypothesis-free from wave 24) whose honest charge is at most
`f·m^{1+2δ}`.  The witness is real: `le_selChainCharge` pins its
`steps` above the carrier size. -/
theorem isCoverOrdering_timedSelRoutine (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, CoverSpec.IsCoverOrdering C R δ f (timedSelRoutine sel R) := by
  obtain ⟨f, _hf0, hf⟩ := exists_selChainCharge_le_double sel C hC R δ hδ
  exact ⟨f, ⟨fun _n _Gn _hGn m G _hsub => timedSelRoutine_data sel R m G,
    fun n Gn hGn m G hsub => hf n Gn hGn m G hsub⟩⟩

/-- **The anti-vacuity control, at the routine**: the priced routine's
`steps` field is at least the carrier size, so the discharge above is
not the `steps := 0` one `CoverSpec.IsCoverOrdering` would also accept
(module docstring).  This is `le_selChainCharge` read through
`timedSelRoutine_steps`. -/
theorem le_timedSelRoutine_steps (sel : ∀ m : ℕ, MinDegSel m) (R m : ℕ)
    (G : SimpleGraph (Fin m)) :
    (m : ℝ) ≤ ((timedSelRoutine sel R) m G).steps := by
  rw [timedSelRoutine_steps]
  exact_mod_cast le_selChainCharge (sel m) G R

/-- The pinned tie-break as a special case: at `sel := mdSel` the timed
routine's order is `mdOrderingRoutine`'s, so a ledger at either is a
ledger at the other.  (`selOrderingRoutine_mdSel` is the routine-level
identity; `steps` is the one field that differs, and only because
`mdOrderingRoutine` still carries the placeholder `0`.) -/
theorem timedSelRoutine_mdSel_order (R m : ℕ) (G : SimpleGraph (Fin m)) :
    ((timedSelRoutine (fun m => mdSel m) R) m G).order
      = ((mdOrderingRoutine R) m G).order := by
  rw [timedSelRoutine_order_eq, selOrderingRoutine_mdSel]

/-! ## §5 The wreach degree of the selection routine's ordering

The hypothesis `Impl.sweepCharge_le` consumes, derived for the
selection chain's final ordering from the class — not assumed. -/

/-- **The wreach-degree bound of the selection routine's ordering**: on
a nowhere dense class, with the radius arithmetic, there is a `c ≥ 0` —
fixed before the graph — bounding every wreach set of the ordering the
routine outputs by `⌈c·m^δ⌉₊`.  This is
`CoverDegree.wreach_degree_of_data` consumed at the landed,
hypothesis-free `selOrderingRoutine_data`. -/
theorem exists_wreach_degree_selOrderingRoutine (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ v : Fin m,
          (wreach G ((selOrderingRoutine sel R) m G).order (2 * rc) v).ncard
            ≤ ⌈c * (m : ℝ) ^ δ⌉₊ := by
  obtain ⟨c, hc⟩ := wreach_degree_of_data C hC rc R t ht hrt δ hδ
  refine ⟨max c 0, le_max_right _ _, fun n Gn hGn m G hsub v => ?_⟩
  have h := hc n Gn hGn m G hsub _ _ _ _ (selOrderingRoutine_data sel R m G) v
  refine h.trans (Nat.ceil_mono ?_)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (Nat.cast_nonneg m) δ)

/-- The same bound at the pinned tie-break — `mdOrderingRoutine`'s
ordering, for consumers still stated there. -/
theorem exists_wreach_degree_mdOrderingRoutine (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ v : Fin m,
          (wreach G ((mdOrderingRoutine R) m G).order (2 * rc) v).ncard
            ≤ ⌈c * (m : ℝ) ^ δ⌉₊ := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_wreach_degree_selOrderingRoutine (fun m => mdSel m) C hC rc R t ht hrt δ hδ
  refine ⟨c, hc0, fun n Gn hGn m G hsub v => ?_⟩
  have h := hc n Gn hGn m G hsub v
  rwa [selOrderingRoutine_mdSel] at h

/-! ## §6 The cover slot's charge vector, at the selection -/

open Classical in
/-- **The cover slot's charge vector at a selection**: the ordering
stage in `"cover.order"` — the honest `selChainCharge` — and the sweep
stage in `"cover.sweep"` — `Impl.sweepCharge` at the selection
routine's ordering and the slot's degree parameter.  This is `coverC`
with `timedGreedyRoutine` replaced throughout. -/
noncomputable def coverCSel {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m))
    (rc R D : ℕ) : ACost String ℕ :=
  ACost.cost "cover.order" (selChainCharge sel G R)
    + ACost.cost "cover.sweep"
        (Impl.sweepCharge G (selPerm sel (selChain sel G R).toGraph) rc D)

open Classical in
@[simp] theorem coverCSel_toFun_order {m : ℕ} (sel : MinDegSel m)
    (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    (coverCSel sel G rc R D).toFun "cover.order" = selChainCharge sel G R := by
  simp [coverCSel, ACost.toFun_add]

open Classical in
@[simp] theorem coverCSel_toFun_sweep {m : ℕ} (sel : MinDegSel m)
    (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    (coverCSel sel G rc R D).toFun "cover.sweep"
      = Impl.sweepCharge G (selPerm sel (selChain sel G R).toGraph) rc D := by
  simp [coverCSel, ACost.toFun_add]

open Classical in
/-- **Slot hygiene**: the cover slot spends only its own two
currencies. -/
theorem coverCSel_toFun_ne {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m))
    (rc R D : ℕ) {k : String}
    (h₁ : k ≠ "cover.order") (h₂ : k ≠ "cover.sweep") :
    (coverCSel sel G rc R D).toFun k = 0 := by
  simp [coverCSel, ACost.toFun_add, ACost.toFun_cost_ne h₁, ACost.toFun_cost_ne h₂]

open Classical in
/-- The slot's vector spends only program currencies — the
support-honesty input `mcChargeMS_toFun_eq_zero` asks of a cover
family, here at one node. -/
theorem coverCSel_toFun_eq_zero_of_notMem {m : ℕ} (sel : MinDegSel m)
    (G : SimpleGraph (Fin m)) (rc R D : ℕ) {k : String} (hk : k ∉ progKeys) :
    (coverCSel sel G rc R D).toFun k = 0 :=
  coverCSel_toFun_ne sel G rc R D (by rintro rfl; exact hk (by decide))
    (by rintro rfl; exact hk (by decide))

open Classical in
/-- **The ledger–routine seam**: the slot's `"cover.order"` entry is
exactly the *priced* routine's abstract `steps` field — the answer to
the vacuity note, at the selection.  `SolveSweepOrder`'s machine pass
owes the same number. -/
theorem coverCSel_order_eq_steps (sel : ∀ m : ℕ, MinDegSel m) (m : ℕ)
    (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    (((coverCSel (sel m) G rc R D).toFun "cover.order" : ℕ) : ℝ)
      = ((timedSelRoutine sel R) m G).steps := by
  rw [coverCSel_toFun_order, timedSelRoutine_steps]

open Classical in
/-- The slot's total: the two entries, summed over the ten program
currencies. -/
theorem chargeTotal_coverCSel {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m))
    (rc R D : ℕ) :
    chargeTotal (coverCSel sel G rc R D)
      = selChainCharge sel G R
        + Impl.sweepCharge G (selPerm sel (selChain sel G R).toGraph) rc D := by
  rw [coverCSel, chargeTotal_add, chargeTotal_cost (by decide),
    chargeTotal_cost (by decide)]

open Classical in
/-- **The cover pipeline's cost at a selection, proved**: on a nowhere
dense class, with the radius arithmetic `3t ≤ R`, `2·rc ≤ 2^t` and the
sweep's genuine side condition `1 ≤ rc`, there are `c, f ≥ 0` — both
fixed before the graph — such that on every subgraph copy of every
member the **whole** cover charge, ordering phase plus sweep at the
derived degree `D = ⌈c·m^δ⌉₊`, is at most `f·m^{1+2δ}`.  The degree
parameter is derived (`exists_wreach_degree_selOrderingRoutine`), not
assumed; the order half enters through
`exists_selChainCharge_le_double` and the sweep through
`Impl.sweepCharge_le`, whose `2·D·(m·D)` is the term that forces
`1 + 2δ`. -/
theorem exists_coverChargeSel_le (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (hrc : 1 ≤ rc)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c f : ℝ, 0 ≤ c ∧ 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ((selChainCharge (sel m) G R
          + Impl.sweepCharge G ((selOrderingRoutine sel R) m G).order rc
              ⌈c * (m : ℝ) ^ δ⌉₊ : ℕ) : ℝ)
          ≤ f * (m : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨c, hc0, hdeg⟩ :=
    exists_wreach_degree_selOrderingRoutine sel C hC rc R t ht hrt δ hδ
  obtain ⟨f₁, hf₁0, hf₁⟩ := exists_selChainCharge_le_double sel C hC R δ hδ
  refine ⟨c, f₁ + 2 * (c + 1) * (c + 1), hc0, by positivity, ?_⟩
  intro n Gn hGn m G hsub
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [selChainCharge_zero, Impl.sweepCharge,
      Real.zero_rpow (show (1 : ℝ) + 2 * δ ≠ 0 by positivity)]
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set Dd : ℕ := ⌈c * (m : ℝ) ^ δ⌉₊ with hDddef
  have hD := hdeg n Gn hGn m G hsub
  have hsw : Impl.sweepCharge G ((selOrderingRoutine sel R) m G).order rc Dd
      ≤ 2 * Dd * (m * Dd) := Impl.sweepCharge_le hrc hD
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
        refine add_le_add (hf₁ n Gn hGn m G hsub) ?_
        calc ((Impl.sweepCharge G ((selOrderingRoutine sel R) m G).order rc Dd : ℕ) : ℝ)
            ≤ ((2 * Dd * (m * Dd) : ℕ) : ℝ) := by exact_mod_cast hsw
          _ = 2 * ((Dd : ℕ) : ℝ) * ((m : ℝ) * ((Dd : ℕ) : ℝ)) := by push_cast; ring
          _ ≤ 2 * ((c + 1) * (m : ℝ) ^ δ) * ((m : ℝ) * ((c + 1) * (m : ℝ) ^ δ)) := by
              gcongr
    _ = (f₁ + 2 * (c + 1) * (c + 1)) * (m : ℝ) ^ (1 + 2 * δ) := by rw [hpow]; ring

open Classical in
/-- The capstone, read on the slot's ledger: the total of `coverCSel`'s
two entries — the whole charge vector, by `coverCSel_toFun_ne` — is at
most `f·m^{1+2δ}`, the degree parameter derived from the class. -/
theorem exists_coverCSel_total_le (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C)
    (rc R t : ℕ) (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (hrc : 1 ≤ rc)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c f : ℝ, 0 ≤ c ∧ 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ((chargeTotal (coverCSel (sel m) G rc R ⌈c * (m : ℝ) ^ δ⌉₊) : ℕ) : ℝ)
          ≤ f * (m : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨c, f, hc0, hf0, h⟩ := exists_coverChargeSel_le sel C hC rc R t ht hrt hrc δ hδ
  refine ⟨c, f, hc0, hf0, fun n Gn hGn m G hsub => ?_⟩
  rw [chargeTotal_coverCSel]
  exact h n Gn hGn m G hsub

/-! ## §7 The capstones, re-instantiated at the selection

Every use of the `OrderingRoutine` argument inside `Prog.mcChargeMS` is
through `.order` (module docstring), and the ordering phase's charge
enters through the cover family.  So both capstones are proved once,
for **any** routine whose order is the selection's (`hord`) — and then
instantiated at the untimed `selOrderingRoutine` (which
`SolveSweepOrder`'s machine pass is proved against, so
`KsChargeBridge`'s two sides can end at the same `ord`), at the priced
`timedSelRoutine`, and at `mdOrderingRoutine`. -/

open Classical in
/-- **The headline's cover family, at a selection** — the slot vector
per node: the selection routine at `3·S.R` rounds, sweep radius `S.R`,
degree parameter `⌈cf·N^δ⌉₊`.  `coverCF` with `timedGreedyRoutine`
replaced. -/
noncomputable def coverCFSel (sel : ∀ m : ℕ, MinDegSel m) (S : Setup L) (cf δ : ℝ) :
    (j : ℕ) → Arena (S.pal j) n₀ → ACost String ℕ :=
  fun _j A => coverCSel (sel A.N) A.G S.R (3 * S.R) ⌈cf * (A.N : ℝ) ^ δ⌉₊

open Classical in
/-- The sel cover family spends only program currencies. -/
theorem coverCFSel_toFun_eq_zero_of_notMem (sel : ∀ m : ℕ, MinDegSel m)
    (S : Setup L) (cf δ : ℝ) (j : ℕ) (A : Arena (S.pal j) n₀)
    {k : String} (hk : k ∉ progKeys) :
    (coverCFSel sel S cf δ j A).toFun k = 0 :=
  coverCSel_toFun_eq_zero_of_notMem (sel A.N) A.G S.R (3 * S.R)
    ⌈cf * (A.N : ℝ) ^ δ⌉₊ hk

open Classical in
/-- **The leaf's headline at the charge level** (`mcCharge_le`-shaped,
at the MS-routed budget): on a nowhere dense class, for every setup,
`ε > 0` and history-round profile `ℓp`, there are constants `cf, κ ≥ 0`
— fixed before any graph — such that on every member the whole root
budget of the program, at **any** ordering routine whose order is the
selection's and the concrete cover family `coverCFSel`, is

    chargeTotal (mcChargeMS …) ≤ κ · (‖G‖+1)^{1+ε}.

The degree parameter of the sweep is `exists_coverChargeSel_le`'s
derived `⌈cf·N^δ⌉₊`; the wreach-degree constant of the recursion is
`exists_wreach_degree_selOrderingRoutine`'s (it lives inside `κ`
through `KP`).  The radius arithmetic is discharged by the setup itself
(`t := S.R`, `Setup.one_le_R`, `two_mul_le_two_pow`). -/
theorem exists_mcChargeMS_chargeTotal_le_sel (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (S : Setup L) {ε : ℝ} (hε : 0 < ε)
    (ℓp : ℕ → ℕ) (ord : CoverSpec.OrderingRoutine)
    (hord : ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
      (ord m H).order = ((selOrderingRoutine sel (3 * S.R)) m H).order) :
    ∃ cf κ : ℝ, 0 ≤ cf ∧ 0 ≤ κ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n L)
          (htabF : (j : ℕ) → (A : Arena (S.pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N)),
          (chargeTotal (mcChargeMS S ord ℓp htabF
              (coverCFSel sel S cf (headlineδ S ε)) G col) : ℝ)
            ≤ κ * ((graphWeight G : ℝ) + 1) ^ (1 + ε) := by
  have hδ : 0 < headlineδ S ε := by
    unfold headlineδ
    positivity
  obtain ⟨cdeg, hcdeg0, hdegAll⟩ := exists_wreach_degree_selOrderingRoutine sel C hC
    S.R (3 * S.R) S.R le_rfl (two_mul_le_two_pow S.one_le_R) (headlineδ S ε) hδ
  obtain ⟨cs, fs, hcs0, hfs0, hcovAll⟩ := exists_coverChargeSel_le sel C hC
    S.R (3 * S.R) S.R le_rfl (two_mul_le_two_pow S.one_le_R) S.one_le_R
    (headlineδ S ε) hδ
  have hK1 : (1 : ℝ) ≤ KP S ℓp cdeg fs := one_le_KP S ℓp hcdeg0 hfs0
  have hκ0 : (0 : ℝ) ≤ KP S ℓp cdeg fs ^ (S.depth + 1) + 2 * (topBudget S : ℝ) := by
    have h1 : (0 : ℝ) ≤ KP S ℓp cdeg fs ^ (S.depth + 1) :=
      pow_nonneg (by linarith) _
    have h2 : (0 : ℝ) ≤ (topBudget S : ℝ) := Nat.cast_nonneg _
    linarith
  refine ⟨cs, KP S ℓp cdeg fs ^ (S.depth + 1) + 2 * (topBudget S : ℝ),
    hcs0, hκ0, ?_⟩
  intro n G hG col htabF
  by_cases hW : 1 ≤ graphWeight G
  · -- the honest case: the lift at the root, then the exponent choice
    have hcovG : ∀ (j : ℕ) (A : Arena (S.pal j) n), A.G ⊑ G →
        (chargeTotal (coverCFSel sel S cs (headlineδ S ε) j A) : ℝ)
          ≤ fs * (A.N : ℝ) ^ (1 + 2 * headlineδ S ε) := by
      intro j A hsub
      have hCF : chargeTotal (coverCFSel sel S cs (headlineδ S ε) j A)
          = selChainCharge (sel A.N) A.G (3 * S.R)
            + Impl.sweepCharge A.G
                ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order S.R
                ⌈cs * (A.N : ℝ) ^ headlineδ S ε⌉₊ :=
        chargeTotal_coverCSel (sel A.N) A.G S.R (3 * S.R) _
      rw [hCF]
      exact_mod_cast hcovAll n G hG A.N A.G hsub
    have hdegG : ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
        ∀ v : Fin m,
          (wreach H ((ord m H).order) (2 * S.R) v).ncard
            ≤ ⌈cdeg * (m : ℝ) ^ headlineδ S ε⌉₊ := by
      intro m H hsub v
      rw [hord m H]
      exact hdegAll n G hG m H hsub v
    have hmc := mcChargeMS_chargeTotal_le S ord ℓp
      htabF (coverCFSel sel S cs (headlineδ S ε)) hcdeg0 hfs0 hδ.le G col hcovG hdegG hW
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
        htabF (coverCFSel sel S cs (headlineδ S ε)) S.depth 0 (rootArena G col)) = 0 :=
      chargeTotal_driverChargeMS_of_N_eq_zero S ord
        ℓp htabF _ S.depth 0 (rootArena G col) hn
    have htopz : topScatterCost S G col
        (tables S ord 0 (rootArena G col)) = 0 := by
      have h := topScatterCost_le S G col
        (tables S ord 0 (rootArena G col))
      rw [hgw] at h
      omega
    have hmcz : chargeTotal (mcChargeMS S ord ℓp htabF
        (coverCFSel sel S cs (headlineδ S ε)) G col) = 0 := by
      rw [mcChargeMS, chargeTotal_add, chargeTotal_cost (by decide), hdz, htopz]
    rw [hmcz, hgw]
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    exact hκ0

open Lax11.GraphEncoding in
open Classical in
/-- **The leaf's headline** — the endorsed axiom's `T` clause at the
selection, stated so F7 need only multiply by the machine's `L.const`:
for every nowhere dense `C`, plain sentence `φ : FO 0`, `ε > 0` and
history profile `ℓp`, and for **any** ordering routine whose order is
the selection's, there are `cf, c' ≥ 0` and a ℕ-valued
`T : List ℕ → ℕ` — all fixed before any input — with

* `T x ≤ c'·(|x|+1)^{1+ε}` for **every** word `x`, and
* on every member of `C` and every CSR encoding `x` of it, the root
  program's whole ledger total at the campaign setup — `mcChargeMS` at
  that routine and the sel cover family — is at most `T x`.

This is `exists_mcChargeMS_T` with `timedGreedyRoutine` replaced by a
routine a machine pass can be proved against; it is the statement F7
consumes, and `KsChargeBridge`'s `ord` can be the same one. -/
theorem exists_mcChargeMS_T_sel (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (φ : Lax3.FirstOrder.FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) (ord : CoverSpec.OrderingRoutine)
    (hord : ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
      (ord m H).order
        = ((selOrderingRoutine sel (3 * (Headline.headlineSetup C hC φ).R)) m H).order) :
    ∃ (cf c' : ℝ) (T : List ℕ → ℕ), 0 ≤ cf ∧ 0 ≤ c' ∧
      (∀ x : List ℕ, (T x : ℝ) ≤ c' * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
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
  obtain ⟨cf, κ, hcf0, hκ0, hmain⟩ :=
    exists_mcChargeMS_chargeTotal_le_sel sel C hC (Headline.headlineSetup C hC φ)
      hε ℓp ord hord
  refine ⟨cf, κ + 1, fun x => ⌈κ * ((x.length : ℝ) + 1) ^ (1 + ε)⌉₊, hcf0,
    by linarith, ?_, ?_⟩
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

/-! ### The three instantiations

The routine the ledger runs at is free in the two capstones above; here
it is pinned, once per consumer. -/

open Classical in
/-- The charge capstone at the **untimed** selection routine — the one
`SolveSweepOrder`'s machine pass (`covOrderIn_of_aug_mdPeel` and its
sel re-pin) is proved against, so `SolveChain.KsChargeBridge` can carry
this `ord` on both sides. -/
theorem exists_mcChargeMS_chargeTotal_le_selOrdering (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (S : Setup L) {ε : ℝ} (hε : 0 < ε)
    (ℓp : ℕ → ℕ) :
    ∃ cf κ : ℝ, 0 ≤ cf ∧ 0 ≤ κ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n L)
          (htabF : (j : ℕ) → (A : Arena (S.pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N)),
          (chargeTotal (mcChargeMS S (selOrderingRoutine sel (3 * S.R)) ℓp htabF
              (coverCFSel sel S cf (headlineδ S ε)) G col) : ℝ)
            ≤ κ * ((graphWeight G : ℝ) + 1) ^ (1 + ε) :=
  exists_mcChargeMS_chargeTotal_le_sel sel C hC S hε ℓp _ fun _ _ => rfl

open Classical in
/-- The charge capstone at the **priced** selection routine: the same
bound, at the routine whose `steps` field carries the honest
`selChainCharge` (`coverCSel_order_eq_steps`). -/
theorem exists_mcChargeMS_chargeTotal_le_timedSel (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (S : Setup L) {ε : ℝ} (hε : 0 < ε)
    (ℓp : ℕ → ℕ) :
    ∃ cf κ : ℝ, 0 ≤ cf ∧ 0 ≤ κ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n L)
          (htabF : (j : ℕ) → (A : Arena (S.pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N)),
          (chargeTotal (mcChargeMS S (timedSelRoutine sel (3 * S.R)) ℓp htabF
              (coverCFSel sel S cf (headlineδ S ε)) G col) : ℝ)
            ≤ κ * ((graphWeight G : ℝ) + 1) ^ (1 + ε) :=
  exists_mcChargeMS_chargeTotal_le_sel sel C hC S hε ℓp _ fun _ _ => rfl

open Classical in
/-- The charge capstone at the pinned tie-break: `mdOrderingRoutine`,
the routine wave 22's machine pass is stated at. -/
theorem exists_mcChargeMS_chargeTotal_le_mdOrdering
    (C : GraphClass) (hC : NowhereDense C) (S : Setup L) {ε : ℝ} (hε : 0 < ε)
    (ℓp : ℕ → ℕ) :
    ∃ cf κ : ℝ, 0 ≤ cf ∧ 0 ≤ κ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n L)
          (htabF : (j : ℕ) → (A : Arena (S.pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N)),
          (chargeTotal (mcChargeMS S (mdOrderingRoutine (3 * S.R)) ℓp htabF
              (coverCFSel (fun m => mdSel m) S cf (headlineδ S ε)) G col) : ℝ)
            ≤ κ * ((graphWeight G : ℝ) + 1) ^ (1 + ε) :=
  exists_mcChargeMS_chargeTotal_le_sel (fun m => mdSel m) C hC S hε ℓp _
    (fun _ _ => by rw [selOrderingRoutine_mdSel])

open Lax11.GraphEncoding in
open Classical in
/-- **The `T` capstone at the untimed selection routine** — the
statement F7 consumes: the same `ord` its `CovOrderIn` is at, so
`KsChargeBridge`'s two sides end at one routine. -/
theorem exists_mcChargeMS_T_selOrdering (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (φ : Lax3.FirstOrder.FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) :
    ∃ (cf c' : ℝ) (T : List ℕ → ℕ), 0 ≤ cf ∧ 0 ≤ c' ∧
      (∀ x : List ℕ, (T x : ℝ) ≤ c' * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
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
  exists_mcChargeMS_T_sel sel C hC φ hε ℓp _ fun _ _ => rfl

open Lax11.GraphEncoding in
open Classical in
/-- The `T` capstone at the **priced** selection routine. -/
theorem exists_mcChargeMS_T_timedSel (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (φ : Lax3.FirstOrder.FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) :
    ∃ (cf c' : ℝ) (T : List ℕ → ℕ), 0 ≤ cf ∧ 0 ≤ c' ∧
      (∀ x : List ℕ, (T x : ℝ) ≤ c' * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n 0)
          (htabF : (j : ℕ) →
            (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N))
          (x : List ℕ), EncodesGraph x n G →
          chargeTotal (mcChargeMS (Headline.headlineSetup C hC φ)
              (timedSelRoutine sel (3 * (Headline.headlineSetup C hC φ).R))
              ℓp htabF
              (coverCFSel sel (Headline.headlineSetup C hC φ) cf
                (headlineδ (Headline.headlineSetup C hC φ) ε))
              G col) ≤ T x :=
  exists_mcChargeMS_T_sel sel C hC φ hε ℓp _ fun _ _ => rfl

open Lax11.GraphEncoding in
open Classical in
/-- The `T` capstone at the pinned tie-break, `mdOrderingRoutine` — the
routine `SolveSweepOrder.covOrderIn_of_aug_mdPeel` concludes at. -/
theorem exists_mcChargeMS_T_mdOrdering
    (C : GraphClass) (hC : NowhereDense C) (φ : Lax3.FirstOrder.FO 0)
    {ε : ℝ} (hε : 0 < ε) (ℓp : ℕ → ℕ) :
    ∃ (cf c' : ℝ) (T : List ℕ → ℕ), 0 ≤ cf ∧ 0 ≤ c' ∧
      (∀ x : List ℕ, (T x : ℝ) ≤ c' * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n 0)
          (htabF : (j : ℕ) →
            (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
            Fin A.N → Fin (ℓp j) → List (Fin A.N))
          (x : List ℕ), EncodesGraph x n G →
          chargeTotal (mcChargeMS (Headline.headlineSetup C hC φ)
              (mdOrderingRoutine (3 * (Headline.headlineSetup C hC φ).R))
              ℓp htabF
              (coverCFSel (fun m => mdSel m) (Headline.headlineSetup C hC φ) cf
                (headlineδ (Headline.headlineSetup C hC φ) ε))
              G col) ≤ T x :=
  exists_mcChargeMS_T_sel (fun m => mdSel m) C hC φ hε ℓp _
    (fun _ _ => by rw [selOrderingRoutine_mdSel])

/-! ## §8 The slot's program, at the selection

The same hardwiring one level down: `ProgCover.coverProg` names
`timedGreedyRoutine` in the value it returns, so F3's `hcover`
hypothesis could only be discharged at that routine.  Here it is at the
selection's ordering, with `coverCSel` as the budget — the pair
`(coverProgSel, coverCSel)` the frame's cover slot is filled with. -/

open Classical in
/-- **The cover slot's program at a selection** (F3's `coverProg`
parameter, filled): pay the ordering phase and hold the selection
routine's ordering; run the sweep — the cluster list and the `ctr`
assignment, GKS's routine as landed in `ImplCover` — and pay its
account; return the ordering.  `ProgCover.coverProg` with
`timedGreedyRoutine` replaced. -/
noncomputable def coverProgSel {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m))
    (rc R D : ℕ) : NRest (Equiv.Perm (Fin m)) ECost :=
  NRest.bindT (NRest.consume
      (NRest.returnT (selPerm sel (selChain sel G R).toGraph))
      (liftACost (ACost.cost "cover.order" (selChainCharge sel G R)))) fun π =>
  NRest.bindT (NRest.consume
      (NRest.returnT (Impl.sweepClusters G π rc, Impl.sweepCtr G π rc))
      (liftACost (ACost.cost "cover.sweep" (Impl.sweepCharge G π rc D)))) fun _sw =>
  NRest.returnT π

open Classical in
/-- **The slot's refinement**: the cover program returns exactly the
selection routine's ordering, for budget `coverCSel` — the shape of
F3's `hcover` hypothesis, proved through the frame's own spec
calculus. -/
theorem coverProgSel_le_spec {m : ℕ} (sel : MinDegSel m) (G : SimpleGraph (Fin m))
    (rc R D : ℕ) :
    coverProgSel sel G rc R D ≤
      NRest.spec (fun π => π = selPerm sel (selChain sel G R).toGraph)
        (fun _ => liftACost (coverCSel sel G rc R D)) := by
  rw [coverProgSel, coverCSel, liftACost_add]
  refine bindT_le_spec
    (consume_returnT_le_spec
      (P := fun π => π = selPerm sel (selChain sel G R).toGraph) rfl _)
    fun π hπ => ?_
  subst hπ
  refine le_spec_weaken
    (bindT_le_spec
      (consume_returnT_le_spec (P := fun _ => True) trivial _)
      (fun _ _ => returnT_le_spec
        (P := fun π' => π' = selPerm sel (selChain sel G R).toGraph) rfl 0))
    (fun _ hx => hx) (add_zero _).le

open Classical in
/-- The refinement read at the routine: the returned value is
`((selOrderingRoutine sel R) m G).order` — definitionally the same
permutation, and also `((timedSelRoutine sel R) m G).order`. -/
theorem coverProgSel_le_spec_routine (sel : ∀ m : ℕ, MinDegSel m) (m : ℕ)
    (G : SimpleGraph (Fin m)) (rc R D : ℕ) :
    coverProgSel (sel m) G rc R D ≤
      NRest.spec (fun π => π = ((selOrderingRoutine sel R) m G).order)
        (fun _ => liftACost (coverCSel (sel m) G rc R D)) :=
  coverProgSel_le_spec (sel m) G rc R D

open Classical in
/-- The slot, at an arena: **F3's `hcover` hypothesis, discharged** for
`ord := selOrderingRoutine sel R` and
`covC := coverCSel (sel A.N) A.G S.R R D` — `frameProg_le_spec`
composes with this directly, at the routine the machine ordering pass
is proved against. -/
theorem coverProgSel_slot (sel : ∀ m : ℕ, MinDegSel m) {L n₀ : ℕ}
    (S : Driver.Setup L) (j : ℕ) (A : Driver.Arena (S.pal j) n₀) (R D : ℕ) :
    coverProgSel (sel A.N) A.G S.R R D ≤
      NRest.spec (fun π => π = ((selOrderingRoutine sel R) A.N A.G).order)
        (fun _ => liftACost (coverCSel (sel A.N) A.G S.R R D)) :=
  coverProgSel_le_spec (sel A.N) A.G S.R R D

end Lax3Proofs.Prog
