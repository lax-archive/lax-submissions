import Lax3Proofs.Refine.OrderActiveDriver

/-!
# Arena-relative width and cost of the active ordering

The compact ordering phase is already charged in its live carrier and
live row mass.  This file identifies their sum with the driver's
`arenaWeight`, chooses one resident width affine in that weight, and
packages the resulting `OrderImplementsA` instance at an affine cost.
-/

namespace Lax3Proofs.Refine.OrderActiveBudget

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverMember (OrderImplementsA)
open Lax3Proofs.Refine.ScatterBlock (MemList)
open Lax3Proofs.Refine.ElimCompact (memGraph memRowSum)
open Lax3Proofs.Refine.OrderActiveChain (activeChainWidthE)
open Lax3Proofs.Refine.OrderActiveDriver

/-- The resident live-width coefficient.  With no augmentation rounds the
compact input itself supplies all target storage, so the coefficient is one
and is independent of the graph's degeneracy bound. -/
def activeOrderWidthCoeff (d D₁ R : ℕ) : ℕ :=
  if R = 0 then 1 else
    (Lax3Proofs.Augmentation.budget d D₁ R + 1) ^ 2 +
      Lax3Proofs.Augmentation.budget d D₁ R + 1

/-- A resident width sufficient for every compact ordering call in an
arena of weight `a`. -/
def activeOrderWidth (d D₁ R a : ℕ) : ℕ :=
  activeOrderWidthCoeff d D₁ R * (a + 1)

/-- The formula-dependent coefficient of the complete ordering charge. -/
def activeOrderCostCoeff (d D₁ R : ℕ) : ℕ :=
  (3953 + R * 17226) * activeOrderWidthCoeff d D₁ R +
    (1008 + R * 9232)

/-- The active ordering charge, affine in the current arena weight. -/
def activeOrderCost (d D₁ R a : ℕ) : ℕ :=
  activeOrderCostCoeff d D₁ R * (a + 1)

theorem activeOrderWidth_mono {d D₁ R a a' : ℕ} (h : a ≤ a') :
    activeOrderWidth d D₁ R a ≤ activeOrderWidth d D₁ R a' := by
  simp only [activeOrderWidth]
  exact Nat.mul_le_mul_left _ (by omega)

theorem activeOrderCost_mono {d D₁ R a a' : ℕ} (h : a ≤ a') :
    activeOrderCost d D₁ R a ≤ activeOrderCost d D₁ R a' := by
  simp only [activeOrderCost]
  exact Nat.mul_le_mul_left _ (by omega)

/-- The member count plus the live input-row sum is exactly the level
arena's graph weight. -/
theorem memberWeight_eq_arenaWeight {n mm ns : ℕ}
    {G : SimpleGraph (Fin n)} {O T M Mem : ℕ → ℕ}
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T)
    (hml : MemList n mm Mem (Lax3Proofs.RamDriverCluster.markSet n M)) :
    mm + memRowSum mm O Mem =
      Lax3Proofs.Refine.MassWeight.arenaWeight n G M := by
  calc
    mm + memRowSum mm O Mem =
        Lax3Proofs.Refine.MassWeight.wsum
          (Lax3Proofs.Refine.MassWeight.csrW n O)
          (Lax3Proofs.RamDriverCluster.markSet n M) :=
      (Lax3Proofs.Refine.ElimCompactWalks.wsum_csrW_markSet hml).symm
    _ = Lax3Proofs.Refine.MassWeight.arenaWeight n G M := by
      rw [Lax3Proofs.Refine.MassWeight.arenaWeight_eq_csr hcsr M]
      rfl

/-- The chosen arena-affine width dominates the exact compact-chain
workspace requirement. -/
theorem activeChainWidthE_le_weight {n mm ns d D₁ R : ℕ}
    {G : SimpleGraph (Fin n)} {O T M Mem : ℕ → ℕ}
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T)
    (hml : MemList n mm Mem (Lax3Proofs.RamDriverCluster.markSet n M)) :
    activeChainWidthE mm (memRowSum mm O Mem) d D₁ R ≤
      activeOrderWidth d D₁ R
        (Lax3Proofs.Refine.MassWeight.arenaWeight n G M) := by
  rw [← memberWeight_eq_arenaWeight hcsr hml]
  by_cases hR : R = 0
  · subst R
    simp [activeOrderWidth, activeOrderWidthCoeff]
  let b := Lax3Proofs.Augmentation.budget d D₁ R
  let p := (b + 1) ^ 2
  have hmm : mm ≤ mm + memRowSum mm O Mem + 1 := by omega
  have hrs : memRowSum mm O Mem + 1 ≤ mm + memRowSum mm O Mem + 1 := by omega
  have h₁ : mm * p ≤ p * (mm + memRowSum mm O Mem + 1) := by
    rw [Nat.mul_comm mm p]
    exact Nat.mul_le_mul_left p hmm
  have h₂ : mm * b ≤ b * (mm + memRowSum mm O Mem + 1) := by
    rw [Nat.mul_comm mm b]
    exact Nat.mul_le_mul_left b hmm
  have h₃ : memRowSum mm O Mem + 1 ≤
      1 * (mm + memRowSum mm O Mem + 1) := by
    rw [one_mul]
    exact hrs
  simp only [activeChainWidthE, activeOrderWidth, activeOrderWidthCoeff,
    if_neg hR]
  calc
    mm * (Lax3Proofs.Augmentation.budget d D₁ R + 1) ^ 2 +
          mm * Lax3Proofs.Augmentation.budget d D₁ R +
          memRowSum mm O Mem + 1 =
        mm * p + mm * b + (memRowSum mm O Mem + 1) := by
      simp only [b, p]
      omega
    _ ≤ p * (mm + memRowSum mm O Mem + 1) +
          b * (mm + memRowSum mm O Mem + 1) +
          1 * (mm + memRowSum mm O Mem + 1) :=
      Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃
    _ = (p + b + 1) * (mm + memRowSum mm O Mem + 1) := by ring

/-- Once the resident width is chosen from the arena weight, the exact
phase charge is bounded by one formula-dependent affine function. -/
theorem activeOrderPhaseCost_le_weight (d D₁ R a : ℕ) :
    activeOrderPhaseCost (activeOrderWidth d D₁ R a)
        (activeOrderWidth d D₁ R a) (activeOrderWidth d D₁ R a) R ≤
      activeOrderCost d D₁ R a := by
  have hone : 1 ≤ a + 1 := by omega
  have hc : 1008 + R * 9232 ≤ (1008 + R * 9232) * (a + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (1008 + R * 9232) hone
  calc
    activeOrderPhaseCost (activeOrderWidth d D₁ R a)
        (activeOrderWidth d D₁ R a) (activeOrderWidth d D₁ R a) R =
      ((3953 + R * 17226) * activeOrderWidthCoeff d D₁ R) * (a + 1) +
        (1008 + R * 9232) := by
          simp only [activeOrderPhaseCost, activeOrderWidth]
          ring
    _ ≤ ((3953 + R * 17226) * activeOrderWidthCoeff d D₁ R) * (a + 1) +
        (1008 + R * 9232) * (a + 1) := Nat.add_le_add_left hc _
    _ = activeOrderCost d D₁ R a := by
      simp only [activeOrderCost, activeOrderCostCoeff]
      ring

/-- The driver-facing phase at the arena-relative allocation and cost.
This is the form consumed by the active level induction. -/
theorem activeOrderPhase_weight_spec
    {B n cap mb ns W j R d D₁ Kmass : ℕ}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ}
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T)
    (hBns : n + ns + 1 < B)
    (hBw : n + activeOrderWidth d D₁ R
      (Lax3Proofs.Refine.MassWeight.arenaWeight n G M) + 1 < B)
    (hwW : activeOrderWidth d D₁ R
      (Lax3Proofs.Refine.MassWeight.arenaWeight n G M) ≤ W)
    (hd : ∀ {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : MemList n mm Mem (Lax3Proofs.RamDriverCluster.markSet n M)),
      Lax3Proofs.Augmentation.LowDegreeVertices (memGraph G M hml) d)
    (hdens : ∀ {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : MemList n mm Mem (Lax3Proofs.RamDriverCluster.markSet n M))
        (D : ℕ → Lax3Proofs.Augmentation.Orientation mm) (i : ℕ), i ≤ R →
      Lax3Proofs.Augmentation.IsAugChain (memGraph G M hml) D i →
      (∀ l < i, Lax3Proofs.Augmentation.GreedyFratRound (D l) (D (l + 1))) →
      Lax3Proofs.Augmentation.AugmentedDepthOneDensity D i D₁)
    (hKmass : 1 ≤ Kmass)
    (hdegree : ∀ {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : MemList n mm Mem (Lax3Proofs.RamDriverCluster.markSet n M))
        {D : ℕ → Lax3Proofs.Augmentation.Orientation mm}
        {d₀ k : ℕ} {pi : Equiv.Perm (Fin mm)},
      Lax3Proofs.CoverDegree.AugChainData (memGraph G M hml) D pi R d₀ k →
      ∀ v : Fin mm,
        (Lax12.ColoringNumbers.wreach (memGraph G M hml) pi (2 * cap) v).ncard ≤ Kmass) :
    OrderImplementsA B n W cap mb ns j O T M Gm C
      (Lax3Proofs.RamCoverActiveMass.ActiveOrderP G cap Kmass)
      (activeOrderPhase j R)
      (activeOrderCost d D₁ R
        (Lax3Proofs.Refine.MassWeight.arenaWeight n G M)) := by
  exact (activeOrderPhase_spec (mb := mb) (j := j) (Gm := Gm) (C := C)
    (w := activeOrderWidth d D₁ R
      (Lax3Proofs.Refine.MassWeight.arenaWeight n G M))
    hcsr hBns hBw hwW hd hdens
    (fun hml => activeChainWidthE_le_weight hcsr hml) hKmass hdegree).mono
      (activeOrderPhaseCost_le_weight d D₁ R
        (Lax3Proofs.Refine.MassWeight.arenaWeight n G M))

/-! ## Axioms -/

#print axioms memberWeight_eq_arenaWeight
#print axioms activeChainWidthE_le_weight
#print axioms activeOrderPhase_weight_spec

end Lax3Proofs.Refine.OrderActiveBudget
