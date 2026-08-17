import Lax3Proofs.Refine.CoverActiveCompact
import Lax3Proofs.RamCoverActiveMass

/-!
# Mathematical budgets for the active-cover program

The mutable search mask changes after every centre, but its search ball is
always contained in the fixed weak-reach cluster of that centre in the
ambient mask.  This file uses that fixed cluster as the executable loop's
row and vertex budget.  One CSR weight pays either quantity, and the sum of
those weights is exactly the active-cover double count.
-/

namespace Lax3Proofs.Refine.CoverActiveBudget

open Finset
open Lax3.ColoredGraphs
open Lax11.GraphEncoding
open Lax3Proofs.RamBfs (WD masked wd_iff_withinDist)
open Lax3Proofs.RamCover
open Lax3Proofs.RamCoverActive
open Lax3Proofs.RamCoverActiveMass
open Lax3Proofs.RamDriver (arenaSize)
open Lax3Proofs.Refine.CoverActiveCompact
open Lax3Proofs.Refine.CoverActiveInit
open Lax3Proofs.Refine.CoverActiveLoop
open Lax3Proofs.Refine.CoverActiveRadixLoop
open Lax3Proofs.Refine.CoverBlock (coverLoopK_eq)
open Lax3Proofs.Refine.MassMath (clusterAt)
open Lax3Proofs.Refine.MassWeight
  (arenaSize_le_arenaWeight arenaWeight arenaWeight_eq_csr csrW natW slotWeight wsum)
open Lax13Proofs.Reasoning.Lib

variable {n q r c : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre O : ℕ → ℕ} {π : Equiv.Perm (Fin n)}

/-- The finite presentation of one mathematical active cluster. -/
noncomputable def activeClusterFin (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) (r c : ℕ) : Finset (Fin n) :=
  (Set.toFinite (clusterAt G A₀ π centre r c)).toFinset

/-- The same cluster in the number representation consumed by `WD`. -/
noncomputable def activeClusterNat (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) (r c : ℕ) : Finset ℕ :=
  (activeClusterFin G A₀ π centre r c).image fun v : Fin n => (v : ℕ)

/-- A single CSR weight pays both one emitted vertex and its adjacency row. -/
noncomputable def activeBallWeight (n : ℕ) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (centre O : ℕ → ℕ)
    (r c : ℕ) : ℕ :=
  wsum (csrW n O) (clusterAt G A₀ π centre r c)

@[simp] theorem mem_activeClusterFin {v : Fin n} :
    v ∈ activeClusterFin G A₀ π centre r c ↔
      v ∈ clusterAt G A₀ π centre r c := by
  simp [activeClusterFin]

private theorem activeClusterNat_sum_rows
    (c : ℕ) :
    (∑ v ∈ activeClusterNat G A₀ π centre r c, Csr.rowLen O v) =
      ∑ v ∈ activeClusterFin G A₀ π centre r c, Csr.rowLen O (v : ℕ) := by
  rw [activeClusterNat, Finset.sum_image]
  intro a _ b _ hab
  exact Fin.val_injective hab

theorem activeClusterFin_rows_le_weight (c : ℕ) :
    (∑ v ∈ activeClusterFin G A₀ π centre r c, Csr.rowLen O (v : ℕ)) ≤
      activeBallWeight n G A₀ π centre O r c := by
  rw [activeBallWeight, wsum]
  change (∑ v ∈ activeClusterFin G A₀ π centre r c, Csr.rowLen O (v : ℕ)) ≤
    ∑ v ∈ activeClusterFin G A₀ π centre r c, csrW n O v
  exact Finset.sum_le_sum fun v _ => by simp [csrW]

theorem activeClusterFin_card_le_weight (c : ℕ) :
    (activeClusterFin G A₀ π centre r c).card ≤
      activeBallWeight n G A₀ π centre O r c := by
  rw [activeBallWeight, wsum]
  change (activeClusterFin G A₀ π centre r c).card ≤
    ∑ v ∈ activeClusterFin G A₀ π centre r c, csrW n O v
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v _ => by simp [csrW]

/-- The natural-number presentation of a streamed cluster has the same
row-sum budget as its finite-vertex presentation. -/
theorem activeClusterNat_rows_le_weight (c : ℕ) :
    (∑ v ∈ activeClusterNat G A₀ π centre r c, Csr.rowLen O v) ≤
      activeBallWeight n G A₀ π centre O r c := by
  rw [activeClusterNat_sum_rows]
  exact activeClusterFin_rows_le_weight c

/-- The natural-number presentation of a streamed cluster also fits in the
same vertex budget. -/
theorem activeClusterNat_card_le_weight (c : ℕ) :
    (activeClusterNat G A₀ π centre r c).card ≤
      activeBallWeight n G A₀ π centre O r c := by
  rw [activeClusterNat, Finset.card_image_of_injective _ Fin.val_injective]
  exact activeClusterFin_card_le_weight c

/-- The fixed mathematical cluster budgets every progressive-mask BFS turn.
No individual cluster-size bound is asserted. -/
theorem activeBallBudget
    (hcentres : CentresBy n q A₀ π centre) :
    ActiveBallBudget q r G A₀ centre O
      (activeBallWeight n G A₀ π centre O r)
      (activeBallWeight n G A₀ π centre O r) := by
  intro c hc M hmask
  refine ⟨activeClusterNat G A₀ π centre r c, ?_, ?_, ?_⟩
  · intro v hv _halive hwd
    have hcentre : centre c < n := hcentres.centre_lt c hc
    have hdist : WithinDist (masked G M) (2 * r)
        ⟨centre c, hcentre⟩ ⟨v, hv⟩ :=
      (wd_iff_withinDist hcentre hv).mp hwd
    have hcluster : InCluster (masked G A₀) π r (centre c) v := by
      apply (inCluster_iff hcentre hv).mpr
      apply (mem_wreach_iff_withinDist_pred
        (masked G A₀) π (2 * r) ⟨centre c, hcentre⟩ ⟨v, hv⟩).mpr
      rw [← masked_step hcentres hc hmask]
      exact hdist
    apply Finset.mem_image.mpr
    exact ⟨⟨v, hv⟩, mem_activeClusterFin.mpr hcluster, rfl⟩
  · rw [activeClusterNat_sum_rows]
    exact activeClusterFin_rows_le_weight c
  · rw [activeClusterNat, Finset.card_image_of_injective _ Fin.val_injective]
    exact activeClusterFin_card_le_weight c

/-! ## Closed cost -/

/-- The sum of the fixed ball budgets is paid by the active arena's CSR
weight, with the weak-reach degree as coefficient. -/
theorem sum_activeBallWeight_le {ns : ℕ} {T : ℕ → ℕ} {d : ℕ}
    (horder : ActiveOrderP G r d A₀ q π centre)
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T) :
    (∑ k ∈ range q, activeBallWeight n G A₀ π centre O r k) ≤
      d * (arenaWeight n G A₀ + 1) := by
  rw [arenaWeight_eq_csr hcsr A₀]
  exact activeClusterMassW_le (csrW n O) horder.centres horder.degree

theorem activeInitCost_eq (q : ℕ) : activeInitCost q = 29 * q + 13 := by
  rw [activeInitCost, coverLoopK_eq]
  simp only [sum_const_zero]
  omega

theorem activeLoopK_self_eq (q : ℕ) (w : ℕ → ℕ) :
    activeLoopK q w w =
      300 * (∑ k ∈ range q, w k) + 154 * q + 6 := by
  rw [activeLoopK, coverLoopK_eq]
  simp only [sum_add_distrib]
  ring

/-- Closed charge for initialization, active searches, and uniform radix
sorting.  The physical arrays remain carrier-sized, but the charge is
linear in the current arena weight. -/
def activeCoverCoreCost (n d a : ℕ) : ℕ :=
  (29 * a + 13) +
    ((300 * (d * (a + 1)) + 154 * a + 6) +
      (236 * Nat.clog 2 n * (d * a) +
        (28 * Nat.clog 2 n + 26) * a + 12 * Nat.clog 2 n + 14))

/-- Whole active-cover phase, including the compacted identity prefix. -/
def activeCoverCost (n d a : ℕ) : ℕ :=
  activeCoverCoreCost n d a + (11 * a + 10)

theorem activeCompactCost_le
    (hcentres : CentresBy n q A₀ π centre) :
    activeCompactCost q ≤ 11 * arenaWeight n G A₀ + 10 := by
  rw [activeCompactCost]
  have hq := centreCount_le_arenaWeight G hcentres
  omega

theorem activeCoverCoreCost_le {ns xp : ℕ} {T Xoff Xmem asg : ℕ → ℕ}
    {d : ℕ}
    (horder : ActiveOrderP G r d A₀ q π centre)
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T)
    (hraw : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    (hxp : xp ≤ d * arenaSize n A₀) :
    activeInitCost q +
        (activeLoopK q (activeBallWeight n G A₀ π centre O r)
            (activeBallWeight n G A₀ π centre O r) +
          radixCoverUniformCost n q Xoff) ≤
      activeCoverCoreCost n d (arenaWeight n G A₀) := by
  let a := arenaWeight n G A₀
  let b := Nat.clog 2 n
  let w := activeBallWeight n G A₀ π centre O r
  have hq : q ≤ a := centreCount_le_arenaWeight G horder.centres
  have hw : (∑ k ∈ range q, w k) ≤ d * (a + 1) :=
    sum_activeBallWeight_le horder hcsr
  have hsize : arenaSize n A₀ ≤ a :=
    arenaSize_le_arenaWeight n G A₀
  have hxpa : xp ≤ d * a :=
    le_trans hxp (Nat.mul_le_mul_left d hsize)
  have hi : 29 * q + 13 ≤ 29 * a + 13 := by omega
  have hl₁ : 300 * (∑ k ∈ range q, w k) ≤ 300 * (d * (a + 1)) :=
    Nat.mul_le_mul_left 300 hw
  have hl₂ : 154 * q ≤ 154 * a := Nat.mul_le_mul_left 154 hq
  have hl : 300 * (∑ k ∈ range q, w k) + 154 * q + 6 ≤
      300 * (d * (a + 1)) + 154 * a + 6 := by omega
  have hs₁ : 236 * b * xp ≤ 236 * b * (d * a) :=
    Nat.mul_le_mul_left (236 * b) hxpa
  have hs₂ : (28 * b + 26) * q ≤ (28 * b + 26) * a :=
    Nat.mul_le_mul_left (28 * b + 26) hq
  have hs : 236 * b * xp + (28 * b + 26) * q + 12 * b + 14 ≤
      236 * b * (d * a) + (28 * b + 26) * a + 12 * b + 14 := by omega
  rw [activeInitCost_eq, activeLoopK_self_eq, radixCoverUniformCost_eq hraw]
  change (29 * q + 13) +
      ((300 * (∑ k ∈ range q, w k) + 154 * q + 6) +
        (236 * b * xp + (28 * b + 26) * q + 12 * b + 14)) ≤
    (29 * a + 13) +
      ((300 * (d * (a + 1)) + 154 * a + 6) +
        (236 * b * (d * a) + (28 * b + 26) * a + 12 * b + 14))
  exact Nat.add_le_add hi (Nat.add_le_add hl hs)

/-! ## Axiom audit -/

#print axioms activeClusterNat_rows_le_weight
#print axioms activeClusterNat_card_le_weight
#print axioms activeBallBudget
#print axioms sum_activeBallWeight_le
#print axioms activeCoverCoreCost_le

end Lax3Proofs.Refine.CoverActiveBudget
