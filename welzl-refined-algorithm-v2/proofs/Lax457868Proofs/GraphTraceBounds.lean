import Lax195003.WelzlOrdersNeighborhoodComplexity
import Lax457868Proofs.SamplerPhases

set_option autoImplicit false

namespace Lax457868Proofs.GraphTraceBounds

open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax457868Proofs.SamplerPhases

/-- The neighborhood of b restricted to the finite left vertex set A. -/
noncomputable def finiteNeighborhood {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (b : Fin n) : Finset (Fin n) := by
  classical
  exact A.filter (fun a => G.Adj b a)

private lemma traceCount_le_neighborhoodComplexity {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Set (Fin n)) :
    traceCount G A ≤ neighborhoodComplexity G A.ncard := by
  unfold neighborhoodComplexity
  apply le_csSup
  · refine ⟨2 ^ n, ?_⟩
    rintro q ⟨B, -, rfl⟩
    exact (Set.ncard_le_card
      {S : Set (Fin n) | ∃ v : Fin n, S = G.neighborSet v ∩ B}).trans_eq
      (by simp)
  · exact ⟨A, le_rfl, rfl⟩

private lemma traceCount_le_mul_card {n c : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    {Y : Finset (Fin n)} (hY : Y.Nonempty) :
    traceCount G (Y : Set (Fin n)) ≤ c * Y.card := by
  have hYpos : 1 ≤ (Y : Set (Fin n)).ncard := by
    rw [Set.ncard_coe_finset]
    exact Finset.card_pos.mpr hY
  exact (traceCount_le_neighborhoodComplexity G Y).trans
    (by simpa [Set.ncard_coe_finset] using hG (Y : Set (Fin n)).ncard hYpos)

private lemma finiteNeighborhood_inter_eq_trace {n : ℕ}
    (G : SimpleGraph (Fin n)) {A Y : Finset (Fin n)}
    (hYA : Y ⊆ A) (b : Fin n) :
    ((finiteNeighborhood G A b ∩ Y : Finset (Fin n)) : Set (Fin n)) =
      G.neighborSet b ∩ (Y : Set (Fin n)) := by
  ext a
  simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_inter,
    finiteNeighborhood, Finset.mem_filter, SimpleGraph.mem_neighborSet]
  constructor
  · rintro ⟨⟨_, hba⟩, haY⟩
    exact ⟨hba, haY⟩
  · rintro ⟨hba, haY⟩
    exact ⟨⟨hYA haY, hba⟩, haY⟩

/-- Primal finite traces on every nonempty restriction of the left side. -/
lemma finiteNeighborhood_primal_trace_bound {n c : ℕ}
    {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    (A B Y : Finset (Fin n)) (hYA : Y ⊆ A) (hY : Y.Nonempty) :
    (B.image (fun b => finiteNeighborhood G A b ∩ Y)).card ≤ c * Y.card := by
  classical
  let T := B.image (fun b => finiteNeighborhood G A b ∩ Y)
  have hT : T.card ≤ traceCount G (Y : Set (Fin n)) := by
    rw [← Set.ncard_coe_finset]
    unfold traceCount
    apply Set.ncard_le_ncard_of_injOn
      (fun S : Finset (Fin n) => (S : Set (Fin n)))
    · intro S hS
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hS
      exact ⟨b, finiteNeighborhood_inter_eq_trace G hYA b⟩
    · intro S _ T _ hST
      exact Finset.coe_injective hST
  exact hT.trans (traceCount_le_mul_card hG hY)

private lemma dual_label_eq_neighborhood {n : ℕ}
    (G : SimpleGraph (Fin n)) {A B' : Finset (Fin n)}
    (a : Fin n) (ha : a ∈ A) :
    B'.filter (fun b => a ∈ finiteNeighborhood G A b) =
      finiteNeighborhood G B' a := by
  classical
  ext b
  simp only [finiteNeighborhood, Finset.mem_filter]
  constructor
  · rintro ⟨hb, hA, hba⟩
    exact ⟨hb, hba.symm⟩
  · rintro ⟨hb, hab⟩
    exact ⟨hb, ha, hab.symm⟩

/-- Dual labels are primal neighborhood traces after swapping the two sides
of the restricted bipartite instance. -/
lemma finiteNeighborhood_dual_trace_bound {n c : ℕ}
    {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    (A B' : Finset (Fin n)) (hB' : B'.Nonempty) :
    (A.image (fun a => B'.filter (fun b => a ∈ finiteNeighborhood G A b))).card ≤
      c * B'.card := by
  classical
  have heq :
      A.image (fun a => B'.filter (fun b => a ∈ finiteNeighborhood G A b)) =
        A.image (fun a => finiteNeighborhood G B' a) := by
    apply Finset.image_congr
    intro a ha
    exact dual_label_eq_neighborhood G a ha
  rw [heq]
  have hfull (a : Fin n) : finiteNeighborhood G B' a ∩ B' =
      finiteNeighborhood G B' a := by
    apply Finset.inter_eq_left.mpr
    exact Finset.filter_subset _ _
  simpa only [hfull] using
    finiteNeighborhood_primal_trace_bound hG B' A B' subset_rfl hB'

/-- The sampler's trace classes inherit the same primal bound directly. -/
lemma traceClasses_finiteNeighborhood_bound {n c : ℕ}
    {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    (A B Y : Finset (Fin n)) (hYA : Y ⊆ A) (hY : Y.Nonempty) :
    (traceClasses (finiteNeighborhood G A) Y B).card ≤ c * Y.card := by
  change (B.image (fun b => finiteNeighborhood G A b ∩ Y)).card ≤ c * Y.card
  exact finiteNeighborhood_primal_trace_bound hG A B Y hYA hY

end Lax457868Proofs.GraphTraceBounds
