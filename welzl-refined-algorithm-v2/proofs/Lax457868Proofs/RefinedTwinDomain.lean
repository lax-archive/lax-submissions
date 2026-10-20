import Lax457868Proofs.DistinctNeighborhoodDomain

/-! The full-neighborhood quotient is needed only once. The two existing
trace partitions preserve distinct neighborhoods on the reduced ground set,
and a crossing bound on the initial quotient covers all original vertices. -/
namespace Lax457868Proofs.RefinedTwinDomain

open Lax457868Proofs.ReusedOriginal.Construction.NeighborhoodComplexity
open Lax457868Proofs.ReusedOriginal.Construction.TracePartitions
open Lax457868Proofs.ReusedOriginal.Construction.ListCrossing

/-- Every original neighborhood is represented in the full-ground quotient. -/
lemma full_partition_covers {n : ℕ} {G : SimpleGraph (Fin n)}
    {R : Set (Fin n)} (h : TracePartition G Set.univ Set.univ R) :
    ∀ v : Fin n, ∃ r ∈ R, G.neighborSet v = G.neighborSet r := by
  intro v
  refine ⟨h.representative v, h.representative_mem v (Set.mem_univ _), ?_⟩
  simpa [neighborhoodTrace] using (h.same_trace v (Set.mem_univ _)).symm

/-- Quotienting the ground side by its traces on `R` retains all distinctions
between the representatives of the first partition. -/
lemma dual_partition_separated {n : ℕ} {G : SimpleGraph (Fin n)}
    {A C W R S : Set (Fin n)} (hW : W ⊆ A)
    (hB : TracePartition G C W R) (hA : TracePartition G A R S) :
    Set.InjOn (neighborhoodTrace G S) R := by
  intro u hu v hv huv
  apply hB.reps_separated hu hv
  ext a
  by_cases ha : a ∈ W
  · have haA := hW ha
    let r := hA.representative a
    have hrS : r ∈ S := hA.representative_mem a haA
    have htrace := hA.same_trace a haA
    have hru : G.Adj r u ↔ G.Adj a u := by
      have h := Set.ext_iff.mp htrace u
      simpa [neighborhoodTrace, hu] using h
    have hrv : G.Adj r v ↔ G.Adj a v := by
      have h := Set.ext_iff.mp htrace v
      simpa [neighborhoodTrace, hv] using h
    have huvR : G.Adj u r ↔ G.Adj v r := by
      have h := Set.ext_iff.mp huv r
      simpa [neighborhoodTrace, hrS] using h
    have haUV : G.Adj u a ↔ G.Adj v a := by
      calc
        G.Adj u a ↔ G.Adj a u := G.adj_comm _ _
        _ ↔ G.Adj r u := hru.symm
        _ ↔ G.Adj u r := G.adj_comm _ _
        _ ↔ G.Adj v r := huvR
        _ ↔ G.Adj r v := G.adj_comm _ _
        _ ↔ G.Adj a v := hrv
        _ ↔ G.Adj v a := G.adj_comm _ _
    simpa [neighborhoodTrace, ha] using haUV
  · simp [neighborhoodTrace, ha]

/-- The final crossing estimate on the initial quotient implies the same
estimate for every vertex of the original graph, without changing the order. -/
lemma crossing_bound_of_cover {n K : ℕ} {G : SimpleGraph (Fin n)}
    {R : Set (Fin n)} {order : List (Fin n)}
    (hcover : ∀ v : Fin n, ∃ r ∈ R, G.neighborSet v = G.neighborSet r)
    (hbound : ∀ r ∈ R, crossingCount (G.neighborSet r) order ≤ K) :
    ∀ v : Fin n, crossingCount (G.neighborSet v) order ≤ K := by
  intro v
  obtain ⟨r, hr, heq⟩ := hcover v
  rw [heq]
  exact hbound r hr

end Lax457868Proofs.RefinedTwinDomain
