import Lax195003.WelzlOrdersNeighborhoodComplexity

/-!
The elementary interface to the submitted neighborhood-complexity
definition used by the Welzl-order algorithm.

The paper speaks about the number of twin classes induced by a test set.
In the submitted concepts that number is `traceCount`; the first lemma below
checks that the particular trace count is one of the values over which
`neighborhoodComplexity` takes its supremum.  The second lemma is the form
used at every refinement step of the algorithm.
-/

namespace Lax235315Proofs.Construction.NeighborhoodComplexity

open Lax195003.WelzlOrdersNeighborhoodComplexity

/-- The trace of the neighborhood of `v` on `A`. -/
def neighborhoodTrace {V : Type*} (G : SimpleGraph V) (A : Set V)
    (v : V) : Set V :=
  G.neighborSet v ∩ A

lemma range_neighborhoodTrace {V : Type*} (G : SimpleGraph V) (A : Set V) :
    Set.range (neighborhoodTrace G A) =
      {S : Set V | ∃ v : V, S = G.neighborSet v ∩ A} := by
  ext S
  simp [neighborhoodTrace, eq_comm]

lemma ncard_image_neighborhoodTrace_le_traceCount {n : ℕ}
    (G : SimpleGraph (Fin n)) (A R : Set (Fin n)) :
    (neighborhoodTrace G A '' R).ncard ≤ traceCount G A := by
  unfold traceCount
  have hfinite :
      {S : Set (Fin n) | ∃ v : Fin n, S = G.neighborSet v ∩ A}.Finite := by
    rw [← range_neighborhoodTrace G A, ← Set.image_univ]
    exact Set.finite_univ.image _
  apply Set.ncard_le_ncard (ht := hfinite)
  intro S hS
  obtain ⟨v, -, rfl⟩ := hS
  exact ⟨v, rfl⟩

/-- Any set of vertices having pairwise distinct traces on `A` has at most
`traceCount G A` members. -/
lemma ncard_le_traceCount_of_injOn {n : ℕ} (G : SimpleGraph (Fin n))
    (A R : Set (Fin n))
    (hR : Set.InjOn (neighborhoodTrace G A) R) :
    R.ncard ≤ traceCount G A := by
  rw [← hR.ncard_image]
  exact ncard_image_neighborhoodTrace_le_traceCount G A R

/-- Every particular trace count is bounded by the graph's neighborhood
complexity at the cardinality of the test set. -/
lemma traceCount_le_neighborhoodComplexity {n : ℕ}
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

/-- On every nonempty test set, a linear-neighborhood-complexity constant
bounds the number of induced twin classes by `c * |A|`. -/
lemma traceCount_le_mul_ncard {n c : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    {A : Set (Fin n)} (hA : A.Nonempty) :
    traceCount G A ≤ c * A.ncard := by
  exact (traceCount_le_neighborhoodComplexity G A).trans
    (hG A.ncard (by have := hA.ncard_pos; omega))

/-- The representative-count estimate used twice in each iteration of the
paper's algorithm. -/
lemma ncard_le_mul_of_injOn {n c : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    {A R : Set (Fin n)} (hA : A.Nonempty)
    (hR : Set.InjOn (neighborhoodTrace G A) R) :
    R.ncard ≤ c * A.ncard :=
  (ncard_le_traceCount_of_injOn G A R hR).trans
    (traceCount_le_mul_ncard hG hA)

end Lax235315Proofs.Construction.NeighborhoodComplexity
