import Lax17Proofs.Source.FlowDefs
import Lax17Proofs.Source.Menger

namespace Lax17Proofs

universe u v w

/-!
# Integral vertex-capacitated path flows

This file proves the standard extraction step used in the Chekuri--Chuzhoy
boosting theorem: a path flow of value at least `k` with unit vertex congestion
contains `k` pairwise vertex-disjoint source-to-target paths.

The proof is a direct Menger argument.  If no such packing exists, finite
vertex-Menger gives a separator of size `< k`.  Every flow path must meet that
separator, so the total separator vertex load is at least the flow value, while
unit vertex congestion bounds the same load by the separator size.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {S T X : Finset V}

namespace OrientedPathFlow

omit [Fintype V] in
/-- A separator captures at least the full value of any path flow between the
two terminal sides. -/
theorem value_le_sum_vertexLoad_of_STSeparator
    (F : OrientedPathFlow G S T) (hsep : STSeparator G S T X) :
    F.value ≤ ∑ v ∈ X, F.vertexLoad v := by
  classical
  unfold value vertexLoad
  calc
    (∑ i : F.Index, F.weight i)
        ≤ ∑ i : F.Index, ∑ v ∈ X,
            if v ∈ (F.path i).vertexSet then F.weight i else 0 := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          rcases hsep (F.path i)
              (Or.inl ⟨F.source_mem i, F.target_mem i⟩) with
            ⟨v, hvPath, hvX⟩
          have hnonneg :
              ∀ x ∈ X,
                0 ≤ if x ∈ (F.path i).vertexSet then F.weight i else 0 := by
            intro x _hx
            by_cases hx : x ∈ (F.path i).vertexSet
            · simpa [hx] using F.weight_nonneg i
            · simp [hx]
          have hsingle :=
            Finset.single_le_sum hnonneg hvX
          have hterm :
              (if v ∈ (F.path i).vertexSet then F.weight i else 0) =
                F.weight i := by
            simp [hvPath]
          simpa [hterm] using hsingle
    _ = ∑ v ∈ X, ∑ i : F.Index,
            if v ∈ (F.path i).vertexSet then F.weight i else 0 := by
          rw [Finset.sum_comm]

/-- A unit-vertex-capacity path flow of value at least `k` yields `k`
node-disjoint paths. -/
theorem hasDisjointSTPaths_of_unitVertexCapacityValueAtLeast
    {k : ℕ}
    (hflow : OrientedPathFlow.HasUnitVertexCapacityValueAtLeast G S T k) :
    HasDisjointSTPaths G S T k := by
  classical
  rcases hflow with ⟨F, hvalue, hcapacity⟩
  rcases Menger.finite_vertex_menger_sharp G S T k with hpaths | hsep
  · exact hpaths
  · rcases hsep with ⟨X, hXcard, hseparator⟩
    have hload_lower : F.value ≤ ∑ v ∈ X, F.vertexLoad v :=
      F.value_le_sum_vertexLoad_of_STSeparator hseparator
    have hload_upper : ∑ v ∈ X, F.vertexLoad v ≤ ∑ v ∈ X, (1 : ℚ) := by
      exact Finset.sum_le_sum fun v _hv => hcapacity v
    have hsum_card : (∑ v ∈ X, (1 : ℚ)) = X.card := by
      simp
    have hcard_ge : (k : ℚ) ≤ (X.card : ℚ) := by
      calc
        (k : ℚ) ≤ F.value := hvalue
        _ ≤ ∑ v ∈ X, F.vertexLoad v := hload_lower
        _ ≤ ∑ v ∈ X, (1 : ℚ) := hload_upper
        _ = (X.card : ℚ) := hsum_card
    have hcard_lt : (X.card : ℚ) < (k : ℚ) := by
      exact_mod_cast hXcard
    linarith

end OrientedPathFlow

namespace FlowIntegrality

/-- Contract-shaped name for the vertex-capacitated integral-flow extraction,
proved from finite vertex-Menger. -/
theorem unitVertexCapacityFlow_hasDisjointSTPaths
    {k : ℕ}
    (hflow : OrientedPathFlow.HasUnitVertexCapacityValueAtLeast G S T k) :
    HasDisjointSTPaths G S T k :=
  OrientedPathFlow.hasDisjointSTPaths_of_unitVertexCapacityValueAtLeast hflow

end FlowIntegrality

end SimpleGraph

end Lax17Proofs
