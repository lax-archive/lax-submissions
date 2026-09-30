import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lax909950.EdgeDensity
import Lax909950.LowDegree

namespace Lax909950Proofs

open Lax909950

/--
---
conclusion: Lax909950.LowDegree.exists_degree_le_five
---
If every vertex had degree at least $6$, the degree sum $2e$ would be at least
$6v$, contradicting the edge density bound $e \leq 3v - 6$. Graphs with at most
$6$ vertices are handled directly.
-/
theorem exists_degree_le_five {V : Type*} [Finite V] [Nonempty V] {G : SimpleGraph V}
    (hG : Lax68.Planar.IsPlanar G) :
    ∃ x : V, (G.neighborSet x).ncard ≤ 5 := by
  classical
  have := Fintype.ofFinite V
  have hdeg : ∀ x, (G.neighborSet x).ncard = G.degree x := fun x => by
    rw [← G.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  simp_rw [hdeg]
  by_cases hsmall : Fintype.card V ≤ 6
  · obtain ⟨x⟩ := ‹Nonempty V›
    exact ⟨x, by have := G.degree_lt_card_verts x; omega⟩
  · by_contra hcon
    push Not at hcon
    have hV : 3 ≤ Nat.card V := by rw [Nat.card_eq_fintype_card]; omega
    have hE := EdgeDensity.edge_density hG hV
    rw [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card', Set.toFinset_card,
      ← SimpleGraph.edgeFinset_card] at hE
    have hsum := G.sum_degrees_eq_twice_card_edges
    have hlow : ∑ x : V, 6 ≤ ∑ x : V, G.degree x :=
      Finset.sum_le_sum fun x _ => hcon x
    simp at hlow
    omega

end Lax909950Proofs
