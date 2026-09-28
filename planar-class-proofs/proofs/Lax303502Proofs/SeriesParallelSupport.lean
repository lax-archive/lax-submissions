import Lax68.SeriesParallelPlanar

set_option autoImplicit false
namespace Lax303502Proofs
open Lax68.SeriesParallel

theorem support_union {V : Type*} (G H : SimpleGraph V) :
    (G ⊔ H).support = G.support ∪ H.support := by
  ext v
  simp only [SimpleGraph.mem_support, SimpleGraph.sup_adj, Set.mem_union]
  exact exists_or

theorem edge_support {V : Type*} {s t : V} (hst : s ≠ t) :
    (edgeGraph s t).support = {s, t} := by
  ext v
  simp only [SimpleGraph.mem_support, edgeGraph, SimpleGraph.fromRel_adj,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, _, (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨_, rfl⟩ | ⟨_, rfl⟩)⟩ <;> simp
  · rintro (rfl | rfl)
    · exact ⟨t, hst, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨s, hst.symm, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩

end Lax303502Proofs
