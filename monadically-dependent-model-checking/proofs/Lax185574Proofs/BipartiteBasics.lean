import Lax185574.BipartiteGraphs
import Lax185574Proofs.AtomicTypeBridge

/-!
Adjacency in the bipartite graph of a relation, and its atomic types:
the vertices of the left side have as many atomic types over the right
side as there are distinct neighborhoods.
-/

namespace Lax185574Proofs.BipartiteBasics

open Lax185574.BipartiteGraphs Lax185574.AtomicTypes Lax185574.Partitions

universe u v

variable {L : Type u} {R : Type v}

@[simp] theorem adj_inl_inr (E : L → R → Prop) (a : L) (b : R) :
    (bipartiteGraph E).Adj (.inl a) (.inr b) ↔ E a b := by
  simp [bipartiteGraph]

/-- The number of atomic types of the left side over the right side is
the number of distinct neighborhoods of left vertices. -/
theorem atomicTypeCount_eq_card [Fintype L] [Fintype R] [DecidableEq R]
    (E : L → R → Prop) [DecidableRel E] :
    atomicTypeCount (bipartiteGraph E) (Set.range Sum.inl) (Set.range Sum.inr) =
      (Finset.univ.image fun a => Finset.univ.filter (E a)).card := by
  rw [Lax185574Proofs.AtomicTypeBridge.atomicTypeCount_eq_partCount, partCount,
    show Set.range (Sum.inl : L → L ⊕ R) = Sum.inl '' Set.univ from Set.image_univ.symm,
    Set.image_image, ← Set.ncard_coe_finset, Finset.coe_image,
    Finset.coe_univ]
  refine Lax185574Proofs.AtomicTypeBridge.ncard_image_congr _ _ fun a _ a' _ => ?_
  rw [Quotient.eq, Lax185574Proofs.FlipBasics.atomicTypes_rel_iff']
  constructor
  · rintro (h | ⟨-, -, h⟩)
    · rw [Sum.inl_injective h]
    · ext b
      simpa using h (.inr b) ⟨b, rfl⟩
  · intro h
    right
    refine ⟨by simp, by simp, ?_⟩
    rintro _ ⟨b, rfl⟩
    have := congrArg (fun T => b ∈ T) h
    simpa using this

end Lax185574Proofs.BipartiteBasics
