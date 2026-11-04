import Lax185574.DefinableFlipTransitivity
import Lax185574Proofs.FlipBasics

namespace Lax185574Proofs.DefinableFlipTransitivity

open Lax185574.Flips Lax185574.Partitions Lax185574.DefinableFlips
open Lax185574Proofs.FlipBasics

universe u

/--
---
conclusion: Lax185574.DefinableFlipTransitivity.isDefinableFlip_trans
---
Let `S₁` and `S₂` witness the two flips and put `S = S₁ ∪ S₂`. The
partition into atomic types over `S` in `G₀` refines the one over `S₁`
in `G₀`, and also the one over `S₂` in `G₁`: two vertices outside `S`
with the same neighbors in `S` lie in the same part over `S₁`, so their
adjacency to a vertex of `S₂` is preserved or complemented alike when
passing to `G₁`. A flip of a flip is a flip for a common refinement.
-/
theorem isDefinableFlip_trans {V : Type u} {G₀ G₁ G₂ : SimpleGraph V}
    {s₁ s₂ : ℕ} (h₁ : IsDefinableFlip G₀ s₁ G₁) (h₂ : IsDefinableFlip G₁ s₂ G₂) :
    IsDefinableFlip G₀ (s₁ + s₂) G₂ := by
  classical
  obtain ⟨S₁, hS₁, hf₁⟩ := h₁
  obtain ⟨S₂, hS₂, hf₂⟩ := h₂
  refine ⟨S₁ ∪ S₂, (Finset.card_union_le _ _).trans (Nat.add_le_add hS₁ hS₂), ?_⟩
  rw [Finset.coe_union]
  exact isFlip_trans hf₁ hf₂ (atomicTypes_anti G₀ Set.subset_union_left)
    (atomicTypes_union_le_of_isFlip hf₁)

end Lax185574Proofs.DefinableFlipTransitivity
