import Lax185574.DefinableFlips

/-!
---
title: Transitivity of definable flips
type: fact
---
Let G₁ be an s₁-definable flip of G₀ and G₂ be an s₂-definable flip of
G₁. Then G₂ is an (s₁ + s₂)-definable flip of G₀.

# Formalization notes

The three graphs share a vertex type, which may be infinite. The paper
states this as well known and refers to Lemma 2.6 in the full version
of the cited work on flipper games. With the definition of
`DefinableFlips`, the parameter set of G₂ over G₀ can be taken to be the
union of the two given parameter sets.
-/

namespace Lax185574.DefinableFlipTransitivity

open Lax185574.DefinableFlips

universe u

/-- **Transitivity of definable flips.** An `s₂`-definable flip of an
`s₁`-definable flip of `G₀` is an `(s₁ + s₂)`-definable flip of `G₀`. -/
axiom isDefinableFlip_trans {V : Type u} {G₀ G₁ G₂ : SimpleGraph V}
    {s₁ s₂ : ℕ} (h₁ : IsDefinableFlip G₀ s₁ G₁) (h₂ : IsDefinableFlip G₁ s₂ G₂) :
    IsDefinableFlip G₀ (s₁ + s₂) G₂

end Lax185574.DefinableFlipTransitivity
