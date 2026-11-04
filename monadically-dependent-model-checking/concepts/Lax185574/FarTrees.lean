import Lax185574.TypeTrees

/-!
---
title: The far tree
type: definition
---
For a partial graph G, k ∈ ℕ, q ≥ 1 and a nonempty tuple ā of at most k
vertices,

  ftree_{k,q}(ā) = {tree_{k+1,q−1}(b) | b ∈ V(G), dist(ā, b) > ρ⁻(k+1, q−1)}.

It is the set of type trees of the vertices far from ā.

# Formalization notes

dist(ā, b) > r means that no entry of ā is within distance r of b. The
far tree is a finite set of type trees. It is encoded as the sorted list
of the words of its trees, like the sets inside a type tree.
-/

namespace Lax185574.FarTrees

open Lax185574.PartialGraphs Lax185574.GaifmanGraph
open Lax185574.TypeTrees
open Lax3.DistFO (rhoMinus rhoPlus)

variable {V : Type*}

/-- `ftree_{k,q}(a)`: the type trees of the vertices far from `a`. -/
noncomputable def ftree (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (a : Fin ℓ → V) :
    Finset TypeTree :=
  finsetOf {ν | ∃ b : V,
    (∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) (q - 1)) (a i) b) ∧
    ν = tree G (k + 1) (q - 1) ![b]}

end Lax185574.FarTrees
