import Mathlib.Data.List.Basic

/-!
---
title: String homomorphisms
type: definition
---
A *string homomorphism* $h : A^* \to B^*$ is a function that applies a fixed map
$A \to B^*$ to every letter of the input and concatenates the results; a letter
may be erased or replaced by a longer string. It is a homomorphism of the free
monoids, $h(uv) = h(u)h(v)$. Homomorphisms are among the prime rational
functions (Theorem B.2.6), and the complement of the graph of a homomorphism is
a rational relation (Claim B.1.7), which is the observation behind the
undecidability of equivalence of rational relations.

# Formalization notes

`homOf φ` is the homomorphism determined by `φ : A → List B`.
-/

namespace Lax132576.StringHomomorphisms

/-- The string homomorphism that applies `φ` to every letter and concatenates the
results. -/
def homOf {A B : Type} (φ : A → List B) : List A → List B := fun w => (w.map φ).flatten

end Lax132576.StringHomomorphisms
