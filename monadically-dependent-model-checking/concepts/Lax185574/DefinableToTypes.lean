import Lax185574.LocalDefinability
import Lax185574.Width
import Lax185574.MonadicDependence

/-!
---
title: Local definability bounds the width
type: theorem
---
Let q ∈ ℕ and h ≔ 7^q. The following holds for every monadically
dependent graph class 𝒞 and all r, c, s, q₀ ∈ ℕ. If a
construction sequence of a graph G ∈ 𝒞 is radius-(r+h) definable with c
unary predicates, s parameters and rank q₀, then its radius-r depth-q
width is at most O_{𝒞,q,q₀,c}(1) · poly_{𝒞,q,q₀}(s).

# Formalization notes

The bound is spelled out as `F · (s + 1)^a`. The exponent `a` depends on
the class, `q` and `q₀`, and the factor `F` additionally on `c`. Neither
depends on `r` or `s`. The paper says that there is a radius increase
h depending on q alone. Its proof takes h = 7^q, the radius of
`Lax185574.LocalToGlobal`, and the statement here names this value,
because the algorithm of `Lax185574.FewTypes` computes the radius from
q.
-/

namespace Lax185574.DefinableToTypes

open Lax185574.Graphs Lax185574.MonadicDependence
open Lax185574.ConstructionSequences Lax185574.LocalDefinability Lax185574.PartialGraphs
open Lax185574.Width

/-- **Local definability bounds the width.** A construction sequence of
a member of a monadically dependent class that is radius-`(r + 7^q)`
definable with `c` unary predicates, `s` parameters and rank `q₀` has
radius-`r` depth-`q` width at most `F · (s + 1)^a`. -/
axiom width_le_of_isRadiusDefinable (q : ℕ) (C : GraphClass) (hC : MonadicallyDependent C)
    (q₀ : ℕ) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ, ∀ r s : ℕ, ∀ G ∈ C,
      ∀ seq : List (PartialGraph (Fin G.n)), IsConstructionSequence G.toSimpleGraph seq →
        IsRadiusDefinable G.toSimpleGraph seq (r + 7 ^ q) c s q₀ →
          width r q seq ≤ F * (s + 1) ^ a

end Lax185574.DefinableToTypes
