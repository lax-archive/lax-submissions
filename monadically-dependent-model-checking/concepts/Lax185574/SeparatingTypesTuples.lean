import Lax185574.Colorings
import Lax185574.FirstOrderTypes
import Lax185574.GraphBalls

/-!
---
title: Few types far from a parameter set, with a fixed tuple of parameters
type: lemma
---
For every q, k, c ∈ ℕ there are numbers r = r(q) and T = T(q, k, c)
with the following property. Let H be a graph expanded by at most c
unary predicates and U ⊆ V(H). Fix a tuple ū of vertices of U of finite
length. Let F ≔ { a ∈ V(H) : dist^H(a, U) > r }. Then

  |{ tp^H_q(ā ū/U) : ā ∈ F^k }| ≤ T(q, k, c).

# Formalization notes

The quantifier order is that of `SeparatingTypes`: r depends on q only,
and T on q, k and c only. In particular T does not depend on the length
m of ū. The tuple ā ū is the concatenation `Fin.append ā ū` of length
k + m. The far set F is the complement of the ball Ball^H_r[U] of
`GraphBalls.graphBall`. As in `SeparatingTypes`, the graph
is finite and its expansion has exactly c, possibly empty, color sets.
-/

namespace Lax185574.SeparatingTypesTuples

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.FirstOrderTypes Lax185574.Colorings Lax185574.GraphBalls

universe z

/-- **Few types far from a parameter set, with fixed parameters.** For a
fixed tuple `ū` from `U`, the tuples `ā ū` with `ā` a `k`-tuple far from
`U` realize at most `T(q, k, c)` types of quantifier rank `q` over `U`,
independently of the length of `ū`. -/
axiom ncard_rankTypeOver_append_le (q : ℕ) :
    ∃ r : ℕ, ∀ k c : ℕ, ∃ T : ℕ,
      ∀ (V : Type z) [Finite V] (G : SimpleGraph V) (colors : Fin c → Set V)
        (U : Set V) (m : ℕ) (u : Fin m → V), (∀ i, u i ∈ U) →
        ((fun a : Fin k → V =>
            @rankTypeOver (withColors Language.graph c) V (expansion G colors) q U
              (k + m) (Fin.append a u)) ''
          {a | ∀ i, a i ∉ graphBall G r U}).ncard ≤ T

end Lax185574.SeparatingTypesTuples
