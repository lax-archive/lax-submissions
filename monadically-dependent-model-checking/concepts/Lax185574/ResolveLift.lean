import Lax185574.TypeTrees
import Lax185574.ConstructionSequences
import Lax185574.DistanceMatrix
import Lax185574.Algorithms

/-!
---
title: Lifting type trees through a resolve
type: lemma
---
Let k ≥ 1 and q ∈ ℕ. Given a partial graph G, its distance matrix D_G,
colors P, Q, a sign ±, and (tree^G_{k,q}(a) : a ∈ V(G)), one can compute
H = resolve^±_{P,Q}(G), its distance matrix D_H, and
(tree^H_{k,q}(a) : a ∈ V(G)) in time

  |G|² · poly_{k,q}(M + T),

where

  M = max_{a ∈ V(G)} ‖tree^G_{k,q}(a)‖,
  T = max_{a ∈ V(G)} |{tree^G_{k+i,q−i}(v̄) | 0 ≤ i ≤ q, ℓ ∈ [k+i],
                       v̄ ∈ (Ball^H_{ρ⁺(k,q)}(a))^ℓ}|.

Each output tree has size poly_{k,q}(T).

# Formalization notes

The algorithm is an algorithm in the sense of `Lax185574.Algorithms`,
one for all k and q. Its input is the tuple of G, its distance matrix,
P, Q, the sign and the family of type trees, with the encodings of
`Lax185574.Encodings`. The sign is a Boolean, `true` for + and `false`
for −. The output is the triple of H, its distance matrix and the new
family. The partial graph is on `Fin n`, so |G| = n. M is
`maxTreeSize G k q`, the time is `O(n² · (M + T + 1)^a)`, and each new
tree has an encoding of length at most `c · (T + 1)^a`, where the degree
`a` and the constant `c` may depend on k and q. The second factor of
the time is increased by one, so that it is positive. The set in the
definition of T collects trees of G of tuples from balls in H.
-/

namespace Lax185574.ResolveLift

open Lax185574.Encoding Lax185574.Algorithms
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ConstructionSequences
open Lax185574.DistanceMatrix
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ}

/-- `resolve^±_{P,Q}(G)`, positive for `true`. -/
def resolveBy (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) : PartialGraph (Fin n) :=
  if s then resolvePos G P Q else resolveNeg G P Q

/-- The parameter `T`: the largest number of type trees in `G` of
tuples from a ball of radius `ρ⁺(k, q)` in `H`, over all ranks
`(k+i, q−i)` and arities `ℓ ∈ [k+i]`. -/
noncomputable def treeCount (G H : PartialGraph (Fin n)) (k q : ℕ) : ℕ :=
  Finset.univ.sup fun a : Fin n =>
    Set.ncard {τ : TypeTree | ∃ (i ℓ : ℕ) (v : Fin ℓ → Fin n), i ≤ q ∧ 1 ≤ ℓ ∧ ℓ ≤ k + i ∧
      (∀ j, v j ∈ H.ball (rhoPlus k q) a) ∧ τ = tree G (k + i) (q - i) v}

/-- **Resolve lift.** One algorithm computes the partial graph `H` after
a resolve, its distance matrix and the type trees of all vertices in it,
from the partial graph `G` before, its distance matrix, `P`, `Q`, the
sign and its type trees, in time `O(n² · (M + T + 1)^a)`. Each new tree
has size `O((T + 1)^a)`. -/
axiom exists_program_resolveLift :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), 1 ≤ k →
        let H := resolveBy G s P Q
        let T := treeCount G H k q
        A.Computes c (G, distMatrix G, P, Q, s, family G k q) (H, distMatrix H, family H k q)
            (n ^ 2 * (maxTreeSize G k q + T + 1) ^ a) ∧
          ∀ b : Fin n, (encode (tree H k q ![b])).length ≤ c * (T + 1) ^ a

end Lax185574.ResolveLift
