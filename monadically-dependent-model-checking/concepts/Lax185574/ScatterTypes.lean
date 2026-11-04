import Lax185574.TypeTrees
import Mathlib.Data.List.FinRange

/-!
---
title: Scatter types
type: definition
---
Let G be a partial graph. A set S of vertices is *r-scattered* if all
vertices of S have pairwise distance larger than r. Fix a linear order
on V(G). For X ⊆ V(G) and r ∈ ℕ, S_r(X) is the inclusion-wise maximal
r-scattered subset of X built by the greedy process that repeatedly adds
the least available vertex.

The *(k, q)-scatter type* stp^G_{k,q} is the function with domain

  {(r, tree_{k+i,q−i}(b)) | i ∈ [q], b ∈ V(G),
   r ∈ [9^{k+i} · ρ⁻(k+i, q−i)]}

given by stp^G_{k,q}(r, ν) = min(|S_r([ν]^G)|, k + q). For q = 0 the
domain is empty. A scatter type is represented canonically as the sorted
list of its triples (r, ν, stp_{k,q}(r, ν)), using the canonical
representation of ν. Its size ‖stp_{k,q}‖ is the size of this list.

# Formalization notes

The vertices are `Fin n`, ordered as numbers. The greedy process scans
the vertices in increasing order and adds a vertex of X when its
distance to every vertex added so far is larger than r. [k] = {1, …, k}
as in the paper, so i and r start at 1. The domain of stp^G_{k,q},
written domain(stp_{k,q}) in the paper, is `domain G k q`.

The scatter type is given by its graph, the finite set of the pairs
((r, ν), stp_{k,q}(r, ν)) with (r, ν) in its domain. As a finite set it is
encoded as the sorted list of the words of these pairs, by
`Lax185574.Encodings`. The word of a pair is r, then the word of ν,
then the value.
-/

namespace Lax185574.ScatterTypes

open Lax185574.PartialGraphs Lax185574.GaifmanGraph
open Lax185574.TypeTrees
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ}

/-- `S_r(X)`: the greedy maximal `r`-scattered subset of `X`, scanning
the vertices in increasing order. -/
noncomputable def greedyScattered (G : PartialGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    List (Fin n) :=
  open Classical in
  (List.finRange n).foldl
    (fun S v => if v ∈ X ∧ ∀ u ∈ S, ¬ WithinDist G.resolved r u v then S ++ [v] else S) []

/-- The domain `domain(stp_{k,q})` of the scatter type. -/
def domain (G : PartialGraph (Fin n)) (k q : ℕ) : Set (ℕ × TypeTree) :=
  {p | ∃ (i : ℕ) (b : Fin n), 1 ≤ i ∧ i ≤ q ∧ 1 ≤ p.1 ∧
    p.1 ≤ 9 ^ (k + i) * rhoMinus (k + i) (q - i) ∧
    p.2 = tree G (k + i) (q - i) ![b]}

/-- The value `min(|S_r([ν]^G)|, k + q)` at the pair `p = (r, ν)`. -/
noncomputable def value (G : PartialGraph (Fin n)) (k q : ℕ) (p : ℕ × TypeTree) : ℕ :=
  min (greedyScattered G p.1 (realizations G p.2)).length (k + q)

/-- The graph `{(x, f x) | x ∈ D}` of a function on a finite domain. -/
noncomputable def graphOn {α β : Type*} (D : Set α) (f : α → β) : Finset (α × β) :=
  finsetOf {p | p.1 ∈ D ∧ p.2 = f p.1}

/-- `stp^G_{k,q}`, as its graph: the pairs `((r, ν), stp(r, ν))` with
`(r, ν) ∈ domain(stp_{k,q})`. -/
noncomputable def stp (G : PartialGraph (Fin n)) (k q : ℕ) : Finset ((ℕ × TypeTree) × ℕ) :=
  graphOn (domain G k q) (value G k q)

end Lax185574.ScatterTypes
