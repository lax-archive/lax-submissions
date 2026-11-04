import Lax185574.FirstOrderLogic
import Mathlib.Data.Fin.VecNotation

/-!
---
title: Monadically dependent graph classes
type: definition
---
A graph class C *transduces the class of all graphs* if there are a
number k and a first-order formula ψ(x₀, x₁) with k colors such that
every graph H can be found inside a k-colored graph from C, with ψ
defining the edges of H. That is, there are a graph G ∈ C, a coloring of
G with k colors, and an injective map f from the vertices of H to the
vertices of G such that for all distinct vertices u and v of H

  u and v are adjacent in H ⟺ ψ(f(u), f(v)) holds in the colored G.

The class C is *monadically dependent* if it does not transduce the
class of all graphs.

# Formalization notes

This is the transduction-based definition of monadic dependence. A
general transduction also has a domain formula, which selects the
vertices of the output graph. It is not needed here, because the vertex
set of H is the image of f, and the class of all graphs is closed under
induced subgraphs. A transduction with domain formula δ(x) and edge
formula ψ that produces every graph gives an f as above (map H to the
vertices of its copy that δ selects). Conversely, f gives the
transduction whose domain formula is a fresh color marking the image of
f and whose edge formula is ψ(x₀, x₁) ∧ x₀ ≠ x₁. The conjunct x₀ ≠ x₁ is
needed because the condition above constrains ψ on distinct vertices
only, while the edge formula of a transduction defines the adjacency on
all pairs of selected vertices, and a vertex is not adjacent to itself.

The definition of the paper is of this form. It starts from a formula
φ(x, y), takes the graph with the edges uv such that φ(u, v) or φ(v, u)
holds, and asks for every finite graph as an induced subgraph. Such a φ
gives ψ = φ(x₀, x₁) ∨ φ(x₁, x₀) here. Conversely, a ψ as above serves as
φ, since on the image of f it holds of u and v in both orders or in
neither. So the two definitions agree.

Monadic dependence is often defined by forbidding the independence
property for formulas on the colorings of the graphs in C. By a theorem
of Baldwin and Shelah the two definitions agree.
-/

namespace Lax185574.MonadicDependence

open Lax185574.Graphs Lax185574.FirstOrderLogic

/-- The class `C` transduces the class of all graphs: some formula
`ψ(x₀, x₁)` with `k` colors defines every graph `H` on the image of an
injective map `f` into some `k`-colored graph `G ∈ C`. -/
def TransducesAllGraphs (C : GraphClass) : Prop :=
  ∃ (k : ℕ) (ψ : Formula (Fin k) 2),
    ∀ H : Graph, ∃ G ∈ C, ∃ (col : Fin k → Set (Fin G.n)) (f : Fin H.n ↪ Fin G.n),
      ∀ u v : Fin H.n, u ≠ v → (H.Adj u v ↔ ψ.Holds G col ![f u, f v])

/-- A graph class is monadically dependent if it does not transduce the
class of all graphs. -/
def MonadicallyDependent (C : GraphClass) : Prop :=
  ¬ TransducesAllGraphs C

end Lax185574.MonadicDependence
