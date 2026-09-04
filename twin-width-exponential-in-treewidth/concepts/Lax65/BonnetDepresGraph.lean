import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: The Bonnet–Déprés graph
type: definition
---
Fix a real $\varepsilon$ and an integer $t$, and set

$$C_t = \frac{2^{(1-\varepsilon)t}}{\varepsilon}, \qquad
f(t) = \left\lceil 2 + C_t\, 2^{(1-\varepsilon)t\,(2 + C_t\,(2^{(1-\varepsilon)t} + 1))} \right\rceil .$$

Let $T$ be the full $2^t$-ary tree of depth $f(t)$, i.e. with root-to-leaf
paths on $f(t)$ edges, and let $X$ be a set of $t$ vertices, identified with
$[t]$. The vertex set of $G_{t,\varepsilon}$ is $X \uplus V(T)$. Its edges
are such that $X$ is an independent set, the subgraph on $V(T)$ is $T$, the
root of $T$ has no neighbour in $X$, and the $2^t$ children of every internal
node of $T$ each have a distinct neighbourhood in $X$. This defines a single
graph up to isomorphism.

# Formalization notes

A node of `T` at level ℓ is the sequence of the ℓ neighbourhoods in `X`
chosen along the path from the root, one subset of `X` per edge, and the last
entry is the node's own neighbourhood in `X`. The 2ᵗ children of a node are
thus indexed by the subsets of `X`, which makes `T` the full 2ᵗ-ary tree and
gives the children distinct neighbourhoods by construction. The parameters
`ε` and `t` are free in the definition; the paper's standing constraints
0 < ε ≤ 1/2 and t > 1/ε are hypotheses of the statements about the graph.
-/

namespace Lax65.BonnetDepresGraph

/-- The constant `C_t = 2^{(1-ε)t} / ε`. -/
noncomputable def C (ε : ℝ) (t : ℕ) : ℝ :=
  2 ^ ((1 - ε) * t) / ε

/-- The depth `f(t) = ⌈2 + C_t · 2^{(1-ε)t (2 + C_t (2^{(1-ε)t} + 1))}⌉` of the
tree. -/
noncomputable def f (ε : ℝ) (t : ℕ) : ℕ :=
  ⌈2 + C ε t * 2 ^ ((1 - ε) * t * (2 + C ε t * (2 ^ ((1 - ε) * t) + 1)))⌉₊

/-- A node of the full `2^t`-ary tree of depth `depth`: its level `ℓ ≤ depth`
together with the neighbourhood in `X = Fin t` chosen on each of the `ℓ`
edges of the path from the root. -/
abbrev TreeNode (t depth : ℕ) : Type :=
  Σ ℓ : Fin (depth + 1), Fin ℓ.val → Finset (Fin t)

/-- `u` is the parent of `v` in the tree: the path of `v` extends the path of
`u` by one edge. -/
def IsParent {t depth : ℕ} (u v : TreeNode t depth) : Prop :=
  ∃ h : v.1.val = u.1.val + 1, ∀ i : Fin u.1.val, v.2 ⟨i.val, by omega⟩ = u.2 i

/-- The neighbourhood in `X` of a node other than the root: the subset chosen
on the last edge of its path. -/
def apexNeighborhood {t depth : ℕ} (v : TreeNode t depth) (h : 0 < v.1.val) :
    Finset (Fin t) :=
  v.2 ⟨v.1.val - 1, by omega⟩

/-- The vertices of `G_{t,ε}`: the apex set `X = Fin t` and the nodes of
`T`. -/
abbrev Vertex (t depth : ℕ) : Type :=
  Fin t ⊕ TreeNode t depth

/-- The edges: a node of `T` and one of its children, or an apex `x` and a
node other than the root whose neighbourhood in `X` contains `x`. -/
def EdgeRel {t depth : ℕ} : Vertex t depth → Vertex t depth → Prop
  | Sum.inr u, Sum.inr v => IsParent u v
  | Sum.inl x, Sum.inr v => ∃ h : 0 < v.1.val, x ∈ apexNeighborhood v h
  | _, _ => False

/-- The graph on the apex set `Fin t` and the full `2^t`-ary tree of depth
`depth`. -/
def graph (t depth : ℕ) : SimpleGraph (Vertex t depth) :=
  SimpleGraph.fromRel EdgeRel

/-- The graph `G_{t,ε}`: the tree has depth `f(t)`. -/
noncomputable def bonnetDepres (ε : ℝ) (t : ℕ) : SimpleGraph (Vertex t (f ε t)) :=
  graph t (f ε t)

end Lax65.BonnetDepresGraph
