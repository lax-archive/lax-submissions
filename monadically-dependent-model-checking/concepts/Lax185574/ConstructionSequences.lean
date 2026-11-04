import Lax185574.PartialGraphs

/-!
---
title: Construction sequences
type: definition
---
For colors P, Q and a partial graph G, the partial graphs merge_{P,Q}(G)
(for P ≠ Q), resolve⁺_{P,Q}(G) and resolve⁻_{P,Q}(G) are obtained from G
by leaving everything unchanged, apart from the following:

- merge_{P,Q}(G): P^H = P^G ∪ Q^G and Q^H = ∅, for P ≠ Q;
- resolve⁺_{P,Q}(G): E(H) = E(G) ∪ (P^G Q^G ∖ N(G));
- resolve⁻_{P,Q}(G): N(H) = N(G) ∪ (P^G Q^G ∖ E(G)).

Here P^G Q^G is the set of pairs xy of distinct vertices with x ∈ P^G and
y ∈ Q^G. After either resolve, every pair in P^G Q^G is resolved.

An *initial* partial graph has no resolved pairs, and every part is a
singleton. A *construction sequence* of a graph G = (V, E) is a sequence
G₁, …, G_λ of partial graphs with vertex set V such that G₁ is initial,
every step is one merge or one resolve, and G_λ has a single part,
E(G_λ) = E and N(G_λ) = (V choose 2) ∖ E.

# Formalization notes

A sequence is a nonempty list of partial graphs. Its first entry is G₁,
and the step condition relates consecutive entries `s[t]` and `s[t+1]`.
"Every part is a singleton" says that the coloring is injective, and "a
single part" says that all vertices have the same color. The colors P
and Q of a step are arbitrary natural numbers, as in the paper. A resolve naming a color that no vertex
has, or a merge whose second color no vertex has, changes nothing, and
is still counted as a step. Such steps only lengthen a sequence. The pairs `P^G Q^G` are built with `SimpleGraph.fromRel`,
which symmetrizes the relation and removes the diagonal.

The paper defines construction sequences twice, in the technical
overview through merges and resolves of parts, and in the preliminaries
of the model-checking part through the operators on colors above. Both
passages describe the same sequences. A merge of two distinct parts is a
merge of their colors, and a resolve of two parts is a resolve of their
colors.

Algorithms receive and produce a construction sequence on `Fin n` as a
`Script`: the colors of the initial partial graph, which has no resolved
pairs, and the list of the steps. `Script.run` is the sequence it
produces, the initial partial graph followed by the results of the
steps. The derived encoding of `Lax185574.Encoding` writes a script as
n, the n colors, the number of steps, and then each step as three
numbers, an opcode (0 for a merge, 1 for a positive resolve and 2 for a
negative resolve) followed by the colors P and Q. Nothing in a script
forces its colors to be distinct, or its sequence to be a construction
sequence of a particular graph. Those are properties of the sequence,
stated through `IsConstructionSequence` where they are needed.
-/

namespace Lax185574.ConstructionSequences

open Lax185574.PartialGraphs

universe z

variable {V : Type z}

/-- The pairs `P^G Q^G`: distinct vertices, one of color `P` and the
other of color `Q`. -/
def between (G : PartialGraph V) (P Q : ℕ) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => G.color x = P ∧ G.color y = Q

/-- `merge_{P,Q}(G)`: the vertices of color `Q` get color `P`. -/
def merge (G : PartialGraph V) (P Q : ℕ) : PartialGraph V :=
  { G with color := fun v => if G.color v = Q then P else G.color v }

/-- `resolve⁺_{P,Q}(G)`: the unresolved pairs in `P^G Q^G` become
edges. -/
def resolvePos (G : PartialGraph V) (P Q : ℕ) : PartialGraph V where
  edge := G.edge ⊔ (between G P Q \ G.nonEdge)
  nonEdge := G.nonEdge
  disjoint := disjoint_sup_left.2 ⟨G.disjoint, disjoint_sdiff_self_left⟩
  color := G.color

/-- `resolve⁻_{P,Q}(G)`: the unresolved pairs in `P^G Q^G` become
non-edges. -/
def resolveNeg (G : PartialGraph V) (P Q : ℕ) : PartialGraph V where
  edge := G.edge
  nonEdge := G.nonEdge ⊔ (between G P Q \ G.edge)
  disjoint := disjoint_sup_right.2 ⟨G.disjoint, disjoint_sdiff_self_right⟩
  color := G.color

/-- An initial partial graph: no resolved pairs, and every part is a
singleton. -/
def IsInitial (G : PartialGraph V) : Prop :=
  G.edge = ⊥ ∧ G.nonEdge = ⊥ ∧ Function.Injective G.color

/-- `H` is obtained from `G` by one merge or one resolve. -/
def IsStep (G H : PartialGraph V) : Prop :=
  ∃ P Q : ℕ, (P ≠ Q ∧ H = merge G P Q) ∨ H = resolvePos G P Q ∨
    H = resolveNeg G P Q

/-- `s` is a construction sequence of the graph `G`: it starts with an
initial partial graph, each entry is obtained from the previous one by
one merge or one resolve, and the last entry has a single part, the
edges of `G` as edges and the non-edges of `G` as non-edges. -/
def IsConstructionSequence (G : SimpleGraph V) (s : List (PartialGraph V)) :
    Prop :=
  ∃ h : s ≠ [],
    IsInitial (s.head h) ∧
    (∀ (t : ℕ) (ht : t + 1 < s.length), IsStep s[t] s[t + 1]) ∧
    (∀ u v : V, (s.getLast h).color u = (s.getLast h).color v) ∧
    (s.getLast h).edge = G ∧ (s.getLast h).nonEdge = Gᶜ

open Lax185574.Encoding

/-- One step of a construction sequence. -/
inductive Step
  /-- `merge_{P,Q}`. -/
  | merge (P Q : ℕ)
  /-- `resolve⁺_{P,Q}`. -/
  | resolvePos (P Q : ℕ)
  /-- `resolve⁻_{P,Q}`. -/
  | resolveNeg (P Q : ℕ)
  deriving Encode

/-- The partial graph obtained by applying a step. -/
def apply (G : PartialGraph V) : Step → PartialGraph V
  | .merge P Q => merge G P Q
  | .resolvePos P Q => resolvePos G P Q
  | .resolveNeg P Q => resolveNeg G P Q

/-- The partial graph with no resolved pairs and the given colors. -/
def unresolved (color : V → ℕ) : PartialGraph V where
  edge := ⊥
  nonEdge := ⊥
  disjoint := disjoint_bot_left
  color := color

/-- A construction script on `Fin n`: the colors of the initial partial
graph, which has no resolved pairs, and the steps. -/
structure Script (n : ℕ) where
  /-- The colors of the initial partial graph. -/
  colors : Fin n → ℕ
  /-- The steps, in order. -/
  steps : List Step
  deriving Encode

/-- The sequence produced by a script: the initial partial graph
followed by the results of the steps. -/
def Script.run {n : ℕ} (σ : Script n) : List (PartialGraph (Fin n)) :=
  σ.steps.scanl apply (unresolved σ.colors)

/-- Every number in the encoding of the script `σ` is at most the
length of the encoding plus `n`. This holds when the colors of the
initial partial graph and of the steps are vertices. It lets an
algorithm pass the script on to another one, whose word length depends
on the numbers of its input. -/
def Script.HasSmallNumbers {n : ℕ} (σ : Script n) : Prop :=
  ∀ v ∈ encode σ, v ≤ (encode σ).length + n

/-- The list `y` encodes the sequence `s` of partial graphs on `n`
vertices: it is the encoding of a script that produces `s`. -/
def EncodesSequence {n : ℕ} (y : List ℕ) (s : List (PartialGraph (Fin n))) :
    Prop :=
  ∃ σ : Script n, y = encode σ ∧ s = σ.run

end Lax185574.ConstructionSequences
