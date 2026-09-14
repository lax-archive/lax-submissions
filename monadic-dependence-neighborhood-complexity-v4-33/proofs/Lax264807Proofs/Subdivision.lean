import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
The pattern graphs for the weakly-sparse argument: the biclique
`K_{k,k}` and the `r`-subdivisions of complete graphs and bicliques,
each on a canonical vertex type so that containment statements can be
phrased with `⊑`.
-/

namespace Lax264807Proofs.Subdivision

/-- Vertex type of the `r`-subdivision of the complete graph `K_n`.
Either a principal vertex `.inl i` (with `i : Fin n`) or a subdivision
vertex `.inr (e, k)`, where `e : {p : Fin n × Fin n // p.1 < p.2}`
represents the edge `{e.1, e.2}` of `K_n` oriented by `<`, and
`k : Fin r` is its position along the path `e.1 ↝ e.2` (0-indexed). -/
abbrev SubdividedCliqueVert (n r : ℕ) : Type :=
  Fin n ⊕ ({p : Fin n × Fin n // p.1 < p.2} × Fin r)

/-- Vertex type of the `r`-subdivision of the biclique `K_{n,n}`.
Either a root (`.inl (.inl i)` = `aᵢ` or `.inl (.inr j)` = `bⱼ`) or a
subdivision vertex `.inr ((i, j), k)` = `π_{i,j,k+1}`, the `(k+1)`-st
interior vertex on the `a_i ↝ b_j` path (`k : Fin r`). -/
abbrev SubdividedBicliqueVert (n r : ℕ) : Type :=
  (Fin n ⊕ Fin n) ⊕ ((Fin n × Fin n) × Fin r)

/-- The `r`-subdivision of the complete graph on `Fin n`. Each edge
`{i, j}` of `K_n` (represented as the ordered pair `(i, j)` with `i < j`)
is replaced by a path of length `r + 1`:
`i — π₀ — π₁ — ⋯ — π_{r-1} — j`. For `r = 0` the graph equals `K_n`
(the subdivision-vertex component is indexed by `Fin 0 = ∅`, so it is
empty, and the principal-principal clause `r = 0` kicks in).

`SimpleGraph.fromRel` adds the `x ≠ y` guard and symmetrizes by
disjunction, so the catch-all `False` branch accounts for pattern pairs
whose reverse is handled by an earlier clause. -/
def subdividedClique (n r : ℕ) : SimpleGraph (SubdividedCliqueVert n r) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | .inl _, .inl _ => r = 0
    | .inl i, .inr ⟨e, k⟩ =>
        (i = e.val.1 ∧ k.val = 0) ∨ (i = e.val.2 ∧ k.val = r - 1)
    | .inr ⟨e, k⟩, .inr ⟨e', k'⟩ => e = e' ∧ k.val + 1 = k'.val
    | _, _ => False

/-- The `r`-subdivision of the biclique `K_{n,n}`. Each edge `a_i b_j` is
replaced by the `(r+1)`-edge path
`a_i — π_{i,j,1} — ⋯ — π_{i,j,r} — b_j`. For `r = 0` the graph equals
`K_{n,n}` (subdivision-vertex component empty; the root-root clauses
produce the biclique).

The thesis's star `r`-crossings augment this graph's adjacency without
changing its vertices, so they share this vertex type. -/
def subdividedBiclique (n r : ℕ) : SimpleGraph (SubdividedBicliqueVert n r) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | .inl (.inl _), .inl (.inr _) => r = 0
    | .inl (.inl i), .inr ⟨⟨a, _⟩, k⟩ => i = a ∧ k.val = 0
    | .inl (.inr j), .inr ⟨⟨_, b⟩, k⟩ => j = b ∧ k.val = r - 1
    | .inr ⟨e, k⟩, .inr ⟨e', k'⟩ => e = e' ∧ k.val + 1 = k'.val
    | _, _ => False

/-- The biclique of order `k` is the complete bipartite graph `K_{k,k}`
on vertex set `Fin k ⊕ Fin k`: sides `a_1,…,a_k` (the `Sum.inl i`) and
`b_1,…,b_k` (the `Sum.inr j`), with `a_i` adjacent to `b_j` for all
`i, j ∈ Fin k`.

"`G` contains the biclique of order `k` as a subgraph" (Mählmann, p. 22)
is `(biclique k).IsContained G` — i.e., an injective
graph homomorphism `biclique k →g G`, equivalently `2k` distinct vertices
of `G` forming the bipartite edge pattern, with no constraint on other
adjacencies. Mathlib exposes this relation via the scoped notation
`biclique k ⊑ G` and supplies `completeBipartiteGraph_isContained_iff`
for a finset-level characterization. -/
abbrev biclique (k : ℕ) : SimpleGraph (Fin k ⊕ Fin k) :=
  completeBipartiteGraph (Fin k) (Fin k)

end Lax264807Proofs.Subdivision
