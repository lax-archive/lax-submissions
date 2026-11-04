import Lax185574Proofs.ResolveRam.Glue.DistCmd
import Lax185574Proofs.Conversions.Ram.Encode
import Lax185574Proofs.Conversions.Ram.MergeSpec

/-!
The word of the partial graph after the resolve.

The final round of the glue program writes `H = resolve^±_{P,Q}(G)`.
Its word is the colors of `G`, then the graph of the edges and the graph
of the non-edges (`toWord_resolve`), each written row by row from a 0/1
matrix (`Conversions.Ram.writeGraph`). The matrices are those of `G`
with the unresolved pairs between the classes of `P` and `Q` added to the
edges for the sign `+` and to the non-edges for the sign `−`
(`edgeR`, `nonEdgeR`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.ConstructionSequences
open Lax185574.ResolveLift Lax185574Proofs.Conversions.Ram Lax185574Proofs.StpRam
open Lax185574Proofs.TreeAlgo

variable {n : ℕ}

/-- The pair `u, v` lies between the classes of `P` and `Q`. -/
def btw (G : PartialGraph (Fin n)) (P Q u v : ℕ) : Prop :=
  u ≠ v ∧ ((colN G u = P ∧ colN G v = Q) ∨ (colN G v = P ∧ colN G u = Q))

/-- The edges after the resolve, on numbers. -/
def edgeR (G : PartialGraph (Fin n)) (s : Bool) (P Q u v : ℕ) : Prop :=
  gA G.edge u v ∨ (s = true ∧ u < n ∧ v < n ∧ btw G P Q u v ∧ ¬ gA G.nonEdge u v)

/-- The non-edges after the resolve, on numbers. -/
def nonEdgeR (G : PartialGraph (Fin n)) (s : Bool) (P Q u v : ℕ) : Prop :=
  gA G.nonEdge u v ∨ (s = false ∧ u < n ∧ v < n ∧ btw G P Q u v ∧ ¬ gA G.edge u v)

theorem between_adj (G : PartialGraph (Fin n)) (P Q : ℕ) (u v : Fin n) :
    (between G P Q).Adj u v ↔ btw G P Q u v := by
  simp only [between, SimpleGraph.fromRel_adj, btw, colN, u.isLt, v.isLt, dif_pos, ne_eq,
    Fin.val_inj]

theorem gA_resolve_edge (G : PartialGraph (Fin n)) (s : Bool) (P Q u v : ℕ) :
    gA (resolveBy G s P Q).edge u v ↔ edgeR G s P Q u v := by
  unfold edgeR
  cases s with
  | true =>
    simp only [resolveBy, if_true, resolvePos, gA, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
      between_adj]
    constructor
    · rintro ⟨hu, hv, h | ⟨h1, h2⟩⟩
      · exact Or.inl ⟨hu, hv, h⟩
      · exact Or.inr ⟨trivial, hu, hv, h1, fun ⟨_, _, h⟩ => h2 h⟩
    · rintro (⟨hu, hv, h⟩ | ⟨-, hu, hv, h1, h2⟩)
      · exact ⟨hu, hv, Or.inl h⟩
      · exact ⟨hu, hv, Or.inr ⟨h1, fun h => h2 ⟨hu, hv, h⟩⟩⟩
  | false =>
    simp only [resolveBy, Bool.false_eq_true, if_false, resolveNeg]
    simp

theorem gA_resolve_nonEdge (G : PartialGraph (Fin n)) (s : Bool) (P Q u v : ℕ) :
    gA (resolveBy G s P Q).nonEdge u v ↔ nonEdgeR G s P Q u v := by
  unfold nonEdgeR
  cases s with
  | false =>
    simp only [resolveBy, Bool.false_eq_true, if_false, resolveNeg, gA, SimpleGraph.sup_adj,
      SimpleGraph.sdiff_adj, between_adj]
    constructor
    · rintro ⟨hu, hv, h | ⟨h1, h2⟩⟩
      · exact Or.inl ⟨hu, hv, h⟩
      · exact Or.inr ⟨trivial, hu, hv, h1, fun ⟨_, _, h⟩ => h2 h⟩
    · rintro (⟨hu, hv, h⟩ | ⟨-, hu, hv, h1, h2⟩)
      · exact ⟨hu, hv, Or.inl h⟩
      · exact ⟨hu, hv, Or.inr ⟨h1, fun h => h2 ⟨hu, hv, h⟩⟩⟩
  | true =>
    simp only [resolveBy, if_true, resolvePos]
    simp

/-- **The word of the partial graph after the resolve.** -/
theorem toWord_resolve (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) :
    toWord (resolveBy G s P Q) = (n :: List.ofFn G.color) ++ graphWord n (edgeR G s P Q) ++
      graphWord n (nonEdgeR G s P Q) := by
  have hc : (resolveBy G s P Q).color = G.color := by cases s <;> rfl
  rw [toWord_pg, hc, toWord_graph, toWord_graph]
  have e1 : gA (resolveBy G s P Q).edge = edgeR G s P Q := by
    funext u v; exact propext (gA_resolve_edge G s P Q u v)
  have e2 : gA (resolveBy G s P Q).nonEdge = nonEdgeR G s P Q := by
    funext u v; exact propext (gA_resolve_nonEdge G s P Q u v)
  rw [e1, e2]

end Lax185574Proofs.ResolveRam.Glue
