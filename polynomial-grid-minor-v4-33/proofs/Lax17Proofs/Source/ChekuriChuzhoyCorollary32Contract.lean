import Lax17Proofs.Source.ChekuriChuzhoyTheorem31Contract

namespace Lax17Proofs

universe u v w

/-!
# Contract for Chekuri--Chuzhoy Corollary 3.2

Corollary 3.2 applies the local routing theorem in the even clusters of a
path-of-sets system.  Structurally, it returns either a grid minor or a global
family of row paths from the first left nail set to the last right nail set,
with pairwise bridges available inside every even one-based cluster.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


/-- The vertex set of the subgraph spanned by a path-of-sets system: all
clusters together with all connector paths.  This is the vertex-level part of
the paper's graph `G'` spanned by the system. -/
noncomputable def pathOfSetsSpannedVertexSet {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w : ℕ}
    (P : PathOfSetsSystem G ell w) : Finset V := by
  classical
  exact
    (Finset.univ.biUnion fun i : Fin ell => P.cluster i) ∪
      (Finset.univ.biUnion fun i : Fin ell =>
        if h : i.1 + 1 < ell then
          (P.connector i h).toPathPacking.vertexSet
        else
          ∅)

/-- The non-grid output of Chekuri--Chuzhoy Corollary 3.2.

The rows connect the first left nail set to the last right nail set, stay in
the subgraph spanned by the path-of-sets system, meet each cluster in a
path-shaped trace, traverse the clusters in order, and have all pairwise
bridges inside each even one-based cluster. -/
structure Corollary32Rows {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w : ℕ}
    (P : PathOfSetsSystem G ell w) (q : ℕ) where
  /-- The global row paths. -/
  rows : PathPacking G (P.left P.firstIndex) (P.right P.lastIndex)
  /-- The number of row paths. -/
  rows_card : rows.card = q
  /-- The rows lie in the subgraph spanned by the path-of-sets system. -/
  rows_staysIn_spanned : rows.StaysIn (pathOfSetsSpannedVertexSet P)
  /-- Each row meets each cluster in a path-shaped trace. -/
  row_trace_cluster :
    ∀ (a : rows.Index) (i : Fin ell), (rows.path a).TraceOn (P.cluster i)
  /-- Along each row, cluster traces appear in the cluster order. -/
  row_clusters_ordered :
    ∀ (a : rows.Index) ⦃i j : Fin ell⦄,
      i.1 < j.1 →
        ∀ ⦃u v : V⦄,
          u ∈ (rows.path a).vertexSet → u ∈ P.cluster i →
            v ∈ (rows.path a).vertexSet → v ∈ P.cluster j →
              (rows.path a).Before u v
  /-- Every even one-based cluster supplies bridges between every pair of rows. -/
  bridge_in_even_cluster :
    ∀ i : Fin ell, (i.1 + 1) % 2 = 0 →
      rows.HasPairwiseBridgesIn (P.cluster i)

end ChekuriChuzhoy

namespace ChekuriChuzhoyContract


end ChekuriChuzhoyContract
end SimpleGraph

end Lax17Proofs
