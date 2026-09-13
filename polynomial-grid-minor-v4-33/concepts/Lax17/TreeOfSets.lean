import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Lax17.Degree
import Lax17.PathOfSets

/-!
---
title: Strong tree-of-sets systems
type: definition
---
A tree-of-sets system replaces the linear order of a path-of-sets system by a
subcubic tree.  Its vertices index disjoint connected clusters, and each
tree edge has a linkage between equal-size interfaces in its endpoint
clusters.  A strong system makes every interface well-linked and every pair of
interfaces incident with one cluster mutually linked inside that cluster.
-/

namespace Lax17.TreeOfSets

universe u

open Lax17.Degree
open Lax17.Linkedness
open Lax17.PathOfSets
open Lax17.Paths

/-- A subcubic tree-of-sets system with `m` clusters and width `w`. -/
structure System {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (m w : ℕ) where
  clusterCount_pos : 0 < m
  width_pos : 0 < w
  metaTree : SimpleGraph (Fin m)
  meta_isTree : metaTree.IsTree
  meta_subcubic : MaximumAtMost metaTree 3
  cluster : Fin m → Finset V
  cluster_connected : ∀ i : Fin m, IsCluster G (cluster i)
  cluster_disjoint :
    ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (cluster i) (cluster j)
  interface :
    (i j : Fin m) → metaTree.Adj i j → Finset V
  interface_subset :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      interface i j hij ⊆ cluster i
  interface_card :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      (interface i j hij).card = w
  incident_interfaces_disjoint :
    ∀ {i j k : Fin m} (hij : metaTree.Adj i j)
      (hik : metaTree.Adj i k),
        j ≠ k → Disjoint (interface i j hij) (interface i k hik)
  connector :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      VertexLinkage G (interface i j hij)
        (interface j i (metaTree.symm.symm i j hij)) w
  connector_avoids_clusters :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j)
      (r : Fin m) (a : Fin w),
        ((connector i j hij).path a).InternallyAvoids (cluster r)
  connectors_disjoint :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j)
      (p q : Fin m) (hpq : metaTree.Adj p q),
        s(i, j) ≠ s(p, q) →
          ∀ a b : Fin w,
            Disjoint ((connector i j hij).path a).vertices
              ((connector p q hpq).path b).vertices

/-- A strong tree-of-sets system. -/
structure StrongSystem {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (m w : ℕ) extends System G m w where
  interface_well_linked :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      NodeWellLinkedIn G (cluster i) (interface i j hij)
  incident_interfaces_linked :
    ∀ {i j k : Fin m} (hij : metaTree.Adj i j)
      (hik : metaTree.Adj i k),
        j ≠ k →
          NodeLinkedIn G (cluster i)
            (interface i j hij) (interface i k hik)

/-- The meta-tree contains an ordered simple path with `ℓ` vertices. -/
def HasMetaPath {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {m w : ℕ}
    (T : StrongSystem G m w) (ℓ : ℕ) : Prop :=
  ∃ order : Fin ℓ → Fin m,
    Function.Injective order ∧
      ∀ (i : Fin ℓ) (hi : i.1 + 1 < ℓ),
        T.metaTree.Adj (order i) (order ⟨i.1 + 1, hi⟩)

end Lax17.TreeOfSets
