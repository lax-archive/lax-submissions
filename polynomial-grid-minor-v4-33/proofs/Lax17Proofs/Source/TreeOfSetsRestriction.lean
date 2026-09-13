import Lax17Proofs.Source.TreeOfSets

namespace Lax17Proofs

universe u v w

/-!
# Coherent restrictions of tree-of-sets connectors

A `TreeOfSetsSystem` stores both orientations of every meta-edge independently.
When a connector is restricted, choosing subfamilies in both orientations would
therefore create an unnecessary coherence obligation.  This module chooses the
orientation from the smaller endpoint of `Fin m` to the larger endpoint, takes
one index set there, and defines the opposite connector by reversal.

`StrongRestrictionData` asks only for those canonical index sets and the
well-linkedness properties that do not follow from the original system.  The
remaining fields of the restricted strong tree-of-sets system are derived.
-/

namespace SimpleGraph


open scoped Classical

namespace TreeOfSetsSystem

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {m w W : ℕ}

/-- One index set for each meta-edge, stored only in its increasing
orientation. -/
abbrev CanonicalIndexSets (T : TreeOfSetsSystem G m w) :=
  (i j : Fin m) → (hij : T.metaTree.Adj i j) → i < j →
    Finset (T.connector i j hij).Index

/-- The endpoint interface induced by a canonical family of connector
indices.  At the smaller endpoint this is a source set; at the larger endpoint
it is the target set of the same increasing connector. -/
noncomputable def restrictedInterface (T : TreeOfSetsSystem G m w)
    (I : CanonicalIndexSets T) (i j : Fin m)
    (hij : T.metaTree.Adj i j) : Finset V := by
  classical
  by_cases h : i < j
  · exact (T.connector i j hij).sourceSet (I i j hij h)
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    exact (T.connector j i (T.metaTree.symm hij)).targetSet
      (I j i (T.metaTree.symm hij) hji)

/-- The oriented restricted connector.  Both orientations of a meta-edge use
the restriction selected in the increasing orientation. -/
noncomputable def restrictedConnector (T : TreeOfSetsSystem G m w)
    (I : CanonicalIndexSets T) (i j : Fin m)
    (hij : T.metaTree.Adj i j) :
    PerfectPathPacking G
      (T.restrictedInterface I i j hij)
      (T.restrictedInterface I j i (T.metaTree.symm hij)) := by
  classical
  by_cases h : i < j
  · let P := (T.connector i j hij).restrictIndexSet (I i j hij h)
    exact P.copyTerminals
      (by simp [restrictedInterface, h])
      (by simp [restrictedInterface, not_lt_of_ge h.le])
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    let P := ((T.connector j i (T.metaTree.symm hij)).restrictIndexSet
      (I j i (T.metaTree.symm hij) hji)).reverse
    exact P.copyTerminals
      (by simp [restrictedInterface, h])
      (by simp [restrictedInterface, hji])

/-- A restricted endpoint remains in the original interface. -/
theorem restrictedInterface_subset_interface
    (T : TreeOfSetsSystem G m w) (I : CanonicalIndexSets T)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    T.restrictedInterface I i j hij ⊆ T.interface i j hij := by
  classical
  by_cases h : i < j
  · simpa [restrictedInterface, h] using
      (T.connector i j hij).sourceSet_subset_left (I i j hij h)
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    simpa [restrictedInterface, h, hji] using
      (T.connector j i (T.metaTree.symm hij)).targetSet_subset_right
        (I j i (T.metaTree.symm hij) hji)

/-- A restricted endpoint lies in its cluster. -/
theorem restrictedInterface_subset_cluster
    (T : TreeOfSetsSystem G m w) (I : CanonicalIndexSets T)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    T.restrictedInterface I i j hij ⊆ T.cluster i :=
  subset_trans (T.restrictedInterface_subset_interface I i j hij)
    (T.interface_subset_cluster i j hij)

/-- Restriction preserves disjointness of distinct interfaces incident with a
cluster. -/
theorem restrictedInterface_disjoint
    (T : TreeOfSetsSystem G m w) (I : CanonicalIndexSets T)
    {i j k : Fin m} (hij : T.metaTree.Adj i j)
    (hik : T.metaTree.Adj i k) (hjk : j ≠ k) :
    Disjoint (T.restrictedInterface I i j hij)
      (T.restrictedInterface I i k hik) := by
  rw [Finset.disjoint_left]
  intro v hvj hvk
  exact Finset.disjoint_left.mp (T.interface_disjoint hij hik hjk)
    (T.restrictedInterface_subset_interface I i j hij hvj)
    (T.restrictedInterface_subset_interface I i k hik hvk)

/-- The size of a restricted endpoint is the size of its canonical index
set. -/
theorem restrictedInterface_card
    (T : TreeOfSetsSystem G m w) (I : CanonicalIndexSets T)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    (T.restrictedInterface I i j hij).card =
      if h : i < j then (I i j hij h).card
      else (I j i (T.metaTree.symm hij)
        (lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm)).card := by
  classical
  by_cases h : i < j
  · simp [restrictedInterface, h]
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    simp [restrictedInterface, h]

/-- Data not inherited automatically when restricting a tree-of-sets system.
Only one index set is supplied per unordered meta-edge; all oriented output
data is derived from it. -/
structure StrongRestrictionData (T : TreeOfSetsSystem G m w) (W : ℕ) where
  /-- The new width is positive. -/
  width_pos : 0 < W
  /-- Selected paths, represented in the increasing orientation. -/
  indexSet : CanonicalIndexSets T
  /-- Every selected canonical connector has the new width. -/
  indexSet_card :
    ∀ (i j : Fin m) (hij : T.metaTree.Adj i j) (hij_lt : i < j),
      (indexSet i j hij hij_lt).card = W
  /-- Every induced endpoint interface is node-well-linked in its cluster. -/
  interface_nodeWellLinked :
    ∀ (i j : Fin m) (hij : T.metaTree.Adj i j),
      NodeWellLinkedIn G (T.cluster i)
        (T.restrictedInterface indexSet i j hij)
  /-- Every pair of distinct induced interfaces at a cluster is linked. -/
  interface_pair_nodeLinked :
    ∀ {i j k : Fin m} (hij : T.metaTree.Adj i j)
      (hik : T.metaTree.Adj i k), j ≠ k →
        NodeLinkedIn G (T.cluster i)
          (T.restrictedInterface indexSet i j hij)
          (T.restrictedInterface indexSet i k hik)

namespace StrongRestrictionData

variable {T : TreeOfSetsSystem G m w}

/-- Every induced endpoint has the requested width. -/
theorem interface_card (D : StrongRestrictionData T W)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    (T.restrictedInterface D.indexSet i j hij).card = W := by
  classical
  by_cases h : i < j
  · simpa [restrictedInterface, h] using D.indexSet_card i j hij h
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    simpa [restrictedInterface, h, hji] using
      D.indexSet_card j i (T.metaTree.symm hij) hji

/-- Every oriented restricted connector has the requested width. -/
theorem connector_card (D : StrongRestrictionData T W)
    (i j : Fin m) (hij : T.metaTree.Adj i j) :
    (T.restrictedConnector D.indexSet i j hij).card = W :=
  (T.restrictedConnector D.indexSet i j hij).card_eq_left_card.trans
    (D.interface_card i j hij)

/-- Restricted connectors retain internal avoidance of every cluster. -/
theorem connector_internallyDisjointFromSet
    (D : StrongRestrictionData T W) (i j : Fin m)
    (hij : T.metaTree.Adj i j) (r : Fin m) :
    PathPacking.InternallyDisjointFromSet
      (T.restrictedConnector D.indexSet i j hij).toPathPacking
      (T.cluster r) := by
  classical
  by_cases h : i < j
  · simpa [restrictedConnector, h, not_lt_of_ge h.le] using
      (T.connector i j hij).restrictIndexSet_internallyDisjointFromSet
        (D.indexSet i j hij h)
        (T.connector_internally_disjoint_cluster i j hij r)
  · have hji : j < i :=
      lt_of_le_of_ne (le_of_not_gt h) hij.ne.symm
    have hrestricted :=
      (T.connector j i (T.metaTree.symm hij))
        |>.restrictIndexSet_internallyDisjointFromSet
            (D.indexSet j i (T.metaTree.symm hij) hji)
            (T.connector_internally_disjoint_cluster j i
              (T.metaTree.symm hij) r)
    simpa [restrictedConnector, h, hji] using
      PerfectPathPacking.reverse_internallyDisjointFromSet _ hrestricted

/-- In the increasing orientation, restriction only removes vertices from the
trace of the original connector family. -/
theorem connector_vertexSet_subset_of_lt
    (D : StrongRestrictionData T W) (i j : Fin m)
    (hij : T.metaTree.Adj i j) (hij_lt : i < j) :
    (T.restrictedConnector D.indexSet i j hij).toPathPacking.vertexSet ⊆
      (T.connector i j hij).toPathPacking.vertexSet := by
  simpa [restrictedConnector, hij_lt] using
    (T.connector i j hij).restrictIndexSet_vertexSet_subset
      (D.indexSet i j hij hij_lt)

private theorem reverse_vertexSet_eq
    {S U : Finset V} (P : PerfectPathPacking G S U) :
    P.reverse.toPathPacking.vertexSet = P.toPathPacking.vertexSet := by
  classical
  ext v
  rw [PathPacking.mem_vertexSet, PathPacking.mem_vertexSet]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩

/-- In the decreasing orientation, the restricted connector is the reversal
of a subfamily of the increasing (`j -> i`) original connector. -/
theorem connector_vertexSet_subset_of_not_lt
    (D : StrongRestrictionData T W) (i j : Fin m)
    (hij : T.metaTree.Adj i j) (hij_lt : ¬ i < j) :
    (T.restrictedConnector D.indexSet i j hij).toPathPacking.vertexSet ⊆
      (T.connector j i (T.metaTree.symm hij)).toPathPacking.vertexSet := by
  classical
  have hji : j < i :=
    lt_of_le_of_ne (le_of_not_gt hij_lt) hij.ne.symm
  let P := (T.connector j i (T.metaTree.symm hij)).restrictIndexSet
    (D.indexSet j i (T.metaTree.symm hij) hji)
  calc
    (T.restrictedConnector D.indexSet i j hij).toPathPacking.vertexSet =
        P.reverse.toPathPacking.vertexSet := by
      simp [P, restrictedConnector, hij_lt]
    _ = P.toPathPacking.vertexSet := reverse_vertexSet_eq P
    _ ⊆ (T.connector j i (T.metaTree.symm hij)).toPathPacking.vertexSet :=
      PerfectPathPacking.restrictIndexSet_vertexSet_subset
        (T.connector j i (T.metaTree.symm hij))
        (D.indexSet j i (T.metaTree.symm hij) hji)

/-- Restricted connector families on distinct meta-edges remain mutually
node-disjoint. -/
theorem connector_mutuallyNodeDisjoint
    (D : StrongRestrictionData T W)
    (i j : Fin m) (hij : T.metaTree.Adj i j)
    (p q : Fin m) (hpq : T.metaTree.Adj p q)
    (hedge : s(i, j) ≠ s(p, q)) :
    PathPacking.MutuallyNodeDisjoint
      (T.restrictedConnector D.indexSet i j hij).toPathPacking
      (T.restrictedConnector D.indexSet p q hpq).toPathPacking := by
  classical
  intro a b
  rw [GraphPath.NodeDisjoint]
  by_cases hij_lt : i < j
  · by_cases hpq_lt : p < q
    · have hdisj := PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (T.connector_mutually_nodeDisjoint i j hij p q hpq hedge)
      exact hdisj.mono
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (T.restrictedConnector D.indexSet i j hij).toPathPacking a)
          (D.connector_vertexSet_subset_of_lt i j hij hij_lt))
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (T.restrictedConnector D.indexSet p q hpq).toPathPacking b)
          (D.connector_vertexSet_subset_of_lt p q hpq hpq_lt))
    · have hedge' : s(i, j) ≠ s(q, p) := by
        simpa [Sym2.eq_swap] using hedge
      have hdisj := PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (T.connector_mutually_nodeDisjoint i j hij q p
          (T.metaTree.symm hpq) hedge')
      exact hdisj.mono
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (T.restrictedConnector D.indexSet i j hij).toPathPacking a)
          (D.connector_vertexSet_subset_of_lt i j hij hij_lt))
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (T.restrictedConnector D.indexSet p q hpq).toPathPacking b)
          (D.connector_vertexSet_subset_of_not_lt p q hpq hpq_lt))
  · by_cases hpq_lt : p < q
    · have hedge' : s(j, i) ≠ s(p, q) := by
        simpa [Sym2.eq_swap] using hedge
      have hdisj := PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (T.connector_mutually_nodeDisjoint j i (T.metaTree.symm hij)
          p q hpq hedge')
      exact hdisj.mono
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (T.restrictedConnector D.indexSet i j hij).toPathPacking a)
          (D.connector_vertexSet_subset_of_not_lt i j hij hij_lt))
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (T.restrictedConnector D.indexSet p q hpq).toPathPacking b)
          (D.connector_vertexSet_subset_of_lt p q hpq hpq_lt))
    · have hedge' : s(j, i) ≠ s(q, p) := by
        simpa [Sym2.eq_swap] using hedge
      have hdisj := PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (T.connector_mutually_nodeDisjoint j i (T.metaTree.symm hij)
          q p (T.metaTree.symm hpq) hedge')
      exact hdisj.mono
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (T.restrictedConnector D.indexSet i j hij).toPathPacking a)
          (D.connector_vertexSet_subset_of_not_lt i j hij hij_lt))
        (subset_trans
          (PathPacking.path_vertexSet_subset_vertexSet
            (T.restrictedConnector D.indexSet p q hpq).toPathPacking b)
          (D.connector_vertexSet_subset_of_not_lt p q hpq hpq_lt))

/-- Build the strong restricted system.  Meta-tree and cluster data are shared
with `T`; connector avoidance and mutual disjointness are inherited by taking
subfamilies and reversing paths. -/
noncomputable def toStrongTreeOfSetsSystem
    (D : StrongRestrictionData T W) : StrongTreeOfSetsSystem G m W where
  clusterCount_pos := T.clusterCount_pos
  width_pos := D.width_pos
  metaTree := T.metaTree
  meta_isTree := T.meta_isTree
  meta_maxDegree_three := T.meta_maxDegree_three
  cluster := T.cluster
  cluster_connected := T.cluster_connected
  cluster_disjoint := T.cluster_disjoint
  interface := T.restrictedInterface D.indexSet
  interface_subset_cluster := T.restrictedInterface_subset_cluster D.indexSet
  interface_card := D.interface_card
  interface_disjoint := T.restrictedInterface_disjoint D.indexSet
  connector := T.restrictedConnector D.indexSet
  connector_card := D.connector_card
  connector_internally_disjoint_clusters := by
    intro i j hij r a
    exact D.connector_internallyDisjointFromSet i j hij r a
  connector_mutually_nodeDisjoint := D.connector_mutuallyNodeDisjoint
  interface_nodeWellLinked := D.interface_nodeWellLinked
  interface_pair_nodeLinked := D.interface_pair_nodeLinked

end StrongRestrictionData

end TreeOfSetsSystem

end SimpleGraph

end Lax17Proofs
