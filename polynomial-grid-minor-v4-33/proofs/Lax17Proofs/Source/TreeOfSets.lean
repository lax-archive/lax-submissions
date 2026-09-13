import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic
import Lax17Proofs.Source.Degree
import Lax17Proofs.Source.PathOfSets

namespace Lax17Proofs

universe u v w

/-!
# Tree-of-sets systems

This file introduces the tree-of-sets object used in Chekuri--Chuzhoy,
JACM 2016, Section 4.  It also proves the basic conversion needed in the easy
case of Theorem 4.6: a simple meta-tree path with two buffer vertices yields a
strong path-of-sets system on the middle clusters.

The two buffer vertices are intentional.  The repository's
`StrongPathOfSetsSystem` asks every cluster, including endpoints, to have
disjoint left and right nail sets.  Taking the middle clusters of a longer
meta-path gives every selected cluster a previous and a next incident tree edge,
so the two nail sides are supplied directly by the strong tree-of-sets
interfaces.
-/

namespace SimpleGraph


open scoped Classical

/-- A tree-of-sets system with `m` clusters and interface width `w`.

For every oriented meta-edge `i -> j`, `interface i j hij` is the subset of the
cluster `i` used as endpoints of the paths crossing the unoriented tree edge
`{i,j}`.  The connector is oriented from the `i`-interface to the `j`-interface;
the reverse orientation is available by applying `connector` to `j,i`.
-/
structure TreeOfSetsSystem {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (m w : ℕ) where
  /-- The meta-tree has at least one cluster. -/
  clusterCount_pos : 0 < m
  /-- The interface width is positive. -/
  width_pos : 0 < w
  /-- The meta-tree whose vertices index the clusters. -/
  metaTree : _root_.SimpleGraph (Fin m)
  /-- The meta-graph is a tree. -/
  meta_isTree : metaTree.IsTree
  /-- The meta-tree has maximum degree at most three. -/
  meta_maxDegree_three : MaxDegreeAtMost metaTree 3
  /-- The cluster assigned to a meta-vertex. -/
  cluster : Fin m → Finset V
  /-- Every cluster is connected in the ambient graph. -/
  cluster_connected : ∀ i : Fin m, IsCluster G (cluster i)
  /-- Distinct clusters are vertex-disjoint. -/
  cluster_disjoint :
    ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (cluster i) (cluster j)
  /-- Endpoint set in cluster `i` for the meta-edge `i-j`. -/
  interface : (i j : Fin m) → metaTree.Adj i j → Finset V
  /-- Interfaces lie in their clusters. -/
  interface_subset_cluster :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j), interface i j hij ⊆ cluster i
  /-- Every interface has the prescribed width. -/
  interface_card :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j), (interface i j hij).card = w
  /-- Different interfaces incident with the same cluster are disjoint. -/
  interface_disjoint :
    ∀ {i j k : Fin m} (hij : metaTree.Adj i j) (hik : metaTree.Adj i k),
      j ≠ k → Disjoint (interface i j hij) (interface i k hik)
  /-- Connector paths crossing an oriented meta-edge. -/
  connector :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      PerfectPathPacking G (interface i j hij) (interface j i (metaTree.symm hij))
  /-- Each connector has cardinality `w`. -/
  connector_card :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j), (connector i j hij).card = w
  /-- Connector paths are internally disjoint from every cluster. -/
  connector_internally_disjoint_clusters :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j) (r : Fin m)
      (a : (connector i j hij).Index),
        ((connector i j hij).path a).InternallyDisjointFromSet (cluster r)
  /-- Connector families for different meta-edges are mutually node-disjoint. -/
  connector_mutually_nodeDisjoint :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j)
      (p q : Fin m) (hpq : metaTree.Adj p q),
        s(i, j) ≠ s(p, q) →
          (connector i j hij).toPathPacking.MutuallyNodeDisjoint
            (connector p q hpq).toPathPacking

namespace TreeOfSetsSystem

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {m w : ℕ}

/-- View a tree-of-sets system inside a same-vertex supergraph. -/
def mapLe (T : TreeOfSetsSystem G m w) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') : TreeOfSetsSystem G' m w where
  clusterCount_pos := T.clusterCount_pos
  width_pos := T.width_pos
  metaTree := T.metaTree
  meta_isTree := T.meta_isTree
  meta_maxDegree_three := T.meta_maxDegree_three
  cluster := T.cluster
  cluster_connected := fun i => (T.cluster_connected i).mono_graph hGG'
  cluster_disjoint := T.cluster_disjoint
  interface := T.interface
  interface_subset_cluster := T.interface_subset_cluster
  interface_card := T.interface_card
  interface_disjoint := T.interface_disjoint
  connector := fun i j hij => (T.connector i j hij).mapLe hGG'
  connector_card := by
    intro i j hij
    simpa using T.connector_card i j hij
  connector_internally_disjoint_clusters := by
    intro i j hij r a
    change (((T.connector i j hij).path a).mapLe hGG').InternallyDisjointFromSet
      (T.cluster r)
    simpa [GraphPath.InternallyDisjointFromSet, GraphPath.IsEndpoint] using
      T.connector_internally_disjoint_clusters i j hij r a
  connector_mutually_nodeDisjoint := by
    intro i j hij p q hpq hedge a b
    change GraphPath.NodeDisjoint
      (((T.connector i j hij).path a).mapLe hGG')
      (((T.connector p q hpq).path b).mapLe hGG')
    simpa [GraphPath.NodeDisjoint] using
      T.connector_mutually_nodeDisjoint i j hij p q hpq hedge a b

/-- The connector across a meta-edge is internally disjoint from a specific
cluster. -/
theorem connector_internally_disjoint_cluster
    (T : TreeOfSetsSystem G m w)
    (i j : Fin m) (hij : T.metaTree.Adj i j) (r : Fin m) :
    (T.connector i j hij).toPathPacking.InternallyDisjointFromSet
      (T.cluster r) := by
  intro a
  exact T.connector_internally_disjoint_clusters i j hij r a

/-- A connector is wholly vertex-disjoint from every cluster other than its
two endpoint clusters.  Internal vertices avoid every cluster by definition;
the two endpoints lie in the incident interfaces. -/
theorem connector_vertexSet_disjoint_cluster_of_ne
    (T : TreeOfSetsSystem G m w)
    (i j : Fin m) (hij : T.metaTree.Adj i j) (r : Fin m)
    (hri : r ≠ i) (hrj : r ≠ j) :
    Disjoint (T.connector i j hij).toPathPacking.vertexSet (T.cluster r) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvConnector hvCluster
  rcases ((T.connector i j hij).toPathPacking.mem_vertexSet).1 hvConnector with
    ⟨a, hva⟩
  rcases T.connector_internally_disjoint_clusters i j hij r a
      hva hvCluster with hsource | htarget
  · have hsourceCluster :
        ((T.connector i j hij).path a).source ∈ T.cluster i :=
      T.interface_subset_cluster i j hij
        ((T.connector i j hij).source_mem a)
    exact Finset.disjoint_left.mp (T.cluster_disjoint (Ne.symm hri))
      hsourceCluster (by simpa [hsource] using hvCluster)
  · have htargetCluster :
        ((T.connector i j hij).path a).target ∈ T.cluster j :=
      T.interface_subset_cluster j i hij.symm
        ((T.connector i j hij).target_mem a)
    exact Finset.disjoint_left.mp (T.cluster_disjoint (Ne.symm hrj))
      htargetCluster (by simpa [htarget] using hvCluster)

end TreeOfSetsSystem

/-- A strong tree-of-sets system.  Every incident interface is node-well-linked
inside its cluster, and every pair of distinct incident interfaces is linked
inside that cluster. -/
structure StrongTreeOfSetsSystem {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (m w : ℕ)
    extends TreeOfSetsSystem G m w where
  /-- Each interface is node-well-linked in its cluster. -/
  interface_nodeWellLinked :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      NodeWellLinkedIn G (cluster i) (interface i j hij)
  /-- Distinct interfaces incident with the same cluster are linked. -/
  interface_pair_nodeLinked :
    ∀ {i j k : Fin m} (hij : metaTree.Adj i j) (hik : metaTree.Adj i k),
      j ≠ k → NodeLinkedIn G (cluster i) (interface i j hij) (interface i k hik)

namespace StrongTreeOfSetsSystem

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {m w ell : ℕ}

/-- View a strong tree-of-sets system inside a same-vertex supergraph. -/
def mapLe (T : StrongTreeOfSetsSystem G m w) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') : StrongTreeOfSetsSystem G' m w where
  toTreeOfSetsSystem := T.toTreeOfSetsSystem.mapLe hGG'
  interface_nodeWellLinked := by
    intro i j hij
    exact NodeWellLinkedIn.mono_graph (T.interface_nodeWellLinked i j hij) hGG'
  interface_pair_nodeLinked := by
    intro i j k hij hik hjk
    exact NodeLinkedIn.mono_graph (T.interface_pair_nodeLinked hij hik hjk) hGG'

/-- A strong tree cluster links equal-size subsets of two distinct incident
interfaces by a perfect packing contained in the cluster. -/
theorem exists_interface_pair_perfect_linkage_between_subsets
    (T : StrongTreeOfSetsSystem G m w)
    {i j k : Fin m} (hij : T.metaTree.Adj i j) (hik : T.metaTree.Adj i k)
    (hjk : j ≠ k) {A B : Finset V}
    (hA : A ⊆ T.interface i j hij)
    (hB : B ⊆ T.interface i k hik)
    (hcard : A.card = B.card) :
    ∃ Q : PerfectPathPacking G A B,
      Q.card = A.card ∧ Q.toPathPacking.StaysIn (T.cluster i) := by
  exact NodeLinkedIn.exists_perfectPathPacking_of_card_eq
    ((T.interface_pair_nodeLinked hij hik hjk).mono_terminals hA hB) hcard

/-- A strong tree interface is node-well-linked inside its cluster, so any two
disjoint subsets of that interface can be linked inside the cluster. -/
theorem exists_interface_self_linkage_between_disjoint_subsets
    (T : StrongTreeOfSetsSystem G m w)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {A B : Finset V}
    (hA : A ⊆ T.interface i j hij)
    (hB : B ⊆ T.interface i j hij)
    (hdisj : Disjoint A B) :
    ∃ Q : PathPacking G A B,
      Q.card = min A.card B.card ∧ Q.StaysIn (T.cluster i) := by
  exact (T.interface_nodeWellLinked i j hij).2 hA hB hdisj

/-- Equal-size disjoint subsets of one strong interface have an oriented
perfect linkage inside the cluster. -/
theorem exists_interface_self_perfect_linkage_between_disjoint_subsets
    (T : StrongTreeOfSetsSystem G m w)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {A B : Finset V}
    (hA : A ⊆ T.interface i j hij)
    (hB : B ⊆ T.interface i j hij)
    (hdisj : Disjoint A B) (hcard : A.card = B.card) :
    ∃ Q : PerfectPathPacking G A B,
      Q.card = A.card ∧ Q.toPathPacking.StaysIn (T.cluster i) := by
  rcases T.exists_interface_self_linkage_between_disjoint_subsets
      hij hA hB hdisj with ⟨Q, hQcard, hQstay⟩
  have hQcardA : Q.card = A.card := by
    simpa [hcard] using hQcard
  have hQcardB : Q.card = B.card := hQcardA.trans hcard
  refine ⟨Q.toPerfectOfCardEq hQcardA hQcardB, ?_, ?_⟩
  · simpa [PathPacking.toPerfectOfCardEq, PerfectPathPacking.card,
      PathPacking.card] using hQcardA
  · exact PathPacking.orient_staysIn hQstay

/-- The selected middle cluster for a buffered meta-path. -/
def bufferedClusterIndex (order : Fin (ell + 2) → Fin m) (i : Fin ell) :
    Fin m :=
  order ⟨i.1 + 1, by omega⟩

/-- The previous meta-vertex adjacent to a selected middle cluster. -/
def bufferedPrevIndex (order : Fin (ell + 2) → Fin m) (i : Fin ell) :
    Fin m :=
  order ⟨i.1, by omega⟩

/-- The next meta-vertex adjacent to a selected middle cluster. -/
def bufferedNextIndex (order : Fin (ell + 2) → Fin m) (i : Fin ell) :
    Fin m :=
  order ⟨i.1 + 2, by omega⟩

@[simp] theorem bufferedClusterIndex_eq
    (order : Fin (ell + 2) → Fin m) (i : Fin ell) :
    bufferedClusterIndex order i = order ⟨i.1 + 1, by omega⟩ := rfl

@[simp] theorem bufferedPrevIndex_eq
    (order : Fin (ell + 2) → Fin m) (i : Fin ell) :
    bufferedPrevIndex order i = order ⟨i.1, by omega⟩ := rfl

@[simp] theorem bufferedNextIndex_eq
    (order : Fin (ell + 2) → Fin m) (i : Fin ell) :
    bufferedNextIndex order i = order ⟨i.1 + 2, by omega⟩ := rfl

/-- A simple meta-tree path with two buffer vertices around the requested
`ell` clusters. -/
def HasBufferedMetaPath (T : StrongTreeOfSetsSystem G m w) (ell : ℕ) : Prop :=
  ∃ order : Fin (ell + 2) → Fin m,
    Function.Injective order ∧
      ∀ r : Fin (ell + 1),
        T.metaTree.Adj (order ⟨r.1, by omega⟩)
          (order ⟨r.1 + 1, by omega⟩)

/-- The meta-tree contains a graph path with at least the number of edges
needed for a buffered `ell`-cluster path-of-sets extraction. -/
def HasMetaPathLengthAtLeast (T : StrongTreeOfSetsSystem G m w) (ell : ℕ) :
    Prop :=
  ∃ P : GraphPath T.metaTree, ell + 1 ≤ P.walk.length

/-- The meta-tree has at least `L` leaves.  This is the tree side used in the
many-leaves branch of Chekuri--Chuzhoy Theorem 4.6. -/
def HasMetaLeavesAtLeast (T : StrongTreeOfSetsSystem G m w) (L : ℕ) : Prop :=
  ∃ leaves : Finset (Fin m),
    (∀ i : Fin m, i ∈ leaves ↔ DegreeEquals T.metaTree i 1) ∧ L ≤ leaves.card

/-- A sufficiently long simple path in the meta-tree supplies the buffered
meta-path order used by `toStrongPathOfSetsSystem_of_bufferedMetaPath`. -/
theorem hasBufferedMetaPath_of_metaPathLengthAtLeast
    (T : StrongTreeOfSetsSystem G m w)
    (hpath : T.HasMetaPathLengthAtLeast ell) :
    T.HasBufferedMetaPath ell := by
  rcases hpath with ⟨P, hlen⟩
  let order : Fin (ell + 2) → Fin m := fun r => P.walk.getVert r.1
  refine ⟨order, ?_, ?_⟩
  · intro a b hab
    apply Fin.ext
    have hidx := P.isPath.getVert_injOn
      (by simp; omega : a.1 ∈ {i : ℕ | i ≤ P.walk.length})
      (by simp; omega : b.1 ∈ {i : ℕ | i ≤ P.walk.length})
      (by simpa [order] using hab)
    exact hidx
  · intro r
    exact P.walk.adj_getVert_succ (i := r.1) (by omega)

/-- Consecutive edges of an injective vertex sequence are distinct as unordered
edges. -/
theorem buffered_edge_ne_of_ne
    {order : Fin (ell + 2) → Fin m} (hinj : Function.Injective order)
    {i j : Fin ell} (hij : i ≠ j) :
    s(order ⟨i.1 + 1, by omega⟩, order ⟨i.1 + 2, by omega⟩) ≠
      s(order ⟨j.1 + 1, by omega⟩, order ⟨j.1 + 2, by omega⟩) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hidx : (⟨i.1 + 1, by omega⟩ : Fin (ell + 2)) =
        ⟨j.1 + 1, by omega⟩ := hinj hleft
    have hval : i.1 + 1 = j.1 + 1 := congrArg Fin.val hidx
    exact hij (Fin.ext (by omega))
  · have hidx : (⟨i.1 + 1, by omega⟩ : Fin (ell + 2)) =
        ⟨j.1 + 2, by omega⟩ := hinj hleft
    have hidx' : (⟨i.1 + 2, by omega⟩ : Fin (ell + 2)) =
        ⟨j.1 + 1, by omega⟩ := hinj hright
    have hval : i.1 + 1 = j.1 + 2 := congrArg Fin.val hidx
    have hval' : i.1 + 2 = j.1 + 1 := congrArg Fin.val hidx'
    omega

/-- A buffered simple path in the meta-tree yields a strong path-of-sets system
on the middle clusters.

The sequence `order : Fin (ell + 2) -> Fin m` lists the meta-vertices of the
buffered path.  The selected path-of-sets clusters are positions
`1, ..., ell`; their left interfaces come from the preceding meta-edge and
their right interfaces from the following meta-edge.
-/
noncomputable def toStrongPathOfSetsSystem_of_bufferedMetaPath
    (T : StrongTreeOfSetsSystem G m w)
    (hell : 0 < ell)
    (order : Fin (ell + 2) → Fin m)
    (hinj : Function.Injective order)
    (hadj :
      ∀ r : Fin (ell + 1),
        T.metaTree.Adj (order ⟨r.1, by omega⟩) (order ⟨r.1 + 1, by omega⟩)) :
    StrongPathOfSetsSystem G ell w where
  length_pos := hell
  width_pos := T.width_pos
  cluster := fun i => T.cluster (bufferedClusterIndex order i)
  cluster_connected := fun i => T.cluster_connected (bufferedClusterIndex order i)
  cluster_disjoint := by
    intro i j hij
    apply T.cluster_disjoint
    intro hclusters
    apply hij
    apply Fin.ext
    apply Nat.succ.inj
    have hidx : (⟨i.1 + 1, by omega⟩ : Fin (ell + 2)) =
        ⟨j.1 + 1, by omega⟩ := hinj hclusters
    exact congrArg Fin.val hidx
  left := fun i =>
    T.interface (bufferedClusterIndex order i) (bufferedPrevIndex order i)
      (T.metaTree.symm (hadj ⟨i.1, by omega⟩))
  right := fun i =>
    T.interface (bufferedClusterIndex order i) (bufferedNextIndex order i)
      (hadj ⟨i.1 + 1, by omega⟩)
  left_subset_cluster := by
    intro i
    exact T.interface_subset_cluster _ _ _
  right_subset_cluster := by
    intro i
    exact T.interface_subset_cluster _ _ _
  left_right_disjoint := by
    intro i
    apply T.interface_disjoint
    intro hprev_next
    have hidx : (⟨i.1, by omega⟩ : Fin (ell + 2)) =
        ⟨i.1 + 2, by omega⟩ := hinj hprev_next
    have hval : i.1 = i.1 + 2 := congrArg Fin.val hidx
    omega
  left_card := by
    intro i
    exact T.interface_card _ _ _
  right_card := by
    intro i
    exact T.interface_card _ _ _
  connector := by
    intro i hi
    exact T.connector
      (bufferedClusterIndex order i)
      (bufferedClusterIndex order ⟨i.1 + 1, hi⟩)
      (hadj ⟨i.1 + 1, by omega⟩)
  connector_card := by
    intro i hi
    exact T.connector_card _ _ _
  connector_internally_disjoint_clusters := by
    intro i hi j a
    exact T.connector_internally_disjoint_clusters _ _ _ _ a
  connector_mutually_nodeDisjoint := by
    intro i j hi hj hij a b
    exact T.connector_mutually_nodeDisjoint
      (bufferedClusterIndex order i)
      (bufferedClusterIndex order ⟨i.1 + 1, hi⟩)
      (hadj ⟨i.1 + 1, by omega⟩)
      (bufferedClusterIndex order j)
      (bufferedClusterIndex order ⟨j.1 + 1, hj⟩)
      (hadj ⟨j.1 + 1, by omega⟩)
      (buffered_edge_ne_of_ne (order := order) hinj hij) a b
  left_nodeWellLinked := by
    intro i
    exact T.interface_nodeWellLinked _ _ _
  right_nodeWellLinked := by
    intro i
    exact T.interface_nodeWellLinked _ _ _
  left_right_nodeLinked := by
    intro i
    apply T.interface_pair_nodeLinked
    intro hprev_next
    have hidx : (⟨i.1, by omega⟩ : Fin (ell + 2)) =
        ⟨i.1 + 2, by omega⟩ := hinj hprev_next
    have hval : i.1 = i.1 + 2 := congrArg Fin.val hidx
    omega

/-- Existential wrapper for the buffered meta-path conversion. -/
theorem exists_strongPathOfSetsSystem_of_bufferedMetaPath
    (T : StrongTreeOfSetsSystem G m w)
    (hell : 0 < ell)
    (order : Fin (ell + 2) → Fin m)
    (hinj : Function.Injective order)
    (hadj :
      ∀ r : Fin (ell + 1),
        T.metaTree.Adj (order ⟨r.1, by omega⟩) (order ⟨r.1 + 1, by omega⟩)) :
    Nonempty (StrongPathOfSetsSystem G ell w) :=
  ⟨T.toStrongPathOfSetsSystem_of_bufferedMetaPath hell order hinj hadj⟩

/-- Predicate-form wrapper for the buffered meta-path conversion. -/
theorem exists_strongPathOfSetsSystem_of_hasBufferedMetaPath
    (T : StrongTreeOfSetsSystem G m w)
    (hell : 0 < ell)
    (hpath : T.HasBufferedMetaPath ell) :
    Nonempty (StrongPathOfSetsSystem G ell w) := by
  rcases hpath with ⟨order, hinj, hadj⟩
  exact T.exists_strongPathOfSetsSystem_of_bufferedMetaPath hell order hinj hadj

/-- Long-meta-path wrapper for the strong path-of-sets conversion. -/
theorem exists_strongPathOfSetsSystem_of_metaPathLengthAtLeast
    (T : StrongTreeOfSetsSystem G m w)
    (hell : 0 < ell)
    (hpath : T.HasMetaPathLengthAtLeast ell) :
    Nonempty (StrongPathOfSetsSystem G ell w) :=
  T.exists_strongPathOfSetsSystem_of_hasBufferedMetaPath hell
    (T.hasBufferedMetaPath_of_metaPathLengthAtLeast hpath)

/-- Buffered meta-path conversion followed by width restriction.

This is the form used in the proof of Chekuri--Chuzhoy Theorem 4.6 when the
strong tree-of-sets system has width `w` but the requested path-of-sets width is
only `w'`. -/
theorem exists_strongPathOfSetsSystem_of_hasBufferedMetaPath_of_width_le
    (T : StrongTreeOfSetsSystem G m w)
    {w' : ℕ} (hell : 0 < ell) (hw' : 0 < w') (hle : w' ≤ w)
    (hpath : T.HasBufferedMetaPath ell) :
    Nonempty (StrongPathOfSetsSystem G ell w') := by
  rcases T.exists_strongPathOfSetsSystem_of_hasBufferedMetaPath hell hpath with ⟨P⟩
  exact ⟨P.restrictWidth hw' hle⟩

/-- Long-meta-path conversion followed by width restriction. -/
theorem exists_strongPathOfSetsSystem_of_metaPathLengthAtLeast_of_width_le
    (T : StrongTreeOfSetsSystem G m w)
    {w' : ℕ} (hell : 0 < ell) (hw' : 0 < w') (hle : w' ≤ w)
    (hpath : T.HasMetaPathLengthAtLeast ell) :
    Nonempty (StrongPathOfSetsSystem G ell w') :=
  T.exists_strongPathOfSetsSystem_of_hasBufferedMetaPath_of_width_le
    hell hw' hle (T.hasBufferedMetaPath_of_metaPathLengthAtLeast hpath)

end StrongTreeOfSetsSystem

end SimpleGraph

end Lax17Proofs
