import Lax17Proofs.Source.ChekuriChuzhoyClaim48
import Lax17Proofs.Source.ChekuriChuzhoyTheorem46Defs
import Lax17Proofs.Source.ChekuriChuzhoyRootedTreeComponents

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Theorem 4.7

This module formalizes the top-down, root-to-selected-leaf routing used in
Step 1 of the many-leaves proof of journal Theorem 4.6.

The first part records the rooted-tree bookkeeping needed by the recursive
construction.  In a degree-three tree rooted at a leaf, every nonroot vertex
has at most two children, and the selected leaves below a nonselected vertex
partition over those child subtrees.  The path construction then applies
Claim 4.8 at the two-child vertices.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical
open ChekuriChuzhoyRootedTreePruning
open ChekuriChuzhoyRootedTreeComponents

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {m W ell : ℕ}
variable {T : StrongTreeOfSetsSystem G m W}

/-- The selected leaves contained in the rooted subtree at `v`. -/
noncomputable def Theorem46LeafExtractionSetup.selectedBelow
    (S : Theorem46LeafExtractionSetup T ell) (v : Fin m) :
    Finset (Fin m) :=
  S.leaves ∩ descendants T.meta_isTree S.root v

theorem Theorem46LeafExtractionSetup.selectedBelow_subset_leaves
    (S : Theorem46LeafExtractionSetup T ell) (v : Fin m) :
    S.selectedBelow v ⊆ S.leaves :=
  Finset.inter_subset_left

theorem Theorem46LeafExtractionSetup.selectedBelow_subset_descendants
    (S : Theorem46LeafExtractionSetup T ell) (v : Fin m) :
    S.selectedBelow v ⊆ descendants T.meta_isTree S.root v :=
  Finset.inter_subset_right

theorem Theorem46LeafExtractionSetup.mem_selectedBelow
    (S : Theorem46LeafExtractionSetup T ell) (v x : Fin m) :
    x ∈ S.selectedBelow v ↔
      x ∈ S.leaves ∧ x ∈ descendants T.meta_isTree S.root v := by
  simp [Theorem46LeafExtractionSetup.selectedBelow]

/-- The parent-distance equation used by all rooted subtree decompositions. -/
theorem Theorem46LeafExtractionSetup.parentDistanceDecreases
    (S : Theorem46LeafExtractionSetup T ell) :
    ParentDistanceDecreases T.meta_isTree S.root :=
  fun {_x} hx => dist_parent_add_one T.meta_isTree S.root hx

/-- Every child of a meta-vertex is one of its graph neighbors. -/
theorem Theorem46LeafExtractionSetup.children_subset_neighborFinset
    (S : Theorem46LeafExtractionSetup T ell) (v : Fin m) :
    children T.meta_isTree S.root v ⊆
      MaxDegreeAtMost.neighborFinset T.meta_maxDegree_three v := by
  intro c hc
  have hchild :
      IsChild T.meta_isTree S.root v c :=
    (mem_children T.meta_isTree S.root v c).1 hc
  have hadj :
      T.metaTree.Adj v c := by
    simpa [hchild.2] using
      parent_adj T.meta_isTree S.root hchild.1
  exact
    (MaxDegreeAtMost.mem_neighborFinset
      T.meta_maxDegree_three v c).2 hadj

/-- A nonroot vertex's parent is a neighbor. -/
theorem Theorem46LeafExtractionSetup.parent_mem_neighborFinset
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ≠ S.root) :
    parent T.meta_isTree S.root v ∈
      MaxDegreeAtMost.neighborFinset T.meta_maxDegree_three v := by
  exact
    (MaxDegreeAtMost.mem_neighborFinset T.meta_maxDegree_three v
      (parent T.meta_isTree S.root v)).2
      (parent_adj T.meta_isTree S.root hv).symm

/-- The parent of a nonroot vertex is not one of that vertex's children. -/
theorem Theorem46LeafExtractionSetup.parent_not_mem_children
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ≠ S.root) :
    parent T.meta_isTree S.root v ∉
      children T.meta_isTree S.root v := by
  intro hp
  have hchild :
      IsChild T.meta_isTree S.root v
        (parent T.meta_isTree S.root v) :=
    (mem_children T.meta_isTree S.root v _).1 hp
  have hdown :=
    hchild.dist_eq_add_one T.meta_isTree S.root
      S.parentDistanceDecreases
  have hup := dist_parent_add_one T.meta_isTree S.root hv
  omega

/-- Rooting a degree-three tree at a leaf leaves at most two children at every
nonroot vertex. -/
theorem Theorem46LeafExtractionSetup.children_card_le_two
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ≠ S.root) :
    (children T.meta_isTree S.root v).card ≤ 2 := by
  let N :=
    MaxDegreeAtMost.neighborFinset T.meta_maxDegree_three v
  let p := parent T.meta_isTree S.root v
  have hpN : p ∈ N := S.parent_mem_neighborFinset hv
  have hchildrenErase :
      children T.meta_isTree S.root v ⊆ N.erase p := by
    intro c hc
    exact Finset.mem_erase.mpr
      ⟨by
        intro hcp
        exact S.parent_not_mem_children hv (by simpa [hcp] using hc),
        S.children_subset_neighborFinset v hc⟩
  have hNcard : N.card ≤ 3 :=
    MaxDegreeAtMost.card_neighborFinset_le
      T.meta_maxDegree_three v
  have hEraseCard : (N.erase p).card = N.card - 1 :=
    Finset.card_erase_of_mem hpN
  calc
    (children T.meta_isTree S.root v).card ≤
        (N.erase p).card :=
      Finset.card_le_card hchildrenErase
    _ = N.card - 1 := hEraseCard
    _ ≤ 2 := by omega

/-- Distinct child branches contain disjoint selected-leaf sets. -/
theorem Theorem46LeafExtractionSetup.selectedBelow_children_disjoint
    (S : Theorem46LeafExtractionSetup T ell)
    {v c d : Fin m}
    (hc : c ∈ children T.meta_isTree S.root v)
    (hd : d ∈ children T.meta_isTree S.root v)
    (hcd : c ≠ d) :
    Disjoint (S.selectedBelow c) (S.selectedBelow d) := by
  have hcChild :
      IsChild T.meta_isTree S.root v c :=
    (mem_children T.meta_isTree S.root v c).1 hc
  have hdChild :
      IsChild T.meta_isTree S.root v d :=
    (mem_children T.meta_isTree S.root v d).1 hd
  exact
    (childSubtree_disjoint T.meta_isTree S.root
      S.parentDistanceDecreases hcChild hdChild hcd).mono
        (S.selectedBelow_subset_descendants c)
        (S.selectedBelow_subset_descendants d)

/-- At a nonselected meta-vertex, selected descendants partition over its
immediate child subtrees. -/
theorem Theorem46LeafExtractionSetup.selectedBelow_eq_biUnion_children
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ∉ S.leaves) :
    S.selectedBelow v =
      (children T.meta_isTree S.root v).biUnion S.selectedBelow := by
  classical
  ext x
  constructor
  · intro hx
    have hxL := (S.mem_selectedBelow v x).1 hx
    have hxne : x ≠ v := by
      intro hxv
      exact hv (by simpa [hxv] using hxL.1)
    rcases exists_child_of_mem_descendants_of_ne
        T.meta_isTree S.root S.parentDistanceDecreases
        hxL.2 hxne with
      ⟨c, hc, hxc⟩
    exact Finset.mem_biUnion.mpr
      ⟨c, hc, (S.mem_selectedBelow c x).2 ⟨hxL.1, hxc⟩⟩
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨c, hc, hxc⟩
    have hcChild :
        IsChild T.meta_isTree S.root v c :=
      (mem_children T.meta_isTree S.root v c).1 hc
    have hxc' := (S.mem_selectedBelow c x).1 hxc
    have hxDesc :
        x ∈ descendants T.meta_isTree S.root v := by
      rw [mem_descendants_iff_eq_or_childSubtree
        T.meta_isTree S.root S.parentDistanceDecreases]
      exact Or.inr ⟨c, hc, hxc'.2⟩
    exact (S.mem_selectedBelow v x).2 ⟨hxc'.1, hxDesc⟩

/-- A selected leaf is never the separate DFS root. -/
theorem Theorem46LeafExtractionSetup.selectedLeaf_ne_root_routing
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ∈ S.leaves) :
    v ≠ S.root := by
  intro h
  exact S.root_not_mem_leaves (by simpa [h] using hv)

/-- A selected meta-tree leaf has no children in the rooted tree. -/
theorem Theorem46LeafExtractionSetup.children_eq_empty_of_mem_leaves
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ∈ S.leaves) :
    children T.meta_isTree S.root v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hvroot : v ≠ S.root := S.selectedLeaf_ne_root_routing hv
  have hcChild :
      IsChild T.meta_isTree S.root v c :=
    (mem_children T.meta_isTree S.root v c).1 hc
  rcases DegreeEquals.one_exists_unique_adj (S.leaves_leaf v hv) with
    ⟨z, _hvz, hzUnique⟩
  have hcz : c = z := hzUnique c (by
    simpa [hcChild.2] using parent_adj T.meta_isTree S.root hcChild.1)
  have hpz : parent T.meta_isTree S.root v = z :=
    hzUnique _ (parent_adj T.meta_isTree S.root hvroot).symm
  have hcp : c = parent T.meta_isTree S.root v := hcz.trans hpz.symm
  exact S.parent_not_mem_children hvroot (by simpa [hcp] using hc)

/-- The only selected leaf below a selected meta-tree leaf is itself. -/
theorem Theorem46LeafExtractionSetup.selectedBelow_eq_singleton_of_mem_leaves
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ∈ S.leaves) :
    S.selectedBelow v = {v} := by
  classical
  ext x
  constructor
  · intro hx
    have hxDesc := (S.mem_selectedBelow v x).1 hx
    rw [mem_descendants_iff_eq_or_childSubtree
      T.meta_isTree S.root S.parentDistanceDecreases] at hxDesc
    rcases hxDesc.2 with h | ⟨c, hc, _hxc⟩
    · simpa [h]
    · rw [S.children_eq_empty_of_mem_leaves hv] at hc
      simp at hc
  · intro hx
    have hxv : x = v := by simpa using hx
    subst x
    exact (S.mem_selectedBelow v v).2
      ⟨hv, self_mem_descendants T.meta_isTree S.root v⟩

/-- Children carrying at least one selected leaf.  These are precisely the
branches processed by the top-down routing recursion. -/
noncomputable def Theorem46LeafExtractionSetup.activeChildren
    (S : Theorem46LeafExtractionSetup T ell) (v : Fin m) :
    Finset (Fin m) :=
  (children T.meta_isTree S.root v).filter fun c =>
    (S.selectedBelow c).Nonempty

theorem Theorem46LeafExtractionSetup.mem_activeChildren
    (S : Theorem46LeafExtractionSetup T ell) (v c : Fin m) :
    c ∈ S.activeChildren v ↔
      c ∈ children T.meta_isTree S.root v ∧
        (S.selectedBelow c).Nonempty := by
  simp [Theorem46LeafExtractionSetup.activeChildren]

theorem Theorem46LeafExtractionSetup.activeChildren_subset_children
    (S : Theorem46LeafExtractionSetup T ell) (v : Fin m) :
    S.activeChildren v ⊆ children T.meta_isTree S.root v :=
  Finset.filter_subset _ _

/-- There are at most two active branches below any nonroot vertex. -/
theorem Theorem46LeafExtractionSetup.activeChildren_card_le_two
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ≠ S.root) :
    (S.activeChildren v).card ≤ 2 :=
  Finset.card_le_card (S.activeChildren_subset_children v) |>.trans
    (S.children_card_le_two hv)

/-- The meta-edge from a vertex to one of its rooted children. -/
theorem Theorem46LeafExtractionSetup.adj_child
    (S : Theorem46LeafExtractionSetup T ell)
    {v c : Fin m} (hc : IsChild T.meta_isTree S.root v c) :
    T.metaTree.Adj v c := by
  simpa [hc.2] using parent_adj T.meta_isTree S.root hc.1

/-- The vertex trace of the connector from a rooted vertex to one of its
children.  The `if` makes this a total function under finite `biUnion`; only
the child case is used. -/
noncomputable def Theorem46LeafExtractionSetup.childConnectorVertexSet
    (S : Theorem46LeafExtractionSetup T ell) (v c : Fin m) : Finset V :=
  if hc : IsChild T.meta_isTree S.root v c then
    (T.connector v c (S.adj_child hc)).toPathPacking.vertexSet
  else ∅

@[simp] theorem Theorem46LeafExtractionSetup.childConnectorVertexSet_eq
    (S : Theorem46LeafExtractionSetup T ell)
    {v c : Fin m} (hc : IsChild T.meta_isTree S.root v c) :
    S.childConnectorVertexSet v c =
      (T.connector v c (S.adj_child hc)).toPathPacking.vertexSet := by
  simp [Theorem46LeafExtractionSetup.childConnectorVertexSet, hc]

/-- The structural support below `v`: every descendant cluster and every
connector from a descendant to one of its children.  It excludes the connector
entering `v` from its parent. -/
noncomputable def Theorem46LeafExtractionSetup.subtreeRegion
    (S : Theorem46LeafExtractionSetup T ell) (v : Fin m) : Finset V :=
  (descendants T.meta_isTree S.root v).biUnion fun x =>
    T.cluster x ∪
      (children T.meta_isTree S.root x).biUnion
        (S.childConnectorVertexSet x)

/-- A child of a vertex in a nonroot descendant subtree remains in that
subtree. -/
theorem Theorem46LeafExtractionSetup.mem_descendants_of_child
    (S : Theorem46LeafExtractionSetup T ell)
    {a x c : Fin m} (ha : a ≠ S.root)
    (hx : x ∈ descendants T.meta_isTree S.root a)
    (hc : IsChild T.meta_isTree S.root x c) :
    c ∈ descendants T.meta_isTree S.root a := by
  apply mem_descendants_of_parent_mem
    T.meta_isTree S.root S.parentDistanceDecreases ha hc.1
  simpa [hc.2] using hx

/-- Structural supports rooted at two distinct children are vertex-disjoint.
This is the separation used when recursively unioning the two top-down routing
families. -/
theorem Theorem46LeafExtractionSetup.subtreeRegion_disjoint
    (S : Theorem46LeafExtractionSetup T ell)
    {v c d : Fin m}
    (hc : IsChild T.meta_isTree S.root v c)
    (hd : IsChild T.meta_isTree S.root v d)
    (hcd : c ≠ d) :
    Disjoint (S.subtreeRegion c) (S.subtreeRegion d) := by
  classical
  have hbranches :
      Disjoint
        (descendants T.meta_isTree S.root c)
        (descendants T.meta_isTree S.root d) := by
    simpa [childSubtree] using
      childSubtree_disjoint T.meta_isTree S.root
        S.parentDistanceDecreases hc hd hcd
  rw [Finset.disjoint_left]
  intro z hzC hzD
  rcases Finset.mem_biUnion.mp hzC with ⟨x, hxC, hzx⟩
  rcases Finset.mem_biUnion.mp hzD with ⟨y, hyD, hzy⟩
  rcases Finset.mem_union.mp hzx with hzxCluster | hzxConnector
  · rcases Finset.mem_union.mp hzy with hzyCluster | hzyConnector
    · have hxy : x ≠ y := by
        intro h
        subst y
        exact Finset.disjoint_left.mp hbranches hxC hyD
      exact Finset.disjoint_left.mp (T.cluster_disjoint hxy)
        hzxCluster hzyCluster
    · rcases Finset.mem_biUnion.mp hzyConnector with
        ⟨e, heChildMem, hze⟩
      have heChild :
          IsChild T.meta_isTree S.root y e :=
        (mem_children T.meta_isTree S.root y e).1 heChildMem
      have heD :
          e ∈ descendants T.meta_isTree S.root d :=
        S.mem_descendants_of_child hd.1 hyD heChild
      have hxy : x ≠ y := by
        intro h
        subst y
        exact Finset.disjoint_left.mp hbranches hxC hyD
      have hxe : x ≠ e := by
        intro h
        subst e
        exact Finset.disjoint_left.mp hbranches hxC heD
      have hdisj :=
        T.connector_vertexSet_disjoint_cluster_of_ne
          y e (S.adj_child heChild) x hxy hxe
      exact Finset.disjoint_left.mp hdisj.symm hzxCluster
        (by simpa [S.childConnectorVertexSet_eq heChild] using hze)
  · rcases Finset.mem_biUnion.mp hzxConnector with
      ⟨e, heChildMem, hze⟩
    have heChild :
        IsChild T.meta_isTree S.root x e :=
      (mem_children T.meta_isTree S.root x e).1 heChildMem
    have heC :
        e ∈ descendants T.meta_isTree S.root c :=
      S.mem_descendants_of_child hc.1 hxC heChild
    rcases Finset.mem_union.mp hzy with hzyCluster | hzyConnector
    · have hyx : y ≠ x := by
        intro h
        subst y
        exact Finset.disjoint_left.mp hbranches hxC hyD
      have hye : y ≠ e := by
        intro h
        subst y
        exact Finset.disjoint_left.mp hbranches heC hyD
      have hdisj :=
        T.connector_vertexSet_disjoint_cluster_of_ne
          x e (S.adj_child heChild) y hyx hye
      exact Finset.disjoint_left.mp hdisj
        (by simpa [S.childConnectorVertexSet_eq heChild] using hze)
        hzyCluster
    · rcases Finset.mem_biUnion.mp hzyConnector with
        ⟨f, hfChildMem, hzf⟩
      have hfChild :
          IsChild T.meta_isTree S.root y f :=
        (mem_children T.meta_isTree S.root y f).1 hfChildMem
      have hfD :
          f ∈ descendants T.meta_isTree S.root d :=
        S.mem_descendants_of_child hd.1 hyD hfChild
      have hedge : s(x, e) ≠ s(y, f) := by
        intro hedgeEq
        rw [Sym2.eq_iff] at hedgeEq
        rcases hedgeEq with h | h
        · exact Finset.disjoint_left.mp hbranches hxC
            (by simpa [h.1] using hyD)
        · exact Finset.disjoint_left.mp hbranches hxC
            (by simpa [h.1] using hfD)
      have hdisj :=
        PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (T.connector_mutually_nodeDisjoint
            x e (S.adj_child heChild)
            y f (S.adj_child hfChild) hedge)
      exact Finset.disjoint_left.mp hdisj
        (by simpa [S.childConnectorVertexSet_eq heChild] using hze)
        (by simpa [S.childConnectorVertexSet_eq hfChild] using hzf)

/-- The root cluster of a structural subtree belongs to its region. -/
theorem Theorem46LeafExtractionSetup.cluster_subset_subtreeRegion
    (S : Theorem46LeafExtractionSetup T ell) (v : Fin m) :
    T.cluster v ⊆ S.subtreeRegion v := by
  intro x hx
  rw [Theorem46LeafExtractionSetup.subtreeRegion]
  exact Finset.mem_biUnion.mpr
    ⟨v, self_mem_descendants T.meta_isTree S.root v,
      Finset.mem_union_left _ hx⟩

/-- Every descendant cluster belongs to the structural region. -/
theorem Theorem46LeafExtractionSetup.cluster_subset_subtreeRegion_of_mem
    (S : Theorem46LeafExtractionSetup T ell)
    {v x : Fin m}
    (hx : x ∈ descendants T.meta_isTree S.root v) :
    T.cluster x ⊆ S.subtreeRegion v := by
  intro z hz
  rw [Theorem46LeafExtractionSetup.subtreeRegion]
  exact Finset.mem_biUnion.mpr
    ⟨x, hx, Finset.mem_union_left _ hz⟩

/-- The connector from a subtree root to a child belongs to the root's
structural region. -/
theorem Theorem46LeafExtractionSetup.childConnector_subset_subtreeRegion
    (S : Theorem46LeafExtractionSetup T ell)
    {v c : Fin m} (hc : IsChild T.meta_isTree S.root v c) :
    (T.connector v c (S.adj_child hc)).toPathPacking.vertexSet ⊆
      S.subtreeRegion v := by
  intro x hx
  rw [Theorem46LeafExtractionSetup.subtreeRegion]
  refine Finset.mem_biUnion.mpr
    ⟨v, self_mem_descendants T.meta_isTree S.root v,
      Finset.mem_union_right _ ?_⟩
  exact Finset.mem_biUnion.mpr
    ⟨c, (mem_children T.meta_isTree S.root v c).2 hc,
      by simpa [S.childConnectorVertexSet_eq hc] using hx⟩

/-- Every descendant of a child is also a descendant of its parent. -/
theorem Theorem46LeafExtractionSetup.mem_descendants_of_childSubtree
    (S : Theorem46LeafExtractionSetup T ell)
    {v c x : Fin m}
    (hc : IsChild T.meta_isTree S.root v c)
    (hx : x ∈ descendants T.meta_isTree S.root c) :
    x ∈ descendants T.meta_isTree S.root v := by
  rw [mem_descendants] at hx ⊢
  rcases hx with ⟨n, hncard, hn⟩
  refine ⟨n + 1, ?_, ?_⟩
  · have hchain :=
      dist_add_iterate_eq T.meta_isTree S.root
        S.parentDistanceDecreases hc.1 hn
    have hcstep := hc.dist_eq_add_one
      T.meta_isTree S.root S.parentDistanceDecreases
    have hdistLt := dist_lt_card T.meta_isTree S.root x
    omega
  · simpa only [Function.iterate_succ_apply', hn, hc.2]

/-- A child structural region is contained in its parent's region. -/
theorem Theorem46LeafExtractionSetup.subtreeRegion_mono_child
    (S : Theorem46LeafExtractionSetup T ell)
    {v c : Fin m} (hc : IsChild T.meta_isTree S.root v c) :
    S.subtreeRegion c ⊆ S.subtreeRegion v := by
  intro z hz
  rw [Theorem46LeafExtractionSetup.subtreeRegion] at hz ⊢
  rcases Finset.mem_biUnion.mp hz with ⟨x, hxc, hzx⟩
  exact Finset.mem_biUnion.mpr
    ⟨x, S.mem_descendants_of_childSubtree hc hxc, hzx⟩

/-- A parent cluster is disjoint from the entire structural region rooted at
one of its children. -/
theorem Theorem46LeafExtractionSetup.cluster_disjoint_subtreeRegion
    (S : Theorem46LeafExtractionSetup T ell)
    {v c : Fin m} (hc : IsChild T.meta_isTree S.root v c) :
    Disjoint (T.cluster v) (S.subtreeRegion c) := by
  classical
  have hvNot :
      v ∉ descendants T.meta_isTree S.root c := by
    simpa [childSubtree] using
      parent_not_mem_childSubtree T.meta_isTree S.root
        S.parentDistanceDecreases hc
  rw [Finset.disjoint_left]
  intro z hzV hzRegion
  rcases Finset.mem_biUnion.mp hzRegion with ⟨x, hx, hzx⟩
  rcases Finset.mem_union.mp hzx with hzCluster | hzConnector
  · have hvx : v ≠ x := by
      intro h
      subst x
      exact hvNot hx
    exact Finset.disjoint_left.mp (T.cluster_disjoint hvx)
      hzV hzCluster
  · rcases Finset.mem_biUnion.mp hzConnector with
      ⟨e, heMem, hze⟩
    have heChild :
        IsChild T.meta_isTree S.root x e :=
      (mem_children T.meta_isTree S.root x e).1 heMem
    have heDesc :
        e ∈ descendants T.meta_isTree S.root c :=
      S.mem_descendants_of_child hc.1 hx heChild
    have hvx : v ≠ x := by
      intro h
      subst x
      exact hvNot hx
    have hve : v ≠ e := by
      intro h
      subst e
      exact hvNot heDesc
    have hdisj :=
      T.connector_vertexSet_disjoint_cluster_of_ne
        x e (S.adj_child heChild) v hvx hve
    exact Finset.disjoint_left.mp hdisj.symm hzV
      (by simpa [S.childConnectorVertexSet_eq heChild] using hze)

/-- The connector entering one child is disjoint from the downstream region of
a distinct sibling. -/
theorem Theorem46LeafExtractionSetup.enteringConnector_disjoint_siblingRegion
    (S : Theorem46LeafExtractionSetup T ell)
    {v c d : Fin m}
    (hc : IsChild T.meta_isTree S.root v c)
    (hd : IsChild T.meta_isTree S.root v d)
    (hcd : c ≠ d) :
    Disjoint
      (T.connector v d (S.adj_child hd)).toPathPacking.vertexSet
      (S.subtreeRegion c) := by
  classical
  have hvNot :
      v ∉ descendants T.meta_isTree S.root c := by
    simpa [childSubtree] using
      parent_not_mem_childSubtree T.meta_isTree S.root
        S.parentDistanceDecreases hc
  have hdNot :
      d ∉ descendants T.meta_isTree S.root c := by
    intro hdc
    have hdd :
        d ∈ descendants T.meta_isTree S.root d :=
      self_mem_descendants T.meta_isTree S.root d
    have hbranches :
        Disjoint
          (descendants T.meta_isTree S.root c)
          (descendants T.meta_isTree S.root d) := by
      simpa [childSubtree] using
        childSubtree_disjoint T.meta_isTree S.root
          S.parentDistanceDecreases hc hd hcd
    exact Finset.disjoint_left.mp hbranches hdc hdd
  rw [Finset.disjoint_left]
  intro z hzEnter hzRegion
  rcases Finset.mem_biUnion.mp hzRegion with ⟨x, hx, hzx⟩
  rcases Finset.mem_union.mp hzx with hzCluster | hzConnector
  · have hxv : x ≠ v := by
      intro h
      subst x
      exact hvNot hx
    have hxd : x ≠ d := by
      intro h
      subst x
      exact hdNot hx
    have hdisj :=
      T.connector_vertexSet_disjoint_cluster_of_ne
        v d (S.adj_child hd) x hxv hxd
    exact Finset.disjoint_left.mp hdisj hzEnter hzCluster
  · rcases Finset.mem_biUnion.mp hzConnector with
      ⟨e, heMem, hze⟩
    have heChild :
        IsChild T.meta_isTree S.root x e :=
      (mem_children T.meta_isTree S.root x e).1 heMem
    have heDesc :
        e ∈ descendants T.meta_isTree S.root c :=
      S.mem_descendants_of_child hc.1 hx heChild
    have hedge : s(v, d) ≠ s(x, e) := by
      intro hedgeEq
      rw [Sym2.eq_iff] at hedgeEq
      rcases hedgeEq with h | h
      · exact hvNot (by simpa [h.1] using hx)
      · exact hvNot (by simpa [h.1] using heDesc)
    have hdisj :=
      PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (T.connector_mutually_nodeDisjoint
          v d (S.adj_child hd)
          x e (S.adj_child heChild) hedge)
    exact Finset.disjoint_left.mp hdisj hzEnter
      (by simpa [S.childConnectorVertexSet_eq heChild] using hze)

/-- A packing supported in a parent cluster, the entering connector of one
child, and an additional set disjoint from the child subtree is internally
disjoint from the child's downstream region.  Its only permitted intersection
with that region is the endpoint in the child interface. -/
theorem Theorem46LeafExtractionSetup.transition_internallyDisjoint_subtreeRegion
    (S : Theorem46LeafExtractionSetup T ell)
    {v c : Fin m} (hc : IsChild T.meta_isTree S.root v c)
    {A B : Finset V} (P : PerfectPathPacking G A B)
    {Z : Finset V}
    (hstay :
      P.toPathPacking.StaysIn
        (T.cluster v ∪
          ((T.connector v c (S.adj_child hc)).toPathPacking.vertexSet ∪ Z)))
    (hinternalC :
      P.toPathPacking.InternallyDisjointFromSet (T.cluster c))
    (hZ : Disjoint Z (S.subtreeRegion c)) :
    P.toPathPacking.InternallyDisjointFromSet (S.subtreeRegion c) := by
  classical
  have hvNot :
      v ∉ descendants T.meta_isTree S.root c := by
    simpa [childSubtree] using
      parent_not_mem_childSubtree T.meta_isTree S.root
        S.parentDistanceDecreases hc
  intro i z hzP hzRegion
  rcases Finset.mem_union.mp (hstay i hzP) with hzV | hzRest
  · exact False.elim
      (Finset.disjoint_left.mp (S.cluster_disjoint_subtreeRegion hc)
        hzV hzRegion)
  rcases Finset.mem_union.mp hzRest with hzEnter | hzZ
  · rcases Finset.mem_biUnion.mp hzRegion with ⟨x, hx, hzx⟩
    rcases Finset.mem_union.mp hzx with hzCluster | hzConnector
    · by_cases hxc : x = c
      · subst x
        exact hinternalC i hzP hzCluster
      · have hxv : x ≠ v := by
          intro h
          subst x
          exact hvNot hx
        have hdisj :=
          T.connector_vertexSet_disjoint_cluster_of_ne
            v c (S.adj_child hc) x hxv hxc
        exact False.elim
          (Finset.disjoint_left.mp hdisj hzEnter hzCluster)
    · rcases Finset.mem_biUnion.mp hzConnector with
        ⟨e, heMem, hze⟩
      have heChild :
          IsChild T.meta_isTree S.root x e :=
        (mem_children T.meta_isTree S.root x e).1 heMem
      have heDesc :
          e ∈ descendants T.meta_isTree S.root c :=
        S.mem_descendants_of_child hc.1 hx heChild
      have hedge : s(v, c) ≠ s(x, e) := by
        intro hedgeEq
        rw [Sym2.eq_iff] at hedgeEq
        rcases hedgeEq with h | h
        · exact hvNot (by simpa [h.1] using hx)
        · exact hvNot (by simpa [h.1] using heDesc)
      have hdisj :=
        PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (T.connector_mutually_nodeDisjoint
            v c (S.adj_child hc)
            x e (S.adj_child heChild) hedge)
      exact False.elim
        (Finset.disjoint_left.mp hdisj hzEnter
          (by simpa [S.childConnectorVertexSet_eq heChild] using hze))
  · exact False.elim (Finset.disjoint_left.mp hZ hzZ hzRegion)

/-- Empty child branches contribute nothing to a union of selected leaves. -/
theorem Theorem46LeafExtractionSetup.selectedBelow_eq_biUnion_activeChildren
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ∉ S.leaves) :
    S.selectedBelow v =
      (S.activeChildren v).biUnion S.selectedBelow := by
  classical
  rw [S.selectedBelow_eq_biUnion_children hv]
  ext x
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨c, hc, hxc⟩
    exact Finset.mem_biUnion.mpr
      ⟨c, (S.mem_activeChildren v c).2
        ⟨hc, ⟨x, hxc⟩⟩, hxc⟩
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨c, hc, hxc⟩
    exact Finset.mem_biUnion.mpr
      ⟨c, (S.mem_activeChildren v c).1 hc |>.1, hxc⟩

/-- Selected-leaf sets belonging to distinct active children are disjoint. -/
theorem Theorem46LeafExtractionSetup.activeChildren_pairwiseDisjoint_selectedBelow
    (S : Theorem46LeafExtractionSetup T ell) (v : Fin m) :
    (S.activeChildren v : Set (Fin m)).PairwiseDisjoint S.selectedBelow := by
  intro c hc d hd hcd
  exact S.selectedBelow_children_disjoint
    ((S.mem_activeChildren v c).1 hc).1
    ((S.mem_activeChildren v d).1 hd).1 hcd

/-- The descendant count at a nonselected vertex is the sum of the active
child descendant counts. -/
theorem Theorem46LeafExtractionSetup.selectedBelow_card_eq_sum_activeChildren
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ∉ S.leaves) :
    (S.selectedBelow v).card =
      ∑ c ∈ S.activeChildren v, (S.selectedBelow c).card := by
  rw [S.selectedBelow_eq_biUnion_activeChildren hv,
    Finset.card_biUnion
      (S.activeChildren_pairwiseDisjoint_selectedBelow v)]

/-- Quotas obtained by multiplying descendant counts by `q` add across the
active child branches. -/
theorem Theorem46LeafExtractionSetup.selectedBelow_mul_eq_sum_activeChildren
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ∉ S.leaves) (q : ℕ) :
    (S.selectedBelow v).card * q =
      ∑ c ∈ S.activeChildren v, (S.selectedBelow c).card * q := by
  rw [S.selectedBelow_card_eq_sum_activeChildren hv,
    Finset.sum_mul]

/-- The DFS root has exactly its distinguished child. -/
theorem Theorem46LeafExtractionSetup.children_root_eq_singleton
    (S : Theorem46LeafExtractionSetup T ell) :
    children T.meta_isTree S.root S.root = {S.child} := by
  classical
  ext c
  constructor
  · intro hc
    have hcChild :
        IsChild T.meta_isTree S.root S.root c :=
      (mem_children T.meta_isTree S.root S.root c).1 hc
    have hadj : T.metaTree.Adj S.root c := by
      simpa [hcChild.2] using
        parent_adj T.meta_isTree S.root hcChild.1
    simpa [S.root_child_unique c hadj]
  · intro hc
    have hcEq : c = S.child := by simpa using hc
    subst c
    exact (mem_children T.meta_isTree S.root S.root S.child).2
      ⟨by
        intro h
        exact T.metaTree.loopless.irrefl S.root (by
          simpa [h] using S.root_child_adj),
       parent_eq_of_adj_of_dist_eq_add_one
         T.meta_isTree S.root S.root_child_adj.symm (by
           rw [T.metaTree.dist_self]
           simp [T.metaTree.dist_eq_one_iff_adj.mpr S.root_child_adj])⟩

/-- All selected leaves lie in the subtree rooted at the distinguished child
of the DFS root. -/
theorem Theorem46LeafExtractionSetup.selectedBelow_child_eq_leaves
    (S : Theorem46LeafExtractionSetup T ell) :
    S.selectedBelow S.child = S.leaves := by
  classical
  apply Finset.Subset.antisymm (S.selectedBelow_subset_leaves S.child)
  intro x hx
  have hxroot : x ≠ S.root := S.selectedLeaf_ne_root_routing hx
  have hxDescRoot :
      x ∈ descendants T.meta_isTree S.root S.root :=
    mem_descendants_root T.meta_isTree S.root x
  rcases exists_child_of_mem_descendants_of_ne
      T.meta_isTree S.root S.parentDistanceDecreases
      hxDescRoot hxroot with
    ⟨c, hc, hxc⟩
  have hcEq : c = S.child := by
    have : c ∈ ({S.child} : Finset (Fin m)) := by
      simpa [S.children_root_eq_singleton] using hc
    simpa using this
  exact (S.mem_selectedBelow S.child x).2
    ⟨hx, by simpa [hcEq] using hxc⟩

/-- Every selected leaf is below the DFS root. -/
theorem Theorem46LeafExtractionSetup.selectedBelow_root_eq_leaves
    (S : Theorem46LeafExtractionSetup T ell) :
    S.selectedBelow S.root = S.leaves := by
  classical
  apply Finset.Subset.antisymm (S.selectedBelow_subset_leaves S.root)
  intro x hx
  exact (S.mem_selectedBelow S.root x).2
    ⟨hx, mem_descendants_root T.meta_isTree S.root x⟩

@[simp] theorem Theorem46LeafExtractionSetup.selectedBelow_child_card
    (S : Theorem46LeafExtractionSetup T ell) :
    (S.selectedBelow S.child).card = ell := by
  rw [S.selectedBelow_child_eq_leaves, S.leaves_card]

/-- The one-child top-down transition at a degree-two meta-vertex.  It links
the incoming endpoints across the current cluster and then follows the
restricted child connector. -/
structure Theorem47OneChildTransitionData
    (T : StrongTreeOfSetsSystem G m W)
    {v p c : Fin m}
    (hpv : T.metaTree.Adj v p) (hvc : T.metaTree.Adj v c)
    (A : Finset V) where
  childIncoming : Finset V
  childIncoming_subset :
    childIncoming ⊆ T.interface c v hvc.symm
  childIncoming_card : childIncoming.card = A.card
  transition : PerfectPathPacking G A childIncoming
  transition_card : transition.card = A.card
  transition_staysIn :
    transition.toPathPacking.StaysIn
      (T.cluster v ∪ (T.connector v c hvc).toPathPacking.vertexSet)
  transition_internallyDisjoint_child :
    transition.toPathPacking.InternallyDisjointFromSet (T.cluster c)

/-- Existence of the source-faithful one-child transition used in the
top-down proof of Theorem 4.7. -/
theorem exists_theorem47_oneChildTransitionData
    {v p c : Fin m}
    (hpv : T.metaTree.Adj v p) (hvc : T.metaTree.Adj v c)
    (hpc : p ≠ c)
    {A : Finset V}
    (hA : A ⊆ T.interface v p hpv)
    (hAle : A.card ≤ W) :
    Nonempty (Theorem47OneChildTransitionData T hpv hvc A) := by
  classical
  have hAleInterface :
      A.card ≤ (T.interface v c hvc).card := by
    simpa [T.interface_card v c hvc] using hAle
  rcases Finset.exists_subset_card_eq hAleInterface with
    ⟨B, hB, hBcard⟩
  have hABcard : A.card = B.card := hBcard.symm
  rcases T.exists_interface_pair_perfect_linkage_between_subsets
      hpv hvc hpc hA hB hABcard with
    ⟨L, hLcard, hLstay⟩
  let C := T.connector v c hvc
  let R := C.restrictSourceSet B hB
  let U := C.targetSet (C.sourceIndexSetOfSubset B)
  have hRstay :
      R.toPathPacking.StaysIn C.toPathPacking.vertexSet :=
    C.restrictSourceSet_staysIn_vertexSet B hB
  have hRinternalV :
      R.toPathPacking.InternallyDisjointFromSet (T.cluster v) :=
    C.restrictSourceSet_internallyDisjointFromSet B hB
      (T.connector_internally_disjoint_cluster v c hvc v)
  have hRinternalC :
      R.toPathPacking.InternallyDisjointFromSet (T.cluster c) :=
    C.restrictSourceSet_internallyDisjointFromSet B hB
      (T.connector_internally_disjoint_cluster v c hvc c)
  have hUsub : U ⊆ T.interface c v hvc.symm := by
    exact C.targetSet_subset_right _
  have hUdisjV : Disjoint U (T.cluster v) := by
    exact Finset.disjoint_of_subset_left
      (hUsub.trans (T.interface_subset_cluster c v hvc.symm))
      (T.cluster_disjoint hvc.ne.symm)
  have hBdisjC : Disjoint B (T.cluster c) := by
    exact Finset.disjoint_of_subset_left
      (hB.trans (T.interface_subset_cluster v c hvc))
      (T.cluster_disjoint hvc.ne)
  let P : PerfectPathPacking G A U :=
    L.concatOfFirstStaysInSecondInternallyDisjoint
      R hLstay hRinternalV hUdisjV
  have hPstay :
      P.toPathPacking.StaysIn
        (T.cluster v ∪ C.toPathPacking.vertexSet) := by
    exact
      L.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        R hLstay hRinternalV hUdisjV hRstay
  have hLinternalC :
      L.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
    intro i x hx hxC
    exact False.elim
      (Finset.disjoint_left.mp (T.cluster_disjoint hvc.ne)
        (hLstay i hx) hxC)
  have hPinternalC :
      P.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
    exact
      L.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
        R hLstay hRinternalV hUdisjV
        hLinternalC hRinternalC hBdisjC
  exact ⟨{
    childIncoming := U
    childIncoming_subset := hUsub
    childIncoming_card := by
      calc
        U.card = R.card := R.card_eq_right_card.symm
        _ = B.card := by simp [R]
        _ = A.card := hBcard
    transition := P
    transition_card := by
      calc
        P.card = L.card := by simp [P]
        _ = A.card := hLcard
    transition_staysIn := hPstay
    transition_internallyDisjoint_child := hPinternalC }⟩

/-- The two-child top-down transition at a degree-three meta-vertex.  Claim 4.8
splits the incoming terminals into the two prescribed descendant quotas; the
two restricted child connectors then transport those endpoints into the child
clusters. -/
structure Theorem47TwoChildTransitionData
    (T : StrongTreeOfSetsSystem G m W)
    {v p c d : Fin m}
    (hpv : T.metaTree.Adj v p)
    (hvc : T.metaTree.Adj v c) (hvd : T.metaTree.Adj v d)
    (A : Finset V) (k₁ k₂ : ℕ) where
  parent_ne_left : p ≠ c
  parent_ne_right : p ≠ d
  children_ne : c ≠ d
  leftParent : Finset V
  rightParent : Finset V
  leftParent_subset :
    leftParent ⊆ T.interface v c hvc
  rightParent_subset :
    rightParent ⊆ T.interface v d hvd
  leftIncoming : Finset V
  rightIncoming : Finset V
  leftIncoming_subset :
    leftIncoming ⊆ T.interface c v hvc.symm
  rightIncoming_subset :
    rightIncoming ⊆ T.interface d v hvd.symm
  leftIncoming_card : leftIncoming.card = k₁
  rightIncoming_card : rightIncoming.card = k₂
  incoming_disjoint : Disjoint leftIncoming rightIncoming
  leftConnector :
    PerfectPathPacking G leftParent leftIncoming
  rightConnector :
    PerfectPathPacking G rightParent rightIncoming
  leftConnector_staysIn :
    leftConnector.toPathPacking.StaysIn
      (T.connector v c hvc).toPathPacking.vertexSet
  rightConnector_staysIn :
    rightConnector.toPathPacking.StaysIn
      (T.connector v d hvd).toPathPacking.vertexSet
  leftConnector_internallyDisjoint_clusters :
    ∀ x : Fin m,
      leftConnector.toPathPacking.InternallyDisjointFromSet (T.cluster x)
  rightConnector_internallyDisjoint_clusters :
    ∀ x : Fin m,
      rightConnector.toPathPacking.InternallyDisjointFromSet (T.cluster x)
  /-- The Claim 4.8 linkage inside the branching cluster, before the two
  child connector families are appended.  Step 2 reuses its reverse as the
  portions of the Step 1 paths lying inside the current cluster. -/
  parentPacking :
    PerfectPathPacking G A (leftParent ∪ rightParent)
  parentPacking_staysIn :
    parentPacking.toPathPacking.StaysIn (T.cluster v)
  transition :
    PerfectPathPacking G A (leftIncoming ∪ rightIncoming)
  transition_card : transition.card = A.card
  transition_staysIn :
    transition.toPathPacking.StaysIn
      (T.cluster v ∪
        ((T.connector v c hvc).toPathPacking.vertexSet ∪
          (T.connector v d hvd).toPathPacking.vertexSet))
  transition_internallyDisjoint_left :
    transition.toPathPacking.InternallyDisjointFromSet (T.cluster c)
  transition_internallyDisjoint_right :
    transition.toPathPacking.InternallyDisjointFromSet (T.cluster d)

/-- Existence of the source-faithful two-child transition.  This is the local
branching operation in Theorem 4.7, with exact natural-number quotas. -/
theorem exists_theorem47_twoChildTransitionData
    {v p c d : Fin m}
    (hpv : T.metaTree.Adj v p)
    (hvc : T.metaTree.Adj v c) (hvd : T.metaTree.Adj v d)
    (hpc : p ≠ c) (hpd : p ≠ d) (hcd : c ≠ d)
    {A : Finset V} {k₁ k₂ : ℕ}
    (hA : A ⊆ T.interface v p hpv)
    (hAcard : A.card = k₁ + k₂)
    (hAle : A.card ≤ W) :
    Nonempty
      (Theorem47TwoChildTransitionData T hpv hvc hvd A k₁ k₂) := by
  classical
  have hlinkC :
      NodeLinkedIn G (T.cluster v) A (T.interface v c hvc) :=
    (T.interface_pair_nodeLinked hpv hvc hpc).mono_terminals hA subset_rfl
  have hlinkD :
      NodeLinkedIn G (T.cluster v) A (T.interface v d hvd) :=
    (T.interface_pair_nodeLinked hpv hvd hpd).mono_terminals hA subset_rfl
  have hchildInterfaces :
      Disjoint (T.interface v c hvc) (T.interface v d hvd) :=
    T.interface_disjoint hvc hvd hcd
  have hAleC : A.card ≤ (T.interface v c hvc).card := by
    simpa [T.interface_card v c hvc] using hAle
  have hAleD : A.card ≤ (T.interface v d hvd).card := by
    simpa [T.interface_card v d hvd] using hAle
  let D :=
    Classical.choice
      (exists_claim48_quotaSplitData
        hlinkC hlinkD hchildInterfaces hAcard hAleC hAleD)
  let C₁ := T.connector v c hvc
  let C₂ := T.connector v d hvd
  let R₁ := C₁.restrictSourceSet D.leftTargets D.leftTargets_subset
  let R₂ := C₂.restrictSourceSet D.rightTargets D.rightTargets_subset
  let U₁ := C₁.targetSet
    (C₁.sourceIndexSetOfSubset D.leftTargets)
  let U₂ := C₂.targetSet
    (C₂.sourceIndexSetOfSubset D.rightTargets)
  have hU₁sub : U₁ ⊆ T.interface c v hvc.symm := by
    exact C₁.targetSet_subset_right _
  have hU₂sub : U₂ ⊆ T.interface d v hvd.symm := by
    exact C₂.targetSet_subset_right _
  have hUdisj : Disjoint U₁ U₂ := by
    exact Finset.disjoint_of_subset_left
      (hU₁sub.trans (T.interface_subset_cluster c v hvc.symm))
      (Finset.disjoint_of_subset_right
        (hU₂sub.trans (T.interface_subset_cluster d v hvd.symm))
        (T.cluster_disjoint hcd))
  have hedge : s(v, c) ≠ s(v, d) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hcd h.2
    · exact hvd.ne h.1
  have hRnode :
      R₁.toPathPacking.MutuallyNodeDisjoint R₂.toPathPacking := by
    exact C₁.restrictSourceSet_mutuallyNodeDisjoint C₂
      D.leftTargets D.leftTargets_subset
      D.rightTargets D.rightTargets_subset
      (T.connector_mutually_nodeDisjoint v c hvc v d hvd hedge)
  let Q : PerfectPathPacking G
      (D.leftTargets ∪ D.rightTargets) (U₁ ∪ U₂) :=
    R₁.disjointUnion R₂ D.targets_disjoint hUdisj hRnode
  have hR₁stay :
      R₁.toPathPacking.StaysIn C₁.toPathPacking.vertexSet :=
    C₁.restrictSourceSet_staysIn_vertexSet
      D.leftTargets D.leftTargets_subset
  have hR₂stay :
      R₂.toPathPacking.StaysIn C₂.toPathPacking.vertexSet :=
    C₂.restrictSourceSet_staysIn_vertexSet
      D.rightTargets D.rightTargets_subset
  have hQstay :
      Q.toPathPacking.StaysIn
        (C₁.toPathPacking.vertexSet ∪ C₂.toPathPacking.vertexSet) := by
    apply PerfectPathPacking.disjointUnion_staysIn
    · intro i x hx
      exact Finset.mem_union_left _ (hR₁stay i hx)
    · intro i x hx
      exact Finset.mem_union_right _ (hR₂stay i hx)
  have hR₁internalV :
      R₁.toPathPacking.InternallyDisjointFromSet (T.cluster v) :=
    C₁.restrictSourceSet_internallyDisjointFromSet
      D.leftTargets D.leftTargets_subset
      (T.connector_internally_disjoint_cluster v c hvc v)
  have hR₂internalV :
      R₂.toPathPacking.InternallyDisjointFromSet (T.cluster v) :=
    C₂.restrictSourceSet_internallyDisjointFromSet
      D.rightTargets D.rightTargets_subset
      (T.connector_internally_disjoint_cluster v d hvd v)
  have hQinternalV :
      Q.toPathPacking.InternallyDisjointFromSet (T.cluster v) :=
    PerfectPathPacking.disjointUnion_internallyDisjointFromSet
      R₁ R₂ D.targets_disjoint hUdisj hRnode
      hR₁internalV hR₂internalV
  have hUdisjV : Disjoint (U₁ ∪ U₂) (T.cluster v) := by
    rw [Finset.disjoint_left]
    intro x hxU hxV
    rcases Finset.mem_union.mp hxU with hx₁ | hx₂
    · exact Finset.disjoint_left.mp (T.cluster_disjoint hvc.ne.symm)
        (hU₁sub.trans (T.interface_subset_cluster c v hvc.symm) hx₁) hxV
    · exact Finset.disjoint_left.mp (T.cluster_disjoint hvd.ne.symm)
        (hU₂sub.trans (T.interface_subset_cluster d v hvd.symm) hx₂) hxV
  let P : PerfectPathPacking G A (U₁ ∪ U₂) :=
    D.packing.concatOfFirstStaysInSecondInternallyDisjoint
      Q D.packing_staysIn hQinternalV hUdisjV
  have hPstay :
      P.toPathPacking.StaysIn
        (T.cluster v ∪
          (C₁.toPathPacking.vertexSet ∪ C₂.toPathPacking.vertexSet)) := by
    exact
      D.packing.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        Q D.packing_staysIn hQinternalV hUdisjV hQstay
  have hDinternalC :
      D.packing.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
    intro i x hx hxC
    exact False.elim
      (Finset.disjoint_left.mp (T.cluster_disjoint hvc.ne)
        (D.packing_staysIn i hx) hxC)
  have hDinternalD :
      D.packing.toPathPacking.InternallyDisjointFromSet (T.cluster d) := by
    intro i x hx hxD
    exact False.elim
      (Finset.disjoint_left.mp (T.cluster_disjoint hvd.ne)
        (D.packing_staysIn i hx) hxD)
  have hQinternalC :
      Q.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
    exact PerfectPathPacking.disjointUnion_internallyDisjointFromSet
      R₁ R₂ D.targets_disjoint hUdisj hRnode
      (C₁.restrictSourceSet_internallyDisjointFromSet
        D.leftTargets D.leftTargets_subset
        (T.connector_internally_disjoint_cluster v c hvc c))
      (C₂.restrictSourceSet_internallyDisjointFromSet
        D.rightTargets D.rightTargets_subset
        (T.connector_internally_disjoint_cluster v d hvd c))
  have hQinternalD :
      Q.toPathPacking.InternallyDisjointFromSet (T.cluster d) := by
    exact PerfectPathPacking.disjointUnion_internallyDisjointFromSet
      R₁ R₂ D.targets_disjoint hUdisj hRnode
      (C₁.restrictSourceSet_internallyDisjointFromSet
        D.leftTargets D.leftTargets_subset
        (T.connector_internally_disjoint_cluster v c hvc d))
      (C₂.restrictSourceSet_internallyDisjointFromSet
        D.rightTargets D.rightTargets_subset
        (T.connector_internally_disjoint_cluster v d hvd d))
  have hTargetsDisjC :
      Disjoint (D.leftTargets ∪ D.rightTargets) (T.cluster c) := by
    exact Finset.disjoint_of_subset_left
      (Finset.union_subset
        (D.leftTargets_subset.trans (T.interface_subset_cluster v c hvc))
        (D.rightTargets_subset.trans (T.interface_subset_cluster v d hvd)))
      (T.cluster_disjoint hvc.ne)
  have hTargetsDisjD :
      Disjoint (D.leftTargets ∪ D.rightTargets) (T.cluster d) := by
    exact Finset.disjoint_of_subset_left
      (Finset.union_subset
        (D.leftTargets_subset.trans (T.interface_subset_cluster v c hvc))
        (D.rightTargets_subset.trans (T.interface_subset_cluster v d hvd)))
      (T.cluster_disjoint hvd.ne)
  have hPinternalC :
      P.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
    exact
      D.packing.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
        Q D.packing_staysIn hQinternalV hUdisjV
        hDinternalC hQinternalC hTargetsDisjC
  have hPinternalD :
      P.toPathPacking.InternallyDisjointFromSet (T.cluster d) := by
    exact
      D.packing.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
        Q D.packing_staysIn hQinternalV hUdisjV
        hDinternalD hQinternalD hTargetsDisjD
  exact ⟨{
    parent_ne_left := hpc
    parent_ne_right := hpd
    children_ne := hcd
    leftParent := D.leftTargets
    rightParent := D.rightTargets
    leftParent_subset := D.leftTargets_subset
    rightParent_subset := D.rightTargets_subset
    leftIncoming := U₁
    rightIncoming := U₂
    leftIncoming_subset := hU₁sub
    rightIncoming_subset := hU₂sub
    leftIncoming_card := by
      calc
        U₁.card = R₁.card := R₁.card_eq_right_card.symm
        _ = D.leftTargets.card := by simp [R₁]
        _ = k₁ := D.leftTargets_card
    rightIncoming_card := by
      calc
        U₂.card = R₂.card := R₂.card_eq_right_card.symm
        _ = D.rightTargets.card := by simp [R₂]
        _ = k₂ := D.rightTargets_card
    incoming_disjoint := hUdisj
    leftConnector := R₁
    rightConnector := R₂
    leftConnector_staysIn := hR₁stay
    rightConnector_staysIn := hR₂stay
    leftConnector_internallyDisjoint_clusters := by
      intro x
      exact C₁.restrictSourceSet_internallyDisjointFromSet
        D.leftTargets D.leftTargets_subset
        (T.connector_internally_disjoint_cluster v c hvc x)
    rightConnector_internallyDisjoint_clusters := by
      intro x
      exact C₂.restrictSourceSet_internallyDisjointFromSet
        D.rightTargets D.rightTargets_subset
        (T.connector_internally_disjoint_cluster v d hvd x)
    parentPacking := D.packing
    parentPacking_staysIn := D.packing_staysIn
    transition := P
    transition_card := by
      calc
        P.card = D.packing.card := by simp [P]
        _ = A.card := D.packing_card
    transition_staysIn := hPstay
    transition_internallyDisjoint_left := hPinternalC
    transition_internallyDisjoint_right := hPinternalD }⟩

/-- Recursive output of Theorem 4.7 below one active meta-vertex.  The target
terminals are partitioned by selected leaf, and the single perfect packing
certifies global vertex-disjointness across all leaf families. -/
structure Theorem47SubtreeRoutingData
    (S : Theorem46LeafExtractionSetup T ell)
    (v : Fin m) (A : Finset V) (q : ℕ) where
  leafTarget : Fin m → Finset V
  leafTarget_empty :
    ∀ x, x ∉ S.selectedBelow v → leafTarget x = ∅
  leafTarget_subset :
    ∀ x, x ∈ S.selectedBelow v → leafTarget x ⊆ T.cluster x
  leafTarget_card :
    ∀ x, x ∈ S.selectedBelow v → (leafTarget x).card = q
  leafTarget_nodeWellLinked :
    ∀ x, x ∈ S.selectedBelow v →
      NodeWellLinkedIn G (T.cluster x) (leafTarget x)
  packing :
    PerfectPathPacking G A
      ((S.selectedBelow v).biUnion leafTarget)
  packing_staysIn :
    packing.toPathPacking.StaysIn (S.subtreeRegion v)
  packing_internallyDisjoint_leafCluster :
    ∀ x, x ∈ S.selectedBelow v →
      packing.toPathPacking.InternallyDisjointFromSet (T.cluster x)
  packing_trivial_of_root_selected :
    v ∈ S.leaves →
      ∀ i : packing.Index, (packing.path i).source = (packing.path i).target

/-- The selected-leaf base case of the top-down recursion. -/
theorem exists_theorem47_leafSubtreeRoutingData
    (S : Theorem46LeafExtractionSetup T ell)
    {v : Fin m} (hv : v ∈ S.leaves)
    {A : Finset V} {q : ℕ}
    (hAcluster : A ⊆ T.cluster v)
    (hAnodeWellLinked : NodeWellLinkedIn G (T.cluster v) A)
    (hAcard : A.card = q) :
    Nonempty (Theorem47SubtreeRoutingData S v A q) := by
  classical
  let target : Fin m → Finset V := fun x => if x = v then A else ∅
  have hbelow : S.selectedBelow v = {v} :=
    S.selectedBelow_eq_singleton_of_mem_leaves hv
  have htargetUnion :
      (S.selectedBelow v).biUnion target = A := by
    simp [hbelow, target]
  let P : PerfectPathPacking G A
      ((S.selectedBelow v).biUnion target) :=
    (PerfectPathPacking.refl G A).copyTerminals rfl htargetUnion.symm
  exact ⟨{
    leafTarget := target
    leafTarget_empty := by
      intro x hx
      have hxv : x ≠ v := by
        intro h
        subst x
        exact hx (by simp [hbelow])
      simp [target, hxv]
    leafTarget_subset := by
      intro x hx
      have hxv : x = v := by simpa [hbelow] using hx
      subst x
      simpa [target] using hAcluster
    leafTarget_card := by
      intro x hx
      have hxv : x = v := by simpa [hbelow] using hx
      subst x
      simpa [target] using hAcard
    leafTarget_nodeWellLinked := by
      intro x hx
      have hxv : x = v := by simpa [hbelow] using hx
      subst x
      simpa [target] using hAnodeWellLinked
    packing := P
    packing_staysIn := by
      intro i x hx
      apply S.cluster_subset_subtreeRegion v
      apply hAcluster
      have hxi : x = (A.equivFin.symm i).1 := by
        simpa [P, PerfectPathPacking.copyTerminals,
          PerfectPathPacking.refl] using hx
      rw [hxi]
      exact (A.equivFin.symm i).2
    packing_internallyDisjoint_leafCluster := by
      intro x hx i z hz _hzCluster
      have hxv : x = v := by simpa [hbelow] using hx
      subst x
      have hzEq : z = (A.equivFin.symm i).1 := by
        simpa [P, PerfectPathPacking.copyTerminals,
          PerfectPathPacking.refl] using hz
      exact Or.inl (by
        simpa [P, PerfectPathPacking.copyTerminals,
          PerfectPathPacking.refl, hzEq])
    packing_trivial_of_root_selected := by
      intro _hv i
      simp [P, PerfectPathPacking.copyTerminals,
        PerfectPathPacking.refl] }⟩

/-- Compose a one-child local transition with the recursively constructed
packing below that child. -/
theorem Theorem47OneChildTransitionData.composeSubtreeRouting
    (S : Theorem46LeafExtractionSetup T ell)
    {v p c : Fin m}
    {hpv : T.metaTree.Adj v p} {hvc : T.metaTree.Adj v c}
    {A : Finset V} {q : ℕ}
    (hc : IsChild T.meta_isTree S.root v c)
    (hbelow : S.selectedBelow v = S.selectedBelow c)
    (hvnotleaf : v ∉ S.leaves)
    (hAcluster : A ⊆ T.cluster v)
    (D : Theorem47OneChildTransitionData T hpv hvc A)
    (E : Theorem47SubtreeRoutingData S c D.childIncoming q) :
    Nonempty (Theorem47SubtreeRoutingData S v A q) := by
  classical
  have hvcEq : hvc = S.adj_child hc := Subsingleton.elim _ _
  have hDinternal :
      D.transition.toPathPacking.InternallyDisjointFromSet
        (S.subtreeRegion c) := by
    apply S.transition_internallyDisjoint_subtreeRegion
      hc D.transition (Z := ∅)
    · simpa [hvcEq] using D.transition_staysIn
    · simpa [hvcEq] using D.transition_internallyDisjoint_child
    · exact Finset.disjoint_empty_left _
  have hAdisj :
      Disjoint A (S.subtreeRegion c) :=
    Finset.disjoint_of_subset_left hAcluster
      (S.cluster_disjoint_subtreeRegion hc)
  let P :=
    D.transition.concatOfFirstInternallyDisjointSecondStaysIn
      E.packing hDinternal E.packing_staysIn hAdisj
  have hPstayUnion :
      P.toPathPacking.StaysIn
        ((T.cluster v ∪
            (T.connector v c hvc).toPathPacking.vertexSet) ∪
          S.subtreeRegion c) := by
    exact
      D.transition.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
        E.packing hDinternal E.packing_staysIn hAdisj
        D.transition_staysIn
  have hSupportSubset :
      ((T.cluster v ∪
          (T.connector v c hvc).toPathPacking.vertexSet) ∪
        S.subtreeRegion c) ⊆ S.subtreeRegion v := by
    apply Finset.union_subset
    · apply Finset.union_subset
      · exact S.cluster_subset_subtreeRegion v
      · simpa [hvcEq] using S.childConnector_subset_subtreeRegion hc
    · exact S.subtreeRegion_mono_child hc
  have hPstay :
      P.toPathPacking.StaysIn (S.subtreeRegion v) := by
    intro i x hx
    exact hSupportSubset (hPstayUnion i hx)
  have hPinternalLeaf :
      ∀ x, x ∈ S.selectedBelow c →
        P.toPathPacking.InternallyDisjointFromSet (T.cluster x) := by
    intro x hx i z hz hzCluster
    have hxDesc :
        x ∈ descendants T.meta_isTree S.root c :=
      S.selectedBelow_subset_descendants c hx
    have hclusterSub :
        T.cluster x ⊆ S.subtreeRegion c :=
      S.cluster_subset_subtreeRegion_of_mem hxDesc
    have hsplit :=
      D.transition
        |>.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
          E.packing hDinternal E.packing_staysIn hAdisj i hz
    let j := D.transition.indexOfSourceTarget E.packing i
    have hmatch :
        (E.packing.path j).source = (D.transition.path i).target :=
      D.transition.source_indexOfSourceTarget E.packing i
    have hglueCluster :
        (D.transition.path i).target ∈ T.cluster c :=
      D.childIncoming_subset
        (D.transition.target_mem i) |>
          T.interface_subset_cluster c v hvc.symm
    have hglue_eq_fullTarget (hzGlue : z = (D.transition.path i).target) :
        z = (P.path i).target := by
      by_cases hxc : x = c
      · subst x
        have hcleaf : c ∈ S.leaves :=
          S.selectedBelow_subset_leaves c hx
        have htriv := E.packing_trivial_of_root_selected hcleaf j
        calc
          z = (D.transition.path i).target := hzGlue
          _ = (E.packing.path j).source := hmatch.symm
          _ = (E.packing.path j).target := htriv
          _ = (P.path i).target := rfl
      · exact False.elim
          (Finset.disjoint_left.mp
            (T.cluster_disjoint hxc)
            hzCluster (by simpa [hzGlue] using hglueCluster))
    rcases Finset.mem_union.mp hsplit with hzD | hzE
    · rcases hDinternal i hzD (hclusterSub hzCluster) with hsource | htarget
      · exact Or.inl (by simpa [P] using hsource)
      · exact Or.inr (hglue_eq_fullTarget htarget)
    · rcases E.packing_internallyDisjoint_leafCluster x hx j hzE hzCluster with
        hsource | htarget
      · exact Or.inr
          (hglue_eq_fullTarget (by
            calc
              z = (E.packing.path j).source := hsource
              _ = (D.transition.path i).target := hmatch))
      · exact Or.inr (by simpa [P, j] using htarget)
  let P' :
      PerfectPathPacking G A
        ((S.selectedBelow v).biUnion E.leafTarget) :=
    P.copyTerminals rfl (by simp [hbelow])
  exact ⟨{
    leafTarget := E.leafTarget
    leafTarget_empty := by
      intro x hx
      exact E.leafTarget_empty x (by simpa [hbelow] using hx)
    leafTarget_subset := by
      intro x hx
      exact E.leafTarget_subset x (by simpa [hbelow] using hx)
    leafTarget_card := by
      intro x hx
      exact E.leafTarget_card x (by simpa [hbelow] using hx)
    leafTarget_nodeWellLinked := by
      intro x hx
      exact E.leafTarget_nodeWellLinked x (by simpa [hbelow] using hx)
    packing := P'
    packing_staysIn :=
      P.copyTerminals_staysIn rfl (by simp [hbelow]) hPstay
    packing_internallyDisjoint_leafCluster := by
      intro x hx
      simpa [P'] using hPinternalLeaf x (by simpa [hbelow] using hx)
    packing_trivial_of_root_selected := by
      intro hv
      exact False.elim (hvnotleaf hv) }⟩

/-- Compose a two-child transition with the two recursively constructed,
structurally separated child packings. -/
theorem Theorem47TwoChildTransitionData.composeSubtreeRouting
    (S : Theorem46LeafExtractionSetup T ell)
    {v p c d : Fin m}
    {hpv : T.metaTree.Adj v p}
    {hvc : T.metaTree.Adj v c} {hvd : T.metaTree.Adj v d}
    {A : Finset V} {q k₁ k₂ : ℕ}
    (hc : IsChild T.meta_isTree S.root v c)
    (hd : IsChild T.meta_isTree S.root v d)
    (hcd : c ≠ d)
    (hbelow :
      S.selectedBelow v = S.selectedBelow c ∪ S.selectedBelow d)
    (hAcluster : A ⊆ T.cluster v)
    (D : Theorem47TwoChildTransitionData T hpv hvc hvd A k₁ k₂)
    (E₁ : Theorem47SubtreeRoutingData S c D.leftIncoming q)
    (E₂ : Theorem47SubtreeRoutingData S d D.rightIncoming q) :
    Nonempty (Theorem47SubtreeRoutingData S v A q) := by
  classical
  have hvcEq : hvc = S.adj_child hc := Subsingleton.elim _ _
  have hvdEq : hvd = S.adj_child hd := Subsingleton.elim _ _
  let U₁ := (S.selectedBelow c).biUnion E₁.leafTarget
  let U₂ := (S.selectedBelow d).biUnion E₂.leafTarget
  have hU₁region : U₁ ⊆ S.subtreeRegion c := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨x, hxc, hzx⟩
    exact S.cluster_subset_subtreeRegion_of_mem
      (S.selectedBelow_subset_descendants c hxc)
      (E₁.leafTarget_subset x hxc hzx)
  have hU₂region : U₂ ⊆ S.subtreeRegion d := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨x, hxd, hzx⟩
    exact S.cluster_subset_subtreeRegion_of_mem
      (S.selectedBelow_subset_descendants d hxd)
      (E₂.leafTarget_subset x hxd hzx)
  have hRegions :
      Disjoint (S.subtreeRegion c) (S.subtreeRegion d) :=
    S.subtreeRegion_disjoint hc hd hcd
  have hUdisj : Disjoint U₁ U₂ :=
    Finset.disjoint_of_subset_left hU₁region
      (Finset.disjoint_of_subset_right hU₂region hRegions)
  have hChildNode :
      E₁.packing.toPathPacking.MutuallyNodeDisjoint
        E₂.packing.toPathPacking := by
    intro i j
    rw [GraphPath.NodeDisjoint]
    exact hRegions.mono (E₁.packing_staysIn i) (E₂.packing_staysIn j)
  let Q : PerfectPathPacking G
      (D.leftIncoming ∪ D.rightIncoming) (U₁ ∪ U₂) :=
    E₁.packing.disjointUnion E₂.packing
      D.incoming_disjoint hUdisj hChildNode
  have hQstay :
      Q.toPathPacking.StaysIn
        (S.subtreeRegion c ∪ S.subtreeRegion d) := by
    apply PerfectPathPacking.disjointUnion_staysIn
    · intro i z hz
      exact Finset.mem_union_left _ (E₁.packing_staysIn i hz)
    · intro i z hz
      exact Finset.mem_union_right _ (E₂.packing_staysIn i hz)
  have hEnterDdisjC :
      Disjoint
        (T.connector v d hvd).toPathPacking.vertexSet
        (S.subtreeRegion c) := by
    simpa [hvdEq] using
      S.enteringConnector_disjoint_siblingRegion hc hd hcd
  have hEnterCdisjD :
      Disjoint
        (T.connector v c hvc).toPathPacking.vertexSet
        (S.subtreeRegion d) := by
    simpa [hvcEq] using
      S.enteringConnector_disjoint_siblingRegion hd hc hcd.symm
  have hDinternalC :
      D.transition.toPathPacking.InternallyDisjointFromSet
        (S.subtreeRegion c) := by
    apply S.transition_internallyDisjoint_subtreeRegion
      hc D.transition
      (Z := (T.connector v d hvd).toPathPacking.vertexSet)
    · simpa [hvcEq] using D.transition_staysIn
    · simpa [hvcEq] using D.transition_internallyDisjoint_left
    · exact hEnterDdisjC
  have hDinternalD :
      D.transition.toPathPacking.InternallyDisjointFromSet
        (S.subtreeRegion d) := by
    apply S.transition_internallyDisjoint_subtreeRegion
      hd D.transition
      (Z := (T.connector v c hvc).toPathPacking.vertexSet)
    · simpa [hvdEq, Finset.union_left_comm, Finset.union_comm,
        Finset.union_assoc] using D.transition_staysIn
    · simpa [hvdEq] using D.transition_internallyDisjoint_right
    · exact hEnterCdisjD
  have hDinternal :
      D.transition.toPathPacking.InternallyDisjointFromSet
        (S.subtreeRegion c ∪ S.subtreeRegion d) := by
    intro i z hz hzUnion
    rcases Finset.mem_union.mp hzUnion with hzC | hzD
    · exact hDinternalC i hz hzC
    · exact hDinternalD i hz hzD
  have hAdisj :
      Disjoint A (S.subtreeRegion c ∪ S.subtreeRegion d) := by
    rw [Finset.disjoint_left]
    intro z hzA hzUnion
    have hzV := hAcluster hzA
    rcases Finset.mem_union.mp hzUnion with hzC | hzD
    · exact Finset.disjoint_left.mp
        (S.cluster_disjoint_subtreeRegion hc) hzV hzC
    · exact Finset.disjoint_left.mp
        (S.cluster_disjoint_subtreeRegion hd) hzV hzD
  let P :=
    D.transition.concatOfFirstInternallyDisjointSecondStaysIn
      Q hDinternal hQstay hAdisj
  have hPstayUnion :
      P.toPathPacking.StaysIn
        ((T.cluster v ∪
            ((T.connector v c hvc).toPathPacking.vertexSet ∪
              (T.connector v d hvd).toPathPacking.vertexSet)) ∪
          (S.subtreeRegion c ∪ S.subtreeRegion d)) := by
    exact
      D.transition.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
        Q hDinternal hQstay hAdisj D.transition_staysIn
  have hSupportSubset :
      ((T.cluster v ∪
          ((T.connector v c hvc).toPathPacking.vertexSet ∪
            (T.connector v d hvd).toPathPacking.vertexSet)) ∪
        (S.subtreeRegion c ∪ S.subtreeRegion d)) ⊆
          S.subtreeRegion v := by
    apply Finset.union_subset
    · apply Finset.union_subset
      · exact S.cluster_subset_subtreeRegion v
      · apply Finset.union_subset
        · simpa [hvcEq] using S.childConnector_subset_subtreeRegion hc
        · simpa [hvdEq] using S.childConnector_subset_subtreeRegion hd
    · exact Finset.union_subset
        (S.subtreeRegion_mono_child hc)
        (S.subtreeRegion_mono_child hd)
  have hPstay :
      P.toPathPacking.StaysIn (S.subtreeRegion v) := by
    intro i z hz
    exact hSupportSubset (hPstayUnion i hz)
  have hSelectedDisj :
      Disjoint (S.selectedBelow c) (S.selectedBelow d) :=
    S.selectedBelow_children_disjoint
      ((mem_children T.meta_isTree S.root v c).2 hc)
      ((mem_children T.meta_isTree S.root v d).2 hd)
      hcd
  have hQinternalLeaf :
      ∀ x, x ∈ S.selectedBelow v →
        Q.toPathPacking.InternallyDisjointFromSet (T.cluster x) := by
    intro x hx
    have hx' : x ∈ S.selectedBelow c ∨ x ∈ S.selectedBelow d := by
      simpa [hbelow] using hx
    rcases hx' with hxc | hxd
    · have hxRegion :
          T.cluster x ⊆ S.subtreeRegion c :=
        S.cluster_subset_subtreeRegion_of_mem
          (S.selectedBelow_subset_descendants c hxc)
      have hE₂internal :
          E₂.packing.toPathPacking.InternallyDisjointFromSet
            (T.cluster x) := by
        intro i z hz hzCluster
        exact False.elim
          (Finset.disjoint_left.mp hRegions
            (hxRegion hzCluster) (E₂.packing_staysIn i hz))
      exact PerfectPathPacking.disjointUnion_internallyDisjointFromSet
        E₁.packing E₂.packing D.incoming_disjoint hUdisj hChildNode
        (E₁.packing_internallyDisjoint_leafCluster x hxc)
        hE₂internal
    · have hxRegion :
          T.cluster x ⊆ S.subtreeRegion d :=
        S.cluster_subset_subtreeRegion_of_mem
          (S.selectedBelow_subset_descendants d hxd)
      have hE₁internal :
          E₁.packing.toPathPacking.InternallyDisjointFromSet
            (T.cluster x) := by
        intro i z hz hzCluster
        exact False.elim
          (Finset.disjoint_left.mp hRegions
            (E₁.packing_staysIn i hz) (hxRegion hzCluster))
      exact PerfectPathPacking.disjointUnion_internallyDisjointFromSet
        E₁.packing E₂.packing D.incoming_disjoint hUdisj hChildNode
        hE₁internal
        (E₂.packing_internallyDisjoint_leafCluster x hxd)
  have hPinternalLeaf :
      ∀ x, x ∈ S.selectedBelow v →
        P.toPathPacking.InternallyDisjointFromSet (T.cluster x) := by
    intro x hx i z hz hzCluster
    have hx' : x ∈ S.selectedBelow c ∨ x ∈ S.selectedBelow d := by
      simpa [hbelow] using hx
    have hxRegion :
        T.cluster x ⊆
          (S.subtreeRegion c ∪ S.subtreeRegion d) := by
      rcases hx' with hxc | hxd
      · intro y hy
        exact Finset.mem_union_left _
          (S.cluster_subset_subtreeRegion_of_mem
            (S.selectedBelow_subset_descendants c hxc) hy)
      · intro y hy
        exact Finset.mem_union_right _
          (S.cluster_subset_subtreeRegion_of_mem
            (S.selectedBelow_subset_descendants d hxd) hy)
    have hsplit :=
      D.transition
        |>.concatOfFirstInternallyDisjointSecondStaysIn_path_vertexSet_subset
          Q hDinternal hQstay hAdisj i hz
    let j := D.transition.indexOfSourceTarget Q i
    have hmatch :
        (Q.path j).source = (D.transition.path i).target :=
      D.transition.source_indexOfSourceTarget Q i
    have hfullTarget :
        (Q.path j).target = (P.path i).target := rfl
    have hglue_eq_fullTarget
        (hzGlue : z = (D.transition.path i).target) :
        z = (P.path i).target := by
      have hzQsource : z = (Q.path j).source := by
        calc
          z = (D.transition.path i).target := hzGlue
          _ = (Q.path j).source := hmatch.symm
      rcases hx' with hxc | hxd
      · by_cases hxcEq : x = c
        · subst x
          have hcleaf : c ∈ S.leaves :=
            S.selectedBelow_subset_leaves c hxc
          cases hj : j with
          | inl a =>
              have htriv :=
                E₁.packing_trivial_of_root_selected hcleaf a
              have hzQa : z = (E₁.packing.path a).source := by
                simpa [Q, PerfectPathPacking.disjointUnion, hj] using hzQsource
              calc
                z = (E₁.packing.path a).source := hzQa
                _ = (E₁.packing.path a).target := htriv
                _ = (P.path i).target := by
                  simpa [Q, PerfectPathPacking.disjointUnion, hj] using
                    hfullTarget
          | inr b =>
              have hzQb : z = (E₂.packing.path b).source := by
                simpa [Q, PerfectPathPacking.disjointUnion, hj] using hzQsource
              have hzD : z ∈ T.cluster d := by
                apply D.rightIncoming_subset.trans
                  (T.interface_subset_cluster d v hvd.symm)
                have hb := E₂.packing.source_mem b
                simpa [hzQb] using hb
              exact False.elim
                (Finset.disjoint_left.mp (T.cluster_disjoint hcd)
                  hzCluster hzD)
        · have hzChild :
              z ∈ T.cluster c ∨ z ∈ T.cluster d := by
            have hzi := D.transition.target_mem i
            rcases Finset.mem_union.mp hzi with hi | hi
            · exact Or.inl
                (D.leftIncoming_subset.trans
                  (T.interface_subset_cluster c v hvc.symm)
                  (by simpa [hzGlue] using hi))
            · exact Or.inr
                (D.rightIncoming_subset.trans
                  (T.interface_subset_cluster d v hvd.symm)
                  (by simpa [hzGlue] using hi))
          rcases hzChild with hzC | hzD
          · exact False.elim
              (Finset.disjoint_left.mp (T.cluster_disjoint hxcEq)
                hzCluster hzC)
          · exact False.elim
              (Finset.disjoint_left.mp hRegions
                (S.cluster_subset_subtreeRegion_of_mem
                  (S.selectedBelow_subset_descendants c hxc) hzCluster)
                (S.cluster_subset_subtreeRegion d hzD))
      · by_cases hxdEq : x = d
        · subst x
          have hdleaf : d ∈ S.leaves :=
            S.selectedBelow_subset_leaves d hxd
          cases hj : j with
          | inl a =>
              have hzQa : z = (E₁.packing.path a).source := by
                simpa [Q, PerfectPathPacking.disjointUnion, hj] using hzQsource
              have hzC : z ∈ T.cluster c := by
                apply D.leftIncoming_subset.trans
                  (T.interface_subset_cluster c v hvc.symm)
                have ha := E₁.packing.source_mem a
                simpa [hzQa] using ha
              exact False.elim
                (Finset.disjoint_left.mp (T.cluster_disjoint hcd.symm)
                  hzCluster hzC)
          | inr b =>
              have htriv :=
                E₂.packing_trivial_of_root_selected hdleaf b
              have hzQb : z = (E₂.packing.path b).source := by
                simpa [Q, PerfectPathPacking.disjointUnion, hj] using hzQsource
              calc
                z = (E₂.packing.path b).source := hzQb
                _ = (E₂.packing.path b).target := htriv
                _ = (P.path i).target := by
                  simpa [Q, PerfectPathPacking.disjointUnion, hj] using
                    hfullTarget
        · have hzChild :
              z ∈ T.cluster c ∨ z ∈ T.cluster d := by
            have hzi := D.transition.target_mem i
            rcases Finset.mem_union.mp hzi with hi | hi
            · exact Or.inl
                (D.leftIncoming_subset.trans
                  (T.interface_subset_cluster c v hvc.symm)
                  (by simpa [hzGlue] using hi))
            · exact Or.inr
                (D.rightIncoming_subset.trans
                  (T.interface_subset_cluster d v hvd.symm)
                  (by simpa [hzGlue] using hi))
          rcases hzChild with hzC | hzD
          · exact False.elim
              (Finset.disjoint_left.mp hRegions
                (S.cluster_subset_subtreeRegion c hzC)
                (S.cluster_subset_subtreeRegion_of_mem
                  (S.selectedBelow_subset_descendants d hxd) hzCluster))
          · exact False.elim
              (Finset.disjoint_left.mp (T.cluster_disjoint hxdEq)
                hzCluster hzD)
    rcases Finset.mem_union.mp hsplit with hzD | hzQ
    · rcases hDinternal i hzD (hxRegion hzCluster) with hsource | htarget
      · exact Or.inl (by simpa [P] using hsource)
      · exact Or.inr (hglue_eq_fullTarget htarget)
    · rcases hQinternalLeaf x hx j hzQ hzCluster with hsource | htarget
      · exact Or.inr
          (hglue_eq_fullTarget (by
            calc
              z = (Q.path j).source := hsource
              _ = (D.transition.path i).target := hmatch))
      · exact Or.inr (by simpa [P, j] using htarget)
  let target : Fin m → Finset V := fun x =>
    if x ∈ S.selectedBelow c then E₁.leafTarget x else E₂.leafTarget x
  have htargetUnion :
      (S.selectedBelow v).biUnion target = U₁ ∪ U₂ := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_biUnion.mp hz with ⟨x, hxv, hzx⟩
      have hx : x ∈ S.selectedBelow c ∨ x ∈ S.selectedBelow d := by
        simpa [hbelow] using hxv
      rcases hx with hxc | hxd
      · exact Finset.mem_union_left _
          (Finset.mem_biUnion.mpr
            ⟨x, hxc, by simpa [target, hxc] using hzx⟩)
      · have hxnc : x ∉ S.selectedBelow c := by
          intro hxc
          exact Finset.disjoint_left.mp hSelectedDisj hxc hxd
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr
            ⟨x, hxd, by simpa [target, hxnc] using hzx⟩)
    · intro hz
      rcases Finset.mem_union.mp hz with hz₁ | hz₂
      · rcases Finset.mem_biUnion.mp hz₁ with ⟨x, hxc, hzx⟩
        exact Finset.mem_biUnion.mpr
          ⟨x, by simpa [hbelow, hxc],
            by simpa [target, hxc] using hzx⟩
      · rcases Finset.mem_biUnion.mp hz₂ with ⟨x, hxd, hzx⟩
        have hxnc : x ∉ S.selectedBelow c := by
          intro hxc
          exact Finset.disjoint_left.mp hSelectedDisj hxc hxd
        exact Finset.mem_biUnion.mpr
          ⟨x, by simpa [hbelow, hxd],
            by simpa [target, hxnc] using hzx⟩
  let P' :
      PerfectPathPacking G A
        ((S.selectedBelow v).biUnion target) :=
    P.copyTerminals rfl htargetUnion.symm
  exact ⟨{
    leafTarget := target
    leafTarget_empty := by
      intro x hx
      have hxnc : x ∉ S.selectedBelow c := by
        intro hxc
        exact hx (by simpa [hbelow, hxc])
      have hxnd : x ∉ S.selectedBelow d := by
        intro hxd
        exact hx (by simpa [hbelow, hxd])
      simp [target, hxnc, E₂.leafTarget_empty x hxnd]
    leafTarget_subset := by
      intro x hx
      have hx' : x ∈ S.selectedBelow c ∨ x ∈ S.selectedBelow d := by
        simpa [hbelow] using hx
      rcases hx' with hxc | hxd
      · simpa [target, hxc] using E₁.leafTarget_subset x hxc
      · have hxnc : x ∉ S.selectedBelow c := by
          intro hxc
          exact Finset.disjoint_left.mp hSelectedDisj hxc hxd
        simpa [target, hxnc] using E₂.leafTarget_subset x hxd
    leafTarget_card := by
      intro x hx
      have hx' : x ∈ S.selectedBelow c ∨ x ∈ S.selectedBelow d := by
        simpa [hbelow] using hx
      rcases hx' with hxc | hxd
      · simpa [target, hxc] using E₁.leafTarget_card x hxc
      · have hxnc : x ∉ S.selectedBelow c := by
          intro hxc
          exact Finset.disjoint_left.mp hSelectedDisj hxc hxd
        simpa [target, hxnc] using E₂.leafTarget_card x hxd
    leafTarget_nodeWellLinked := by
      intro x hx
      have hx' : x ∈ S.selectedBelow c ∨ x ∈ S.selectedBelow d := by
        simpa [hbelow] using hx
      rcases hx' with hxc | hxd
      · simpa [target, hxc] using
          E₁.leafTarget_nodeWellLinked x hxc
      · have hxnc : x ∉ S.selectedBelow c := by
          intro hxc
          exact Finset.disjoint_left.mp hSelectedDisj hxc hxd
        simpa [target, hxnc] using
          E₂.leafTarget_nodeWellLinked x hxd
    packing := P'
    packing_staysIn :=
      P.copyTerminals_staysIn rfl htargetUnion.symm hPstay
    packing_internallyDisjoint_leafCluster := by
      intro x hx
      simpa [P'] using hPinternalLeaf x hx
    packing_trivial_of_root_selected := by
      intro hv
      have hdeg := S.leaves_leaf v hv
      have hchildren : c = d := hdeg.one_adj_eq hvc hvd
      exact False.elim (D.children_ne hchildren) }⟩

/-- The full recursive top-down construction below a nonroot active
meta-vertex.  Strong induction is on the cardinality of its descendant
subtree; each recursive call is made at an immediate child. -/
theorem exists_theorem47_subtreeRoutingData
    (S : Theorem46LeafExtractionSetup T ell)
    {q : ℕ} (hq : ell * q ≤ W)
    {v : Fin m} (hvroot : v ≠ S.root)
    (hactive : (S.selectedBelow v).Nonempty)
    {A : Finset V}
    (hA :
      A ⊆ T.interface v (parent T.meta_isTree S.root v)
        (parent_adj T.meta_isTree S.root hvroot).symm)
    (hAcard : A.card = (S.selectedBelow v).card * q) :
    Nonempty (Theorem47SubtreeRoutingData S v A q) := by
  classical
  induction hn : (descendants T.meta_isTree S.root v).card
      using Nat.strong_induction_on generalizing v A with
  | h n ih =>
      subst hn
      by_cases hvleaf : v ∈ S.leaves
      · exact exists_theorem47_leafSubtreeRoutingData S hvleaf
          (hA.trans (T.interface_subset_cluster
            v (parent T.meta_isTree S.root v)
            (parent_adj T.meta_isTree S.root hvroot).symm))
          (NodeWellLinkedIn.mono_terminals
            (T.interface_nodeWellLinked
              v (parent T.meta_isTree S.root v)
              (parent_adj T.meta_isTree S.root hvroot).symm)
            hA)
          (by
            rw [S.selectedBelow_eq_singleton_of_mem_leaves hvleaf] at hAcard
            simpa using hAcard)
      · have hbelowActive :
          S.selectedBelow v =
            (S.activeChildren v).biUnion S.selectedBelow :=
          S.selectedBelow_eq_biUnion_activeChildren hvleaf
        have hactiveChildren : (S.activeChildren v).Nonempty := by
          rcases hactive with ⟨x, hx⟩
          rw [hbelowActive] at hx
          rcases Finset.mem_biUnion.mp hx with ⟨c, hc, _⟩
          exact ⟨c, hc⟩
        have hactiveCardPos : 0 < (S.activeChildren v).card :=
          hactiveChildren.card_pos
        have hactiveCardLe : (S.activeChildren v).card ≤ 2 :=
          S.activeChildren_card_le_two hvroot
        have hAle : A.card ≤ W := by
          have hbelowCard :
              (S.selectedBelow v).card ≤ ell := by
            have :=
              Finset.card_le_card (S.selectedBelow_subset_leaves v)
            simpa [S.leaves_card] using this
          calc
            A.card = (S.selectedBelow v).card * q := hAcard
            _ ≤ ell * q := Nat.mul_le_mul_right q hbelowCard
            _ ≤ W := hq
        by_cases hcardOne : (S.activeChildren v).card = 1
        · rcases Finset.card_eq_one.mp hcardOne with ⟨c, hcEq⟩
          have hcActive : c ∈ S.activeChildren v := by simp [hcEq]
          have hcMem :
              c ∈ children T.meta_isTree S.root v :=
            (S.mem_activeChildren v c).1 hcActive |>.1
          have hc :
              IsChild T.meta_isTree S.root v c :=
            (mem_children T.meta_isTree S.root v c).1 hcMem
          have hcBelow : (S.selectedBelow c).Nonempty :=
            (S.mem_activeChildren v c).1 hcActive |>.2
          have hbelow : S.selectedBelow v = S.selectedBelow c := by
            rw [hbelowActive, hcEq]
            simp
          have hpc :
              parent T.meta_isTree S.root v ≠ c := by
            intro h
            subst c
            exact S.parent_not_mem_children hvroot hcMem
          let hpv :=
            (parent_adj T.meta_isTree S.root hvroot).symm
          let hvc := S.adj_child hc
          let D :=
            Classical.choice
              (exists_theorem47_oneChildTransitionData
                (T := T) hpv hvc hpc hA hAle)
          have hDescSubset :
              descendants T.meta_isTree S.root c ⊆
                descendants T.meta_isTree S.root v := by
            intro x hx
            exact S.mem_descendants_of_childSubtree hc hx
          have hvNotChild :
              v ∉ descendants T.meta_isTree S.root c := by
            simpa [childSubtree] using
              parent_not_mem_childSubtree T.meta_isTree S.root
                S.parentDistanceDecreases hc
          have hDescStrict :
              descendants T.meta_isTree S.root c ⊂
                descendants T.meta_isTree S.root v := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨hDescSubset, ?_⟩
            intro heq
            exact hvNotChild (by
              rw [heq]
              exact self_mem_descendants T.meta_isTree S.root v)
          have hDescCard :
              (descendants T.meta_isTree S.root c).card <
                (descendants T.meta_isTree S.root v).card :=
            Finset.card_lt_card hDescStrict
          have hDcanonical :
              D.childIncoming ⊆
                T.interface c (parent T.meta_isTree S.root c)
                  (parent_adj T.meta_isTree S.root hc.1).symm := by
            simpa [hc.2, hvc] using D.childIncoming_subset
          have hDcard :
              D.childIncoming.card =
                (S.selectedBelow c).card * q := by
            rw [D.childIncoming_card, hAcard, hbelow]
          let E :=
            Classical.choice
              (ih _ hDescCard hc.1 hcBelow hDcanonical hDcard rfl)
          exact D.composeSubtreeRouting S hc hbelow hvleaf
            (hA.trans (T.interface_subset_cluster
              v (parent T.meta_isTree S.root v)
              (parent_adj T.meta_isTree S.root hvroot).symm)) E
        · have hcardTwo : (S.activeChildren v).card = 2 := by
            omega
          rcases Finset.card_eq_two.mp hcardTwo with
            ⟨c, d, hcd, hchildrenEq⟩
          have hcActive : c ∈ S.activeChildren v := by
            simp [hchildrenEq]
          have hdActive : d ∈ S.activeChildren v := by
            simp [hchildrenEq]
          have hcMem :
              c ∈ children T.meta_isTree S.root v :=
            (S.mem_activeChildren v c).1 hcActive |>.1
          have hdMem :
              d ∈ children T.meta_isTree S.root v :=
            (S.mem_activeChildren v d).1 hdActive |>.1
          have hc :
              IsChild T.meta_isTree S.root v c :=
            (mem_children T.meta_isTree S.root v c).1 hcMem
          have hd :
              IsChild T.meta_isTree S.root v d :=
            (mem_children T.meta_isTree S.root v d).1 hdMem
          have hcBelow : (S.selectedBelow c).Nonempty :=
            (S.mem_activeChildren v c).1 hcActive |>.2
          have hdBelow : (S.selectedBelow d).Nonempty :=
            (S.mem_activeChildren v d).1 hdActive |>.2
          have hbelow :
              S.selectedBelow v =
                S.selectedBelow c ∪ S.selectedBelow d := by
            rw [hbelowActive, hchildrenEq]
            simp [Finset.union_comm]
          have hpNeC :
              parent T.meta_isTree S.root v ≠ c := by
            intro h
            subst c
            exact S.parent_not_mem_children hvroot hcMem
          have hpNeD :
              parent T.meta_isTree S.root v ≠ d := by
            intro h
            subst d
            exact S.parent_not_mem_children hvroot hdMem
          let k₁ := (S.selectedBelow c).card * q
          let k₂ := (S.selectedBelow d).card * q
          have hQuota :
              A.card = k₁ + k₂ := by
            rw [hAcard, hbelow,
              Finset.card_union_of_disjoint
                (S.selectedBelow_children_disjoint hcMem hdMem hcd)]
            simp [k₁, k₂, Nat.add_mul]
          let hpv :=
            (parent_adj T.meta_isTree S.root hvroot).symm
          let hvc := S.adj_child hc
          let hvd := S.adj_child hd
          let D :=
            Classical.choice
              (exists_theorem47_twoChildTransitionData
                (T := T) hpv hvc hvd hpNeC hpNeD hcd hA hQuota hAle)
          have childCardLt :
              ∀ {x : Fin m},
                IsChild T.meta_isTree S.root v x →
                (descendants T.meta_isTree S.root x).card <
                  (descendants T.meta_isTree S.root v).card := by
            intro x hx
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨?_, ?_⟩
            · intro y hy
              exact S.mem_descendants_of_childSubtree hx hy
            · intro heq
              have hvNot :
                  v ∉ descendants T.meta_isTree S.root x := by
                simpa [childSubtree] using
                  parent_not_mem_childSubtree T.meta_isTree S.root
                    S.parentDistanceDecreases hx
              exact hvNot (by
                rw [heq]
                exact self_mem_descendants T.meta_isTree S.root v)
          have hLeftCanonical :
              D.leftIncoming ⊆
                T.interface c (parent T.meta_isTree S.root c)
                  (parent_adj T.meta_isTree S.root hc.1).symm := by
            simpa [hc.2, hvc] using D.leftIncoming_subset
          have hRightCanonical :
              D.rightIncoming ⊆
                T.interface d (parent T.meta_isTree S.root d)
                  (parent_adj T.meta_isTree S.root hd.1).symm := by
            simpa [hd.2, hvd] using D.rightIncoming_subset
          have hLeftCard :
              D.leftIncoming.card =
                (S.selectedBelow c).card * q := by
            simpa [k₁] using D.leftIncoming_card
          have hRightCard :
              D.rightIncoming.card =
                (S.selectedBelow d).card * q := by
            simpa [k₂] using D.rightIncoming_card
          let E₁ :=
            Classical.choice
              (ih _ (childCardLt hc) hc.1 hcBelow
                hLeftCanonical hLeftCard rfl)
          let E₂ :=
            Classical.choice
              (ih _ (childCardLt hd) hd.1 hdBelow
                hRightCanonical hRightCard rfl)
          exact D.composeSubtreeRouting S hc hd hcd hbelow
            (hA.trans (T.interface_subset_cluster
              v (parent T.meta_isTree S.root v)
              (parent_adj T.meta_isTree S.root hvroot).symm))
            E₁ E₂

/-- Chekuri--Chuzhoy Theorem 4.7.  The resulting single perfect packing is
partitioned into `W / ell` target terminals at every selected leaf.  Since a
`PerfectPathPacking` is node-disjoint by construction, this is the paper's
global family `⋃ Q_S`, not merely a collection of independently chosen local
routes. -/
theorem exists_theorem47_routingData
    (S : Theorem46LeafExtractionSetup T ell)
    (hell : 0 < ell) :
    ∃ A : Finset V,
      A ⊆ T.interface S.root S.child S.root_child_adj ∧
      Nonempty
        (Theorem47SubtreeRoutingData S S.root A (W / ell)) := by
  classical
  let q := W / ell
  have hquota : ell * q ≤ W := by
    dsimp [q]
    exact Nat.mul_div_le W ell
  have hAcardLe :
      ell * q ≤
        (T.interface S.root S.child S.root_child_adj).card := by
    simpa [T.interface_card S.root S.child S.root_child_adj] using hquota
  rcases Finset.exists_subset_card_eq hAcardLe with
    ⟨A, hA, hAcard⟩
  let C := T.connector S.root S.child S.root_child_adj
  let R := C.restrictSourceSet A hA
  let B := C.targetSet (C.sourceIndexSetOfSubset A)
  have hBsub :
      B ⊆ T.interface S.child S.root S.root_child_adj.symm :=
    C.targetSet_subset_right _
  have hBcard : B.card = ell * q := by
    calc
      B.card = R.card := R.card_eq_right_card.symm
      _ = A.card := by simp [R]
      _ = ell * q := hAcard
  have hc :
      IsChild T.meta_isTree S.root S.root S.child := by
    exact (mem_children T.meta_isTree S.root S.root S.child).1
      (by simp [S.children_root_eq_singleton])
  have hBcanonical :
      B ⊆
        T.interface S.child
          (parent T.meta_isTree S.root S.child)
          (parent_adj T.meta_isTree S.root hc.1).symm := by
    simpa [hc.2] using hBsub
  have hchildActive :
      (S.selectedBelow S.child).Nonempty := by
    rw [S.selectedBelow_child_eq_leaves]
    exact Finset.card_pos.mp (by simpa [S.leaves_card] using hell)
  have hBcardCanonical :
      B.card = (S.selectedBelow S.child).card * q := by
    simpa [S.selectedBelow_child_card] using hBcard
  let E :=
    Classical.choice
      (exists_theorem47_subtreeRoutingData S hquota
        hc.1 hchildActive hBcanonical hBcardCanonical)
  let D :
      Theorem47OneChildTransitionData T
        S.root_child_adj S.root_child_adj A := {
    childIncoming := B
    childIncoming_subset := hBsub
    childIncoming_card := by
      calc
        B.card = A.card := by
          rw [hBcard, hAcard]
        _ = A.card := rfl
    transition := R
    transition_card := by simp [R]
    transition_staysIn := by
      intro i x hx
      exact Finset.mem_union_right _
        (C.restrictSourceSet_staysIn_vertexSet A hA i hx)
    transition_internallyDisjoint_child :=
      C.restrictSourceSet_internallyDisjointFromSet A hA
        (T.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj S.child) }
  have hbelow :
      S.selectedBelow S.root = S.selectedBelow S.child := by
    rw [S.selectedBelow_root_eq_leaves, S.selectedBelow_child_eq_leaves]
  have hAcluster :
      A ⊆ T.cluster S.root :=
    hA.trans
      (T.interface_subset_cluster
        S.root S.child S.root_child_adj)
  exact ⟨A, hA,
    D.composeSubtreeRouting S hc hbelow S.root_not_mem_leaves hAcluster E⟩

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
