import Lax17Proofs.Source.TreeOfSets
import Lax17Proofs.Source.TreewidthContract
import Lax17Proofs.Source.ChekuriChuzhoyTheorem215
import Lax17Proofs.Source.ChekuriChuzhoyMetaTreeDichotomy
import Lax17Proofs.Source.ChekuriChuzhoySection5CoreAssembly
import Lax17Proofs.Source.ChekuriChuzhoySection5Arithmetic
import Lax17Proofs.Source.ChekuriChuzhoyTheorem46Defs
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.Nat.Log

namespace Lax17Proofs

universe u v w


/-!
# Chekuri--Chuzhoy Theorem 3.5, source-route decomposition

Theorem 3.5 of Chekuri--Chuzhoy (JACM 2016) says that sufficiently large
treewidth forces a strong path-of-sets system of prescribed length and width.
The proof goes through the Section 4 tree-of-sets construction.  This file
records the formally useful intermediate target and proves the final
path-of-sets statement from that target using `TreeOfSets.lean`.

No axiom is introduced here.  The remaining mathematical obligation for this
route is to prove `StrongTreeOfSetsWithBufferedPathFromTreewidth`, by
formalizing Theorem 2.21, Theorem 4.3, Lemma 4.5, and the non-buffered part of
Theorem 4.6.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical


/-- Chekuri--Chuzhoy Theorem 2.21, in the threshold form used in the proof of
Theorem 3.5.

The statement says that a graph of treewidth at least `k` contains a same-vertex
subgraph of polylogarithmic maximum degree and a node-well-linked terminal set
of any requested size `x` below `k / polylog k`. -/
def NodeWellLinkedCoreFromTreewidth
    (cCore cCoreLog cDeg cDegLog : ℕ) : Prop :=
  0 < cCore ∧ 0 < cCoreLog ∧ 0 < cDeg ∧ 0 < cDegLog ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {k x : ℕ},
        1 < k →
          0 < x →
            k ≤ treewidth G →
              cCore * x * (Nat.log 2 k) ^ cCoreLog < k →
                ∃ H : _root_.SimpleGraph V,
                  H ≤ G ∧
                    MaxDegreeAtMost H (cDeg * (Nat.log 2 k) ^ cDegLog) ∧
                      ∃ X : Finset V,
                        X.card = x ∧ NodeWellLinkedIn H Finset.univ X

/-- The Section 4 construction route, after Theorem 4.3 and Lemma 4.5 have
produced a strong tree-of-sets system and Theorem 4.6 has supplied either a
long meta-path or the DFS-tour path-of-sets extraction.

This is deliberately stated over a graph already containing a node-well-linked
terminal set; the proof of Theorem 3.5 uses `NodeWellLinkedCoreFromTreewidth`
to obtain that graph from treewidth. -/
def StrongTreeOfSetsFromNodeWellLinkedCore
    (cRoute cRouteLog cDeltaPow : ℕ) : Prop :=
  0 < cRoute ∧ 0 < cRouteLog ∧ 0 < cDeltaPow ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {ell w x Δ : ℕ}
      (X : Finset V),
        1 < ell →
          1 < w →
            1 < x →
              MaxDegreeAtMost G Δ →
                X.card = x →
                  NodeWellLinkedIn G Finset.univ X →
                    cRoute * w * ell ^ 50 * Δ ^ cDeltaPow *
                        (Nat.log 2 x) ^ cRouteLog < x →
                      ∃ m : ℕ, ∃ T : StrongTreeOfSetsSystem G m w,
                        T.HasBufferedMetaPath ell

/-- Faithful Section 4 route from the node-well-linked core to the final strong
path-of-sets system.

This is the direct conclusion of the proof of Chekuri--Chuzhoy Theorem 3.5
after Theorem 4.3, Lemma 4.5, and Theorem 4.6.  Unlike
`StrongTreeOfSetsFromNodeWellLinkedCore`, it does not restrict Theorem 4.6 to
the long/buffered meta-path branch; the DFS/many-leaves branch is allowed to
produce the strong path-of-sets system directly. -/
def StrongPathOfSetsFromNodeWellLinkedCore
    (cRoute cRouteLog cDeltaPow : ℕ) : Prop :=
  0 < cRoute ∧ 0 < cRouteLog ∧ 0 < cDeltaPow ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {ell w x Δ : ℕ}
      (X : Finset V),
        1 < ell →
          1 < w →
            1 < x →
              MaxDegreeAtMost G Δ →
                X.card = x →
                  NodeWellLinkedIn G Finset.univ X →
                    cRoute * w * ell ^ 50 * Δ ^ cDeltaPow *
                        (Nat.log 2 x) ^ cRouteLog < x →
                      Nonempty (StrongPathOfSetsSystem G ell w)

/-- Chekuri--Chuzhoy Section 4.3--4.5, after the tree-of-sets construction and
strongification steps have been combined.

The input is a graph with a node-well-linked terminal set of size `x` and
maximum degree `Δ`.  Under the Section 4 threshold it returns a strong
tree-of-sets system with a prescribed number `m` of meta-tree vertices and
interface width `W`.  This keeps the construction of the strong tree separate
from Theorem 4.6, which extracts a strong path-of-sets system from it. -/
def StrongTreeOfSetsCoreFromNodeWellLinkedCore
    (cBuild cBuildLog cDeltaPow : ℕ) : Prop :=
  0 < cBuild ∧ 0 < cBuildLog ∧ 0 < cDeltaPow ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {m W x Δ : ℕ}
      (X : Finset V),
        1 < m →
          1 < W →
            1 < x →
              MaxDegreeAtMost G Δ →
                X.card = x →
                  NodeWellLinkedIn G Finset.univ X →
                    cBuild * W * m ^ 24 * Δ ^ cDeltaPow *
                        (Nat.log 2 x) ^ cBuildLog < x →
                      Nonempty (StrongTreeOfSetsSystem G m W)

/-- The source-specific form of the exponent-24 threshold used by the direct
Section 5 construction. -/
def StrongTreeOfSetsCoreFromNodeWellLinkedCore24
    (cBuild cBuildLog cDeltaPow : ℕ) : Prop :=
  0 < cBuild ∧ 0 < cBuildLog ∧ 0 < cDeltaPow ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {m W x Δ : ℕ}
      (X : Finset V),
        1 < m →
          1 < W →
            1 < x →
              MaxDegreeAtMost G Δ →
                X.card = x →
                  NodeWellLinkedIn G Finset.univ X →
                    ChekuriChuzhoySection5Arithmetic.buildConstant24 * W *
                        m ^ 24 * Δ ^ 10 * (Nat.log 2 x) ^ 5 < x →
                      Nonempty (StrongTreeOfSetsSystem G m W)

/-- Proof-producing WP1C endpoint at exponent 24. -/
theorem strongTreeOfSetsCoreFromNodeWellLinkedCore24_proved :
    StrongTreeOfSetsCoreFromNodeWellLinkedCore24.{u}
      ChekuriChuzhoySection5Arithmetic.buildConstant24 5 10 := by
  refine ⟨by
      simp [ChekuriChuzhoySection5Arithmetic.buildConstant24],
    by decide, by decide, ?_⟩
  intro V _ _ G m W x Δ X hm hW hx hdegree hXcard hXwell hlarge
  exact
    ChekuriChuzhoySection5Arithmetic.exists_strongTreeOfSetsSystem_of_m24_threshold
      G X (by omega) (by omega) (by omega) hdegree hXcard hXwell hlarge

/-- Existential form consumed by package-level composition code. -/
theorem exists_strongTreeOfSetsCoreFromNodeWellLinkedCore24 :
    ∃ cBuild cBuildLog cDeltaPow : ℕ,
      StrongTreeOfSetsCoreFromNodeWellLinkedCore24.{u}
        cBuild cBuildLog cDeltaPow :=
  ⟨ChekuriChuzhoySection5Arithmetic.buildConstant24, 5, 10,
    strongTreeOfSetsCoreFromNodeWellLinkedCore24_proved⟩

/-- WP1C in the parameterized Section 4 interface.  After accepting the
source construction with an `m^24` loss, Theorem 4.6 contributes the
corresponding `ell^50` threshold downstream. -/
theorem strongTreeOfSetsCoreFromNodeWellLinkedCore_proved :
    StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
      ChekuriChuzhoySection5Arithmetic.buildConstant24 5 10 := by
  simpa [StrongTreeOfSetsCoreFromNodeWellLinkedCore,
    StrongTreeOfSetsCoreFromNodeWellLinkedCore24] using
    strongTreeOfSetsCoreFromNodeWellLinkedCore24_proved

theorem exists_strongTreeOfSetsCoreFromNodeWellLinkedCore_proved :
    ∃ cBuild cBuildLog cDeltaPow : ℕ,
      StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
        cBuild cBuildLog cDeltaPow :=
  ⟨ChekuriChuzhoySection5Arithmetic.buildConstant24, 5, 10,
    strongTreeOfSetsCoreFromNodeWellLinkedCore_proved⟩

/-- Chekuri--Chuzhoy Theorem 4.6, as a standalone extraction interface.

Given a strong tree-of-sets system with at least `ell^2` clusters and width
larger than `16 * w * ell^2 + 1`, it extracts a strong path-of-sets system of
length `ell` and width `w`.  The buffered-meta-path branch of this theorem is
proved in `TreeOfSets.lean`; this interface also covers the DFS/many-leaves
branch from the paper. -/
def StrongPathOfSetsFromStrongTreeOfSets : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell w : ℕ}
    (_T : StrongTreeOfSetsSystem G m W),
      1 < ell →
        1 < w →
          ell ^ 2 ≤ m →
            16 * w * ell ^ 2 + 1 < W →
              Nonempty (StrongPathOfSetsSystem G ell w)

/-- The pure meta-tree dichotomy used at the start of Chekuri--Chuzhoy
Theorem 4.6: a sufficiently large bounded-degree meta-tree either contains the
buffered path needed by the direct conversion, or it has enough leaves for the
DFS construction. -/
def StrongTreeMetaDichotomy : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell : ℕ}
    (T : StrongTreeOfSetsSystem G m W),
      1 < ell →
        ell ^ 2 ≤ m →
          T.HasBufferedMetaPath ell ∨ T.HasMetaLeavesAtLeast (ell + 1)

/-- Self-contained proof of the meta-tree dichotomy used in
Chekuri--Chuzhoy Theorem 4.6.

The proof is purely graph-theoretic: a finite tree on at least `ell^2`
vertices either contains the buffered simple path of `ell + 1` edges, or,
after rooting at a leaf, the longest-rooted-path injection forces at least
`ell + 1` leaves. -/
theorem strongTreeMetaDichotomy : StrongTreeMetaDichotomy.{u} := by
  intro V _ _ G m W ell T hell hm
  classical
  letI := Classical.decRel T.metaTree.Adj
  have hcard : ell ^ 2 ≤ Fintype.card (Fin m) := by
    simpa using hm
  rcases exists_bufferedPath_or_manyLeaves_of_tree
      (G := T.metaTree) T.meta_isTree hell hcard with hpath | hleaves
  · exact Or.inl hpath
  · rcases hleaves with ⟨leaves, hleaf, hcard, _hshort⟩
    exact Or.inr ⟨leaves, hleaf, hcard⟩

/-- The first finite-tree setup step in the many-leaves branch of
Chekuri--Chuzhoy Theorem 4.6.

From `ell + 1` meta-tree leaves, choose `ell` leaves that will be the final
clusters and a separate leaf to serve as the DFS root. -/
theorem exists_metaLeaf_root_and_selectedLeaves
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    (hleaves : T.HasMetaLeavesAtLeast (ell + 1)) :
    ∃ root : Fin m, ∃ L : Finset (Fin m),
      DegreeEquals T.metaTree root 1 ∧
        root ∉ L ∧ L.card = ell ∧
          ∀ i ∈ L, DegreeEquals T.metaTree i 1 := by
  classical
  rcases hleaves with ⟨leaves, hleaves_iff, hcard⟩
  have hleaves_nonempty : leaves.Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos ell) hcard)
  rcases hleaves_nonempty with ⟨root, hroot_mem⟩
  have hroot_leaf : DegreeEquals T.metaTree root 1 :=
    (hleaves_iff root).1 hroot_mem
  have hell_le_erase : ell ≤ (leaves.erase root).card := by
    rw [Finset.card_erase_of_mem hroot_mem]
    omega
  rcases Finset.exists_subset_card_eq hell_le_erase with ⟨L, hLsub, hLcard⟩
  refine ⟨root, L, hroot_leaf, ?_, hLcard, ?_⟩
  · intro hrootL
    exact (Finset.mem_erase.mp (hLsub hrootL)).1 rfl
  · intro i hiL
    have hiLeaves : i ∈ leaves := Finset.mem_of_mem_erase (hLsub hiL)
    exact (hleaves_iff i).1 hiLeaves

/-- Root-selection form with the unique child of the DFS root exposed.

This is the data used to start Step 1 of the many-leaves proof of
Chekuri--Chuzhoy Theorem 4.6: a root leaf outside the selected leaf clusters,
its unique adjacent meta-tree vertex, and the selected leaf set. -/
theorem exists_metaLeaf_root_child_and_selectedLeaves
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    (hleaves : T.HasMetaLeavesAtLeast (ell + 1)) :
    ∃ root child : Fin m, ∃ L : Finset (Fin m),
      DegreeEquals T.metaTree root 1 ∧
        T.metaTree.Adj root child ∧
          (∀ z : Fin m, T.metaTree.Adj root z → z = child) ∧
            root ∉ L ∧ L.card = ell ∧
              ∀ i ∈ L, DegreeEquals T.metaTree i 1 := by
  rcases exists_metaLeaf_root_and_selectedLeaves T hleaves with
    ⟨root, L, hroot_leaf, hroot_not_L, hLcard, hLleaf⟩
  rcases DegreeEquals.one_exists_unique_adj hroot_leaf with
    ⟨child, hroot_child, hchild_unique⟩
  exact ⟨root, child, L, hroot_leaf, hroot_child, hchild_unique,
    hroot_not_L, hLcard, hLleaf⟩

/-- The selected leaves below a meta-vertex in the rooted meta-tree, using the
paper's notation `n(S)`.

A selected leaf is counted below `v` when some simple path from the DFS root to
that leaf passes through `v`.  In a tree this path is unique; the existential
form avoids carrying uniqueness through the bookkeeping lemmas. -/
noncomputable def selectedMetaLeafDescendants
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    (root : Fin m) (L : Finset (Fin m)) (v : Fin m) :
    Finset (Fin m) := by
  classical
  exact L.filter fun leaf =>
    ∃ p : T.metaTree.Path root leaf,
      v ∈ (p : T.metaTree.Walk root leaf).support

theorem selectedMetaLeafDescendants_subset
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    (root : Fin m) (L : Finset (Fin m)) (v : Fin m) :
    selectedMetaLeafDescendants T root L v ⊆ L := by
  classical
  intro leaf hleaf
  exact (Finset.mem_filter.mp hleaf).1

theorem selectedMetaLeafDescendants_card_le
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    (root : Fin m) (L : Finset (Fin m)) (v : Fin m) :
    (selectedMetaLeafDescendants T root L v).card ≤ L.card := by
  classical
  exact Finset.card_le_card (selectedMetaLeafDescendants_subset T root L v)

theorem selectedMetaLeafDescendants_card_le_length
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    (root : Fin m) {L : Finset (Fin m)} (v : Fin m)
    (hLcard : L.card = ell) :
    (selectedMetaLeafDescendants T root L v).card ≤ ell := by
  simpa [hLcard] using selectedMetaLeafDescendants_card_le T root L v

/-- Every selected leaf is a descendant of the root. -/
theorem selectedMetaLeafDescendants_root_eq
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    (root : Fin m) (L : Finset (Fin m)) :
    selectedMetaLeafDescendants T root L root = L := by
  classical
  apply Finset.Subset.antisymm
  · exact selectedMetaLeafDescendants_subset T root L root
  · intro leaf hleaf
    rcases (T.meta_isTree.connected root leaf).exists_path_of_dist with
      ⟨p, hp, _hlen⟩
    exact Finset.mem_filter.mpr
      ⟨hleaf, ⟨⟨p, hp⟩, by simp⟩⟩

/-- Cardinality form of `selectedMetaLeafDescendants_root_eq`. -/
theorem selectedMetaLeafDescendants_root_card
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    (root : Fin m) {L : Finset (Fin m)}
    (hLcard : L.card = ell) :
    (selectedMetaLeafDescendants T root L root).card = ell := by
  rw [selectedMetaLeafDescendants_root_eq T root L]
  exact hLcard

/-- A selected leaf counts itself as a descendant of itself. -/
theorem mem_selectedMetaLeafDescendants_self_of_connected
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    {root leaf : Fin m} {L : Finset (Fin m)}
    (hleaf : leaf ∈ L) :
    leaf ∈ selectedMetaLeafDescendants T root L leaf := by
  classical
  rcases (T.meta_isTree.connected root leaf).exists_path_of_dist with
    ⟨p, hp, _hlen⟩
  exact Finset.mem_filter.mpr
    ⟨hleaf, ⟨⟨p, hp⟩, by simp⟩⟩

/-- If the DFS root is a leaf with unique child `child`, all selected leaves
except the root itself are descendants of `child`. -/
theorem selectedLeaves_subset_descendants_of_root_child
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    {root child : Fin m} {L : Finset (Fin m)}
    (hchild_unique : ∀ z : Fin m, T.metaTree.Adj root z → z = child)
    (hroot_not_L : root ∉ L) :
    L ⊆ selectedMetaLeafDescendants T root L child := by
  classical
  intro leaf hleaf
  rcases (T.meta_isTree.connected root leaf).exists_path_of_dist with
    ⟨p, hp, _hlen⟩
  have hleaf_ne_root : leaf ≠ root := by
    intro hleaf_root
    exact hroot_not_L (by simpa [hleaf_root] using hleaf)
  have hp_not_nil : ¬ p.Nil := by
    intro hnil
    have hsupport : p.support = [root] :=
      _root_.SimpleGraph.Walk.nil_iff_support_eq.mp hnil
    have hleaf_mem : leaf ∈ p.support := by simp
    have hleaf_root : leaf = root := by
      simpa [hsupport] using hleaf_mem
    exact hleaf_ne_root hleaf_root
  have hlen_pos : 0 < p.length :=
    _root_.SimpleGraph.Walk.not_nil_iff_lt_length.mp hp_not_nil
  have hadj_first : T.metaTree.Adj root (p.getVert 1) := by
    simpa using p.adj_getVert_succ (i := 0) hlen_pos
  have hfirst_child : p.getVert 1 = child :=
    hchild_unique (p.getVert 1) hadj_first
  have hchild_mem : child ∈ p.support := by
    simpa [hfirst_child] using p.getVert_mem_support 1
  exact Finset.mem_filter.mpr
    ⟨hleaf, ⟨⟨p, hp⟩, hchild_mem⟩⟩

/-- The unique child of the DFS root has exactly all selected leaves below it. -/
theorem selectedMetaLeafDescendants_root_child_eq
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    {root child : Fin m} {L : Finset (Fin m)}
    (hchild_unique : ∀ z : Fin m, T.metaTree.Adj root z → z = child)
    (hroot_not_L : root ∉ L) :
    selectedMetaLeafDescendants T root L child = L :=
  Finset.Subset.antisymm
    (selectedMetaLeafDescendants_subset T root L child)
    (selectedLeaves_subset_descendants_of_root_child T hchild_unique hroot_not_L)

/-- Cardinality form of `selectedMetaLeafDescendants_root_child_eq`. -/
theorem selectedMetaLeafDescendants_root_child_card
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    {root child : Fin m} {L : Finset (Fin m)}
    (hchild_unique : ∀ z : Fin m, T.metaTree.Adj root z → z = child)
    (hroot_not_L : root ∉ L) (hLcard : L.card = ell) :
    (selectedMetaLeafDescendants T root L child).card = ell := by
  rw [selectedMetaLeafDescendants_root_child_eq T hchild_unique hroot_not_L]
  exact hLcard

/-- A selected leaf has only itself below it in the rooted meta-tree. -/
theorem selectedMetaLeafDescendants_leaf_eq_singleton
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    {root leaf : Fin m} {L : Finset (Fin m)}
    (hroot_not_L : root ∉ L) (hleaf_deg : DegreeEquals T.metaTree leaf 1)
    (hleafL : leaf ∈ L) :
    selectedMetaLeafDescendants T root L leaf = {leaf} := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨_hxL, p, hleaf_on_path⟩
    have hleaf_ne_root : leaf ≠ root := by
      intro hleaf_root
      exact hroot_not_L (by simpa [hleaf_root] using hleafL)
    let P : GraphPath T.metaTree :=
      { source := root
        target := x
        walk := (p : T.metaTree.Walk root x)
        isPath := p.2 }
    have hleaf_vertex : leaf ∈ P.vertexSet := by
      simpa [P, GraphPath.vertexSet] using hleaf_on_path
    rcases P.isEndpoint_of_mem_vertexSet_of_degreeEquals_one
        hleaf_deg hleaf_vertex with hsource | htarget
    · exact False.elim (hleaf_ne_root hsource)
    · simpa [P] using htarget.symm
  · intro hx
    have hx_eq : x = leaf := by simpa using hx
    subst x
    exact mem_selectedMetaLeafDescendants_self_of_connected T hleafL

/-- Cardinality form of `selectedMetaLeafDescendants_leaf_eq_singleton`. -/
theorem selectedMetaLeafDescendants_leaf_card
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    {root leaf : Fin m} {L : Finset (Fin m)}
    (hroot_not_L : root ∉ L) (hleaf_deg : DegreeEquals T.metaTree leaf 1)
    (hleafL : leaf ∈ L) :
    (selectedMetaLeafDescendants T root L leaf).card = 1 := by
  rw [selectedMetaLeafDescendants_leaf_eq_singleton T hroot_not_L hleaf_deg hleafL]
  simp

/-- Width arithmetic used in Step 2 of the many-leaves proof of
Chekuri--Chuzhoy Theorem 4.6.

The paper keeps at least `⌊W/(2 ell)⌋ - 8 * ell * w` root-to-leaf paths in
reserve.  The theorem's hypothesis `W > 16 * w * ell^2 + 1` makes this reserve
nonnegative. -/
theorem theorem46_halfWidth_reserve_le
    {W ell w : ℕ} (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W) :
    8 * ell * w ≤ W / (2 * ell) := by
  have hden_pos : 0 < 2 * ell := by positivity
  rw [Nat.le_div_iff_mul_le hden_pos]
  have hmul : 8 * ell * w * (2 * ell) = 16 * w * ell ^ 2 := by
    ring
  rw [hmul]
  omega

/-- The same Step 2 reserve bound for any rooted subtree whose height is at
most `ell`. -/
theorem theorem46_height_reserve_le
    {W ell w h : ℕ} (hell : 0 < ell)
    (hh : h ≤ ell) (hW : 16 * w * ell ^ 2 + 1 < W) :
    8 * h * w ≤ W / (2 * ell) := by
  have hheight : 8 * h * w ≤ 8 * ell * w := by
    exact Nat.mul_le_mul_right w (Nat.mul_le_mul_left 8 hh)
  exact hheight.trans (theorem46_halfWidth_reserve_le hell hW)

/-- The final width `w` fits inside each half-width reserve used in
Chekuri--Chuzhoy Theorem 4.6. -/
theorem theorem46_width_le_halfWidth_reserve
    {W ell w : ℕ} (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W) :
    w ≤ W / (2 * ell) := by
  have hreserve : 8 * ell * w ≤ W / (2 * ell) :=
    theorem46_halfWidth_reserve_le (W := W) (ell := ell) (w := w) hell hW
  have hw_le : w ≤ 8 * ell * w := by
    have hcoef : 1 ≤ 8 * ell := by omega
    calc
      w = 1 * w := by ring
      _ ≤ (8 * ell) * w := Nat.mul_le_mul_right w hcoef
      _ = 8 * ell * w := by ring
  exact hw_le.trans hreserve

/-- The final width `w` also fits inside every full per-leaf tranche of size
`floor(W / ell)`. -/
theorem theorem46_width_le_perLeafWidth
    {W ell w : ℕ} (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W) :
    w ≤ W / ell := by
  rw [Nat.le_div_iff_mul_le hell]
  have hell_le_sq : ell ≤ ell ^ 2 := by
    calc
      ell = ell * 1 := by ring
      _ ≤ ell * ell := Nat.mul_le_mul_left ell (Nat.succ_le_of_lt hell)
      _ = ell ^ 2 := by ring
  have hbase : w * ell ≤ w * ell ^ 2 :=
    Nat.mul_le_mul_left w hell_le_sq
  have hscale : w * ell ^ 2 ≤ 16 * w * ell ^ 2 := by
    calc
      w * ell ^ 2 = 1 * (w * ell ^ 2) := by ring
      _ ≤ 16 * (w * ell ^ 2) :=
        Nat.mul_le_mul_right (w * ell ^ 2) (by decide : 1 ≤ 16)
      _ = 16 * w * ell ^ 2 := by ring
  have hterm : w * ell ≤ 16 * w * ell ^ 2 + 1 :=
    (hbase.trans hscale).trans (Nat.le_succ _)
  exact Nat.le_of_lt (lt_of_le_of_lt hterm hW)

/-- Finite-set form of `theorem46_width_le_halfWidth_reserve`: every
half-width reserve contains a width-`w` subfamily. -/
theorem exists_subset_card_theorem46_width_from_half_reserve
    {α : Type u} [DecidableEq α] {A : Finset α} {W ell w : ℕ}
    (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W)
    (hAcard : A.card = W / (2 * ell)) :
    ∃ A₀ : Finset α, A₀ ⊆ A ∧ A₀.card = w := by
  have hw_le_A : w ≤ A.card := by
    simpa [hAcard] using
      theorem46_width_le_halfWidth_reserve (W := W) (ell := ell) (w := w) hell hW
  exact Finset.exists_subset_card_eq hw_le_A

/-- An ordered decomposition of a finite set into equal-size blocks. -/
structure FinsetBlockDecomposition
    {α : Type u} [DecidableEq α] (A : Finset α) (ell q : ℕ) where
  block : Fin ell → Finset α
  block_subset : ∀ r : Fin ell, block r ⊆ A
  block_card : ∀ r : Fin ell, (block r).card = q
  block_pairwise_disjoint :
    ∀ ⦃r s : Fin ell⦄, r ≠ s → Disjoint (block r) (block s)

/-- An equal-size block decomposition indexed by a finite set. -/
structure FinsetIndexedBlockDecomposition
    {α : Type u} [DecidableEq α] {β : Type v} [DecidableEq β]
    (A : Finset α) (I : Finset β) (q : ℕ) where
  block : I → Finset α
  block_subset : ∀ r : I, block r ⊆ A
  block_card : ∀ r : I, (block r).card = q
  block_pairwise_disjoint :
    ∀ ⦃r s : I⦄, r ≠ s → Disjoint (block r) (block s)

/-- The canonical block of an equal-size finite-set decomposition induced by
an arbitrary equivalence with `Fin (ell * q)`. -/
noncomputable def finsetCardMulBlock
    {α : Type u} [DecidableEq α] (A : Finset α) {ell q : ℕ}
    (hAcard : A.card = ell * q) (r : Fin ell) : Finset α :=
  let E : A ≃ Fin (ell * q) := Finset.equivFinOfCardEq hAcard
  (Finset.univ : Finset (Fin q)).image fun a : Fin q =>
    (E.symm ⟨r.1 * q + a.1, by
      calc
        r.1 * q + a.1 < r.1 * q + q :=
          Nat.add_lt_add_left a.2 _
        _ = (r.1 + 1) * q := by ring
        _ ≤ ell * q :=
          Nat.mul_le_mul_right q (Nat.succ_le_of_lt r.2)⟩).1

/-- A finite set whose cardinality is `ell * q` can be decomposed into `ell`
ordered, pairwise-disjoint blocks of size `q`. -/
theorem exists_finsetBlockDecomposition_of_card_mul
    {α : Type u} [DecidableEq α] {A : Finset α} {ell q : ℕ}
    (hAcard : A.card = ell * q) :
    Nonempty (FinsetBlockDecomposition A ell q) := by
  classical
  let E : A ≃ Fin (ell * q) := Finset.equivFinOfCardEq hAcard
  let block : Fin ell → Finset α := finsetCardMulBlock A hAcard
  have hblock_eq :
      ∀ r : Fin ell,
        block r =
          (Finset.univ : Finset (Fin q)).image fun a : Fin q =>
            (E.symm ⟨r.1 * q + a.1, by
              calc
                r.1 * q + a.1 < r.1 * q + q :=
                  Nat.add_lt_add_left a.2 _
                _ = (r.1 + 1) * q := by ring
                _ ≤ ell * q :=
                  Nat.mul_le_mul_right q (Nat.succ_le_of_lt r.2)⟩).1 := by
    intro r
    rfl
  refine ⟨{
    block := block
    block_subset := ?_
    block_card := ?_
    block_pairwise_disjoint := ?_ }⟩
  · intro r x hx
    rw [hblock_eq r] at hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, hx⟩
    rw [← hx]
    exact (E.symm _).2
  · intro r
    rw [hblock_eq r]
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have hsub :
          E.symm ⟨r.1 * q + a.1, by
            calc
              r.1 * q + a.1 < r.1 * q + q :=
                Nat.add_lt_add_left a.2 _
              _ = (r.1 + 1) * q := by ring
              _ ≤ ell * q :=
                Nat.mul_le_mul_right q (Nat.succ_le_of_lt r.2)⟩ =
            E.symm ⟨r.1 * q + b.1, by
            calc
              r.1 * q + b.1 < r.1 * q + q :=
                Nat.add_lt_add_left b.2 _
              _ = (r.1 + 1) * q := by ring
              _ ≤ ell * q :=
                Nat.mul_le_mul_right q (Nat.succ_le_of_lt r.2)⟩ := by
        exact Subtype.ext hab
      have hidx := E.symm.injective hsub
      have hval : r.1 * q + a.1 = r.1 * q + b.1 :=
        congrArg Fin.val hidx
      exact Fin.ext (Nat.add_left_cancel hval)
  · intro r s hrs
    rw [hblock_eq r, hblock_eq s, Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨a, _ha, hx⟩
    rcases Finset.mem_image.mp hy with ⟨b, _hb, hy⟩
    have hsub :
        E.symm ⟨r.1 * q + a.1, by
          calc
            r.1 * q + a.1 < r.1 * q + q :=
              Nat.add_lt_add_left a.2 _
            _ = (r.1 + 1) * q := by ring
            _ ≤ ell * q :=
              Nat.mul_le_mul_right q (Nat.succ_le_of_lt r.2)⟩ =
          E.symm ⟨s.1 * q + b.1, by
          calc
            s.1 * q + b.1 < s.1 * q + q :=
              Nat.add_lt_add_left b.2 _
            _ = (s.1 + 1) * q := by ring
            _ ≤ ell * q :=
              Nat.mul_le_mul_right q (Nat.succ_le_of_lt s.2)⟩ := by
      exact Subtype.ext (hx.trans hy.symm)
    have hidx := E.symm.injective hsub
    have hval : r.1 * q + a.1 = s.1 * q + b.1 :=
      congrArg Fin.val hidx
    have hq_pos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) a.2
    have hrdiv : (r.1 * q + a.1) / q = r.1 := by
      calc
        (r.1 * q + a.1) / q = (a.1 + q * r.1) / q := by ring_nf
        _ = a.1 / q + r.1 := Nat.add_mul_div_left a.1 r.1 hq_pos
        _ = r.1 := by
          rw [Nat.div_eq_of_lt a.2]
          simp
    have hsdiv : (s.1 * q + b.1) / q = s.1 := by
      calc
        (s.1 * q + b.1) / q = (b.1 + q * s.1) / q := by ring_nf
        _ = b.1 / q + s.1 := Nat.add_mul_div_left b.1 s.1 hq_pos
        _ = s.1 := by
          rw [Nat.div_eq_of_lt b.2]
          simp
    have hdiv := congrArg (fun n : ℕ => n / q) hval
    change (r.1 * q + a.1) / q = (s.1 * q + b.1) / q at hdiv
    rw [hrdiv, hsdiv] at hdiv
    exact hrs (Fin.ext hdiv)

/-- A finite set of size `|I| * q` can be decomposed into `q`-element blocks
indexed by the elements of `I`. -/
theorem exists_finsetIndexedBlockDecomposition_of_card_mul
    {α : Type u} [DecidableEq α] {β : Type v} [DecidableEq β]
    {A : Finset α} {I : Finset β} {q : ℕ}
    (hAcard : A.card = I.card * q) :
    Nonempty (FinsetIndexedBlockDecomposition A I q) := by
  classical
  rcases exists_finsetBlockDecomposition_of_card_mul
      (A := A) (ell := I.card) (q := q) hAcard with ⟨B⟩
  exact ⟨{
    block := fun r => B.block (I.equivFin r)
    block_subset := fun r => B.block_subset (I.equivFin r)
    block_card := fun r => B.block_card (I.equivFin r)
    block_pairwise_disjoint := by
      intro r s hrs
      exact B.block_pairwise_disjoint (by
        intro h
        exact hrs (I.equivFin.injective h)) }⟩

/-- Step 1 path-count arithmetic: any subtree containing at most `ell`
selected leaves needs at most `W` connector paths when each leaf receives
`⌊W/ell⌋` paths. -/
theorem theorem46_step1_descendant_path_count_le_width
    {W ell n : ℕ} (hn : n ≤ ell) :
    n * (W / ell) ≤ W := by
  calc
    n * (W / ell) ≤ ell * (W / ell) :=
      Nat.mul_le_mul_right (W / ell) hn
    _ = (W / ell) * ell := by ring
    _ ≤ W := Nat.div_mul_le_self W ell

/-- Finite-set form of the Step 1 count: a width-`W` interface contains a
subfamily of size `n * ⌊W/ell⌋` whenever `n ≤ ell`. -/
theorem exists_subset_card_theorem46_descendant_path_count
    {α : Type u} [DecidableEq α] {A : Finset α} {W ell n : ℕ}
    (hAcard : A.card = W) (hn : n ≤ ell) :
    ∃ A₀ : Finset α, A₀ ⊆ A ∧ A₀.card = n * (W / ell) := by
  have hcount_le : n * (W / ell) ≤ A.card := by
    simpa [hAcard] using theorem46_step1_descendant_path_count_le_width
      (W := W) (ell := ell) (n := n) hn
  exact Finset.exists_subset_card_eq hcount_le

/-- The two leaf reserves of size `⌊W/(2 * ell)⌋` fit inside the Step 1
root-to-leaf bundle of size `⌊W/ell⌋`. -/
theorem theorem46_two_half_counts_le_step1_count
    {W ell : ℕ} (hell : 0 < ell) :
    2 * (W / (2 * ell)) ≤ W / ell := by
  rw [Nat.le_div_iff_mul_le hell]
  have hmul :
      2 * (W / (2 * ell)) * ell = (W / (2 * ell)) * (2 * ell) := by
    ring
  rw [hmul]
  exact Nat.div_mul_le_self W (2 * ell)

/-- Finite-set form of `theorem46_two_half_counts_le_step1_count`: a bundle of
`⌊W/ell⌋` paths contains two disjoint subbundles of size `⌊W/(2 * ell)⌋`. -/
theorem exists_two_disjoint_subsets_card_theorem46_half_count
    {α : Type u} [DecidableEq α] {A : Finset α} {W ell : ℕ}
    (hell : 0 < ell) (hAcard : A.card = W / ell) :
    ∃ A₁ A₂ : Finset α,
      A₁ ⊆ A ∧ A₂ ⊆ A ∧ Disjoint A₁ A₂ ∧
        A₁.card = W / (2 * ell) ∧ A₂.card = W / (2 * ell) := by
  classical
  let q := W / (2 * ell)
  have htwo_q_le_A : 2 * q ≤ A.card := by
    simpa [q, hAcard] using theorem46_two_half_counts_le_step1_count
      (W := W) (ell := ell) hell
  have hq_le_A : q ≤ A.card := by omega
  rcases Finset.exists_subset_card_eq hq_le_A with ⟨A₁, hA₁sub, hA₁card⟩
  have hq_le_sdiff : q ≤ (A \ A₁).card := by
    have hsdiff_card : (A \ A₁).card = A.card - q := by
      rw [Finset.card_sdiff_of_subset hA₁sub, hA₁card]
    rw [hsdiff_card]
    omega
  rcases Finset.exists_subset_card_eq hq_le_sdiff with ⟨A₂, hA₂sub_sdiff, hA₂card⟩
  have hA₂sub : A₂ ⊆ A := subset_trans hA₂sub_sdiff Finset.sdiff_subset
  have hdisj : Disjoint A₁ A₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    exact (Finset.mem_sdiff.mp (hA₂sub_sdiff hx₂)).2 hx₁
  exact ⟨A₁, A₂, hA₁sub, hA₂sub, hdisj, hA₁card, hA₂card⟩

/-- Connector-specific Step 1 subbundle selection.

For any meta-edge connector of width `W`, and any descendant count `n ≤ ell`,
one can select `n * ⌊W/ell⌋` connector paths; their source and target endpoint
sets have the same cardinality. -/
theorem exists_connector_indexSet_card_theorem46_descendant_path_count
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell n : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    (hn : n ≤ ell) :
    ∃ I : Finset (T.connector i j hij).Index,
      I.card = n * (W / ell) ∧
        ((T.connector i j hij).sourceSet I).card = n * (W / ell) ∧
          ((T.connector i j hij).targetSet I).card = n * (W / ell) ∧
            ((T.connector i j hij).restrictIndexSet I).card =
              n * (W / ell) := by
  classical
  let P := T.connector i j hij
  have hcount_le : n * (W / ell) ≤ P.card := by
    rw [show P.card = W by simpa [P] using T.connector_card i j hij]
    exact theorem46_step1_descendant_path_count_le_width
      (W := W) (ell := ell) (n := n) hn
  rcases P.exists_indexSet_card_eq hcount_le with ⟨I, hIcard, hrestrict⟩
  refine ⟨I, hIcard, ?_, ?_, hrestrict⟩
  · simp [P, hIcard]
  · simp [P, hIcard]

/-- The many-leaves hypothesis supplies the full root/child/selected-leaf setup
used by the DFS branch of Theorem 4.6. -/
theorem exists_theorem46_leafExtractionSetup
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {m W ell : ℕ}
    (T : StrongTreeOfSetsSystem G m W)
    (hleaves : T.HasMetaLeavesAtLeast (ell + 1)) :
    Nonempty (Theorem46LeafExtractionSetup T ell) := by
  rcases exists_metaLeaf_root_child_and_selectedLeaves T hleaves with
    ⟨root, child, L, hroot_leaf, hroot_child, hchild_unique,
      hroot_not_L, hLcard, hLleaf⟩
  exact ⟨{
    root := root
    child := child
    leaves := L
    root_leaf := hroot_leaf
    root_child_adj := hroot_child
    root_child_unique := hchild_unique
    root_not_mem_leaves := hroot_not_L
    leaves_card := hLcard
    leaves_leaf := hLleaf }⟩

namespace Theorem46LeafExtractionSetup

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {m W ell : ℕ}
variable {T : StrongTreeOfSetsSystem G m W}

/-- Descendant count at any meta-vertex is bounded by the requested length. -/
theorem descendants_card_le_length (S : Theorem46LeafExtractionSetup T ell)
    (v : Fin m) :
    (selectedMetaLeafDescendants T S.root S.leaves v).card ≤ ell :=
  selectedMetaLeafDescendants_card_le_length T S.root v S.leaves_card

/-- The DFS root sees all selected leaves below it. -/
theorem descendants_root_eq (S : Theorem46LeafExtractionSetup T ell) :
    selectedMetaLeafDescendants T S.root S.leaves S.root = S.leaves :=
  selectedMetaLeafDescendants_root_eq T S.root S.leaves

/-- Cardinality form for the DFS root. -/
theorem descendants_root_card (S : Theorem46LeafExtractionSetup T ell) :
    (selectedMetaLeafDescendants T S.root S.leaves S.root).card = ell :=
  selectedMetaLeafDescendants_root_card T S.root S.leaves_card

/-- The root child sees all selected leaves below it. -/
theorem descendants_root_child_eq (S : Theorem46LeafExtractionSetup T ell) :
    selectedMetaLeafDescendants T S.root S.leaves S.child = S.leaves :=
  selectedMetaLeafDescendants_root_child_eq T
    S.root_child_unique S.root_not_mem_leaves

/-- Cardinality form: the root child has descendant count exactly `ell`. -/
theorem descendants_root_child_card (S : Theorem46LeafExtractionSetup T ell) :
    (selectedMetaLeafDescendants T S.root S.leaves S.child).card = ell :=
  selectedMetaLeafDescendants_root_child_card T
    S.root_child_unique S.root_not_mem_leaves S.leaves_card

/-- A selected leaf has itself as its only selected descendant. -/
theorem descendants_leaf_eq_singleton (S : Theorem46LeafExtractionSetup T ell)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    selectedMetaLeafDescendants T S.root S.leaves leaf = {leaf} :=
  selectedMetaLeafDescendants_leaf_eq_singleton T
    S.root_not_mem_leaves (S.leaves_leaf leaf hleaf) hleaf

/-- Cardinality form for selected leaves. -/
theorem descendants_leaf_card (S : Theorem46LeafExtractionSetup T ell)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    (selectedMetaLeafDescendants T S.root S.leaves leaf).card = 1 :=
  selectedMetaLeafDescendants_leaf_card T
    S.root_not_mem_leaves (S.leaves_leaf leaf hleaf) hleaf

/-- Connector selection with the exact `n(S) * floor(W / ell)` path count,
where `n(S)` is the selected-descendant count of a meta-vertex. -/
theorem exists_connector_selection_for_descendant_count
    (S : Theorem46LeafExtractionSetup T ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j) (v : Fin m) :
    ∃ I : Finset (T.connector i j hij).Index,
      I.card =
          (selectedMetaLeafDescendants T S.root S.leaves v).card * (W / ell) ∧
        ((T.connector i j hij).sourceSet I).card =
          (selectedMetaLeafDescendants T S.root S.leaves v).card * (W / ell) ∧
          ((T.connector i j hij).targetSet I).card =
            (selectedMetaLeafDescendants T S.root S.leaves v).card * (W / ell) ∧
            ((T.connector i j hij).restrictIndexSet I).card =
              (selectedMetaLeafDescendants T S.root S.leaves v).card * (W / ell) :=
  exists_connector_indexSet_card_theorem46_descendant_path_count
    (T := T) (ell := ell)
    (n := (selectedMetaLeafDescendants T S.root S.leaves v).card)
    hij (S.descendants_card_le_length v)

/-- Step 1 connector data for a meta-edge, split into one tranche for each
selected leaf below a specified meta-vertex. -/
structure ConnectorDescendantTrancheData
    (S : Theorem46LeafExtractionSetup T ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j) (v : Fin m) where
  indexSet : Finset (T.connector i j hij).Index
  index_card :
    indexSet.card =
      (selectedMetaLeafDescendants T S.root S.leaves v).card * (W / ell)
  source_card :
    ((T.connector i j hij).sourceSet indexSet).card =
      (selectedMetaLeafDescendants T S.root S.leaves v).card * (W / ell)
  target_card :
    ((T.connector i j hij).targetSet indexSet).card =
      (selectedMetaLeafDescendants T S.root S.leaves v).card * (W / ell)
  restricted_card :
    ((T.connector i j hij).restrictIndexSet indexSet).card =
      (selectedMetaLeafDescendants T S.root S.leaves v).card * (W / ell)
  tranche :
    selectedMetaLeafDescendants T S.root S.leaves v →
      Finset (T.connector i j hij).Index
  tranche_subset_index :
    ∀ leaf : selectedMetaLeafDescendants T S.root S.leaves v,
      tranche leaf ⊆ indexSet
  tranche_card :
    ∀ leaf : selectedMetaLeafDescendants T S.root S.leaves v,
      (tranche leaf).card = W / ell
  tranche_pairwise_disjoint :
    ∀ ⦃leaf leaf' : selectedMetaLeafDescendants T S.root S.leaves v⦄,
      leaf ≠ leaf' → Disjoint (tranche leaf) (tranche leaf')
  tranche_source_card :
    ∀ leaf : selectedMetaLeafDescendants T S.root S.leaves v,
      ((T.connector i j hij).sourceSet (tranche leaf)).card = W / ell
  tranche_target_card :
    ∀ leaf : selectedMetaLeafDescendants T S.root S.leaves v,
      ((T.connector i j hij).targetSet (tranche leaf)).card = W / ell
  tranche_restricted_card :
    ∀ leaf : selectedMetaLeafDescendants T S.root S.leaves v,
      ((T.connector i j hij).restrictIndexSet (tranche leaf)).card = W / ell
  tranche_restricted_staysIn :
    ∀ leaf : selectedMetaLeafDescendants T S.root S.leaves v,
      ((T.connector i j hij).restrictIndexSet (tranche leaf)).toPathPacking.StaysIn
        (T.connector i j hij).toPathPacking.vertexSet
  tranche_restricted_internallyDisjoint_clusters :
    ∀ leaf : selectedMetaLeafDescendants T S.root S.leaves v, ∀ c : Fin m,
      PathPacking.InternallyDisjointFromSet
        ((T.connector i j hij).restrictIndexSet (tranche leaf)).toPathPacking
        (T.cluster c)
  tranche_restricted_mutuallyNodeDisjoint :
    ∀ ⦃leaf leaf' : selectedMetaLeafDescendants T S.root S.leaves v⦄,
      leaf ≠ leaf' →
        PathPacking.MutuallyNodeDisjoint
          ((T.connector i j hij).restrictIndexSet (tranche leaf)).toPathPacking
          ((T.connector i j hij).restrictIndexSet (tranche leaf')).toPathPacking

/-- Every Step 1 connector selection admits a selected-descendant-indexed
tranche decomposition. -/
theorem exists_connectorDescendantTrancheData
    (S : Theorem46LeafExtractionSetup T ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j) (v : Fin m) :
    Nonempty (ConnectorDescendantTrancheData S hij v) := by
  classical
  let Dset : Finset (Fin m) :=
    selectedMetaLeafDescendants T S.root S.leaves v
  let P := T.connector i j hij
  rcases S.exists_connector_selection_for_descendant_count hij v with
    ⟨J, hJcard, hsource, htarget, hrestrict⟩
  rcases exists_finsetIndexedBlockDecomposition_of_card_mul
      (A := J) (I := Dset) (q := W / ell) hJcard with ⟨B⟩
  exact ⟨{
    indexSet := J
    index_card := hJcard
    source_card := hsource
    target_card := htarget
    restricted_card := hrestrict
    tranche := B.block
    tranche_subset_index := B.block_subset
    tranche_card := B.block_card
    tranche_pairwise_disjoint := by
      intro leaf leaf' hne
      exact B.block_pairwise_disjoint hne
    tranche_source_card := by
      intro leaf
      simp [B.block_card leaf]
    tranche_target_card := by
      intro leaf
      simp [B.block_card leaf]
    tranche_restricted_card := by
      intro leaf
      simp [B.block_card leaf]
    tranche_restricted_staysIn := by
      intro leaf
      exact P.restrictIndexSet_staysIn_vertexSet (B.block leaf)
    tranche_restricted_internallyDisjoint_clusters := by
      intro leaf c
      exact P.restrictIndexSet_internallyDisjointFromSet (B.block leaf)
        (T.connector_internally_disjoint_cluster i j hij c)
    tranche_restricted_mutuallyNodeDisjoint := by
      intro leaf leaf' hne a b
      exact P.node_disjoint (by
        intro h
        exact Finset.disjoint_left.mp (B.block_pairwise_disjoint hne)
          a.2 (by simp [h, b.2])) }⟩

/-- Step 1 connector selection at the root-child edge, where all selected leaves
are descendants of the child. -/
theorem exists_root_child_connector_selection
    (S : Theorem46LeafExtractionSetup T ell) :
    ∃ I : Finset (T.connector S.root S.child S.root_child_adj).Index,
      I.card = ell * (W / ell) ∧
        ((T.connector S.root S.child S.root_child_adj).sourceSet I).card =
          ell * (W / ell) ∧
          ((T.connector S.root S.child S.root_child_adj).targetSet I).card =
            ell * (W / ell) ∧
            ((T.connector S.root S.child S.root_child_adj).restrictIndexSet I).card =
              ell * (W / ell) := by
  rcases S.exists_connector_selection_for_descendant_count
      S.root_child_adj S.child with
    ⟨I, hIcard, hsource, htarget, hrestrict⟩
  rw [S.descendants_root_child_card] at hIcard hsource htarget hrestrict
  exact ⟨I, hIcard, hsource, htarget, hrestrict⟩

/-- At a selected leaf the Step 1 connector count specializes to
`floor(W / ell)`. -/
theorem exists_connector_selection_for_selected_leaf
    (S : Theorem46LeafExtractionSetup T ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    ∃ I : Finset (T.connector i j hij).Index,
      I.card = W / ell ∧
        ((T.connector i j hij).sourceSet I).card = W / ell ∧
          ((T.connector i j hij).targetSet I).card = W / ell ∧
            ((T.connector i j hij).restrictIndexSet I).card = W / ell := by
  rcases S.exists_connector_selection_for_descendant_count hij leaf with
    ⟨I, hIcard, hsource, htarget, hrestrict⟩
  rw [S.descendants_leaf_card hleaf] at hIcard hsource htarget hrestrict
  have hIcard' : I.card = W / ell := by
    simpa only [one_mul] using hIcard
  have hsource' : ((T.connector i j hij).sourceSet I).card = W / ell := by
    simpa only [one_mul] using hsource
  have htarget' : ((T.connector i j hij).targetSet I).card = W / ell := by
    simpa only [one_mul] using htarget
  have hrestrict' :
      ((T.connector i j hij).restrictIndexSet I).card = W / ell := by
    simpa only [one_mul] using hrestrict
  exact ⟨I, hIcard', hsource', htarget', hrestrict'⟩

/-- The selected-leaf connector subbundle as an actual restricted perfect
packing, with the inherited region and cluster-separation invariants exposed. -/
theorem exists_restricted_connector_for_selected_leaf
    (S : Theorem46LeafExtractionSetup T ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    ∃ I : Finset (T.connector i j hij).Index,
      I.card = W / ell ∧
        ((T.connector i j hij).sourceSet I).card = W / ell ∧
          ((T.connector i j hij).targetSet I).card = W / ell ∧
            ((T.connector i j hij).restrictIndexSet I).card = W / ell ∧
              ((T.connector i j hij).restrictIndexSet I).toPathPacking.StaysIn
                (T.connector i j hij).toPathPacking.vertexSet ∧
                ∀ r : Fin m,
                  PathPacking.InternallyDisjointFromSet
                    ((T.connector i j hij).restrictIndexSet I).toPathPacking
                    (T.cluster r) := by
  rcases S.exists_connector_selection_for_selected_leaf hij hleaf with
    ⟨I, hIcard, hsource, htarget, hrestrict⟩
  refine ⟨I, hIcard, hsource, htarget, hrestrict, ?_, ?_⟩
  · exact (T.connector i j hij).restrictIndexSet_staysIn_vertexSet I
  · intro r
    exact (T.connector i j hij).restrictIndexSet_internallyDisjointFromSet I
      (T.connector_internally_disjoint_cluster i j hij r)

/-- Root-child connector subbundle as an actual restricted perfect packing.

The cardinality is `ell * floor(W / ell)`, because the root child contains all
selected leaves as descendants. -/
theorem exists_root_child_restricted_connector
    (S : Theorem46LeafExtractionSetup T ell) :
    ∃ I : Finset (T.connector S.root S.child S.root_child_adj).Index,
      I.card = ell * (W / ell) ∧
        ((T.connector S.root S.child S.root_child_adj).sourceSet I).card =
          ell * (W / ell) ∧
          ((T.connector S.root S.child S.root_child_adj).targetSet I).card =
            ell * (W / ell) ∧
            ((T.connector S.root S.child S.root_child_adj).restrictIndexSet I).card =
              ell * (W / ell) ∧
              PathPacking.StaysIn
                (((T.connector S.root S.child S.root_child_adj).restrictIndexSet I).toPathPacking)
                (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet ∧
                ∀ r : Fin m,
                  PathPacking.InternallyDisjointFromSet
                    (((T.connector S.root S.child S.root_child_adj).restrictIndexSet I).toPathPacking)
                    (T.cluster r) := by
  rcases S.exists_root_child_connector_selection with
    ⟨I, hIcard, hsource, htarget, hrestrict⟩
  refine ⟨I, hIcard, hsource, htarget, hrestrict, ?_, ?_⟩
  · exact (T.connector S.root S.child S.root_child_adj).restrictIndexSet_staysIn_vertexSet I
  · intro r
    exact (T.connector S.root S.child S.root_child_adj).restrictIndexSet_internallyDisjointFromSet I
        (T.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj r)

/-- For a selected leaf connector bundle, the source endpoints contain the two
half-size reserves used by Step 2 of Theorem 4.6. -/
theorem exists_source_reserves_for_selected_leaf_connector
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    ∃ I : Finset (T.connector i j hij).Index,
      ∃ A₁ A₂ : Finset V,
        I.card = W / ell ∧
          ((T.connector i j hij).sourceSet I).card = W / ell ∧
            A₁ ⊆ (T.connector i j hij).sourceSet I ∧
              A₂ ⊆ (T.connector i j hij).sourceSet I ∧
                Disjoint A₁ A₂ ∧
                  A₁.card = W / (2 * ell) ∧
                    A₂.card = W / (2 * ell) := by
  rcases S.exists_connector_selection_for_selected_leaf hij hleaf with
    ⟨I, hIcard, hsource, _htarget, _hrestrict⟩
  rcases exists_two_disjoint_subsets_card_theorem46_half_count
      (A := (T.connector i j hij).sourceSet I) (W := W) (ell := ell)
      hell hsource with
    ⟨A₁, A₂, hA₁, hA₂, hdisj, hA₁card, hA₂card⟩
  exact ⟨I, A₁, A₂, hIcard, hsource, hA₁, hA₂, hdisj, hA₁card, hA₂card⟩

/-- Target-endpoint version of
`exists_source_reserves_for_selected_leaf_connector`. -/
theorem exists_target_reserves_for_selected_leaf_connector
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    ∃ I : Finset (T.connector i j hij).Index,
      ∃ A₁ A₂ : Finset V,
        I.card = W / ell ∧
          ((T.connector i j hij).targetSet I).card = W / ell ∧
            A₁ ⊆ (T.connector i j hij).targetSet I ∧
              A₂ ⊆ (T.connector i j hij).targetSet I ∧
                Disjoint A₁ A₂ ∧
                  A₁.card = W / (2 * ell) ∧
                    A₂.card = W / (2 * ell) := by
  rcases S.exists_connector_selection_for_selected_leaf hij hleaf with
    ⟨I, hIcard, _hsource, htarget, _hrestrict⟩
  rcases exists_two_disjoint_subsets_card_theorem46_half_count
      (A := (T.connector i j hij).targetSet I) (W := W) (ell := ell)
      hell htarget with
    ⟨A₁, A₂, hA₁, hA₂, hdisj, hA₁card, hA₂card⟩
  exact ⟨I, A₁, A₂, hIcard, htarget, hA₁, hA₂, hdisj, hA₁card, hA₂card⟩

/-- The two source reserves of a selected-leaf connector can be linked inside
the source-side cluster. -/
theorem exists_source_reserve_linkage_for_selected_leaf_connector
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    ∃ I : Finset (T.connector i j hij).Index,
      ∃ A₁ A₂ : Finset V,
        ∃ Q : PerfectPathPacking G A₁ A₂,
          I.card = W / ell ∧
            ((T.connector i j hij).sourceSet I).card = W / ell ∧
              A₁ ⊆ (T.connector i j hij).sourceSet I ∧
                A₂ ⊆ (T.connector i j hij).sourceSet I ∧
                  Disjoint A₁ A₂ ∧
                    A₁.card = W / (2 * ell) ∧
                      A₂.card = W / (2 * ell) ∧
                        Q.card = W / (2 * ell) ∧
                          Q.toPathPacking.StaysIn (T.cluster i) := by
  rcases S.exists_source_reserves_for_selected_leaf_connector
      hell hij hleaf with
    ⟨I, A₁, A₂, hIcard, hsource, hA₁, hA₂, hdisj, hA₁card, hA₂card⟩
  have hsource_subset :
      (T.connector i j hij).sourceSet I ⊆ T.interface i j hij :=
    (T.connector i j hij).sourceSet_subset_left I
  have hA₁_interface : A₁ ⊆ T.interface i j hij :=
    subset_trans hA₁ hsource_subset
  have hA₂_interface : A₂ ⊆ T.interface i j hij :=
    subset_trans hA₂ hsource_subset
  have hcard : A₁.card = A₂.card := hA₁card.trans hA₂card.symm
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      hij hA₁_interface hA₂_interface hdisj hcard with
    ⟨Q, hQcard, hQstay⟩
  exact ⟨I, A₁, A₂, Q, hIcard, hsource, hA₁, hA₂, hdisj,
    hA₁card, hA₂card, hQcard.trans hA₁card, hQstay⟩

/-- The two target reserves of a selected-leaf connector can be linked inside
the target-side cluster. -/
theorem exists_target_reserve_linkage_for_selected_leaf_connector
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    ∃ I : Finset (T.connector i j hij).Index,
      ∃ A₁ A₂ : Finset V,
        ∃ Q : PerfectPathPacking G A₁ A₂,
          I.card = W / ell ∧
            ((T.connector i j hij).targetSet I).card = W / ell ∧
              A₁ ⊆ (T.connector i j hij).targetSet I ∧
                A₂ ⊆ (T.connector i j hij).targetSet I ∧
                  Disjoint A₁ A₂ ∧
                    A₁.card = W / (2 * ell) ∧
                      A₂.card = W / (2 * ell) ∧
                        Q.card = W / (2 * ell) ∧
                          Q.toPathPacking.StaysIn (T.cluster j) := by
  rcases S.exists_target_reserves_for_selected_leaf_connector
      hell hij hleaf with
    ⟨I, A₁, A₂, hIcard, htarget, hA₁, hA₂, hdisj, hA₁card, hA₂card⟩
  have htarget_subset :
      (T.connector i j hij).targetSet I ⊆
        T.interface j i (T.metaTree.symm hij) :=
    (T.connector i j hij).targetSet_subset_right I
  have hA₁_interface :
      A₁ ⊆ T.interface j i (T.metaTree.symm hij) :=
    subset_trans hA₁ htarget_subset
  have hA₂_interface :
      A₂ ⊆ T.interface j i (T.metaTree.symm hij) :=
    subset_trans hA₂ htarget_subset
  have hcard : A₁.card = A₂.card := hA₁card.trans hA₂card.symm
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      (T.metaTree.symm hij) hA₁_interface hA₂_interface hdisj hcard with
    ⟨Q, hQcard, hQstay⟩
  exact ⟨I, A₁, A₂, Q, hIcard, htarget, hA₁, hA₂, hdisj,
    hA₁card, hA₂card, hQcard.trans hA₁card, hQstay⟩

/-- Step 2 data on a selected-leaf connector bundle.

The same connector index set is used on both ends.  Its source endpoints
contain two equal half-size reserves linked inside the source cluster, and its
target endpoints contain two equal half-size reserves linked inside the target
cluster. -/
structure SelectedLeafConnectorStep2Data
    (S : Theorem46LeafExtractionSetup T ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j) where
  indexSet : Finset (T.connector i j hij).Index
  sourceReserveLeft : Finset V
  sourceReserveRight : Finset V
  targetReserveLeft : Finset V
  targetReserveRight : Finset V
  sourceLinkage : PerfectPathPacking G sourceReserveLeft sourceReserveRight
  targetLinkage : PerfectPathPacking G targetReserveLeft targetReserveRight
  index_card : indexSet.card = W / ell
  source_card : ((T.connector i j hij).sourceSet indexSet).card = W / ell
  target_card : ((T.connector i j hij).targetSet indexSet).card = W / ell
  restricted_card : ((T.connector i j hij).restrictIndexSet indexSet).card =
    W / ell
  sourceReserveLeft_subset :
    sourceReserveLeft ⊆ (T.connector i j hij).sourceSet indexSet
  sourceReserveRight_subset :
    sourceReserveRight ⊆ (T.connector i j hij).sourceSet indexSet
  targetReserveLeft_subset :
    targetReserveLeft ⊆ (T.connector i j hij).targetSet indexSet
  targetReserveRight_subset :
    targetReserveRight ⊆ (T.connector i j hij).targetSet indexSet
  sourceReserve_disjoint : Disjoint sourceReserveLeft sourceReserveRight
  targetReserve_disjoint : Disjoint targetReserveLeft targetReserveRight
  sourceReserveLeft_card : sourceReserveLeft.card = W / (2 * ell)
  sourceReserveRight_card : sourceReserveRight.card = W / (2 * ell)
  targetReserveLeft_card : targetReserveLeft.card = W / (2 * ell)
  targetReserveRight_card : targetReserveRight.card = W / (2 * ell)
  sourceLinkage_card : sourceLinkage.card = W / (2 * ell)
  targetLinkage_card : targetLinkage.card = W / (2 * ell)
  sourceLinkage_staysIn : sourceLinkage.toPathPacking.StaysIn (T.cluster i)
  targetLinkage_staysIn : targetLinkage.toPathPacking.StaysIn (T.cluster j)
  restricted_staysIn :
    ((T.connector i j hij).restrictIndexSet indexSet).toPathPacking.StaysIn
      (T.connector i j hij).toPathPacking.vertexSet
  restricted_internallyDisjoint_clusters :
    ∀ r : Fin m,
      PathPacking.InternallyDisjointFromSet
        ((T.connector i j hij).restrictIndexSet indexSet).toPathPacking
        (T.cluster r)

/-- A width-`w` trimming of the four half-width reserves carried by Step 2. -/
structure SelectedLeafConnectorWidthData
    (S : Theorem46LeafExtractionSetup T ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j) (w : ℕ) where
  step2 : SelectedLeafConnectorStep2Data S hij
  sourceLeft : Finset V
  sourceRight : Finset V
  targetLeft : Finset V
  targetRight : Finset V
  sourceLeft_subset : sourceLeft ⊆ step2.sourceReserveLeft
  sourceRight_subset : sourceRight ⊆ step2.sourceReserveRight
  targetLeft_subset : targetLeft ⊆ step2.targetReserveLeft
  targetRight_subset : targetRight ⊆ step2.targetReserveRight
  sourceLeft_card : sourceLeft.card = w
  sourceRight_card : sourceRight.card = w
  targetLeft_card : targetLeft.card = w
  targetRight_card : targetRight.card = w

/-- Coherent Step 2 data on a selected-leaf connector.

Unlike `SelectedLeafConnectorStep2Data`, the two half-width bundles are chosen
as disjoint subfamilies of connector indices first.  The source and target
reserves are then the matched endpoint sets of those same connector paths. -/
structure SelectedLeafConnectorCoherentStep2Data
    (S : Theorem46LeafExtractionSetup T ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j) where
  indexSet : Finset (T.connector i j hij).Index
  leftIndexSet : Finset (T.connector i j hij).Index
  rightIndexSet : Finset (T.connector i j hij).Index
  sourceLinkage :
    PerfectPathPacking G
      ((T.connector i j hij).sourceSet leftIndexSet)
      ((T.connector i j hij).sourceSet rightIndexSet)
  targetLinkage :
    PerfectPathPacking G
      ((T.connector i j hij).targetSet leftIndexSet)
      ((T.connector i j hij).targetSet rightIndexSet)
  index_card : indexSet.card = W / ell
  leftIndex_subset : leftIndexSet ⊆ indexSet
  rightIndex_subset : rightIndexSet ⊆ indexSet
  index_disjoint : Disjoint leftIndexSet rightIndexSet
  leftIndex_card : leftIndexSet.card = W / (2 * ell)
  rightIndex_card : rightIndexSet.card = W / (2 * ell)
  sourceLeft_card :
    ((T.connector i j hij).sourceSet leftIndexSet).card = W / (2 * ell)
  sourceRight_card :
    ((T.connector i j hij).sourceSet rightIndexSet).card = W / (2 * ell)
  targetLeft_card :
    ((T.connector i j hij).targetSet leftIndexSet).card = W / (2 * ell)
  targetRight_card :
    ((T.connector i j hij).targetSet rightIndexSet).card = W / (2 * ell)
  sourceLeft_subset :
    (T.connector i j hij).sourceSet leftIndexSet ⊆
      (T.connector i j hij).sourceSet indexSet
  sourceRight_subset :
    (T.connector i j hij).sourceSet rightIndexSet ⊆
      (T.connector i j hij).sourceSet indexSet
  targetLeft_subset :
    (T.connector i j hij).targetSet leftIndexSet ⊆
      (T.connector i j hij).targetSet indexSet
  targetRight_subset :
    (T.connector i j hij).targetSet rightIndexSet ⊆
      (T.connector i j hij).targetSet indexSet
  sourceReserve_disjoint :
    Disjoint ((T.connector i j hij).sourceSet leftIndexSet)
      ((T.connector i j hij).sourceSet rightIndexSet)
  targetReserve_disjoint :
    Disjoint ((T.connector i j hij).targetSet leftIndexSet)
      ((T.connector i j hij).targetSet rightIndexSet)
  sourceLinkage_card : sourceLinkage.card = W / (2 * ell)
  targetLinkage_card : targetLinkage.card = W / (2 * ell)
  sourceLinkage_staysIn : sourceLinkage.toPathPacking.StaysIn (T.cluster i)
  targetLinkage_staysIn : targetLinkage.toPathPacking.StaysIn (T.cluster j)

/-- Coherent Step 2 data after trimming to the final width `w`.

The right half-index set is induced by the source-cluster linkage, so the
source linkage, the two connector subfamilies, and the rebuilt target linkage
all use the same matched connector endpoints. -/
structure SelectedLeafConnectorCoherentWidthData
    (S : Theorem46LeafExtractionSetup T ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j) (w : ℕ) where
  step2 : SelectedLeafConnectorCoherentStep2Data S hij
  leftIndexSet : Finset (T.connector i j hij).Index
  rightIndexSet : Finset (T.connector i j hij).Index
  sourceLinkage :
    PerfectPathPacking G
      ((T.connector i j hij).sourceSet leftIndexSet)
      ((T.connector i j hij).sourceSet rightIndexSet)
  targetLinkage :
    PerfectPathPacking G
      ((T.connector i j hij).targetSet leftIndexSet)
      ((T.connector i j hij).targetSet rightIndexSet)
  leftIndex_subset : leftIndexSet ⊆ step2.leftIndexSet
  rightIndex_subset : rightIndexSet ⊆ step2.rightIndexSet
  index_disjoint : Disjoint leftIndexSet rightIndexSet
  leftIndex_card : leftIndexSet.card = w
  rightIndex_card : rightIndexSet.card = w
  sourceLeft_card :
    ((T.connector i j hij).sourceSet leftIndexSet).card = w
  sourceRight_card :
    ((T.connector i j hij).sourceSet rightIndexSet).card = w
  targetLeft_card :
    ((T.connector i j hij).targetSet leftIndexSet).card = w
  targetRight_card :
    ((T.connector i j hij).targetSet rightIndexSet).card = w
  sourceReserve_disjoint :
    Disjoint ((T.connector i j hij).sourceSet leftIndexSet)
      ((T.connector i j hij).sourceSet rightIndexSet)
  targetReserve_disjoint :
    Disjoint ((T.connector i j hij).targetSet leftIndexSet)
      ((T.connector i j hij).targetSet rightIndexSet)
  sourceLinkage_card : sourceLinkage.card = w
  targetLinkage_card : targetLinkage.card = w
  sourceLinkage_staysIn : sourceLinkage.toPathPacking.StaysIn (T.cluster i)
  targetLinkage_staysIn : targetLinkage.toPathPacking.StaysIn (T.cluster j)

/-- The left restricted parent-to-leaf connector in a coherent width package. -/
noncomputable def SelectedLeafConnectorCoherentWidthData.leftRestrictedPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    PerfectPathPacking G
      ((T.connector i j hij).sourceSet D.leftIndexSet)
      ((T.connector i j hij).targetSet D.leftIndexSet) :=
  (T.connector i j hij).restrictIndexSet D.leftIndexSet

/-- The right restricted parent-to-leaf connector in a coherent width package. -/
noncomputable def SelectedLeafConnectorCoherentWidthData.rightRestrictedPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    PerfectPathPacking G
      ((T.connector i j hij).sourceSet D.rightIndexSet)
      ((T.connector i j hij).targetSet D.rightIndexSet) :=
  (T.connector i j hij).restrictIndexSet D.rightIndexSet

@[simp] theorem SelectedLeafConnectorCoherentWidthData.leftRestrictedPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    D.leftRestrictedPacking.card = w := by
  dsimp [SelectedLeafConnectorCoherentWidthData.leftRestrictedPacking]
  simp [D.leftIndex_card]

@[simp] theorem SelectedLeafConnectorCoherentWidthData.rightRestrictedPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    D.rightRestrictedPacking.card = w := by
  dsimp [SelectedLeafConnectorCoherentWidthData.rightRestrictedPacking]
  simp [D.rightIndex_card]

/-- The left restricted parent-to-leaf connector stays inside the full
connector vertex set. -/
theorem SelectedLeafConnectorCoherentWidthData.leftRestrictedPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    D.leftRestrictedPacking.toPathPacking.StaysIn
      (T.connector i j hij).toPathPacking.vertexSet := by
  dsimp [SelectedLeafConnectorCoherentWidthData.leftRestrictedPacking]
  exact (T.connector i j hij).restrictIndexSet_staysIn_vertexSet D.leftIndexSet

/-- The right restricted parent-to-leaf connector stays inside the full
connector vertex set. -/
theorem SelectedLeafConnectorCoherentWidthData.rightRestrictedPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    D.rightRestrictedPacking.toPathPacking.StaysIn
      (T.connector i j hij).toPathPacking.vertexSet := by
  dsimp [SelectedLeafConnectorCoherentWidthData.rightRestrictedPacking]
  exact (T.connector i j hij).restrictIndexSet_staysIn_vertexSet D.rightIndexSet

/-- The left restricted parent-to-leaf connector is internally disjoint from
every cluster. -/
theorem SelectedLeafConnectorCoherentWidthData.leftRestrictedPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) (c : Fin m) :
    D.leftRestrictedPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [SelectedLeafConnectorCoherentWidthData.leftRestrictedPacking]
  exact (T.connector i j hij).restrictIndexSet_internallyDisjointFromSet
    D.leftIndexSet (T.connector_internally_disjoint_cluster i j hij c)

/-- The right restricted parent-to-leaf connector is internally disjoint from
every cluster. -/
theorem SelectedLeafConnectorCoherentWidthData.rightRestrictedPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) (c : Fin m) :
    D.rightRestrictedPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [SelectedLeafConnectorCoherentWidthData.rightRestrictedPacking]
  exact (T.connector i j hij).restrictIndexSet_internallyDisjointFromSet
    D.rightIndexSet (T.connector_internally_disjoint_cluster i j hij c)

/-- The left restricted connector, traversed from the leaf side back toward
its parent. -/
noncomputable def SelectedLeafConnectorCoherentWidthData.leftLeafToParentPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    PerfectPathPacking G
      ((T.connector i j hij).targetSet D.leftIndexSet)
      ((T.connector i j hij).sourceSet D.leftIndexSet) :=
  D.leftRestrictedPacking.reverse

/-- The right restricted connector, traversed from the leaf side back toward
its parent. -/
noncomputable def SelectedLeafConnectorCoherentWidthData.rightLeafToParentPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    PerfectPathPacking G
      ((T.connector i j hij).targetSet D.rightIndexSet)
      ((T.connector i j hij).sourceSet D.rightIndexSet) :=
  D.rightRestrictedPacking.reverse

@[simp] theorem SelectedLeafConnectorCoherentWidthData.leftLeafToParentPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    D.leftLeafToParentPacking.card = w := by
  dsimp [SelectedLeafConnectorCoherentWidthData.leftLeafToParentPacking]
  simp

@[simp] theorem SelectedLeafConnectorCoherentWidthData.rightLeafToParentPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    D.rightLeafToParentPacking.card = w := by
  dsimp [SelectedLeafConnectorCoherentWidthData.rightLeafToParentPacking]
  simp

/-- Reversing the left restricted connector preserves its connector-region
containment. -/
theorem SelectedLeafConnectorCoherentWidthData.leftLeafToParentPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    D.leftLeafToParentPacking.toPathPacking.StaysIn
      (T.connector i j hij).toPathPacking.vertexSet := by
  dsimp [SelectedLeafConnectorCoherentWidthData.leftLeafToParentPacking]
  exact PerfectPathPacking.reverse_staysIn D.leftRestrictedPacking
    D.leftRestrictedPacking_staysIn

/-- Reversing the right restricted connector preserves its connector-region
containment. -/
theorem SelectedLeafConnectorCoherentWidthData.rightLeafToParentPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) :
    D.rightLeafToParentPacking.toPathPacking.StaysIn
      (T.connector i j hij).toPathPacking.vertexSet := by
  dsimp [SelectedLeafConnectorCoherentWidthData.rightLeafToParentPacking]
  exact PerfectPathPacking.reverse_staysIn D.rightRestrictedPacking
    D.rightRestrictedPacking_staysIn

/-- Reversing the left restricted connector preserves cluster internal
disjointness. -/
theorem SelectedLeafConnectorCoherentWidthData.leftLeafToParentPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) (c : Fin m) :
    D.leftLeafToParentPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [SelectedLeafConnectorCoherentWidthData.leftLeafToParentPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet
    D.leftRestrictedPacking
    (D.leftRestrictedPacking_internallyDisjoint_clusters c)

/-- Reversing the right restricted connector preserves cluster internal
disjointness. -/
theorem SelectedLeafConnectorCoherentWidthData.rightLeafToParentPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w) (c : Fin m) :
    D.rightLeafToParentPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [SelectedLeafConnectorCoherentWidthData.rightLeafToParentPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet
    D.rightRestrictedPacking
    (D.rightRestrictedPacking_internallyDisjoint_clusters c)

/-- The coherent target-side endpoint sets on one connector form the
one-cluster strong path-of-sets system used as the leaf base case of Step 2. -/
noncomputable def SelectedLeafConnectorCoherentWidthData.toTargetSingletonStrongPath
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    {w : ℕ} (D : SelectedLeafConnectorCoherentWidthData S hij w)
    (hw : 0 < w) :
    StrongPathOfSetsSystem G 1 w where
  length_pos := by omega
  width_pos := hw
  cluster := fun _ => T.cluster j
  cluster_connected := fun _ => T.cluster_connected j
  cluster_disjoint := by
    intro a b hne
    exact False.elim (hne (Subsingleton.elim a b))
  left := fun _ => (T.connector i j hij).targetSet D.leftIndexSet
  right := fun _ => (T.connector i j hij).targetSet D.rightIndexSet
  left_subset_cluster := by
    intro _
    exact subset_trans
      ((T.connector i j hij).targetSet_subset_right D.leftIndexSet)
      (T.interface_subset_cluster j i (T.metaTree.symm hij))
  right_subset_cluster := by
    intro _
    exact subset_trans
      ((T.connector i j hij).targetSet_subset_right D.rightIndexSet)
      (T.interface_subset_cluster j i (T.metaTree.symm hij))
  left_right_disjoint := by
    intro _
    exact D.targetReserve_disjoint
  left_card := by
    intro _
    exact D.targetLeft_card
  right_card := by
    intro _
    exact D.targetRight_card
  connector := by
    intro a ha
    have hfalse : False := by omega
    exact False.elim hfalse
  connector_card := by
    intro a ha
    have hfalse : False := by omega
    exact False.elim hfalse
  connector_internally_disjoint_clusters := by
    intro a ha b
    have hfalse : False := by omega
    exact False.elim hfalse
  connector_mutually_nodeDisjoint := by
    intro a b ha hb hne
    have hfalse : False := by omega
    exact False.elim hfalse
  left_nodeWellLinked := by
    intro _
    exact NodeWellLinkedIn.mono_terminals
      (T.interface_nodeWellLinked j i (T.metaTree.symm hij))
      ((T.connector i j hij).targetSet_subset_right D.leftIndexSet)
  right_nodeWellLinked := by
    intro _
    exact NodeWellLinkedIn.mono_terminals
      (T.interface_nodeWellLinked j i (T.metaTree.symm hij))
      ((T.connector i j hij).targetSet_subset_right D.rightIndexSet)
  left_right_nodeLinked := by
    intro _
    exact NodeWellLinkedIn.nodeLinkedIn_between_disjoint_subsets
      (T.interface_nodeWellLinked j i (T.metaTree.symm hij))
      ((T.connector i j hij).targetSet_subset_right D.leftIndexSet)
      ((T.connector i j hij).targetSet_subset_right D.rightIndexSet)
      D.targetReserve_disjoint

/-- A coherent half-width Step 2 package can be trimmed to a coherent
width-`w` package. -/
theorem SelectedLeafConnectorCoherentStep2Data.exists_widthData
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    (D : SelectedLeafConnectorCoherentStep2Data S hij)
    {w : ℕ} (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W) :
    Nonempty (SelectedLeafConnectorCoherentWidthData S hij w) := by
  let P := T.connector i j hij
  have hw_half : w ≤ W / (2 * ell) :=
    theorem46_width_le_halfWidth_reserve (W := W) (ell := ell) (w := w) hell hW
  have hw_left : w ≤ D.leftIndexSet.card := by
    simpa [D.leftIndex_card] using hw_half
  rcases Finset.exists_subset_card_eq hw_left with
    ⟨leftIndexSet, hleft_subset, hleft_card⟩
  let sourceLeft : Finset V := P.sourceSet leftIndexSet
  have hsourceLeft_subset :
      sourceLeft ⊆ P.sourceSet D.leftIndexSet := by
    dsimp [sourceLeft]
    exact P.sourceSet_mono hleft_subset
  let sourceLinkageIndexSet :
      Finset D.sourceLinkage.Index :=
    D.sourceLinkage.sourceIndexSetOfSubset sourceLeft
  let sourceRight : Finset V :=
    D.sourceLinkage.targetSet sourceLinkageIndexSet
  have hsourceRight_subset :
      sourceRight ⊆ P.sourceSet D.rightIndexSet := by
    dsimp [sourceRight, sourceLinkageIndexSet]
    exact D.sourceLinkage.targetSet_subset_right _
  have hsourceRight_subset_interface :
      sourceRight ⊆ T.interface i j hij :=
    subset_trans hsourceRight_subset (P.sourceSet_subset_left D.rightIndexSet)
  let rightIndexSet : Finset P.Index :=
    P.sourceIndexSetOfSubset sourceRight
  have hright_subset : rightIndexSet ⊆ D.rightIndexSet := by
    dsimp [rightIndexSet]
    exact P.sourceIndexSetOfSubset_subset_indexSet hsourceRight_subset
  have hsourceLeft_card : sourceLeft.card = w := by
    dsimp [sourceLeft]
    simp [hleft_card]
  have hsourceLinkageIndex_card : sourceLinkageIndexSet.card = w := by
    dsimp [sourceLinkageIndexSet]
    simpa [hsourceLeft_card] using
      D.sourceLinkage.sourceIndexSetOfSubset_card hsourceLeft_subset
  have hsourceRight_card : sourceRight.card = w := by
    dsimp [sourceRight]
    rw [D.sourceLinkage.targetSet_card sourceLinkageIndexSet]
    exact hsourceLinkageIndex_card
  have hright_card : rightIndexSet.card = w := by
    dsimp [rightIndexSet]
    simpa [hsourceRight_card] using
      P.sourceIndexSetOfSubset_card hsourceRight_subset_interface
  have hsourceRight_eq :
      P.sourceSet rightIndexSet = sourceRight := by
    dsimp [rightIndexSet]
    exact P.sourceSet_sourceIndexSetOfSubset hsourceRight_subset_interface
  let sourceLinkageWidth :
      PerfectPathPacking G (P.sourceSet leftIndexSet) (P.sourceSet rightIndexSet) :=
    (D.sourceLinkage.restrictSourceSet sourceLeft hsourceLeft_subset).copyTerminals
      (by rfl) hsourceRight_eq.symm
  have hsourceLinkageWidth_card : sourceLinkageWidth.card = w := by
    dsimp [sourceLinkageWidth]
    rw [PerfectPathPacking.restrictSourceSet_card]
    exact hsourceLeft_card
  have hsourceLinkageWidth_stays :
      sourceLinkageWidth.toPathPacking.StaysIn (T.cluster i) := by
    dsimp [sourceLinkageWidth]
    exact PerfectPathPacking.copyTerminals_staysIn
      (D.sourceLinkage.restrictSourceSet sourceLeft hsourceLeft_subset)
      (by rfl) hsourceRight_eq.symm
      (D.sourceLinkage.restrictSourceSet_staysIn
        sourceLeft hsourceLeft_subset D.sourceLinkage_staysIn)
  have hindexDisj : Disjoint leftIndexSet rightIndexSet := by
    rw [Finset.disjoint_left]
    intro x hxL hxR
    exact Finset.disjoint_left.mp D.index_disjoint
      (hleft_subset hxL) (hright_subset hxR)
  have hsourceDisj :
      Disjoint (P.sourceSet leftIndexSet) (P.sourceSet rightIndexSet) :=
    P.sourceSet_disjoint hindexDisj
  have htargetDisj :
      Disjoint (P.targetSet leftIndexSet) (P.targetSet rightIndexSet) :=
    P.targetSet_disjoint hindexDisj
  have htargetLeft_interface :
      P.targetSet leftIndexSet ⊆ T.interface j i (T.metaTree.symm hij) :=
    P.targetSet_subset_right leftIndexSet
  have htargetRight_interface :
      P.targetSet rightIndexSet ⊆ T.interface j i (T.metaTree.symm hij) :=
    P.targetSet_subset_right rightIndexSet
  have htargetLeft_card : (P.targetSet leftIndexSet).card = w := by
    simp [hleft_card]
  have htargetRight_card : (P.targetSet rightIndexSet).card = w := by
    simp [hright_card]
  have htargetCardEq :
      (P.targetSet leftIndexSet).card = (P.targetSet rightIndexSet).card :=
    htargetLeft_card.trans htargetRight_card.symm
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      (T.metaTree.symm hij) htargetLeft_interface htargetRight_interface
      htargetDisj htargetCardEq with
    ⟨targetLinkage, htargetLinkageCard, htargetLinkageStay⟩
  exact ⟨{
    step2 := D
    leftIndexSet := leftIndexSet
    rightIndexSet := rightIndexSet
    sourceLinkage := sourceLinkageWidth
    targetLinkage := targetLinkage
    leftIndex_subset := hleft_subset
    rightIndex_subset := hright_subset
    index_disjoint := hindexDisj
    leftIndex_card := hleft_card
    rightIndex_card := hright_card
    sourceLeft_card := by simpa using hleft_card
    sourceRight_card := by simpa using hright_card
    targetLeft_card := by simpa using hleft_card
    targetRight_card := by simpa using hright_card
    sourceReserve_disjoint := hsourceDisj
    targetReserve_disjoint := htargetDisj
    sourceLinkage_card := hsourceLinkageWidth_card
    targetLinkage_card := htargetLinkageCard.trans htargetLeft_card
    sourceLinkage_staysIn := hsourceLinkageWidth_stays
    targetLinkage_staysIn := htargetLinkageStay }⟩

/-- Step 2 reserves can be trimmed to the final width `w` under the theorem's
width hypothesis. -/
theorem SelectedLeafConnectorStep2Data.exists_widthData
    {S : Theorem46LeafExtractionSetup T ell}
    {i j : Fin m} {hij : T.metaTree.Adj i j}
    (D : SelectedLeafConnectorStep2Data S hij)
    {w : ℕ} (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W) :
    Nonempty (SelectedLeafConnectorWidthData S hij w) := by
  rcases exists_subset_card_theorem46_width_from_half_reserve
      (A := D.sourceReserveLeft) hell hW D.sourceReserveLeft_card with
    ⟨sourceLeft, hsourceLeft_subset, hsourceLeft_card⟩
  rcases exists_subset_card_theorem46_width_from_half_reserve
      (A := D.sourceReserveRight) hell hW D.sourceReserveRight_card with
    ⟨sourceRight, hsourceRight_subset, hsourceRight_card⟩
  rcases exists_subset_card_theorem46_width_from_half_reserve
      (A := D.targetReserveLeft) hell hW D.targetReserveLeft_card with
    ⟨targetLeft, htargetLeft_subset, htargetLeft_card⟩
  rcases exists_subset_card_theorem46_width_from_half_reserve
      (A := D.targetReserveRight) hell hW D.targetReserveRight_card with
    ⟨targetRight, htargetRight_subset, htargetRight_card⟩
  exact ⟨{
    step2 := D
    sourceLeft := sourceLeft
    sourceRight := sourceRight
    targetLeft := targetLeft
    targetRight := targetRight
    sourceLeft_subset := hsourceLeft_subset
    sourceRight_subset := hsourceRight_subset
    targetLeft_subset := htargetLeft_subset
    targetRight_subset := htargetRight_subset
    sourceLeft_card := hsourceLeft_card
    sourceRight_card := hsourceRight_card
    targetLeft_card := htargetLeft_card
    targetRight_card := htargetRight_card }⟩

/-- A selected-leaf connector admits the full Step 2 reserve/linkage package
with one common retained connector subfamily. -/
theorem exists_selectedLeafConnectorStep2Data
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    Nonempty (SelectedLeafConnectorStep2Data S hij) := by
  rcases S.exists_connector_selection_for_selected_leaf hij hleaf with
    ⟨I, hIcard, hsource, htarget, hrestrict⟩
  rcases exists_two_disjoint_subsets_card_theorem46_half_count
      (A := (T.connector i j hij).sourceSet I) (W := W) (ell := ell)
      hell hsource with
    ⟨sourceLeft, sourceRight, hsourceLeft, hsourceRight, hsourceDisj,
      hsourceLeftCard, hsourceRightCard⟩
  rcases exists_two_disjoint_subsets_card_theorem46_half_count
      (A := (T.connector i j hij).targetSet I) (W := W) (ell := ell)
      hell htarget with
    ⟨targetLeft, targetRight, htargetLeft, htargetRight, htargetDisj,
      htargetLeftCard, htargetRightCard⟩
  have hsource_subset :
      (T.connector i j hij).sourceSet I ⊆ T.interface i j hij :=
    (T.connector i j hij).sourceSet_subset_left I
  have htarget_subset :
      (T.connector i j hij).targetSet I ⊆
        T.interface j i (T.metaTree.symm hij) :=
    (T.connector i j hij).targetSet_subset_right I
  have hsourceLeft_interface : sourceLeft ⊆ T.interface i j hij :=
    subset_trans hsourceLeft hsource_subset
  have hsourceRight_interface : sourceRight ⊆ T.interface i j hij :=
    subset_trans hsourceRight hsource_subset
  have htargetLeft_interface :
      targetLeft ⊆ T.interface j i (T.metaTree.symm hij) :=
    subset_trans htargetLeft htarget_subset
  have htargetRight_interface :
      targetRight ⊆ T.interface j i (T.metaTree.symm hij) :=
    subset_trans htargetRight htarget_subset
  have hsourceCardEq : sourceLeft.card = sourceRight.card :=
    hsourceLeftCard.trans hsourceRightCard.symm
  have htargetCardEq : targetLeft.card = targetRight.card :=
    htargetLeftCard.trans htargetRightCard.symm
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      hij hsourceLeft_interface hsourceRight_interface hsourceDisj
      hsourceCardEq with
    ⟨sourceLinkage, hsourceLinkageCard, hsourceLinkageStay⟩
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      (T.metaTree.symm hij) htargetLeft_interface htargetRight_interface
      htargetDisj htargetCardEq with
    ⟨targetLinkage, htargetLinkageCard, htargetLinkageStay⟩
  exact ⟨{
    indexSet := I
    sourceReserveLeft := sourceLeft
    sourceReserveRight := sourceRight
    targetReserveLeft := targetLeft
    targetReserveRight := targetRight
    sourceLinkage := sourceLinkage
    targetLinkage := targetLinkage
    index_card := hIcard
    source_card := hsource
    target_card := htarget
    restricted_card := hrestrict
    sourceReserveLeft_subset := hsourceLeft
    sourceReserveRight_subset := hsourceRight
    targetReserveLeft_subset := htargetLeft
    targetReserveRight_subset := htargetRight
    sourceReserve_disjoint := hsourceDisj
    targetReserve_disjoint := htargetDisj
    sourceReserveLeft_card := hsourceLeftCard
    sourceReserveRight_card := hsourceRightCard
    targetReserveLeft_card := htargetLeftCard
    targetReserveRight_card := htargetRightCard
    sourceLinkage_card := hsourceLinkageCard.trans hsourceLeftCard
    targetLinkage_card := htargetLinkageCard.trans htargetLeftCard
    sourceLinkage_staysIn := hsourceLinkageStay
    targetLinkage_staysIn := htargetLinkageStay
    restricted_staysIn :=
      (T.connector i j hij).restrictIndexSet_staysIn_vertexSet I
    restricted_internallyDisjoint_clusters := by
      intro r
      exact (T.connector i j hij).restrictIndexSet_internallyDisjointFromSet I
        (T.connector_internally_disjoint_cluster i j hij r) }⟩

/-- A selected-leaf connector admits the Step 2 package trimmed to the final
width `w`. -/
theorem exists_selectedLeafConnectorWidthData
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves)
    {w : ℕ} (hW : 16 * w * ell ^ 2 + 1 < W) :
    Nonempty (SelectedLeafConnectorWidthData S hij w) := by
  rcases S.exists_selectedLeafConnectorStep2Data hell hij hleaf with ⟨D⟩
  exact D.exists_widthData hell hW

/-- A selected-leaf connector admits coherent Step 2 data: the two half-width
bundles are matched source/target endpoint sets of disjoint connector
subfamilies. -/
theorem exists_selectedLeafConnectorCoherentStep2Data
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    Nonempty (SelectedLeafConnectorCoherentStep2Data S hij) := by
  rcases S.exists_connector_selection_for_selected_leaf hij hleaf with
    ⟨I, hIcard, _hsource, _htarget, _hrestrict⟩
  rcases exists_two_disjoint_subsets_card_theorem46_half_count
      (A := I) (W := W) (ell := ell) hell hIcard with
    ⟨leftIndexSet, rightIndexSet, hleft_subset, hright_subset, hdisj,
      hleft_card, hright_card⟩
  let P := T.connector i j hij
  have hsourceLeft_interface :
      P.sourceSet leftIndexSet ⊆ T.interface i j hij :=
    P.sourceSet_subset_left leftIndexSet
  have hsourceRight_interface :
      P.sourceSet rightIndexSet ⊆ T.interface i j hij :=
    P.sourceSet_subset_left rightIndexSet
  have htargetLeft_interface :
      P.targetSet leftIndexSet ⊆ T.interface j i (T.metaTree.symm hij) :=
    P.targetSet_subset_right leftIndexSet
  have htargetRight_interface :
      P.targetSet rightIndexSet ⊆ T.interface j i (T.metaTree.symm hij) :=
    P.targetSet_subset_right rightIndexSet
  have hsourceDisj :
      Disjoint (P.sourceSet leftIndexSet) (P.sourceSet rightIndexSet) :=
    P.sourceSet_disjoint hdisj
  have htargetDisj :
      Disjoint (P.targetSet leftIndexSet) (P.targetSet rightIndexSet) :=
    P.targetSet_disjoint hdisj
  have hsourceCardEq :
      (P.sourceSet leftIndexSet).card = (P.sourceSet rightIndexSet).card := by
    simp [hleft_card, hright_card]
  have htargetCardEq :
      (P.targetSet leftIndexSet).card = (P.targetSet rightIndexSet).card := by
    simp [hleft_card, hright_card]
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      hij hsourceLeft_interface hsourceRight_interface hsourceDisj
      hsourceCardEq with
    ⟨sourceLinkage, hsourceLinkageCard, hsourceLinkageStay⟩
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      (T.metaTree.symm hij) htargetLeft_interface htargetRight_interface
      htargetDisj htargetCardEq with
    ⟨targetLinkage, htargetLinkageCard, htargetLinkageStay⟩
  exact ⟨{
    indexSet := I
    leftIndexSet := leftIndexSet
    rightIndexSet := rightIndexSet
    sourceLinkage := sourceLinkage
    targetLinkage := targetLinkage
    index_card := hIcard
    leftIndex_subset := hleft_subset
    rightIndex_subset := hright_subset
    index_disjoint := hdisj
    leftIndex_card := hleft_card
    rightIndex_card := hright_card
    sourceLeft_card := by simp [hleft_card]
    sourceRight_card := by simp [hright_card]
    targetLeft_card := by simp [hleft_card]
    targetRight_card := by simp [hright_card]
    sourceLeft_subset := by
      simpa [P] using P.sourceSet_mono hleft_subset
    sourceRight_subset := by
      simpa [P] using P.sourceSet_mono hright_subset
    targetLeft_subset := by
      simpa [P] using P.targetSet_mono hleft_subset
    targetRight_subset := by
      simpa [P] using P.targetSet_mono hright_subset
    sourceReserve_disjoint := by simpa [P] using hsourceDisj
    targetReserve_disjoint := by simpa [P] using htargetDisj
    sourceLinkage_card := by
      simpa [P, hleft_card] using hsourceLinkageCard
    targetLinkage_card := by
      simpa [P, hleft_card] using htargetLinkageCard
    sourceLinkage_staysIn := hsourceLinkageStay
    targetLinkage_staysIn := htargetLinkageStay }⟩

/-- A selected-leaf connector admits coherent Step 2 data trimmed to the final
width `w`. -/
theorem exists_selectedLeafConnectorCoherentWidthData
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {i j : Fin m} (hij : T.metaTree.Adj i j)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves)
    {w : ℕ} (hW : 16 * w * ell ^ 2 + 1 < W) :
    Nonempty (SelectedLeafConnectorCoherentWidthData S hij w) := by
  rcases S.exists_selectedLeafConnectorCoherentStep2Data hell hij hleaf with ⟨D⟩
  exact D.exists_widthData hell hW

/-- The DFS root is distinct from every selected leaf. -/
theorem root_ne_selected_leaf
    (S : Theorem46LeafExtractionSetup T ell)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    S.root ≠ leaf := by
  intro hroot_leaf
  exact S.root_not_mem_leaves (by simpa [hroot_leaf] using hleaf)

/-- Reindex the selected leaves by `Fin ell`. -/
noncomputable def selectedLeafEquiv
    (S : Theorem46LeafExtractionSetup T ell) :
    S.leaves ≃ Fin ell :=
  Finset.equivFinOfCardEq S.leaves_card

/-- The `r`-th selected leaf in the chosen finite ordering. -/
noncomputable def selectedLeaf
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) : Fin m :=
  ((S.selectedLeafEquiv).symm r).1

/-- The ordered selected leaf belongs to the selected leaf set. -/
theorem selectedLeaf_mem
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    S.selectedLeaf r ∈ S.leaves :=
  ((S.selectedLeafEquiv).symm r).2

/-- If more than one selected leaf is kept, the distinguished root child cannot
itself be one of the selected leaves. -/
theorem child_not_mem_leaves_of_one_lt_length
    (S : Theorem46LeafExtractionSetup T ell) (hell : 1 < ell) :
    S.child ∉ S.leaves := by
  intro hchild
  have hchild_card :
      (selectedMetaLeafDescendants T S.root S.leaves S.child).card = 1 :=
    S.descendants_leaf_card hchild
  have hroot_child_card :
      (selectedMetaLeafDescendants T S.root S.leaves S.child).card = ell :=
    S.descendants_root_child_card
  have hell_eq_one : ell = 1 := hroot_child_card.symm.trans hchild_card
  omega

/-- The `r`-th selected leaf as an element of the selected-leaf subtype. -/
noncomputable def selectedLeafSubtype
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    {x : Fin m // x ∈ S.leaves} :=
  ⟨S.selectedLeaf r, S.selectedLeaf_mem r⟩

/-- The ordered selected leaves are pairwise distinct. -/
theorem selectedLeaf_injective
    (S : Theorem46LeafExtractionSetup T ell) :
    Function.Injective S.selectedLeaf := by
  intro r s hrs
  apply S.selectedLeafEquiv.symm.injective
  exact Subtype.ext hrs

/-- The selected leaf `r`, viewed as a descendant below the distinguished
root-child edge. -/
noncomputable def rootChildSelectedLeafDescendant
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    selectedMetaLeafDescendants T S.root S.leaves S.child :=
  ⟨S.selectedLeaf r, by
    rw [S.descendants_root_child_eq]
    exact S.selectedLeaf_mem r⟩

/-- A shared descendant-tranche package on the distinguished root-child edge. -/
noncomputable def rootChildDescendantTrancheData
    (S : Theorem46LeafExtractionSetup T ell) :
    ConnectorDescendantTrancheData S S.root_child_adj S.child :=
  Classical.choice (S.exists_connectorDescendantTrancheData S.root_child_adj S.child)

/-- The root-child tranche assigned to a selected leaf, using the shared
root-child descendant-tranche package. -/
noncomputable def rootChildSelectedLeafTranche
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    Finset (T.connector S.root S.child S.root_child_adj).Index :=
  (S.rootChildDescendantTrancheData).tranche
    (S.rootChildSelectedLeafDescendant r)

@[simp] theorem rootChildSelectedLeafTranche_card
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    (S.rootChildSelectedLeafTranche r).card = W / ell := by
  dsimp [rootChildSelectedLeafTranche]
  exact (S.rootChildDescendantTrancheData).tranche_card
    (S.rootChildSelectedLeafDescendant r)

@[simp] theorem rootChildSelectedLeafTranche_source_card
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    ((T.connector S.root S.child S.root_child_adj).sourceSet
      (S.rootChildSelectedLeafTranche r)).card = W / ell := by
  dsimp [rootChildSelectedLeafTranche]
  exact (S.rootChildDescendantTrancheData).tranche_source_card
    (S.rootChildSelectedLeafDescendant r)

@[simp] theorem rootChildSelectedLeafTranche_target_card
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    ((T.connector S.root S.child S.root_child_adj).targetSet
      (S.rootChildSelectedLeafTranche r)).card = W / ell := by
  dsimp [rootChildSelectedLeafTranche]
  exact (S.rootChildDescendantTrancheData).tranche_target_card
    (S.rootChildSelectedLeafDescendant r)

/-- Distinct selected leaves receive disjoint tranches on the shared root-child
edge. -/
theorem rootChildSelectedLeafTranche_pairwise_disjoint
    (S : Theorem46LeafExtractionSetup T ell)
    {r s : Fin ell} (hrs : r ≠ s) :
    Disjoint (S.rootChildSelectedLeafTranche r)
      (S.rootChildSelectedLeafTranche s) := by
  dsimp [rootChildSelectedLeafTranche]
  apply (S.rootChildDescendantTrancheData).tranche_pairwise_disjoint
  intro h
  apply hrs
  have hleaf : S.selectedLeaf r = S.selectedLeaf s := by
    simpa [rootChildSelectedLeafDescendant] using congrArg Subtype.val h
  exact S.selectedLeaf_injective hleaf

/-- The selected leaf's shared root-child restricted connector packing. -/
noncomputable def rootChildSelectedLeafRestrictedPacking
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet
        (S.rootChildSelectedLeafTranche r))
      ((T.connector S.root S.child S.root_child_adj).targetSet
        (S.rootChildSelectedLeafTranche r)) :=
  (T.connector S.root S.child S.root_child_adj).restrictIndexSet
    (S.rootChildSelectedLeafTranche r)

@[simp] theorem rootChildSelectedLeafRestrictedPacking_card
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    (S.rootChildSelectedLeafRestrictedPacking r).card = W / ell := by
  dsimp [rootChildSelectedLeafRestrictedPacking, rootChildSelectedLeafTranche]
  exact (S.rootChildDescendantTrancheData).tranche_restricted_card
    (S.rootChildSelectedLeafDescendant r)

/-- The selected leaf's shared root-child restricted connector stays in the full
root-child connector vertex set. -/
theorem rootChildSelectedLeafRestrictedPacking_staysIn
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    (S.rootChildSelectedLeafRestrictedPacking r).toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [rootChildSelectedLeafRestrictedPacking, rootChildSelectedLeafTranche]
  exact (S.rootChildDescendantTrancheData).tranche_restricted_staysIn
    (S.rootChildSelectedLeafDescendant r)

/-- The selected leaf's shared root-child restricted connector is internally
disjoint from every cluster. -/
theorem rootChildSelectedLeafRestrictedPacking_internallyDisjoint_clusters
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) (c : Fin m) :
    (S.rootChildSelectedLeafRestrictedPacking r).toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [rootChildSelectedLeafRestrictedPacking, rootChildSelectedLeafTranche]
  exact (S.rootChildDescendantTrancheData).tranche_restricted_internallyDisjoint_clusters
    (S.rootChildSelectedLeafDescendant r) c

/-- Distinct selected leaves' shared root-child restricted connectors are
mutually node-disjoint. -/
theorem rootChildSelectedLeafRestrictedPacking_mutuallyNodeDisjoint
    (S : Theorem46LeafExtractionSetup T ell)
    {r s : Fin ell} (hrs : r ≠ s) :
    (S.rootChildSelectedLeafRestrictedPacking r).toPathPacking.MutuallyNodeDisjoint
      (S.rootChildSelectedLeafRestrictedPacking s).toPathPacking := by
  dsimp [rootChildSelectedLeafRestrictedPacking, rootChildSelectedLeafTranche]
  apply (S.rootChildDescendantTrancheData).tranche_restricted_mutuallyNodeDisjoint
  intro h
  apply hrs
  have hleaf : S.selectedLeaf r = S.selectedLeaf s := by
    simpa [rootChildSelectedLeafDescendant] using congrArg Subtype.val h
  exact S.selectedLeaf_injective hleaf

/-- Coherent left/right width-`w` subtranches inside the shared root-child
tranche assigned to one selected leaf.  These are the two sides later used by
the previous and next adjacent leaf-pair connectors. -/
structure RootChildSelectedLeafDoubleWidthData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) (w : ℕ) where
  leftIndexSet :
    Finset (T.connector S.root S.child S.root_child_adj).Index
  rightIndexSet :
    Finset (T.connector S.root S.child S.root_child_adj).Index
  leftIndex_subset_tranche : leftIndexSet ⊆ S.rootChildSelectedLeafTranche r
  rightIndex_subset_tranche : rightIndexSet ⊆ S.rootChildSelectedLeafTranche r
  leftIndex_card : leftIndexSet.card = w
  rightIndex_card : rightIndexSet.card = w
  index_disjoint : Disjoint leftIndexSet rightIndexSet
  sourceLeft_card :
    ((T.connector S.root S.child S.root_child_adj).sourceSet leftIndexSet).card =
      w
  sourceRight_card :
    ((T.connector S.root S.child S.root_child_adj).sourceSet rightIndexSet).card =
      w
  targetLeft_card :
    ((T.connector S.root S.child S.root_child_adj).targetSet leftIndexSet).card =
      w
  targetRight_card :
    ((T.connector S.root S.child S.root_child_adj).targetSet rightIndexSet).card =
      w
  source_disjoint :
    Disjoint
      ((T.connector S.root S.child S.root_child_adj).sourceSet leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet rightIndexSet)
  target_disjoint :
    Disjoint
      ((T.connector S.root S.child S.root_child_adj).targetSet leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet rightIndexSet)
  leftRestricted_staysIn :
    ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
      leftIndexSet).toPathPacking.StaysIn
        (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  rightRestricted_staysIn :
    ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
      rightIndexSet).toPathPacking.StaysIn
        (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  leftRestricted_internallyDisjoint_clusters :
    ∀ c : Fin m,
      ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
        leftIndexSet).toPathPacking.InternallyDisjointFromSet (T.cluster c)
  rightRestricted_internallyDisjoint_clusters :
    ∀ c : Fin m,
      ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
        rightIndexSet).toPathPacking.InternallyDisjointFromSet (T.cluster c)

/-- Every selected leaf's shared root-child tranche contains two disjoint
width-`w` subtranches under the Theorem 4.6 width hypothesis. -/
theorem exists_rootChildSelectedLeafDoubleWidthData
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {w : ℕ} (hW : 16 * w * ell ^ 2 + 1 < W)
    (r : Fin ell) :
    Nonempty (RootChildSelectedLeafDoubleWidthData S r w) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  rcases exists_two_disjoint_subsets_card_theorem46_half_count
      (A := S.rootChildSelectedLeafTranche r) (W := W) (ell := ell)
      hell (S.rootChildSelectedLeafTranche_card r) with
    ⟨leftHalf, rightHalf, hleftHalf_subset, hrightHalf_subset,
      hhalf_disjoint, hleftHalf_card, hrightHalf_card⟩
  have hw_half : w ≤ W / (2 * ell) :=
    theorem46_width_le_halfWidth_reserve (W := W) (ell := ell) (w := w)
      hell hW
  have hw_leftHalf : w ≤ leftHalf.card := by
    simpa [hleftHalf_card] using hw_half
  have hw_rightHalf : w ≤ rightHalf.card := by
    simpa [hrightHalf_card] using hw_half
  rcases Finset.exists_subset_card_eq hw_leftHalf with
    ⟨leftIndexSet, hleft_subset_half, hleft_card⟩
  rcases Finset.exists_subset_card_eq hw_rightHalf with
    ⟨rightIndexSet, hright_subset_half, hright_card⟩
  have hleft_subset :
      leftIndexSet ⊆ S.rootChildSelectedLeafTranche r :=
    subset_trans hleft_subset_half hleftHalf_subset
  have hright_subset :
      rightIndexSet ⊆ S.rootChildSelectedLeafTranche r :=
    subset_trans hright_subset_half hrightHalf_subset
  have hindex_disjoint : Disjoint leftIndexSet rightIndexSet := by
    rw [Finset.disjoint_left]
    intro x hxleft hxright
    exact Finset.disjoint_left.mp hhalf_disjoint
      (hleft_subset_half hxleft) (hright_subset_half hxright)
  have hsourceLeft_card : (P.sourceSet leftIndexSet).card = w := by
    simp [P, hleft_card]
  have hsourceRight_card : (P.sourceSet rightIndexSet).card = w := by
    simp [P, hright_card]
  have htargetLeft_card : (P.targetSet leftIndexSet).card = w := by
    simp [P, hleft_card]
  have htargetRight_card : (P.targetSet rightIndexSet).card = w := by
    simp [P, hright_card]
  exact ⟨{
    leftIndexSet := leftIndexSet
    rightIndexSet := rightIndexSet
    leftIndex_subset_tranche := hleft_subset
    rightIndex_subset_tranche := hright_subset
    leftIndex_card := hleft_card
    rightIndex_card := hright_card
    index_disjoint := hindex_disjoint
    sourceLeft_card := by simpa [P] using hsourceLeft_card
    sourceRight_card := by simpa [P] using hsourceRight_card
    targetLeft_card := by simpa [P] using htargetLeft_card
    targetRight_card := by simpa [P] using htargetRight_card
    source_disjoint := by
      simpa [P] using P.sourceSet_disjoint hindex_disjoint
    target_disjoint := by
      simpa [P] using P.targetSet_disjoint hindex_disjoint
    leftRestricted_staysIn :=
      P.restrictIndexSet_staysIn_vertexSet leftIndexSet
    rightRestricted_staysIn :=
      P.restrictIndexSet_staysIn_vertexSet rightIndexSet
    leftRestricted_internallyDisjoint_clusters := by
      intro c
      exact P.restrictIndexSet_internallyDisjointFromSet leftIndexSet
        (T.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj c)
    rightRestricted_internallyDisjoint_clusters := by
      intro c
      exact P.restrictIndexSet_internallyDisjointFromSet rightIndexSet
        (T.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj c) }⟩

/-- The coherent left root-child subtranche as a restricted connector. -/
noncomputable def RootChildSelectedLeafDoubleWidthData.leftRestrictedPacking
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet D.leftIndexSet) :=
  (T.connector S.root S.child S.root_child_adj).restrictIndexSet D.leftIndexSet

/-- The coherent right root-child subtranche as a restricted connector. -/
noncomputable def RootChildSelectedLeafDoubleWidthData.rightRestrictedPacking
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet D.rightIndexSet) :=
  (T.connector S.root S.child S.root_child_adj).restrictIndexSet D.rightIndexSet

@[simp] theorem RootChildSelectedLeafDoubleWidthData.leftRestrictedPacking_card
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    D.leftRestrictedPacking.card = w := by
  dsimp [RootChildSelectedLeafDoubleWidthData.leftRestrictedPacking]
  simp [D.leftIndex_card]

@[simp] theorem RootChildSelectedLeafDoubleWidthData.rightRestrictedPacking_card
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    D.rightRestrictedPacking.card = w := by
  dsimp [RootChildSelectedLeafDoubleWidthData.rightRestrictedPacking]
  simp [D.rightIndex_card]

/-- The coherent left restricted root-child connector stays in the full
root-child connector region. -/
theorem RootChildSelectedLeafDoubleWidthData.leftRestrictedPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    D.leftRestrictedPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildSelectedLeafDoubleWidthData.leftRestrictedPacking]
  exact D.leftRestricted_staysIn

/-- The coherent right restricted root-child connector stays in the full
root-child connector region. -/
theorem RootChildSelectedLeafDoubleWidthData.rightRestrictedPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    D.rightRestrictedPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildSelectedLeafDoubleWidthData.rightRestrictedPacking]
  exact D.rightRestricted_staysIn

/-- The coherent left restricted root-child connector is internally disjoint
from every cluster. -/
theorem RootChildSelectedLeafDoubleWidthData.leftRestrictedPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) (c : Fin m) :
    D.leftRestrictedPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildSelectedLeafDoubleWidthData.leftRestrictedPacking]
  exact D.leftRestricted_internallyDisjoint_clusters c

/-- The coherent right restricted root-child connector is internally disjoint
from every cluster. -/
theorem RootChildSelectedLeafDoubleWidthData.rightRestrictedPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) (c : Fin m) :
    D.rightRestrictedPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildSelectedLeafDoubleWidthData.rightRestrictedPacking]
  exact D.rightRestricted_internallyDisjoint_clusters c

/-- The coherent left root-child subtranche traversed from the child side back
to the root side. -/
noncomputable def RootChildSelectedLeafDoubleWidthData.leftChildToRootPacking
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet D.leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.leftIndexSet) :=
  D.leftRestrictedPacking.reverse

/-- The coherent right root-child subtranche traversed from the child side back
to the root side. -/
noncomputable def RootChildSelectedLeafDoubleWidthData.rightChildToRootPacking
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet D.rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.rightIndexSet) :=
  D.rightRestrictedPacking.reverse

@[simp] theorem RootChildSelectedLeafDoubleWidthData.leftChildToRootPacking_card
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    D.leftChildToRootPacking.card = w := by
  dsimp [RootChildSelectedLeafDoubleWidthData.leftChildToRootPacking]
  simp

@[simp] theorem RootChildSelectedLeafDoubleWidthData.rightChildToRootPacking_card
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    D.rightChildToRootPacking.card = w := by
  dsimp [RootChildSelectedLeafDoubleWidthData.rightChildToRootPacking]
  simp

/-- Reversing the coherent left root-child connector preserves containment. -/
theorem RootChildSelectedLeafDoubleWidthData.leftChildToRootPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    D.leftChildToRootPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildSelectedLeafDoubleWidthData.leftChildToRootPacking]
  exact PerfectPathPacking.reverse_staysIn D.leftRestrictedPacking
    D.leftRestrictedPacking_staysIn

/-- Reversing the coherent right root-child connector preserves containment. -/
theorem RootChildSelectedLeafDoubleWidthData.rightChildToRootPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    D.rightChildToRootPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildSelectedLeafDoubleWidthData.rightChildToRootPacking]
  exact PerfectPathPacking.reverse_staysIn D.rightRestrictedPacking
    D.rightRestrictedPacking_staysIn

/-- Reversing the coherent left root-child connector preserves cluster internal
disjointness. -/
theorem RootChildSelectedLeafDoubleWidthData.leftChildToRootPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) (c : Fin m) :
    D.leftChildToRootPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildSelectedLeafDoubleWidthData.leftChildToRootPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet
    D.leftRestrictedPacking
    (D.leftRestrictedPacking_internallyDisjoint_clusters c)

/-- Reversing the coherent right root-child connector preserves cluster
internal disjointness. -/
theorem RootChildSelectedLeafDoubleWidthData.rightChildToRootPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w) (c : Fin m) :
    D.rightChildToRootPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildSelectedLeafDoubleWidthData.rightChildToRootPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet
    D.rightRestrictedPacking
    (D.rightRestrictedPacking_internallyDisjoint_clusters c)

/-- No ordered selected leaf is the DFS root. -/
theorem selectedLeaf_ne_root
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    S.selectedLeaf r ≠ S.root := by
  intro hleaf_root
  have hmem : S.selectedLeaf r ∈ S.leaves := S.selectedLeaf_mem r
  rw [hleaf_root] at hmem
  exact S.root_not_mem_leaves hmem

/-- If more than one selected leaf is kept, no ordered selected leaf is the
distinguished child of the DFS root. -/
theorem selectedLeaf_ne_child_of_one_lt_length
    (S : Theorem46LeafExtractionSetup T ell) (hell : 1 < ell)
    (r : Fin ell) :
    S.selectedLeaf r ≠ S.child := by
  intro hleaf_child
  exact S.child_not_mem_leaves_of_one_lt_length hell
    (by simpa [hleaf_child] using S.selectedLeaf_mem r)

/-- Every ordered selected leaf is a meta-tree leaf. -/
theorem selectedLeaf_leaf
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    DegreeEquals T.metaTree (S.selectedLeaf r) 1 :=
  S.leaves_leaf (S.selectedLeaf r) (S.selectedLeaf_mem r)

/-- A chosen meta-tree path from the DFS root to an ordered selected leaf. -/
noncomputable def selectedLeafMetaPath
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    T.metaTree.Path S.root (S.selectedLeaf r) :=
  let h := (T.meta_isTree.connected S.root (S.selectedLeaf r)).exists_path_of_dist
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

/-- The chosen selected-leaf meta-path is a simple path. -/
theorem selectedLeafMetaPath_isPath
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    (S.selectedLeafMetaPath r : T.metaTree.Walk S.root (S.selectedLeaf r)).IsPath :=
  (S.selectedLeafMetaPath r).2

/-- The length of the chosen root-to-selected-leaf meta-path. -/
noncomputable def selectedLeafMetaPathLength
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) : ℕ :=
  (S.selectedLeafMetaPath r : T.metaTree.Walk S.root (S.selectedLeaf r)).length

/-- The chosen root-to-selected-leaf meta-path is nonempty. -/
theorem selectedLeafMetaPathLength_pos
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    0 < S.selectedLeafMetaPathLength r := by
  let p : T.metaTree.Walk S.root (S.selectedLeaf r) :=
    (S.selectedLeafMetaPath r : T.metaTree.Walk S.root (S.selectedLeaf r))
  by_contra hpos
  have hlen : p.length = 0 := Nat.eq_zero_of_not_pos hpos
  have hroot_leaf : S.root = S.selectedLeaf r := by
    calc
      S.root = p.getVert 0 := by simp
      _ = p.getVert p.length := by rw [hlen]
      _ = S.selectedLeaf r := by simp
  exact S.selectedLeaf_ne_root r hroot_leaf.symm

/-- The `a`-th vertex on the chosen root-to-selected-leaf meta-path. -/
noncomputable def selectedLeafMetaPathVertex
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) (a : ℕ) :
    Fin m :=
  (S.selectedLeafMetaPath r : T.metaTree.Walk S.root (S.selectedLeaf r)).getVert a

/-- The first edge index of a selected root-to-leaf meta-path. -/
def selectedLeafMetaPathFirstEdgeIndex
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    Fin (S.selectedLeafMetaPathLength r) :=
  ⟨0, S.selectedLeafMetaPathLength_pos r⟩

/-- The chosen root-to-selected-leaf meta-path starts at the DFS root. -/
@[simp] theorem selectedLeafMetaPathVertex_zero
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    S.selectedLeafMetaPathVertex r 0 = S.root := by
  simp [selectedLeafMetaPathVertex]

/-- The chosen root-to-selected-leaf meta-path ends at the selected leaf. -/
@[simp] theorem selectedLeafMetaPathVertex_length
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r) =
      S.selectedLeaf r := by
  simp [selectedLeafMetaPathVertex, selectedLeafMetaPathLength]

/-- Consecutive vertices on the chosen root-to-selected-leaf meta-path are
adjacent in the meta-tree. -/
theorem selectedLeafMetaPathVertex_adj_succ
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) {a : ℕ}
    (ha : a < S.selectedLeafMetaPathLength r) :
    T.metaTree.Adj (S.selectedLeafMetaPathVertex r a)
      (S.selectedLeafMetaPathVertex r (a + 1)) := by
  simpa [selectedLeafMetaPathVertex, selectedLeafMetaPathLength] using
    (S.selectedLeafMetaPath r : T.metaTree.Walk S.root
      (S.selectedLeaf r)).adj_getVert_succ (i := a) ha

/-- The first step of every selected root-to-leaf meta-path is the distinguished
root-child edge. -/
@[simp] theorem selectedLeafMetaPathVertex_one
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    S.selectedLeafMetaPathVertex r 1 = S.child := by
  have hadj :
      T.metaTree.Adj S.root (S.selectedLeafMetaPathVertex r 1) := by
    simpa using
      (S.selectedLeafMetaPathVertex_adj_succ r
        (a := 0) (S.selectedLeafMetaPathLength_pos r))
  exact S.root_child_unique (S.selectedLeafMetaPathVertex r 1) hadj

/-- With at least two selected leaves, every selected root-to-leaf meta-path has
at least two edges, so its first turn after the root-child edge exists. -/
theorem selectedLeafMetaPathLength_one_lt_of_one_lt_length
    (S : Theorem46LeafExtractionSetup T ell) (hell : 1 < ell)
    (r : Fin ell) :
    1 < S.selectedLeafMetaPathLength r := by
  by_contra hnot
  have hle : S.selectedLeafMetaPathLength r ≤ 1 := Nat.le_of_not_gt hnot
  have hpos : 0 < S.selectedLeafMetaPathLength r :=
    S.selectedLeafMetaPathLength_pos r
  have hlen : S.selectedLeafMetaPathLength r = 1 := by omega
  have hleaf_child : S.selectedLeaf r = S.child := by
    calc
      S.selectedLeaf r =
          S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r) := by
        simp
      _ = S.selectedLeafMetaPathVertex r 1 := by rw [hlen]
      _ = S.child := S.selectedLeafMetaPathVertex_one r
  exact S.selectedLeaf_ne_child_of_one_lt_length hell r hleaf_child

/-- Vertices two steps apart on the chosen simple root-to-leaf meta-path are
distinct. -/
theorem selectedLeafMetaPathVertex_ne_two_step
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) {a : ℕ}
    (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    S.selectedLeafMetaPathVertex r a ≠
      S.selectedLeafMetaPathVertex r (a + 2) := by
  intro h
  have ha_walk :
      a + 1 < (S.selectedLeafMetaPath r : T.metaTree.Walk S.root
        (S.selectedLeaf r)).length := by
    simpa [selectedLeafMetaPathLength] using ha
  have hidx := (S.selectedLeafMetaPath_isPath r).getVert_injOn
    (by
      change a ≤ (S.selectedLeafMetaPath r : T.metaTree.Walk S.root
        (S.selectedLeaf r)).length
      omega :
        a ∈ {i : ℕ |
          i ≤ (S.selectedLeafMetaPath r : T.metaTree.Walk S.root
            (S.selectedLeaf r)).length})
    (by
      change a + 2 ≤ (S.selectedLeafMetaPath r : T.metaTree.Walk S.root
        (S.selectedLeaf r)).length
      omega :
        a + 2 ∈ {i : ℕ |
          i ≤ (S.selectedLeafMetaPath r : T.metaTree.Walk S.root
            (S.selectedLeaf r)).length})
    (by
      simpa [selectedLeafMetaPathVertex] using h)
  omega

/-- Consecutive meta-edges on a selected root-to-leaf path are distinct as
unoriented edges. -/
theorem selectedLeafMetaPathEdge_ne_succ
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) {a : ℕ}
    (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    s(S.selectedLeafMetaPathVertex r a,
      S.selectedLeafMetaPathVertex r (a + 1)) ≠
      s(S.selectedLeafMetaPathVertex r (a + 1),
        S.selectedLeafMetaPathVertex r (a + 2)) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hprev_mid, _hmid_next⟩ | ⟨hprev_next, _hmid_mid⟩
  · exact (S.selectedLeafMetaPathVertex_adj_succ r (by omega)).ne hprev_mid
  · exact S.selectedLeafMetaPathVertex_ne_two_step r ha hprev_next

/-- Every vertex on the chosen root-to-selected-leaf meta-path has that
selected leaf as a descendant. -/
theorem selectedLeaf_mem_descendants_of_mem_selectedLeafMetaPath_support
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) {v : Fin m}
    (hv : v ∈ (S.selectedLeafMetaPath r : T.metaTree.Walk S.root
      (S.selectedLeaf r)).support) :
    S.selectedLeaf r ∈ selectedMetaLeafDescendants T S.root S.leaves v := by
  classical
  exact Finset.mem_filter.mpr
    ⟨S.selectedLeaf_mem r, ⟨S.selectedLeafMetaPath r, hv⟩⟩

/-- The `(a+1)`-st vertex of the chosen root-to-leaf meta-path has the leaf
below it. -/
theorem selectedLeaf_mem_descendants_of_selectedLeafMetaPath_getVert_succ
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) {a : ℕ}
    (_ha :
      a < (S.selectedLeafMetaPath r : T.metaTree.Walk S.root
        (S.selectedLeaf r)).length) :
    S.selectedLeaf r ∈
      selectedMetaLeafDescendants T S.root S.leaves
        ((S.selectedLeafMetaPath r : T.metaTree.Walk S.root
          (S.selectedLeaf r)).getVert (a + 1)) := by
  apply S.selectedLeaf_mem_descendants_of_mem_selectedLeafMetaPath_support r
  exact (S.selectedLeafMetaPath r : T.metaTree.Walk S.root
    (S.selectedLeaf r)).getVert_mem_support (a + 1)

/-- The successor vertex on the chosen root-to-leaf meta-path has the selected
leaf below it. -/
theorem selectedLeaf_mem_descendants_of_selectedLeafMetaPathVertex_succ
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) {a : ℕ}
    (ha : a < S.selectedLeafMetaPathLength r) :
    S.selectedLeaf r ∈
      selectedMetaLeafDescendants T S.root S.leaves
        (S.selectedLeafMetaPathVertex r (a + 1)) := by
  simpa [selectedLeafMetaPathVertex, selectedLeafMetaPathLength] using
    S.selectedLeaf_mem_descendants_of_selectedLeafMetaPath_getVert_succ r ha

/-- Step 1 tranche data on one edge of a chosen root-to-selected-leaf
meta-path, specialized to the selected leaf carried by that path. -/
structure SelectedLeafMetaPathEdgeTrancheData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (a : Fin (S.selectedLeafMetaPathLength r)) where
  edgeTranches :
    ConnectorDescendantTrancheData S
      (S.selectedLeafMetaPathVertex_adj_succ r a.2)
      (S.selectedLeafMetaPathVertex r (a.1 + 1))
  selectedLeafDescendant :
    S.selectedLeaf r ∈
      selectedMetaLeafDescendants T S.root S.leaves
        (S.selectedLeafMetaPathVertex r (a.1 + 1))
  selectedLeafTranche_subset_index :
    edgeTranches.tranche ⟨S.selectedLeaf r, selectedLeafDescendant⟩ ⊆
      edgeTranches.indexSet
  selectedLeafTranche_card :
    (edgeTranches.tranche ⟨S.selectedLeaf r, selectedLeafDescendant⟩).card =
      W / ell
  selectedLeafTranche_source_card :
    ((T.connector (S.selectedLeafMetaPathVertex r a.1)
      (S.selectedLeafMetaPathVertex r (a.1 + 1))
      (S.selectedLeafMetaPathVertex_adj_succ r a.2)).sourceSet
        (edgeTranches.tranche ⟨S.selectedLeaf r, selectedLeafDescendant⟩)).card =
      W / ell
  selectedLeafTranche_target_card :
    ((T.connector (S.selectedLeafMetaPathVertex r a.1)
      (S.selectedLeafMetaPathVertex r (a.1 + 1))
      (S.selectedLeafMetaPathVertex_adj_succ r a.2)).targetSet
        (edgeTranches.tranche ⟨S.selectedLeaf r, selectedLeafDescendant⟩)).card =
      W / ell
  selectedLeafTranche_restricted_card :
    ((T.connector (S.selectedLeafMetaPathVertex r a.1)
      (S.selectedLeafMetaPathVertex r (a.1 + 1))
      (S.selectedLeafMetaPathVertex_adj_succ r a.2)).restrictIndexSet
        (edgeTranches.tranche ⟨S.selectedLeaf r, selectedLeafDescendant⟩)).card =
      W / ell
  selectedLeafTranche_restricted_staysIn :
    ((T.connector (S.selectedLeafMetaPathVertex r a.1)
      (S.selectedLeafMetaPathVertex r (a.1 + 1))
      (S.selectedLeafMetaPathVertex_adj_succ r a.2)).restrictIndexSet
        (edgeTranches.tranche ⟨S.selectedLeaf r, selectedLeafDescendant⟩)).toPathPacking.StaysIn
      (T.connector (S.selectedLeafMetaPathVertex r a.1)
        (S.selectedLeafMetaPathVertex r (a.1 + 1))
        (S.selectedLeafMetaPathVertex_adj_succ r a.2)).toPathPacking.vertexSet
  selectedLeafTranche_restricted_internallyDisjoint_clusters :
    ∀ c : Fin m,
      PathPacking.InternallyDisjointFromSet
        ((T.connector (S.selectedLeafMetaPathVertex r a.1)
          (S.selectedLeafMetaPathVertex r (a.1 + 1))
          (S.selectedLeafMetaPathVertex_adj_succ r a.2)).restrictIndexSet
            (edgeTranches.tranche ⟨S.selectedLeaf r, selectedLeafDescendant⟩)).toPathPacking
        (T.cluster c)

/-- The selected leaf's index tranche on this meta-path edge. -/
noncomputable def SelectedLeafMetaPathEdgeTrancheData.selectedLeafTranche
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell}
    {a : Fin (S.selectedLeafMetaPathLength r)}
    (D : SelectedLeafMetaPathEdgeTrancheData S r a) :
    Finset (T.connector (S.selectedLeafMetaPathVertex r a.1)
      (S.selectedLeafMetaPathVertex r (a.1 + 1))
      (S.selectedLeafMetaPathVertex_adj_succ r a.2)).Index :=
  D.edgeTranches.tranche ⟨S.selectedLeaf r, D.selectedLeafDescendant⟩

/-- Source endpoints of the selected leaf's tranche on this meta-path edge. -/
noncomputable def SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell}
    {a : Fin (S.selectedLeafMetaPathLength r)}
    (D : SelectedLeafMetaPathEdgeTrancheData S r a) : Finset V :=
  (T.connector (S.selectedLeafMetaPathVertex r a.1)
    (S.selectedLeafMetaPathVertex r (a.1 + 1))
    (S.selectedLeafMetaPathVertex_adj_succ r a.2)).sourceSet
      D.selectedLeafTranche

/-- Target endpoints of the selected leaf's tranche on this meta-path edge. -/
noncomputable def SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell}
    {a : Fin (S.selectedLeafMetaPathLength r)}
    (D : SelectedLeafMetaPathEdgeTrancheData S r a) : Finset V :=
  (T.connector (S.selectedLeafMetaPathVertex r a.1)
    (S.selectedLeafMetaPathVertex r (a.1 + 1))
    (S.selectedLeafMetaPathVertex_adj_succ r a.2)).targetSet
      D.selectedLeafTranche

/-- The selected leaf's restricted connector packing on this meta-path edge,
with the source and target endpoint sets exposed through the selected-tranche
accessors. -/
noncomputable def SelectedLeafMetaPathEdgeTrancheData.selectedLeafRestrictedPacking
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell}
    {a : Fin (S.selectedLeafMetaPathLength r)}
    (D : SelectedLeafMetaPathEdgeTrancheData S r a) :
    PerfectPathPacking G D.selectedLeafSourceSet D.selectedLeafTargetSet :=
  (T.connector (S.selectedLeafMetaPathVertex r a.1)
    (S.selectedLeafMetaPathVertex r (a.1 + 1))
    (S.selectedLeafMetaPathVertex_adj_succ r a.2)).restrictIndexSet
      D.selectedLeafTranche

@[simp] theorem SelectedLeafMetaPathEdgeTrancheData.selectedLeafRestrictedPacking_card
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell}
    {a : Fin (S.selectedLeafMetaPathLength r)}
    (D : SelectedLeafMetaPathEdgeTrancheData S r a) :
    D.selectedLeafRestrictedPacking.card = W / ell := by
  dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafRestrictedPacking]
  exact D.selectedLeafTranche_restricted_card

/-- The selected restricted connector still stays inside the full connector
spanning set. -/
theorem SelectedLeafMetaPathEdgeTrancheData.selectedLeafRestrictedPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell}
    {a : Fin (S.selectedLeafMetaPathLength r)}
    (D : SelectedLeafMetaPathEdgeTrancheData S r a) :
    D.selectedLeafRestrictedPacking.toPathPacking.StaysIn
      (T.connector (S.selectedLeafMetaPathVertex r a.1)
        (S.selectedLeafMetaPathVertex r (a.1 + 1))
        (S.selectedLeafMetaPathVertex_adj_succ r a.2)).toPathPacking.vertexSet := by
  dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafRestrictedPacking]
  exact D.selectedLeafTranche_restricted_staysIn

/-- The selected restricted connector remains internally disjoint from every
cluster. -/
theorem SelectedLeafMetaPathEdgeTrancheData.selectedLeafRestrictedPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell}
    {a : Fin (S.selectedLeafMetaPathLength r)}
    (D : SelectedLeafMetaPathEdgeTrancheData S r a) (c : Fin m) :
    D.selectedLeafRestrictedPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafRestrictedPacking]
  exact D.selectedLeafTranche_restricted_internallyDisjoint_clusters c

/-- Every edge of a chosen root-to-selected-leaf meta-path admits the selected
leaf's Step 1 tranche package. -/
theorem exists_selectedLeafMetaPathEdgeTrancheData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (a : Fin (S.selectedLeafMetaPathLength r)) :
    Nonempty (SelectedLeafMetaPathEdgeTrancheData S r a) := by
  classical
  let hAdj := S.selectedLeafMetaPathVertex_adj_succ r a.2
  let D : ConnectorDescendantTrancheData S hAdj
      (S.selectedLeafMetaPathVertex r (a.1 + 1)) :=
    Classical.choice (S.exists_connectorDescendantTrancheData hAdj
      (S.selectedLeafMetaPathVertex r (a.1 + 1)))
  have hleaf :
      S.selectedLeaf r ∈
        selectedMetaLeafDescendants T S.root S.leaves
          (S.selectedLeafMetaPathVertex r (a.1 + 1)) :=
    S.selectedLeaf_mem_descendants_of_selectedLeafMetaPathVertex_succ r a.2
  exact ⟨{
    edgeTranches := D
    selectedLeafDescendant := hleaf
    selectedLeafTranche_subset_index :=
      D.tranche_subset_index ⟨S.selectedLeaf r, hleaf⟩
    selectedLeafTranche_card :=
      D.tranche_card ⟨S.selectedLeaf r, hleaf⟩
    selectedLeafTranche_source_card :=
      D.tranche_source_card ⟨S.selectedLeaf r, hleaf⟩
    selectedLeafTranche_target_card :=
      D.tranche_target_card ⟨S.selectedLeaf r, hleaf⟩
    selectedLeafTranche_restricted_card :=
      D.tranche_restricted_card ⟨S.selectedLeaf r, hleaf⟩
    selectedLeafTranche_restricted_staysIn :=
      D.tranche_restricted_staysIn ⟨S.selectedLeaf r, hleaf⟩
    selectedLeafTranche_restricted_internallyDisjoint_clusters := by
      intro c
      exact D.tranche_restricted_internallyDisjoint_clusters
        ⟨S.selectedLeaf r, hleaf⟩ c }⟩

/-- A chosen selected-leaf tranche package on one edge of its root-to-leaf
meta-path. -/
noncomputable def selectedLeafMetaPathEdgeTrancheData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (a : Fin (S.selectedLeafMetaPathLength r)) :
    SelectedLeafMetaPathEdgeTrancheData S r a :=
  Classical.choice (S.exists_selectedLeafMetaPathEdgeTrancheData r a)

/-- Step 1 linkage through an internal meta-path cluster, connecting the
selected leaf's incoming connector tranche to its outgoing connector tranche. -/
structure SelectedLeafMetaPathTurnLinkageData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (a : ℕ) (ha : a + 1 < S.selectedLeafMetaPathLength r) where
  incoming :
    SelectedLeafMetaPathEdgeTrancheData S r
      ⟨a, by omega⟩
  outgoing :
    SelectedLeafMetaPathEdgeTrancheData S r
      ⟨a + 1, ha⟩
  turnLinkage :
    PerfectPathPacking G incoming.selectedLeafTargetSet
      outgoing.selectedLeafSourceSet
  turnLinkage_card : turnLinkage.card = W / ell
  turnLinkage_staysIn :
    turnLinkage.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafMetaPathVertex r (a + 1)))

/-- Consecutive selected-leaf tranches along a root-to-leaf meta-path can be
linked inside the intermediate cluster. -/
theorem exists_selectedLeafMetaPathTurnLinkageData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    Nonempty (SelectedLeafMetaPathTurnLinkageData S r a ha) := by
  classical
  let ia : Fin (S.selectedLeafMetaPathLength r) := ⟨a, by omega⟩
  let ib : Fin (S.selectedLeafMetaPathLength r) := ⟨a + 1, ha⟩
  let incoming := S.selectedLeafMetaPathEdgeTrancheData r ia
  let outgoing := S.selectedLeafMetaPathEdgeTrancheData r ib
  let prev := S.selectedLeafMetaPathVertex r a
  let mid := S.selectedLeafMetaPathVertex r (a + 1)
  let next := S.selectedLeafMetaPathVertex r (a + 2)
  let hin : T.metaTree.Adj prev mid :=
    S.selectedLeafMetaPathVertex_adj_succ r ia.2
  let hout : T.metaTree.Adj mid next :=
    S.selectedLeafMetaPathVertex_adj_succ r ib.2
  have hprev_next : prev ≠ next := by
    exact S.selectedLeafMetaPathVertex_ne_two_step r ha
  have hincoming_subset :
      incoming.selectedLeafTargetSet ⊆
        T.interface mid prev (T.metaTree.symm hin) := by
    dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet,
      incoming, ia, prev, mid, hin]
    exact (T.connector (S.selectedLeafMetaPathVertex r a)
      (S.selectedLeafMetaPathVertex r (a + 1))
      (S.selectedLeafMetaPathVertex_adj_succ r (by omega))).targetSet_subset_right _
  have houtgoing_subset :
      outgoing.selectedLeafSourceSet ⊆ T.interface mid next hout := by
    dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet,
      outgoing, ib, mid, next, hout]
    exact (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
      (S.selectedLeafMetaPathVertex r (a + 2))
      (S.selectedLeafMetaPathVertex_adj_succ r ha)).sourceSet_subset_left _
  have hcard :
      incoming.selectedLeafTargetSet.card =
        outgoing.selectedLeafSourceSet.card := by
    dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet,
      SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet,
      incoming, outgoing, ia, ib]
    exact incoming.selectedLeafTranche_target_card.trans
      outgoing.selectedLeafTranche_source_card.symm
  rcases T.exists_interface_pair_perfect_linkage_between_subsets
      (i := mid) (j := prev) (k := next)
      (hij := T.metaTree.symm hin) (hik := hout)
      hprev_next hincoming_subset houtgoing_subset hcard with
    ⟨Q, hQcard, hQstay⟩
  exact ⟨{
    incoming := incoming
    outgoing := outgoing
    turnLinkage := Q
    turnLinkage_card := by
      dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet,
        incoming, ia] at hQcard
      exact hQcard.trans incoming.selectedLeafTranche_target_card
    turnLinkage_staysIn := hQstay }⟩

/-- A chosen Step 1 turn linkage for two consecutive edges of a selected
root-to-leaf meta-path. -/
noncomputable def selectedLeafMetaPathTurnLinkageData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    SelectedLeafMetaPathTurnLinkageData S r a ha :=
  Classical.choice (S.exists_selectedLeafMetaPathTurnLinkageData r ha)

/-- The source endpoints of the incoming selected tranche are disjoint from the
middle cluster of the turn. -/
theorem SelectedLeafMetaPathTurnLinkageData.incomingSource_disjoint_middleCluster
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell}
    {a : ℕ} {ha : a + 1 < S.selectedLeafMetaPathLength r}
    (D : SelectedLeafMetaPathTurnLinkageData S r a ha) :
    Disjoint D.incoming.selectedLeafSourceSet
      (T.cluster (S.selectedLeafMetaPathVertex r (a + 1))) := by
  classical
  let prev := S.selectedLeafMetaPathVertex r a
  let mid := S.selectedLeafMetaPathVertex r (a + 1)
  have hprev_mid : prev ≠ mid :=
    (S.selectedLeafMetaPathVertex_adj_succ r (by omega)).ne
  have hsource_cluster :
      D.incoming.selectedLeafSourceSet ⊆ T.cluster prev := by
    have hsource_interface :
        D.incoming.selectedLeafSourceSet ⊆
          T.interface prev mid
            (S.selectedLeafMetaPathVertex_adj_succ r (by omega)) := by
      dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet,
        prev, mid]
      exact (T.connector (S.selectedLeafMetaPathVertex r a)
        (S.selectedLeafMetaPathVertex r (a + 1))
        (S.selectedLeafMetaPathVertex_adj_succ r (by omega))).sourceSet_subset_left _
    exact subset_trans hsource_interface
      (T.interface_subset_cluster prev mid
        (S.selectedLeafMetaPathVertex_adj_succ r (by omega)))
  exact Finset.disjoint_of_subset_left hsource_cluster
    (T.cluster_disjoint hprev_mid)

/-- Concatenating the incoming selected connector tranche with the linkage
through the middle cluster gives a perfect packing from the incoming sources to
the outgoing sources.  This is the first concrete path-composition step in the
many-leaves extraction branch of Theorem 4.6. -/
structure SelectedLeafMetaPathIncomingTurnConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (a : ℕ) (ha : a + 1 < S.selectedLeafMetaPathLength r) where
  turn : SelectedLeafMetaPathTurnLinkageData S r a ha
  incomingTurnPacking :
    PerfectPathPacking G turn.incoming.selectedLeafSourceSet
      turn.outgoing.selectedLeafSourceSet
  incomingTurnPacking_card : incomingTurnPacking.card = W / ell
  incomingTurnPacking_staysIn :
    incomingTurnPacking.toPathPacking.StaysIn
      ((T.connector (S.selectedLeafMetaPathVertex r a)
        (S.selectedLeafMetaPathVertex r (a + 1))
        (S.selectedLeafMetaPathVertex_adj_succ r (by omega))).toPathPacking.vertexSet ∪
        T.cluster (S.selectedLeafMetaPathVertex r (a + 1)))
  incomingTurnPacking_internallyDisjoint_cluster_of_ne_mid :
    ∀ {c : Fin m}, c ≠ S.selectedLeafMetaPathVertex r (a + 1) →
      incomingTurnPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)

/-- The incoming selected connector tranche can be composed with its turn
linkage inside the intermediate cluster. -/
theorem exists_selectedLeafMetaPathIncomingTurnConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    Nonempty (SelectedLeafMetaPathIncomingTurnConcatData S r a ha) := by
  classical
  let D := S.selectedLeafMetaPathTurnLinkageData r ha
  let P := D.incoming.selectedLeafRestrictedPacking
  let Q := D.turnLinkage
  let A := T.cluster (S.selectedLeafMetaPathVertex r (a + 1))
  have hP : P.toPathPacking.InternallyDisjointFromSet A := by
    dsimp [P, A]
    exact D.incoming.selectedLeafRestrictedPacking_internallyDisjoint_clusters
      (S.selectedLeafMetaPathVertex r (a + 1))
  have hQ : Q.toPathPacking.StaysIn A := by
    dsimp [Q, A]
    exact D.turnLinkage_staysIn
  have hSdisj : Disjoint D.incoming.selectedLeafSourceSet A := by
    dsimp [A]
    exact D.incomingSource_disjoint_middleCluster
  let R : PerfectPathPacking G D.incoming.selectedLeafSourceSet
      D.outgoing.selectedLeafSourceSet :=
    P.concatOfFirstInternallyDisjointSecondStaysIn Q hP hQ hSdisj
  exact ⟨{
    turn := D
    incomingTurnPacking := R
    incomingTurnPacking_card := by
      dsimp [R, P]
      rw [PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_card]
      exact D.incoming.selectedLeafRestrictedPacking_card
    incomingTurnPacking_staysIn := by
      dsimp [R, P, Q, A]
      exact PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
        D.incoming.selectedLeafRestrictedPacking D.turnLinkage hP hQ hSdisj
        D.incoming.selectedLeafRestrictedPacking_staysIn
    incomingTurnPacking_internallyDisjoint_cluster_of_ne_mid := by
      intro c hc
      have hPC :
          P.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        dsimp [P]
        exact D.incoming.selectedLeafRestrictedPacking_internallyDisjoint_clusters c
      have hQC :
          Q.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        intro i v hv hvC
        have hvA : v ∈ A := by
          dsimp [Q, A] at *
          exact D.turnLinkage_staysIn i hv
        exact False.elim
          (Finset.disjoint_left.mp
            (T.cluster_disjoint (hc.symm)) hvA hvC)
      have hTdisj : Disjoint D.incoming.selectedLeafTargetSet (T.cluster c) := by
        let prev := S.selectedLeafMetaPathVertex r a
        let mid := S.selectedLeafMetaPathVertex r (a + 1)
        have htarget_cluster :
            D.incoming.selectedLeafTargetSet ⊆ T.cluster mid := by
          have htarget_interface :
              D.incoming.selectedLeafTargetSet ⊆
                T.interface mid prev
                  (T.metaTree.symm
                    (S.selectedLeafMetaPathVertex_adj_succ r (by omega))) := by
            dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet,
              prev, mid]
            exact (T.connector (S.selectedLeafMetaPathVertex r a)
              (S.selectedLeafMetaPathVertex r (a + 1))
              (S.selectedLeafMetaPathVertex_adj_succ r (by omega))).targetSet_subset_right _
          exact subset_trans htarget_interface
            (T.interface_subset_cluster mid prev
              (T.metaTree.symm
                (S.selectedLeafMetaPathVertex_adj_succ r (by omega))))
        exact Finset.disjoint_of_subset_left htarget_cluster
          (T.cluster_disjoint (hc.symm))
      dsimp [R]
      exact
        PerfectPathPacking.concatOfFirstInternallyDisjointSecondStaysIn_internallyDisjointFromSet
          P Q hP hQ hSdisj hPC hQC hTdisj }⟩

/-- A chosen concatenation package for an internal selected-leaf meta-path
turn. -/
noncomputable def selectedLeafMetaPathIncomingTurnConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    SelectedLeafMetaPathIncomingTurnConcatData S r a ha :=
  Classical.choice
    (S.exists_selectedLeafMetaPathIncomingTurnConcatData r ha)

/-- Concatenating the linkage through the middle cluster with the outgoing
selected connector tranche gives a perfect packing from the incoming targets to
the outgoing targets. -/
structure SelectedLeafMetaPathTurnOutgoingConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (a : ℕ) (ha : a + 1 < S.selectedLeafMetaPathLength r) where
  turn : SelectedLeafMetaPathTurnLinkageData S r a ha
  turnOutgoingPacking :
    PerfectPathPacking G turn.incoming.selectedLeafTargetSet
      turn.outgoing.selectedLeafTargetSet
  turnOutgoingPacking_card : turnOutgoingPacking.card = W / ell
  turnOutgoingPacking_staysIn :
    turnOutgoingPacking.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafMetaPathVertex r (a + 1)) ∪
        (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
          (S.selectedLeafMetaPathVertex r (a + 2))
          (S.selectedLeafMetaPathVertex_adj_succ r ha)).toPathPacking.vertexSet)
  turnOutgoingPacking_internallyDisjoint_cluster_of_ne_mid :
    ∀ {c : Fin m}, c ≠ S.selectedLeafMetaPathVertex r (a + 1) →
      turnOutgoingPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)

/-- The middle-cluster linkage can be composed with the outgoing selected
connector tranche. -/
theorem exists_selectedLeafMetaPathTurnOutgoingConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    Nonempty (SelectedLeafMetaPathTurnOutgoingConcatData S r a ha) := by
  classical
  let D := S.selectedLeafMetaPathTurnLinkageData r ha
  let P := D.turnLinkage
  let Q := D.outgoing.selectedLeafRestrictedPacking
  let A := T.cluster (S.selectedLeafMetaPathVertex r (a + 1))
  have hP : P.toPathPacking.StaysIn A := by
    dsimp [P, A]
    exact D.turnLinkage_staysIn
  have hQ : Q.toPathPacking.InternallyDisjointFromSet A := by
    dsimp [Q, A]
    exact D.outgoing.selectedLeafRestrictedPacking_internallyDisjoint_clusters
      (S.selectedLeafMetaPathVertex r (a + 1))
  have hUdisj : Disjoint D.outgoing.selectedLeafTargetSet A := by
    let mid := S.selectedLeafMetaPathVertex r (a + 1)
    let next := S.selectedLeafMetaPathVertex r (a + 2)
    have hmid_next : mid ≠ next :=
      (S.selectedLeafMetaPathVertex_adj_succ r ha).ne
    have htarget_cluster :
        D.outgoing.selectedLeafTargetSet ⊆ T.cluster next := by
      have htarget_interface :
          D.outgoing.selectedLeafTargetSet ⊆
            T.interface next mid
              (T.metaTree.symm
                (S.selectedLeafMetaPathVertex_adj_succ r ha)) := by
        dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet,
          mid, next]
        exact (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
          (S.selectedLeafMetaPathVertex r (a + 2))
          (S.selectedLeafMetaPathVertex_adj_succ r ha)).targetSet_subset_right _
      exact subset_trans htarget_interface
        (T.interface_subset_cluster next mid
          (T.metaTree.symm
            (S.selectedLeafMetaPathVertex_adj_succ r ha)))
    dsimp [A]
    exact Finset.disjoint_of_subset_left htarget_cluster
      (T.cluster_disjoint hmid_next.symm)
  let R : PerfectPathPacking G D.incoming.selectedLeafTargetSet
      D.outgoing.selectedLeafTargetSet :=
    P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj
  exact ⟨{
    turn := D
    turnOutgoingPacking := R
    turnOutgoingPacking_card := by
      dsimp [R, P]
      rw [PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_card]
      exact D.turnLinkage_card
    turnOutgoingPacking_staysIn := by
      dsimp [R, P, Q, A]
      exact PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        D.turnLinkage D.outgoing.selectedLeafRestrictedPacking hP hQ hUdisj
        D.outgoing.selectedLeafRestrictedPacking_staysIn
    turnOutgoingPacking_internallyDisjoint_cluster_of_ne_mid := by
      intro c hc
      have hPC :
          P.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        intro i v hv hvC
        have hvA : v ∈ A := by
          dsimp [P, A] at *
          exact D.turnLinkage_staysIn i hv
        exact False.elim
          (Finset.disjoint_left.mp
            (T.cluster_disjoint (hc.symm)) hvA hvC)
      have hQC :
          Q.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        dsimp [Q]
        exact D.outgoing.selectedLeafRestrictedPacking_internallyDisjoint_clusters c
      have hTdisj : Disjoint D.outgoing.selectedLeafSourceSet (T.cluster c) := by
        let mid := S.selectedLeafMetaPathVertex r (a + 1)
        let next := S.selectedLeafMetaPathVertex r (a + 2)
        have hsource_cluster :
            D.outgoing.selectedLeafSourceSet ⊆ T.cluster mid := by
          have hsource_interface :
              D.outgoing.selectedLeafSourceSet ⊆
                T.interface mid next
                  (S.selectedLeafMetaPathVertex_adj_succ r ha) := by
            dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet,
              mid, next]
            exact (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
              (S.selectedLeafMetaPathVertex r (a + 2))
              (S.selectedLeafMetaPathVertex_adj_succ r ha)).sourceSet_subset_left _
          exact subset_trans hsource_interface
            (T.interface_subset_cluster mid next
              (S.selectedLeafMetaPathVertex_adj_succ r ha))
        exact Finset.disjoint_of_subset_left hsource_cluster
          (T.cluster_disjoint (hc.symm))
      dsimp [R]
      exact
        PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
          P Q hP hQ hUdisj hPC hQC hTdisj }⟩

/-- A chosen turn-outgoing concatenation package for an internal selected-leaf
meta-path turn. -/
noncomputable def selectedLeafMetaPathTurnOutgoingConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    SelectedLeafMetaPathTurnOutgoingConcatData S r a ha :=
  Classical.choice
    (S.exists_selectedLeafMetaPathTurnOutgoingConcatData r ha)

/-- A width-restricted turn-outgoing selected-route packing.  Given a chosen
subset of the incoming target side of a turn, this keeps exactly the paths
starting at that subset and records the induced target subset on the next
selected connector. -/
structure SelectedLeafMetaPathTurnOutgoingWidthRestrictionData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (a : ℕ) (ha : a + 1 < S.selectedLeafMetaPathLength r)
    (sourceSet : Finset V) (w : ℕ) where
  turnOutgoing : SelectedLeafMetaPathTurnOutgoingConcatData S r a ha
  source_subset : sourceSet ⊆ turnOutgoing.turn.incoming.selectedLeafTargetSet
  source_card : sourceSet.card = w
  restrictedPacking :
    PerfectPathPacking G sourceSet
      (turnOutgoing.turnOutgoingPacking.targetSet
        (turnOutgoing.turnOutgoingPacking.sourceIndexSetOfSubset sourceSet))
  restrictedPacking_card : restrictedPacking.card = w
  target_card :
    (turnOutgoing.turnOutgoingPacking.targetSet
      (turnOutgoing.turnOutgoingPacking.sourceIndexSetOfSubset sourceSet)).card = w
  restrictedPacking_staysIn :
    restrictedPacking.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafMetaPathVertex r (a + 1)) ∪
        (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
          (S.selectedLeafMetaPathVertex r (a + 2))
          (S.selectedLeafMetaPathVertex_adj_succ r ha)).toPathPacking.vertexSet)
  restrictedPacking_internallyDisjoint_cluster_of_ne_mid :
    ∀ {c : Fin m}, c ≠ S.selectedLeafMetaPathVertex r (a + 1) →
      restrictedPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)

/-- Restrict a selected-route turn-outgoing packing to any prescribed width-`w`
incoming target subset. -/
theorem exists_selectedLeafMetaPathTurnOutgoingWidthRestrictionData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r)
    (D : SelectedLeafMetaPathTurnOutgoingConcatData S r a ha)
    (sourceSet : Finset V) {w : ℕ}
    (hsource : sourceSet ⊆ D.turn.incoming.selectedLeafTargetSet)
    (hcard : sourceSet.card = w) :
    Nonempty
      (SelectedLeafMetaPathTurnOutgoingWidthRestrictionData
        S r a ha sourceSet w) := by
  classical
  let P := D.turnOutgoingPacking
  let R : PerfectPathPacking G sourceSet
      (D.turnOutgoingPacking.targetSet
        (D.turnOutgoingPacking.sourceIndexSetOfSubset sourceSet)) :=
    P.restrictSourceSet sourceSet hsource
  have hidx_card :
      (P.sourceIndexSetOfSubset sourceSet).card = w := by
    simpa [hcard] using P.sourceIndexSetOfSubset_card hsource
  exact ⟨{
    turnOutgoing := D
    source_subset := hsource
    source_card := hcard
    restrictedPacking := R
    restrictedPacking_card := by
      dsimp [R, P]
      simp [hcard]
    target_card := by
      calc
        (D.turnOutgoingPacking.targetSet
            (D.turnOutgoingPacking.sourceIndexSetOfSubset sourceSet)).card =
            (D.turnOutgoingPacking.sourceIndexSetOfSubset sourceSet).card := by
          exact D.turnOutgoingPacking.targetSet_card
            (D.turnOutgoingPacking.sourceIndexSetOfSubset sourceSet)
        _ = w := by
          simpa [P] using hidx_card
    restrictedPacking_staysIn := by
      dsimp [R, P]
      exact D.turnOutgoingPacking.restrictSourceSet_staysIn sourceSet hsource
        D.turnOutgoingPacking_staysIn
    restrictedPacking_internallyDisjoint_cluster_of_ne_mid := by
      intro c hc
      dsimp [R, P]
      exact D.turnOutgoingPacking.restrictSourceSet_internallyDisjointFromSet
        sourceSet hsource
        (D.turnOutgoingPacking_internallyDisjoint_cluster_of_ne_mid hc) }⟩

/-- First-turn linkage out of the shared root-child tranche for a selected
leaf.  This avoids comparing the independently chosen first-edge tranche with
the coherent root-child tranche. -/
structure RootChildSelectedLeafFirstTurnLinkageData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (ha : 1 < S.selectedLeafMetaPathLength r) where
  outgoing :
    SelectedLeafMetaPathEdgeTrancheData S r ⟨1, ha⟩
  turnLinkage :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet
        (S.rootChildSelectedLeafTranche r))
      outgoing.selectedLeafSourceSet
  turnLinkage_card : turnLinkage.card = W / ell
  turnLinkage_staysIn : turnLinkage.toPathPacking.StaysIn (T.cluster S.child)

/-- The shared root-child selected-leaf tranche links inside the root child to
the selected tranche on the second edge of the chosen root-to-leaf meta-path. -/
theorem exists_rootChildSelectedLeafFirstTurnLinkageData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (ha : 1 < S.selectedLeafMetaPathLength r) :
    Nonempty (RootChildSelectedLeafFirstTurnLinkageData S r ha) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  let next := S.selectedLeafMetaPathVertex r 2
  let outgoing := S.selectedLeafMetaPathEdgeTrancheData r ⟨1, ha⟩
  have hchild_next : T.metaTree.Adj S.child next := by
    simpa [next] using
      (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha)
  have hroot_ne_next : S.root ≠ next := by
    have h := S.selectedLeafMetaPathVertex_ne_two_step r (a := 0) ha
    simpa [next] using h
  have hrootChildTarget_subset :
      P.targetSet (S.rootChildSelectedLeafTranche r) ⊆
        T.interface S.child S.root (T.metaTree.symm S.root_child_adj) := by
    exact P.targetSet_subset_right _
  have houtgoing_subset :
      outgoing.selectedLeafSourceSet ⊆ T.interface S.child next hchild_next := by
    dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet,
      outgoing, next]
    simpa [next] using
      (T.connector (S.selectedLeafMetaPathVertex r 1)
        (S.selectedLeafMetaPathVertex r 2)
        (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha)).sourceSet_subset_left _
  have hcard :
      (P.targetSet (S.rootChildSelectedLeafTranche r)).card =
        outgoing.selectedLeafSourceSet.card :=
    (S.rootChildSelectedLeafTranche_target_card r).trans
      outgoing.selectedLeafTranche_source_card.symm
  rcases T.exists_interface_pair_perfect_linkage_between_subsets
      (i := S.child) (j := S.root) (k := next)
      (hij := T.metaTree.symm S.root_child_adj) (hik := hchild_next)
      hroot_ne_next hrootChildTarget_subset houtgoing_subset hcard with
    ⟨Q, hQcard, hQstay⟩
  exact ⟨{
    outgoing := outgoing
    turnLinkage := Q
    turnLinkage_card := by
      dsimp [P] at hQcard
      exact hQcard.trans (S.rootChildSelectedLeafTranche_target_card r)
    turnLinkage_staysIn := hQstay }⟩

/-- A chosen first-turn linkage out of the shared root-child tranche. -/
noncomputable def rootChildSelectedLeafFirstTurnLinkageData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (ha : 1 < S.selectedLeafMetaPathLength r) :
    RootChildSelectedLeafFirstTurnLinkageData S r ha :=
  Classical.choice (S.exists_rootChildSelectedLeafFirstTurnLinkageData r ha)

/-- Concatenating the first-turn child-cluster linkage with the second selected
connector tranche gives a route from the shared root-child child-side endpoints
to the far side of the second edge. -/
structure RootChildSelectedLeafFirstTurnOutgoingConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (ha : 1 < S.selectedLeafMetaPathLength r) where
  firstTurn : RootChildSelectedLeafFirstTurnLinkageData S r ha
  firstTurnOutgoingPacking :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet
        (S.rootChildSelectedLeafTranche r))
      firstTurn.outgoing.selectedLeafTargetSet
  firstTurnOutgoingPacking_card : firstTurnOutgoingPacking.card = W / ell
  firstTurnOutgoingPacking_staysIn :
    firstTurnOutgoingPacking.toPathPacking.StaysIn
      (T.cluster S.child ∪
        (T.connector (S.selectedLeafMetaPathVertex r 1)
          (S.selectedLeafMetaPathVertex r 2)
          (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha)).toPathPacking.vertexSet)
  firstTurnOutgoingPacking_internallyDisjoint_cluster_of_ne_child :
    ∀ {c : Fin m}, c ≠ S.child →
      firstTurnOutgoingPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)

/-- The first-turn linkage can be composed with the second selected connector
tranche. -/
theorem exists_rootChildSelectedLeafFirstTurnOutgoingConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (ha : 1 < S.selectedLeafMetaPathLength r) :
    Nonempty (RootChildSelectedLeafFirstTurnOutgoingConcatData S r ha) := by
  classical
  let D := S.rootChildSelectedLeafFirstTurnLinkageData r ha
  let P := D.turnLinkage
  let Q := D.outgoing.selectedLeafRestrictedPacking
  let A := T.cluster S.child
  let next := S.selectedLeafMetaPathVertex r 2
  have hchild_next : T.metaTree.Adj S.child next := by
    simpa [next] using
      (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha)
  have hP : P.toPathPacking.StaysIn A := by
    dsimp [P, A]
    exact D.turnLinkage_staysIn
  have hQ : Q.toPathPacking.InternallyDisjointFromSet A := by
    dsimp [Q, A]
    exact D.outgoing.selectedLeafRestrictedPacking_internallyDisjoint_clusters S.child
  have hUdisj : Disjoint D.outgoing.selectedLeafTargetSet A := by
    have htarget_cluster :
        D.outgoing.selectedLeafTargetSet ⊆ T.cluster next := by
      have htarget_interface :
          D.outgoing.selectedLeafTargetSet ⊆
            T.interface next S.child (T.metaTree.symm hchild_next) := by
        dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet,
          next]
        simpa [next] using
          (T.connector (S.selectedLeafMetaPathVertex r 1)
            (S.selectedLeafMetaPathVertex r 2)
            (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha)).targetSet_subset_right _
      exact subset_trans htarget_interface
        (T.interface_subset_cluster next S.child (T.metaTree.symm hchild_next))
    dsimp [A]
    exact Finset.disjoint_of_subset_left htarget_cluster
      (T.cluster_disjoint hchild_next.ne.symm)
  let R : PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet
        (S.rootChildSelectedLeafTranche r))
      D.outgoing.selectedLeafTargetSet :=
    P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj
  exact ⟨{
    firstTurn := D
    firstTurnOutgoingPacking := R
    firstTurnOutgoingPacking_card := by
      dsimp [R, P]
      rw [PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_card]
      exact D.turnLinkage_card
    firstTurnOutgoingPacking_staysIn := by
      dsimp [R, P, Q, A]
      exact PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        D.turnLinkage D.outgoing.selectedLeafRestrictedPacking hP hQ hUdisj
        D.outgoing.selectedLeafRestrictedPacking_staysIn
    firstTurnOutgoingPacking_internallyDisjoint_cluster_of_ne_child := by
      intro c hc
      have hPC :
          P.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        intro i v hv hvC
        have hvA : v ∈ A := by
          dsimp [P, A] at *
          exact D.turnLinkage_staysIn i hv
        exact False.elim
          (Finset.disjoint_left.mp
            (T.cluster_disjoint hc.symm) hvA hvC)
      have hQC :
          Q.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        dsimp [Q]
        exact D.outgoing.selectedLeafRestrictedPacking_internallyDisjoint_clusters c
      have hTdisj : Disjoint D.outgoing.selectedLeafSourceSet (T.cluster c) := by
        have hsource_cluster :
            D.outgoing.selectedLeafSourceSet ⊆ T.cluster S.child := by
          have hsource_interface :
              D.outgoing.selectedLeafSourceSet ⊆
                T.interface S.child next hchild_next := by
            dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet,
              next]
            simpa [next] using
              (T.connector (S.selectedLeafMetaPathVertex r 1)
                (S.selectedLeafMetaPathVertex r 2)
                (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha)).sourceSet_subset_left _
          exact subset_trans hsource_interface
            (T.interface_subset_cluster S.child next hchild_next)
        exact Finset.disjoint_of_subset_left hsource_cluster
          (T.cluster_disjoint hc.symm)
      dsimp [R]
      exact
        PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
          P Q hP hQ hUdisj hPC hQC hTdisj }⟩

/-- A chosen first-turn outgoing package from the shared root-child tranche. -/
noncomputable def rootChildSelectedLeafFirstTurnOutgoingConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (ha : 1 < S.selectedLeafMetaPathLength r) :
    RootChildSelectedLeafFirstTurnOutgoingConcatData S r ha :=
  Classical.choice
    (S.exists_rootChildSelectedLeafFirstTurnOutgoingConcatData r ha)

/-- Width restriction of the first-turn route out of the shared root-child
child-side endpoints. -/
structure RootChildSelectedLeafFirstTurnWidthRestrictionData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (ha : 1 < S.selectedLeafMetaPathLength r)
    (sourceSet : Finset V) (w : ℕ) where
  firstTurnOutgoing :
    RootChildSelectedLeafFirstTurnOutgoingConcatData S r ha
  source_subset :
    sourceSet ⊆
      (T.connector S.root S.child S.root_child_adj).targetSet
        (S.rootChildSelectedLeafTranche r)
  source_card : sourceSet.card = w
  restrictedPacking :
    PerfectPathPacking G sourceSet
      (firstTurnOutgoing.firstTurnOutgoingPacking.targetSet
        (firstTurnOutgoing.firstTurnOutgoingPacking.sourceIndexSetOfSubset sourceSet))
  restrictedPacking_card : restrictedPacking.card = w
  target_card :
    (firstTurnOutgoing.firstTurnOutgoingPacking.targetSet
      (firstTurnOutgoing.firstTurnOutgoingPacking.sourceIndexSetOfSubset sourceSet)).card = w
  target_subset_interface :
    (firstTurnOutgoing.firstTurnOutgoingPacking.targetSet
      (firstTurnOutgoing.firstTurnOutgoingPacking.sourceIndexSetOfSubset sourceSet)) ⊆
        T.interface (S.selectedLeafMetaPathVertex r 2) S.child
          (T.metaTree.symm
            (by
              simpa using
                (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha)))
  restrictedPacking_staysIn :
    restrictedPacking.toPathPacking.StaysIn
      (T.cluster S.child ∪
        (T.connector (S.selectedLeafMetaPathVertex r 1)
          (S.selectedLeafMetaPathVertex r 2)
          (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha)).toPathPacking.vertexSet)
  restrictedPacking_internallyDisjoint_cluster_of_ne_child :
    ∀ {c : Fin m}, c ≠ S.child →
      restrictedPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)

/-- Restrict a first-turn route to any prescribed width-`w` child-side subset
of the shared root-child selected-leaf tranche. -/
theorem exists_rootChildSelectedLeafFirstTurnWidthRestrictionData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (ha : 1 < S.selectedLeafMetaPathLength r)
    (D : RootChildSelectedLeafFirstTurnOutgoingConcatData S r ha)
    (sourceSet : Finset V) {w : ℕ}
    (hsource :
      sourceSet ⊆
        (T.connector S.root S.child S.root_child_adj).targetSet
          (S.rootChildSelectedLeafTranche r))
    (hcard : sourceSet.card = w) :
    Nonempty
      (RootChildSelectedLeafFirstTurnWidthRestrictionData
        S r ha sourceSet w) := by
  classical
  let P := D.firstTurnOutgoingPacking
  let R : PerfectPathPacking G sourceSet
      (D.firstTurnOutgoingPacking.targetSet
        (D.firstTurnOutgoingPacking.sourceIndexSetOfSubset sourceSet)) :=
    P.restrictSourceSet sourceSet hsource
  have hidx_card :
      (P.sourceIndexSetOfSubset sourceSet).card = w := by
    simpa [hcard] using P.sourceIndexSetOfSubset_card hsource
  exact ⟨{
    firstTurnOutgoing := D
    source_subset := hsource
    source_card := hcard
    restrictedPacking := R
    restrictedPacking_card := by
      dsimp [R, P]
      simp [hcard]
    target_card := by
      calc
        (D.firstTurnOutgoingPacking.targetSet
            (D.firstTurnOutgoingPacking.sourceIndexSetOfSubset sourceSet)).card =
            (D.firstTurnOutgoingPacking.sourceIndexSetOfSubset sourceSet).card := by
          exact D.firstTurnOutgoingPacking.targetSet_card
            (D.firstTurnOutgoingPacking.sourceIndexSetOfSubset sourceSet)
        _ = w := by
          simpa [P] using hidx_card
    target_subset_interface := by
      have htarget_subset :
          D.firstTurnOutgoingPacking.targetSet
              (D.firstTurnOutgoingPacking.sourceIndexSetOfSubset sourceSet) ⊆
            D.firstTurn.outgoing.selectedLeafTargetSet :=
        D.firstTurnOutgoingPacking.targetSet_subset_right
          (D.firstTurnOutgoingPacking.sourceIndexSetOfSubset sourceSet)
      have htarget_interface :
          D.firstTurn.outgoing.selectedLeafTargetSet ⊆
            T.interface (S.selectedLeafMetaPathVertex r 2) S.child
              (T.metaTree.symm
                (by
                  simpa using
                    (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha))) := by
        dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet]
        simpa using
          (T.connector (S.selectedLeafMetaPathVertex r 1)
          (S.selectedLeafMetaPathVertex r 2)
          (S.selectedLeafMetaPathVertex_adj_succ r (a := 1) ha)).targetSet_subset_right _
      exact subset_trans htarget_subset htarget_interface
    restrictedPacking_staysIn := by
      dsimp [R, P]
      exact D.firstTurnOutgoingPacking.restrictSourceSet_staysIn sourceSet hsource
        D.firstTurnOutgoingPacking_staysIn
    restrictedPacking_internallyDisjoint_cluster_of_ne_child := by
      intro c hc
      dsimp [R, P]
      exact D.firstTurnOutgoingPacking.restrictSourceSet_internallyDisjointFromSet
        sourceSet hsource
        (D.firstTurnOutgoingPacking_internallyDisjoint_cluster_of_ne_child hc) }⟩

/-- One coherent forward advance along a selected root-to-leaf meta-path,
starting from any width-`w` subset of the incoming interface at the middle
cluster.  The outgoing connector is still chosen at the stronger `W / ell`
scale and only then restricted to width `w`. -/
structure SelectedLeafMetaPathAdvanceRouteData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (a : ℕ) (ha : a + 1 < S.selectedLeafMetaPathLength r)
    (sourceSet : Finset V) (w : ℕ) where
  source_subset_interface :
    sourceSet ⊆
      T.interface (S.selectedLeafMetaPathVertex r (a + 1))
        (S.selectedLeafMetaPathVertex r a)
        (T.metaTree.symm
          (S.selectedLeafMetaPathVertex_adj_succ r (a := a) (by omega)))
  source_card : sourceSet.card = w
  outgoing :
    SelectedLeafMetaPathEdgeTrancheData S r ⟨a + 1, ha⟩
  outgoingSourceSet : Finset V
  outgoingSource_subset :
    outgoingSourceSet ⊆ outgoing.selectedLeafSourceSet
  outgoingSource_card : outgoingSourceSet.card = w
  turnLinkage :
    PerfectPathPacking G sourceSet outgoingSourceSet
  turnLinkage_card : turnLinkage.card = w
  turnLinkage_staysIn :
    turnLinkage.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafMetaPathVertex r (a + 1)))
  advancePacking :
    PerfectPathPacking G sourceSet
      (outgoing.selectedLeafRestrictedPacking.targetSet
        (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet))
  advancePacking_card : advancePacking.card = w
  target_card :
    (outgoing.selectedLeafRestrictedPacking.targetSet
      (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet)).card = w
  target_subset_interface :
    (outgoing.selectedLeafRestrictedPacking.targetSet
      (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet)) ⊆
        T.interface (S.selectedLeafMetaPathVertex r (a + 2))
          (S.selectedLeafMetaPathVertex r (a + 1))
          (T.metaTree.symm
            (S.selectedLeafMetaPathVertex_adj_succ r (a := a + 1) ha))
  advancePacking_staysIn :
    advancePacking.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafMetaPathVertex r (a + 1)) ∪
        (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
          (S.selectedLeafMetaPathVertex r (a + 2))
          (S.selectedLeafMetaPathVertex_adj_succ r (a := a + 1) ha)).toPathPacking.vertexSet)
  advancePacking_internallyDisjoint_cluster_of_ne_mid :
    ∀ {c : Fin m}, c ≠ S.selectedLeafMetaPathVertex r (a + 1) →
      advancePacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)

/-- Existence of one coherent forward advance from an arbitrary already-routed
width-`w` incoming subset. -/
theorem exists_selectedLeafMetaPathAdvanceRouteData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r)
    (sourceSet : Finset V) {w : ℕ}
    (hw_le : w ≤ W / ell)
    (hsource_interface :
      sourceSet ⊆
        T.interface (S.selectedLeafMetaPathVertex r (a + 1))
          (S.selectedLeafMetaPathVertex r a)
          (T.metaTree.symm
            (S.selectedLeafMetaPathVertex_adj_succ r (a := a) (by omega))))
    (hsource_card : sourceSet.card = w) :
    Nonempty
      (SelectedLeafMetaPathAdvanceRouteData S r a ha sourceSet w) := by
  classical
  let prev := S.selectedLeafMetaPathVertex r a
  let mid := S.selectedLeafMetaPathVertex r (a + 1)
  let next := S.selectedLeafMetaPathVertex r (a + 2)
  let hin : T.metaTree.Adj prev mid :=
    S.selectedLeafMetaPathVertex_adj_succ r (a := a) (by omega)
  let hout : T.metaTree.Adj mid next :=
    S.selectedLeafMetaPathVertex_adj_succ r (a := a + 1) ha
  let outgoing := S.selectedLeafMetaPathEdgeTrancheData r ⟨a + 1, ha⟩
  have hw_outgoing : w ≤ outgoing.selectedLeafSourceSet.card := by
    have hcard : outgoing.selectedLeafSourceSet.card = W / ell := by
      dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet,
        SelectedLeafMetaPathEdgeTrancheData.selectedLeafTranche]
      exact outgoing.selectedLeafTranche_source_card
    rw [hcard]
    exact hw_le
  rcases Finset.exists_subset_card_eq hw_outgoing with
    ⟨outgoingSourceSet, houtgoingSource_subset, houtgoingSource_card⟩
  have hprev_next : prev ≠ next := by
    exact S.selectedLeafMetaPathVertex_ne_two_step r ha
  have houtgoing_interface :
      outgoingSourceSet ⊆ T.interface mid next hout := by
    have hselected_source :
        outgoing.selectedLeafSourceSet ⊆ T.interface mid next hout := by
      dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet,
        outgoing, mid, next, hout]
      exact (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
        (S.selectedLeafMetaPathVertex r (a + 2))
        (S.selectedLeafMetaPathVertex_adj_succ r (a := a + 1) ha)).sourceSet_subset_left _
    exact subset_trans houtgoingSource_subset hselected_source
  have hcard_eq : sourceSet.card = outgoingSourceSet.card :=
    hsource_card.trans houtgoingSource_card.symm
  rcases T.exists_interface_pair_perfect_linkage_between_subsets
      (i := mid) (j := prev) (k := next)
      (hij := T.metaTree.symm hin) (hik := hout)
      hprev_next hsource_interface houtgoing_interface hcard_eq with
    ⟨Qturn, hQturn_card, hQturn_stay⟩
  let Qout : PerfectPathPacking G outgoingSourceSet
      (outgoing.selectedLeafRestrictedPacking.targetSet
        (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet)) :=
    outgoing.selectedLeafRestrictedPacking.restrictSourceSet
      outgoingSourceSet houtgoingSource_subset
  have hQturn : Qturn.toPathPacking.StaysIn (T.cluster mid) := hQturn_stay
  have hQout_mid :
      Qout.toPathPacking.InternallyDisjointFromSet (T.cluster mid) := by
    dsimp [Qout]
    exact outgoing.selectedLeafRestrictedPacking.restrictSourceSet_internallyDisjointFromSet
      outgoingSourceSet houtgoingSource_subset
      (outgoing.selectedLeafRestrictedPacking_internallyDisjoint_clusters mid)
  have htarget_interface :
      outgoing.selectedLeafRestrictedPacking.targetSet
          (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet) ⊆
        T.interface next mid (T.metaTree.symm hout) := by
    have htarget_selected :
        outgoing.selectedLeafRestrictedPacking.targetSet
            (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet) ⊆
          outgoing.selectedLeafTargetSet :=
      outgoing.selectedLeafRestrictedPacking.targetSet_subset_right _
    have hselected_target :
        outgoing.selectedLeafTargetSet ⊆
          T.interface next mid (T.metaTree.symm hout) := by
      dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet,
        outgoing, mid, next, hout]
      exact (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
        (S.selectedLeafMetaPathVertex r (a + 2))
        (S.selectedLeafMetaPathVertex_adj_succ r (a := a + 1) ha)).targetSet_subset_right _
    exact subset_trans htarget_selected hselected_target
  have htarget_disj_mid :
      Disjoint
        (outgoing.selectedLeafRestrictedPacking.targetSet
          (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet))
        (T.cluster mid) := by
    have htarget_cluster :
        outgoing.selectedLeafRestrictedPacking.targetSet
            (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet) ⊆
          T.cluster next :=
      subset_trans htarget_interface
        (T.interface_subset_cluster next mid (T.metaTree.symm hout))
    exact Finset.disjoint_of_subset_left htarget_cluster
      (T.cluster_disjoint hout.ne.symm)
  let R : PerfectPathPacking G sourceSet
      (outgoing.selectedLeafRestrictedPacking.targetSet
        (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet)) :=
    Qturn.concatOfFirstStaysInSecondInternallyDisjoint
      Qout hQturn hQout_mid htarget_disj_mid
  have hidx_card :
      (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet).card =
        w := by
    simpa [houtgoingSource_card] using
      outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset_card
        houtgoingSource_subset
  exact ⟨{
    source_subset_interface := hsource_interface
    source_card := hsource_card
    outgoing := outgoing
    outgoingSourceSet := outgoingSourceSet
    outgoingSource_subset := houtgoingSource_subset
    outgoingSource_card := houtgoingSource_card
    turnLinkage := Qturn
    turnLinkage_card := hQturn_card.trans hsource_card
    turnLinkage_staysIn := by
      simpa [mid] using hQturn_stay
    advancePacking := R
    advancePacking_card := by
      dsimp [R]
      rw [PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_card]
      exact hQturn_card.trans hsource_card
    target_card := by
      calc
        (outgoing.selectedLeafRestrictedPacking.targetSet
            (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet)).card =
            (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet).card := by
          exact outgoing.selectedLeafRestrictedPacking.targetSet_card
            (outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset outgoingSourceSet)
        _ = w := hidx_card
    target_subset_interface := by
      simpa [mid, next, hout] using htarget_interface
    advancePacking_staysIn := by
      dsimp [R, Qout, mid, next, hout]
      exact PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        Qturn
        (outgoing.selectedLeafRestrictedPacking.restrictSourceSet
          outgoingSourceSet houtgoingSource_subset)
        hQturn hQout_mid htarget_disj_mid
        (outgoing.selectedLeafRestrictedPacking.restrictSourceSet_staysIn
          outgoingSourceSet houtgoingSource_subset
          outgoing.selectedLeafRestrictedPacking_staysIn)
    advancePacking_internallyDisjoint_cluster_of_ne_mid := by
      intro c hc
      have hPC :
          Qturn.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        intro i v hv hvC
        have hvMid : v ∈ T.cluster mid := hQturn_stay i hv
        exact False.elim
          (Finset.disjoint_left.mp
            (T.cluster_disjoint hc.symm) hvMid hvC)
      have hQC :
          Qout.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        dsimp [Qout]
        exact outgoing.selectedLeafRestrictedPacking.restrictSourceSet_internallyDisjointFromSet
          outgoingSourceSet houtgoingSource_subset
          (outgoing.selectedLeafRestrictedPacking_internallyDisjoint_clusters c)
      have hTdisj : Disjoint outgoingSourceSet (T.cluster c) := by
        have hsource_cluster : outgoingSourceSet ⊆ T.cluster mid :=
          subset_trans houtgoing_interface
            (T.interface_subset_cluster mid next hout)
        exact Finset.disjoint_of_subset_left hsource_cluster
          (T.cluster_disjoint hc.symm)
      dsimp [R]
      exact
        PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
          Qturn Qout hQturn hQout_mid htarget_disj_mid hPC hQC hTdisj }⟩

/-- A width-`w` boundary state at the `b`-th vertex of the selected
root-to-leaf meta-path.  The stored set lies in the interface from vertex `b`
back to vertex `b - 1`; this is exactly the kind of set consumed by the next
turn, or by the final parent-to-leaf advance when `b` is the selected leaf's
parent. -/
structure SelectedLeafMetaPathBoundaryState
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (b : ℕ) (w : ℕ) where
  b_pos : 0 < b
  b_lt_length : b < S.selectedLeafMetaPathLength r
  sourceSet : Finset V
  source_subset_interface :
    sourceSet ⊆
      T.interface (S.selectedLeafMetaPathVertex r b)
        (S.selectedLeafMetaPathVertex r (b - 1))
        (T.metaTree.symm
          (by
            have hb_pred_add : b - 1 + 1 = b := by omega
            simpa [hb_pred_add] using
              (S.selectedLeafMetaPathVertex_adj_succ r
                (a := b - 1) (by omega))))
  source_card : sourceSet.card = w

/-- The left child-side root-child subtranche gives the initial boundary state
at the distinguished child of the DFS root. -/
theorem exists_rootChildSelectedLeafLeftBoundaryState
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {w : ℕ} (hL : 1 < S.selectedLeafMetaPathLength r)
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    Nonempty (SelectedLeafMetaPathBoundaryState S r 1 w) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  have htarget :
      P.targetSet D.leftIndexSet ⊆
        T.interface S.child S.root (T.metaTree.symm S.root_child_adj) :=
    P.targetSet_subset_right D.leftIndexSet
  exact ⟨{
    b_pos := by omega
    b_lt_length := hL
    sourceSet := P.targetSet D.leftIndexSet
    source_subset_interface := by
      simpa [P] using htarget
    source_card := by
      simpa [P] using D.targetLeft_card }⟩

/-- The right child-side root-child subtranche gives the symmetric initial
boundary state at the distinguished child of the DFS root. -/
theorem exists_rootChildSelectedLeafRightBoundaryState
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {w : ℕ} (hL : 1 < S.selectedLeafMetaPathLength r)
    (D : RootChildSelectedLeafDoubleWidthData S r w) :
    Nonempty (SelectedLeafMetaPathBoundaryState S r 1 w) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  have htarget :
      P.targetSet D.rightIndexSet ⊆
        T.interface S.child S.root (T.metaTree.symm S.root_child_adj) :=
    P.targetSet_subset_right D.rightIndexSet
  exact ⟨{
    b_pos := by omega
    b_lt_length := hL
    sourceSet := P.targetSet D.rightIndexSet
    source_subset_interface := by
      simpa [P] using htarget
    source_card := by
      simpa [P] using D.targetRight_card }⟩

/-- Advance a selected-leaf boundary state by one internal turn, as long as the
next boundary is still before the selected leaf. -/
theorem exists_selectedLeafMetaPathBoundaryState_succ
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {b w : ℕ}
    (B : SelectedLeafMetaPathBoundaryState S r b w)
    (hb_next : b + 1 < S.selectedLeafMetaPathLength r)
    (hw_le : w ≤ W / ell) :
    Nonempty (SelectedLeafMetaPathBoundaryState S r (b + 1) w) := by
  classical
  have hb_pos : 0 < b := B.b_pos
  have hb_pred_add : b - 1 + 1 = b := by omega
  have hsource :
      B.sourceSet ⊆
        T.interface (S.selectedLeafMetaPathVertex r ((b - 1) + 1))
          (S.selectedLeafMetaPathVertex r (b - 1))
          (T.metaTree.symm
            (S.selectedLeafMetaPathVertex_adj_succ r
              (a := b - 1) (by omega))) := by
    simpa [hb_pred_add] using B.source_subset_interface
  rcases S.exists_selectedLeafMetaPathAdvanceRouteData
      r (a := b - 1) (by simpa [hb_pred_add] using B.b_lt_length)
      B.sourceSet hw_le hsource B.source_card with
    ⟨A⟩
  exact ⟨{
    b_pos := by omega
    b_lt_length := hb_next
    sourceSet :=
      A.outgoing.selectedLeafRestrictedPacking.targetSet
        (A.outgoing.selectedLeafRestrictedPacking.sourceIndexSetOfSubset
          A.outgoingSourceSet)
    source_subset_interface := by
      have hb_next_eq : (b - 1) + 2 = b + 1 := by omega
      simpa [hb_pred_add, hb_next_eq] using A.target_subset_interface
    source_card := A.target_card }⟩

/-- Starting from the left root-child side, the boundary state can be advanced
to any non-root vertex before the selected leaf on the chosen meta-path. -/
theorem exists_rootChildSelectedLeafLeftBoundaryState_at
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {b w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w)
    (hb_pos : 0 < b)
    (hb_lt : b < S.selectedLeafMetaPathLength r)
    (hw_le : w ≤ W / ell) :
    Nonempty (SelectedLeafMetaPathBoundaryState S r b w) := by
  classical
  induction b with
  | zero =>
      exact False.elim (Nat.lt_asymm hb_pos hb_pos)
  | succ b ih =>
      by_cases hb_zero : b = 0
      · subst b
        exact S.exists_rootChildSelectedLeafLeftBoundaryState r hb_lt D
      · have hb_pos' : 0 < b := Nat.pos_of_ne_zero hb_zero
        have hb_lt' : b < S.selectedLeafMetaPathLength r := by omega
        rcases ih hb_pos' hb_lt' with ⟨B⟩
        exact S.exists_selectedLeafMetaPathBoundaryState_succ
          r B hb_lt hw_le

/-- Starting from the right root-child side, the boundary state can be advanced
to any non-root vertex before the selected leaf on the chosen meta-path. -/
theorem exists_rootChildSelectedLeafRightBoundaryState_at
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {b w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w)
    (hb_pos : 0 < b)
    (hb_lt : b < S.selectedLeafMetaPathLength r)
    (hw_le : w ≤ W / ell) :
    Nonempty (SelectedLeafMetaPathBoundaryState S r b w) := by
  classical
  induction b with
  | zero =>
      exact False.elim (Nat.lt_asymm hb_pos hb_pos)
  | succ b ih =>
      by_cases hb_zero : b = 0
      · subst b
        exact S.exists_rootChildSelectedLeafRightBoundaryState r hb_lt D
      · have hb_pos' : 0 < b := Nat.pos_of_ne_zero hb_zero
        have hb_lt' : b < S.selectedLeafMetaPathLength r := by omega
        rcases ih hb_pos' hb_lt' with ⟨B⟩
        exact S.exists_selectedLeafMetaPathBoundaryState_succ
          r B hb_lt hw_le

/-- The left root-child side reaches the selected leaf's parent-side
interface, at the boundary level. -/
theorem exists_rootChildSelectedLeafLeftParentBoundaryState
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w)
    (hL : 1 < S.selectedLeafMetaPathLength r)
    (hw_le : w ≤ W / ell) :
    Nonempty
      (SelectedLeafMetaPathBoundaryState S r
        (S.selectedLeafMetaPathLength r - 1) w) := by
  exact S.exists_rootChildSelectedLeafLeftBoundaryState_at r D
    (by omega) (by omega) hw_le

/-- The right root-child side reaches the selected leaf's parent-side
interface, at the boundary level. -/
theorem exists_rootChildSelectedLeafRightParentBoundaryState
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w)
    (hL : 1 < S.selectedLeafMetaPathLength r)
    (hw_le : w ≤ W / ell) :
    Nonempty
      (SelectedLeafMetaPathBoundaryState S r
        (S.selectedLeafMetaPathLength r - 1) w) := by
  exact S.exists_rootChildSelectedLeafRightBoundaryState_at r D
    (by omega) (by omega) hw_le

/-- The full three-piece concatenation across one internal turn: incoming
connector tranche, middle-cluster linkage, and outgoing connector tranche. -/
structure SelectedLeafMetaPathFullTurnConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (a : ℕ) (ha : a + 1 < S.selectedLeafMetaPathLength r) where
  incomingTurn : SelectedLeafMetaPathIncomingTurnConcatData S r a ha
  fullTurnPacking :
    PerfectPathPacking G incomingTurn.turn.incoming.selectedLeafSourceSet
      incomingTurn.turn.outgoing.selectedLeafTargetSet
  fullTurnPacking_card : fullTurnPacking.card = W / ell
  fullTurnPacking_staysIn :
    fullTurnPacking.toPathPacking.StaysIn
      (((T.connector (S.selectedLeafMetaPathVertex r a)
          (S.selectedLeafMetaPathVertex r (a + 1))
          (S.selectedLeafMetaPathVertex_adj_succ r (by omega))).toPathPacking.vertexSet ∪
          T.cluster (S.selectedLeafMetaPathVertex r (a + 1))) ∪
        (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
          (S.selectedLeafMetaPathVertex r (a + 2))
          (S.selectedLeafMetaPathVertex_adj_succ r ha)).toPathPacking.vertexSet)
  fullTurnPacking_internallyDisjoint_cluster_of_ne_mid :
    ∀ {c : Fin m}, c ≠ S.selectedLeafMetaPathVertex r (a + 1) →
      fullTurnPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)

/-- The three local Step 1 pieces around an internal selected-leaf meta-path
turn compose to one perfect packing. -/
theorem exists_selectedLeafMetaPathFullTurnConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    Nonempty (SelectedLeafMetaPathFullTurnConcatData S r a ha) := by
  classical
  let C := S.selectedLeafMetaPathIncomingTurnConcatData r ha
  let P := C.incomingTurnPacking
  let Q := C.turn.outgoing.selectedLeafRestrictedPacking
  let prev := S.selectedLeafMetaPathVertex r a
  let mid := S.selectedLeafMetaPathVertex r (a + 1)
  let next := S.selectedLeafMetaPathVertex r (a + 2)
  let hin : T.metaTree.Adj prev mid :=
    S.selectedLeafMetaPathVertex_adj_succ r (by omega)
  let hout : T.metaTree.Adj mid next :=
    S.selectedLeafMetaPathVertex_adj_succ r ha
  let prevConnectorVertexSet : Finset V :=
    (T.connector prev mid hin).toPathPacking.vertexSet
  let outConnectorVertexSet : Finset V :=
    (T.connector mid next hout).toPathPacking.vertexSet
  let A : Finset V := prevConnectorVertexSet ∪ T.cluster mid
  have hedge_ne : s(prev, mid) ≠ s(mid, next) := by
    dsimp [prev, mid, next]
    exact S.selectedLeafMetaPathEdge_ne_succ r ha
  have hprev_out_disj :
      Disjoint prevConnectorVertexSet outConnectorVertexSet := by
    dsimp [prevConnectorVertexSet, outConnectorVertexSet]
    exact PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
      (T.connector_mutually_nodeDisjoint prev mid hin mid next hout hedge_ne)
  have hQ_stays :
      Q.toPathPacking.StaysIn outConnectorVertexSet := by
    dsimp [Q, outConnectorVertexSet, mid, next, hout]
    exact C.turn.outgoing.selectedLeafRestrictedPacking_staysIn
  have hQ_vertex_subset :
      Q.toPathPacking.vertexSet ⊆ outConnectorVertexSet :=
    PathPacking.vertexSet_subset_of_staysIn hQ_stays
  have hQ_prev_disj :
      Disjoint Q.toPathPacking.vertexSet prevConnectorVertexSet :=
    Finset.disjoint_of_subset_left hQ_vertex_subset hprev_out_disj.symm
  have hP : P.toPathPacking.StaysIn A := by
    dsimp [P, A, prevConnectorVertexSet, prev, mid, hin]
    exact C.incomingTurnPacking_staysIn
  have hQmid :
      Q.toPathPacking.InternallyDisjointFromSet (T.cluster mid) := by
    dsimp [Q, mid]
    exact C.turn.outgoing.selectedLeafRestrictedPacking_internallyDisjoint_clusters mid
  have hQ : Q.toPathPacking.InternallyDisjointFromSet A := by
    have htmp :
        Q.toPathPacking.InternallyDisjointFromSet
          (T.cluster mid ∪ prevConnectorVertexSet) :=
      PathPacking.internallyDisjointFromSet_union_of_disjoint_vertexSet
        Q.toPathPacking hQmid hQ_prev_disj
    simpa [A, Finset.union_comm] using htmp
  have htarget_next :
      C.turn.outgoing.selectedLeafTargetSet ⊆ T.cluster next := by
    have htarget_interface :
        C.turn.outgoing.selectedLeafTargetSet ⊆
          T.interface next mid (T.metaTree.symm hout) := by
      dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafTargetSet,
        mid, next, hout]
      exact (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
        (S.selectedLeafMetaPathVertex r (a + 2))
        (S.selectedLeafMetaPathVertex_adj_succ r ha)).targetSet_subset_right _
    exact subset_trans htarget_interface
      (T.interface_subset_cluster next mid (T.metaTree.symm hout))
  have htarget_prev :
      Disjoint C.turn.outgoing.selectedLeafTargetSet prevConnectorVertexSet := by
    have htarget_out :
        C.turn.outgoing.selectedLeafTargetSet ⊆ outConnectorVertexSet := by
      have htarget_Q :
          C.turn.outgoing.selectedLeafTargetSet ⊆ Q.toPathPacking.vertexSet := by
        intro v hv
        rcases Q.target_bijective.2 ⟨v, hv⟩ with ⟨i, hi⟩
        have hvtarget : (Q.path i).target = v :=
          congrArg (fun x : {x // x ∈ C.turn.outgoing.selectedLeafTargetSet} => x.1) hi
        exact (Q.toPathPacking.mem_vertexSet).2
          ⟨i, by simpa [hvtarget] using GraphPath.target_mem_vertexSet (Q.path i)⟩
      exact subset_trans htarget_Q hQ_vertex_subset
    exact Finset.disjoint_of_subset_left htarget_out hprev_out_disj.symm
  have htarget_mid :
      Disjoint C.turn.outgoing.selectedLeafTargetSet (T.cluster mid) := by
    exact Finset.disjoint_of_subset_left htarget_next
      (T.cluster_disjoint (hout.ne.symm))
  have hUdisj :
      Disjoint C.turn.outgoing.selectedLeafTargetSet A := by
    rw [Finset.disjoint_left]
    intro v hvU hvA
    rcases Finset.mem_union.mp hvA with hvPrev | hvMid
    · exact Finset.disjoint_left.mp htarget_prev hvU hvPrev
    · exact Finset.disjoint_left.mp htarget_mid hvU hvMid
  let R : PerfectPathPacking G C.turn.incoming.selectedLeafSourceSet
      C.turn.outgoing.selectedLeafTargetSet :=
    P.concatOfFirstStaysInSecondInternallyDisjoint Q hP hQ hUdisj
  exact ⟨{
    incomingTurn := C
    fullTurnPacking := R
    fullTurnPacking_card := by
      dsimp [R, P]
      rw [PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_card]
      exact C.incomingTurnPacking_card
    fullTurnPacking_staysIn := by
      dsimp [R, P, Q, A, prevConnectorVertexSet, outConnectorVertexSet,
        prev, mid, next, hin, hout]
      exact PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        C.incomingTurnPacking C.turn.outgoing.selectedLeafRestrictedPacking
        hP hQ hUdisj hQ_stays
    fullTurnPacking_internallyDisjoint_cluster_of_ne_mid := by
      intro c hc
      have hPC :
          P.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        dsimp [P]
        exact C.incomingTurnPacking_internallyDisjoint_cluster_of_ne_mid hc
      have hQC :
          Q.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        dsimp [Q]
        exact C.turn.outgoing.selectedLeafRestrictedPacking_internallyDisjoint_clusters c
      have hTdisj :
          Disjoint C.turn.outgoing.selectedLeafSourceSet (T.cluster c) := by
        have hsource_mid :
            C.turn.outgoing.selectedLeafSourceSet ⊆ T.cluster mid := by
          have hsource_interface :
              C.turn.outgoing.selectedLeafSourceSet ⊆ T.interface mid next hout := by
            dsimp [SelectedLeafMetaPathEdgeTrancheData.selectedLeafSourceSet,
              mid, next, hout]
            exact (T.connector (S.selectedLeafMetaPathVertex r (a + 1))
              (S.selectedLeafMetaPathVertex r (a + 2))
              (S.selectedLeafMetaPathVertex_adj_succ r ha)).sourceSet_subset_left _
          exact subset_trans hsource_interface
            (T.interface_subset_cluster mid next hout)
        exact Finset.disjoint_of_subset_left hsource_mid
          (T.cluster_disjoint (hc.symm))
      dsimp [R]
      exact
        PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
          P Q hP hQ hUdisj hPC hQC hTdisj }⟩

/-- A chosen full three-piece concatenation package for an internal
selected-leaf meta-path turn. -/
noncomputable def selectedLeafMetaPathFullTurnConcatData
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {a : ℕ} (ha : a + 1 < S.selectedLeafMetaPathLength r) :
    SelectedLeafMetaPathFullTurnConcatData S r a ha :=
  Classical.choice
    (S.exists_selectedLeafMetaPathFullTurnConcatData r ha)

/-- Every selected leaf has a unique parent neighbor in the meta-tree. -/
theorem exists_selected_leaf_parent
    (S : Theorem46LeafExtractionSetup T ell)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    ∃ parent : Fin m, ∃ _hparent_leaf : T.metaTree.Adj parent leaf,
      ∀ z : Fin m, T.metaTree.Adj leaf z → z = parent := by
  rcases DegreeEquals.one_exists_unique_adj (S.leaves_leaf leaf hleaf) with
    ⟨parent, hleaf_parent, hunique⟩
  exact ⟨parent, T.metaTree.symm hleaf_parent, hunique⟩

/-- The actual parent-to-leaf connector of a selected leaf admits the full
Step 2 reserve/linkage package. -/
theorem exists_selectedLeafParentStep2Data
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    ∃ parent : Fin m, ∃ hparent_leaf : T.metaTree.Adj parent leaf,
      (∀ z : Fin m, T.metaTree.Adj leaf z → z = parent) ∧
        Nonempty (SelectedLeafConnectorStep2Data S hparent_leaf) := by
  rcases S.exists_selected_leaf_parent hleaf with
    ⟨parent, hparent_leaf, hunique⟩
  exact ⟨parent, hparent_leaf, hunique,
    S.exists_selectedLeafConnectorStep2Data hell hparent_leaf hleaf⟩

/-- The actual parent-to-leaf connector of a selected leaf admits coherent
Step 2 data. -/
theorem exists_selectedLeafParentCoherentStep2Data
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves) :
    ∃ parent : Fin m, ∃ hparent_leaf : T.metaTree.Adj parent leaf,
      (∀ z : Fin m, T.metaTree.Adj leaf z → z = parent) ∧
        Nonempty (SelectedLeafConnectorCoherentStep2Data S hparent_leaf) := by
  rcases S.exists_selected_leaf_parent hleaf with
    ⟨parent, hparent_leaf, hunique⟩
  exact ⟨parent, hparent_leaf, hunique,
    S.exists_selectedLeafConnectorCoherentStep2Data hell hparent_leaf hleaf⟩

/-- The actual parent-to-leaf connector of a selected leaf admits the Step 2
package trimmed to the final width `w`. -/
theorem exists_selectedLeafParentWidthData
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves)
    {w : ℕ} (hW : 16 * w * ell ^ 2 + 1 < W) :
    ∃ parent : Fin m, ∃ hparent_leaf : T.metaTree.Adj parent leaf,
      (∀ z : Fin m, T.metaTree.Adj leaf z → z = parent) ∧
        Nonempty (SelectedLeafConnectorWidthData S hparent_leaf w) := by
  rcases S.exists_selected_leaf_parent hleaf with
    ⟨parent, hparent_leaf, hunique⟩
  exact ⟨parent, hparent_leaf, hunique,
    S.exists_selectedLeafConnectorWidthData hell hparent_leaf hleaf hW⟩

/-- The actual parent-to-leaf connector of a selected leaf admits coherent
Step 2 data trimmed to the final width `w`. -/
theorem exists_selectedLeafParentCoherentWidthData
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {leaf : Fin m} (hleaf : leaf ∈ S.leaves)
    {w : ℕ} (hW : 16 * w * ell ^ 2 + 1 < W) :
    ∃ parent : Fin m, ∃ hparent_leaf : T.metaTree.Adj parent leaf,
      (∀ z : Fin m, T.metaTree.Adj leaf z → z = parent) ∧
        Nonempty (SelectedLeafConnectorCoherentWidthData S hparent_leaf w) := by
  rcases S.exists_selected_leaf_parent hleaf with
    ⟨parent, hparent_leaf, hunique⟩
  exact ⟨parent, hparent_leaf, hunique,
    S.exists_selectedLeafConnectorCoherentWidthData hell hparent_leaf hleaf hW⟩

/-- The chosen parent of a selected leaf in the rooted meta-tree. -/
noncomputable def selectedLeafParent
    (S : Theorem46LeafExtractionSetup T ell)
    (leaf : {x : Fin m // x ∈ S.leaves}) : Fin m :=
  Classical.choose (S.exists_selected_leaf_parent leaf.property)

/-- The chosen selected-leaf parent is adjacent to the leaf. -/
theorem selectedLeafParent_adj
    (S : Theorem46LeafExtractionSetup T ell)
    (leaf : {x : Fin m // x ∈ S.leaves}) :
    T.metaTree.Adj (S.selectedLeafParent leaf) leaf.1 :=
  Classical.choose
    (Classical.choose_spec (S.exists_selected_leaf_parent leaf.property))

/-- The chosen selected-leaf parent is the unique neighbor of that leaf. -/
theorem selectedLeafParent_unique
    (S : Theorem46LeafExtractionSetup T ell)
    (leaf : {x : Fin m // x ∈ S.leaves}) :
    ∀ z : Fin m, T.metaTree.Adj leaf.1 z → z = S.selectedLeafParent leaf :=
  Classical.choose_spec
    (Classical.choose_spec (S.exists_selected_leaf_parent leaf.property))

/-- The penultimate vertex of the chosen root-to-selected-leaf meta-path is the
selected leaf's unique meta-tree parent. -/
theorem selectedLeafMetaPathVertex_penultimate_eq_parent
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell) :
    S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 1) =
      S.selectedLeafParent (S.selectedLeafSubtype r) := by
  let L := S.selectedLeafMetaPathLength r
  have hLpos : 0 < L := by
    simpa [L] using S.selectedLeafMetaPathLength_pos r
  have hpred_lt : L - 1 < L := by omega
  have hsucc : (L - 1) + 1 = L := by omega
  have hadj_raw :
      T.metaTree.Adj (S.selectedLeafMetaPathVertex r (L - 1))
        (S.selectedLeafMetaPathVertex r ((L - 1) + 1)) :=
    S.selectedLeafMetaPathVertex_adj_succ r (a := L - 1) hpred_lt
  have hadj_leaf :
      T.metaTree.Adj (S.selectedLeaf r)
        (S.selectedLeafMetaPathVertex r (L - 1)) := by
    have hadj_prev_leaf :
        T.metaTree.Adj (S.selectedLeafMetaPathVertex r (L - 1))
          (S.selectedLeaf r) := by
      simpa [L, hsucc] using hadj_raw
    exact hadj_prev_leaf.symm
  simpa [L] using
    S.selectedLeafParent_unique (S.selectedLeafSubtype r)
      (S.selectedLeafMetaPathVertex r (L - 1)) hadj_leaf

/-- The pre-penultimate vertex on a selected root-to-leaf meta-path is adjacent
to the selected leaf's parent. -/
theorem selectedLeafMetaPathVertex_prepenultimate_adj_parent
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (hL : 1 < S.selectedLeafMetaPathLength r) :
    T.metaTree.Adj
      (S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2))
      (S.selectedLeafParent (S.selectedLeafSubtype r)) := by
  let L := S.selectedLeafMetaPathLength r
  have hpred_lt : L - 2 < L := by omega
  have hsucc : (L - 2) + 1 = L - 1 := by omega
  have hadj :
      T.metaTree.Adj (S.selectedLeafMetaPathVertex r (L - 2))
        (S.selectedLeafMetaPathVertex r ((L - 2) + 1)) :=
    S.selectedLeafMetaPathVertex_adj_succ r (a := L - 2) hpred_lt
  have hparent :
      S.selectedLeafMetaPathVertex r (L - 1) =
        S.selectedLeafParent (S.selectedLeafSubtype r) := by
    simpa [L] using S.selectedLeafMetaPathVertex_penultimate_eq_parent r
  simpa [L, hsucc, hparent] using hadj

/-- The pre-penultimate vertex on a selected root-to-leaf meta-path is not the
selected leaf. -/
theorem selectedLeafMetaPathVertex_prepenultimate_ne_selectedLeaf
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (hL : 1 < S.selectedLeafMetaPathLength r) :
    S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2) ≠
      S.selectedLeaf r := by
  let L := S.selectedLeafMetaPathLength r
  have hstep : (L - 2) + 1 < L := by omega
  have hsum : (L - 2) + 2 = L := by omega
  have hneq :
      S.selectedLeafMetaPathVertex r (L - 2) ≠
        S.selectedLeafMetaPathVertex r L := by
    simpa [L, hsum] using
      (S.selectedLeafMetaPathVertex_ne_two_step r (a := L - 2) hstep)
  intro h
  exact hneq (h.trans (by
    simp [L]))

/-- The Step 2 package chosen on the actual parent-to-leaf connector. -/
noncomputable def selectedLeafParentStep2Data
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    (leaf : {x : Fin m // x ∈ S.leaves}) :
    SelectedLeafConnectorStep2Data S (S.selectedLeafParent_adj leaf) :=
  Classical.choice
    (S.exists_selectedLeafConnectorStep2Data hell
      (S.selectedLeafParent_adj leaf) leaf.property)

/-- The Step 2 parent-to-leaf package trimmed to the final width `w`. -/
noncomputable def selectedLeafParentWidthData
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {w : ℕ} (hW : 16 * w * ell ^ 2 + 1 < W)
    (leaf : {x : Fin m // x ∈ S.leaves}) :
    SelectedLeafConnectorWidthData S (S.selectedLeafParent_adj leaf) w :=
  Classical.choice
    ((S.selectedLeafParentStep2Data hell leaf).exists_widthData hell hW)

/-- The coherent Step 2 package chosen on the actual parent-to-leaf connector. -/
noncomputable def selectedLeafParentCoherentStep2Data
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    (leaf : {x : Fin m // x ∈ S.leaves}) :
    SelectedLeafConnectorCoherentStep2Data S (S.selectedLeafParent_adj leaf) :=
  Classical.choice
    (S.exists_selectedLeafConnectorCoherentStep2Data hell
      (S.selectedLeafParent_adj leaf) leaf.property)

/-- The coherent Step 2 parent-to-leaf package trimmed to the final width `w`. -/
noncomputable def selectedLeafParentCoherentWidthData
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {w : ℕ} (hW : 16 * w * ell ^ 2 + 1 < W)
    (leaf : {x : Fin m // x ∈ S.leaves}) :
    SelectedLeafConnectorCoherentWidthData S (S.selectedLeafParent_adj leaf) w :=
  Classical.choice
    ((S.selectedLeafParentCoherentStep2Data hell leaf).exists_widthData hell hW)

/-- Final left-side advance into a selected leaf.  It starts from any width-`w`
incoming interface subset at the selected leaf's parent, links inside the
parent cluster to the coherent left source set of the parent-to-leaf connector,
and then traverses that connector to the leaf's left nail set. -/
structure SelectedLeafParentLeftAdvanceRouteData
    (S : Theorem46LeafExtractionSetup T ell)
    (leaf : {x : Fin m // x ∈ S.leaves})
    (prev : Fin m)
    (hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf))
    (sourceSet : Finset V) (w : ℕ)
    (D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w) where
  source_subset_interface :
    sourceSet ⊆
      T.interface (S.selectedLeafParent leaf) prev (T.metaTree.symm hprev_parent)
  source_card : sourceSet.card = w
  parentLinkage :
    PerfectPathPacking G sourceSet
      ((T.connector (S.selectedLeafParent leaf) leaf.1
        (S.selectedLeafParent_adj leaf)).sourceSet D.leftIndexSet)
  parentLinkage_card : parentLinkage.card = w
  parentLinkage_staysIn :
    parentLinkage.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafParent leaf))
  advancePacking :
    PerfectPathPacking G sourceSet
      ((T.connector (S.selectedLeafParent leaf) leaf.1
        (S.selectedLeafParent_adj leaf)).targetSet D.leftIndexSet)
  advancePacking_card : advancePacking.card = w
  advancePacking_staysIn :
    advancePacking.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafParent leaf) ∪
        (T.connector (S.selectedLeafParent leaf) leaf.1
          (S.selectedLeafParent_adj leaf)).toPathPacking.vertexSet)
  advancePacking_internallyDisjoint_cluster_of_ne_parent :
    ∀ {c : Fin m}, c ≠ S.selectedLeafParent leaf →
      advancePacking.toPathPacking.InternallyDisjointFromSet (T.cluster c)

/-- Existence of the final left-side advance into a selected leaf. -/
theorem exists_selectedLeafParentLeftAdvanceRouteData
    (S : Theorem46LeafExtractionSetup T ell)
    (leaf : {x : Fin m // x ∈ S.leaves})
    {prev : Fin m}
    (hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf))
    (hprev_ne_leaf : prev ≠ leaf.1)
    (sourceSet : Finset V) {w : ℕ}
    (D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w)
    (hsource_interface :
      sourceSet ⊆
        T.interface (S.selectedLeafParent leaf) prev
          (T.metaTree.symm hprev_parent))
    (hsource_card : sourceSet.card = w) :
    Nonempty
      (SelectedLeafParentLeftAdvanceRouteData
        S leaf prev hprev_parent sourceSet w D) := by
  classical
  let parent := S.selectedLeafParent leaf
  let hparent_leaf := S.selectedLeafParent_adj leaf
  let P := T.connector parent leaf.1 hparent_leaf
  have hleft_source_interface :
      P.sourceSet D.leftIndexSet ⊆ T.interface parent leaf.1 hparent_leaf :=
    P.sourceSet_subset_left D.leftIndexSet
  have hcard_eq : sourceSet.card = (P.sourceSet D.leftIndexSet).card := by
    exact hsource_card.trans D.sourceLeft_card.symm
  rcases T.exists_interface_pair_perfect_linkage_between_subsets
      (i := parent) (j := prev) (k := leaf.1)
      (hij := T.metaTree.symm hprev_parent) (hik := hparent_leaf)
      hprev_ne_leaf hsource_interface hleft_source_interface hcard_eq with
    ⟨Qturn, hQturn_card, hQturn_stay⟩
  have hQturn :
      Qturn.toPathPacking.StaysIn (T.cluster parent) :=
    hQturn_stay
  have hQconn :
      D.leftRestrictedPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster parent) := by
    exact D.leftRestrictedPacking_internallyDisjoint_clusters parent
  have htarget_disj_parent :
      Disjoint (P.targetSet D.leftIndexSet) (T.cluster parent) := by
    have htarget_cluster : P.targetSet D.leftIndexSet ⊆ T.cluster leaf.1 := by
      exact subset_trans (P.targetSet_subset_right D.leftIndexSet)
        (T.interface_subset_cluster leaf.1 parent (T.metaTree.symm hparent_leaf))
    exact Finset.disjoint_of_subset_left htarget_cluster
      (T.cluster_disjoint hparent_leaf.ne.symm)
  let R : PerfectPathPacking G sourceSet (P.targetSet D.leftIndexSet) :=
    Qturn.concatOfFirstStaysInSecondInternallyDisjoint
      D.leftRestrictedPacking hQturn hQconn htarget_disj_parent
  exact ⟨{
    source_subset_interface := hsource_interface
    source_card := hsource_card
    parentLinkage := Qturn
    parentLinkage_card := hQturn_card.trans hsource_card
    parentLinkage_staysIn := by
      simpa [parent] using hQturn_stay
    advancePacking := R
    advancePacking_card := by
      dsimp [R]
      rw [PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_card]
      exact hQturn_card.trans hsource_card
    advancePacking_staysIn := by
      dsimp [R, P, parent, hparent_leaf]
      exact PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        Qturn D.leftRestrictedPacking hQturn hQconn htarget_disj_parent
        D.leftRestrictedPacking_staysIn
    advancePacking_internallyDisjoint_cluster_of_ne_parent := by
      intro c hc
      have hPC :
          Qturn.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        intro i v hv hvC
        have hvParent : v ∈ T.cluster parent := hQturn_stay i hv
        exact False.elim
          (Finset.disjoint_left.mp
            (T.cluster_disjoint hc.symm) hvParent hvC)
      have hQC :
          D.leftRestrictedPacking.toPathPacking.InternallyDisjointFromSet
            (T.cluster c) :=
        D.leftRestrictedPacking_internallyDisjoint_clusters c
      have hTdisj :
          Disjoint (P.sourceSet D.leftIndexSet) (T.cluster c) := by
        have hsource_parent : P.sourceSet D.leftIndexSet ⊆ T.cluster parent := by
          exact subset_trans (P.sourceSet_subset_left D.leftIndexSet)
            (T.interface_subset_cluster parent leaf.1 hparent_leaf)
        exact Finset.disjoint_of_subset_left hsource_parent
          (T.cluster_disjoint hc.symm)
      dsimp [R]
      exact
        PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
          Qturn D.leftRestrictedPacking hQturn hQconn htarget_disj_parent
          hPC hQC hTdisj }⟩

/-- Final right-side advance into a selected leaf, symmetric to
`SelectedLeafParentLeftAdvanceRouteData`. -/
structure SelectedLeafParentRightAdvanceRouteData
    (S : Theorem46LeafExtractionSetup T ell)
    (leaf : {x : Fin m // x ∈ S.leaves})
    (prev : Fin m)
    (hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf))
    (sourceSet : Finset V) (w : ℕ)
    (D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w) where
  source_subset_interface :
    sourceSet ⊆
      T.interface (S.selectedLeafParent leaf) prev (T.metaTree.symm hprev_parent)
  source_card : sourceSet.card = w
  parentLinkage :
    PerfectPathPacking G sourceSet
      ((T.connector (S.selectedLeafParent leaf) leaf.1
        (S.selectedLeafParent_adj leaf)).sourceSet D.rightIndexSet)
  parentLinkage_card : parentLinkage.card = w
  parentLinkage_staysIn :
    parentLinkage.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafParent leaf))
  advancePacking :
    PerfectPathPacking G sourceSet
      ((T.connector (S.selectedLeafParent leaf) leaf.1
        (S.selectedLeafParent_adj leaf)).targetSet D.rightIndexSet)
  advancePacking_card : advancePacking.card = w
  advancePacking_staysIn :
    advancePacking.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafParent leaf) ∪
        (T.connector (S.selectedLeafParent leaf) leaf.1
          (S.selectedLeafParent_adj leaf)).toPathPacking.vertexSet)
  advancePacking_internallyDisjoint_cluster_of_ne_parent :
    ∀ {c : Fin m}, c ≠ S.selectedLeafParent leaf →
      advancePacking.toPathPacking.InternallyDisjointFromSet (T.cluster c)

/-- Existence of the final right-side advance into a selected leaf. -/
theorem exists_selectedLeafParentRightAdvanceRouteData
    (S : Theorem46LeafExtractionSetup T ell)
    (leaf : {x : Fin m // x ∈ S.leaves})
    {prev : Fin m}
    (hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf))
    (hprev_ne_leaf : prev ≠ leaf.1)
    (sourceSet : Finset V) {w : ℕ}
    (D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w)
    (hsource_interface :
      sourceSet ⊆
        T.interface (S.selectedLeafParent leaf) prev
          (T.metaTree.symm hprev_parent))
    (hsource_card : sourceSet.card = w) :
    Nonempty
      (SelectedLeafParentRightAdvanceRouteData
        S leaf prev hprev_parent sourceSet w D) := by
  classical
  let parent := S.selectedLeafParent leaf
  let hparent_leaf := S.selectedLeafParent_adj leaf
  let P := T.connector parent leaf.1 hparent_leaf
  have hright_source_interface :
      P.sourceSet D.rightIndexSet ⊆ T.interface parent leaf.1 hparent_leaf :=
    P.sourceSet_subset_left D.rightIndexSet
  have hcard_eq : sourceSet.card = (P.sourceSet D.rightIndexSet).card := by
    exact hsource_card.trans D.sourceRight_card.symm
  rcases T.exists_interface_pair_perfect_linkage_between_subsets
      (i := parent) (j := prev) (k := leaf.1)
      (hij := T.metaTree.symm hprev_parent) (hik := hparent_leaf)
      hprev_ne_leaf hsource_interface hright_source_interface hcard_eq with
    ⟨Qturn, hQturn_card, hQturn_stay⟩
  have hQturn :
      Qturn.toPathPacking.StaysIn (T.cluster parent) :=
    hQturn_stay
  have hQconn :
      D.rightRestrictedPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster parent) := by
    exact D.rightRestrictedPacking_internallyDisjoint_clusters parent
  have htarget_disj_parent :
      Disjoint (P.targetSet D.rightIndexSet) (T.cluster parent) := by
    have htarget_cluster : P.targetSet D.rightIndexSet ⊆ T.cluster leaf.1 := by
      exact subset_trans (P.targetSet_subset_right D.rightIndexSet)
        (T.interface_subset_cluster leaf.1 parent (T.metaTree.symm hparent_leaf))
    exact Finset.disjoint_of_subset_left htarget_cluster
      (T.cluster_disjoint hparent_leaf.ne.symm)
  let R : PerfectPathPacking G sourceSet (P.targetSet D.rightIndexSet) :=
    Qturn.concatOfFirstStaysInSecondInternallyDisjoint
      D.rightRestrictedPacking hQturn hQconn htarget_disj_parent
  exact ⟨{
    source_subset_interface := hsource_interface
    source_card := hsource_card
    parentLinkage := Qturn
    parentLinkage_card := hQturn_card.trans hsource_card
    parentLinkage_staysIn := by
      simpa [parent] using hQturn_stay
    advancePacking := R
    advancePacking_card := by
      dsimp [R]
      rw [PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_card]
      exact hQturn_card.trans hsource_card
    advancePacking_staysIn := by
      dsimp [R, P, parent, hparent_leaf]
      exact PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
        Qturn D.rightRestrictedPacking hQturn hQconn htarget_disj_parent
        D.rightRestrictedPacking_staysIn
    advancePacking_internallyDisjoint_cluster_of_ne_parent := by
      intro c hc
      have hPC :
          Qturn.toPathPacking.InternallyDisjointFromSet (T.cluster c) := by
        intro i v hv hvC
        have hvParent : v ∈ T.cluster parent := hQturn_stay i hv
        exact False.elim
          (Finset.disjoint_left.mp
            (T.cluster_disjoint hc.symm) hvParent hvC)
      have hQC :
          D.rightRestrictedPacking.toPathPacking.InternallyDisjointFromSet
            (T.cluster c) :=
        D.rightRestrictedPacking_internallyDisjoint_clusters c
      have hTdisj :
          Disjoint (P.sourceSet D.rightIndexSet) (T.cluster c) := by
        have hsource_parent : P.sourceSet D.rightIndexSet ⊆ T.cluster parent := by
          exact subset_trans (P.sourceSet_subset_left D.rightIndexSet)
            (T.interface_subset_cluster parent leaf.1 hparent_leaf)
        exact Finset.disjoint_of_subset_left hsource_parent
          (T.cluster_disjoint hc.symm)
      dsimp [R]
      exact
        PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
          Qturn D.rightRestrictedPacking hQturn hQconn htarget_disj_parent
          hPC hQC hTdisj }⟩

/-- The final left-side advance instantiated at the actual pre-penultimate
vertex of the selected root-to-leaf meta-path. -/
theorem exists_selectedLeafParentLeftAdvanceRouteData_prepenultimate
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (hL : 1 < S.selectedLeafMetaPathLength r)
    (sourceSet : Finset V) {w : ℕ}
    (D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj (S.selectedLeafSubtype r)) w)
    (hsource_interface :
      sourceSet ⊆
        T.interface (S.selectedLeafParent (S.selectedLeafSubtype r))
          (S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2))
          (T.metaTree.symm
            (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)))
    (hsource_card : sourceSet.card = w) :
    Nonempty
      (SelectedLeafParentLeftAdvanceRouteData S (S.selectedLeafSubtype r)
        (S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2))
        (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)
        sourceSet w D) :=
  S.exists_selectedLeafParentLeftAdvanceRouteData
    (S.selectedLeafSubtype r)
    (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)
    (S.selectedLeafMetaPathVertex_prepenultimate_ne_selectedLeaf r hL)
    sourceSet D hsource_interface hsource_card

/-- The final right-side advance instantiated at the actual pre-penultimate
vertex of the selected root-to-leaf meta-path. -/
theorem exists_selectedLeafParentRightAdvanceRouteData_prepenultimate
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (hL : 1 < S.selectedLeafMetaPathLength r)
    (sourceSet : Finset V) {w : ℕ}
    (D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj (S.selectedLeafSubtype r)) w)
    (hsource_interface :
      sourceSet ⊆
        T.interface (S.selectedLeafParent (S.selectedLeafSubtype r))
          (S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2))
          (T.metaTree.symm
            (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)))
    (hsource_card : sourceSet.card = w) :
    Nonempty
      (SelectedLeafParentRightAdvanceRouteData S (S.selectedLeafSubtype r)
        (S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2))
        (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)
        sourceSet w D) :=
  S.exists_selectedLeafParentRightAdvanceRouteData
    (S.selectedLeafSubtype r)
    (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)
    (S.selectedLeafMetaPathVertex_prepenultimate_ne_selectedLeaf r hL)
    sourceSet D hsource_interface hsource_card

/-- A boundary state at the selected leaf's parent feeds the coherent final
left-side parent-to-leaf advance. -/
theorem exists_selectedLeafParentLeftAdvanceRouteData_of_boundaryState
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (hL : 1 < S.selectedLeafMetaPathLength r)
    {w : ℕ}
    (B : SelectedLeafMetaPathBoundaryState
      S r (S.selectedLeafMetaPathLength r - 1) w)
    (D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj (S.selectedLeafSubtype r)) w) :
    Nonempty
      (SelectedLeafParentLeftAdvanceRouteData S (S.selectedLeafSubtype r)
        (S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2))
        (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)
        B.sourceSet w D) := by
  classical
  let L := S.selectedLeafMetaPathLength r
  have hparent :
      S.selectedLeafMetaPathVertex r (L - 1) =
        S.selectedLeafParent (S.selectedLeafSubtype r) := by
    simpa [L] using S.selectedLeafMetaPathVertex_penultimate_eq_parent r
  have hprev : (L - 1) - 1 = L - 2 := by omega
  have hsource :
      B.sourceSet ⊆
        T.interface (S.selectedLeafParent (S.selectedLeafSubtype r))
          (S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2))
          (T.metaTree.symm
            (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)) := by
    simpa [L, hparent, hprev] using B.source_subset_interface
  exact S.exists_selectedLeafParentLeftAdvanceRouteData_prepenultimate
    r hL B.sourceSet D hsource B.source_card

/-- A boundary state at the selected leaf's parent feeds the coherent final
right-side parent-to-leaf advance. -/
theorem exists_selectedLeafParentRightAdvanceRouteData_of_boundaryState
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    (hL : 1 < S.selectedLeafMetaPathLength r)
    {w : ℕ}
    (B : SelectedLeafMetaPathBoundaryState
      S r (S.selectedLeafMetaPathLength r - 1) w)
    (D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj (S.selectedLeafSubtype r)) w) :
    Nonempty
      (SelectedLeafParentRightAdvanceRouteData S (S.selectedLeafSubtype r)
        (S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2))
        (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)
        B.sourceSet w D) := by
  classical
  let L := S.selectedLeafMetaPathLength r
  have hparent :
      S.selectedLeafMetaPathVertex r (L - 1) =
        S.selectedLeafParent (S.selectedLeafSubtype r) := by
    simpa [L] using S.selectedLeafMetaPathVertex_penultimate_eq_parent r
  have hprev : (L - 1) - 1 = L - 2 := by omega
  have hsource :
      B.sourceSet ⊆
        T.interface (S.selectedLeafParent (S.selectedLeafSubtype r))
          (S.selectedLeafMetaPathVertex r (S.selectedLeafMetaPathLength r - 2))
          (T.metaTree.symm
            (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)) := by
    simpa [L, hparent, hprev] using B.source_subset_interface
  exact S.exists_selectedLeafParentRightAdvanceRouteData_prepenultimate
    r hL B.sourceSet D hsource B.source_card

/-- The left root-child boundary chain reaches the selected leaf parent and
then feeds the coherent final left parent-to-leaf advance.  This is a boundary
skeleton: it records the parent-side boundary state used by the final advance,
but does not yet concatenate all earlier route pieces into one packing. -/
theorem exists_selectedLeafParentLeftAdvanceRouteData_after_leftBoundaryAdvances
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {w : ℕ}
    (Droot : RootChildSelectedLeafDoubleWidthData S r w)
    (Dparent : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj (S.selectedLeafSubtype r)) w)
    (hL : 1 < S.selectedLeafMetaPathLength r)
    (hw_le : w ≤ W / ell) :
    ∃ B : SelectedLeafMetaPathBoundaryState S r
        (S.selectedLeafMetaPathLength r - 1) w,
      Nonempty
        (SelectedLeafParentLeftAdvanceRouteData S (S.selectedLeafSubtype r)
          (S.selectedLeafMetaPathVertex r
            (S.selectedLeafMetaPathLength r - 2))
          (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)
          B.sourceSet w Dparent) := by
  rcases S.exists_rootChildSelectedLeafLeftParentBoundaryState
      r Droot hL hw_le with ⟨B⟩
  exact ⟨B,
    S.exists_selectedLeafParentLeftAdvanceRouteData_of_boundaryState
      r hL B Dparent⟩

/-- The right root-child boundary chain reaches the selected leaf parent and
then feeds the coherent final right parent-to-leaf advance. -/
theorem exists_selectedLeafParentRightAdvanceRouteData_after_rightBoundaryAdvances
    (S : Theorem46LeafExtractionSetup T ell) (r : Fin ell)
    {w : ℕ}
    (Droot : RootChildSelectedLeafDoubleWidthData S r w)
    (Dparent : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj (S.selectedLeafSubtype r)) w)
    (hL : 1 < S.selectedLeafMetaPathLength r)
    (hw_le : w ≤ W / ell) :
    ∃ B : SelectedLeafMetaPathBoundaryState S r
        (S.selectedLeafMetaPathLength r - 1) w,
      Nonempty
        (SelectedLeafParentRightAdvanceRouteData S (S.selectedLeafSubtype r)
          (S.selectedLeafMetaPathVertex r
            (S.selectedLeafMetaPathLength r - 2))
          (S.selectedLeafMetaPathVertex_prepenultimate_adj_parent r hL)
          B.sourceSet w Dparent) := by
  rcases S.exists_rootChildSelectedLeafRightParentBoundaryState
      r Droot hL hw_le with ⟨B⟩
  exact ⟨B,
    S.exists_selectedLeafParentRightAdvanceRouteData_of_boundaryState
      r hL B Dparent⟩

/-- Reverse of a final left-side advance, from the selected leaf's left nails
back to the incoming parent-side interface subset. -/
noncomputable def SelectedLeafParentLeftAdvanceRouteData.leafToParentIncomingPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {leaf : {x : Fin m // x ∈ S.leaves}}
    {prev : Fin m}
    {hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf)}
    {sourceSet : Finset V} {w : ℕ}
    {D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w}
    (A : SelectedLeafParentLeftAdvanceRouteData
      S leaf prev hprev_parent sourceSet w D) :
    PerfectPathPacking G
      ((T.connector (S.selectedLeafParent leaf) leaf.1
        (S.selectedLeafParent_adj leaf)).targetSet D.leftIndexSet)
      sourceSet :=
  A.advancePacking.reverse

@[simp] theorem SelectedLeafParentLeftAdvanceRouteData.leafToParentIncomingPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {leaf : {x : Fin m // x ∈ S.leaves}}
    {prev : Fin m}
    {hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf)}
    {sourceSet : Finset V} {w : ℕ}
    {D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w}
    (A : SelectedLeafParentLeftAdvanceRouteData
      S leaf prev hprev_parent sourceSet w D) :
    A.leafToParentIncomingPacking.card = w := by
  dsimp [SelectedLeafParentLeftAdvanceRouteData.leafToParentIncomingPacking]
  simp [A.advancePacking_card]

/-- Reversing a final left-side advance preserves its containment region. -/
theorem SelectedLeafParentLeftAdvanceRouteData.leafToParentIncomingPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {leaf : {x : Fin m // x ∈ S.leaves}}
    {prev : Fin m}
    {hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf)}
    {sourceSet : Finset V} {w : ℕ}
    {D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w}
    (A : SelectedLeafParentLeftAdvanceRouteData
      S leaf prev hprev_parent sourceSet w D) :
    A.leafToParentIncomingPacking.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafParent leaf) ∪
        (T.connector (S.selectedLeafParent leaf) leaf.1
          (S.selectedLeafParent_adj leaf)).toPathPacking.vertexSet) := by
  dsimp [SelectedLeafParentLeftAdvanceRouteData.leafToParentIncomingPacking]
  exact PerfectPathPacking.reverse_staysIn A.advancePacking
    A.advancePacking_staysIn

/-- Reversing a final left-side advance preserves cluster internal
disjointness away from the selected leaf parent. -/
theorem SelectedLeafParentLeftAdvanceRouteData.leafToParentIncomingPacking_internallyDisjoint_cluster_of_ne_parent
    {S : Theorem46LeafExtractionSetup T ell}
    {leaf : {x : Fin m // x ∈ S.leaves}}
    {prev : Fin m}
    {hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf)}
    {sourceSet : Finset V} {w : ℕ}
    {D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w}
    (A : SelectedLeafParentLeftAdvanceRouteData
      S leaf prev hprev_parent sourceSet w D)
    {c : Fin m} (hc : c ≠ S.selectedLeafParent leaf) :
    A.leafToParentIncomingPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [SelectedLeafParentLeftAdvanceRouteData.leafToParentIncomingPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet A.advancePacking
    (A.advancePacking_internallyDisjoint_cluster_of_ne_parent hc)

/-- Reverse of a final right-side advance, from the selected leaf's right nails
back to the incoming parent-side interface subset. -/
noncomputable def SelectedLeafParentRightAdvanceRouteData.leafToParentIncomingPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {leaf : {x : Fin m // x ∈ S.leaves}}
    {prev : Fin m}
    {hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf)}
    {sourceSet : Finset V} {w : ℕ}
    {D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w}
    (A : SelectedLeafParentRightAdvanceRouteData
      S leaf prev hprev_parent sourceSet w D) :
    PerfectPathPacking G
      ((T.connector (S.selectedLeafParent leaf) leaf.1
        (S.selectedLeafParent_adj leaf)).targetSet D.rightIndexSet)
      sourceSet :=
  A.advancePacking.reverse

@[simp] theorem SelectedLeafParentRightAdvanceRouteData.leafToParentIncomingPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {leaf : {x : Fin m // x ∈ S.leaves}}
    {prev : Fin m}
    {hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf)}
    {sourceSet : Finset V} {w : ℕ}
    {D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w}
    (A : SelectedLeafParentRightAdvanceRouteData
      S leaf prev hprev_parent sourceSet w D) :
    A.leafToParentIncomingPacking.card = w := by
  dsimp [SelectedLeafParentRightAdvanceRouteData.leafToParentIncomingPacking]
  simp [A.advancePacking_card]

/-- Reversing a final right-side advance preserves its containment region. -/
theorem SelectedLeafParentRightAdvanceRouteData.leafToParentIncomingPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {leaf : {x : Fin m // x ∈ S.leaves}}
    {prev : Fin m}
    {hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf)}
    {sourceSet : Finset V} {w : ℕ}
    {D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w}
    (A : SelectedLeafParentRightAdvanceRouteData
      S leaf prev hprev_parent sourceSet w D) :
    A.leafToParentIncomingPacking.toPathPacking.StaysIn
      (T.cluster (S.selectedLeafParent leaf) ∪
        (T.connector (S.selectedLeafParent leaf) leaf.1
          (S.selectedLeafParent_adj leaf)).toPathPacking.vertexSet) := by
  dsimp [SelectedLeafParentRightAdvanceRouteData.leafToParentIncomingPacking]
  exact PerfectPathPacking.reverse_staysIn A.advancePacking
    A.advancePacking_staysIn

/-- Reversing a final right-side advance preserves cluster internal
disjointness away from the selected leaf parent. -/
theorem SelectedLeafParentRightAdvanceRouteData.leafToParentIncomingPacking_internallyDisjoint_cluster_of_ne_parent
    {S : Theorem46LeafExtractionSetup T ell}
    {leaf : {x : Fin m // x ∈ S.leaves}}
    {prev : Fin m}
    {hprev_parent : T.metaTree.Adj prev (S.selectedLeafParent leaf)}
    {sourceSet : Finset V} {w : ℕ}
    {D : SelectedLeafConnectorCoherentWidthData S
      (S.selectedLeafParent_adj leaf) w}
    (A : SelectedLeafParentRightAdvanceRouteData
      S leaf prev hprev_parent sourceSet w D)
    {c : Fin m} (hc : c ≠ S.selectedLeafParent leaf) :
    A.leafToParentIncomingPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [SelectedLeafParentRightAdvanceRouteData.leafToParentIncomingPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet A.advancePacking
    (A.advancePacking_internallyDisjoint_cluster_of_ne_parent hc)

/-- Step 1 data on the root-child connector, where the child contains all
selected leaves below it. -/
structure RootChildConnectorStep1Data
    (S : Theorem46LeafExtractionSetup T ell) where
  indexSet : Finset (T.connector S.root S.child S.root_child_adj).Index
  index_card : indexSet.card = ell * (W / ell)
  source_card :
    ((T.connector S.root S.child S.root_child_adj).sourceSet indexSet).card =
      ell * (W / ell)
  target_card :
    ((T.connector S.root S.child S.root_child_adj).targetSet indexSet).card =
      ell * (W / ell)
  restricted_card :
    ((T.connector S.root S.child S.root_child_adj).restrictIndexSet indexSet).card =
      ell * (W / ell)
  restricted_staysIn :
    PathPacking.StaysIn
      (((T.connector S.root S.child S.root_child_adj).restrictIndexSet indexSet).toPathPacking)
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  restricted_internallyDisjoint_clusters :
    ∀ r : Fin m,
      PathPacking.InternallyDisjointFromSet
        (((T.connector S.root S.child S.root_child_adj).restrictIndexSet indexSet).toPathPacking)
        (T.cluster r)

/-- The root-child Step 1 bundle split into one ordered tranche per selected
leaf. -/
structure RootChildConnectorTrancheData
    (S : Theorem46LeafExtractionSetup T ell) where
  step1 : RootChildConnectorStep1Data S
  tranche :
    Fin ell → Finset (T.connector S.root S.child S.root_child_adj).Index
  tranche_subset_index : ∀ r : Fin ell, tranche r ⊆ step1.indexSet
  tranche_card : ∀ r : Fin ell, (tranche r).card = W / ell
  tranche_pairwise_disjoint :
    ∀ ⦃r s : Fin ell⦄, r ≠ s → Disjoint (tranche r) (tranche s)
  source_card :
    ∀ r : Fin ell,
      ((T.connector S.root S.child S.root_child_adj).sourceSet
        (tranche r)).card = W / ell
  target_card :
    ∀ r : Fin ell,
      ((T.connector S.root S.child S.root_child_adj).targetSet
        (tranche r)).card = W / ell
  restricted_card :
    ∀ r : Fin ell,
      ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
        (tranche r)).card = W / ell
  restricted_staysIn :
    ∀ r : Fin ell,
      (((T.connector S.root S.child S.root_child_adj).restrictIndexSet
        (tranche r)).toPathPacking).StaysIn
          (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  restricted_internallyDisjoint_clusters :
    ∀ r : Fin ell, ∀ c : Fin m,
      PathPacking.InternallyDisjointFromSet
        (((T.connector S.root S.child S.root_child_adj).restrictIndexSet
          (tranche r)).toPathPacking)
        (T.cluster c)
  restricted_mutuallyNodeDisjoint :
    ∀ ⦃r s : Fin ell⦄, r ≠ s →
      (((T.connector S.root S.child S.root_child_adj).restrictIndexSet
        (tranche r)).toPathPacking).MutuallyNodeDisjoint
      (((T.connector S.root S.child S.root_child_adj).restrictIndexSet
        (tranche s)).toPathPacking)

/-- A width-`w` linkage inside the root cluster between two root-child
tranches.  The connector index subsets are kept, so the linkage can later be
concatenated with the corresponding root-child connector restrictions. -/
structure RootChildTranchePairWidthLinkageData
    (S : Theorem46LeafExtractionSetup T ell)
    (R : RootChildConnectorTrancheData S) (r s : Fin ell) (w : ℕ) where
  leftIndexSet :
    Finset (T.connector S.root S.child S.root_child_adj).Index
  rightIndexSet :
    Finset (T.connector S.root S.child S.root_child_adj).Index
  leftIndex_subset_tranche : leftIndexSet ⊆ R.tranche r
  rightIndex_subset_tranche : rightIndexSet ⊆ R.tranche s
  leftIndex_subset_index : leftIndexSet ⊆ R.step1.indexSet
  rightIndex_subset_index : rightIndexSet ⊆ R.step1.indexSet
  leftIndex_card : leftIndexSet.card = w
  rightIndex_card : rightIndexSet.card = w
  index_disjoint : Disjoint leftIndexSet rightIndexSet
  sourceLinkage :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet rightIndexSet)
  sourceLeft_card :
    ((T.connector S.root S.child S.root_child_adj).sourceSet leftIndexSet).card =
      w
  sourceRight_card :
    ((T.connector S.root S.child S.root_child_adj).sourceSet rightIndexSet).card =
      w
  targetLeft_card :
    ((T.connector S.root S.child S.root_child_adj).targetSet leftIndexSet).card =
      w
  targetRight_card :
    ((T.connector S.root S.child S.root_child_adj).targetSet rightIndexSet).card =
      w
  source_disjoint :
    Disjoint
      ((T.connector S.root S.child S.root_child_adj).sourceSet leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet rightIndexSet)
  target_disjoint :
    Disjoint
      ((T.connector S.root S.child S.root_child_adj).targetSet leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet rightIndexSet)
  sourceLinkage_card : sourceLinkage.card = w
  sourceLinkage_staysIn : sourceLinkage.toPathPacking.StaysIn (T.cluster S.root)
  leftRestricted_staysIn :
    ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
      leftIndexSet).toPathPacking.StaysIn
        (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  rightRestricted_staysIn :
    ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
      rightIndexSet).toPathPacking.StaysIn
        (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  leftRestricted_internallyDisjoint_clusters :
    ∀ c : Fin m,
      PathPacking.InternallyDisjointFromSet
        ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
          leftIndexSet).toPathPacking
        (T.cluster c)
  rightRestricted_internallyDisjoint_clusters :
    ∀ c : Fin m,
      PathPacking.InternallyDisjointFromSet
        ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
          rightIndexSet).toPathPacking
        (T.cluster c)

/-- The left restricted root-child connector in a tranche-pair package. -/
noncomputable def RootChildTranchePairWidthLinkageData.leftRestrictedPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet D.leftIndexSet) :=
  (T.connector S.root S.child S.root_child_adj).restrictIndexSet D.leftIndexSet

/-- The right restricted root-child connector in a tranche-pair package. -/
noncomputable def RootChildTranchePairWidthLinkageData.rightRestrictedPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet D.rightIndexSet) :=
  (T.connector S.root S.child S.root_child_adj).restrictIndexSet D.rightIndexSet

@[simp] theorem RootChildTranchePairWidthLinkageData.leftRestrictedPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.leftRestrictedPacking.card = w := by
  dsimp [RootChildTranchePairWidthLinkageData.leftRestrictedPacking]
  simp [D.leftIndex_card]

@[simp] theorem RootChildTranchePairWidthLinkageData.rightRestrictedPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.rightRestrictedPacking.card = w := by
  dsimp [RootChildTranchePairWidthLinkageData.rightRestrictedPacking]
  simp [D.rightIndex_card]

/-- The left restricted root-child connector stays inside the full connector
vertex set. -/
theorem RootChildTranchePairWidthLinkageData.leftRestrictedPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.leftRestrictedPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildTranchePairWidthLinkageData.leftRestrictedPacking]
  exact D.leftRestricted_staysIn

/-- The right restricted root-child connector stays inside the full connector
vertex set. -/
theorem RootChildTranchePairWidthLinkageData.rightRestrictedPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.rightRestrictedPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildTranchePairWidthLinkageData.rightRestrictedPacking]
  exact D.rightRestricted_staysIn

/-- The left restricted root-child connector is internally disjoint from every
cluster. -/
theorem RootChildTranchePairWidthLinkageData.leftRestrictedPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) (c : Fin m) :
    D.leftRestrictedPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildTranchePairWidthLinkageData.leftRestrictedPacking]
  exact D.leftRestricted_internallyDisjoint_clusters c

/-- The right restricted root-child connector is internally disjoint from every
cluster. -/
theorem RootChildTranchePairWidthLinkageData.rightRestrictedPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) (c : Fin m) :
    D.rightRestrictedPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildTranchePairWidthLinkageData.rightRestrictedPacking]
  exact D.rightRestricted_internallyDisjoint_clusters c

/-- The left root-child connector, traversed from the child side back to the
root. -/
noncomputable def RootChildTranchePairWidthLinkageData.leftChildToRootPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet D.leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.leftIndexSet) :=
  D.leftRestrictedPacking.reverse

/-- The right root-child connector, traversed from the child side back to the
root. -/
noncomputable def RootChildTranchePairWidthLinkageData.rightChildToRootPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet D.rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.rightIndexSet) :=
  D.rightRestrictedPacking.reverse

@[simp] theorem RootChildTranchePairWidthLinkageData.leftChildToRootPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.leftChildToRootPacking.card = w := by
  dsimp [RootChildTranchePairWidthLinkageData.leftChildToRootPacking]
  simp

@[simp] theorem RootChildTranchePairWidthLinkageData.rightChildToRootPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.rightChildToRootPacking.card = w := by
  dsimp [RootChildTranchePairWidthLinkageData.rightChildToRootPacking]
  simp

/-- Reversing the left restricted root-child connector preserves connector
containment. -/
theorem RootChildTranchePairWidthLinkageData.leftChildToRootPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.leftChildToRootPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildTranchePairWidthLinkageData.leftChildToRootPacking]
  exact PerfectPathPacking.reverse_staysIn D.leftRestrictedPacking
    D.leftRestrictedPacking_staysIn

/-- Reversing the right restricted root-child connector preserves connector
containment. -/
theorem RootChildTranchePairWidthLinkageData.rightChildToRootPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.rightChildToRootPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildTranchePairWidthLinkageData.rightChildToRootPacking]
  exact PerfectPathPacking.reverse_staysIn D.rightRestrictedPacking
    D.rightRestrictedPacking_staysIn

/-- Reversing the left restricted root-child connector preserves cluster
internal disjointness. -/
theorem RootChildTranchePairWidthLinkageData.leftChildToRootPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) (c : Fin m) :
    D.leftChildToRootPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildTranchePairWidthLinkageData.leftChildToRootPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet
    D.leftRestrictedPacking
    (D.leftRestrictedPacking_internallyDisjoint_clusters c)

/-- Reversing the right restricted root-child connector preserves cluster
internal disjointness. -/
theorem RootChildTranchePairWidthLinkageData.rightChildToRootPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) (c : Fin m) :
    D.rightChildToRootPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildTranchePairWidthLinkageData.rightChildToRootPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet
    D.rightRestrictedPacking
    (D.rightRestrictedPacking_internallyDisjoint_clusters c)

/-- The root-side linkage, traversed in the opposite direction. -/
noncomputable def RootChildTranchePairWidthLinkageData.sourceLinkageReverse
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.leftIndexSet) :=
  D.sourceLinkage.reverse

@[simp] theorem RootChildTranchePairWidthLinkageData.sourceLinkageReverse_card
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.sourceLinkageReverse.card = w := by
  dsimp [RootChildTranchePairWidthLinkageData.sourceLinkageReverse]
  simp [D.sourceLinkage_card]

/-- Reversing the root-side linkage preserves containment in the root cluster. -/
theorem RootChildTranchePairWidthLinkageData.sourceLinkageReverse_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w) :
    D.sourceLinkageReverse.toPathPacking.StaysIn (T.cluster S.root) := by
  dsimp [RootChildTranchePairWidthLinkageData.sourceLinkageReverse]
  exact PerfectPathPacking.reverse_staysIn D.sourceLinkage D.sourceLinkage_staysIn

/-- The root-side linkage is internally disjoint from every selected leaf
cluster, since it stays inside the root cluster. -/
theorem RootChildTranchePairWidthLinkageData.sourceLinkage_internallyDisjoint_selectedLeafCluster
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w)
    (q : Fin ell) :
    D.sourceLinkage.toPathPacking.InternallyDisjointFromSet
      (T.cluster (S.selectedLeaf q)) := by
  intro i v hv hvLeaf
  have hvRoot : v ∈ T.cluster S.root := D.sourceLinkage_staysIn i hv
  exact False.elim
    (Finset.disjoint_left.mp
      (T.cluster_disjoint (S.selectedLeaf_ne_root q).symm) hvRoot hvLeaf)

/-- The reversed root-side linkage is internally disjoint from every selected
leaf cluster. -/
theorem RootChildTranchePairWidthLinkageData.sourceLinkageReverse_internallyDisjoint_selectedLeafCluster
    {S : Theorem46LeafExtractionSetup T ell}
    {R : RootChildConnectorTrancheData S} {r s : Fin ell}
    {w : ℕ} (D : RootChildTranchePairWidthLinkageData S R r s w)
    (q : Fin ell) :
    D.sourceLinkageReverse.toPathPacking.InternallyDisjointFromSet
      (T.cluster (S.selectedLeaf q)) := by
  dsimp [RootChildTranchePairWidthLinkageData.sourceLinkageReverse]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet D.sourceLinkage
    (D.sourceLinkage_internallyDisjoint_selectedLeafCluster q)

/-- A width-`w` linkage inside the root cluster between the shared root-child
tranches assigned to two selected leaves.  Unlike
`RootChildTranchePairWidthLinkageData`, this package is coherent with the
selected-leaf labels used by the root-to-leaf routes. -/
structure RootChildSelectedLeafPairWidthLinkageData
    (S : Theorem46LeafExtractionSetup T ell) (r s : Fin ell) (w : ℕ) where
  leftIndexSet :
    Finset (T.connector S.root S.child S.root_child_adj).Index
  rightIndexSet :
    Finset (T.connector S.root S.child S.root_child_adj).Index
  leftIndex_subset_tranche : leftIndexSet ⊆ S.rootChildSelectedLeafTranche r
  rightIndex_subset_tranche : rightIndexSet ⊆ S.rootChildSelectedLeafTranche s
  leftIndex_card : leftIndexSet.card = w
  rightIndex_card : rightIndexSet.card = w
  index_disjoint : Disjoint leftIndexSet rightIndexSet
  sourceLinkage :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet rightIndexSet)
  sourceLeft_card :
    ((T.connector S.root S.child S.root_child_adj).sourceSet leftIndexSet).card =
      w
  sourceRight_card :
    ((T.connector S.root S.child S.root_child_adj).sourceSet rightIndexSet).card =
      w
  targetLeft_card :
    ((T.connector S.root S.child S.root_child_adj).targetSet leftIndexSet).card =
      w
  targetRight_card :
    ((T.connector S.root S.child S.root_child_adj).targetSet rightIndexSet).card =
      w
  source_disjoint :
    Disjoint
      ((T.connector S.root S.child S.root_child_adj).sourceSet leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet rightIndexSet)
  target_disjoint :
    Disjoint
      ((T.connector S.root S.child S.root_child_adj).targetSet leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet rightIndexSet)
  sourceLinkage_card : sourceLinkage.card = w
  sourceLinkage_staysIn : sourceLinkage.toPathPacking.StaysIn (T.cluster S.root)
  leftRestricted_staysIn :
    ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
      leftIndexSet).toPathPacking.StaysIn
        (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  rightRestricted_staysIn :
    ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
      rightIndexSet).toPathPacking.StaysIn
        (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  leftRestricted_internallyDisjoint_clusters :
    ∀ c : Fin m,
      PathPacking.InternallyDisjointFromSet
        ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
          leftIndexSet).toPathPacking
        (T.cluster c)
  rightRestricted_internallyDisjoint_clusters :
    ∀ c : Fin m,
      PathPacking.InternallyDisjointFromSet
        ((T.connector S.root S.child S.root_child_adj).restrictIndexSet
          rightIndexSet).toPathPacking
        (T.cluster c)

/-- Two distinct shared root-child selected-leaf tranches contain width-`w`
subfamilies whose root-side endpoints can be linked inside the root cluster. -/
theorem exists_rootChildSelectedLeafPairWidthLinkageData
    (S : Theorem46LeafExtractionSetup T ell)
    {w : ℕ} (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W)
    {r s : Fin ell} (hrs : r ≠ s) :
    Nonempty (RootChildSelectedLeafPairWidthLinkageData S r s w) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  have hw_tranche_r : w ≤ (S.rootChildSelectedLeafTranche r).card := by
    simpa [S.rootChildSelectedLeafTranche_card r] using
      theorem46_width_le_perLeafWidth (W := W) (ell := ell) (w := w) hell hW
  have hw_tranche_s : w ≤ (S.rootChildSelectedLeafTranche s).card := by
    simpa [S.rootChildSelectedLeafTranche_card s] using
      theorem46_width_le_perLeafWidth (W := W) (ell := ell) (w := w) hell hW
  rcases Finset.exists_subset_card_eq hw_tranche_r with
    ⟨leftIndexSet, hleft_subset, hleft_card⟩
  rcases Finset.exists_subset_card_eq hw_tranche_s with
    ⟨rightIndexSet, hright_subset, hright_card⟩
  have hindexDisj : Disjoint leftIndexSet rightIndexSet := by
    rw [Finset.disjoint_left]
    intro x hxleft hxright
    exact Finset.disjoint_left.mp
      (S.rootChildSelectedLeafTranche_pairwise_disjoint hrs)
      (hleft_subset hxleft) (hright_subset hxright)
  have hsourceDisj : Disjoint (P.sourceSet leftIndexSet)
      (P.sourceSet rightIndexSet) :=
    P.sourceSet_disjoint hindexDisj
  have htargetDisj : Disjoint (P.targetSet leftIndexSet)
      (P.targetSet rightIndexSet) :=
    P.targetSet_disjoint hindexDisj
  have hsourceLeft_interface :
      P.sourceSet leftIndexSet ⊆ T.interface S.root S.child S.root_child_adj :=
    P.sourceSet_subset_left leftIndexSet
  have hsourceRight_interface :
      P.sourceSet rightIndexSet ⊆ T.interface S.root S.child S.root_child_adj :=
    P.sourceSet_subset_left rightIndexSet
  have hsourceLeft_card : (P.sourceSet leftIndexSet).card = w := by
    simp [P, hleft_card]
  have hsourceRight_card : (P.sourceSet rightIndexSet).card = w := by
    simp [P, hright_card]
  have htargetLeft_card : (P.targetSet leftIndexSet).card = w := by
    simp [P, hleft_card]
  have htargetRight_card : (P.targetSet rightIndexSet).card = w := by
    simp [P, hright_card]
  have hsourceCardEq :
      (P.sourceSet leftIndexSet).card = (P.sourceSet rightIndexSet).card :=
    hsourceLeft_card.trans hsourceRight_card.symm
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      S.root_child_adj hsourceLeft_interface hsourceRight_interface
      hsourceDisj hsourceCardEq with
    ⟨sourceLinkage, hsourceLinkageCard, hsourceLinkageStay⟩
  exact ⟨{
    leftIndexSet := leftIndexSet
    rightIndexSet := rightIndexSet
    leftIndex_subset_tranche := hleft_subset
    rightIndex_subset_tranche := hright_subset
    leftIndex_card := hleft_card
    rightIndex_card := hright_card
    index_disjoint := hindexDisj
    sourceLinkage := sourceLinkage
    sourceLeft_card := by simpa [P] using hsourceLeft_card
    sourceRight_card := by simpa [P] using hsourceRight_card
    targetLeft_card := by simpa [P] using htargetLeft_card
    targetRight_card := by simpa [P] using htargetRight_card
    source_disjoint := by simpa [P] using hsourceDisj
    target_disjoint := by simpa [P] using htargetDisj
    sourceLinkage_card := hsourceLinkageCard.trans hsourceLeft_card
    sourceLinkage_staysIn := hsourceLinkageStay
    leftRestricted_staysIn :=
      P.restrictIndexSet_staysIn_vertexSet leftIndexSet
    rightRestricted_staysIn :=
      P.restrictIndexSet_staysIn_vertexSet rightIndexSet
    leftRestricted_internallyDisjoint_clusters := by
      intro c
      exact P.restrictIndexSet_internallyDisjointFromSet leftIndexSet
        (T.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj c)
    rightRestricted_internallyDisjoint_clusters := by
      intro c
      exact P.restrictIndexSet_internallyDisjointFromSet rightIndexSet
        (T.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj c) }⟩

/-- The left restricted shared root-child connector in a selected-leaf pair
package. -/
noncomputable def RootChildSelectedLeafPairWidthLinkageData.leftRestrictedPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet D.leftIndexSet) :=
  (T.connector S.root S.child S.root_child_adj).restrictIndexSet D.leftIndexSet

/-- The right restricted shared root-child connector in a selected-leaf pair
package. -/
noncomputable def RootChildSelectedLeafPairWidthLinkageData.rightRestrictedPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet D.rightIndexSet) :=
  (T.connector S.root S.child S.root_child_adj).restrictIndexSet D.rightIndexSet

@[simp] theorem RootChildSelectedLeafPairWidthLinkageData.leftRestrictedPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.leftRestrictedPacking.card = w := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.leftRestrictedPacking]
  simp [D.leftIndex_card]

@[simp] theorem RootChildSelectedLeafPairWidthLinkageData.rightRestrictedPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.rightRestrictedPacking.card = w := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.rightRestrictedPacking]
  simp [D.rightIndex_card]

/-- The left restricted shared root-child connector stays in the full root-child
connector vertex set. -/
theorem RootChildSelectedLeafPairWidthLinkageData.leftRestrictedPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.leftRestrictedPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.leftRestrictedPacking]
  exact D.leftRestricted_staysIn

/-- The right restricted shared root-child connector stays in the full root-child
connector vertex set. -/
theorem RootChildSelectedLeafPairWidthLinkageData.rightRestrictedPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.rightRestrictedPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.rightRestrictedPacking]
  exact D.rightRestricted_staysIn

/-- The left restricted shared root-child connector is internally disjoint from
every cluster. -/
theorem RootChildSelectedLeafPairWidthLinkageData.leftRestrictedPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) (c : Fin m) :
    D.leftRestrictedPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.leftRestrictedPacking]
  exact D.leftRestricted_internallyDisjoint_clusters c

/-- The right restricted shared root-child connector is internally disjoint from
every cluster. -/
theorem RootChildSelectedLeafPairWidthLinkageData.rightRestrictedPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) (c : Fin m) :
    D.rightRestrictedPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.rightRestrictedPacking]
  exact D.rightRestricted_internallyDisjoint_clusters c

/-- The left shared root-child connector, traversed from the child side back to
the root. -/
noncomputable def RootChildSelectedLeafPairWidthLinkageData.leftChildToRootPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet D.leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.leftIndexSet) :=
  D.leftRestrictedPacking.reverse

/-- The right shared root-child connector, traversed from the child side back to
the root. -/
noncomputable def RootChildSelectedLeafPairWidthLinkageData.rightChildToRootPacking
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet D.rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.rightIndexSet) :=
  D.rightRestrictedPacking.reverse

@[simp] theorem RootChildSelectedLeafPairWidthLinkageData.leftChildToRootPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.leftChildToRootPacking.card = w := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.leftChildToRootPacking]
  simp

@[simp] theorem RootChildSelectedLeafPairWidthLinkageData.rightChildToRootPacking_card
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.rightChildToRootPacking.card = w := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.rightChildToRootPacking]
  simp

/-- Reversing the left shared root-child connector preserves connector
containment. -/
theorem RootChildSelectedLeafPairWidthLinkageData.leftChildToRootPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.leftChildToRootPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.leftChildToRootPacking]
  exact PerfectPathPacking.reverse_staysIn D.leftRestrictedPacking
    D.leftRestrictedPacking_staysIn

/-- Reversing the right shared root-child connector preserves connector
containment. -/
theorem RootChildSelectedLeafPairWidthLinkageData.rightChildToRootPacking_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.rightChildToRootPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.rightChildToRootPacking]
  exact PerfectPathPacking.reverse_staysIn D.rightRestrictedPacking
    D.rightRestrictedPacking_staysIn

/-- Reversing the left shared root-child connector preserves cluster internal
disjointness. -/
theorem RootChildSelectedLeafPairWidthLinkageData.leftChildToRootPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) (c : Fin m) :
    D.leftChildToRootPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.leftChildToRootPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet
    D.leftRestrictedPacking
    (D.leftRestrictedPacking_internallyDisjoint_clusters c)

/-- Reversing the right shared root-child connector preserves cluster internal
disjointness. -/
theorem RootChildSelectedLeafPairWidthLinkageData.rightChildToRootPacking_internallyDisjoint_clusters
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) (c : Fin m) :
    D.rightChildToRootPacking.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.rightChildToRootPacking]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet
    D.rightRestrictedPacking
    (D.rightRestrictedPacking_internallyDisjoint_clusters c)

/-- The root-side linkage between shared selected-leaf tranches, traversed in
the opposite direction. -/
noncomputable def RootChildSelectedLeafPairWidthLinkageData.sourceLinkageReverse
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet D.leftIndexSet) :=
  D.sourceLinkage.reverse

@[simp] theorem RootChildSelectedLeafPairWidthLinkageData.sourceLinkageReverse_card
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.sourceLinkageReverse.card = w := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.sourceLinkageReverse]
  simp [D.sourceLinkage_card]

/-- Reversing the shared root-side linkage preserves containment in the root
cluster. -/
theorem RootChildSelectedLeafPairWidthLinkageData.sourceLinkageReverse_staysIn
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) :
    D.sourceLinkageReverse.toPathPacking.StaysIn (T.cluster S.root) := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.sourceLinkageReverse]
  exact PerfectPathPacking.reverse_staysIn D.sourceLinkage D.sourceLinkage_staysIn

/-- The shared root-side linkage is internally disjoint from every selected leaf
cluster, since it stays inside the root cluster. -/
theorem RootChildSelectedLeafPairWidthLinkageData.sourceLinkage_internallyDisjoint_selectedLeafCluster
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) (q : Fin ell) :
    D.sourceLinkage.toPathPacking.InternallyDisjointFromSet
      (T.cluster (S.selectedLeaf q)) := by
  intro i v hv hvLeaf
  have hvRoot : v ∈ T.cluster S.root := D.sourceLinkage_staysIn i hv
  exact False.elim
    (Finset.disjoint_left.mp
      (T.cluster_disjoint (S.selectedLeaf_ne_root q).symm) hvRoot hvLeaf)

/-- The reversed shared root-side linkage is internally disjoint from every
selected leaf cluster. -/
theorem RootChildSelectedLeafPairWidthLinkageData.sourceLinkageReverse_internallyDisjoint_selectedLeafCluster
    {S : Theorem46LeafExtractionSetup T ell}
    {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w) (q : Fin ell) :
    D.sourceLinkageReverse.toPathPacking.InternallyDisjointFromSet
      (T.cluster (S.selectedLeaf q)) := by
  dsimp [RootChildSelectedLeafPairWidthLinkageData.sourceLinkageReverse]
  exact PerfectPathPacking.reverse_internallyDisjointFromSet D.sourceLinkage
    (D.sourceLinkage_internallyDisjoint_selectedLeafCluster q)

/-- The first-turn route data attached to both sides of a width-`w` pair of
shared root-child selected-leaf tranches. -/
structure RootChildSelectedLeafPairFirstTurnRoutesData
    {S : Theorem46LeafExtractionSetup T ell} {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w)
    (hr : 1 < S.selectedLeafMetaPathLength r)
    (hs : 1 < S.selectedLeafMetaPathLength s) where
  leftFirstTurn :
    RootChildSelectedLeafFirstTurnWidthRestrictionData S r hr
      ((T.connector S.root S.child S.root_child_adj).targetSet D.leftIndexSet) w
  rightFirstTurn :
    RootChildSelectedLeafFirstTurnWidthRestrictionData S s hs
      ((T.connector S.root S.child S.root_child_adj).targetSet D.rightIndexSet) w

/-- Both width-`w` sides of a shared root-child selected-leaf pair inherit
first-turn routes into their respective selected root-to-leaf paths. -/
theorem RootChildSelectedLeafPairWidthLinkageData.exists_firstTurnRoutes
    {S : Theorem46LeafExtractionSetup T ell} {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w)
    (hr : 1 < S.selectedLeafMetaPathLength r)
    (hs : 1 < S.selectedLeafMetaPathLength s) :
    Nonempty (RootChildSelectedLeafPairFirstTurnRoutesData D hr hs) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  let L := S.rootChildSelectedLeafFirstTurnOutgoingConcatData r hr
  let R := S.rootChildSelectedLeafFirstTurnOutgoingConcatData s hs
  have hleft_source :
      P.targetSet D.leftIndexSet ⊆
        P.targetSet (S.rootChildSelectedLeafTranche r) :=
    P.targetSet_mono D.leftIndex_subset_tranche
  have hright_source :
      P.targetSet D.rightIndexSet ⊆
        P.targetSet (S.rootChildSelectedLeafTranche s) :=
    P.targetSet_mono D.rightIndex_subset_tranche
  rcases S.exists_rootChildSelectedLeafFirstTurnWidthRestrictionData
      r hr L (P.targetSet D.leftIndexSet) hleft_source D.targetLeft_card with
    ⟨leftRoute⟩
  rcases S.exists_rootChildSelectedLeafFirstTurnWidthRestrictionData
      s hs R (P.targetSet D.rightIndexSet) hright_source D.targetRight_card with
    ⟨rightRoute⟩
  exact ⟨{
    leftFirstTurn := leftRoute
    rightFirstTurn := rightRoute }⟩

/-- A chosen pair of first-turn routes attached to a shared root-child
selected-leaf pair. -/
noncomputable def RootChildSelectedLeafPairWidthLinkageData.firstTurnRoutes
    {S : Theorem46LeafExtractionSetup T ell} {r s : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafPairWidthLinkageData S r s w)
    (hr : 1 < S.selectedLeafMetaPathLength r)
    (hs : 1 < S.selectedLeafMetaPathLength s) :
    RootChildSelectedLeafPairFirstTurnRoutesData D hr hs :=
  Classical.choice (D.exists_firstTurnRoutes hr hs)

/-- First-turn routes for the coherent left/right root-child subtranches of a
single selected leaf. -/
structure RootChildSelectedLeafDoubleFirstTurnRoutesData
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w)
    (hr : 1 < S.selectedLeafMetaPathLength r) where
  leftFirstTurn :
    RootChildSelectedLeafFirstTurnWidthRestrictionData S r hr
      ((T.connector S.root S.child S.root_child_adj).targetSet D.leftIndexSet) w
  rightFirstTurn :
    RootChildSelectedLeafFirstTurnWidthRestrictionData S r hr
      ((T.connector S.root S.child S.root_child_adj).targetSet D.rightIndexSet) w

/-- Both coherent sides of a selected leaf's root-child double subtranche route
through the first turn of the selected root-to-leaf meta-path. -/
theorem RootChildSelectedLeafDoubleWidthData.exists_firstTurnRoutes
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w)
    (hr : 1 < S.selectedLeafMetaPathLength r) :
    Nonempty (RootChildSelectedLeafDoubleFirstTurnRoutesData D hr) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  let F := S.rootChildSelectedLeafFirstTurnOutgoingConcatData r hr
  have hleft_source :
      P.targetSet D.leftIndexSet ⊆
        P.targetSet (S.rootChildSelectedLeafTranche r) :=
    P.targetSet_mono D.leftIndex_subset_tranche
  have hright_source :
      P.targetSet D.rightIndexSet ⊆
        P.targetSet (S.rootChildSelectedLeafTranche r) :=
    P.targetSet_mono D.rightIndex_subset_tranche
  rcases S.exists_rootChildSelectedLeafFirstTurnWidthRestrictionData
      r hr F (P.targetSet D.leftIndexSet) hleft_source D.targetLeft_card with
    ⟨leftRoute⟩
  rcases S.exists_rootChildSelectedLeafFirstTurnWidthRestrictionData
      r hr F (P.targetSet D.rightIndexSet) hright_source D.targetRight_card with
    ⟨rightRoute⟩
  exact ⟨{
    leftFirstTurn := leftRoute
    rightFirstTurn := rightRoute }⟩

/-- Chosen first-turn routes for the coherent left/right subtranches of one
selected leaf. -/
noncomputable def RootChildSelectedLeafDoubleWidthData.firstTurnRoutes
    {S : Theorem46LeafExtractionSetup T ell} {r : Fin ell} {w : ℕ}
    (D : RootChildSelectedLeafDoubleWidthData S r w)
    (hr : 1 < S.selectedLeafMetaPathLength r) :
    RootChildSelectedLeafDoubleFirstTurnRoutesData D hr :=
  Classical.choice (D.exists_firstTurnRoutes hr)

/-- Root-cluster linkage for one adjacent gap, using the coherent double
root-child subtranches: the right side of selected leaf `r` links to the left
side of selected leaf `r + 1`. -/
structure RootChildSelectedLeafAdjacentGapRootLinkageData
    {S : Theorem46LeafExtractionSetup T ell} {w : ℕ}
    (D : ∀ r : Fin ell, RootChildSelectedLeafDoubleWidthData S r w)
    (r : Fin ell) (hr : r.1 + 1 < ell) where
  sourceLinkage :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet
        (D r).rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet
        (D ⟨r.1 + 1, hr⟩).leftIndexSet)
  sourceLinkage_card : sourceLinkage.card = w
  sourceLinkage_staysIn : sourceLinkage.toPathPacking.StaysIn (T.cluster S.root)

/-- The coherent double root-child subtranche family supplies a root-cluster
linkage for every adjacent selected-leaf gap. -/
theorem exists_rootChildSelectedLeafAdjacentGapRootLinkageData
    {S : Theorem46LeafExtractionSetup T ell} {w : ℕ}
    (D : ∀ r : Fin ell, RootChildSelectedLeafDoubleWidthData S r w)
    (r : Fin ell) (hr : r.1 + 1 < ell) :
    Nonempty (RootChildSelectedLeafAdjacentGapRootLinkageData D r hr) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  let s : Fin ell := ⟨r.1 + 1, hr⟩
  have hrs : r ≠ s := by
    intro h
    have hval : r.1 = r.1 + 1 := congrArg Fin.val h
    omega
  have hright_interface :
      P.sourceSet (D r).rightIndexSet ⊆
        T.interface S.root S.child S.root_child_adj :=
    P.sourceSet_subset_left (D r).rightIndexSet
  have hleft_interface :
      P.sourceSet (D s).leftIndexSet ⊆
        T.interface S.root S.child S.root_child_adj :=
    P.sourceSet_subset_left (D s).leftIndexSet
  have hindex_disjoint :
      Disjoint (D r).rightIndexSet (D s).leftIndexSet := by
    rw [Finset.disjoint_left]
    intro x hxright hxleft
    exact Finset.disjoint_left.mp
      (S.rootChildSelectedLeafTranche_pairwise_disjoint hrs)
      ((D r).rightIndex_subset_tranche hxright)
      ((D s).leftIndex_subset_tranche hxleft)
  have hsource_disjoint :
      Disjoint (P.sourceSet (D r).rightIndexSet)
        (P.sourceSet (D s).leftIndexSet) :=
    P.sourceSet_disjoint hindex_disjoint
  have hcard :
      (P.sourceSet (D r).rightIndexSet).card =
        (P.sourceSet (D s).leftIndexSet).card :=
    (D r).sourceRight_card.trans (D s).sourceLeft_card.symm
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      S.root_child_adj hright_interface hleft_interface
      hsource_disjoint hcard with
    ⟨Q, hQcard, hQstay⟩
  exact ⟨{
    sourceLinkage := Q
    sourceLinkage_card := hQcard.trans (D r).sourceRight_card
    sourceLinkage_staysIn := hQstay }⟩

/-- Chosen root-cluster linkage for one coherent adjacent selected-leaf gap. -/
noncomputable def rootChildSelectedLeafAdjacentGapRootLinkageData
    {S : Theorem46LeafExtractionSetup T ell} {w : ℕ}
    (D : ∀ r : Fin ell, RootChildSelectedLeafDoubleWidthData S r w)
    (r : Fin ell) (hr : r.1 + 1 < ell) :
    RootChildSelectedLeafAdjacentGapRootLinkageData D r hr :=
  Classical.choice
    (exists_rootChildSelectedLeafAdjacentGapRootLinkageData D r hr)

/-- The adjacent-gap root linkage is internally disjoint from every non-root
cluster, since it stays in the root cluster. -/
theorem RootChildSelectedLeafAdjacentGapRootLinkageData.sourceLinkage_internallyDisjoint_cluster_of_ne_root
    {S : Theorem46LeafExtractionSetup T ell} {w : ℕ}
    {D : ∀ r : Fin ell, RootChildSelectedLeafDoubleWidthData S r w}
    {r : Fin ell} {hr : r.1 + 1 < ell}
    (L : RootChildSelectedLeafAdjacentGapRootLinkageData D r hr)
    {c : Fin m} (hc : c ≠ S.root) :
    L.sourceLinkage.toPathPacking.InternallyDisjointFromSet
      (T.cluster c) := by
  intro i v hv hvC
  have hvRoot : v ∈ T.cluster S.root := L.sourceLinkage_staysIn i hv
  exact False.elim
    (Finset.disjoint_left.mp (T.cluster_disjoint hc) hvC hvRoot)

/-- The three coherent root-detour pieces for one adjacent selected-leaf gap:
right root-child connector reversed, root-cluster linkage, and next left
root-child connector forward. -/
structure RootChildSelectedLeafAdjacentGapRoutePiecesData
    {S : Theorem46LeafExtractionSetup T ell} {w : ℕ}
    (D : ∀ r : Fin ell, RootChildSelectedLeafDoubleWidthData S r w)
    (r : Fin ell) (hr : r.1 + 1 < ell) where
  rootLinkage :
    RootChildSelectedLeafAdjacentGapRootLinkageData D r hr
  rightChildToRootPacking :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).targetSet
        (D r).rightIndexSet)
      ((T.connector S.root S.child S.root_child_adj).sourceSet
        (D r).rightIndexSet)
  leftRootToChildPacking :
    PerfectPathPacking G
      ((T.connector S.root S.child S.root_child_adj).sourceSet
        (D ⟨r.1 + 1, hr⟩).leftIndexSet)
      ((T.connector S.root S.child S.root_child_adj).targetSet
        (D ⟨r.1 + 1, hr⟩).leftIndexSet)
  rightChildToRootPacking_card : rightChildToRootPacking.card = w
  leftRootToChildPacking_card : leftRootToChildPacking.card = w
  rightChildToRootPacking_staysIn :
    rightChildToRootPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  leftRootToChildPacking_staysIn :
    leftRootToChildPacking.toPathPacking.StaysIn
      (T.connector S.root S.child S.root_child_adj).toPathPacking.vertexSet
  rightChildToRootPacking_internallyDisjoint_clusters :
    ∀ c : Fin m,
      rightChildToRootPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)
  leftRootToChildPacking_internallyDisjoint_clusters :
    ∀ c : Fin m,
      leftRootToChildPacking.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)
  rootLinkage_internallyDisjoint_cluster_of_ne_root :
    ∀ {c : Fin m}, c ≠ S.root →
      rootLinkage.sourceLinkage.toPathPacking.InternallyDisjointFromSet
        (T.cluster c)

/-- The coherent double subtranche family supplies all three root-detour pieces
for every adjacent selected-leaf gap. -/
theorem exists_rootChildSelectedLeafAdjacentGapRoutePiecesData
    {S : Theorem46LeafExtractionSetup T ell} {w : ℕ}
    (D : ∀ r : Fin ell, RootChildSelectedLeafDoubleWidthData S r w)
    (r : Fin ell) (hr : r.1 + 1 < ell) :
    Nonempty (RootChildSelectedLeafAdjacentGapRoutePiecesData D r hr) := by
  classical
  let s : Fin ell := ⟨r.1 + 1, hr⟩
  let L := rootChildSelectedLeafAdjacentGapRootLinkageData D r hr
  exact ⟨{
    rootLinkage := L
    rightChildToRootPacking := (D r).rightChildToRootPacking
    leftRootToChildPacking := (D s).leftRestrictedPacking
    rightChildToRootPacking_card := by
      exact (D r).rightChildToRootPacking_card
    leftRootToChildPacking_card := by
      exact (D s).leftRestrictedPacking_card
    rightChildToRootPacking_staysIn := by
      exact (D r).rightChildToRootPacking_staysIn
    leftRootToChildPacking_staysIn := by
      dsimp [s]
      exact (D s).leftRestrictedPacking_staysIn
    rightChildToRootPacking_internallyDisjoint_clusters := by
      intro c
      exact (D r).rightChildToRootPacking_internallyDisjoint_clusters c
    leftRootToChildPacking_internallyDisjoint_clusters := by
      intro c
      dsimp [s]
      exact (D s).leftRestrictedPacking_internallyDisjoint_clusters c
    rootLinkage_internallyDisjoint_cluster_of_ne_root := by
      intro c hc
      exact L.sourceLinkage_internallyDisjoint_cluster_of_ne_root hc }⟩

/-- Chosen coherent root-detour pieces for one adjacent selected-leaf gap. -/
noncomputable def rootChildSelectedLeafAdjacentGapRoutePiecesData
    {S : Theorem46LeafExtractionSetup T ell} {w : ℕ}
    (D : ∀ r : Fin ell, RootChildSelectedLeafDoubleWidthData S r w)
    (r : Fin ell) (hr : r.1 + 1 < ell) :
    RootChildSelectedLeafAdjacentGapRoutePiecesData D r hr :=
  Classical.choice
    (exists_rootChildSelectedLeafAdjacentGapRoutePiecesData D r hr)

/-- The local data now available for every ordered selected leaf in the
many-leaves branch: a root-child tranche family, and for each selected leaf a
coherent parent-to-leaf Step 2 package of the final width. -/
structure OrderedLeafExtractionLocalData
    (S : Theorem46LeafExtractionSetup T ell) (w : ℕ) where
  rootTranches : RootChildConnectorTrancheData S
  rootPairLinkage :
    ∀ r : Fin ell, ∀ hr : r.1 + 1 < ell,
      RootChildTranchePairWidthLinkageData S rootTranches r ⟨r.1 + 1, hr⟩ w
  rootSelectedPairLinkage :
    ∀ r : Fin ell, ∀ hr : r.1 + 1 < ell,
      RootChildSelectedLeafPairWidthLinkageData S r ⟨r.1 + 1, hr⟩ w
  rootChildDoubleWidth :
    ∀ r : Fin ell, RootChildSelectedLeafDoubleWidthData S r w
  rootChildDoubleFirstTurnRoutes :
    ∀ r : Fin ell, ∀ hr : 1 < S.selectedLeafMetaPathLength r,
      RootChildSelectedLeafDoubleFirstTurnRoutesData
        (rootChildDoubleWidth r) hr
  rootChildAdjacentGapRootLinkage :
    ∀ r : Fin ell, ∀ hr : r.1 + 1 < ell,
      RootChildSelectedLeafAdjacentGapRootLinkageData
        rootChildDoubleWidth r hr
  rootChildAdjacentGapRoutePieces :
    ∀ r : Fin ell, ∀ hr : r.1 + 1 < ell,
      RootChildSelectedLeafAdjacentGapRoutePiecesData
        rootChildDoubleWidth r hr
  pathEdgeTranches :
    ∀ r : Fin ell, ∀ a : Fin (S.selectedLeafMetaPathLength r),
      SelectedLeafMetaPathEdgeTrancheData S r a
  pathTurnLinkages :
    ∀ r : Fin ell, ∀ a : ℕ,
      ∀ ha : a + 1 < S.selectedLeafMetaPathLength r,
        SelectedLeafMetaPathTurnLinkageData S r a ha
  pathIncomingTurnConcats :
    ∀ r : Fin ell, ∀ a : ℕ,
      ∀ ha : a + 1 < S.selectedLeafMetaPathLength r,
        SelectedLeafMetaPathIncomingTurnConcatData S r a ha
  pathTurnOutgoingConcats :
    ∀ r : Fin ell, ∀ a : ℕ,
      ∀ ha : a + 1 < S.selectedLeafMetaPathLength r,
        SelectedLeafMetaPathTurnOutgoingConcatData S r a ha
  pathFullTurnConcats :
    ∀ r : Fin ell, ∀ a : ℕ,
      ∀ ha : a + 1 < S.selectedLeafMetaPathLength r,
        SelectedLeafMetaPathFullTurnConcatData S r a ha
  parentWidthData :
    ∀ r : Fin ell,
      SelectedLeafConnectorCoherentWidthData S
        (S.selectedLeafParent_adj (S.selectedLeafSubtype r)) w

/-- The root-child connector admits the full Step 1 restricted-bundle package. -/
theorem exists_rootChildConnectorStep1Data
    (S : Theorem46LeafExtractionSetup T ell) :
    Nonempty (RootChildConnectorStep1Data S) := by
  rcases S.exists_root_child_restricted_connector with
    ⟨I, hIcard, hsource, htarget, hrestrict, hstay, hdisj⟩
  exact ⟨{
    indexSet := I
    index_card := hIcard
    source_card := hsource
    target_card := htarget
    restricted_card := hrestrict
    restricted_staysIn := hstay
    restricted_internallyDisjoint_clusters := hdisj }⟩

/-- The root-child Step 1 connector bundle can be split into `ell` disjoint
ordered tranches, each of the per-leaf size `floor(W / ell)`. -/
theorem RootChildConnectorStep1Data.exists_trancheData
    (S : Theorem46LeafExtractionSetup T ell)
    (D : RootChildConnectorStep1Data S) :
    Nonempty (RootChildConnectorTrancheData S) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  rcases exists_finsetBlockDecomposition_of_card_mul
      (A := D.indexSet) (ell := ell) (q := W / ell) D.index_card with
    ⟨B⟩
  exact ⟨{
    step1 := D
    tranche := B.block
    tranche_subset_index := B.block_subset
    tranche_card := B.block_card
    tranche_pairwise_disjoint := by
      intro r s hrs
      exact B.block_pairwise_disjoint hrs
    source_card := by
      intro r
      simp [B.block_card r]
    target_card := by
      intro r
      simp [B.block_card r]
    restricted_card := by
      intro r
      simp [B.block_card r]
    restricted_staysIn := by
      intro r
      exact P.restrictIndexSet_staysIn_vertexSet (B.block r)
    restricted_internallyDisjoint_clusters := by
      intro r c
      exact P.restrictIndexSet_internallyDisjointFromSet (B.block r)
        (T.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj c)
    restricted_mutuallyNodeDisjoint := by
      intro r s hrs a b
      exact P.node_disjoint (by
        intro h
        exact Finset.disjoint_left.mp (B.block_pairwise_disjoint hrs)
          a.2 (by simp [h, b.2])) }⟩

/-- Two distinct root-child tranches contain width-`w` subfamilies whose
root-side endpoints can be linked inside the root cluster. -/
theorem RootChildConnectorTrancheData.exists_pairWidthLinkageData
    (S : Theorem46LeafExtractionSetup T ell)
    (R : RootChildConnectorTrancheData S)
    {w : ℕ} (hell : 0 < ell)
    (hW : 16 * w * ell ^ 2 + 1 < W)
    {r s : Fin ell} (hrs : r ≠ s) :
    Nonempty (RootChildTranchePairWidthLinkageData S R r s w) := by
  classical
  let P := T.connector S.root S.child S.root_child_adj
  have hw_tranche_r : w ≤ (R.tranche r).card := by
    simpa [R.tranche_card r] using
      theorem46_width_le_perLeafWidth (W := W) (ell := ell) (w := w) hell hW
  have hw_tranche_s : w ≤ (R.tranche s).card := by
    simpa [R.tranche_card s] using
      theorem46_width_le_perLeafWidth (W := W) (ell := ell) (w := w) hell hW
  rcases Finset.exists_subset_card_eq hw_tranche_r with
    ⟨leftIndexSet, hleft_subset, hleft_card⟩
  rcases Finset.exists_subset_card_eq hw_tranche_s with
    ⟨rightIndexSet, hright_subset, hright_card⟩
  have hleft_index : leftIndexSet ⊆ R.step1.indexSet :=
    subset_trans hleft_subset (R.tranche_subset_index r)
  have hright_index : rightIndexSet ⊆ R.step1.indexSet :=
    subset_trans hright_subset (R.tranche_subset_index s)
  have hindexDisj : Disjoint leftIndexSet rightIndexSet := by
    rw [Finset.disjoint_left]
    intro x hxleft hxright
    exact Finset.disjoint_left.mp (R.tranche_pairwise_disjoint hrs)
      (hleft_subset hxleft) (hright_subset hxright)
  have hsourceDisj : Disjoint (P.sourceSet leftIndexSet)
      (P.sourceSet rightIndexSet) :=
    P.sourceSet_disjoint hindexDisj
  have htargetDisj : Disjoint (P.targetSet leftIndexSet)
      (P.targetSet rightIndexSet) :=
    P.targetSet_disjoint hindexDisj
  have hsourceLeft_interface :
      P.sourceSet leftIndexSet ⊆ T.interface S.root S.child S.root_child_adj :=
    P.sourceSet_subset_left leftIndexSet
  have hsourceRight_interface :
      P.sourceSet rightIndexSet ⊆ T.interface S.root S.child S.root_child_adj :=
    P.sourceSet_subset_left rightIndexSet
  have hsourceLeft_card : (P.sourceSet leftIndexSet).card = w := by
    simp [P, hleft_card]
  have hsourceRight_card : (P.sourceSet rightIndexSet).card = w := by
    simp [P, hright_card]
  have htargetLeft_card : (P.targetSet leftIndexSet).card = w := by
    simp [P, hleft_card]
  have htargetRight_card : (P.targetSet rightIndexSet).card = w := by
    simp [P, hright_card]
  have hsourceCardEq :
      (P.sourceSet leftIndexSet).card = (P.sourceSet rightIndexSet).card :=
    hsourceLeft_card.trans hsourceRight_card.symm
  rcases T.exists_interface_self_perfect_linkage_between_disjoint_subsets
      S.root_child_adj hsourceLeft_interface hsourceRight_interface
      hsourceDisj hsourceCardEq with
    ⟨sourceLinkage, hsourceLinkageCard, hsourceLinkageStay⟩
  exact ⟨{
    leftIndexSet := leftIndexSet
    rightIndexSet := rightIndexSet
    leftIndex_subset_tranche := hleft_subset
    rightIndex_subset_tranche := hright_subset
    leftIndex_subset_index := hleft_index
    rightIndex_subset_index := hright_index
    leftIndex_card := hleft_card
    rightIndex_card := hright_card
    index_disjoint := hindexDisj
    sourceLinkage := sourceLinkage
    sourceLeft_card := by simpa [P] using hsourceLeft_card
    sourceRight_card := by simpa [P] using hsourceRight_card
    targetLeft_card := by simpa [P] using htargetLeft_card
    targetRight_card := by simpa [P] using htargetRight_card
    source_disjoint := by simpa [P] using hsourceDisj
    target_disjoint := by simpa [P] using htargetDisj
    sourceLinkage_card := hsourceLinkageCard.trans hsourceLeft_card
    sourceLinkage_staysIn := hsourceLinkageStay
    leftRestricted_staysIn :=
      P.restrictIndexSet_staysIn_vertexSet leftIndexSet
    rightRestricted_staysIn :=
      P.restrictIndexSet_staysIn_vertexSet rightIndexSet
    leftRestricted_internallyDisjoint_clusters := by
      intro c
      exact P.restrictIndexSet_internallyDisjointFromSet leftIndexSet
        (T.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj c)
    rightRestricted_internallyDisjoint_clusters := by
      intro c
      exact P.restrictIndexSet_internallyDisjointFromSet rightIndexSet
        (T.connector_internally_disjoint_cluster
          S.root S.child S.root_child_adj c) }⟩

/-- The root-child connector admits ordered Step 1 tranche data. -/
theorem exists_rootChildConnectorTrancheData
    (S : Theorem46LeafExtractionSetup T ell) :
    Nonempty (RootChildConnectorTrancheData S) := by
  rcases S.exists_rootChildConnectorStep1Data with ⟨D⟩
  exact D.exists_trancheData S

/-- A chosen root-child Step 1 connector package. -/
noncomputable def rootChildConnectorStep1Data
    (S : Theorem46LeafExtractionSetup T ell) :
    RootChildConnectorStep1Data S :=
  Classical.choice S.exists_rootChildConnectorStep1Data

/-- A chosen ordered root-child Step 1 tranche package. -/
noncomputable def rootChildConnectorTrancheData
    (S : Theorem46LeafExtractionSetup T ell) :
    RootChildConnectorTrancheData S :=
  Classical.choice S.exists_rootChildConnectorTrancheData

/-- The ordered selected leaves have the local root/leaf connector packages
used by the many-leaves extraction. -/
theorem exists_orderedLeafExtractionLocalData
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {w : ℕ} (hW : 16 * w * ell ^ 2 + 1 < W) :
    Nonempty (OrderedLeafExtractionLocalData S w) := by
  rcases S.exists_rootChildConnectorTrancheData with ⟨R⟩
  let doubleWidth : ∀ r : Fin ell, RootChildSelectedLeafDoubleWidthData S r w :=
    fun r => Classical.choice
      (S.exists_rootChildSelectedLeafDoubleWidthData hell hW r)
  exact ⟨{
    rootTranches := R
    rootPairLinkage := fun r hr =>
      Classical.choice (R.exists_pairWidthLinkageData S hell hW (by
        intro h
        have hval : r.1 = r.1 + 1 := congrArg Fin.val h
        omega))
    rootSelectedPairLinkage := fun r hr =>
      Classical.choice (S.exists_rootChildSelectedLeafPairWidthLinkageData
        hell hW (by
          intro h
          have hval : r.1 = r.1 + 1 := congrArg Fin.val h
          omega))
    rootChildDoubleWidth := doubleWidth
    rootChildDoubleFirstTurnRoutes := fun r hr =>
      (doubleWidth r).firstTurnRoutes hr
    rootChildAdjacentGapRootLinkage := fun r hr =>
      rootChildSelectedLeafAdjacentGapRootLinkageData doubleWidth r hr
    rootChildAdjacentGapRoutePieces := fun r hr =>
      rootChildSelectedLeafAdjacentGapRoutePiecesData doubleWidth r hr
    pathEdgeTranches := fun r a =>
      S.selectedLeafMetaPathEdgeTrancheData r a
    pathTurnLinkages := fun r a ha =>
      S.selectedLeafMetaPathTurnLinkageData r ha
    pathIncomingTurnConcats := fun r a ha =>
      S.selectedLeafMetaPathIncomingTurnConcatData r ha
    pathTurnOutgoingConcats := fun r a ha =>
      S.selectedLeafMetaPathTurnOutgoingConcatData r ha
    pathFullTurnConcats := fun r a ha =>
      S.selectedLeafMetaPathFullTurnConcatData r ha
    parentWidthData := fun r =>
      S.selectedLeafParentCoherentWidthData hell hW (S.selectedLeafSubtype r) }⟩

/-- A chosen package of all currently formalized local connector data for the
ordered selected leaves. -/
noncomputable def orderedLeafExtractionLocalData
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {w : ℕ} (hW : 16 * w * ell ^ 2 + 1 < W) :
    OrderedLeafExtractionLocalData S w :=
  Classical.choice (S.exists_orderedLeafExtractionLocalData hell hW)

/-- The leaf base case of Step 2, extracted from the ordered local data. -/
noncomputable def OrderedLeafExtractionLocalData.leafSingletonStrongPath
    {S : Theorem46LeafExtractionSetup T ell} {w : ℕ}
    (D : OrderedLeafExtractionLocalData S w) (hw : 0 < w)
    (r : Fin ell) :
    StrongPathOfSetsSystem G 1 w :=
  (D.parentWidthData r).toTargetSingletonStrongPath hw

/-- Existence form of the selected-leaf base case of Step 2. -/
theorem exists_selectedLeafSingletonStrongPath
    (S : Theorem46LeafExtractionSetup T ell) (hell : 0 < ell)
    {w : ℕ} (hw : 0 < w)
    (hW : 16 * w * ell ^ 2 + 1 < W)
    (r : Fin ell) :
    Nonempty (StrongPathOfSetsSystem G 1 w) := by
  exact ⟨(S.orderedLeafExtractionLocalData hell hW).leafSingletonStrongPath hw r⟩

end Theorem46LeafExtractionSetup

/-- The full Chekuri--Chuzhoy Theorem 4.6 extraction follows from the
meta-tree dichotomy and the DFS/many-leaves branch.

The long/buffered-path case is discharged here using the self-contained
conversion theorem from `TreeOfSets.lean`; only the genuinely remaining branch
is passed as an input. -/
theorem strongPathOfSetsFromStrongTreeOfSets_of_metaDichotomy_and_leafExtraction
    (hdichotomy : StrongTreeMetaDichotomy.{u})
    (hleaf : StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    StrongPathOfSetsFromStrongTreeOfSets.{u} := by
  intro V _ _ G m W ell w T hell hw hm hW
  rcases hdichotomy T hell hm with hbuffered | hleaves
  · have hell_pos : 0 < ell := lt_trans Nat.zero_lt_one hell
    have hw_pos : 0 < w := lt_trans Nat.zero_lt_one hw
    have hell_sq_one : 1 ≤ ell ^ 2 :=
      Nat.succ_le_of_lt (Nat.pow_pos hell_pos)
    have hw_le_W : w ≤ W := by
      have hw_le_term : w ≤ 16 * w * ell ^ 2 + 1 := by
        calc
          w = w * 1 := by simp
          _ ≤ w * ell ^ 2 := Nat.mul_le_mul_left w hell_sq_one
          _ ≤ 16 * w * ell ^ 2 := by
            calc
              w * ell ^ 2 = 1 * (w * ell ^ 2) := by ring
              _ ≤ 16 * (w * ell ^ 2) :=
                Nat.mul_le_mul_right (w * ell ^ 2) (by decide : 1 ≤ 16)
              _ = 16 * w * ell ^ 2 := by ring
          _ ≤ 16 * w * ell ^ 2 + 1 := Nat.le_succ _
      exact Nat.le_of_lt (lt_of_le_of_lt hw_le_term hW)
    exact T.exists_strongPathOfSetsSystem_of_hasBufferedMetaPath_of_width_le
      hell_pos hw_pos hw_le_W hbuffered
  · exact hleaf T hell hw hm hW hleaves

/-- The full Theorem 4.6 extraction after the self-contained meta-tree
dichotomy has been discharged.  The only remaining input is the
many-leaves/DFS extraction branch. -/
theorem strongPathOfSetsFromStrongTreeOfSets_of_leafExtraction
    (hleaf : StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    StrongPathOfSetsFromStrongTreeOfSets.{u} :=
  strongPathOfSetsFromStrongTreeOfSets_of_metaDichotomy_and_leafExtraction
    strongTreeMetaDichotomy hleaf

/-- The Section 4 strong-tree construction plus Theorem 4.6 imply the direct
node-well-linked-core-to-strong-path route used in Theorem 3.5.

This is the proof of the `ell^50` arithmetic in the Section 4 part of
Chekuri--Chuzhoy: build a strong tree on `ell^2` clusters and width
`16 * w * ell^2 + 2`; Theorem 4.3 contributes an `m^19` loss and Lemma 4.5
contributes the additional `m^4` strongification loss.  With `m = ell^2`,
the resulting `W * m^24` term is exactly absorbed by the existing `ell^50`
route bound. -/
theorem strongPathOfSetsFromNodeWellLinkedCore_of_strongTreeCore_and_extraction
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cRoute cRouteLog cDeltaPow : ℕ,
      StrongPathOfSetsFromNodeWellLinkedCore.{u}
        cRoute cRouteLog cDeltaPow := by
  rcases hbuild with
    ⟨cBuild, cBuildLog, cDeltaPow,
      hcBuild, hcBuildLog, hcDeltaPow, hbuild'⟩
  let cRoute := cBuild * 17
  refine ⟨cRoute, cBuildLog, cDeltaPow, ?_, hcBuildLog, hcDeltaPow, ?_⟩
  · dsimp [cRoute]
    positivity
  intro V _ _ G ell w x Δ X hell hw hx hdegree hXcard hXnode hlarge
  let L := Nat.log 2 x
  let m := ell ^ 2
  let W := 16 * w * ell ^ 2 + 2
  have hell_pos : 0 < ell := lt_trans Nat.zero_lt_one hell
  have hw_pos : 0 < w := lt_trans Nat.zero_lt_one hw
  have hm_gt_one : 1 < m := by
    dsimp [m]
    nlinarith [hell]
  have hW_gt_one : 1 < W := by
    dsimp [W]
    nlinarith [hw_pos, hell_pos]
  have hW_le : W ≤ 17 * w * ell ^ 2 := by
    have hell_sq_pos : 0 < ell ^ 2 :=
      Nat.pow_pos hell_pos
    have hell_sq_one : 1 ≤ ell ^ 2 :=
      Nat.succ_le_of_lt hell_sq_pos
    have htwo_le : 2 ≤ w * ell ^ 2 := by
      calc
        2 = 2 * 1 := by omega
        _ ≤ w * ell ^ 2 := Nat.mul_le_mul hw hell_sq_one
    calc
      W = 16 * w * ell ^ 2 + 2 := rfl
      _ ≤ 16 * w * ell ^ 2 + w * ell ^ 2 :=
        Nat.add_le_add_left htwo_le _
      _ = 17 * w * ell ^ 2 := by ring
  have hbuild_large :
      cBuild * W * m ^ 24 * Δ ^ cDeltaPow * L ^ cBuildLog < x := by
    have hle :
        cBuild * W * m ^ 24 * Δ ^ cDeltaPow * L ^ cBuildLog ≤
          cRoute * w * ell ^ 50 * Δ ^ cDeltaPow * L ^ cBuildLog := by
      calc
        cBuild * W * m ^ 24 * Δ ^ cDeltaPow * L ^ cBuildLog
            ≤ cBuild * (17 * w * ell ^ 2) * m ^ 24 *
                Δ ^ cDeltaPow * L ^ cBuildLog := by
              have hcoef_le :
                  cBuild * W * m ^ 24 ≤
                    cBuild * (17 * w * ell ^ 2) * m ^ 24 := by
                exact Nat.mul_le_mul_right (m ^ 24)
                  (Nat.mul_le_mul_left cBuild hW_le)
              exact Nat.mul_le_mul_right (L ^ cBuildLog)
                (Nat.mul_le_mul_right (Δ ^ cDeltaPow) hcoef_le)
        _ = cBuild * 17 * w * ell ^ 50 *
              Δ ^ cDeltaPow * L ^ cBuildLog := by
              dsimp [m]
              ring
        _ = cRoute * w * ell ^ 50 *
              Δ ^ cDeltaPow * L ^ cBuildLog := by
              dsimp [cRoute]
    exact lt_of_le_of_lt hle (by simpa [cRoute, L] using hlarge)
  rcases hbuild' G X hm_gt_one hW_gt_one hx hdegree hXcard hXnode
      hbuild_large with
    ⟨T⟩
  exact hextract T hell hw (by simp [m]) (by simp [W])

/-- The long/buffered meta-path route is a special case of the faithful direct
Section 4 route. -/
theorem strongPathOfSetsFromNodeWellLinkedCore_of_strongTreeRoute
    {cRoute cRouteLog cDeltaPow : ℕ}
    (hroute :
      StrongTreeOfSetsFromNodeWellLinkedCore.{u}
        cRoute cRouteLog cDeltaPow) :
    StrongPathOfSetsFromNodeWellLinkedCore.{u}
      cRoute cRouteLog cDeltaPow := by
  rcases hroute with
    ⟨hcRoute, hcRouteLog, hcDeltaPow, hroute'⟩
  refine ⟨hcRoute, hcRouteLog, hcDeltaPow, ?_⟩
  intro V _ _ G ell w x Δ X hell hw hx hdegree hXcard hXnode hlarge
  rcases hroute' G X hell hw hx hdegree hXcard hXnode hlarge with
    ⟨m, T, hpath⟩
  exact T.exists_strongPathOfSetsSystem_of_hasBufferedMetaPath
    (lt_trans Nat.zero_lt_one hell) hpath

/-- Source-route target for Chekuri--Chuzhoy Theorem 3.5.

For suitable constants, the same threshold as Theorem 3.5 yields a strong
tree-of-sets system whose meta-tree contains a simple path with two buffer
vertices around the requested `ell` clusters.  The conversion from this target
to a strong path-of-sets system is fully proved in `TreeOfSets.lean`.
-/
def StrongTreeOfSetsWithBufferedPathFromTreewidth
    (cTree cTreeLog : ℕ) : Prop :=
  0 < cTree ∧ 0 < cTreeLog ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {ell w k : ℕ},
        1 < ell →
          1 < w →
            1 < k →
              k ≤ treewidth G →
                cTree * w * ell ^ 50 * (Nat.log 2 k) ^ cTreeLog < k →
                  ∃ m : ℕ, ∃ T : StrongTreeOfSetsSystem G m w,
                    T.HasBufferedMetaPath ell

/-- Chekuri--Chuzhoy Theorem 3.5, reduced to its two paper-internal source
obligations: Theorem 2.21 and the Section 4 tree-of-sets route.

No axiom is introduced here.  The proof only composes the quantitative losses:
Theorem 2.21 supplies a node-well-linked core of size `x = Θ(w ell^50
log^O(1) k)`, and the Section 4 route consumes that core while paying for the
polylogarithmic maximum-degree bound. -/
theorem strongTreeOfSetsWithBufferedPathFromTreewidth_of_core_and_route
    (hcore :
      ∃ cCore cCoreLog cDeg cDegLog : ℕ,
        NodeWellLinkedCoreFromTreewidth.{u}
          cCore cCoreLog cDeg cDegLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cTree cTreeLog : ℕ,
      StrongTreeOfSetsWithBufferedPathFromTreewidth.{u} cTree cTreeLog := by
  rcases hcore with
    ⟨cCore, cCoreLog, cDeg, cDegLog,
      hcCore, hcCoreLog, hcDeg, _hcDegLog, hcore'⟩
  rcases hroute with
    ⟨cRoute, cRouteLog, cDeltaPow,
      hcRoute, hcRouteLog, _hcDeltaPow, hroute'⟩
  let cTree := cCore * (cRoute * cDeg ^ cDeltaPow + 1)
  let cTreeLog := (cDegLog * cDeltaPow + cRouteLog) + cCoreLog
  refine ⟨cTree, cTreeLog, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hcCore (Nat.succ_pos _)
  · exact Nat.add_pos_right _ hcCoreLog
  intro V _ _ G ell w k hell hw hk htw hlarge
  let L := Nat.log 2 k
  let B := w * ell ^ 50 * L ^ (cDegLog * cDeltaPow + cRouteLog)
  let x := cRoute * cDeg ^ cDeltaPow * B + 1
  have hlog_pos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos
      (Nat.mul_pos (lt_trans Nat.zero_lt_one hw)
        (Nat.pow_pos (lt_trans Nat.zero_lt_one hell)))
      (Nat.pow_pos hlog_pos)
  have hB_one : 1 ≤ B := Nat.succ_le_of_lt hB_pos
  have hx_pos : 0 < x := by
    dsimp [x]
    omega
  have hx_gt_one : 1 < x := by
    have hmul_pos : 0 < cRoute * cDeg ^ cDeltaPow * B := by
      exact Nat.mul_pos (Nat.mul_pos hcRoute (Nat.pow_pos hcDeg)) hB_pos
    dsimp [x]
    omega
  have hx_le_scaledB :
      x ≤ (cRoute * cDeg ^ cDeltaPow + 1) * B := by
    dsimp [x]
    calc
      cRoute * cDeg ^ cDeltaPow * B + 1
          ≤ cRoute * cDeg ^ cDeltaPow * B + B :=
            Nat.add_le_add_left hB_one _
      _ = (cRoute * cDeg ^ cDeltaPow + 1) * B := by ring
  have hcore_large :
      cCore * x * L ^ cCoreLog < k := by
    have hle :
        cCore * x * L ^ cCoreLog ≤
          cTree * w * ell ^ 50 * L ^ cTreeLog := by
      calc
        cCore * x * L ^ cCoreLog
            = cCore * (x * L ^ cCoreLog) := by ring
        _ ≤ cCore *
              (((cRoute * cDeg ^ cDeltaPow + 1) * B) *
                L ^ cCoreLog) := by
              exact Nat.mul_le_mul_left cCore
                (Nat.mul_le_mul_right (L ^ cCoreLog) hx_le_scaledB)
        _ = cTree * w * ell ^ 50 * L ^ cTreeLog := by
              dsimp [cTree, cTreeLog, B]
              rw [Nat.pow_add]
              ring
    exact lt_of_le_of_lt hle (by simpa [cTree, cTreeLog, L] using hlarge)
  have hx_le_coreProduct : x ≤ cCore * x * L ^ cCoreLog := by
    have hfactor_pos : 0 < cCore * L ^ cCoreLog :=
      Nat.mul_pos hcCore (Nat.pow_pos hlog_pos)
    have hfactor_one : 1 ≤ cCore * L ^ cCoreLog :=
      Nat.succ_le_of_lt hfactor_pos
    calc
      x = 1 * x := by simp
      _ ≤ (cCore * L ^ cCoreLog) * x :=
        Nat.mul_le_mul_right x hfactor_one
      _ = cCore * x * L ^ cCoreLog := by ring
  have hx_lt_k : x < k := lt_of_le_of_lt hx_le_coreProduct hcore_large
  have hx_le_k : x ≤ k := Nat.le_of_lt hx_lt_k
  rcases hcore' G hk hx_pos htw hcore_large with
    ⟨H, hHG, hdegree, X, hXcard, hXnode⟩
  have hlog_x_le : Nat.log 2 x ≤ L := by
    simpa [L] using Nat.log_mono_right hx_le_k
  have hroute_large :
      cRoute * w * ell ^ 50 *
          (cDeg * L ^ cDegLog) ^ cDeltaPow *
          (Nat.log 2 x) ^ cRouteLog < x := by
    have hpow_log_le : (Nat.log 2 x) ^ cRouteLog ≤ L ^ cRouteLog :=
      Nat.pow_le_pow_left hlog_x_le cRouteLog
    have hle :
        cRoute * w * ell ^ 50 *
            (cDeg * L ^ cDegLog) ^ cDeltaPow *
            (Nat.log 2 x) ^ cRouteLog ≤
          cRoute * cDeg ^ cDeltaPow * B := by
      calc
        cRoute * w * ell ^ 50 *
            (cDeg * L ^ cDegLog) ^ cDeltaPow *
            (Nat.log 2 x) ^ cRouteLog
            ≤ cRoute * w * ell ^ 50 *
                (cDeg * L ^ cDegLog) ^ cDeltaPow *
                L ^ cRouteLog := by
                exact Nat.mul_le_mul_left
                  (cRoute * w * ell ^ 50 *
                    (cDeg * L ^ cDegLog) ^ cDeltaPow)
                  hpow_log_le
        _ = cRoute * cDeg ^ cDeltaPow * B := by
              dsimp [B]
              rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add]
              ring
    have hterm_lt : cRoute * cDeg ^ cDeltaPow * B < x := by
      dsimp [x]
      omega
    exact lt_of_le_of_lt hle hterm_lt
  rcases hroute' H X hell hw hx_gt_one hdegree hXcard hXnode
      hroute_large with
    ⟨m, T, hpath⟩
  refine ⟨m, T.mapLe hHG, ?_⟩
  simpa [StrongTreeOfSetsSystem.HasBufferedMetaPath,
    StrongTreeOfSetsSystem.mapLe, TreeOfSetsSystem.mapLe] using hpath

/-- Chekuri--Chuzhoy Theorem 3.5 follows from the strong-tree-of-sets
source-route target. -/
theorem exists_strongPathOfSets_of_treewidth_from_strongTreeOfSets
    (h :
      ∃ cTree cTreeLog : ℕ,
        StrongTreeOfSetsWithBufferedPathFromTreewidth.{u} cTree cTreeLog) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) := by
  rcases h with ⟨cTree, cTreeLog, hcTree, hcTreeLog, htree⟩
  refine ⟨cTree, cTreeLog, hcTree, hcTreeLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  rcases htree G hell hw hk htw hlarge with ⟨m, T, hpath⟩
  exact T.exists_strongPathOfSetsSystem_of_hasBufferedMetaPath
    (Nat.lt_trans Nat.zero_lt_one hell) hpath

/-- Chekuri--Chuzhoy Theorem 3.5 from Theorem 2.21 and the faithful direct
Section 4 path-of-sets route. -/
theorem exists_strongPathOfSets_of_treewidth_from_core_and_pathRoute
    (hcore :
      ∃ cCore cCoreLog cDeg cDegLog : ℕ,
        NodeWellLinkedCoreFromTreewidth.{u}
          cCore cCoreLog cDeg cDegLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) := by
  rcases hcore with
    ⟨cCore, cCoreLog, cDeg, cDegLog,
      hcCore, hcCoreLog, hcDeg, _hcDegLog, hcore'⟩
  rcases hroute with
    ⟨cRoute, cRouteLog, cDeltaPow,
      hcRoute, hcRouteLog, _hcDeltaPow, hroute'⟩
  let cPath := cCore * (cRoute * cDeg ^ cDeltaPow + 1)
  let cPathLog := (cDegLog * cDeltaPow + cRouteLog) + cCoreLog
  refine ⟨cPath, cPathLog, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hcCore (Nat.succ_pos _)
  · exact Nat.add_pos_right _ hcCoreLog
  intro V _ _ G ell w k hell hw hk htw hlarge
  let L := Nat.log 2 k
  let B := w * ell ^ 50 * L ^ (cDegLog * cDeltaPow + cRouteLog)
  let x := cRoute * cDeg ^ cDeltaPow * B + 1
  have hlog_pos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos
      (Nat.mul_pos (lt_trans Nat.zero_lt_one hw)
        (Nat.pow_pos (lt_trans Nat.zero_lt_one hell)))
      (Nat.pow_pos hlog_pos)
  have hB_one : 1 ≤ B := Nat.succ_le_of_lt hB_pos
  have hx_pos : 0 < x := by
    dsimp [x]
    omega
  have hx_gt_one : 1 < x := by
    have hmul_pos : 0 < cRoute * cDeg ^ cDeltaPow * B := by
      exact Nat.mul_pos (Nat.mul_pos hcRoute (Nat.pow_pos hcDeg)) hB_pos
    dsimp [x]
    omega
  have hx_le_scaledB :
      x ≤ (cRoute * cDeg ^ cDeltaPow + 1) * B := by
    dsimp [x]
    calc
      cRoute * cDeg ^ cDeltaPow * B + 1
          ≤ cRoute * cDeg ^ cDeltaPow * B + B :=
            Nat.add_le_add_left hB_one _
      _ = (cRoute * cDeg ^ cDeltaPow + 1) * B := by ring
  have hcore_large :
      cCore * x * L ^ cCoreLog < k := by
    have hle :
        cCore * x * L ^ cCoreLog ≤
          cPath * w * ell ^ 50 * L ^ cPathLog := by
      calc
        cCore * x * L ^ cCoreLog
            = cCore * (x * L ^ cCoreLog) := by ring
        _ ≤ cCore *
              (((cRoute * cDeg ^ cDeltaPow + 1) * B) *
                L ^ cCoreLog) := by
              exact Nat.mul_le_mul_left cCore
                (Nat.mul_le_mul_right (L ^ cCoreLog) hx_le_scaledB)
        _ = cPath * w * ell ^ 50 * L ^ cPathLog := by
              dsimp [cPath, cPathLog, B]
              rw [Nat.pow_add]
              ring
    exact lt_of_le_of_lt hle (by simpa [cPath, cPathLog, L] using hlarge)
  have hx_le_coreProduct : x ≤ cCore * x * L ^ cCoreLog := by
    have hfactor_pos : 0 < cCore * L ^ cCoreLog :=
      Nat.mul_pos hcCore (Nat.pow_pos hlog_pos)
    have hfactor_one : 1 ≤ cCore * L ^ cCoreLog :=
      Nat.succ_le_of_lt hfactor_pos
    calc
      x = 1 * x := by simp
      _ ≤ (cCore * L ^ cCoreLog) * x :=
        Nat.mul_le_mul_right x hfactor_one
      _ = cCore * x * L ^ cCoreLog := by ring
  have hx_lt_k : x < k := lt_of_le_of_lt hx_le_coreProduct hcore_large
  have hx_le_k : x ≤ k := Nat.le_of_lt hx_lt_k
  rcases hcore' G hk hx_pos htw hcore_large with
    ⟨H, hHG, hdegree, X, hXcard, hXnode⟩
  have hlog_x_le : Nat.log 2 x ≤ L := by
    simpa [L] using Nat.log_mono_right hx_le_k
  have hroute_large :
      cRoute * w * ell ^ 50 *
          (cDeg * L ^ cDegLog) ^ cDeltaPow *
          (Nat.log 2 x) ^ cRouteLog < x := by
    have hpow_log_le : (Nat.log 2 x) ^ cRouteLog ≤ L ^ cRouteLog :=
      Nat.pow_le_pow_left hlog_x_le cRouteLog
    have hle :
        cRoute * w * ell ^ 50 *
            (cDeg * L ^ cDegLog) ^ cDeltaPow *
            (Nat.log 2 x) ^ cRouteLog ≤
          cRoute * cDeg ^ cDeltaPow * B := by
      calc
        cRoute * w * ell ^ 50 *
            (cDeg * L ^ cDegLog) ^ cDeltaPow *
            (Nat.log 2 x) ^ cRouteLog
            ≤ cRoute * w * ell ^ 50 *
                (cDeg * L ^ cDegLog) ^ cDeltaPow *
                L ^ cRouteLog := by
                exact Nat.mul_le_mul_left
                  (cRoute * w * ell ^ 50 *
                    (cDeg * L ^ cDegLog) ^ cDeltaPow)
                  hpow_log_le
        _ = cRoute * cDeg ^ cDeltaPow * B := by
              dsimp [B]
              rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add]
              ring
    have hterm_lt : cRoute * cDeg ^ cDeltaPow * B < x := by
      dsimp [x]
      omega
    exact lt_of_le_of_lt hle hterm_lt
  rcases hroute' H X hell hw hx_gt_one hdegree hXcard hXnode
      hroute_large with
    ⟨P⟩
  exact ⟨P.mapLe hHG⟩

/-- Chekuri--Chuzhoy Theorem 3.5 from Theorem 2.21 and the split Section 4
route: the strong-tree construction plus the Theorem 4.6 extraction. -/
theorem exists_strongPathOfSets_of_treewidth_from_core_treeCore_and_extraction
    (hcore :
      ∃ cCore cCoreLog cDeg cDegLog : ℕ,
        NodeWellLinkedCoreFromTreewidth.{u}
          cCore cCoreLog cDeg cDegLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_and_pathRoute
    hcore
    (strongPathOfSetsFromNodeWellLinkedCore_of_strongTreeCore_and_extraction
      hbuild hextract)

/-- Chekuri--Chuzhoy Theorem 3.5 from Theorem 2.21, the strong-tree
construction, and the split proof of Theorem 4.6: buffered paths are handled by
`TreeOfSets.lean`, while the DFS branch remains explicit. -/
theorem exists_strongPathOfSets_of_treewidth_from_core_treeCore_metaDichotomy_and_leafExtraction
    (hcore :
      ∃ cCore cCoreLog cDeg cDegLog : ℕ,
        NodeWellLinkedCoreFromTreewidth.{u}
          cCore cCoreLog cDeg cDegLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : StrongTreeMetaDichotomy.{u})
    (hleaf : StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_treeCore_and_extraction
    hcore hbuild
    (strongPathOfSetsFromStrongTreeOfSets_of_metaDichotomy_and_leafExtraction
      hdichotomy hleaf)

/-- Chekuri--Chuzhoy Theorem 3.5 from Theorem 2.21, the strong-tree
construction, and the remaining many-leaves/DFS branch of Theorem 4.6.

The finite meta-tree dichotomy is proved in this file by
`strongTreeMetaDichotomy`, so it is no longer an external input. -/
theorem exists_strongPathOfSets_of_treewidth_from_core_treeCore_leafExtraction
    (hcore :
      ∃ cCore cCoreLog cDeg cDegLog : ℕ,
        NodeWellLinkedCoreFromTreewidth.{u}
          cCore cCoreLog cDeg cDegLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_treeCore_and_extraction
    hcore hbuild
    (strongPathOfSetsFromStrongTreeOfSets_of_leafExtraction hleaf)

/-- Chekuri--Chuzhoy Theorem 3.5 from the two source-route obligations used in
its proof: Theorem 2.21 and the Section 4 tree-of-sets route. -/
theorem exists_strongPathOfSets_of_treewidth_from_core_and_route
    (hcore :
      ∃ cCore cCoreLog cDeg cDegLog : ℕ,
        NodeWellLinkedCoreFromTreewidth.{u}
          cCore cCoreLog cDeg cDegLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_strongTreeOfSets
    (strongTreeOfSetsWithBufferedPathFromTreewidth_of_core_and_route
      hcore hroute)

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
