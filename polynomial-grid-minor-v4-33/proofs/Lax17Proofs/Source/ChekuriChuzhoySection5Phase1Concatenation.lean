import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1RootExtraction
import Lax17Proofs.Source.ChekuriChuzhoySection5Phase1Support
import Lax17Proofs.Source.ChekuriChuzhoyMetaTreeDichotomy

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5.4.1: root-clean leaf paths

Before the Claim 5.15 paths are concatenated with linkages inside the root
router, each path is truncated at its first visit to that router.  This is the
canonical source-faithful normalization implicit in the directed network of
the paper: every normalized path meets the root router only at its target.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Phase1Concatenation


open Finset
open ChekuriChuzhoySection5Phase1Restoration
open ChekuriChuzhoySection5Phase1RootExtraction

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A path packing cleaned at the root router, together with the exact endpoint
sets actually used after cleaning. -/
structure RootCleanLeafPackingFamily
    (G : _root_.SimpleGraph V) {m : Nat}
    (leafRouter : Fin m -> Finset V) (root : Finset V) (q : Nat) where
  sourceSet : Fin m -> Finset V
  targetSet : Fin m -> Finset V
  packing : forall i, PathPacking G (sourceSet i) root
  sourceSet_subset_leaf : forall i, sourceSet i ⊆ leafRouter i
  sourceSet_subset_interface : forall i,
    sourceSet i ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G (leafRouter i)
  targetSet_subset_root : forall i, targetSet i ⊆ root
  targetSet_subset_interface : forall i,
    targetSet i ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G root
  sourceSet_card : forall i, (sourceSet i).card = q
  targetSet_card : forall i, (targetSet i).card = q
  path_count : forall i, (packing i).card = q
  exact_sourceSet : forall i, (packing i).sourceSet = sourceSet i
  exact_targetSet : forall i, (packing i).targetSet = targetSet i
  sourceSet_disjoint_root :
    forall i, Disjoint (sourceSet i) root
  root_disjoint_selectedLeaves :
    Disjoint root
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter)
  internallyDisjointRoot :
    forall i, (packing i).InternallyDisjointFromSet root
  internallyDisjointLeaves :
    forall i,
      (packing i).InternallyDisjointFromSet
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter)
  mutuallyNodeDisjoint :
    forall {i j : Fin m}, i ≠ j ->
      (packing i).MutuallyNodeDisjoint (packing j)

/-- Cleaning at a right terminal region makes every used target an interface
vertex when all left terminals lie outside that region. -/
theorem PathPacking.cleanToRight_targetSet_subset_interface
    {S root : Finset V} (P : PathPacking G S root)
    (hdisj : Disjoint S root) :
    P.cleanToRight.targetSet ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G root := by
  classical
  intro v hv
  rcases P.cleanToRight.exists_orient_target_eq_of_mem_targetSet hv with
    ⟨i, hi⟩
  let Q := P.cleanToRight.orient.path i
  have hsourceS : Q.source ∈ S :=
    GraphPath.orient_source_mem
      (P.cleanToRight.path i) (P.cleanToRight.connects i)
  have htargetRoot : Q.target ∈ root :=
    GraphPath.orient_target_mem
      (P.cleanToRight.path i) (P.cleanToRight.connects i)
  have hne : Q.source ≠ Q.target := by
    intro h
    exact Finset.disjoint_left.mp hdisj hsourceS
      (by simpa [h] using htargetRoot)
  have hadj : G.Adj Q.penultimate Q.target :=
    Q.penultimate_adj_target hne
  have hpenOutside : Q.penultimate ∉ root := by
    intro hpen
    have hclean :
        Q.InternallyDisjointFromSet root := by
      exact PathPacking.orient_internallyDisjointFromSet
        P.cleanToRight_internallyDisjointFromSet i
    rcases hclean (Q.penultimate_mem_vertexSet hne) hpen with hp | hp
    · exact Finset.disjoint_left.mp hdisj
        (by simpa [hp] using hsourceS) hpen
    · exact hadj.ne hp
  apply ChekuriChuzhoySection5Clustering.mem_interfaceVertices.mpr
  exact ⟨by rw [← hi]; exact htargetRoot, Q.penultimate, hpenOutside,
    by rw [← hi]; exact hadj.symm⟩

/-- Widen the restored target carrier to the whole root router and truncate
every path at its first root visit. -/
noncomputable def cleanedPacking
    {m q : Nat} {leafRouter : Fin m -> Finset V}
    {targetCarrier root : Finset V}
    (R : RestoredLeafPackingFamily G leafRouter targetCarrier q)
    (htargetRoot : targetCarrier ⊆ root) (i : Fin m) :
    PathPacking G (R.sourceSet i) root :=
  ((R.packing i).widenTerminals Finset.Subset.rfl
    ((R.targetSet_subset_root i).trans htargetRoot)).cleanToRight

/-- First-hit normalization of a restored Claim 5.15 family. -/
theorem exists_rootCleanLeafPackingFamily
    {m q : Nat} {leafRouter : Fin m -> Finset V}
    {targetCarrier root : Finset V}
    (R : RestoredLeafPackingFamily G leafRouter targetCarrier q)
    (htargetRoot : targetCarrier ⊆ root)
    (hrootLeaf : forall i, Disjoint root (leafRouter i)) :
    Nonempty (RootCleanLeafPackingFamily G leafRouter root q) := by
  classical
  let W : forall i, PathPacking G (R.sourceSet i) root :=
    fun i => (R.packing i).widenTerminals Finset.Subset.rfl
      ((R.targetSet_subset_root i).trans htargetRoot)
  let P : forall i, PathPacking G (R.sourceSet i) root :=
    fun i => (W i).cleanToRight
  have hsourceDisjoint : forall i, Disjoint (R.sourceSet i) root :=
    fun i => (hrootLeaf i).symm.mono_left (R.sourceSet_subset_cluster i)
  have hrootSelected :
      Disjoint root
        (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) := by
    rw [Finset.disjoint_left]
    intro v hvRoot hvSelected
    rcases ChekuriChuzhoySection5Phase1Leaves.mem_selectedUnion.mp hvSelected with
      ⟨i, hvLeaf⟩
    exact Finset.disjoint_left.mp (hrootLeaf i) hvRoot hvLeaf
  have htargetCard : forall i, (P i).targetSet.card = q := by
    intro i
    rw [(P i).targetSet_card]
    simpa [P, W] using R.path_count i
  refine ⟨{
    sourceSet := R.sourceSet
    targetSet := fun i => (P i).targetSet
    packing := fun i => P i
    sourceSet_subset_leaf := R.sourceSet_subset_cluster
    sourceSet_subset_interface := R.sourceSet_subset_interface
    targetSet_subset_root := fun i => (P i).targetSet_subset_right
    targetSet_subset_interface := ?_
    sourceSet_card := R.sourceSet_card
    targetSet_card := htargetCard
    path_count := ?_
    exact_sourceSet := ?_
    exact_targetSet := fun _ => rfl
    sourceSet_disjoint_root := hsourceDisjoint
    root_disjoint_selectedLeaves := hrootSelected
    internallyDisjointRoot := fun i => by
      simpa [P] using (W i).cleanToRight_internallyDisjointFromSet
    internallyDisjointLeaves := ?_
    mutuallyNodeDisjoint := ?_ }⟩
  · intro i
    exact PathPacking.cleanToRight_targetSet_subset_interface (W i)
      (hsourceDisjoint i)
  · intro i
    simpa [P, W] using R.path_count i
  · intro i
    apply (P i).sourceSet_eq_left_of_card_eq
    rw [show (P i).card = q by
      simpa [P, W] using R.path_count i, R.sourceSet_card i]
  · intro i k v hv hvSelected
    have hW :
        (W i).InternallyDisjointFromSet
          (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) := by
      intro a x hx hxSelected
      exact R.internallyDisjoint i a
        (by simpa [W, PathPacking.widenTerminals] using hx) hxSelected
    have hOrient :=
      PathPacking.orient_internallyDisjointFromSet hW k
    exact
      (W i).orient.path k |>.takeUntil_internallyDisjointFromSet
        ((W i).orient.path k |>.firstHitVertex_mem_vertexSet root
          ((W i).orient_path_meets_right k))
        hOrient
        (by simpa [P, PathPacking.cleanToRight] using hv)
        hvSelected
  · intro i j hij a b
    apply (R.mutuallyNodeDisjoint hij a b).mono
    · exact (W i).cleanToRight_path_vertexSet_subset a
    · exact (W j).cleanToRight_path_vertexSet_subset b

namespace RootCleanLeafPackingFamily

variable {m q width : Nat} {leafRouter : Fin m -> Finset V}
variable {root : Finset V}

/-- Orient a cleaned family and expose its exact used terminal sets. -/
noncomputable def perfect
    (C : RootCleanLeafPackingFamily G leafRouter root q) (i : Fin m) :
    PerfectPathPacking G (C.sourceSet i) (C.targetSet i) :=
  (C.packing i).toPerfectUsedTerminals.copyTerminals
    (C.exact_sourceSet i) (C.exact_targetSet i)

@[simp] theorem perfect_card
    (C : RootCleanLeafPackingFamily G leafRouter root q) (i : Fin m) :
    (C.perfect i).card = q := by
  simpa [perfect] using C.path_count i

theorem perfect_internallyDisjointRoot
    (C : RootCleanLeafPackingFamily G leafRouter root q) (i : Fin m) :
    (C.perfect i).toPathPacking.InternallyDisjointFromSet root := by
  simpa [perfect, PerfectPathPacking.copyTerminals] using
    (C.packing i).toPerfectUsedTerminals_internallyDisjointFromSet
      (C.internallyDisjointRoot i)

theorem perfect_internallyDisjointLeaves
    (C : RootCleanLeafPackingFamily G leafRouter root q) (i : Fin m) :
    (C.perfect i).toPathPacking.InternallyDisjointFromSet
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) := by
  simpa [perfect, PerfectPathPacking.copyTerminals] using
    (C.packing i).toPerfectUsedTerminals_internallyDisjointFromSet
      (C.internallyDisjointLeaves i)

/-- The leaf-side endpoints retained when the cleaned paths are restricted to
the root block extracted for router `i`. -/
noncomputable def leafEndpoint
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) : Finset V :=
  (C.perfect i).sourceSet
    ((C.perfect i).targetIndexSetOfSubset (E.endpoint i))

/-- The canonical restricted leaf-to-root leg ending at the extracted block. -/
noncomputable def leafLeg
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    PerfectPathPacking G (C.leafEndpoint E i) (E.endpoint i) :=
  (C.perfect i).restrictTargetSet (E.endpoint i) (E.endpoint_subset i)

theorem leafEndpoint_subset_sourceSet
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    C.leafEndpoint E i ⊆ C.sourceSet i :=
  (C.perfect i).sourceSet_subset_left _

theorem leafEndpoint_subset_leaf
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    C.leafEndpoint E i ⊆ leafRouter i :=
  (C.leafEndpoint_subset_sourceSet E i).trans
    (C.sourceSet_subset_leaf i)

theorem leafEndpoint_subset_interface
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    C.leafEndpoint E i ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G (leafRouter i) :=
  (C.leafEndpoint_subset_sourceSet E i).trans
    (C.sourceSet_subset_interface i)

@[simp] theorem leafEndpoint_card
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    (C.leafEndpoint E i).card = width := by
  rw [← (C.leafLeg E i).card_eq_left_card]
  exact (C.perfect i).restrictTargetSet_card
    (E.endpoint i) (E.endpoint_subset i) |>.trans (E.endpoint_card i)

@[simp] theorem leafLeg_card
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    (C.leafLeg E i).card = width := by
  exact (C.perfect i).restrictTargetSet_card
    (E.endpoint i) (E.endpoint_subset i) |>.trans (E.endpoint_card i)

theorem leafEndpoint_disjoint_root
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    Disjoint (C.leafEndpoint E i) root :=
  (C.sourceSet_disjoint_root i).mono_left
    (C.leafEndpoint_subset_sourceSet E i)

theorem leafLeg_internallyDisjointRoot
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    (C.leafLeg E i).toPathPacking.InternallyDisjointFromSet root :=
  (C.perfect i).restrictTargetSet_internallyDisjointFromSet
    (E.endpoint i) (E.endpoint_subset i)
    (C.perfect_internallyDisjointRoot i)

theorem leafLeg_internallyDisjointLeaves
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    (C.leafLeg E i).toPathPacking.InternallyDisjointFromSet
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) :=
  (C.perfect i).restrictTargetSet_internallyDisjointFromSet
    (E.endpoint i) (E.endpoint_subset i)
    (C.perfect_internallyDisjointLeaves i)

theorem leafLeg_staysIn_perfectVertexSet
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    (C.leafLeg E i).toPathPacking.StaysIn
      (C.perfect i).toPathPacking.vertexSet :=
  (C.perfect i).restrictTargetSet_staysIn_vertexSet
    (E.endpoint i) (E.endpoint_subset i)

theorem leafLeg_mutuallyNodeDisjoint
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (C.leafLeg E i).toPathPacking.MutuallyNodeDisjoint
      (C.leafLeg E j).toPathPacking := by
  intro a b
  simpa [leafLeg, perfect, PerfectPathPacking.restrictTargetSet,
    PerfectPathPacking.restrictIndexSet, PerfectPathPacking.copyTerminals,
    PathPacking.toPerfectUsedTerminals, GraphPath.NodeDisjoint] using
    C.mutuallyNodeDisjoint hij a.1 b.1

/-- A full root-router linkage between two extracted endpoint blocks. -/
noncomputable def rootLinkage
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    PerfectPathPacking G (E.endpoint i) (E.endpoint j) :=
  (E.endpoint_pair_nodeLinked hij).exists_perfectPathPacking_of_card_eq
    ((E.endpoint_card i).trans (E.endpoint_card j).symm) |>.choose

@[simp] theorem rootLinkage_card
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (C.rootLinkage E hij).card = width := by
  exact
    (E.endpoint_pair_nodeLinked hij).exists_perfectPathPacking_of_card_eq
      ((E.endpoint_card i).trans (E.endpoint_card j).symm) |>.choose_spec.1
    |>.trans (E.endpoint_card i)

theorem rootLinkage_staysIn_root
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (C.rootLinkage E hij).toPathPacking.StaysIn root :=
  (E.endpoint_pair_nodeLinked hij).exists_perfectPathPacking_of_card_eq
    ((E.endpoint_card i).trans (E.endpoint_card j).symm) |>.choose_spec.2

theorem endpoint_disjoint_selectedLeaves
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    Disjoint (E.endpoint i)
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) :=
  C.root_disjoint_selectedLeaves.mono_left
    ((E.endpoint_subset i).trans (C.targetSet_subset_root i))

theorem rootLinkage_internallyDisjointLeaves
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (C.rootLinkage E hij).toPathPacking.InternallyDisjointFromSet
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) := by
  intro a v hv hvLeaves
  exact False.elim <|
    Finset.disjoint_left.mp C.root_disjoint_selectedLeaves
      (C.rootLinkage_staysIn_root E hij a hv) hvLeaves

theorem leafEndpoint_subset_leafLegVertexSet
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) (i : Fin m) :
    C.leafEndpoint E i ⊆ (C.leafLeg E i).toPathPacking.vertexSet := by
  intro v hv
  rcases (C.leafLeg E i).source_bijective.2 ⟨v, hv⟩ with ⟨a, ha⟩
  have hsource : ((C.leafLeg E i).path a).source = v :=
    congrArg Subtype.val ha
  exact (C.leafLeg E i).toPathPacking.mem_vertexSet.mpr
    ⟨a, by simpa [hsource] using
      GraphPath.source_mem_vertexSet ((C.leafLeg E i).path a)⟩

/-- The root linkage followed by the reversed leg of the destination leaf. -/
noncomputable def rootToLeafLeg
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    PerfectPathPacking G (E.endpoint i) (C.leafEndpoint E j) :=
  (C.rootLinkage E hij).concatOfFirstStaysInSecondInternallyDisjoint
    (C.leafLeg E j).reverse
    (C.rootLinkage_staysIn_root E hij)
    ((C.leafLeg E j).reverse_internallyDisjointFromSet
      (C.leafLeg_internallyDisjointRoot E j))
    (C.leafEndpoint_disjoint_root E j)

@[simp] theorem rootToLeafLeg_card
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (C.rootToLeafLeg E hij).card = width := by
  simpa [rootToLeafLeg] using C.rootLinkage_card E hij

theorem rootToLeafLeg_staysIn
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (C.rootToLeafLeg E hij).toPathPacking.StaysIn
      (root ∪ (C.leafLeg E j).toPathPacking.vertexSet) := by
  exact
    (C.rootLinkage E hij).concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
      (C.leafLeg E j).reverse
      (C.rootLinkage_staysIn_root E hij)
      ((C.leafLeg E j).reverse_internallyDisjointFromSet
        (C.leafLeg_internallyDisjointRoot E j))
      (C.leafEndpoint_disjoint_root E j)
      ((C.leafLeg E j).reverse_staysIn
        (fun a => (C.leafLeg E j).toPathPacking.path_vertexSet_subset_vertexSet a))

theorem rootToLeafLeg_path_edgeSet_subset
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j)
    (a : (C.rootToLeafLeg E hij).Index) :
    ((C.rootToLeafLeg E hij).path a).edgeSet ⊆
      ((C.rootLinkage E hij).path a).edgeSet ∪
        ((C.leafLeg E j).reverse.path
          ((C.rootLinkage E hij).indexOfSourceTarget
            (C.leafLeg E j).reverse a)).edgeSet := by
  exact
    (C.rootLinkage E hij).concatOfFirstStaysInSecondInternallyDisjoint_path_edgeSet_subset
      (C.leafLeg E j).reverse
      (C.rootLinkage_staysIn_root E hij)
      ((C.leafLeg E j).reverse_internallyDisjointFromSet
        (C.leafLeg_internallyDisjointRoot E j))
      (C.leafEndpoint_disjoint_root E j) a

theorem rootToLeafLeg_internallyDisjointLeaves
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (C.rootToLeafLeg E hij).toPathPacking.InternallyDisjointFromSet
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) := by
  exact
    (C.rootLinkage E hij).concatOfFirstStaysInSecondInternallyDisjoint_internallyDisjointFromSet
      (C.leafLeg E j).reverse
      (C.rootLinkage_staysIn_root E hij)
      ((C.leafLeg E j).reverse_internallyDisjointFromSet
        (C.leafLeg_internallyDisjointRoot E j))
      (C.leafEndpoint_disjoint_root E j)
      (C.rootLinkage_internallyDisjointLeaves E hij)
      ((C.leafLeg E j).reverse_internallyDisjointFromSet
        (C.leafLeg_internallyDisjointLeaves E j))
      (C.endpoint_disjoint_selectedLeaves E j)

/-- The complete leaf-to-leaf splice from Section 5.4.1: a restricted first
leaf leg, a root-router linkage, and a reversed restricted second leaf leg. -/
noncomputable def pairPacking
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    PerfectPathPacking G (C.leafEndpoint E i) (C.leafEndpoint E j) :=
  (C.leafLeg E i).concatOfFirstInternallyDisjointSecondStaysIn
    (C.rootToLeafLeg E hij)
    ((C.leafLeg E i).toPathPacking.internallyDisjointFromSet_union_of_disjoint_vertexSet
      (C.leafLeg_internallyDisjointRoot E i)
      (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (C.leafLeg_mutuallyNodeDisjoint E hij)))
    (C.rootToLeafLeg_staysIn E hij)
    (by
      rw [Finset.disjoint_left]
      intro v hv hiUnion
      rcases Finset.mem_union.mp hiUnion with hvRoot | hvOther
      · exact Finset.disjoint_left.mp (C.leafEndpoint_disjoint_root E i)
          hv hvRoot
      · exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (C.leafLeg_mutuallyNodeDisjoint E hij))
          (C.leafEndpoint_subset_leafLegVertexSet E i hv) hvOther)

@[simp] theorem pairPacking_card
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (C.pairPacking E hij).card = width := by
  simpa [pairPacking] using C.leafLeg_card E i

theorem pairPacking_internallyDisjointLeaves
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j) :
    (C.pairPacking E hij).toPathPacking.InternallyDisjointFromSet
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter) := by
  exact
    (C.leafLeg E i).concatOfFirstInternallyDisjointSecondStaysIn_internallyDisjointFromSet
      (C.rootToLeafLeg E hij)
      ((C.leafLeg E i).toPathPacking.internallyDisjointFromSet_union_of_disjoint_vertexSet
        (C.leafLeg_internallyDisjointRoot E i)
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (C.leafLeg_mutuallyNodeDisjoint E hij)))
      (C.rootToLeafLeg_staysIn E hij)
      (by
        rw [Finset.disjoint_left]
        intro v hv hiUnion
        rcases Finset.mem_union.mp hiUnion with hvRoot | hvOther
        · exact Finset.disjoint_left.mp (C.leafEndpoint_disjoint_root E i)
            hv hvRoot
        · exact Finset.disjoint_left.mp
            (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
              (C.leafLeg_mutuallyNodeDisjoint E hij))
            (C.leafEndpoint_subset_leafLegVertexSet E i hv) hvOther)
      (C.leafLeg_internallyDisjointLeaves E i)
      (C.rootToLeafLeg_internallyDisjointLeaves E hij)
      (C.endpoint_disjoint_selectedLeaves E i)

theorem pairPacking_path_edgeSet_subset
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width)
    {i j : Fin m} (hij : i ≠ j)
    (a : (C.pairPacking E hij).Index) :
    ((C.pairPacking E hij).path a).edgeSet ⊆
      ((C.leafLeg E i).path a).edgeSet ∪
        ((C.rootToLeafLeg E hij).path
          ((C.leafLeg E i).indexOfSourceTarget
            (C.rootToLeafLeg E hij) a)).edgeSet := by
  exact
    (C.leafLeg E i).concatOfFirstInternallyDisjointSecondStaysIn_path_edgeSet_subset
      (C.rootToLeafLeg E hij)
      ((C.leafLeg E i).toPathPacking.internallyDisjointFromSet_union_of_disjoint_vertexSet
        (C.leafLeg_internallyDisjointRoot E i)
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (C.leafLeg_mutuallyNodeDisjoint E hij)))
      (C.rootToLeafLeg_staysIn E hij)
      (by
        rw [Finset.disjoint_left]
        intro v hv hiUnion
        rcases Finset.mem_union.mp hiUnion with hvRoot | hvOther
        · exact Finset.disjoint_left.mp (C.leafEndpoint_disjoint_root E i)
            hv hvRoot
        · exact Finset.disjoint_left.mp
            (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
              (C.leafLeg_mutuallyNodeDisjoint E hij))
            (C.leafEndpoint_subset_leafLegVertexSet E i hv) hvOther)
      a

/-- The all-pairs direct routing conclusion produced at the end of Phase 1. -/
structure LeafPairRouting
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) where
  boundary : Fin m -> Finset V
  boundary_eq : forall i, boundary i = C.leafEndpoint E i
  boundary_subset_leaf : forall i, boundary i ⊆ leafRouter i
  boundary_subset_interface : forall i,
    boundary i ⊆
      ChekuriChuzhoySection5Clustering.interfaceVertices G (leafRouter i)
  boundary_card : forall i, (boundary i).card = width
  packing : forall {i j : Fin m}, i ≠ j ->
    PerfectPathPacking G (boundary i) (boundary j)
  packing_card : forall {i j : Fin m} (hij : i ≠ j),
    (packing hij).card = width
  packing_direct : forall {i j : Fin m} (hij : i ≠ j),
    (packing hij).toPathPacking.InternallyDisjointFromSet
      (ChekuriChuzhoySection5Phase1Leaves.selectedUnion leafRouter)

/-- Assemble the deterministic all-pairs routing package from the normalized
Claim 5.15 family and the specialized Corollary 2.12 extraction. -/
noncomputable def leafPairRouting
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (E : RootExtraction G root C.targetSet width) :
    LeafPairRouting C E where
  boundary := C.leafEndpoint E
  boundary_eq := fun _ => rfl
  boundary_subset_leaf := C.leafEndpoint_subset_leaf E
  boundary_subset_interface := C.leafEndpoint_subset_interface E
  boundary_card := C.leafEndpoint_card E
  packing := fun hij => C.pairPacking E hij
  packing_card := fun hij => C.pairPacking_card E hij
  packing_direct := fun hij => C.pairPacking_internallyDisjointLeaves E hij

end RootCleanLeafPackingFamily

/-- Apply the proved root extraction to a normalized leaf-path family. -/
theorem exists_rootExtraction_of_rootCleanLeafPackingFamily
    {m q cap alphaNum alphaDen Delta groupSize groupedWidth
      carrierWidth outWidth : Nat}
    {leafRouter : Fin m -> Finset V} {root : Finset V}
    (C : RootCleanLeafPackingFamily G leafRouter root q)
    (hroot : IsCluster G root)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G root cap alphaNum alphaDen)
    (hunionCap : m * q ≤ cap)
    (hgroupSize : 0 < groupSize)
    (hgroupSizeWidth : groupSize ≤ q)
    (hscale : alphaDen ≤ alphaNum * groupSize)
    (hgroupedWidth : groupedWidth ≤ q / (3 * groupSize))
    (hcarrierWidth :
      carrierWidth ≤ (3 * groupedWidth) / (10 * Delta * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    Nonempty (RootExtraction G root C.targetSet outWidth) := by
  classical
  have htargetVertex :
      forall i, C.targetSet i ⊆ (C.packing i).vertexSet := by
    intro i v hv
    rw [← C.exact_targetSet i] at hv
    rcases (C.packing i).exists_orient_target_eq_of_mem_targetSet hv with
      ⟨k, hk⟩
    exact (C.packing i).mem_vertexSet.mpr
      ⟨k, by
        rw [← (C.packing i).orient_path_vertexSet]
        simpa [hk] using GraphPath.target_mem_vertexSet
          ((C.packing i).orient.path k)⟩
  have htargetDisjoint :
      Set.PairwiseDisjoint Set.univ C.targetSet := by
    intro i _ j _ hij
    exact
      (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
        (C.mutuallyNodeDisjoint hij)).mono
          (htargetVertex i) (htargetVertex j)
  exact exists_rootExtraction_of_truncatedBandwidth
    C.targetSet hroot hdegree hDelta C.targetSet_subset_root
    C.targetSet_subset_interface C.targetSet_card htargetDisjoint
    hband hunionCap hgroupSize hgroupSizeWidth hscale hgroupedWidth
    hcarrierWidth houtCarrier hlink

/-- The normalized Claim 5.15 paths and their root-router extraction. -/
structure RootCleanExtractionPackage
    (G : _root_.SimpleGraph V) {m : Nat}
    (leafRouter : Fin m -> Finset V) (root : Finset V)
    (q outWidth : Nat) where
  cleaned : RootCleanLeafPackingFamily G leafRouter root q
  extraction : RootExtraction G root cleaned.targetSet outWidth

/-- The full end-of-Phase-1 package, including the all-pairs direct leaf
routing obtained by the three-way concatenation. -/
structure LeafPairRoutingPackage
    (G : _root_.SimpleGraph V) {m : Nat}
    (leafRouter : Fin m -> Finset V) (root : Finset V)
    (q outWidth : Nat) where
  cleaned : RootCleanLeafPackingFamily G leafRouter root q
  extraction : RootExtraction G root cleaned.targetSet outWidth
  routing : RootCleanLeafPackingFamily.LeafPairRouting cleaned extraction

/-- An injective choice of selected support-tree leaves together with a
separate root. -/
structure SupportTreeLeafSelection
    {n : Nat} (T : _root_.SimpleGraph (Fin n)) (m : Nat) where
  leafRouter : Fin m -> Fin n
  leafRouter_injective : Function.Injective leafRouter
  leafRouter_degree_one : forall i, DegreeEquals T (leafRouter i) 1
  rootRouter : Fin n
  rootRouter_ne_leaf : forall i, rootRouter ≠ leafRouter i
  rootRouter_dist_le : forall i, T.dist rootRouter (leafRouter i) ≤ m

/-- Choose `m` support-tree leaves and a distinct root from any family of at
least `m + 1` leaves. -/
theorem exists_supportTreeLeafSelection_of_manyLeaves
    {n m : Nat} (T : _root_.SimpleGraph (Fin n))
    (leaves : Finset (Fin n))
    (hleaf : forall v, v ∈ leaves -> DegreeEquals T v 1)
    (hcard : m + 1 ≤ leaves.card)
    (hdist : forall a b, T.dist a b ≤ m) :
    Nonempty (SupportTreeLeafSelection T m) := by
  classical
  let order : Fin (m + 1) -> Fin n := fun r =>
    (leaves.equivFin.symm
      ⟨r.1, lt_of_lt_of_le r.2 hcard⟩).1
  have horderInjective : Function.Injective order := by
    intro a b hab
    apply Fin.ext
    have hsub :
        leaves.equivFin.symm
            ⟨a.1, lt_of_lt_of_le a.2 hcard⟩ =
          leaves.equivFin.symm
            ⟨b.1, lt_of_lt_of_le b.2 hcard⟩ :=
      Subtype.ext hab
    have hfin :=
      leaves.equivFin.symm.injective hsub
    exact congrArg (fun x : Fin leaves.card => x.val) hfin
  let leafRouter : Fin m -> Fin n :=
    fun i => order ⟨i.1 + 1, by omega⟩
  let rootRouter : Fin n := order ⟨0, by omega⟩
  refine ⟨{
    leafRouter := leafRouter
    leafRouter_injective := ?_
    leafRouter_degree_one := ?_
    rootRouter := rootRouter
    rootRouter_ne_leaf := ?_
    rootRouter_dist_le := ?_ }⟩
  · intro i j hij
    apply Fin.ext
    have hindex :
        (⟨i.1 + 1, by omega⟩ : Fin (m + 1)) =
          ⟨j.1 + 1, by omega⟩ :=
      horderInjective (by simpa [leafRouter] using hij)
    have hval := congrArg Fin.val hindex
    change i.1 + 1 = j.1 + 1 at hval
    omega
  · intro i
    apply hleaf
    exact (leaves.equivFin.symm
      ⟨i.1 + 1, lt_of_lt_of_le (by omega) hcard⟩).2
  · intro i hroot
    have hindex :
        (⟨0, by omega⟩ : Fin (m + 1)) =
          ⟨i.1 + 1, by omega⟩ :=
      horderInjective (by simpa [rootRouter, leafRouter] using hroot)
    have hval := congrArg Fin.val hindex
    change 0 = i.1 + 1 at hval
    omega
  · intro i
    exact hdist rootRouter (leafRouter i)

/-- The finite-tree branch used at the start of Phase 1. A support tree on at
least `m^2` vertices either has the buffered long path used by Case 1 or
provides the selected leaves and separate root required by Case 2. -/
theorem exists_bufferedSupportPath_or_leafSelection
    {n m : Nat} (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree) (hm : 1 < m) (hcard : m ^ 2 ≤ n) :
    (∃ order : Fin (m + 2) -> Fin n,
        Function.Injective order ∧
          forall r : Fin (m + 1),
            T.Adj (order ⟨r.1, by omega⟩)
              (order ⟨r.1 + 1, by omega⟩)) ∨
      Nonempty (SupportTreeLeafSelection T m) := by
  classical
  letI := Classical.decRel T.Adj
  rcases ChekuriChuzhoy.exists_bufferedPath_or_manyLeaves_of_tree
      hT hm (by simpa using hcard) with hpath | hleaves
  · exact Or.inl hpath
  · rcases hleaves with ⟨leaves, hleaf, hleafCard, hshort⟩
    have hdist : ∀ a b, T.dist a b ≤ m := by
      intro a b
      rcases (hT.connected a b).exists_path_of_dist with ⟨p, hp, hlen⟩
      rw [← hlen]
      exact hshort p hp
    exact Or.inr <|
      exists_supportTreeLeafSelection_of_manyLeaves T leaves
        (fun v hv => (hleaf v).1 hv) hleafCard hdist

/-- Normalize a restored family at the root and immediately apply the proved
specialized Corollary 2.12 extraction. -/
theorem exists_rootCleanExtractionPackage_of_restored
    {m q cap alphaNum alphaDen Delta groupSize groupedWidth
      carrierWidth outWidth : Nat}
    {leafRouter : Fin m -> Finset V}
    {targetCarrier root : Finset V}
    (R : RestoredLeafPackingFamily G leafRouter targetCarrier q)
    (htargetRoot : targetCarrier ⊆ root)
    (hrootLeaf : forall i, Disjoint root (leafRouter i))
    (hroot : IsCluster G root)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G root cap alphaNum alphaDen)
    (hunionCap : m * q ≤ cap)
    (hgroupSize : 0 < groupSize)
    (hgroupSizeWidth : groupSize ≤ q)
    (hscale : alphaDen ≤ alphaNum * groupSize)
    (hgroupedWidth : groupedWidth ≤ q / (3 * groupSize))
    (hcarrierWidth :
      carrierWidth ≤ (3 * groupedWidth) / (10 * Delta * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    Nonempty
      (RootCleanExtractionPackage G leafRouter root q outWidth) := by
  rcases exists_rootCleanLeafPackingFamily R htargetRoot hrootLeaf with ⟨C⟩
  rcases exists_rootExtraction_of_rootCleanLeafPackingFamily
      C hroot hdegree hDelta hband hunionCap hgroupSize hgroupSizeWidth
      hscale hgroupedWidth hcarrierWidth houtCarrier hlink with
    ⟨E⟩
  exact ⟨⟨C, E⟩⟩

/-- End-to-end Phase 1 assembly from restored Claim 5.15 paths: normalize at
the first root visit, carry out the specialized Corollary 2.12 extraction,
and concatenate the two leaf legs with every root linkage. -/
theorem exists_leafPairRoutingPackage_of_restored
    {m q cap alphaNum alphaDen Delta groupSize groupedWidth
      carrierWidth outWidth : Nat}
    {leafRouter : Fin m -> Finset V}
    {targetCarrier root : Finset V}
    (R : RestoredLeafPackingFamily G leafRouter targetCarrier q)
    (htargetRoot : targetCarrier ⊆ root)
    (hrootLeaf : forall i, Disjoint root (leafRouter i))
    (hroot : IsCluster G root)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (hband :
      ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
        G root cap alphaNum alphaDen)
    (hunionCap : m * q ≤ cap)
    (hgroupSize : 0 < groupSize)
    (hgroupSizeWidth : groupSize ≤ q)
    (hscale : alphaDen ≤ alphaNum * groupSize)
    (hgroupedWidth : groupedWidth ≤ q / (3 * groupSize))
    (hcarrierWidth :
      carrierWidth ≤ (3 * groupedWidth) / (10 * Delta * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    Nonempty
      (LeafPairRoutingPackage G leafRouter root q outWidth) := by
  rcases exists_rootCleanExtractionPackage_of_restored
      R htargetRoot hrootLeaf hroot hdegree hDelta hband hunionCap
      hgroupSize hgroupSizeWidth hscale hgroupedWidth hcarrierWidth
      houtCarrier hlink with
    ⟨P⟩
  exact ⟨⟨P.cleaned, P.extraction,
    P.cleaned.leafPairRouting P.extraction⟩⟩

open ChekuriChuzhoySection5Phase1Bundle
open ChekuriChuzhoySection5RouterSkeleton

/-- Complete Case-2 Phase 1 routing from the selected support tree.

The order of construction is essential: restore the Claim 5.15 paths, truncate
them at their first root-router visit, extract root endpoint blocks from those
new targets, and only then perform the all-pairs concatenation. -/
theorem exists_leafPairRoutingPackage_of_supportTree_leafFamily
    {n m : Nat} {router : Fin n -> Finset V}
    (S : RouterPathSkeleton G router)
    (T : _root_.SimpleGraph (Fin n))
    (hT : T.IsTree)
    {Delta width cap routerDen eta replicas q groupSize
      groupedWidth carrierWidth outWidth : Nat}
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (hn : 0 < n)
    (hgroups : S.GroupSizeAtMost n)
    (hbundle :
      ∀ p, p ∈ T.edgeSet ->
        n * (8 * Delta ^ 2 * width) ≤ (S.edgeBundleKey p).card)
    (leafRouter : Fin m -> Fin n)
    (hleafInjective : Function.Injective leafRouter)
    (hleaf : forall i, DegreeEquals T (leafRouter i) 1)
    (rootRouter : Fin n)
    (hrootLeaf : forall i, rootRouter ≠ leafRouter i)
    (hrouterDisjoint :
      forall {i j : Fin n}, i ≠ j -> Disjoint (router i) (router j))
    (hrouterCluster : forall i, IsCluster G (router i))
    (hband :
      forall i : Fin n,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (router i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      forall i,
        1 + (T.dist rootRouter (leafRouter i) - 1) *
            (routerDen + 1) ≤ eta)
    {c : Rat} (hc : 0 ≤ c)
    (hreplicasPos : 0 < replicas)
    (hreplicaValue : (replicas : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1)
    (hthin : Delta * q ≤ replicas)
    (hunionCap : m * q ≤ cap)
    (hgroupSize : 0 < groupSize)
    (hgroupSizeWidth : groupSize ≤ q)
    (hscale : routerDen ≤ groupSize)
    (hgroupedWidth : groupedWidth ≤ q / (3 * groupSize))
    (hcarrierWidth :
      carrierWidth ≤ (3 * groupedWidth) / (10 * Delta * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    Nonempty
      (LeafPairRoutingPackage G
        (fun i => router (leafRouter i)) (router rootRouter)
        q outWidth) := by
  rcases S.exists_supportBundleTransversal
      T hn hgroups hbundle with
    ⟨B⟩
  rcases
      exists_restoredLeafPackingFamily_of_supportTree_leafFamily_interfaceRoot
        S T hT hload hdegree (by omega) B leafRouter hleafInjective hleaf
        rootRouter hrootLeaf (fun {_ _} h => hrouterDisjoint h)
        hband hcap heta hc hreplicasPos hreplicaValue hcapacity hthin with
    ⟨R⟩
  exact
    exists_leafPairRoutingPackage_of_restored R
      (ChekuriChuzhoySection5Clustering.interfaceVertices_subset
        G (router rootRouter))
      (fun i => hrouterDisjoint (hrootLeaf i))
      (hrouterCluster rootRouter) hdegree hDelta (hband rootRouter)
      hunionCap hgroupSize hgroupSizeWidth (by simpa using hscale)
      hgroupedWidth hcarrierWidth houtCarrier hlink

open ChekuriChuzhoySection5Phase1Support

/-- Structural completion of Phase 1 after the terminal skeleton is available.

The connected heavy support supplies a spanning tree and the simultaneous
bundle lower bounds. The finite-tree dichotomy then returns either the Case-1
buffered support path or the complete Case-2 all-pairs routing package. -/
theorem exists_bufferedSupportPath_or_leafPairRoutingPackage
    {n m h : Nat} {router : Fin n -> Finset V}
    (S : RouterPathSkeleton G router)
    {Delta width cap routerDen eta replicas q groupSize
      groupedWidth carrierWidth outWidth : Nat}
    (hn : 0 < n)
    (hh : 0 < h)
    (hm : 1 < m)
    (hcard : m ^ 2 ≤ n)
    (hconnected : S.graph.IsEdgeConnected h)
    (hsupportWidth :
      n ^ 2 * (n * (8 * Delta ^ 2 * width)) ≤ h)
    (hload : S.EndpointCongestionAtMost 2)
    (hgroups : S.GroupSizeAtMost n)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (hrouterDisjoint :
      forall {i j : Fin n}, i ≠ j -> Disjoint (router i) (router j))
    (hrouterCluster : forall i, IsCluster G (router i))
    (hband :
      forall i : Fin n,
        ChekuriChuzhoySection5Clustering.TruncatedScaledBandwidth
          G (router i) cap 1 routerDen)
    (hcap : 2 * width ≤ cap)
    (heta :
      forall T : _root_.SimpleGraph (Fin n), T.IsTree ->
        forall root leaf : Fin n,
          1 + (T.dist root leaf - 1) * (routerDen + 1) ≤ eta)
    {c : Rat} (hc : 0 ≤ c)
    (hreplicasPos : 0 < replicas)
    (hreplicaValue : (replicas : Rat) ≤ c * width)
    (hcapacity :
      (m : Rat) * c * (1 + (Delta : Rat) * eta / 2) ≤ 1)
    (hthin : Delta * q ≤ replicas)
    (hunionCap : m * q ≤ cap)
    (hgroupSize : 0 < groupSize)
    (hgroupSizeWidth : groupSize ≤ q)
    (hscale : routerDen ≤ groupSize)
    (hgroupedWidth : groupedWidth ≤ q / (3 * groupSize))
    (hcarrierWidth :
      carrierWidth ≤ (3 * groupedWidth) / (10 * Delta * 2))
    (houtCarrier : outWidth ≤ carrierWidth)
    (hlink : 4 * Delta * outWidth ≤ carrierWidth) :
    (∃ T : _root_.SimpleGraph (Fin n),
        ∃ order : Fin (m + 2) -> Fin n,
          T ≤ phase1Support S.graph h ∧
            T.IsTree ∧
              Function.Injective order ∧
                forall r : Fin (m + 1),
                  T.Adj (order ⟨r.1, by omega⟩)
                    (order ⟨r.1 + 1, by omega⟩)) ∨
      ∃ T : _root_.SimpleGraph (Fin n),
        ∃ leafRouter : Fin m -> Fin n, ∃ rootRouter : Fin n,
          T ≤ phase1Support S.graph h ∧
            T.IsTree ∧
              Function.Injective leafRouter ∧
                (forall i, DegreeEquals T (leafRouter i) 1) ∧
                  (forall i, rootRouter ≠ leafRouter i) ∧
                    Nonempty
                      (LeafPairRoutingPackage G
                        (fun i => router (leafRouter i))
                        (router rootRouter) q outWidth) := by
  rcases exists_phase1Support_spanningTree_with_bundle_lower_bound
      S.graph hn hh hconnected hsupportWidth with
    ⟨T, hTsupport, hTtree, hTbundle⟩
  have hbundle :
      ∀ p, p ∈ T.edgeSet ->
        n * (8 * Delta ^ 2 * width) ≤ (S.edgeBundleKey p).card := by
    intro p hp
    induction p using Sym2.inductionOn with
    | _ i j =>
      have hij : T.Adj i j := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using hp
      simpa [S.edgeBundle_eq_edgeBundleKey i j] using
        hTbundle i j hij
  rcases exists_bufferedSupportPath_or_leafSelection
      T hTtree hm hcard with hpath | hselection
  · rcases hpath with ⟨order, horder, hadj⟩
    exact Or.inl ⟨T, order, hTsupport, hTtree, horder, hadj⟩
  · rcases hselection with ⟨L⟩
    refine Or.inr
      ⟨T, L.leafRouter, L.rootRouter, hTsupport, hTtree,
        L.leafRouter_injective, L.leafRouter_degree_one,
        L.rootRouter_ne_leaf, ?_⟩
    exact exists_leafPairRoutingPackage_of_supportTree_leafFamily
      S T hTtree hload hdegree hDelta hn hgroups
      hbundle L.leafRouter L.leafRouter_injective
      L.leafRouter_degree_one L.rootRouter L.rootRouter_ne_leaf
      hrouterDisjoint hrouterCluster hband hcap
      (fun i => heta T hTtree L.rootRouter (L.leafRouter i))
      hc hreplicasPos hreplicaValue hcapacity hthin hunionCap
      hgroupSize hgroupSizeWidth hscale hgroupedWidth hcarrierWidth
      houtCarrier hlink

end ChekuriChuzhoySection5Phase1Concatenation
end SimpleGraph

end Lax17Proofs
