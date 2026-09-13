import Lax17Proofs.Source.Exponent8.Observation54Unique
import Lax17Proofs.Source.Exponent8.RecursiveSlicing

namespace Lax17Proofs

/-!
# Auxiliary deletion and retained-row restriction for Observation 5.4

This module formalizes the two hereditary steps after slice uniqueness in
Chuzhoy--Tan Observation 5.4:

1. deleting auxiliary edges preserves uniqueness when all canonical linkage
   paths remain and still span the smaller graph;
2. restricting to the support of a selected set of canonical rows preserves
   perfect unique linkage, by adjoining all discarded canonical rows to any
   alleged alternative retained linkage.

The cleaned type-two slice producer is built on these two graph-generic
lemmas.
-/

namespace SimpleGraph
namespace Exponent8

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Ksmall Klarge : _root_.SimpleGraph V}
variable {A B : Finset V}

/-- Uniqueness is downward monotone when the canonical paths remain in a
subgraph and still span its ambient vertex type.  This is the exact operation
used when unwanted auxiliary edges are deleted from a slice support. -/
theorem uniqueLinkage_preserved_by_auxiliary_deletion
    (hKL : Ksmall ≤ Klarge)
    (Rsmall : PerfectPathPacking Ksmall A B)
    (hspan : Rsmall.SpansVertices)
    (hunique : (Rsmall.mapLe hKL).IsUniqueLinkage) :
    Rsmall.IsUniqueLinkage := by
  refine ⟨hspan, ?_⟩
  intro Lsmall
  have h :=
    hunique.2 (Lsmall.mapLe hKL)
  simpa using h

/-- The edge trace of `disjointUnion` is exactly the union of the two input
traces. -/
theorem disjointUnion_edgeSet_eq_union_local
    {S₁ T₁ S₂ T₂ : Finset V}
    (P₁ : PerfectPathPacking Ksmall S₁ T₁)
    (P₂ : PerfectPathPacking Ksmall S₂ T₂)
    (hS : Disjoint S₁ S₂) (hT : Disjoint T₁ T₂)
    (hnode : P₁.toPathPacking.MutuallyNodeDisjoint P₂.toPathPacking) :
    (P₁.disjointUnion P₂ hS hT hnode).toPathPacking.edgeSet =
      P₁.toPathPacking.edgeSet ∪ P₂.toPathPacking.edgeSet := by
  classical
  apply Finset.Subset.antisymm
  · exact PerfectPathPacking.disjointUnion_edgeSet_subset_union
      P₁ P₂ hS hT hnode
  · intro e he
    rcases Finset.mem_union.mp he with he₁ | he₂
    · rcases P₁.toPathPacking.mem_edgeSet.1 he₁ with ⟨p, hep⟩
      apply
        (P₁.disjointUnion P₂ hS hT hnode).toPathPacking.mem_edgeSet.2
      exact ⟨Sum.inl p, by
        simpa [PerfectPathPacking.disjointUnion] using hep⟩
    · rcases P₂.toPathPacking.mem_edgeSet.1 he₂ with ⟨p, hep⟩
      apply
        (P₁.disjointUnion P₂ hS hT hnode).toPathPacking.mem_edgeSet.2
      exact ⟨Sum.inr p, by
        simpa [PerfectPathPacking.disjointUnion] using hep⟩

/-- Splitting the index set into selected and discarded paths splits the edge
trace exactly. -/
theorem restrictIndexSet_union_compl_edgeSet
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) :
    P.toPathPacking.edgeSet =
      (P.restrictIndexSet I).toPathPacking.edgeSet ∪
        (P.restrictIndexSet
          ((Finset.univ : Finset P.Index) \ I)).toPathPacking.edgeSet := by
  classical
  ext e
  constructor
  · intro he
    rcases P.toPathPacking.mem_edgeSet.1 he with ⟨p, hep⟩
    by_cases hp : p ∈ I
    · apply Finset.mem_union_left
      exact (P.restrictIndexSet I).toPathPacking.mem_edgeSet.2
        ⟨⟨p, hp⟩, hep⟩
    · apply Finset.mem_union_right
      exact
        (P.restrictIndexSet
          ((Finset.univ : Finset P.Index) \ I)).toPathPacking.mem_edgeSet.2
          ⟨⟨p, by simp [hp]⟩, hep⟩
  · intro he
    rcases Finset.mem_union.mp he with heI | heD
    · rcases
        (P.restrictIndexSet I).toPathPacking.mem_edgeSet.1 heI with
        ⟨p, hep⟩
      exact P.toPathPacking.mem_edgeSet.2 ⟨p.1, hep⟩
    · rcases
        (P.restrictIndexSet
          ((Finset.univ : Finset P.Index) \ I)).toPathPacking
            |>.mem_edgeSet.1 heD with
        ⟨p, hep⟩
      exact P.toPathPacking.mem_edgeSet.2 ⟨p.1, hep⟩

/-- If a packing's full vertex support is disjoint from `U`, none of its
edges survives the two-endpoint filter. -/
theorem edgesInside_edgeSet_eq_empty_of_disjoint
    (P : PathPacking Ksmall A B) (U : Finset V)
    (hdisj : Disjoint P.vertexSet U) :
    PathSlicing.edgesInside U P.edgeSet = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro e he
  rcases PathSlicing.mem_edgesInside.1 he with ⟨heP, heU⟩
  rcases P.mem_edgeSet.1 heP with ⟨p, hep⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxP :
          x ∈ P.vertexSet :=
        P.path_vertexSet_subset_vertexSet p
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (P.path p) hep).1
      have hxU : x ∈ U :=
        heU (by simp [Sym2.toFinset_mk_eq])
      exact Finset.disjoint_left.mp hdisj hxP hxU

/-- Exact ambient support of a selected subfamily of canonical rows. -/
noncomputable def selectedRowVertexSet
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) : Finset V :=
  (P.restrictIndexSet I).toPathPacking.vertexSet

theorem selectedRow_sourceSet_subset
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) :
    P.sourceSet I ⊆ selectedRowVertexSet P I := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
  exact
    (P.restrictIndexSet I).toPathPacking
      |>.path_vertexSet_subset_vertexSet ⟨p, hp⟩
        (GraphPath.source_mem_vertexSet _)

theorem selectedRow_targetSet_subset
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) :
    P.targetSet I ⊆ selectedRowVertexSet P I := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
  exact
    (P.restrictIndexSet I).toPathPacking
      |>.path_vertexSet_subset_vertexSet ⟨p, hp⟩
        (GraphPath.target_mem_vertexSet _)

/-- The selected canonical rows on the subtype consisting exactly of their
vertices. -/
noncomputable def selectedRowsInSupport
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) :
    PerfectPathPacking
      (Ksmall.induce {v : V | v ∈ selectedRowVertexSet P I})
      (PathPacking.subtypeFinset
        (P.sourceSet I) (selectedRowVertexSet P I)
        (selectedRow_sourceSet_subset P I))
      (PathPacking.subtypeFinset
        (P.targetSet I) (selectedRowVertexSet P I)
        (selectedRow_targetSet_subset P I)) :=
  (P.restrictIndexSet I).induce
    (selectedRowVertexSet P I)
    (by
      intro p
      exact (P.restrictIndexSet I).toPathPacking
        |>.path_vertexSet_subset_vertexSet p)
    (selectedRow_sourceSet_subset P I)
    (selectedRow_targetSet_subset P I)

theorem selectedRowsInSupport_spansVertices
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) :
    (selectedRowsInSupport P I).SpansVertices := by
  intro z
  rcases
      (P.restrictIndexSet I).toPathPacking.mem_vertexSet.1 z.2 with
    ⟨p, hzp⟩
  apply (selectedRowsInSupport P I).toPathPacking.mem_vertexSet.2
  refine ⟨p, ?_⟩
  exact
    (GraphPath.mem_induce_vertexSet
      ((P.restrictIndexSet I).path p)
      (selectedRowVertexSet P I)
      ((P.restrictIndexSet I).toPathPacking
        |>.path_vertexSet_subset_vertexSet p) z).2 hzp

theorem selected_discarded_index_disjoint
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) :
    Disjoint I ((Finset.univ : Finset P.Index) \ I) := by
  rw [Finset.disjoint_left]
  intro p hpI hpD
  exact (Finset.mem_sdiff.mp hpD).2 hpI

theorem discardedRows_vertexSet_disjoint_selected
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) :
    Disjoint
      (P.restrictIndexSet
        ((Finset.univ : Finset P.Index) \ I)).toPathPacking.vertexSet
      (selectedRowVertexSet P I) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvDiscard hvSelected
  rcases
      (P.restrictIndexSet
        ((Finset.univ : Finset P.Index) \ I)).toPathPacking
          |>.mem_vertexSet.1 hvDiscard with
    ⟨d, hvd⟩
  rcases
      (P.restrictIndexSet I).toPathPacking.mem_vertexSet.1 hvSelected with
    ⟨r, hvr⟩
  have hrd : r.1 ≠ d.1 := by
    intro h
    have hdI : d.1 ∈ I := by simpa [h] using r.2
    exact (Finset.mem_sdiff.mp d.2).2 hdI
  exact Finset.disjoint_left.mp
    (P.toPathPacking.node_disjoint hrd) hvr hvd

theorem sourceSet_union_compl_eq_left
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) :
    P.sourceSet I ∪
      P.sourceSet ((Finset.univ : Finset P.Index) \ I) = A := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hvI | hvD
    · exact P.sourceSet_subset_left I hvI
    · exact P.sourceSet_subset_left
        ((Finset.univ : Finset P.Index) \ I) hvD
  · intro hv
    rcases P.source_bijective.2 ⟨v, hv⟩ with ⟨p, hp⟩
    have hsource : (P.path p).source = v :=
      congrArg Subtype.val hp
    by_cases hpI : p ∈ I
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨p, hpI, hsource⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨p, by simp [hpI], hsource⟩

theorem targetSet_union_compl_eq_right
    (P : PerfectPathPacking Ksmall A B)
    (I : Finset P.Index) :
    P.targetSet I ∪
      P.targetSet ((Finset.univ : Finset P.Index) \ I) = B := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hvI | hvD
    · exact P.targetSet_subset_right I hvI
    · exact P.targetSet_subset_right
        ((Finset.univ : Finset P.Index) \ I) hvD
  · intro hv
    rcases P.target_bijective.2 ⟨v, hv⟩ with ⟨p, hp⟩
    have htarget : (P.path p).target = v :=
      congrArg Subtype.val hp
    by_cases hpI : p ∈ I
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨p, hpI, htarget⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨p, by simp [hpI], htarget⟩

/-- A perfect unique linkage restricted to any chosen set of its rows remains
a perfect unique linkage on the exact subtype support of those rows.

The proof is the add-back argument required by Observation 5.4: lift an
arbitrary alternative retained linkage, adjoin every discarded canonical row,
apply global uniqueness, and filter the resulting edge equality back to the
selected support. -/
theorem restrict_separated_rows_isUniqueLinkage
    (P : PerfectPathPacking Ksmall A B)
    (hunique : P.IsUniqueLinkage)
    (I : Finset P.Index) :
    (selectedRowsInSupport P I).IsUniqueLinkage := by
  classical
  refine ⟨selectedRowsInSupport_spansVertices P I, ?_⟩
  intro L
  let U : Finset V := selectedRowVertexSet P I
  let RI := P.restrictIndexSet I
  let D :=
    P.restrictIndexSet ((Finset.univ : Finset P.Index) \ I)
  let Lambient : PerfectPathPacking Ksmall (P.sourceSet I) (P.targetSet I) :=
    SimpleGraph.Exponent8.liftInducedPerfect
      (selectedRow_sourceSet_subset P I)
      (selectedRow_targetSet_subset P I) L
  have hLstay : Lambient.toPathPacking.StaysIn U := by
    intro p
    change
      (SimpleGraph.Exponent8.liftInducedPath (L.path p)).vertexSet ⊆ U
    exact SimpleGraph.Exponent8.liftInducedPath_vertexSet_subset (L.path p)
  have hDdisj : Disjoint D.toPathPacking.vertexSet U := by
    simpa [D, U] using discardedRows_vertexSet_disjoint_selected P I
  have hnode :
      Lambient.toPathPacking.MutuallyNodeDisjoint D.toPathPacking := by
    intro p d
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hvL hvD
    have hvU : v ∈ U := hLstay p hvL
    have hvDtotal : v ∈ D.toPathPacking.vertexSet :=
      D.toPathPacking.path_vertexSet_subset_vertexSet d hvD
    exact Finset.disjoint_left.mp hDdisj hvDtotal hvU
  have hIndexDisjoint :
      Disjoint I ((Finset.univ : Finset P.Index) \ I) :=
    selected_discarded_index_disjoint P I
  have hSourceDisjoint :
      Disjoint (P.sourceSet I)
        (P.sourceSet ((Finset.univ : Finset P.Index) \ I)) :=
    P.sourceSet_disjoint hIndexDisjoint
  have hTargetDisjoint :
      Disjoint (P.targetSet I)
        (P.targetSet ((Finset.univ : Finset P.Index) \ I)) :=
    P.targetSet_disjoint hIndexDisjoint
  let Lunion :=
    Lambient.disjointUnion D
      hSourceDisjoint hTargetDisjoint hnode
  let Lfull : PerfectPathPacking Ksmall A B :=
    Lunion.copyTerminals
      (sourceSet_union_compl_eq_left P I)
      (targetSet_union_compl_eq_right P I)
  have hFull :
      Lfull.toPathPacking.edgeSet = P.toPathPacking.edgeSet :=
    hunique.2 Lfull
  have hEdgeEq :
      Lambient.toPathPacking.edgeSet ∪ D.toPathPacking.edgeSet =
        RI.toPathPacking.edgeSet ∪ D.toPathPacking.edgeSet := by
    calc
      Lambient.toPathPacking.edgeSet ∪ D.toPathPacking.edgeSet =
          Lunion.toPathPacking.edgeSet := by
        symm
        exact disjointUnion_edgeSet_eq_union_local
          Lambient D hSourceDisjoint hTargetDisjoint hnode
      _ = Lfull.toPathPacking.edgeSet := by
        simp [Lfull]
      _ = P.toPathPacking.edgeSet := hFull
      _ = RI.toPathPacking.edgeSet ∪ D.toPathPacking.edgeSet := by
        simpa [RI, D] using restrictIndexSet_union_compl_edgeSet P I
  have hFiltered :=
    congrArg (PathSlicing.edgesInside U) hEdgeEq
  have hRIstay : RI.toPathPacking.StaysIn U := by
    intro r
    exact RI.toPathPacking.path_vertexSet_subset_vertexSet r
  have hDempty :
      PathSlicing.edgesInside U D.toPathPacking.edgeSet = ∅ :=
    edgesInside_edgeSet_eq_empty_of_disjoint D.toPathPacking U hDdisj
  have hAmbient :
      Lambient.toPathPacking.edgeSet = RI.toPathPacking.edgeSet := by
    simpa [PathSlicing.edgesInside_union,
      PathSlicing.edgesInside_edgeSet_eq_of_staysIn
        Lambient.toPathPacking U hLstay,
      PathSlicing.edgesInside_edgeSet_eq_of_staysIn
        RI.toPathPacking U hRIstay,
      hDempty] using hFiltered
  apply PathSlicing.ambientEdgeImage_injective U
  calc
    PathSlicing.ambientEdgeImage U L.toPathPacking.edgeSet =
        Lambient.toPathPacking.edgeSet := by
      symm
      exact PathSlicing.liftInducedPerfect_edgeSet_eq_ambientEdgeImage
        (selectedRow_sourceSet_subset P I)
        (selectedRow_targetSet_subset P I) L
    _ = RI.toPathPacking.edgeSet := hAmbient
    _ = PathSlicing.ambientEdgeImage U
        (selectedRowsInSupport P I).toPathPacking.edgeSet := by
      symm
      exact PathSlicing.ambientEdgeImage_induce_edgeSet_eq
        RI
        (by
          intro r
          exact RI.toPathPacking.path_vertexSet_subset_vertexSet r)
        (selectedRow_sourceSet_subset P I)
        (selectedRow_targetSet_subset P I)

/-- Induce a packing onto a vertex support while retagging both terminal sets
as `univ`.  Recursive slicing only needs the path family and its intersections,
so retaining unused ambient terminal labels would create irrelevant subtype
obligations. -/
noncomputable def PathPacking.induceUniv
    {S T : Finset V} (P : PathPacking Ksmall S T)
    (U : Finset V) (hP : P.StaysIn U) :
    PathPacking (Ksmall.induce {v : V | v ∈ U})
      Finset.univ Finset.univ where
  Index := P.Index
  path := fun p => (P.path p).induce U (hP p)
  connects := by
    intro p
    exact Or.inl ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  node_disjoint := by
    intro p q hpq
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro z hzp hzq
    have hzp' :
        z.1 ∈ (P.path p).vertexSet :=
      (GraphPath.mem_induce_vertexSet
        (P.path p) U (hP p) z).1 hzp
    have hzq' :
        z.1 ∈ (P.path q).vertexSet :=
      (GraphPath.mem_induce_vertexSet
        (P.path q) U (hP q) z).1 hzq
    exact Finset.disjoint_left.mp (P.node_disjoint hpq) hzp' hzq'

@[simp] theorem PathPacking.induceUniv_card
    {S T : Finset V} (P : PathPacking Ksmall S T)
    (U : Finset V) (hP : P.StaysIn U) :
    (PathPacking.induceUniv P U hP).card = P.card := rfl

@[simp] theorem PathPacking.induceUniv_path_vertexSet
    {S T : Finset V} (P : PathPacking Ksmall S T)
    (U : Finset V) (hP : P.StaysIn U)
    (p : (PathPacking.induceUniv P U hP).Index)
    (z : {v : V // v ∈ U}) :
    z ∈ ((PathPacking.induceUniv P U hP).path p).vertexSet ↔
      z.1 ∈ (P.path p).vertexSet :=
  GraphPath.mem_induce_vertexSet (P.path p) U (hP p) z

end Exponent8
end SimpleGraph

end Lax17Proofs
