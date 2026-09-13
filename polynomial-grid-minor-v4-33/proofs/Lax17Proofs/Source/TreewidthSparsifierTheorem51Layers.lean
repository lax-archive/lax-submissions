import Lax17Proofs.Source.CutMatchingGameDefs
import Lax17Proofs.Source.LocalSubgraph
import Lax17Proofs.Source.PathOfSets
import Lax17Proofs.Source.TreewidthSparsifierSection2
import Lax17Proofs.Source.TreewidthSparsifierTwoRoutingMinimal

namespace Lax17Proofs

universe u v w

/-!
# Degree-three treewidth sparsifier: one cut-matching layer

This file formalizes Step 1 of Theorem 5.1 of
Chekuri--Chuzhoy, *Degree-3 Treewidth Sparsifiers*, at one cluster of a
strong path-of-sets system.

For a current labelling of the left nails and a balanced abstract cut, the
left-nail well-linkedness supplies the blue routing and the left-to-right
linkedness supplies the red routing.  The already proved Theorem 1.3 replaces
the two routings by a pair whose union has at most `8 * h^4 + 8 * h` branch
vertices.  The blue endpoint bijections induce the matching-player response
across the abstract cut, while the red endpoint bijections transport the
labelling to the right nails.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h : ℕ}

/-- The image in ambient vertices of a finite set of labelled nails. -/
def labelledImage {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A})
    (S : Finset X) : Finset V :=
  S.map ⟨fun x => (label x).1, fun x y hxy => label.injective (Subtype.ext hxy)⟩

@[simp] theorem mem_labelledImage
    {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A})
    (S : Finset X) (v : V) :
    v ∈ labelledImage label S ↔
      ∃ x ∈ S, (label x).1 = v := by
  simp [labelledImage]

theorem labelledImage_subset
    {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A})
    (S : Finset X) :
    labelledImage label S ⊆ A := by
  intro v hv
  rcases (mem_labelledImage label S v).1 hv with ⟨x, _hx, rfl⟩
  exact (label x).2

theorem labelledImage_card
    {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A})
    (S : Finset X) :
    (labelledImage label S).card = S.card := by
  simp [labelledImage]

theorem labelledImage_disjoint
    {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A})
    {S T : Finset X} (hST : Disjoint S T) :
    Disjoint (labelledImage label S) (labelledImage label T) := by
  classical
  rw [Finset.disjoint_left] at hST ⊢
  intro v hvS hvT
  rcases (mem_labelledImage label S v).1 hvS with ⟨x, hxS, hxv⟩
  rcases (mem_labelledImage label T v).1 hvT with ⟨y, hyT, hyv⟩
  have hxy : x = y := by
    apply label.injective
    apply Subtype.ext
    exact hxv.trans hyv.symm
  exact hST hxS (hxy ▸ hyT)

theorem labelledImage_union
    {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A})
    (S T : Finset X) :
    labelledImage label (S ∪ T) =
      labelledImage label S ∪ labelledImage label T := by
  classical
  simp [labelledImage, Finset.map_union]

theorem labelledImage_univ
    {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A}) :
    labelledImage label Finset.univ = A := by
  classical
  ext v
  constructor
  · exact fun hv => labelledImage_subset label Finset.univ hv
  · intro hv
    let x : X := label.symm ⟨v, hv⟩
    apply (mem_labelledImage label Finset.univ v).2
    refine ⟨x, Finset.mem_univ x, ?_⟩
    exact congrArg Subtype.val (label.apply_symm_apply ⟨v, hv⟩)

/-- The subtype of the image of a labelled finite subset is canonically
equivalent to the corresponding subtype of labels. -/
noncomputable def labelledImageEquiv
    {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A})
    (S : Finset X) :
    {x : X // x ∈ S} ≃ {v : V // v ∈ labelledImage label S} where
  toFun x := ⟨(label x.1).1,
    (mem_labelledImage label S _).2 ⟨x.1, x.2, rfl⟩⟩
  invFun v := by
    let x : X := label.symm
      ⟨v.1, labelledImage_subset label S v.2⟩
    refine ⟨x, ?_⟩
    rcases (mem_labelledImage label S v.1).1 v.2 with
      ⟨y, hyS, hyv⟩
    have hxy : x = y := by
      apply label.injective
      apply Subtype.ext
      simpa [x] using hyv.symm
    simpa [hxy] using hyS
  left_inv x := by
    apply Subtype.ext
    exact label.symm_apply_apply x.1
  right_inv v := by
    apply Subtype.ext
    change
      (label (label.symm
        ⟨v.1, labelledImage_subset label S v.2⟩)).1 = v.1
    exact congrArg Subtype.val (label.apply_symm_apply
      ⟨v.1, labelledImage_subset label S v.2⟩)

/-- The two physical left-nail sides corresponding to an abstract
bisection. -/
def physicalLeft
    {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A})
    (B : Bisection X) : Finset V :=
  labelledImage label B.left

def physicalRight
    {X : Type v} [Fintype X] [DecidableEq X]
    {A : Finset V} (label : X ≃ {v : V // v ∈ A})
    (B : Bisection X) : Finset V :=
  labelledImage label B.right

/-- The complete proof data produced at one cluster in Step 1. -/
structure Layer
    (P : StrongPathOfSetsSystem G ell h)
    {X : Type v} [Fintype X] [DecidableEq X]
    (i : Fin ell)
    (label : X ≃ {v : V // v ∈ P.left i})
    (B : Bisection X) where
  /-- The same-vertex graph induced by the current cluster. -/
  localGraph : _root_.SimpleGraph V
  localGraph_le_induced :
    localGraph ≤ inducedOnFinset G (P.cluster i)
  /-- Red paths propagate all rows from left to right. -/
  red :
    PerfectPathPacking localGraph (P.left i) (P.right i)
  /-- Blue paths realize the matching-player answer. -/
  blue :
    PerfectPathPacking localGraph
      (physicalLeft label B) (physicalRight label B)
  /-- Minimality leaves no edge outside the selected red/blue support. -/
  support_eq :
    localGraph = twoPackingUnionGraph red blue
  /-- Theorem 1.3's branch-vertex bound. -/
  branch_bound :
    branchVertexCount (twoPackingUnionGraph red blue) ≤
      8 * h ^ 4 + 8 * h
  /-- Source Step 1 makes the simultaneous support edge-minimal. -/
  deleteEdge_failure :
    ∀ ⦃a b : V⦄, localGraph.Adj a b →
      ¬ (RoutableIn
          (localGraph.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (P.left i) (P.right i) ∧
        RoutableIn
          (localGraph.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (physicalLeft label B) (physicalRight label B))

namespace Layer

variable
    (P : StrongPathOfSetsSystem G ell h)
    {X : Type v} [Fintype X] [DecidableEq X]
    (i : Fin ell)
    (label : X ≃ {v : V // v ∈ P.left i})
    (B : Bisection X)

private theorem physical_cover :
    physicalLeft label B ∪ physicalRight label B = P.left i := by
  unfold physicalLeft physicalRight
  rw [← labelledImage_union, B.cover, labelledImage_univ]

private theorem physical_disjoint :
    Disjoint (physicalLeft label B) (physicalRight label B) :=
  labelledImage_disjoint label B.disjoint

private theorem physical_card_eq :
    (physicalLeft label B).card = (physicalRight label B).card := by
  simpa [physicalLeft, physicalRight, labelledImage_card] using B.card_eq

private theorem exists_red_local :
    Nonempty
      (PerfectPathPacking (inducedOnFinset G (P.cluster i))
        (P.left i) (P.right i)) := by
  rcases P.exists_left_right_perfect_linkage i with
    ⟨R, _hcard, hstay⟩
  exact ⟨R.inInducedOnFinset hstay⟩

private theorem exists_blue_local :
    Nonempty
      (PerfectPathPacking (inducedOnFinset G (P.cluster i))
        (physicalLeft label B) (physicalRight label B)) := by
  have hleft : physicalLeft label B ⊆ P.left i :=
    labelledImage_subset label B.left
  have hright : physicalRight label B ⊆ P.left i :=
    labelledImage_subset label B.right
  have hlinked :
      NodeLinkedIn G (P.cluster i)
        (physicalLeft label B) (physicalRight label B) :=
    (P.left_nodeWellLinked i).nodeLinkedIn_between_disjoint_subsets
      hleft hright (physical_disjoint P i label B)
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      hlinked
      (physical_card_eq P i label B) with
    ⟨Q, _hcard, hstay⟩
  exact ⟨Q.inInducedOnFinset hstay⟩

/-- Theorem 1.3 produces the red/blue pair required at every Step-1
cluster. -/
theorem exists_layer :
    Nonempty (Layer P i label B) := by
  classical
  let K := inducedOnFinset G (P.cluster i)
  have hred : RoutableIn K (P.left i) (P.right i) :=
    exists_red_local P i
  have hblue :
      RoutableIn K (physicalLeft label B) (physicalRight label B) :=
    exists_blue_local P i label B
  rcases theorem13_two_pair_routability_sparsifier
      (k₁ := h) (k₂ := B.left.card)
      K (P.left i) (P.right i)
      (physicalLeft label B) (physicalRight label B)
      (P.left_card i) (P.right_card i)
      (by simp [physicalLeft, labelledImage_card])
      (by
        rw [show (physicalRight label B).card = B.right.card by
          exact labelledImage_card label B.right]
        exact B.card_eq.symm)
      (by
        have hXcard : Fintype.card X = h := by
          calc
            Fintype.card X = Fintype.card {v : V // v ∈ P.left i} :=
              Fintype.card_congr label
            _ = (P.left i).card := Fintype.card_coe _
            _ = h := P.left_card i
        have hhalf := B.two_mul_left_card
        omega)
      hred hblue with
    ⟨R, Q, hbranch⟩
  let J := twoPackingUnionGraph R Q
  have hJred : RoutableIn J (P.left i) (P.right i) :=
    ⟨R.inSpanningGraph.mapLe le_sup_left⟩
  have hJblue :
      RoutableIn J (physicalLeft label B) (physicalRight label B) :=
    ⟨Q.inSpanningGraph.mapLe le_sup_right⟩
  let M : EdgeMinimalTwoRoutingSubgraph J
      (P.left i) (P.right i)
      (physicalLeft label B) (physicalRight label B) :=
    Classical.choice
      (EdgeMinimalTwoRoutingSubgraph.exists_of_routable hJred hJblue)
  exact ⟨{
    localGraph := M.graph
    localGraph_le_induced :=
      M.le_original.trans (twoPackingUnionGraph_le R Q)
    red := M.red
    blue := M.blue
    support_eq := M.graph_eq_twoPackingUnion
    branch_bound := by
      have hunion :
          branchVertexCount (twoPackingUnionGraph M.red M.blue) ≤
            branchVertexCount M.graph :=
        branchVertexCount_le_of_injective_adj
          (fun v : V => v) Function.injective_id
          (fun {_ _} huv => twoPackingUnionGraph_le M.red M.blue huv)
      exact hunion.trans (M.branchVertexCount_le.trans hbranch)
    deleteEdge_failure := M.deleteEdge_failure
  }⟩

variable {P i label B}

/-- The union of two node-disjoint path packings has maximum degree four. -/
theorem maxDegreeAtMost_four (L : Layer P i label B) :
    MaxDegreeAtMost L.localGraph 4 := by
  rw [L.support_eq]
  intro v
  exact DegreeAtMost.mono
    (degreeAtMost_sup
      (perfectPathPacking_spanningGraph_degreeAtMost_two L.red v)
      (perfectPathPacking_spanningGraph_degreeAtMost_two L.blue v))
    (by omega)

/-- The matching across the abstract cut induced by the selected blue
endpoint bijections. -/
noncomputable def matching (L : Layer P i label B) :
    MatchingAcross B where
  toEquiv :=
    (labelledImageEquiv label B.left).trans
      ((L.blue.sourceEquiv.symm.trans L.blue.targetEquiv).trans
        (labelledImageEquiv label B.right).symm)

/-- Transport the current labels through the selected red routing to the
right nails. -/
noncomputable def rightLabel (L : Layer P i label B) :
    X ≃ {v : V // v ∈ P.right i} :=
  label.trans (L.red.sourceEquiv.symm.trans L.red.targetEquiv)

/-- Transport labels through the selected red routing and then through the
path-of-sets connector to the next cluster. -/
noncomputable def nextLabel (L : Layer P i label B)
    (hi : i.1 + 1 < ell) :
    X ≃ {v : V // v ∈ P.left ⟨i.1 + 1, hi⟩} :=
  L.rightLabel.trans
    ((P.connector i hi).sourceEquiv.symm.trans
      (P.connector i hi).targetEquiv)

@[simp] theorem matching_rightEndpoint_val
    (L : Layer P i label B) (x : {x : X // x ∈ B.left}) :
    (L.matching.rightEndpoint x) =
      ((labelledImageEquiv label B.right).symm
        (L.blue.targetEquiv
          (L.blue.indexOfSource
            (labelledImageEquiv label B.left x)))).1 := by
  rfl

@[simp] theorem rightLabel_apply_val
    (L : Layer P i label B) (x : X) :
    (L.rightLabel x).1 =
      (L.red.path
        (L.red.indexOfSource (label x))).target := by
  rfl

@[simp] theorem nextLabel_apply_val
    (L : Layer P i label B) (hi : i.1 + 1 < ell) (x : X) :
    (L.nextLabel hi x).1 =
      ((P.connector i hi).path
        ((P.connector i hi).indexOfSource
          (L.rightLabel x))).target := by
  rfl

end Layer

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
