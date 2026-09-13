import Lax17Proofs.Source.TreewidthSparsifierContract

namespace Lax17Proofs

universe u v w

/-!
# Degree-four to degree-three blue-edge thinning

In Step 1 of Theorem 5.1 every degree-four vertex is incident with exactly two
blue-only edges.  The paper chooses one of those two edges at every such
vertex and deletes every chosen edge.  Independently of the later probability
argument, every outcome has maximum degree three.  This file formalizes that
deterministic part of the construction.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51


variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Vertices at which a degree-four support must lose one blue edge. -/
noncomputable def degreeFourVertices
    (H : _root_.SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ¬ DegreeAtMost H v 3

/-- A formulation independent of a chosen orientation of `Sym2`: an edge is
incident when one of its endpoints is the named vertex. -/
def EdgeIncident
    (H : _root_.SimpleGraph V) (v : V) (e : H.edgeSet) : Prop :=
  ∃ u : V, H.Adj v u ∧ (e.1 : Sym2 V) = s(v, u)

/-- Regard the edges of a spanning subgraph as named edges of its
supergraph. -/
noncomputable def edgesOfSubgraph
    (H K : _root_.SimpleGraph V) (hKH : K ≤ H) :
    Finset H.edgeSet := by
  classical
  exact Finset.univ.filter fun e => (e.1 : Sym2 V) ∈ K.edgeSet

@[simp] theorem mem_edgesOfSubgraph
    (H K : _root_.SimpleGraph V) (hKH : K ≤ H) (e : H.edgeSet) :
    e ∈ edgesOfSubgraph H K hKH ↔ (e.1 : Sym2 V) ∈ K.edgeSet := by
  classical
  simp [edgesOfSubgraph]

/-- Blue-only edges incident with a named vertex. -/
noncomputable def blueAt
    (H : _root_.SimpleGraph V) (blue : Finset H.edgeSet) (v : V) :
    Finset H.edgeSet := by
  classical
  exact blue.filter fun e => EdgeIncident H v e

/-- Incidences of a spanning subgraph are counted by the corresponding
named-edge choices in the supergraph. -/
theorem blueAt_edgesOfSubgraph_card
    (H K : _root_.SimpleGraph V) [DecidableRel K.Adj]
    (hKH : K ≤ H) (v : V) :
    (blueAt H (edgesOfSubgraph H K hKH) v).card = K.degree v := by
  classical
  let toIncidence :
      {e : H.edgeSet //
        e ∈ blueAt H (edgesOfSubgraph H K hKH) v} →
        K.incidenceSet v :=
    fun e => by
      have hmem := Finset.mem_filter.mp e.2
      refine ⟨e.1.1, ?_⟩
      refine ⟨(mem_edgesOfSubgraph H K hKH e.1).mp hmem.1, ?_⟩
      rcases hmem.2 with ⟨u, _hvu, he⟩
      rw [he]
      simp
  let fromIncidence :
      K.incidenceSet v →
        {e : H.edgeSet //
          e ∈ blueAt H (edgesOfSubgraph H K hKH) v} :=
    fun e => by
      have heK : (e.1 : Sym2 V) ∈ K.edgeSet := e.2.1
      have heH : (e.1 : Sym2 V) ∈ H.edgeSet :=
        _root_.SimpleGraph.edgeSet_mono hKH heK
      let named : H.edgeSet := ⟨e.1, heH⟩
      refine ⟨named, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact (mem_edgesOfSubgraph H K hKH named).mpr heK
      · let u := K.otherVertexOfIncident e.2
        refine ⟨u, hKH ?_, ?_⟩
        · exact K.incidence_other_prop e.2
        · exact (Sym2.other_spec' e.2.2).symm
  let equiv :
      {e : H.edgeSet //
        e ∈ blueAt H (edgesOfSubgraph H K hKH) v} ≃
        K.incidenceSet v := {
    toFun := toIncidence
    invFun := fromIncidence
    left_inv := by
      intro e
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro e
      apply Subtype.ext
      rfl
  }
  calc
    (blueAt H (edgesOfSubgraph H K hKH) v).card =
        Fintype.card
          {e : H.edgeSet //
            e ∈ blueAt H (edgesOfSubgraph H K hKH) v} := by
      rw [← Fintype.card_coe]
    _ = Fintype.card (K.incidenceSet v) :=
      Fintype.card_congr equiv
    _ = K.degree v := K.card_incidenceSet_eq_degree v

/-- The exact source invariant needed by the thinning operation. -/
structure BlueThinningInput
    (H : _root_.SimpleGraph V) where
  blue : Finset H.edgeSet
  max_degree_four : MaxDegreeAtMost H 4
  two_blue_at_degree_four :
    ∀ v ∈ degreeFourVertices H,
      (blueAt H blue v).card = 2

private theorem degree_le_of_degreeAtMost
    {H : _root_.SimpleGraph V} [DecidableRel H.Adj]
    {v : V} {d : ℕ} (hd : DegreeAtMost H v d) :
    H.degree v ≤ d := by
  rcases hd with ⟨N, hN, hcard⟩
  have hN : N = H.neighborFinset v := by
    ext u
    exact (hN u).trans (H.mem_neighborFinset v u).symm
  simpa [hN] using hcard

/-- The red/blue union invariant from source Step 1 supplies the deterministic
thinning input.  At a degree-four vertex, each degree-two support must
contribute two distinct incidences, so there are exactly two blue choices. -/
noncomputable def BlueThinningInput.ofTwoDegreeTwoSupports
    (H redGraph blueGraph : _root_.SimpleGraph V)
    (hsupport : H = redGraph ⊔ blueGraph)
    (hred : MaxDegreeAtMost redGraph 2)
    (hblue : MaxDegreeAtMost blueGraph 2) :
    BlueThinningInput H := by
  classical
  letI : DecidableRel redGraph.Adj := Classical.decRel _
  letI : DecidableRel blueGraph.Adj := Classical.decRel _
  have hblue_le : blueGraph ≤ H := by
    rw [hsupport]
    exact le_sup_right
  refine {
    blue := edgesOfSubgraph H blueGraph hblue_le
    max_degree_four := ?_
    two_blue_at_degree_four := ?_
  }
  · rw [hsupport]
    intro v
    exact DegreeAtMost.mono
      (degreeAtMost_sup (hred v) (hblue v)) (by omega)
  · intro v hv
    have hnot3 : ¬DegreeAtMost H v 3 := by
      simpa [degreeFourVertices] using hv
    have hblueDegree : blueGraph.degree v = 2 := by
      have hle :
          blueGraph.degree v ≤ 2 :=
        degree_le_of_degreeAtMost (hblue v)
      by_contra hne
      have hle1 : blueGraph.degree v ≤ 1 := by omega
      have hblue1 : DegreeAtMost blueGraph v 1 := by
        refine ⟨blueGraph.neighborFinset v, ?_, hle1⟩
        intro u
        simp
      apply hnot3
      rw [hsupport]
      exact DegreeAtMost.mono
        (degreeAtMost_sup (hred v) hblue1) (by omega)
    rw [blueAt_edgesOfSubgraph_card H blueGraph hblue_le v,
      hblueDegree]

namespace BlueThinningInput

variable {H : _root_.SimpleGraph V} (I : BlueThinningInput H)

/-- The two available blue choices at a bad vertex. -/
noncomputable def choices (v : {v : V // v ∈ degreeFourVertices H}) :
    Finset H.edgeSet :=
  blueAt H I.blue v.1

@[simp] theorem choices_card
    (v : {v : V // v ∈ degreeFourVertices H}) :
    (I.choices v).card = 2 :=
  I.two_blue_at_degree_four v.1 v.2

/-- Canonical enumeration of the two choices. -/
noncomputable def choiceEquiv
    (v : {v : V // v ∈ degreeFourVertices H}) :
    Fin 2 ≃ {e : H.edgeSet // e ∈ I.choices v} :=
  (Equiv.cast (congrArg Fin (I.choices_card v).symm)).trans
    (I.choices v).equivFin.symm

/-- An outcome independently chooses one of the two blue edges at every
degree-four vertex. -/
abbrev Outcome :=
  {v : V // v ∈ degreeFourVertices H} → Fin 2

/-- The named edge selected at one degree-four vertex. -/
noncomputable def selectedEdge
    (outcome : Outcome (H := H))
    (v : {v : V // v ∈ degreeFourVertices H}) : H.edgeSet :=
  (I.choiceEquiv v (outcome v)).1

theorem selectedEdge_mem_choices
    (outcome : Outcome (H := H))
    (v : {v : V // v ∈ degreeFourVertices H}) :
    I.selectedEdge outcome v ∈ I.choices v :=
  (I.choiceEquiv v (outcome v)).2

theorem selectedEdge_blue
    (outcome : Outcome (H := H))
    (v : {v : V // v ∈ degreeFourVertices H}) :
    I.selectedEdge outcome v ∈ I.blue := by
  classical
  exact (Finset.mem_filter.mp (I.selectedEdge_mem_choices outcome v)).1

theorem selectedEdge_incident
    (outcome : Outcome (H := H))
    (v : {v : V // v ∈ degreeFourVertices H}) :
    EdgeIncident H v.1 (I.selectedEdge outcome v) := by
  classical
  exact (Finset.mem_filter.mp (I.selectedEdge_mem_choices outcome v)).2

/-- The set of underlying host edges selected by at least one endpoint. -/
noncomputable def deletedEdges
    (outcome : Outcome (H := H)) : Set (Sym2 V) :=
  {e | ∃ v : {v : V // v ∈ degreeFourVertices H},
    e = (I.selectedEdge outcome v).1}

/-- The degree-three candidate for a fixed outcome. -/
noncomputable def thinnedGraph (outcome : Outcome (H := H)) :
    _root_.SimpleGraph V :=
  H.deleteEdges (I.deletedEdges outcome)

theorem thinnedGraph_le (outcome : Outcome (H := H)) :
    I.thinnedGraph outcome ≤ H :=
  _root_.SimpleGraph.deleteEdges_le _

private theorem exists_other_endpoint
    (outcome : Outcome (H := H))
    (v : {v : V // v ∈ degreeFourVertices H}) :
    ∃ u : V,
      H.Adj v.1 u ∧
        s(v.1, u) = (I.selectedEdge outcome v).1 := by
  rcases I.selectedEdge_incident outcome v with ⟨u, hvu, he⟩
  exact ⟨u, hvu, he.symm⟩

/-- Every deletion outcome has maximum degree at most three. -/
theorem thinnedGraph_maxDegreeAtMost
    (outcome : Outcome (H := H)) :
    MaxDegreeAtMost (I.thinnedGraph outcome) 3 := by
  classical
  intro v
  by_cases hv : v ∈ degreeFourVertices H
  · let bad : {v : V // v ∈ degreeFourVertices H} := ⟨v, hv⟩
    rcases I.exists_other_endpoint outcome bad with
      ⟨u, hvu, hedge⟩
    let oldN := MaxDegreeAtMost.neighborFinset I.max_degree_four v
    let N : Finset V :=
      (oldN.erase u).filter fun z => (I.thinnedGraph outcome).Adj v z
    refine ⟨N, ?_, ?_⟩
    · intro z
      constructor
      · exact fun hz => (Finset.mem_filter.mp hz).2
      · intro hvz
        have hvzH : H.Adj v z := I.thinnedGraph_le outcome hvz
        have hzold : z ∈ oldN :=
          (MaxDegreeAtMost.mem_neighborFinset
            I.max_degree_four v z).2 hvzH
        have hzu : z ≠ u := by
          intro hzu
          subst z
          have hdeleted :
              s(v, u) ∈ I.deletedEdges outcome := by
            exact ⟨bad, hedge⟩
          have hnot :=
            (_root_.SimpleGraph.deleteEdges_adj
              (G := H) (s := I.deletedEdges outcome)
              (v := v) (w := u)).1 hvz
          exact hnot.2 hdeleted
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hzu, hzold⟩, hvz⟩
    · have huold : u ∈ oldN :=
        (MaxDegreeAtMost.mem_neighborFinset
          I.max_degree_four v u).2 hvu
      have holdcard : oldN.card ≤ 4 :=
        MaxDegreeAtMost.card_neighborFinset_le I.max_degree_four v
      calc
        N.card ≤ (oldN.erase u).card := Finset.card_filter_le _ _
        _ = oldN.card - 1 := Finset.card_erase_of_mem huold
        _ ≤ 3 := by omega
  · have hv3 : DegreeAtMost H v 3 := by
      simpa [degreeFourVertices] using hv
    rcases hv3 with ⟨oldN, holdN, hcard⟩
    let N : Finset V :=
      oldN.filter fun z => (I.thinnedGraph outcome).Adj v z
    refine ⟨N, ?_, (Finset.card_filter_le _ _).trans hcard⟩
    intro z
    constructor
    · exact fun hz => (Finset.mem_filter.mp hz).2
    · intro hvz
      exact Finset.mem_filter.mpr
        ⟨(holdN z).2 (I.thinnedGraph_le outcome hvz), hvz⟩

/-- If two degree-two supports share an incidence at `v`, then their union
has degree at most three at `v`.  This is the elementary observation which
ensures that the random deletion at a degree-four vertex never selects a red
edge. -/
private theorem degreeAtMost_three_of_common_incidence
    (redGraph blueGraph : _root_.SimpleGraph V)
    (hred : MaxDegreeAtMost redGraph 2)
    (hblue : MaxDegreeAtMost blueGraph 2)
    {v u : V} (hru : redGraph.Adj v u)
    (hbu : blueGraph.Adj v u) :
    DegreeAtMost (redGraph ⊔ blueGraph) v 3 := by
  classical
  let R := MaxDegreeAtMost.neighborFinset hred v
  let B := MaxDegreeAtMost.neighborFinset hblue v
  refine ⟨R ∪ B, ?_, ?_⟩
  · intro w
    simp only [Finset.mem_union]
    rw [MaxDegreeAtMost.mem_neighborFinset,
      MaxDegreeAtMost.mem_neighborFinset]
    rfl
  · have hu : u ∈ R ∩ B := by
      simp only [Finset.mem_inter]
      exact
        ⟨(MaxDegreeAtMost.mem_neighborFinset hred v u).2 hru,
          (MaxDegreeAtMost.mem_neighborFinset hblue v u).2 hbu⟩
    have hinter : 1 ≤ (R ∩ B).card :=
      Finset.one_le_card.mpr ⟨u, hu⟩
    have hR : R.card ≤ 2 :=
      MaxDegreeAtMost.card_neighborFinset_le hred v
    have hB : B.card ≤ 2 :=
      MaxDegreeAtMost.card_neighborFinset_le hblue v
    have hcard := Finset.card_union_add_card_inter R B
    omega

/-- In the source red/blue construction, thinning deletes only blue-only
edges.  Hence the complete red support survives every outcome. -/
theorem ofTwoDegreeTwoSupports_red_le_thinnedGraph
    (redGraph blueGraph : _root_.SimpleGraph V)
    (hred : MaxDegreeAtMost redGraph 2)
    (hblue : MaxDegreeAtMost blueGraph 2)
    (outcome :
      Outcome
        (H := redGraph ⊔ blueGraph)) :
    redGraph ≤
      (BlueThinningInput.ofTwoDegreeTwoSupports
        (redGraph ⊔ blueGraph) redGraph blueGraph rfl hred hblue).thinnedGraph
        outcome := by
  classical
  let I :=
    BlueThinningInput.ofTwoDegreeTwoSupports
      (redGraph ⊔ blueGraph) redGraph blueGraph rfl hred hblue
  intro v w hvw
  rw [thinnedGraph, _root_.SimpleGraph.deleteEdges_adj]
  refine ⟨Or.inl hvw, ?_⟩
  intro hdeleted
  rcases hdeleted with ⟨z, hselected⟩
  have hblueEdge : (I.selectedEdge outcome z).1 ∈ blueGraph.edgeSet := by
    have hmem := I.selectedEdge_blue outcome z
    change
      I.selectedEdge outcome z ∈
        edgesOfSubgraph (redGraph ⊔ blueGraph) blueGraph le_sup_right at hmem
    rw [mem_edgesOfSubgraph] at hmem
    exact hmem
  rcases I.selectedEdge_incident outcome z with
    ⟨u, hzu, hedge⟩
  have hbluezu : blueGraph.Adj z.1 u := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    rw [← hedge]
    exact hblueEdge
  have hredEdge : (I.selectedEdge outcome z).1 ∈ redGraph.edgeSet := by
    rw [← hselected]
    rw [_root_.SimpleGraph.mem_edgeSet]
    exact hvw
  have hredzu : redGraph.Adj z.1 u := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    rw [← hedge]
    exact hredEdge
  have hdegree :
      DegreeAtMost (redGraph ⊔ blueGraph) z.1 3 :=
    degreeAtMost_three_of_common_incidence
      redGraph blueGraph hred hblue hredzu hbluezu
  have hz := z.2
  change
    z.1 ∈ Finset.univ.filter
      (fun x => ¬ DegreeAtMost (redGraph ⊔ blueGraph) x 3) at hz
  have hnot :
      ¬ DegreeAtMost (redGraph ⊔ blueGraph) z.1 3 :=
    (Finset.mem_filter.mp hz).2
  exact hnot hdegree

end BlueThinningInput

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
