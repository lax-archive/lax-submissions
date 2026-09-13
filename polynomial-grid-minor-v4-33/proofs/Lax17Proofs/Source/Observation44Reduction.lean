import Lax17Proofs.Source.PseudoGridReduction
import Lax17Proofs.Source.PseudoGridSlicing
import Lax17Proofs.Source.PathPackingSupportDegree

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Observation 4.4

This module formalizes the two finite edge-contraction loops in Observation
4.4.  Unlike the obsolete row-contact shortcut, the reduction state retains
the actual `Q''` paths and their containment in distinct original `Q` paths.
That information is needed in Sections 4.3 and 4.4.
-/

namespace SimpleGraph


namespace Section4Reduction

open TreewidthSparsifier

/-- An invariant state for the two contraction loops in Chuzhoy--Tan
Observation 4.4.

`H` is the current contraction of the graph `H'` consisting of the rows and
retained auxiliary paths.  `K` is a supergraph carrying all original `Q`
paths; it is used only to remember which row edges are original `Q` edges.
-/
structure Observation44State
    {V₀ : Type u} [Fintype V₀] [DecidableEq V₀]
    (G₀ : _root_.SimpleGraph V₀) (D N Kcard : ℕ) where
  W : Type u
  [wFintype : Fintype W]
  [wDecidableEq : DecidableEq W]
  H : _root_.SimpleGraph W
  K : _root_.SimpleGraph W
  H_le_K : H ≤ K
  Arow : Finset W
  Brow : Finset W
  Aq : Finset W
  Bq : Finset W
  Sq : Finset W
  Tq : Finset W
  row : PerfectPathPacking H Arow Brow
  originalQ : PerfectPathPacking K Aq Bq
  retainedQ : PathPacking H Sq Tq
  parent : retainedQ.Index → originalQ.Index
  parent_injective : Function.Injective parent
  retained_vertex_subset :
    ∀ i : retainedQ.Index,
      (retainedQ.path i).vertexSet ⊆
        (originalQ.path (parent i)).vertexSet
  retained_edge_subset :
    ∀ i : retainedQ.Index,
      (retainedQ.path i).edgeSet ⊆
        (originalQ.path (parent i)).edgeSet
  minor : IsMinor H G₀
  row_card : row.card = N
  retained_card : retainedQ.card = Kcard
  /-- Every retained auxiliary path still meets at least one row from each of
  the `D` pseudo-grid levels. -/
  dense :
    ∀ i : retainedQ.Index,
      D ≤
        ((Finset.univ : Finset row.Index).filter fun r =>
          ¬ Disjoint (retainedQ.path i).vertexSet
            (row.path r).vertexSet).card
  /-- Observation 4.3, transported through all contractions. -/
  deletion_bound :
    ∀ e ∈ row.toPathPacking.edgeSet,
      e ∉ originalQ.toPathPacking.edgeSet →
        ∀ L : PathPacking
            (H.deleteEdges ({e} : Set (Sym2 W))) Arow Brow,
          L.card ≤ row.card - 1

attribute [instance] Observation44State.wFintype
attribute [instance] Observation44State.wDecidableEq

namespace Observation44State

variable {V₀ : Type u} [Fintype V₀] [DecidableEq V₀]
variable {G₀ : _root_.SimpleGraph V₀} {D N Kcard : ℕ}

/-- A convenient name for the set of rows met by one retained path. -/
noncomputable def metRows
    (State : Observation44State G₀ D N Kcard)
    (i : State.retainedQ.Index) : Finset State.row.Index := by
  classical
  exact Finset.univ.filter fun r =>
    ¬ Disjoint (State.retainedQ.path i).vertexSet
      (State.row.path r).vertexSet

@[simp] theorem mem_metRows
    (State : Observation44State G₀ D N Kcard)
    (i : State.retainedQ.Index) (r : State.row.Index) :
    r ∈ State.metRows i ↔
      ¬ Disjoint (State.retainedQ.path i).vertexSet
        (State.row.path r).vertexSet := by
  classical
  simp [metRows]

theorem dense_metRows
    (State : Observation44State G₀ D N Kcard)
    (i : State.retainedQ.Index) :
    D ≤ (State.metRows i).card := by
  simpa [metRows] using State.dense i

/-- The information about the retained `Q''` family needed after projecting
through one contraction.  Both paper contraction cases construct this object:
either the edge lies on one retained path, or its left endpoint is unused by
the entire retained family. -/
structure RetainedProjection
    (State : Observation44State G₀ D N Kcard)
    {a b : State.W} (hab : State.H.Adj a b) where
  projected :
    PathPacking (contractEdgeGraph State.H hab)
      (edgeContractImageSet (a := a) (b := b) State.Sq)
      (edgeContractImageSet (a := a) (b := b) State.Tq)
  oldIndex : projected.Index → State.retainedQ.Index
  oldIndex_bijective : Function.Bijective oldIndex
  vertex_image :
    ∀ i : projected.Index,
      (projected.path i).vertexSet =
        (State.retainedQ.path (oldIndex i)).vertexSet.image
          (EdgeContractVertex.projection
            (V := State.W) (u := a) (v := b))
  edge_preimage :
    ∀ (i : projected.Index) {e' : Sym2 (EdgeContractVertex State.W a b)},
      e' ∈ (projected.path i).edgeSet →
        ∃ p q : State.W,
          s(p, q) ∈
              (State.retainedQ.path (oldIndex i)).edgeSet ∧
            EdgeContractVertex.projection
                (V := State.W) (u := a) (v := b) p ≠
              EdgeContractVertex.projection
                (V := State.W) (u := a) (v := b) q ∧
            s(EdgeContractVertex.projection
                (V := State.W) (u := a) (v := b) p,
              EdgeContractVertex.projection
                (V := State.W) (u := a) (v := b) q) = e'

namespace RetainedProjection

/-- Project the retained family when the contracted edge lies on one retained
path. -/
noncomputable def ofSamePath
    (State : Observation44State G₀ D N Kcard)
    {a b : State.W} (hab : State.H.Adj a b)
    (i₀ : State.retainedQ.Index)
    (he : s(a, b) ∈ (State.retainedQ.path i₀).edgeSet) :
    RetainedProjection State hab where
  projected :=
    Section4Reduction.PathPacking.contractEdgeOfSamePath
      State.retainedQ hab i₀
      ((State.retainedQ.path i₀).endpoints_mem_vertexSet_of_edgeSet he).1
      ((State.retainedQ.path i₀).endpoints_mem_vertexSet_of_edgeSet he).2
  oldIndex := id
  oldIndex_bijective := Function.bijective_id
  vertex_image := by
    intro i
    by_cases hi : i = i₀
    · subst i
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_edge_mem
        (G := State.H) (hab := hab) (State.retainedQ.path i₀) he
    · have ha_not : a ∉ (State.retainedQ.path i).vertexSet := by
        intro hai
        exact Finset.disjoint_left.mp
          (State.retainedQ.node_disjoint hi) hai
          ((State.retainedQ.path i₀).endpoints_mem_vertexSet_of_edgeSet he).1
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_left_not_mem
        (G := State.H) (hab := hab) (State.retainedQ.path i) ha_not
  edge_preimage := by
    intro i e' he'
    by_cases hi : i = i₀
    · subst i
      exact ProjectionWalk.toGraphPath_edge_preimage_of_edge_mem
        (G := State.H) (hab := hab) (State.retainedQ.path i₀) he he'
    · have ha_not : a ∉ (State.retainedQ.path i).vertexSet := by
        intro hai
        exact Finset.disjoint_left.mp
          (State.retainedQ.node_disjoint hi) hai
          ((State.retainedQ.path i₀).endpoints_mem_vertexSet_of_edgeSet he).1
      exact ProjectionWalk.toGraphPath_edge_preimage_of_isPath
        (G := State.H) (hab := hab) (State.retainedQ.path i)
        (ProjectionWalk.ofWalk_isPath_of_left_not_mem
          (G := State.H) (hab := hab) (State.retainedQ.path i) ha_not)
        he'

/-- Project the retained family when the left endpoint is unused by every
retained path. -/
noncomputable def ofLeftUnused
    (State : Observation44State G₀ D N Kcard)
    {a b : State.W} (hab : State.H.Adj a b)
    (ha : a ∉ State.retainedQ.vertexSet) :
    RetainedProjection State hab where
  projected :=
    Section4Reduction.PathPacking.contractEdgeOfLeftUnused
      State.retainedQ hab ha
  oldIndex := id
  oldIndex_bijective := Function.bijective_id
  vertex_image := by
    intro i
    apply ProjectionWalk.toGraphPath_vertexSet_eq_image_of_left_not_mem
      (G := State.H) (hab := hab)
    intro hai
    exact ha ((State.retainedQ.mem_vertexSet).2 ⟨i, hai⟩)
  edge_preimage := by
    intro i e' he'
    have hai : a ∉ (State.retainedQ.path i).vertexSet := by
      intro haPath
      exact ha ((State.retainedQ.mem_vertexSet).2 ⟨i, haPath⟩)
    exact ProjectionWalk.toGraphPath_edge_preimage_of_isPath
      (G := State.H) (hab := hab) (State.retainedQ.path i)
      (ProjectionWalk.ofWalk_isPath_of_left_not_mem
        (G := State.H) (hab := hab) (State.retainedQ.path i) hai)
      he'

@[simp] theorem card
    (State : Observation44State G₀ D N Kcard)
    {a b : State.W} {hab : State.H.Adj a b}
    (Proj : RetainedProjection State hab) :
    Proj.projected.card = State.retainedQ.card := by
  dsimp [PathPacking.card]
  exact Fintype.card_congr
    (Equiv.ofBijective Proj.oldIndex Proj.oldIndex_bijective)

end RetainedProjection

/-- One source-faithful contraction step.  The contracted edge lies on both a
row and an original `Q` path.  `Proj` records which of the two retained-family
cases applies. -/
noncomputable def contractCommonEdge
    (State : Observation44State G₀ D N Kcard)
    {a b : State.W} (hab : State.H.Adj a b)
    (r₀ : State.row.Index)
    (hrow : s(a, b) ∈ (State.row.path r₀).edgeSet)
    (q₀ : State.originalQ.Index)
    (hq : s(a, b) ∈ (State.originalQ.path q₀).edgeSet)
    (Proj : RetainedProjection State hab) :
    Observation44State G₀ D N Kcard := by
  classical
  let habK : State.K.Adj a b := State.H_le_K hab
  let row' :=
    Section4Reduction.PerfectPathPacking.contractEdgeOfSamePath
      State.row hab r₀
      ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).1
      ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).2
  let originalQ' :=
    Section4Reduction.PerfectPathPacking.contractEdgeOfSamePath
      State.originalQ habK q₀
      ((State.originalQ.path q₀).endpoints_mem_vertexSet_of_edgeSet hq).1
      ((State.originalQ.path q₀).endpoints_mem_vertexSet_of_edgeSet hq).2
  have row_vertex_image :
      ∀ r : row'.Index,
        (row'.path r).vertexSet =
          (State.row.path r).vertexSet.image
            (EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b)) := by
    intro r
    by_cases hr : r = r₀
    · subst r
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_edge_mem
        (G := State.H) (hab := hab) (State.row.path r₀) hrow
    · have ha_not : a ∉ (State.row.path r).vertexSet := by
        intro har
        exact Finset.disjoint_left.mp (State.row.node_disjoint hr) har
          ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).1
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_left_not_mem
        (G := State.H) (hab := hab) (State.row.path r) ha_not
  have originalQ_vertex_image :
      ∀ q : originalQ'.Index,
        (originalQ'.path q).vertexSet =
          (State.originalQ.path q).vertexSet.image
            (EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b)) := by
    intro q
    by_cases hqi : q = q₀
    · subst q
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_edge_mem
        (G := State.K) (hab := habK) (State.originalQ.path q₀) hq
    · have ha_not : a ∉ (State.originalQ.path q).vertexSet := by
        intro haq
        exact Finset.disjoint_left.mp
          (State.originalQ.node_disjoint hqi) haq
          ((State.originalQ.path q₀).endpoints_mem_vertexSet_of_edgeSet hq).1
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_left_not_mem
        (G := State.K) (hab := habK) (State.originalQ.path q) ha_not
  have originalQ_edge_survives :
      ∀ (q : originalQ'.Index) {x y : State.W},
        s(x, y) ∈ (State.originalQ.path q).edgeSet →
          EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b) x ≠
            EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b) y →
            s(EdgeContractVertex.projection
                (V := State.W) (u := a) (v := b) x,
              EdgeContractVertex.projection
                (V := State.W) (u := a) (v := b) y) ∈
              (originalQ'.path q).edgeSet := by
    intro q x y hxy hne
    by_cases hqi : q = q₀
    · subst q
      exact ProjectionWalk.mem_toGraphPath_edgeSet_of_mem_of_isPath
        (State.originalQ.path q₀)
        (ProjectionWalk.ofWalk_isPath_of_edge_mem
          (G := State.K) (hab := habK)
          (State.originalQ.path q₀) hq)
        hxy hne
    · have ha_not : a ∉ (State.originalQ.path q).vertexSet := by
        intro haq
        exact Finset.disjoint_left.mp
          (State.originalQ.node_disjoint hqi) haq
          ((State.originalQ.path q₀).endpoints_mem_vertexSet_of_edgeSet hq).1
      exact ProjectionWalk.mem_toGraphPath_edgeSet_of_mem_of_isPath
        (State.originalQ.path q)
        (ProjectionWalk.ofWalk_isPath_of_left_not_mem
          (G := State.K) (hab := habK)
          (State.originalQ.path q) ha_not)
        hxy hne
  refine
    { W := EdgeContractVertex State.W a b
      H := contractEdgeGraph State.H hab
      K := contractEdgeGraph State.K habK
      H_le_K := contractEdgeGraph_mono State.H_le_K hab
      Arow := edgeContractImageSet (a := a) (b := b) State.Arow
      Brow := edgeContractImageSet (a := a) (b := b) State.Brow
      Aq := edgeContractImageSet (a := a) (b := b) State.Aq
      Bq := edgeContractImageSet (a := a) (b := b) State.Bq
      Sq := edgeContractImageSet (a := a) (b := b) State.Sq
      Tq := edgeContractImageSet (a := a) (b := b) State.Tq
      row := row'
      originalQ := originalQ'
      retainedQ := Proj.projected
      parent := fun i => State.parent (Proj.oldIndex i)
      parent_injective := by
        intro i j hij
        apply Proj.oldIndex_bijective.1
        apply State.parent_injective
        exact hij
      retained_vertex_subset := ?_
      retained_edge_subset := ?_
      minor :=
        (contractEdgeGraph.isMinor (G := State.H) (huv := hab)).trans
          State.minor
      row_card := by
        calc
          row'.card = State.row.card := rfl
          _ = N := State.row_card
      retained_card := by
        rw [Proj.card, State.retained_card]
      dense := ?_
      deletion_bound := ?_ }
  · intro i
    rw [Proj.vertex_image, originalQ_vertex_image]
    exact Finset.image_mono _
      (State.retained_vertex_subset (Proj.oldIndex i))
  · intro i e' he'
    rcases Proj.edge_preimage i he' with
      ⟨x, y, hxy, hne, hmap⟩
    rw [← hmap]
    exact originalQ_edge_survives
      (State.parent (Proj.oldIndex i))
      (State.retained_edge_subset (Proj.oldIndex i) hxy) hne
  · intro i
    have hdense := State.dense (Proj.oldIndex i)
    apply hdense.trans
    apply Finset.card_le_card
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rcases Finset.not_disjoint_iff.1 hr with ⟨v, hvQ, hvR⟩
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ r, ?_⟩
    rw [Proj.vertex_image, row_vertex_image,
      Finset.not_disjoint_iff]
    exact ⟨EdgeContractVertex.projection
        (V := State.W) (u := a) (v := b) v,
      Finset.mem_image.2 ⟨v, hvQ, rfl⟩,
      Finset.mem_image.2 ⟨v, hvR, rfl⟩⟩
  · intro e' heRow' heQ' L
    rcases (row'.toPathPacking.mem_edgeSet).1 heRow' with ⟨r, her⟩
    have hrowPath :
        (TreewidthSparsifier.contractEdgeGraph.ProjectionWalk.ofWalk
          (G := State.H) (huv := hab) (State.row.path r).walk).IsPath := by
      by_cases hr : r = r₀
      · subst r
        exact ProjectionWalk.ofWalk_isPath_of_edge_mem
          (G := State.H) (hab := hab) (State.row.path r₀) hrow
      · have ha_not : a ∉ (State.row.path r).vertexSet := by
          intro har
          exact Finset.disjoint_left.mp (State.row.node_disjoint hr) har
            ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).1
        exact ProjectionWalk.ofWalk_isPath_of_left_not_mem
          (G := State.H) (hab := hab) (State.row.path r) ha_not
    rcases ProjectionWalk.toGraphPath_edge_preimage_of_isPath
        (G := State.H) (hab := hab) (State.row.path r) hrowPath her with
      ⟨x, y, hxyRow, hprojNe, hmap⟩
    subst e'
    let e : Sym2 State.W := s(x, y)
    have heRow : e ∈ State.row.toPathPacking.edgeSet :=
      (State.row.toPathPacking.mem_edgeSet).2 ⟨r, hxyRow⟩
    have hxyAdj : State.H.Adj x y :=
      State.row.edgeSet_subset_edgeSet heRow
    have hdiff : e ≠ s(a, b) := by
      intro heq
      exact hprojNe
        ((EdgeContractVertex.projection_eq_iff_sym2_eq hab hxyAdj.ne).2 heq)
    have heQ : e ∉ State.originalQ.toPathPacking.edgeSet := by
      intro heOldQ
      have heNewQ :
          s(EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b) x,
            EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b) y) ∈
            originalQ'.toPathPacking.edgeSet := by
        apply
          Section4Reduction.PathPacking.mem_edgeSet_contractEdgeOfSamePath
            State.originalQ.toPathPacking habK q₀ hq heOldQ hprojNe
      exact heQ' heNewQ
    have hLle : L.card ≤ row'.card := by
      calc
        L.card ≤
            (edgeContractImageSet (a := a) (b := b) State.Arow).card :=
          L.card_le_left_card
        _ = row'.card := row'.card_eq_left_card.symm
    by_contra hnot
    have hfull : L.card = row'.card := by omega
    have hleft :
        L.card =
          (edgeContractImageSet (a := a) (b := b) State.Arow).card := by
      rw [hfull, row'.card_eq_left_card]
    have hright :
        L.card =
          (edgeContractImageSet (a := a) (b := b) State.Brow).card := by
      rw [hfull, row'.card_eq_right_card]
    let Lperfect := L.toPerfectOfCardEq hleft hright
    let Lifted :=
      liftPerfectPathPacking_deleteEdgeContract
        hab hxyAdj hdiff hprojNe
        (PerfectPathPacking.projection_injOn_left_of_same_path State.row r₀
          ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).1
          ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).2)
        (PerfectPathPacking.projection_injOn_right_of_same_path State.row r₀
          ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).1
          ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).2)
        Lperfect
    have hbound := State.deletion_bound e heRow heQ Lifted.toPathPacking
    have hLiftedCard : Lifted.card = State.row.card := by
      calc
        Lifted.card = Lperfect.card := rfl
        _ = L.card := rfl
        _ = row'.card := hfull
        _ = State.row.card := rfl
    have hbound' : State.row.card ≤ State.row.card - 1 := by
      calc
        State.row.card = Lifted.card := hLiftedCard.symm
        _ ≤ State.row.card - 1 := hbound
    have hrowpos : 0 < State.row.card := by
      dsimp [PerfectPathPacking.card]
      exact Fintype.card_pos_iff.mpr ⟨r⟩
    omega

/-- The second contraction move: contract an edge of a retained `Q''` path
incident with a vertex outside the row linkage. -/
noncomputable def contractOffRowEdge
    (State : Observation44State G₀ D N Kcard)
    {a b : State.W} (hab : State.H.Adj a b)
    (haRow : a ∉ State.row.toPathPacking.vertexSet)
    (i₀ : State.retainedQ.Index)
    (hret : s(a, b) ∈ (State.retainedQ.path i₀).edgeSet)
    (q₀ : State.originalQ.Index)
    (hq : s(a, b) ∈ (State.originalQ.path q₀).edgeSet)
    (hparent : State.parent i₀ = q₀) :
    Observation44State G₀ D N Kcard := by
  classical
  let habK : State.K.Adj a b := State.H_le_K hab
  let row' :=
    Section4Reduction.PerfectPathPacking.contractEdgeOfLeftUnused
      State.row hab haRow
  let originalQ' :=
    Section4Reduction.PerfectPathPacking.contractEdgeOfSamePath
      State.originalQ habK q₀
      ((State.originalQ.path q₀).endpoints_mem_vertexSet_of_edgeSet hq).1
      ((State.originalQ.path q₀).endpoints_mem_vertexSet_of_edgeSet hq).2
  let Proj : State.RetainedProjection hab :=
    RetainedProjection.ofSamePath State hab i₀ hret
  have row_vertex_image :
      ∀ r : row'.Index,
        (row'.path r).vertexSet =
          (State.row.path r).vertexSet.image
            (EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b)) := by
    intro r
    apply ProjectionWalk.toGraphPath_vertexSet_eq_image_of_left_not_mem
      (G := State.H) (hab := hab)
    intro har
    exact haRow ((State.row.toPathPacking.mem_vertexSet).2 ⟨r, har⟩)
  have originalQ_vertex_image :
      ∀ q : originalQ'.Index,
        (originalQ'.path q).vertexSet =
          (State.originalQ.path q).vertexSet.image
            (EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b)) := by
    intro q
    by_cases hqi : q = q₀
    · subst q
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_edge_mem
        (G := State.K) (hab := habK) (State.originalQ.path q₀) hq
    · have ha_not : a ∉ (State.originalQ.path q).vertexSet := by
        intro haq
        exact Finset.disjoint_left.mp
          (State.originalQ.node_disjoint hqi) haq
          ((State.originalQ.path q₀).endpoints_mem_vertexSet_of_edgeSet hq).1
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_left_not_mem
        (G := State.K) (hab := habK) (State.originalQ.path q) ha_not
  have originalQ_edge_survives :
      ∀ (q : originalQ'.Index) {x y : State.W},
        s(x, y) ∈ (State.originalQ.path q).edgeSet →
          EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b) x ≠
            EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b) y →
            s(EdgeContractVertex.projection
                (V := State.W) (u := a) (v := b) x,
              EdgeContractVertex.projection
                (V := State.W) (u := a) (v := b) y) ∈
              (originalQ'.path q).edgeSet := by
    intro q x y hxy hne
    by_cases hqi : q = q₀
    · subst q
      exact ProjectionWalk.mem_toGraphPath_edgeSet_of_mem_of_isPath
        (State.originalQ.path q₀)
        (ProjectionWalk.ofWalk_isPath_of_edge_mem
          (G := State.K) (hab := habK)
          (State.originalQ.path q₀) hq)
        hxy hne
    · have ha_not : a ∉ (State.originalQ.path q).vertexSet := by
        intro haq
        exact Finset.disjoint_left.mp
          (State.originalQ.node_disjoint hqi) haq
          ((State.originalQ.path q₀).endpoints_mem_vertexSet_of_edgeSet hq).1
      exact ProjectionWalk.mem_toGraphPath_edgeSet_of_mem_of_isPath
        (State.originalQ.path q)
        (ProjectionWalk.ofWalk_isPath_of_left_not_mem
          (G := State.K) (hab := habK)
          (State.originalQ.path q) ha_not)
        hxy hne
  have haArow : a ∉ State.Arow := by
    intro haA
    let r := State.row.indexOfSource ⟨a, haA⟩
    apply haRow
    apply State.row.toPathPacking.mem_vertexSet.2
    refine ⟨r, ?_⟩
    have hsrc : (State.row.path r).source = a := by
      exact congrArg Subtype.val (State.row.source_indexOfSource ⟨a, haA⟩)
    simpa [hsrc] using GraphPath.source_mem_vertexSet (State.row.path r)
  have haBrow : a ∉ State.Brow := by
    intro haB
    let r := State.row.indexOfTarget ⟨a, haB⟩
    apply haRow
    apply State.row.toPathPacking.mem_vertexSet.2
    refine ⟨r, ?_⟩
    have htgt : (State.row.path r).target = a := by
      exact congrArg Subtype.val (State.row.target_indexOfTarget ⟨a, haB⟩)
    simpa [htgt] using GraphPath.target_mem_vertexSet (State.row.path r)
  refine
    { W := EdgeContractVertex State.W a b
      H := contractEdgeGraph State.H hab
      K := contractEdgeGraph State.K habK
      H_le_K := contractEdgeGraph_mono State.H_le_K hab
      Arow := edgeContractImageSet (a := a) (b := b) State.Arow
      Brow := edgeContractImageSet (a := a) (b := b) State.Brow
      Aq := edgeContractImageSet (a := a) (b := b) State.Aq
      Bq := edgeContractImageSet (a := a) (b := b) State.Bq
      Sq := edgeContractImageSet (a := a) (b := b) State.Sq
      Tq := edgeContractImageSet (a := a) (b := b) State.Tq
      row := row'
      originalQ := originalQ'
      retainedQ := Proj.projected
      parent := fun i => State.parent (Proj.oldIndex i)
      parent_injective := by
        intro i j hij
        apply Proj.oldIndex_bijective.1
        apply State.parent_injective
        exact hij
      retained_vertex_subset := ?_
      retained_edge_subset := ?_
      minor :=
        (contractEdgeGraph.isMinor (G := State.H) (huv := hab)).trans
          State.minor
      row_card := by
        calc
          row'.card = State.row.card := rfl
          _ = N := State.row_card
      retained_card := by
        rw [Proj.card, State.retained_card]
      dense := ?_
      deletion_bound := ?_ }
  · intro i
    rw [Proj.vertex_image, originalQ_vertex_image]
    exact Finset.image_mono _
      (State.retained_vertex_subset (Proj.oldIndex i))
  · intro i e' he'
    rcases Proj.edge_preimage i he' with
      ⟨x, y, hxy, hne, hmap⟩
    rw [← hmap]
    exact originalQ_edge_survives
      (State.parent (Proj.oldIndex i))
      (State.retained_edge_subset (Proj.oldIndex i) hxy) hne
  · intro i
    have hdense := State.dense (Proj.oldIndex i)
    apply hdense.trans
    apply Finset.card_le_card
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rcases Finset.not_disjoint_iff.1 hr with ⟨v, hvQ, hvR⟩
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ r, ?_⟩
    rw [Proj.vertex_image, row_vertex_image,
      Finset.not_disjoint_iff]
    exact ⟨EdgeContractVertex.projection
        (V := State.W) (u := a) (v := b) v,
      Finset.mem_image.2 ⟨v, hvQ, rfl⟩,
      Finset.mem_image.2 ⟨v, hvR, rfl⟩⟩
  · intro e' heRow' heQ' L
    rcases (row'.toPathPacking.mem_edgeSet).1 heRow' with ⟨r, her⟩
    have ha_not : a ∉ (State.row.path r).vertexSet := by
      intro har
      exact haRow ((State.row.toPathPacking.mem_vertexSet).2 ⟨r, har⟩)
    have hrowPath :=
      ProjectionWalk.ofWalk_isPath_of_left_not_mem
        (G := State.H) (hab := hab) (State.row.path r) ha_not
    rcases ProjectionWalk.toGraphPath_edge_preimage_of_isPath
        (G := State.H) (hab := hab) (State.row.path r) hrowPath her with
      ⟨x, y, hxyRow, hprojNe, hmap⟩
    subst e'
    let e : Sym2 State.W := s(x, y)
    have heRow : e ∈ State.row.toPathPacking.edgeSet :=
      (State.row.toPathPacking.mem_edgeSet).2 ⟨r, hxyRow⟩
    have hxyAdj : State.H.Adj x y :=
      State.row.edgeSet_subset_edgeSet heRow
    have hdiff : e ≠ s(a, b) := by
      intro heq
      exact hprojNe
        ((EdgeContractVertex.projection_eq_iff_sym2_eq hab hxyAdj.ne).2 heq)
    have heQ : e ∉ State.originalQ.toPathPacking.edgeSet := by
      intro heOldQ
      have heNewQ :
          s(EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b) x,
            EdgeContractVertex.projection
              (V := State.W) (u := a) (v := b) y) ∈
            originalQ'.toPathPacking.edgeSet := by
        apply
          Section4Reduction.PathPacking.mem_edgeSet_contractEdgeOfSamePath
            State.originalQ.toPathPacking habK q₀ hq heOldQ hprojNe
      exact heQ' heNewQ
    have hLle : L.card ≤ row'.card := by
      calc
        L.card ≤
            (edgeContractImageSet (a := a) (b := b) State.Arow).card :=
          L.card_le_left_card
        _ = row'.card := row'.card_eq_left_card.symm
    by_contra hnot
    have hfull : L.card = row'.card := by omega
    have hleft :
        L.card =
          (edgeContractImageSet (a := a) (b := b) State.Arow).card := by
      rw [hfull, row'.card_eq_left_card]
    have hright :
        L.card =
          (edgeContractImageSet (a := a) (b := b) State.Brow).card := by
      rw [hfull, row'.card_eq_right_card]
    let Lperfect := L.toPerfectOfCardEq hleft hright
    let Lifted :=
      liftPerfectPathPacking_deleteEdgeContract
        hab hxyAdj hdiff hprojNe
        (EdgeContractVertex.projection_injOn_of_left_not_mem haArow)
        (EdgeContractVertex.projection_injOn_of_left_not_mem haBrow)
        Lperfect
    have hbound := State.deletion_bound e heRow heQ Lifted.toPathPacking
    have hLiftedCard : Lifted.card = State.row.card := by
      calc
        Lifted.card = Lperfect.card := rfl
        _ = L.card := rfl
        _ = row'.card := hfull
        _ = State.row.card := rfl
    have hbound' : State.row.card ≤ State.row.card - 1 := by
      calc
        State.row.card = Lifted.card := hLiftedCard.symm
        _ ≤ State.row.card - 1 := hbound
    have hrowpos : 0 < State.row.card := by
      dsimp [PerfectPathPacking.card]
      exact Fintype.card_pos_iff.mpr ⟨r⟩
    omega

/-- If a current row edge is still an original-`Q` edge, the first loop of
Observation 4.4 produces a strictly smaller invariant state. -/
theorem exists_smaller_of_common_edge
    (State : Observation44State G₀ D N Kcard)
    {e : Sym2 State.W}
    (heRow : e ∈ State.row.toPathPacking.edgeSet)
    (heQ : e ∈ State.originalQ.toPathPacking.edgeSet) :
    ∃ Next : Observation44State G₀ D N Kcard,
      Fintype.card Next.W < Fintype.card State.W := by
  classical
  let a : State.W := e.out.1
  let b : State.W := e.out.2
  have heq : s(a, b) = e := e.out_eq
  rcases (State.row.toPathPacking.mem_edgeSet).1 heRow with
    ⟨r₀, hr₀⟩
  rcases (State.originalQ.toPathPacking.mem_edgeSet).1 heQ with
    ⟨q₀, hq₀⟩
  have hrow : s(a, b) ∈ (State.row.path r₀).edgeSet := by
    simpa [heq] using hr₀
  have hq : s(a, b) ∈ (State.originalQ.path q₀).edgeSet := by
    simpa [heq] using hq₀
  have hab : State.H.Adj a b :=
    State.row.edgeSet_subset_edgeSet
      ((State.row.toPathPacking.mem_edgeSet).2 ⟨r₀, hrow⟩)
  by_cases hret : s(a, b) ∈ State.retainedQ.edgeSet
  · rcases (State.retainedQ.mem_edgeSet).1 hret with ⟨i₀, hi₀⟩
    let Proj : State.RetainedProjection hab :=
      RetainedProjection.ofSamePath State hab i₀ hi₀
    let Next :=
      State.contractCommonEdge hab r₀ hrow q₀ hq Proj
    refine ⟨Next, ?_⟩
    exact EdgeContractVertex.card_lt_of_ne hab.ne
  · rcases
      PathPacking.left_or_right_not_mem_vertexSet_of_subpaths
        State.retainedQ State.originalQ.toPathPacking State.H_le_K State.parent
        State.parent_injective State.retained_vertex_subset
        State.retained_edge_subset hq hret with ha | hb
    · let Proj : State.RetainedProjection hab :=
        RetainedProjection.ofLeftUnused State hab ha
      let Next :=
        State.contractCommonEdge hab r₀ hrow q₀ hq Proj
      refine ⟨Next, ?_⟩
      exact EdgeContractVertex.card_lt_of_ne hab.ne
    · have hba : State.H.Adj b a := hab.symm
      have hrow' : s(b, a) ∈ (State.row.path r₀).edgeSet := by
        simpa only [Sym2.eq_swap] using hrow
      have hq' : s(b, a) ∈ (State.originalQ.path q₀).edgeSet := by
        simpa only [Sym2.eq_swap] using hq
      let Proj : State.RetainedProjection hba :=
        RetainedProjection.ofLeftUnused State hba hb
      let Next :=
        State.contractCommonEdge hba r₀ hrow' q₀ hq' Proj
      refine ⟨Next, ?_⟩
      exact EdgeContractVertex.card_lt_of_ne hba.ne

/-- If a vertex of a retained `Q''` path is outside the row linkage, an
incident retained edge can be contracted.  Positivity of `D` guarantees that
the retained path also meets a row, and hence is nontrivial. -/
theorem exists_smaller_of_off_row_vertex
    (State : Observation44State G₀ D N Kcard)
    (hD : 0 < D)
    {a : State.W}
    (haRetained : a ∈ State.retainedQ.vertexSet)
    (haRow : a ∉ State.row.toPathPacking.vertexSet) :
    ∃ Next : Observation44State G₀ D N Kcard,
      Fintype.card Next.W < Fintype.card State.W := by
  classical
  rcases State.retainedQ.mem_vertexSet.1 haRetained with ⟨i₀, hai₀⟩
  have hmetPos : 0 < (State.metRows i₀).card :=
    hD.trans_le (State.dense_metRows i₀)
  rcases Finset.card_pos.mp hmetPos with ⟨r, hr⟩
  have hmeet :
      ¬ Disjoint (State.retainedQ.path i₀).vertexSet
        (State.row.path r).vertexSet :=
    (State.mem_metRows i₀ r).1 hr
  rcases Finset.not_disjoint_iff.1 hmeet with
    ⟨w, hwRetained, hwRow⟩
  have haw : a ≠ w := by
    intro haw
    subst w
    exact haRow
      (State.row.toPathPacking.mem_vertexSet.2 ⟨r, hwRow⟩)
  have hnontrivial :
      (State.retainedQ.path i₀).source ≠
        (State.retainedQ.path i₀).target := by
    intro hst
    have haSource :=
      (State.retainedQ.path i₀)
        |>.eq_source_of_source_eq_target_of_mem_vertexSet hst hai₀
    have hwSource :=
      (State.retainedQ.path i₀)
        |>.eq_source_of_source_eq_target_of_mem_vertexSet hst hwRetained
    exact haw (haSource.trans hwSource.symm)
  rcases
      (State.retainedQ.path i₀)
        |>.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
          hnontrivial hai₀ with
    ⟨e, heRetained, hae⟩
  rcases Sym2.mem_iff_exists.mp hae with ⟨b, rfl⟩
  have hab : State.H.Adj a b :=
    State.retainedQ.edgeSet_subset_edgeSet
      (State.retainedQ.mem_edgeSet.2 ⟨i₀, heRetained⟩)
  have heOriginal :
      s(a, b) ∈
        (State.originalQ.path (State.parent i₀)).edgeSet :=
    State.retained_edge_subset i₀ heRetained
  let Next :=
    State.contractOffRowEdge hab haRow i₀ heRetained
      (State.parent i₀) heOriginal rfl
  refine ⟨Next, ?_⟩
  exact EdgeContractVertex.card_lt_of_ne hab.ne

/-- The terminal invariant of both contraction loops in Observation 4.4:
no row edge is an edge of an original `Q` path, and every retained `Q''`
vertex lies on a row. -/
def IsReduced (State : Observation44State G₀ D N Kcard) : Prop :=
  (∀ e ∈ State.row.toPathPacking.edgeSet,
      e ∉ State.originalQ.toPathPacking.edgeSet) ∧
    State.retainedQ.vertexSet ⊆ State.row.toPathPacking.vertexSet

/-- Finite minimization simultaneously terminates the two contraction loops.
Minimizing the current vertex cardinality is equivalent to repeatedly using
whichever of the two paper contraction moves is presently available. -/
theorem exists_reduced_of_state
    (Initial : Observation44State G₀ D N Kcard)
    (hD : 0 < D) :
    ∃ State : Observation44State G₀ D N Kcard, State.IsReduced := by
  classical
  let HasCard : ℕ → Prop := fun n =>
    ∃ State : Observation44State G₀ D N Kcard,
      Fintype.card State.W = n
  have hExists : ∃ n : ℕ, HasCard n :=
    ⟨Fintype.card Initial.W, Initial, rfl⟩
  rcases Nat.find_spec hExists with ⟨State, hStateCard⟩
  refine ⟨State, ?_, ?_⟩
  · intro e heRow heOriginal
    rcases State.exists_smaller_of_common_edge heRow heOriginal with
      ⟨Next, hNext⟩
    have hNextCandidate : HasCard (Fintype.card Next.W) :=
      ⟨Next, rfl⟩
    have hminimal :
        Nat.find hExists ≤ Fintype.card Next.W :=
      Nat.find_min' (H := hExists) hNextCandidate
    omega
  · intro a haRetained
    by_contra haRow
    rcases
        State.exists_smaller_of_off_row_vertex hD haRetained haRow with
      ⟨Next, hNext⟩
    have hNextCandidate : HasCard (Fintype.card Next.W) :=
      ⟨Next, rfl⟩
    have hminimal :
        Nat.find hExists ≤ Fintype.card Next.W :=
      Nat.find_min' (H := hExists) hNextCandidate
    omega

/-! ## The vertex-exact reduced support -/

/-- The ambient type of the final paper graph `H''`: exactly the vertices of
the row linkage. -/
abbrev RowVertex (State : Observation44State G₀ D N Kcard) :=
  {v : State.W // v ∈ State.row.toPathPacking.vertexSet}

theorem Arow_subset_row_vertexSet
    (State : Observation44State G₀ D N Kcard) :
    State.Arow ⊆ State.row.toPathPacking.vertexSet := by
  intro a ha
  let r := State.row.indexOfSource ⟨a, ha⟩
  apply State.row.toPathPacking.mem_vertexSet.2
  refine ⟨r, ?_⟩
  have hsource : (State.row.path r).source = a :=
    congrArg Subtype.val (State.row.source_indexOfSource ⟨a, ha⟩)
  simpa [hsource] using GraphPath.source_mem_vertexSet (State.row.path r)

theorem Brow_subset_row_vertexSet
    (State : Observation44State G₀ D N Kcard) :
    State.Brow ⊆ State.row.toPathPacking.vertexSet := by
  intro b hb
  let r := State.row.indexOfTarget ⟨b, hb⟩
  apply State.row.toPathPacking.mem_vertexSet.2
  refine ⟨r, ?_⟩
  have htarget : (State.row.path r).target = b :=
    congrArg Subtype.val (State.row.target_indexOfTarget ⟨b, hb⟩)
  simpa [htarget] using GraphPath.target_mem_vertexSet (State.row.path r)

/-- The row linkage lifted to the induced graph on its exact vertex support. -/
noncomputable def rowInduced
    (State : Observation44State G₀ D N Kcard) :
    PerfectPathPacking
      (State.H.induce
        {v : State.W | v ∈ State.row.toPathPacking.vertexSet})
      (PathPacking.subtypeFinset State.Arow
        State.row.toPathPacking.vertexSet State.Arow_subset_row_vertexSet)
      (PathPacking.subtypeFinset State.Brow
        State.row.toPathPacking.vertexSet State.Brow_subset_row_vertexSet) :=
  State.row.induce State.row.toPathPacking.vertexSet
    (fun i => State.row.toPathPacking.path_vertexSet_subset_vertexSet i)
    State.Arow_subset_row_vertexSet State.Brow_subset_row_vertexSet

/-- The retained auxiliary packing lifted to the same exact row-support
vertex type. -/
noncomputable def retainedInduced
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    PathPacking
      (State.H.induce
        {v : State.W | v ∈ State.row.toPathPacking.vertexSet})
      (Finset.univ : Finset (State.RowVertex))
      (Finset.univ : Finset (State.RowVertex)) := by
  classical
  let hstay :
      ∀ i : State.retainedQ.Index,
        (State.retainedQ.path i).vertexSet ⊆
          State.row.toPathPacking.vertexSet :=
    fun i v hv => hReduced.2
      ((State.retainedQ.mem_vertexSet).2 ⟨i, hv⟩)
  exact
    { Index := State.retainedQ.Index
      path := fun i =>
        (State.retainedQ.path i).induce
          State.row.toPathPacking.vertexSet (hstay i)
      connects := by
        intro i
        exact Or.inl ⟨Finset.mem_univ _, Finset.mem_univ _⟩
      node_disjoint := by
        intro i j hij
        rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
        intro v hvi hvj
        exact Finset.disjoint_left.mp (State.retainedQ.node_disjoint hij)
          ((GraphPath.mem_induce_vertexSet
            (State.retainedQ.path i)
            State.row.toPathPacking.vertexSet (hstay i) v).1 hvi)
          ((GraphPath.mem_induce_vertexSet
            (State.retainedQ.path j)
            State.row.toPathPacking.vertexSet (hstay j) v).1 hvj) }

/-- The final graph `H''` is exactly the union of the induced row linkage and
the induced retained auxiliary paths. -/
noncomputable def reducedGraph
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    _root_.SimpleGraph State.RowVertex :=
  State.rowInduced.toPathPacking.spanningGraph ⊔
    (State.retainedInduced hReduced).spanningGraph

/-- The reduced support is the union of two node-disjoint path packings, so
its maximum degree is at most four. -/
theorem reducedGraph_maxDegreeAtMost_four
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    MaxDegreeAtMost (State.reducedGraph hReduced) 4 := by
  simpa [reducedGraph] using
    maxDegreeAtMost_sup
      State.rowInduced.toPathPacking.maxDegreeAtMost_spanningGraph
      (State.retainedInduced hReduced).maxDegreeAtMost_spanningGraph

/-- The row linkage viewed in `H''`. -/
noncomputable def reducedRow
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    PerfectPathPacking (State.reducedGraph hReduced)
      (PathPacking.subtypeFinset State.Arow
        State.row.toPathPacking.vertexSet State.Arow_subset_row_vertexSet)
      (PathPacking.subtypeFinset State.Brow
        State.row.toPathPacking.vertexSet State.Brow_subset_row_vertexSet) :=
  State.rowInduced.inSpanningGraph.mapLe le_sup_left

/-- The retained auxiliary family viewed in `H''`. -/
noncomputable def reducedRetained
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    PathPacking (State.reducedGraph hReduced)
      (Finset.univ : Finset State.RowVertex) Finset.univ :=
  (State.retainedInduced hReduced).inSpanningGraph.mapLe le_sup_right

@[simp] theorem reducedRow_card
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    (State.reducedRow hReduced).card = N := by
  simpa [reducedRow, rowInduced] using State.row_card

@[simp] theorem reducedRetained_card
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    (State.reducedRetained hReduced).card = Kcard := by
  simpa [reducedRetained, retainedInduced] using State.retained_card

/-- Property I1 survives the contractions and the final restriction to the
row-support vertex type.  In particular, every retained auxiliary path still
meets at least `D` distinct paths of the reduced row linkage. -/
theorem reducedRetained_metRows_card
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced)
    (q : (State.reducedRetained hReduced).Index) :
    D ≤
      ((Finset.univ : Finset (State.reducedRow hReduced).Index).filter
        fun r =>
          ¬ Disjoint
            ((State.reducedRetained hReduced).path q).vertexSet
            ((State.reducedRow hReduced).path r).vertexSet).card := by
  classical
  apply (State.dense q).trans
  apply Finset.card_le_card
  intro r hr
  have hmeet :
      ¬ Disjoint (State.retainedQ.path q).vertexSet
        (State.row.path r).vertexSet :=
    (Finset.mem_filter.1 hr).2
  rcases Finset.not_disjoint_iff.1 hmeet with ⟨x, hxq, hxr⟩
  have hxSupport : x ∈ State.row.toPathPacking.vertexSet :=
    State.row.toPathPacking.mem_vertexSet.2 ⟨r, hxr⟩
  let x' : State.RowVertex := ⟨x, hxSupport⟩
  refine Finset.mem_filter.2
    ⟨Finset.mem_univ r, Finset.not_disjoint_iff.2 ⟨x', ?_, ?_⟩⟩
  · simpa [x', reducedRetained, retainedInduced,
      PathPacking.inSpanningGraph, PathPacking.mapLe, PathPacking.transfer]
      using
        (GraphPath.mem_induce_vertexSet
          (State.retainedQ.path q) State.row.toPathPacking.vertexSet
          (fun v hv => hReduced.2
            (State.retainedQ.mem_vertexSet.2 ⟨q, hv⟩)) x').2 hxq
  · simpa [x', reducedRow, rowInduced,
      PerfectPathPacking.inSpanningGraph, PerfectPathPacking.mapLe,
      PathPacking.inSpanningGraph, PathPacking.mapLe, PathPacking.transfer]
      using
        (GraphPath.mem_induce_vertexSet
          (State.row.path r) State.row.toPathPacking.vertexSet
          (State.row.toPathPacking.path_vertexSet_subset_vertexSet r) x').2 hxr

/-- The intersection hypothesis needed by Theorem 4.6, now for the actual
retained auxiliary paths rather than length-zero contact paths. -/
theorem reducedRetained_intersects_reducedRow
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced)
    (hD : 0 < D) :
    PathSlicing.PathPackingIntersectsLinkage
      (State.reducedRow hReduced) (State.reducedRetained hReduced) := by
  classical
  intro q
  have hpos :
      0 <
        ((Finset.univ : Finset (State.reducedRow hReduced).Index).filter
          fun r =>
            ¬ Disjoint
              ((State.reducedRetained hReduced).path q).vertexSet
              ((State.reducedRow hReduced).path r).vertexSet).card :=
    hD.trans_le (State.reducedRetained_metRows_card hReduced q)
  rcases Finset.card_pos.mp hpos with ⟨r, hr⟩
  exact ⟨r, (Finset.mem_filter.1 hr).2⟩

theorem reducedRow_spansVertices
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    (State.reducedRow hReduced).SpansVertices := by
  intro v
  have hv : v.1 ∈ State.row.toPathPacking.vertexSet := v.2
  rcases State.row.toPathPacking.mem_vertexSet.1 hv with ⟨i, hvi⟩
  apply (State.reducedRow hReduced).toPathPacking.mem_vertexSet.2
  refine ⟨i, ?_⟩
  simpa [reducedRow, rowInduced, PerfectPathPacking.inSpanningGraph,
    PerfectPathPacking.mapLe, PathPacking.inSpanningGraph,
    PathPacking.mapLe, PathPacking.transfer] using
      (GraphPath.mem_induce_vertexSet
        (State.row.path i) State.row.toPathPacking.vertexSet
        (State.row.toPathPacking.path_vertexSet_subset_vertexSet i) v).2 hvi

theorem reducedGraph_le_induced
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    State.reducedGraph hReduced ≤
      State.H.induce
        {v : State.W | v ∈ State.row.toPathPacking.vertexSet} :=
  sup_le
    State.rowInduced.toPathPacking.spanningGraph_le
    (State.retainedInduced hReduced).spanningGraph_le

/-- The vertex-exact support graph is a minor of the current contraction
state, using singleton branch sets under subtype inclusion. -/
theorem reducedGraph_isMinor_state
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    IsMinor (State.reducedGraph hReduced) State.H := by
  classical
  apply IsMinor.of_branchSets
    (fun v : State.RowVertex => ({v.1} : Finset State.W))
  · intro v
    exact ⟨v.1, by simp⟩
  · intro v
    haveI : Nonempty {x : State.W | x ∈ ({v.1} : Finset State.W)} :=
      ⟨⟨v.1, by simp⟩⟩
    haveI : Subsingleton
        {x : State.W | x ∈ ({v.1} : Finset State.W)} := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : x.1 = v.1 := by simpa using x.2
      have hy : y.1 = v.1 := by simpa using y.2
      exact hx.trans hy.symm
    exact _root_.SimpleGraph.Connected.of_subsingleton
  · intro u v huv
    simp [Finset.disjoint_left, huv]
  · intro u v huv
    refine ⟨u.1, by simp, v.1, by simp, ?_⟩
    exact State.reducedGraph_le_induced hReduced huv

theorem reducedGraph_isMinor
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced) :
    IsMinor (State.reducedGraph hReduced) G₀ :=
  (State.reducedGraph_isMinor_state hReduced).trans State.minor

/-- Map a path along an injective graph homomorphism.  This local version
avoids imposing a graph-embedding (edge-reflection) requirement on a spanning
subgraph inclusion. -/
def mapInjectiveHom
    {W Z : Type u} [DecidableEq W] [DecidableEq Z]
    {H : _root_.SimpleGraph W} {J : _root_.SimpleGraph Z}
    (P : GraphPath H) (f : H →g J) (hf : Function.Injective f) :
    GraphPath J where
  source := f P.source
  target := f P.target
  walk := P.walk.map f
  isPath :=
    _root_.SimpleGraph.Walk.map_isPath_of_injective hf P.isPath

@[simp] theorem mapInjectiveHom_vertexSet
    {W Z : Type u} [DecidableEq W] [DecidableEq Z]
    {H : _root_.SimpleGraph W} {J : _root_.SimpleGraph Z}
    (P : GraphPath H) (f : H →g J) (hf : Function.Injective f) :
    (mapInjectiveHom P f hf).vertexSet =
      P.vertexSet.image f := by
  classical
  ext z
  simp [mapInjectiveHom, GraphPath.vertexSet,
    _root_.SimpleGraph.Walk.support_map]

/-- Lift a candidate linkage in `H'' - e` back to the contraction state
`H - e`.  The endpoint sets become the original `Arow,Brow`, exactly as
required by the transported Observation 4.3 bound. -/
noncomputable def liftDeletedPacking
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced)
    (e : Sym2 State.RowVertex)
    (L : PathPacking
      ((State.reducedGraph hReduced).deleteEdges
        ({e} : Set (Sym2 State.RowVertex)))
      (PathPacking.subtypeFinset State.Arow
        State.row.toPathPacking.vertexSet State.Arow_subset_row_vertexSet)
      (PathPacking.subtypeFinset State.Brow
        State.row.toPathPacking.vertexSet State.Brow_subset_row_vertexSet)) :
    PathPacking
      (State.H.deleteEdges
        ({Sym2.map Subtype.val e} : Set (Sym2 State.W)))
      State.Arow State.Brow := by
  classical
  let f :
      ((State.reducedGraph hReduced).deleteEdges
          ({e} : Set (Sym2 State.RowVertex))) →g
        (State.H.deleteEdges
          ({Sym2.map Subtype.val e} : Set (Sym2 State.W))) :=
    { toFun := Subtype.val
      map_rel' := by
        intro u v huv
        rw [_root_.SimpleGraph.deleteEdges_adj] at huv ⊢
        refine ⟨State.reducedGraph_le_induced hReduced huv.1, ?_⟩
        intro hdeleted
        apply huv.2
        simp only [Set.mem_singleton_iff] at hdeleted ⊢
        apply Sym2.map.injective Subtype.val_injective
        simpa using hdeleted }
  exact
    { Index := L.Index
      path := fun i => mapInjectiveHom (L.path i) f Subtype.val_injective
      connects := by
        intro i
        rcases L.connects i with h | h
        · exact Or.inl
            ⟨(PathPacking.mem_subtypeFinset
                State.Arow_subset_row_vertexSet _).1 h.1,
              (PathPacking.mem_subtypeFinset
                State.Brow_subset_row_vertexSet _).1 h.2⟩
        · exact Or.inr
            ⟨(PathPacking.mem_subtypeFinset
                State.Brow_subset_row_vertexSet _).1 h.1,
              (PathPacking.mem_subtypeFinset
                State.Arow_subset_row_vertexSet _).1 h.2⟩
      node_disjoint := by
        intro i j hij
        rw [GraphPath.NodeDisjoint, mapInjectiveHom_vertexSet,
          mapInjectiveHom_vertexSet, Finset.disjoint_left]
        intro v hvi hvj
        rcases Finset.mem_image.mp hvi with ⟨x, hxi, hxv⟩
        rcases Finset.mem_image.mp hvj with ⟨y, hyj, hyv⟩
        have hxy : x = y :=
          Subtype.val_injective (hxv.trans hyv.symm)
        subst y
        exact Finset.disjoint_left.mp (L.node_disjoint hij) hxi hyj }

@[simp] theorem liftDeletedPacking_card
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced)
    (e : Sym2 State.RowVertex)
    (L : PathPacking
      ((State.reducedGraph hReduced).deleteEdges
        ({e} : Set (Sym2 State.RowVertex)))
      (PathPacking.subtypeFinset State.Arow
        State.row.toPathPacking.vertexSet State.Arow_subset_row_vertexSet)
      (PathPacking.subtypeFinset State.Brow
        State.row.toPathPacking.vertexSet State.Brow_subset_row_vertexSet)) :
    (State.liftDeletedPacking hReduced e L).card = L.card := rfl

/-- The row linkage in the reduced support is unique.  The proof is exactly
the last paragraph of Observation 4.4: equal component counts give the
missing-row-edge property, and the transported Observation 4.3 bound rules
out a full linkage after that edge is deleted. -/
theorem reducedRow_isUniqueLinkage
    (State : Observation44State G₀ D N Kcard)
    (hReduced : State.IsReduced)
    (hN : 0 < N) :
    (State.reducedRow hReduced).IsUniqueLinkage := by
  classical
  let R := State.reducedRow hReduced
  apply R.isUniqueLinkage_of_edge_deletion_bound
    (State.reducedRow_spansVertices hReduced)
    (by simpa [R] using hN)
  · intro R' hne
    by_contra hmissing
    push_neg at hmissing
    have hsub :
        R.toPathPacking.edgeSet ⊆ R'.toPathPacking.edgeSet :=
      fun e he => hmissing e he
    have hRvertices :
        R.toPathPacking.vertexSet =
          (Finset.univ : Finset State.RowVertex) := by
      apply Finset.eq_univ_of_forall
      exact State.reducedRow_spansVertices hReduced
    have hR'vertices :
        R'.toPathPacking.vertexSet.card ≤
          R.toPathPacking.vertexSet.card := by
      rw [hRvertices]
      exact Finset.card_le_univ _
    have hR'card : R'.card = R.card := by
      exact R'.card_eq_left_card.trans R.card_eq_left_card.symm
    have hRcount :=
      Lax17Proofs.SimpleGraph.Section4Reduction.PathPacking.edgeSet_card_add_card_eq_vertexSet_card
        R.toPathPacking
    have hR'count :=
      Lax17Proofs.SimpleGraph.Section4Reduction.PathPacking.edgeSet_card_add_card_eq_vertexSet_card
        R'.toPathPacking
    have hedgeCard :
        R'.toPathPacking.edgeSet.card ≤
          R.toPathPacking.edgeSet.card := by
      change R'.toPathPacking.card = R.toPathPacking.card at hR'card
      omega
    have heq :
        R.toPathPacking.edgeSet = R'.toPathPacking.edgeSet :=
      Finset.eq_of_subset_of_card_le hsub hedgeCard
    exact hne heq.symm
  · intro e heRow L
    rcases R.toPathPacking.mem_edgeSet.1 heRow with ⟨i, hei⟩
    have heiInduced :
        e ∈ (State.rowInduced.path i).edgeSet := by
      simpa [R, reducedRow, PerfectPathPacking.inSpanningGraph,
        PerfectPathPacking.mapLe, PathPacking.inSpanningGraph,
        PathPacking.mapLe, PathPacking.transfer] using hei
    have heiBase :
        Sym2.map Subtype.val e ∈ (State.row.path i).edgeSet := by
      exact
        (GraphPath.mem_induce_edgeSet
          (State.row.path i) State.row.toPathPacking.vertexSet
          (State.row.toPathPacking.path_vertexSet_subset_vertexSet i) e).1
          (by simpa [rowInduced] using heiInduced)
    have heStateRow :
        Sym2.map Subtype.val e ∈ State.row.toPathPacking.edgeSet :=
      State.row.toPathPacking.mem_edgeSet.2 ⟨i, heiBase⟩
    have heNotOriginal :
        Sym2.map Subtype.val e ∉
          State.originalQ.toPathPacking.edgeSet :=
      hReduced.1 _ heStateRow
    have hbound :=
      State.deletion_bound (Sym2.map Subtype.val e)
        heStateRow heNotOriginal
        (State.liftDeletedPacking hReduced e L)
    rw [State.row_card] at hbound
    simpa [R, State.reducedRow_card hReduced] using hbound

end Observation44State

namespace PseudoGrid

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D : ℕ}
variable {P : PerfectPathPacking G A B}
variable {Q : PerfectPathPacking G A X}

/-- Property I1 gives `D` distinct row paths met by every retained auxiliary
path. -/
theorem goodQPathPackingInHPrime_metRows_card
    (Gamma : PseudoGrid G A B X g D P Q)
    (j : Gamma.goodQPathPackingInHPrime.Index) :
    D ≤
      ((Finset.univ : Finset Gamma.rowPerfectPackingInHPrime.Index).filter
        fun r =>
          ¬ Disjoint
            (Gamma.goodQPathPackingInHPrime.path j).vertexSet
            (Gamma.rowPerfectPackingInHPrime.path r).vertexSet).card := by
  classical
  let pick : Fin D → Gamma.rowPerfectPackingInHPrime.Index := fun i =>
    ⟨Classical.choose
        (Gamma.goodQPathPacking_intersects_row j i),
      Finset.mem_biUnion.2
        ⟨i, by simp,
          (Classical.choose_spec
            (Gamma.goodQPathPacking_intersects_row j i)).1⟩⟩
  have hpick_meets :
      ∀ i : Fin D,
        ¬ Disjoint
          (Gamma.goodQPathPackingInHPrime.path j).vertexSet
          (Gamma.rowPerfectPackingInHPrime.path (pick i)).vertexSet := by
    intro i
    have hmeet :=
      (Classical.choose_spec
        (Gamma.goodQPathPacking_intersects_row j i)).2
    intro hdisjoint
    apply hmeet
    simpa [pick, PseudoGrid.goodQPathPackingInHPrime,
      PseudoGrid.rowPerfectPackingInHPrime,
      PerfectPathPacking.mapLe, PerfectPathPacking.inSpanningGraph,
      PathPacking.mapLe, PathPacking.inSpanningGraph, PathPacking.transfer,
      PseudoGrid.goodQPathPacking, PseudoGrid.rowPerfectPacking] using
        hdisjoint.symm
  have hpick_injective : Function.Injective pick := by
    intro i k hik
    by_contra hne
    have hp :
        (pick i).1 ∈ Gamma.reserved i :=
      (Classical.choose_spec
        (Gamma.goodQPathPacking_intersects_row j i)).1
    have hpk :
        (pick k).1 ∈ Gamma.reserved k :=
      (Classical.choose_spec
        (Gamma.goodQPathPacking_intersects_row j k)).1
    exact Finset.disjoint_left.mp (Gamma.reserved_disjoint hne)
      hp (by simpa [hik] using hpk)
  let rows :=
    (Finset.univ : Finset Gamma.rowPerfectPackingInHPrime.Index).filter
      fun r =>
        ¬ Disjoint
          (Gamma.goodQPathPackingInHPrime.path j).vertexSet
          (Gamma.rowPerfectPackingInHPrime.path r).vertexSet
  have himage :
      (Finset.univ : Finset (Fin D)).image pick ⊆ rows := by
    intro r hr
    rcases Finset.mem_image.1 hr with ⟨i, _hi, rfl⟩
    exact Finset.mem_filter.2 ⟨by simp, hpick_meets i⟩
  calc
    D = ((Finset.univ : Finset (Fin D)).image pick).card := by
      rw [Finset.card_image_iff.2 hpick_injective.injOn]
      simp
    _ ≤ rows.card := Finset.card_le_card himage
    _ = _ := rfl

/-- The initial state before either contraction loop. -/
noncomputable def observation44InitialState
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q) :
    Observation44State G D Gamma.rowPacking.card
      Gamma.goodQPathPacking.card where
  W := V
  H := Gamma.hPrimeGraph
  K := G
  H_le_K := Gamma.hPrimeGraph_le
  Arow := P.sourceSet Gamma.reservedUnion
  Brow := P.targetSet Gamma.reservedUnion
  Aq := A
  Bq := X
  Sq := Finset.univ
  Tq := X
  row := Gamma.rowPerfectPackingInHPrime
  originalQ := Q
  retainedQ := Gamma.goodQPathPackingInHPrime
  parent := fun j =>
    P.matchedSourceIndex Q (Gamma.parent j.1)
  parent_injective := by
    intro i j hij
    apply Subtype.ext
    apply Gamma.parent_injective
    exact P.matchedSourceIndex_injective Q hij
  retained_vertex_subset := by
    intro j
    simpa [PseudoGrid.goodQPathPackingInHPrime,
      PathPacking.mapLe, PathPacking.inSpanningGraph, PathPacking.transfer,
      PseudoGrid.goodQPathPacking] using
      Gamma.qPath_subset_matched j.1
  retained_edge_subset := by
    intro j
    simpa [PseudoGrid.goodQPathPackingInHPrime,
      PathPacking.mapLe, PathPacking.inSpanningGraph, PathPacking.transfer,
      PseudoGrid.goodQPathPacking] using
      Gamma.qPath_edgeSet_subset_matched j.1
  minor := Gamma.hPrimeGraph_isMinor
  row_card := by
    calc
      Gamma.rowPerfectPackingInHPrime.card =
          Gamma.rowPerfectPacking.card := by simp
      _ = Gamma.rowPacking.card := by
        rw [Gamma.rowPerfectPacking_card, Gamma.rowPacking_card]
  retained_card := by simp
  dense := goodQPathPackingInHPrime_metRows_card Gamma
  deletion_bound := by
    intro e heR heQ L
    apply Gamma.observation_four_three_edge_deletion_bound hminimal e
    · rcases
        (Gamma.rowPerfectPackingInHPrime.toPathPacking.mem_edgeSet).1 heR with
          ⟨i, hei⟩
      rw [PathPacking.mem_edgeSet]
      refine ⟨i, ?_⟩
      have hpath :
          (Gamma.rowPerfectPackingInHPrime.path i).edgeSet =
            (Gamma.rowPacking.path i).edgeSet := by
        simp [PseudoGrid.rowPerfectPackingInHPrime,
          PseudoGrid.rowPerfectPacking, PseudoGrid.rowPacking,
          PerfectPathPacking.mapLe, PerfectPathPacking.inSpanningGraph,
          PerfectPathPacking.transfer, PerfectPathPacking.restrictIndexSet,
          PathPacking.mapLe, PathPacking.inSpanningGraph,
          PathPacking.transfer, PathPacking.restrictIndexSet,
          GraphPath.mapLe_edgeSet, GraphPath.transfer_edgeSet]
      exact hpath ▸ hei
    · simpa using heQ

/-- The source-faithful contraction conclusion of Observation 4.4.  The
returned state still contains the actual retained auxiliary paths, preserves
their original-`Q` parents and density, and is a minor of the input graph. -/
theorem exists_observation44_reduced_state
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hD : 0 < D) :
    ∃ State :
        Observation44State G D Gamma.rowPacking.card
          Gamma.goodQPathPacking.card,
      State.IsReduced :=
  (observation44InitialState Gamma hminimal).exists_reduced_of_state hD

end PseudoGrid

end Section4Reduction

end SimpleGraph

end Lax17Proofs
