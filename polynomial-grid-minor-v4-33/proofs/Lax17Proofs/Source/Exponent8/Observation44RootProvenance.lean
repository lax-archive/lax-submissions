import Lax17Proofs.Source.Observation44Reduction
import Lax17Proofs.Source.Exponent8.LastHitCrossbar

namespace Lax17Proofs

/-!
# Root provenance through Chuzhoy--Tan Observation 4.4

The ordinary `Observation44State` deliberately stores only information needed
by the degree-ten Section 4 argument.  In particular, its finite minimization
may choose any state satisfying the numerical invariant, and the state does
not remember incidence with the fixed paths before contraction.

The Section 5 last-hit argument needs more: every final row--auxiliary
incidence must agree with incidence between the corresponding paths in the
initial pseudo-grid.  This file enriches the state by exact incidence
provenance, proves that both legal Observation 4.4 contractions preserve it,
and will run the finite descent over enriched states rather than arbitrary
`Observation44State`s.

The root paths live in the original graph while a current state lives on a
nested edge-contraction type.  Consequently provenance is stated as an
equivalence of incidence propositions, not as a cross-type vertex-set
containment.
-/

namespace SimpleGraph
namespace Exponent8

open Section4Reduction
open TreewidthSparsifier

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D : ℕ}
variable {P : PerfectPathPacking G A B}
variable {Q : PerfectPathPacking G A X}

/-- An Observation 4.4 state together with fixed roots in the initial row and
retained auxiliary families.

Both root maps are equivalences because the two contraction operations
project every path and never discard or duplicate a row or retained
auxiliary path. -/
structure RootedObservation44State
    (Gamma : PseudoGrid G A B X g D P Q) where
  state :
    Observation44State G D Gamma.rowPacking.card
      Gamma.goodQPathPacking.card
  rowRoot :
    state.row.Index ≃ Gamma.rowPerfectPackingInHPrime.Index
  qRoot :
    state.retainedQ.Index ≃ Gamma.goodQPathPackingInHPrime.Index
  hit_iff_root :
    ∀ (r : state.row.Index) (q : state.retainedQ.Index),
      PathPacking.PathsIntersect
          (state.row.path r) (state.retainedQ.path q) ↔
        PathPacking.PathsIntersect
          (Gamma.rowPerfectPackingInHPrime.path (rowRoot r))
          (Gamma.goodQPathPackingInHPrime.path (qRoot q))

namespace RootedObservation44State

variable {Gamma : PseudoGrid G A B X g D P Q}

attribute [instance] Section4Reduction.Observation44State.wFintype
attribute [instance] Section4Reduction.Observation44State.wDecidableEq

/-- The initial Observation 4.4 state has identity root maps. -/
noncomputable def initial
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q) :
    RootedObservation44State Gamma where
  state := Section4Reduction.PseudoGrid.observation44InitialState
    Gamma hminimal
  rowRoot := Equiv.refl _
  qRoot := Equiv.refl _
  hit_iff_root := by
    intro r q
    rfl

/-! ## Exact incidence through one legal contraction -/

/-- Contracting an edge of a row cannot create or destroy incidence between
the projected row packing and the projected retained auxiliary packing.

The retained projection may be either of the two cases used by the source
proof.  Exactness follows from the fact that both contraction endpoints lie
on one row: any pair of old vertices newly identified by the projection
already meets that row at one of the two endpoints. -/
theorem contractCommonEdge_hit_iff
    (State :
      Observation44State G D Gamma.rowPacking.card
        Gamma.goodQPathPacking.card)
    {a b : State.W} (hab : State.H.Adj a b)
    (r₀ : State.row.Index)
    (hrow : s(a, b) ∈ (State.row.path r₀).edgeSet)
    (q₀ : State.originalQ.Index)
    (hq : s(a, b) ∈ (State.originalQ.path q₀).edgeSet)
    (Proj : State.RetainedProjection hab)
    (r : State.row.Index) (q : Proj.projected.Index) :
    PathPacking.PathsIntersect
        ((State.contractCommonEdge hab r₀ hrow q₀ hq Proj).row.path r)
        ((State.contractCommonEdge hab r₀ hrow q₀ hq Proj).retainedQ.path q) ↔
      PathPacking.PathsIntersect
        (State.row.path r) (State.retainedQ.path (Proj.oldIndex q)) := by
  classical
  let projection :=
    EdgeContractVertex.projection (V := State.W) (u := a) (v := b)
  have hrowImage :
      ((State.contractCommonEdge hab r₀ hrow q₀ hq Proj).row.path r).vertexSet =
        (State.row.path r).vertexSet.image projection := by
    dsimp [Observation44State.contractCommonEdge, projection]
    by_cases hr : r = r₀
    · subst r
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_edge_mem
        (G := State.H) (hab := hab) (State.row.path r₀) hrow
    · have haNot : a ∉ (State.row.path r).vertexSet := by
        intro ha
        exact Finset.disjoint_left.mp (State.row.node_disjoint hr) ha
          ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).1
      exact ProjectionWalk.toGraphPath_vertexSet_eq_image_of_left_not_mem
        (G := State.H) (hab := hab) (State.row.path r) haNot
  have hqImage :
      ((State.contractCommonEdge hab r₀ hrow q₀ hq Proj).retainedQ.path q).vertexSet =
        (State.retainedQ.path (Proj.oldIndex q)).vertexSet.image projection := by
    simpa [Observation44State.contractCommonEdge, projection] using
      Proj.vertex_image q
  rw [PathPacking.PathsIntersect, PathPacking.PathsIntersect,
    hrowImage, hqImage]
  constructor
  · intro h
    rcases Finset.not_disjoint_iff.mp h with ⟨z, hzRow, hzQ⟩
    rcases Finset.mem_image.mp hzRow with ⟨x, hxRow, hxz⟩
    rcases Finset.mem_image.mp hzQ with ⟨y, hyQ, hyz⟩
    have hproj : projection x = projection y := hxz.trans hyz.symm
    apply Finset.not_disjoint_iff.mpr
    rcases
        EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := State.W) (u := a) (v := b) hproj with hxy | hend
    · subst y
      exact ⟨x, hxRow, hyQ⟩
    · have hxRoot : x ∈ (State.row.path r₀).vertexSet := by
        rcases hend.1 with rfl | rfl
        · exact
            ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).1
        · exact
            ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).2
      by_cases hr : r = r₀
      · subst r
        have hyRoot : y ∈ (State.row.path r₀).vertexSet := by
          rcases hend.2 with rfl | rfl
          · exact
              ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).1
          · exact
              ((State.row.path r₀).endpoints_mem_vertexSet_of_edgeSet hrow).2
        exact ⟨y, hyRoot, hyQ⟩
      · exact
          (Finset.disjoint_left.mp
            (State.row.node_disjoint hr) hxRow hxRoot).elim
  · intro h
    rcases Finset.not_disjoint_iff.mp h with ⟨x, hxRow, hxQ⟩
    exact Finset.not_disjoint_iff.mpr
      ⟨projection x,
        Finset.mem_image.mpr ⟨x, hxRow, rfl⟩,
        Finset.mem_image.mpr ⟨x, hxQ, rfl⟩⟩

/-- Contracting an edge of a retained auxiliary path from an off-row endpoint
also preserves exact row--auxiliary incidence.

If projection identifies a row vertex with a different auxiliary vertex,
the row vertex must be `b` because `a` lies on no row.  The auxiliary vertex
is `a` or `b`; in the former case node-disjointness identifies its path with
the unique retained path containing the contracted edge, which also contains
`b`. -/
theorem contractOffRowEdge_hit_iff
    (State :
      Observation44State G D Gamma.rowPacking.card
        Gamma.goodQPathPacking.card)
    {a b : State.W} (hab : State.H.Adj a b)
    (haRow : a ∉ State.row.toPathPacking.vertexSet)
    (i₀ : State.retainedQ.Index)
    (hret : s(a, b) ∈ (State.retainedQ.path i₀).edgeSet)
    (q₀ : State.originalQ.Index)
    (hq : s(a, b) ∈ (State.originalQ.path q₀).edgeSet)
    (hparent : State.parent i₀ = q₀)
    (r : State.row.Index)
    (q :
      (Observation44State.RetainedProjection.ofSamePath
        State hab i₀ hret).projected.Index) :
    PathPacking.PathsIntersect
        ((State.contractOffRowEdge
          hab haRow i₀ hret q₀ hq hparent).row.path r)
        ((State.contractOffRowEdge
          hab haRow i₀ hret q₀ hq hparent).retainedQ.path q) ↔
      PathPacking.PathsIntersect
        (State.row.path r)
        (State.retainedQ.path
          ((Observation44State.RetainedProjection.ofSamePath
            State hab i₀ hret).oldIndex q)) := by
  classical
  let projection :=
    EdgeContractVertex.projection (V := State.W) (u := a) (v := b)
  let Proj : State.RetainedProjection hab :=
    Observation44State.RetainedProjection.ofSamePath State hab i₀ hret
  have hrowImage :
      ((State.contractOffRowEdge
        hab haRow i₀ hret q₀ hq hparent).row.path r).vertexSet =
          (State.row.path r).vertexSet.image projection := by
    dsimp [Observation44State.contractOffRowEdge, projection]
    apply ProjectionWalk.toGraphPath_vertexSet_eq_image_of_left_not_mem
      (G := State.H) (hab := hab)
    intro ha
    exact haRow
      ((State.row.toPathPacking.mem_vertexSet).2 ⟨r, ha⟩)
  have hqImage :
      ((State.contractOffRowEdge
        hab haRow i₀ hret q₀ hq hparent).retainedQ.path q).vertexSet =
          (State.retainedQ.path (Proj.oldIndex q)).vertexSet.image projection := by
    simpa [Observation44State.contractOffRowEdge, Proj, projection] using
      Proj.vertex_image q
  rw [PathPacking.PathsIntersect, PathPacking.PathsIntersect,
    hrowImage, hqImage]
  constructor
  · intro h
    rcases Finset.not_disjoint_iff.mp h with ⟨z, hzRow, hzQ⟩
    rcases Finset.mem_image.mp hzRow with ⟨x, hxRow, hxz⟩
    rcases Finset.mem_image.mp hzQ with ⟨y, hyQ, hyz⟩
    have hproj : projection x = projection y := hxz.trans hyz.symm
    apply Finset.not_disjoint_iff.mpr
    rcases
        EdgeContractVertex.eq_or_endpoint_pair_of_projection_eq
          (V := State.W) (u := a) (v := b) hproj with hxy | hend
    · subst y
      exact ⟨x, hxRow, hyQ⟩
    · have hxa : x ≠ a := by
        intro h
        subst x
        exact haRow
          ((State.row.toPathPacking.mem_vertexSet).2 ⟨r, hxRow⟩)
      have hxb : x = b := hend.1.resolve_left hxa
      subst x
      rcases hend.2 with hya | hyb
      · subst y
        have haI₀ :
            a ∈ (State.retainedQ.path i₀).vertexSet :=
          ((State.retainedQ.path i₀).endpoints_mem_vertexSet_of_edgeSet hret).1
        have hqi : Proj.oldIndex q = i₀ := by
          by_contra hne
          exact Finset.disjoint_left.mp
            (State.retainedQ.node_disjoint hne) hyQ haI₀
        rw [hqi]
        exact
          ⟨b, hxRow,
            ((State.retainedQ.path i₀).endpoints_mem_vertexSet_of_edgeSet
              hret).2⟩
      · subst y
        exact ⟨b, hxRow, hyQ⟩
  · intro h
    rcases Finset.not_disjoint_iff.mp h with ⟨x, hxRow, hxQ⟩
    exact Finset.not_disjoint_iff.mpr
      ⟨projection x,
        Finset.mem_image.mpr ⟨x, hxRow, rfl⟩,
        Finset.mem_image.mpr ⟨x, hxQ, rfl⟩⟩

/-! ## Rooted transition constructors -/

/-- Lift the common row--auxiliary edge contraction to a rooted state. -/
noncomputable def contractCommonEdge
    (Root : RootedObservation44State Gamma)
    {a b : Root.state.W} (hab : Root.state.H.Adj a b)
    (r₀ : Root.state.row.Index)
    (hrow : s(a, b) ∈ (Root.state.row.path r₀).edgeSet)
    (q₀ : Root.state.originalQ.Index)
    (hq : s(a, b) ∈ (Root.state.originalQ.path q₀).edgeSet)
    (Proj : Root.state.RetainedProjection hab) :
    RootedObservation44State Gamma where
  state :=
    Root.state.contractCommonEdge hab r₀ hrow q₀ hq Proj
  rowRoot := Root.rowRoot
  qRoot :=
    (Equiv.ofBijective Proj.oldIndex Proj.oldIndex_bijective).trans
      Root.qRoot
  hit_iff_root := by
    intro r q
    exact
      (contractCommonEdge_hit_iff
        Root.state hab r₀ hrow q₀ hq Proj r q).trans
        (Root.hit_iff_root r (Proj.oldIndex q))

/-- Lift the legal off-row auxiliary contraction to a rooted state. -/
noncomputable def contractOffRowEdge
    (Root : RootedObservation44State Gamma)
    {a b : Root.state.W} (hab : Root.state.H.Adj a b)
    (haRow : a ∉ Root.state.row.toPathPacking.vertexSet)
    (i₀ : Root.state.retainedQ.Index)
    (hret : s(a, b) ∈ (Root.state.retainedQ.path i₀).edgeSet)
    (q₀ : Root.state.originalQ.Index)
    (hq : s(a, b) ∈ (Root.state.originalQ.path q₀).edgeSet)
    (hparent : Root.state.parent i₀ = q₀) :
    RootedObservation44State Gamma := by
  let Proj : Root.state.RetainedProjection hab :=
    Observation44State.RetainedProjection.ofSamePath
      Root.state hab i₀ hret
  refine
    { state :=
        Root.state.contractOffRowEdge
          hab haRow i₀ hret q₀ hq hparent
      rowRoot := Root.rowRoot
      qRoot :=
        (Equiv.ofBijective Proj.oldIndex Proj.oldIndex_bijective).trans
          Root.qRoot
      hit_iff_root := ?_ }
  intro r q
  exact
    (contractOffRowEdge_hit_iff
      Root.state hab haRow i₀ hret q₀ hq hparent r q).trans
      (Root.hit_iff_root r (Proj.oldIndex q))

/-! ## Rooted finite descent -/

/-- The first Observation 4.4 move can be performed without forgetting the
fixed initial paths. -/
theorem exists_smaller_of_common_edge
    (Root : RootedObservation44State Gamma)
    {e : Sym2 Root.state.W}
    (heRow : e ∈ Root.state.row.toPathPacking.edgeSet)
    (heQ : e ∈ Root.state.originalQ.toPathPacking.edgeSet) :
    ∃ Next : RootedObservation44State Gamma,
      Fintype.card Next.state.W < Fintype.card Root.state.W := by
  classical
  let a : Root.state.W := e.out.1
  let b : Root.state.W := e.out.2
  have heq : s(a, b) = e := e.out_eq
  rcases (Root.state.row.toPathPacking.mem_edgeSet).1 heRow with
    ⟨r₀, hr₀⟩
  rcases (Root.state.originalQ.toPathPacking.mem_edgeSet).1 heQ with
    ⟨q₀, hq₀⟩
  have hrow : s(a, b) ∈ (Root.state.row.path r₀).edgeSet := by
    simpa [heq] using hr₀
  have hq : s(a, b) ∈ (Root.state.originalQ.path q₀).edgeSet := by
    simpa [heq] using hq₀
  have hab : Root.state.H.Adj a b :=
    Root.state.row.edgeSet_subset_edgeSet
      ((Root.state.row.toPathPacking.mem_edgeSet).2 ⟨r₀, hrow⟩)
  by_cases hret : s(a, b) ∈ Root.state.retainedQ.edgeSet
  · rcases (Root.state.retainedQ.mem_edgeSet).1 hret with ⟨i₀, hi₀⟩
    let Proj : Root.state.RetainedProjection hab :=
      Observation44State.RetainedProjection.ofSamePath
        Root.state hab i₀ hi₀
    let Next :=
      contractCommonEdge Root hab r₀ hrow q₀ hq Proj
    refine ⟨Next, ?_⟩
    exact EdgeContractVertex.card_lt_of_ne hab.ne
  · rcases
      PathPacking.left_or_right_not_mem_vertexSet_of_subpaths
        Root.state.retainedQ Root.state.originalQ.toPathPacking
        Root.state.H_le_K Root.state.parent Root.state.parent_injective
        Root.state.retained_vertex_subset Root.state.retained_edge_subset
        hq hret with ha | hb
    · let Proj : Root.state.RetainedProjection hab :=
        Observation44State.RetainedProjection.ofLeftUnused
          Root.state hab ha
      let Next :=
        contractCommonEdge Root hab r₀ hrow q₀ hq Proj
      refine ⟨Next, ?_⟩
      exact EdgeContractVertex.card_lt_of_ne hab.ne
    · have hba : Root.state.H.Adj b a := hab.symm
      have hrow' :
          s(b, a) ∈ (Root.state.row.path r₀).edgeSet := by
        simpa only [Sym2.eq_swap] using hrow
      have hq' :
          s(b, a) ∈ (Root.state.originalQ.path q₀).edgeSet := by
        simpa only [Sym2.eq_swap] using hq
      let Proj : Root.state.RetainedProjection hba :=
        Observation44State.RetainedProjection.ofLeftUnused
          Root.state hba hb
      let Next :=
        contractCommonEdge Root hba r₀ hrow' q₀ hq' Proj
      refine ⟨Next, ?_⟩
      exact EdgeContractVertex.card_lt_of_ne hba.ne

/-- The second Observation 4.4 move can be performed without forgetting the
fixed initial paths. -/
theorem exists_smaller_of_off_row_vertex
    (Root : RootedObservation44State Gamma)
    (hD : 0 < D)
    {a : Root.state.W}
    (haRetained : a ∈ Root.state.retainedQ.vertexSet)
    (haRow : a ∉ Root.state.row.toPathPacking.vertexSet) :
    ∃ Next : RootedObservation44State Gamma,
      Fintype.card Next.state.W < Fintype.card Root.state.W := by
  classical
  rcases Root.state.retainedQ.mem_vertexSet.1 haRetained with
    ⟨i₀, hai₀⟩
  have hmetPos : 0 < (Root.state.metRows i₀).card :=
    hD.trans_le (Root.state.dense_metRows i₀)
  rcases Finset.card_pos.mp hmetPos with ⟨r, hr⟩
  have hmeet :
      ¬ Disjoint (Root.state.retainedQ.path i₀).vertexSet
        (Root.state.row.path r).vertexSet :=
    (Root.state.mem_metRows i₀ r).1 hr
  rcases Finset.not_disjoint_iff.1 hmeet with
    ⟨w, hwRetained, hwRow⟩
  have haw : a ≠ w := by
    intro haw
    subst w
    exact haRow
      (Root.state.row.toPathPacking.mem_vertexSet.2 ⟨r, hwRow⟩)
  have hnontrivial :
      (Root.state.retainedQ.path i₀).source ≠
        (Root.state.retainedQ.path i₀).target := by
    intro hst
    have haSource :=
      (Root.state.retainedQ.path i₀)
        |>.eq_source_of_source_eq_target_of_mem_vertexSet hst hai₀
    have hwSource :=
      (Root.state.retainedQ.path i₀)
        |>.eq_source_of_source_eq_target_of_mem_vertexSet hst hwRetained
    exact haw (haSource.trans hwSource.symm)
  rcases
      (Root.state.retainedQ.path i₀)
        |>.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
          hnontrivial hai₀ with
    ⟨e, heRetained, hae⟩
  rcases Sym2.mem_iff_exists.mp hae with ⟨b, rfl⟩
  have hab : Root.state.H.Adj a b :=
    Root.state.retainedQ.edgeSet_subset_edgeSet
      (Root.state.retainedQ.mem_edgeSet.2 ⟨i₀, heRetained⟩)
  have heOriginal :
      s(a, b) ∈
        (Root.state.originalQ.path (Root.state.parent i₀)).edgeSet :=
    Root.state.retained_edge_subset i₀ heRetained
  let Next :=
    contractOffRowEdge Root hab haRow i₀ heRetained
      (Root.state.parent i₀) heOriginal rfl
  refine ⟨Next, ?_⟩
  exact EdgeContractVertex.card_lt_of_ne hab.ne

/-- Finite minimization over rooted states.  Unlike minimization over bare
`Observation44State`s, every candidate in this search space carries an exact
incidence certificate relative to the fixed pseudo-grid paths. -/
theorem exists_reduced
    (Initial : RootedObservation44State Gamma)
    (hD : 0 < D) :
    ∃ Root : RootedObservation44State Gamma, Root.state.IsReduced := by
  classical
  let HasCard : ℕ → Prop := fun n =>
    ∃ Root : RootedObservation44State Gamma,
      Fintype.card Root.state.W = n
  have hExists : ∃ n : ℕ, HasCard n :=
    ⟨Fintype.card Initial.state.W, Initial, rfl⟩
  rcases Nat.find_spec hExists with ⟨Root, hRootCard⟩
  refine ⟨Root, ?_, ?_⟩
  · intro e heRow heOriginal
    rcases Root.exists_smaller_of_common_edge heRow heOriginal with
      ⟨Next, hNext⟩
    have hNextCandidate : HasCard (Fintype.card Next.state.W) :=
      ⟨Next, rfl⟩
    have hminimal :
        Nat.find hExists ≤ Fintype.card Next.state.W :=
      Nat.find_min' (H := hExists) hNextCandidate
    omega
  · intro a haRetained
    by_contra haRow
    rcases
        Root.exists_smaller_of_off_row_vertex hD haRetained haRow with
      ⟨Next, hNext⟩
    have hNextCandidate : HasCard (Fintype.card Next.state.W) :=
      ⟨Next, rfl⟩
    have hminimal :
        Nat.find hExists ≤ Fintype.card Next.state.W :=
      Nat.find_min' (H := hExists) hNextCandidate
    omega

/-- Observation 4.4 with exact source-path incidence provenance. -/
theorem exists_reduced_of_pseudoGrid
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hD : 0 < D) :
    ∃ Root : RootedObservation44State Gamma, Root.state.IsReduced :=
  (initial Gamma hminimal).exists_reduced hD

/-! ## Passing provenance to the reduced row-support graph -/

/-- Restricting a reduced state to the exact row-support subtype preserves
row--auxiliary incidence. -/
theorem reduced_hit_iff_state_hit
    (Root : RootedObservation44State Gamma)
    (hReduced : Root.state.IsReduced)
    (r : (Root.state.reducedRow hReduced).Index)
    (q : (Root.state.reducedRetained hReduced).Index) :
    PathPacking.PathsIntersect
        ((Root.state.reducedRow hReduced).path r)
        ((Root.state.reducedRetained hReduced).path q) ↔
      PathPacking.PathsIntersect
        (Root.state.row.path r) (Root.state.retainedQ.path q) := by
  classical
  rw [PathPacking.PathsIntersect, PathPacking.PathsIntersect,
    Finset.not_disjoint_iff, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨x, hxr, hxq⟩
    refine ⟨x.1, ?_, ?_⟩
    · have hxr' :
          x ∈
            (Root.state.rowInduced.path r).vertexSet := by
        simpa [Observation44State.reducedRow,
          PerfectPathPacking.inSpanningGraph, PerfectPathPacking.mapLe,
          PathPacking.inSpanningGraph, PathPacking.mapLe,
          PathPacking.transfer] using hxr
      exact
        (GraphPath.mem_induce_vertexSet
          (Root.state.row.path r)
          Root.state.row.toPathPacking.vertexSet
          (Root.state.row.toPathPacking.path_vertexSet_subset_vertexSet r)
          x).1 (by
            simpa [Observation44State.rowInduced] using hxr')
    · have hxq' :
          x ∈
            ((Root.state.retainedInduced hReduced).path q).vertexSet := by
        simpa [Observation44State.reducedRetained,
          PathPacking.inSpanningGraph, PathPacking.mapLe,
          PathPacking.transfer] using hxq
      exact
        (GraphPath.mem_induce_vertexSet
          (Root.state.retainedQ.path q)
          Root.state.row.toPathPacking.vertexSet
          (fun v hv => hReduced.2
            (Root.state.retainedQ.mem_vertexSet.2 ⟨q, hv⟩))
          x).1 (by
            simpa [Observation44State.retainedInduced] using hxq')
  · rintro ⟨x, hxr, hxq⟩
    have hxSupport : x ∈ Root.state.row.toPathPacking.vertexSet :=
      Root.state.row.toPathPacking.mem_vertexSet.2 ⟨r, hxr⟩
    let x' : Root.state.RowVertex := ⟨x, hxSupport⟩
    refine ⟨x', ?_, ?_⟩
    · simpa [x', Observation44State.reducedRow,
        Observation44State.rowInduced,
        PerfectPathPacking.inSpanningGraph, PerfectPathPacking.mapLe,
        PathPacking.inSpanningGraph, PathPacking.mapLe,
        PathPacking.transfer] using
          (GraphPath.mem_induce_vertexSet
            (Root.state.row.path r)
            Root.state.row.toPathPacking.vertexSet
            (Root.state.row.toPathPacking.path_vertexSet_subset_vertexSet r)
            x').2 hxr
    · simpa [x', Observation44State.reducedRetained,
        Observation44State.retainedInduced,
        PathPacking.inSpanningGraph, PathPacking.mapLe,
        PathPacking.transfer] using
          (GraphPath.mem_induce_vertexSet
            (Root.state.retainedQ.path q)
            Root.state.row.toPathPacking.vertexSet
            (fun v hv => hReduced.2
              (Root.state.retainedQ.mem_vertexSet.2 ⟨q, hv⟩))
            x').2 hxq

/-- Exact reduced incidence with the fixed initial pseudo-grid paths. -/
theorem reduced_hit_iff_root_hit
    (Root : RootedObservation44State Gamma)
    (hReduced : Root.state.IsReduced)
    (r : (Root.state.reducedRow hReduced).Index)
    (q : (Root.state.reducedRetained hReduced).Index) :
    PathPacking.PathsIntersect
        ((Root.state.reducedRow hReduced).path r)
        ((Root.state.reducedRetained hReduced).path q) ↔
      PathPacking.PathsIntersect
        (Gamma.rowPerfectPackingInHPrime.path (Root.rowRoot r))
        (Gamma.goodQPathPackingInHPrime.path (Root.qRoot q)) :=
  (Root.reduced_hit_iff_state_hit hReduced r q).trans
    (Root.hit_iff_root r q)

@[simp] theorem rootRow_vertexSet
    (Root : RootedObservation44State Gamma)
    (r : Root.state.row.Index) :
    (Gamma.rowPerfectPackingInHPrime.path (Root.rowRoot r)).vertexSet =
      (P.path (Root.rowRoot r).1).vertexSet := by
  simp [PseudoGrid.rowPerfectPackingInHPrime,
    PseudoGrid.rowPerfectPacking, PerfectPathPacking.inSpanningGraph,
    PerfectPathPacking.mapLe, PathPacking.inSpanningGraph,
    PathPacking.mapLe, PathPacking.transfer,
    PerfectPathPacking.restrictIndexSet]

@[simp] theorem rootQ_vertexSet
    (Root : RootedObservation44State Gamma)
    (q : Root.state.retainedQ.Index) :
    (Gamma.goodQPathPackingInHPrime.path (Root.qRoot q)).vertexSet =
      (Gamma.qPath (Root.qRoot q).1).vertexSet := by
  simp [PseudoGrid.goodQPathPackingInHPrime,
    PseudoGrid.goodQPathPacking, PathPacking.inSpanningGraph,
    PathPacking.mapLe, PathPacking.transfer]

/-- Root incidence rewritten entirely in the original graph. -/
theorem root_hit_iff_original_hit
    (Root : RootedObservation44State Gamma)
    (r : Root.state.row.Index)
    (q : Root.state.retainedQ.Index) :
    PathPacking.PathsIntersect
        (Gamma.rowPerfectPackingInHPrime.path (Root.rowRoot r))
        (Gamma.goodQPathPackingInHPrime.path (Root.qRoot q)) ↔
      PathPacking.PathsIntersect
        (P.path (Root.rowRoot r).1)
        (Gamma.qPath (Root.qRoot q).1) := by
  simp only [PathPacking.PathsIntersect, Root.rootRow_vertexSet,
    Root.rootQ_vertexSet]

/-- Construct the last-hit provenance interface directly from a rooted
Observation 4.4 reduction.

The represented source segment is deliberately the whole source row.  For a
localized contracted path, `PathInSlice` first identifies a hit on the
contracted strict slice with a hit on the full contracted row; rooted
incidence then identifies that hit with the full source row.  This is exactly
the information used by the last-hit fibre count and avoids attempting to
lift contraction fibres through slice boundaries. -/
noncomputable def toSliceLocalizationInvariant_fullRows
    (Root : RootedObservation44State Gamma)
    (hReduced : Root.state.IsReduced)
    {M : ℕ}
    (sigma : PathSlicing (Root.state.reducedRow hReduced) M)
    (i : Fin M)
    (localizedQ :
      Finset (Root.state.reducedRetained hReduced).Index)
    (hlocalized :
      localizedQ ⊆
        sigma.pathsInSlice (Root.state.reducedRetained hReduced) i)
    (hXdisjoint :
      ∀ p : P.Index, Disjoint X (P.path p).vertexSet) :
    SliceLocalizationInvariant
      G (Root.state.reducedGraph hReduced) A B X P Q
      (Root.state.reducedRow hReduced)
      (Root.state.reducedRetained hReduced) sigma i where
  rowRoot := fun r => (Root.rowRoot r).1
  rowRoot_injective := by
    intro r s hrs
    apply Root.rowRoot.injective
    exact Subtype.ext hrs
  uncontractedSegment := fun r => P.path (Root.rowRoot r).1
  segment_vertexSet_subset_main := by
    intro r
    exact Finset.Subset.rfl
  uncontractedQ := fun q => Gamma.qPath (Root.qRoot q).1
  qParent := fun q =>
    P.matchedSourceIndex Q (Gamma.parent (Root.qRoot q).1)
  qParent_injective := by
    intro q q' hqq'
    apply Root.qRoot.injective
    apply Subtype.ext
    apply Gamma.parent_injective
    exact P.matchedSourceIndex_injective Q hqq'
  uncontractedQ_vertexSet_subset_parent := by
    intro q
    exact Gamma.qPath_subset_matched (Root.qRoot q).1
  uncontractedQ_edgeSet_subset_parent := by
    intro q
    exact Gamma.qPath_edgeSet_subset_matched (Root.qRoot q).1
  localizedQ := localizedQ
  localizedQ_subset_slice := hlocalized
  uncontractedQ_exactlyOneEndpointIn_X := by
    intro q
    exact Gamma.qPath_exactly_one_endpoint_in_X (Root.qRoot q).1
  contracted_hit_iff_uncontracted_hit := by
    intro r q hq
    exact
      (sigma.sliceSegmentIntersectsPath_iff_pathsIntersect_of_mem_pathsInSlice
        (Root.state.reducedRetained hReduced) (hlocalized hq)).trans
        ((Root.reduced_hit_iff_root_hit hReduced r q).trans
          (Root.root_hit_iff_original_hit r q))
  main_hit_localized := by
    intro r q x hq hxQ hxMain
    exact hxMain
  X_disjoint_main := by
    intro r
    exact hXdisjoint (Root.rowRoot r).1

end RootedObservation44State

end Exponent8
end SimpleGraph

end Lax17Proofs
