import Lax17Proofs.Source.ChekuriChuzhoySection5SplitOff

namespace Lax17Proofs

universe u v w

/-!
# Contraction of a vertex set for Mader split-off bookkeeping

This module contracts a nonempty finite vertex set to one vertex in a finite
edge-indexed multigraph.  Named edge copies are retained unless their two
endpoints have the same image, in which case the resulting loop is discarded.
Parallel surviving copies remain distinct.

The results are finite bookkeeping for applying split-off operations away from
the contracted set.  In particular, no Mader admissibility statement is used
or proved here.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

/-! ## Vertices after contracting a finite set -/

/-- A quotient-like vertex type in which `T` is represented by `merged` and
each vertex outside `T` is retained separately. -/
inductive SetContractVertex (W : Type u) (T : Finset W) where
  | merged : SetContractVertex W T
  | keep : {w : W // w ∉ T} -> SetContractVertex W T
deriving DecidableEq

namespace SetContractVertex

variable {W : Type u} {T : Finset W}

noncomputable instance [Fintype W] [DecidableEq W] :
    Fintype (SetContractVertex W T) := by
  classical
  exact Fintype.ofEquiv
    (Unit ⊕ {w : W // w ∉ T})
    { toFun := fun x =>
        match x with
        | Sum.inl _ => merged
        | Sum.inr w => keep w
      invFun := fun x =>
        match x with
        | merged => Sum.inl ()
        | keep w => Sum.inr w
      left_inv := by
        intro x
        cases x with
        | inl x => cases x; rfl
        | inr x => rfl
      right_inv := by
        intro x
        cases x <;> rfl }

/-- Project an original vertex to the vertex obtained after contracting `T`. -/
def projection [DecidableEq W] (w : W) : SetContractVertex W T :=
  if hw : w ∈ T then merged else keep ⟨w, hw⟩

@[simp] theorem projection_eq_merged_iff [DecidableEq W] {w : W} :
    projection (T := T) w = merged ↔ w ∈ T := by
  by_cases hw : w ∈ T <;> simp [projection, hw]

theorem projection_eq_keep [DecidableEq W] {w : W} (hw : w ∉ T) :
    projection (T := T) w = keep ⟨w, hw⟩ := by
  simp [projection, hw]

theorem eq_or_both_mem_of_projection_eq [DecidableEq W] {x y : W}
    (h : projection (T := T) x = projection (T := T) y) :
    x = y ∨ (x ∈ T ∧ y ∈ T) := by
  by_cases hx : x ∈ T
  · right
    refine ⟨hx, ?_⟩
    rw [← projection_eq_merged_iff]
    simpa [projection, hx] using h.symm
  · by_cases hy : y ∈ T
    · have hxMerged : projection (T := T) x = merged := by
        simpa [projection, hy] using h
      exact (hx (projection_eq_merged_iff.mp hxMerged)).elim
    · left
      have hkeep : keep ⟨x, hx⟩ = (keep ⟨y, hy⟩ : SetContractVertex W T) := by
        simpa [projection, hx, hy] using h
      injection hkeep with hsub
      exact congrArg Subtype.val hsub

theorem eq_of_projection_eq_of_right_not_mem [DecidableEq W] {x y : W}
    (h : projection (T := T) x = projection (T := T) y) (hy : y ∉ T) :
    x = y := by
  rcases eq_or_both_mem_of_projection_eq h with hxy | ⟨_, hyT⟩
  · exact hxy
  · exact (hy hyT).elim

theorem projection_injective_outside [DecidableEq W] :
    Set.InjOn (projection (T := T)) {w : W | w ∉ T} := by
  intro x hx y hy hxy
  exact eq_of_projection_eq_of_right_not_mem hxy hy

theorem projection_surjective [DecidableEq W] (hT : T.Nonempty) :
    Function.Surjective (projection (W := W) (T := T)) := by
  intro x
  cases x with
  | merged =>
      rcases hT with ⟨t, ht⟩
      exact ⟨t, projection_eq_merged_iff.mpr ht⟩
  | keep w => exact ⟨w.1, projection_eq_keep w.2⟩

/-- Contracting `T` leaves one vertex for `T` and one for each vertex outside
`T`.  For nonempty `T`, this is the cardinality of the usual quotient. -/
theorem card [Fintype W] [DecidableEq W] :
    Fintype.card (SetContractVertex W T) =
      Fintype.card W - T.card + 1 := by
  classical
  let e : SetContractVertex W T ≃ Unit ⊕ {w : W // w ∉ T} :=
    { toFun := fun x =>
        match x with
        | merged => Sum.inl ()
        | keep w => Sum.inr w
      invFun := fun x =>
        match x with
        | Sum.inl _ => merged
        | Sum.inr w => keep w
      left_inv := by
        intro x
        cases x <;> rfl
      right_inv := by
        intro x
        cases x with
        | inl x => cases x; rfl
        | inr x => rfl }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_unique,
    Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter fun w : W => w ∉ T) = Finset.univ \ T := by
    ext w
    simp
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ T),
    Finset.card_univ]
  omega

/-- The image of an original vertex finset in the contracted vertex type. -/
def imageFinset [DecidableEq W] (X : Finset W) :
    Finset (SetContractVertex W T) :=
  X.image (projection (T := T))

@[simp] theorem mem_imageFinset [DecidableEq W]
    {X : Finset W} {z : SetContractVertex W T} :
    z ∈ imageFinset (T := T) X ↔
      ∃ x ∈ X, projection (T := T) x = z := by
  simp [imageFinset]

/-- Pull a contracted vertex finset back along the projection. -/
def preimageFinset [Fintype W] [DecidableEq W]
    (Y : Finset (SetContractVertex W T)) : Finset W :=
  Finset.univ.filter fun w => projection (T := T) w ∈ Y

@[simp] theorem mem_preimageFinset [Fintype W] [DecidableEq W]
    {Y : Finset (SetContractVertex W T)} {w : W} :
    w ∈ preimageFinset Y ↔ projection (T := T) w ∈ Y := by
  simp [preimageFinset]

theorem image_preimageFinset [Fintype W] [DecidableEq W]
    (hT : T.Nonempty) (Y : Finset (SetContractVertex W T)) :
    imageFinset (T := T) (preimageFinset Y) = Y := by
  ext z
  constructor
  · rw [mem_imageFinset]
    rintro ⟨w, hw, rfl⟩
    exact mem_preimageFinset.mp hw
  · intro hz
    rcases projection_surjective hT z with ⟨w, rfl⟩
    exact mem_imageFinset.mpr ⟨w, mem_preimageFinset.mpr hz, rfl⟩

/-- A cut is saturated for the contraction of `T` when it contains all of
`T`, or none of `T`. -/
def Saturated (T X : Finset W) : Prop :=
  T ⊆ X ∨ Disjoint T X

theorem preimageFinset_saturated [Fintype W] [DecidableEq W]
    (Y : Finset (SetContractVertex W T)) :
    Saturated T (preimageFinset Y) := by
  by_cases hmerged : (merged : SetContractVertex W T) ∈ Y
  · left
    intro t ht
    rw [mem_preimageFinset, projection_eq_merged_iff.mpr ht]
    exact hmerged
  · right
    exact Finset.disjoint_left.mpr fun t htT htpre =>
      hmerged (by simpa [projection_eq_merged_iff.mpr htT] using
        mem_preimageFinset.mp htpre)

theorem preimage_imageFinset_eq [Fintype W] [DecidableEq W]
    (_hT : T.Nonempty) {X : Finset W} (hX : Saturated T X) :
    preimageFinset (imageFinset (T := T) X) = X := by
  apply Finset.Subset.antisymm
  · intro w hw
    rw [mem_preimageFinset, mem_imageFinset] at hw
    rcases hw with ⟨x, hx, hproj⟩
    rcases eq_or_both_mem_of_projection_eq hproj with rfl | ⟨hxT, hwT⟩
    · exact hx
    · rcases hX with hcontains | hdisjoint
      · exact hcontains hwT
      · exact (Finset.disjoint_left.mp hdisjoint hxT hx).elim
  · intro w hw
    exact mem_preimageFinset.mpr (mem_imageFinset.mpr ⟨w, hw, rfl⟩)

theorem preimageFinset_nonempty [Fintype W] [DecidableEq W]
    (hT : T.Nonempty) {Y : Finset (SetContractVertex W T)}
    (hY : Y.Nonempty) : (preimageFinset Y).Nonempty := by
  rcases hY with ⟨z, hz⟩
  rcases projection_surjective hT z with ⟨w, rfl⟩
  exact ⟨w, mem_preimageFinset.mpr hz⟩

theorem preimageFinset_ne_univ [Fintype W] [DecidableEq W]
    (hT : T.Nonempty) {Y : Finset (SetContractVertex W T)}
    (hY : Y ≠ Finset.univ) : preimageFinset Y ≠ Finset.univ := by
  intro hpre
  apply hY
  rw [← image_preimageFinset hT Y, hpre]
  ext z
  simp only [mem_imageFinset, mem_univ, iff_true]
  rcases projection_surjective hT z with ⟨w, hw⟩
  exact ⟨w, True.intro, hw⟩

end SetContractVertex

/-! ## Named-edge set contraction -/

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- An edge survives contraction of `T` exactly when its projected endpoints
remain distinct. -/
def SurvivesSetContraction (H : FiniteEdgeIndexedGraph W)
    (T : Finset W) (e : H.Edge) : Prop :=
  SetContractVertex.projection (T := T) (H.left e) ≠
    SetContractVertex.projection (T := T) (H.right e)

/-- Contract all vertices of `T`, retaining precisely the named edge copies
which do not become loops. -/
noncomputable def contractSet (H : FiniteEdgeIndexedGraph W) (T : Finset W) :
    FiniteEdgeIndexedGraph (SetContractVertex W T) := by
  classical
  exact
    { Edge := {e : H.Edge // H.SurvivesSetContraction T e}
      left := fun e => SetContractVertex.projection (T := T) (H.left e.1)
      right := fun e => SetContractVertex.projection (T := T) (H.right e.1)
      end_ne := fun e => e.2 }

omit [Fintype W] in
@[simp] theorem contractSet_left (H : FiniteEdgeIndexedGraph W)
    (T : Finset W) (e : (H.contractSet T).Edge) :
    (H.contractSet T).left e =
      SetContractVertex.projection (T := T) (H.left e.1) := rfl

omit [Fintype W] in
@[simp] theorem contractSet_right (H : FiniteEdgeIndexedGraph W)
    (T : Finset W) (e : (H.contractSet T).Edge) :
    (H.contractSet T).right e =
      SetContractVertex.projection (T := T) (H.right e.1) := rfl

theorem contractSet_crosses_iff (H : FiniteEdgeIndexedGraph W)
    (T : Finset W) (Y : Finset (SetContractVertex W T))
    (e : (H.contractSet T).Edge) :
    (H.contractSet T).Crosses Y e ↔
      H.Crosses (SetContractVertex.preimageFinset Y) e.1 := by
  simp only [Crosses, contractSet_left, contractSet_right,
    SetContractVertex.mem_preimageFinset]

/-- Boundary copies are in canonical bijection between a contracted cut and
its saturated preimage. -/
noncomputable def contractSetBoundaryEquiv
    (H : FiniteEdgeIndexedGraph W) (T : Finset W)
    (Y : Finset (SetContractVertex W T)) :
    (H.contractSet T).boundary Y ≃
      H.boundary (SetContractVertex.preimageFinset Y) where
  toFun e := ⟨e.1.1, by
    rw [H.mem_boundary]
    exact (contractSet_crosses_iff H T Y e.1).mp
      (((H.contractSet T).mem_boundary Y e.1).mp e.2)⟩
  invFun e := by
    have hcross : H.Crosses (SetContractVertex.preimageFinset Y) e.1 :=
      (H.mem_boundary _ e.1).mp e.2
    have hsurvives : H.SurvivesSetContraction T e.1 := by
      intro heq
      rcases hcross with h | h
      · exact h.2 (SetContractVertex.mem_preimageFinset.mpr
          (heq ▸ SetContractVertex.mem_preimageFinset.mp h.1))
      · exact h.2 (SetContractVertex.mem_preimageFinset.mpr
          (heq.symm ▸ SetContractVertex.mem_preimageFinset.mp h.1))
    exact ⟨⟨e.1, hsurvives⟩,
      (H.contractSet T).mem_boundary Y ⟨e.1, hsurvives⟩ |>.mpr
        ((contractSet_crosses_iff H T Y ⟨e.1, hsurvives⟩).mpr hcross)⟩
  left_inv := by
    intro e
    exact Subtype.ext (Subtype.ext rfl)
  right_inv := by
    intro e
    exact Subtype.ext rfl

theorem contractSet_boundary_card (H : FiniteEdgeIndexedGraph W)
    (T : Finset W) (Y : Finset (SetContractVertex W T)) :
    ((H.contractSet T).boundary Y).card =
      (H.boundary (SetContractVertex.preimageFinset Y)).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (contractSetBoundaryEquiv H T Y)

/-- Exact boundary cardinality for an original cut saturated with respect to
`T`. -/
theorem contractSet_boundary_card_of_saturated
    (H : FiniteEdgeIndexedGraph W) (T X : Finset W) (hT : T.Nonempty)
    (hX : SetContractVertex.Saturated T X) :
    ((H.contractSet T).boundary
        (SetContractVertex.imageFinset (T := T) X)).card =
      (H.boundary X).card := by
  rw [contractSet_boundary_card,
    SetContractVertex.preimage_imageFinset_eq hT hX]

/-- Exact boundary bijection for an original saturated cut. -/
noncomputable def contractSetBoundaryEquivOfSaturated
    (H : FiniteEdgeIndexedGraph W) (T X : Finset W) (hT : T.Nonempty)
    (hX : SetContractVertex.Saturated T X) :
    (H.contractSet T).boundary
        (SetContractVertex.imageFinset (T := T) X) ≃ H.boundary X := by
  let e := contractSetBoundaryEquiv H T
    (SetContractVertex.imageFinset (T := T) X)
  rw [SetContractVertex.preimage_imageFinset_eq hT hX] at e
  exact e

/-! ## Incidence and split-pair transport away from the contracted set -/

omit [Fintype W] in
theorem survivesSetContraction_of_incident_outside
    (H : FiniteEdgeIndexedGraph W) (T : Finset W) (e : H.Edge) {s : W}
    (hs : s ∉ T) (he : H.left e = s ∨ H.right e = s) :
    H.SurvivesSetContraction T e := by
  intro hproj
  rcases SetContractVertex.eq_or_both_mem_of_projection_eq hproj with heq | hboth
  · exact H.end_ne e heq
  · rcases he with hleft | hright
    · exact hs (hleft ▸ hboth.1)
    · exact hs (hright ▸ hboth.2)

/-- Contraction preserves the complete named incidence set at a center outside
`T`. -/
noncomputable def contractSetIncidentEquiv
    (H : FiniteEdgeIndexedGraph W) (T : Finset W) (s : W) (hs : s ∉ T) :
    (H.contractSet T).incidentEdges
        (SetContractVertex.projection (T := T) s) ≃ H.incidentEdges s where
  toFun e := ⟨e.1.1, by
    rw [H.mem_incidentEdges]
    rcases ((H.contractSet T).mem_incidentEdges _ e.1).mp e.2 with h | h
    · left
      exact SetContractVertex.eq_of_projection_eq_of_right_not_mem h hs
    · right
      exact SetContractVertex.eq_of_projection_eq_of_right_not_mem h hs⟩
  invFun e :=
    ⟨⟨e.1, survivesSetContraction_of_incident_outside H T e.1 hs
      ((H.mem_incidentEdges s e.1).mp e.2)⟩, by
      rw [(H.contractSet T).mem_incidentEdges]
      rcases (H.mem_incidentEdges s e.1).mp e.2 with h | h
      · exact Or.inl (congrArg (SetContractVertex.projection (T := T)) h)
      · exact Or.inr (congrArg (SetContractVertex.projection (T := T)) h)⟩
  left_inv := by
    intro e
    exact Subtype.ext (Subtype.ext rfl)
  right_inv := by
    intro e
    exact Subtype.ext rfl

theorem contractSet_degree_outside (H : FiniteEdgeIndexedGraph W)
    (T : Finset W) (s : W) (hs : s ∉ T) :
    (H.contractSet T).degree (SetContractVertex.projection (T := T) s) =
      H.degree s := by
  unfold degree
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (contractSetIncidentEquiv H T s hs)

/-- Map a Mader split pair at a center outside `T` through set contraction.
The mapped other endpoints may coincide at `merged`; that is the loop case
already represented by `MaderSplitPair`. -/
noncomputable def MaderSplitPair.mapContractSet
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s)
    (T : Finset W) (hs : s ∉ T) :
    (H.contractSet T).MaderSplitPair
      (SetContractVertex.projection (T := T) s) where
  first := ⟨p.first, survivesSetContraction_of_incident_outside H T p.first hs
    ((H.mem_incidentEdges s p.first).mp p.first_mem_incidentEdges)⟩
  second := ⟨p.second, survivesSetContraction_of_incident_outside H T p.second hs
    ((H.mem_incidentEdges s p.second).mp p.second_mem_incidentEdges)⟩
  edge_ne := by
    intro h
    exact p.edge_ne (congrArg Subtype.val h)
  firstOther := SetContractVertex.projection (T := T) p.firstOther
  secondOther := SetContractVertex.projection (T := T) p.secondOther
  first_ends := by
    rcases p.first_ends with h | h
    · exact Or.inl ⟨congrArg (SetContractVertex.projection (T := T)) h.1,
        congrArg (SetContractVertex.projection (T := T)) h.2⟩
    · exact Or.inr ⟨congrArg (SetContractVertex.projection (T := T)) h.1,
        congrArg (SetContractVertex.projection (T := T)) h.2⟩
  second_ends := by
    rcases p.second_ends with h | h
    · exact Or.inl ⟨congrArg (SetContractVertex.projection (T := T)) h.1,
        congrArg (SetContractVertex.projection (T := T)) h.2⟩
    · exact Or.inr ⟨congrArg (SetContractVertex.projection (T := T)) h.1,
        congrArg (SetContractVertex.projection (T := T)) h.2⟩

@[simp] theorem MaderSplitPair.mapContractSet_first
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s)
    (T : Finset W) (hs : s ∉ T) :
    (p.mapContractSet T hs).first.1 = p.first := rfl

@[simp] theorem MaderSplitPair.mapContractSet_second
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s)
    (T : Finset W) (hs : s ∉ T) :
    (p.mapContractSet T hs).second.1 = p.second := rfl

@[simp] theorem MaderSplitPair.mapContractSet_firstOther
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s)
    (T : Finset W) (hs : s ∉ T) :
    (p.mapContractSet T hs).firstOther =
      SetContractVertex.projection (T := T) p.firstOther := rfl

@[simp] theorem MaderSplitPair.mapContractSet_secondOther
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s)
    (T : Finset W) (hs : s ∉ T) :
    (p.mapContractSet T hs).secondOther =
      SetContractVertex.projection (T := T) p.secondOther := rfl

/-- After mapping a split pair through contraction, splitting it has exactly
the same boundary copies as splitting first and pulling the cut back.  This
also covers the case where the new split edge becomes a loop at `merged`. -/
noncomputable def maderSplit_mapContractSetBoundaryEquiv
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (T : Finset W) (hs : s ∉ T)
    (Y : Finset (SetContractVertex W T)) :
    ((H.contractSet T).maderSplit (p.mapContractSet T hs)).boundary Y ≃
      (H.maderSplit p).boundary (SetContractVertex.preimageFinset Y) where
  toFun e := by
    obtain ⟨value, hvalue⟩ := e
    rcases value with old | new
    · let original : (H.maderSplit p).Edge := Sum.inl
        ⟨old.1.1, by
          exact ⟨fun h => old.2.1 (Subtype.ext h),
            fun h => old.2.2 (Subtype.ext h)⟩⟩
      refine ⟨original, ?_⟩
      rw [(H.maderSplit p).mem_boundary]
      have hcross := (((H.contractSet T).maderSplit
        (p.mapContractSet T hs)).mem_boundary Y (Sum.inl old)).mp hvalue
      simpa only [Crosses, maderSplit_old_left, maderSplit_old_right,
        contractSet_left, contractSet_right,
        SetContractVertex.mem_preimageFinset] using hcross
    · have horiginal : p.firstOther ≠ p.secondOther := by
        intro h
        exact new.2 (congrArg (SetContractVertex.projection (T := T)) h)
      let original : (H.maderSplit p).Edge := Sum.inr ⟨(), horiginal⟩
      refine ⟨original, ?_⟩
      rw [(H.maderSplit p).mem_boundary]
      have hcross := (((H.contractSet T).maderSplit
        (p.mapContractSet T hs)).mem_boundary Y (Sum.inr new)).mp hvalue
      simpa only [Crosses, maderSplit_new_left, maderSplit_new_right,
        MaderSplitPair.mapContractSet_firstOther,
        MaderSplitPair.mapContractSet_secondOther,
        SetContractVertex.mem_preimageFinset] using hcross
  invFun e := by
    obtain ⟨value, hvalue⟩ := e
    have hcross := ((H.maderSplit p).mem_boundary
      (SetContractVertex.preimageFinset Y) value).mp hvalue
    rcases value with old | new
    · have hsurvives : H.SurvivesSetContraction T old.1 := by
        have hcross' : H.Crosses (SetContractVertex.preimageFinset Y) old.1 := by
          simpa only [Crosses, maderSplit_old_left, maderSplit_old_right] using hcross
        intro heq
        rcases hcross' with h | h
        · exact h.2 (SetContractVertex.mem_preimageFinset.mpr
            (heq ▸ SetContractVertex.mem_preimageFinset.mp h.1))
        · exact h.2 (SetContractVertex.mem_preimageFinset.mpr
            (heq.symm ▸ SetContractVertex.mem_preimageFinset.mp h.1))
      let contracted : (H.contractSet T).Edge := ⟨old.1, hsurvives⟩
      have hne : contracted ≠ (p.mapContractSet T hs).first ∧
          contracted ≠ (p.mapContractSet T hs).second := by
        exact ⟨fun h => old.2.1 (congrArg Subtype.val h),
          fun h => old.2.2 (congrArg Subtype.val h)⟩
      refine ⟨Sum.inl ⟨contracted, hne⟩, ?_⟩
      rw [((H.contractSet T).maderSplit
        (p.mapContractSet T hs)).mem_boundary]
      simpa only [Crosses, maderSplit_old_left, maderSplit_old_right,
        contractSet_left, contractSet_right,
        SetContractVertex.mem_preimageFinset] using hcross
    · have hproj : SetContractVertex.projection (T := T) p.firstOther ≠
          SetContractVertex.projection (T := T) p.secondOther := by
        have hcross' :
            (p.firstOther ∈ SetContractVertex.preimageFinset Y ∧
              p.secondOther ∉ SetContractVertex.preimageFinset Y) ∨
            (p.secondOther ∈ SetContractVertex.preimageFinset Y ∧
              p.firstOther ∉ SetContractVertex.preimageFinset Y) := by
          simpa only [Crosses, maderSplit_new_left, maderSplit_new_right] using hcross
        intro heq
        rcases hcross' with h | h
        · exact h.2 (SetContractVertex.mem_preimageFinset.mpr
            (heq ▸ SetContractVertex.mem_preimageFinset.mp h.1))
        · exact h.2 (SetContractVertex.mem_preimageFinset.mpr
            (heq.symm ▸ SetContractVertex.mem_preimageFinset.mp h.1))
      let mappedNew :
          {u : Unit // (p.mapContractSet T hs).firstOther ≠
            (p.mapContractSet T hs).secondOther} := ⟨(), by simpa using hproj⟩
      refine ⟨Sum.inr mappedNew, ?_⟩
      rw [((H.contractSet T).maderSplit
        (p.mapContractSet T hs)).mem_boundary]
      simpa only [Crosses, maderSplit_new_left, maderSplit_new_right,
        MaderSplitPair.mapContractSet_firstOther,
        MaderSplitPair.mapContractSet_secondOther,
        SetContractVertex.mem_preimageFinset] using hcross
  left_inv := by
    intro e
    obtain ⟨value, hvalue⟩ := e
    rcases value with old | new
    · exact Subtype.ext rfl
    · exact Subtype.ext rfl
  right_inv := by
    intro e
    obtain ⟨value, hvalue⟩ := e
    rcases value with old | new
    · exact Subtype.ext rfl
    · exact Subtype.ext rfl

theorem maderSplit_mapContractSet_boundary_card
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (T : Finset W) (hs : s ∉ T)
    (Y : Finset (SetContractVertex W T)) :
    (((H.contractSet T).maderSplit (p.mapContractSet T hs)).boundary Y).card =
      ((H.maderSplit p).boundary
        (SetContractVertex.preimageFinset Y)).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr
    (maderSplit_mapContractSetBoundaryEquiv H p T hs Y)

/-- Splitting a mapped pair preserves the exact cut cardinality obtained by
splitting before contraction, for every saturated original cut. -/
theorem maderSplit_mapContractSet_boundary_card_of_saturated
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (T X : Finset W) (hT : T.Nonempty) (hs : s ∉ T)
    (hX : SetContractVertex.Saturated T X) :
    (((H.contractSet T).maderSplit (p.mapContractSet T hs)).boundary
      (SetContractVertex.imageFinset (T := T) X)).card =
      ((H.maderSplit p).boundary X).card := by
  rw [maderSplit_mapContractSet_boundary_card,
    SetContractVertex.preimage_imageFinset_eq hT hX]

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
