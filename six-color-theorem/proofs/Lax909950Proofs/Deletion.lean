import Lax909950Proofs.Geometry

/-!
Deleting an edge from a drawing: the two side faces of the edge merge (together
with the open segment) into a single face, and all other faces are unchanged.
-/

namespace Lax909950Proofs

open Lax68.StraightLineDrawings Lax909950.EulerFormula Set Topology

variable {V : Type*} {G : SimpleGraph V}

section Helpers

variable [Finite V] (D : StraightLineDrawing G) {a b : V}

omit [Finite V] in
theorem edgeSeg_nonempty (a b : V) : (edgeSeg D a b).Nonempty :=
  ⟨(1 / 2 : ℝ) • D.point a + (1 / 2 : ℝ) • D.point b, 1 / 2, 1 / 2, by norm_num, by norm_num,
    by norm_num, rfl⟩

omit [Finite V] in
theorem compl_image_deleteEdge (hab : G.Adj a b) :
    (image (restrictDrawing D (G.deleteEdges_le {s(a, b)})))ᶜ =
      (image D)ᶜ ∪ edgeSeg D a b := by
  rw [image_deleteEdge D hab]
  ext y
  have := @edgeSeg_subset_image _ _ D a b hab y
  simp only [mem_compl_iff, mem_sdiff, not_and, not_not, mem_union]
  tauto

theorem closure_inter_subset_of_ne (hab : G.Adj a b) {F : Set Point} (hF : F ∈ faces D)
    (h1 : F ≠ edgeFace D a b true) (h2 : F ≠ edgeFace D a b false) :
    closure F ∩ ((image D)ᶜ ∪ edgeSeg D a b) ⊆ F := by
  rintro y ⟨hyc, hyU⟩
  by_contra hyF
  have hyfr : y ∈ frontier F := by
    rw [frontier, (isOpen_of_mem_faces D hF).interior_eq]; exact ⟨hyc, hyF⟩
  have hyI := frontier_subset_image D hF hyfr
  rcases hyU with hyU | hyS
  · exact hyU hyI
  · rcases eq_edgeFace_of_mem_closure D hab hF hyS hyc with h | h
    · exact h1 h
    · exact h2 h

theorem subset_of_inter_nonempty (hab : G.Adj a b) {F : Set Point} (hF : F ∈ faces D)
    (h1 : F ≠ edgeFace D a b true) (h2 : F ≠ edgeFace D a b false) {C : Set Point}
    (hC : IsPreconnected C) (hCU : C ⊆ (image D)ᶜ ∪ edgeSeg D a b) (hne : (C ∩ F).Nonempty) :
    C ⊆ F :=
  hC.subset_of_closure_inter_subset (isOpen_of_mem_faces D hF) hne
    (fun _ hy => closure_inter_subset_of_ne D hab hF h1 h2 ⟨hy.1, hCU hy.2⟩)

/-- The merged face. -/
def mergedFace (a b : V) : Set Point :=
  edgeFace D a b true ∪ edgeFace D a b false ∪ edgeSeg D a b

theorem isPreconnected_mergedFace (hab : G.Adj a b) : IsPreconnected (mergedFace D a b) := by
  obtain ⟨x, hx⟩ := edgeSeg_nonempty D a b
  have h : ∀ s, IsPreconnected (edgeFace D a b s ∪ edgeSeg D a b) := fun s =>
    (isConnected_of_mem_faces D (edgeFace_mem_faces D hab s)).isPreconnected.subset_closure
      subset_union_left
      (union_subset subset_closure (edgeSeg_subset_closure_edgeFace D hab s))
  have := (h true).union x (Or.inr hx) (Or.inr hx) (h false)
  convert this using 1
  unfold mergedFace
  ext y; simp only [mem_union]; tauto

theorem mergedFace_subset (hab : G.Adj a b) :
    mergedFace D a b ⊆ (image D)ᶜ ∪ edgeSeg D a b := by
  unfold mergedFace
  refine union_subset (union_subset ?_ ?_) subset_union_right <;>
    exact (subset_compl_of_mem_faces D (edgeFace_mem_faces D hab _)).trans subset_union_left

omit [Finite V] in
theorem mergedFace_not_mem_faces (hab : G.Adj a b) : mergedFace D a b ∉ faces D := by
  intro h
  obtain ⟨x, hx⟩ := edgeSeg_nonempty D a b
  exact subset_compl_of_mem_faces D h (Or.inr hx) (edgeSeg_subset_image D hab hx)

/-- A connected set in the new complement that meets the edge segment lies in the merged
face. -/
theorem subset_mergedFace (hab : G.Adj a b) {C : Set Point} (hC : IsPreconnected C)
    (hCU : C ⊆ (image D)ᶜ ∪ edgeSeg D a b) (hCS : (C ∩ edgeSeg D a b).Nonempty) :
    C ⊆ mergedFace D a b := by
  intro y hy
  by_contra hyM
  have hyU : y ∉ image D := by
    rcases hCU hy with h | h
    · exact h
    · exact absurd (Or.inr h) hyM
  obtain ⟨F, hF, hyF⟩ := exists_mem_faces D hyU
  have h1 : F ≠ edgeFace D a b true := by
    rintro rfl; exact hyM (Or.inl (Or.inl hyF))
  have h2 : F ≠ edgeFace D a b false := by
    rintro rfl; exact hyM (Or.inl (Or.inr hyF))
  have hsub := subset_of_inter_nonempty D hab hF h1 h2 hC hCU ⟨y, hy, hyF⟩
  obtain ⟨z, hzC, hzS⟩ := hCS
  exact subset_compl_of_mem_faces D hF (hsub hzC) (edgeSeg_subset_image D hab hzS)

theorem faces_deleteEdge (hab : G.Adj a b) :
    faces (restrictDrawing D (G.deleteEdges_le {s(a, b)})) =
      insert (mergedFace D a b) (faces D \ {edgeFace D a b true, edgeFace D a b false}) := by
  have hU := compl_image_deleteEdge D hab
  ext F
  simp only [mem_faces_iff, mem_insert_iff, mem_sdiff, mem_singleton_iff, not_or]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← mem_compl_iff, hU] at hx
    rw [hU]
    have hC : IsPreconnected (connectedComponentIn ((image D)ᶜ ∪ edgeSeg D a b) x) :=
      isPreconnected_connectedComponentIn
    have hCU : connectedComponentIn ((image D)ᶜ ∪ edgeSeg D a b) x ⊆
        (image D)ᶜ ∪ edgeSeg D a b := connectedComponentIn_subset _ _
    have hxC : x ∈ connectedComponentIn ((image D)ᶜ ∪ edgeSeg D a b) x :=
      mem_connectedComponentIn hx
    by_cases hxM : x ∈ mergedFace D a b
    · left
      have hMC : mergedFace D a b ⊆ connectedComponentIn ((image D)ᶜ ∪ edgeSeg D a b) x :=
        (isPreconnected_mergedFace D hab).subset_connectedComponentIn hxM
          (mergedFace_subset D hab)
      obtain ⟨z, hz⟩ := edgeSeg_nonempty D a b
      exact (subset_mergedFace D hab hC hCU ⟨z, hMC (Or.inr hz), hz⟩).antisymm hMC
    · right
      have hxU : x ∉ image D := by
        rcases hx with h | h
        · exact h
        · exact absurd (Or.inr h) hxM
      obtain ⟨F, hF, hxF⟩ := exists_mem_faces D hxU
      have h1 : F ≠ edgeFace D a b true := by
        rintro rfl; exact hxM (Or.inl (Or.inl hxF))
      have h2 : F ≠ edgeFace D a b false := by
        rintro rfl; exact hxM (Or.inl (Or.inr hxF))
      have hsub := subset_of_inter_nonempty D hab hF h1 h2 hC hCU ⟨x, hxC, hxF⟩
      have hsup : F ⊆ connectedComponentIn ((image D)ᶜ ∪ edgeSeg D a b) x :=
        (isConnected_of_mem_faces D hF).isPreconnected.subset_connectedComponentIn hxF
          ((subset_compl_of_mem_faces D hF).trans subset_union_left)
      have hEq := hsub.antisymm hsup
      rw [hEq]
      exact ⟨hF, h1, h2⟩
  · rintro (rfl | ⟨hF, h1, h2⟩)
    · obtain ⟨z, hz⟩ := edgeSeg_nonempty D a b
      have hz' : z ∈ (image (restrictDrawing D (G.deleteEdges_le {s(a, b)})))ᶜ := by
        rw [hU]; exact Or.inr hz
      refine ⟨z, hz', ?_⟩
      rw [hU] at hz' ⊢
      have hC : IsPreconnected (connectedComponentIn ((image D)ᶜ ∪ edgeSeg D a b) z) :=
        isPreconnected_connectedComponentIn
      have hMC : mergedFace D a b ⊆ connectedComponentIn ((image D)ᶜ ∪ edgeSeg D a b) z :=
        (isPreconnected_mergedFace D hab).subset_connectedComponentIn (Or.inr hz)
          (mergedFace_subset D hab)
      exact hMC.antisymm (subset_mergedFace D hab hC (connectedComponentIn_subset _ _)
        ⟨z, mem_connectedComponentIn hz', hz⟩)
    · obtain ⟨x, hxF⟩ := (isConnected_of_mem_faces D hF).nonempty
      have hx' : x ∈ (image (restrictDrawing D (G.deleteEdges_le {s(a, b)})))ᶜ := by
        rw [hU]; exact Or.inl (subset_compl_of_mem_faces D hF hxF)
      refine ⟨x, hx', ?_⟩
      rw [hU] at hx' ⊢
      have hsub := subset_of_inter_nonempty D hab hF h1 h2 isPreconnected_connectedComponentIn
        (connectedComponentIn_subset _ _) ⟨x, mem_connectedComponentIn hx', hxF⟩
      have hsup : F ⊆ connectedComponentIn ((image D)ᶜ ∪ edgeSeg D a b) x :=
        (isConnected_of_mem_faces D hF).isPreconnected.subset_connectedComponentIn hxF
          ((subset_compl_of_mem_faces D hF).trans subset_union_left)
      exact hsup.antisymm hsub

theorem encard_faces_deleteEdge (hab : G.Adj a b) :
    (faces (restrictDrawing D (G.deleteEdges_le {s(a, b)}))).encard =
      (faces D \ {edgeFace D a b true, edgeFace D a b false}).encard + 1 := by
  rw [faces_deleteEdge D hab, encard_insert_of_notMem]
  exact fun h => mergedFace_not_mem_faces D hab h.1

theorem encard_faces_eq (hab : G.Adj a b) :
    (faces D).encard = (faces D \ {edgeFace D a b true, edgeFace D a b false}).encard +
      ({edgeFace D a b true, edgeFace D a b false} : Set (Set Point)).encard :=
  (encard_sdiff_add_encard_of_subset (pair_subset (edgeFace_mem_faces D hab true)
    (edgeFace_mem_faces D hab false))).symm

end Helpers

/-- If the two sides of `ab` lie in different faces, deleting `ab` decreases the
number of faces by one. -/
theorem encard_faces_deleteEdge_of_ne [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) (hne : edgeFace D a b true ≠ edgeFace D a b false) :
    (faces D).encard =
      (faces (restrictDrawing D (G.deleteEdges_le {s(a, b)}))).encard + 1 := by
  rw [encard_faces_eq D hab, encard_faces_deleteEdge D hab, encard_pair hne, add_assoc]
  rfl

/-- If both sides of `ab` lie in the same face, deleting `ab` does not change the
number of faces. -/
theorem encard_faces_deleteEdge_of_eq [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) (heq : edgeFace D a b true = edgeFace D a b false) :
    (faces D).encard =
      (faces (restrictDrawing D (G.deleteEdges_le {s(a, b)}))).encard := by
  rw [encard_faces_eq D hab, encard_faces_deleteEdge D hab, heq, pair_eq_singleton,
    encard_singleton]

end Lax909950Proofs
