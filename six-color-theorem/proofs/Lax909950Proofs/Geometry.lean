import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Lax909950.EulerFormula

/-!
Basic geometry of straight-line drawings: open edge segments, the faces on the
two sides of an edge, and restriction of a drawing to a subgraph.
-/

namespace Lax909950Proofs

open Lax68.StraightLineDrawings Lax909950.EulerFormula Set Topology

variable {V : Type*} {G : SimpleGraph V}

/-! ### Restriction to subgraphs -/

/-- A drawing of `G` is also a drawing of every subgraph with the same vertex set. -/
def restrictDrawing (D : StraightLineDrawing G) {H : SimpleGraph V} (h : H ≤ G) :
    StraightLineDrawing H where
  point := D.point
  injective := D.injective
  noVertexOnEdge := fun hab hca hcb => D.noVertexOnEdge (h hab) hca hcb
  disjointEdges := fun hab hcd hdisj => D.disjointEdges (h hab) (h hcd) hdisj

theorem image_restrictDrawing_subset (D : StraightLineDrawing G) {H : SimpleGraph V}
    (h : H ≤ G) : image (restrictDrawing D h) ⊆ image D := by
  rintro y (hy | hy)
  · exact Or.inl hy
  · simp only [mem_iUnion] at hy
    obtain ⟨c, d, hcd, hy⟩ := hy
    exact Or.inr (mem_iUnion.2 ⟨c, mem_iUnion.2 ⟨d, mem_iUnion.2 ⟨h hcd, hy⟩⟩⟩)

/-! ### Edge segments -/

/-- The open segment drawn for the pair `a, b`. -/
def edgeSeg (D : StraightLineDrawing G) (a b : V) : Set Point :=
  openSegment ℝ (D.point a) (D.point b)

theorem edgeSeg_subset_image (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b) :
    edgeSeg D a b ⊆ image D := by
  intro y hy
  exact Or.inr (mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨b, mem_iUnion.2
    ⟨hab, openSegment_subset_segment _ _ _ hy⟩⟩⟩)

theorem segment_subset_image (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b) :
    segment ℝ (D.point a) (D.point b) ⊆ image D := fun _ hy =>
  Or.inr (mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨hab, hy⟩⟩⟩)

/-- Two segments from a common point `p`, the first open one meeting the second:
one of the far endpoints lies on the other segment. -/
theorem seg_aux {p q r x : Point} (hpq : p ≠ q) (hx : x ∈ openSegment ℝ p q)
    (hx' : x ∈ segment ℝ p r) : r ∈ segment ℝ p q ∨ q ∈ segment ℝ p r := by
  rw [openSegment_eq_image'] at hx
  rw [segment_eq_image'] at hx' ⊢
  rw [segment_eq_image']
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hx
  obtain ⟨u, ⟨hu0, hu1⟩, hxu⟩ := hx'
  have h1 : u * (r.1 - p.1) = s * (q.1 - p.1) := by
    have := congrArg Prod.fst hxu; simp at this; linarith
  have h2 : u * (r.2 - p.2) = s * (q.2 - p.2) := by
    have := congrArg Prod.snd hxu; simp at this; linarith
  have hu : u ≠ 0 := by
    rintro rfl
    apply hpq
    have e1 : s * (q.1 - p.1) = 0 := by rw [← h1]; ring
    have e2 : s * (q.2 - p.2) = 0 := by rw [← h2]; ring
    rcases mul_eq_zero.1 e1 with h | h
    · linarith
    rcases mul_eq_zero.1 e2 with h' | h'
    · linarith
    exact Prod.ext (by linarith) (by linarith)
  have hu0' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  rcases le_or_gt s u with hsu | hsu
  · left
    refine ⟨s / u, ⟨div_nonneg hs0.le hu0, (div_le_one hu0').2 hsu⟩, ?_⟩
    ext <;> simp <;> field_simp <;> linarith
  · right
    refine ⟨u / s, ⟨div_nonneg hu0 hs0.le, (div_le_one hs0).2 hsu.le⟩, ?_⟩
    ext <;> simp <;> field_simp <;> linarith

theorem share_aux (D : StraightLineDrawing G) {a b d : V} (hab : G.Adj a b) (had : G.Adj a d)
    (hdb : d ≠ b) {x : Point} (hx : x ∈ openSegment ℝ (D.point a) (D.point b))
    (hx' : x ∈ segment ℝ (D.point a) (D.point d)) : False := by
  rcases seg_aux (D.injective.ne hab.ne) hx hx' with h | h
  · exact D.noVertexOnEdge hab had.ne.symm hdb h
  · exact D.noVertexOnEdge had hab.ne.symm hdb.symm h

/-- The open segment of an edge `ab` meets the image of the drawing only in
itself: it contains no vertex point and meets no other edge segment. -/
theorem edgeSeg_inter_image (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b)
    {x : Point} (hx : x ∈ edgeSeg D a b) {c d : V} (hcd : G.Adj c d)
    (hx' : x ∈ segment ℝ (D.point c) (D.point d)) : s(c, d) = s(a, b) := by
  have hx0 : x ∈ openSegment ℝ (D.point a) (D.point b) := hx
  by_cases hdisj : Disjoint ({a, b} : Set V) ({c, d} : Set V)
  · exact absurd (D.disjointEdges hab hcd hdisj)
      (Set.not_disjoint_iff.2 ⟨x, openSegment_subset_segment _ _ _ hx0, hx'⟩)
  · rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨e, he1, he2⟩ := hdisj
    simp only [mem_insert_iff, mem_singleton_iff] at he1 he2
    rcases he1 with h1 | h1 <;> rcases he2 with h2 | h2
    · -- c = a
      have hca : c = a := h2.symm.trans h1
      rw [hca] at hcd hx' ⊢
      by_cases hdb : d = b
      · rw [hdb]
      · exact (share_aux D hab hcd hdb hx0 hx').elim
    · -- d = a
      have hda : d = a := h2.symm.trans h1
      rw [hda] at hcd hx' ⊢
      by_cases hcb : c = b
      · rw [hcb, Sym2.eq_swap]
      · exact (share_aux D hab hcd.symm hcb hx0 (by rwa [segment_symm] at hx')).elim
    · -- c = b
      have hcb : c = b := h2.symm.trans h1
      rw [hcb] at hcd hx' ⊢
      by_cases hda : d = a
      · rw [hda, Sym2.eq_swap]
      · exact (share_aux D hab.symm hcd hda (by rwa [openSegment_symm] at hx0) hx').elim
    · -- d = b
      have hdb : d = b := h2.symm.trans h1
      rw [hdb] at hcd hx' ⊢
      by_cases hca : c = a
      · rw [hca]
      · exact (share_aux D hab.symm hcd.symm hca (by rwa [openSegment_symm] at hx0)
          (by rwa [segment_symm] at hx')).elim

theorem edgeSeg_disjoint_range (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b) :
    Disjoint (edgeSeg D a b) (range D.point) := by
  rw [Set.disjoint_right]
  rintro _ ⟨c, rfl⟩ hc
  have hc0 : D.point c ∈ openSegment ℝ (D.point a) (D.point b) := hc
  by_cases hca : c = a
  · rw [hca] at hc0
    exact hab.ne (D.injective (left_mem_openSegment_iff.1 hc0))
  by_cases hcb : c = b
  · rw [hcb] at hc0
    exact hab.ne (D.injective (right_mem_openSegment_iff.1 hc0))
  exact D.noVertexOnEdge hab hca hcb (openSegment_subset_segment _ _ _ hc0)

/-- The image of all vertices and of all edges other than `ab`. -/
def rest (D : StraightLineDrawing G) (a b : V) : Set Point :=
  range D.point ∪ ⋃ (c : V) (d : V) (_ : G.Adj c d) (_ : s(c, d) ≠ s(a, b)),
    segment ℝ (D.point c) (D.point d)

theorem image_subset_rest_union (D : StraightLineDrawing G) (a b : V) :
    image D ⊆ rest D a b ∪ segment ℝ (D.point a) (D.point b) := by
  rintro y (hy | hy)
  · exact Or.inl (Or.inl hy)
  · simp only [mem_iUnion] at hy
    obtain ⟨c, d, hcd, hy⟩ := hy
    by_cases h : s(c, d) = s(a, b)
    · right
      rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hy
      · rwa [segment_symm]
    · left; right; simp only [mem_iUnion]; exact ⟨c, d, hcd, h, hy⟩

theorem disjoint_edgeSeg_rest (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b) :
    Disjoint (edgeSeg D a b) (rest D a b) := by
  rw [Set.disjoint_left]
  rintro x hx (hr | hr)
  · exact Set.disjoint_left.1 (edgeSeg_disjoint_range D hab) hx hr
  · simp only [mem_iUnion] at hr
    obtain ⟨c, d, hcd, hne, hr⟩ := hr
    exact hne (edgeSeg_inter_image D hab hx hcd hr)

/-- Deleting the edge `ab` removes exactly its open segment from the image. -/
theorem image_deleteEdge (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b) :
    image (restrictDrawing D (G.deleteEdges_le {s(a, b)})) = image D \ edgeSeg D a b := by
  ext y
  constructor
  · rintro (hy | hy)
    · exact ⟨Or.inl hy, fun h => Set.disjoint_left.1 (edgeSeg_disjoint_range D hab) h hy⟩
    · simp only [mem_iUnion] at hy
      obtain ⟨c, d, hcd, hy⟩ := hy
      rw [SimpleGraph.deleteEdges_adj] at hcd
      refine ⟨Or.inr (mem_iUnion.2 ⟨c, mem_iUnion.2 ⟨d, mem_iUnion.2 ⟨hcd.1, hy⟩⟩⟩),
        fun h => hcd.2 (mem_singleton_iff.2 ?_)⟩
      exact edgeSeg_inter_image D hab h hcd.1 hy
  · rintro ⟨hy, hy'⟩
    rcases image_subset_rest_union D a b hy with hr | hr
    · rcases hr with hr | hr
      · exact Or.inl hr
      · simp only [mem_iUnion] at hr
        obtain ⟨c, d, hcd, hne, hr⟩ := hr
        exact Or.inr (mem_iUnion.2 ⟨c, mem_iUnion.2 ⟨d, mem_iUnion.2
          ⟨(SimpleGraph.deleteEdges_adj).2 ⟨hcd, fun h => hne (mem_singleton_iff.1 h)⟩, hr⟩⟩⟩)
    · rw [← insert_endpoints_openSegment] at hr
      rcases hr with rfl | rfl | hr
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inl ⟨b, rfl⟩
      · exact absurd hr hy'

/-! ### Basic topology of the image and the faces -/

theorem isCompact_segment' (p q : Point) : IsCompact (segment ℝ p q) := by
  rw [segment_eq_image']; exact isCompact_Icc.image (by fun_prop)

theorem isCompact_image [Finite V] (D : StraightLineDrawing G) : IsCompact (image D) :=
  (finite_range _).isCompact.union (isCompact_iUnion fun _ => isCompact_iUnion fun _ =>
    isCompact_iUnion fun _ => isCompact_segment' _ _)

theorem isClosed_rest [Finite V] (D : StraightLineDrawing G) (a b : V) :
    IsClosed (rest D a b) :=
  ((finite_range _).isCompact.union (isCompact_iUnion fun _ => isCompact_iUnion fun _ =>
    isCompact_iUnion fun _ => isCompact_iUnion fun _ => isCompact_segment' _ _)).isClosed

theorem isClosed_image [Finite V] (D : StraightLineDrawing G) : IsClosed (image D) :=
  (isCompact_image D).isClosed

theorem isOpen_compl_image [Finite V] (D : StraightLineDrawing G) : IsOpen (image D)ᶜ :=
  (isClosed_image D).isOpen_compl

theorem mem_faces_iff (D : StraightLineDrawing G) {F : Set Point} :
    F ∈ faces D ↔ ∃ x ∉ image D, F = connectedComponentIn (image D)ᶜ x := Iff.rfl

theorem isOpen_of_mem_faces [Finite V] (D : StraightLineDrawing G) {F : Set Point}
    (hF : F ∈ faces D) : IsOpen F := by
  obtain ⟨x, _, rfl⟩ := hF
  exact (isOpen_compl_image D).connectedComponentIn

theorem isConnected_of_mem_faces (D : StraightLineDrawing G) {F : Set Point}
    (hF : F ∈ faces D) : IsConnected F := by
  obtain ⟨x, hx, rfl⟩ := hF
  exact isConnected_connectedComponentIn_iff.2 hx

theorem subset_compl_of_mem_faces (D : StraightLineDrawing G) {F : Set Point}
    (hF : F ∈ faces D) : F ⊆ (image D)ᶜ := by
  obtain ⟨x, _, rfl⟩ := hF
  exact connectedComponentIn_subset _ _

/-- Two faces are equal as soon as they share a point. -/
theorem eq_of_mem_faces (D : StraightLineDrawing G) {F F' : Set Point}
    (hF : F ∈ faces D) (hF' : F' ∈ faces D) {x : Point} (hx : x ∈ F) (hx' : x ∈ F') :
    F = F' := by
  obtain ⟨y, _, rfl⟩ := hF
  obtain ⟨y', _, rfl⟩ := hF'
  rw [connectedComponentIn_eq hx, connectedComponentIn_eq hx']

/-- Every point off the image lies in some face. -/
theorem exists_mem_faces (D : StraightLineDrawing G) {x : Point} (hx : x ∉ image D) :
    ∃ F ∈ faces D, x ∈ F :=
  ⟨_, ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩

/-- A connected set off the image lies in a single face. -/
theorem subset_face_of_isPreconnected (D : StraightLineDrawing G) {S : Set Point}
    (hS : IsPreconnected S) (hSI : S ⊆ (image D)ᶜ) {F : Set Point} (hF : F ∈ faces D)
    {x : Point} (hxS : x ∈ S) (hxF : x ∈ F) : S ⊆ F := by
  obtain ⟨y, _, rfl⟩ := hF
  rw [connectedComponentIn_eq hxF]
  exact hS.subset_connectedComponentIn hxS hSI

theorem frontier_subset_image [Finite V] (D : StraightLineDrawing G) {F : Set Point}
    (hF : F ∈ faces D) : frontier F ⊆ image D := by
  obtain ⟨x0, _, rfl⟩ := hF
  intro y hy
  by_contra hyI
  have hopen : IsOpen (connectedComponentIn (image D)ᶜ x0) :=
    (isOpen_compl_image D).connectedComponentIn
  rw [frontier, hopen.interior_eq] at hy
  obtain ⟨hyc, hyF⟩ := hy
  have hO : IsOpen (connectedComponentIn (image D)ᶜ y) :=
    (isOpen_compl_image D).connectedComponentIn
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hyc _ hO (mem_connectedComponentIn hyI)
  apply hyF
  rw [connectedComponentIn_eq hz2, ← connectedComponentIn_eq hz1]
  exact mem_connectedComponentIn hyI

/-- A drawing of a graph without edges has exactly one face. -/
theorem encard_faces_of_edgeless [Finite V] (D : StraightLineDrawing G)
    (hG : G = ⊥) : (faces D).encard = 1 := by
  subst hG
  have himg : image D = range D.point := by
    simp [Lax909950.EulerFormula.image]
  have hconn : IsConnected (image D)ᶜ := by
    rw [himg]
    exact (finite_range _).countable.isConnected_compl_of_one_lt_rank (by simp; norm_num)
  have key : ∀ x ∈ (image D)ᶜ, connectedComponentIn (image D)ᶜ x = (image D)ᶜ := fun x hx =>
    Subset.antisymm (connectedComponentIn_subset _ _)
      (hconn.isPreconnected.subset_connectedComponentIn hx subset_rfl)
  have : faces D = {(image D)ᶜ} := by
    ext F
    simp only [mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact key x hx
    · rintro rfl
      obtain ⟨x, hx⟩ := hconn.nonempty
      exact ⟨x, hx, (key x hx).symm⟩
  rw [this, encard_singleton]

/-! ### The two sides of an edge -/

/-- The normal vector of `p → q`, obtained by rotating `q - p` by a quarter turn. -/
def normal (p q : Point) : Point := (-(q.2 - p.2), q.1 - p.1)

/-- The point at signed distance parameter `t` from the midpoint of the edge `ab`,
in direction of the normal. -/
noncomputable def sidePt (D : StraightLineDrawing G) (a b : V) (t : ℝ) : Point :=
  (1 / 2 : ℝ) • (D.point a + D.point b) + t • normal (D.point a) (D.point b)

/-- `ε` is a clearance for the edge `ab` if the normal segment through the midpoint of
`ab` meets the image only at the midpoint, for parameters `|t| ≤ ε`. -/
def IsClearance (D : StraightLineDrawing G) (a b : V) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ ε → sidePt D a b t ∉ image D

/-! ### Affine coordinates along an edge -/

/-- The point with coordinates `(s, t)` in the frame of `p → q`. -/
def chartPt (p q : Point) (s t : ℝ) : Point := p + s • (q - p) + t • normal p q

/-- Squared length of `q - p`. -/
def sqLen (p q : Point) : ℝ := (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2

/-- Coordinate along `p → q`. -/
noncomputable def sCoord (p q y : Point) : ℝ :=
  ((y.1 - p.1) * (q.1 - p.1) + (y.2 - p.2) * (q.2 - p.2)) / sqLen p q

/-- Coordinate along the normal of `p → q`. -/
noncomputable def tCoord (p q y : Point) : ℝ :=
  ((y.2 - p.2) * (q.1 - p.1) - (y.1 - p.1) * (q.2 - p.2)) / sqLen p q

theorem sqLen_pos {p q : Point} (h : p ≠ q) : 0 < sqLen p q := by
  unfold sqLen
  by_contra hle
  push Not at hle
  apply h
  have h1 : (q.1 - p.1) ^ 2 = 0 := by nlinarith [sq_nonneg (q.1 - p.1), sq_nonneg (q.2 - p.2)]
  have h2 : (q.2 - p.2) ^ 2 = 0 := by nlinarith [sq_nonneg (q.1 - p.1), sq_nonneg (q.2 - p.2)]
  have e1 := (pow_eq_zero_iff two_ne_zero).1 h1
  have e2 := (pow_eq_zero_iff two_ne_zero).1 h2
  exact Prod.ext (by linarith) (by linarith)

theorem normal_ne_zero {p q : Point} (h : p ≠ q) : normal p q ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [normal, Prod.fst_zero, Prod.snd_zero] at h1 h2
  exact Prod.ext (by linarith) (by linarith)

theorem chartPt_fst (p q : Point) (s t : ℝ) :
    (chartPt p q s t).1 = p.1 + s * (q.1 - p.1) - t * (q.2 - p.2) := by
  simp [chartPt, normal]; ring

theorem chartPt_snd (p q : Point) (s t : ℝ) :
    (chartPt p q s t).2 = p.2 + s * (q.2 - p.2) + t * (q.1 - p.1) := by
  simp [chartPt, normal]

theorem sCoord_chartPt {p q : Point} (h : p ≠ q) (s t : ℝ) :
    sCoord p q (chartPt p q s t) = s := by
  have := (sqLen_pos h).ne'
  unfold sCoord
  rw [chartPt_fst, chartPt_snd, div_eq_iff this]
  unfold sqLen; ring

theorem tCoord_chartPt {p q : Point} (h : p ≠ q) (s t : ℝ) :
    tCoord p q (chartPt p q s t) = t := by
  have := (sqLen_pos h).ne'
  unfold tCoord
  rw [chartPt_fst, chartPt_snd, div_eq_iff this]
  unfold sqLen; ring

theorem chartPt_coords {p q : Point} (h : p ≠ q) (y : Point) :
    chartPt p q (sCoord p q y) (tCoord p q y) = y := by
  have := (sqLen_pos h).ne'
  ext
  · rw [chartPt_fst]; unfold sCoord tCoord; field_simp; unfold sqLen; ring
  · rw [chartPt_snd]; unfold sCoord tCoord; field_simp; unfold sqLen; ring

theorem continuous_sCoord (p q : Point) : Continuous (sCoord p q) := by
  unfold sCoord; fun_prop

theorem continuous_tCoord (p q : Point) : Continuous (tCoord p q) := by
  unfold tCoord; fun_prop

theorem continuous_chartPt (p q : Point) :
    Continuous fun st : ℝ × ℝ => chartPt p q st.1 st.2 := by
  unfold chartPt; fun_prop

theorem chartPt_zero (p q : Point) (s : ℝ) : chartPt p q s 0 = p + s • (q - p) := by
  simp [chartPt]

theorem chartPt_mem_segment {p q : Point} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    chartPt p q s 0 ∈ segment ℝ p q := by
  rw [segment_eq_image']; exact ⟨s, hs, (chartPt_zero p q s).symm⟩

theorem chartPt_mem_openSegment {p q : Point} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    chartPt p q s 0 ∈ openSegment ℝ p q := by
  rw [openSegment_eq_image']; exact ⟨s, hs, (chartPt_zero p q s).symm⟩

theorem tCoord_eq_zero_of_mem_segment {p q y : Point} (h : p ≠ q) (hy : y ∈ segment ℝ p q) :
    tCoord p q y = 0 := by
  rw [segment_eq_image'] at hy
  obtain ⟨θ, _, rfl⟩ := hy
  show tCoord p q (p + θ • (q - p)) = 0
  rw [← chartPt_zero, tCoord_chartPt h]

theorem sidePt_eq (D : StraightLineDrawing G) (a b : V) (t : ℝ) :
    sidePt D a b t = chartPt (D.point a) (D.point b) (1 / 2) t := by
  ext <;> simp [sidePt, chartPt, normal] <;> ring

theorem sidePt_swap (D : StraightLineDrawing G) (a b : V) (t : ℝ) :
    sidePt D b a t = sidePt D a b (-t) := by
  ext <;> simp [sidePt, normal] <;> ring

theorem continuous_sidePt (D : StraightLineDrawing G) (a b : V) :
    Continuous (sidePt D a b) := by
  unfold sidePt; fun_prop

/-- Tube lemma: a thin strip around a compact middle part of the edge `ab` meets
the image only in the edge itself. -/
theorem tube [Finite V] (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b) {α : ℝ}
    (hα : 0 < α) :
    ∃ δ > 0, ∀ s t : ℝ, α ≤ s → s ≤ 1 - α → t ≠ 0 → |t| ≤ δ →
      chartPt (D.point a) (D.point b) s t ∉ image D := by
  have hpq : D.point a ≠ D.point b := D.injective.ne hab.ne
  set C := (fun s => chartPt (D.point a) (D.point b) s 0) '' Icc α (1 - α) with hCdef
  have hC : IsCompact C := isCompact_Icc.image (by unfold chartPt; fun_prop)
  have hCR : C ⊆ (rest D a b)ᶜ := by
    rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩ hr
    have : chartPt (D.point a) (D.point b) s 0 ∈ edgeSeg D a b :=
      chartPt_mem_openSegment ⟨by linarith, by linarith⟩
    exact Set.disjoint_left.1 (disjoint_edgeSeg_rest D hab) this hr
  obtain ⟨δ0, hδ0, hsub⟩ :=
    hC.exists_cthickening_subset_open (isClosed_rest D a b).isOpen_compl hCR
  have hn : 0 < ‖normal (D.point a) (D.point b)‖ := norm_pos_iff.2 (normal_ne_zero hpq)
  refine ⟨δ0 / ‖normal (D.point a) (D.point b)‖, div_pos hδ0 hn,
    fun s t hs1 hs2 ht0 ht hmem => ?_⟩
  rcases image_subset_rest_union D a b hmem with hr | hr
  · refine hsub (Metric.mem_cthickening_of_dist_le _
      (chartPt (D.point a) (D.point b) s 0) _ _ ⟨s, ⟨hs1, hs2⟩, rfl⟩ ?_) hr
    rw [dist_eq_norm]
    have : chartPt (D.point a) (D.point b) s t - chartPt (D.point a) (D.point b) s 0 =
        t • normal (D.point a) (D.point b) := by simp [chartPt]
    rw [this, norm_smul, Real.norm_eq_abs]
    rwa [le_div_iff₀ hn] at ht
  · exact ht0 (by have := tCoord_eq_zero_of_mem_segment hpq hr; rwa [tCoord_chartPt hpq] at this)

theorem exists_clearance [Finite V] (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b) :
    ∃ ε, IsClearance D a b ε := by
  obtain ⟨δ, hδ, h⟩ := tube D hab (α := 1 / 4) (by norm_num)
  refine ⟨δ, hδ, fun t ht0 ht => ?_⟩
  rw [sidePt_eq]; exact h _ _ (by norm_num) (by norm_num) ht0 ht

open Classical in
/-- A fixed clearance for the edge `ab`. -/
noncomputable def clearance (D : StraightLineDrawing G) (a b : V) : ℝ :=
  if h : ∃ ε, IsClearance D a b ε then h.choose else 1

/-- The face on the side `s` of the directed edge `ab`: `true` is the side into which
`normal (D.point a) (D.point b)` points, `false` is the opposite side. -/
noncomputable def edgeFace (D : StraightLineDrawing G) (a b : V) (s : Bool) : Set Point :=
  connectedComponentIn (image D)ᶜ
    (sidePt D a b (if s then clearance D a b else -clearance D a b))

theorem isClearance_swap {D : StraightLineDrawing G} {a b : V} {ε : ℝ} :
    IsClearance D b a ε ↔ IsClearance D a b ε := by
  constructor <;> rintro ⟨h0, h⟩ <;> refine ⟨h0, fun t ht1 ht2 => ?_⟩
  · have := h (-t) (neg_ne_zero.2 ht1) (by rwa [abs_neg])
    rwa [sidePt_swap, neg_neg] at this
  · rw [sidePt_swap]; exact h (-t) (neg_ne_zero.2 ht1) (by rwa [abs_neg])

theorem clearance_spec [Finite V] (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b) :
    IsClearance D a b (clearance D a b) := by
  have h := exists_clearance D hab
  unfold clearance; rw [dif_pos h]; exact h.choose_spec

theorem cc_eq_of_Icc {D : StraightLineDrawing G} {a b : V} {ε : ℝ}
    (hε : IsClearance D a b ε) {t t' : ℝ} (htt : t ≤ t') (h0 : (0 : ℝ) ∉ Icc t t')
    (h1 : -ε ≤ t) (h2 : t' ≤ ε) :
    connectedComponentIn (image D)ᶜ (sidePt D a b t) =
      connectedComponentIn (image D)ᶜ (sidePt D a b t') := by
  have hS : sidePt D a b '' Icc t t' ⊆ (image D)ᶜ := by
    rintro _ ⟨u, hu, rfl⟩
    exact hε.2 u (fun h => h0 (h ▸ hu)) (abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hpre : IsPreconnected (sidePt D a b '' Icc t t') :=
    isPreconnected_Icc.image _ (continuous_sidePt D a b).continuousOn
  exact connectedComponentIn_eq (hpre.subset_connectedComponentIn
    ⟨t, left_mem_Icc.2 htt, rfl⟩ hS ⟨t', right_mem_Icc.2 htt, rfl⟩)

theorem cc_clearance_eq {D : StraightLineDrawing G} {a b : V} {ε ε' : ℝ}
    (hε : IsClearance D a b ε) (hε' : IsClearance D a b ε') :
    connectedComponentIn (image D)ᶜ (sidePt D a b ε) =
        connectedComponentIn (image D)ᶜ (sidePt D a b ε') ∧
      connectedComponentIn (image D)ᶜ (sidePt D a b (-ε)) =
        connectedComponentIn (image D)ᶜ (sidePt D a b (-ε')) := by
  have hm : 0 < min ε ε' := lt_min hε.1 hε'.1
  have hm1 := min_le_left ε ε'
  have hm2 := min_le_right ε ε'
  have n0 : ∀ u v : ℝ, 0 < u → (0 : ℝ) ∉ Icc u v := fun u v hu h => by linarith [h.1]
  have n1 : ∀ u v : ℝ, v < 0 → (0 : ℝ) ∉ Icc u v := fun u v hv h => by linarith [h.2]
  constructor
  · rw [← cc_eq_of_Icc hε hm1 (n0 _ _ hm) (by linarith) le_rfl,
      ← cc_eq_of_Icc hε' hm2 (n0 _ _ hm) (by linarith) le_rfl]
  · rw [cc_eq_of_Icc hε (neg_le_neg hm1) (n1 _ _ (neg_neg_of_pos hm)) le_rfl (by linarith),
      cc_eq_of_Icc hε' (neg_le_neg hm2) (n1 _ _ (neg_neg_of_pos hm)) le_rfl (by linarith)]

theorem edgeFace_true (D : StraightLineDrawing G) (a b : V) :
    edgeFace D a b true = connectedComponentIn (image D)ᶜ (sidePt D a b (clearance D a b)) :=
  rfl

theorem edgeFace_false (D : StraightLineDrawing G) (a b : V) :
    edgeFace D a b false =
      connectedComponentIn (image D)ᶜ (sidePt D a b (-clearance D a b)) :=
  rfl

theorem edgeFace_mem_faces [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) (s : Bool) : edgeFace D a b s ∈ faces D := by
  have hc := clearance_spec D hab
  cases s
  · rw [edgeFace_false]
    exact ⟨_, hc.2 _ (neg_ne_zero.2 hc.1.ne') (by rw [abs_neg, abs_of_pos hc.1]), rfl⟩
  · rw [edgeFace_true]
    exact ⟨_, hc.2 _ hc.1.ne' (by rw [abs_of_pos hc.1]), rfl⟩

/-- Reversing the edge swaps its sides. -/
theorem edgeFace_swap [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) (s : Bool) : edgeFace D b a s = edgeFace D a b (!s) := by
  have hc := clearance_spec D hab
  have hc' : IsClearance D a b (clearance D b a) := isClearance_swap.1 (clearance_spec D hab.symm)
  cases s
  · rw [Bool.not_false, edgeFace_false, edgeFace_true, sidePt_swap, neg_neg]
    exact (cc_clearance_eq hc' hc).1
  · rw [Bool.not_true, edgeFace_false, edgeFace_true, sidePt_swap]
    exact (cc_clearance_eq hc' hc).2

/-- Points on the normal through the midpoint, close enough to the edge, lie in the
corresponding side face. -/
theorem sidePt_mem_edgeFace [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) :
    ∃ ε > 0, ∀ t, 0 < t → t < ε →
      sidePt D a b t ∈ edgeFace D a b true ∧ sidePt D a b (-t) ∈ edgeFace D a b false := by
  have hc := clearance_spec D hab
  refine ⟨clearance D a b, hc.1, fun t ht0 htc => ⟨?_, ?_⟩⟩
  · rw [edgeFace_true, ← cc_eq_of_Icc hc htc.le (fun h => by linarith [h.1]) (by linarith) le_rfl]
    exact mem_connectedComponentIn (hc.2 t ht0.ne' (by rw [abs_of_pos ht0]; exact htc.le))
  · rw [edgeFace_false, cc_eq_of_Icc hc (neg_le_neg htc.le) (fun h => by linarith [h.2]) le_rfl
      (by linarith)]
    exact mem_connectedComponentIn (hc.2 (-t) (neg_ne_zero.2 ht0.ne')
      (by rw [abs_neg, abs_of_pos ht0]; exact htc.le))

/-- Points of a thin strip along the edge lie in the corresponding side face. -/
theorem chartPt_mem_edgeFace [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) {α δ : ℝ} (hα2 : α ≤ 1 / 2) (hδ : 0 < δ)
    (htube : ∀ s t : ℝ, α ≤ s → s ≤ 1 - α → t ≠ 0 → |t| ≤ δ →
      chartPt (D.point a) (D.point b) s t ∉ image D)
    {s t : ℝ} (hs1 : α ≤ s) (hs2 : s ≤ 1 - α) :
    (0 < t → t ≤ δ → chartPt (D.point a) (D.point b) s t ∈ edgeFace D a b true) ∧
    (-δ ≤ t → t < 0 → chartPt (D.point a) (D.point b) s t ∈ edgeFace D a b false) := by
  have hc := clearance_spec D hab
  have hm : 0 < min δ (clearance D a b) := lt_min hδ hc.1
  have hm1 := min_le_left δ (clearance D a b)
  have hm2 := min_le_right δ (clearance D a b)
  constructor
  · intro ht0 htδ
    set S := (fun st : ℝ × ℝ => chartPt (D.point a) (D.point b) st.1 st.2) ''
      (Icc α (1 - α) ×ˢ Ioc 0 δ)
    have hS : S ⊆ (image D)ᶜ := by
      rintro _ ⟨⟨s', t'⟩, ⟨hs', ht'⟩, rfl⟩
      exact htube s' t' hs'.1 hs'.2 (ne_of_gt ht'.1) (abs_le.2 ⟨by linarith [ht'.1], ht'.2⟩)
    have hpre : IsPreconnected S :=
      ((convex_Icc _ _).prod (convex_Ioc _ _)).isPreconnected.image _
        (continuous_chartPt (D.point a) (D.point b)).continuousOn
    have hmS : sidePt D a b (min δ (clearance D a b)) ∈ S :=
      ⟨(1 / 2, min δ (clearance D a b)), ⟨⟨by linarith, by linarith⟩, ⟨hm, hm1⟩⟩,
        (sidePt_eq D a b _).symm⟩
    rw [edgeFace_true, ← cc_eq_of_Icc hc hm2 (fun h => by linarith [h.1]) (by linarith) le_rfl]
    exact hpre.subset_connectedComponentIn hmS hS ⟨(s, t), ⟨⟨hs1, hs2⟩, ⟨ht0, htδ⟩⟩, rfl⟩
  · intro htδ ht0
    set S := (fun st : ℝ × ℝ => chartPt (D.point a) (D.point b) st.1 st.2) ''
      (Icc α (1 - α) ×ˢ Ico (-δ) 0)
    have hS : S ⊆ (image D)ᶜ := by
      rintro _ ⟨⟨s', t'⟩, ⟨hs', ht'⟩, rfl⟩
      exact htube s' t' hs'.1 hs'.2 (ne_of_lt ht'.2) (abs_le.2 ⟨ht'.1, by linarith [ht'.2]⟩)
    have hpre : IsPreconnected S :=
      ((convex_Icc _ _).prod (convex_Ico _ _)).isPreconnected.image _
        (continuous_chartPt (D.point a) (D.point b)).continuousOn
    have hmS : sidePt D a b (-min δ (clearance D a b)) ∈ S :=
      ⟨(1 / 2, -min δ (clearance D a b)), ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
        (sidePt_eq D a b _).symm⟩
    rw [edgeFace_false, cc_eq_of_Icc hc (neg_le_neg hm2) (fun h => by linarith [h.2]) le_rfl
      (by linarith)]
    exact hpre.subset_connectedComponentIn hmS hS ⟨(s, t), ⟨⟨hs1, hs2⟩, ⟨htδ, ht0⟩⟩, rfl⟩

/-- Coordinates and a tube around a point of the open segment. -/
theorem edge_setup [Finite V] (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b)
    {x : Point} (hx : x ∈ edgeSeg D a b) :
    ∃ s0 α δ : ℝ, x = chartPt (D.point a) (D.point b) s0 0 ∧ 0 < α ∧ α ≤ 1 / 2 ∧
      α < s0 ∧ s0 < 1 - α ∧ 0 < δ ∧
      ∀ s t : ℝ, α ≤ s → s ≤ 1 - α → t ≠ 0 → |t| ≤ δ →
        chartPt (D.point a) (D.point b) s t ∉ image D := by
  have hx0 : x ∈ openSegment ℝ (D.point a) (D.point b) := hx
  rw [openSegment_eq_image'] at hx0
  obtain ⟨s0, ⟨h0, h1⟩, rfl⟩ := hx0
  have hm1 := min_le_left s0 (1 - s0)
  have hm2 := min_le_right s0 (1 - s0)
  have hm : 0 < min s0 (1 - s0) := lt_min h0 (by linarith)
  obtain ⟨δ, hδ, htube⟩ := tube D hab (α := min s0 (1 - s0) / 2) (by linarith)
  exact ⟨s0, min s0 (1 - s0) / 2, δ, (chartPt_zero _ _ _).symm, by linarith, by linarith,
    by linarith, by linarith, hδ, htube⟩

/-- Local structure along an edge: near a point of the open segment of `ab`, every
point off the image lies in one of the two side faces. -/
theorem edge_chart [Finite V] (D : StraightLineDrawing G) {a b : V} (hab : G.Adj a b)
    {x : Point} (hx : x ∈ edgeSeg D a b) :
    ∃ r > 0, ∀ y ∈ Metric.ball x r, y ∉ image D →
      y ∈ edgeFace D a b true ∨ y ∈ edgeFace D a b false := by
  obtain ⟨s0, α, δ, rfl, hα, hα2, hs0, hs1, hδ, htube⟩ := edge_setup D hab hx
  have hpq : D.point a ≠ D.point b := D.injective.ne hab.ne
  set p := D.point a
  set q := D.point b
  have hO : IsOpen ({y | α < sCoord p q y} ∩ {y | sCoord p q y < 1 - α} ∩
      {y | |tCoord p q y| < δ}) :=
    ((isOpen_lt continuous_const (continuous_sCoord p q)).inter
      (isOpen_lt (continuous_sCoord p q) continuous_const)).inter
      (isOpen_lt (continuous_abs.comp (continuous_tCoord p q)) continuous_const)
  have hxO : chartPt p q s0 0 ∈ {y | α < sCoord p q y} ∩ {y | sCoord p q y < 1 - α} ∩
      {y | |tCoord p q y| < δ} := by
    simp only [mem_inter_iff, mem_ofPred_eq, sCoord_chartPt hpq, tCoord_chartPt hpq, abs_zero]
    exact ⟨⟨hs0, hs1⟩, hδ⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO _ hxO
  refine ⟨r, hr, fun y hy hyI => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hball hy
  simp only [mem_ofPred_eq] at h1 h2 h3
  have hy' : y = chartPt p q (sCoord p q y) (tCoord p q y) := (chartPt_coords hpq y).symm
  have htne : tCoord p q y ≠ 0 := by
    intro h0
    apply hyI
    rw [hy', h0]
    exact segment_subset_image D hab (chartPt_mem_segment ⟨by linarith, by linarith⟩)
  have hce := chartPt_mem_edgeFace D hab hα2 hδ htube (t := tCoord p q y) h1.le h2.le
  rw [hy']
  rcases lt_or_gt_of_ne htne with hneg | hpos
  · exact Or.inr (hce.2 (by linarith [(abs_lt.1 h3).1]) hneg)
  · exact Or.inl (hce.1 hpos (by linarith [(abs_lt.1 h3).2]))

/-- Every point of the open segment of `ab` lies in the closure of both side faces. -/
theorem edgeSeg_subset_closure_edgeFace [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) (s : Bool) : edgeSeg D a b ⊆ closure (edgeFace D a b s) := by
  intro x hx
  obtain ⟨s0, α, δ, rfl, hα, hα2, hs0, hs1, hδ, htube⟩ := edge_setup D hab hx
  have hcont : Continuous fun t : ℝ => chartPt (D.point a) (D.point b) s0 t := by
    unfold chartPt; fun_prop
  have hT := hcont.tendsto 0
  cases s
  · refine mem_closure_of_tendsto (hT.mono_left (nhdsWithin_le_nhds (s := Iio 0))) ?_
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.2 hδ)] with t ht
    exact (chartPt_mem_edgeFace D hab hα2 hδ htube hs0.le hs1.le).2 ht.1.le ht.2
  · refine mem_closure_of_tendsto (hT.mono_left (nhdsWithin_le_nhds (s := Ioi 0))) ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    exact (chartPt_mem_edgeFace D hab hα2 hδ htube hs0.le hs1.le).1 ht.1 ht.2.le

/-- A face whose closure meets the open segment of `ab` is one of its two side faces. -/
theorem eq_edgeFace_of_mem_closure [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) {F : Set Point} (hF : F ∈ faces D) {x : Point}
    (hx : x ∈ edgeSeg D a b) (hxF : x ∈ closure F) :
    F = edgeFace D a b true ∨ F = edgeFace D a b false := by
  obtain ⟨r, hr, hchart⟩ := edge_chart D hab hx
  obtain ⟨y, hyF, hyx⟩ := Metric.mem_closure_iff.1 hxF r hr
  have hyI : y ∉ image D := subset_compl_of_mem_faces D hF hyF
  rcases hchart y (by rw [Metric.mem_ball, dist_comm]; exact hyx) hyI with h | h
  · exact Or.inl (eq_of_mem_faces D hF (edgeFace_mem_faces D hab true) hyF h)
  · exact Or.inr (eq_of_mem_faces D hF (edgeFace_mem_faces D hab false) hyF h)

end Lax909950Proofs
