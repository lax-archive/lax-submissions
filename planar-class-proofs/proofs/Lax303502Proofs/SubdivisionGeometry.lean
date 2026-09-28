import Lax303502Proofs.PolygonalWalks
import Lax68.GraphTopologicalMinors

set_option autoImplicit false

namespace Lax303502Proofs
namespace Polygonal

open SimpleGraph Lax68.StraightLineDrawings Lax68.GraphTopologicalMinors

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem branch_mem_route_iff (M : TopologicalMinorModel H G)
    {a b : W} (h : H.Adj a b) (w : W) :
    M.branch w ∈ (M.route h).support ↔ w = a ∨ w = b := by
  constructor
  · intro hw
    by_contra hn
    push Not at hn
    exact M.branch_avoids_interiors h w ⟨hw,M.branch.injective.ne hn.1,
      M.branch.injective.ne hn.2⟩
  · rintro (rfl | rfl)
    · exact (M.route h).start_mem_support
    · exact (M.route h).end_mem_support

/-- Distinct subdivision routes share only branch vertices representing common ends. -/
theorem route_support_intersection (M : TopologicalMinorModel H G)
    {a b c d : W} (hab : H.Adj a b) (hcd : H.Adj c d)
    (hne : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))
    {x : V} (hx : x ∈ (M.route hab).support) (hx' : x ∈ (M.route hcd).support) :
    ∃ w, x = M.branch w ∧ (w = a ∨ w = b) ∧ (w = c ∨ w = d) := by
  by_cases ha : x = M.branch a
  · exact ⟨a,ha,Or.inl rfl,(branch_mem_route_iff M hcd a).mp (ha ▸ hx')⟩
  by_cases hb : x = M.branch b
  · exact ⟨b,hb,Or.inr rfl,(branch_mem_route_iff M hcd b).mp (hb ▸ hx')⟩
  have hi : x ∈ walkInterior (M.route hab) := ⟨hx,ha,hb⟩
  have hc : x ≠ M.branch c := fun he => M.branch_avoids_interiors hab c (he ▸ hi)
  have hd : x ≠ M.branch d := fun he => M.branch_avoids_interiors hab d (he ▸ hi)
  exact (Set.disjoint_left.mp (M.route_interiors_disjoint hab hcd hne) hi ⟨hx',hc,hd⟩).elim

theorem route_edges_disjoint (M : TopologicalMinorModel H G)
    {a b c d : W} (hab : H.Adj a b) (hcd : H.Adj c d)
    (hne : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    ∀ e, e ∈ (M.route hab).edges → e ∉ (M.route hcd).edges := by
  intro e he he'
  induction e using Sym2.inductionOn with | _ x y =>
  have hx := route_support_intersection M hab hcd hne
    ((M.route hab).fst_mem_support_of_mem_edges he)
    ((M.route hcd).fst_mem_support_of_mem_edges he')
  have hy := route_support_intersection M hab hcd hne
    ((M.route hab).snd_mem_support_of_mem_edges he)
    ((M.route hcd).snd_mem_support_of_mem_edges he')
  obtain ⟨u,rfl,hu,hu'⟩ := hx
  obtain ⟨v,rfl,hv,hv'⟩ := hy
  have huv : u ≠ v := fun h =>
    (show G.Adj (M.branch u) (M.branch v) from (M.route hab).edges_subset_edgeSet he).ne
      (congrArg M.branch h)
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    rcases hu' with h | h <;> rcases hv' with h' | h' <;> simp_all

/-- The polygonal realizations of distinct subdivision routes meet only at drawn common ends. -/
theorem subdivision_trace_intersection (D : StraightLineDrawing G)
    (M : TopologicalMinorModel H G)
    {a b c d : W} (hab : H.Adj a b) (hcd : H.Adj c d)
    (hne : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))
    {z : Point} (hz : z ∈ trace D (M.route hab)) (hz' : z ∈ trace D (M.route hcd)) :
    ∃ w, (w = a ∨ w = b) ∧ (w = c ∨ w = d) ∧ z = D.point (M.branch w) := by
  obtain ⟨x,hx,hx',hzx⟩ := trace_intersection D _ _ (route_edges_disjoint M hab hcd hne) hz hz'
  obtain ⟨w,rfl,hw,hw'⟩ := route_support_intersection M hab hcd hne hx hx'
  exact ⟨w,hw,hw',hzx⟩

theorem interior_reverse {a b : V} (P : G.Walk a b) :
    walkInterior P.reverse = walkInterior P := by
  ext x
  simp [walkInterior,and_comm,and_assoc]

/-- Choose one route for each unordered edge, using the vertex order to fix its orientation. -/
noncomputable def orient [LinearOrder W] (M : TopologicalMinorModel H G) :
    TopologicalMinorModel H G where
  branch := M.branch
  route := fun {a b} h => if a < b then M.route h else (M.route h.symm).reverse
  route_isPath := by
    intro a b h
    split_ifs
    · exact M.route_isPath h
    · exact (M.route_isPath h.symm).reverse
  branch_avoids_interiors := by
    intro a b h w
    split_ifs
    · exact M.branch_avoids_interiors h w
    · simpa only [interior_reverse] using M.branch_avoids_interiors h.symm w
  route_interiors_disjoint := by
    intro a b c d hab hcd hne
    split_ifs <;> try simp only [interior_reverse]
    · exact M.route_interiors_disjoint hab hcd hne
    · exact M.route_interiors_disjoint hab hcd.symm (by aesop)
    · exact M.route_interiors_disjoint hab.symm hcd (by aesop)
    · exact M.route_interiors_disjoint hab.symm hcd.symm (by aesop)

theorem orient_reverse [LinearOrder W] (M : TopologicalMinorModel H G)
    {a b : W} (h : H.Adj a b) : (orient M).route h.symm = ((orient M).route h).reverse := by
  rcases lt_or_gt_of_ne h.ne with hlt | hgt
  · simp [orient,hlt,not_lt.mpr hlt.le]
  · simp [orient,hgt,not_lt.mpr hgt.le]

theorem trace_reverse (D : StraightLineDrawing G) {a b : V} (P : G.Walk a b) :
    trace D P.reverse = trace D P := by
  have subset {a b c d : V} (P : G.Walk a b) (Q : G.Walk c d)
      (hs : ∀ x, x ∈ P.support → x ∈ Q.support)
      (he : ∀ e, e ∈ P.edges → e ∈ Q.edges) : trace D P ⊆ trace D Q := by
    intro z hz
    rcases mem_trace_cases D P hz with ⟨x,hx,rfl⟩ | ⟨x,y,hxy,hz⟩
    · exact (vertex_mem_trace_iff D Q).mpr (hs x hx)
    · have hxy' := he _ hxy
      clear hs he
      induction Q with
      | nil => simp at hxy'
      | @cons a b c h Q ih =>
        rcases List.mem_cons.mp hxy' with heq | hmem
        · left
          rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact hz
          · simpa only [segment_symm] using hz
        · exact Or.inr (ih hmem)
  apply Set.Subset.antisymm
  · exact subset _ _ (by simp) (by simp)
  · exact subset _ _ (by simp) (by simp)

/-- A plane drawing whose edges are injective polygonal arcs. Each unoriented
edge has a well-defined image, and distinct edges meet only at common ends. -/
structure PolygonalDrawing (H : SimpleGraph W) where
  point : W → Point
  injective : Function.Injective point
  arc : ∀ {a b : W}, H.Adj a b → Path (point a) (point b)
  arc_injective : ∀ {a b : W} (h : H.Adj a b), Function.Injective (arc h)
  arc_segments : ∀ {a b : W} (h : H.Adj a b),
    ∃ S : Finset (Point × Point), Set.range (arc h) = ⋃ e ∈ S, segment ℝ e.1 e.2
  reverse_range : ∀ {a b : W} (h : H.Adj a b), Set.range (arc h.symm) = Set.range (arc h)
  vertex_on_arc : ∀ {a b : W} (h : H.Adj a b) (w : W),
    point w ∈ Set.range (arc h) → w = a ∨ w = b
  arc_intersection : ∀ {a b c d : W} (hab : H.Adj a b) (hcd : H.Adj c d),
    ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
    ∀ z, z ∈ Set.range (arc hab) → z ∈ Set.range (arc hcd) →
    ∃ w, (w = a ∨ w = b) ∧ (w = c ∨ w = d) ∧ z = point w

/-- Realize any subdivision model in a straight-line drawing as a polygonal drawing.
This is the geometric subdivision step in Diestel, Section 4.2. It uses no
planarity characterization or straightening theorem. -/
noncomputable def subdivisionDrawing [LinearOrder W] (D : StraightLineDrawing G)
    (M : TopologicalMinorModel H G) : PolygonalDrawing H where
  point := D.point ∘ (orient M).branch
  injective := D.injective.comp (orient M).branch.injective
  arc := fun h => walkPath D ((orient M).route h)
  arc_injective := fun h => injective_walkPath D _ ((orient M).route_isPath h)
    (Walk.not_nil_of_ne ((orient M).branch.injective.ne h.ne))
  arc_segments := by
    intro a b h
    rw [range_walkPath]
    exact trace_finite_segments D _
  reverse_range := by
    intro a b h
    rw [range_walkPath,range_walkPath,orient_reverse,trace_reverse]
  vertex_on_arc := by
    intro a b h w hw
    rw [range_walkPath,Function.comp_apply,vertex_mem_trace_iff] at hw
    exact (branch_mem_route_iff (orient M) h w).mp hw
  arc_intersection := by
    intro a b c d hab hcd hne z hz hz'
    rw [range_walkPath] at hz hz'
    exact subdivision_trace_intersection D (orient M) hab hcd hne hz hz'

end Polygonal
end Lax303502Proofs
