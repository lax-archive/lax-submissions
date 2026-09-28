import Lax303502Proofs.EdgeGeometry
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

namespace Lax303502Proofs
namespace Polygonal

open SimpleGraph Lax68.StraightLineDrawings

variable {V : Type*} {G : SimpleGraph V}

/-- The geometric trace of a walk, including the vertex of a zero-length walk. -/
def trace (D : StraightLineDrawing G) : {a b : V} → G.Walk a b → Set Point
  | a, _, .nil => {D.point a}
  | a, _, .cons (v := b) _ P => segment ℝ (D.point a) (D.point b) ∪ trace D P

theorem vertex_mem_segment_iff (D : StraightLineDrawing G) {a b x : V}
    (h : G.Adj a b) : D.point x ∈ segment ℝ (D.point a) (D.point b) ↔ x = a ∨ x = b := by
  constructor
  · intro hx
    by_contra hn
    push Not at hn
    exact D.noVertexOnEdge h hn.1 hn.2 hx
  · rintro (rfl | rfl)
    · exact left_mem_segment ..
    · exact right_mem_segment ..

/-- The trace contains exactly the drawn vertices in the walk's support. -/
theorem vertex_mem_trace_iff (D : StraightLineDrawing G) {a b x : V} (P : G.Walk a b) :
    D.point x ∈ trace D P ↔ x ∈ P.support := by
  induction P with
  | nil => simp [trace,D.injective.eq_iff]
  | @cons a b c h P ih =>
    simp only [trace,Set.mem_union,vertex_mem_segment_iff D h,ih,Walk.support_cons,
      List.mem_cons]
    have hb := P.start_mem_support
    constructor
    · rintro ((h | rfl) | h)
      · exact Or.inl h
      · exact Or.inr hb
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

/-- Every trace point is either a drawn vertex or lies on one of the walk's edges. -/
theorem mem_trace_cases (D : StraightLineDrawing G) {a b : V} (P : G.Walk a b)
    {z : Point} (hz : z ∈ trace D P) :
    (∃ x ∈ P.support, z = D.point x) ∨
      ∃ x y, s(x,y) ∈ P.edges ∧ z ∈ segment ℝ (D.point x) (D.point y) := by
  induction P with
  | nil => exact Or.inl ⟨_,by simp, hz⟩
  | @cons a b c h P ih =>
    rcases hz with hz | hz
    · exact Or.inr ⟨a,b,by simp,hz⟩
    · rcases ih hz with ⟨x,hx,hz⟩ | ⟨x,y,hxy,hz⟩
      · exact Or.inl ⟨x,by simp [hx],hz⟩
      · exact Or.inr ⟨x,y,by simp [hxy],hz⟩

/-- Walks sharing no edge can intersect geometrically only at a shared vertex. -/
theorem trace_intersection (D : StraightLineDrawing G) {a b c d : V}
    (P : G.Walk a b) (Q : G.Walk c d)
    (he : ∀ e, e ∈ P.edges → e ∉ Q.edges)
    {z : Point} (hz : z ∈ trace D P) (hz' : z ∈ trace D Q) :
    ∃ x, x ∈ P.support ∧ x ∈ Q.support ∧ z = D.point x := by
  have hP := hz
  rcases mem_trace_cases D P hz with ⟨x,hx,rfl⟩ | ⟨x,y,hxy,hz⟩
  · exact ⟨x,hx,(vertex_mem_trace_iff D Q).mp hz',rfl⟩
  rcases mem_trace_cases D Q hz' with ⟨u,hu,rfl⟩ | ⟨u,v,huv,hz'⟩
  · exact ⟨u,(vertex_mem_trace_iff D P).mp hP,hu,rfl⟩
  have hp : G.Adj x y := P.edges_subset_edgeSet hxy
  have hq : G.Adj u v := Q.edges_subset_edgeSet huv
  have hne : ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
    rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact he _ hxy huv
    · exact he _ hxy (by simpa only [Sym2.eq_swap] using huv)
  obtain ⟨w,hw,hw',hzw⟩ := distinct_edges_intersection D hp hq hne hz hz'
  refine ⟨w,?_,?_,hzw⟩
  · rcases hw with rfl | rfl
    · exact P.fst_mem_support_of_mem_edges hxy
    · exact P.snd_mem_support_of_mem_edges hxy
  · rcases hw' with rfl | rfl
    · exact Q.fst_mem_support_of_mem_edges huv
    · exact Q.snd_mem_support_of_mem_edges huv

/-- Traverse the segments of a walk. The last edge has no constant waiting interval. -/
noncomputable def walkPath (D : StraightLineDrawing G) :
    {a b : V} → (P : G.Walk a b) → Path (D.point a) (D.point b)
  | a, _, .nil => Path.refl (D.point a)
  | a, b, .cons _ .nil => Path.segment (D.point a) (D.point b)
  | a, _, .cons (v := b) _ (.cons h P) =>
    (Path.segment (D.point a) (D.point b)).trans (walkPath D (.cons h P))

theorem range_walkPath (D : StraightLineDrawing G) {a b : V} (P : G.Walk a b) :
    Set.range (walkPath D P) = trace D P := by
  induction P with
  | nil => simp [walkPath,trace]
  | @cons a b c h P ih =>
    cases P with
    | nil =>
      simp only [walkPath,Path.range_segment,trace]
      exact (Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (right_mem_segment ..))).symm
    | cons h' Q =>
      simpa only [walkPath,Path.trans_range,Path.range_segment,trace] using
        (congrArg (fun S => segment ℝ (D.point a) (D.point b) ∪ S) ih)

/-- The trace is a finite union of closed line segments. -/
theorem trace_finite_segments (D : StraightLineDrawing G) {a b : V} (P : G.Walk a b) :
    ∃ S : Finset (Point × Point), trace D P = ⋃ e ∈ S, segment ℝ e.1 e.2 := by
  classical
  induction P with
  | @nil a => exact ⟨{(D.point a,D.point a)},by simp [trace]⟩
  | @cons a b c h P ih =>
    obtain ⟨S,hS⟩ := ih
    exact ⟨insert (D.point a,D.point b) S,by simp [trace,hS]⟩

/-- A nontrivial graph path is realized as an injective continuous polygonal path. -/
theorem injective_walkPath (D : StraightLineDrawing G) {a b : V} (P : G.Walk a b)
    (hp : P.IsPath) (hn : ¬P.Nil) : Function.Injective (walkPath D P) := by
  induction P with
  | nil => exact (hn Walk.Nil.nil).elim
  | @cons a b c h P ih =>
    obtain ⟨hp,ha⟩ := (Walk.cons_isPath_iff h P).mp hp
    cases P with
    | nil => exact injective_segment (D.injective.ne h.ne)
    | cons h' Q =>
      apply injective_trans _ _ (injective_segment (D.injective.ne h.ne)) (ih hp (by simp))
      intro z hz hz'
      rw [Path.range_segment] at hz
      rw [range_walkPath] at hz'
      let P := Walk.cons h' Q
      have he : ∀ e, e ∈ h.toWalk.edges → e ∉ P.edges := by
        intro e he he'
        have heq : e = s(a,b) := by simpa using he
        subst e
        exact ha (P.fst_mem_support_of_mem_edges he')
      have hz0 : z ∈ trace D h.toWalk := Or.inl hz
      obtain ⟨x,hx,hx',hzx⟩ := trace_intersection D h.toWalk P he hz0 hz'
      have hx0 : x = a ∨ x = b := by simpa using hx
      rcases hx0 with rfl | rfl
      · exact (ha hx').elim
      · exact hzx

end Polygonal
end Lax303502Proofs
