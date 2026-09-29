import Lax303502Proofs.CyclicVertexSplit
import Mathlib.Analysis.Convex.Hull

/-!
Convex boundary control for the local vertex expansion in Diestel's
contraction proof (Chapter 4, Exercise 19; see also Kaiser, Lecture 3,
page 4). Moving one vertex makes every signed triangle area affine in the
displacement. Strict inequalities persist; collapsed triangles open with
the sign of their linear coefficient. Finiteness supplies one displacement
bound for all boundary inequalities and all drawing cells.

Boundaries are supplied as cyclic vertex lists. The convexity certificate
requires every other vertex strictly to the left of each oriented edge;
`StrictConvexBoundary.convexHull_side` relates it to the actual convex hull.
The outer boundary can be included with the same counterclockwise
orientation around its bounded polygon. No claim that the lists enumerate
the graph's faces is made here; that belongs to the remaining face theory.
-/

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.StraightLineDrawings Set Topology Filter

/-- Every oriented polygon edge has all other vertices strictly to its
left. Indices run cyclically, including the last-to-first edge. -/
def StrictConvexBoundary {n : ℕ} (q : Fin (n+3) → Point) : Prop :=
  ∀ i j, j ≠ i → j ≠ i+1 → 0 < area (q i) (q (i+1)) (q j)

/-- The supporting half-plane inequalities also hold throughout the
convex hull, not merely at the listed vertices. -/
theorem StrictConvexBoundary.convexHull_side {n : ℕ} {q : Fin (n+3) → Point}
    (hq : StrictConvexBoundary q) (i : Fin (n+3)) :
    convexHull ℝ (range q) ⊆ {z | 0 ≤ area (q i) (q (i+1)) z} := by
  apply convexHull_min
  · rintro _ ⟨j,rfl⟩
    by_cases hji : j = i
    · subst j; simp [area,cross,mul_comm]
    by_cases hjn : j = i+1
    · subst j; simp [area,cross,mul_comm]
    exact (hq i j hji hjn).le
  · intro z hz w hw s t hs ht hst
    change 0 ≤ crossLinear (q (i+1)-q i) (s • z + t • w - q i)
    have he : s • z + t • w - q i = s • (z-q i) + t • (w-q i) := by
      rw [smul_sub,smul_sub,sub_add_sub_comm,← add_smul,hst,one_smul]
    rw [he,map_add,map_smul,map_smul]
    exact add_nonneg (mul_nonneg hs hz) (mul_nonneg ht hw)

/-- Testing a line against just the two neighbours of a polygon corner
is enough: every other polygon vertex lies strictly on that same side.
This connects the angular corner choice to the collapsed-face area tests. -/
theorem StrictConvexBoundary.cross_pos_at_zero {n : ℕ}
    {q : Fin (n+3) → Point} (hq : StrictConvexBoundary q) {w : Point}
    (hnext : 0 < cross w (q 1-q 0))
    (hprev : 0 < cross w (q (Fin.last (n+2))-q 0)) :
    ∀ j, j ≠ 0 → 0 < cross w (q j-q 0) := by
  let last : Fin (n+3) := Fin.last (n+2)
  have hl0 : last ≠ 0 := by simp [last,Fin.ext_iff]
  have hl1 : last ≠ 0+1 := by
    simp [last,Fin.ext_iff]
  have hladd : last+1 = 0 := by
    apply Fin.ext
    simp [last]
  have hsector : 0 < cross (q 1-q 0) (q last-q 0) := by
    simpa [area] using hq 0 last hl0 hl1
  intro j hj
  by_cases hjnext : j = 1
  · simpa [hjnext] using hnext
  by_cases hjprev : j = last
  · simpa [hjprev,last] using hprev
  have huz : 0 < cross (q 1-q 0) (q j-q 0) := by
    simpa [area] using hq 0 j hj (by simpa using hjnext)
  have hzv : 0 < cross (q j-q 0) (q last-q 0) := by
    have h := hq last j hjprev (by rwa [hladd])
    rw [hladd] at h
    have he : area (q last) (q 0) (q j) = cross (q j-q 0) (q last-q 0) := by
      simp [area,cross]; ring
    rwa [he] at h
  have hz : q j-q 0 ≠ 0 := by
    intro he
    rw [he] at huz
    simp [cross] at huz
  exact cross_pos_of_closed_sector hsector huz.le hzv.le hz hnext hprev

theorem StrictConvexBoundary.cross_neg_at_zero {n : ℕ}
    {q : Fin (n+3) → Point} (hq : StrictConvexBoundary q) {w : Point}
    (hnext : cross w (q 1-q 0) < 0)
    (hprev : cross w (q (Fin.last (n+2))-q 0) < 0) :
    ∀ j, j ≠ 0 → cross w (q j-q 0) < 0 := by
  have h := hq.cross_pos_at_zero (w := -w)
    (by simp [cross] at *; linarith) (by simp [cross] at *; linarith)
  intro j hj
  have hh := h j hj
  simp [cross] at hh ⊢
  linarith

/-- The coefficient of the displacement in the signed area of a triangle.
Only the vertex `y` moves. -/
def splitAreaSlope {V : Type*} [DecidableEq V] (p : V → Point)
    (y : V) (w : Point) (a b c : V) : ℝ :=
  cross ((if b=y then w else 0) - (if a=y then w else 0)) (p c-p a) +
    cross (p b-p a) ((if c=y then w else 0) - (if a=y then w else 0))

/-- There is no quadratic term: the only displacements are `0` and `w`,
whose pairwise determinants vanish. -/
theorem area_splitPlacement {V : Type*} [DecidableEq V]
    (p : V → Point) (y : V) (w : Point) (t : ℝ) (a b c : V) :
    area (splitPlacement p y w t a) (splitPlacement p y w t b)
        (splitPlacement p y w t c) =
      area (p a) (p b) (p c) + t * splitAreaSlope p y w a b c := by
  by_cases ha : a=y <;> by_cases hb : b=y <;> by_cases hc : c=y
  all_goals simp [area,cross,splitPlacement,splitAreaSlope,ha,hb,hc] <;> ring

/-- For a newly opened triangle `x,y,z`, the coefficient is just the side
of the displacement line on which `z` lies. -/
theorem splitAreaSlope_xy {V : Type*} [DecidableEq V]
    {p : V → Point} {x y z : V} (hxy : x ≠ y) (hzy : z ≠ y)
    (hp : p x = p y) (w : Point) :
    splitAreaSlope p y w x y z = cross w (p z-p x) := by
  simp [splitAreaSlope,hxy,hzy,hp,cross]

/-- Positivity at zero, or a positive slope from zero, suffices uniformly
for any finite collection of affine inequalities. -/
theorem affine_positive_small {I : Type*} [Finite I] (a b : I → ℝ)
    (h : ∀ i, 0 < a i ∨ (a i = 0 ∧ 0 < b i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε → ∀ i, 0 < a i + t*b i := by
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < a i → 0 < a i+t*b i := by
    simp only [Filter.eventually_all]
    intro i hi
    have hc : Continuous (fun t : ℝ => a i+t*b i) := by fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by simpa using hi))
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε,hε,?_⟩
  intro t ht htε i
  rcases h i with hi | ⟨hi,hb⟩
  · exact he (by simpa [Real.dist_eq,abs_of_pos ht] using htε) i hi
  · rw [hi,zero_add]
    exact mul_pos ht hb

/-- Simultaneously preserve any finite set of oriented triangle tests.
The zero-area cases must open in the specified orientation. -/
theorem split_orientations_small {V : Type*} [Finite V] [DecidableEq V]
    (p : V → Point) (y : V) (w : Point) (T : V → V → V → Prop)
    (h : ∀ a b c, T a b c → 0 < area (p a) (p b) (p c) ∨
      (area (p a) (p b) (p c) = 0 ∧ 0 < splitAreaSlope p y w a b c)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε → ∀ a b c, T a b c →
      0 < area (splitPlacement p y w t a) (splitPlacement p y w t b)
        (splitPlacement p y w t c) := by
  let I := {s : V × V × V // T s.1 s.2.1 s.2.2}
  obtain ⟨ε,hε,he⟩ := affine_positive_small
    (fun s : I => area (p s.val.1) (p s.val.2.1) (p s.val.2.2))
    (fun s : I => splitAreaSlope p y w s.val.1 s.val.2.1 s.val.2.2)
    (fun s => h _ _ _ s.property)
  refine ⟨ε,hε,?_⟩
  intro t ht htε a b c habc
  rw [area_splitPlacement]
  exact he t ht htε ⟨(a,b,c),habc⟩

/-- Preserve supplied polygon boundaries, independently of the graph
whose edges they may bound. -/
theorem split_boundaries_small {V F : Type*} [Finite V] [DecidableEq V]
    (p : V → Point) (y : V) (w : Point)
    (n : F → ℕ) (c : ∀ f, Fin (n f+3) → V)
    (hc : ∀ f i j, j ≠ i → j ≠ i+1 →
      0 < area (p (c f i)) (p (c f (i+1))) (p (c f j)) ∨
        (area (p (c f i)) (p (c f (i+1))) (p (c f j)) = 0 ∧
          0 < splitAreaSlope p y w (c f i) (c f (i+1)) (c f j))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε →
      ∀ f, StrictConvexBoundary (splitPlacement p y w t ∘ c f) := by
  let T := fun a b z => ∃ f i j, j ≠ i ∧ j ≠ i+1 ∧
    c f i = a ∧ c f (i+1) = b ∧ c f j = z
  have hT : ∀ a b z, T a b z → 0 < area (p a) (p b) (p z) ∨
      (area (p a) (p b) (p z) = 0 ∧ 0 < splitAreaSlope p y w a b z) := by
    rintro a b z ⟨f,i,j,hji,hjn,rfl,rfl,rfl⟩
    exact hc f i j hji hjn
  obtain ⟨ε,hε,he⟩ := split_orientations_small p y w T hT
  refine ⟨ε,hε,?_⟩
  intro t ht htε f i j hji hjn
  exact he t ht htε _ _ _ ⟨f,i,j,hji,hjn,rfl,rfl,rfl⟩

/-- A drawing and all supplied convex polygon boundaries survive one
common sufficiently small split. The face index type need not itself be
finite: on a finite graph there are only finitely many triangle tests. -/
theorem vertex_split_convex_small {V F : Type*} [Finite V] [DecidableEq V]
    {G : SimpleGraph V} {x y : V} (hxy : x ≠ y)
    (D : StraightLineDrawing (edgeContract G hxy)) {w : Point}
    (hw : SplitDirection G (D.point ∘ contractMap hxy) x y w)
    (n : F → ℕ) (c : ∀ f, Fin (n f+3) → V)
    (hc : ∀ f i j, j ≠ i → j ≠ i+1 →
      let p := D.point ∘ contractMap hxy
      0 < area (p (c f i)) (p (c f (i+1))) (p (c f j)) ∨
        (area (p (c f i)) (p (c f (i+1))) (p (c f j)) = 0 ∧
          0 < splitAreaSlope p y w (c f i) (c f (i+1)) (c f j))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε →
      SeparatedPlacement G (splitPlacement (D.point ∘ contractMap hxy) y w t) ∧
      ∀ f, StrictConvexBoundary (splitPlacement (D.point ∘ contractMap hxy) y w t ∘ c f) := by
  obtain ⟨ε,hε,he⟩ := split_boundaries_small (D.point ∘ contractMap hxy) y w n c hc
  obtain ⟨δ,hδ,hd⟩ := vertex_split_small hxy D hw
  refine ⟨min ε δ,lt_min hε hδ,?_⟩
  intro t ht htε
  refine ⟨hd t ht (lt_min_iff.mp htε).2,?_⟩
  exact he t ht (lt_min_iff.mp htε).1

end Lax303502Proofs
