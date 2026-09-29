import Lax303502Proofs.VertexSplit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
The geometric neighbour-order step in the contraction proof of Diestel,
Chapter 4, Lemma 4.4.3 (convex version: Exercise 19). Rays in one consecutive
block of width at most π can be separated from the complementary block.
This proves the half-plane certificate used by `VertexSplit`; it does not
assume a planar characterization. Identifying such a block from the graph's
facial order remains a separate combinatorial/topological step.
-/

set_option autoImplicit false

namespace Lax303502Proofs

open SimpleGraph Lax68.StraightLineDrawings Set

/-- The oriented area of the parallelogram on two vectors. -/
def cross (u v : Point) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Counterclockwise signed twice-area of a triangle. -/
def area (a b c : Point) : ℝ := cross (b-a) (c-a)

/-- The unit vector at the real, unwrapped angle `θ`. -/
noncomputable def ray (θ : ℝ) : Point := (Real.cos θ, Real.sin θ)

theorem cross_ray (α β : ℝ) : cross (ray α) (ray β) = Real.sin (β-α) := by
  simp [cross,ray,Real.sin_sub]
  ring

@[simp] theorem cross_smul_right (u v : Point) (r : ℝ) :
    cross u (r • v) = r * cross u v := by simp [cross]; ring

@[simp] theorem cross_smul_left (u v : Point) (r : ℝ) :
    cross (r • u) v = r * cross u v := by simp [cross]; ring

/-- The signed side functional for the line through the ray `u`. -/
def crossLinear (u : Point) : Point →ₗ[ℝ] ℝ where
  toFun := cross u
  map_add' a b := by simp [cross]; ring
  map_smul' r a := by simp [cross]; ring

/-- A sector supplies two possible separating lines. A retained neighbour
may lie on either side of the sector; each moved neighbour is inside it. -/
theorem splitDirection_of_sector {V : Type*} {G : SimpleGraph V}
    {p : V → Point} {x y : V} {u v w : Point}
    (hx : ∀ a, DrawingCell G x a → a ≠ y →
      cross u (p a-p x) ≤ 0 ∨ cross (p a-p x) v ≤ 0)
    (hy : ∀ b, DrawingCell G y b → b ≠ x →
      0 ≤ cross u (p b-p x) ∧ 0 ≤ cross (p b-p x) v)
    (hwu : 0 < cross u w) (hwv : 0 < cross w v) :
    SplitDirection G p x y w := by
  intro a b ha hb hay hbx _
  obtain ⟨hbu,hbv⟩ := hy b hb hbx
  rcases hx a ha hay with hau | hav
  · exact ⟨crossLinear u,hau,hbu,hwu⟩
  · refine ⟨-crossLinear v,?_,?_,?_⟩
    all_goals dsimp [crossLinear,cross] at *; linarith

/-- Positive multiples of rays in a closed angular interval of width at
most π lie in its closed sector. Zero multiples cover singleton cells. -/
theorem ray_mem_sector {α β θ r : ℝ} (hwidth : β-α ≤ Real.pi)
    (hθ : θ ∈ Icc α β) (hr : 0 ≤ r) :
    0 ≤ cross (ray α) (r • ray θ) ∧
      0 ≤ cross (r • ray θ) (ray β) := by
  simp only [cross_smul_right,cross_smul_left,cross_ray]
  constructor <;> apply mul_nonneg hr
  · apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1,hθ.2]
  · apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1,hθ.2]

/-- A ray on the complementary part of a full turn is outside the open
sector. The endpoints are allowed, for neighbours shared by both stars. -/
theorem ray_outside_sector {α β θ r : ℝ} (hab : α ≤ β)
    (hθ : θ ∈ Icc β (α+2*Real.pi)) (hr : 0 ≤ r) :
    cross (ray α) (r • ray θ) ≤ 0 ∨
      cross (r • ray θ) (ray β) ≤ 0 := by
  simp only [cross_smul_right,cross_smul_left,cross_ray]
  by_cases h : θ ≤ α+Real.pi
  · right
    apply mul_nonpos_of_nonneg_of_nonpos hr
    apply Real.sin_nonpos_of_nonpos_of_neg_pi_le <;> linarith [hθ.1]
  · left
    have hn : Real.sin (θ-α-Real.pi) ≥ 0 := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.2]
    have he : Real.sin (θ-α) = -Real.sin (θ-α-Real.pi) := by
      rw [Real.sin_sub_pi]
      simp
    rw [he]
    exact mul_nonpos_of_nonneg_of_nonpos hr (by linarith)

/-- Cyclically consecutive blocks of incident rays give the splitting
certificate for every direction strictly inside the smaller block.
Angles are unwrapped over one full turn; shared boundary rays may be
represented at either endpoint. The interval may be a semicircle. -/
theorem splitDirection_of_cyclic_rays {V : Type*} {G : SimpleGraph V}
    {p : V → Point} {x y : V} {α β θ : ℝ}
    (hab : α < β) (hwidth : β-α ≤ Real.pi) (hθ : θ ∈ Ioo α β)
    (hx : ∀ a, DrawingCell G x a → a ≠ y →
      ∃ r φ : ℝ, 0 ≤ r ∧ φ ∈ Icc β (α+2*Real.pi) ∧ p a-p x = r • ray φ)
    (hy : ∀ b, DrawingCell G y b → b ≠ x →
      ∃ r φ : ℝ, 0 ≤ r ∧ φ ∈ Icc α β ∧ p b-p x = r • ray φ) :
    SplitDirection G p x y (ray θ) := by
  apply splitDirection_of_sector (u := ray α) (v := ray β)
  · intro a ha hay
    obtain ⟨r,φ,hr,hφ,he⟩ := hx a ha hay
    rw [he]
    exact ray_outside_sector hab.le hφ hr
  · intro b hb hbx
    obtain ⟨r,φ,hr,hφ,he⟩ := hy b hb hbx
    rw [he]
    exact ray_mem_sector hwidth hφ hr
  · rw [cross_ray]
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1,hθ.2]
  · rw [cross_ray]
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1,hθ.2]

/-- Of two consecutive complementary blocks, at least one spans at
most a half-turn, even when there are gaps between them. -/
theorem one_cyclic_block_le_pi {l a b r : ℝ} (hla : l ≤ a) (hbr : b ≤ r) :
    b-a ≤ Real.pi ∨ l+2*Real.pi-r ≤ Real.pi := by
  by_cases h : b-a ≤ Real.pi
  · exact Or.inl h
  · right; linarith

/-- Interchanging the two blocks reverses a valid displacement. Thus the
angular argument can use the smaller of two complementary blocks. -/
theorem splitDirection_swap {V : Type*} {G : SimpleGraph V}
    {p : V → Point} {x y : V} {w : Point} (hxy : p x = p y)
    (h : SplitDirection G p y x w) : SplitDirection G p x y (-w) := by
  intro a b ha hb hay hbx hab
  obtain ⟨f,hb',ha',hw⟩ := h b a hb ha hbx hay hab.symm
  refine ⟨-f,?_,?_,?_⟩
  · simpa [hxy] using neg_nonpos.mpr ha'
  · simpa [hxy] using neg_nonneg.mpr hb'
  · simpa using hw

/-- A nonzero vector in a nondegenerate closed sector lies strictly on
any side of a line that contains both bounding rays strictly on that side.
This propagates the two corner tests to every vertex of a convex face. -/
theorem cross_pos_of_closed_sector {u v w z : Point}
    (huv : 0 < cross u v) (huz : 0 ≤ cross u z) (hzv : 0 ≤ cross z v)
    (hz : z ≠ 0) (hwu : 0 < cross w u) (hwv : 0 < cross w v) :
    0 < cross w z := by
  have hrep : cross u v • z = cross z v • u + cross u z • v := by
    ext <;> simp [cross] <;> ring
  have hsome : 0 < cross z v ∨ 0 < cross u z := by
    by_contra h
    push Not at h
    have h₁ : cross z v = 0 := le_antisymm h.1 hzv
    have h₂ : cross u z = 0 := le_antisymm h.2 huz
    rw [h₁,h₂,zero_smul,zero_smul,add_zero] at hrep
    exact hz ((smul_eq_zero.mp hrep).resolve_left huv.ne')
  have hid : cross u v * cross w z =
      cross z v * cross w u + cross u z * cross w v := by
    simp [cross]
    ring
  have hpos : 0 < cross z v * cross w u + cross u z * cross w v := by
    rcases hsome with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos h hwu) (mul_nonneg huz hwv.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hzv hwu.le) (mul_pos h hwv)
  exact (mul_pos_iff_of_pos_left huv).mp (hid ▸ hpos)

theorem cross_neg_of_closed_sector {u v w z : Point}
    (huv : 0 < cross u v) (huz : 0 ≤ cross u z) (hzv : 0 ≤ cross z v)
    (hz : z ≠ 0) (hwu : cross w u < 0) (hwv : cross w v < 0) :
    cross w z < 0 := by
  have h : 0 < cross (-w) z := cross_pos_of_closed_sector huv huz hzv hz
    (by simp [cross] at *; linarith) (by simp [cross] at *; linarith)
  simp [cross] at *
  linarith

/-- Strict side tests on rays less than a half-turn apart. -/
theorem cross_ray_pos {α β : ℝ} (h : α < β) (hπ : β-α < Real.pi) :
    0 < cross (ray α) (ray β) := by
  rw [cross_ray]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) hπ

theorem cross_ray_neg {α β : ℝ} (h : β < α) (hπ : α-β < Real.pi) :
    cross (ray α) (ray β) < 0 := by
  rw [cross_ray]
  apply Real.sin_neg_of_neg_of_neg_pi_lt <;> linarith

/-- The reversed side test across the exterior, reflex angle of a convex
outer boundary. -/
theorem cross_ray_pos_reflex {α β : ℝ} (hπ : Real.pi < α-β)
    (h2π : α-β < 2*Real.pi) : 0 < cross (ray α) (ray β) := by
  rw [cross_ray]
  have h : 0 < Real.sin (β-α+2*Real.pi) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  simpa using h

theorem cross_ray_neg_reflex {α β : ℝ} (hπ : Real.pi < β-α)
    (h2π : β-α < 2*Real.pi) : cross (ray α) (ray β) < 0 := by
  have h := cross_ray_pos_reflex hπ h2π
  dsimp [cross] at *
  linarith

/-- Choose a splitting direction compatible with both transition corners.
The four angles occur in cyclic order `l ≤ a < b ≤ r < l+2π`; the moved
block is `[a,b]`, the retained block is `[r,l+2π]`. For a bounded transition
face the two bordering rays are on the expected side of the new edge.
For an outer transition face (gap greater than π), that side reverses.
Straight angles are excluded, as required by strict convexity.

This is the small geometric choice left implicit in Kaiser's description
of a convex vertex expansion. In particular, an arbitrary direction in
the moved block need not preserve convexity. -/
theorem exists_convex_split_direction {V : Type*} {G : SimpleGraph V}
    {p : V → Point} {x y : V} {l a b r : ℝ}
    (hla : l ≤ a) (hab : a < b) (hbr : b ≤ r) (hturn : r < l+2*Real.pi)
    (hwidth : b-a ≤ Real.pi) (hl : a-l ≠ Real.pi) (hr : r-b ≠ Real.pi)
    (hx : ∀ v, DrawingCell G x v → v ≠ y →
      ∃ ρ φ : ℝ, 0 ≤ ρ ∧ φ ∈ Icc r (l+2*Real.pi) ∧ p v-p x = ρ • ray φ)
    (hy : ∀ v, DrawingCell G y v → v ≠ x →
      ∃ ρ φ : ℝ, 0 ≤ ρ ∧ φ ∈ Icc a b ∧ p v-p x = ρ • ray φ) :
    ∃ w, SplitDirection G p x y w ∧
      (if a-l < Real.pi then cross w (ray l) < 0 ∧ cross w (ray a) < 0
        else 0 < cross w (ray l) ∧ 0 < cross w (ray a)) ∧
      (if r-b < Real.pi then 0 < cross w (ray b) ∧ 0 < cross w (ray r)
        else cross w (ray b) < 0 ∧ cross w (ray r) < 0) := by
  have cert {α β θ : ℝ} (hlα : l ≤ α) (hαa : α ≤ a) (hbβ : b ≤ β)
      (hβr : β ≤ r) (hαθ : α < θ) (hθβ : θ < β) (hw : β-α ≤ Real.pi) :
      SplitDirection G p x y (ray θ) := by
    apply splitDirection_of_cyclic_rays (lt_trans hαθ hθβ) hw ⟨hαθ,hθβ⟩
    · intro v hv hvy
      obtain ⟨ρ,φ,hρ,hφ,he⟩ := hx v hv hvy
      exact ⟨ρ,φ,hρ,⟨by linarith [hφ.1],by linarith [hφ.2]⟩,he⟩
    · intro v hv hvx
      obtain ⟨ρ,φ,hρ,hφ,he⟩ := hy v hv hvx
      exact ⟨ρ,φ,hρ,⟨by linarith [hφ.1],by linarith [hφ.2]⟩,he⟩
  by_cases hleft : a-l < Real.pi
  · by_cases hright : r-b < Real.pi
    · have hgap : max a (r-Real.pi) < min b (l+Real.pi) := by
        rw [max_lt_iff,lt_min_iff,lt_min_iff]
        exact ⟨⟨hab,by linarith⟩,⟨by linarith,by linarith⟩⟩
      obtain ⟨θ,hθ₁,hθ₂⟩ := exists_between hgap
      have hθa : a < θ := lt_of_le_of_lt (le_max_left _ _) hθ₁
      have hθr : r-Real.pi < θ := lt_of_le_of_lt (le_max_right _ _) hθ₁
      have hθb : θ < b := lt_of_lt_of_le hθ₂ (min_le_left _ _)
      have hθl : θ < l+Real.pi := lt_of_lt_of_le hθ₂ (min_le_right _ _)
      refine ⟨ray θ,cert hla le_rfl le_rfl hbr hθa hθb hwidth,?_⟩
      simp only [if_pos hleft,if_pos hright]
      exact ⟨⟨cross_ray_neg (by linarith) (by linarith),
        cross_ray_neg hθa (by linarith)⟩,
        ⟨cross_ray_pos hθb (by linarith),cross_ray_pos (by linarith) (by linarith)⟩⟩
    · have hright' : Real.pi < r-b := lt_of_le_of_ne (le_of_not_gt hright) hr.symm
      obtain ⟨θ,hbθ,hθr⟩ := exists_between (show b < r-Real.pi by linarith)
      let β := (θ+(r-Real.pi))/2
      have hθβ : θ < β := by dsimp [β]; linarith
      have hβr : β ≤ r := by dsimp [β]; linarith [Real.pi_pos]
      have hw : β-a ≤ Real.pi := by dsimp [β]; linarith
      refine ⟨ray θ,cert hla le_rfl (by linarith) hβr (by linarith) hθβ hw,?_⟩
      simp only [if_pos hleft,if_neg hright]
      exact ⟨⟨cross_ray_neg (by linarith) (by linarith),
        cross_ray_neg (by linarith) (by linarith)⟩,
        ⟨cross_ray_neg hbθ (by linarith),cross_ray_neg_reflex (by linarith) (by linarith)⟩⟩
  · have hleft' : Real.pi < a-l := lt_of_le_of_ne (le_of_not_gt hleft) hl.symm
    have hright : r-b < Real.pi := by linarith
    obtain ⟨θ,hlθ,hθa⟩ := exists_between (show l+Real.pi < a by linarith)
    let α := (l+Real.pi+θ)/2
    have hαθ : α < θ := by dsimp [α]; linarith
    have hlα : l ≤ α := by dsimp [α]; linarith [Real.pi_pos]
    have hw : b-α ≤ Real.pi := by dsimp [α]; linarith
    refine ⟨ray θ,cert hlα (by linarith) le_rfl hbr hαθ (by linarith) hw,?_⟩
    simp only [if_neg hleft,if_pos hright]
    exact ⟨⟨cross_ray_pos_reflex (by linarith) (by linarith),
      cross_ray_pos hθa (by linarith)⟩,
      ⟨cross_ray_pos (by linarith) (by linarith),cross_ray_pos (by linarith) (by linarith)⟩⟩

end Lax303502Proofs
