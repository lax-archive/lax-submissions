import Lax303502Proofs.PlaneCells

set_option autoImplicit false

namespace Lax303502Proofs.SP

/-- The fixed triangle above the terminal segment. -/
def Triangle (p : Point) : Prop := 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.2 ≤ 1-p.1

theorem Triangle.x_bounds {p : Point} (h : Triangle p) : 0 ≤ p.1 ∧ p.1 ≤ 1 := by
  obtain ⟨h₀,h₁,h₂⟩ := h
  constructor <;> linarith

theorem Triangle.mix {p q : Point} (hp : Triangle p) (hq : Triangle q)
    {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) : Triangle (mix u p q) := by
  obtain ⟨hp₀,hp₁,hp₂⟩ := hp
  obtain ⟨hq₀,hq₁,hq₂⟩ := hq
  have hn : 0≤1-u := by linarith
  dsimp [Triangle,SP.mix]
  refine ⟨by positivity,?_,?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr hp₁),
      mul_nonneg hu (sub_nonneg.mpr hq₁)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr hp₂),
      mul_nonneg hu (sub_nonneg.mpr hq₂)]

/-- Positive separation of the nonterminal vertices from the baseline.
Keeping this explicit makes the construction independent of finite extrema. -/
structure Frame {V : Type*} (S : Set V) (p : V → Point) (s t : V) where
  source : p s = (0,0)
  sink : p t = (1,0)
  height : ℝ
  positive : 0 < height
  small : height ≤ 1
  triangle : ∀ v ∈ S, Triangle (p v)
  gap : ∀ v ∈ S, v ≠ s → v ≠ t → height ≤ (p v).2

variable {V : Type*} {S : Set V} {p : V → Point} {s t : V}

theorem Frame.x_zero (F : Frame S p s t) {a : V} (ha : a ∈ S)
    (hx : (p a).1 = 0) : a = s := by
  by_contra hs
  by_cases ht : a = t
  · subst a
    simp [F.sink] at hx
  · have hg := F.gap a ha hs ht
    have hb := (F.triangle a ha).2.1
    have hp := F.positive
    linarith

theorem Frame.x_one (F : Frame S p s t) {a : V} (ha : a ∈ S)
    (hx : (p a).1 = 1) : a = t := by
  by_contra ht
  by_cases hs : a = s
  · subst a
    simp [F.source] at hx
  · have hg := F.gap a ha hs ht
    have hb := (F.triangle a ha).2.2
    have hp := F.positive
    linarith

theorem Frame.y_zero (F : Frame S p s t) {a : V} (ha : a ∈ S)
    (hy : (p a).2 = 0) : a = s ∨ a = t := by
  by_cases hs : a = s
  · exact Or.inl hs
  by_cases ht : a = t
  · exact Or.inr ht
  have hg := F.gap a ha hs ht
  have hp := F.positive
  linarith

theorem mix_eq_zero_endpoint {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : 0 ≤ u) (hu' : u ≤ 1) (he : (1-u)*a+u*b = 0) : a=0 ∨ b=0 := by
  by_cases ha' : a=0
  · exact Or.inl ha'
  right
  have hpa : 0<a := lt_of_le_of_ne ha (Ne.symm ha')
  have hn := mul_nonneg (sub_nonneg.mpr hu') ha
  have hm := mul_nonneg hu hb
  by_cases hu0 : u=0
  · simp [hu0] at he
    exact (ha' he).elim
  · have hu1 : 0<u := lt_of_le_of_ne hu (Ne.symm hu0)
    nlinarith

theorem Frame.mix_x_zero (F : Frame S p s t) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    {u : ℝ} (hu : 0≤u) (hu' : u≤1) (he : (mix u (p a) (p b)).1 = 0) :
    a=s ∨ b=s := by
  rcases mix_eq_zero_endpoint (F.triangle a ha).x_bounds.1
    (F.triangle b hb).x_bounds.1 hu hu' he with h | h
  · exact Or.inl (F.x_zero ha h)
  · exact Or.inr (F.x_zero hb h)

theorem Frame.mix_x_one (F : Frame S p s t) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    {u : ℝ} (hu : 0≤u) (hu' : u≤1) (he : (mix u (p a) (p b)).1 = 1) :
    a=t ∨ b=t := by
  have he' : (1-u)*(1-(p a).1)+u*(1-(p b).1)=0 := by dsimp [mix] at he; nlinarith
  rcases mix_eq_zero_endpoint (sub_nonneg.mpr (F.triangle a ha).x_bounds.2)
    (sub_nonneg.mpr (F.triangle b hb).x_bounds.2) hu hu' he' with h | h
  · exact Or.inl (F.x_one ha (by linarith))
  · exact Or.inr (F.x_one hb (by linarith))

theorem Frame.mix_y_zero (F : Frame S p s t) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    {u : ℝ} (hu : 0≤u) (hu' : u≤1) (he : (mix u (p a) (p b)).2 = 0) :
    (a=s ∨ a=t) ∨ (b=s ∨ b=t) := by
  rcases mix_eq_zero_endpoint (F.triangle a ha).1 (F.triangle b hb).1 hu hu' he with h | h
  · exact Or.inl (F.y_zero ha h)
  · exact Or.inr (F.y_zero hb h)

def squash (k : ℝ) (p : Point) : Point := (p.1,k*p.2)

theorem squash_injective {k : ℝ} (hk : 0<k) : Function.Injective (squash k) := by
  intro p q he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp [squash] at hx hy
  exact Prod.ext hx (mul_left_cancel₀ (ne_of_gt hk) hy)

theorem squash_mix (k u : ℝ) (p q : Point) :
    mix u (squash k p) (squash k q) = squash k (mix u p q) := by
  apply Prod.ext
  · rfl
  · dsimp [mix,squash]; ring

def Frame.squash (F : Frame S p s t) {k : ℝ} (hk : 0<k) (hk' : k≤1) :
    Frame S (squash k ∘ p) s t where
  source := by simp [SP.squash,F.source]
  sink := by simp [SP.squash,F.sink]
  height := k*F.height
  positive := mul_pos hk F.positive
  small := by nlinarith [F.small,F.positive]
  triangle := by
    intro a ha
    obtain ⟨h₀,h₁,h₂⟩ := F.triangle a ha
    dsimp [Function.comp_def,SP.squash,Triangle]
    refine ⟨mul_nonneg hk.le h₀,?_,?_⟩ <;> nlinarith
  gap := by
    intro a ha hs ht
    exact mul_le_mul_of_nonneg_left (F.gap a ha hs ht) hk.le

/-- If a segment enters a triangle thinner than the height gap, any
nonterminal endpoint must have zero weight in that convex combination. -/
theorem Frame.thin_weight (F : Frame S p s t) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (has : a≠s) (hat : a≠t) {u : ℝ} (hu : 0≤u) (hu' : u≤1)
    (h₁ : (mix u (p a) (p b)).2 ≤ F.height/2*(mix u (p a) (p b)).1)
    (h₂ : (mix u (p a) (p b)).2 ≤ F.height/2*(1-(mix u (p a) (p b)).1)) : u=1 := by
  have hgap := F.gap a ha has hat
  have hp := F.positive
  have hax := (F.triangle a ha).x_bounds
  have hn : 0≤1-u := by linarith
  dsimp [mix] at h₁ h₂
  have hlo := mul_le_mul_of_nonneg_left hgap hn
  by_cases hbs : b=s
  · subst b
    simp only [F.source,mul_zero,add_zero] at h₁
    have hx := mul_le_mul_of_nonneg_left hax.2 hn
    have hm := mul_le_mul_of_nonneg_left hx (show 0≤F.height/2 by positivity)
    nlinarith
  by_cases hbt : b=t
  · subst b
    simp only [F.sink,mul_one,mul_zero,add_zero] at h₂
    have hx := mul_nonneg hn hax.1
    have hm := mul_nonneg (show 0≤F.height/2 by positivity) hx
    nlinarith
  · have hgb := F.gap b hb hbs hbt
    have hlo' := mul_le_mul_of_nonneg_left hgb hu
    have hx := (Triangle.mix (F.triangle a ha) (F.triangle b hb) hu hu').x_bounds.2
    dsimp [mix] at hx
    have hm := mul_le_mul_of_nonneg_left hx (show 0≤F.height/2 by positivity)
    nlinarith

theorem mix_swap (u : ℝ) (p q : Point) : mix (1-u) q p = mix u p q := by
  ext <;> dsimp [mix] <;> ring

theorem shared_of_common {a b c d w : V} (h : a=w ∨ b=w) (h' : c=w ∨ d=w) :
    Shared a b c d := by
  rcases h with h | h <;> rcases h' with h' | h' <;> simp_all [Shared]

theorem cross_of_thin {G H : SimpleGraph V} {q : V → Point}
    (F : Frame G.support p s t) (Q : Frame H.support q s t)
    (thin : ∀ c ∈ H.support, ∀ d ∈ H.support, ∀ v : ℝ, 0≤v → v≤1 →
      (mix v (q c) (q d)).2 ≤ F.height/2*(mix v (q c) (q d)).1 ∧
      (mix v (q c) (q d)).2 ≤ F.height/2*(1-(mix v (q c) (q d)).1)) :
    CrossClean G H p q := by
  intro a b c d u v hab hcd hu hu' hv hv' he
  have hthin := thin c hcd.1 d hcd.2.1 v hv hv'
  rw [← he] at hthin
  have at_source (hs : a=s ∨ b=s) (hz : mix u (p a) (p b) = (0,0)) :
      Shared a b c d := by
    have hx : (mix v (q c) (q d)).1 = 0 := by rw [← he,hz]
    exact shared_of_common hs (Q.mix_x_zero hcd.1 hcd.2.1 hv hv' hx)
  have at_sink (ht : a=t ∨ b=t) (hz : mix u (p a) (p b) = (1,0)) :
      Shared a b c d := by
    have hx : (mix v (q c) (q d)).1 = 1 := by rw [← he,hz]
    exact shared_of_common ht (Q.mix_x_one hcd.1 hcd.2.1 hv hv' hx)
  have at_base (hs : a=s ∨ b=s) (ht : a=t ∨ b=t)
      (hz : (mix u (p a) (p b)).2 = 0) : Shared a b c d := by
    have hy : (mix v (q c) (q d)).2 = 0 := by rw [← he]; exact hz
    rcases Q.mix_y_zero hcd.1 hcd.2.1 hv hv' hy with (hc | hc) | (hd | hd)
    · exact shared_of_common hs (Or.inl hc)
    · exact shared_of_common ht (Or.inl hc)
    · exact shared_of_common hs (Or.inr hd)
    · exact shared_of_common ht (Or.inr hd)
  by_cases hat : a=s ∨ a=t
  · by_cases hbt : b=s ∨ b=t
    · rcases hat with rfl | rfl <;> rcases hbt with rfl | rfl
      · exact at_source (Or.inl rfl) (by simp [F.source])
      · exact at_base (Or.inl rfl) (Or.inr rfl) (by simp [mix,F.source,F.sink])
      · exact at_base (Or.inr rfl) (Or.inl rfl) (by simp [mix,F.source,F.sink])
      · exact at_sink (Or.inl rfl) (by simp [F.sink])
    · have hw := F.thin_weight hab.2.1 hab.1
        (fun h => hbt (Or.inl h)) (fun h => hbt (Or.inr h))
        (u:=1-u) (by linarith) (by linarith)
        (by simpa only [mix_swap] using hthin.1) (by simpa only [mix_swap] using hthin.2)
      have hu0 : u=0 := by linarith
      rcases hat with rfl | rfl
      · exact at_source (Or.inl rfl) (by simp [hu0,F.source])
      · exact at_sink (Or.inl rfl) (by simp [hu0,F.sink])
  · have hu1 := F.thin_weight hab.1 hab.2.1
      (fun h => hat (Or.inl h)) (fun h => hat (Or.inr h)) hu hu' hthin.1 hthin.2
    by_cases hbt : b=s ∨ b=t
    · rcases hbt with rfl | rfl
      · exact at_source (Or.inr rfl) (by simp [hu1,F.source])
      · exact at_sink (Or.inr rfl) (by simp [hu1,F.sink])
    · have hw := F.thin_weight hab.2.1 hab.1
        (fun h => hbt (Or.inl h)) (fun h => hbt (Or.inr h))
        (u:=1-u) (by linarith) (by linarith)
        (by simpa only [mix_swap] using hthin.1) (by simpa only [mix_swap] using hthin.2)
      linarith

end Lax303502Proofs.SP
