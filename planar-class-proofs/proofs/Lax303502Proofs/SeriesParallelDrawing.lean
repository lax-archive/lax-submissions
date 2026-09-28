import Lax303502Proofs.TerminalGeometry

set_option autoImplicit false

namespace Lax303502Proofs.SP

open Lax68.SeriesParallel

structure Drawing {V : Type*} (G : SimpleGraph V) (s t : V) where
  point : V → Point
  frame : Frame G.support point s t
  clean : Clean G point
  source_mem : s ∈ G.support
  sink_mem : t ∈ G.support

variable {V : Type*} {G H : SimpleGraph V} {s m t : V}

noncomputable def Drawing.edge (hst : s≠t) : Drawing (edgeGraph s t) s t := by
  classical
  let p : V → Point := fun v => if v=s then (0,0) else (1,0)
  have ps : p s = (0,0) := by simp [p]
  have pt : p t = (1,0) := by simp [p,hst.symm]
  have terminal (v : V) (hv : v ∈ (edgeGraph s t).support) : v=s ∨ v=t := by
    simpa only [edge_support hst,Set.mem_insert_iff,Set.mem_singleton_iff] using hv
  refine ⟨p,⟨ps,pt,1/4,by norm_num,by norm_num,?_,?_⟩,?_,?_,?_⟩
  · intro v hv
    rcases terminal v hv with rfl | rfl <;> simp [Triangle,ps,pt]
  · intro v hv hvs hvt
    exact ((terminal v hv).elim hvs hvt).elim
  · intro a b c d u v hab hcd hu hu' hv hv' he
    have ha := terminal a hab.1
    have hb := terminal b hab.2.1
    have hc := terminal c hcd.1
    have hd := terminal d hcd.2.1
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr rfl))
      | norm_num [ps,pt,mix] at he
  · rw [edge_support hst]; simp
  · rw [edge_support hst]; simp

noncomputable def Drawing.parallel (D : Drawing G s t) (E : Drawing H s t)
    (meet : ∀ v, v ∈ G.support → v ∈ H.support → v=s ∨ v=t) :
    Drawing (G ⊔ H) s t := by
  let k := D.frame.height/2
  have hk : 0<k := by dsimp [k]; exact half_pos D.frame.positive
  have hk' : k≤1 := by dsimp [k]; linarith [D.frame.small]
  let q := squash k ∘ E.point
  let Q : Frame H.support q s t := E.frame.squash hk hk'
  have agree (v : V) (hg : v ∈ G.support) (hh : v ∈ H.support) : D.point v = q v := by
    rcases meet v hg hh with rfl | rfl
    · rw [D.frame.source,Q.source]
    · rw [D.frame.sink,Q.sink]
  have cross : CrossClean G H D.point q := by
    apply cross_of_thin D.frame Q
    intro c hc d hd v hv hv'
    have hb := Triangle.mix (E.frame.triangle c hc) (E.frame.triangle d hd) hv hv'
    simp only [q,Function.comp_apply,squash_mix]
    change k*(mix v (E.point c) (E.point d)).2 ≤ k*(mix v (E.point c) (E.point d)).1 ∧
      k*(mix v (E.point c) (E.point d)).2 ≤ k*(1-(mix v (E.point c) (E.point d)).1)
    exact ⟨mul_le_mul_of_nonneg_left hb.2.1 hk.le,mul_le_mul_of_nonneg_left hb.2.2 hk.le⟩
  refine ⟨merge G D.point q,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,min D.frame.height Q.height,lt_min D.frame.positive Q.positive,
      (min_le_left _ _).trans D.frame.small,?_,?_⟩
    · rw [merge_left D.source_mem,D.frame.source]
    · rw [merge_left D.sink_mem,D.frame.sink]
    · intro v hv
      rw [support_union] at hv
      rcases hv with hv | hv
      · rw [merge_left hv]; exact D.frame.triangle v hv
      · rw [merge_right agree hv]; exact Q.triangle v hv
    · intro v hv hvs hvt
      rw [support_union] at hv
      rcases hv with hv | hv
      · rw [merge_left hv]; exact (min_le_left _ _).trans (D.frame.gap v hv hvs hvt)
      · rw [merge_right agree hv]; exact (min_le_right _ _).trans (Q.gap v hv hvs hvt)
  · exact clean_merge D.clean (clean_transform E.clean (squash k) (squash_injective hk)
      (squash_mix k)) agree cross
  · rw [support_union]; exact Or.inl D.source_mem
  · rw [support_union]; exact Or.inl D.sink_mem

noncomputable def leftMap (p : Point) : Point := (p.1/2,(p.2+p.1)/4)
noncomputable def rightMap (p : Point) : Point := ((1+p.1)/2,(p.2+1-p.1)/4)

theorem leftMap_injective : Function.Injective leftMap := by
  intro p q he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp [leftMap] at hx hy
  exact Prod.ext (by linarith) (by linarith)

theorem rightMap_injective : Function.Injective rightMap := by
  intro p q he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp [rightMap] at hx hy
  exact Prod.ext (by linarith) (by linarith)

theorem leftMap_mix (u : ℝ) (p q : Point) :
    mix u (leftMap p) (leftMap q) = leftMap (mix u p q) := by
  ext <;> dsimp [mix,leftMap] <;> ring

theorem rightMap_mix (u : ℝ) (p q : Point) :
    mix u (rightMap p) (rightMap q) = rightMap (mix u p q) := by
  ext <;> dsimp [mix,rightMap] <;> ring

theorem Triangle.leftMap {p : Point} (hp : Triangle p) : Triangle (leftMap p) := by
  have hb := hp.x_bounds
  obtain ⟨h₀,h₁,h₂⟩ := hp
  dsimp [Triangle,SP.leftMap]
  constructor
  · linarith
  · constructor <;> linarith

theorem Triangle.rightMap {p : Point} (hp : Triangle p) : Triangle (rightMap p) := by
  have hb := hp.x_bounds
  obtain ⟨h₀,h₁,h₂⟩ := hp
  dsimp [Triangle,SP.rightMap]
  constructor
  · linarith
  · constructor <;> linarith

noncomputable def Drawing.series (D : Drawing G s m) (E : Drawing H m t)
    (meet : ∀ v, v ∈ G.support → v ∈ H.support → v=m) :
    Drawing (G ⊔ H) s t := by
  let p := leftMap ∘ D.point
  let q := rightMap ∘ E.point
  have agree (v : V) (hg : v ∈ G.support) (hh : v ∈ H.support) : p v = q v := by
    have hv := meet v hg hh
    subst v
    simp [p,q,D.frame.sink,E.frame.source,leftMap,rightMap]
  have cross : CrossClean G H p q := by
    intro a b c d u v hab hcd hu hu' hv hv' he
    have hl := (Triangle.mix (D.frame.triangle a hab.1)
      (D.frame.triangle b hab.2.1) hu hu').x_bounds
    have hr := (Triangle.mix (E.frame.triangle c hcd.1)
      (E.frame.triangle d hcd.2.1) hv hv').x_bounds
    change mix u (leftMap (D.point a)) (leftMap (D.point b)) =
      mix v (rightMap (E.point c)) (rightMap (E.point d)) at he
    rw [leftMap_mix,rightMap_mix] at he
    have hx := congrArg Prod.fst he
    dsimp [leftMap,rightMap] at hx
    have h₁ : (mix u (D.point a) (D.point b)).1 = 1 := by linarith
    have h₂ : (mix v (E.point c) (E.point d)).1 = 0 := by linarith
    exact shared_of_common (D.frame.mix_x_one hab.1 hab.2.1 hu hu' h₁)
      (E.frame.mix_x_zero hcd.1 hcd.2.1 hv hv' h₂)
  refine ⟨merge G p q,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,min D.frame.height E.frame.height/4,?_,?_,?_,?_⟩
    · rw [merge_left D.source_mem]
      simp [p,D.frame.source,leftMap]
    · rw [merge_right agree E.sink_mem]
      simp [q,E.frame.sink,rightMap]
    · exact div_pos (lt_min D.frame.positive E.frame.positive) (by norm_num)
    · have h := (min_le_left D.frame.height E.frame.height).trans D.frame.small
      linarith
    · intro v hv
      rw [support_union] at hv
      rcases hv with hv | hv
      · rw [merge_left hv]; exact (D.frame.triangle v hv).leftMap
      · rw [merge_right agree hv]; exact (E.frame.triangle v hv).rightMap
    · intro v hv hvs hvt
      rw [support_union] at hv
      rcases hv with hv | hv
      · rw [merge_left hv]
        have hm := min_le_left D.frame.height E.frame.height
        by_cases hvm : v=m
        · subst v
          simp only [p,Function.comp_apply,D.frame.sink,leftMap]
          linarith [D.frame.small]
        · have hg := D.frame.gap v hv hvs hvm
          have hx := (D.frame.triangle v hv).x_bounds.1
          dsimp [p,leftMap]
          linarith
      · rw [merge_right agree hv]
        have hm := min_le_right D.frame.height E.frame.height
        by_cases hvm : v=m
        · subst v
          simp only [q,Function.comp_apply,E.frame.source,rightMap]
          linarith [E.frame.small]
        · have hg := E.frame.gap v hv hvm hvt
          have hx := (E.frame.triangle v hv).x_bounds.2
          dsimp [q,rightMap]
          linarith
  · exact clean_merge
      (clean_transform D.clean leftMap leftMap_injective leftMap_mix)
      (clean_transform E.clean rightMap rightMap_injective rightMap_mix) agree cross
  · rw [support_union]; exact Or.inl D.source_mem
  · rw [support_union]; exact Or.inr E.sink_mem

theorem twoTerminal_drawing (h : TwoTerminal G s t) : Nonempty (Drawing G s t) := by
  induction h with
  | edge s t hst => exact ⟨Drawing.edge hst⟩
  | series hG hH meet ihG ihH =>
    obtain ⟨D⟩ := ihG
    obtain ⟨E⟩ := ihH
    exact ⟨D.series E meet⟩
  | parallel hG hH meet ihG ihH =>
    obtain ⟨D⟩ := ihG
    obtain ⟨E⟩ := ihH
    exact ⟨D.parallel E meet⟩

end Lax303502Proofs.SP
