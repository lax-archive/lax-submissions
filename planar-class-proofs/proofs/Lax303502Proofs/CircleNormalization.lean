import Lax303502Proofs.Trees
import Lax303502Proofs.PlaneCells

set_option autoImplicit false

namespace Lax303502Proofs

theorem circlePoint_inverse {p : ℝ × ℝ}
    (hp : p.1^2+p.2^2=1) (hne : p.1≠-1) :
    circlePoint (p.2/(1+p.1)) = p := by
  have hb : -1 ≤ p.1 := by nlinarith [sq_nonneg p.2]
  have hx : 0<1+p.1 := by
    have := lt_of_le_of_ne hb (Ne.symm hne)
    linarith
  have hd : 1+(p.2/(1+p.1))^2 = 2/(1+p.1) := by
    field_simp
    nlinarith
  apply Prod.ext
  · dsimp [circlePoint]
    rw [hd]
    field_simp
    nlinarith
  · dsimp [circlePoint]
    rw [hd]
    field_simp

noncomputable def circleRotate (u p : ℝ × ℝ) : ℝ × ℝ :=
  (u.1*p.1+u.2*p.2,u.1*p.2-u.2*p.1)

theorem circleRotate_norm (u p : ℝ × ℝ) :
    (circleRotate u p).1^2+(circleRotate u p).2^2 =
      (u.1^2+u.2^2)*(p.1^2+p.2^2) := by
  dsimp [circleRotate]
  ring

theorem circleRotate_injective {u : ℝ × ℝ} (hu : u.1^2+u.2^2=1) :
    Function.Injective (circleRotate u) := by
  intro p q he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp [circleRotate] at hx hy
  apply Prod.ext
  · linear_combination u.1*hx-u.2*hy-(p.1-q.1)*hu
  · linear_combination u.2*hx+u.1*hy-(p.2-q.2)*hu

theorem circleRotate_mix (u p q : ℝ × ℝ) (a : ℝ) :
    SP.mix a (circleRotate u p) (circleRotate u q) =
      circleRotate u (SP.mix a p q) := by
  ext <;> dsimp [SP.mix,circleRotate] <;> ring

theorem circleRotate_fst_ne_neg_one {u p : ℝ × ℝ}
    (hu : u.1^2+u.2^2=1) (hp : p.1^2+p.2^2=1)
    (hne : u ≠ (-p.1,-p.2)) : (circleRotate u p).1 ≠ -1 := by
  intro he
  dsimp [circleRotate] at he
  have hzero : (u.1+p.1)^2+(u.2+p.2)^2=0 := by nlinarith
  have hx : u.1 = -p.1 := by nlinarith [sq_nonneg (u.2+p.2)]
  have hy : u.2 = -p.2 := by nlinarith [sq_nonneg (u.1+p.1)]
  exact hne (Prod.ext hx hy)

/-- Rotate a finite circle drawing away from the omitted point of the
rational parametrization. No vertex order or drawing property is changed. -/
theorem outerplane_parametric {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : Lax68.Outerplanar.OuterplaneDrawing G) : Nonempty (ParametricDrawing G) := by
  classical
  let r := D.radius
  have hr : r≠0 := ne_of_gt D.radius_pos
  let p : V → ℝ × ℝ := fun v => ((D.point v).1/r,(D.point v).2/r)
  have hp (v : V) : (p v).1^2+(p v).2^2=1 := by
    dsimp [p]
    have hb := D.onBoundary v
    change (D.point v).1^2+(D.point v).2^2=r^2 at hb
    field_simp
    exact hb
  have pi : Function.Injective p := by
    intro a b he
    apply D.injective
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp [p] at hx hy
    exact Prod.ext ((div_left_inj' hr).mp hx) ((div_left_inj' hr).mp hy)
  let banned : Set (ℝ × ℝ) := Set.range (fun v => (-(p v).1,-(p v).2))
  have hf : (circlePoint ⁻¹' banned).Finite :=
    Set.Finite.preimage circlePoint_injective.injOn (Set.finite_range _)
  obtain ⟨z,hz⟩ := hf.exists_notMem
  let u := circlePoint z
  have hu : u.1^2+u.2^2=1 := circlePoint_onCircle z
  let q := circleRotate u ∘ p
  have hq (v : V) : (q v).1^2+(q v).2^2=1 := by
    dsimp [q,Function.comp_def]
    rw [circleRotate_norm,hu,hp,mul_one]
  have hqne (v : V) : (q v).1 ≠ -1 := by
    apply circleRotate_fst_ne_neg_one hu (hp v)
    intro he
    exact hz ⟨v,he.symm⟩
  let t : V → ℝ := fun v => (q v).2/(1+(q v).1)
  have recover (v : V) : circlePoint (t v) = q v := circlePoint_inverse (hq v) (hqne v)
  have qi : Function.Injective q := (circleRotate_injective hu).comp pi
  refine ⟨⟨t,?_,?_⟩⟩
  · intro a b he
    apply qi
    rw [← recover,← recover,he]
  · intro a b c d hab hcd hd
    simp only [recover]
    rw [Set.disjoint_left]
    intro x hx hy
    obtain ⟨v,hv,hv',he⟩ := SP.segment_mix hx
    obtain ⟨w,hw,hw',he'⟩ := SP.segment_mix hy
    have heq := he.trans he'.symm
    change SP.mix v (circleRotate u (p a)) (circleRotate u (p b)) =
      SP.mix w (circleRotate u (p c)) (circleRotate u (p d)) at heq
    rw [circleRotate_mix,circleRotate_mix] at heq
    have heq' := circleRotate_injective hu heq
    have hm : SP.mix v (D.point a) (D.point b) = SP.mix w (D.point c) (D.point d) := by
      have hx := congrArg Prod.fst heq'
      have hy := congrArg Prod.snd heq'
      dsimp [SP.mix,p] at hx hy ⊢
      apply Prod.ext
      · field_simp at hx
        exact hx
      · field_simp at hy
        exact hy
    apply Set.disjoint_left.mp (D.disjointEdges hab hcd hd)
      (show SP.mix v (D.point a) (D.point b) ∈ segment ℝ (D.point a) (D.point b) from
        ⟨1-v,v,by linarith,hv,by ring,rfl⟩)
    rw [hm]
    exact ⟨1-w,w,by linarith,hw,by ring,rfl⟩

end Lax303502Proofs
