import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Order.IntermediateValue
import Lax909950Proofs.Geometry

/-!
An edge that lies on a cycle separates its two sides: they lie in different faces.
The proof uses the winding number of the polygon drawn for the cycle.
-/

namespace Lax909950Proofs

open Lax68.StraightLineDrawings Lax909950.EulerFormula Set Topology Filter Complex
open scoped Real

/-! ### Winding sums of closed polygons in `ℂ` -/

noncomputable def windTerm (p q x : ℂ) : ℝ := arg ((q - x) / (p - x))

theorem mem_slitPlane_of_not_mem_segment {p q x : ℂ} (h : x ∉ segment ℝ p q) :
    (q - x) / (p - x) ∈ slitPlane := by
  have hp : p - x ≠ 0 := by
    intro h0; apply h; rw [sub_eq_zero.mp h0]; exact left_mem_segment ℝ _ _
  rw [mem_slitPlane_iff_not_le_zero]
  intro hz
  rw [Complex.le_def] at hz
  obtain ⟨hre, him⟩ := hz
  set z := (q - x) / (p - x) with hzdef
  have hzr : z = ((z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hq : q - x = z * (p - x) := by rw [hzdef]; field_simp
  set s := -z.re with hs
  have hs0 : 0 ≤ s := by simp at hre; linarith
  apply h
  refine ⟨s / (1 + s), 1 / (1 + s), by positivity, by positivity, ?_, ?_⟩
  · field_simp; ring
  · have h1 : (1 + s) ≠ 0 := by positivity
    have hq' : q - x = -(s : ℂ) * (p - x) := by
      rw [hq, hzr]; simp [hs]
    rw [Complex.real_smul, Complex.real_smul]
    have h1' : ((1 + s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1
    push_cast at h1' ⊢
    field_simp
    linear_combination hq'

theorem continuousAt_windTerm {p q x : ℂ} (h : x ∉ segment ℝ p q) :
    ContinuousAt (windTerm p q) x := by
  have hp : p - x ≠ 0 := by
    intro h0; apply h; rw [sub_eq_zero.mp h0]; exact left_mem_segment ℝ _ _
  unfold windTerm
  exact (continuousAt_arg (mem_slitPlane_of_not_mem_segment h)).comp (f := fun y => (q - y) / (p - y)) <| (continuousAt_const.sub continuousAt_id).div (continuousAt_const.sub continuousAt_id) hp


/-- The winding sum of the closed polygon `p 0, …, p k` around `x`. -/
noncomputable def wind (p : ℕ → ℂ) (k : ℕ) (x : ℂ) : ℝ :=
  ∑ i ∈ Finset.range k, windTerm (p i) (p (i + 1)) x

/-- Points off all segments of the polygon. -/
def polyCompl (p : ℕ → ℂ) (k : ℕ) : Set ℂ := {x | ∀ i < k, x ∉ segment ℝ (p i) (p (i + 1))}

theorem continuousOn_wind (p : ℕ → ℂ) (k : ℕ) : ContinuousOn (wind p k) (polyCompl p k) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold wind
  exact tendsto_finsetSum _ fun i hi => continuousAt_windTerm (hx i (Finset.mem_range.mp hi))

theorem exp_windTerm {p q x : ℂ} (h : x ∉ segment ℝ p q) :
    exp (windTerm p q x * I) = ((q - x) / (p - x)) / (‖(q - x) / (p - x)‖ : ℂ) := by
  have hne : (q - x) / (p - x) ≠ 0 := by
    intro h0; have := mem_slitPlane_of_not_mem_segment h; rw [h0] at this
    exact slitPlane_ne_zero this rfl
  have hn : (‖(q - x) / (p - x)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hne
  rw [eq_div_iff hn, mul_comm]
  exact norm_mul_exp_arg_mul_I _

theorem prod_range_telescope (f : ℕ → ℂ) (n : ℕ) (hf : ∀ i ≤ n, f i ≠ 0) :
    ∏ i ∈ Finset.range n, f (i + 1) / f i = f n / f 0 := by
  induction n with
  | zero => simp [div_self (hf 0 le_rfl)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih fun i hi => hf i (by omega)]
    have := hf n (by omega)
    field_simp

theorem exp_wind {p : ℕ → ℂ} {k : ℕ} (hk0 : 0 < k) (hk : p k = p 0) {x : ℂ} (hx : x ∈ polyCompl p k) :
    exp (wind p k x * I) = 1 := by
  have hf : ∀ i ≤ k, p i - x ≠ 0 := by
    intro i hi h0
    rcases Nat.lt_or_ge i k with h | h
    · apply hx i h; rw [← sub_eq_zero.mp h0]; exact left_mem_segment ℝ _ _
    · have : i = k := le_antisymm hi h
      subst this
      apply hx (i - 1) (by omega)
      rw [Nat.sub_add_cancel hk0, ← sub_eq_zero.mp h0]; exact right_mem_segment ℝ _ _
  unfold wind
  push_cast
  rw [Finset.sum_mul, exp_sum]
  rw [Finset.prod_congr rfl fun i hi => exp_windTerm (hx i (Finset.mem_range.mp hi))]
  rw [Finset.prod_div_distrib]
  have htel := prod_range_telescope (fun i => p i - x) k hf
  rw [htel, hk, div_self (hf 0 (Nat.zero_le _))]
  have : ∏ i ∈ Finset.range k, ((‖(p (i + 1) - x) / (p i - x)‖ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_prod, ← norm_prod]
    simp only [htel, hk, div_self (hf 0 (Nat.zero_le _)), norm_one, Complex.ofReal_one]
  rw [this, div_one]

theorem wind_mem_two_pi_int {p : ℕ → ℂ} {k : ℕ} (hk0 : 0 < k) (hk : p k = p 0) {x : ℂ}
    (hx : x ∈ polyCompl p k) : ∃ n : ℤ, wind p k x = 2 * π * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (exp_wind hk0 hk hx)
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

theorem eq_of_isPreconnected_of_two_pi_int {T : Set ℝ} (hT : IsPreconnected T)
    (hT' : ∀ y ∈ T, ∃ n : ℤ, y = 2 * π * n) {u v : ℝ} (hu : u ∈ T) (hv : v ∈ T)
    (huv : u ≤ v) : u = v := by
  obtain ⟨n, rfl⟩ := hT' u hu
  obtain ⟨m, rfl⟩ := hT' v hv
  rcases lt_or_ge n m with h | h
  · exfalso
    have hm : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    have hmem : 2 * π * n + π ∈ T := hT.Icc_subset hu hv
      ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    obtain ⟨j, hj⟩ := hT' _ hmem
    have h2 : ((2 * n + 1 : ℤ) : ℝ) = ((2 * j : ℤ) : ℝ) := by
      push_cast
      have := Real.pi_pos
      field_simp at hj ⊢
      linarith
    have := Int.cast_injective h2
    omega
  · have hm : (m : ℝ) ≤ n := by exact_mod_cast h
    apply le_antisymm huv; nlinarith [Real.pi_pos]

theorem wind_eq_of_isPreconnected {p : ℕ → ℂ} {k : ℕ} (hk0 : 0 < k) (hk : p k = p 0) {S : Set ℂ}
    (hS : IsPreconnected S) (hSC : S ⊆ polyCompl p k) {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) :
    wind p k x = wind p k y := by
  have hT := hS.image _ ((continuousOn_wind p k).mono hSC)
  have hT' : ∀ z ∈ wind p k '' S, ∃ n : ℤ, z = 2 * π * n := by
    rintro _ ⟨w, hw, rfl⟩; exact wind_mem_two_pi_int hk0 hk (hSC hw)
  rcases le_total (wind p k x) (wind p k y) with h | h
  · exact eq_of_isPreconnected_of_two_pi_int hT hT' ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ h
  · exact (eq_of_isPreconnected_of_two_pi_int hT hT' ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩ h).symm

/-- Points on the normal line through the midpoint of `pa pb`. -/
noncomputable def normPt (pa pb : ℂ) (t : ℝ) : ℂ := (pa + pb) / 2 + t * I * (pb - pa)

theorem continuous_normPt (pa pb : ℂ) : Continuous (normPt pa pb) := by
  unfold normPt; fun_prop

/-- The ratio `(pb - x) / (pa - x)` at `x = normPt pa pb t`. -/
noncomputable def normRatio (t : ℝ) : ℂ := (1 - 2 * t * I) / (-1 - 2 * t * I)

theorem normRatio_den_ne (t : ℝ) : (-1 - 2 * t * I : ℂ) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem windTerm_normPt {pa pb : ℂ} (h : pa ≠ pb) (t : ℝ) :
    windTerm pa pb (normPt pa pb t) = arg (normRatio t) := by
  unfold windTerm normPt normRatio
  congr 1
  have hd : pb - pa ≠ 0 := sub_ne_zero.mpr h.symm
  have h1 := normRatio_den_ne t
  have h2 : pa - ((pa + pb) / 2 + t * I * (pb - pa)) ≠ 0 := by
    have : pa - ((pa + pb) / 2 + t * I * (pb - pa)) = (pb - pa) * (-1 - 2 * t * I) / 2 := by ring
    rw [this]; exact div_ne_zero (mul_ne_zero hd h1) two_ne_zero
  rw [div_eq_div_iff h2 h1]
  ring

theorem continuous_normRatio : Continuous normRatio := by
  unfold normRatio
  exact Continuous.div (by fun_prop) (by fun_prop) normRatio_den_ne

theorem normRatio_zero : normRatio 0 = -1 := by
  simp [normRatio]

theorem normRatio_im (t : ℝ) : (normRatio t).im = 4 * t / normSq (-1 - 2 * t * I) := by
  simp [normRatio, Complex.div_im]
  ring

theorem tendsto_arg_normRatio_pos :
    Tendsto (fun t => arg (normRatio t)) (𝓝[>] 0) (𝓝 π) := by
  have h1 : Tendsto normRatio (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] (-1)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [← normRatio_zero]
      exact (continuous_normRatio.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      show 0 ≤ (normRatio t).im
      rw [normRatio_im]; exact div_nonneg (by linarith) (normSq_nonneg _)
  have h2 := continuousWithinAt_arg_of_re_neg_of_im_zero (z := -1) (by simp) (by simp)
  rw [ContinuousWithinAt, arg_neg_one] at h2
  exact h2.comp h1

theorem tendsto_arg_normRatio_neg :
    Tendsto (fun t => arg (normRatio (-t))) (𝓝[>] 0) (𝓝 (-π)) := by
  have h1 : Tendsto (fun t => normRatio (-t)) (𝓝[>] 0) (𝓝[{z : ℂ | z.im < 0}] (-1)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [← normRatio_zero]
      have : Continuous fun t : ℝ => normRatio (-t) := continuous_normRatio.comp continuous_neg
      have h := this.tendsto 0
      simp only [neg_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      show (normRatio (-t)).im < 0
      rw [normRatio_im]
      apply div_neg_of_neg_of_pos (by linarith)
      exact normSq_pos.mpr (normRatio_den_ne _)
  exact (tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero (z := -1) (by simp) (by simp)).comp h1

theorem tendsto_wind_jump {p : ℕ → ℂ} {n : ℕ} (hne : p 0 ≠ p 1)
    (hm : ∀ i < n, normPt (p 0) (p 1) 0 ∉ segment ℝ (p (i + 1)) (p (i + 1 + 1))) :
    Tendsto (fun t => wind p (n + 1) (normPt (p 0) (p 1) t) -
      wind p (n + 1) (normPt (p 0) (p 1) (-t))) (𝓝[>] 0) (𝓝 (2 * π)) := by
  set x := normPt (p 0) (p 1)
  have hrest : Tendsto (fun t => ∑ i ∈ Finset.range n,
      (windTerm (p (i + 1)) (p (i + 1 + 1)) (x t) - windTerm (p (i + 1)) (p (i + 1 + 1)) (x (-t))))
      (𝓝[>] 0) (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := Finset.range n)]
    refine tendsto_finsetSum _ fun i hi => ?_
    have hc := continuousAt_windTerm (hm i (Finset.mem_range.mp hi))
    have ha : Tendsto (fun t => windTerm (p (i + 1)) (p (i + 1 + 1)) (x t)) (𝓝 0)
        (𝓝 (windTerm (p (i + 1)) (p (i + 1 + 1)) (x 0))) :=
      hc.tendsto.comp ((continuous_normPt _ _).tendsto 0)
    have hb : Tendsto (fun t => windTerm (p (i + 1)) (p (i + 1 + 1)) (x (-t))) (𝓝 0)
        (𝓝 (windTerm (p (i + 1)) (p (i + 1 + 1)) (x 0))) := by
      have h := ((continuous_normPt (p 0) (p 1)).comp continuous_neg).tendsto 0
      simp only [Function.comp_def, neg_zero] at h
      exact hc.tendsto.comp h
    simpa using (ha.sub hb).mono_left nhdsWithin_le_nhds
  have h0 := tendsto_arg_normRatio_pos.sub tendsto_arg_normRatio_neg
  have := h0.add hrest
  rw [show π - -π + 0 = 2 * π by ring] at this
  refine this.congr fun t => ?_
  simp only [wind, Finset.sum_range_succ', x, windTerm_normPt hne, Finset.sum_sub_distrib]
  ring

/-! ### Transfer to drawings -/

/-- The identification of the plane `ℝ × ℝ` with `ℂ`. -/
noncomputable abbrev toC : Point ≃L[ℝ] ℂ := Complex.equivRealProdCLM.symm

theorem mem_segment_of_toC {P Q y : Point} (h : toC y ∈ segment ℝ (toC P) (toC Q)) :
    y ∈ segment ℝ P Q := by
  obtain ⟨α, β, hα, hβ, hαβ, h⟩ := h
  refine ⟨α, β, hα, hβ, hαβ, toC.injective ?_⟩
  rw [map_add, map_smul, map_smul]; exact h

variable {V : Type*} {G : SimpleGraph V}

theorem toC_sidePt (D : StraightLineDrawing G) (a b : V) (t : ℝ) :
    toC (sidePt D a b t) = normPt (toC (D.point a)) (toC (D.point b)) t := by
  apply Complex.ext <;>
    simp [sidePt, normal, normPt, Complex.equivRealProdCLM_symm_apply] <;> ring

/-- If `a` and `b` remain connected after deleting the edge `ab`, then the two
sides of `ab` lie in different faces. -/
theorem edgeFace_ne_of_reachable [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) (hr : (G.deleteEdges {s(a, b)}).Reachable a b) :
    edgeFace D a b true ≠ edgeFace D a b false := by
  intro hF
  obtain ⟨w⟩ := hr.symm
  set n := w.length with hn
  let v : ℕ → V := fun i => match i with
    | 0 => a
    | i + 1 => w.getVert i
  let p : ℕ → ℂ := fun i => toC (D.point (v i))
  have hv1 : v 1 = b := w.getVert_zero
  have hvk : v (n + 1) = a := w.getVert_length
  have hadj : ∀ i < n, (G.deleteEdges {s(a, b)}).Adj (v (i + 1)) (v (i + 1 + 1)) :=
    fun i hi => w.adj_getVert_succ hi
  have hGadj : ∀ i < n + 1, G.Adj (v i) (v (i + 1)) := by
    intro i hi
    cases i with
    | zero => rw [hv1]; exact hab
    | succ i => exact (SimpleGraph.deleteEdges_adj.mp (hadj i (by omega))).1
  have hk : p (n + 1) = p 0 := by simp only [p, hvk]; rfl
  have hp0 : p 0 = toC (D.point a) := rfl
  have hp1 : p 1 = toC (D.point b) := by simp only [p, hv1]
  have hcompl : ∀ y ∉ image D, toC y ∈ polyCompl p (n + 1) := by
    intro y hy i hi hmem
    apply hy
    have := mem_segment_of_toC hmem
    simp only [Lax909950.EulerFormula.image, mem_union, mem_iUnion]
    exact Or.inr ⟨_, _, hGadj i hi, this⟩
  have hFm := edgeFace_mem_faces D hab true
  set F := edgeFace D a b true
  have hS : IsPreconnected (toC '' F) :=
    (isConnected_of_mem_faces D hFm).isPreconnected.image _ toC.continuous.continuousOn
  have hSC : toC '' F ⊆ polyCompl p (n + 1) := by
    rintro _ ⟨y, hy, rfl⟩; exact hcompl y (subset_compl_of_mem_faces D hFm hy)
  have hne : p 0 ≠ p 1 := by
    rw [hp0, hp1]; intro h
    exact hab.ne (D.injective (toC.injective h))
  have hm : ∀ i < n, normPt (p 0) (p 1) 0 ∉ segment ℝ (p (i + 1)) (p (i + 1 + 1)) := by
    intro i hi hmem
    rw [hp0, hp1, ← toC_sidePt] at hmem
    have hseg := mem_segment_of_toC hmem
    have hmid : sidePt D a b 0 ∈ edgeSeg D a b := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      simp [sidePt, smul_add]
    have h1 := edgeSeg_inter_image D hab hmid (hGadj (i + 1) (by omega)) hseg
    exact (SimpleGraph.deleteEdges_adj.mp (hadj i hi)).2 (mem_singleton_iff.mpr h1)
  have hjump := tendsto_wind_jump hne hm
  obtain ⟨ε, hε, hside⟩ := sidePt_mem_edgeFace D hab
  have hev : (fun t => wind p (n + 1) (normPt (p 0) (p 1) t) -
      wind p (n + 1) (normPt (p 0) (p 1) (-t))) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    obtain ⟨h1, h2⟩ := hside t ht.1 ht.2
    rw [← hF] at h2
    rw [hp0, hp1, ← toC_sidePt, ← toC_sidePt, sub_eq_zero]
    exact wind_eq_of_isPreconnected (Nat.succ_pos n) hk hS hSC ⟨_, h1, rfl⟩ ⟨_, h2, rfl⟩
  have h0 : Tendsto (fun t => wind p (n + 1) (normPt (p 0) (p 1) t) -
      wind p (n + 1) (normPt (p 0) (p 1) (-t))) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  have := tendsto_nhds_unique hjump h0
  linarith [Real.pi_pos]

end Lax909950Proofs
