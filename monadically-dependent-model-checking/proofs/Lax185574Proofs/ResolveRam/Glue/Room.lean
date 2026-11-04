import Lax185574Proofs.ResolveRam.Glue.RIn
import Lax185574Proofs.MC.Glue.Sat

/-!
The room check of a later round of the glue program of lem:resolve-lift.

After reading its input, a later round computes the size
`Su = |u| + max (max window, max library, max answer) + 1` of its input
and the radius bound `Rm = rhoPlus (k₀ + 1) q₀ = 9 ^ ((k₀ + q₀ + 1) (q₀ + 1))`,
with saturating arithmetic, and sets `ovf` unless
`2^24 (Rm + 2)^4 (Su + 1)^2 < W` (`rmChk_run`). All later steps of the
round run only if the check passed.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- The bound that the room check compares with `W`. -/
def bigOf (R S : ℕ) : ℕ := 2 ^ 24 * (R + 2) ^ 4 * (S + 1) ^ 2

theorem min_mul_left (a b W : ℕ) : min (min a W * b) W = min (a * b) W := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  by_cases h : a ≤ W
  · rw [min_eq_left h]
  · rw [min_eq_right (show W ≤ a by omega)]
    have h1 : W ≤ W * b := Nat.le_mul_of_pos_right W hb
    have h2 : W * b ≤ a * b := Nat.mul_le_mul_right b (by omega)
    rw [min_eq_right h1, min_eq_right (le_trans h1 h2)]

theorem min_mul_right (a b W : ℕ) : min (a * min b W) W = min (a * b) W := by
  rw [mul_comm, min_mul_left, mul_comm]

theorem min_add_right (a b W : ℕ) : min (min a W + b) W = min (a + b) W := by omega

/-- The maximum of three scalars into `rM`. -/
def max3 : Com :=
  .seq (.assign "rM" (.var "mw"))
    (.seq (.ite (.lt (.var "rM") (.var "rA")) (.assign "rM" (.var "rA")) .skip)
      (.ite (.lt (.var "rM") (.var "rY")) (.assign "rM" (.var "rY")) .skip))

/-- The size of the input and the maxima. -/
def rmA : Com :=
  .seq (mxSeg "a" "z0" "lt") (.seq (.assign "rA" (.var "mx")) (.seq (mxSeg "y" "z0" "bl")
  (.seq (.assign "rY" (.var "mx")) (.seq max3
  (.assign "rS" (.add (.add (.add (.add (.var "tg") (.var "sl")) (.var "bl")) (.var "rM"))
    (.lit 4)))))))

/-- The radius bound, plus two. -/
def rmR : Com :=
  .seq (.assign "e1" (.add (.add (.var "gK") (.var "gq")) (.lit 1)))
  (.seq (.assign "e2" (.add (.var "gq") (.lit 1))) (.seq (satMul "e1" "e2" "rE")
  (.seq (.assign "rR" (.lit 1)) (.seq (.assign "r9" (.lit 9)) (.seq (satPow "rR" "r9" "rk" "rE")
  (.seq (.assign "r2" (.lit 2)) (satAdd "rR" "r2" "rR")))))))

/-- The bound and the test. -/
def rmB : Com :=
  .seq (.assign "rB" (.lit (2 ^ 24))) (.seq (satMul "rB" "rR" "rB") (.seq (satMul "rB" "rR" "rB")
  (.seq (satMul "rB" "rR" "rB") (.seq (satMul "rB" "rR" "rB") (.seq (satMul "rB" "rS" "rB")
  (.seq (satMul "rB" "rS" "rB")
    (.ite (.lt (.var "rB") (.var "W")) .skip (.assign "ovf" (.lit 1)))))))))

/-- The room check. -/
def rmChk : Com := .seq rmA (.seq rmR rmB)

theorem seg_wordsAt {ws : List (List ℕ)} {τ : Env} (h : WordsAt ws τ) :
    ∀ i, i ≤ ws.length → (τ.arrs "a").take (off ws i) = (ws.take i).flatten := by
  intro i
  induction i with
  | zero => intro _; simp [off]
  | succ i ih =>
    intro hi
    have hi' : i < ws.length := by omega
    rw [off_succ hi', List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
      List.flatten_append, ← ih (by omega), List.take_add, List.flatten_singleton]
    congr 1
    apply List.ext_getElem?
    intro j
    rcases Nat.lt_or_ge j ws[i].length with h1 | h1
    · rw [List.getElem?_take_of_lt h1, List.getElem?_drop, h.a i hi' j h1, List.getElem?_eq_getElem h1]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h1]

theorem seg_lib {ws : List (List ℕ)} {τ : Env} (h : WordsAt ws τ) :
    seg (τ.arrs "a") 0 (total ws) = ws.flatten := by
  have := seg_wordsAt h ws.length le_rfl
  rw [off_length, List.take_length] at this
  simpa [seg, total] using this

/-- The size that the room check computes. -/
def suOf (t sl bl mw ma mb : ℕ) : ℕ := t + sl + bl + max (max mw ma) mb + 3

theorem max3_run {W a b c : ℕ} {τ : Env} (ha : τ.vars "mw" = a) (hb : τ.vars "rA" = b)
    (hc : τ.vars "rY" = c) (hW : a ≤ W ∧ b ≤ W ∧ c ≤ W) :
    ∃ τ', Run (W + 1) max3 τ τ' 20 ∧ Only "rM" (max (max a b) c) τ τ' := by
  obtain ⟨τ1, r1, o1⟩ := asg_run (x := "rM") (ev_var (B := W + 1) ha (by omega))
  have h2 : ∃ τ2, Run (W + 1) (.ite (.lt (.var "rM") (.var "rA")) (.assign "rM" (.var "rA")) .skip) τ1 τ2 8 ∧
      Only "rM" (max a b) τ τ2 := by
    have hc1 := evalB_condLt (B := W + 1) (σ := τ1) (e := .var "rM") (f := .var "rA")
      (ev_var o1.self (by omega)) (ev_var (x := "rA") (v := b) (by simp (disch := decide) only [o1.vars, hb]) (by omega))
    by_cases h : a < b
    · obtain ⟨τ2, r2, o2⟩ := asg_run (x := "rM") (ev_var (B := W + 1) (σ := τ1) (x := "rA") (v := b)
        (by simp (disch := decide) only [o1.vars, hb]) (by omega))
      refine ⟨τ2, (Run.ite_true (by rw [hc1]; simp [h]) r2).mono (by simp [Cond.size, Expr.size]),
        ⟨by rw [o2.self]; omega, fun y hy => by rw [o2.vars y hy, o1.vars y hy], by rw [o2.arrs, o1.arrs],
          by rw [o2.out, o1.out], by rw [o2.inp, o1.inp]⟩⟩
    · refine ⟨τ1, (Run.ite_false (by rw [hc1]; simp [h]) Run.skip).mono (by simp [Cond.size, Expr.size]),
        ⟨by rw [o1.self]; omega, o1.vars, o1.arrs, o1.out, o1.inp⟩⟩
  obtain ⟨τ2, r2, o2⟩ := h2
  have hc2 := evalB_condLt (B := W + 1) (σ := τ2) (e := .var "rM") (f := .var "rY")
    (ev_var o2.self (by omega)) (ev_var (x := "rY") (v := c) (by simp (disch := decide) only [o2.vars, hc]) (by omega))
  by_cases h : max a b < c
  · obtain ⟨τ3, r3, o3⟩ := asg_run (x := "rM") (ev_var (B := W + 1) (σ := τ2) (x := "rY") (v := c)
      (by simp (disch := decide) only [o2.vars, hc]) (by omega))
    refine ⟨τ3, (Run.seq r1 (Run.seq r2 (Run.ite_true (by rw [hc2]; simp [h]) r3))).mono
      (by simp [Cond.size, Expr.size]),
      ⟨by rw [o3.self]; omega, fun y hy => by rw [o3.vars y hy, o2.vars y hy], by rw [o3.arrs, o2.arrs],
        by rw [o3.out, o2.out], by rw [o3.inp, o2.inp]⟩⟩
  · refine ⟨τ2, (Run.seq r1 (Run.seq r2 (Run.ite_false (by rw [hc2]; simp [h]) Run.skip))).mono
      (by simp [Cond.size, Expr.size]), ⟨by rw [o2.self]; omega, o2.vars, o2.arrs, o2.out, o2.inp⟩⟩


/-- **The maxima and the size.** -/
theorem rmA_run {W t sl mw : ℕ} {ws : List (List ℕ)} {b : List ℕ} {τ : Env}
    (hL : Lib ws τ) (hz : τ.vars "z0" = 0) (hbl : τ.vars "bl" = b.length) (hy : SegAt "y" 0 b τ)
    (harr : ArrW W τ) (htg : τ.vars "tg" = t) (hsl : τ.vars "sl" = sl) (hmw : τ.vars "mw" = mw)
    (hsz : 64 * (t + sl + b.length + mw + total ws + 8) ≤ W)
    (hva : ∀ w ∈ ws, ∀ v ∈ w, 64 * v ≤ W) (hvb : ∀ v ∈ b, 64 * v ≤ W) :
    ∃ τ', Run (W + 1) rmA τ τ' (30 * total ws + 30 * b.length + 100) ∧
      τ'.vars "rS" = t + sl + b.length + max (max mw (maxEntry ws.flatten)) (maxEntry b) + 4 ∧
      (∀ y, y ∉ rmA.wvars → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  have hT := hL.lt
  have hmA : maxEntry ws.flatten ≤ W / 64 := maxEntry_le fun v hv => by
    obtain ⟨w, hw, hv'⟩ := List.mem_flatten.1 hv; have := hva w hw v hv'; omega
  have hmB : maxEntry b ≤ W / 64 := maxEntry_le fun v hv => by have := hvb v hv; omega
  have hsa := seg_lib hL.at_
  have hsy : seg (τ.arrs "y") 0 b.length = b := by
    apply List.ext_getElem?; intro j
    simp only [seg, List.drop_zero]
    rcases Nat.lt_or_ge j b.length with h | h
    · rw [List.getElem?_take_of_lt h, show (τ.arrs "y")[j]? = some b[j] by simpa using hy j h,
        List.getElem?_eq_getElem h]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h]
  obtain ⟨τ1, r1, m1⟩ := mxSeg_run (B := W + 1) (ar := "a") (s := "z0") (l := "lt") (σ := τ)
    (a := 0) (N := total ws) hz hT (by decide) (by decide) (by decide) (by decide)
    (by rw [harr]; omega) (by omega) (by rw [hsa]; intro v hv; have := le_maxEntry hv; omega)
  rw [hsa] at m1
  have a1 : τ1.arrs = τ.arrs := r1.frame_arrs_eqOn (by simp [mxSeg, mxBody, forUp, Com.warrs])
  obtain ⟨τ2, r2, o2⟩ := asg_run (x := "rA") (ev_var (B := W + 1) m1 (by omega))
  obtain ⟨τ3, r3, m3⟩ := mxSeg_run (B := W + 1) (ar := "y") (s := "z0") (l := "bl") (σ := τ2)
    (a := 0) (N := b.length)
    (by simp (disch := decide) only [o2.vars, r1.frame_var "z0" (by decide), hz])
    (by simp (disch := decide) only [o2.vars, r1.frame_var "bl" (by decide), hbl])
    (by decide) (by decide) (by decide) (by decide)
    (by rw [o2.arrs, a1, harr]; omega) (by omega)
    (by rw [o2.arrs, a1, hsy]; intro v hv; have := hvb v hv; omega)
  rw [o2.arrs, a1, hsy] at m3
  obtain ⟨τ4, r4, o4⟩ := asg_run (x := "rY") (ev_var (B := W + 1) m3 (by omega))
  have e4 : ∀ y, y ∉ ["mx", "ci", "rA", "rY"] → τ4.vars y = τ.vars y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [o4.vars y hy.2.2.2, r3.frame_var y (by simp [mxSeg, mxBody, forUp, Com.wvars]; tauto),
      o2.vars y hy.2.2.1, r1.frame_var y (by simp [mxSeg, mxBody, forUp, Com.wvars]; tauto)]
  obtain ⟨τ5, r5, o5⟩ := max3_run (W := W) (τ := τ4) (a := mw) (b := maxEntry ws.flatten) (c := maxEntry b) (by simp (disch := decide) only [e4, hmw])
    (by simp (disch := decide) only [o4.vars, r3.frame_var "rA" (by decide), o2.self])
    o4.self ⟨by omega, by omega, by omega⟩
  obtain ⟨τ6, r6, o6⟩ := asg_run (x := "rS") (B := W + 1) (σ := τ5)
    (ev_add (ev_add (ev_add (ev_add (ev_var (x := "tg") (v := t) (by simp (disch := decide) only [o5.vars, e4, htg]) (by omega))
      (ev_var (x := "sl") (v := sl) (by simp (disch := decide) only [o5.vars, e4, hsl]) (by omega)) (by omega))
      (ev_var (x := "bl") (v := b.length) (by simp (disch := decide) only [o5.vars, e4, hbl]) (by omega)) (by omega))
      (ev_var o5.self (by omega)) (by omega)) (evalB_lit (n := 4) (by omega)) (by omega))
  have hrun : Run (W + 1) rmA τ τ6 (30 * total ws + 30 * b.length + 100) := by
    unfold rmA
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono
      (by simp only [Expr.size]; omega)
  refine ⟨τ6, hrun, o6.self, fun y hy => hrun.frame_var y hy, ?_, hrun.out_eq (by decide),
    hrun.frame_inp (by decide)⟩
  rw [o6.arrs, o5.arrs, o4.arrs, r3.frame_arrs_eqOn (by simp [mxSeg, mxBody, forUp, Com.warrs]), o2.arrs, a1]

/-- **The radius bound.** -/
theorem rmR_run {W k₀ q₀ : ℕ} {τ : Env} (hW : τ.vars "W" = W) (hW16 : 16 ≤ W)
    (hk : τ.vars "gK" = k₀) (hq : τ.vars "gq" = q₀) (hsz : 4 * (k₀ + q₀ + 2) ≤ W) :
    ∃ τ', Run (W + 1) rmR τ τ' (23 * min ((k₀ + q₀ + 1) * (q₀ + 1)) W + 100) ∧
      τ'.vars "rR" = min (Lax3.DistFO.rhoPlus (k₀ + 1) q₀ + 2) W ∧
      (∀ y, y ∉ rmR.wvars → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  have hW' : W < W + 1 := by omega
  have hW1 : 1 ≤ W := by omega
  obtain ⟨τ1, r1, o1⟩ := asg_run (x := "e1") (B := W + 1) (σ := τ)
    (ev_add (ev_add (ev_var hk (by omega)) (ev_var hq (by omega)) (by omega)) (evalB_lit (n := 1) (by omega))
      (by omega))
  obtain ⟨τ2, r2, o2⟩ := asg_run (x := "e2") (B := W + 1) (σ := τ1)
    (ev_add (ev_var (x := "gq") (v := q₀) (by simp (disch := decide) only [o1.vars, hq]) (by omega))
      (evalB_lit (n := 1) (by omega)) (by omega))
  have hW2 : τ2.vars "W" = W := by simp (disch := decide) only [o2.vars, o1.vars, hW]
  have r3 := satMul_run (B := W + 1) (x := "e1") (y := "e2") (z := "rE") (σ := τ2) hW2 hW'
    (by simp (disch := decide) only [o2.vars, o1.self]; omega) (by rw [o2.self]; omega)
  have he12 : min (τ2.vars "e1" * τ2.vars "e2") W = min ((k₀ + q₀ + 1) * (q₀ + 1)) W := by
    simp (disch := decide) only [o2.vars, o1.self, o2.self]
  rw [he12] at r3
  have o3 := Only.of_setVar τ2 "rE" (min ((k₀ + q₀ + 1) * (q₀ + 1)) W)
  generalize τ2.setVar "rE" (min ((k₀ + q₀ + 1) * (q₀ + 1)) W) = τ3 at r3 o3
  obtain ⟨τ4, r4, o4⟩ := asg_run (x := "rR") (B := W + 1) (σ := τ3) (evalB_lit (n := 1) (by omega))
  obtain ⟨τ5, r5, o5⟩ := asg_run (x := "r9") (B := W + 1) (σ := τ4) (evalB_lit (n := 9) (by omega))
  have hW5 : τ5.vars "W" = W := by
    simp (disch := decide) only [o5.vars, o4.vars, o3.vars, hW2]
  obtain ⟨τ6, r6, h6, f6, a6⟩ := satPow_run (B := W + 1) (a0 := 1) (b := 9)
    (N := min ((k₀ + q₀ + 1) * (q₀ + 1)) W) (acc := "rR") (base := "r9") (i := "rk") (n := "rE")
    (σ := τ5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hW5 hW'
    (by simp (disch := decide) only [o5.vars, o4.self]; omega) (by rw [o5.self]; omega)
    (by simp (disch := decide) only [o5.vars, o4.vars, o3.self]) (by omega)
  rw [one_mul, pow_min_sat 9 _ W hW1] at h6
  obtain ⟨τ7, r7, o7⟩ := asg_run (x := "r2") (B := W + 1) (σ := τ6) (evalB_lit (n := 2) (by omega))
  have hW7 : τ7.vars "W" = W := by simp (disch := decide) only [o7.vars, f6, hW5]
  have r8 := satAdd_run (B := W + 1) (x := "rR") (y := "r2") (z := "rR") (σ := τ7) hW7 hW'
    (by simp (disch := decide) only [o7.vars, h6]; omega) (by rw [o7.self]; omega)
  have o8 := Only.of_setVar τ7 "rR" (min (τ7.vars "rR" + τ7.vars "r2") W)
  generalize τ7.setVar "rR" (min (τ7.vars "rR" + τ7.vars "r2") W) = τ8 at r8 o8
  have hrun : Run (W + 1) rmR τ τ8 (23 * min ((k₀ + q₀ + 1) * (q₀ + 1)) W + 100) := by
    unfold rmR
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8))))))).mono
      (by simp [Expr.size]; omega)
  refine ⟨τ8, hrun, ?_, fun y hy => hrun.frame_var y hy, ?_, hrun.out_eq (by decide),
    hrun.frame_inp (by decide)⟩
  · simp (disch := decide) only [o8.self, o7.vars, h6, o7.self]
    have : Lax3.DistFO.rhoPlus (k₀ + 1) q₀ = 9 ^ ((k₀ + q₀ + 1) * (q₀ + 1)) := by
      simp only [Lax3.DistFO.rhoPlus]; congr 2; ring
    rw [this]; omega
  · rw [o8.arrs, o7.arrs, a6, o5.arrs, o4.arrs, o3.arrs, o2.arrs, o1.arrs]

/-- **The bound and the test.** -/
theorem rmB_run {W R S : ℕ} {τ : Env} (hW : τ.vars "W" = W) (hW24 : 2 ^ 24 < W)
    (hR : τ.vars "rR" = min R W) (hS : τ.vars "rS" = S) (hSW : S ≤ W) :
    ∃ τ', Run (W + 1) rmB τ τ' 200 ∧
      τ'.vars "ovf" = (if 2 ^ 24 * R * R * R * R * S * S < W then τ.vars "ovf" else 1) ∧
      (∀ y, y ∉ rmB.wvars → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  have hW' : W < W + 1 := by omega
  have mul : ∀ (ρ : Env) (z : String) (a c : ℕ), ρ.vars "W" = W → ρ.vars "rB" = min a W →
      ρ.vars z = min c W → z ≠ "rB" →
      ∃ ρ', Run (W + 1) (satMul "rB" z "rB") ρ ρ' 15 ∧ Only "rB" (min (a * c) W) ρ ρ' := by
    intro ρ z a c hWρ ha hc hz
    have := satMul_run (B := W + 1) (x := "rB") (y := z) (z := "rB") hWρ hW' (by rw [ha]; omega)
      (by rw [hc]; omega)
    rw [ha, hc, min_mul_min] at this
    exact ⟨_, this, Only.of_setVar _ _ _⟩
  obtain ⟨τ0, r0, o0⟩ := asg_run (x := "rB") (B := W + 1) (σ := τ) (evalB_lit (n := 2 ^ 24) (by omega))
  have k0 : ∀ y, y ≠ "rB" → τ0.vars y = τ.vars y := o0.vars
  obtain ⟨τ1, r1, o1⟩ := mul τ0 "rR" (2 ^ 24) R (by simp (disch := decide) only [k0, hW])
    (by rw [o0.self]; omega) (by simp (disch := decide) only [k0, hR]) (by decide)
  obtain ⟨τ2, r2, o2⟩ := mul τ1 "rR" (2 ^ 24 * R) R (by simp (disch := decide) only [o1.vars, k0, hW])
    o1.self (by simp (disch := decide) only [o1.vars, k0, hR]) (by decide)
  obtain ⟨τ3, r3, o3⟩ := mul τ2 "rR" (2 ^ 24 * R * R) R
    (by simp (disch := decide) only [o2.vars, o1.vars, k0, hW])
    o2.self (by simp (disch := decide) only [o2.vars, o1.vars, k0, hR]) (by decide)
  obtain ⟨τ4, r4, o4⟩ := mul τ3 "rR" (2 ^ 24 * R * R * R) R
    (by simp (disch := decide) only [o3.vars, o2.vars, o1.vars, k0, hW])
    o3.self (by simp (disch := decide) only [o3.vars, o2.vars, o1.vars, k0, hR])
    (by decide)
  have kv : ∀ y, y ≠ "rB" → τ4.vars y = τ.vars y := fun y hy => by
    rw [o4.vars y hy, o3.vars y hy, o2.vars y hy, o1.vars y hy, k0 y hy]
  obtain ⟨τ5, r5, o5⟩ := mul τ4 "rS" (2 ^ 24 * R * R * R * R) S (by simp (disch := decide) only [kv, hW])
    o4.self (by simp (disch := decide) only [kv, hS]; omega) (by decide)
  obtain ⟨τ6, r6, o6⟩ := mul τ5 "rS" (2 ^ 24 * R * R * R * R * S) S
    (by simp (disch := decide) only [o5.vars, kv, hW])
    o5.self (by simp (disch := decide) only [o5.vars, kv, hS]; omega) (by decide)
  set Bg := 2 ^ 24 * R * R * R * R * S * S
  have hc := evalB_condLt (B := W + 1) (σ := τ6) (e := .var "rB") (f := .var "W")
    (ev_var o6.self (by omega)) (ev_var (by simp (disch := decide) only [o6.vars, o5.vars, kv, hW]) hW')
  have kv6 : ∀ y, y ≠ "rB" → τ6.vars y = τ.vars y := fun y hy => by
    rw [o6.vars y hy, o5.vars y hy, kv y hy]
  have hfin : ∃ ρ7, Run (W + 1) (.ite (.lt (.var "rB") (.var "W")) .skip (.assign "ovf" (.lit 1))) τ6 ρ7 8 ∧
      ρ7.vars "ovf" = (if Bg < W then τ.vars "ovf" else 1) ∧ ρ7.arrs = τ6.arrs ∧ ρ7.out = τ6.out ∧
      ρ7.inp = τ6.inp := by
    by_cases h : Bg < W
    · exact ⟨τ6, (Run.ite_true (by rw [hc]; simp only [Option.some.injEq, decide_eq_true_eq]; omega) Run.skip).mono (by simp [Cond.size, Expr.size]),
        by simp [h, kv6 "ovf" (by decide)], rfl, rfl, rfl⟩
    · exact ⟨_, (Run.ite_false (by rw [hc]; simp only [Option.some.injEq, decide_eq_false_iff_not]; omega)
        (Run.assign (evalB_lit (n := 1) (by omega)))).mono
        (by simp [Cond.size, Expr.size]), by simp [h], rfl, rfl, rfl⟩
  obtain ⟨τ7, r7, h7, a7, u7, i7⟩ := hfin
  have hrun : Run (W + 1) rmB τ τ7 200 := by
    unfold rmB
    exact (Run.seq r0 (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7))))))).mono
      (by simp [Expr.size])
  refine ⟨τ7, hrun, h7, fun y hy => hrun.frame_var y hy, ?_, hrun.out_eq (by decide), hrun.frame_inp (by decide)⟩
  rw [a7, o6.arrs, o5.arrs, o4.arrs, o3.arrs, o2.arrs, o1.arrs, o0.arrs]

end Lax185574Proofs.ResolveRam.Glue

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- The size of the library, the answer, the input and the buffer, for the room check. -/
def rmS : Com :=
  .seq (mxSeg "a" "z0" "lt") (.seq (.assign "rA" (.var "mx")) (.seq (mxSeg "y" "z0" "bl")
  (.seq (.assign "rY" (.var "mx")) (.seq max3
  (.assign "rS" (.add (.add (.add (.add (.add (.add (.var "lt") (.var "lt")) (.var "m")) (.var "m"))
    (.add (.var "bl") (.var "po"))) (.add (.var "nx") (.var "rM"))) (.lit 64)))))))

/-- The room check during a later round. -/
def rmL : Com := .seq rmS rmB

/-- The size that `rmS` computes. -/
def sOf (lt m bl po nx mw ma mb : ℕ) : ℕ := 2 * lt + 2 * m + bl + po + nx + max (max mw ma) mb + 64

/-- **The size of the library and the rest.** -/
theorem rmS_run {W nx mw po : ℕ} {ws : List (List ℕ)} {b : List ℕ} {τ : Env}
    (hL : Lib ws τ) (hz : τ.vars "z0" = 0) (hbl : τ.vars "bl" = b.length) (hy : SegAt "y" 0 b τ)
    (harr : ArrW W τ) (hnx : τ.vars "nx" = nx) (hpo : τ.vars "po" = po) (hmw : τ.vars "mw" = mw)
    (hsz : 64 * (nx + po + b.length + mw + total ws + ws.length + 8) ≤ W)
    (hva : ∀ w ∈ ws, ∀ v ∈ w, 64 * v ≤ W) (hvb : ∀ v ∈ b, 64 * v ≤ W) :
    ∃ τ', Run (W + 1) rmS τ τ' (30 * total ws + 30 * b.length + 100) ∧
      τ'.vars "rS" = sOf (total ws) ws.length b.length po nx mw (maxEntry ws.flatten) (maxEntry b) ∧
      (∀ y, y ∉ rmS.wvars → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  have hT := hL.lt
  have hm := hL.m
  have hmA : maxEntry ws.flatten ≤ W / 64 := maxEntry_le fun v hv => by
    obtain ⟨w, hw, hv'⟩ := List.mem_flatten.1 hv; have := hva w hw v hv'; omega
  have hmB : maxEntry b ≤ W / 64 := maxEntry_le fun v hv => by have := hvb v hv; omega
  have hsa := seg_lib hL.at_
  have hsy : seg (τ.arrs "y") 0 b.length = b := by
    apply List.ext_getElem?; intro j
    simp only [seg, List.drop_zero]
    rcases Nat.lt_or_ge j b.length with h | h
    · rw [List.getElem?_take_of_lt h, show (τ.arrs "y")[j]? = some b[j] by simpa using hy j h,
        List.getElem?_eq_getElem h]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h]
  obtain ⟨τ1, r1, m1⟩ := mxSeg_run (B := W + 1) (ar := "a") (s := "z0") (l := "lt") (σ := τ)
    (a := 0) (N := total ws) hz hT (by decide) (by decide) (by decide) (by decide)
    (by rw [harr]; omega) (by omega) (by rw [hsa]; intro v hv; have := le_maxEntry hv; omega)
  rw [hsa] at m1
  have a1 : τ1.arrs = τ.arrs := r1.frame_arrs_eqOn (by simp [mxSeg, mxBody, forUp, Com.warrs])
  obtain ⟨τ2, r2, o2⟩ := asg_run (x := "rA") (ev_var (B := W + 1) m1 (by omega))
  obtain ⟨τ3, r3, m3⟩ := mxSeg_run (B := W + 1) (ar := "y") (s := "z0") (l := "bl") (σ := τ2)
    (a := 0) (N := b.length)
    (by simp (disch := decide) only [o2.vars, r1.frame_var "z0" (by decide), hz])
    (by simp (disch := decide) only [o2.vars, r1.frame_var "bl" (by decide), hbl])
    (by decide) (by decide) (by decide) (by decide)
    (by rw [o2.arrs, a1, harr]; omega) (by omega)
    (by rw [o2.arrs, a1, hsy]; intro v hv; have := hvb v hv; omega)
  rw [o2.arrs, a1, hsy] at m3
  obtain ⟨τ4, r4, o4⟩ := asg_run (x := "rY") (ev_var (B := W + 1) m3 (by omega))
  have e4 : ∀ y, y ∉ ["mx", "ci", "rA", "rY"] → τ4.vars y = τ.vars y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [o4.vars y hy.2.2.2, r3.frame_var y (by simp [mxSeg, mxBody, forUp, Com.wvars]; tauto),
      o2.vars y hy.2.2.1, r1.frame_var y (by simp [mxSeg, mxBody, forUp, Com.wvars]; tauto)]
  obtain ⟨τ5, r5, o5⟩ := max3_run (W := W) (τ := τ4) (a := mw) (b := maxEntry ws.flatten) (c := maxEntry b)
    (by rw [e4 "mw" (by decide), hmw])
    (by rw [o4.vars "rA" (by decide), r3.frame_var "rA" (by decide), o2.self])
    o4.self ⟨by omega, by omega, by omega⟩
  have g : ∀ y, y ∉ ["mx", "ci", "rA", "rY", "rM"] → τ5.vars y = τ.vars y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [o5.vars y hy.2.2.2.2, e4 y (by simp; tauto)]
  obtain ⟨τ6, r6, o6⟩ := asg_run (x := "rS") (B := W + 1) (σ := τ5)
    (ev_add (ev_add (ev_add (ev_add (ev_add (ev_add
      (ev_var (x := "lt") (v := total ws) (by rw [g "lt" (by decide), hT]) (by omega))
      (ev_var (x := "lt") (v := total ws) (by rw [g "lt" (by decide), hT]) (by omega)) (by omega))
      (ev_var (x := "m") (v := ws.length) (by rw [g "m" (by decide), hm]) (by omega)) (by omega))
      (ev_var (x := "m") (v := ws.length) (by rw [g "m" (by decide), hm]) (by omega)) (by omega))
      (ev_add (ev_var (x := "bl") (v := b.length) (by rw [g "bl" (by decide), hbl]) (by omega))
        (ev_var (x := "po") (v := po) (by rw [g "po" (by decide), hpo]) (by omega)) (by omega)) (by omega))
      (ev_add (ev_var (x := "nx") (v := nx) (by rw [g "nx" (by decide), hnx]) (by omega))
        (ev_var o5.self (by omega)) (by omega)) (by omega)) (evalB_lit (n := 64) (by omega)) (by omega))
  have hrun : Run (W + 1) rmS τ τ6 (30 * total ws + 30 * b.length + 100) := by
    unfold rmS
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono
      (by simp only [Expr.size]; omega)
  refine ⟨τ6, hrun, by rw [o6.self, sOf]; omega, fun y hy => hrun.frame_var y hy, ?_, hrun.out_eq (by decide),
    hrun.frame_inp (by decide)⟩
  rw [o6.arrs, o5.arrs, o4.arrs, r3.frame_arrs_eqOn (by simp [mxSeg, mxBody, forUp, Com.warrs]), o2.arrs, a1]


/-- **The room check during a round.** -/
theorem rmL_run {W nx mw po R : ℕ} {ws : List (List ℕ)} {b : List ℕ} {τ : Env}
    (hW : τ.vars "W" = W) (hW24 : 2 ^ 24 < W) (hR : τ.vars "rR" = min R W)
    (hL : Lib ws τ) (hz : τ.vars "z0" = 0) (hbl : τ.vars "bl" = b.length) (hy : SegAt "y" 0 b τ)
    (harr : ArrW W τ) (hnx : τ.vars "nx" = nx) (hpo : τ.vars "po" = po) (hmw : τ.vars "mw" = mw)
    (hsz : 64 * (nx + po + b.length + mw + total ws + ws.length + 8) ≤ W)
    (hva : ∀ w ∈ ws, ∀ v ∈ w, 64 * v ≤ W) (hvb : ∀ v ∈ b, 64 * v ≤ W) :
    ∃ τ', Run (W + 1) rmL τ τ' (30 * total ws + 30 * b.length + 300) ∧
      τ'.vars "ovf" = (if 2 ^ 24 * R * R * R * R *
          sOf (total ws) ws.length b.length po nx mw (maxEntry ws.flatten) (maxEntry b) *
          sOf (total ws) ws.length b.length po nx mw (maxEntry ws.flatten) (maxEntry b) < W
        then τ.vars "ovf" else 1) ∧
      (∀ y, y ∉ rmL.wvars → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  obtain ⟨τ1, r1, s1, f1, a1, u1, i1⟩ := rmS_run hL hz hbl hy harr hnx hpo hmw hsz hva hvb
  have hS : sOf (total ws) ws.length b.length po nx mw (maxEntry ws.flatten) (maxEntry b) ≤ W := by
    have hmA : maxEntry ws.flatten ≤ W / 64 := maxEntry_le fun v hv => by
      obtain ⟨w, hw, hv'⟩ := List.mem_flatten.1 hv; have := hva w hw v hv'; omega
    have hmB : maxEntry b ≤ W / 64 := maxEntry_le fun v hv => by have := hvb v hv; omega
    unfold sOf; omega
  obtain ⟨τ2, r2, h2, f2, a2, u2, i2⟩ := rmB_run (R := R) (τ := τ1)
    (by rw [f1 "W" (by decide), hW]) hW24 (by rw [f1 "rR" (by decide), hR]) s1 hS
  refine ⟨τ2, (Run.seq r1 r2).mono (by omega), by rw [h2, f1 "ovf" (by decide)], fun y hy => ?_,
    by rw [a2, a1], by rw [u2, u1], by rw [i2, i1]⟩
  rw [f2 y (fun h => hy (by simp [rmL, Com.wvars] at h ⊢; tauto)),
    f1 y (fun h => hy (by simp [rmL, Com.wvars] at h ⊢; tauto))]

end Lax185574Proofs.ResolveRam.Glue
