import Lax185574Proofs.MC.Ram.InitTop
import Lax185574Proofs.MC.Glue.Loc


/-!
Saturating arithmetic for the glue program of thm:mc.

With `W` in the scalar `"W"`, `satAdd x y z` and `satMul x y z` set `z`
to `min (x + y) W` and `min (x * y) W`, and never produce a value above
`W`. Since `min · W` commutes with sums and products, a chain of these
operations computes `min f W` for the polynomial `f` it follows. The
glue program uses this to test `4 L + c + 20 < W` for the length `L` of
the initial trees before it writes them, through the bound `glM q ≥ L`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC

/-! ### The two operations -/

/-- `z := min (x + y) W`. -/
def satAdd (x y z : String) : Com :=
  .ite (.lt (.sub (.var "W") (.var x)) (.var y)) (.assign z (.var "W"))
    (.assign z (.add (.var x) (.var y)))

/-- `z := min (x * y) W`. -/
def satMul (x y z : String) : Com :=
  .ite (.eq (.var y) (.lit 0)) (.assign z (.lit 0))
    (.ite (.lt (.div (.var "W") (.var y)) (.var x)) (.assign z (.var "W"))
      (.assign z (.mul (.var x) (.var y))))

theorem satAdd_run {B W : ℕ} {x y z : String} {σ : Env} (hW : σ.vars "W" = W) (hWB : W < B)
    (hx : σ.vars x ≤ W) (hy : σ.vars y ≤ W) :
    Run B (satAdd x y z) σ (σ.setVar z (min (σ.vars x + σ.vars y) W)) 10 := by
  unfold satAdd
  have hc : (Cond.lt (.sub (.var "W") (.var x)) (.var y)).evalB B σ =
      some (decide (W - σ.vars x < σ.vars y)) :=
    evalB_condLt (ev_sub (ev_var hW hWB) (evalB_var (by omega)) (by omega)) (evalB_var (by omega))
  by_cases h : W - σ.vars x < σ.vars y
  · have : min (σ.vars x + σ.vars y) W = W := by omega
    rw [this]
    exact (Run.ite_true (by rw [hc]; simp [h]) (Run.assign (ev_var hW hWB))).mono (by simp)
  · have : min (σ.vars x + σ.vars y) W = σ.vars x + σ.vars y := by omega
    rw [this]
    exact (Run.ite_false (by rw [hc]; simp [h]) (Run.assign (ev_add (evalB_var (by omega))
      (evalB_var (by omega)) (by omega)))).mono (by simp)

theorem satMul_run {B W : ℕ} {x y z : String} {σ : Env} (hW : σ.vars "W" = W) (hWB : W < B)
    (hx : σ.vars x ≤ W) (hy : σ.vars y ≤ W) :
    Run B (satMul x y z) σ (σ.setVar z (min (σ.vars x * σ.vars y) W)) 15 := by
  unfold satMul
  have hc0 : (Cond.eq (.var y) (.lit 0)).evalB B σ = some (σ.vars y == 0) :=
    evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))
  by_cases h0 : σ.vars y = 0
  · rw [h0, Nat.mul_zero, Nat.zero_min]
    exact (Run.ite_true (by rw [hc0]; simp [h0]) (Run.assign (evalB_lit (by omega)))).mono
      (by simp)
  · have hd : (Expr.div (.var "W") (.var y)).evalB B σ = some (W / σ.vars y) :=
      evalB_bin (ev_var hW hWB) (evalB_var (by omega)) (lt_of_le_of_lt (Nat.div_le_self _ _) hWB)
    have hc : (Cond.lt (.div (.var "W") (.var y)) (.var x)).evalB B σ =
        some (decide (W / σ.vars y < σ.vars x)) := evalB_condLt hd (evalB_var (by omega))
    have hiff : W / σ.vars y < σ.vars x ↔ W < σ.vars x * σ.vars y :=
      Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero h0)
    by_cases h : W / σ.vars y < σ.vars x
    · have : min (σ.vars x * σ.vars y) W = W := by have := hiff.mp h; omega
      rw [this]
      exact (Run.ite_false (by rw [hc0]; simp [h0]) (Run.ite_true (by rw [hc]; simp [h])
        (Run.assign (ev_var hW hWB)))).mono (by simp)
    · have hle : σ.vars x * σ.vars y ≤ W := by
        by_contra hh; exact h (hiff.mpr (by omega))
      have : min (σ.vars x * σ.vars y) W = σ.vars x * σ.vars y := by omega
      rw [this]
      exact (Run.ite_false (by rw [hc0]; simp [h0]) (Run.ite_false (by rw [hc]; simp [h])
        (Run.assign (evalB_bin (evalB_var (by omega)) (evalB_var (by omega))
          (by simp [Bop.apply]; omega))))).mono (by simp)

/-! ### Saturation commutes with sums and products -/

theorem min_add_min (a b W : ℕ) : min (min a W + min b W) W = min (a + b) W := by omega

theorem min_mul_min (a b W : ℕ) : min (min a W * min b W) W = min (a * b) W := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  by_cases hA : a ≤ W <;> by_cases hB : b ≤ W
  · rw [min_eq_left hA, min_eq_left hB]
  · have hb' : W < b := not_le.mp hB
    rw [min_eq_left hA, min_eq_right hb'.le,
      min_eq_right (Nat.le_mul_of_pos_left W ha),
      min_eq_right (le_trans hb'.le (Nat.le_mul_of_pos_left b ha))]
  · have ha' : W < a := not_le.mp hA
    rw [min_eq_left hB, min_eq_right ha'.le,
      min_eq_right (Nat.le_mul_of_pos_right W hb),
      min_eq_right (le_trans ha'.le (Nat.le_mul_of_pos_right a hb))]
  · have ha' : W < a := not_le.mp hA
    rw [min_eq_right ha'.le, min_eq_right (not_le.mp hB).le,
      min_eq_right (le_trans ha'.le (Nat.le_mul_of_pos_right a hb))]
    rcases Nat.eq_zero_or_pos W with h | h
    · simp [h]
    · exact min_eq_right (Nat.le_mul_of_pos_right W h)


/-! ### Powers -/

/-- `acc := min (acc * base ^ N) W`, with `N` the value of `n` and the counter `i`. -/
def satPow (acc base i n : String) : Com := forUp i (.var n) (satMul acc base acc)

theorem satPow_run {B W a0 b N : ℕ} {acc base i n : String} {σ : Env}
    (h1 : acc ≠ base) (h2 : acc ≠ i) (h3 : acc ≠ n) (h4 : base ≠ i) (h5 : n ≠ i)
    (h6 : acc ≠ "W") (h7 : i ≠ "W")
    (hW : σ.vars "W" = W) (hWB : W < B) (hacc : σ.vars acc = min a0 W)
    (hb : σ.vars base = min b W) (hn : σ.vars n = N) (hN : N < B) :
    ∃ σ', Run B (satPow acc base i n) σ σ' (N * 23 + 6) ∧ σ'.vars acc = min (a0 * b ^ N) W ∧
      (∀ y, y ≠ acc → y ≠ i → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ', r, ⟨hA, hF, hR⟩, -⟩ := forUp_run (B := B) (σ := σ) (i := i) (e := .var n)
    (body := satMul acc base acc) (N := N) (K := 15)
    (fun k τ => τ.vars acc = min (a0 * b ^ k) W ∧ (∀ y, y ≠ acc → y ≠ i → τ.vars y = σ.vars y) ∧
      τ.arrs = σ.arrs) hN
    (fun k _ τ hI _ => ev_var (by rw [hI.2.1 n h3.symm h5, hn]) hN)
    ⟨by simp [h2, hacc], fun y hy hy' => by simp [hy'], by simp⟩
    (by
      rintro k - τ ⟨hA, hF, hR⟩ hik
      have hτW : τ.vars "W" = W := by rw [hF "W" (Ne.symm h6) (Ne.symm h7), hW]
      have hτb : τ.vars base = min b W := by rw [hF base (Ne.symm h1) h4, hb]
      refine ⟨_, satMul_run hτW hWB (by rw [hA]; omega) (by rw [hτb]; omega), by simp [h2.symm, hik],
        ?_, fun y hy hy' => ?_, by simp [hR]⟩
      · simp only [vars_setVar, if_neg h2, ↓reduceIte]
        rw [hA, hτb, min_mul_min, pow_succ, Nat.mul_assoc]
      · simp [hy, hy', hF y hy hy'])
  exact ⟨σ', r.mono (by simp), hA, hF, hR⟩

/-! ### A bound on the length of the initial trees -/

/-- The largest arity, `q + 1`. -/
def glA (q : ℕ) : ℕ := q + 1
/-- A bound on the radii of the initial trees. -/
def glP (q : ℕ) : ℕ := 9 ^ ((q + 2) * (q + 1))
/-- A bound on the length of one atom word. -/
def glC (q : ℕ) : ℕ := 20 * (glA q * glA q) * (glP q + 1)
/-- A bound on the length of the initial trees. -/
def glM (q : ℕ) : ℕ := (glC q + 3) * (glA q + 1) ^ (q + 1)

theorem alen_mono {a a' rm rm' rp rp' : ℕ} (ha : a ≤ a') (hm : rm ≤ rm') (hp : rp ≤ rp') :
    alen a rm rp ≤ alen a' rm' rp' := by
  unfold alen
  have h1 : a * a ≤ a' * a' := Nat.mul_le_mul ha ha
  have h2 : (rm + 1) * (a * a) ≤ (rm' + 1) * (a' * a') := Nat.mul_le_mul (by omega) h1
  have h3 : rp * a ≤ rp' * a' := Nat.mul_le_mul hp ha
  omega

theorem alen_le_glC {q d : ℕ} (hd : d ≤ q) :
    alen (1 + q - d) (rmD (1 + q) d) (rpD (1 + q) d) ≤ glC q := by
  have hm : rmD (1 + q) d ≤ glP q := Nat.pow_le_pow_right (by norm_num) (by
    have : (1 + q + 1) * d ≤ (q + 2) * (q + 1) := Nat.mul_le_mul (by omega) (by omega)
    exact this)
  have hp : rpD (1 + q) d ≤ glP q := Nat.pow_le_pow_right (by norm_num) (by
    have : (1 + q) * (d + 1) ≤ (q + 2) * (q + 1) := by
      rw [Nat.mul_comm (q + 2)]; exact Nat.mul_le_mul (by omega) (by omega)
    exact this)
  refine le_trans (alen_mono (a' := glA q) (by simp [glA]; omega) hm hp) ?_
  simp only [alen, glC]
  have hA : 1 ≤ glA q := by simp [glA]
  generalize glA q = A at *
  generalize glP q = P
  have h1 : 1 ≤ A * A := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : A ≤ A * A := Nat.le_mul_of_pos_left A hA
  have h3 : P * A ≤ (P + 1) * (A * A) := Nat.mul_le_mul (by omega) h2
  nlinarith

theorem lvlLen_le_glM (q : ℕ) : ∀ d, d ≤ q →
    lvlLen (1 + q) q 1 d ≤ (glC q + 3) * (glA q + 1) ^ (d + 1)
  | 0, _ => by
      have h : alen (1 + q) (rmD (1 + q) 0) (rpD (1 + q) 0) ≤ glC q :=
        alen_le_glC (q := q) (d := 0) (Nat.zero_le _)
      show alen (1 + q) (rmD (1 + q) 0) (rpD (1 + q) 0) ≤ (glC q + 3) * (glA q + 1) ^ (0 + 1)
      have : glC q + 3 ≤ (glC q + 3) * (glA q + 1) ^ (0 + 1) :=
        Nat.le_mul_of_pos_right _ (by positivity)
      omega
  | d + 1, hd => by
      have ih := lvlLen_le_glM q d (by omega)
      have h := alen_le_glC (q := q) (d := d + 1) hd
      have ha : 1 + q - (d + 1) ≤ glA q := by simp [glA]; omega
      simp only [lvlLen]
      rw [show 1 + q - (d + 1) = 1 + q - (d + 1) from rfl] at h
      have e1 : (1 + q - (d + 1)) * (lvlLen (1 + q) q 1 d + 2) ≤
          glA q * ((glC q + 3) * (glA q + 1) ^ (d + 1) + 2) := Nat.mul_le_mul ha (by omega)
      have e2 : (glC q + 3) * (glA q + 1) ^ (d + 1 + 1) =
          glA q * ((glC q + 3) * (glA q + 1) ^ (d + 1)) + (glC q + 3) * (glA q + 1) ^ (d + 1) := by
        ring
      have e3 : glC q + 3 + 2 * glA q ≤ (glC q + 3) * (glA q + 1) ^ (d + 1) := by
        have : (glA q + 1) ^ 1 ≤ (glA q + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hA : 1 ≤ glA q := by simp [glA]
        nlinarith
      rw [show 1 + q - (d + 1) = q - d from by omega] at h e1
      rw [show (1 : ℕ) + q - (d + 1) = q - d from by omega]
      nlinarith

theorem lvlLen_le_glM' (q : ℕ) : lvlLen (1 + q) q 1 q ≤ glM q := lvlLen_le_glM q q le_rfl


theorem min_pow9 (E W : ℕ) : min (9 ^ (min E W)) W = min (9 ^ E) W := by
  by_cases h : E ≤ W
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega : W ≤ E)]
    have h1 := lt_nine_pow W
    have h2 : 9 ^ W ≤ 9 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- `zM := min (glM q) W` for `q` in `rk`. -/
def mInit : Com :=
  .seq (.assign "zc1" (.lit 1)) (.seq (.assign "zc3" (.lit 3)) (.seq (.assign "zc9" (.lit 9))
  (.seq (.assign "zc20" (.lit 20)) (.seq (.assign "zA" (.add (.var "rk") (.lit 1)))
  (.assign "zA2" (.add (.var "rk") (.lit 2)))))))

def mBound : Com :=
  .seq mInit
  (.seq (satMul "zA2" "zA" "zE") (.seq (.assign "zP" (.lit 1))
  (.seq (satPow "zP" "zc9" "zi" "zE") (.seq (satAdd "zP" "zc1" "zP1")
  (.seq (satMul "zA" "zA" "zAA") (.seq (satMul "zc20" "zAA" "zT")
  (.seq (satMul "zT" "zP1" "zC") (.seq (satAdd "zC" "zc3" "zM")
  (satPow "zM" "zA2" "zi" "zA")))))))))

theorem mBound_run {B W q : ℕ} {σ : Env} (hW : σ.vars "W" = W) (hWB : W < B)
    (hq : σ.vars "rk" = q) (hqW : q + 2 ≤ W) (h20 : 20 ≤ W) :
    ∃ σ', Run B mBound σ σ' (23 * ((q + 2) * (q + 1)) + 23 * (q + 1) + 200) ∧
      σ'.vars "zM" = min (glM q) W := by
  set τ₁ := (((((σ.setVar "zc1" 1).setVar "zc3" 3).setVar "zc9" 9).setVar "zc20" 20).setVar "zA"
    (q + 1)).setVar "zA2" (q + 2) with hτ₁
  have r₁ : Run B mInit σ τ₁ 22 := by
    unfold mInit
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.seq (Run.assign (ev_add (ev_var (by simp [hq]) (by omega)) (evalB_lit (by omega))
        (by omega))) (Run.assign (ev_add (ev_var (by simp [hq]) (by omega)) (evalB_lit (by omega))
        (by omega)))))))).mono (by simp)
  have hW₁ : τ₁.vars "W" = W := by simp [hτ₁, hW]
  have r₂ := satMul_run (B := B) (x := "zA2") (y := "zA") (z := "zE") hW₁ hWB
    (by simp [hτ₁]; omega) (by simp [hτ₁]; omega)
  set τ₂ := τ₁.setVar "zE" (min (τ₁.vars "zA2" * τ₁.vars "zA") W) with hτ₂
  set τ₃ := τ₂.setVar "zP" 1 with hτ₃
  have r₃ : Run B (.assign "zP" (.lit 1)) τ₂ τ₃ 2 := Run.assign (evalB_lit (by omega))
  have hE : τ₃.vars "zE" = min ((q + 2) * (q + 1)) W := by simp [hτ₃, hτ₂, hτ₁]
  obtain ⟨σ₄, r₄, hP₄, hF₄, -⟩ := satPow_run (B := B) (W := W) (a0 := 1) (b := 9)
    (acc := "zP") (base := "zc9") (i := "zi") (n := "zE") (σ := τ₃) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [hτ₃, hτ₂, hW₁]) hWB
    (by simp [hτ₃]; omega) (by simp [hτ₃, hτ₂, hτ₁]; omega) hE (by omega)
  rw [Nat.one_mul, min_pow9] at hP₄
  have v₄ (y : String) (h1 : y ≠ "zP") (h2 : y ≠ "zi") : σ₄.vars y = τ₃.vars y := hF₄ y h1 h2
  have hW₄ : σ₄.vars "W" = W := by rw [v₄ _ (by decide) (by decide)]; simp [hτ₃, hτ₂, hW₁]
  have hc1 : σ₄.vars "zc1" = 1 := by rw [v₄ _ (by decide) (by decide)]; simp [hτ₃, hτ₂, hτ₁]
  have hc3 : σ₄.vars "zc3" = 3 := by rw [v₄ _ (by decide) (by decide)]; simp [hτ₃, hτ₂, hτ₁]
  have hc20 : σ₄.vars "zc20" = 20 := by rw [v₄ _ (by decide) (by decide)]; simp [hτ₃, hτ₂, hτ₁]
  have hA : σ₄.vars "zA" = q + 1 := by rw [v₄ _ (by decide) (by decide)]; simp [hτ₃, hτ₂, hτ₁]
  have hA2 : σ₄.vars "zA2" = q + 2 := by rw [v₄ _ (by decide) (by decide)]; simp [hτ₃, hτ₂, hτ₁]
  -- the straight-line part
  have r₅ := satAdd_run (B := B) (x := "zP") (y := "zc1") (z := "zP1") hW₄ hWB
    (by rw [hP₄]; omega) (by rw [hc1]; omega)
  set τ₅ := σ₄.setVar "zP1" (min (σ₄.vars "zP" + σ₄.vars "zc1") W) with hτ₅
  have r₆ := satMul_run (B := B) (x := "zA") (y := "zA") (z := "zAA") (σ := τ₅)
    (by simp [hτ₅, hW₄]) hWB (by simp [hτ₅, hA]; omega) (by simp [hτ₅, hA]; omega)
  set τ₆ := τ₅.setVar "zAA" (min (τ₅.vars "zA" * τ₅.vars "zA") W) with hτ₆
  have r₇ := satMul_run (B := B) (x := "zc20") (y := "zAA") (z := "zT") (σ := τ₆)
    (by simp [hτ₆, hτ₅, hW₄]) hWB (by simp [hτ₆, hτ₅, hc20]; omega) (by simp [hτ₆])
  set τ₇ := τ₆.setVar "zT" (min (τ₆.vars "zc20" * τ₆.vars "zAA") W) with hτ₇
  have r₈ := satMul_run (B := B) (x := "zT") (y := "zP1") (z := "zC") (σ := τ₇)
    (by simp [hτ₇, hτ₆, hτ₅, hW₄]) hWB (by simp [hτ₇]) (by simp [hτ₇, hτ₆, hτ₅])
  set τ₈ := τ₇.setVar "zC" (min (τ₇.vars "zT" * τ₇.vars "zP1") W) with hτ₈
  have r₉ := satAdd_run (B := B) (x := "zC") (y := "zc3") (z := "zM") (σ := τ₈)
    (by simp [hτ₈, hτ₇, hτ₆, hτ₅, hW₄]) hWB (by simp [hτ₈]) (by simp [hτ₈, hτ₇, hτ₆, hτ₅, hc3]; omega)
  set τ₉ := τ₈.setVar "zM" (min (τ₈.vars "zC" + τ₈.vars "zc3") W) with hτ₉
  have p5 : τ₅.vars "zP1" = min (glP q + 1) W := by
    simp [hτ₅, hP₄, hc1, glP]; omega
  have a6 : τ₆.vars "zAA" = min ((q + 1) * (q + 1)) W := by simp [hτ₆, hτ₅, hA]
  have t7 : τ₇.vars "zT" = min (20 * ((q + 1) * (q + 1))) W := by
    have h := min_mul_min 20 ((q + 1) * (q + 1)) W
    rw [min_eq_left (by omega : 20 ≤ W)] at h
    rw [← h, ← a6]; simp [hτ₇, hτ₆, hτ₅, hc20]
  have c8 : τ₈.vars "zC" = min (glC q) W := by
    have h := min_mul_min (20 * ((q + 1) * (q + 1))) (glP q + 1) W
    rw [show glC q = 20 * ((q + 1) * (q + 1)) * (glP q + 1) by simp [glC, glA], ← h, ← t7, ← p5]
    simp [hτ₈, hτ₇, hτ₆]
  have hM₉ : τ₉.vars "zM" = min (glC q + 3) W := by
    have h3 : τ₈.vars "zc3" = 3 := by simp [hτ₈, hτ₇, hτ₆, hτ₅, hc3]
    have : τ₉.vars "zM" = min (τ₈.vars "zC" + τ₈.vars "zc3") W := by simp [hτ₉]
    rw [this, c8, h3]; omega
  obtain ⟨σ', r₁₀, hM, -, -⟩ := satPow_run (B := B) (W := W) (a0 := glC q + 3) (b := q + 2)
    (N := q + 1)
    (acc := "zM") (base := "zA2") (i := "zi") (n := "zA") (σ := τ₉) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [hτ₉, hτ₈, hτ₇, hτ₆, hτ₅, hW₄]) hWB hM₉
    (by simp [hτ₉, hτ₈, hτ₇, hτ₆, hτ₅, hA2]; omega) (by simp [hτ₉, hτ₈, hτ₇, hτ₆, hτ₅, hA]) (by omega)
  refine ⟨σ', ?_, by rw [hM]; simp [glM, glA]⟩
  have hEle : min ((q + 2) * (q + 1)) W ≤ (q + 2) * (q + 1) := min_le_left _ _
  unfold mBound
  exact (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ (Run.seq r₆
    (Run.seq r₇ (Run.seq r₈ (Run.seq r₉ r₁₀))))))))).mono (by nlinarith)

end Lax185574Proofs.MC.Glue
