import Lax185574Proofs.StpRam.Spec
import Lax185574Proofs.Words.ForLoop

/-!
The table of the radius bounds of lem:compute-stp.

`rtCmd` stores `radius k q i = 9^(k + i + (k + q + 1)(q − i))` into
entry `i` of the array `rt`, for `i = 0, …, q`, by repeated
multiplication with `9`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax3.DistFO (rhoMinus)

/-- The exponent of the radius bound of level `i`. -/
def radExp (k q i : ℕ) : ℕ := (k + i) + (k + q + 1) * (q - i)

theorem radius_eq (k q i : ℕ) (hi : i ≤ q) : radius k q i = 9 ^ radExp k q i := by
  unfold radius radExp
  simp only [Lax3.DistFO.rhoMinus]
  rw [← pow_add, show k + i + (q - i) + 1 = k + q + 1 by omega]

theorem radExp_le (k q i : ℕ) (hi : i ≤ q) : radExp k q i ≤ radExp k q 0 := by
  unfold radExp
  obtain ⟨m, rfl⟩ : ∃ m, q = i + m := ⟨q - i, by omega⟩
  rw [show i + m - i = m by omega, Nat.sub_zero, Nat.mul_add]
  have : i ≤ (k + (i + m) + 1) * i := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem radius_le_zero (k q i : ℕ) (hi : i ≤ q) : radius k q i ≤ radius k q 0 := by
  rw [radius_eq k q i hi, radius_eq k q 0 (Nat.zero_le _)]
  exact Nat.pow_le_pow_right (by norm_num) (radExp_le k q i hi)

theorem radExp_lt (k q : ℕ) : radExp k q 0 < radius k q 0 := by
  rw [radius_eq k q 0 (Nat.zero_le _)]
  exact Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by norm_num) _)

/-- Multiply `rp` by `9`, `re` times. -/
def powLoop : Com := forUp "rj" (.var "re") (.assign "rp" (.mul (.var "rp") (.lit 9)))

def rtBody : Com :=
  .seq (.assign "re" (.add (.add (.var "kk") (.var "ri"))
    (.mul (.add (.add (.var "kk") (.var "qq")) (.lit 1)) (.sub (.var "qq") (.var "ri")))))
    (.seq (.assign "rp" (.lit 1)) (.seq powLoop (.store "rt" (.var "ri") (.var "rp"))))

def rtCmd : Com := forUp "ri" (.add (.var "qq") (.lit 1)) rtBody

theorem powLoop_run {B e : ℕ} {σ : Env} (he : σ.vars "re" = e) (hp : σ.vars "rp" = 1)
    (hB : 9 ^ e < B) (heB : e < B) (h9B : 9 < B) :
    ∃ σ', Run B powLoop σ σ' (e * 13 + 6) ∧ σ'.vars "rp" = 9 ^ e ∧
      (∀ x, x ≠ "rj" → x ≠ "rp" → σ'.vars x = σ.vars x) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ', hr, ⟨hp', hv', ha'⟩, -⟩ := forUp_run (B := B) (i := "rj") (e := .var "re")
    (body := .assign "rp" (.mul (.var "rp") (.lit 9))) (N := e) (K := 5)
    (fun j τ => τ.vars "rp" = 9 ^ j ∧ (∀ x, x ≠ "rj" → x ≠ "rp" → τ.vars x = σ.vars x) ∧
      τ.arrs = σ.arrs) (σ := σ) heB
    (fun j _ τ hI _ => by
      simp only [evalB_var_iff]
      exact ⟨by rw [hI.2.1 "re" (by decide) (by decide), he], by
        rw [hI.2.1 "re" (by decide) (by decide), he]; exact heB⟩)
    ⟨by simp [hp], fun x h1 h2 => by simp [h1], by simp⟩
    (by
      rintro j hj τ ⟨hpj, hv, ha⟩ hrj
      have h9 : 9 ^ (j + 1) < B :=
        Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hB
      have h9' : 9 ^ j < B := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hB
      refine ⟨τ.setVar "rp" (9 ^ (j + 1)), (Run.assign ?_).mono (by simp), by simp [hrj],
        by simp, fun x h1 h2 => by simp [h1, h2, hv x h1 h2], by simp [ha]⟩
      simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨9 ^ j, 9, ⟨hpj.symm, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply, pow_succ], h9⟩)
  exact ⟨σ', hr.mono (by simp), hp', hv', ha'⟩

/-- **The radius table.** -/
theorem kq_le_radius (k q : ℕ) : k + q + 1 ≤ radius k q 0 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [radius_eq k 0 0 le_rfl]
    simp only [radExp, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
    exact Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by norm_num) _)
  · have h1 : k + q + 1 ≤ radExp k q 0 := by
      unfold radExp; simp only [Nat.sub_zero, Nat.add_zero]; nlinarith
    have := radExp_lt k q
    omega

theorem rtCmd_run {B k q : ℕ} {σ : Env} (hk : σ.vars "kk" = k) (hq : σ.vars "qq" = q)
    (hrt : q + 1 ≤ (σ.arrs "rt").length) (hB : radius k q 0 + 1 < B) (h9B : 9 < B) :
    ∃ σ', Run B rtCmd σ σ' ((q + 1) * (13 * radExp k q 0 + 50) + 8) ∧
      (∀ i ≤ q, (σ'.arrs "rt")[i]? = some (radius k q i)) ∧
      (σ'.arrs "rt").length = (σ.arrs "rt").length ∧
      (∀ x, x ∉ ["ri", "re", "rp", "rj"] → σ'.vars x = σ.vars x) ∧
      (∀ a, a ≠ "rt" → σ'.arrs a = σ.arrs a) := by
  have hE := radExp_lt k q
  have hkq := kq_le_radius k q
  set E := radExp k q 0 with hEdef
  obtain ⟨σ', hr, ⟨hrt', hl', hv', ha'⟩, -⟩ := forUp_run (B := B) (i := "ri")
    (e := .add (.var "qq") (.lit 1)) (body := rtBody) (N := q + 1) (K := 13 * E + 40)
    (fun j τ => (∀ i < j, (τ.arrs "rt")[i]? = some (radius k q i)) ∧
      (τ.arrs "rt").length = (σ.arrs "rt").length ∧
      (∀ x, x ∉ ["ri", "re", "rp", "rj"] → τ.vars x = σ.vars x) ∧
      (∀ a, a ≠ "rt" → τ.arrs a = σ.arrs a)) (σ := σ) (by omega)
    (fun j _ τ hI _ => by
      have hq' : τ.vars "qq" = q := by rw [hI.2.2.1 "qq" (by decide), hq]
      simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨q, 1, ⟨hq'.symm, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩)
    ⟨fun i hi => absurd hi (Nat.not_lt_zero _), by simp, fun x hx => by
      simp at hx; simp [show x ≠ "ri" by intro h; exact hx.1 h], fun a _ => by simp⟩
    (by
      rintro j hj τ ⟨hrtτ, hlτ, hvτ, haτ⟩ hri
      have hkτ : τ.vars "kk" = k := by rw [hvτ "kk" (by decide), hk]
      have hqτ : τ.vars "qq" = q := by rw [hvτ "qq" (by decide), hq]
      have hjq : j ≤ q := by omega
      have hEj := radExp_le k q j hjq
      have hradj := radius_eq k q j hjq
      have h9 : 9 ^ radExp k q j < B := by
        rw [← hradj]; have := radius_le_zero k q j hjq; omega
      have hlt : radExp k q j < B := by omega
      set τ1 := τ.setVar "re" (radExp k q j) with hτ1
      have r1 : Run B (.assign "re" (.add (.add (.var "kk") (.var "ri"))
          (.mul (.add (.add (.var "kk") (.var "qq")) (.lit 1)) (.sub (.var "qq") (.var "ri"))))) τ τ1
          20 := by
        refine (Run.assign ?_).mono (by simp)
        simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
        have hmul : (k + q + 1) * (q - j) ≤ radExp k q j := by unfold radExp; omega
        refine ⟨k + j, (k + q + 1) * (q - j), ⟨k, j, ⟨hkτ.symm, by omega⟩, ⟨hri.symm, by omega⟩,
          by simp [Bop.apply], by omega⟩, ⟨k + q + 1, q - j, ⟨k + q, 1, ⟨k, q, ⟨hkτ.symm, by omega⟩,
          ⟨hqτ.symm, by omega⟩, by simp [Bop.apply], by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply],
          by omega⟩, ⟨q, j, ⟨hqτ.symm, by omega⟩, ⟨hri.symm, by omega⟩, by simp [Bop.apply],
          by omega⟩, by simp [Bop.apply], by omega⟩, by simp [Bop.apply, radExp], hlt⟩
      set τ2 := τ1.setVar "rp" 1 with hτ2
      have r2 : Run B (.assign "rp" (.lit 1)) τ1 τ2 2 := (Run.assign (by simp; omega)).mono (by simp)
      obtain ⟨τ3, r3, hp3, hv3, ha3⟩ := powLoop_run (σ := τ2) (B := B) (e := radExp k q j)
        (by simp [hτ2, hτ1]) (by simp [hτ2]) h9 hlt h9B
      have hri3 : τ3.vars "ri" = j := by rw [hv3 "ri" (by decide) (by decide)]; simp [hτ2, hτ1, hri]
      have hl3 : (τ3.arrs "rt").length = (σ.arrs "rt").length := by rw [ha3]; simp [hτ2, hτ1, hlτ]
      refine ⟨τ3.setArr "rt" j (9 ^ radExp k q j), (Run.seq r1 (Run.seq r2 (Run.seq r3
        (Run.store (by simp [hri3]; omega) (by simp [hp3]; omega) (by rw [hl3]; omega))))).mono ?_,
        by simp [hri3], fun i hi => ?_, by simp [hl3], fun x hx => ?_, fun a ha => ?_⟩
      · have : radExp k q j * 13 ≤ 13 * E := by omega
        simp only [Expr.size]; omega
      · simp only [arrs_setVar, arrs_setArr, if_true, List.getElem?_set]
        by_cases hij : j = i
        · subst hij; simp [hl3]; rw [hradj]; omega
        · rw [if_neg hij, ha3]
          simp only [hτ2, hτ1, arrs_setVar]
          exact hrtτ i (by omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp only [vars_setVar, vars_setArr, if_neg hx.1]
        rw [hv3 x hx.2.2.2 hx.2.2.1]
        simp [hτ2, hτ1, hx.2.1, hx.2.2.1, hvτ x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2])]
      · simp only [arrs_setVar, arrs_setArr, if_neg ha, ha3, hτ2, hτ1]
        exact haτ a ha)
  refine ⟨σ', hr.mono ?_, fun i hi => hrt' i (by omega), hl', hv', ha'⟩
  simp only [Expr.size]
  nlinarith

end Lax185574Proofs.StpRam
