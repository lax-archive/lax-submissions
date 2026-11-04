import Lax185574Proofs.MC.Glue.Sat


/-!
The table of radii of the localization: `RP[d] = rhoPlus (d + 2) (q - d - 1)`
for `d < q`, computed by saturating powers. The table is exact when
`9 ^ ((q + 1) * q) ≤ W`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC
open Lax3.DistFO (rhoPlus)

/-- One entry of the table. -/
def rpBody : Com :=
  .seq (.assign "zx" (.sub (.var "rk") (.var "zd"))) (.seq (.assign "zy" (.add (.var "rk") (.lit 1)))
    (.seq (satMul "zy" "zx" "ze") (.seq (.assign "zP" (.lit 1))
      (.seq (satPow "zP" "zc9" "zi" "ze") (.store "RP" (.var "zd") (.var "zP"))))))

/-- The table. -/
def rpTab : Com := forUp "zd" (.var "rk") rpBody

theorem rhoPlus_eq_pow {q d : ℕ} (h : d < q) : rhoPlus (d + 2) (q - d - 1) = 9 ^ ((q + 1) * (q - d)) := by
  simp only [rhoPlus]; congr 1
  have : d + 2 + (q - d - 1) = q + 1 := by omega
  rw [this, show q - d - 1 + 1 = q - d by omega]

theorem rpTab_run {B W q : ℕ} {σ : Env} (hW : σ.vars "W" = W) (hWB : W < B)
    (hq : σ.vars "rk" = q) (hc9 : σ.vars "zc9" = 9) (hqW : q + 2 ≤ W) (h9 : 9 ≤ W)
    (hP : 9 ^ ((q + 1) * q) ≤ W) (hlen : q ≤ (σ.arrs "RP").length) :
    ∃ σ', Run B rpTab σ σ' (q * (23 * ((q + 1) * q) + 80) + 10) ∧
      (∀ d < q, (σ'.arrs "RP")[d]? = some (rhoPlus (d + 2) (q - d - 1))) ∧
      (∀ a, a ≠ "RP" → σ'.arrs a = σ.arrs a) := by
  obtain ⟨σ', r, ⟨hT, hF, hA, hL⟩, -⟩ := forUp_run (B := B) (σ := σ) (i := "zd") (e := .var "rk")
    (body := rpBody) (N := q) (K := 23 * ((q + 1) * q) + 70)
    (fun k τ => (∀ d < k, (τ.arrs "RP")[d]? = some (rhoPlus (d + 2) (q - d - 1))) ∧
      (∀ y ∈ ["W", "rk", "zc9"], τ.vars y = σ.vars y) ∧
      (∀ a, a ≠ "RP" → τ.arrs a = σ.arrs a) ∧ (τ.arrs "RP").length = (σ.arrs "RP").length)
    (by omega)
    (fun k _ τ hI _ => ev_var (by rw [hI.2.1 "rk" (by simp), hq]) (by omega))
    ⟨fun d h => absurd h (by omega), fun y hy => by simp at hy; rcases hy with rfl | rfl | rfl <;> simp,
      fun a _ => by simp, by simp⟩
    (by
      rintro k hk τ ⟨hT, hF, hA, hL⟩ hik
      have hτW : τ.vars "W" = W := by rw [hF "W" (by simp), hW]
      have hτq : τ.vars "rk" = q := by rw [hF "rk" (by simp), hq]
      have hτ9 : τ.vars "zc9" = 9 := by rw [hF "zc9" (by simp), hc9]
      set τ₁ := (τ.setVar "zx" (q - k)).setVar "zy" (q + 1) with hτ₁
      have r₁a : Run B (.assign "zx" (.sub (.var "rk") (.var "zd"))) τ (τ.setVar "zx" (q - k)) 4 :=
        Run.assign (ev_sub (ev_var hτq (by omega)) (ev_var hik (by omega)) (by omega))
      have r₁b : Run B (.assign "zy" (.add (.var "rk") (.lit 1))) (τ.setVar "zx" (q - k)) τ₁ 4 :=
        Run.assign (ev_add (ev_var (by simp [hτq]) (by omega)) (evalB_lit (by omega)) (by omega))
      have hE : (q + 1) * (q - k) ≤ (q + 1) * q := Nat.mul_le_mul_left _ (by omega)
      have hEW : (q + 1) * (q - k) ≤ W := by
        have := lt_nine_pow ((q + 1) * q); omega
      have r₂ := satMul_run (B := B) (x := "zy") (y := "zx") (z := "ze") (σ := τ₁)
        (by simp [hτ₁, hτW]) hWB (by simp [hτ₁]; omega) (by simp [hτ₁]; omega)
      set τ₂ := τ₁.setVar "ze" (min (τ₁.vars "zy" * τ₁.vars "zx") W) with hτ₂
      have he : τ₂.vars "ze" = (q + 1) * (q - k) := by simp [hτ₂, hτ₁]; omega
      obtain ⟨σ₄, r₄, hP₄, hF₄, hA₄⟩ := satPow_run (B := B) (W := W) (a0 := 1) (b := 9)
        (N := (q + 1) * (q - k))
        (acc := "zP") (base := "zc9") (i := "zi") (n := "ze") (σ := τ₂.setVar "zP" 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp [hτ₂, hτ₁, hτW]) hWB (by simp; omega) (by simp [hτ₂, hτ₁, hτ9]; omega)
        (by simp [he]) (by omega)
      rw [Nat.one_mul] at hP₄
      have hpow : 9 ^ ((q + 1) * (q - k)) ≤ W :=
        le_trans (Nat.pow_le_pow_right (by norm_num) hE) hP
      rw [min_eq_left hpow] at hP₄
      have hzd : σ₄.vars "zd" = k := by rw [hF₄ _ (by decide) (by decide)]; simp [hτ₂, hτ₁, hik]
      have hRl : k < (σ₄.arrs "RP").length := by rw [hA₄]; simp [hτ₂, hτ₁, hL]; omega
      refine ⟨σ₄.setArr "RP" k (9 ^ ((q + 1) * (q - k))), ?_, by simp [hzd], ?_, ?_, ?_, ?_⟩
      · refine (Run.seq r₁a (Run.seq r₁b (Run.seq r₂ (Run.seq (Run.assign (evalB_lit (by omega)))
          (Run.seq r₄ (Run.store (ev_var hzd (by omega)) (ev_var hP₄ (by omega)) hRl)))))).mono ?_
        simp; omega
      · intro d hd
        simp only [arrs_setVar, arrs_setArr, if_true]
        rw [List.getElem?_set]
        by_cases hdk : k = d
        · subst hdk; simp [hRl, rhoPlus_eq_pow hk]
        · rw [if_neg hdk, hA₄]; simp [hτ₂, hτ₁]; exact hT d (by omega)
      · intro y hy
        simp at hy
        rcases hy with rfl | rfl | rfl <;>
          · simp only [vars_setVar, vars_setArr, arrs_setVar]
            rw [hF₄ _ (by decide) (by decide)]; simp [hτ₂, hτ₁, hF]
      · intro a ha
        simp [ha, hA₄, hτ₂, hτ₁, hA a ha]
      · simp [hA₄, hτ₂, hτ₁, hL])
  refine ⟨σ', r.mono (by simp; nlinarith), fun d hd => hT d hd, fun a ha => hA a ha⟩

end Lax185574Proofs.MC.Glue
