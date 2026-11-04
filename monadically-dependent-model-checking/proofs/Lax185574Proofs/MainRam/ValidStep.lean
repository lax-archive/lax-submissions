import Lax185574Proofs.MainRam.ValidChk2

/-!
The validation program, part five: the simulation of the script on the
color vector `col` and the status matrix `S`. A merge computes the new
colors into `c2` and copies them back, a resolve computes the new
statuses into `S2` and copies them back.
-/

namespace Lax185574Proofs.MainRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Classical

theorem one_sub_eq_ind (x : ℕ) : 1 - x = ind (x = 0) := by
  unfold ind; split_ifs with h <;> omega

/-! ### A merge -/

def eqColQ : Expr := eqX (.get "col" (.var "b")) (.var "Q")

def eM : Expr :=
  .add (.mul (.get "col" (.var "b")) (.sub (.lit 1) eqColQ)) (.mul (.var "P") eqColQ)

def mergeC : Com :=
  .seq (rowFill "c2" (.var "b") eM) (rowFill "col" (.var "b") (.get "c2" (.var "b")))

/-- The colors after a merge. -/
noncomputable def mergeCol (c : ℕ → ℕ) (P Q : ℕ) : ℕ → ℕ := fun v => if c v = Q then P else c v

theorem mergeC_run {B Λ : ℕ} {σ : Env} {n P Q : ℕ} {c : ℕ → ℕ} (hn : σ.vars "n" = n)
    (hP : σ.vars "P" = P) (hQ : σ.vars "Q" = Q) (hc : Vec σ "col" n c)
    (hc2 : (σ.arrs "c2").length = n) (hcΛ : ∀ v < n, c v ≤ Λ) (hPΛ : P ≤ Λ) (hQΛ : Q ≤ Λ)
    (hnΛ : n ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ σ', Run B mergeC σ σ' (n * 80 + 20) ∧ Vec σ' "col" n (mergeCol c P Q) ∧
      (∀ z, z ≠ "b" → σ'.vars z = σ.vars z) ∧
      (∀ a, a ≠ "col" → a ≠ "c2" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      (σ'.arrs "c2").length = n := by
  let Ctx : Env → Prop := fun τ => τ.vars "n" = n ∧ τ.vars "P" = P ∧ τ.vars "Q" = Q ∧
    Vec τ "col" n c ∧ (∀ z, z ≠ "b" → τ.vars z = σ.vars z) ∧
    (∀ a, a ≠ "c2" → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out
  have hfB : ∀ k < n, mergeCol c P Q k < B := by
    intro k hk; unfold mergeCol; split_ifs <;> [omega; (have := hcΛ k hk; omega)]
  obtain ⟨σ₁, r₁, ⟨hn1, hP1, hQ1, hc1, hv1, ha1, hi1, ho1⟩, hl1, hg1⟩ := rowFill_run (B := B)
    (n := n) (base := 0) (K := 60) (arr := "c2") (ie := .var "b") (e := eM) Ctx
    (mergeCol c P Q) (by omega) (fun τ h => h.1)
    (fun τ x h => ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1], h.2.2.2.1.of_eq (by simp),
      fun z hz => by simp [hz, h.2.2.2.2.1 z hz], fun a ha => by simp [h.2.2.2.2.2.1 a ha],
      by simp [h.2.2.2.2.2.2.1], by simp [h.2.2.2.2.2.2.2]⟩)
    (fun τ i x h => ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1],
      h.2.2.2.1.of_eq (by simp), fun z hz => by simp [h.2.2.2.2.1 z hz],
      fun a ha => by simp [ha, h.2.2.2.2.2.1 a ha], by simp [h.2.2.2.2.2.2.1],
      by simp [h.2.2.2.2.2.2.2]⟩)
    (fun τ k h hb hk => by rw [evalB_var (by rw [hb]; omega), hb]; simp)
    (fun τ k h hb hk => by
      obtain ⟨hn', hP', hQ', hc', -⟩ := h
      have hck := hcΛ k hk
      have e1 := Vec.evalB (B := B) hc' hb hk (by omega) (by omega)
      have e2 := evalB_eqX (B := B) e1 (evalB_var (x := "Q") (by rw [hQ']; omega)) (by omega)
        (by omega) (by rw [hQ']; omega)
      rw [hQ'] at e2
      have e3 := evalB_bin (op := .sub) (evalB_lit (n := 1) (B := B) (σ := τ) (by omega)) e2
        (by have := ind_le_one (c k = Q); simp; omega)
      rw [Bop.apply_sub, one_sub_ind] at e3
      have e4 := evalB_bin (op := .mul) e1 e3 (by
        have := ind_le_one (¬ c k = Q)
        simp only [Bop.apply_mul]; nlinarith)
      have e5 := evalB_bin (op := .mul) (evalB_var (x := "P") (by rw [hP']; omega)) e2 (by
        have := ind_le_one (c k = Q)
        simp only [Bop.apply_mul]; rw [hP']; nlinarith)
      rw [hP'] at e5
      have e6 := evalB_bin (op := .add) e4 e5 (by
        have := ind_le_one (c k = Q); have := ind_le_one (¬ c k = Q)
        simp only [Bop.apply_mul, Bop.apply_add]; nlinarith)
      unfold eM eqColQ
      rw [e6]
      congr 1
      simp only [Bop.apply_add, Bop.apply_mul, mergeCol]
      by_cases h : c k = Q <;> simp [ind, h])
    (by simp [eM, eqColQ]) ⟨hn, hP, hQ, hc, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    (by omega)
  have hv2 : Vec σ₁ "c2" n (mergeCol c P Q) :=
    ⟨by rw [hl1, hc2], fun i hi => by rw [hg1 i, if_pos ⟨Nat.zero_le _, by omega⟩]; simp⟩
  let Ctx2 : Env → Prop := fun τ => τ.vars "n" = n ∧ Vec τ "c2" n (mergeCol c P Q) ∧
    (∀ z, z ≠ "b" → τ.vars z = σ.vars z) ∧
    (∀ a, a ≠ "c2" → a ≠ "col" → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out
  obtain ⟨σ₂, r₂, ⟨hn2, hc22, hv2', ha2, hi2, ho2⟩, hl2, hg2⟩ := rowFill_run (B := B)
    (n := n) (base := 0) (K := 4) (arr := "col") (ie := .var "b") (e := .get "c2" (.var "b"))
    Ctx2 (mergeCol c P Q) (by omega) (fun τ h => h.1)
    (fun τ x h => ⟨by simp [h.1], h.2.1.of_eq (by simp), fun z hz => by simp [hz, h.2.2.1 z hz],
      fun a h1 h2 => by simp [h.2.2.2.1 a h1 h2], by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2]⟩)
    (fun τ i x h => ⟨by simp [h.1], h.2.1.of_eq (by simp), fun z hz => by simp [h.2.2.1 z hz],
      fun a h1 h2 => by simp [h2, h.2.2.2.1 a h1 h2], by simp [h.2.2.2.2.1],
      by simp [h.2.2.2.2.2]⟩)
    (fun τ k h hb hk => by rw [evalB_var (by rw [hb]; omega), hb]; simp)
    (fun τ k h hb hk => Vec.evalB (B := B) h.2.1 hb hk (by omega) (hfB k hk))
    (by simp)
    ⟨hn1, hv2, hv1, fun a h1 _ => ha1 a h1, hi1, ho1⟩ (by have := hc1.len; omega)
  refine ⟨σ₂, (r₁.seq r₂).mono (by omega), ⟨by rw [hl2, hc1.len], fun i hi => by
      rw [hg2 i, if_pos ⟨Nat.zero_le _, by omega⟩]; simp⟩, hv2', fun a h1 h2 => ha2 a h2 h1, hi2, ho2,
    by rw [hc22.len]⟩

/-! ### A resolve -/

def btwE : Expr :=
  .or (.mul (eqX (.get "col" (.var "a")) (.var "P")) (eqX (.get "col" (.var "b")) (.var "Q")))
    (.mul (eqX (.get "col" (.var "a")) (.var "Q")) (eqX (.get "col" (.var "b")) (.var "P")))

def eR : Expr :=
  .add (.get "S" (rm "a" "b")) (.mul (.var "op") (.mul (.sub (.lit 1) (.get "S" (rm "a" "b")))
    (.mul (.sub (.lit 1) (eqE "a" "b")) btwE)))

def resolveC : Com := .seq (matFill "S2" eR) (matFill "S" (.get "S2" (rm "a" "b")))

/-- The statuses after a resolve. -/
noncomputable def resStat (c : ℕ → ℕ) (st : ℕ → ℕ → ℕ) (op P Q : ℕ) : ℕ → ℕ → ℕ :=
  fun i j => if st i j = 0 ∧ Btw ⟨c, st⟩ P Q i j then op else st i j

theorem resolveC_run {B Λ : ℕ} {σ : Env} {n op P Q : ℕ} {c : ℕ → ℕ} {st : ℕ → ℕ → ℕ}
    (hn : σ.vars "n" = n) (hop : σ.vars "op" = op) (hP : σ.vars "P" = P) (hQ : σ.vars "Q" = Q)
    (hc : Vec σ "col" n c) (hS : Mat σ "S" n st) (hS2 : (σ.arrs "S2").length = n * n)
    (hcΛ : ∀ v < n, c v ≤ Λ) (hsΛ : ∀ u < n, ∀ v < n, st u v ≤ Λ) (hopΛ : op ≤ Λ)
    (hPΛ : P ≤ Λ) (hQΛ : Q ≤ Λ) (hnΛ : n * n + n ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ σ', Run B resolveC σ σ' (n * (n * 120 + 28) + 12) ∧
      Mat σ' "S" n (resStat c st op P Q) ∧
      (∀ z, z ≠ "a" → z ≠ "b" → σ'.vars z = σ.vars z) ∧
      (∀ a, a ≠ "S" → a ≠ "S2" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      (σ'.arrs "S2").length = n * n := by
  let Ctx : Env → Prop := fun τ => τ.vars "n" = n ∧ τ.vars "op" = op ∧ τ.vars "P" = P ∧
    τ.vars "Q" = Q ∧ Vec τ "col" n c ∧ Mat τ "S" n st ∧
    (∀ z, z ≠ "a" → z ≠ "b" → τ.vars z = σ.vars z) ∧
    (∀ a, a ≠ "S2" → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out
  have hfB : ∀ i < n, ∀ j < n, resStat c st op P Q i j < B := by
    intro i hi j hj; unfold resStat; split_ifs <;> [omega; (have := hsΛ i hi j hj; omega)]
  obtain ⟨σ₁, r₁, ⟨hn1, hop1, hP1, hQ1, hc1, hS1, hv1, ha1, hi1, ho1⟩, hM1⟩ := matFill_run
    (B := B) (n := n) (K := 90) (arr := "S2") (e := eR) Ctx (resStat c st op P Q) (by omega)
    (fun τ h => h.1)
    (fun τ x h => ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2.1],
      h.2.2.2.2.1.of_eq (by simp), h.2.2.2.2.2.1.of_eq (by simp),
      fun z h1 h2 => by simp [h1, h.2.2.2.2.2.2.1 z h1 h2], fun a ha => by
        simp [h.2.2.2.2.2.2.2.1 a ha], by simp [h.2.2.2.2.2.2.2.2.1],
        by simp [h.2.2.2.2.2.2.2.2.2]⟩)
    (fun τ x h => ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2.1],
      h.2.2.2.2.1.of_eq (by simp), h.2.2.2.2.2.1.of_eq (by simp),
      fun z h1 h2 => by simp [h2, h.2.2.2.2.2.2.1 z h1 h2], fun a ha => by
        simp [h.2.2.2.2.2.2.2.1 a ha], by simp [h.2.2.2.2.2.2.2.2.1],
        by simp [h.2.2.2.2.2.2.2.2.2]⟩)
    (fun τ i x h => ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2.1],
      h.2.2.2.2.1.of_eq (by simp), h.2.2.2.2.2.1.of_eq (by simp),
      fun z h1 h2 => by simp [h.2.2.2.2.2.2.1 z h1 h2], fun a ha => by
        simp [ha, h.2.2.2.2.2.2.2.1 a ha], by simp [h.2.2.2.2.2.2.2.2.1],
        by simp [h.2.2.2.2.2.2.2.2.2]⟩)
    (fun τ i j h ha hb hi hj => by
      obtain ⟨hn', hop', hP', hQ', hc', hS', -⟩ := h
      have hci := hcΛ i hi
      have hcj := hcΛ j hj
      have hsij := hsΛ i hi j hj
      have hnn : n * n < B := by omega
      have eS := Mat.evalB (B := B) hS' hn' ha hb hi hj hnn (by omega) (by omega)
      have eci := Vec.evalB (B := B) hc' ha hi (by omega) (by omega)
      have ecj := Vec.evalB (B := B) hc' hb hj (by omega) (by omega)
      have vP : (Expr.var "P").evalB B τ = some P := by rw [evalB_var (by omega), hP']
      have vQ : (Expr.var "Q").evalB B τ = some Q := by rw [evalB_var (by omega), hQ']
      have vop : (Expr.var "op").evalB B τ = some op := by rw [evalB_var (by omega), hop']
      have x1 := evalB_eqX (B := B) eci vP (by omega) (by omega) (by omega)
      have x2 := evalB_eqX (B := B) ecj vQ (by omega) (by omega) (by omega)
      have x3 := evalB_eqX (B := B) eci vQ (by omega) (by omega) (by omega)
      have x4 := evalB_eqX (B := B) ecj vP (by omega) (by omega) (by omega)
      have m1 := evalB_bin (op := .mul) x1 x2
        (by rw [Bop.apply_mul, ind_mul_ind]; exact ind_lt_B _ (by omega))
      rw [Bop.apply_mul, ind_mul_ind] at m1
      have m2 := evalB_bin (op := .mul) x3 x4
        (by rw [Bop.apply_mul, ind_mul_ind]; exact ind_lt_B _ (by omega))
      rw [Bop.apply_mul, ind_mul_ind] at m2
      have bt := evalB_bin (op := .or) m1 m2
        (by rw [Bop.apply_or, lor_ind]; exact ind_lt_B _ (by omega))
      rw [Bop.apply_or, lor_ind] at bt
      have e0 := evalB_eqE (B := B) (σ := τ) (x := "a") (y := "b") (by rw [ha]; omega)
        (by rw [hb]; omega) (by omega)
      rw [ha, hb] at e0
      have nd := evalB_bin (op := .sub) (evalB_lit (n := 1) (B := B) (σ := τ) (by omega)) e0
        (by have := ind_le_one (i = j); simp; omega)
      rw [Bop.apply_sub, one_sub_ind] at nd
      have nb := evalB_bin (op := .mul) nd bt
        (by rw [Bop.apply_mul, ind_mul_ind]; exact ind_lt_B _ (by omega))
      rw [Bop.apply_mul, ind_mul_ind] at nb
      have z0 := evalB_bin (op := .sub) (evalB_lit (n := 1) (B := B) (σ := τ) (by omega)) eS
        (by simp; omega)
      rw [Bop.apply_sub, one_sub_eq_ind] at z0
      have zb := evalB_bin (op := .mul) z0 nb
        (by rw [Bop.apply_mul, ind_mul_ind]; exact ind_lt_B _ (by omega))
      rw [Bop.apply_mul, ind_mul_ind] at zb
      set C := st i j = 0 ∧ ¬ i = j ∧ ((c i = P ∧ c j = Q) ∨ (c i = Q ∧ c j = P)) with hCdef
      have ho := evalB_bin (op := .mul) vop zb (by
        have := ind_le_one C; simp only [Bop.apply_mul]; nlinarith)
      have hs := evalB_bin (op := .add) eS ho (by
        have := ind_le_one C; simp only [Bop.apply_mul, Bop.apply_add]; nlinarith)
      have hval : Bop.add.apply (st i j) (Bop.mul.apply op (ind C)) = resStat c st op P Q i j := by
        simp only [Bop.apply_add, Bop.apply_mul, resStat, Btw, ne_eq]
        by_cases hC : C
        · rw [ind, if_pos hC]
          have h2 : st i j = 0 ∧ ¬i = j ∧ (c i = P ∧ c j = Q ∨ c i = Q ∧ c j = P) :=
            ⟨hC.1, hC.2.1, hC.2.2⟩
          simp [h2]
        · rw [ind, if_neg hC]
          have h2 : ¬ (st i j = 0 ∧ ¬i = j ∧ (c i = P ∧ c j = Q ∨ c i = Q ∧ c j = P)) :=
            fun h => hC ⟨h.1, h.2.1, h.2.2⟩
          simp [h2]
      unfold eR btwE
      rw [hs, hval])
    (by simp [eR, btwE]) ⟨hn, hop, hP, hQ, hc, hS, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    hS2
  let Ctx2 : Env → Prop := fun τ => τ.vars "n" = n ∧ Mat τ "S2" n (resStat c st op P Q) ∧
    (∀ z, z ≠ "a" → z ≠ "b" → τ.vars z = σ.vars z) ∧
    (∀ a, a ≠ "S2" → a ≠ "S" → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out
  obtain ⟨σ₂, r₂, ⟨hn2, hM2, hv2, ha2, hi2, ho2⟩, hS'⟩ := matFill_run (B := B) (n := n) (K := 12)
    (arr := "S") (e := .get "S2" (rm "a" "b")) Ctx2 (resStat c st op P Q) (by omega)
    (fun τ h => h.1)
    (fun τ x h => ⟨by simp [h.1], h.2.1.of_eq (by simp),
      fun z h1 h2 => by simp [h1, h.2.2.1 z h1 h2], fun a h1 h2 => by simp [h.2.2.2.1 a h1 h2],
      by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2]⟩)
    (fun τ x h => ⟨by simp [h.1], h.2.1.of_eq (by simp),
      fun z h1 h2 => by simp [h2, h.2.2.1 z h1 h2], fun a h1 h2 => by simp [h.2.2.2.1 a h1 h2],
      by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2]⟩)
    (fun τ i x h => ⟨by simp [h.1], h.2.1.of_eq (by simp),
      fun z h1 h2 => by simp [h.2.2.1 z h1 h2], fun a h1 h2 => by simp [h2, h.2.2.2.1 a h1 h2],
      by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2]⟩)
    (fun τ i j h ha hb hi hj => Mat.evalB (B := B) h.2.1 h.1 ha hb hi hj (by omega) (by omega)
      (hfB i hi j hj))
    (by simp) ⟨hn1, hM1, hv1, fun a h1 _ => ha1 a h1, hi1, ho1⟩ hS1.len
  refine ⟨σ₂, (r₁.seq r₂).mono (by nlinarith), hS', hv2, fun a h1 h2 => ha2 a h2 h1, hi2, ho2,
    hM2.len⟩

/-! ### The loop over the steps -/

def stepBody : Com :=
  .seq (.assign "op" (.get "Y" opIdx)) (.seq (.assign "P" (.get "Y" (.add opIdx (.lit 1))))
    (.seq (.assign "Q" (.get "Y" (.add opIdx (.lit 2))))
      (.ite (.eq (.var "op") (.lit 0)) mergeC resolveC)))

def stepPh : Com := forUp "t" (.var "m") stepBody

theorem simFold_le {n : ℕ} {y : List ℕ} {Λ : ℕ} (hy : ∀ a ∈ y, a ≤ Λ) (k : ℕ) :
    (∀ v, (simFold n y k).col v ≤ Λ) ∧ ∀ u v, (simFold n y k).st u v ≤ Λ := by
  induction k with
  | zero => exact ⟨fun v => getD_le hy _, fun _ _ => Nat.zero_le _⟩
  | succ k ih =>
      rw [simFold_succ]
      unfold simStep
      split_ifs with h0
      · refine ⟨fun v => ?_, ih.2⟩
        dsimp only; split_ifs
        · exact getD_le hy _
        · exact ih.1 v
      · refine ⟨ih.1, fun u v => ?_⟩
        dsimp only; split_ifs
        · exact getD_le hy _
        · exact ih.2 u v

theorem simStep_eq (s : SimSt) (op P Q : ℕ) : simStep s op P Q =
    if op = 0 then ⟨mergeCol s.col P Q, s.st⟩ else ⟨s.col, resStat s.col s.st op P Q⟩ := by
  unfold simStep mergeCol resStat; rfl

set_option maxHeartbeats 1000000 in
theorem stepPh_run {B Λ M : ℕ} {σ : Env} {n : ℕ} {y : List ℕ} (hn : σ.vars "n" = n)
    (hm : σ.vars "m" = M) (hY : σ.arrs "Y" = y)
    (hc : Vec σ "col" n (simInit y).col) (hS : Mat σ "S" n (simInit y).st)
    (hc2 : (σ.arrs "c2").length = n) (hS2 : (σ.arrs "S2").length = n * n)
    (hyΛ : ∀ a ∈ y, a ≤ Λ) (hlen : n + 2 + 3 * M ≤ y.length) (hlΛ : y.length ≤ Λ)
    (hnΛ : n * n + n ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ σ', Run B stepPh σ σ' (M * (n * (n * 120 + 108) + 120) + 6) ∧
      Vec σ' "col" n (simFold n y M).col ∧ Mat σ' "S" n (simFold n y M).st ∧
      (∀ z, z ∉ ["t", "op", "P", "Q", "a", "b"] → σ'.vars z = σ.vars z) ∧
      (∀ a, a ∉ ["col", "c2", "S", "S2"] → σ'.arrs a = σ.arrs a) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have hbnd := simFold_le (n := n) hyΛ
  let I : ℕ → Env → Prop := fun k τ => Vec τ "col" n (simFold n y k).col ∧
    Mat τ "S" n (simFold n y k).st ∧ (τ.arrs "c2").length = n ∧ (τ.arrs "S2").length = n * n ∧
    (∀ z, z ∉ ["t", "op", "P", "Q", "a", "b"] → τ.vars z = σ.vars z) ∧
    (∀ a, a ∉ ["col", "c2", "S", "S2"] → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out
  obtain ⟨σ', hr, ⟨hc', hS', -, -, hv', ha', hi', ho'⟩, -⟩ := forUp_run (B := B) (i := "t")
    (e := .var "m") (body := stepBody) (N := M) (K := n * (n * 120 + 108) + 60) I (σ := σ)
    (by omega)
    (fun k _ τ hI _ => by
      rw [evalB_var (by rw [hI.2.2.2.2.1 "m" (by decide), hm]; omega),
        hI.2.2.2.2.1 "m" (by decide), hm])
    ⟨hc.of_eq (by simp), hS.of_eq (by simp), by simp [hc2], by simp [hS2],
      fun z hz => by simp [show z ≠ "t" from fun e => hz (by simp [e])],
      fun a _ => by simp, by simp, by simp⟩
    (by
      rintro k hk τ ⟨hck, hSk, hc2k, hS2k, hvk, hak, hik, hok⟩ htk
      have hi0 : n + 4 + 3 * k < y.length := by omega
      have hgetd : ∀ (ρ : Env) (d : ℕ), ρ.vars "n" = n → ρ.vars "t" = k → ρ.arrs "Y" = y →
          d < 3 → (Expr.get "Y" (.add opIdx (.lit d))).evalB B ρ =
            some (y.getD (n + 2 + 3 * k + d) 0) := by
        intro ρ d h1 h2 h3 hd
        have hidx := evalB_opIdx (B := B) h1 h2 (by omega)
        have hi := evalB_bin (op := .add) hidx (evalB_lit (n := d) (B := B) (σ := ρ) (by omega))
          (by show n + 2 + 3 * k + d < B; omega)
        simp only [Bop.apply_add] at hi
        exact evalB_get hi (by rw [h3]; exact getY (by omega))
          (by have := getD_le hyΛ (n + 2 + 3 * k + d); omega)
      have hnτ : τ.vars "n" = n := by rw [hvk "n" (by decide), hn]
      have hYτ : τ.arrs "Y" = y := by rw [hak "Y" (by decide), hY]
      have hget0 : (Expr.get "Y" opIdx).evalB B τ = some (y.getD (n + 2 + 3 * k) 0) :=
        evalB_get (evalB_opIdx (B := B) hnτ htk (by omega)) (by rw [hYτ]; exact getY (by omega))
          (by have := getD_le hyΛ (n + 2 + 3 * k); omega)
      obtain ⟨τ1, r1, a1, f1, ar1, i1, o1⟩ := assign_step (B := B) (σ := τ) "op" hget0
      obtain ⟨τ2, r2, a2, f2, ar2, i2, o2⟩ := assign_step (B := B) (σ := τ1) "P"
        (hgetd τ1 1 (by rw [f1 _ (by decide), hnτ]) (by rw [f1 _ (by decide), htk])
          (by rw [ar1, hYτ]) (by omega))
      obtain ⟨τ3, r3, a3, f3, ar3, i3, o3⟩ := assign_step (B := B) (σ := τ2) "Q"
        (hgetd τ2 2 (by rw [f2 _ (by decide), f1 _ (by decide), hnτ])
          (by rw [f2 _ (by decide), f1 _ (by decide), htk]) (by rw [ar2, ar1, hYτ]) (by omega))
      set op := y.getD (n + 2 + 3 * k) 0 with hop
      set P := y.getD (n + 2 + 3 * k + 1) 0 with hP
      set Q := y.getD (n + 2 + 3 * k + 2) 0 with hQ
      have hopΛ : op ≤ Λ := getD_le hyΛ _
      have hPΛ : P ≤ Λ := getD_le hyΛ _
      have hQΛ : Q ≤ Λ := getD_le hyΛ _
      have hn3 : τ3.vars "n" = n := by rw [f3 _ (by decide), f2 _ (by decide), f1 _ (by decide), hnτ]
      have hop3 : τ3.vars "op" = op := by rw [f3 _ (by decide), f2 _ (by decide), a1]
      have hP3 : τ3.vars "P" = P := by rw [f3 _ (by decide), a2]
      have hQ3 : τ3.vars "Q" = Q := a3
      have ha3 : τ3.arrs = τ.arrs := by rw [ar3, ar2, ar1]
      have hfr3 : ∀ z, z ∉ ["t", "op", "P", "Q", "a", "b"] → τ3.vars z = σ.vars z := by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        rw [f3 z hz.2.2.2.1, f2 z hz.2.2.1, f1 z hz.2.1]
        exact hvk z (by simp [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2])
      have hc3 : Vec τ3 "col" n (simFold n y k).col := hck.of_eq (by rw [ha3])
      have hS3 : Mat τ3 "S" n (simFold n y k).st := hSk.of_eq (by rw [ha3])
      have hcond := evalB_condEq' (B := B) (σ := τ3) (e := .var "op") (f := .lit 0)
        (evalB_var (by rw [hop3]; omega)) (evalB_lit (by omega))
      rw [hop3] at hcond
      have hsucc : simFold n y (k + 1) = simStep (simFold n y k) op P Q := by
        rw [simFold_succ]
        have e1 : pAt n y k = P := by simp only [pAt, hP]; congr 1; omega
        have e2 : qAt n y k = Q := by simp only [qAt, hQ]; congr 1; omega
        rw [e1, e2]; rfl
      rw [simStep_eq] at hsucc
      by_cases h0 : op = 0
      · rw [if_pos h0] at hsucc
        obtain ⟨τ4, r4, hc4, hv4, ha4, hi4, ho4, hl4⟩ := mergeC_run (B := B) (Λ := Λ) hn3 hP3 hQ3
          hc3 (by rw [ha3]; exact hc2k) (fun v _ => (hbnd k).1 v) hPΛ hQΛ (by omega) hB
        refine ⟨τ4, (r1.seq (r2.seq (r3.seq (Run.ite_true (by rw [hcond, decide_eq_true h0])
          r4)))).mono (by simp [opIdx]; nlinarith), by rw [hv4 _ (by decide), f3 _ (by decide),
          f2 _ (by decide), f1 _ (by decide), htk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hsucc]; exact hc4.of_eq (by simp)
        · rw [hsucc]; exact (hS3.of_eq (by rw [ha4 "S" (by decide) (by decide)])).of_eq (by simp)
        · simp [hl4]
        · simp [ha4 "S2" (by decide) (by decide), ha3, hS2k]
        · intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
          simp only [vars_setVar, if_neg hz.1]
          rw [hv4 z hz.2.2.2.2.2, hfr3 z (by simp [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1,
            hz.2.2.2.2.1, hz.2.2.2.2.2])]
        · intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
          simp only [arrs_setVar]
          rw [ha4 a ha.1 ha.2.1, ha3, hak a (by simp [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2])]
        · simp [hi4, i3, i2, i1, hik]
        · simp [ho4, o3, o2, o1, hok]
      · rw [if_neg h0] at hsucc
        obtain ⟨τ4, r4, hS4, hv4, ha4, hi4, ho4, hl4⟩ := resolveC_run (B := B) (Λ := Λ) hn3 hop3
          hP3 hQ3 hc3 hS3 (by rw [ha3]; exact hS2k) (fun v _ => (hbnd k).1 v)
          (fun u _ v _ => (hbnd k).2 u v) hopΛ hPΛ hQΛ hnΛ hB
        refine ⟨τ4, (r1.seq (r2.seq (r3.seq (Run.ite_false (by rw [hcond, decide_eq_false h0])
          r4)))).mono (by simp [opIdx]; nlinarith), by rw [hv4 _ (by decide) (by decide),
          f3 _ (by decide), f2 _ (by decide), f1 _ (by decide), htk], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_⟩
        · rw [hsucc]; exact (hc3.of_eq (by rw [ha4 "col" (by decide) (by decide)])).of_eq (by simp)
        · rw [hsucc]; exact hS4.of_eq (by simp)
        · simp [ha4 "c2" (by decide) (by decide), ha3, hc2k]
        · simp [hl4]
        · intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
          simp only [vars_setVar, if_neg hz.1]
          rw [hv4 z hz.2.2.2.2.1 hz.2.2.2.2.2, hfr3 z (by simp [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1,
            hz.2.2.2.2.1, hz.2.2.2.2.2])]
        · intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
          simp only [arrs_setVar]
          rw [ha4 a ha.2.2.1 ha.2.2.2, ha3, hak a (by simp [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2])]
        · simp [hi4, i3, i2, i1, hik]
        · simp [ho4, o3, o2, o1, hok])
  exact ⟨σ', hr.mono (by simp; nlinarith), hc', hS', hv', ha', hi', ho'⟩

end Lax185574Proofs.MainRam
