import Lax185574Proofs.StpRam.EmitLoop

/-!
The loops of the final round of lem:compute-stp: counting the triples,
and writing them.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax185574Proofs.Words

/-- The step of the counting loop. -/
def countInner : Com :=
  .seq (.assign "gu" (.get "ord" (.var "es")))
    (.seq (.assign "gi" (.sub (.get "a" (.get "st" (.var "gu"))) (.var "kk")))
      (.ite (.lt (.get "rt" (.var "gi")) (.var "gr")) .skip
        (.assign "tot" (.add (.var "tot") (.lit 1)))))

/-- **A step of the counting loop.** -/
theorem countInner_run {B n nsE nsN k q R1 L : ℕ} {oE tE oN tN g : ℕ → ℕ} {A : List (List ℕ)}
    (hF : AFacts A n k q L) (hb : WordsBound B A) (hR1 : R1 = radius k q 1)
    (hRB : R1 + 1 < B) {σ : Env} (hC : ECtx A n nsE nsN oE tE oN tN g k q R1 σ) {s r t : ℕ}
    (hs : σ.vars "es" = s) (hsl : s < (sortedDistinct A).length) (hr : σ.vars "gr" = r)
    (hr1 : 1 ≤ r) (hrR : r ≤ R1) (ht : σ.vars "tot" = t) (htB : t + 1 < B) :
    ∃ σ', Run B countInner σ σ' 20 ∧
      ECtx A n nsE nsN oE tE oN tN g k q R1 σ' ∧ σ'.vars "es" = s ∧ σ'.vars "gr" = r ∧
      σ'.vars "tot" = t + (if r ≤ radius k q ((sortedDistinct A)[s].headD 0 - k) then 1 else 0) := by
  obtain ⟨hG, hw, hkk, hcap, hR, hcnt, hord, hrt, hdm, hdn, hbl, hol⟩ := hC
  have hlen := hb.len
  set SD := sortedDistinct A with hSD
  have hSDA : SD.length ≤ A.length := length_sortedDistinct_le A
  obtain ⟨hoA, hwo⟩ := hord s hsl
  set ui := (σ.arrs "ord").getD s 0 with hui
  have hu : A[ui] = SD[s] := by rw [← wd_eq hoA, hwo, List.getD_eq_getElem _ _ hsl]
  have huA : A[ui] ∈ A := List.getElem_mem hoA
  obtain ⟨hk1, hkq⟩ := hF.head _ huA
  have hne := hF.ne _ huA
  obtain ⟨x, xs, hxs⟩ : ∃ x xs, A[ui] = x :: xs := List.exists_cons_of_ne_nil hne
  have hhead : A[ui].headD 0 = x := by rw [hxs]; rfl
  set lev := x - k with hlev
  have hlev1 : 1 ≤ lev := by omega
  have hlevq : lev ≤ q := by omega
  have hrad : radius k q lev ≤ R1 := by rw [hR1]; exact radius_le_one k q lev hlev1 hlevq
  have hxB : x < B := hb.ent _ huA x (by rw [hxs]; simp)
  -- the two assignments
  set τ1 := σ.setVar "gu" ui with hτ1
  have hords : (σ.arrs "ord")[s]? = some ui := by
    rw [hui, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  have r1 : Run B (.assign "gu" (.get "ord" (.var "es"))) σ τ1 3 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff]
    exact ⟨s, ⟨hs.symm, by omega⟩, hords, by omega⟩
  set τ2 := τ1.setVar "gi" lev with hτ2
  have hent0 : (σ.arrs "a")[off A ui]? = some x := by
    have := hw.a ui hoA 0 (by rw [hxs]; simp)
    rw [Nat.add_zero] at this
    rw [this]; simp [hxs]
  have r2 : Run B (.assign "gi" (.sub (.get "a" (.get "st" (.var "gu"))) (.var "kk"))) τ1 τ2 6 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff]
    refine ⟨x, k, ⟨off A ui, ⟨ui, ⟨by simp [hτ1], by simp [hτ1]; omega⟩, by
        simp only [hτ1, arrs_setVar]; exact hw.st ui hoA, by have := off_add_le hoA; omega⟩,
        by simp only [hτ1, arrs_setVar]; exact hent0, hxB⟩,
      ⟨by simp [hτ1, hkk], by simp [hτ1, hkk]; omega⟩, by simp [Bop.apply, hlev], by omega⟩
  have hrtv : (τ2.arrs "rt")[lev]? = some (radius k q lev) := by
    simp only [hτ2, hτ1, arrs_setVar, hrt]; exact getElem?_arrOf _ (by omega)
  have hgr2 : τ2.vars "gr" = r := by simp [hτ2, hτ1, hr]
  have he1 : (Expr.get "rt" (.var "gi")).evalB B τ2 = some (radius k q lev) := by
    simp only [evalB_get_iff, evalB_var_iff]
    exact ⟨lev, ⟨by simp [hτ2], by simp [hτ2]; omega⟩, hrtv, by omega⟩
  have he2 : (Expr.var "gr").evalB B τ2 = some r := by
    simp only [evalB_var_iff]; exact ⟨hgr2.symm, by rw [hgr2]; omega⟩
  have hcond := evalB_condLt he1 he2
  have hlevS : SD[s].headD 0 - k = lev := by rw [← hu, hhead]
  have hC2 : ECtx A n nsE nsN oE tE oN tN g k q R1 τ2 :=
    ECtx.of_eq (τ := σ) ⟨hG, hw, hkk, hcap, hR, hcnt, hord, hrt, hdm, hdn, hbl, hol⟩
      (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [hτ2, hτ1])
      (fun x hx => by simp [hτ2, hτ1])
      (fun x hx => by simp [hτ2, hτ1])
  have hsize : (Cond.lt (.get "rt" (.var "gi")) (.var "gr")).size = 4 := rfl
  have ht2 : τ2.vars "tot" = t := by simp [hτ2, hτ1, ht]
  by_cases hlt : radius k q lev < r
  · refine ⟨τ2, (Run.seq r1 (Run.seq r2 (Run.ite_true (by rw [hcond]; simp [hlt]) Run.skip))).mono ?_,
      hC2, by simp [hτ2, hτ1, hs], by simp [hτ2, hτ1, hr], ?_⟩
    · simp only [hsize]; omega
    · rw [hlevS, if_neg (by omega), ht2]; rfl
  · refine ⟨τ2.setVar "tot" (t + 1), (Run.seq r1 (Run.seq r2 (Run.ite_false (by rw [hcond]; simp [hlt])
      (Run.assign (v := t + 1) ?_)))).mono ?_, ?_, by simp [hτ2, hτ1, hs], by simp [hτ2, hτ1, hr], ?_⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨t, 1, ⟨ht2.symm, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
    · simp only [hsize, Expr.size]; omega
    · exact ECtx.of_eq hC2 (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)
        (fun x hx => by simp) (fun x hx => by simp)
    · rw [hlevS, if_pos (by omega)]; simp

/-! ### The loops -/

theorem length_emitRk_le {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q r s : ℕ) :
    (emitRk adj A k q r s).length ≤ (emitR adj A k q r).length := by
  simp only [emitRk, emitR, List.length_map]
  exact ((List.take_sublist s _).filter _).length_le

theorem length_emitR_le {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q r : ℕ) :
    (emitR adj A k q r).length ≤ (sortedDistinct A).length := by
  simp only [emitR, List.length_map]
  exact List.length_filter_le _ _

theorem length_emitPre_le {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q : ℕ) :
    ∀ j, (emitPre adj A k q j).length ≤ j * (sortedDistinct A).length
  | 0 => by simp [emitPre]
  | j + 1 => by
    rw [emitPre_succ, List.length_append, Nat.add_mul, one_mul]
    have := length_emitPre_le adj A k q j
    have := length_emitR_le adj A k q (j + 1)
    omega

def countLoop : Com := forUp "es" (.var "cnt") countInner

def countLoops : Com :=
  .seq (.assign "tot" (.lit 0))
    (forUp "er" (.var "R1") (.seq (.assign "gr" (.add (.var "er") (.lit 1))) countLoop))

def emitInner : Com := forUp "es" (.var "cnt") innerBody

def emitLoops : Com :=
  forUp "er" (.var "R1") (.seq (.assign "gr" (.add (.var "er") (.lit 1))) emitInner)

/-- **Counting the triples.** -/
theorem countLoops_run {B n nsE nsN k q R1 L : ℕ} {oE tE oN tN g : ℕ → ℕ} {A : List (List ℕ)}
    {adj : Fin n → List (Fin n)}
    (hF : AFacts A n k q L) (hb : WordsBound B A) (hR1 : R1 = radius k q 1)
    (hRB : R1 + 1 < B) (hTB : R1 * A.length + 1 < B) {σ : Env}
    (hC : ECtx A n nsE nsN oE tE oN tN g k q R1 σ) :
    ∃ σ', Run B countLoops σ σ' (R1 * (A.length * 28 + 20) + 10) ∧
      ECtx A n nsE nsN oE tE oN tN g k q R1 σ' ∧
      σ'.vars "tot" = (emitPre adj A k q R1).length := by
  have hSDA : (sortedDistinct A).length ≤ A.length := length_sortedDistinct_le A
  have hlen := hb.len
  set N := (sortedDistinct A).length with hN
  -- the inner loop for the radius `r`
  have hinner : ∀ (r : ℕ) (τ : Env), 1 ≤ r → r ≤ R1 → ECtx A n nsE nsN oE tE oN tN g k q R1 τ →
      τ.vars "gr" = r → τ.vars "tot" = (emitPre adj A k q (r - 1)).length →
      ∃ τ', Run B countLoop τ τ' (N * 28 + 6) ∧ ECtx A n nsE nsN oE tE oN tN g k q R1 τ' ∧
        τ'.vars "gr" = r ∧ τ'.vars "tot" = (emitPre adj A k q r).length := by
    intro r τ hr1 hrR hCτ hgr htot
    have hpre : ∀ s ≤ N, (emitPre adj A k q (r - 1)).length + (emitRk adj A k q r s).length ≤
        R1 * A.length := by
      intro s hs
      have h1 := length_emitPre_le adj A k q (r - 1)
      have h2 := length_emitRk_le adj A k q r s
      have h3 := length_emitR_le adj A k q r
      rw [← hN] at h1 h3
      have h4 : (r - 1) * N + N ≤ R1 * A.length := by
        have : (r - 1) * N + N = r * N := by
          obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
          simp [Nat.add_mul]
        rw [this]; exact Nat.mul_le_mul hrR hSDA
      omega
    obtain ⟨τ', hr', ⟨hC', hgr', htot'⟩, -⟩ := forUp_run (B := B) (i := "es") (e := .var "cnt")
      (body := countInner) (N := N) (K := 20)
      (fun s τ => ECtx A n nsE nsN oE tE oN tN g k q R1 τ ∧ τ.vars "gr" = r ∧
        τ.vars "tot" = (emitPre adj A k q (r - 1)).length + (emitRk adj A k q r s).length)
      (σ := τ) (by omega)
      (fun s _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.1.2.2.2.2.2.1.symm, by
        rw [hI.1.2.2.2.2.2.1]; omega⟩)
      ⟨hCτ.of_eq (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)
        (fun x hx => by simp) (fun x hx => by simp), by simp [hgr], by simp [htot, emitRk]⟩
      (by
        rintro s hs τ1 ⟨hC1, hgr1, htot1⟩ hes
        have hb1 := hpre (s + 1) (by omega)
        rw [emitRk_succ adj A k q r s hs] at hb1
        obtain ⟨τ2, r2, hC2, hes2, hgr2, htot2⟩ := countInner_run hF hb hR1 hRB hC1 hes hs hgr1 hr1 hrR
          htot1 (by have := hpre s (by omega); omega)
        refine ⟨τ2, r2, hes2, hC2.of_eq (fun x hx => by
          simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp) (fun x hx => by simp)
          (fun x hx => by simp), by simp [hgr2], ?_⟩
        simp only [vars_setVar, show ("tot" : String) = "es" ↔ False by decide, if_false, htot2,
          emitRk_succ adj A k q r s hs]
        split_ifs <;> simp <;> omega)
    refine ⟨τ', hr'.mono (by simp), hC', hgr', ?_⟩
    rw [htot', emitRk_full]
    conv_rhs => rw [show r = (r - 1) + 1 by omega, emitPre_succ]
    rw [List.length_append, show r - 1 + 1 = r by omega]
  obtain ⟨σ', hr', ⟨hC', htot'⟩, -⟩ := forUp_run (B := B) (i := "er") (e := .var "R1")
    (body := .seq (.assign "gr" (.add (.var "er") (.lit 1))) countLoop) (N := R1) (K := N * 28 + 10)
    (fun j τ => ECtx A n nsE nsN oE tE oN tN g k q R1 τ ∧ τ.vars "tot" = (emitPre adj A k q j).length)
    (σ := σ.setVar "tot" 0) (by omega)
    (fun j _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.1.2.2.2.2.1.symm, by
      rw [hI.1.2.2.2.2.1]; omega⟩)
    ⟨ECtx.of_eq (τ' := (σ.setVar "tot" 0).setVar "er" 0) hC
        (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)
        (fun x hx => by simp) (fun x hx => by simp), by simp [emitPre]⟩
    (by
      rintro j hj τ ⟨hCτ, htot⟩ her
      set τ1 := τ.setVar "gr" (j + 1) with hτ1
      have r1 : Run B (.assign "gr" (.add (.var "er") (.lit 1))) τ τ1 4 := by
        refine (Run.assign ?_).mono (by simp)
        simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨j, 1, ⟨her.symm, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
      obtain ⟨τ2, r2, hC2, hgr2, htot2⟩ := hinner (j + 1) τ1 (by omega) (by omega)
        (hCτ.of_eq (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [hτ1])
          (fun x hx => by simp [hτ1]) (fun x hx => by simp [hτ1])) (by simp [hτ1])
        (by simp [hτ1, htot])
      refine ⟨τ2, (Run.seq r1 r2).mono (by omega), ?_, ?_, ?_⟩
      · rw [r2.frame_var "er" (by decide)]; simp [hτ1, her]
      · exact hC2.of_eq (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)
          (fun x hx => by simp) (fun x hx => by simp)
      · simp [htot2])
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hr').mono ?_, hC', htot'⟩
  simp only [Expr.size]
  have : N * 28 ≤ A.length * 28 := Nat.mul_le_mul_right _ hSDA
  have := Nat.mul_le_mul_left R1 (show N * 28 + 10 + 1 + 7 ≤ A.length * 28 + 20 by omega)
  nlinarith

/-- **Writing the triples.** -/
theorem emitLoops_run {B n nsE nsN k q R1 L : ℕ} {oE tE oN tN g : ℕ → ℕ} {A : List (List ℕ)}
    {adj : Fin n → List (Fin n)} (hD : ∀ (s v : Fin n) (r : ℕ), DT g n s v r ↔ v ∈ Lax185574Proofs.TreeAlgo.ballFrom adj s r)
    (hF : AFacts A n k q L) (hb : WordsBound B A) (hR1 : R1 = radius k q 1)
    (hnB : n + 2 < B) (hnnB : n * n < B) (hgB : ∀ j < n * n, g j < B) (hRB : R1 + 1 < B)
    (hcB : k + q + 1 < B)
    (htB : total A + 3 < B) {σ : Env} (hC : ECtx A n nsE nsN oE tE oN tN g k q R1 σ) :
    ∃ σ', Run B emitLoops σ σ'
        (R1 * (A.length * (innerCost n L (k + q) + 8) + 18) + 6) ∧
      ECtx A n nsE nsN oE tE oN tN g k q R1 σ' ∧
      σ'.out = σ.out ++ frames (emitPre adj A k q R1) := by
  have hSDA : (sortedDistinct A).length ≤ A.length := length_sortedDistinct_le A
  have hlen := hb.len
  set N := (sortedDistinct A).length with hN
  set KI := innerCost n L (k + q) with hKI
  have hinner : ∀ (r : ℕ) (τ : Env), 1 ≤ r → r ≤ R1 → ECtx A n nsE nsN oE tE oN tN g k q R1 τ →
      τ.vars "gr" = r →
      ∃ τ', Run B emitInner τ τ' (N * (KI + 8) + 6) ∧ ECtx A n nsE nsN oE tE oN tN g k q R1 τ' ∧
        τ'.vars "gr" = r ∧ τ'.out = τ.out ++ frames (emitR adj A k q r) := by
    intro r τ hr1 hrR hCτ hgr
    obtain ⟨τ', hr', ⟨hC', hgr', hout'⟩, -⟩ := forUp_run (B := B) (i := "es") (e := .var "cnt")
      (body := innerBody) (N := N) (K := KI)
      (fun s ρ => ECtx A n nsE nsN oE tE oN tN g k q R1 ρ ∧ ρ.vars "gr" = r ∧
        ρ.out = τ.out ++ frames (emitRk adj A k q r s))
      (σ := τ) (by omega)
      (fun s _ ρ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.1.2.2.2.2.2.1.symm, by
        rw [hI.1.2.2.2.2.2.1]; omega⟩)
      ⟨hCτ.of_eq (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)
        (fun x hx => by simp) (fun x hx => by simp), by simp [hgr], by simp [emitRk, frames]⟩
      (by
        rintro s hs ρ1 ⟨hC1, hgr1, hout1⟩ hes
        obtain ⟨ρ2, r2, hC2, hes2, hgr2, hout2⟩ := innerBody_run hD hF hb hR1 hnB hnnB hgB hRB hcB
          htB hC1 hes hs hgr1 hr1 hrR
        refine ⟨ρ2, r2, hes2, hC2.of_eq (fun x hx => by
          simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp) (fun x hx => by simp)
          (fun x hx => by simp), by simp [hgr2], ?_⟩
        simp only [out_setVar, hout2, hout1, emitRk_succ adj A k q r s hs, frames_append',
          List.append_assoc])
    refine ⟨τ', hr'.mono (by simp), hC', hgr', ?_⟩
    rw [hout', emitRk_full]
  obtain ⟨σ', hr', ⟨hC', hout'⟩, -⟩ := forUp_run (B := B) (i := "er") (e := .var "R1")
    (body := .seq (.assign "gr" (.add (.var "er") (.lit 1))) emitInner) (N := R1)
    (K := N * (KI + 8) + 10)
    (fun j τ => ECtx A n nsE nsN oE tE oN tN g k q R1 τ ∧ τ.out = σ.out ++ frames (emitPre adj A k q j))
    (σ := σ) (by omega)
    (fun j _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.1.2.2.2.2.1.symm, by
      rw [hI.1.2.2.2.2.1]; omega⟩)
    ⟨ECtx.of_eq (τ' := σ.setVar "er" 0) hC
        (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)
        (fun x hx => by simp) (fun x hx => by simp), by simp [emitPre, frames]⟩
    (by
      rintro j hj τ ⟨hCτ, hout⟩ her
      set τ1 := τ.setVar "gr" (j + 1) with hτ1
      have r1 : Run B (.assign "gr" (.add (.var "er") (.lit 1))) τ τ1 4 := by
        refine (Run.assign ?_).mono (by simp)
        simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨j, 1, ⟨her.symm, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
      obtain ⟨τ2, r2, hC2, hgr2, hout2⟩ := hinner (j + 1) τ1 (by omega) (by omega)
        (hCτ.of_eq (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [hτ1])
          (fun x hx => by simp [hτ1]) (fun x hx => by simp [hτ1])) (by simp [hτ1])
      refine ⟨τ2, (Run.seq r1 r2).mono (by omega), ?_, ?_, ?_⟩
      · rw [r2.frame_var "er" (by decide)]; simp [hτ1, her]
      · exact hC2.of_eq (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)
          (fun x hx => by simp) (fun x hx => by simp)
      · simp only [out_setVar, hout2, hτ1, hout, emitPre_succ, frames_append', List.append_assoc])
  refine ⟨σ', hr'.mono ?_, hC', hout'⟩
  simp only [Expr.size]
  have : N * (KI + 8) ≤ A.length * (KI + 8) := Nat.mul_le_mul_right _ hSDA
  have := Nat.mul_le_mul_left R1 (show N * (KI + 8) + 10 + 1 + 7 ≤ A.length * (KI + 8) + 18 by omega)
  omega

end Lax185574Proofs.StpRam
