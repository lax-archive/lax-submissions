import Lax185574Proofs.MC.Glue.Step

/-!
**The glue program of thm:mc.** `glueHyp : GlueHyp`.

The program is the guarded program of `glueCmd eM eR eE d` with
`d = D + 16 - guardBits gLayout`, the input shift is
`sI = guardBits gLayout + 6`, and the constant `cG` of the sentence
covers the cost of round `0`, the constants of the heads and the fixed
words.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile Lax808846.Ram
open Lax808846.RamComputes Lax185574Proofs.RamSim
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees

variable {n : ℕ}

/-- The constant of the sentence. -/
noncomputable def cGA (eM eR eE d : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  r0C (Lax3.FirstOrder.rank φ) + glM (Lax3.FirstOrder.rank φ) + iL (Lax3.FirstOrder.rank φ) +
    treeCst (Lax3.FirstOrder.rank φ) +
    (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length +
    maxEntry (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) +
    Lax3.FirstOrder.rank φ + dK + 2 ^ d + eM + eR + eE + 100

noncomputable def cGof (eM eR eE d : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ := 200000 * cGA eM eR eE d φ

theorem cGA_ge (eM eR eE d : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    r0C (Lax3.FirstOrder.rank φ) + glM (Lax3.FirstOrder.rank φ) + iL (Lax3.FirstOrder.rank φ) + dK +
      2 ^ d + eM + eR + eE + 100 ≤ cGA eM eR eE d φ := by
  unfold cGA; generalize 2 ^ d = p; omega

/-! ### Word sizes -/

theorem ent_conv {v r e : ℕ} (hv : r + 6 ≤ v) (he : e < 2 ^ (v - (r + 6))) :
    64 * (e + 1) ≤ 2 ^ (v - r) - 1 + 1 := by
  have h : 2 ^ (v - r) = 64 * 2 ^ (v - (r + 6)) := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; congr 1; omega
  have : 1 ≤ 2 ^ (v - r) := Nat.one_le_two_pow
  omega

/-- The completeness hypothesis makes the word size large. -/
theorem big_of {v r sQ W cG Base E : ℕ} (hsQ : r + 26 ≤ sQ) (hW1 : W + 1 = 2 ^ (v - r))
    (hE : 1 ≤ E) (hB : 1 ≤ Base) (hcG : 2 ≤ cG) (h : cG * Base ^ E ≤ 2 ^ (v - sQ)) :
    cG * Base ≤ 2 ^ (v - sQ) ∧ 2 ^ (v - sQ) ≤ W / 1024 ∧ sQ < v := by
  have h1 : Base ≤ Base ^ E := by
    calc Base = Base ^ 1 := (pow_one _).symm
      _ ≤ Base ^ E := Nat.pow_le_pow_right hB hE
  have h2 : cG * Base ≤ 2 ^ (v - sQ) := le_trans (Nat.mul_le_mul_left _ h1) h
  have hv : sQ < v := by
    by_contra hc
    rw [show v - sQ = 0 by omega] at h2
    have : 2 ≤ cG * Base := le_trans hcG (Nat.le_mul_of_pos_right _ hB)
    simp at h2; omega
  have hsplit : 2 ^ (v - r) = 2 ^ (sQ - r) * 2 ^ (v - sQ) := by rw [← pow_add]; congr 1; omega
  have h3 : 2 ^ 26 ≤ 2 ^ (sQ - r) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hZ : 1 ≤ 2 ^ (v - sQ) := Nat.one_le_two_pow
  refine ⟨h2, ?_, hv⟩
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have : 2 ^ 26 * 2 ^ (v - sQ) ≤ W + 1 := by rw [hW1, hsplit]; exact Nat.mul_le_mul_right _ h3
  omega

/-! ### The rounds -/

/-- The input word without the graph. -/
def xOf (σ : Script n) (φ : Lax3.FirstOrder.FO 0) : List ℕ := [n] ++ toWord σ ++ toWord φ

/-- The heads. -/
noncomputable def hdS (σ : Script n) (φ : Lax3.FirstOrder.FO 0) : ℕ → List ℕ :=
  hdSeq σ.run (Lax3.FirstOrder.rank φ) (n + 3) σ.steps.length
    (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) (pcalls n σ.steps)

/-- The input of round `j`. -/
noncomputable def pUj (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) : List ℕ :=
  pU (xOf σ φ) σ.run (Lax3.FirstOrder.rank φ) φ (pcalls n σ.steps) (hdS σ φ)
    (finAns σ.run (Lax3.FirstOrder.rank φ) φ) j

/-- The output of round `j`. -/
noncomputable def gOj (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) : List ℕ :=
  glueOut σ.run (Lax3.FirstOrder.rank φ) φ (pcalls n σ.steps) (hdS σ φ)
    (finAns σ.run (Lax3.FirstOrder.rank φ) φ) j

/-- The glue program. -/
noncomputable def gProg (eM eR eE D : ℕ) : Program :=
  guardedProgram gLayout (glueCmd eM eR eE (D + 16 - guardBits gLayout))

/-- The guard of the working callee at word size `W`. -/
def GuardW (eM eR eE d W : ℕ) (u : List ℕ) (k : ℕ) : Prop :=
  min ((u.length + maxEntry u + 1) ^ (expOf eM eR eE k + 1)) W ≤ W / min (2 ^ d) W

theorem guardOK_of_W {eM eR eE D v W : ℕ} {s : List (PartialGraph (Fin n))} {q : ℕ}
    {φ : Lax3.FirstOrder.FO 0} (c : PCall n) (hD : guardBits gLayout + 10 ≤ D)
    (hW1 : W + 1 = 2 ^ (v - guardBits gLayout)) (hW : 2 ≤ W)
    (h : GuardW eM eR eE (D + 16 - guardBits gLayout) W (workQ s q φ c) (ckOf c)) :
    GuardOK s q φ eM eR eE v (D + 16) c :=
  guardOK_workQ c (guard_sound_arith (sQ := D + 16) hW1 (by omega) hW h)

theorem guardW_of {eM eR eE D v W cG Base E : ℕ} {u : List ℕ} {k : ℕ}
    (hD : guardBits gLayout + 10 ≤ D) (hW1 : W + 1 = 2 ^ (v - guardBits gLayout))
    (hE : expOf eM eR eE k + 1 ≤ E) (hcG : 2 ≤ cG)
    (hs : u.length + maxEntry u + 1 ≤ Base) (h : cG * Base ^ E ≤ 2 ^ (v - (D + 16))) :
    GuardW eM eR eE (D + 16 - guardBits gLayout) W u k := by
  refine guard_compl_arith (sQ := D + 16) hW1 (by omega) (by omega) ?_
  have hB : 1 ≤ Base := by omega
  calc 2 * (u.length + maxEntry u + 1) ^ (expOf eM eR eE k + 1)
      ≤ 2 * Base ^ (expOf eM eR eE k + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _)
    _ ≤ 2 * Base ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB hE)
    _ ≤ cG * Base ^ E := Nat.mul_le_mul_right _ hcG
    _ ≤ _ := h

theorem expOf_le (eM eR eE k : ℕ) : expOf eM eR eE k + 1 ≤ eM + eR + eE + 1 := by
  unfold expOf; split_ifs <;> omega

theorem lengths_call0 (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n) :
    (gwOf σ.run σ.steps.length (call0 hn σ.steps)).length = 3 * n + 3 + (1 + n * (n + 1)) ∧
    (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length (call0 hn σ.steps)).length =
      1 + n * (iL (Lax3.FirstOrder.rank φ) + 3) := by
  set q := Lax3.FirstOrder.rank φ
  set c := inCol ([n] ++ toWord σ ++ toWord φ) 1
  have hcol : ∀ k (hk : k < n), σ.colors ⟨k, hk⟩ = c k := fun k hk => (inCol_spec [n] σ _ hk).2
  have hf : fwOf σ.run q σ.steps.length (call0 hn σ.steps) = fw0 n q c := by
    rw [← toWord_family_zero σ q c hcol, fwOf, ctOf_call0]
  refine ⟨?_, by rw [hf, length_fw0]⟩
  rw [gwOf, ctOf_call0, toWord_gd_zero σ c hcol, length_gd0]

theorem length_hdOf (s : List (PartialGraph (Fin n))) (q off m : ℕ) (lw : List ℕ) (c : PCall n) :
    (hdOf s q off m lw c).length = 17 + (gwOf s m c).length + (fwOf s q m c).length + lw.length := by
  simp [hdOf, hdW, stW, scOf]; omega

theorem maxEntry_append_le {a b : List ℕ} : maxEntry b ≤ maxEntry (a ++ b) :=
  maxEntry_le (fun v h => le_maxEntry (List.mem_append_right _ h))

theorem maxEntry_append_le' {a b : List ℕ} : maxEntry a ≤ maxEntry (a ++ b) :=
  maxEntry_le (fun v h => le_maxEntry (List.mem_append_left _ h))

theorem time0_arith {A r0 P O x Lw dk p e : ℕ} (hA : r0 + dk + p + e + 100 ≤ A) (hx : x + 3 = P)
    (hL : Lw ≤ O) :
    10 * (r0 * (x + 1) + 16 * x + 750 * Lw + 700 * dk + 60 * (e + 1) + 30 * p + 30 * dk + 4000) + 5 ≤
      200000 * A * (P + O + 1) := by
  have h1 : r0 * (x + 1) ≤ A * (P + O + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : x + Lw + 1 ≤ P + O + 1 := by omega
  have h3 : A * (x + Lw + 1) ≤ A * (P + O + 1) := Nat.mul_le_mul_left _ h2
  have h4 : 100 * (x + Lw + 1) ≤ A * (x + Lw + 1) := Nat.mul_le_mul_right _ (by omega)
  have h5 : dk + p + e + 1 ≤ A := by omega
  have h6 : A ≤ A * (P + O + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

set_option maxHeartbeats 1000000 in
theorem c4_zero {eM eR eE D : ℕ} (hD : guardBits gLayout + 10 ≤ D) (σ : Script n)
    (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n) {v : ℕ} (hv : guardBits gLayout + 6 ≤ v)
    (hent : ∀ e ∈ pUj σ φ 0, e < 2 ^ (v - (guardBits gLayout + 6))) :
    (∀ o t, RunsTo v (gProg eM eR eE D) (pUj σ φ 0) o t → o = gOj σ φ 0 ∧
      (∀ e ∈ o, e < 2 ^ (v - (guardBits gLayout + 6) - 4)) ∧
      ∀ c, (pcalls n σ.steps)[0]? = some c → GuardOK σ.run (Lax3.FirstOrder.rank φ) φ eM eR eE v (D + 16) c) ∧
    (cGof eM eR eE (D + 16 - guardBits gLayout) φ * (((pUj σ φ 0).length + (gOj σ φ 0).length +
        maxEntry (pUj σ φ 0 ++ gOj σ φ 0) + 1) ^ (eM + eR + eE + 1)) ≤ 2 ^ (v - (D + 16)) →
      ∃ t ≤ cGof eM eR eE (D + 16 - guardBits gLayout) φ * ((pUj σ φ 0).length + (gOj σ φ 0).length + 1),
        RunsTo v (gProg eM eR eE D) (pUj σ φ 0) (gOj σ φ 0) t) := by
  set r := guardBits gLayout with hr
  set d := D + 16 - r with hd
  set q := Lax3.FirstOrder.rank φ with hq
  set W := guardW gLayout v with hWd
  have hW1 : W + 1 = 2 ^ (v - r) := guardW_succ gLayout v
  have hp0 : pUj σ φ 0 = 0 :: (xOf σ φ).length :: (xOf σ φ ++ [0]) := pU_zero _ _ _ _ _ _ _
  have hc0 := pcalls_zero hn σ.steps
  set c0 := call0 hn σ.steps with hc0d
  set lw := Lax185574.DistanceLogic.DistFO.code (loc q φ) with hlw
  set o := hdOf σ.run q (n + 3) σ.steps.length lw c0 ++ callQ σ.run q φ c0 with ho
  have hg0 : gOj σ φ 0 = o := by simp only [gOj, glueOut, hc0, hdS, hdSeq]; rfl
  have hent' : ∀ e ∈ 0 :: (xOf σ φ).length :: (xOf σ φ ++ [0]), 64 * (e + 1) ≤ W + 1 :=
    fun e h => by
      have := ent_conv hv (hent e (by rw [hp0]; exact h))
      rw [hW1]; omega
  have hW63 : 63 ≤ W := by
    have : 2 ^ 6 ≤ 2 ^ (v - r) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨σ', k, hrun, hk, -, hS, hC⟩ := glue0_run (W := W) (eM := eM) (eR := eR) (eE := eE) (d := d)
    σ φ hW63 hent'
  obtain ⟨hl1, hl2⟩ := lengths_call0 σ φ hn
  have key := step_clause (glueCmd_ok eM eR eE d) (u := pUj σ φ 0) (o := o) (v := v) (W := W)
    (K := glue0C eM eR eE d q (xOf σ φ).length (3 * n + 3 + (1 + n * (n + 1)) + (1 + n * (iL q + 3)) +
      lw.length))
    (P := GuardW eM eR eE d W (workQ σ.run q φ c0) (ckOf c0))
    (C := dK < W / 8 ∧ glM q < W / 8 ∧ n * (glM q + 3 + n) < W / 8 ∧
      dK + (3 * n + 3 + (1 + n * (n + 1))) + (1 + n * (iL q + 3)) + lw.length < W / 8 ∧
      maxEntry o < W / 32 / 32 ∧
      GuardW eM eR eE d W (workQ σ.run q φ c0) (ckOf c0))
    hWd hv (by rw [hp0]; exact hent')
    ⟨σ', k, by rw [hp0]; exact hrun, hk, hS hn, fun h => hC hn h.1 h.2.1 h.2.2.1 h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2⟩
  obtain ⟨hsound, hcomp⟩ := key
  refine ⟨fun o' t h => ?_, fun hcond => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hsound o' t h
    refine ⟨by rw [h1, hg0], by rw [h1]; exact h2, fun c hc => ?_⟩
    rw [hc0] at hc; cases hc
    exact guardOK_of_W c0 hD hW1 (by omega) h3
  · rw [hg0] at hcond ⊢
    obtain ⟨P, hP⟩ : ∃ P, (pUj σ φ 0).length = P := ⟨_, rfl⟩
    have hPx : P = (xOf σ φ).length + 3 := by rw [← hP, hp0]; simp
    obtain ⟨A, hA⟩ : ∃ A, cGA eM eR eE d φ = A := ⟨_, rfl⟩
    have hAge : r0C q + glM q + iL q + dK + 2 ^ d + eM + eR + eE + 100 ≤ A :=
      hA ▸ cGA_ge eM eR eE d φ
    have hAf : 100 ≤ A ∧ dK + 1 ≤ A ∧ glM q + 3 ≤ A ∧ r0C q + dK + 2 ^ d + (eM + eR + eE) + 100 ≤ A := by
      clear * - hAge; generalize 2 ^ d = p at *; omega
    clear hAge
    have hcG : cGof eM eR eE d φ = 200000 * A := by rw [← hA]; rfl
    obtain ⟨Base, hBase⟩ : ∃ Base, P + o.length + maxEntry (pUj σ φ 0 ++ o) + 1 = Base := ⟨_, rfl⟩
    rw [hP, hBase] at hcond
    rw [hP]
    have hcG2 : 2 ≤ cGof eM eR eE d φ := by rw [hcG]; omega
    obtain ⟨hb1, hb2, -⟩ := big_of (r := r) (sQ := D + 16) (W := W) (cG := cGof eM eR eE d φ)
      (Base := Base) (E := eM + eR + eE + 1) (by omega) hW1 (by omega) (by omega) hcG2 (by
        rw [← hBase] at hcond ⊢; exact hcond)
    have hB1 : 1 ≤ Base := by omega
    have hcB : cGof eM eR eE d φ ≤ cGof eM eR eE d φ * Base := Nat.le_mul_of_pos_right _ hB1
    have hBc : Base ≤ cGof eM eR eE d φ * Base := Nat.le_mul_of_pos_left _ (by omega)
    have hW8 : W / 1024 < W / 8 := by omega
    have h32 : W / 32 / 32 = W / 1024 := by rw [Nat.div_div_eq_div_mul]
    have hlo : (hdOf σ.run q (n + 3) σ.steps.length lw c0).length ≤ o.length := by simp [ho]
    rw [length_hdOf, hl1, hl2] at hlo
    have hmo : maxEntry o ≤ maxEntry (pUj σ φ 0 ++ o) := maxEntry_append_le
    have hnx : n ≤ (xOf σ φ).length := by rw [xOf, length_x]; omega
    have eq4 : n * (iL q + 3) = n * (iL (Lax3.FirstOrder.rank φ) + 3) := rfl
    have eq5 : lw.length = (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length :=
      rfl
    obtain ⟨hw1, hw2⟩ := workQ_sub σ.run q φ c0
    have hwo : (workQ σ.run q φ c0).length ≤ o.length := le_trans hw1 (by simp [ho])
    have hwm : maxEntry (workQ σ.run q φ c0) ≤ maxEntry o :=
      maxEntry_le (fun v h => le_maxEntry (List.mem_append_right _ (hw2 v h)))
    have hng0 : n * (glM q + 3) ≤ Base * A := Nat.mul_le_mul (by omega) (by omega)
    have hnn1 : n * (n + 1) = n * n + n := by ring
    have hnF : n * (glM q + 3 + n) = n * (glM q + 3) + n * n := by ring
    have hcAB : cGof eM eR eE d φ * Base = 200000 * (Base * A) := by rw [hcG]; ring
    have hAB : Base ≤ Base * A := Nat.le_mul_of_pos_right _ (by omega)
    have hng : n * (glM q + 3 + n) ≤ cGof eM eR eE d φ * Base := by omega
    obtain ⟨t, ht, hR⟩ := hcomp ⟨by omega, by omega, by omega, by omega, by omega,
      guardW_of hD hW1 (expOf_le _ _ _ _) hcG2 (by omega) hcond⟩
    refine ⟨t, le_trans ht ?_, hR⟩
    unfold glue0C
    rw [hcG]
    exact time0_arith (r0 := r0C q) (dk := dK) (p := 2 ^ d) (e := eM + eR + eE) hAf.2.2.2 hPx.symm
      (by omega)

theorem timeJ_arith {A P O L dk p e : ℕ} (hA : dk + p + e + 100 ≤ A) (hL : L ≤ 2 * P) :
    10 * (30 * dk + 50 + (500 * L + 2000 + (900 * (2 * L) + 900 * dk + 60 * (e + 1) + 30 * p + 4000))) +
      5 ≤ 200000 * A * (P + O + 1) := by
  have h3 : A * (L + 1) ≤ A * (2 * (P + O + 1)) := Nat.mul_le_mul_left _ (by omega)
  have h4 : 100 * (L + 1) ≤ A * (L + 1) := Nat.mul_le_mul_right _ (by omega)
  have h6 : A ≤ A * (P + O + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

theorem gw_len (σ : Script n) (c : PCall n) : n + 1 ≤ (gwOf σ.run σ.steps.length c).length := by
  show n + 1 ≤ (toWord (sAt σ.run (ctOf σ.steps.length c)) ++ _).length
  rw [toWord_pg]; simp

theorem inJ_len (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) :
    (stOf σ φ c).length + (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length + n ≤ 2 * (inJ σ φ c).length := by
  have h1 : (stOf σ φ c).length = 14 + (gwOf σ.run σ.steps.length c).length +
      (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length +
      (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length := by
    rw [stOf, length_stW, length_scOf]
  have h2 := gw_len σ c
  simp only [inJ, List.length_cons, List.length_append]
  omega

set_option maxHeartbeats 1000000 in
theorem c4_succ {eM eR eE D : ℕ} (hD : guardBits gLayout + 10 ≤ D) (σ : Script n)
    (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n) {i : ℕ} (hi : i < (pcalls n σ.steps).length) {v : ℕ}
    (hv : guardBits gLayout + 6 ≤ v)
    (hent : ∀ e ∈ pUj σ φ (i + 1), e < 2 ^ (v - (guardBits gLayout + 6))) :
    (∀ o t, RunsTo v (gProg eM eR eE D) (pUj σ φ (i + 1)) o t → o = gOj σ φ (i + 1) ∧
      (∀ e ∈ o, e < 2 ^ (v - (guardBits gLayout + 6) - 4)) ∧
      ∀ c, (pcalls n σ.steps)[i + 1]? = some c →
        GuardOK σ.run (Lax3.FirstOrder.rank φ) φ eM eR eE v (D + 16) c) ∧
    (cGof eM eR eE (D + 16 - guardBits gLayout) φ * (((pUj σ φ (i + 1)).length +
        (gOj σ φ (i + 1)).length + maxEntry (pUj σ φ (i + 1) ++ gOj σ φ (i + 1)) + 1) ^
          (eM + eR + eE + 1)) ≤ 2 ^ (v - (D + 16)) →
      ∃ t ≤ cGof eM eR eE (D + 16 - guardBits gLayout) φ * ((pUj σ φ (i + 1)).length +
        (gOj σ φ (i + 1)).length + 1),
        RunsTo v (gProg eM eR eE D) (pUj σ φ (i + 1)) (gOj σ φ (i + 1)) t) := by
  set r := guardBits gLayout with hr
  set d := D + 16 - r with hd
  set q := Lax3.FirstOrder.rank φ with hq
  set W := guardW gLayout v with hWd
  have hW1 : W + 1 = 2 ^ (v - r) := guardW_succ gLayout v
  obtain ⟨c, hc⟩ : ∃ c, (pcalls n σ.steps)[i]? = some c :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  have hval : Valid σ.steps c := pcalls_valid σ.steps (List.mem_of_getElem? hc)
  have hnext := pcalls_succ hn σ.steps hc
  have hval' : ∀ c', nextCall hn σ.steps c = some c' → Valid σ.steps c' := fun c' h =>
    pcalls_valid σ.steps (List.mem_of_getElem? (hnext.trans h))
  have hp : pUj σ φ (i + 1) = inJ σ φ c := pU_succ σ φ _ hc
  have hent' : ∀ e ∈ inJ σ φ c, 64 * (e + 1) ≤ W + 1 := fun e h => by
    have := ent_conv hv (hent e (by rw [hp]; exact h))
    rw [hW1]; omega
  have hW63 : 63 ≤ W := by
    have : 2 ^ 6 ≤ 2 ^ (v - r) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨σ', k, hrun, hk, hS, hE⟩ := glueJ_run (W := W) (eM := eM) (eR := eR) (eE := eE) (d := d)
    σ φ hn c hval hval' hW63 hent'
  set lw := Lax185574.DistanceLogic.DistFO.code (loc q φ) with hlw
  obtain ⟨A, hA⟩ : ∃ A, cGA eM eR eE d φ = A := ⟨_, rfl⟩
  have hAge : r0C q + glM q + iL q + dK + 2 ^ d + eM + eR + eE + 100 ≤ A :=
    hA ▸ cGA_ge eM eR eE d φ
  have hAf : 100 ≤ A ∧ dK + 1 ≤ A ∧ dK + 2 ^ d + (eM + eR + eE) + 100 ≤ A := by
    clear * - hAge; generalize 2 ^ d = p at *; omega
  clear hAge
  have hcG : cGof eM eR eE d φ = 200000 * A := by rw [← hA]; rfl
  have hcG2 : 2 ≤ cGof eM eR eE d φ := by rw [hcG]; omega
  have hW8 : ∀ Z, 1 ≤ Z → Z ≤ W / 1024 → W / 1024 < W / 8 := fun Z h1 h2 => by omega
  have h32 : W / 32 / 32 = W / 1024 := by rw [Nat.div_div_eq_div_mul]
  have hLj := inJ_len σ φ c
  have eqb : (callY σ.run q φ c).length = (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length := rfl
  cases hcn : nextCall hn σ.steps c with
  | some c' =>
    set o := hdOf σ.run q (n + 3) σ.steps.length lw c' ++ callQ σ.run q φ c' with ho
    have hg : gOj σ φ (i + 1) = o := by
      simp only [gOj, glueOut, hnext, hcn, hdS, hdSeq]; rfl
    obtain ⟨hS1, hS2⟩ := hS c' hcn
    have key := step_clause (glueCmd_ok eM eR eE d) (u := pUj σ φ (i + 1)) (o := o) (v := v) (W := W)
      (K := 30 * dK + 50 + roundJC eM eR eE d ((stOf σ φ c).length + (callY σ.run q φ c).length + n))
      (P := GuardW eM eR eE d W (workQ σ.run q φ c') (ckOf c'))
      (C := dK < W / 8 ∧ dK + (gwOf σ.run σ.steps.length c').length +
        (fwOf σ.run q σ.steps.length c').length + lw.length < W / 8 ∧ maxEntry o < W / 32 / 32 ∧
        GuardW eM eR eE d W (workQ σ.run q φ c') (ckOf c'))
      hWd hv (by rw [hp]; exact hent')
      ⟨σ', k, by rw [hp]; exact hrun, hk, hS1, fun h => hS2 h.1 h.2.1 h.2.2.1 h.2.2.2⟩
    obtain ⟨hsound, hcomp⟩ := key
    refine ⟨fun o' t h => ?_, fun hcond => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hsound o' t h
      refine ⟨by rw [h1, hg], by rw [h1]; exact h2, fun c'' hc'' => ?_⟩
      rw [hnext, hcn] at hc''; cases hc''
      exact guardOK_of_W c' hD hW1 (by omega) h3
    · rw [hg] at hcond ⊢
      obtain ⟨P, hP⟩ : ∃ P, (pUj σ φ (i + 1)).length = P := ⟨_, rfl⟩
      obtain ⟨Base, hBase⟩ : ∃ Base, P + o.length + maxEntry (pUj σ φ (i + 1) ++ o) + 1 = Base :=
        ⟨_, rfl⟩
      rw [hP, hBase] at hcond
      rw [hP]
      obtain ⟨hb1, hb2, -⟩ := big_of (r := r) (sQ := D + 16) (W := W) (cG := cGof eM eR eE d φ)
        (Base := Base) (E := eM + eR + eE + 1) (by omega) hW1 (by omega) (by omega) hcG2 hcond
      have hB1 : 1 ≤ Base := by omega
      have hcB : cGof eM eR eE d φ ≤ cGof eM eR eE d φ * Base := Nat.le_mul_of_pos_right _ hB1
      have hBc : Base ≤ cGof eM eR eE d φ * Base := Nat.le_mul_of_pos_left _ (by omega)
      have hlo : (hdOf σ.run q (n + 3) σ.steps.length lw c').length ≤ o.length := by simp [ho]
      rw [length_hdOf] at hlo
      have hmo : maxEntry o ≤ maxEntry (pUj σ φ (i + 1) ++ o) := maxEntry_append_le
      obtain ⟨hw1, hw2⟩ := workQ_sub σ.run q φ c'
      have hwo : (workQ σ.run q φ c').length ≤ o.length := le_trans hw1 (by simp [ho])
      have hwm : maxEntry (workQ σ.run q φ c') ≤ maxEntry o :=
        maxEntry_le (fun v h => le_maxEntry (List.mem_append_right _ (hw2 v h)))
      have hW8' := hW8 Base hB1 (by omega)
      obtain ⟨t, ht, hR⟩ := hcomp ⟨by omega, by omega, by omega,
        guardW_of hD hW1 (expOf_le _ _ _ _) hcG2 (by omega) hcond⟩
      refine ⟨t, le_trans ht ?_, hR⟩
      rw [hcG]
      unfold roundJC issueC
      have hPl : (inJ σ φ c).length = P := by rw [← hp]; exact hP
      exact timeJ_arith (dk := dK) (p := 2 ^ d) (e := eM + eR + eE) hAf.2.2 (by omega)
  | none =>
    set o := 0 :: finAns σ.run q φ with ho
    have hg : gOj σ φ (i + 1) = o := by
      simp only [gOj, glueOut, hnext, hcn]; rfl
    obtain ⟨hE1, hE2⟩ := hE hcn
    have key := step_clause (glueCmd_ok eM eR eE d) (u := pUj σ φ (i + 1)) (o := o) (v := v) (W := W)
      (K := 30 * dK + 50 + roundJC eM eR eE d ((stOf σ φ c).length + (callY σ.run q φ c).length + n))
      (P := True) (C := dK < W / 8 ∧ maxEntry o < W / 32 / 32)
      hWd hv (by rw [hp]; exact hent')
      ⟨σ', k, by rw [hp]; exact hrun, hk, fun h => ⟨(hE1 h).1, (hE1 h).2, trivial⟩,
        fun h => hE2 h.1 h.2⟩
    obtain ⟨hsound, hcomp⟩ := key
    refine ⟨fun o' t h => ?_, fun hcond => ?_⟩
    · obtain ⟨h1, h2, -⟩ := hsound o' t h
      refine ⟨by rw [h1, hg], by rw [h1]; exact h2, fun c'' hc'' => ?_⟩
      rw [hnext, hcn] at hc''; cases hc''
    · rw [hg] at hcond ⊢
      obtain ⟨P, hP⟩ : ∃ P, (pUj σ φ (i + 1)).length = P := ⟨_, rfl⟩
      obtain ⟨Base, hBase⟩ : ∃ Base, P + o.length + maxEntry (pUj σ φ (i + 1) ++ o) + 1 = Base :=
        ⟨_, rfl⟩
      rw [hP, hBase] at hcond
      rw [hP]
      obtain ⟨hb1, hb2, -⟩ := big_of (r := r) (sQ := D + 16) (W := W) (cG := cGof eM eR eE d φ)
        (Base := Base) (E := eM + eR + eE + 1) (by omega) hW1 (by omega) (by omega) hcG2 hcond
      have hB1 : 1 ≤ Base := by omega
      have hcB : cGof eM eR eE d φ ≤ cGof eM eR eE d φ * Base := Nat.le_mul_of_pos_right _ hB1
      have hBc : Base ≤ cGof eM eR eE d φ * Base := Nat.le_mul_of_pos_left _ (by omega)
      have hmo : maxEntry o ≤ maxEntry (pUj σ φ (i + 1) ++ o) := maxEntry_append_le
      have hW8' := hW8 Base hB1 (by omega)
      obtain ⟨t, ht, hR⟩ := hcomp ⟨by omega, by omega⟩
      refine ⟨t, le_trans ht ?_, hR⟩
      rw [hcG]
      unfold roundJC issueC
      have hPl : (inJ σ φ c).length = P := by rw [← hp]; exact hP
      exact timeJ_arith (dk := dK) (p := 2 ^ d) (e := eM + eR + eE) hAf.2.2 (by omega)

/-! ### The heads -/

theorem head_arith {X Mx M n T tc Lw ml q K H E : ℕ} (hM : M ≤ Mx)
    (hK : 3 * tc + 3 * Lw + ml + q + 100 ≤ K)
    (hH : H ≤ 17 + (6 * (n + 1) ^ 2 + (1 + n * (T + tc))) + Lw)
    (hE : E ≤ X + M + 2 * (6 * (n + 1) ^ 2 + (1 + n * (T + tc))) + 2 * Lw + ml + q + 40) :
    H + E ≤ K * (X + Mx + n * T + (n + 1) ^ 2) := by
  have h1 : n * tc ≤ tc * (n + 1) ^ 2 := by
    have : n ≤ (n + 1) ^ 2 := by nlinarith
    calc n * tc ≤ (n + 1) ^ 2 * tc := Nat.mul_le_mul_right _ this
      _ = tc * (n + 1) ^ 2 := Nat.mul_comm _ _
  have h2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : (3 * tc + 3 * Lw + ml + q + 100) * (n + 1) ^ 2 ≤ K * (n + 1) ^ 2 :=
    Nat.mul_le_mul_right _ hK
  have h4 : 3 * (X + Mx + n * T) ≤ K * (X + Mx + n * T) := Nat.mul_le_mul_right _ (by omega)
  have h5 : K * (X + Mx + n * T) + K * (n + 1) ^ 2 = K * (X + Mx + n * T + (n + 1) ^ 2) := by ring
  have h6 : n * (T + tc) = n * T + n * tc := by ring
  nlinarith

theorem head_arith' {n T tc Lw K H k : ℕ} (hK : 3 * tc + 3 * Lw + 100 ≤ K)
    (hH : H ≤ 17 + (6 * (n + 1) ^ 2 + (1 + n * (T + tc))) + Lw) (hk : k ≤ 3) :
    H + k ≤ K * (n * T + (n + 1) ^ 2) := by
  have h1 : n * tc ≤ tc * (n + 1) ^ 2 := by
    have : n ≤ (n + 1) ^ 2 := by nlinarith
    calc n * tc ≤ (n + 1) ^ 2 * tc := Nat.mul_le_mul_right _ this
      _ = tc * (n + 1) ^ 2 := Nat.mul_comm _ _
  have h2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : (3 * tc + 3 * Lw + 100) * (n + 1) ^ 2 ≤ K * (n + 1) ^ 2 := Nat.mul_le_mul_right _ hK
  have h4 : n * T ≤ K * (n * T) := Nat.le_mul_of_pos_left _ (by omega)
  have h6 : n * (T + tc) = n * T + n * tc := by ring
  nlinarith

theorem cGA_ge' (eM eR eE d : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    3 * treeCst (Lax3.FirstOrder.rank φ) +
      3 * (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length +
      maxEntry (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) +
      Lax3.FirstOrder.rank φ + 100 ≤ cGof eM eR eE d φ := by
  unfold cGof cGA; generalize 2 ^ d = p; omega

theorem hd_get (σ : Script n) (φ : Lax3.FirstOrder.FO 0) {j : ℕ} (hj : j < (pcalls n σ.steps).length) :
    ∃ c, (pcalls n σ.steps)[j]? = some c ∧ Valid σ.steps c ∧
      hdS σ φ j = hdOf σ.run (Lax3.FirstOrder.rank φ) (n + 3) σ.steps.length
        (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) c := by
  have h := List.getElem?_eq_getElem hj
  refine ⟨_, h, pcalls_valid σ.steps (List.getElem_mem hj), ?_⟩
  simp only [hdS, hdSeq, h]

/-! ### The glue program -/

set_option maxHeartbeats 1000000 in
theorem glueAt_of {eM eR eE D : ℕ} (hD : guardBits gLayout + 10 ≤ D) (φ : Lax3.FirstOrder.FO 0)
    (σ : Script n) :
    GlueAt (gProg eM eR eE D) (guardBits gLayout + 6) (D + 16) eM eR eE
      (cGof eM eR eE (D + 16 - guardBits gLayout) φ) φ ([n] ++ toWord σ ++ toWord φ) σ.run σ.steps := by
  constructor
  · intro hn0 v o t hv hent hR
    set W := guardW gLayout v with hWd
    have hW1 : W + 1 = 2 ^ (v - guardBits gLayout) := guardW_succ gLayout v
    have hp0 : lpU ([n] ++ toWord σ ++ toWord φ) (lpA0 ([n] ++ toWord σ ++ toWord φ)) [] =
        0 :: ([n] ++ toWord σ ++ toWord φ).length :: (([n] ++ toWord σ ++ toWord φ) ++ [0]) :=
      pU_zero ([n] ++ toWord σ ++ toWord φ) σ.run (Lax3.FirstOrder.rank φ) φ (pcalls n σ.steps)
        (hdS σ φ) []
    have hent' : ∀ e ∈ 0 :: ([n] ++ toWord σ ++ toWord φ).length :: (([n] ++ toWord σ ++ toWord φ) ++ [0]),
        64 * (e + 1) ≤ W + 1 := fun e h => by
      have := ent_conv hv (hent e (by rw [hp0]; exact h)); rw [hW1]; omega
    have hW63 : 63 ≤ W := by
      have : 2 ^ 6 ≤ 2 ^ (v - guardBits gLayout) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨σ', k, hrun, -, hz, -, -⟩ := glue0_run (W := W) (eM := eM) (eR := eR) (eE := eE)
      (d := D + 16 - guardBits gLayout) σ φ hW63 hent'
    rw [hp0] at hR
    obtain ⟨hsound, -⟩ := guarded_sound (glueCmd_ok eM eR eE _) (by simp [gLayout]) (by simp [gLayout])
      (w := v) (by omega) (fun e h => by have := hent' e h; rw [← hWd]; omega) (by rw [← hWd]; exact hrun)
    exact hz hn0 (hsound o t hR).1
  · intro hn1
    have hn : 0 < n := by omega
    refine ⟨hdS σ φ, fun j hj => hdSeq_shape _ _ _ _ _ _ _ hj, fun j hj => ?_, fun j hj => ?_,
      fun j hj v hv hent => ?_⟩
    · obtain ⟨c, -, hval, he⟩ := hd_get σ φ hj
      rw [he]
      obtain ⟨h1, h2⟩ := hd_bounds σ φ hval
      exact head_arith (toWord_le_x σ φ) (cGA_ge' _ _ _ _ φ) h1 (maxEntry_le h2)
    · obtain ⟨c, -, hval, he⟩ := hd_get σ φ hj
      rw [he]
      obtain ⟨h1, -⟩ := hd_bounds σ φ hval
      have hk : (hdOf σ.run (Lax3.FirstOrder.rank φ) (n + 3) σ.steps.length
          (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) c).getD 2 0 ≤ 3 := by
        simp only [hdOf, hdW]; show kOf σ.steps.length c ≤ 3; unfold kOf; split_ifs <;> omega
      have := cGA_ge' eM eR eE (D + 16 - guardBits gLayout) φ
      exact head_arith' (by omega) h1 hk
    · cases j with
      | zero => exact c4_zero hD σ φ hn hv hent
      | succ i => exact c4_succ hD σ φ hn (by omega) hv hent

/-- **The glue program of thm:mc.** -/
theorem glueHyp : GlueHyp :=
  ⟨guardBits gLayout + 6, fun eM eR eE D hD => ⟨gProg eM eR eE D, fun φ =>
    ⟨cGof eM eR eE (D + 16 - guardBits gLayout) φ, fun n σ => glueAt_of (by omega) φ σ⟩⟩⟩

end Lax185574Proofs.MC.Glue
