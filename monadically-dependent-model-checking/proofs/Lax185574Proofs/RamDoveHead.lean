import Lax185574Proofs.RamDoveSteps

/-!
The head of a slot of the dovetailer: find the thread, check it, and
load its record.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.Ruler

variable {w K B : ℕ} {Q : Program} {x : List ℕ}

/-- The halving loop: from `q` with `r` halvings done, reach the exit of
the loop with `r + ruler q` halvings, changing only the cells 9, 21
and 22. -/
theorem dv_halve (G : DGlob w K B Q x) :
    ∀ (n q r : ℕ) (S : State), ruler q = n → q ≠ 0 → q * 2 ^ r < 2 ^ w → S.pc = dvL0 + 3 →
      S.mem 22 = q → S.mem 21 = r → S.mem 29 = 2 → S.mem rOne = 1 → WordMem w S.mem →
      ∃ S', Exec w (dvProg Q B K) (7 * n + 5) S S' ∧ S'.pc = dvL0 + 11 ∧
        S'.mem 21 = r + n ∧ (∀ a, a ≠ rT → a ≠ 21 → a ≠ 22 → S'.mem a = S.mem a) ∧
        S'.input = S.input ∧ S'.inp = S.inp ∧ S'.out = S.out := by
  have hw := G.hw
  have hf := dv_fits_head Q B K
  intro n
  induction n with
  | zero =>
      intro q r S hq hq0 hqr hpc h22 h21 h29 h1 hm
      have hodd : q % 2 = 1 := by
        by_contra h
        rw [ruler_even hq0 (by omega)] at hq; omega
      obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_div (w := w) (s := S)
        (fetch hf (i := 3) (by simp [hpc]) rfl) hm (by omega) (by omega) (by omega)).upd
      obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_mul (w := w) (s := S1)
        (fetch hf (i := 4) (by simp [hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
      obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_sub (w := w) (s := S2)
        (fetch hf (i := 5) (by simp [hpc2, hpc1, hpc]) rfl) (hm.exec (e1.trans e2)) (by omega)
        (by omega) (by omega)).upd
      have hqw : q < 2 ^ w := by have := hm 22; rwa [h22] at this
      have a2 : S2.mem rT = q / 2 * 2 := by
        rw [hm2, if_pos rfl, hm1, if_pos rfl, hm1, if_neg (by decide), h22, h29,
          Nat.mod_eq_of_lt (by omega)]
      have hT3 : S3.mem rT = 1 := by
        rw [hm3, if_pos rfl, a2, hm2, if_neg (by decide), hm1, if_neg (by decide), h22]; omega
      have e4 := (x_jzero_neg (w := w) (s := S3) (fetch hf (i := 6) (by simp [hpc3, hpc2, hpc1, hpc])
        rfl) (by omega) (by rw [hT3]; omega)).trans
        (x_jump (fetch hf (i := 7) (by simp [hpc3, hpc2, hpc1, hpc]) rfl))
      refine ⟨_, (((e1.trans e2).trans e3).trans e4).cast (by omega), rfl, ?_, ?_, ?_⟩
      · show S3.mem 21 = _
        rw [hm3, if_neg (by decide), hm2, if_neg (by decide), hm1, if_neg (by decide), h21,
          Nat.add_zero]
      · intro a h1 h2 h3
        show S3.mem a = _
        rw [hm3, if_neg h1, hm2, if_neg h1, hm1, if_neg h1]
      · exact ⟨by rw [hi3, hi2, hi1], by rw [hn3, hn2, hn1], by rw [ho3, ho2, ho1]⟩
  | succ n ih =>
      intro q r S hq hq0 hqr hpc h22 h21 h29 h1 hm
      have heven : q % 2 = 0 := by
        by_contra h
        rw [ruler_odd (by omega)] at hq; omega
      have hq' : ruler (q / 2) = n := by rw [ruler_even hq0 heven] at hq; omega
      have hqw : q < 2 ^ w := by have := hm 22; rwa [h22] at this
      obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_div (w := w) (s := S)
        (fetch hf (i := 3) (by simp [hpc]) rfl) hm (by omega) (by omega) (by omega)).upd
      obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_mul (w := w) (s := S1)
        (fetch hf (i := 4) (by simp [hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
      obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_sub (w := w) (s := S2)
        (fetch hf (i := 5) (by simp [hpc2, hpc1, hpc]) rfl) (hm.exec (e1.trans e2)) (by omega)
        (by omega) (by omega)).upd
      have a2 : S2.mem rT = q / 2 * 2 := by
        rw [hm2, if_pos rfl, hm1, if_pos rfl, hm1, if_neg (by decide), h22, h29,
          Nat.mod_eq_of_lt (by omega)]
      have hT3 : S3.mem rT = 0 := by
        rw [hm3, if_pos rfl, a2, hm2, if_neg (by decide), hm1, if_neg (by decide), h22]; omega
      have e4 := x_jzero_pos (w := w) (s := S3) (fetch hf (i := 6) (by simp [hpc3, hpc2, hpc1, hpc])
        rfl) (by omega) hT3
      have hm3w := hm.exec ((e1.trans e2).trans e3)
      obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_div (w := w)
        (s := { S3 with pc := dvL0 + 8 }) (fetch hf (i := 8) (by simp) rfl) hm3w (by omega)
        (by omega) (by omega)).upd
      obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_add (w := w) (s := S5)
        (fetch hf (i := 9) (by simp [hpc5]) rfl) (by omega) (by omega) (by omega)).upd
      have e7 := x_jump (w := w) (s := S6) (fetch hf (i := 10) (by simp [hpc6, hpc5]) rfl)
      have hS3 : ∀ a, a ≠ rT → S3.mem a = S.mem a := fun a h => by
        rw [hm3, if_neg h, hm2, if_neg h, hm1, if_neg h]
      have h22' : S6.mem 22 = q / 2 := by
        rw [hm6, if_neg (by decide), hm5, if_pos rfl]
        show (S3.mem 22 / S3.mem 29) = _
        rw [hS3 _ (by decide), hS3 _ (by decide), h22, h29]
      have h21' : S6.mem 21 = r + 1 := by
        rw [hm6, if_pos rfl, hm5, if_neg (by decide), hm5, if_neg (by decide)]
        show (S3.mem 21 + S3.mem 1) % 2 ^ w = _
        rw [hS3 _ (by decide), hS3 _ (by decide), h21, h1, Nat.mod_eq_of_lt]
        have h2r : 2 ^ (r + 1) < 2 ^ w := by
          rw [pow_succ]
          have : 2 ≤ q := by omega
          calc 2 ^ r * 2 ≤ 2 ^ r * q := Nat.mul_le_mul_left _ this
            _ = q * 2 ^ r := by ring
            _ < 2 ^ w := hqr
        have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2r
        have := Nat.lt_two_pow_self (n := w)
        omega
      have hqr' : q / 2 * 2 ^ (r + 1) < 2 ^ w := by
        rw [pow_succ, show q / 2 * (2 ^ r * 2) = (q / 2 * 2) * 2 ^ r by ring,
          Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)]; exact hqr
      obtain ⟨S', e', hpc', h21'', hfr', hi', hn', ho'⟩ := ih (q / 2) (r + 1)
        { S6 with pc := dvL0 + 3 } hq' (by omega) hqr' rfl h22' h21'
        (by show S6.mem 29 = 2; rw [hm6, if_neg (by decide), hm5, if_neg (by decide),
          hS3 _ (by decide), h29])
        (by show S6.mem 1 = 1; rw [hm6, if_neg (by decide), hm5, if_neg (by decide),
          hS3 _ (by decide), h1])
        (show WordMem w S6.mem from (WordMem.exec (s := { S3 with pc := dvL0 + 8 }) hm3w e5).exec e6)
      refine ⟨S', (((((e1.trans e2).trans e3).trans e4).trans ((e5.trans e6).trans e7)).trans
        e').cast (by ring), hpc', by rw [h21'']; ring, fun a h1 h2 h3 => ?_, ?_, ?_, ?_⟩
      · rw [hfr' a h1 h2 h3]
        show S6.mem a = _
        rw [hm6, if_neg h2, hm5, if_neg h3, hS3 a h1]
      · rw [hi']; show S6.input = _; rw [hi6, hi5, hi3, hi2, hi1]
      · rw [hn']; show S6.inp = _; rw [hn6, hn5, hn3, hn2, hn1]
      · rw [ho']; show S6.out = _; rw [ho6, ho5, ho3, ho2, ho1]

/-- Load the record of a live thread. -/
theorem dv_load (G : DGlob w K B Q x) {j I c : ℕ} {s S : State} (hpc : S.pc = dvL0 + 21)
    (C : DConst w K B x S) (hslot : S.mem 20 = j % 2 ^ w) (hj : 1 ≤ j) (hIj : ruler j = I)
    (hI : I + K < w) (h21 : S.mem 21 = I) (h23 : S.mem 23 = 2 ^ (K + I))
    (h24 : S.mem 24 = dvCtx B I) (hcnt : count I j = c) (hS : Saved w K B x I S s)
    (hothers : ∀ i, i + K < w → i ≠ I → TInv w K B Q x i (count i j) S) :
    ∃ S', Exec w (dvProg Q B K) 15 S S' ∧ S'.pc = dvDisp ∧ Running w K B Q x j I c s S' ∧
      S'.mem rD = s.pc := by
  have hw := G.hw
  have hc := dvCtx_le G hI
  have hR : dvR B = B + 5 := rfl
  have hK2 : 2 ≤ K := by have := G.k2; omega
  have hb := dvBase_bounds hK2 hI
  have room := G.room
  have hf := dv_fits_head Q B K
  have hm := C.word
  have hpow : 2 ^ (w - K - I) ≤ 2 ^ (w - K) := two_pow_le_two_pow_of_le (by omega)
  have hpowK : 2 ^ (w - K) * 2 ≤ 2 ^ (w - 1) := by
    rw [← pow_succ]; exact two_pow_le_two_pow_of_le (by omega)
  have hhalf : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have hp1 : 1 ≤ 2 ^ (w - K - I) := Nat.one_le_two_pow
  obtain ⟨S1, e1, hpc1, hm1, -, -, ho1⟩ := (x_div (w := w) (s := S)
    (fetch hf (i := 21) (by simp [hpc]) rfl) hm (by omega) (by omega) (by omega)).upd
  have v1 : S1.mem rMask = 2 ^ (w - K - I) - 1 := by
    rw [hm1, if_pos rfl, C.wm, h23, two_pow_sub_one_div_two_pow (by omega)]
    congr 2; omega
  obtain ⟨S2, e2, hpc2, hm2, -, -, ho2⟩ := (x_add (w := w) (s := S1)
    (fetch hf (i := 22) (by simp [hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
  have v2 : S2.mem rU = 2 ^ (w - K - I) := by
    rw [hm2, if_pos rfl, v1, hm1, if_neg (by decide), C.one, Nat.sub_add_cancel hp1,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨S3, e3, hpc3, hm3, -, -, ho3⟩ := (x_sub (w := w) (s := S2)
    (fetch hf (i := 23) (by simp [hpc2, hpc1, hpc]) rfl) (hm.exec (e1.trans e2)) (by omega)
    (by omega) (by omega)).upd
  have v3 : S3.mem rT = 2 ^ (w - K) - 2 ^ (w - K - I) := by
    rw [hm3, if_pos rfl, v2, hm2, if_neg (by decide), hm1, if_neg (by decide), C.size0]
  obtain ⟨S4, e4, hpc4, hm4, -, -, ho4⟩ := (x_add (w := w) (s := S3)
    (fetch hf (i := 24) (by simp [hpc3, hpc2, hpc1, hpc]) rfl) (by omega) (by omega)
    (by omega)).upd
  have v4 : S4.mem rT = 2 * (2 ^ (w - K) - 2 ^ (w - K - I)) := by
    rw [hm4, if_pos rfl, v3, Nat.mod_eq_of_lt (by omega)]; ring
  obtain ⟨S5, e5, hpc5, hm5, -, -, ho5⟩ := (x_add (w := w) (s := S4)
    (fetch hf (i := 25) (by simp [hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega) (by omega)
    (by omega)).upd
  have v5 : S5.mem rBase = dvBase w K I := by
    rw [hm5, if_pos rfl, v4, hm4, if_neg (by decide), hm3, if_neg (by decide), hm2,
      if_neg (by decide), hm1, if_neg (by decide), C.half, Nat.mod_eq_of_lt (by
        simp only [dvBase] at hb; omega)]; rfl
  -- cells 2, 3 are final; the rest only touches 4, 6, 7, 9, 13, 17
  have f5 : ∀ a, a ≠ rMask → a ≠ rBase → a ≠ rT → a ≠ rU → S5.mem a = S.mem a := by
    intro a h1 h2 h3 h4
    rw [hm5, if_neg h2, hm4, if_neg h3, hm3, if_neg h3, hm2, if_neg h4, hm1, if_neg h1]
  have hW5 := hm.exec ((((e1.trans e2).trans e3).trans e4).trans e5)
  have h24' : S5.mem 24 = dvCtx B I := by rw [f5 _ (by decide) (by decide) (by decide) (by decide), h24]
  obtain ⟨S6, e6, hpc6, hm6, -, -, ho6⟩ := (x_set (w := w) (s := S5)
    (fetch hf (i := 26) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega)).upd
  obtain ⟨S7, e7, hpc7, hm7, -, -, ho7⟩ := (x_add (w := w) (s := S6)
    (fetch hf (i := 27) (by simp [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega)
    (by omega) (by omega)).upd
  have v7 : S7.mem rT = dvCtx B I + 1 := by
    rw [hm7, if_pos rfl, hm6, if_pos rfl, hm6, if_neg (by decide), h24',
      Nat.mod_eq_of_lt (show 1 < 2 ^ w by omega), Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨S8, e8, hpc8, hm8, -, -, ho8⟩ := (x_load (w := w) (s := S7)
    (fetch hf (i := 28) (by simp [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl)
    ((hW5.exec e6).exec e7) (by omega) (by omega)).upd
  have f8 : ∀ a, a ≠ rT → a ≠ rCur → S8.mem a = S5.mem a := by
    intro a h1 h2; rw [hm8, if_neg h2, hm7, if_neg h1, hm6, if_neg h1]
  have v8 : S8.mem rCur = S.mem (dvCtx B I + 1) := by
    rw [hm8, if_pos rfl, v7, hm7, if_neg (by simp only [dvCtx]; omega), hm6,
      if_neg (by simp only [dvCtx]; omega), f5 _ (by simp only [dvCtx]; omega)
      (by simp only [dvCtx]; omega) (by simp only [dvCtx]; omega) (by simp only [dvCtx]; omega)]
  have hW8 := ((hW5.exec e6).exec e7).exec e8
  obtain ⟨S9, e9, hpc9, hm9, -, -, ho9⟩ := (x_set (w := w) (s := S8)
    (fetch hf (i := 29) (by simp [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl)
    (by omega)).upd
  obtain ⟨S10, e10, hpc10, hm10, -, -, ho10⟩ := (x_add (w := w) (s := S9)
    (fetch hf (i := 30) (by simp [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl)
    (by omega) (by omega) (by omega)).upd
  have v10 : S10.mem rT = dvCtx B I + 2 := by
    rw [hm10, if_pos rfl, hm9, if_pos rfl, hm9, if_neg (by decide), f8 _ (by decide) (by decide),
      h24', Nat.mod_eq_of_lt (show 2 < 2 ^ w by omega), Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨S11, e11, hpc11, hm11, -, -, ho11⟩ := (x_load (w := w) (s := S10)
    (fetch hf (i := 31) (by simp [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1,
      hpc]) rfl) ((hW8.exec e9).exec e10) (by omega) (by omega)).upd
  have f11 : ∀ a, a ≠ rT → a ≠ rOC → S11.mem a = S8.mem a := by
    intro a h1 h2; rw [hm11, if_neg h2, hm10, if_neg h1, hm9, if_neg h1]
  have v11 : S11.mem rOC = S.mem (dvCtx B I + 2) := by
    rw [hm11, if_pos rfl, v10, hm10, if_neg (by simp only [dvCtx]; omega), hm9,
      if_neg (by simp only [dvCtx]; omega), f8 _ (by simp only [dvCtx]; omega)
      (by simp only [dvCtx]; omega), f5 _ (by simp only [dvCtx]; omega)
      (by simp only [dvCtx]; omega) (by simp only [dvCtx]; omega) (by simp only [dvCtx]; omega)]
  have hW11 := ((hW8.exec e9).exec e10).exec e11
  obtain ⟨S12, e12, hpc12, hm12, -, -, ho12⟩ := (x_set (w := w) (s := S11)
    (fetch hf (i := 32) (by simp [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2,
      hpc1, hpc]) rfl) (by omega)).upd
  obtain ⟨S13, e13, hpc13, hm13, -, -, ho13⟩ := (x_add (w := w) (s := S12)
    (fetch hf (i := 33) (by simp [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3,
      hpc2, hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S14, e14, hpc14, hm14, -, -, ho14⟩ := (x_add (w := w) (s := S13)
    (fetch hf (i := 34) (by simp [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4,
      hpc3, hpc2, hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S15, e15, hpc15, hm15, hi15, hn15, ho15⟩ := (x_load (w := w) (s := S14)
    (fetch hf (i := 35) (by simp [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5,
      hpc4, hpc3, hpc2, hpc1, hpc]) rfl)
    (((hW11.exec e12).exec e13).exec e14) (by omega) (by omega)).upd
  have f15 : ∀ a, a ≠ rD → a ≠ 17 → a ≠ rOB → a ≠ rT → S15.mem a = S11.mem a := by
    intro a h1 h2 h3 h4
    rw [hm15, if_neg h1, hm14, if_neg h2, hm13, if_neg h3, hm12, if_neg h4]
  -- everything outside the loaded cells is unchanged
  have fAll : ∀ a, a ≠ rMask → a ≠ rBase → a ≠ rCur → a ≠ rOB → a ≠ rOC → a ≠ rT → a ≠ rD →
      a ≠ rU → a ≠ 17 → S15.mem a = S.mem a := by
    intro a h2 h3 h4 h6 h7 h9 h13 h14 h17
    rw [f15 a h13 h17 h6 h9, f11 a h9 h7, f8 a h9 h4, f5 a h2 h3 h9 h14]
  have hctx := fun (a : ℕ) (ha : 40 ≤ a) => fAll a (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have w2 : S15.mem rMask = 2 ^ (w - K - I) - 1 := by
    rw [f15 _ (by decide) (by decide) (by decide) (by decide), f11 _ (by decide) (by decide),
      f8 _ (by decide) (by decide), hm5, if_neg (by decide), hm4, if_neg (by decide), hm3,
      if_neg (by decide), hm2, if_neg (by decide), v1]
  have w3 : S15.mem rBase = dvBase w K I := by
    rw [f15 _ (by decide) (by decide) (by decide) (by decide), f11 _ (by decide) (by decide),
      f8 _ (by decide) (by decide), v5]
  have w4 : S15.mem rCur = S.mem (dvCtx B I + 1) := by
    rw [f15 _ (by decide) (by decide) (by decide) (by decide), f11 _ (by decide) (by decide), v8]
  have w7 : S15.mem rOC = S.mem (dvCtx B I + 2) := by
    rw [f15 _ (by decide) (by decide) (by decide) (by decide), v11]
  have a11 : S11.mem 24 = dvCtx B I := by
    rw [f11 _ (by decide) (by decide), f8 _ (by decide) (by decide), h24']
  have a12 : S12.mem 24 = dvCtx B I := by rw [hm12, if_neg (by decide), a11]
  have b12 : S12.mem rT = 4 := by
    rw [hm12, if_pos rfl, Nat.mod_eq_of_lt (show 4 < 2 ^ w by omega)]
  have w6 : S15.mem rOB = dvCtx B I + 4 := by
    rw [hm15, if_neg (by decide), hm14, if_neg (by decide), hm13, if_pos rfl, a12, b12,
      Nat.mod_eq_of_lt (by omega)]
  have f14 : ∀ a, a ≠ 17 → a ≠ rOB → a ≠ rT → S14.mem a = S11.mem a := by
    intro a h1 h2 h3
    rw [hm14, if_neg h1, hm13, if_neg h2, hm12, if_neg h3]
  have g14 : ∀ a, 40 ≤ a → S14.mem a = S.mem a := by
    intro a ha
    rw [f14 a (by omega) (by omega) (by omega), f11 a (by omega) (by omega),
      f8 a (by omega) (by omega), f5 a (by omega) (by omega) (by omega) (by omega)]
  have w17 : S15.mem 17 = I := by
    rw [hm15, if_neg (by decide), hm14, if_pos rfl, hm13, if_neg (by decide), hm13,
      if_neg (by decide), hm12, if_neg (by decide), hm12, if_neg (by decide),
      f11 _ (by decide) (by decide), f11 _ (by decide) (by decide), f8 _ (by decide) (by decide),
      f8 _ (by decide) (by decide), f5 _ (by decide) (by decide) (by decide) (by decide),
      f5 _ (by decide) (by decide) (by decide) (by decide), h21, C.zero, Nat.add_zero,
      Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := w); omega)]
  have a14 : S14.mem 24 = dvCtx B I := by
    rw [f14 _ (by decide) (by decide) (by decide), a11]
  have w13 : S15.mem rD = s.pc := by
    rw [hm15, if_pos rfl, a14, g14 _ (by simp only [dvCtx]; omega), hS.pc]
  have hW15 := (((hW11.exec e12).exec e13).exec e14).exec e15
  have eAll := (((((((((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans
    e8).trans e9).trans e10).trans e11).trans e12).trans e13).trans e14).trans e15
  have hin15 : S15.input = x := by rw [run_input eAll, C.input]
  have hout15 : S15.out = [] := by
    rw [ho15, ho14, ho13, ho12, ho11, ho10, ho9, ho8, ho7, ho6, ho5, ho4, ho3, ho2, ho1, C.out]
  have hx := G.xlen
  have hx' : x.length < 2 ^ w := by omega
  refine ⟨S15, eAll, by
    simp only [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3,
      hpc2, hpc1, hpc]; rfl, ?_, w13⟩
  have hW : ∀ a, (dvGeo w K B I).W a → a = rCur ∨ a = rOC ∨ (rT ≤ a ∧ a ≤ rU) ∨
      (dvBase w K I ≤ a ∧ a < dvBase w K I + 2 ^ (w - K - I)) ∨
      (dvCtx B I + 4 ≤ a ∧ a < dvCtx B I + 4 + (B + 1)) := fun a h => dvGeo_W G hI h
  refine
    { const := C.frame (fun a ha => fAll a (by simp only [DConstCell] at ha; omega)
        (by simp only [DConstCell] at ha; omega) (by simp only [DConstCell] at ha; omega)
        (by simp only [DConstCell] at ha; omega) (by simp only [DConstCell] at ha; omega)
        (by simp only [DConstCell] at ha; omega) (by simp only [DConstCell] at ha; omega)
        (by simp only [DConstCell] at ha; omega) (by simp only [DConstCell] at ha; omega))
        hW15 (by rw [hin15, C.input]) (by rw [hout15, C.out])
      slot := by rw [fAll 20 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; exact hslot
      pos := hj
      thr := hIj
      valid := hI
      ctx := by rw [fAll 24 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; exact h24
      cnt := hcnt
      rel := ?_
      alive := by rw [hctx _ (by simp only [dvCtx]; omega)]; exact hS.alive
      others := fun i hi hne => (hothers i hi hne).frame (fun a ha => hctx a
        (dv_area_ge G hi ha)) }
  have hS16 : S15.mem 16 = 1 := by
    rw [fAll 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact C.len0
  have hS18 : S15.mem 18 = x.length := by
    rw [fAll 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact C.len1
  have hS19 : S15.mem 19 = 0 := by
    rw [fAll 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact C.st1
  have hnW : ∀ a, 16 ≤ a → a < 20 → ¬ (dvGeo w K B I).W a := fun a h1 h2 hWa => by
    rcases hW a hWa with h | h | h | h | h <;> simp only [dvCtx] at * <;> omega
  exact
    { env := ⟨hW15, by rw [fAll 0 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact C.zero,
        by rw [fAll 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]; exact C.one, w2, w3, hb.2.1,
        by show 16 ≤ dvBase w K I; have := hb.1; omega, by show w - K - I ≤ w; omega⟩
      cword := hS.cword
      mem := fun a ha => by
        rw [hctx _ (by have := hb.1; simp only [dvGeo]; omega)]; exact hS.mem a ha
      input := hS.input
      cur := by rw [w4]; simpa using hS.cur
      inp := by rw [w4]; exact hS.inp
      tot := by
        rw [fAll 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), C.tot]; simp
      table := ⟨[[I], x], ⟨hnW 16 (by omega) (by omega), hnW 17 (by omega) (by omega),
          ⟨hS16, I, rfl, by rw [w17, Nat.mod_eq_of_lt (by
            have := Nat.lt_two_pow_self (n := w); omega)]⟩,
          hnW 18 (by omega) (by omega), hnW 19 (by omega) (by omega),
          ⟨by rw [hS19, hS18, hin15]; simp, fun _ => by rw [hS19, hS18, hin15]; omega,
            by rw [hin15]; exact hx'⟩, trivial⟩, by simp⟩
      tb16 := le_rfl
      tbw := by simp [dvKs]; omega
      out := ⟨hout15, w6, by rw [w7, hS.oc], by
          rw [fAll 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)]; exact C.cap, hS.ocB,
        by show 16 ≤ dvCtx B I + 4; simp only [dvCtx]; omega,
        by show dvCtx B I + 4 + (B + 1) ≤ 2 ^ w; omega,
        Or.inl (by show dvCtx B I + 4 + (B + 1) ≤ dvBase w K I; have := hb.1; omega), fun k hk => by
          simp only [dvGeo]
          rw [hctx _ (by simp only [dvCtx]; omega)]; exact hS.buf k hk⟩ }

theorem pow_ruler_dvd (q : ℕ) : 2 ^ ruler q ∣ q := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
      by_cases h : q ≠ 0 ∧ q % 2 = 0
      · rw [ruler_even h.1 h.2, pow_succ]
        obtain ⟨m, hm⟩ := ih (q / 2) (by omega)
        exact ⟨m, by rw [mul_comm (2 ^ ruler (q / 2)) 2, mul_assoc, ← hm]; omega⟩
      · rw [ruler, dif_neg h, pow_zero]; exact one_dvd _

theorem ruler_lt {q w : ℕ} (h0 : q ≠ 0) (h : q < 2 ^ w) : ruler q < w := by
  have := Nat.le_of_dvd (by omega) (pow_ruler_dvd q)
  by_contra hc
  have := two_pow_le_two_pow_of_le (show w ≤ ruler q by omega)
  omega

/-- A slot with no live valid thread: count it and go on. -/
theorem dv_skip_slot (G : DGlob w K B Q x) {j : ℕ} {S S' : State} (D : DInv w K B Q x j S)
    (hpc : S'.pc = dvSkip Q) (hfr : ∀ a, (a < 9 ∨ 14 < a) → (a < 21 ∨ 24 < a) →
      S'.mem a = S.mem a) (hW : WordMem w S'.mem) (hi : S'.input = S.input)
    (ho : S'.out = S.out)
    (hthr : ∀ i, i + K < w → ruler j = i → j ≠ 0 → S.mem (dvCtx B i + 3) ≠ 0) :
    ∃ S'', Exec w (dvProg Q B K) 2 S' S'' ∧ DInv w K B Q x (j + 1) S'' := by
  have hj := D.pos
  refine dv_next G (Fits.sub (dv_fits_skip Q B K) 0 2) (by simpa using hpc)
    (D.const.frame (fun a ha => hfr a (by simp only [DConstCell] at ha; omega)
      (by simp only [DConstCell] at ha; omega)) hW hi ho)
    (by rw [hfr 20 (by omega) (by omega)]; exact D.slot) hj (fun i hi' => ?_)
  have hf40 : ∀ a, 40 ≤ a → S'.mem a = S.mem a := fun a ha => hfr a (by omega) (by omega)
  have hT := D.threads i hi'
  by_cases hc : j ≠ 0 ∧ ruler j = i
  · have hd := hthr i hi' hc.2 hc.1
    rcases hT with ⟨s, -, -, hS⟩ | ⟨h1, h2⟩
    · exact absurd hS.alive hd
    · refine Or.inr ⟨?_, h2⟩
      rw [hf40 _ (by simp only [dvCtx]; omega)]; exact h1
  · rw [count_succ, if_neg hc, Nat.add_zero]
    exact hT.frame (fun a ha => hf40 a (dv_area_ge G hi' ha))

/-- The head of a slot: skip it, or load the live thread of the slot. -/
theorem dv_head (G : DGlob w K B Q x) {j : ℕ} {S : State} (D : DInv w K B Q x j S) :
    (∃ n ≤ 7 * ruler j + 40, ∃ S', Exec w (dvProg Q B K) n S S' ∧
      DInv w K B Q x (j + 1) S') ∨
    (∃ n ≤ 7 * ruler j + 40, ∃ S' s, Exec w (dvProg Q B K) n S S' ∧ S'.pc = dvDisp ∧
      Running w K B Q x j (ruler j) (count (ruler j) j) s S' ∧
      run (w - ruler j - K) Q (count (ruler j) j) (initState (ruler j :: x)) = some s ∧
      (s.pc < Q.length ∨ s.pc = 0) ∧ S'.mem rD = s.pc) := by
  have hw := G.hw
  have hwlt : w < 2 ^ w := Nat.lt_two_pow_self
  have hR : dvR B = B + 5 := rfl
  have h5w : 5 * w ≤ dvR B * w := Nat.mul_le_mul_right _ (by simp [dvR])
  have hf := dv_fits_head Q B K
  have C := D.const
  have hm := C.word
  have hpc := D.pc
  have hj := D.pos
  by_cases hz : j % 2 ^ w = 0
  · -- the slot counter wrapped around: no thread has this slot
    have e1 := x_jzero_pos (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)
      (by rw [D.slot, hz])
    obtain ⟨S'', e2, hD⟩ := dv_skip_slot G D (S' := { S with pc := dvSkip Q }) rfl
      (fun _ _ _ => rfl) hm rfl rfl (fun i hi hij hj0 => by
        have := le_ruler_of_dvd hj0 (Nat.dvd_of_mod_eq_zero hz); omega)
    exact Or.inl ⟨1 + 2, by omega, S'', e1.trans e2, hD⟩
  · have e1 := x_jzero_neg (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)
      (by rw [D.slot]; exact hz)
    obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_add (w := w) (s := { S with pc := S.pc + 1 })
      (fetch hf (i := 1) (by simp [hpc]) rfl) (by omega) (by omega) (by omega)).upd
    obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_set (w := w) (s := S2)
      (fetch hf (i := 2) (by simp [hpc2, hpc]) rfl) (by omega)).upd
    have hq : S3.mem 22 = j % 2 ^ w := by
      rw [hm3, if_neg (by decide), hm2, if_pos rfl]
      show (S.mem 20 + S.mem 0) % 2 ^ w = _
      rw [D.slot, C.zero, Nat.add_zero, Nat.mod_mod]
    have hr0 : S3.mem 21 = 0 := by rw [hm3, if_pos rfl, Nat.zero_mod]
    have f3 : ∀ a, a ≠ 21 → a ≠ 22 → S3.mem a = S.mem a := by
      intro a h1 h2; rw [hm3, if_neg h1, hm2, if_neg h2]
    have hW3 : WordMem w S3.mem := (WordMem.exec (s := { S with pc := S.pc + 1 }) hm e2).exec e3
    obtain ⟨S4, e4, hpc4, h21, f4, hi4, hn4, ho4⟩ := dv_halve G (ruler (j % 2 ^ w))
      (j % 2 ^ w) 0 S3 rfl hz (by simpa using Nat.mod_lt j (two_pow_pos w))
      (by rw [hpc3, hpc2]; simp [hpc]) hq hr0
      (by rw [f3 _ (by decide) (by decide)]; exact C.two)
      (by rw [f3 _ (by decide) (by decide)]; exact C.one) hW3
    rw [ruler_mod hz, Nat.zero_add] at h21
    set I := ruler j with hI
    have hIw : I < w := by rw [hI, ← ruler_mod hz]; exact ruler_lt hz (Nat.mod_lt _ (two_pow_pos w))
    have f4' : ∀ a, a ≠ rT → a ≠ 21 → a ≠ 22 → S4.mem a = S.mem a := fun a h1 h2 h3 => by
      rw [f4 a h1 h2 h3, f3 a h2 h3]
    have hW4 := hW3.exec e4
    have hfF := Fits.sub hf 11 10
    obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_add (w := w) (s := S4)
      (fetch hfF (i := 0) (by simp [hpc4]) rfl) (by omega) (by omega) (by omega)).upd
    have hKI : S5.mem rT = K + I := by
      rw [hm5, if_pos rfl, f4' _ (by decide) (by decide) (by decide), C.kk, h21,
        Nat.mod_eq_of_lt (by have := G.kw; omega)]
    obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_shiftl (w := w) (s := S5)
      (fetch hfF (i := 1) (by simp [hpc5, hpc4]) rfl) (by omega) (by omega) (by omega)).upd
    have hP : S6.mem 23 = 2 ^ (K + I) % 2 ^ w := by
      rw [hm6, if_pos rfl, hm5, if_neg (by decide), f4' _ (by decide) (by decide) (by decide),
        C.one, one_mul, hKI]
    have f6 : ∀ a, a ≠ rT → a ≠ 21 → a ≠ 22 → a ≠ 23 → S6.mem a = S.mem a := by
      intro a h1 h2 h3 h4; rw [hm6, if_neg h4, hm5, if_neg h1, f4' a h1 h2 h3]
    have h21' : S6.mem 21 = I := by
      rw [hm6, if_neg (by decide), hm5, if_neg (by decide), h21]
    have hW6 := (hW4.exec e5).exec e6
    have hio6 : S6.input = S.input ∧ S6.out = S.out := ⟨by rw [hi6, hi5, hi4, hi3, hi2],
      by rw [ho6, ho5, ho4, ho3, ho2]⟩
    by_cases hv : I + K < w
    · -- a valid thread: check its dead flag
      have hP' : S6.mem 23 = 2 ^ (K + I) := by
        rw [hP, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
      have hc := dvCtx_le G hv
      have hc' : I * dvR B + 40 + dvR B ≤ 40 + dvR B * w := hc
      have e7 := x_jzero_neg (w := w) (s := S6) (fetch hfF (i := 2) (by simp [hpc6, hpc5, hpc4])
        rfl) (by omega) (by rw [hP']; positivity)
      obtain ⟨S8, e8, hpc8, hm8, hi8, hn8, ho8⟩ := (x_mul (w := w)
        (s := { S6 with pc := S6.pc + 1 }) (fetch hfF (i := 3) (by simp [hpc6, hpc5, hpc4]) rfl)
        (by omega) (by omega) (by omega)).upd
      obtain ⟨S9, e9, hpc9, hm9, hi9, hn9, ho9⟩ := (x_add (w := w) (s := S8)
        (fetch hfF (i := 4) (by simp [hpc8, hpc6, hpc5, hpc4]) rfl) (by omega) (by omega)
        (by omega)).upd
      have h24 : S9.mem 24 = dvCtx B I := by
        rw [hm9, if_pos rfl, hm8, if_pos rfl, hm8, if_neg (by decide)]
        show ((S6.mem 21 * S6.mem 34) % 2 ^ w + S6.mem 35) % 2 ^ w = _
        rw [h21', f6 _ (by decide) (by decide) (by decide) (by decide), C.rsize,
          f6 _ (by decide) (by decide) (by decide) (by decide), C.rbase,
          Nat.mod_eq_of_lt (show I * dvR B < 2 ^ w by omega),
          Nat.mod_eq_of_lt (show I * dvR B + 40 < 2 ^ w by omega)]; rfl
      obtain ⟨S10, e10, hpc10, hm10, hi10, hn10, ho10⟩ := (x_set (w := w) (s := S9)
        (fetch hfF (i := 5) (by simp [hpc9, hpc8, hpc6, hpc5, hpc4]) rfl) (by omega)).upd
      obtain ⟨S11, e11, hpc11, hm11, hi11, hn11, ho11⟩ := (x_add (w := w) (s := S10)
        (fetch hfF (i := 6) (by simp [hpc10, hpc9, hpc8, hpc6, hpc5, hpc4]) rfl) (by omega)
        (by omega) (by omega)).upd
      have hT11 : S11.mem rT = dvCtx B I + 3 := by
        rw [hm11, if_pos rfl, hm10, if_pos rfl, hm10, if_neg (by decide), h24,
          Nat.mod_eq_of_lt (show 3 < 2 ^ w by omega), Nat.mod_eq_of_lt (by omega)]; omega
      have hW11 := ((((hW6.exec (s := { S6 with pc := S6.pc + 1 }) e8)).exec e9).exec e10).exec e11
      obtain ⟨S12, e12, hpc12, hm12, hi12, hn12, ho12⟩ := (x_load (w := w) (s := S11)
        (fetch hfF (i := 7) (by simp [hpc11, hpc10, hpc9, hpc8, hpc6, hpc5, hpc4]) rfl) hW11
        (by omega) (by omega)).upd
      have f12 : ∀ a, a ≠ rT → a ≠ rU → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 24 →
          S12.mem a = S.mem a := by
        intro a h1 h2 h3 h4 h5 h6
        rw [hm12, if_neg h2, hm11, if_neg h1, hm10, if_neg h1, hm9, if_neg h6, hm8, if_neg h6]
        exact f6 a h1 h3 h4 h5
      have hflag : S12.mem rU = S.mem (dvCtx B I + 3) := by
        rw [hm12, if_pos rfl, hT11, hm11, if_neg (by simp only [dvCtx]; omega), hm10,
          if_neg (by simp only [dvCtx]; omega), hm9, if_neg (by simp only [dvCtx]; omega), hm8,
          if_neg (by simp only [dvCtx]; omega)]
        exact f6 _ (by simp only [dvCtx]; omega) (by simp only [dvCtx]; omega)
          (by simp only [dvCtx]; omega) (by simp only [dvCtx]; omega)
      have h24' : S12.mem 24 = dvCtx B I := by
        rw [hm12, if_neg (by decide), hm11, if_neg (by decide), hm10, if_neg (by decide), h24]
      have h21'' : S12.mem 21 = I := by
        rw [hm12, if_neg (by decide), hm11, if_neg (by decide), hm10, if_neg (by decide), hm9,
          if_neg (by decide), hm8, if_neg (by decide)]; exact h21'
      have h23 : S12.mem 23 = 2 ^ (K + I) := by
        rw [hm12, if_neg (by decide), hm11, if_neg (by decide), hm10, if_neg (by decide), hm9,
          if_neg (by decide), hm8, if_neg (by decide)]; exact hP'
      have hW12 := hW11.exec e12
      have hio12 : S12.input = S.input ∧ S12.out = S.out :=
        ⟨by rw [hi12, hi11, hi10, hi9, hi8]; exact hio6.1,
          by rw [ho12, ho11, ho10, ho9, ho8]; exact hio6.2⟩
      have e12' := ((((((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans
        e7).trans e8).trans e9).trans e10).trans e11).trans e12
      have hf40 : ∀ a, 40 ≤ a → S12.mem a = S.mem a := fun a ha =>
        f12 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rcases D.threads I hv with ⟨s, hrun, hspc, hS⟩ | ⟨hd, hnot⟩
      · -- alive: load it
        have e13 := x_jzero_pos (w := w) (s := S12) (fetch hfF (i := 8)
          (by simp [hpc12, hpc11, hpc10, hpc9, hpc8, hpc6, hpc5, hpc4]) rfl) (by omega)
          (by rw [hflag]; exact hS.alive)
        obtain ⟨S', e14, hpc', hR', hD⟩ := dv_load G (S := { S12 with pc := dvL0 + 21 }) rfl
          (C.frame (fun a ha => f12 a (by simp only [DConstCell] at ha; omega)
            (by simp only [DConstCell] at ha; omega) (by simp only [DConstCell] at ha; omega)
            (by simp only [DConstCell] at ha; omega) (by simp only [DConstCell] at ha; omega)
            (by simp only [DConstCell] at ha; omega)) hW12 hio12.1 hio12.2)
          (by show S12.mem 20 = _; rw [f12 _ (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact D.slot) hj hI.symm hv h21'' h23 h24' rfl
          (hS.frame (fun a ha => hf40 a (dv_area_ge G hv ha)))
          (fun i hi hne => (D.threads i hi).frame (fun a ha => hf40 a (dv_area_ge G hi ha)))
        refine Or.inr ⟨_, ?_, S', s, (e12'.trans e13).trans e14, hpc', hR', hrun, hspc, hD⟩
        have := Nat.mod_lt j (two_pow_pos w)
        rw [ruler_mod hz] at *
        omega
      · -- dead: skip
        have e13 := (x_jzero_neg (w := w) (s := S12) (fetch hfF (i := 8)
          (by simp [hpc12, hpc11, hpc10, hpc9, hpc8, hpc6, hpc5, hpc4]) rfl) (by omega)
          (by rw [hflag]; exact hd)).trans (x_jump (fetch hfF (i := 9)
          (by simp [hpc12, hpc11, hpc10, hpc9, hpc8, hpc6, hpc5, hpc4]) rfl))
        obtain ⟨S'', e14, hD⟩ := dv_skip_slot G D (S' := { S12 with pc := dvSkip Q }) rfl
          (fun a h1 h2 => f12 a (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega)) hW12 hio12.1 hio12.2
          (fun i hi hij _ => by rw [← hI] at hij; subst hij; exact hd)
        refine Or.inl ⟨_, ?_, S'', (e12'.trans e13).trans e14, hD⟩
        have := Nat.mod_lt j (two_pow_pos w)
        rw [ruler_mod hz] at *
        omega
    · -- the thread would have word length zero
      have hP0 : S6.mem 23 = 0 := by
        rw [hP]; exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
      have e7 := x_jzero_pos (w := w) (s := S6) (fetch hfF (i := 2) (by simp [hpc6, hpc5, hpc4])
        rfl) (by omega) hP0
      obtain ⟨S'', e8, hD⟩ := dv_skip_slot G D (S' := { S6 with pc := dvSkip Q }) rfl
        (fun a h1 h2 => f6 a (by omega) (by omega) (by omega) (by omega)) hW6 hio6.1 hio6.2
        (fun i hi hij _ => by rw [← hI] at hij; omega)
      refine Or.inl ⟨_, ?_, S'', ((((((e1.trans e2).trans e3).trans e4).trans e5).trans
        e6).trans e7).trans e8, hD⟩
      have := Nat.mod_lt j (two_pow_pos w)
      rw [ruler_mod hz] at *
      omega

end Lax185574Proofs.RamSim
