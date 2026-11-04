import Lax185574Proofs.RamLoopRun

/-!
The invariant of the loop driver at the start of a round, and its
initialization.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ} {p : Program}

/-- At the start of the round that uses region `i`: the constants, the
allocator, fresh memory above the next region, and the words `a` and
`b` in memory. -/
structure LInv (w : ℕ) (x a b : List ℕ) (i : ℕ) (S : State) : Prop where
  word : WordMem w S.mem
  zero : S.mem rZ = 0
  one : S.mem rOne = 1
  four : S.mem 52 = 4
  cap : S.mem 51 = lpCap w
  c4 : S.mem 54 = 4 * lpCap w
  c5 : S.mem 55 = 5 * lpCap w
  c6 : S.mem 56 = 6 * lpCap w
  c7 : S.mem 57 = 7 * lpCap w
  len : S.mem 15 = x.length
  input : S.input = x
  out : S.out = []
  alloc : AllocAt S (lpAlloc (lpCap w) i)
  fresh : ∀ c, lpBase w i ≤ c → c < 4 * lpCap w → S.mem c = 0
  acur : S.mem 44 = 4 * lpCap w ∨ S.mem 44 = 5 * lpCap w
  pcur : S.mem 46 = 6 * lpCap w ∨ S.mem 46 = 7 * lpCap w
  abuf : (S.mem 40 = 37 ∧ a.length ≤ 3) ∨ S.mem 40 = 4 * lpCap w + (5 * lpCap w - S.mem 44)
  bbuf : b.length = 0 ∨ S.mem 42 = 6 * lpCap w + (7 * lpCap w - S.mem 46)
  alen : S.mem 41 = a.length
  ale : a.length ≤ lpCap w
  aval : ∀ k < a.length, S.mem (S.mem 40 + k) = a.getD k 0
  blen : S.mem 43 = b.length
  ble : b.length ≤ lpCap w
  bval : ∀ k < b.length, S.mem (S.mem 42 + k) = b.getD k 0

theorem two_pow_sub_one_div_eight {w : ℕ} (hw : 3 ≤ w) : (2 ^ w - 1) / 8 = 2 ^ (w - 3) - 1 := by
  have h : 2 ^ w = 8 * 2 ^ (w - 3) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
  have : 1 ≤ 2 ^ (w - 3) := Nat.one_le_two_pow
  omega

/-- The initialization reaches the first round with `a = [0, |x|, |x|]`
and `b = []`. -/
theorem lp_init (G P : Program) {x : List ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ w) :
    ∃ S, Exec w (lpProg G P) 21 (initState x) S ∧ S.pc = lpLoop ∧
      LInv w x (lpA0 x) [] 0 S := by
  have hf := lp_fits_init G P
  obtain ⟨hC32, hCw⟩ := lpCap_bounds hw
  set C := lpCap w with hCdef
  set S0 := initState x
  obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_set (w := w) (s := S0)
    (fetch hf (i := 0) rfl rfl) (by omega)).upd
  obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_set (w := w) (s := S1)
    (fetch hf (i := 1) (by simp [hpc1, S0, initState]) rfl) (by omega)).upd
  obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_not (w := w) (s := S2)
    (fetch hf (i := 2) (by simp [hpc2, hpc1, S0, initState]) rfl) (by omega) (by omega)).upd
  have hW0 : WordMem w S0.mem := fun c => by simp [S0, initState]
  have hW3 : WordMem w S3.mem := hW0.exec ((e1.trans e2).trans e3)
  obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_div (w := w) (s := S3)
    (fetch hf (i := 3) (by simp [hpc3, hpc2, hpc1, S0, initState]) rfl) hW3 (by omega)
    (by omega) (by omega)).upd
  obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_add (w := w) (s := S4)
    (fetch hf (i := 4) (by simp [hpc4, hpc3, hpc2, hpc1, S0, initState]) rfl) (by omega)
    (by omega) (by omega)).upd
  obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_inputLength (w := w) (s := S5)
    (fetch hf (i := 5) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, S0, initState]) rfl)
    (by omega)).upd
  have hin5 : S5.input = x := by rw [hi5, hi4, hi3, hi2, hi1]; rfl
  -- the values of the first six steps
  have v1 : S6.mem rOne = 1 := by
    simp only [hm6, hm5, hm4, hm3, hm2, hm1]; simp [Nat.mod_eq_of_lt (show 1 < 2 ^ w by omega)]
  have v0 : S6.mem rZ = 0 := by
    simp only [hm6, hm5, hm4, hm3, hm2, hm1]; simp [S0, initState]
  have vC : S6.mem 51 = C := by
    have a1 : S1.mem 1 = 1 := by rw [hm1, if_pos rfl, Nat.mod_eq_of_lt (by omega)]
    have a2 : S2.mem 9 = 8 := by rw [hm2, if_pos rfl, Nat.mod_eq_of_lt (by omega)]
    have a3 : S3.mem 2 = 2 ^ w - 1 := by
      rw [hm3, if_pos rfl, hm2, if_neg (by decide), hm1, if_neg (by decide)]; simp [S0, initState]
    have a4 : S4.mem 2 = 2 ^ (w - 3) - 1 := by
      rw [hm4, if_pos rfl, a3, hm3, if_neg (by decide), a2, two_pow_sub_one_div_eight (by omega)]
    have a4' : S4.mem 1 = 1 := by
      rw [hm4, if_neg (by decide), hm3, if_neg (by decide), hm2, if_neg (by decide), a1]
    rw [hm6, if_neg (by decide), hm5, if_pos rfl, a4, a4']
    have : 1 ≤ 2 ^ (w - 3) := Nat.one_le_two_pow
    have hc : lpCap w = 2 ^ (w - 3) := rfl
    rw [hCdef, hc, Nat.sub_add_cancel this, Nat.mod_eq_of_lt (by omega)]
  have v15 : S6.mem 15 = x.length := by
    rw [hm6, if_pos rfl, hin5, Nat.mod_eq_of_lt hx]
  have hz6 : ∀ c, 15 < c → c ≠ 51 → S6.mem c = 0 := by
    intro c h1 h2
    rw [hm6, if_neg (by omega), hm5, if_neg h2, hm4, if_neg (by omega), hm3, if_neg (by omega),
      hm2, if_neg (by omega), hm1, if_neg (by omega)]; rfl
  have hW6 : WordMem w S6.mem := hW3.exec ((e4.trans e5).trans e6)
  have hpc6' : S6.pc = 6 := by simp [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, S0, initState]
  have hio6 : S6.input = x ∧ S6.out = [] := ⟨by rw [hi6, hin5], by
    rw [ho6, ho5, ho4, ho3, ho2, ho1]; rfl⟩
  -- the remaining fifteen steps write constants and copies
  obtain ⟨S7, e7, hpc7, hm7, -, -, ho7⟩ := (x_add (w := w) (s := S6)
    (fetch hf (i := 6) (by simp [hpc6']) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S8, e8, hpc8, hm8, -, -, ho8⟩ := (x_add (w := w) (s := S7)
    (fetch hf (i := 7) (by simp [hpc7, hpc6']) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S9, e9, hpc9, hm9, -, -, ho9⟩ := (x_set (w := w) (s := S8)
    (fetch hf (i := 8) (by simp [hpc8, hpc7, hpc6']) rfl) (by omega)).upd
  obtain ⟨S10, e10, hpc10, hm10, -, -, ho10⟩ := (x_set (w := w) (s := S9)
    (fetch hf (i := 9) (by simp [hpc9, hpc8, hpc7, hpc6']) rfl) (by omega)).upd
  obtain ⟨S11, e11, hpc11, hm11, -, -, ho11⟩ := (x_add (w := w) (s := S10)
    (fetch hf (i := 10) (by simp [hpc10, hpc9, hpc8, hpc7, hpc6']) rfl) (by omega) (by omega)
    (by omega)).upd
  obtain ⟨S12, e12, hpc12, hm12, -, -, ho12⟩ := (x_add (w := w) (s := S11)
    (fetch hf (i := 11) (by simp [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6']) rfl) (by omega)
    (by omega) (by omega)).upd
  obtain ⟨S13, e13, hpc13, hm13, -, -, ho13⟩ := (x_add (w := w) (s := S12)
    (fetch hf (i := 12) (by simp [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6']) rfl)
    (by omega) (by omega) (by omega)).upd
  obtain ⟨S14, e14, hpc14, hm14, -, -, ho14⟩ := (x_add (w := w) (s := S13)
    (fetch hf (i := 13) (by simp [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6']) rfl)
    (by omega) (by omega) (by omega)).upd
  obtain ⟨S15, e15, hpc15, hm15, -, -, ho15⟩ := (x_add (w := w) (s := S14)
    (fetch hf (i := 14) (by simp [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6'])
      rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S16, e16, hpc16, hm16, -, -, ho16⟩ := (x_add (w := w) (s := S15)
    (fetch hf (i := 15) (by simp [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7,
      hpc6']) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S17, e17, hpc17, hm17, -, -, ho17⟩ := (x_add (w := w) (s := S16)
    (fetch hf (i := 16) (by simp [hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8,
      hpc7, hpc6']) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S18, e18, hpc18, hm18, -, -, ho18⟩ := (x_set (w := w) (s := S17)
    (fetch hf (i := 17) (by simp [hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9,
      hpc8, hpc7, hpc6']) rfl) (by omega)).upd
  obtain ⟨S19, e19, hpc19, hm19, -, -, ho19⟩ := (x_add (w := w) (s := S18)
    (fetch hf (i := 18) (by simp [hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10,
      hpc9, hpc8, hpc7, hpc6']) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S20, e20, hpc20, hm20, -, -, ho20⟩ := (x_set (w := w) (s := S19)
    (fetch hf (i := 19) (by simp [hpc19, hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11,
      hpc10, hpc9, hpc8, hpc7, hpc6']) rfl) (by omega)).upd
  obtain ⟨S21, e21, hpc21, hm21, hi21, -, ho21⟩ := (x_set (w := w) (s := S20)
    (fetch hf (i := 20) (by simp [hpc20, hpc19, hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12,
      hpc11, hpc10, hpc9, hpc8, hpc7, hpc6']) rfl) (by omega)).upd
  have e := (((((((((((((((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans
    e7).trans e8).trans e9).trans e10).trans e11).trans e12).trans e13).trans e14).trans
    e15).trans e16).trans e17).trans e18).trans e19).trans e20).trans e21
  have hW21 : WordMem w S21.mem := hW0.exec e
  -- frames and values of the last fifteen steps
  have f7 : ∀ c, c ≠ 38 → S7.mem c = S6.mem c := fun c h => by rw [hm7, if_neg h]
  have f8 : ∀ c, c ≠ 39 → S8.mem c = S7.mem c := fun c h => by rw [hm8, if_neg h]
  have f9 : ∀ c, c ≠ 40 → S9.mem c = S8.mem c := fun c h => by rw [hm9, if_neg h]
  have f10 : ∀ c, c ≠ 41 → S10.mem c = S9.mem c := fun c h => by rw [hm10, if_neg h]
  have f11 : ∀ c, c ≠ 53 → S11.mem c = S10.mem c := fun c h => by rw [hm11, if_neg h]
  have f12 : ∀ c, c ≠ 54 → S12.mem c = S11.mem c := fun c h => by rw [hm12, if_neg h]
  have f13 : ∀ c, c ≠ 55 → S13.mem c = S12.mem c := fun c h => by rw [hm13, if_neg h]
  have f14 : ∀ c, c ≠ 56 → S14.mem c = S13.mem c := fun c h => by rw [hm14, if_neg h]
  have f15 : ∀ c, c ≠ 57 → S15.mem c = S14.mem c := fun c h => by rw [hm15, if_neg h]
  have f16 : ∀ c, c ≠ 44 → S16.mem c = S15.mem c := fun c h => by rw [hm16, if_neg h]
  have f17 : ∀ c, c ≠ 46 → S17.mem c = S16.mem c := fun c h => by rw [hm17, if_neg h]
  have f18 : ∀ c, c ≠ 47 → S18.mem c = S17.mem c := fun c h => by rw [hm18, if_neg h]
  have f19 : ∀ c, c ≠ 48 → S19.mem c = S18.mem c := fun c h => by rw [hm19, if_neg h]
  have f20 : ∀ c, c ≠ 50 → S20.mem c = S19.mem c := fun c h => by rw [hm20, if_neg h]
  have f21 : ∀ c, c ≠ 52 → S21.mem c = S20.mem c := fun c h => by rw [hm21, if_neg h]
  have v7 : S7.mem 38 = x.length := by
    rw [hm7, if_pos rfl, v15, v0, Nat.add_zero, Nat.mod_eq_of_lt hx]
  have v8 : S8.mem 39 = x.length := by
    rw [hm8, if_pos rfl, f7 _ (by decide), f7 _ (by decide), v15, v0, Nat.add_zero,
      Nat.mod_eq_of_lt hx]
  have v9 : S9.mem 40 = 37 := by rw [hm9, if_pos rfl, Nat.mod_eq_of_lt (by omega)]
  have v10 : S10.mem 41 = 3 := by rw [hm10, if_pos rfl, Nat.mod_eq_of_lt (by omega)]
  have r10 : S10.mem 51 = C := by
    simp (disch := decide) only [f10, f9, f8, f7]; exact vC
  have v11 : S11.mem 53 = 2 * C := by
    rw [hm11, if_pos rfl, r10, Nat.mod_eq_of_lt (by omega)]; ring
  have v12 : S12.mem 54 = 4 * C := by
    rw [hm12, if_pos rfl, v11, Nat.mod_eq_of_lt (by omega)]; ring
  have r12 : S12.mem 51 = C := by simp (disch := decide) only [f12, f11]; exact r10
  have v13 : S13.mem 55 = 5 * C := by
    rw [hm13, if_pos rfl, v12, r12, Nat.mod_eq_of_lt (by omega)]; ring
  have r13 : S13.mem 51 = C := by simp (disch := decide) only [f13]; exact r12
  have v14 : S14.mem 56 = 6 * C := by
    rw [hm14, if_pos rfl, v13, r13, Nat.mod_eq_of_lt (by omega)]; ring
  have r14 : S14.mem 51 = C := by simp (disch := decide) only [f14]; exact r13
  have v15' : S15.mem 57 = 7 * C := by
    rw [hm15, if_pos rfl, v14, r14, Nat.mod_eq_of_lt (by omega)]; ring
  have z15 : S15.mem 0 = 0 := by
    simp (disch := decide) only [f15, f14, f13, f12, f11, f10, f9, f8, f7]; exact v0
  have v16 : S16.mem 44 = 4 * C := by
    have : S15.mem 54 = 4 * C := by simp (disch := decide) only [f15, f14, f13]; exact v12
    rw [hm16, if_pos rfl, z15, Nat.add_zero, this, Nat.mod_eq_of_lt (by omega)]
  have v17 : S17.mem 46 = 6 * C := by
    have : S15.mem 56 = 6 * C := by simp (disch := decide) only [f15]; exact v14
    rw [hm17, if_pos rfl, f16 _ (by decide), f16 _ (by decide), z15, Nat.add_zero, this,
      Nat.mod_eq_of_lt (by omega)]
  have v18 : S18.mem 47 = 64 := by rw [hm18, if_pos rfl, Nat.mod_eq_of_lt (by omega)]
  have v19 : S19.mem 48 = C := by
    rw [hm19, if_pos rfl]
    simp (disch := decide) only [f18, f17, f16, f15, f14, f13, f12, f11, f10, f9, f8, f7]
    rw [vC, v0, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have v20 : S20.mem 50 = 1 := by rw [hm20, if_pos rfl, Nat.mod_eq_of_lt (by omega)]
  have v21 : S21.mem 52 = 4 := by rw [hm21, if_pos rfl, Nat.mod_eq_of_lt (by omega)]
  -- the low cells of the last fifteen steps are those of `S6`
  have g21 : ∀ c, c < 38 ∨ (41 < c ∧ c < 44) ∨ c = 45 ∨ c = 49 ∨ c = 51 ∨ 57 < c →
      S21.mem c = S6.mem c := by
    intro c hc
    rw [f21 c (by omega), f20 c (by omega), f19 c (by omega), f18 c (by omega),
      f17 c (by omega), f16 c (by omega), f15 c (by omega), f14 c (by omega), f13 c (by omega),
      f12 c (by omega), f11 c (by omega), f10 c (by omega), f9 c (by omega), f8 c (by omega),
      f7 c (by omega)]
  have hpc21 : S21.pc = lpLoop := by
    rw [hpc21, hpc20, hpc19, hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10,
      hpc9, hpc8, hpc7, hpc6']; rfl
  have hout21 : S21.out = [] := by
    rw [ho21, ho20, ho19, ho18, ho17, ho16, ho15, ho14, ho13, ho12, ho11, ho10, ho9, ho8, ho7,
      hio6.2]
  have hin21 : S21.input = x := run_input e
  -- cells read from earlier steps
  have r40 : S21.mem 40 = 37 := by
    simp (disch := decide) only [f21, f20, f19, f18, f17, f16, f15, f14, f13, f12, f11, f10]
    exact v9
  have r41 : S21.mem 41 = 3 := by
    simp (disch := decide) only [f21, f20, f19, f18, f17, f16, f15, f14, f13, f12, f11]
    exact v10
  have r38 : S21.mem 38 = x.length := by
    simp (disch := decide) only [f21, f20, f19, f18, f17, f16, f15, f14, f13, f12, f11, f10, f9, f8]
    exact v7
  have r39 : S21.mem 39 = x.length := by
    simp (disch := decide) only [f21, f20, f19, f18, f17, f16, f15, f14, f13, f12, f11, f10, f9]
    exact v8
  have r44 : S21.mem 44 = 4 * C := by
    simp (disch := decide) only [f21, f20, f19, f18, f17]
    exact v16
  have r46 : S21.mem 46 = 6 * C := by
    simp (disch := decide) only [f21, f20, f19, f18]
    exact v17
  have r47 : S21.mem 47 = 64 := by
    simp (disch := decide) only [f21, f20, f19]
    exact v18
  have r48 : S21.mem 48 = C := by
    simp (disch := decide) only [f21, f20]
    exact v19
  have r50 : S21.mem 50 = 1 := by
    simp (disch := decide) only [f21]
    exact v20
  have r54 : S21.mem 54 = 4 * C := by
    simp (disch := decide) only [f21, f20, f19, f18, f17, f16, f15, f14, f13]
    exact v12
  have r55 : S21.mem 55 = 5 * C := by
    simp (disch := decide) only [f21, f20, f19, f18, f17, f16, f15, f14]
    exact v13
  have r56 : S21.mem 56 = 6 * C := by
    simp (disch := decide) only [f21, f20, f19, f18, f17, f16, f15]
    exact v14
  have r57 : S21.mem 57 = 7 * C := by
    simp (disch := decide) only [f21, f20, f19, f18, f17, f16]
    exact v15'
  have hlow : ∀ c, 15 < c → c < 38 ∨ (41 < c ∧ c < 44) ∨ c = 45 ∨ c = 49 ∨ 57 < c →
      S21.mem c = 0 := fun c h1 h2 => by
    rw [g21 c (by omega)]; exact hz6 c h1 (by omega)
  refine ⟨S21, e, hpc21, ?_⟩
  exact
    { word := hW21
      zero := by rw [g21 0 (by omega)]; exact v0
      one := by rw [g21 1 (by omega)]; exact v1
      four := v21
      cap := by rw [g21 51 (by omega)]; exact vC
      c4 := r54
      c5 := r55
      c6 := r56
      c7 := r57
      len := by rw [g21 15 (by omega)]; exact v15
      input := hin21
      out := hout21
      alloc := ⟨r47, r48, by rw [hlow 49 (by decide) (by omega)]; rfl, r50⟩
      fresh := fun c h1 _ => hlow c (by simp [lpBase, lpAlloc] at h1; omega)
        (by simp [lpBase, lpAlloc] at h1; omega)
      acur := Or.inl r44
      pcur := Or.inl r46
      abuf := Or.inl ⟨r40, by simp [lpA0]⟩
      bbuf := Or.inl rfl
      alen := by rw [r41]; simp [lpA0]
      ale := by simp [lpA0]; omega
      aval := by
        intro k hk
        simp only [lpA0, List.length_cons, List.length_nil] at hk
        rw [r40]
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
        · rw [hlow 37 (by decide) (by omega)]; rfl
        · exact r38
        · exact r39
      blen := by rw [hlow 43 (by decide) (by omega)]; rfl
      ble := by simp
      bval := fun k hk => by simp at hk }

end Lax185574Proofs.RamSim
