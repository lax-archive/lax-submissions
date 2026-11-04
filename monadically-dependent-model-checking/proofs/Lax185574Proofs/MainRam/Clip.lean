import Lax185574Proofs.MainRam.Defs

/-!
The clipping program of a thread, in raw word-RAM code: it writes
`min (a mod 2^w) |u|` for every entry `a` of its input `u`. An IMP+
program cannot read arbitrary words, because every value of its run
must stay below a bound smaller than `2^w`, so this step is written
directly. Its output has entries at most `|u|`, which the validation
can read.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec

/-- Cells: `1` the length, `2` the position, `3` the entry, `4` a
difference, `5` the constant one, `6` the constant zero. -/
def clipProg : Program :=
  [.inputLength 1, .set 2 0, .set 5 1,
   .sub 4 1 2, .jzero 4 12, .inputLoad 3 2, .sub 4 3 1, .jzero 4 9, .add 3 1 6,
   .write 3, .add 2 2 5, .jump 3, .halt]

/-- The state at the loop head after `k` entries. -/
structure ClipInv (w : ℕ) (u : List ℕ) (k : ℕ) (s : State) : Prop where
  pc : s.pc = 3
  len : s.mem 1 = u.length
  pos : s.mem 2 = k
  one : s.mem 5 = 1
  zero : s.mem 6 = 0
  word : WordMem w s.mem
  input : s.input = u
  out : s.out = (clipList w u).take k

theorem clip_iter {w : ℕ} {u : List ℕ} {k : ℕ} {s : State} (hw : 4 ≤ w)
    (hu : u.length < 2 ^ w) (I : ClipInv w u k s) (hk : k < u.length) :
    ∃ n ≤ 9, ∃ s', Exec w clipProg n s s' ∧ ClipInv w u (k + 1) s' := by
  have h16 : 16 ≤ 2 ^ w := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hpc := I.pc
  have hm := I.word
  have e3 := x_sub (w := w) (p := clipProg) (s := s) (a := 4) (b := 1) (c := 2)
    (by rw [hpc]; rfl) hm (by omega) (by omega) (by omega)
  set s3 := { s with pc := s.pc + 1, mem := Function.update s.mem 4 (s.mem 1 - s.mem 2) }
  have hm3 : WordMem w s3.mem := hm.exec e3
  have e4 := x_jzero_neg (w := w) (p := clipProg) (s := s3) (a := 4) (l := 12)
    (by simp [s3, hpc]; rfl) (by omega) (by simp [s3, I.len, I.pos]; omega)
  set s4 := { s3 with pc := s3.pc + 1 }
  have e5 := x_inputLoad (w := w) (p := clipProg) (s := s4) (a := 3) (b := 2)
    (by simp [s4, s3, hpc]; rfl) (hm3.exec e4) (by omega) (by omega)
  set v := (s4.input[s4.mem 2]?.getD 0) % 2 ^ w
  have hv : v = u[k]?.getD 0 % 2 ^ w := by simp [v, s4, s3, I.input, I.pos]
  set s5 := { s4 with pc := s4.pc + 1, mem := Function.update s4.mem 3 v }
  have hm5 : WordMem w s5.mem := (hm3.exec e4).exec e5
  have e6 := x_sub (w := w) (p := clipProg) (s := s5) (a := 4) (b := 3) (c := 1)
    (by simp [s5, s4, s3, hpc]; rfl) hm5 (by omega) (by omega) (by omega)
  set s6 := { s5 with pc := s5.pc + 1, mem := Function.update s5.mem 4 (s5.mem 3 - s5.mem 1) }
  have hm6 : WordMem w s6.mem := hm5.exec e6
  have h61 : s6.mem 1 = u.length := by simp [s6, s5, s4, s3, I.len]
  have h63 : s6.mem 3 = v := by simp [s6, s5]
  have h64 : s6.mem 4 = v - u.length := by simp [s6, s5, s4, s3, I.len]
  have hvw : v < 2 ^ w := Nat.mod_lt _ (by positivity)
  have hent : (clipList w u)[k]? = some (min v u.length) := by
    simp [clipList, hv, List.getElem?_map, List.getElem?_eq_getElem hk]
  have htake : (clipList w u).take (k + 1) = (clipList w u).take k ++ [min v u.length] := by
    rw [List.take_succ, hent]; rfl
  -- the entry to write is in cell 3 at pc 9
  obtain ⟨n₁, hn₁, s8, e78, hpc8, hm83, hm8eq, hin8, ho8, hw8⟩ :
      ∃ n₁ ≤ 2, ∃ s8 : State, Exec w clipProg n₁ s6 s8 ∧ s8.pc = 9 ∧
        s8.mem 3 = min v u.length ∧ (∀ c, c ≠ 3 → s8.mem c = s6.mem c) ∧
        s8.input = s6.input ∧ s8.out = s6.out ∧ WordMem w s8.mem := by
    by_cases hle : v ≤ u.length
    · have e7 := x_jzero_pos (w := w) (p := clipProg) (s := s6) (a := 4) (l := 9)
        (by simp [s6, s5, s4, s3, hpc]; rfl) (by omega) (by rw [h64]; omega)
      exact ⟨1, by omega, _, e7, rfl, by simp [h63]; omega, fun c _ => rfl, rfl, rfl, hm6.exec e7⟩
    · have e7 := x_jzero_neg (w := w) (p := clipProg) (s := s6) (a := 4) (l := 9)
        (by simp [s6, s5, s4, s3, hpc]; rfl) (by omega) (by rw [h64]; omega)
      have e8 := x_add (w := w) (p := clipProg) (s := { s6 with pc := s6.pc + 1 }) (a := 3) (b := 1)
        (c := 6) (by simp [s6, s5, s4, s3, hpc]; rfl) (by omega) (by omega) (by omega)
      have e78 := e7.trans e8
      refine ⟨2, le_rfl, _, e78, by simp [s6, s5, s4, s3, hpc], ?_, ?_, rfl, rfl, hm6.exec e78⟩
      · have h66 : s6.mem 6 = 0 := by simp [s6, s5, s4, s3, I.zero]
        simp only [Function.update_self, h61, h66, Nat.add_zero]
        rw [Nat.mod_eq_of_lt hu]; omega
      · intro c hc; simp [Function.update_of_ne hc]
  have e9 := x_write (w := w) (p := clipProg) (s := s8) (a := 3) (by rw [hpc8]; rfl) hw8 (by omega)
  set s9 := { s8 with pc := s8.pc + 1, out := s8.out ++ [s8.mem 3] }
  have h92 : s9.mem 2 = k := by
    simp only [s9]; rw [hm8eq 2 (by omega)]; simp [s6, s5, s4, s3, I.pos]
  have h95 : s9.mem 5 = 1 := by
    simp only [s9]; rw [hm8eq 5 (by omega)]; simp [s6, s5, s4, s3, I.one]
  have e10 := x_add (w := w) (p := clipProg) (s := s9) (a := 2) (b := 2) (c := 5)
    (by simp [s9, hpc8]; rfl) (by omega) (by omega) (by omega)
  set s10 := { s9 with pc := s9.pc + 1, mem := Function.update s9.mem 2 ((s9.mem 2 + s9.mem 5) % 2 ^ w) }
  have e11 := x_jump (w := w) (p := clipProg) (s := s10) (l := 3) (by simp [s10, s9, hpc8]; rfl)
  have eAll := ((((((e3.trans e4).trans e5).trans e6).trans e78).trans e9).trans e10).trans e11
  refine ⟨_, by omega, _, eAll, ?_⟩
  have hm10 : WordMem w s10.mem := (hw8.exec e9).exec e10
  exact
    { pc := rfl
      len := by
        simp only [s10, s9]; rw [Function.update_of_ne (by omega), hm8eq 1 (by omega), h61]
      pos := by
        simp only [s10, Function.update_self]; rw [h92, h95, Nat.mod_eq_of_lt (by omega)]
      one := by simp only [s10, Function.update_of_ne (show (5 : ℕ) ≠ 2 by omega)]; exact h95
      zero := by
        simp only [s10, s9]; rw [Function.update_of_ne (by omega), hm8eq 6 (by omega)]
        simp [s6, s5, s4, s3, I.zero]
      word := hm10
      input := by simp only [s10, s9]; rw [hin8]; simp [s6, s5, s4, s3, I.input]
      out := by
        simp only [s10, s9]; rw [ho8, hm83, htake]; simp [s6, s5, s4, s3, I.out] }

/-- **The clipping program.** -/
theorem clipSpec : ClipSpec clipProg 15 := by
  intro w u hw hu
  have h16 : 16 ≤ 2 ^ w := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  set s0 := initState u
  have hm0 : WordMem w s0.mem := fun _ => by simp [s0, initState]
  obtain ⟨S1, e1, hpc1, hm1, hi1, -, ho1⟩ :=
    (x_inputLength (w := w) (p := clipProg) (s := s0) (a := 1) rfl (by omega)).upd
  obtain ⟨S2, e2, hpc2, hm2, hi2, -, ho2⟩ :=
    (x_set (w := w) (p := clipProg) (s := S1) (a := 2) (n := 0) (by rw [hpc1]; rfl)
      (by omega)).upd
  obtain ⟨S3, e3, hpc3, hm3, hi3, -, ho3⟩ :=
    (x_set (w := w) (p := clipProg) (s := S2) (a := 5) (n := 1) (by rw [hpc2, hpc1]; rfl)
      (by omega)).upd
  have eI := (e1.trans e2).trans e3
  have I0 : ClipInv w u 0 S3 := by
    refine ⟨by rw [hpc3, hpc2, hpc1]; rfl, ?_, ?_, ?_, ?_, hm0.exec eI, by rw [hi3, hi2, hi1]; rfl,
      by rw [ho3, ho2, ho1]; simp [s0, initState]⟩
    · rw [hm3, hm2, hm1]; simp [s0, initState, Nat.mod_eq_of_lt hu]
    · rw [hm3, hm2]; simp
    · rw [hm3]; simp; omega
    · rw [hm3, hm2, hm1]; simp [s0, initState]
  -- the loop
  have hloop : ∀ k ≤ u.length, ∃ n ≤ 3 + 9 * k, ∃ s, Exec w clipProg n s0 s ∧ ClipInv w u k s := by
    intro k hk
    induction k with
    | zero => exact ⟨_, le_refl _, _, eI, I0⟩
    | succ k ih =>
        obtain ⟨n, hn, s, e, I⟩ := ih (by omega)
        obtain ⟨n', hn', s', e', I'⟩ := clip_iter hw hu I (by omega)
        exact ⟨n + n', by omega, s', e.trans e', I'⟩
  obtain ⟨n, hn, s, e, I⟩ := hloop u.length le_rfl
  have hm := I.word
  obtain ⟨T3, e3, hpcT3, hmT3, -, -, hoT3⟩ :=
    (x_sub (w := w) (p := clipProg) (s := s) (a := 4) (b := 1) (c := 2)
      (by rw [I.pc]; rfl) hm (by omega) (by omega) (by omega)).upd
  have e4 := x_jzero_pos (w := w) (p := clipProg) (s := T3) (a := 4) (l := 12)
    (by rw [hpcT3, I.pc]; rfl) (by omega) (by rw [hmT3]; simp [I.len, I.pos])
  have hhalt : clipProg[({ T3 with pc := 12 } : State).pc]? = some .halt := rfl
  have hr := runsTo_of_exec ((e.trans e3).trans e4) (step_halt hhalt) (by
    show T3.out = _
    rw [hoT3, I.out, List.take_of_length_le (by simp [clipList])])
  refine ⟨_, ?_, hr⟩
  rw [terminalCost_of_getElem? hhalt]
  omega

end Lax185574Proofs.MainRam
