import Lax185574Proofs.RamDoveExit

/-!
The dovetailer: one slot, the start, and the main theorem.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.Ruler

variable {w K B : ℕ} {Q : Program} {x : List ℕ}

/-- A bound on the cost of a slot, apart from the halvings. -/
def dvSC (Q : Program) (B : ℕ) : ℕ := 2 * Q.length + stepBound dvKs + 7 * B + 120

/-- The machine has halted, within the first `j` slots, with the output
`y` of an accepting thread `I` that took `t` steps. -/
def DHalt (w K B : ℕ) (Q : Program) (x : List ℕ) (j : ℕ) (S : State) : Prop :=
  (dvProg Q B K)[S.pc]? = some .halt ∧ ∃ I y t, I + K < w ∧ y.length ≤ B ∧
    RunsTo (w - I - K) Q (I :: x) (1 :: y) t ∧ S.out = y ∧ 2 ^ I * t ≤ 3 * j

theorem DHalt.mono {w K B : ℕ} {Q : Program} {x : List ℕ} {j j' : ℕ} {S : State}
    (h : DHalt w K B Q x j S) (hj : j ≤ j') : DHalt w K B Q x j' S := by
  obtain ⟨hh, I, y, t, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hh, I, y, t, h1, h2, h3, h4, by omega⟩

/-- One slot. -/
theorem dv_slot (G : DGlob w K B Q x) {j : ℕ} {S : State} (D : DInv w K B Q x j S) :
    ∃ n ≤ dvSC Q B + 7 * ruler j, ∃ S', Exec w (dvProg Q B K) n S S' ∧
      (DInv w K B Q x (j + 1) S' ∨ DHalt w K B Q x j S') := by
  have hSC : 40 + (2 * Q.length + 1) + (stepBound dvKs + 2) + 9 + 10 + 5 ≤ dvSC Q B := by
    simp only [dvSC]; omega
  have hSC' : 40 + (2 * Q.length + 1) + (stepBound dvKs + 2) + (7 * (B + 1) + 10) ≤ dvSC Q B := by
    simp only [dvSC]; omega
  -- the exit handler, then retirement
  have fin_exit : ∀ (n₀ c c' : ℕ) (s S1 : State), n₀ ≤ 40 + (2 * Q.length + 1) +
      (stepBound dvKs + 2) + 7 * ruler j → Exec w (dvProg Q B K) n₀ S S1 →
      Running w K B Q x j (ruler j) c s S1 → S1.pc = dvExit Q → c' ≤ c + 1 →
      run (w - ruler j - K) Q c' (initState (ruler j :: x)) = some s →
      step (w - ruler j - K) Q s = none →
      ∃ n ≤ dvSC Q B + 7 * ruler j, ∃ S', Exec w (dvProg Q B K) n S S' ∧
        (DInv w K B Q x (j + 1) S' ∨ DHalt w K B Q x j S') := by
    intro n₀ c c' s S1 hn₀ e1 h1 hpc1 hc' hrun hs
    rcases dv_exit G h1 hpc1 hrun hs with ⟨n, hn, S2, e2, hhalt, y, hy, ho⟩ |
      ⟨n, hn, S2, e2, hpc2, hdy⟩
    · refine ⟨n₀ + n, by omega, S2, e1.trans e2, Or.inr ⟨hhalt, ruler j, y, c' + terminalCost Q s,
        h1.valid, ?_, ?_, ho, ?_⟩⟩
      · have := h1.rel.out.2.2.2.2.1
        simp only [dvGeo, hy, List.length_cons] at this; omega
      · rw [← hy]; exact runsTo_of_exec hrun hs rfl
      · have hcnt := pow_mul_count_le (ruler j) j
        rw [h1.cnt] at hcnt
        have hpj : 2 ^ ruler j ≤ j := Nat.le_of_dvd (by have := D.pos; omega) (pow_ruler_dvd j)
        have htc := terminalCost_le_one Q s
        have : 2 ^ ruler j * (c' + terminalCost Q s) ≤ 2 ^ ruler j * (c + 2) :=
          Nat.mul_le_mul_left _ (by omega)
        nlinarith
    · obtain ⟨S3, e3, hD⟩ := dv_dead G hpc2 hdy.const hdy.slot hdy.pos hdy.valid hdy.thr hdy.ctx
        hdy.others hdy.never
      exact ⟨n₀ + n + 5, by omega, S3, (e1.trans e2).trans e3, Or.inl hD⟩
  rcases dv_head G D with ⟨n, hn, S', e, hD⟩ | ⟨n, hn, S1, s, e1, hpc1, h1, hrun, hspc, hD1⟩
  · exact ⟨n, by omega, S', e, Or.inl hD⟩
  · have hdisp := dv_dispatch G h1 hpc1 hD1
    by_cases hlt : s.pc < Q.length
    · obtain ⟨S2, e2, hpc2, h2⟩ := hdisp.1 hlt
      obtain ⟨n3, hn3, S3, e3, hcase⟩ := dv_exec G h2 hpc2 hlt hrun
      rcases hcase with ⟨s', hrun', hlt', hpc3, h25, h3⟩ | ⟨c', s', hc', hrun', hs', hpc3, h3⟩ |
        ⟨hpc3, hdy⟩
      · rw [← h3.cnt] at hrun'
        obtain ⟨S4, e4, hD4⟩ := dv_save G hpc3 h3 h25 hlt' (by rw [h3.cnt] at hrun' ⊢; exact hrun')
        exact ⟨n + (2 * s.pc + 1) + n3 + 9, by omega, S4, ((e1.trans e2).trans e3).trans e4,
          Or.inl hD4⟩
      · exact fin_exit (n + (2 * s.pc + 1) + n3) _ c' s' S3 (by omega)
          ((e1.trans e2).trans e3) h3 hpc3 hc' hrun' hs'
      · obtain ⟨S4, e4, hD4⟩ := dv_dead G hpc3 hdy.const hdy.slot hdy.pos hdy.valid hdy.thr
          hdy.ctx hdy.others hdy.never
        exact ⟨n + (2 * s.pc + 1) + n3 + 5, by omega, S4, ((e1.trans e2).trans e3).trans e4,
          Or.inl hD4⟩
    · obtain ⟨S2, e2, hpc2, h2⟩ := hdisp.2 (by omega)
      exact fin_exit (n + (2 * Q.length + 1)) _ _ s S2 (by omega) (e1.trans e2) h2 hpc2
        (Nat.le_succ _) hrun
        (step_none_of_length_le (by omega))

theorem count_one (i : ℕ) : count i 1 = 0 := by
  simp [count, Finset.range_one]

/-- The start: constants, and every thread fresh. -/
theorem dv_init (G : DGlob w K B Q x) :
    ∃ S, Exec w (dvProg Q B K) 16 (initState x) S ∧ DInv w K B Q x 1 S := by
  have hw := G.hw
  have hKw := G.kw
  have hx := G.xlen
  have hf := dv_fits_init Q B K
  have hwlt : w < 2 ^ w := Nat.lt_two_pow_self
  set S0 := initState x
  have hm0 : WordMem w S0.mem := fun _ => two_pow_pos w
  have hpc0 : S0.pc = 0 := rfl
  obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_set (w := w) (s := S0)
    (fetch hf (i := 0) (by simp [hpc0]) rfl) (by omega)).upd
  obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_set (w := w) (s := S1)
    (fetch hf (i := 1) (by simp [hpc1, hpc0]) rfl) (by omega)).upd
  obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_not (w := w) (s := S2)
    (fetch hf (i := 2) (by simp [hpc2, hpc1, hpc0]) rfl) (by omega) (by omega)).upd
  have hW3 := hm0.exec ((e1.trans e2).trans e3)
  obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_div (w := w) (s := S3)
    (fetch hf (i := 3) (by simp [hpc3, hpc2, hpc1, hpc0]) rfl) hW3 (by omega) (by omega)
    (by omega)).upd
  obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_add (w := w) (s := S4)
    (fetch hf (i := 4) (by simp [hpc4, hpc3, hpc2, hpc1, hpc0]) rfl) (by omega) (by omega)
    (by omega)).upd
  obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_set (w := w) (s := S5)
    (fetch hf (i := 5) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]) rfl) (by omega)).upd
  obtain ⟨S7, e7, hpc7, hm7, hi7, hn7, ho7⟩ := (x_shiftl (w := w) (s := S6)
    (fetch hf (i := 6) (by simp [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]) rfl) (by omega)
    (by omega) (by omega)).upd
  have hW7 := hW3.exec ((((e4.trans e5).trans e6).trans e7))
  obtain ⟨S8, e8, hpc8, hm8, hi8, hn8, ho8⟩ := (x_div (w := w) (s := S7)
    (fetch hf (i := 7) (by simp [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]) rfl) hW7
    (by omega) (by omega) (by omega)).upd
  obtain ⟨S9, e9, hpc9, hm9, hi9, hn9, ho9⟩ := (x_add (w := w) (s := S8)
    (fetch hf (i := 8) (by simp [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]) rfl)
    (by omega) (by omega) (by omega)).upd
  obtain ⟨S10, e10, hpc10, hm10, hi10, hn10, ho10⟩ := (x_inputLength (w := w) (s := S9)
    (fetch hf (i := 9) (by simp [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0])
      rfl) (by omega)).upd
  obtain ⟨S11, e11, hpc11, hm11, hi11, hn11, ho11⟩ := (x_set (w := w) (s := S10)
    (fetch hf (i := 10) (by simp [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1,
      hpc0]) rfl) (by omega)).upd
  obtain ⟨S12, e12, hpc12, hm12, hi12, hn12, ho12⟩ := (x_add (w := w) (s := S11)
    (fetch hf (i := 11) (by simp [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2,
      hpc1, hpc0]) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S13, e13, hpc13, hm13, hi13, hn13, ho13⟩ := (x_set (w := w) (s := S12)
    (fetch hf (i := 12) (by simp [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3,
      hpc2, hpc1, hpc0]) rfl) (by omega)).upd
  obtain ⟨S14, e14, hpc14, hm14, hi14, hn14, ho14⟩ := (x_set (w := w) (s := S13)
    (fetch hf (i := 13) (by simp [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4,
      hpc3, hpc2, hpc1, hpc0]) rfl) (by omega)).upd
  obtain ⟨S15, e15, hpc15, hm15, hi15, hn15, ho15⟩ := (x_set (w := w) (s := S14)
    (fetch hf (i := 14) (by simp [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5,
      hpc4, hpc3, hpc2, hpc1, hpc0]) rfl) (by omega)).upd
  obtain ⟨S16, e16, hpc16, hm16, hi16, hn16, ho16⟩ := (x_set (w := w) (s := S15)
    (fetch hf (i := 15) (by simp [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6,
      hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]) rfl) (by omega)).upd
  have eAll := ((((((((((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans
    e7).trans e8).trans e9).trans e10).trans e11).trans e12).trans e13).trans e14).trans
    e15).trans e16
  have hW16 := hm0.exec eAll
  have hin : S16.input = x := by rw [run_input eAll]; rfl
  have hout : S16.out = [] := by
    rw [ho16, ho15, ho14, ho13, ho12, ho11, ho10, ho9, ho8, ho7, ho6, ho5, ho4, ho3, ho2, ho1]; rfl
  have hhalf : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have hK : 2 ^ K < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) hKw
  have v26 : S16.mem 26 = 2 ^ w - 1 := by
    simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1,
      S0, initState]
  have hin9 : S9.input = x := by rw [hi9, hi8, hi7, hi6, hi5, hi4, hi3, hi2, hi1]; rfl
  have m2 : 2 % 2 ^ w = 2 := Nat.mod_eq_of_lt (by omega)
  have mK : K % 2 ^ w = K := Nat.mod_eq_of_lt (by omega)
  have m40 : 40 % 2 ^ w = 40 := Nat.mod_eq_of_lt (by omega)
  have mx : x.length % 2 ^ w = x.length := Nat.mod_eq_of_lt (by omega)
  have v1 : S16.mem 1 = 1 := by simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState]; omega
  have v29 : S16.mem 29 = 2 := by simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState, m2]
  have hRw : dvR B ≤ dvR B * w := Nat.le_mul_of_pos_right _ (by omega)
  have hR : dvR B = B + 5 := rfl
  have hp1 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
  have v28 : S16.mem 28 = 2 ^ (w - 1) := by
    simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState, m2]
    rw [two_pow_sub_one_div (by omega), Nat.sub_add_cancel hp1, Nat.mod_eq_of_lt (by omega)]
  have v36 : S16.mem 36 = K := by simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState, mK]
  have v27 : S16.mem 27 = 2 ^ (w - K) := by
    simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState, mK, Nat.mod_eq_of_lt hK]
    have hp : 1 ≤ 2 ^ (w - K) := Nat.one_le_two_pow
    have hp' : 2 ^ (w - K) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by have := G.k2; omega)
    rw [two_pow_sub_one_div_two_pow (by omega), Nat.sub_add_cancel hp, Nat.mod_eq_of_lt hp']
  have v18 : S16.mem 18 = x.length := by simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState, hin9, mx]
  have v16 : S16.mem 16 = 1 := by simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState]; omega
  have v5 : S16.mem 5 = x.length + 1 := by
    simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState, hin9]; exact Nat.mod_eq_of_lt (by omega)
  have v8 : S16.mem 8 = B + 1 := by
    simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState]; exact Nat.mod_eq_of_lt (by omega)
  have v34 : S16.mem 34 = dvR B := by
    simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState]; exact Nat.mod_eq_of_lt (by omega)
  have v35 : S16.mem 35 = 40 := by simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState, m40]
  have v20 : S16.mem 20 = 1 := by simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState]; omega
  have v0 : ∀ c, c ≠ 1 → c ≠ 29 → c ≠ 26 → c ≠ 28 → c ≠ 36 → c ≠ 23 → c ≠ 27 → c ≠ 18 →
      c ≠ 16 → c ≠ 5 → c ≠ 8 → c ≠ 34 → c ≠ 35 → c ≠ 20 → S16.mem c = 0 := by
    intro c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    simp [hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, S0, initState, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  have z : ∀ c, 40 ≤ c → S16.mem c = 0 := fun c hc =>
    v0 c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨S16, eAll, ?_⟩
  exact
    { const :=
        { word := hW16
          zero := v0 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          one := v1
          len0 := v16
          len1 := v18
          st1 := v0 19 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          tot := v5
          cap := v8
          wm := v26
          size0 := v27
          half := v28
          two := v29
          rsize := v34
          rbase := v35
          kk := v36
          input := hin
          out := hout }
      pc := by
        simp only [hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5,
          hpc4, hpc3, hpc2, hpc1, hpc0]; rfl
      slot := by rw [v20, Nat.mod_eq_of_lt (by omega)]
      pos := le_rfl
      threads := fun i hi => by
        rw [count_one]
        have hb := (dvBase_bounds (by have := G.k2; omega) hi).1
        have room := G.room
        refine Or.inl ⟨initState (i :: x), rfl, Or.inr rfl, ?_⟩
        exact
          { pc := by rw [z _ (by simp only [dvCtx]; omega)]; rfl
            cur := by rw [z _ (by simp only [dvCtx]; omega)]; omega
            inp := by rw [z _ (by simp only [dvCtx]; omega)]; rfl
            oc := by rw [z _ (by simp only [dvCtx]; omega)]; rfl
            ocB := by simp [initState]
            alive := z _ (by simp only [dvCtx]; omega)
            buf := fun k hk => by simp [initState] at hk
            mem := fun a ha => by rw [z _ (by omega)]; rfl
            cword := fun a => by simp [initState]
            input := rfl } }

/-- The machine after `m` slots: the next slot is due, or it has
halted. -/
theorem dv_iter (G : DGlob w K B Q x) (m : ℕ) :
    ∃ n ≤ 16 + dvSC Q B * m + 7 * ∑ j ∈ Finset.range m, ruler (j + 1), ∃ S,
      Exec w (dvProg Q B K) n (initState x) S ∧
        (DInv w K B Q x (m + 1) S ∨ DHalt w K B Q x m S) := by
  induction m with
  | zero =>
      obtain ⟨S, e, hD⟩ := dv_init G
      exact ⟨16, by simp, S, e, Or.inl hD⟩
  | succ m ih =>
      obtain ⟨n, hn, S, e, hS⟩ := ih
      rw [Finset.sum_range_succ]
      rcases hS with hD | hH
      · obtain ⟨n', hn', S', e', hS'⟩ := dv_slot G hD
        refine ⟨n + n', by rw [Nat.mul_succ]; omega, S', e.trans e', ?_⟩
        rcases hS' with h | h
        · exact Or.inl h
        · exact Or.inr (h.mono (by have := hD.pos; omega))
      · exact ⟨n, by rw [Nat.mul_succ]; omega, S, e, Or.inr (hH.mono (by omega))⟩

/-- A live thread has made fewer steps than any accepting run takes. -/
theorem alive_lt {v c t : ℕ} {p : Program} {x' y : List ℕ} {s : State}
    (hrun : run v p c (initState x') = some s) (hpc : s.pc < p.length ∨ s.pc = 0)
    (hR : RunsTo v p x' (1 :: y) t) : c < t := by
  obtain ⟨k, sT, hk, hsT, hout, ht⟩ := hR
  by_contra hct
  rcases Nat.lt_or_ge k c with hkc | hkc
  · have : run v p c (initState x') = none := by
      rw [show c = k + ((c - k - 1) + 1) by omega, run_add, hk]
      exact run_succ_of_terminal hsT _
    rw [hrun] at this; cases this
  · have htc : terminalCost p sT = 0 := by omega
    have hck : c = k := by omega
    subst hck
    rw [hrun] at hk
    cases hk
    rw [terminalCost_eq] at htc
    split_ifs at htc with h
    rcases hpc with h1 | h1
    · omega
    · -- the empty program: the initial state is terminal
      have hp : p.length = 0 := by omega
      have h0 : step v p (initState x') = none := step_none_of_length_le (by simp [initState, hp])
      cases c with
      | zero =>
          simp only [run_zero, Option.some.injEq] at hrun
          rw [← hrun] at hout; simp [initState] at hout
      | succ c =>
          rw [run_succ, h0] at hrun; cases hrun

theorem sq_le_two_pow {w : ℕ} (h : 8 ≤ w) : w * w ≤ 2 ^ (w - 1) := by
  induction w, h using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
      rw [show w + 1 - 1 = (w - 1) + 1 by omega, pow_succ]
      nlinarith

/-- The size conditions follow from `i + K < w` for a large `K`. -/
theorem dvGlob_of {w K B : ℕ} {Q : Program} {x : List ℕ} (hK : dvR B + Q.length + 48 ≤ K)
    (hw : K < w) (hx : x.length < 2 ^ (w - 1)) : DGlob w K B Q x :=
  { kw := hw
    k2 := by omega
    room := by
      have := sq_le_two_pow (show 8 ≤ w by omega)
      have : (dvR B + 40) * w ≤ w * w := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    xlen := hx }

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec
open Lax185574Proofs.Ruler

/-- The constant of the dovetailer. -/
def dvK (Q : Program) (B : ℕ) : ℕ := 2 * (dvSC Q B + 7) + 17 + dvR B + Q.length + 48

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.RamSim
open Lax185574Proofs.Ruler

/-- **Dovetailer.** Thread `i` runs `Q` on `i :: x` at word length
`w - i - K`, in a fresh memory region that is never reused. Slots follow
the ruler sequence, so thread `i` gets every `2 ^ (i + 1)`-th slot at
`O(1)` amortized switching cost. A thread's writes go to a buffer of
`B + 1` words, and overflow retires the thread. A thread *accepts* if
it halts with output `1 :: y'`. The program `p` stops at the first
accepting thread and outputs its `y'`. That thread may be a thread `i'`
other than the given `i`, so the conclusion is existential in `i'`. The
accepting thread got its `t'` steps within the slots before the halt,
so `2 ^ i' * t' ≤ K * 2 ^ i * (t + 1)`. Threads whose word length would
be `0` are never started. -/
theorem dovetail :
    ∀ (B : ℕ) (Q : Program), ∃ (p : Program) (K : ℕ),
      ∀ (w : ℕ) (x : List ℕ) (i : ℕ) (y : List ℕ) (t : ℕ),
        i + K < w → x.length < 2 ^ (w - 1) → y.length ≤ B →
        RunsTo (w - i - K) Q (i :: x) (1 :: y) t →
        ∃ (i' : ℕ) (y' : List ℕ) (t' T : ℕ),
          i' + K < w ∧ y'.length ≤ B ∧
          RunsTo (w - i' - K) Q (i' :: x) (1 :: y') t' ∧
          2 ^ i' * t' ≤ K * 2 ^ i * (t + 1) ∧
          RunsTo w p x y' T ∧ T ≤ K * 2 ^ i * (t + 1) := by
  intro B Q
  refine ⟨dvProg Q B (dvK Q B), dvK Q B, fun w x i y t hi hx hy hrun => ?_⟩
  set K := dvK Q B
  have G : DGlob w K B Q x := dvGlob_of (by simp only [K, dvK]; omega) (by omega) hx
  have ht : 0 < t := alive_lt (c := 0) rfl (Or.inr rfl) hrun
  set m := 2 ^ i * (2 * (t - 1) + 1)
  obtain ⟨n, hn, S, e, hS⟩ := dv_iter G m
  rcases hS with hD | ⟨hhalt, I, y', t', hI, hy', hR', hout, hIt⟩
  · exfalso
    have hc : t - 1 + 1 ≤ count i (m + 1) := count_ge i (t - 1)
    rcases hD.threads i hi with ⟨s, hs, hpc, -⟩ | ⟨-, hnever⟩
    · have := alive_lt hs hpc hrun
      omega
    · exact hnever y t hy hrun
  · have hm6 : m ≤ 2 * 2 ^ i * t := by
      simp only [m]
      have : 2 * (t - 1) + 1 ≤ 2 * t := by omega
      calc 2 ^ i * (2 * (t - 1) + 1) ≤ 2 ^ i * (2 * t) := Nat.mul_le_mul_left _ this
        _ = 2 * 2 ^ i * t := by ring
    have hK6 : 6 ≤ K := by simp only [K, dvK]; omega
    refine ⟨I, y', t', n + 1, hI, hy', hR', ?_, ?_, ?_⟩
    · have : 6 * (2 ^ i * t) ≤ K * (2 ^ i * t) := Nat.mul_le_mul_right _ hK6
      have : K * (2 ^ i * t) ≤ K * 2 ^ i * (t + 1) := by
        rw [← mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_succ t)
      nlinarith
    · have := runsTo_of_exec e (step_halt hhalt) hout
      rwa [terminalCost_of_getElem? hhalt] at this
    · have hsum := sum_ruler_le m
      have hP : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      have hm : m ≤ 2 * 2 ^ i * t := by
        simp only [m]
        have : 2 * (t - 1) + 1 ≤ 2 * t := by omega
        calc 2 ^ i * (2 * (t - 1) + 1) ≤ 2 ^ i * (2 * t) := Nat.mul_le_mul_left _ this
          _ = 2 * 2 ^ i * t := by ring
      have h1 : n + 1 ≤ 17 + (dvSC Q B + 7) * m := by
        have : 7 * ∑ j ∈ Finset.range m, ruler (j + 1) ≤ 7 * m := Nat.mul_le_mul_left _ hsum
        nlinarith
      have h2 : (dvSC Q B + 7) * m ≤ (dvSC Q B + 7) * (2 * 2 ^ i * t) := Nat.mul_le_mul_left _ hm
      have h3 : 17 + (dvSC Q B + 7) * (2 * 2 ^ i * t) ≤ K * 2 ^ i * (t + 1) := by
        simp only [K, dvK]
        nlinarith
      omega

end Lax185574Proofs.Simulate
