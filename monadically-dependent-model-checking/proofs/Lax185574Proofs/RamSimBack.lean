import Lax185574Proofs.RamSimRun

/-!
Backward soundness of a simulation. If the simulating machine halts,
the simulated program has halted, within no more steps, unless it
overflowed its output buffer, which sends the machine into a loop.

The forward lemma `sim_run` follows a complete run of the simulated
program. Here every block is shown to take at least one machine step,
so that a partial run of `k` simulated steps costs at least `k` machine
steps (`sim_partial`). A machine that halts after `N` steps therefore
cannot have simulated `N + 1` steps, and the simulated run is complete
(`sim_back`).
-/

namespace Lax185574Proofs.RamExec

open Lax808846.Ram Lax808846Proofs.Machine

variable {w : ℕ} {p : Program}

/-- The machine halts from `S` after exactly `N` successful steps, in `S'`. -/
def Halts (w : ℕ) (p : Program) (S : State) (N : ℕ) (S' : State) : Prop :=
  run w p N S = some S' ∧ step w p S' = none

theorem run_none_of_halts {S S' : State} {N : ℕ} (h : Halts w p S N S') {n : ℕ} (hn : N < n) :
    run w p n S = none := by
  rw [show n = N + ((n - N - 1) + 1) by omega, run_add, h.1]
  exact run_succ_of_terminal h.2 _

/-- A halting machine makes at most `N` successful steps. -/
theorem Exec.le_of_halts {S S₁ S' : State} {N n : ℕ} (h : Halts w p S N S')
    (e : Exec w p n S S₁) : n ≤ N := by
  by_contra hn
  have := run_none_of_halts h (n := n) (by omega)
  rw [e] at this; cases this

/-- The rest of a halting run, after `n` of its steps. -/
theorem Halts.rest {S S₁ S' : State} {N n : ℕ} (h : Halts w p S N S') (e : Exec w p n S S₁) :
    Halts w p S₁ (N - n) S' := by
  have hn := e.le_of_halts h
  refine ⟨?_, h.2⟩
  have := h.1
  rw [show N = n + (N - n) by omega, run_add, e] at this
  exact this

/-- A state reached by a halting machine, from which a step is possible,
is reached strictly before the end. -/
theorem Exec.lt_of_halts {S S₁ S' : State} {N n : ℕ} (h : Halts w p S N S')
    (e : Exec w p n S S₁) (hs : step w p S₁ ≠ none) : n < N := by
  have hn := e.le_of_halts h
  rcases Nat.lt_or_ge n N with h1 | h1
  · exact h1
  · have hN : n = N := by omega
    subst hN
    have : S₁ = S' := by
      have := h.1; rw [e] at this; exact Option.some.inj this
    exact absurd (this ▸ h.2) hs

/-- A machine at an instruction `jump d` at address `d` never halts. -/
theorem not_halts_of_loop {S S' : State} {N d : ℕ} (hd : p[d]? = some (.jump d))
    (hpc : S.pc = d) : ¬ Halts w p S N S' := by
  intro h
  have hloop : ∀ m, run w p m S = some S := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [run_succ, step_eq, hpc, hd]
        show (some { S with pc := d }).bind (run w p m) = some S
        have : ({ S with pc := d } : State) = S := by cases S; simp_all
        rw [this]; exact ih
  have := run_none_of_halts h (n := N + 1) (by omega)
  rw [hloop] at this; cases this

/-- A run that cannot make `N + 1` steps ends in a terminal state within
`N` steps. -/
theorem exists_terminal {v : ℕ} {q : Program} :
    ∀ (N : ℕ) (s : State), run v q (N + 1) s = none →
      ∃ j ≤ N, ∃ s', run v q j s = some s' ∧ step v q s' = none := by
  intro N
  induction N with
  | zero =>
      intro s h
      refine ⟨0, le_rfl, s, rfl, ?_⟩
      rw [run_succ] at h
      cases hs : step v q s with
      | none => rfl
      | some t => rw [hs] at h; cases h
  | succ N ih =>
      intro s h
      rw [run_succ] at h
      cases hs : step v q s with
      | none => exact ⟨0, by omega, s, rfl, hs⟩
      | some t =>
          rw [hs] at h
          obtain ⟨j, hj, s', h1, h2⟩ := ih t h
          exact ⟨j + 1, by omega, s', by rw [run_succ, hs]; exact h1, h2⟩

theorem run_prefix {v : ℕ} {q : Program} {s u : State} {j : ℕ}
    (h : run v q (j + 1) s = some u) : ∃ s', run v q j s = some s' ∧ step v q s' = some u := by
  cases hj : run v q j s with
  | none =>
      rw [show j + 1 = j + 1 by rfl, run_add, hj] at h; cases h
  | some s' =>
      refine ⟨s', rfl, ?_⟩
      rw [run_add, hj, Option.bind_some, run_succ] at h
      cases hs : step v q s' with
      | none => rw [hs] at h; cases h
      | some t => rw [hs] at h; exact h

theorem run_le {v : ℕ} {q : Program} {s u : State} {j k : ℕ} (hjk : j ≤ k)
    (h : run v q k s = some u) : ∃ s', run v q j s = some s' := by
  rw [show k = j + (k - j) by omega, run_add] at h
  cases hj : run v q j s with
  | none => rw [hj] at h; cases h
  | some s' => exact ⟨s', rfl⟩

end Lax185574Proofs.RamExec

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec

variable {w : ℕ} {p : Program}
variable {g : Geo} {x' out₀ : List ℕ}

/-! ### Every block takes a step -/

theorem jzero_spec_pos {ks : List SegKind} {tb : ℕ} {mode : OutMode} {s S : State} {A : ℕ}
    {a l l' : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (ldCode rB a ++ [.jzero rB l, .jump l'])) :
    ∃ n, 1 ≤ n ∧ n ≤ 6 ∧ Reaches w p g ks tb mode x' out₀ n S
      (if s.mem (a % 2 ^ g.v) = 0 then l else l') s := by
  obtain ⟨hf1, hf2⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have hav : a % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  obtain ⟨S1, e1, hpc1, hB1, -, t1, E1⟩ := ld_spec' E hf1 hpc (V := rB) (by omega)
  have hB1' : S1.mem rB = s.mem (a % 2 ^ g.v) := by rw [hB1, R.mem _ hav]
  have R1 := R.tempsOnly t1 E1.word
  by_cases h0 : s.mem (a % 2 ^ g.v) = 0
  · have e := e1.trans (x_jzero_pos (fetch hf2 (i := 0) (by simp [hpc1]) rfl) (by omega)
      (by rw [hB1', h0]))
    exact ⟨4 + 1, by omega, by omega, _, e, by simp [h0], R1.tempsOnly TempsOnly.setPc E1.word,
      (t1.trans TempsOnly.setPc).frame⟩
  · have e := (e1.trans (x_jzero_neg (fetch hf2 (i := 0) (by simp [hpc1]) rfl) (by omega)
      (by rw [hB1']; exact h0))).trans (x_jump (fetch hf2 (i := 1) (by simp [hpc1]) rfl))
    exact ⟨4 + 1 + 1, by omega, by omega, _, e, by simp [h0],
      R1.tempsOnly TempsOnly.setPc E1.word, (t1.trans TempsOnly.setPc).frame⟩

theorem jeof_spec_pos {ks : List SegKind} {tb : ℕ} {mode : OutMode} {s S : State} {A : ℕ}
    {l l' : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A [.sub rU rTot rCur, .jzero rU l, .jump l']) :
    ∃ n, 1 ≤ n ∧ n ≤ 3 ∧
      Reaches w p g ks tb mode x' out₀ n S (if s.inp.isEmpty then l else l') s := by
  have E := R.env
  have hw := E.hw
  have e1 := x_sub (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) E.word (by omega)
    (by omega) (by omega)
  obtain ⟨S1, e1, hS1⟩ := (⟨_, e1, rfl⟩ : ∃ S', Exec w p 1 S S' ∧ S' = _)
  have t1 : TempsOnly S S1 := by subst hS1; exact TempsOnly.update (by omega)
  have hU : S1.mem rU = x'.length - S.mem rCur := by subst hS1; simp [R.tot]
  have hpc1 : S1.pc = A + 1 := by subst hS1; simp [hpc]
  have R1 := R.tempsOnly t1 (E.word.exec e1)
  have hm1 := E.word.exec e1
  have hcur := R.cur
  have hemp : s.inp.isEmpty ↔ x'.length - S.mem rCur = 0 := by
    rw [R.inp, List.isEmpty_iff, List.drop_eq_nil_iff]; omega
  by_cases h0 : s.inp.isEmpty
  · have e := e1.trans (x_jzero_pos (fetch hf (i := 1) (by simp [hpc1]) rfl) (by omega)
      (by rw [hU]; exact hemp.1 h0))
    exact ⟨1 + 1, by omega, by omega, _, e, by simp [h0], R1.tempsOnly TempsOnly.setPc hm1,
      (t1.trans TempsOnly.setPc).frame⟩
  · have e := (e1.trans (x_jzero_neg (fetch hf (i := 1) (by simp [hpc1]) rfl) (by omega)
      (by rw [hU]; exact fun h => h0 (hemp.2 h)))).trans
        (x_jump (fetch hf (i := 2) (by simp [hpc1]) rfl))
    exact ⟨1 + 1 + 1, by omega, by omega, _, e, by simp [h0], R1.tempsOnly TempsOnly.setPc hm1,
      (t1.trans TempsOnly.setPc).frame⟩

/-- The first instruction of a block always makes a step. -/
theorem instrCode_head (C : Code) (A i : ℕ) (ins : Instr) :
    ∃ ins₀, (instrCode C A i ins)[0]? = some ins₀ ∧ ∀ v s, ins₀.effect v s ≠ none := by
  cases ins <;> simp [instrCode, binCode, ldCode, addrCode, readCode, Instr.effect]
  cases C.mode <;> simp

/-- A machine at the start of a block can make a step. -/
theorem step_block_start (C : Code) {p₀ pre post : Program} {H L : ℕ}
    (hp : p = pre ++ blocks C H L p₀ ++ post) (hpre : pre.length = H) (hL : blockLen C.ks ≤ L)
    {i : ℕ} (hi : i < p₀.length) {S : State} (hpc : S.pc = H + L * i) :
    step w p S ≠ none := by
  obtain ⟨ins, hins⟩ : ∃ ins, p₀[i]? = some ins := ⟨_, List.getElem?_eq_getElem hi⟩
  have hf : Fits p (H + L * i) (instrCode C (H + L * i) i ins) := by
    rw [hp]; exact blocks_fits C hL hpre (post := post) hins
  obtain ⟨ins₀, h0, hne⟩ := instrCode_head C (H + L * i) i ins
  have hlen : 0 < (instrCode C (H + L * i) i ins).length := by
    rcases List.getElem?_eq_some_iff.mp h0 with ⟨h, -⟩; exact h
  have := hf 0 hlen
  rw [Nat.add_zero, h0] at this
  rw [step_eq, hpc, this]
  simpa using hne w S

/-- The simulation of one successful step takes at least one machine step. -/
theorem block_step_pos (C : Code) {p₀ pre post : Program} {H L : ℕ}
    (hp : p = pre ++ blocks C H L p₀ ++ post) (hpre : pre.length = H) (hL : blockLen C.ks ≤ L)
    (htgt : ∀ l, C.tgt l = if l < p₀.length then H + L * l else C.exit)
    (hexit : H + L * p₀.length ≤ C.exit)
    {s s' S : State} (R : Rel w g C.ks C.tb C.mode x' out₀ s S) (hpc : S.pc = C.tgt s.pc)
    (hst : step g.v p₀ s = some s')
    (hcap : ∀ ovf, C.mode = .buffer ovf → s'.out.length ≤ g.cap) :
    ∃ n, 1 ≤ n ∧ n ≤ stepBound C.ks ∧
      Reaches w p g C.ks C.tb C.mode x' out₀ n S (C.tgt s'.pc) s' := by
  have hst' := hst
  rw [step_eq] at hst'
  cases hins : p₀[s.pc]? with
  | none => simp [hins] at hst'
  | some ins =>
      simp only [hins, Option.bind_some] at hst'
      have hlt : s.pc < p₀.length := (List.getElem?_eq_some_iff.mp hins).1
      have hA : S.pc = H + L * s.pc := by rw [hpc, htgt, if_pos hlt]
      have hf := hp ▸ blocks_fits C hL hpre (post := post) hins
      have hL16 : 16 ≤ L := le_trans (by simp [blockLen]) hL
      -- targets of other counters differ from the start of this block
      have hne : ∀ l, l ≠ s.pc → C.tgt l ≠ H + L * s.pc := by
        intro l hl
        rw [htgt]
        split_ifs with h
        · intro heq
          have : L * l = L * s.pc := by omega
          exact hl (Nat.eq_of_mul_eq_mul_left (by omega) this)
        · have : L * s.pc + L ≤ L * p₀.length := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
          omega
      have B := block_spec C R hA hf
      obtain ⟨n, hn, h⟩ := B.1 s' hst' hcap
      by_cases hn0 : 1 ≤ n
      · exact ⟨n, hn0, hn, h⟩
      · -- no step: the target is this block, so the instruction loops on itself
        have hn0 : n = 0 := by omega
        subst hn0
        obtain ⟨S', e, hpc', -, -⟩ := h
        have hSS : S' = S := by
          have := e; simp only [Exec, run_zero, Option.some.injEq] at this; exact this.symm
        have hsame : s'.pc = s.pc := by
          by_contra hc
          exact hne _ hc (by rw [← hpc', hSS, hA])
        cases ins with
        | jump l =>
            rw [effect_jump] at hst'; cases hst'
            exact ⟨1, le_rfl, by simp [stepBound], (jump_spec R hA hf).setPc _⟩
        | jzero a l =>
            rw [effect_jzero_eq] at hst'; cases hst'
            obtain ⟨m, hm1, hm2, hr⟩ := jzero_spec_pos R hA hf
            refine ⟨m, hm1, by simp [stepBound]; omega, ?_⟩
            have hr' := hr.setPc (if s.mem (a % 2 ^ g.v) = 0 then l else s.pc + 1)
            split_ifs at hr' ⊢ <;> exact hr'
        | jeof l =>
            rw [effect_jeof] at hst'; cases hst'
            obtain ⟨m, hm1, hm2, hr⟩ := jeof_spec_pos R hA hf
            refine ⟨m, hm1, by simp [stepBound]; omega, ?_⟩
            have hr' := hr.setPc (if s.inp.isEmpty then l else s.pc + 1)
            split_ifs at hr' ⊢ <;> exact hr'
        | halt => rw [effect_halt] at hst'; cases hst'
        | read a =>
            rw [effect_read_eq] at hst'
            cases hi : s.inp.head? with
            | none => rw [hi] at hst'; cases hst'
            | some u =>
                rw [hi] at hst'; simp only [Option.map_some, Option.some.injEq] at hst'
                subst hst'; simp at hsame
        | _ =>
            first
              | (rw [effect_set] at hst'; cases hst'; simp at hsame)
              | (rw [effect_load_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_store_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_add_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_sub_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_mul_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_div_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_and_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_shiftl_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_not_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_inputLength] at hst'; cases hst'; simp at hsame)
              | (rw [effect_inputLoad_eq] at hst'; cases hst'; simp at hsame)
              | (rw [effect_write_eq] at hst'; cases hst'; simp at hsame)

/-! ### Partial runs -/

/-- `k` simulated steps cost at least `k` and at most `stepBound · k`
machine steps. -/
theorem sim_partial (C : Code) {p₀ pre post : Program} {H L : ℕ}
    (hp : p = pre ++ blocks C H L p₀ ++ post) (hpre : pre.length = H) (hL : blockLen C.ks ≤ L)
    (htgt : ∀ l, C.tgt l = if l < p₀.length then H + L * l else C.exit)
    (hexit : H + L * p₀.length ≤ C.exit) :
    ∀ (k : ℕ) (s s_k S : State), run g.v p₀ k s = some s_k →
      (∀ ovf, C.mode = .buffer ovf → s_k.out.length ≤ g.cap) →
      Rel w g C.ks C.tb C.mode x' out₀ s S → S.pc = C.tgt s.pc →
      ∃ n, k ≤ n ∧ n ≤ stepBound C.ks * k ∧
        Reaches w p g C.ks C.tb C.mode x' out₀ n S (C.tgt s_k.pc) s_k := by
  intro k
  induction k with
  | zero =>
      intro s s_k S hr _ R hpc
      cases hr
      exact ⟨0, le_rfl, by simp, S, Exec.refl S, hpc, R, Frame.refl g S⟩
  | succ k ih =>
      intro s s_k S hr hcap R hpc
      rw [run_succ] at hr
      cases hst : step g.v p₀ s with
      | none => simp [hst] at hr
      | some s₁ =>
          rw [hst] at hr
          have hcap₁ : ∀ ovf, C.mode = .buffer ovf → s₁.out.length ≤ g.cap := by
            intro ovf hm
            have := (run_out_prefix hr).length_le
            have := hcap ovf hm
            omega
          obtain ⟨n₁, h1, hn₁, S₁, e₁, hpc₁, R₁, fr₁⟩ :=
            block_step_pos C hp hpre hL htgt hexit R hpc hst hcap₁
          obtain ⟨n₂, h2, hn₂, S₂, e₂, hpc₂, R₂, fr₂⟩ := ih s₁ s_k S₁ hr hcap R₁ hpc₁
          refine ⟨n₁ + n₂, by omega, ?_, S₂, e₁.trans e₂, hpc₂, R₂, fr₁.trans fr₂⟩
          rw [Nat.mul_succ]; omega

/-- In buffer mode with a looping overflow handler, a halting machine
never overflows the buffer. -/
theorem sim_no_overflow (C : Code) {p₀ pre post : Program} {H L : ℕ}
    (hp : p = pre ++ blocks C H L p₀ ++ post) (hpre : pre.length = H) (hL : blockLen C.ks ≤ L)
    (htgt : ∀ l, C.tgt l = if l < p₀.length then H + L * l else C.exit)
    (hexit : H + L * p₀.length ≤ C.exit) {ovf : ℕ} (hmode : C.mode = .buffer ovf)
    (hloop : p[ovf]? = some (.jump ovf))
    {s S S_end : State} {N : ℕ} (R : Rel w g C.ks C.tb C.mode x' out₀ s S)
    (hpc : S.pc = C.tgt s.pc) (hH : Halts w p S N S_end) :
    ∀ (j : ℕ) (s_j : State), run g.v p₀ j s = some s_j → s_j.out.length ≤ g.cap := by
  intro j
  induction j with
  | zero =>
      intro s_j h
      cases h
      have R' : Rel w g C.ks C.tb (.buffer ovf) x' out₀ s S := hmode ▸ R
      exact R'.out_le
  | succ j ih =>
      intro s_j h
      obtain ⟨s', h1, h2⟩ := run_prefix h
      have hc := ih s' h1
      by_contra hlt
      push Not at hlt
      obtain ⟨n, -, -, S', e, hpc', R', -⟩ := sim_partial C hp hpre hL htgt hexit j s s' S h1
        (fun _ _ => hc) R hpc
      -- the step from `s'` overflows
      have h2' := h2
      rw [step_eq] at h2'
      cases hins : p₀[s'.pc]? with
      | none => simp [hins] at h2'
      | some ins =>
          simp only [hins, Option.bind_some] at h2'
          have hlt' : s'.pc < p₀.length := (List.getElem?_eq_some_iff.mp hins).1
          have hA : S'.pc = H + L * s'.pc := by rw [hpc', htgt, if_pos hlt']
          have hf := hp ▸ blocks_fits C hL hpre (post := post) hins
          obtain ⟨m, -, S'', e', hpc'', -, -⟩ := (block_spec C R' hA hf).2.2 s_j ovf hmode h2' hlt
          exact not_halts_of_loop hloop hpc'' ((hH.rest e).rest e')

/-- **Backward soundness of a simulation.** If the machine, started in
a state representing `s` at the block of its counter, halts after `N`
steps, then the simulated program halts from `s` within `j` steps with
`j + terminalCost ≤ N`. In buffer mode the overflow handler must loop. -/
theorem sim_back (C : Code) {p₀ pre post : Program} {H L : ℕ}
    (hp : p = pre ++ blocks C H L p₀ ++ post) (hpre : pre.length = H) (hL : blockLen C.ks ≤ L)
    (htgt : ∀ l, C.tgt l = if l < p₀.length then H + L * l else C.exit)
    (hexit : H + L * p₀.length ≤ C.exit)
    (hloop : ∀ ovf, C.mode = .buffer ovf → p[ovf]? = some (.jump ovf))
    {s S S_end : State} {N : ℕ} (R : Rel w g C.ks C.tb C.mode x' out₀ s S)
    (hpc : S.pc = C.tgt s.pc) (hH : Halts w p S N S_end) :
    ∃ j s_j, run g.v p₀ j s = some s_j ∧ step g.v p₀ s_j = none ∧
      j + terminalCost p₀ s_j ≤ N ∧ (∀ ovf, C.mode = .buffer ovf → s_j.out.length ≤ g.cap) := by
  have hcapAll : ∀ (j : ℕ) (s_j : State), run g.v p₀ j s = some s_j →
      ∀ ovf, C.mode = .buffer ovf → s_j.out.length ≤ g.cap := by
    intro j s_j h ovf hm
    exact sim_no_overflow C hp hpre hL htgt hexit hm (hloop ovf hm) R hpc hH j s_j h
  cases hN : run g.v p₀ (N + 1) s with
  | some s' =>
      exfalso
      obtain ⟨n, hn, -, S', e, -⟩ := sim_partial C hp hpre hL htgt hexit (N + 1) s s' S hN
        (hcapAll _ _ hN) R hpc
      have := e.le_of_halts hH
      omega
  | none =>
      obtain ⟨j, hj, s_j, h1, h2⟩ := exists_terminal N s hN
      refine ⟨j, s_j, h1, h2, ?_, hcapAll j s_j h1⟩
      obtain ⟨n, hn, -, S', e, hpc', -⟩ := sim_partial C hp hpre hL htgt hexit j s s_j S h1
        (hcapAll _ _ h1) R hpc
      rw [terminalCost_eq]
      split_ifs with hlt
      · have := e.lt_of_halts hH (step_block_start C hp hpre hL hlt (by rw [hpc', htgt, if_pos hlt]))
        omega
      · have := e.le_of_halts hH
        omega

end Lax185574Proofs.RamSim
