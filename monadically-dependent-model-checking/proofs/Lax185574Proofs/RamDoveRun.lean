import Lax185574Proofs.RamDoveHead

/-!
The middle of a slot of the dovetailer: dispatch to the block of the
thread's next instruction, run it, and record the next counter.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.Ruler

variable {w K B : ℕ} {Q : Program} {x : List ℕ}

theorem getElem?_pairs (n : ℕ) (f : ℕ → Program) (hf : ∀ l, (f l).length = 2)
    {m k : ℕ} (hm : m < n) (hk : k < 2) :
    ((List.range n).map f).flatten[2 * m + k]? = (f m)[k]? := by
  rw [getElem?_flatten_uniform (L := 2) _ (fun b hb => by
    simp only [List.mem_map] at hb; obtain ⟨l, -, rfl⟩ := hb; exact hf l) m k hk]
  simp [List.getElem?_range hm]

theorem dv_fits_disp_at {m : ℕ} (hm : m < Q.length) :
    Fits (dvProg Q B K) (dvDisp + 2 * m) [.jzero rD (dvH Q + dvL * m), .sub rD rD rOne] := by
  have hf := dv_fits_disp Q B K
  have h0 := hf (2 * m) (by simp; omega)
  have h1 := hf (2 * m + 1) (by simp; omega)
  rw [dvDispatch, List.getElem?_append_left (by
    rw [length_flatten_pairs _ _ (fun _ => rfl)]; omega)] at h0 h1
  have g0 := getElem?_pairs (Q.length) (fun l => [Instr.jzero rD (dvH Q + dvL * l),
    Instr.sub rD rD rOne]) (fun _ => rfl) hm (by norm_num : 0 < 2)
  rw [Nat.add_zero] at g0
  rw [g0] at h0
  rw [getElem?_pairs _ _ (fun _ => rfl) hm (by norm_num : 1 < 2)] at h1
  refine fits_cons.2 ⟨by simpa using h0, fits_cons.2 ⟨by
    rw [show dvDisp + 2 * m + 1 = dvDisp + (2 * m + 1) by omega]; simpa using h1,
    fun i hi => by simp at hi⟩⟩

theorem dv_fits_disp_end : Fits (dvProg Q B K) (dvDisp + 2 * Q.length) [.jump (dvExit Q)] := by
  have hf := dv_fits_disp Q B K
  have h0 := hf (2 * Q.length) (by simp)
  rw [dvDispatch, List.getElem?_append_right (by
    rw [length_flatten_pairs _ _ (fun _ => rfl)]), length_flatten_pairs _ _ (fun _ => rfl),
    Nat.sub_self] at h0
  exact fits_singleton.2 h0

theorem dv_disp_loop (G : DGlob w K B Q x) {d : ℕ} {S : State} (hpc : S.pc = dvDisp)
    (hD : S.mem rD = d) (hm : WordMem w S.mem) (h1 : S.mem rOne = 1) :
    ∀ m, m ≤ d → m ≤ Q.length → ∃ S', Exec w (dvProg Q B K) (2 * m) S S' ∧
      S'.pc = dvDisp + 2 * m ∧ S'.mem rD = d - m ∧ TempsOnly S S' := by
  have hw := G.hw
  intro m
  induction m with
  | zero => intro _ _; exact ⟨S, Exec.refl S, by simp [hpc], by simp [hD], TempsOnly.refl S⟩
  | succ m ih =>
      intro hmd hmQ
      obtain ⟨S1, e1, hpc1, hD1, t1⟩ := ih (by omega) (by omega)
      have hf := dv_fits_disp_at (B := B) (K := K) (show m < Q.length by omega)
      have e2 := x_jzero_neg (w := w) (s := S1) (fetch hf (i := 0) (by simp [hpc1]) rfl)
        (by omega) (by rw [hD1]; omega)
      obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_sub (w := w) (s := { S1 with pc := S1.pc + 1 })
        (fetch hf (i := 1) (by simp [hpc1]) rfl) (show WordMem w S1.mem from hm.exec e1)
        (by omega) (by omega) (by omega)).upd
      refine ⟨S3, (e1.trans (e2.trans e3)).cast (by ring), by rw [hpc3]; simp [hpc1]; ring,
        ?_, t1.trans ⟨fun a ha => ?_, hi3, hn3, ho3⟩⟩
      · rw [hm3, if_pos rfl]
        show S1.mem rD - S1.mem rOne = _
        rw [hD1, t1.1 _ (by omega), h1]; omega
      · rw [hm3, if_neg (by omega)]

/-- Dispatch: jump to the block of the thread's counter, or to the exit
handler if the counter is out of range. -/
theorem dv_dispatch (G : DGlob w K B Q x) {j I c : ℕ} {s S : State}
    (h : Running w K B Q x j I c s S) (hpc : S.pc = dvDisp) (hD : S.mem rD = s.pc) :
    (s.pc < Q.length → ∃ S', Exec w (dvProg Q B K) (2 * s.pc + 1) S S' ∧
      S'.pc = dvH Q + dvL * s.pc ∧ Running w K B Q x j I c s S') ∧
    (Q.length ≤ s.pc → ∃ S', Exec w (dvProg Q B K) (2 * Q.length + 1) S S' ∧
      S'.pc = dvExit Q ∧ Running w K B Q x j I c s S') := by
  have hw := G.hw
  have hm := h.const.word
  have run_of := fun (S' : State) (t : TempsOnly S S') (hW : WordMem w S'.mem) =>
    h.step G (TempsOnly.frame t) (h.rel.tempsOnly t hW)
  constructor
  · intro hlt
    obtain ⟨S1, e1, hpc1, hD1, t1⟩ := dv_disp_loop G hpc hD hm h.const.one s.pc le_rfl hlt.le
    have hf := dv_fits_disp_at (B := B) (K := K) hlt
    have e2 := x_jzero_pos (w := w) (s := S1) (fetch hf (i := 0) (by simp [hpc1]) rfl)
      (by omega) (by rw [hD1]; omega)
    refine ⟨_, e1.trans e2, rfl, run_of _ (t1.trans TempsOnly.setPc)
      (show WordMem w S1.mem from hm.exec e1)⟩
  · intro hge
    obtain ⟨S1, e1, hpc1, hD1, t1⟩ := dv_disp_loop G hpc hD hm h.const.one Q.length hge le_rfl
    have e2 := x_jump (w := w) (s := S1) (fetch (dv_fits_disp_end (Q := Q) (B := B) (K := K)) (i := 0)
      (by simp [hpc1]) rfl)
    exact ⟨_, e1.trans e2, rfl, run_of _ (t1.trans TempsOnly.setPc)
      (show WordMem w S1.mem from hm.exec e1)⟩

/-- A thread's representation only depends on the cells below 20, its
memory and its buffer. -/
theorem Rel.frame_dv {g : Geo} {mode : OutMode} {x' out₀ : List ℕ} {s S S' : State}
    (R : Rel w g dvKs 16 mode x' out₀ s S)
    (h : ∀ a, a < 20 ∨ (g.base ≤ a ∧ a < g.base + 2 ^ g.v) ∨ (g.ob ≤ a ∧ a < g.ob + g.cap) →
      S'.mem a = S.mem a) (hw : WordMem w S'.mem) (hi : S'.input = S.input)
    (ho : S'.out = S.out) : Rel w g dvKs 16 mode x' out₀ s S' := by
  have E := R.env
  obtain ⟨segs, hT, hx⟩ := R.table
  have hT' : TableOK w g.W S' dvKs 16 segs := by
    match segs, hT with
    | [s0, s1], ⟨a1, a2, a3, a4, a5, a6, _⟩ =>
      refine ⟨a1, a2, ?_, a4, a5, ?_, trivial⟩
      · rw [h 16 (Or.inl (by omega)), h 17 (Or.inl (by omega))]; exact a3
      · rw [h 18 (Or.inl (by omega)), h 19 (Or.inl (by omega))]
        simpa only [SegOK, hi] using a6
  refine
    { env := ⟨hw, by rw [h _ (Or.inl (by omega))]; exact E.zero,
        by rw [h _ (Or.inl (by omega))]; exact E.one, by rw [h _ (Or.inl (by omega))]; exact E.mask,
        by rw [h _ (Or.inl (by omega))]; exact E.baseCell, E.room, E.low, E.hv⟩
      cword := R.cword
      mem := fun a ha => by rw [h _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact R.mem a ha
      input := R.input
      cur := by rw [h _ (Or.inl (by omega))]; exact R.cur
      inp := by rw [h _ (Or.inl (by omega))]; exact R.inp
      tot := by rw [h _ (Or.inl (by omega))]; exact R.tot
      table := ⟨segs, hT', hx⟩
      tb16 := R.tb16
      tbw := R.tbw
      out := ?_ }
  have ho' := R.out
  cases mode with
  | direct => simp only [OutRel] at ho' ⊢; rw [ho, ho']
  | buffer ovf =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho'
      refine ⟨ho.trans h1, by rw [h _ (Or.inl (by omega))]; exact h2,
        by rw [h _ (Or.inl (by omega))]; exact h3, by rw [h _ (Or.inl (by omega))]; exact h4,
        h5, h6, h7, h8, fun k hk => ?_⟩
      rw [h _ (Or.inr (Or.inr ⟨by omega, by omega⟩))]; exact h9 k hk

theorem dv_fits_stub_at {l : ℕ} (hl : l < Q.length) :
    Fits (dvProg Q B K) (dvStub Q + 2 * l) [.set 25 l, .jump (dvSave Q)] := by
  have hf := dv_fits_stubs Q B K
  have h0 := hf (2 * l) (by simp; omega)
  have h1 := hf (2 * l + 1) (by simp; omega)
  have g0 := getElem?_pairs (Q.length) (fun l => [Instr.set 25 l, Instr.jump (dvSave Q)])
    (fun _ => rfl) hl (by norm_num : 0 < 2)
  rw [Nat.add_zero] at g0
  rw [dvStubs, g0] at h0
  rw [dvStubs, getElem?_pairs _ _ (fun _ => rfl) hl (by norm_num : 1 < 2)] at h1
  refine fits_cons.2 ⟨by simpa using h0, fits_cons.2 ⟨by
    rw [show dvStub Q + 2 * l + 1 = dvStub Q + (2 * l + 1) by omega]; simpa using h1,
    fun i hi => by simp at hi⟩⟩

/-- Writing the saved-counter cell keeps the running thread. -/
theorem Running.update25 (G : DGlob w K B Q x) {j I c : ℕ} {s S S' : State}
    (h : Running w K B Q x j I c s S) (hfr : ∀ a, a ≠ 25 → S'.mem a = S.mem a)
    (hW : WordMem w S'.mem) (hi : S'.input = S.input) (ho : S'.out = S.out) :
    Running w K B Q x j I c s S' := by
  have hI := h.valid
  have hb := (dvBase_bounds (by have := G.k2; omega) hI).1
  have room := G.room
  exact
    { const := h.const.frame (fun a ha => hfr a (by simp only [DConstCell] at ha; omega)) hW hi ho
      slot := by rw [hfr 20 (by omega)]; exact h.slot
      pos := h.pos
      thr := h.thr
      valid := hI
      ctx := by rw [hfr 24 (by omega)]; exact h.ctx
      cnt := h.cnt
      rel := h.rel.frame_dv (fun a ha => hfr a (by
        rcases ha with ha | ha | ha
        · omega
        · simp only [dvGeo] at ha; omega
        · simp only [dvGeo, dvCtx] at ha; omega)) hW hi ho
      alive := by rw [hfr _ (by simp only [dvCtx]; omega)]; exact h.alive
      others := fun i hi' hne => (h.others i hi' hne).frame (fun a ha => hfr a (by
        have := dv_area_ge G hi' ha; omega)) }

/-- Record the counter of the thread's next instruction. -/
theorem dv_stub (G : DGlob w K B Q x) {j I c : ℕ} {s S : State}
    (h : Running w K B Q x j I c s S) (hpc : S.pc = dvStub Q + 2 * s.pc)
    (hlt : s.pc < Q.length) :
    ∃ S', Exec w (dvProg Q B K) 2 S S' ∧ S'.pc = dvSave Q ∧ S'.mem 25 = s.pc ∧
      Running w K B Q x j I c s S' := by
  have hw := G.hw
  have hK := G.k2
  have hKw := G.kw
  have hwlt : w < 2 ^ w := Nat.lt_two_pow_self
  have hf := dv_fits_stub_at (B := B) (K := K) hlt
  obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_set (w := w) (s := S)
    (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)).upd
  have e2 := x_jump (w := w) (s := S1) (fetch hf (i := 1) (by simp [hpc1, hpc]) rfl)
  have hfr : ∀ a, a ≠ 25 → S1.mem a = S.mem a := fun a ha => by rw [hm1, if_neg ha]
  have hW1 := h.const.word.exec e1
  refine ⟨_, e1.trans e2, rfl, by
    show S1.mem 25 = _; rw [hm1, if_pos rfl, Nat.mod_eq_of_lt (by omega)],
    h.update25 G (S' := { S1 with pc := dvSave Q }) hfr hW1 hi1 ho1⟩

theorem run_succ_last {v c : ℕ} {p : Program} {s0 s : State} (h : run v p c s0 = some s) :
    run v p (c + 1) s0 = step v p s := by
  rw [run_add, h]
  show run v p 1 s = step v p s
  rw [run_succ]; cases step v p s <;> rfl

/-- A run that has written more than `B + 1` words has no accepting run
with a short output. -/
theorem no_short_accept {v c B : ℕ} {p : Program} {x' : List ℕ} {s : State}
    (hrun : run v p c (initState x') = some s) (hlong : B + 1 < s.out.length) :
    ∀ y t, y.length ≤ B → ¬ RunsTo v p x' (1 :: y) t := by
  intro y t hy ⟨k, sT, hk, hsT, hout, _⟩
  rcases Nat.lt_or_ge k c with hkc | hkc
  · have : run v p c (initState x') = none := by
      rw [show c = k + ((c - k - 1) + 1) by omega, run_add, hk]
      exact run_succ_of_terminal hsT _
    rw [hrun] at this; cases this
  · have h2 : run v p (c + (k - c)) (initState x') = some sT := by
      rw [show c + (k - c) = k by omega]; exact hk
    rw [run_add, hrun] at h2
    have := (run_out_prefix h2).length_le
    rw [hout] at this
    simp at this; omega

/-- A terminated thread whose output does not start with `1`, or is too
long, has no accepting run with a short output. -/
theorem no_accept_of_terminal {v c B : ℕ} {p : Program} {x' : List ℕ} {s : State}
    (hrun : run v p c (initState x') = some s) (hs : step v p s = none)
    (hno : ∀ y, y.length ≤ B → s.out ≠ 1 :: y) :
    ∀ y t, y.length ≤ B → ¬ RunsTo v p x' (1 :: y) t := by
  intro y t hy hR
  have hR' : RunsTo v p x' s.out (c + terminalCost p s) := runsTo_of_exec hrun hs rfl
  exact hno y hy (runsTo_unique hR' hR).1

/-- What a dead thread leaves behind: everything a retirement needs. -/
structure Dying (w K B : ℕ) (Q : Program) (x : List ℕ) (j I : ℕ) (S : State) : Prop where
  const : DConst w K B x S
  slot : S.mem 20 = j % 2 ^ w
  pos : 1 ≤ j
  thr : ruler j = I
  valid : I + K < w
  ctx : S.mem 24 = dvCtx B I
  others : ∀ i, i + K < w → i ≠ I → TInv w K B Q x i (count i j) S
  never : ∀ y t, y.length ≤ B → ¬ RunsTo (w - I - K) Q (I :: x) (1 :: y) t

/-- Run the block of the thread's next instruction. -/
theorem dv_exec (G : DGlob w K B Q x) {j I c : ℕ} {s S : State}
    (h : Running w K B Q x j I c s S) (hpc : S.pc = dvH Q + dvL * s.pc) (hlt : s.pc < Q.length)
    (hrun : run (w - I - K) Q c (initState (I :: x)) = some s) :
    ∃ n ≤ stepBound dvKs + 2, ∃ S', Exec w (dvProg Q B K) n S S' ∧
      ((∃ s', run (w - I - K) Q (c + 1) (initState (I :: x)) = some s' ∧ s'.pc < Q.length ∧
          S'.pc = dvSave Q ∧ S'.mem 25 = s'.pc ∧ Running w K B Q x j I c s' S') ∨
       (∃ c' s', c' ≤ c + 1 ∧ run (w - I - K) Q c' (initState (I :: x)) = some s' ∧
          step (w - I - K) Q s' = none ∧ S'.pc = dvExit Q ∧ Running w K B Q x j I c s' S') ∨
       (S'.pc = dvDead Q ∧ Dying w K B Q x j I S')) := by
  have hI := h.valid
  have hv : w - I - K = (dvGeo w K B I).v := by simp only [dvGeo]; omega
  obtain ⟨ins, hins⟩ : ∃ ins, Q[s.pc]? = some ins := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hf := blocks_fits (dvCode Q) (le_refl dvL) (dv_pre_length Q B K)
    (post := dvStubs Q ++ dvSaveCode ++ dvSkipCode ++ dvDeadCode ++ dvExitCode Q) hins
  rw [← dv_prog_blocks] at hf
  have Bk := block_spec (dvCode Q) (p := dvProg Q B K) h.rel hpc hf
  have hstep : step (w - I - K) Q s = ins.effect (w - I - K) s := by
    rw [step_eq, hins]; rfl
  have hrun1 := run_succ_last hrun
  rw [hstep] at hrun1
  rw [hv] at hstep hrun1
  cases heff : ins.effect (dvGeo w K B I).v s with
  | none =>
      obtain ⟨n, hn, S1, e1, hpc1, R1, fr1⟩ := Bk.2.1 heff
      replace hn : n ≤ stepBound dvKs := hn
      refine ⟨n, by omega, S1, e1, Or.inr (Or.inl ⟨c, s, by omega, hrun, ?_, hpc1, h.step G fr1 R1⟩)⟩
      rw [hv, hstep, heff]
  | some s' =>
      rw [heff] at hrun1
      by_cases hcap : s'.out.length ≤ B + 1
      · obtain ⟨n, hn, S1, e1, hpc1, R1, fr1⟩ := Bk.1 s' heff (fun _ _ => hcap)
        replace hn : n ≤ stepBound dvKs := hn
        have h1 := h.step G fr1 R1
        by_cases hlt' : s'.pc < Q.length
        · have hpc1' : S1.pc = dvStub Q + 2 * s'.pc := by
            rw [hpc1]; simp [dvCode, hlt']
          obtain ⟨S2, e2, hpc2, h25, h2⟩ := dv_stub G h1 hpc1' hlt'
          exact ⟨n + 2, by omega, S2, e1.trans e2,
            Or.inl ⟨s', by rw [hv]; exact hrun1, hlt', hpc2, h25, h2⟩⟩
        · have hpc1' : S1.pc = dvExit Q := by rw [hpc1]; simp [dvCode, hlt']
          refine ⟨n, by omega, S1, e1, Or.inr (Or.inl ⟨c + 1, s', le_rfl, by rw [hv]; exact hrun1,
            step_none_of_length_le (by omega), hpc1', h1⟩)⟩
      · obtain ⟨n, hn, S1, e1, hpc1, fr1, ho1⟩ := Bk.2.2 s' (dvDead Q) rfl heff
          (by show B + 1 < s'.out.length; omega)
        replace hn : n ≤ stepBound dvKs := hn
        have hb := (dvBase_bounds (by have := G.k2; omega) hI).1
        have room := G.room
        have hR : dvR B = B + 5 := rfl
        have hnw : ∀ a, a < 40 → ¬ (a = rCur ∨ a = rOC ∨ (rT ≤ a ∧ a ≤ rU)) →
            S1.mem a = S.mem a := fun a h1 h2 => fr1.2.2 a (fun hW => by
          rcases dvGeo_W G hI hW with h | h | h | h | h
          · exact h2 (Or.inl h)
          · exact h2 (Or.inr (Or.inl h))
          · exact h2 (Or.inr (Or.inr h))
          · omega
          · simp only [dvCtx] at h; omega)
        refine ⟨n, by omega, S1, e1, Or.inr (Or.inr ⟨hpc1, ?_⟩)⟩
        exact
          { const := h.const.frame (fun a ha => hnw a (by simp only [DConstCell] at ha; omega)
              (by simp only [DConstCell] at ha; omega)) (h.const.word.exec e1) fr1.1 ho1
            slot := by rw [hnw 20 (by omega) (by omega)]; exact h.slot
            pos := h.pos
            thr := h.thr
            valid := hI
            ctx := by rw [hnw 24 (by omega) (by omega)]; exact h.ctx
            others := fun i hi hne => (h.others i hi hne).frame (fun a ha => by
              obtain ⟨h40, hc1, hc2⟩ := dv_disjoint G hI hi (Ne.symm hne) a ha
              exact fr1.2.2 a (fun hW => by
                rcases dvGeo_W G hI hW with h | h | h | h | h
                · omega
                · omega
                · omega
                · exact hc2 h
                · exact hc1 ⟨by omega, by omega⟩))
            never := no_short_accept (by rw [hv]; exact hrun1) (by omega) }

end Lax185574Proofs.RamSim
