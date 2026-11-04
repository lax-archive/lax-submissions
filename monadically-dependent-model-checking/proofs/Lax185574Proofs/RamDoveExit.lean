import Lax185574Proofs.RamDoveRun

/-!
The exit handler of the dovetailer: a thread has halted. If its output
is `1 :: y` the machine writes `y` and halts, otherwise the thread is
retired.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.Ruler

variable {w K B : ℕ} {Q : Program} {x : List ℕ}

theorem Running.toDying (G : DGlob w K B Q x) {j I c : ℕ} {s S S' : State}
    (h : Running w K B Q x j I c s S) (t : TempsOnly S S') (hW : WordMem w S'.mem)
    (hnever : ∀ y t, y.length ≤ B → ¬ RunsTo (w - I - K) Q (I :: x) (1 :: y) t) :
    Dying w K B Q x j I S' :=
  { const := h.const.frame (fun a ha => t.1 a (by simp only [DConstCell] at ha; omega)) hW
      t.2.1 t.2.2.2
    slot := by rw [t.1 20 (by omega)]; exact h.slot
    pos := h.pos
    thr := h.thr
    valid := h.valid
    ctx := by rw [t.1 24 (by omega)]; exact h.ctx
    others := fun i hi hne => (h.others i hi hne).frame (fun a ha =>
      t.1 a (by have := dv_area_ge G hi ha; omega))
    never := hnever }

/-- The write loop: from position `k` of the buffer at `ob`, write the
rest of the list `out` and halt. -/
theorem dv_write_loop (G : DGlob w K B Q x) {ob : ℕ} {out : List ℕ}
    (hob16 : 16 ≤ ob) (hobw : ob + out.length < 2 ^ w) :
    ∀ (r k : ℕ) (S : State), out.length - k = r → 1 ≤ k → k ≤ out.length →
      WordMem w S.mem → S.mem rOne = 1 → S.mem rOB = ob → S.mem rOC = out.length →
      (∀ k < out.length, S.mem (ob + k) = out.getD k 0) →
      S.pc = dvExit Q + 7 → S.mem rC = k →
      ∃ S', Exec w (dvProg Q B K) (7 * r + 2) S S' ∧ S'.pc = dvExit Q + 14 ∧
        S'.out = S.out ++ (out.drop k) := by
  have hw := G.hw
  have hf := dv_fits_exit Q B K
  intro r
  induction r with
  | zero =>
      intro k S hr hk1 hk hm h1 hob hoc hbuf hpc hC
      have hkl : k = out.length := by omega
      obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_sub (w := w) (s := S)
        (fetch hf (i := 7) (by simp [hpc]) rfl) hm (by omega) (by omega)
        (by omega)).upd
      have e2 := x_jzero_pos (w := w) (s := S1) (fetch hf (i := 8) (by simp [hpc1, hpc]) rfl)
        (by omega) (by rw [hm1, if_pos rfl, hoc, hC]; omega)
      refine ⟨_, e1.trans e2, rfl, ?_⟩
      show S1.out = _
      rw [ho1, hkl, List.drop_length, List.append_nil]
  | succ r ih =>
      intro k S hr hk1 hk hm h1 hob hoc hbuf hpc hC
      have hkl : k < out.length := by omega
      obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_sub (w := w) (s := S)
        (fetch hf (i := 7) (by simp [hpc]) rfl) hm (by omega) (by omega) (by omega)).upd
      have e2 := x_jzero_neg (w := w) (s := S1) (fetch hf (i := 8) (by simp [hpc1, hpc]) rfl)
        (by omega) (by rw [hm1, if_pos rfl, hoc, hC]; omega)
      have hm1w := hm.exec e1
      obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_add (w := w) (s := { S1 with pc := S1.pc + 1 })
        (fetch hf (i := 9) (by simp [hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
      have hT3 : S3.mem rT = ob + k := by
        rw [hm3, if_pos rfl]
        show (S1.mem rOB + S1.mem rC) % 2 ^ w = _
        rw [hm1, if_neg (by decide), hm1, if_neg (by decide), hob, hC, Nat.mod_eq_of_lt (by omega)]
      obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_load (w := w) (s := S3)
        (fetch hf (i := 10) (by simp [hpc3, hpc1, hpc]) rfl)
        (show WordMem w S3.mem from (WordMem.exec (s := { S1 with pc := S1.pc + 1 }) hm1w e3))
        (by omega) (by omega)).upd
      have hB4 : S4.mem rB = out.getD k 0 := by
        rw [hm4, if_pos rfl, hT3, hm3, if_neg (by omega)]
        show S1.mem _ = _
        rw [hm1, if_neg (by omega)]
        exact hbuf k hkl
      have hm4w := (WordMem.exec (s := { S1 with pc := S1.pc + 1 }) hm1w e3).exec e4
      have e5 := x_write (w := w) (s := S4) (fetch hf (i := 11) (by simp [hpc4, hpc3, hpc1, hpc])
        rfl) hm4w (by omega)
      obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_add (w := w)
        (s := { S4 with pc := S4.pc + 1, out := S4.out ++ [S4.mem rB] })
        (fetch hf (i := 12) (by simp [hpc4, hpc3, hpc1, hpc]) rfl) (by omega) (by omega)
        (by omega)).upd
      have e7 := x_jump (w := w) (s := S6) (fetch hf (i := 13) (by simp [hpc6, hpc4, hpc3, hpc1,
        hpc]) rfl)
      have hfr : ∀ a, a ≠ rT → a ≠ rU → a ≠ rB → a ≠ rC → S6.mem a = S.mem a := by
        intro a h1 h2 h3 h4
        rw [hm6, if_neg h4]
        show S4.mem a = _
        rw [hm4, if_neg h3, hm3, if_neg h1]
        show S1.mem a = _
        rw [hm1, if_neg h2]
      have hC6 : S6.mem rC = k + 1 := by
        rw [hm6, if_pos rfl]
        show (S4.mem rC + S4.mem rOne) % 2 ^ w = _
        rw [hm4, if_neg (by decide), hm4, if_neg (by decide), hm3, if_neg (by decide), hm3,
          if_neg (by decide)]
        show (S1.mem rC + S1.mem rOne) % 2 ^ w = _
        rw [hm1, if_neg (by decide), hm1, if_neg (by decide), hC, h1,
          Nat.mod_eq_of_lt (by omega)]
      have hW6 := (WordMem.exec (s := { S4 with pc := S4.pc + 1, out := S4.out ++ [S4.mem rB] })
        hm4w e6)
      have g1 : S6.mem rOne = 1 := by
        rw [hfr _ (by decide) (by decide) (by decide) (by decide)]; exact h1
      have g2 : S6.mem rOB = ob := by
        rw [hfr _ (by decide) (by decide) (by decide) (by decide)]; exact hob
      have g3 : S6.mem rOC = out.length := by
        rw [hfr _ (by decide) (by decide) (by decide) (by decide)]; exact hoc
      have g4 : ∀ k' < out.length, S6.mem (ob + k') = out.getD k' 0 := fun k' hk' => by
        rw [hfr _ (by omega) (by omega) (by omega) (by omega)]; exact hbuf k' hk'
      obtain ⟨S', e', hpc', hout'⟩ := ih (k + 1) { S6 with pc := dvExit Q + 7 } (by omega)
        (by omega) (by omega) hW6 g1 g2 g3 g4 rfl hC6
      refine ⟨S', ((((((e1.trans e2).trans e3).trans e4).trans e5).trans (e6.trans e7)).trans
        e').cast (by ring), hpc', ?_⟩
      rw [hout']
      show S6.out ++ _ = _
      rw [ho6]
      show (S4.out ++ [S4.mem rB]) ++ _ = _
      rw [ho4, ho3]
      show (S1.out ++ [S4.mem rB]) ++ _ = _
      rw [ho1, hB4, List.append_assoc, List.singleton_append, List.drop_eq_getElem_cons hkl,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl]
      rfl

/-- The exit handler. -/
theorem dv_exit (G : DGlob w K B Q x) {j I c c' : ℕ} {s S : State}
    (h : Running w K B Q x j I c s S) (hpc : S.pc = dvExit Q)
    (hrun : run (w - I - K) Q c' (initState (I :: x)) = some s)
    (hs : step (w - I - K) Q s = none) :
    (∃ n ≤ 7 * (B + 1) + 10, ∃ S', Exec w (dvProg Q B K) n S S' ∧
      (dvProg Q B K)[S'.pc]? = some .halt ∧ ∃ y, s.out = 1 :: y ∧ S'.out = y) ∨
    (∃ n ≤ 10, ∃ S', Exec w (dvProg Q B K) n S S' ∧ S'.pc = dvDead Q ∧
      Dying w K B Q x j I S') := by
  have hw := G.hw
  have hf := dv_fits_exit Q B K
  have hm := h.const.word
  have R := h.rel
  have hI := h.valid
  obtain ⟨ho, hob, hoc, -, hle, -, -, -, hbuf⟩ := R.out
  have hob' : S.mem rOB = dvCtx B I + 4 := hob
  have hle' : s.out.length ≤ B + 1 := hle
  have hbuf' : ∀ k < s.out.length, S.mem (dvCtx B I + 4 + k) = s.out.getD k 0 := hbuf
  have hc := dvCtx_le G hI
  have hR : dvR B = B + 5 := rfl
  have dead := fun (S' : State) (t : TempsOnly S S') (hW : WordMem w S'.mem)
      (hno : ∀ y, y.length ≤ B → s.out ≠ 1 :: y) =>
    h.toDying G t hW (no_accept_of_terminal hrun hs hno)
  by_cases h0 : s.out.length = 0
  · -- no output: retire
    have e1 := x_jzero_pos (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)
      (by rw [hoc, h0])
    refine Or.inr ⟨1, by omega, _, e1, rfl, dead _ TempsOnly.setPc hm (fun y _ he => ?_)⟩
    rw [he] at h0; simp at h0
  · have e1 := x_jzero_neg (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)
      (by rw [hoc]; exact h0)
    obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_load (w := w) (s := { S with pc := S.pc + 1 })
      (fetch hf (i := 1) (by simp [hpc]) rfl) hm (by omega) (by omega)).upd
    have hB2 : S2.mem rB = s.out.getD 0 0 := by
      rw [hm2, if_pos rfl]
      show S.mem (S.mem rOB) = _
      rw [hob', ← hbuf' 0 (by omega)]
    obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_sub (w := w) (s := S2)
      (fetch hf (i := 2) (by simp [hpc2, hpc]) rfl) (show WordMem w S2.mem from
        WordMem.exec (s := { S with pc := S.pc + 1 }) hm e2) (by omega) (by omega) (by omega)).upd
    have hU3 : S3.mem rU = s.out.getD 0 0 - 1 := by
      rw [hm3, if_pos rfl, hB2, hm2, if_neg (by decide)]
      show _ - S.mem rOne = _
      rw [h.const.one]
    have t3 : TempsOnly S S3 := ⟨fun a ha => by
        rw [hm3, if_neg (by omega), hm2, if_neg (by omega)], by rw [hi3, hi2], by rw [hn3, hn2],
        by rw [ho3, ho2]⟩
    have hW3 := (WordMem.exec (s := { S with pc := S.pc + 1 }) hm e2).exec e3
    have hpc3' : S3.pc = dvExit Q + 3 := by rw [hpc3, hpc2]; simp [hpc]
    by_cases h1 : s.out.getD 0 0 ≤ 1
    · have e4 := x_jzero_pos (w := w) (s := S3) (fetch hf (i := 3) (by simp [hpc3']) rfl)
        (by omega) (by rw [hU3]; omega)
      have hB3 : S3.mem rB = s.out.getD 0 0 := by rw [hm3, if_neg (by decide), hB2]
      by_cases h2 : s.out.getD 0 0 = 0
      · have e5 := x_jzero_pos (w := w) (s := { S3 with pc := dvExit Q + 5 })
          (fetch hf (i := 5) rfl rfl) (by omega) (by rw [← h2]; exact hB3)
        refine Or.inr ⟨_, by omega, _, ((e1.trans e2).trans e3).trans (e4.trans e5), rfl,
          dead _ (t3.trans TempsOnly.setPc) hW3 (fun y _ he => ?_)⟩
        rw [he] at h2; simp at h2
      · -- accept
        have e5 := x_jzero_neg (w := w) (s := { S3 with pc := dvExit Q + 5 })
          (fetch hf (i := 5) rfl rfl) (by omega) (by rw [hB3]; exact h2)
        obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_set (w := w)
          (s := { S3 with pc := dvExit Q + 5 + 1 }) (fetch hf (i := 6) rfl rfl) (by omega)).upd
        have t6 : TempsOnly S S6 := t3.trans ⟨fun a ha => by rw [hm6, if_neg (by omega)],
          hi6, hn6, ho6⟩
        have hW6 := WordMem.exec (s := { S3 with pc := dvExit Q + 5 + 1 }) hW3 e6
        have hx1 : s.out.getD 0 0 = 1 := by omega
        obtain ⟨S', e', hpc', hout'⟩ := dv_write_loop G (ob := dvCtx B I + 4) (out := s.out)
          (by simp only [dvCtx]; omega) (by omega) (s.out.length - 1) 1 { S6 with pc := dvExit Q + 7 }
          rfl le_rfl (by omega) hW6 (by rw [t6.1 _ (by omega)]; exact h.const.one)
          (by rw [t6.1 _ (by omega)]; exact hob') (by rw [t6.1 _ (by omega)]; exact hoc)
          (fun k hk => by rw [t6.1 _ (by simp only [dvCtx]; omega)]; exact hbuf' k hk) rfl
          (by rw [hm6, if_pos rfl, Nat.mod_eq_of_lt (by omega)])
        refine Or.inl ⟨1 + 1 + 1 + 1 + (1 + 1 + (7 * (s.out.length - 1) + 2)), by omega, S',
          ((((e1.trans e2).trans e3).trans e4).trans
          ((e5.trans (e6.at_pc (A := dvExit Q + 7) (by rw [hpc6]))).trans e')), by rw [hpc']; exact (fits_singleton.1 (Fits.sub hf 14 1)),
          s.out.drop 1, ?_, ?_⟩
        · obtain ⟨a, rest, hs'⟩ : ∃ a rest, s.out = a :: rest := by
            cases hs' : s.out with
            | nil => rw [hs'] at h0; simp at h0
            | cons a rest => exact ⟨a, rest, rfl⟩
          rw [hs'] at hx1 ⊢; simp at hx1; simp [hx1]
        · rw [hout']; show S6.out ++ _ = _; rw [t6.2.2.2, ho]; rfl
    · have e4 := (x_jzero_neg (w := w) (s := S3) (fetch hf (i := 3) (by simp [hpc3']) rfl)
        (by omega) (by rw [hU3]; omega)).trans (x_jump (fetch hf (i := 4) (by simp [hpc3']) rfl))
      refine Or.inr ⟨_, by omega, _, ((e1.trans e2).trans e3).trans e4, rfl,
        dead _ (t3.trans TempsOnly.setPc) hW3 (fun y _ he => ?_)⟩
      rw [he] at h1; simp at h1

end Lax185574Proofs.RamSim
