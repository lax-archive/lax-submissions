import Lax185574Proofs.RamDoveSlot

/-!
The ends of a slot of the dovetailer: skipping it, retiring the thread,
and saving the thread after one instruction.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.Ruler

variable {w K B : ℕ} {Q : Program} {x : List ℕ}

/-- The constant cells. -/
def DConstCell (a : ℕ) : Prop :=
  a < 2 ∨ a = 5 ∨ a = 8 ∨ a = 16 ∨ a = 18 ∨ a = 19 ∨ (26 ≤ a ∧ a ≤ 29) ∨ (34 ≤ a ∧ a ≤ 36)

theorem DConst.frame {S S' : State} (h : DConst w K B x S)
    (hf : ∀ a, DConstCell a → S'.mem a = S.mem a) (hw : WordMem w S'.mem)
    (hi : S'.input = S.input) (ho : S'.out = S.out) : DConst w K B x S' :=
  { word := hw
    zero := by rw [hf _ (by simp [DConstCell])]; exact h.zero
    one := by rw [hf _ (by simp [DConstCell])]; exact h.one
    len0 := by rw [hf _ (by simp [DConstCell])]; exact h.len0
    len1 := by rw [hf _ (by simp [DConstCell])]; exact h.len1
    st1 := by rw [hf _ (by simp [DConstCell])]; exact h.st1
    tot := by rw [hf _ (by simp [DConstCell])]; exact h.tot
    cap := by rw [hf _ (by simp [DConstCell])]; exact h.cap
    wm := by rw [hf _ (by simp [DConstCell])]; exact h.wm
    size0 := by rw [hf _ (by simp [DConstCell])]; exact h.size0
    half := by rw [hf _ (by simp [DConstCell])]; exact h.half
    two := by rw [hf _ (by simp [DConstCell])]; exact h.two
    rsize := by rw [hf _ (by simp [DConstCell])]; exact h.rsize
    rbase := by rw [hf _ (by simp [DConstCell])]; exact h.rbase
    kk := by rw [hf _ (by simp [DConstCell])]; exact h.kk
    input := hi.trans h.input
    out := ho.trans h.out }

theorem slot_succ {j : ℕ} (_hw : 0 < 2 ^ w) : (j % 2 ^ w + 1) % 2 ^ w = (j + 1) % 2 ^ w := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- Advance the slot counter and return to the start of the loop. -/
theorem DGlob.hw (G : DGlob w K B Q x) : 40 + dvR B * w < 2 ^ w := by
  have := G.room
  have : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← pow_succ]; congr 1; have := G.kw; omega
  have : 0 < 2 ^ (w - 1) := by positivity
  omega

theorem dv_next (G : DGlob w K B Q x) {j A : ℕ} {S : State}
    (hf : Fits (dvProg Q B K) A [.add 20 20 rOne, .jump dvL0])
    (hpc : S.pc = A) (C : DConst w K B x S) (hslot : S.mem 20 = j % 2 ^ w) (hj : 1 ≤ j)
    (hthr : ∀ i, i + K < w → TInv w K B Q x i (count i (j + 1)) S) :
    ∃ S', Exec w (dvProg Q B K) 2 S S' ∧ DInv w K B Q x (j + 1) S' := by
  have hw := G.hw
  obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_add (w := w) (s := S)
    (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega) (by omega) (by omega)).upd
  have e2 := e1.trans (x_jump (fetch hf (i := 1) (by simp [hpc1, hpc]) rfl))
  have hfr : ∀ a, a ≠ 20 → S1.mem a = S.mem a := fun a ha => by rw [hm1, if_neg ha]
  refine ⟨_, e2, ?_⟩
  exact
    { const := C.frame (fun a ha => by simp only [DConstCell] at ha; exact hfr a (by omega))
        (show WordMem w S1.mem from C.word.exec e1) hi1 ho1
      pc := rfl
      slot := by
        show S1.mem 20 = _
        rw [hm1, if_pos rfl, hslot, C.one, slot_succ (by positivity)]
      pos := by omega
      threads := fun i hi => (hthr i hi).frame (fun a ha => hfr a (by
        have : 40 ≤ a := by
          rcases ha with ha | ha
          · simp only [dvCtx] at ha; omega
          · have := (dvBase_bounds (by have := G.k2; omega) hi).1
            have := G.room
            omega
        omega)) }

theorem count_succ_ne {i j I : ℕ} (hj : ruler j = I) (hne : i ≠ I) :
    count i (j + 1) = count i j := by
  rw [count_succ, if_neg (by intro h; exact hne (h.2.symm.trans hj))]; rfl

theorem count_succ_eq {j : ℕ} (hj : j ≠ 0) : count (ruler j) (j + 1) = count (ruler j) j + 1 := by
  rw [count_succ, if_pos ⟨hj, rfl⟩]

/-- The cells of thread `i` lie above 40. -/
theorem dv_area_ge (G : DGlob w K B Q x) {i a : ℕ} (hi : i + K < w)
    (ha : (dvCtx B i ≤ a ∧ a < dvCtx B i + dvR B) ∨
      (dvBase w K i ≤ a ∧ a < dvBase w K i + 2 ^ (w - K - i))) : 40 ≤ a := by
  rcases ha with ha | ha
  · simp only [dvCtx] at ha; omega
  · have := (dvBase_bounds (by have := G.k2; omega) hi).1
    have := G.room
    omega

theorem dvCtx_le (G : DGlob w K B Q x) {i : ℕ} (hi : i + K < w) :
    dvCtx B i + dvR B ≤ 40 + dvR B * w := by
  simp only [dvCtx]; nlinarith

/-- Retire the thread of the slot. -/
theorem dv_dead (G : DGlob w K B Q x) {j I : ℕ} {S : State} (hpc : S.pc = dvDead Q)
    (C : DConst w K B x S) (hslot : S.mem 20 = j % 2 ^ w) (hj : 1 ≤ j) (hI : I + K < w)
    (hIj : ruler j = I) (h24 : S.mem 24 = dvCtx B I)
    (hothers : ∀ i, i + K < w → i ≠ I → TInv w K B Q x i (count i j) S)
    (hdead : ∀ y t, y.length ≤ B → ¬ RunsTo (w - I - K) Q (I :: x) (1 :: y) t) :
    ∃ S', Exec w (dvProg Q B K) 5 S S' ∧ DInv w K B Q x (j + 1) S' := by
  have hw := G.hw
  have hc := dvCtx_le G hI
  have hR : dvR B = B + 5 := rfl
  have hf := dv_fits_dead Q B K
  have hm := C.word
  obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_set (w := w) (s := S)
    (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)).upd
  obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_add (w := w) (s := S1)
    (fetch hf (i := 1) (by simp [hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
  have hT2 : S2.mem rT = dvCtx B I + 3 := by
    rw [hm2, if_pos rfl, hm1, if_pos rfl, hm1, if_neg (by decide), h24,
      Nat.mod_eq_of_lt (show 3 < 2 ^ w by omega), Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_store (w := w) (s := S2)
    (fetch hf (i := 2) (by simp [hpc2, hpc1, hpc]) rfl) (hm.exec (e1.trans e2)) (by omega)
    (by omega)).upd
  have hfr : ∀ a, a ≠ rT → a ≠ dvCtx B I + 3 → S3.mem a = S.mem a := by
    intro a h1 h2
    rw [hm3, hT2, if_neg h2, hm2, if_neg h1, hm1, if_neg h1]
  obtain ⟨S', e', hD⟩ := dv_next G (A := dvDead Q + 3) (S := S3) (Fits.sub hf 3 2)
    (by rw [hpc3, hpc2, hpc1, hpc]) (C.frame (fun a ha => hfr a (by
        simp only [DConstCell] at ha; omega) (by simp only [DConstCell, dvCtx] at ha ⊢; omega))
      (hm.exec ((e1.trans e2).trans e3)) (by rw [hi3, hi2, hi1]) (by rw [ho3, ho2, ho1]))
    (by rw [hfr _ (by decide) (by simp only [dvCtx]; omega)]; exact hslot) hj
    (fun i hi => by
      by_cases hiI : i = I
      · subst hiI
        refine Or.inr ⟨?_, hdead⟩
        have h1' : S2.mem rOne = 1 := by
          rw [hm2, if_neg (by decide), hm1, if_neg (by decide), C.one]
        rw [hm3, hT2, if_pos rfl, h1']; omega
      · rw [count_succ_ne hIj hiI]
        refine (hothers i hi hiI).frame (fun a ha => ?_)
        obtain ⟨h40, hc1, hc2⟩ := dv_disjoint G hI hi (Ne.symm hiI) a ha
        exact hfr a (by omega) (by omega))
  exact ⟨_, (((e1.trans e2).trans e3).trans e').cast (by omega), hD⟩

/-- The machine runs thread `I` in slot `j`, which has had `c` slots
before, and represents its state `s`. -/
structure Running (w K B : ℕ) (Q : Program) (x : List ℕ) (j I c : ℕ) (s S : State) : Prop where
  const : DConst w K B x S
  slot : S.mem 20 = j % 2 ^ w
  pos : 1 ≤ j
  thr : ruler j = I
  valid : I + K < w
  ctx : S.mem 24 = dvCtx B I
  cnt : count I j = c
  rel : Rel w (dvGeo w K B I) dvKs 16 (.buffer (dvDead Q)) (I :: x) [] s S
  alive : S.mem (dvCtx B I + 3) = 0
  others : ∀ i, i + K < w → i ≠ I → TInv w K B Q x i (count i j) S

theorem dvGeo_W (G : DGlob w K B Q x) {I a : ℕ} (hI : I + K < w) (h : (dvGeo w K B I).W a) :
    a = rCur ∨ a = rOC ∨ (rT ≤ a ∧ a ≤ rU) ∨
      (dvBase w K I ≤ a ∧ a < dvBase w K I + 2 ^ (w - K - I)) ∨
      (dvCtx B I + 4 ≤ a ∧ a < dvCtx B I + 4 + (B + 1)) := by
  simpa [Geo.W, dvGeo] using h

/-- One step of the running thread keeps everything outside its cells. -/
theorem Running.step (G : DGlob w K B Q x) {j I c : ℕ} {s s' S S' : State}
    (h : Running w K B Q x j I c s S) (hfr : Frame (dvGeo w K B I) S S')
    (R : Rel w (dvGeo w K B I) dvKs 16 (.buffer (dvDead Q)) (I :: x) [] s' S') :
    Running w K B Q x j I c s' S' := by
  have hI := h.valid
  have hR : dvR B = B + 5 := rfl
  have hc := dvCtx_le G hI
  have hw := G.hw
  have hb := dvBase_bounds (by have := G.k2; omega) hI
  have room := G.room
  have hnw : ∀ a, a < 40 → ¬ (a = rCur ∨ a = rOC ∨ (rT ≤ a ∧ a ≤ rU)) →
      S'.mem a = S.mem a := fun a h1 h2 => hfr.2.2 a (fun hW => by
    rcases dvGeo_W G hI hW with h | h | h | h | h
    · exact h2 (Or.inl h)
    · exact h2 (Or.inr (Or.inl h))
    · exact h2 (Or.inr (Or.inr h))
    · omega
    · simp only [dvCtx] at h; omega)
  have hO : S'.out = S.out := by
    rw [R.out.1, h.rel.out.1]
  exact
    { const := h.const.frame (fun a ha => hnw a (by simp only [DConstCell] at ha; omega)
        (by simp only [DConstCell] at ha; omega)) R.env.word hfr.1 hO
      slot := by rw [hnw 20 (by omega) (by omega)]; exact h.slot
      pos := h.pos
      thr := h.thr
      valid := hI
      ctx := by rw [hnw 24 (by omega) (by omega)]; exact h.ctx
      cnt := h.cnt
      rel := R
      alive := by
        rw [hfr.2.2 _ (fun hW => by
          rcases dvGeo_W G hI hW with h | h | h | h | h <;> simp only [dvCtx] at * <;> omega)]
        exact h.alive
      others := fun i hi hne => (h.others i hi hne).frame (fun a ha => by
        obtain ⟨h40, hc1, hc2⟩ := dv_disjoint G hI hi (Ne.symm hne) a ha
        exact hfr.2.2 a (fun hW => by
          rcases dvGeo_W G hI hW with h | h | h | h | h
          · omega
          · omega
          · omega
          · exact hc2 h
          · exact hc1 ⟨by omega, by omega⟩)) }

/-- Save the running thread after one instruction and go to the next
slot. -/
theorem dv_save (G : DGlob w K B Q x) {j I c : ℕ} {s S : State} (hpc : S.pc = dvSave Q)
    (h : Running w K B Q x j I c s S) (h25 : S.mem 25 = s.pc) (hpcQ : s.pc < Q.length)
    (hrun : run (w - I - K) Q (c + 1) (initState (I :: x)) = some s) :
    ∃ S', Exec w (dvProg Q B K) 9 S S' ∧ DInv w K B Q x (j + 1) S' := by
  have hI := h.valid
  have hw := G.hw
  have hc := dvCtx_le G hI
  have hR : dvR B = B + 5 := rfl
  have hf := dv_fits_save Q B K
  have hm := h.const.word
  have R := h.rel
  obtain ⟨ho, hob, hoc, hcap, hle, -, -, -, hbuf⟩ := R.out
  obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_store (w := w) (s := S)
    (fetch hf (i := 0) (by simp [hpc]) rfl) hm (by omega) (by omega)).upd
  rw [h.ctx, h25] at hm1
  obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_set (w := w) (s := S1)
    (fetch hf (i := 1) (by simp [hpc1, hpc]) rfl) (by omega)).upd
  obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_add (w := w) (s := S2)
    (fetch hf (i := 2) (by simp [hpc2, hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
  have hT3 : S3.mem rT = dvCtx B I + 1 := by
    rw [hm3, if_pos rfl, hm2, if_pos rfl, hm2, if_neg (by decide), hm1,
      if_neg (by simp only [dvCtx]; omega), h.ctx, Nat.mod_eq_of_lt (show 1 < 2 ^ w by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_store (w := w) (s := S3)
    (fetch hf (i := 3) (by simp [hpc3, hpc2, hpc1, hpc]) rfl)
    (hm.exec ((e1.trans e2).trans e3)) (by omega) (by omega)).upd
  rw [hT3] at hm4
  obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_set (w := w) (s := S4)
    (fetch hf (i := 4) (by simp [hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega)).upd
  obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_add (w := w) (s := S5)
    (fetch hf (i := 5) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega) (by omega)
    (by omega)).upd
  have h24 : S5.mem 24 = dvCtx B I := by
    rw [hm5, if_neg (by decide), hm4, if_neg (by simp only [dvCtx]; omega), hm3, if_neg (by decide),
      hm2, if_neg (by decide), hm1, if_neg (by simp only [dvCtx]; omega), h.ctx]
  have hT6 : S6.mem rT = dvCtx B I + 2 := by
    rw [hm6, if_pos rfl, hm5, if_pos rfl, h24, Nat.mod_eq_of_lt (show 2 < 2 ^ w by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨S7, e7, hpc7, hm7, hi7, hn7, ho7⟩ := (x_store (w := w) (s := S6)
    (fetch hf (i := 6) (by simp [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl)
    (hm.exec (((((e1.trans e2).trans e3).trans e4).trans e5).trans e6)) (by omega) (by omega)).upd
  rw [hT6] at hm7
  -- the cells written
  have hfr : ∀ a, a ≠ rT → a ≠ dvCtx B I → a ≠ dvCtx B I + 1 → a ≠ dvCtx B I + 2 →
      S7.mem a = S.mem a := by
    intro a h1 h2 h3 h4
    rw [hm7, if_neg h4, hm6, if_neg h1, hm5, if_neg h1, hm4, if_neg h3, hm3, if_neg h1, hm2,
      if_neg h1, hm1, if_neg h2]
  have hcur : S7.mem (dvCtx B I + 1) = S.mem rCur := by
    rw [hm7, if_neg (by omega), hm6, if_neg (by simp only [dvCtx]; omega), hm5,
      if_neg (by simp only [dvCtx]; omega), hm4, if_pos rfl, hm3, if_neg (by decide), hm2,
      if_neg (by decide), hm1, if_neg (by simp only [dvCtx]; omega)]
  have hocS : S7.mem (dvCtx B I + 2) = S.mem rOC := by
    rw [hm7, if_pos rfl, hm6, if_neg (by decide), hm5, if_neg (by decide), hm4,
      if_neg (by simp only [dvCtx]; omega), hm3, if_neg (by decide), hm2, if_neg (by decide), hm1,
      if_neg (by simp only [dvCtx]; omega)]
  have hpcS : S7.mem (dvCtx B I) = s.pc := by
    rw [hm7, if_neg (by omega), hm6, if_neg (by simp only [dvCtx]; omega), hm5,
      if_neg (by simp only [dvCtx]; omega), hm4, if_neg (by omega), hm3,
      if_neg (by simp only [dvCtx]; omega), hm2, if_neg (by simp only [dvCtx]; omega), hm1,
      if_pos rfl]
  have hm7w := hm.exec ((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7)
  have hb := dvBase_bounds (by have := G.k2; omega) hI
  have room := G.room
  obtain ⟨S', eN, hD⟩ := dv_next G (A := dvSave Q + 7) (S := S7) (Fits.sub hf 7 2)
    (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc])
    (h.const.frame (fun a ha => hfr a (by simp only [DConstCell] at ha; omega)
      (by simp only [DConstCell, dvCtx] at ha ⊢; omega)
      (by simp only [DConstCell, dvCtx] at ha ⊢; omega)
      (by simp only [DConstCell, dvCtx] at ha ⊢; omega)) hm7w
      (by rw [hi7, hi6, hi5, hi4, hi3, hi2, hi1]) (by rw [ho7, ho6, ho5, ho4, ho3, ho2, ho1]))
    (by rw [hfr _ (by decide) (by simp only [dvCtx]; omega) (by simp only [dvCtx]; omega)
      (by simp only [dvCtx]; omega)]; exact h.slot) h.pos
    (fun i hi => by
      by_cases hiI : i = I
      · subst hiI
        have hj0 : j ≠ 0 := by have := h.pos; omega
        rw [← h.thr, count_succ_eq hj0, h.thr, h.cnt]
        refine Or.inl ⟨s, hrun, Or.inl hpcQ, ?_⟩
        exact
          { pc := hpcS
            cur := by rw [hcur]; have := R.cur; simpa using this
            inp := by rw [hcur]; exact R.inp
            oc := by rw [hocS]; exact hoc
            ocB := hle
            alive := by
              rw [hfr _ (by simp only [dvCtx]; omega) (by omega) (by omega) (by omega)]
              exact h.alive
            buf := fun k hk => by
              rw [hfr _ (by simp only [dvCtx]; omega) (by omega) (by omega) (by omega)]
              exact hbuf k hk
            mem := fun a ha => by
              rw [hfr _ (by omega) (by omega) (by omega) (by omega)]
              exact R.mem a ha
            cword := R.cword
            input := R.input }
      · rw [count_succ_ne h.thr hiI]
        refine (h.others i hi hiI).frame (fun a ha => ?_)
        obtain ⟨h40, hc1, hc2⟩ := dv_disjoint G hI hi (Ne.symm hiI) a ha
        exact hfr a (by omega) (by omega) (by omega) (by omega))
  exact ⟨_, (((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans
    eN).cast (by omega), hD⟩

end Lax185574Proofs.RamSim
