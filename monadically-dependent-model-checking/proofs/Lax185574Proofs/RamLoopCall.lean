import Lax185574Proofs.RamLoopRound

/-!
The rest of a round of the loop driver: the test of the output of `G`,
the run of `P`, the exchange of the buffers, and the final output.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ}

section

variable (G P : Program)

/-- An empty output of `G` ends in the loop. -/
theorem lp_exitG_die {x a b : List ℕ} {i : ℕ} {S S1 : State} (hw : 8 ≤ w)
    (hpc : S1.pc = lpExitG G) (hO : PhaseOut w i (S.mem 44) S S1 []) :
    Exec w (lpProg G P) 1 S1 { S1 with pc := lpDie G P } :=
  x_jzero_pos (fetch (lp_fits_exitG G P) (i := 0) (by simp [hpc]) rfl)
    (by have := lpCap_bounds hw; omega) (by rw [hO.roc]; rfl)

/-- After a call of `G` with a non-empty output not starting with `0`. -/
theorem lp_exitG_call {o : List ℕ} {i : ℕ} {S S1 : State} (hw : 8 ≤ w)
    (hpc : S1.pc = lpExitG G) (hob : 64 ≤ S.mem 44 ∧ S.mem 44 + lpCap w ≤ 2 ^ w)
    (hO : PhaseOut w i (S.mem 44) S S1 o) (hne : o ≠ []) (h0 : o.head? ≠ some 0) :
    ∃ S2, Exec w (lpProg G P) 4 S1 S2 ∧ S2.pc = lpStartP G ∧ S2.mem 45 = o.length ∧
      (∀ c, c ≠ rB → c ≠ 45 → S2.mem c = S1.mem c) ∧ S2.input = S1.input ∧
      S2.out = S1.out := by
  have hC := lpCap_bounds hw
  have hf := lp_fits_exitG G P
  have hlen : o.length ≠ 0 := by simpa using hne
  have hm := hO.word
  have e0 := x_jzero_neg (w := w) (s := S1) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)
    (by rw [hO.roc]; exact hlen)
  obtain ⟨S2, e1, hpc2, hm2, hi2, -, ho2⟩ := (x_load (w := w) (s := { S1 with pc := S1.pc + 1 })
    (fetch hf (i := 1) (by simp [hpc]) rfl) hm (by omega) (by omega)).upd
  have hB : S2.mem rB = o.getD 0 0 := by
    rw [hm2, if_pos rfl]
    show S1.mem (S1.mem rOB) = _
    rw [hO.rob, ← hO.buf 0 (by omega), Nat.add_zero]
  have hB0 : S2.mem rB ≠ 0 := by
    rw [hB]
    cases o with
    | nil => exact absurd rfl hne
    | cons u o => simpa using h0
  have e2 := x_jzero_neg (w := w) (s := S2) (fetch hf (i := 2) (by simp [hpc2, hpc]) rfl)
    (by omega) hB0
  obtain ⟨S3, e3, hpc3, hm3, hi3, -, ho3⟩ := (x_add (w := w) (s := { S2 with pc := S2.pc + 1 })
    (fetch hf (i := 3) (by simp [hpc2, hpc]) rfl) (by omega) (by omega) (by omega)).upd
  refine ⟨S3, ((e0.trans e1).trans e2).trans e3, by rw [hpc3]; simp [hpc2, hpc, lpStartP], ?_,
    ?_, by rw [hi3]; exact hi2, by rw [ho3]; exact ho2⟩
  · rw [hm3, if_pos rfl]
    show (S2.mem rOC + S2.mem rZ) % 2 ^ w = _
    rw [hm2, if_neg (by decide), hm2, if_neg (by decide)]
    show (S1.mem rOC + S1.mem rZ) % 2 ^ w = _
    rw [hO.roc, hO.zero, Nat.add_zero, Nat.mod_eq_of_lt]
    rw [← hO.roc]; exact hm _
  · intro c h1 h2
    rw [hm3, if_neg h2]
    show S2.mem c = _
    rw [hm2, if_neg h1]

/-- After `G` with an output starting with `0`, at the write loop. -/
theorem lp_exitG_done {z : List ℕ} {i : ℕ} {S S1 : State} (hw : 8 ≤ w)
    (hpc : S1.pc = lpExitG G) (hob : 64 ≤ S.mem 44) (hO : PhaseOut w i (S.mem 44) S S1 (0 :: z)) :
    ∃ S2, Exec w (lpProg G P) 3 S1 S2 ∧ S2.pc = lpOut G P ∧ S2.mem rOB = S.mem 44 ∧
      S2.mem rOC = z.length + 1 ∧ S2.mem rOne = 1 ∧
      (∀ j < z.length + 1, S2.mem (S.mem 44 + j) = (0 :: z).getD j 0) ∧ WordMem w S2.mem ∧
      S2.out = S1.out := by
  have hC := lpCap_bounds hw
  have hf := lp_fits_exitG G P
  have hm := hO.word
  have e0 := x_jzero_neg (w := w) (s := S1) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)
    (by rw [hO.roc]; simp)
  obtain ⟨S2, e1, hpc2, hm2, hi2, -, ho2⟩ := (x_load (w := w) (s := { S1 with pc := S1.pc + 1 })
    (fetch hf (i := 1) (by simp [hpc]) rfl) hm (by omega) (by omega)).upd
  have hB : S2.mem rB = 0 := by
    rw [hm2, if_pos rfl]
    show S1.mem (S1.mem rOB) = _
    rw [hO.rob, ← Nat.add_zero (S.mem 44), hO.buf 0 (by simp)]; rfl
  have e2 := x_jzero_pos (w := w) (s := S2) (fetch hf (i := 2) (by simp [hpc2, hpc]) rfl)
    (by omega) hB
  have f2 : ∀ c, c ≠ rB → S2.mem c = S1.mem c := fun c h => by rw [hm2, if_neg h]
  refine ⟨_, (e0.trans e1).trans e2, rfl, ?_, ?_, ?_, ?_, hm.exec ((e0.trans e1).trans e2), ho2⟩
  · show S2.mem rOB = _; rw [f2 _ (by decide)]; exact hO.rob
  · show S2.mem rOC = _; rw [f2 _ (by decide), hO.roc]; rfl
  · show S2.mem rOne = _; rw [f2 _ (by decide)]; exact hO.one
  · intro j hj
    show S2.mem _ = _
    have hj' : S.mem 44 + j ≠ rB := by omega
    rw [f2 _ hj']; exact hO.buf j (by simpa using hj)

/-- The write loop. Adapted from `dv_write_loop`. -/
theorem lp_write_loop (G P : Program) {ob : ℕ} {out : List ℕ} (hw' : 8 ≤ w)
    (hob16 : 16 ≤ ob) (hobw : ob + out.length < 2 ^ w) :
    ∀ (r k : ℕ) (S : State), out.length - k = r → 1 ≤ k → k ≤ out.length →
      WordMem w S.mem → S.mem rOne = 1 → S.mem rOB = ob → S.mem rOC = out.length →
      (∀ k < out.length, S.mem (ob + k) = out.getD k 0) →
      S.pc = lpOut G P + 1 → S.mem rC = k →
      ∃ S', Exec w (lpProg G P) (7 * r + 2) S S' ∧ S'.pc = lpOut G P + 8 ∧
        S'.out = S.out ++ (out.drop k) := by
  have hw : 64 < 2 ^ w := by have := lpCap_bounds hw'; omega
  have hf := lp_fits_out G P
  intro r
  induction r with
  | zero =>
      intro k S hr hk1 hk hm h1 hob hoc hbuf hpc hC
      have hkl : k = out.length := by omega
      obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_sub (w := w) (s := S)
        (fetch hf (i := 1) (by simp [hpc]) rfl) hm (by omega) (by omega)
        (by omega)).upd
      have e2 := x_jzero_pos (w := w) (s := S1) (fetch hf (i := 2) (by simp [hpc1, hpc]) rfl)
        (by omega) (by rw [hm1, if_pos rfl, hoc, hC]; omega)
      refine ⟨_, e1.trans e2, rfl, ?_⟩
      show S1.out = _
      rw [ho1, hkl, List.drop_length, List.append_nil]
  | succ r ih =>
      intro k S hr hk1 hk hm h1 hob hoc hbuf hpc hC
      have hkl : k < out.length := by omega
      obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_sub (w := w) (s := S)
        (fetch hf (i := 1) (by simp [hpc]) rfl) hm (by omega) (by omega) (by omega)).upd
      have e2 := x_jzero_neg (w := w) (s := S1) (fetch hf (i := 2) (by simp [hpc1, hpc]) rfl)
        (by omega) (by rw [hm1, if_pos rfl, hoc, hC]; omega)
      have hm1w := hm.exec e1
      obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_add (w := w) (s := { S1 with pc := S1.pc + 1 })
        (fetch hf (i := 3) (by simp [hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
      have hT3 : S3.mem rT = ob + k := by
        rw [hm3, if_pos rfl]
        show (S1.mem rOB + S1.mem rC) % 2 ^ w = _
        rw [hm1, if_neg (by decide), hm1, if_neg (by decide), hob, hC, Nat.mod_eq_of_lt (by omega)]
      obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_load (w := w) (s := S3)
        (fetch hf (i := 4) (by simp [hpc3, hpc1, hpc]) rfl)
        (show WordMem w S3.mem from (WordMem.exec (s := { S1 with pc := S1.pc + 1 }) hm1w e3))
        (by omega) (by omega)).upd
      have hB4 : S4.mem rB = out.getD k 0 := by
        rw [hm4, if_pos rfl, hT3, hm3, if_neg (by omega)]
        show S1.mem _ = _
        rw [hm1, if_neg (by omega)]
        exact hbuf k hkl
      have hm4w := (WordMem.exec (s := { S1 with pc := S1.pc + 1 }) hm1w e3).exec e4
      have e5 := x_write (w := w) (s := S4) (fetch hf (i := 5) (by simp [hpc4, hpc3, hpc1, hpc])
        rfl) hm4w (by omega)
      obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_add (w := w)
        (s := { S4 with pc := S4.pc + 1, out := S4.out ++ [S4.mem rB] })
        (fetch hf (i := 6) (by simp [hpc4, hpc3, hpc1, hpc]) rfl) (by omega) (by omega)
        (by omega)).upd
      have e7 := x_jump (w := w) (s := S6) (fetch hf (i := 7) (by simp [hpc6, hpc4, hpc3, hpc1,
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
      obtain ⟨S', e', hpc', hout'⟩ := ih (k + 1) { S6 with pc := lpOut G P + 1 } (by omega)
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

end

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ}

/-- The state before the run of `P`, from the start of the round. -/
structure PreP (w : ℕ) (x a b o : List ℕ) (i : ℕ) (S S2 : State) : Prop where
  inv : LInv w x a b i S
  word : WordMem w S2.mem
  zero : S2.mem rZ = 0
  one : S2.mem rOne = 1
  alloc : AllocAt S2 (lpAlloc (lpCap w) (i + 1))
  r45 : S2.mem 45 = o.length
  buf : ∀ j < o.length, S2.mem (S.mem 44 + j) = o.getD j 0
  keep : ∀ c, 15 ≤ c → (c < 16 ∨ 36 ≤ c) → c ≠ 45 → (c < 47 ∨ 50 < c) →
    (c < lpBase w i ∨ lpBase w i + lpSize w i ≤ c) → (c < S.mem 44 ∨ S.mem 44 + lpCap w ≤ c) →
    S2.mem c = S.mem c
  input : S2.input = S.input
  out : S2.out = S.out

theorem PreP.of_call (G P : Program) {x a b o : List ℕ} {i : ℕ} {S S1 S2 : State}
    (L : LInv w x a b i S) (hO : PhaseOut w i (S.mem 44) S S1 o) (e : Exec w (lpProg G P) 4 S1 S2)
    (h45 : S2.mem 45 = o.length) (hfr : ∀ c, c ≠ rB → c ≠ 45 → S2.mem c = S1.mem c)
    (hi : S2.input = S1.input) (ho : S2.out = S1.out) (hw : 8 ≤ w) : PreP w x a b o i S S2 := by
  have hC := lpCap_bounds hw
  have hob : 64 ≤ S.mem 44 := by rcases L.acur with h | h <;> rw [h] <;> omega
  exact
    { inv := L
      word := hO.word.exec e
      zero := by rw [hfr _ (by decide) (by decide)]; exact hO.zero
      one := by rw [hfr _ (by decide) (by decide)]; exact hO.one
      alloc := by
        obtain ⟨a1, a2, a3, a4⟩ := hO.alloc
        exact ⟨by rw [hfr _ (by decide) (by decide)]; exact a1,
          by rw [hfr _ (by decide) (by decide)]; exact a2,
          by rw [hfr _ (by decide) (by decide)]; exact a3,
          by rw [hfr _ (by decide) (by decide)]; exact a4⟩
      r45 := h45
      buf := fun j hj => by rw [hfr _ (by omega) (by omega)]; exact hO.buf j hj
      keep := fun c a1 a2 a0 a3 a4 a5 => by
        rw [hfr _ (by omega) a0]; exact hO.keep c a1 a2 a3 a4 a5
      input := by rw [hi]; exact hO.input
      out := by rw [ho]; exact hO.out }

theorem PreP.pre {x a b o : List ℕ} {i : ℕ} {S S2 : State} (Q : PreP w x a b o i S S2)
    (hw : 8 ≤ w) (hs : lpSize w (i + 1) ≠ 0) : PhasePre w (i + 1) 46 S2 := by
  have hC := lpCap_bounds hw
  have L := Q.inv
  have hob : 64 ≤ S.mem 44 := by rcases L.acur with h | h <;> rw [h] <;> omega
  have hroom := lpAlloc_room (lpCap w) i
  have hnext := lpAlloc_next_mono (lpCap w) i
  have hsz : lpSize w i ≤ 2 * lpCap w + 64 := by simp only [lpSize]; omega
  have h64 := lpAlloc_next_ge (lpCap w) i
  have h64' := lpAlloc_next_ge (lpCap w) (i + 1)
  refine ⟨Q.word, Q.zero, Q.one, ?_, ?_, Q.alloc, hs, ?_, ?_⟩
  · rw [Q.keep 52 (by omega) (by omega) (by omega) (by omega) (by simp only [lpBase, lpSize]; omega)
      (by omega)]; exact L.four
  · rw [Q.keep 51 (by omega) (by omega) (by omega) (by omega) (by simp only [lpBase, lpSize]; omega)
      (by omega)]; exact L.cap
  · intro c h1 h2
    have h1' : lpBase w i + lpSize w i ≤ c := by
      simp only [lpBase, lpSize] at h1 ⊢; omega
    have h64 : 64 ≤ c := by
      have := lpAlloc_next_ge (lpCap w) (i + 1); simp only [lpBase] at h1; omega
    rw [Q.keep c (by omega) (by omega) (by omega) (by omega) (Or.inr h1') (by
      rcases L.acur with h | h <;> rw [h] <;> omega)]
    exact L.fresh c (by simp only [lpBase] at h1 ⊢; omega) h2
  · rw [Q.keep 46 (by omega) (by omega) (by omega) (by omega) (by simp only [lpBase, lpSize]; omega)
      (by omega)]
    rcases L.pcur with h | h <;> rw [h] <;> omega

theorem PreP.src {x a b o : List ℕ} {i : ℕ} {S S2 : State} (Q : PreP w x a b o i S S2)
    (hw : 8 ≤ w) (hs : lpSize w (i + 1) ≠ 0) (ho : o.length ≤ lpCap w) :
    ∀ j, SrcOK w (LpBusy w (i + 1) (S2.mem 46) lpRhoP.length) S2 (lpSrcsP j) (![o] j) := by
  have hC := lpCap_bounds hw
  have L := Q.inv
  have hN : lpRhoP.length ≤ 6 := by simp [lpRhoP]
  have h44 : S2.mem 44 = S.mem 44 := Q.keep 44 (by omega) (by omega) (by omega) (by omega)
    (by have := lpAlloc_next_ge (lpCap w) i; simp only [lpBase]; omega)
    (by rcases L.acur with h | h <;> rw [h] <;> omega)
  have h46 : S2.mem 46 = S.mem 46 := Q.keep 46 (by omega) (by omega) (by omega) (by omega)
    (by have := lpAlloc_next_ge (lpCap w) i; simp only [lpBase]; omega)
    (by rcases L.acur with h | h <;> rw [h] <;> omega)
  have hob : 64 ≤ S2.mem 46 := by rw [h46]; rcases L.pcur with h | h <;> rw [h] <;> omega
  intro j
  fin_cases j
  show SrcOK w _ S2 ⟨.mem 44, 45⟩ o
  refine srcOK_mem Q.word Q.r45 (by omega) (by omega)
    (lpBusy_mid (by omega) (by omega) (by omega) hob hN) (by omega)
    (lpBusy_mid (by omega) (by omega) (by omega) hob hN) ?_ (by rw [h44]; exact Q.buf) ?_
  · rw [h44]; rcases L.acur with h | h <;> rw [h] <;> omega
  · intro k hk
    rw [h44, h46]
    rcases L.acur with h | h <;> rw [h] <;> rcases L.pcur with h' | h' <;> rw [h'] <;>
      exact lpBusy_hi hw hs (by omega) (by omega) hN

theorem lpRhoP_fit {o : List ℕ} {v : ℕ} (hw : 8 ≤ w) (hv : v ≤ w - 3) (ho : o.length ≤ lpCap w)
    (hlt : ∀ e ∈ o, e < 2 ^ v) : lpRhoP.Fits w ![o] := by
  have hC := lpCap_bounds hw
  have h1 : o.getD 1 0 < 2 ^ (w - 3) := by
    have : o.getD 1 0 < 2 ^ v := by
      rw [List.getD_eq_getElem?_getD]
      cases h : o[1]? with
      | none => exact Nat.two_pow_pos v
      | some u => exact hlt u (List.mem_of_getElem? h)
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) hv)
  have : lpCap w = 2 ^ (w - 3) := rfl
  refine ⟨fun j => ?_, ?_, ?_⟩
  · fin_cases j; simp; omega
  · rw [lpRhoP_apply]; simp only [lpQ, List.length_drop]; omega
  · intro seg hseg
    simp only [lpRhoP, List.mem_cons, List.mem_nil_iff, or_false] at hseg
    subst hseg
    simp only [Segment.Fits, HExpr.Fits, HExpr.eval, Matrix.cons_val_zero]
    exact ⟨⟨trivial, by omega⟩, by omega⟩

end Lax185574Proofs.RamSim
