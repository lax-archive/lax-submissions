import Lax185574Proofs.RamLoopCall

/-!
The end of a round of the loop driver: the outputs of `G` and `P`
become `a` and `b` of the next round, and the other buffers are used
next.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ}

theorem LInv.setPc {x a b : List ℕ} {i : ℕ} {S : State} (L : LInv w x a b i S) (l : ℕ) :
    LInv w x a b i { S with pc := l } :=
  { word := L.word, zero := L.zero, one := L.one, four := L.four, cap := L.cap, c4 := L.c4,
    c5 := L.c5, c6 := L.c6, c7 := L.c7, len := L.len, input := L.input, out := L.out,
    alloc := L.alloc, fresh := L.fresh, acur := L.acur, pcur := L.pcur, abuf := L.abuf,
    bbuf := L.bbuf, alen := L.alen, ale := L.ale, aval := L.aval, blen := L.blen, ble := L.ble,
    bval := L.bval }

theorem lp_swap (G P : Program) {x a b o r : List ℕ} {i : ℕ} {S S2 S3 : State} (hw : 8 ≤ w)
    (Q : PreP w x a b o i S S2) (hO : PhaseOut w (i + 1) (S2.mem 46) S2 S3 r)
    (hpc : S3.pc = lpExitP G P) (ho : o.length ≤ lpCap w) (hr : r.length ≤ lpCap w)
    (hs : lpSize w (i + 1) ≠ 0) :
    ∃ S4, Exec w (lpProg G P) 9 S3 S4 ∧ S4.pc = lpLoop ∧ LInv w x o r (i + 2) S4 := by
  have hC := lpCap_bounds hw
  have L := Q.inv
  have hf := lp_fits_swap G P
  have hm := hO.word
  have h64 := lpAlloc_next_ge (lpCap w) i
  have h64' := lpAlloc_next_ge (lpCap w) (i + 1)
  have hroom := lpAlloc_room (lpCap w) (i + 1)
  have hmono := lpAlloc_next_mono (lpCap w) i
  have hmono' : (lpAlloc (lpCap w) (i + 1)).next + (lpAlloc (lpCap w) (i + 1)).size ≤
      (lpAlloc (lpCap w) (i + 2)).next := lpAlloc_next_mono (lpCap w) (i + 1)
  have hroom0 := lpAlloc_room (lpCap w) i
  set A := S.mem 44 with hA
  set B := S.mem 46 with hB
  have hAv : A = 4 * lpCap w ∨ A = 5 * lpCap w := L.acur
  have hBv : B = 6 * lpCap w ∨ B = 7 * lpCap w := L.pcur
  have hA64 : 64 ≤ A := by omega
  -- cells of `S3` read from `S` through both phases
  have k2 : ∀ c, 15 ≤ c → (c < 16 ∨ 36 ≤ c) → c ≠ 45 → (c < 47 ∨ 50 < c) → c < 64 →
      S2.mem c = S.mem c := fun c a1 a2 a3 a4 a5 =>
    Q.keep c a1 a2 a3 a4 (Or.inl (by simp only [lpBase]; omega)) (Or.inl (by omega))
  have h46 : S2.mem 46 = B := k2 46 (by omega) (by omega) (by omega) (by omega) (by omega)
  have hB64 : 64 ≤ S2.mem 46 := by rw [h46]; omega
  have k3 : ∀ c, 15 ≤ c → (c < 16 ∨ 36 ≤ c) → (c < 47 ∨ 50 < c) → c < 64 →
      S3.mem c = S2.mem c := fun c a1 a2 a3 a4 =>
    hO.keep c a1 a2 a3 (Or.inl (by simp only [lpBase]; omega)) (Or.inl (by omega))
  have r44 : S3.mem 44 = A := by
    rw [k3 44 (by omega) (by omega) (by omega) (by omega),
      k2 44 (by omega) (by omega) (by omega) (by omega) (by omega)]
  have r45 : S3.mem 45 = o.length := by
    rw [k3 45 (by omega) (by omega) (by omega) (by omega)]; exact Q.r45
  have r46 : S3.mem 46 = B := by rw [k3 46 (by omega) (by omega) (by omega) (by omega), h46]
  have rc : ∀ c, 51 ≤ c → c < 64 → S3.mem c = S.mem c := fun c a1 a2 => by
    rw [k3 c (by omega) (by omega) (by omega) (by omega),
      k2 c (by omega) (by omega) (by omega) (by omega) (by omega)]
  have r54 : S3.mem 54 = 4 * lpCap w := by rw [rc 54 (by omega) (by omega)]; exact L.c4
  have r55 : S3.mem 55 = 5 * lpCap w := by rw [rc 55 (by omega) (by omega)]; exact L.c5
  have r56 : S3.mem 56 = 6 * lpCap w := by rw [rc 56 (by omega) (by omega)]; exact L.c6
  have r57 : S3.mem 57 = 7 * lpCap w := by rw [rc 57 (by omega) (by omega)]; exact L.c7
  -- the swap
  obtain ⟨T1, e1, hpc1, hm1, hi1, -, ho1⟩ := (x_add (w := w) (s := S3)
    (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨T2, e2, hpc2, hm2, hi2, -, ho2⟩ := (x_add (w := w) (s := T1)
    (fetch hf (i := 1) (by simp [hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
  have hW2 := hm.exec (e1.trans e2)
  obtain ⟨T3, e3, hpc3, hm3, hi3, -, ho3⟩ := (x_sub (w := w) (s := T2)
    (fetch hf (i := 2) (by simp [hpc2, hpc1, hpc]) rfl) hW2 (by omega) (by omega) (by omega)).upd
  obtain ⟨T4, e4, hpc4, hm4, hi4, -, ho4⟩ := (x_add (w := w) (s := T3)
    (fetch hf (i := 3) (by simp [hpc3, hpc2, hpc1, hpc]) rfl) (by omega) (by omega)
    (by omega)).upd
  obtain ⟨T5, e5, hpc5, hm5, hi5, -, ho5⟩ := (x_add (w := w) (s := T4)
    (fetch hf (i := 4) (by simp [hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega) (by omega)
    (by omega)).upd
  obtain ⟨T6, e6, hpc6, hm6, hi6, -, ho6⟩ := (x_add (w := w) (s := T5)
    (fetch hf (i := 5) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega) (by omega)
    (by omega)).upd
  have hW6 := hW2.exec (((e3.trans e4).trans e5).trans e6)
  obtain ⟨T7, e7, hpc7, hm7, hi7, -, ho7⟩ := (x_sub (w := w) (s := T6)
    (fetch hf (i := 6) (by simp [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl) hW6 (by omega)
    (by omega) (by omega)).upd
  obtain ⟨T8, e8, hpc8, hm8, hi8, -, ho8⟩ := (x_add (w := w) (s := T7)
    (fetch hf (i := 7) (by simp [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega)
    (by omega) (by omega)).upd
  have e9 := x_jump (w := w) (s := T8)
    (fetch hf (i := 8) (by simp [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl)
  have e := (((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans e8).trans e9
  have f1 : ∀ c, c ≠ 40 → T1.mem c = S3.mem c := fun c h => by rw [hm1, if_neg h]
  have f2 : ∀ c, c ≠ 41 → T2.mem c = T1.mem c := fun c h => by rw [hm2, if_neg h]
  have f3 : ∀ c, c ≠ 53 → T3.mem c = T2.mem c := fun c h => by rw [hm3, if_neg h]
  have f4 : ∀ c, c ≠ 44 → T4.mem c = T3.mem c := fun c h => by rw [hm4, if_neg h]
  have f5 : ∀ c, c ≠ 42 → T5.mem c = T4.mem c := fun c h => by rw [hm5, if_neg h]
  have f6 : ∀ c, c ≠ 43 → T6.mem c = T5.mem c := fun c h => by rw [hm6, if_neg h]
  have f7 : ∀ c, c ≠ 53 → T7.mem c = T6.mem c := fun c h => by rw [hm7, if_neg h]
  have f8 : ∀ c, c ≠ 46 → T8.mem c = T7.mem c := fun c h => by rw [hm8, if_neg h]
  have z3 : S3.mem rZ = 0 := hO.zero
  have v1 : T1.mem 40 = A := by
    rw [hm1, if_pos rfl, r44, z3, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have v2 : T2.mem 41 = o.length := by
    rw [hm2, if_pos rfl, f1 _ (by decide), f1 _ (by decide), r45, z3, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega)]
  have v3 : T3.mem 53 = 5 * lpCap w - A := by
    rw [hm3, if_pos rfl]
    simp (disch := decide) only [f2, f1]
    rw [r55, r44]
  have v4 : T4.mem 44 = 4 * lpCap w + (5 * lpCap w - A) := by
    rw [hm4, if_pos rfl, v3]
    simp (disch := decide) only [f3, f2, f1]
    rw [r54, Nat.mod_eq_of_lt (by omega)]
  have v5 : T5.mem 42 = B := by
    rw [hm5, if_pos rfl]
    simp (disch := decide) only [f4, f3, f2, f1]
    rw [r46, z3, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have v6 : T6.mem 43 = r.length := by
    rw [hm6, if_pos rfl]
    simp (disch := decide) only [f5, f4, f3, f2, f1]
    rw [hO.roc, z3, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have v7 : T7.mem 53 = 7 * lpCap w - B := by
    rw [hm7, if_pos rfl]
    simp (disch := decide) only [f6, f5, f4, f3, f2, f1]
    rw [r57, r46]
  have v8 : T8.mem 46 = 6 * lpCap w + (7 * lpCap w - B) := by
    rw [hm8, if_pos rfl, v7]
    simp (disch := decide) only [f7, f6, f5, f4, f3, f2, f1]
    rw [r56, Nat.mod_eq_of_lt (by omega)]
  have g8 : ∀ c, (c < 40 ∨ 46 < c) → c ≠ 53 → T8.mem c = S3.mem c := by
    intro c h1 h2
    rw [f8 c (by omega), f7 c h2, f6 c (by omega), f5 c (by omega), f4 c (by omega),
      f3 c h2, f2 c (by omega), f1 c (by omega)]
  have r40 : T8.mem 40 = A := by simp (disch := decide) only [f8, f7, f6, f5, f4, f3, f2]; exact v1
  have r41 : T8.mem 41 = o.length := by
    simp (disch := decide) only [f8, f7, f6, f5, f4, f3]; exact v2
  have r42 : T8.mem 42 = B := by simp (disch := decide) only [f8, f7, f6]; exact v5
  have r43 : T8.mem 43 = r.length := by simp (disch := decide) only [f8, f7]; exact v6
  have r44' : T8.mem 44 = 4 * lpCap w + (5 * lpCap w - A) := by
    simp (disch := decide) only [f8, f7, f6, f5]; exact v4
  -- the far cells of `T8` are those of `S`
  have far : ∀ c, 64 ≤ c → (c < lpBase w i ∨ lpBase w i + lpSize w i ≤ c) →
      (c < lpBase w (i + 1) ∨ lpBase w (i + 1) + lpSize w (i + 1) ≤ c) →
      (c < A ∨ A + lpCap w ≤ c) → (c < B ∨ B + lpCap w ≤ c) → T8.mem c = S.mem c := by
    intro c a1 a2 a3 a4 a5
    rw [g8 c (by omega) (by omega), hO.keep c (by omega) (by omega) (by omega) a3
      (by rw [h46]; exact a5), Q.keep c (by omega) (by omega) (by omega) (by omega) a2 a4]
  refine ⟨{ T8 with pc := lpLoop }, e, rfl, ?_⟩
  have LT : LInv w x o r (i + 2) T8 :=
    { word := hm.exec (((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans
        e7).trans e8)
      zero := by rw [g8 0 (by omega) (by omega)]; exact z3
      one := by rw [g8 1 (by omega) (by omega)]; exact hO.one
      four := by rw [g8 52 (by omega) (by omega), rc 52 (by omega) (by omega)]; exact L.four
      cap := by rw [g8 51 (by omega) (by omega), rc 51 (by omega) (by omega)]; exact L.cap
      c4 := by rw [g8 54 (by omega) (by omega)]; exact r54
      c5 := by rw [g8 55 (by omega) (by omega)]; exact r55
      c6 := by rw [g8 56 (by omega) (by omega)]; exact r56
      c7 := by rw [g8 57 (by omega) (by omega)]; exact r57
      len := by
        rw [g8 15 (by omega) (by omega), k3 15 (by omega) (by omega) (by omega) (by omega),
          k2 15 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact L.len
      input := by
        rw [run_input e, hO.input, Q.input]; exact L.input
      out := by
        rw [ho8, ho7, ho6, ho5, ho4, ho3, ho2, ho1, hO.out, Q.out]; exact L.out
      alloc := by
        obtain ⟨a1, a2, a3, a4⟩ := hO.alloc
        exact ⟨by rw [g8 47 (by omega) (by omega)]; exact a1,
          by rw [g8 48 (by omega) (by omega)]; exact a2,
          by rw [g8 49 (by omega) (by omega)]; exact a3,
          by rw [g8 50 (by omega) (by omega)]; exact a4⟩
      fresh := by
        intro c h1 h2
        have := lpAlloc_next_ge (lpCap w) (i + 2)
        have h1' : lpBase w (i + 1) + lpSize w (i + 1) ≤ c := by
          simp only [lpBase, lpSize] at h1 ⊢; omega
        have h1'' : lpBase w i + lpSize w i ≤ c := by
          simp only [lpBase, lpSize] at h1 ⊢; omega
        rw [far c (by simp only [lpBase] at h1; omega) (Or.inr h1'') (Or.inr h1') (Or.inl (by omega)) (Or.inl (by omega))]
        exact L.fresh c (by simp only [lpBase] at h1 ⊢; omega) h2
      acur := by rw [r44']; omega
      pcur := by rw [v8]; omega
      abuf := Or.inr (by rw [r40, r44']; omega)
      bbuf := Or.inr (by rw [r42, v8]; omega)
      alen := r41
      ale := ho
      aval := by
        intro k hk
        rw [r40, g8 (A + k) (by omega) (by omega), hO.keep (A + k) (by omega) (by omega)
          (by omega) (Or.inr (by simp only [lpBase, lpSize]; omega)) (by rw [h46]; omega)]
        exact Q.buf k hk
      blen := r43
      ble := hr
      bval := by
        intro k hk
        rw [r42, g8 (B + k) (by omega) (by omega), ← h46]
        exact hO.buf k hk }
  exact LT.setPc lpLoop

end Lax185574Proofs.RamSim
