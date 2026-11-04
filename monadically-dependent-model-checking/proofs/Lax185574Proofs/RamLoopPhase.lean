import Lax185574Proofs.RamLoopCode

/-!
One phase of the loop driver: take a fresh region, set up the output
buffer, and launch the simulation of a program on a rewrite of words in
memory.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ} {p : Program}

/-- The cells of the allocator hold the allocation state `A`. -/
def AllocAt (S : State) (A : Alloc) : Prop :=
  S.mem 47 = A.next ∧ S.mem 48 = A.size ∧ S.mem 49 = A.cnt ∧ S.mem 50 = A.lim

theorem lpAlloc_lim_lt {C i : ℕ} (hs : (lpAlloc C i).size ≠ 0) {w : ℕ} (hC : 2 * C < 2 ^ w) :
    2 * (lpAlloc C i).lim < 2 ^ w := by
  obtain ⟨-, h2, h3, -, -⟩ := lpAlloc_inv C i
  rw [h2]
  rw [h3] at hs
  generalize (lpAlloc C i).bat = j at *
  have h4 : 4 ^ j ≤ C := by
    by_contra h; exact hs (Nat.div_eq_of_lt (by omega))
  have h5 : 2 * 2 ^ j ≤ 4 ^ j + 1 := by
    rw [show (4 : ℕ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    nlinarith
  omega

/-- Taking region `i`: base and mask of the region, and the allocator
moves on to region `i + 1`. -/
theorem lp_alloc {die A C i : ℕ} {S : State} (hf : Fits p A (lpAllocCode die A)) (hpc : S.pc = A)
    (hm : WordMem w S.mem) (h0 : S.mem rZ = 0) (h1 : S.mem rOne = 1) (h4 : S.mem 52 = 4)
    (hA : AllocAt S (lpAlloc C i)) (hs : (lpAlloc C i).size ≠ 0) (hC : 64 + 2 * C < 2 ^ w) :
    ∃ n ≤ 11, ∃ S', Exec w p n S S' ∧ S'.pc = A + 11 ∧
      S'.mem rBase = (lpAlloc C i).next ∧ S'.mem rMask = (lpAlloc C i).size - 1 ∧
      AllocAt S' (lpAlloc C (i + 1)) ∧
      (∀ c, c ≠ rBase → c ≠ rMask → c ≠ rU → c ≠ 47 → c ≠ 48 → c ≠ 49 → c ≠ 50 →
        S'.mem c = S.mem c) ∧ S'.input = S.input ∧ S'.inp = S.inp ∧ S'.out = S.out := by
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hA
  obtain ⟨i1, -, -, -, -⟩ := lpAlloc_inv C i
  have hroom := lpAlloc_room C i
  have hlim := lpAlloc_lim_lt hs (w := w) (by omega)
  have hw : 64 < 2 ^ w := by omega
  set Al := lpAlloc C i with hAl
  have e0 := x_jzero_neg (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)
    (by rw [hA2]; exact hs)
  obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_add (w := w) (s := { S with pc := S.pc + 1 })
    (fetch hf (i := 1) (by simp [hpc]) rfl) (by omega) (by omega) (by omega)).upd
  have hW1 : WordMem w S1.mem := hm.exec (e0.trans e1)
  obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_sub (w := w) (s := S1)
    (fetch hf (i := 2) (by simp [hpc1, hpc]) rfl) hW1 (by omega) (by omega) (by omega)).upd
  obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_add (w := w) (s := S2)
    (fetch hf (i := 3) (by simp [hpc2, hpc1, hpc]) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_add (w := w) (s := S3)
    (fetch hf (i := 4) (by simp [hpc3, hpc2, hpc1, hpc]) rfl) (by omega) (by omega)
    (by omega)).upd
  have hW4 : WordMem w S4.mem := hW1.exec (((e2.trans e3).trans e4))
  obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_sub (w := w) (s := S4)
    (fetch hf (i := 5) (by simp [hpc4, hpc3, hpc2, hpc1, hpc]) rfl) hW4 (by omega) (by omega)
    (by omega)).upd
  -- values so far
  have v47 : S4.mem 47 = Al.next + Al.size := by
    simp only [hm4, hm3, hm2, hm1]; simp [hA1, hA2, Nat.mod_eq_of_lt (show Al.next + Al.size < 2 ^ w by omega)]
  have v49 : S4.mem 49 = Al.cnt + 1 := by
    simp only [hm4, hm3, hm2, hm1]; simp [hA3, h1, Nat.mod_eq_of_lt (show Al.cnt + 1 < 2 ^ w by omega)]
  have vB : S4.mem rBase = Al.next := by
    simp only [hm4, hm3, hm2, hm1]; simp [hA1, h0, Nat.mod_eq_of_lt (show Al.next < 2 ^ w by omega)]
  have vM : S4.mem rMask = Al.size - 1 := by
    simp only [hm4, hm3, hm2, hm1]; simp [hA2, h1]
  have f4 : ∀ c, c ≠ rBase → c ≠ rMask → c ≠ 47 → c ≠ 49 → S4.mem c = S.mem c := by
    intro c a1 a2 a3 a4
    rw [hm4, if_neg a4, hm3, if_neg a3, hm2, if_neg a2, hm1, if_neg a1]
  have v50 : S4.mem 50 = Al.lim := by rw [f4 _ (by decide) (by decide) (by decide) (by decide), hA4]
  have v48 : S4.mem 48 = Al.size := by rw [f4 _ (by decide) (by decide) (by decide) (by decide), hA2]
  have hU : S5.mem rU = Al.lim - (Al.cnt + 1) := by rw [hm5, if_pos rfl, v50, v49]
  have hW5 : WordMem w S5.mem := hW4.exec e5
  have f5 : ∀ c, c ≠ rU → S5.mem c = S4.mem c := fun c h => by rw [hm5, if_neg h]
  have hio : S5.input = S.input ∧ S5.inp = S.inp ∧ S5.out = S.out := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hi5, hi4, hi3, hi2, hi1]
    · rw [hn5, hn4, hn3, hn2, hn1]
    · rw [ho5, ho4, ho3, ho2, ho1]
  have e05 := ((((e0.trans e1).trans e2).trans e3).trans e4).trans e5
  by_cases hb : Al.cnt + 1 = Al.lim
  · -- a new batch
    have e6 := x_jzero_pos (w := w) (s := S5)
      (fetch hf (i := 6) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega)
      (by rw [hU]; omega)
    obtain ⟨S7, e7, hpc7, hm7, hi7, hn7, ho7⟩ := (x_set (w := w) (s := { S5 with pc := A + 8 })
      (fetch hf (i := 8) rfl rfl) (by omega)).upd
    obtain ⟨S8, e8, hpc8, hm8, hi8, hn8, ho8⟩ := (x_add (w := w) (s := S7)
      (fetch hf (i := 9) (by simp [hpc7]) rfl) (by omega) (by omega) (by omega)).upd
    have hW8 : WordMem w S8.mem := hW5.exec ((e6.trans e7).trans e8)
    obtain ⟨S9, e9, hpc9, hm9, hi9, hn9, ho9⟩ := (x_div (w := w) (s := S8)
      (fetch hf (i := 10) (by simp [hpc8, hpc7]) rfl) hW8 (by omega) (by omega) (by omega)).upd
    have hstep : lpAlloc C (i + 1) = ⟨Al.next + Al.size, Al.size / 4, 0, 2 * Al.lim, Al.bat + 1⟩ := by
      show Al.step = _; simp [Alloc.step, hb]
    have f9 : ∀ c, c ≠ 48 → c ≠ 49 → c ≠ 50 → S9.mem c = S5.mem c := by
      intro c a1 a2 a3
      rw [hm9, if_neg a1, hm8, if_neg a3, hm7, if_neg a2]
    refine ⟨1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1, by omega, S9,
      (((e05.trans e6).trans e7).trans e8).trans e9, by rw [hpc9, hpc8, hpc7], ?_, ?_, ?_, ?_,
      by rw [hi9, hi8, hi7]; exact hio.1, by rw [hn9, hn8, hn7]; exact hio.2.1,
      by rw [ho9, ho8, ho7]; exact hio.2.2⟩
    · rw [f9 _ (by decide) (by decide) (by decide), f5 _ (by decide)]; exact vB
    · rw [f9 _ (by decide) (by decide) (by decide), f5 _ (by decide)]; exact vM
    · rw [hstep]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [f9 _ (by decide) (by decide) (by decide), f5 _ (by decide)]; exact v47
      · have a1 : S8.mem 48 = Al.size := by
          rw [hm8, if_neg (by decide), hm7, if_neg (by decide), f5 _ (by decide), v48]
        have a2 : S8.mem 52 = 4 := by
          rw [hm8, if_neg (by decide), hm7, if_neg (by decide), f5 _ (by decide),
            f4 _ (by decide) (by decide) (by decide) (by decide), h4]
        rw [hm9, if_pos rfl, a1, a2]
      · rw [hm9, if_neg (by decide), hm8, if_neg (by decide), hm7, if_pos rfl]; simp
      · have a1 : S7.mem 50 = Al.lim := by
          rw [hm7, if_neg (by decide), f5 _ (by decide), v50]
        rw [hm9, if_neg (by decide), hm8, if_pos rfl, a1, Nat.mod_eq_of_lt (by omega)]; ring
    · intro c a1 a2 a3 a4 a5 a6 a7
      rw [f9 _ a5 a6 a7, f5 _ a3, f4 _ a1 a2 a4 a6]
  · -- the same batch
    have hU0 : S5.mem rU ≠ 0 := by rw [hU]; omega
    have e6 := x_jzero_neg (w := w) (s := S5)
      (fetch hf (i := 6) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl) (by omega) hU0
    have e7 := x_jump (w := w) (s := { S5 with pc := S5.pc + 1 })
      (fetch hf (i := 7) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]) rfl)
    have hstep : lpAlloc C (i + 1) = ⟨Al.next + Al.size, Al.size, Al.cnt + 1, Al.lim, Al.bat⟩ := by
      show Al.step = _; simp [Alloc.step, hb]
    refine ⟨1 + 1 + 1 + 1 + 1 + 1 + 1 + 1, by omega, _, (e05.trans e6).trans e7, rfl, ?_, ?_, ?_,
      ?_, hio⟩
    · show S5.mem rBase = _; rw [f5 _ (by decide)]; exact vB
    · show S5.mem rMask = _; rw [f5 _ (by decide)]; exact vM
    · rw [hstep]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show S5.mem 47 = _; rw [f5 _ (by decide)]; exact v47
      · show S5.mem 48 = _; rw [f5 _ (by decide)]; exact v48
      · show S5.mem 49 = _; rw [f5 _ (by decide)]; exact v49
      · show S5.mem 50 = _; rw [f5 _ (by decide)]; exact v50
    · intro c a1 a2 a3 a4 a5 a6 a7
      show S5.mem c = _
      rw [f5 _ a3, f4 _ a1 a2 a4 a6]

/-- An exhausted allocator ends in the loop at `die`. -/
theorem lp_alloc_die {die A C i : ℕ} {S : State} (hf : Fits p A (lpAllocCode die A))
    (hpc : S.pc = A) (hA : AllocAt S (lpAlloc C i)) (hs : (lpAlloc C i).size = 0)
    (hw : 64 < 2 ^ w) : Exec w p 1 S { S with pc := die } :=
  x_jzero_pos (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega) (by rw [hA.2.1, hs])

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ} {p : Program}

/-- The geometry of the run in region `i` with output buffer at `ob`. -/
def lpGeo (w i ob : ℕ) : Geo := ⟨lpV w i, lpBase w i, ob, lpCap w⟩

/-- The cells a phase may change before or during its launch, and the
cells its run may write. Sources must avoid them. -/
def LpBusy (w i ob N : ℕ) (a : ℕ) : Prop :=
  (lpGeo w i ob).W a ∨ LaunchW 16 N 28 8 a ∨ a < 15 ∨ (47 ≤ a ∧ a ≤ 50)

theorem lpCap_bounds {w : ℕ} (hw : 8 ≤ w) : 32 ≤ lpCap w ∧ 2 ^ w = 8 * lpCap w := by
  simp only [lpCap]
  refine ⟨?_, ?_⟩
  · calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (w - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega

theorem lpV_le (w i : ℕ) : lpV w i ≤ w := by simp only [lpV]; omega

/-- One phase: take region `i`, point the output at the buffer whose
base is in `obc`, and launch the simulation on `ρ xs`. -/
theorem lp_phase {s : ℕ} (srcs : Fin s → Src) (ρ : Rewrite s) (xs : Fin s → List ℕ)
    {die A i obc : ℕ} {S : State}
    (hf : Fits p A (lpAllocCode die A ++ lpPrelude obc ++ rwCode srcs 28 16 ρ 0 (A + 16)))
    (hpc : S.pc = A) (hw : 8 ≤ w) (hm : WordMem w S.mem) (h0 : S.mem rZ = 0)
    (h1 : S.mem rOne = 1) (h4 : S.mem 52 = 4) (hcap : S.mem 51 = lpCap w)
    (hA : AllocAt S (lpAlloc (lpCap w) i)) (hs : lpSize w i ≠ 0)
    (hzero : ∀ c, lpBase w i ≤ c → c < 4 * lpCap w → S.mem c = 0)
    (hob : 4 * lpCap w ≤ S.mem obc ∧ S.mem obc + lpCap w ≤ 2 ^ w) (hobc : 15 ≤ obc)
    (hobc' : obc < 47) 
    (hsrc : ∀ j, SrcOK w (LpBusy w i (S.mem obc) ρ.length) S (srcs j) (xs j))
    (hfit : ρ.Fits w xs) (hseg : ∀ seg ∈ ρ, seg.size + 3 ≤ 8) (hlen : 16 + 2 * ρ.length ≤ 28) :
    ∃ n ≤ 16 + 11 * (ρ.map (·.cost xs)).sum, ∃ S', Exec w p n S S' ∧
      S'.pc = A + 16 + (rwCode srcs 28 16 ρ 0 (A + 16)).length ∧
      Rel w (lpGeo w i (S.mem obc)) (ρ.map (segKind srcs)) 16 (.buffer die) (ρ.apply xs) S.out
        (initState (ρ.apply xs)) S' ∧
      AllocAt S' (lpAlloc (lpCap w) (i + 1)) ∧
      (∀ c, 15 ≤ c → (c < 16 ∨ 36 ≤ c) → (c < 47 ∨ 50 < c) → S'.mem c = S.mem c) ∧
      S'.input = S.input ∧ S'.inp = S.inp ∧ S'.out = S.out := by
  obtain ⟨hC32, hCw⟩ := lpCap_bounds hw
  rw [fits_append, fits_append] at hf
  obtain ⟨⟨hfA, hfP⟩, hfR⟩ := hf
  simp only [lpAllocCode, lpPrelude, List.length_cons, List.length_nil] at hfP hfR
  obtain ⟨n₁, hn₁, S1, e1, hpc1, hB1, hM1, hA1, fr1, hi1, hn1, ho1⟩ :=
    lp_alloc hfA hpc hm h0 h1 h4 hA hs (by omega)
  have hW1 := hm.exec e1
  have g1 : ∀ c, 15 ≤ c → c < 47 ∨ 50 < c → S1.mem c = S.mem c := fun c a b =>
    fr1 c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- the prelude
  obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_set (w := w) (s := S1)
    (fetch hfP (i := 0) (by simp [hpc1]) rfl) (by omega)).upd
  obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_set (w := w) (s := S2)
    (fetch hfP (i := 1) (by simp [hpc2, hpc1]) rfl) (by omega)).upd
  obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_add (w := w) (s := S3)
    (fetch hfP (i := 2) (by simp [hpc3, hpc2, hpc1]) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_set (w := w) (s := S4)
    (fetch hfP (i := 3) (by simp [hpc4, hpc3, hpc2, hpc1]) rfl) (by omega)).upd
  obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_add (w := w) (s := S5)
    (fetch hfP (i := 4) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1]) rfl) (by omega) (by omega)
    (by omega)).upd
  have e26 := (((e2.trans e3).trans e4).trans e5).trans e6
  have hW6 := hW1.exec e26
  have f6 : ∀ c, c ≠ rCur → c ≠ rTot → c ≠ rOB → c ≠ rOC → c ≠ rCap → S6.mem c = S1.mem c := by
    intro c a1 a2 a3 a4 a5
    rw [hm6, if_neg a5, hm5, if_neg a4, hm4, if_neg a3, hm3, if_neg a2, hm2, if_neg a1]
  have k5 : ∀ c, c ≠ rCur → c ≠ rTot → c ≠ rOB → c ≠ rOC → S5.mem c = S1.mem c := by
    intro c a1 a2 a3 a4
    rw [hm5, if_neg a4, hm4, if_neg a3, hm3, if_neg a2, hm2, if_neg a1]
  have hz1 : S1.mem rZ = 0 := by
    rw [fr1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h0
  have hob6 : S6.mem rOB = S.mem obc := by
    rw [hm6, if_neg (by decide), hm5, if_neg (by decide), hm4, if_pos rfl, hm3,
      if_neg (by omega), hm2, if_neg (by omega), hm3, if_neg (by decide), hm2, if_neg (by decide),
      hz1, g1 obc hobc (Or.inl hobc'), Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have hcap6 : S6.mem rCap = lpCap w := by
    rw [hm6, if_pos rfl, k5 51 (by decide) (by decide) (by decide) (by decide),
      k5 0 (by decide) (by decide) (by decide) (by decide), hz1, g1 51 (by decide) (by decide),
      hcap, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have hcur6 : S6.mem rCur = 0 := by simp only [hm6, hm5, hm4, hm3, hm2]; simp
  have htot6 : S6.mem rTot = 0 := by simp only [hm6, hm5, hm4, hm3]; simp
  have hoc6 : S6.mem rOC = 0 := by simp only [hm6, hm5]; simp
  have hio6 : S6.input = S.input ∧ S6.inp = S.inp ∧ S6.out = S.out := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hi6, hi5, hi4, hi3, hi2, hi1]
    · rw [hn6, hn5, hn4, hn3, hn2, hn1]
    · rw [ho6, ho5, ho4, ho3, ho2, ho1]
  have g6 : ∀ c, 15 ≤ c → c < 47 ∨ 50 < c → S6.mem c = S.mem c := fun c a b => by
    rw [f6 c (by omega) (by omega) (by omega) (by omega) (by omega), g1 c a b]
  -- the region
  have hsz := lpSize_eq hs
  have hroom := lpAlloc_room (lpCap w) i
  have hbase64 := lpAlloc_next_ge (lpCap w) i
  have hgv : (lpGeo w i (S.mem obc)).v = lpV w i := rfl
  have hgb : (lpGeo w i (S.mem obc)).base = lpBase w i := rfl
  have hsz' : (lpAlloc (lpCap w) i).size = 2 ^ lpV w i := hsz
  have z6 : S6.mem rZ = 0 := by
    rw [f6 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz1
  have o6 : S6.mem rOne = 1 := by
    rw [f6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h1
  have m6 : S6.mem rMask = 2 ^ (lpGeo w i (S.mem obc)).v - 1 := by
    rw [f6 _ (by decide) (by decide) (by decide) (by decide) (by decide), hM1, hsz']; rfl
  have b6 : S6.mem rBase = (lpGeo w i (S.mem obc)).base := by
    rw [f6 _ (by decide) (by decide) (by decide) (by decide) (by decide), hB1]; rfl
  have r6 : (lpGeo w i (S.mem obc)).base + 2 ^ (lpGeo w i (S.mem obc)).v ≤ 2 ^ w := by
    rw [hgb, hgv, ← hsz']; simp only [lpBase]; omega
  have l6 : 16 ≤ (lpGeo w i (S.mem obc)).base := by rw [hgb]; simp only [lpBase]; omega
  have E6 : Env w (lpGeo w i (S.mem obc)).v (lpGeo w i (S.mem obc)).base S6 := ⟨hW6, z6, o6, m6, b6, r6, l6, lpV_le w i⟩
  have hreg : ∀ a < 2 ^ (lpGeo w i (S.mem obc)).v, S6.mem ((lpGeo w i (S.mem obc)).base + a) = 0 := by
    intro a ha
    rw [hgv, ← hsz'] at ha
    rw [g6 _ (by rw [hgb]; simp only [lpBase]; omega) (by rw [hgb]; simp only [lpBase]; omega)]
    exact hzero _ (by rw [hgb]; omega) (by rw [hgb]; simp only [lpBase]; omega)
  have hsrc6 : ∀ j, SrcOK w (fun a => (lpGeo w i (S.mem obc)).W a ∨ LaunchW 16 ρ.length 28 8 a) S6 (srcs j) (xs j) := by
    intro j
    refine ((hsrc j).frame (fun a ha => ?_) hio6.1).anti (fun a h => by
      simp only [LpBusy]; tauto)
    simp only [LpBusy, not_or] at ha
    exact g6 a (by omega) (by omega)
  obtain ⟨n₃, hn₃, S7, e7, hpc7, R7, fr7, hi7, hn7, ho7⟩ := launch_spec srcs 16 28 8 (lpGeo w i (S.mem obc))
    (.buffer die) xs ρ (A + 16) S6 hfR (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]) E6 hsrc6
    hfit hseg le_rfl hlen (by omega)
    (fun a h1 h2 => by simp only [lpGeo, Geo.W, lpBase]; omega)
    hcur6 htot6 hreg
    (fun a ha => by
      simp only [LaunchW] at ha
      show ¬ ((lpAlloc (lpCap w) i).next ≤ a ∧ a < (lpAlloc (lpCap w) i).next + 2 ^ lpV w i)
      omega)
    ⟨rfl, hob6, by rw [hoc6]; rfl, hcap6, by simp [initState], by show 16 ≤ S.mem obc; omega,
      hob.2, Or.inr (by
        show (lpAlloc (lpCap w) i).next + 2 ^ lpV w i ≤ S.mem obc
        rw [← hsz']; omega),
      fun j hj => by simp [initState] at hj⟩
    (fun a ha => by
      simp only [LaunchW] at ha
      show ¬ (S.mem obc ≤ a ∧ a < S.mem obc + lpCap w)
      omega)
  refine ⟨n₁ + (1 + 1 + 1 + 1 + 1) + n₃, by omega, S7, (e1.trans e26).trans e7, hpc7, ?_, ?_,
    ?_, by rw [hi7, hio6.1], by rw [hn7, hio6.2.1], by rw [ho7, hio6.2.2]⟩
  · rw [hio6.2.2] at R7; exact R7
  · have h7 : ∀ c, c = 47 ∨ c = 48 ∨ c = 49 ∨ c = 50 → S7.mem c = S1.mem c := by
      intro c hc
      rw [fr7 c (by simp only [LaunchW]; omega), f6 c (by omega) (by omega) (by omega)
        (by omega) (by omega)]
    obtain ⟨a1, a2, a3, a4⟩ := hA1
    exact ⟨by rw [h7 47 (by omega)]; exact a1, by rw [h7 48 (by omega)]; exact a2,
      by rw [h7 49 (by omega)]; exact a3, by rw [h7 50 (by omega)]; exact a4⟩
  · intro c a b d
    rw [fr7 c (by simp only [LaunchW]; omega), g6 c a d]

end Lax185574Proofs.RamSim
