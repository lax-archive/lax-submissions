import Lax185574Proofs.RamLoopLayout

/-!
A complete phase of the loop driver, forward and backward: from the
allocation of the region to the exit of the simulated program, with its
output in the buffer.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ} {p : Program}

/-- What a phase needs from the state at its start. -/
structure PhasePre (w i obc : ℕ) (S : State) : Prop where
  word : WordMem w S.mem
  zero : S.mem rZ = 0
  one : S.mem rOne = 1
  four : S.mem 52 = 4
  cap : S.mem 51 = lpCap w
  alloc : AllocAt S (lpAlloc (lpCap w) i)
  size : lpSize w i ≠ 0
  fresh : ∀ c, lpBase w i ≤ c → c < 4 * lpCap w → S.mem c = 0
  ob : 4 * lpCap w ≤ S.mem obc ∧ S.mem obc + lpCap w ≤ 2 ^ w

/-- The state after a phase that output `y` into the buffer at `ob`. -/
structure PhaseOut (w i ob : ℕ) (S S' : State) (y : List ℕ) : Prop where
  word : WordMem w S'.mem
  zero : S'.mem rZ = 0
  one : S'.mem rOne = 1
  rob : S'.mem rOB = ob
  roc : S'.mem rOC = y.length
  buf : ∀ j < y.length, S'.mem (ob + j) = y.getD j 0
  alloc : AllocAt S' (lpAlloc (lpCap w) (i + 1))
  keep : ∀ c, 15 ≤ c → (c < 16 ∨ 36 ≤ c) → (c < 47 ∨ 50 < c) →
    (c < lpBase w i ∨ lpBase w i + lpSize w i ≤ c) → (c < ob ∨ ob + lpCap w ≤ c) →
    S'.mem c = S.mem c
  input : S'.input = S.input
  out : S'.out = S.out

theorem lpGeo_not_W {w i ob c : ℕ} (hc : 15 ≤ c) (hc' : c < 64) (hob : 64 ≤ ob) :
    ¬ (lpGeo w i ob).W c := by
  have := lpAlloc_next_ge (lpCap w) i
  simp only [lpGeo, Geo.W, lpBase]; omega

section phase

variable {s : ℕ} (srcs : Fin s → Src) (ρ : Rewrite s) (xs : Fin s → List ℕ)
variable (C : Code) {p₀ pre post : Program} {die A H L i obc : ℕ}

/-- **A phase, forward.** -/
theorem lp_phase_fwd
    (hf : Fits p A (lpAllocCode die A ++ lpPrelude obc ++ rwCode srcs 28 16 ρ 0 (A + 16)))
    (hH : H = A + 16 + (rwCode srcs 28 16 ρ 0 (A + 16)).length)
    (hp : p = pre ++ blocks C H L p₀ ++ post) (hpre : pre.length = H) (hL : L = blockLen C.ks)
    (hks : C.ks = ρ.map (segKind srcs)) (htb : C.tb = 16) (hmode : C.mode = .buffer die)
    (htgt : ∀ l, C.tgt l = if l < p₀.length then H + L * l else C.exit)
    (hexit : C.exit = H + L * p₀.length)
    {S : State} (hpc : S.pc = A) (hw : 8 ≤ w) (hP : PhasePre w i obc S)
    (hobc : 15 ≤ obc) (hobc' : obc < 47)
    (hsrc : ∀ j, SrcOK w (LpBusy w i (S.mem obc) ρ.length) S (srcs j) (xs j))
    (hfit : ρ.Fits w xs) (hseg : ∀ seg ∈ ρ, seg.size + 3 ≤ 8) (hlen : 16 + 2 * ρ.length ≤ 28)
    {y : List ℕ} {t : ℕ} (hrun : RunsTo (lpV w i) p₀ (ρ.apply xs) y t) (hy : y.length ≤ lpCap w) :
    ∃ n ≤ 16 + 11 * (ρ.map (·.cost xs)).sum + stepBound C.ks * (t + 1), ∃ S',
      Exec w p n S S' ∧ S'.pc = C.exit ∧ PhaseOut w i (S.mem obc) S S' y := by
  obtain ⟨n₁, hn₁, S1, e1, hpc1, R1, hA1, fr1, hi1, -, ho1⟩ := lp_phase srcs ρ xs hf hpc hw
    hP.word hP.zero hP.one hP.four hP.cap hP.alloc hP.size hP.fresh hP.ob hobc hobc' hsrc hfit
    hseg hlen
  obtain ⟨k, s_end, hr, hs, hyo, ht⟩ := hrun
  have hpc1' : S1.pc = C.tgt (initState (ρ.apply xs)).pc := by
    rw [hpc1, htgt, ← hH]
    show H = if 0 < p₀.length then H + L * 0 else C.exit
    split_ifs with h
    · simp
    · rw [hexit, show p₀.length = 0 by omega]; simp
  have R1' : Rel w (lpGeo w i (S.mem obc)) C.ks C.tb C.mode (ρ.apply xs) S.out
      (initState (ρ.apply xs)) S1 := by rw [hks, htb, hmode]; exact R1
  obtain ⟨n₂, hn₂, S2, e2, hpc2, R2, fr2⟩ := sim_run C (g := lpGeo w i (S.mem obc)) hp hpre
    (hL ▸ le_rfl) htgt k _ s_end S1 hr hs (fun ovf h => by rw [hyo]; exact hy) R1' hpc1'
  have hk : k ≤ t := by rw [ht]; omega
  refine ⟨n₁ + n₂, ?_, S2, e1.trans e2, hpc2, ?_⟩
  · have := Nat.mul_le_mul_left (stepBound C.ks) (Nat.add_le_add_right hk 1)
    omega
  have R2' := R2
  rw [hmode] at R2'
  obtain ⟨ho2, hob2, hoc2, -, -, -, -, -, hbuf2⟩ := R2'.out
  rw [hyo] at hoc2 hbuf2
  exact
    { word := R2.env.word
      zero := R2.env.zero
      one := R2.env.one
      rob := hob2
      roc := hoc2
      buf := hbuf2
      alloc := by
        obtain ⟨a1, a2, a3, a4⟩ := hA1
        have hob64 : 64 ≤ S.mem obc := by have := hP.ob.1; have := lpCap_bounds hw; omega
        exact ⟨by rw [fr2.2.2 47 (lpGeo_not_W (by decide) (by decide) hob64)]; exact a1,
          by rw [fr2.2.2 48 (lpGeo_not_W (by decide) (by decide) hob64)]; exact a2,
          by rw [fr2.2.2 49 (lpGeo_not_W (by decide) (by decide) hob64)]; exact a3,
          by rw [fr2.2.2 50 (lpGeo_not_W (by decide) (by decide) hob64)]; exact a4⟩
      keep := by
        intro c a1 a2 a3 a4 a5
        have hsz := lpSize_eq hP.size
        rw [fr2.2.2 c (by
          simp only [lpGeo, Geo.W, lpBase]
          simp only [lpSize] at hsz
          simp only [lpBase, lpSize] at a4
          omega), fr1 c a1 a2 a3]
      input := by rw [fr2.1, hi1]
      out := ho2 }

/-- **A phase, backward.** If the machine halts from the start of the
phase, the simulated program halted with an output that fits the
buffer, in no more steps. -/
theorem lp_phase_back
    (hf : Fits p A (lpAllocCode die A ++ lpPrelude obc ++ rwCode srcs 28 16 ρ 0 (A + 16)))
    (hH : H = A + 16 + (rwCode srcs 28 16 ρ 0 (A + 16)).length)
    (hp : p = pre ++ blocks C H L p₀ ++ post) (hpre : pre.length = H) (hL : L = blockLen C.ks)
    (hks : C.ks = ρ.map (segKind srcs)) (htb : C.tb = 16) (hmode : C.mode = .buffer die)
    (htgt : ∀ l, C.tgt l = if l < p₀.length then H + L * l else C.exit)
    (hexit : C.exit = H + L * p₀.length) (hdie : p[die]? = some (.jump die))
    {S : State} (hpc : S.pc = A) (hw : 8 ≤ w) (hP : PhasePre w i obc S)
    (hobc : 15 ≤ obc) (hobc' : obc < 47)
    (hsrc : ∀ j, SrcOK w (LpBusy w i (S.mem obc) ρ.length) S (srcs j) (xs j))
    (hfit : ρ.Fits w xs) (hseg : ∀ seg ∈ ρ, seg.size + 3 ≤ 8) (hlen : 16 + 2 * ρ.length ≤ 28)
    {N : ℕ} {S_end : State} (hhalt : Halts w p S N S_end) :
    ∃ y t, RunsTo (lpV w i) p₀ (ρ.apply xs) y t ∧ t ≤ N ∧ y.length ≤ lpCap w := by
  obtain ⟨n₁, -, S1, e1, hpc1, R1, -, -, -, -, -⟩ := lp_phase srcs ρ xs hf hpc hw
    hP.word hP.zero hP.one hP.four hP.cap hP.alloc hP.size hP.fresh hP.ob hobc hobc' hsrc hfit
    hseg hlen
  have hpc1' : S1.pc = C.tgt (initState (ρ.apply xs)).pc := by
    rw [hpc1, htgt, ← hH]
    show H = if 0 < p₀.length then H + L * 0 else C.exit
    split_ifs with h
    · simp
    · rw [hexit, show p₀.length = 0 by omega]; simp
  have R1' : Rel w (lpGeo w i (S.mem obc)) C.ks C.tb C.mode (ρ.apply xs) S.out
      (initState (ρ.apply xs)) S1 := by rw [hks, htb, hmode]; exact R1
  obtain ⟨j, s_j, h1, h2, hj, hcap⟩ := sim_back C hp hpre (hL ▸ le_rfl) htgt (by rw [hexit])
    (fun ovf h => by rw [hmode] at h; cases h; exact hdie) R1' hpc1' (hhalt.rest e1)
  refine ⟨s_j.out, j + terminalCost p₀ s_j, ⟨j, s_j, h1, h2, rfl, rfl⟩, by omega,
    hcap die hmode⟩

end phase

end Lax185574Proofs.RamSim
