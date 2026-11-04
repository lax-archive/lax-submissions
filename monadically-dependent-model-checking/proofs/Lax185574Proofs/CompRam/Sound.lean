import Lax185574Proofs.CompRam.GlueSpec
import Lax185574Proofs.MC.Asm.Sound
import Lax185574Proofs.RamOut
import Lax185574Proofs.CompRam.FixedW

/-!
Soundness of the composite of lem:compose.

The composite is the loop driver with the glue program and the callee
`switch R S C D`. If the glue program meets `GlueSpec` and the three
programs are sound at the ranks up to `k + q + 1` (`CSound`), then at
every word length at which `2 ^ (w - 3)` exceeds the square of a
constant and the entries of the input, every halting run of the
composite outputs the word of the far composition.

The proof follows the script with `inv_script_sound`, as for thm:mc. The
invariant of round `j` is that its word length `v` is at least `sI` and
the entries of its input are below `2 ^ (v - sI)`. The round test of a
halting round gives `w - 3 ≤ 2 v` (`round_half`), so the constants of the
callees fit at the word lengths of the round, however many rounds the
machine needs.
-/

namespace Lax185574Proofs.CompRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax185574Proofs.MC (SwSpec LoopSpec inv_script_sound lpU_lt catLim_le two_pow_mono le_pow_sub)
open Lax185574Proofs.RamCat Lax185574Proofs.RamExec

/-- The batch of region `i` has at most `i + 1` regions. -/
theorem two_pow_bat_le (C i : ℕ) : 2 ^ (lpAlloc C i).bat ≤ i + 1 := by
  obtain ⟨-, h2, -, h4, -⟩ := lpAlloc_inv C i
  omega

/-- **A halting round has half the word length of the driver.** -/
theorem round_half {w j : ℕ} (ht : (2 * j + 1) ^ 4 ≤ 2 ^ lpV w (2 * j)) : w - 3 ≤ 2 * lpV w (2 * j) := by
  have hb := two_pow_bat_le (lpCap w) (2 * j)
  set b := (lpAlloc (lpCap w) (2 * j)).bat
  have h16 : 2 ^ (4 * b) ≤ 2 ^ lpV w (2 * j) := by
    calc 2 ^ (4 * b) = (2 ^ b) ^ 4 := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ (2 * j + 1) ^ 4 := Nat.pow_le_pow_left hb 4
      _ ≤ _ := ht
  have h4 : 4 * b ≤ lpV w (2 * j) := (Nat.pow_le_pow_iff_right (by norm_num)).1 h16
  simp only [lpV] at h4 ⊢
  omega

theorem lpV_zero (w : ℕ) : lpV w 0 = w - 3 := by
  simp [lpV, lpAlloc]

theorem lpU_nowin {x a b : List ℕ} (h : a.getD 2 0 = 0) : lpU x a b = lpU [] a b := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [lpU, h]

theorem getD_two_outW (j : ℕ) (S : List Fr) (q : Qry) : (outW j (.call S q)).getD 2 0 = 0 := by
  simp [outW]

theorem sum_map_const {α : Type*} (L : List α) (c : ℕ) : (L.map fun _ => c).sum = L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

theorem sum_flatMap_const {α : Type*} (L : List α) (c : ℕ) :
    (L.flatMap fun _ => [c]).sum = L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.flatMap_cons, List.sum_append, ih, List.length_cons]; simp; ring

theorem length_toWord_atL1 (R₁ R₂ : ℕ) :
    (toWord (atL 1 R₁ R₂)).length = 1 + 4 + 4 + 5 * (R₁ + 1) + 5 * R₂ := by
  rw [length_toWord_words]
  simp only [atL, atEq, atCol, atDist, atDcol, List.map_append, List.sum_append, List.map_flatMap,
    List.map_map, Function.comp_def, List.length_cons, List.length_nil,
    List.range_one, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.append_nil, List.sum_cons, List.sum_nil]
  rw [sum_flatMap_const, sum_flatMap_const, List.length_range, List.length_range]
  ring

theorem length_dSq_le : dSq.length ≤ 40000 := by
  rw [dSq_eq, toWord_ext_word]
  simp only [List.length_append, length_toWord_atL2, length_toWord_atL1]
  norm_num

theorem rankLe_mono {K K' : ℕ} {q : Qry} (h : RankLe K q) (hK : K ≤ K') : RankLe K' q := by
  cases q <;> simp only [RankLe] at h ⊢ <;> omega

theorem qWord_length {eR eS eC N : ℕ} {q : Qry} (hg : CGuard eR eS eC N q) :
    (qWord q).length < 2 ^ N + 40010 := by
  have hS := length_dSq_le
  have hR : dRq.length = 5 := by rw [dRq_eq]; rfl
  rw [qWord_parts, Lax185574Proofs.MC.swIn_length_le]
  have := Lax185574Proofs.MC.guard_length hg
  cases q <;> simp only [qR, qS, qC, realQ] at this ⊢ <;> simp <;> omega

/-- **Soundness of the composite.** -/
theorem comp_sound {pR pS pC Gp sw p : Program} {eR eS eC K C Ks KL D sI sQ cG E : ℕ}
    (hS : CSound pR pS pC eR eS eC K C) (hsw : SwSpec sw Ks D pR pS pC)
    (hp : LoopSpec p Gp sw KL) (hG : GlueSpec Gp sI sQ eR eS eC cG E) (hD : sI + 4 ≤ D)
    (hQ : D + 20 ≤ sQ) {n : ℕ} {G : PartialGraph (Fin n)} {k q l1 l2 : ℕ}
    {u₁ : Fin l1 → Fin n} {u₂ : Fin l2 → Fin n} (hI : Inst G k q u₁ u₂) (hK : k + q + 1 ≤ K)
    {w : ℕ} (hw : 8 ≤ w) (hx : (xT G k q u₁ u₂).length < 2 ^ (w - 1))
    (hbig : ((C + Ks + 1) * 2 ^ (sQ + 20)) ^ 2 ≤ 2 ^ (w - 3))
    (hx0 : ((xT G k q u₁ u₂).length + maxEntry (xT G k q u₁ u₂) + 1) * 2 ^ sI ≤ 2 ^ (w - 3)) :
    ∀ z t, RunsTo w p (xT G k q u₁ u₂) z t → z = toWord (tree G k q (Fin.append u₁ u₂)) := by
  have hback : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w Gp sw x 0 (lpA0 x) [] z T :=
    fun w x hw hx => (hp w x hw hx).2
  obtain ⟨-, m, -, hend, hreach, hcall⟩ := inst_script hI
  refine inv_script_sound hback hw hx (A := aT G k q u₁ u₂) (B := bT G k q u₁ u₂)
    (I := fun j => sI ≤ lpV w (2 * j) ∧ ∀ e ∈ uT G k q u₁ u₂ j, e < 2 ^ (lpV w (2 * j) - sI))
    (R := m) rfl rfl ?_ ?_ ?_
  · -- the first round
    show sI ≤ lpV w (2 * 0) ∧ ∀ e ∈ uT G k q u₁ u₂ 0, e < 2 ^ (lpV w (2 * 0) - sI)
    rw [Nat.mul_zero, lpV_zero]
    obtain ⟨h1, h2⟩ := le_pow_sub hx0 (by omega)
    refine ⟨h1, fun e he => ?_⟩
    rw [uT_zero] at he
    have : e ≤ (xT G k q u₁ u₂).length + maxEntry (xT G k q u₁ u₂) := by
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at he
      rcases he with ((rfl | rfl) | he) | rfl
      · omega
      · omega
      · have := le_maxEntry he; omega
      · omega
    omega
  · -- the rounds with a call
    rintro j hj ⟨hsv, hent⟩ o t hrun
    have hRj : Reached G k q u₁ u₂ j := fun i hi => hreach i (by omega)
    obtain ⟨ho, hoe, htest, hqg⟩ := hG.sound n G k q l1 l2 u₁ u₂ hI j hRj _ hsv hent o t hrun
    obtain ⟨g, S, q', htr, -, hA, hRk⟩ := hcall j hj
    have hhalf := round_half (le_trans htest (two_pow_mono (Nat.sub_le _ _)))
    have hvv := lpV_succ_ge w (2 * j)
    have hvv' := lpV_succ_ge w (2 * j + 1)
    set v := lpV w (2 * j) with hv
    set v' := lpV w (2 * j + 1) with hv'
    set v'' := lpV w (2 * j + 2) with hv''
    have hBv : (C + Ks + 1) * 2 ^ (sQ + 20) ≤ 2 ^ v := by
      have : ((C + Ks + 1) * 2 ^ (sQ + 20)) ^ 2 ≤ (2 ^ v) ^ 2 :=
        le_trans hbig (by rw [← pow_mul]; exact two_pow_mono (by omega))
      exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
    obtain ⟨hv20, hCv⟩ := le_pow_sub hBv (by omega)
    have hp1 : 2 ^ (v - (sQ + 20)) ≤ 2 ^ (v - sQ) := two_pow_mono (by omega)
    have hp2 : 2 ^ (v - sQ) ≤ 2 ^ (v' - 8 - D) := two_pow_mono (by omega)
    have hp3 : 2 ^ (v - sQ) * 2 ^ 8 ≤ 2 ^ (v' - 10 - D) := by
      rw [← pow_add]; exact two_pow_mono (by omega)
    have hp4 : 2 ^ 20 ≤ 2 ^ (v - sQ) := two_pow_mono (by omega)
    refine ⟨ho, (head_aT htr).1, fun r t' hr => ?_⟩
    rw [ho, lpQ_aT htr] at hr
    simp only [QGuard, htr] at hqg
    have hql := qWord_length hqg
    rw [qWord_parts] at hr hql
    obtain ⟨y, z, u, tA, tB, tC, hy, hz, hu, hr', hyl, hzl, hul⟩ :=
      (hsw v' _ _ _ (by omega) (by omega) (by omega)).2 r t' hr
    have hY := callee_ans hS hA (rankLe_mono hRk hK) hqg (by omega) (by omega) (by omega)
      (by omega) hy hz hu
    beta_reduce
    rw [show 2 * (j + 1) = 2 * j + 2 by ring]
    refine ⟨by rw [bT_call htr, hr', hY], by omega, ?_⟩
    -- the invariant of the next round
    show ∀ e ∈ uT G k q u₁ u₂ (j + 1), e < 2 ^ (v'' - sI)
    unfold uT
    rw [lpU_nowin (by rw [aT_succ, htr]; exact getD_two_outW _ _ _), ← ho, bT_call htr, ← hY]
    have k1 : 2 ^ (v - sI - 4) ≤ 2 ^ (v'' - sI) := two_pow_mono (by omega)
    have k2 : 2 ^ (v' - 4 - D) ≤ 2 ^ (v'' - sI) := two_pow_mono (by omega)
    have k3 : 2 ^ (v' - 6 - D) ≤ 2 ^ (v' - 4 - D) := two_pow_mono (by omega)
    have k4 : 2 ^ (v' - 8 - D) ≤ 2 ^ (v' - 6 - D) := two_pow_mono (by omega)
    have k5 : 2 ^ (v' - 6 - D) * 2 ^ 2 = 2 ^ (v' - 4 - D) := by
      rw [← pow_add]; congr 1; omega
    have l1 := catLim_le (v' - 4) (D + 2)
    have l2 := catLim_le (v' - 6) (D + 2)
    have l3 := catLim_le (v' - 8) (D + 2)
    rw [show v' - 4 - (D + 2) = v' - 6 - D by omega] at l1
    rw [show v' - 6 - (D + 2) = v' - 8 - D by omega] at l2
    rw [show v' - 8 - (D + 2) = v' - 10 - D by omega] at l3
    have k6 : 2 ^ (v' - 10 - D) ≤ 2 ^ (v' - 8 - D) := two_pow_mono (by omega)
    have oy := runsTo_out_lt hy
    have oz := runsTo_out_lt hz
    have ou := runsTo_out_lt hu
    refine lpU_lt (by positivity) (by simp) (fun e he => lt_of_lt_of_le (hoe e he) k1)
      (fun e he => ?_) ?_
    · simp only [List.mem_append] at he
      rcases he with (he | he) | he
      · exact lt_of_lt_of_le (oy e he) k2
      · exact lt_of_lt_of_le (oz e he) (le_trans k3 k2)
      · exact lt_of_lt_of_le (ou e he) (le_trans k4 (le_trans k3 k2))
    · simp only [List.length_append]; omega
  · -- the last round
    rintro ⟨hsv, hent⟩ o t hrun
    rw [(hG.sound n G k q l1 l2 u₁ u₂ hI m hreach _ hsv hent o t hrun).1, aT_done hend]

end Lax185574Proofs.CompRam
