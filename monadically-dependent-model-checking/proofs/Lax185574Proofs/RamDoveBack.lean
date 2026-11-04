import Lax185574Proofs.RamDovetail
import Lax185574Proofs.RamSimBack

/-!
Backward soundness of the dovetailer: every halting run of the
dovetailer outputs the output of an accepting thread. Every slot takes
at least one step, so the scheduler cannot run through more slots than
the machine makes steps, and a halting machine has halted in the exit
handler of an accepting thread.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.Ruler

variable {w K B : ℕ} {Q : Program} {x : List ℕ}

theorem dv_head_instr : (dvProg Q B K)[dvL0]? = some (.jzero 20 (dvSkip Q)) :=
  (dv_fits_head Q B K).head

/-- A slot takes at least one step. -/
theorem dv_slot_pos (G : DGlob w K B Q x) {j : ℕ} {S : State} (D : DInv w K B Q x j S) :
    ∃ n, 1 ≤ n ∧ ∃ S', Exec w (dvProg Q B K) n S S' ∧
      (DInv w K B Q x (j + 1) S' ∨ DHalt w K B Q x j S') := by
  obtain ⟨n, -, S', e, hS'⟩ := dv_slot G D
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exfalso
    subst h0
    have hSS : S' = S := by
      have := e; simp only [Exec, run_zero, Option.some.injEq] at this; exact this.symm
    subst hSS
    rcases hS' with D' | ⟨hhalt, -⟩
    · have h1 := D.slot
      have h2 := D'.slot
      have hw : 2 ≤ 2 ^ w := by
        have := G.kw
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [h1] at h2
      have h3 := Nat.sub_mod_eq_zero_of_mod_eq h2.symm
      rw [show j + 1 - j = 1 by omega, Nat.one_mod_eq_one.mpr (by omega)] at h3
      exact absurd h3 (by omega)
    · rw [D.pc, dv_head_instr] at hhalt
      cases hhalt
  · exact ⟨n, h0, S', e, hS'⟩

/-- After `m` slots the machine has made at least `m` steps, unless it
has halted in an accepting thread. -/
theorem dv_iter_pos (G : DGlob w K B Q x) (m : ℕ) :
    (∃ n, m ≤ n ∧ ∃ S, Exec w (dvProg Q B K) n (initState x) S ∧ DInv w K B Q x (m + 1) S) ∨
      (∃ n S j, Exec w (dvProg Q B K) n (initState x) S ∧ DHalt w K B Q x j S) := by
  induction m with
  | zero =>
      obtain ⟨S, e, hD⟩ := dv_init G
      exact Or.inl ⟨16, by omega, S, e, hD⟩
  | succ m ih =>
      rcases ih with ⟨n, hn, S, e, hD⟩ | h
      · obtain ⟨n', hn', S', e', hS'⟩ := dv_slot_pos G hD
        rcases hS' with hD' | hH
        · exact Or.inl ⟨n + n', by omega, S', e.trans e', hD'⟩
        · exact Or.inr ⟨n + n', S', _, e.trans e', hH⟩
      · exact Or.inr h

/-- **Backward soundness of the dovetailer.** A halting run outputs the
output `y` of a thread `i` that halts with `1 :: y`. -/
theorem dovetail_back (B : ℕ) (Q : Program) (w : ℕ) (x z : List ℕ) (T : ℕ)
    (hw : dvK Q B < w) (hx : x.length < 2 ^ (w - 1))
    (h : RunsTo w (dvProg Q B (dvK Q B)) x z T) :
    ∃ i t, i + dvK Q B < w ∧ z.length ≤ B ∧
      RunsTo (w - i - dvK Q B) Q (i :: x) (1 :: z) t := by
  have G : DGlob w (dvK Q B) B Q x := dvGlob_of (by simp only [dvK]; omega) hw hx
  obtain ⟨N, S_end, hr, hs, hz, -⟩ := h
  have hH : Halts w (dvProg Q B (dvK Q B)) (initState x) N S_end := ⟨hr, hs⟩
  rcases dv_iter_pos G (N + 1) with ⟨n, hn, S, e, -⟩ | ⟨n, S, -, e, hhalt, I, y, t, hI, hy, hR, hout, -⟩
  · have := e.le_of_halts hH
    omega
  · have hst : step w (dvProg Q B (dvK Q B)) S = none := step_halt hhalt
    obtain ⟨-, rfl⟩ := terminal_run_unique hr hs e hst
    exact ⟨I, t, hI, hz ▸ hout ▸ hy, hz ▸ hout ▸ hR⟩

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.RamSim
open Lax185574Proofs.Ruler

/-- **Dovetailer, both directions.** The forward half is that of
`dovetail`. Conversely, every halting run of `p` outputs the output `y`
of some thread `i` that halts on `i :: x` with output `1 :: y`. So if
every thread that accepts is right, the dovetailer is right. -/
theorem dovetail_sound :
    ∀ (B : ℕ) (Q : Program), ∃ (p : Program) (K : ℕ),
      (∀ (w : ℕ) (x : List ℕ) (i : ℕ) (y : List ℕ) (t : ℕ),
        i + K < w → x.length < 2 ^ (w - 1) → y.length ≤ B →
        RunsTo (w - i - K) Q (i :: x) (1 :: y) t →
        ∃ (i' : ℕ) (y' : List ℕ) (t' T : ℕ),
          i' + K < w ∧ y'.length ≤ B ∧
          RunsTo (w - i' - K) Q (i' :: x) (1 :: y') t' ∧
          RunsTo w p x y' T ∧ T ≤ K * 2 ^ i * (t + 1)) ∧
      (∀ (w : ℕ) (x z : List ℕ) (T : ℕ), K < w → x.length < 2 ^ (w - 1) →
        RunsTo w p x z T →
        ∃ i t, i + K < w ∧ z.length ≤ B ∧ RunsTo (w - i - K) Q (i :: x) (1 :: z) t) := by
  intro B Q
  refine ⟨dvProg Q B (dvK Q B), dvK Q B, fun w x i y t hi hx hy hrun => ?_,
    fun w x z T hw hx h => dovetail_back B Q w x z T hw hx h⟩
  set K := dvK Q B
  have G : DGlob w K B Q x := dvGlob_of (by simp only [K, dvK]; omega) (by omega) hx
  have ht : 0 < t := alive_lt (c := 0) rfl (Or.inr rfl) hrun
  set m := 2 ^ i * (2 * (t - 1) + 1)
  obtain ⟨n, hn, S, e, hS⟩ := dv_iter G m
  rcases hS with hD | ⟨hhalt, I, y', t', hI, hy', hR', hout, -⟩
  · exfalso
    have hc : t - 1 + 1 ≤ count i (m + 1) := count_ge i (t - 1)
    rcases hD.threads i hi with ⟨s, hs, hpc, -⟩ | ⟨-, hnever⟩
    · have := alive_lt hs hpc hrun
      omega
    · exact hnever y t hy hrun
  · refine ⟨I, y', t', n + 1, hI, hy', hR', ?_, ?_⟩
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
