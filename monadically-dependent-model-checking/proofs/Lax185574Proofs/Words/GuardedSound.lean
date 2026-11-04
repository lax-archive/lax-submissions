import Lax185574Proofs.Words.Guarded

/-!
The guarded program at every word length.

`computes_of_guarded` describes the guarded program only at word lengths
at which the input is admissible. A program that is run as one stage of
a composite, at word lengths that shrink from stage to stage, needs the
same description at every word length that leaves room for the layout:
if the command has a bounded run from the input with `W = 2^(w-r) - 1`,
then the guarded program halts exactly when the command does not set
`ovf`, and then with the output of the command. The proof is that of
`computes_of_guarded`.
-/

namespace Lax185574Proofs.Words

open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax808846Proofs.Simulation Lax808846Proofs.Reasoning Lax808846Proofs.Machine

/-- The value of `W` at word length `w`. -/
def guardW (L : Layout) (w : ℕ) : ℕ := 2 ^ (w - guardBits L) - 1

theorem guardW_succ (L : Layout) (w : ℕ) : guardW L w + 1 = 2 ^ (w - guardBits L) := by
  have : 0 < 2 ^ (w - guardBits L) := by positivity
  simp only [guardW]; omega

/-- **Guarded programs at every word length.** If every input entry is
at most `W` and the command has a run in which every value is at most
`W`, then every halting run of the guarded program comes from a run of
the command that does not set `ovf`, with its output, and if the command
does not set `ovf`, the guarded program halts with its output. -/
theorem guarded_sound {L : Layout} {cmd : Com} (hok : Com.Ok L cmd) (hW : "W" ∈ L.scalars)
    (hO : "ovf" ∈ L.scalars) {w : ℕ} (hrw : guardBits L + 2 ≤ w) {x : List ℕ}
    (hx : ∀ v ∈ x, v ≤ guardW L w) {ext : String → ℕ} {σ' : Env} {k : ℕ}
    (hrun : Run (guardW L w + 1) cmd ((initEnv ext x).setVar "W" (guardW L w)) σ' k) :
    (∀ y t, RunsTo w (guardedProgram L cmd) x y t → σ'.vars "ovf" = 0 ∧ y = σ'.out) ∧
    (σ'.vars "ovf" = 0 → ∃ t ≤ L.const * k + 5, RunsTo w (guardedProgram L cmd) x σ'.out t) := by
  set r := guardBits L with hr
  set W := guardW L w with hWdef
  have hW1 : W + 1 = 2 ^ (w - r) := guardW_succ L w
  have hsplit : 2 ^ w = 2 ^ r * 2 ^ (w - r) := by rw [← pow_add]; congr 1; omega
  obtain ⟨k', hk', hbs⟩ := hrun
  have hPQ : L.temps + 2 + L.scalars.length + L.arrays.length ≤ 2 ^ r := by
    have := Nat.lt_two_pow_self (n := r); simp only [hr, guardBits] at this ⊢; omega
  have hfit : L.FitsWords (W + 1) w := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hW1]; exact Nat.one_lt_two_pow (by omega)
    · rw [hW1, hsplit]; exact Nat.le_mul_of_pos_left _ (by positivity)
    · simp only [Layout.span]
      rw [hW1, hsplit]
      have hq : 1 ≤ 2 ^ (w - r) := Nat.one_le_two_pow
      generalize 2 ^ (w - r) = Q at hq ⊢
      nlinarith
  have hwa : L.varAddr "W" < 2 ^ w := L.varAddr_lt_two_pow hfit hW
  have hoa : L.varAddr "ovf" < 2 ^ w := L.varAddr_lt_two_pow hfit hO
  have hWw : W < 2 ^ w := by have := hfit.bound; omega
  have hpre := prelude_run (c := cmd) x (by omega) hwa
  have hrep := represents_prelude ext x hW hwa hWw
  have hinpB : ((initEnv ext x).setVar "W" W).InpBounded (W + 1) := by
    intro v hv
    have := hx v hv
    omega
  obtain ⟨t, s', ht, hrun', hpc', hrep'⟩ :=
    compile_correct hfit hbs hok hinpB 3 (preludeState L w x) rfl hrep (guarded_fits L cmd)
  have hjz : (guardedProgram L cmd)[s'.pc]? =
      some (.jzero (L.varAddr "ovf") (3 + size L cmd + 2)) := by
    rw [hpc', show 3 + size L cmd = 3 + size L cmd + 0 from rfl, guarded_getElem_post]; rfl
  have hmem : s'.mem (L.varAddr "ovf") = σ'.vars "ovf" := hrep'.vars "ovf" hO
  have hreach : run w (guardedProgram L cmd) (3 + t) (initState x) = some s' :=
    run_trans hpre hrun'
  by_cases hov : σ'.vars "ovf" = 0
  · set s'' : State := { s' with pc := 3 + size L cmd + 2 } with hs''
    have hstep : run w (guardedProgram L cmd) 1 s' = some s'' := by
      rw [run_one hjz, effect_jzero hoa, hmem, if_pos hov]
    have hhalt : (guardedProgram L cmd)[s''.pc]? = some .halt := by
      rw [hs'', guarded_getElem_post]; rfl
    have hRuns : RunsTo w (guardedProgram L cmd) x σ'.out (3 + t + 1 + 1) := by
      refine ⟨3 + t + 1, s'', run_trans hreach hstep, ?_, ?_, ?_⟩
      · rw [step_eq, hhalt]; rfl
      · rw [hs'']; show s'.out = _; rw [hrep'.out]
      · rw [terminalCost_of_getElem? hhalt]
    refine ⟨fun y t' h => ⟨hov, (runsTo_unique h hRuns).1⟩, fun _ => ⟨3 + t + 1 + 1, ?_, hRuns⟩⟩
    have h2 : L.const * k' ≤ L.const * k := Nat.mul_le_mul_left _ hk'
    omega
  · set s'' : State := { s' with pc := 3 + size L cmd + 1 } with hs''
    have hstep : run w (guardedProgram L cmd) 1 s' = some s'' := by
      rw [run_one hjz, effect_jzero hoa, hmem, if_neg hov]
      simp [hs'', hpc']
    have hloop : (guardedProgram L cmd)[s''.pc]? = some (.jump s''.pc) := by
      rw [hs'', guarded_getElem_post]; rfl
    exact ⟨fun y t' h => absurd h (not_runsTo_of_loop (run_trans hreach hstep) hloop),
      fun h => absurd h hov⟩

end Lax185574Proofs.Words
