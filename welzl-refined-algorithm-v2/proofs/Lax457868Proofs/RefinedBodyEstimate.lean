import Lax457868Proofs.RefinedBodyExecution
import Lax457868Proofs.RefinedFinalBridge

/-! The remaining probability and mean obligations are expressed on the
actual body execution family, with a checked conversion to `BodyEstimate`. -/

namespace Lax457868Proofs.RefinedBodyEstimate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax195003.WordRamRandomness
open Lax195003.WelzlOrdersInGraphs
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.RefinedRoundTrace
open Lax457868Proofs.RefinedProgramSource
open Lax457868Proofs.RefinedFinalBridge
open scoped BigOperators

structure LargeBodyFamily (B c n N : ℕ) (G : SimpleGraph (Fin n))
    (x : List ℕ) (σ : Env) where
  quotient : Tape N → Env
  terminal : Tape N → Env
  final : Tape N → Env
  cost : Tape N → ℕ
  events : Tape N → List RoundEvent
  run : ∀ tape, Run B algorithmBody {σ with inp := bitTape tape}
    (final tape) (cost tape)
  trace : ∀ tape,
    TraceChain B c G x [] (quotient tape) (terminal tape) (events tape)
  cost_le : ∀ tape, cost tape ≤
    1 + (Cond.lt (.var "cutoffResult") (.var "acount")).size +
      951 * (x.length + 1) + traceCost (events tape) +
      1 + (Cond.eq (.var "acount") (.lit 0)).size + 100 * (n + 1)
  failure_last : ∀ tape, (terminal tape).vars "acount" = 0 →
    ∃ before e, events tape = before ++ [e] ∧ e.accepted = false
  correct_or_failure : ∀ tape, (terminal tape).vars "acount" = 0 ∨
    EncodesGraphWelzlOrder G 1
      (2 * Lax457868Proofs.refinedCutoffK c * Nat.clog 2 n)
      (final tape).out

/-- Every long analysis tape has one concrete traced execution. -/
noncomputable def large_body_family {B c n N : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env}
    (R : Lax457868Proofs.RefinedSetup.Ready c n x [] σ)
    (hbounded : Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B σ)
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hn2 : 2 ≤ n)
    (hB : 4 * (x.length + 1) ≤ B)
    (hlargeN : 2 * Lax457868Proofs.refinedCutoffK c < n)
    (htape : n * Lax457868Proofs.RefinedTapeReserve.roundBitReserve c n ≤ N) :
    LargeBodyFamily B c n N G x σ := by
  classical
  have hbits (tape : Tape N) :
      bitTape tape = (List.ofFn tape).map Bool.toNat := by
    simp only [bitTape, List.map_ofFn, Function.comp_def]
    congr 1
    funext i
    cases tape i <;> rfl
  have hlong (tape : Tape N) :=
    Lax457868Proofs.RefinedBodyExecution.algorithmBody_large_run_traced
      (G := G) (bits := List.ofFn tape) (rest := [])
      (by simpa only [hbits, List.append_nil] using
        (Lax457868Proofs.RefinedFinalBridge.ready_with_input R (bitTape tape)))
      (show Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B
          {σ with inp := bitTape tape} from by
        refine ⟨hbounded.vars, hbounded.arrays, ?_⟩
        intro v hv
        simp only [bitTape, List.mem_ofFn] at hv
        obtain ⟨i, rfl⟩ := hv
        cases tape i <;> simp <;> omega)
      hx hG hc hn2 hB hlargeN (by simpa using htape)
  choose quotient terminal final cost events hrun htrace hcost hlast hcorrect using hlong
  exact ⟨quotient, terminal, final, cost, events,
    (by intro tape; exact hrun tape),
    htrace, hcost, hlast, hcorrect⟩

/-- The only remaining global estimates are the unconditional actual trace
mean and the count of tapes with a failed final source round. -/
lemma bodyEstimate_of_trace_bounds {B c n N Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (F : LargeBodyFamily B c n N G x σ)
    (htraceMean : (∑ tape : Tape N, traceCost (F.events tape)) ≤
      Q * (x.length + 1) * (Nat.clog 2 n + 1) * 2 ^ N)
    (hfailure : 6 * ((Finset.univ.filter fun tape : Tape N =>
        (F.terminal tape).vars "acount" = 0).card) ≤ 2 ^ N) :
    BodyEstimate B c n G x σ N (Q + 1060) := by
  classical
  let bad : Finset (Tape N) := Finset.univ.filter fun tape =>
    (F.terminal tape).vars "acount" = 0
  have hpoint (tape : Tape N) : F.cost tape ≤
      1060 * (x.length + 1) + traceCost (F.events tape) := by
    have hlen := hx.length_eq
    have hn : n ≤ x.length := by omega
    have hh := F.cost_le tape
    dsimp [Cond.size, Expr.size] at hh
    omega
  refine ⟨F.final, F.cost, bad, F.run, ?_, ?_, ?_⟩
  · intro tape hgood
    have hne : (F.terminal tape).vars "acount" ≠ 0 := by
      simpa [bad] using hgood
    rcases F.correct_or_failure tape with hzero | hcorrect
    · exact False.elim (hne hzero)
    · exact hcorrect
  · calc
      (∑ tape : Tape N, F.cost tape) ≤
          ∑ tape : Tape N,
            (1060 * (x.length + 1) + traceCost (F.events tape)) :=
        Finset.sum_le_sum (fun tape _ => hpoint tape)
      _ = 1060 * (x.length + 1) * 2 ^ N +
          ∑ tape : Tape N, traceCost (F.events tape) := by
        simp [Finset.sum_add_distrib, card_tape, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 1060 * (x.length + 1) * 2 ^ N +
          Q * (x.length + 1) * (Nat.clog 2 n + 1) * 2 ^ N :=
        Nat.add_le_add_left htraceMean _
      _ ≤ (Q + 1060) * (x.length + 1) * (Nat.clog 2 n + 1) * 2 ^ N := by
        have hlog : 1 ≤ Nat.clog 2 n + 1 := by omega
        have hbase : 1060 * (x.length + 1) * 2 ^ N ≤
            1060 * (x.length + 1) * (Nat.clog 2 n + 1) * 2 ^ N := by
          have hh := Nat.mul_le_mul_left (1060 * (x.length + 1)) hlog
          exact Nat.mul_le_mul_right _ (by simpa only [mul_one] using hh)
        nlinarith
  · exact hfailure

end Lax457868Proofs.RefinedBodyEstimate
