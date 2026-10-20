import Lax457868Proofs.RefinedReconstruction
import Lax457868Proofs.RefinedRoundTrace

/-! Execute the fixed large-input body while retaining the physical
chronological round trace and its charge for later finite-tape averaging. -/

namespace Lax457868Proofs.RefinedBodyExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedProgramSource
open Lax457868Proofs.RefinedRoundLoop
open Lax457868Proofs.RefinedRoundTrace
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRecordedCommit
open Lax457868Proofs.InitialNeighborhoodQuotient
open Lax457868Proofs.RefinedReconstruction
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlStraight

set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

/-- Each large-input tape determines an actual body run. Its round list is
chronological and exact, and the only zero-active terminal case has a final
explicitly failed prepared round. -/
lemma algorithmBody_large_run_traced {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {bits : List Bool} {σ : Env}
    (R : Lax457868Proofs.RefinedSetup.Ready c n x
      (bits.map Bool.toNat ++ rest) σ)
    (hbounded : ValuesBounded B σ)
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hn2 : 2 ≤ n)
    (hB : 4 * (x.length + 1) ≤ B)
    (hlargeN : 2 * refinedCutoffK c < n)
    (htape : n * Lax457868Proofs.RefinedTapeReserve.roundBitReserve c n ≤ bits.length) :
    ∃ ρ υ τ K events,
      Run B algorithmBody σ τ K ∧
      TraceChain B c G x rest ρ υ events ∧
      K ≤ 1 + (Cond.lt (.var "cutoffResult") (.var "acount")).size +
        951 * (x.length + 1) + traceCost events +
        1 + (Cond.eq (.var "acount") (.lit 0)).size + 100 * (n + 1) ∧
      (υ.vars "acount" = 0 →
        ∃ before e, events = before ++ [e] ∧ e.accepted = false) ∧
      (υ.vars "acount" = 0 ∨
        Lax195003.WelzlOrdersInGraphs.EncodesGraphWelzlOrder G 1
          (2 * refinedCutoffK c * Nat.clog 2 n) τ.out) := by
  have hnB : n < B := by
    have hlen := hx.length_eq
    omega
  have hguard : (Cond.lt (.var "cutoffResult") (.var "acount")).evalB B σ =
      some true := by
    have hcut : σ.vars "cutoffResult" = 2 * refinedCutoffK c := by
      rw [R.cutoff, Nat.min_eq_right hlargeN.le]
    rw [evalB_condLt
      (evalB_var (by rw [hcut]; omega : σ.vars "cutoffResult" < B))
      (evalB_var (by rw [R.activeCount]; exact hnB))]
    simp [hcut, R.activeCount, hlargeN]
  obtain ⟨ρ, C, hquot, D, hCsub, hC, htrace, _, _, _, _⟩ :=
    initialQuotientSource_run R hx hn2 hlargeN hB
  have hready : LoopReady B c G x rest ρ :=
    initial_loopReady R hbounded hquot D hn2 hCsub hC htrace htape
  have hpositive : 0 < ρ.vars "acount" := by
    rw [(hquot.frame_var "acount" (by decide)).trans R.activeCount]
    omega
  obtain ⟨υ, Kloop, events, hloop, hchain, hcost, hnυ, hresult, hlast⟩ :=
    round_while_run_traced hx hG hc hB hlargeN hready hpositive
  by_cases hzero : υ.vars "acount" = 0
  · have hguard0 : (Cond.eq (.var "acount") (.lit 0)).evalB B υ = some true := by
      rw [evalB_condEq
        (evalB_var (by rw [hzero]; omega : υ.vars "acount" < B))
        (evalB_lit (by omega : 0 < B))]
      simp [hzero]
    obtain ⟨τ, hwrite, _⟩ := writeNaturalOrder_run hnυ hnB
    have hfinish : Run B finishRefined υ τ
        (1 + (Cond.eq (.var "acount") (.lit 0)).size + (10 * n + 6)) := by
      simpa [finishRefined] using Run.ite_true hguard0 hwrite
    have hseq : Run B (seqs [initialQuotientSource,
        .while roundGuard Lax457868Proofs.RefinedRoundDriver.preparedRefinedRoundSource,
        finishRefined]) σ τ
        (951 * (x.length + 1) + Kloop +
          (1 + (Cond.eq (.var "acount") (.lit 0)).size + (10 * n + 6))) := by
      simpa [seqs, Nat.add_assoc] using hquot.seq (hloop.seq hfinish)
    have hrun := Run.ite_true (d := writeNaturalOrder) hguard hseq
    let Ktotal := 1 + (Cond.lt (.var "cutoffResult") (.var "acount")).size +
      (951 * (x.length + 1) + Kloop +
        (1 + (Cond.eq (.var "acount") (.lit 0)).size + (10 * n + 6)))
    refine ⟨ρ, υ, τ, Ktotal, events, ?_, hchain, ?_, hlast, Or.inl hzero⟩
    · simpa [algorithmBody, roundGuard, Ktotal] using hrun
    · dsimp [Ktotal]
      rw [← hcost]
      omega
  · rcases hresult with hfail | ⟨hterminal, hsmall⟩
    · exact False.elim (hzero hfail)
    · have hpositive' : 0 < υ.vars "acount" := by omega
      obtain ⟨τ, hfinish, hcorrect⟩ :=
        finishRefined_positive_run hterminal hpositive' hsmall hnB
      have hseq : Run B (seqs [initialQuotientSource,
          .while roundGuard Lax457868Proofs.RefinedRoundDriver.preparedRefinedRoundSource,
          finishRefined]) σ τ
          (951 * (x.length + 1) + Kloop +
            (1 + (Cond.eq (.var "acount") (.lit 0)).size + 100 * (n + 1))) := by
        simpa [seqs, Nat.add_assoc] using hquot.seq (hloop.seq hfinish)
      have hrun := Run.ite_true (d := writeNaturalOrder) hguard hseq
      let Ktotal := 1 + (Cond.lt (.var "cutoffResult") (.var "acount")).size +
        (951 * (x.length + 1) + Kloop +
          (1 + (Cond.eq (.var "acount") (.lit 0)).size + 100 * (n + 1)))
      refine ⟨ρ, υ, τ, Ktotal, events, ?_, hchain, ?_, hlast, Or.inr hcorrect⟩
      · simpa [algorithmBody, roundGuard, Ktotal] using hrun
      · dsimp [Ktotal]
        rw [← hcost]
        omega

end Lax457868Proofs.RefinedBodyExecution
