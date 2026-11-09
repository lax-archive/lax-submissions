import Lax457868Proofs.RefinedBodyExecution
import Lax457868Proofs.RefinedFinalBridge
import Lax457868Proofs.RefinedRoundCost
import Lax457868Proofs.StoppedPrefixAveraging
import Lax457868Proofs.RefinedFailureBudget

/-! The remaining probability and mean obligations are expressed on the
actual body execution family, with a checked conversion to `BodyEstimate`. -/

namespace Lax457868Proofs.RefinedBodyEstimate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax195003.WordRamRandomness
open Lax195003.WelzlOrdersInGraphs
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.RefinedRoundTrace
open Lax457868Proofs.RefinedRoundLoop
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
  quotient_run : ∀ tape,
    Run B Lax457868Proofs.InitialNeighborhoodQuotient.initialQuotientSource
      {σ with inp := bitTape tape} (quotient tape) (951 * (x.length + 1))
  trace : ∀ tape,
    TraceChain B c G x [] (quotient tape) (terminal tape) (events tape)
  length_le : ∀ tape, (events tape).length ≤ Nat.clog 2 n
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

  terminal_guard : ∀ tape, roundGuard.evalB B (terminal tape) = some false

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
  choose quotient terminal final cost events hrun hquot htrace hlength hcost hlast hcorrect hguard using hlong
  exact ⟨quotient, terminal, final, cost, events,
    (by intro tape; exact hrun tape),
    hquot, htrace, hlength, hcost, hlast, hcorrect, hguard⟩

/-- Before each attempt, the recorded consumed prefix lies within the
physical `N`-bit input tape. -/
lemma LargeBodyFamily.usedBefore_le {B c n N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (F : LargeBodyFamily B c n N G x σ) (tape : Tape N) (i : ℕ) :
    usedBefore (F.events tape) i ≤ N := by
  have hquot : (F.quotient tape).inp = bitTape tape := by
    rw [(F.quotient_run tape).frame_inp (by decide)]
  have hchain := (F.trace tape).consumed_append
  rw [hquot] at hchain
  have htotal : ((F.events tape).flatMap fun e => e.consumed).length ≤ N := by
    have hlen := congrArg List.length hchain
    simp only [bitTape, List.length_ofFn, List.length_append] at hlen
    omega
  exact (usedBefore_le_total _ i).trans htotal

/-- At a fixed chronological index, the failed-round tape fiber splits into
the two actual selector-status fibers of that same source event. -/
lemma LargeBodyFamily.failed_index_le_status_fibers {B c n N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (F : LargeBodyFamily B c n N G x σ) (i : ℕ) :
    ((Finset.univ.filter fun tape : Tape N =>
      failedAt (F.events tape) i = true).card) ≤
      ((Finset.univ.filter fun tape : Tape N =>
        initialFailureAt (F.events tape) i = true).card) +
      ((Finset.univ.filter fun tape : Tape N =>
        repairFailureAt (F.events tape) i = true).card) := by
  classical
  let bad : Finset (Tape N) := Finset.univ.filter fun tape =>
    failedAt (F.events tape) i = true
  let initial : Finset (Tape N) := Finset.univ.filter fun tape =>
    initialFailureAt (F.events tape) i = true
  let repair : Finset (Tape N) := Finset.univ.filter fun tape =>
    repairFailureAt (F.events tape) i = true
  have hsub : bad ⊆ initial ∪ repair := by
    intro tape htape
    have hfailed : failedAt (F.events tape) i = true := by
      simpa [bad] using htape
    rcases (F.trace tape).failedAt_initial_or_repair i hfailed with hinit | hrep
    · exact Finset.mem_union_left _ (by simpa [initial] using hinit)
    · exact Finset.mem_union_right _ (by simpa [repair] using hrep)
  simpa only [bad, initial, repair] using
    (Finset.card_le_card hsub).trans (Finset.card_union_le initial repair)

/-- The per-round estimate is conditioned on the exact prefix consumed by
earlier rounds. The active-size potential is fixed by that prefix. -/
def PrefixRoundMeanAt {B c n N M D : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env}
    (F : LargeBodyFamily B c n N G x σ) (i : ℕ) : Prop :=
  ∃ used : Tape N → ℕ,
  ∃ hbound : ∀ tape, used tape ≤ N,
    (∀ tape other, (List.ofFn tape).take (used tape) =
      (List.ofFn other).take (used tape) → used other = used tape) ∧
    (∀ tape other, (List.ofFn tape).take (used tape) =
      (List.ofFn other).take (used tape) →
      activeAt (F.events other) i = activeAt (F.events tape) i) ∧
    ∀ tape, (∑ tail : Tape (N - used tape),
        ((chargeAt
          (F.events ((splitEquiv (hbound tape)).symm
            ((splitEquiv (hbound tape) tape).1, tail))) i : ℕ) : ℚ)) ≤
      (((M * (x.length + 1) +
        D * activeAt (F.events tape) i * (Nat.clog 2 n + 1) : ℕ) : ℚ) *
        2 ^ (N - used tape))

lemma PrefixRoundMeanAt.index_mean {B c n N M D : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    {F : LargeBodyFamily B c n N G x σ} {i : ℕ}
    (h : PrefixRoundMeanAt (M := M) (D := D) F i) :
    (∑ tape : Tape N, chargeAt (F.events tape) i) ≤
      ∑ tape : Tape N,
        (M * (x.length + 1) +
          D * activeAt (F.events tape) i * (Nat.clog 2 n + 1)) := by
  classical
  obtain ⟨used, hbound, hcausal, hstable, htail⟩ := h
  have hY : ∀ tape other, (List.ofFn tape).take (used tape) =
      (List.ofFn other).take (used tape) →
      (((M * (x.length + 1) +
        D * activeAt (F.events other) i * (Nat.clog 2 n + 1) : ℕ) : ℚ)) =
      (((M * (x.length + 1) +
        D * activeAt (F.events tape) i * (Nat.clog 2 n + 1) : ℕ) : ℚ)) := by
    intro tape other hp
    rw [hstable tape other hp]
  have hQ := Lax457868Proofs.StoppedPrefixAveraging.sum_le_of_stopped_prefix
    used hbound hcausal
    (fun tape => ((chargeAt (F.events tape) i : ℕ) : ℚ))
    (fun tape => (((M * (x.length + 1) +
      D * activeAt (F.events tape) i * (Nat.clog 2 n + 1) : ℕ) : ℚ)))
    hY htail
  exact_mod_cast hQ

/-- Every terminal retry failure is one of the bounded chronological
attempt-index events. This is a finite union of actual failed source rounds. -/
lemma final_failure_count_le_sum_index {B c n N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (F : LargeBodyFamily B c n N G x σ) :
    ((Finset.univ.filter fun tape : Tape N =>
      (F.terminal tape).vars "acount" = 0).card) ≤
      ∑ i ∈ Finset.range (Nat.clog 2 n),
        ((Finset.univ.filter fun tape : Tape N =>
          failedAt (F.events tape) i = true).card) := by
  classical
  let bad : Finset (Tape N) := Finset.univ.filter fun tape =>
    (F.terminal tape).vars "acount" = 0
  let badAt (i : ℕ) : Finset (Tape N) :=
    Finset.univ.filter fun tape => failedAt (F.events tape) i = true
  have hsub : bad ⊆ (Finset.range (Nat.clog 2 n)).biUnion badAt := by
    intro tape htape
    have hzero : (F.terminal tape).vars "acount" = 0 :=
      (Finset.mem_filter.mp htape).2
    obtain ⟨before, event, heq, hfalse⟩ := F.failure_last tape hzero
    have hindex : before.length < Nat.clog 2 n := by
      have hlen := F.length_le tape
      simp only [heq, List.length_append, List.length_singleton] at hlen
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨before.length, Finset.mem_range.mpr hindex, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [failedAt, heq, hfalse]
  calc
    _ ≤ ((Finset.range (Nat.clog 2 n)).biUnion badAt).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (Nat.clog 2 n), (badAt i).card :=
      Finset.card_biUnion_le
    _ = _ := rfl

/-- The checked polynomial opportunity budget absorbs a uniform per-round
failure probability of `opportunities / 2^n` across the actual logarithmic
list of attempts. -/
lemma final_failure_sixth_of_index_bounds {B c n N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (F : LargeBodyFamily B c n N G x σ)
    (hc : 2 ≤ c) (hlarge : 2 * Lax457868Proofs.refinedCutoffK c < n)
    (hN : n ≤ N)
    (hindex : ∀ i < Nat.clog 2 n,
      ((Finset.univ.filter fun tape : Tape N =>
        failedAt (F.events tape) i = true).card) ≤
        (n * (2 * n) + n * (n * n) + 1 + n) * 2 ^ (N - n)) :
    6 * ((Finset.univ.filter fun tape : Tape N =>
      (F.terminal tape).vars "acount" = 0).card) ≤ 2 ^ N := by
  classical
  let opp := n * (2 * n) + n * (n * n) + 1 + n
  have hlog : Nat.clog 2 n ≤ n :=
    Nat.clog_le_of_le_pow n.lt_two_pow_self.le
  have hsum : (∑ i ∈ Finset.range (Nat.clog 2 n),
      ((Finset.univ.filter fun tape : Tape N =>
        failedAt (F.events tape) i = true).card)) ≤
      Nat.clog 2 n * (opp * 2 ^ (N - n)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (Nat.clog 2 n), opp * 2 ^ (N - n) :=
        Finset.sum_le_sum (fun i hi => hindex i (Finset.mem_range.mp hi))
      _ = _ := by simp [Nat.mul_comm]
  have hbad := final_failure_count_le_sum_index F
  have hcap : ((Finset.univ.filter fun tape : Tape N =>
      (F.terminal tape).vars "acount" = 0).card) ≤
      n * (opp * 2 ^ (N - n)) := by
    exact hbad.trans (hsum.trans (Nat.mul_le_mul_right _ hlog))
  have hbudget := Lax457868Proofs.RefinedFailureBudget.opportunities_fit_sixth
    hc hlarge
  have hscaled := Nat.mul_le_mul_right (2 ^ (N - n)) hbudget
  have hpow : 2 ^ n * 2 ^ (N - n) = 2 ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hN]
  dsimp [opp] at hcap ⊢
  nlinarith [hscaled, hpow]

/-- A per-index mean for the exact source charges, with zero padding after
stopping, telescopes to the required chronological trace mean. The only
probabilistic premise is the per-index inequality; no independent-round
assumption is used. -/
lemma expected_traceCost_of_index_mean {B c n N M D : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (F : LargeBodyFamily B c n N G x σ)
    (hmean : ∀ i < Nat.clog 2 n,
      (∑ tape : Tape N, chargeAt (F.events tape) i) ≤
        ∑ tape : Tape N,
          (M * (x.length + 1) +
            D * activeAt (F.events tape) i * (Nat.clog 2 n + 1))) :
    (∑ tape : Tape N, traceCost (F.events tape)) ≤
      (M + 3 * D + 4) * (x.length + 1) * (Nat.clog 2 n + 1) * 2 ^ N := by
  classical
  have hfirst (tape : Tape N) : activeAt (F.events tape) 0 ≤ x.length + 1 := by
    have hcard := (F.trace tape).first_active_le
    have hlen := hx.length_eq
    omega
  have hstep (tape : Tape N) (i : ℕ) (_hi : i < Nat.clog 2 n) :
      3 * activeAt (F.events tape) (i + 1) ≤
        2 * activeAt (F.events tape) i :=
    (F.trace tape).active_contract i
  have htotal := Lax457868Proofs.RefinedRoundCost.expected_total_charge
    (fun tape i => activeAt (F.events tape) i)
    (fun tape i => chargeAt (F.events tape) i)
    (Nat.clog 2 n) M D x.length (Nat.clog 2 n)
    (by omega) hfirst hstep hmean
  have htrace (tape : Tape N) : traceCost (F.events tape) =
      (∑ i ∈ Finset.range (Nat.clog 2 n), chargeAt (F.events tape) i) + 4 := by
    rw [traceCost, ← sum_chargeAt_pad _ _ (F.length_le tape)]
    simp [roundGuard, Cond.size, Expr.size]
  calc
    (∑ tape : Tape N, traceCost (F.events tape)) =
        (∑ tape : Tape N, ∑ i ∈ Finset.range (Nat.clog 2 n),
          chargeAt (F.events tape) i) + 4 * 2 ^ N := by
      simp [htrace, Finset.sum_add_distrib, card_tape, Nat.mul_comm]
    _ ≤ (M + 3 * D) * (x.length + 1) * (Nat.clog 2 n + 1) * 2 ^ N +
        4 * 2 ^ N := Nat.add_le_add_right (by simpa only [card_tape] using htotal) _
    _ ≤ (M + 3 * D) * (x.length + 1) * (Nat.clog 2 n + 1) * 2 ^ N +
        4 * (x.length + 1) * (Nat.clog 2 n + 1) * 2 ^ N := by
      have hprod : 1 ≤ (x.length + 1) * (Nat.clog 2 n + 1) := by
        have hh : 0 < (x.length + 1) * (Nat.clog 2 n + 1) := by positivity
        omega
      have hh := Nat.mul_le_mul_left 4 hprod
      have hh' := Nat.mul_le_mul_right (2 ^ N) hh
      exact Nat.add_le_add_left (by simpa only [mul_one, Nat.mul_assoc] using hh') _
    _ = _ := by ring

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

/-- Exact stopped-prefix per-round means and an explicit final-failure
count imply the full large-input body estimate for the fixed program. -/
lemma bodyEstimate_of_prefix_round_means {B c n N M D : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (F : LargeBodyFamily B c n N G x σ)
    (hprefix : ∀ i < Nat.clog 2 n,
      PrefixRoundMeanAt (M := M) (D := D) F i)
    (hfailure : 6 * ((Finset.univ.filter fun tape : Tape N =>
        (F.terminal tape).vars "acount" = 0).card) ≤ 2 ^ N) :
    BodyEstimate B c n G x σ N (M + 3 * D + 1064) := by
  have hmean := expected_traceCost_of_index_mean hx F
    (fun i hi => (hprefix i hi).index_mean)
  simpa only [show M + 3 * D + 4 + 1060 = M + 3 * D + 1064 by omega] using
    (bodyEstimate_of_trace_bounds hx F hmean hfailure)

/-- Final large-branch aggregation: the remaining component obligations are
the stopped-prefix mean for each actual round and the per-index failed-round
fiber bound. -/
lemma bodyEstimate_of_prefix_and_index_failure {B c n N M D : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (F : LargeBodyFamily B c n N G x σ)
    (hc : 2 ≤ c) (hlarge : 2 * Lax457868Proofs.refinedCutoffK c < n)
    (hN : n ≤ N)
    (hprefix : ∀ i < Nat.clog 2 n,
      PrefixRoundMeanAt (M := M) (D := D) F i)
    (hindex : ∀ i < Nat.clog 2 n,
      ((Finset.univ.filter fun tape : Tape N =>
        failedAt (F.events tape) i = true).card) ≤
        (n * (2 * n) + n * (n * n) + 1 + n) * 2 ^ (N - n)) :
    BodyEstimate B c n G x σ N (M + 3 * D + 1064) :=
  bodyEstimate_of_prefix_round_means hx F hprefix
    (final_failure_sixth_of_index_bounds F hc hlarge hN hindex)

end Lax457868Proofs.RefinedBodyEstimate
