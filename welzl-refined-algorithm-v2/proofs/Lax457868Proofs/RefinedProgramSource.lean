import Lax457868Proofs.RefinedClockSetup
import Lax457868Proofs.RefinedRoundDriver
import Lax457868Proofs.InitialNeighborhoodQuotient
import Lax457868Proofs.ReusedOriginal.Construction.WelzlStraight
import Lax457868Proofs.ReusedOriginal.Construction.Correctness
import Lax457868Proofs.SourceTapePrefix

/-! The fixed source command to be compiled for the black-box public theorem.
Only the clock coefficient is a program parameter; it is chosen once from
the proved mean-cost bound, not from the graph input. -/
namespace Lax457868Proofs.RefinedProgramSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.RefinedSetup
open Lax457868Proofs.RefinedClockSetup
open Lax457868Proofs.ClockedSource
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.InitialNeighborhoodQuotient

/-- Failed capped sampling stops the reduction loop by setting `acount` to
zero. That branch outputs the natural order; successful termination replays
the recorded reductions. -/
def finishRefined : Com :=
  .ite (.eq (.var "acount") (.lit 0)) writeNaturalOrder reconstructAndWrite

/-- Initial full-neighborhood deduplication, repeated refined reduction,
and the original reconstruction. Small inputs use the original natural
order source directly. -/
def algorithmBody : Com :=
  .ite (.lt (.var "cutoffResult") (.var "acount"))
    (seqs [initialQuotientSource,
      .while (.lt (.var "cutoffResult") (.var "acount")) preparedRefinedRoundSource,
      finishRefined])
    writeNaturalOrder

/-- The source clock is installed after deterministic input setup. -/
def programSource (D : ℕ) : Com :=
  seqs [refinedSetupSource, clockSetup D, clocked algorithmBody]

/-- Clock initialization changes no fact required by the algorithm's initial
workspace invariant. The working logarithm `L` is intentionally absent from
that invariant: the parameter logarithm is stored in `refinedLogC`. -/
lemma setup_ready_after_clock {c n : ℕ} {x bits : List ℕ} {σ τ : Env}
    (R : RefinedSetup.Ready c n x bits σ)
    (hv : ∀ v, v ≠ "L" → ¬ protectedName v → τ.vars v = σ.vars v)
    (ha : τ.arrs = σ.arrs) (hi : τ.inp = σ.inp) (ho : τ.out = σ.out) :
    RefinedSetup.Ready c n x bits τ := by
  constructor
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.parameter
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.vertices
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.radixSize
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.cutoff
  · intro h; exact (hv _ (by decide) (by unfold protectedName; decide)).trans (R.logParameter h)
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.activeCount
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.activeBCount
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.success
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.round
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.removedCount
  · simpa only [ha] using R.offsets
  · simpa only [ha] using R.targets
  · simpa only [ha] using R.activeA
  · simpa only [ha] using R.activeB
  · simpa only [ha] using R.lengths
  · simpa only [ha] using R.scratch
  · exact hi.trans R.input
  · exact ho.trans R.output
  · exact (hv _ (by decide) (by unfold protectedName; decide)).trans R.edges

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma algorithmBody_fresh : Fresh algorithmBody := by
  unfold Fresh protectedName
  decide

/-- The small-input branch is an actual source run of the original natural
order routine and already meets the exact refined crossing bound. -/
lemma algorithmBody_small_run {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x bits : List ℕ} {σ : Env}
    (R : RefinedSetup.Ready c n x bits σ)
    (hn2 : 2 ≤ n) (hnB : n < B)
    (hsmall : n ≤ 2 * refinedCutoffK c) :
    ∃ τ, Run B algorithmBody σ τ
      (1 + (Cond.lt (.var "cutoffResult") (.var "acount")).size + (10 * n + 6)) ∧
      Lax195003.WelzlOrdersInGraphs.EncodesGraphWelzlOrder G 1
        (2 * refinedCutoffK c * Nat.clog 2 n) τ.out := by
  have hcut : σ.vars "cutoffResult" = n := by
    rw [R.cutoff, Nat.min_eq_left hsmall]
  have hg : (Cond.lt (.var "cutoffResult") (.var "acount")).evalB B σ =
      some false := by
    rw [evalB_condLt (evalB_var (by rw [hcut]; exact hnB))
      (evalB_var (by rw [R.activeCount]; exact hnB))]
    simp [hcut, R.activeCount]
  obtain ⟨τ, hr, ho⟩ :=
    ReusedOriginal.Construction.WelzlStraight.writeNaturalOrder_run R.vertices hnB
  refine ⟨τ, Run.ite_false hg hr, ?_⟩
  rw [ho, R.output, List.nil_append]
  apply ReusedOriginal.Construction.Correctness.naturalOrder_encodesGraphWelzlOrder
  have hl : 1 ≤ Nat.clog 2 n := by
    have hh := Nat.clog_pos (by omega : 1 < 2) (by omega : 1 < n)
    omega
  exact hsmall.trans (by nlinarith)

/-- Initialize the actual algorithm and its clock from the encoded input.
The clock capacity is the desired linear-input-times-logarithm shape. -/
lemma initialize_with_clock_run {B c n D : ℕ} {G : SimpleGraph (Fin n)}
    {x bits : List ℕ} (hx : EncodesGraph x n G) (hc2 : 2 ≤ c) (hn2 : 2 ≤ n)
    (hB : 4 * (x.length + 1) ≤ B) (h768 : 768 < B)
    (hinput : ∀ v ∈ (c :: x) ++ bits, v < B)
    (hD : 1 ≤ D) (hclock : D * (x.length + 1) < B) :
    ∃ σ, Run B (refinedSetupSource.seq (clockSetup D))
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) ((c :: x) ++ bits)) σ
      (40 * (x.length + Nat.clog 2 n + 1) + 24 * Nat.clog 2 n + 284) ∧
      RefinedSetup.Ready c n x bits σ ∧
      RefinedRecordedCommit.ValuesBounded B σ ∧
      ClockedSource.Ready B (D * (x.length + 1)) σ ∧
      capacity (D * (x.length + 1)) σ =
        D * (x.length + 1) * (Nat.clog 2 n + 1) := by
  obtain ⟨τ, hr, R, hb⟩ := refinedSetupSource_run hx hc2 hB h768 hinput
  have hlen := hx.length_eq
  have heq : n + 2 * edgeCount x + 4 = x.length + 1 := by omega
  have hsize : D * (n + 2 * edgeCount x + 4) < B := by
    simpa only [heq] using hclock
  have hpow : 2 ^ Nat.clog 2 n < B := by
    rw [← R.radixSize]
    exact hb.vars _
  have hlog : Nat.clog 2 n + 1 < B := by
    have hh := Nat.clog_le_of_le_pow n.lt_two_pow_self.le
    omega
  obtain ⟨σ, hrc, hready, hcap, hv, ha, hi, ho⟩ :=
    clockSetup_run R.vertices R.edges R.radixSize hn2 hD hsize hpow hlog
  refine ⟨σ, ?_, setup_ready_after_clock R hv ha hi ho,
    RefinedRecordedCommit.run_preserves hrc hb, ?_, ?_⟩
  · convert hr.seq hrc using 1 <;> ring
  · simpa only [heq] using hready
  · simpa only [heq] using hcap

/-- Deterministic initialization has one common memory state on every
random tape. This derives the fresh suffix property from the actual run. -/
lemma initialization_preserves_random_suffix {B c n D : ℕ}
    {x : List ℕ} {σ : Env}
    (R : RefinedSetup.Ready c n x [] σ)
    (hr : Run B (refinedSetupSource.seq (clockSetup D))
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) (c :: x)) σ
      (40 * (x.length + Nat.clog 2 n + 1) + 24 * Nat.clog 2 n + 284))
    (bits : List ℕ) :
    Run B (refinedSetupSource.seq (clockSetup D))
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) ((c :: x) ++ bits))
      {σ with inp := bits}
      (40 * (x.length + Nat.clog 2 n + 1) + 24 * Nat.clog 2 n + 284) := by
  obtain ⟨k, hk, hrun⟩ := hr
  obtain ⟨pre, hin, _, hrep⟩ := SourceTapePrefix.consumed_prefix hrun
  have hp : c :: x = pre := by
    simpa only [initEnv, R.input, List.append_nil] using hin
  subst pre
  exact ⟨k, hk, by simpa [initEnv] using hrep bits⟩

end Lax457868Proofs.RefinedProgramSource
