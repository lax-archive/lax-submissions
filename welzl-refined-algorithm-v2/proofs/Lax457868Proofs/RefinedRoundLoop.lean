import Lax457868Proofs.RefinedRoundDriver
import Lax457868Proofs.AlgorithmRounds
import Lax457868Proofs.RefinedTwinDomain
import Lax457868Proofs.InitialNeighborhoodQuotient
import Lax457868Proofs.RefinedRoundCost

/-! The literal outer reduction loop, with an explicit finite tape reserve.
The loop state contains only facts read from the actual setup and previous
rounds. Its failing branch leaves through `acount = 0`. -/

namespace Lax457868Proofs.RefinedRoundLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.RefinedRecordedCommit

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

def roundGuard : Cond := .lt (.var "cutoffResult") (.var "acount")

/-- Factual state and unconsumed Boolean tape at the entry to a round. -/
def LoopReady {n : ℕ} (B c : ℕ) (G : SimpleGraph (Fin n))
    (x : List ℕ) (rest : List ℕ) (σ : Env) : Prop :=
  ∃ A C : Finset ℕ, ∃ bits : List Bool, ∃ sizes : List ℕ,
    RoundData c n x A C σ ∧
    A ⊆ Finset.range n ∧ C ⊆ Finset.range n ∧ C.Nonempty ∧
    Set.InjOn
      (Lax457868Proofs.ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace
        G (Lax457868Proofs.ReusedOriginal.Construction.PartitionResult.finSetAsSet A))
      (Lax457868Proofs.ReusedOriginal.Construction.PartitionResult.finSetAsSet C) ∧
    Nonempty (Stored G (refinedCutoffK c) σ) ∧
    ValuesBounded B σ ∧
    σ.vars "removedCount" + A.card ≤ n ∧
    σ.vars "round" + A.card ≤ n ∧
    σ.vars "acount" = A.card ∧
    sizes.length = σ.vars "round" ∧
    sizes.sum + 3 * A.card ≤ 3 * n ∧
    2 ^ (σ.vars "round") * (A.card - 2 * c ^ 2) ≤ n ∧
    σ.vars "round" + 1 ≤ Nat.clog 2 n ∧
    σ.out = [] ∧
    σ.inp = bits.map Bool.toNat ++ rest ∧
    A.card * roundBitReserve c n ≤ bits.length

lemma guard_eval {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {A C : Finset ℕ} {σ : Env}
    (D : RoundData c n x A C σ)
    (hA : A ⊆ Finset.range n) (hacount : σ.vars "acount" = A.card)
    (hlargeN : 2 * refinedCutoffK c < n)
    (hB : 4 * (x.length + 1) ≤ B) (hx : Lax11.GraphEncoding.EncodesGraph x n G) :
    roundGuard.evalB B σ = some (decide (2 * refinedCutoffK c < A.card)) := by
  have hnB : n < B := by
    have hlen := hx.length_eq
    omega
  have hcard : A.card ≤ n := by
    simpa using Finset.card_le_card hA
  have hkB : 2 * refinedCutoffK c < B := by
    omega
  have hcutB : σ.vars "cutoffResult" < B := by rw [D.cutoff]; exact hkB
  have hcountB : σ.vars "acount" < B := by rw [hacount]; omega
  simpa [roundGuard, D.cutoff, hacount] using
    (Lax808846Proofs.Reasoning.evalB_condLt
      (Lax808846Proofs.Reasoning.evalB_var hcutB)
      (Lax808846Proofs.Reasoning.evalB_var hcountB))

end Lax457868Proofs.RefinedRoundLoop

namespace Lax457868Proofs.RefinedRoundLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.RefinedRecordedCommit
open Lax457868Proofs.ReusedOriginal.Construction.TracePartitions
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ExceptionRefinementStep

/-- The actual full-neighborhood quotient installs the first loop state.
Its representatives cover all original neighborhoods, and the old history is
still empty. -/
lemma initial_loopReady {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {bits : List Bool} {σ τ : Env} {C : Finset ℕ}
    (R : Lax457868Proofs.RefinedSetup.Ready c n x
      (bits.map Bool.toNat ++ rest) σ)
    (hbounded : ValuesBounded B σ)
    (hrun : Run B Lax457868Proofs.InitialNeighborhoodQuotient.initialQuotientSource σ τ
      (951 * (x.length + 1)))
    (D : RoundData c n x (Finset.range n) C τ)
    (hn2 : 2 ≤ n)
    (hCsub : C ⊆ Finset.range n) (hC : C.Nonempty)
    (htrace : Nonempty (TracePartition G Set.univ Set.univ (finSetAsSet C)))
    (htape : n * roundBitReserve c n ≤ bits.length) :
    LoopReady B c G x rest τ := by
  classical
  have hround : τ.vars "round" = 0 :=
    (hrun.frame_var "round" (by decide)).trans R.round
  have hused : τ.vars "removedCount" = 0 :=
    (hrun.frame_var "removedCount" (by decide)).trans R.removedCount
  have hacount : τ.vars "acount" = n :=
    (hrun.frame_var "acount" (by decide)).trans R.activeCount
  have hremoved : τ.arrs "removed" = arrOf n (fun _ => 0) := by
    rw [hrun.frame_arr "removed" (by decide),
      R.scratch "removed" (by decide) (by decide) (by decide) (by decide)]
    simp [welzlExt, arrOf]
  have hremovedRep : τ.arrs "removedRep" = arrOf n (fun _ => 0) := by
    rw [hrun.frame_arr "removedRep" (by decide),
      R.scratch "removedRep" (by decide) (by decide) (by decide) (by decide)]
    simp [welzlExt, arrOf]
  have hcover : ∀ v : Fin n, ∃ b ∈ finSetAsSet C,
      ∀ a : Fin n, G.Adj v a ↔ G.Adj b a := by
    intro v
    obtain ⟨b, hb, hne⟩ :=
      Lax457868Proofs.RefinedTwinDomain.full_partition_covers
        (Classical.choice htrace) v
    refine ⟨b, hb, ?_⟩
    intro a
    exact Set.ext_iff.mp hne a
  have hstore : Stored G (refinedCutoffK c) τ :=
    initialCovered G (finSetAsSet C) hcover hround hused
      (by
        intro i hi
        rw [view_of_array D.activeA hi]
        simp [setFlag, hi])
      (by
        intro v
        rw [view_of_array D.activeB v.isLt]
        simp [setFlag, finSetAsSet])
      (by
        intro i hi
        rw [view_of_array hremoved hi])
      (by
        intro i hi
        rw [view_of_array hremovedRep hi])
  have hfull : finSetAsSet (n := n) (Finset.range n) = Set.univ := by
    ext v
    simp [finSetAsSet]
  have hsep : Set.InjOn
      (Lax457868Proofs.ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace
        G (finSetAsSet (Finset.range n))) (finSetAsSet C) := by
    rw [hfull]
    exact (Classical.choice htrace).reps_separated
  refine ⟨Finset.range n, C, bits, [], D, Finset.Subset.rfl, hCsub, hC, hsep,
    ⟨hstore⟩, run_preserves hrun hbounded,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hused]
  · simp [hround]
  · simpa using hacount
  · simp [hround]
  · simp
  · simp [hround]
  · rw [hround]
    have hh := Nat.clog_pos (by omega : 1 < 2) (by omega : 1 < n)
    omega
  · rw [hrun.out_eq (by decide), R.output]
  · rw [hrun.frame_inp (by decide), R.input]
  · simpa using htape

end Lax457868Proofs.RefinedRoundLoop

namespace Lax457868Proofs.RefinedRoundLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.RefinedRecordedCommit
open Lax457868Proofs.ReusedOriginal.Construction.TracePartitions
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ExceptionRefinementStep

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-- One true outer-loop iteration either installs a strictly smaller factual
round state, with enough untouched tape for every later round, or executes
the source failure assignment. -/
lemma round_step {B c n : ℕ} {G : SimpleGraph (Fin n)} {x rest : List ℕ}
    {A C : Finset ℕ} {bits : List Bool} {sizes : List ℕ} {σ : Env}
    (D : RoundData c n x A C σ)
    (hA : A ⊆ Finset.range n) (hCsub : C ⊆ Finset.range n)
    (hC : C.Nonempty) (hstore : Stored G (refinedCutoffK c) σ)
    (hbounded : ValuesBounded B σ)
    (hcapacity : σ.vars "removedCount" + A.card ≤ n)
    (hroundCapacity : σ.vars "round" + A.card ≤ n)
    (hacount : σ.vars "acount" = A.card)
    (hsizesLen : sizes.length = σ.vars "round")
    (hsizesSum : sizes.sum + 3 * A.card ≤ 3 * n)
    (hpotential : 2 ^ (σ.vars "round") * (A.card - 2 * c ^ 2) ≤ n)
    (_hroundLog : σ.vars "round" + 1 ≤ Nat.clog 2 n)
    (hout : σ.out = [])
    (hinput : σ.inp = bits.map Bool.toNat ++ rest)
    (htape : A.card * roundBitReserve c n ≤ bits.length)
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hB : 4 * (x.length + 1) ≤ B)
    (hlarge : 2 * refinedCutoffK c < A.card) :
    ∃ τ K, Run B preparedRefinedRoundSource σ τ K ∧
      τ.vars "n" = n ∧
      ((∃ A' : Finset ℕ, A'.card < A.card ∧
          τ.vars "acount" = A'.card ∧ LoopReady B c G x rest τ) ∨
        τ.vars "acount" = 0) := by
  have hbudget :
      n * Lax457868Proofs.InitialSamplerRetriesSource.attemptBitBudget n A.card
          (A.card / (4 * c ^ 2)) n +
        (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) *
          (n * ((64 * Nat.clog 2 c) * n * Nat.clog 2 n)) ≤ bits.length := by
    have hr := round_budget_le (c := c) (n := n) (m := A.card)
      (by simpa using Finset.card_le_card hA)
    have hres : roundBitReserve c n ≤ A.card * roundBitReserve c n := by
      have hh := Nat.mul_le_mul_right (roundBitReserve c n)
        (show 1 ≤ A.card by omega)
      simpa using hh
    exact (hr.trans hres).trans htape
  obtain ⟨τ, K, hrun, hn, hresult⟩ := preparedRefinedRoundSource_run D hx hG hc
    hA hCsub hC hlarge hB hbounded hstore hcapacity
    (by omega : σ.vars "round" < n) hinput hbudget
  refine ⟨τ, K, hrun, hn, ?_⟩
  rcases hresult with ⟨haccepted, hbounded', used, hused, hinput'⟩ | hfail
  · obtain ⟨W, Rnum, Snum, repA, repB, samplerCost, partCostB, partCostA,
      hcostEq, hdata, hstored, hround, hacount', hcapacity', hshrink,
      hpartCost, hSrange, hRrange, hSsub, hRsub, hWsub, hRnonempty,
      hpartA, hpartB⟩ := haccepted
    have hk : 6 * c ^ 2 ≤ refinedCutoffK c := by
      simpa only [refinedCutoffK] using
        Lax457868Proofs.AlgorithmRounds.refined_cutoff_ge_six_sq c hc
    have hstrict : Snum.card < A.card := by nlinarith
    have hcontract : 3 * Snum.card ≤ 2 * A.card := by nlinarith
    have hsizesLen' : (sizes ++ [A.card]).length = τ.vars "round" := by
      simp [hround, hsizesLen]
    have hsizesSum' : (sizes ++ [A.card]).sum + 3 * Snum.card ≤ 3 * n := by
      simp only [List.sum_append, List.sum_singleton]
      omega
    have hmul : Snum.card * roundBitReserve c n + roundBitReserve c n ≤
        A.card * roundBitReserve c n := by
      calc
        _ = (Snum.card + 1) * roundBitReserve c n := by ring
        _ ≤ A.card * roundBitReserve c n :=
          Nat.mul_le_mul_right _ (by omega)
    have husedRes : used ≤ roundBitReserve c n :=
      hused.trans (round_budget_le (c := c) (n := n) (m := A.card)
        (by simpa using Finset.card_le_card hA))
    have htape' : Snum.card * roundBitReserve c n ≤
        (bits.drop used).length := by
      simp only [List.length_drop]
      omega
    have hroundCapacity' : τ.vars "round" + Snum.card ≤ n := by
      omega
    have hpotential' : 2 ^ (τ.vars "round") *
        (Snum.card - 2 * c ^ 2) ≤ n := by
      rw [hround]
      exact Lax457868Proofs.RefinedRoundCost.round_potential_step
        hshrink hpotential
    have hroundLog' : τ.vars "round" + 1 ≤ Nat.clog 2 n := by
      rw [hround]
      exact Lax457868Proofs.RefinedRoundCost.round_counter_with_terminal_after_guard
        (by omega : 1 ≤ c) hk hlarge hpotential
    have hpartB' : TracePartition G (finSetAsSet C)
        (finSetAsSet W) (finSetAsSet Rnum) := by
      simpa [finSetAsSet, setFlag] using (Classical.choice hpartB).partition
    have hpartA' : TracePartition G (finSetAsSet A)
        (finSetAsSet Rnum) (finSetAsSet Snum) := by
      simpa [finSetAsSet, setFlag] using (Classical.choice hpartA).partition
    have hW' : finSetAsSet (n := n) W ⊆ finSetAsSet (n := n) A := by
      intro v hv
      exact hWsub hv
    have hsep' := Lax457868Proofs.RefinedTwinDomain.dual_partition_separated
      hW' hpartB' hpartA'
    exact Or.inl ⟨Snum, hstrict, hacount', Snum, Rnum, bits.drop used,
      sizes ++ [A.card],
      hdata, hSrange, hRrange, hRnonempty, hsep', hstored, hbounded',
      hcapacity', hroundCapacity', hacount', hsizesLen', hsizesSum',
      hpotential', hroundLog', (hrun.out_eq (by decide)).trans hout,
      hinput', htape'⟩
  · exact Or.inr hfail

end Lax457868Proofs.RefinedRoundLoop


namespace Lax457868Proofs.RefinedRoundLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.RefinedRecordedCommit

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private lemma run_while_true {B K K' : ℕ} {b : Cond} {c : Com}
    {σ σ' σ'' : Env} (hb : b.evalB B σ = some true)
    (hbody : Run B c σ σ' K)
    (htail : Run B (.while b c) σ' σ'' K') :
    Run B (.while b c) σ σ'' (1 + b.size + K + K') := by
  obtain ⟨k, hk, hbs⟩ := hbody
  obtain ⟨k', hk', hbs'⟩ := htail
  exact ⟨1 + b.size + k + k', by omega, .while_true hb hbs hbs'⟩

lemma failed_guard_false {B c n : ℕ} {σ : Env}
    (hcut : σ.vars "cutoffResult" = 2 * refinedCutoffK c)
    (hzero : σ.vars "acount" = 0)
    (hlargeN : 2 * refinedCutoffK c < n) (hnB : n < B) :
    roundGuard.evalB B σ = some false := by
  have hcutB : σ.vars "cutoffResult" < B := by rw [hcut]; omega
  have hzeroB : σ.vars "acount" < B := by omega
  simpa [roundGuard, hcut, hzero] using
    (Lax808846Proofs.Reasoning.evalB_condLt
      (Lax808846Proofs.Reasoning.evalB_var hcutB)
      (Lax808846Proofs.Reasoning.evalB_var hzeroB))

/-- The actual reduction loop runs to a threshold state or a marked retry
failure. Every accepted iteration strictly reduces the active ground set, so
strong induction on its physical cardinality closes the loop. -/
lemma round_while_run {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ : Env}
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hB : 4 * (x.length + 1) ≤ B)
    (hlargeN : 2 * refinedCutoffK c < n)
    (hready : LoopReady B c G x rest σ) :
    ∃ τ K, Run B (.while roundGuard preparedRefinedRoundSource) σ τ K ∧
      τ.vars "n" = n ∧
      (τ.vars "acount" = 0 ∨
        (LoopReady B c G x rest τ ∧ τ.vars "acount" ≤ 2 * refinedCutoffK c)) := by
  have hnB : n < B := by
    have hlen := hx.length_eq
    omega
  have core : ∀ m : ℕ, ∀ ρ : Env,
      LoopReady B c G x rest ρ → ρ.vars "acount" = m →
      ∃ τ K, Run B (.while roundGuard preparedRefinedRoundSource) ρ τ K ∧
        τ.vars "n" = n ∧
        (τ.vars "acount" = 0 ∨
          (LoopReady B c G x rest τ ∧ τ.vars "acount" ≤ 2 * refinedCutoffK c)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro ρ hreadyρ hm
      have hreadyKeep := hreadyρ
      obtain ⟨A, C, bits, sizes, D, hA, hCsub, hC, hsep, ⟨hstore⟩, hbounded,
        hcapacity, hroundCapacity, hacount, hsizesLen, hsizesSum,
        hpotential, hroundLog, hout,
        hinput, htape⟩ := hreadyρ
      have hAm : A.card = m := by omega
      have hguard := guard_eval D hA hacount hlargeN hB hx
      by_cases hlarge : 2 * refinedCutoffK c < A.card
      · have htrue : roundGuard.evalB B ρ = some true := by
          simpa [hlarge] using hguard
        obtain ⟨ρ', K, hstep, hnStep, hresult⟩ := round_step D hA hCsub hC hstore
          hbounded hcapacity hroundCapacity hacount hsizesLen hsizesSum
          hpotential hroundLog hout
          hinput htape hx hG hc hB hlarge
        rcases hresult with ⟨A', hstrict, hacount', hready'⟩ | hfail
        · obtain ⟨τ, K', htail, hnTail, hresult'⟩ := ih A'.card
            (by omega) ρ' hready' hacount'
          exact ⟨τ, _, run_while_true htrue hstep htail, hnTail, hresult'⟩
        · have hcut' : ρ'.vars "cutoffResult" = 2 * refinedCutoffK c := by
            rw [hstep.frame_var "cutoffResult" (by decide)]
            exact D.cutoff
          have hfalse := failed_guard_false hcut' hfail hlargeN hnB
          have htail : Run B (.while roundGuard preparedRefinedRoundSource)
              ρ' ρ' (1 + roundGuard.size) := Run.while_false hfalse
          exact ⟨ρ', _, run_while_true htrue hstep htail,
            hnStep, Or.inl hfail⟩
      · have hfalse : roundGuard.evalB B ρ = some false := by
          simpa [hlarge] using hguard
        exact ⟨ρ, 1 + roundGuard.size, Run.while_false hfalse,
          D.vertices, Or.inr ⟨hreadyKeep, by omega⟩⟩
  have hreadyKeep := hready
  obtain ⟨A, C, bits, sizes, D, hA, hC, hne, hsep, hs, hb, hcap, hrc,
    hac, hlen, hsum, hpot, hlog, hout, hin, ht⟩ := hready
  exact core A.card σ hreadyKeep hac

end Lax457868Proofs.RefinedRoundLoop
