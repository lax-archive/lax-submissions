import Lax457868Proofs.RefinedRoundDriver
import Lax457868Proofs.AlgorithmRounds

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

def roundGuard : Cond := .lt (.var "cutoffResult") (.var "acount")

/-- Factual state and unconsumed Boolean tape at the entry to a round. -/
def LoopReady {n : ℕ} (B c : ℕ) (G : SimpleGraph (Fin n))
    (x : List ℕ) (rest : List ℕ) (σ : Env) : Prop :=
  ∃ A C : Finset ℕ, ∃ bits : List Bool,
    RoundData c n x A C σ ∧
    A ⊆ Finset.range n ∧ C ⊆ Finset.range n ∧ C.Nonempty ∧
    Nonempty (Stored G (refinedCutoffK c) σ) ∧
    ValuesBounded B σ ∧
    σ.vars "removedCount" + A.card ≤ n ∧
    σ.vars "round" + A.card ≤ n ∧
    σ.vars "acount" = A.card ∧
    σ.inp = bits.map Bool.toNat ++ rest ∧
    A.card * roundBitReserve c n ≤ bits.length

private lemma guard_eval {B c n : ℕ} {G : SimpleGraph (Fin n)}
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
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.RefinedRecordedCommit

set_option maxRecDepth 4000

/-- One true outer-loop iteration either installs a strictly smaller factual
round state, with enough untouched tape for every later round, or executes
the source failure assignment. -/
lemma round_step {B c n : ℕ} {G : SimpleGraph (Fin n)} {x rest : List ℕ}
    {A C : Finset ℕ} {bits : List Bool} {σ : Env}
    (D : RoundData c n x A C σ)
    (hA : A ⊆ Finset.range n) (hCsub : C ⊆ Finset.range n)
    (hC : C.Nonempty) (hstore : Stored G (refinedCutoffK c) σ)
    (hbounded : ValuesBounded B σ)
    (hcapacity : σ.vars "removedCount" + A.card ≤ n)
    (hroundCapacity : σ.vars "round" + A.card ≤ n)
    (hacount : σ.vars "acount" = A.card)
    (hinput : σ.inp = bits.map Bool.toNat ++ rest)
    (htape : A.card * roundBitReserve c n ≤ bits.length)
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hB : 4 * (x.length + 1) ≤ B)
    (hlarge : 2 * refinedCutoffK c < A.card) :
    ∃ τ K, Run B preparedRefinedRoundSource σ τ K ∧
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
  obtain ⟨τ, K, hrun, hresult⟩ := preparedRefinedRoundSource_run D hx hG hc
    hA hCsub hC hlarge hB hbounded hstore hcapacity
    (by omega : σ.vars "round" < n) hinput hbudget
  refine ⟨τ, K, hrun, ?_⟩
  rcases hresult with ⟨haccepted, hbounded', used, hused, hinput'⟩ | hfail
  · obtain ⟨W, Rnum, Snum, repA, repB, samplerCost, partCostB, partCostA,
      hcostEq, hdata, hstored, hround, hacount', hcapacity', hshrink,
      hpartCost, hSrange, hRrange, hSsub, hRsub, hWsub, hRnonempty,
      hpartA, hpartB⟩ := haccepted
    have hk : 6 * c ^ 2 ≤ refinedCutoffK c := by
      simpa only [refinedCutoffK] using
        Lax457868Proofs.AlgorithmRounds.refined_cutoff_ge_six_sq c hc
    have hstrict : Snum.card < A.card := by nlinarith
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
    exact Or.inl ⟨Snum, hstrict, hacount', Snum, Rnum, bits.drop used,
      hdata, hSrange, hRrange, hRnonempty, hstored, hbounded',
      hcapacity', hroundCapacity', hacount', hinput', htape'⟩
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

private lemma run_while_true {B K K' : ℕ} {b : Cond} {c : Com}
    {σ σ' σ'' : Env} (hb : b.evalB B σ = some true)
    (hbody : Run B c σ σ' K)
    (htail : Run B (.while b c) σ' σ'' K') :
    Run B (.while b c) σ σ'' (1 + b.size + K + K') := by
  obtain ⟨k, hk, hbs⟩ := hbody
  obtain ⟨k', hk', hbs'⟩ := htail
  exact ⟨1 + b.size + k + k', by omega, .while_true hb hbs hbs'⟩

private lemma failed_guard_false {B c n : ℕ} {σ : Env}
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
      (τ.vars "acount" = 0 ∨
        (LoopReady B c G x rest τ ∧ τ.vars "acount" ≤ 2 * refinedCutoffK c)) := by
  have hnB : n < B := by
    have hlen := hx.length_eq
    omega
  have core : ∀ m : ℕ, ∀ ρ : Env,
      LoopReady B c G x rest ρ → ρ.vars "acount" = m →
      ∃ τ K, Run B (.while roundGuard preparedRefinedRoundSource) ρ τ K ∧
        (τ.vars "acount" = 0 ∨
          (LoopReady B c G x rest τ ∧ τ.vars "acount" ≤ 2 * refinedCutoffK c)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro ρ hreadyρ hm
      have hreadyKeep := hreadyρ
      obtain ⟨A, C, bits, D, hA, hCsub, hC, ⟨hstore⟩, hbounded,
        hcapacity, hroundCapacity, hacount, hinput, htape⟩ := hreadyρ
      have hAm : A.card = m := by omega
      have hguard := guard_eval D hA hacount hlargeN hB hx
      by_cases hlarge : 2 * refinedCutoffK c < A.card
      · have htrue : roundGuard.evalB B ρ = some true := by
          simpa [hlarge] using hguard
        obtain ⟨ρ', K, hstep, hresult⟩ := round_step D hA hCsub hC hstore
          hbounded hcapacity hroundCapacity hacount hinput htape hx hG hc hB hlarge
        rcases hresult with ⟨A', hstrict, hacount', hready'⟩ | hfail
        · obtain ⟨τ, K', htail, hresult'⟩ := ih A'.card
            (by omega) ρ' hready' hacount'
          exact ⟨τ, _, run_while_true htrue hstep htail, hresult'⟩
        · have hcut' : ρ'.vars "cutoffResult" = 2 * refinedCutoffK c := by
            rw [hstep.frame_var "cutoffResult" (by decide)]
            exact D.cutoff
          have hfalse := failed_guard_false hcut' hfail hlargeN hnB
          have htail : Run B (.while roundGuard preparedRefinedRoundSource)
              ρ' ρ' (1 + roundGuard.size) := Run.while_false hfalse
          exact ⟨ρ', _, run_while_true htrue hstep htail, Or.inl hfail⟩
      · have hfalse : roundGuard.evalB B ρ = some false := by
          simpa [hlarge] using hguard
        exact ⟨ρ, 1 + roundGuard.size, Run.while_false hfalse,
          Or.inr ⟨hreadyKeep, by omega⟩⟩
  have hreadyKeep := hready
  obtain ⟨A, C, bits, D, hA, hC, hne, hs, hb, hcap, hrc, hac, hin, ht⟩ := hready
  exact core A.card σ hreadyKeep hac

end Lax457868Proofs.RefinedRoundLoop
