import Lax457868Proofs.RefinedSampleSpec
import Lax457868Proofs.SamplerOutputSize
import Lax457868Proofs.SamplerPhases
import Mathlib.Tactic

/-!
The public refined-sample contract follows from the deterministic sampler's
pairwise correctness and its independently proved output subset and size
bounds.
-/

namespace Lax457868Proofs.SamplerContract

open Lax195003.WelzlOrders
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerOutputSize
open Lax457868Proofs.RefinedSampleSpec

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The set system induced by a finite family of neighborhood vertices. -/
def neighborhoodFamily (B : Finset β) (N : β → Finset α) : SetSystem α :=
  {X | ∃ b ∈ B, (N b : Set α) = X}

/-- Under the paper's quotient choices, every successful finite-choice run
satisfies the public refined-sample contract. The only run-specific premise is
that the sampler returns `out`; legal draws and scan orders are explicit in
the sampler's inputs. -/
lemma refinedSampler_IsRefinedSample
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r cap k s c : ℕ)
    (initialAttempts : List (InitialChoice A B N r))
    (groundOrder : List α) (groundOrder_finset : groundOrder.toFinset = A)
    (groundOrder_nodup : groundOrder.Nodup)
    (repairTrials : ∀ choice : InitialChoice A B N r, ∀ b : β,
      List (LocalTrial
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)) s))
    (exceptionOrder : ∀ choice : InitialChoice A B N r, List β)
    (exceptionOrder_finset : ∀ choice,
      (exceptionOrder choice).toFinset = choice.exceptions k)
    (exceptionOrder_nodup : ∀ choice, (exceptionOrder choice).Nodup)
    (hc : 0 < c)
    (hr : r = A.card / (4 * c ^ 2))
    (hcap : cap = A.card / (4 * c ^ 2 * (s + 1)))
    (hN : ∀ b ∈ B, N b ⊆ A)
    (out : Finset α)
    (hret : refinedSampler A B N r cap k s initialAttempts groundOrder
      groundOrder_finset groundOrder_nodup repairTrials exceptionOrder
      exceptionOrder_finset exceptionOrder_nodup = some out) :
    IsRefinedSample (neighborhoodFamily B N) (A : Set α) (out : Set α)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k := by
  have hout := refinedSampler_output_bound A B N r cap k s c
    initialAttempts groundOrder groundOrder_finset groundOrder_nodup
    repairTrials exceptionOrder exceptionOrder_finset exceptionOrder_nodup
    hc hr hcap hN out hret
  have hpair := refinedSampler_pairwise_correct A B N r cap k s
    initialAttempts groundOrder groundOrder_finset groundOrder_nodup
    repairTrials exceptionOrder exceptionOrder_finset exceptionOrder_nodup
    hN out hret
  refine ⟨A.finite_toSet, ?_, ?_, ?_, ?_⟩
  · intro X hX
    rcases hX with ⟨b, hb, rfl⟩
    intro a ha
    exact hN b hb ha
  · intro a ha
    exact hout.1 ha
  · simpa using hout.2
  · intro X hX Y hY htrace
    rcases hX with ⟨b, hb, rfl⟩
    rcases hY with ⟨b', hb', rfl⟩
    have htraceFin : N b ∩ out = N b' ∩ out := by
      apply Finset.coe_injective
      simpa only [Finset.coe_inter] using htrace
    have htrace' : trace N out b = trace N out b' := by
      simpa [trace, Finset.inter_comm] using htraceFin
    have hclose := hpair b hb b' hb' htrace'
    have hset :
        (((N b : Set α) \ (N b' : Set α)) ∪
          ((N b' : Set α) \ (N b : Set α))) =
          (↑((N b \ N b') ∪ (N b' \ N b)) : Set α) := by
      ext a
      simp
    rw [hset, Set.ncard_coe_finset]
    exact hclose

end Lax457868Proofs.SamplerContract
