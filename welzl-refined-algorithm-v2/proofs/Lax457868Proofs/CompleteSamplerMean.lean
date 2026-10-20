import Lax457868Proofs.CompleteSamplerSource
import Lax457868Proofs.FullInitialAttemptMean

/-! The actual initial-retry boundary used to compose the complete sampler's
cost and failure estimates with the deterministic preparation and repair loop. -/
namespace Lax457868Proofs.CompleteSamplerMean
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.CompleteSamplerSource
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.StoppedPrefixAveraging
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting

variable {B n m domainCap r t bufferCap targetCap Q k cap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}

structure Cut
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (attemptCap : ℕ) where
  final : Env
  used : ℕ
  cost : ℕ
  run : Run B initialSamplerRetriesSource R.I.σ final cost
  used_le : used ≤ attemptCap*attemptBitBudget n m r t
  input : final.inp = (R.I.bits.drop used).map Bool.toNat ++ R.I.rest
  vertices : final.vars "n" = n
  power : final.vars "qpow" = Q
  status : final.vars "initialRetryStatus" = 1 ∨
    final.vars "initialRetryStatus" = 2 ∨ final.vars "initialRetryStatus" = 3
  accepted : final.vars "initialRetryStatus" = 1 →
    AcceptedResult G A (activeVertices n R.I.activeB) r k cap final

lemma cut_exists
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (attemptCap : ℕ) (hcap : R.I.σ.vars "initialRetryCap" = attemptCap)
    (hcapB : attemptCap < B)
    (hb : attemptCap*attemptBitBudget n m r t ≤ R.I.bits.length) :
    Nonempty (Cut R attemptCap) := by
  obtain ⟨σ,charges,used,hr,hchecked,hlen,hu,hi,hn,hq,ho⟩ :=
    initialSamplerRetriesSource_run attemptCap R hcap hcapB hb
  have hgood (h : AcceptedResult G A (activeVertices n R.I.activeB) r k cap σ) :
      σ.vars "initialRetryStatus" = 1 := by
    obtain ⟨rep,choice,packed,sample,hstatus,hrest⟩ := h
    exact hstatus
  refine ⟨⟨σ,used,_,hr,hu,hi,hn,hq,?_,?_⟩⟩
  · rcases ho with ha | h2 | h3
    · exact Or.inl (hgood ha)
    · exact Or.inr (Or.inl h2.1)
    · exact Or.inr (Or.inr h3.1)
  · intro hs
    rcases ho with ha | h2 | h3
    · exact ha
    · omega
    · omega

/-- The literal guarded remainder after the retry loop. -/
def afterInitial : Com := .ite (.eq (.var "initialRetryStatus") (.lit 1))
  completeSamplerTail .skip

lemma actual_decompose
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    {attemptCap : ℕ} (C : Cut R attemptCap) {τ : Env} {cost : ℕ}
    (ha : BigStepB B completeSamplerSource R.I.σ τ cost) :
    ∃ ki kt, BigStepB B initialSamplerRetriesSource R.I.σ C.final ki ∧
      BigStepB B afterInitial C.final τ kt ∧ cost = ki+kt := by
  change BigStepB B (initialSamplerRetriesSource.seq afterInitial) R.I.σ τ cost at ha
  cases ha with
  | seq hi ht =>
    obtain ⟨_,_,hc⟩ := C.run
    obtain ⟨he,hk⟩ := BigStep.unique hi.bigStep hc.bigStep
    subst_vars
    exact ⟨_,_,hi,ht,rfl⟩

/-- Replaying an unread suffix preserves the actual retry stopping state,
including its acceptance status and all representative arrays. -/
lemma cut_causal
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (attemptCap N : ℕ) (hper : attemptBitBudget n m r t ≤ N)
    (hb : attemptCap*attemptBitBudget n m r t ≤ N)
    (C : ∀ ρ : Tape N, Cut
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)) attemptCap)
    (ρ η : Tape N)
    (hp : (List.ofFn ρ).take (C ρ).used = (List.ofFn η).take (C ρ).used) :
    (C η).used = (C ρ).used ∧ (C η).final =
      {(C ρ).final with inp := ((List.ofFn η).drop (C ρ).used).map Bool.toNat ++ R.I.rest} := by
  exact bool_run_same_prefix (σ := R.I.σ) (List.ofFn ρ) (List.ofFn η) R.I.rest
    (C ρ).run (C η).run (C ρ).input (C η).input
    (by simpa using (C ρ).used_le.trans hb)
    (by simpa using (C η).used_le.trans hb) hp

end Lax457868Proofs.CompleteSamplerMean
