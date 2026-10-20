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

/-- The accepted continuation contains the actual packed repair execution;
all deterministic preparation contributes the computed additive bound. -/
lemma actual_accepted_tail
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    {s repairCap attemptCap : ℕ} (S : RuntimeInput R s repairCap)
    (C : Cut R attemptCap) (hs : C.final.vars "initialRetryStatus" = 1)
    {τ : Env} {cost : ℕ} (ha : BigStepB B afterInitial C.final τ cost) :
    ∃ choice : SamplerPhases.InitialChoice A (activeVertices n R.I.activeB)
        (fun b => ExceptionPhaseSource.numericNeighborhood G b ∩ A) r,
    ∃ q : ℕ,
    ∃ L : ExceptionRepairLoop.LoopInput B n s t bufferCap targetCap q repairCap k
        (choice.exceptions k).card G x (choice.exceptions k)
        (activeVertices n R.I.activeB)
        (ExceptionPhaseSource.phaseTwoSample G (choice.exceptions k) A choice.sample)
        A (ExceptionPhaseSource.phaseTwoSample G (choice.exceptions k) A choice.sample),
    ∃ repairCost : ℕ,
      BigStepB B ExceptionRepairLoop.exceptionRepairPackedSource L.σ τ repairCost ∧
      cost ≤ repairCost + (1229*n+987*targetCap+64*Q+575) ∧
      L.bits = R.I.bits.drop C.used ∧ L.rest = R.I.rest ∧
      (choice.exceptions k).card ≤ cap ∧
      (∀ b ∈ activeVertices n R.I.activeB, choice.representative b = L.rep b) := by
  obtain ⟨choice,q,L,pc,fc,gc,oc,ip,pp,hprep,hpc,hfc,hgc,hoc,hip,hpp,hq,
    hbits,hrest,hstatus,hcap,hrep,hbound⟩ := accepted_preparation_run R S C.run
      C.vertices C.power (R.I.bits.drop C.used) C.input (C.accepted hs)
  have hg : (Cond.eq (.var "initialRetryStatus") (.lit 1)).evalB B C.final =
      some true := by
    simp [Cond.evalB, Expr.evalB, fit, hs, R.I.honeB]
  change BigStepB B (.ite _ (prepareRepairSource.seq
    ExceptionRepairLoop.exceptionRepairPackedSource) .skip) C.final τ cost at ha
  cases ha with
  | ite_false hf _ => simp [hg] at hf
  | ite_true _ ht =>
    cases ht with
    | seq hp hr =>
      obtain ⟨kp,hkp,hp'⟩ := hprep
      obtain ⟨he,hcost⟩ := BigStep.unique hp.bigStep hp'.bigStep
      subst_vars
      refine ⟨choice,q,L,_,hr,?_,hbits,hrest,hcap,hrep⟩
      simp only [Cond.size, Expr.size]
      omega

lemma actual_stopped_tail
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    {attemptCap : ℕ} (C : Cut R attemptCap)
    (hs : C.final.vars "initialRetryStatus" ≠ 1)
    {τ : Env} {cost : ℕ} (ha : BigStepB B afterInitial C.final τ cost) :
    τ = C.final ∧ cost = 5 := by
  have hstatus := C.status
  have hb : C.final.vars "initialRetryStatus" < B := by
    have := R.hnB
    have hn : 0 < n := by
      obtain ⟨a,ha⟩ := R.I.hAnonempty
      have := Finset.mem_range.mp (R.I.hA ha)
      omega
    omega
  have hg : (Cond.eq (.var "initialRetryStatus") (.lit 1)).evalB B C.final =
      some false := by
    simp [Cond.evalB, Expr.evalB, fit, hb, hs, R.I.honeB]
  have hr := Run.ite_false (c := completeSamplerTail) hg (Run.skip (B := B))
  obtain ⟨j,hj,hh⟩ := hr
  obtain ⟨he,hk⟩ := BigStep.unique ha.bigStep hh.bigStep
  constructor
  · exact he
  · change BigStepB B (.ite _ _ .skip) C.final C.final j at hh
    cases hh with
    | ite_true ht _ => simp [hg] at ht
    | ite_false _ ht => cases ht; simpa [Cond.size,Expr.size] using hk

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
