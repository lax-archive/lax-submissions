import Lax457868Proofs.RefinedRoundPrefix
import Lax457868Proofs.CompleteSamplerMean

/-! Relate the actual source-round cost to the actual complete-sampler cost.
All deterministic preparation, partition and history work is already checked. -/
namespace Lax457868Proofs.RefinedRoundMean
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.PrepareRefinedRound
open Lax457868Proofs.CompleteSamplerSource
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.RefinedRecordedCommit

lemma sampler_subrun {B K cost : ℕ} {σ σp τ : Env}
    (hp : Run B prepareRefinedRound σ σp K)
    (ha : BigStepB B preparedRefinedRoundSource σ τ cost) :
    ∃ σs ks, BigStepB B completeSamplerSource σp σs ks := by
  change BigStepB B (prepareRefinedRound.seq (completeSamplerSource.seq _)) σ τ cost at ha
  cases ha with
  | seq hpre hr =>
    obtain ⟨kp,hkp,hp⟩ := hp
    obtain ⟨he,hk⟩ := BigStep.unique hpre.bigStep hp.bigStep
    subst_vars
    cases hr with
    | seq hs ht => exact ⟨_,_,hs⟩

lemma actual_prepared_cost
    {B c n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A C : Finset ℕ} {σ τ : Env} {cost : ℕ}
    (D : RoundData c n x A C σ)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hCsub : C ⊆ Finset.range n) (hC : C.Nonempty)
    (hlarge : 2 * refinedCutoffK c < A.card)
    (hbounded : ValuesBounded B σ) (hstore : Stored G (refinedCutoffK c) σ)
    (hcapacity : σ.vars "removedCount" + A.card ≤ n)
    (hround : σ.vars "round" < n)
    (R : ReadyInput B n A.card n (A.card/(4*c^2)) n n
      (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n) (refinedCutoffK c)
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) G x A)
    (S : RuntimeInput R (64*Nat.clog 2 c) n)
    (hprep : Run B prepareRefinedRound σ R.I.σ (40*n+58))
    (hCarray : R.I.activeB = setFlag C)
    (hretryCap : R.I.σ.vars "initialRetryCap" = n)
    (hbudget : n*attemptBitBudget n A.card (A.card/(4*c^2)) n +
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) *
        (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ R.I.bits.length)
    (ha : BigStepB B preparedRefinedRoundSource σ τ cost) :
    ∃ σs ks, BigStepB B completeSamplerSource R.I.σ σs ks ∧
      cost ≤ ks+1946*(x.length+1) := by
  obtain ⟨σs,ks,hs⟩ := sampler_subrun hprep ha
  refine ⟨σs,ks,hs,?_⟩
  have hrs : Run B completeSamplerSource R.I.σ σs ks := Run.of_bigStepB hs
  have hCnonempty : (activeVertices n R.I.activeB).Nonempty := by
    rw [hCarray]
    obtain ⟨v,hv⟩ := hC
    exact ⟨v,mem_activeVertices.mpr ⟨Finset.mem_range.mp (hCsub hv),
      by simp [setFlag,hv]⟩⟩
  obtain ⟨σa,charges,phaseCost,partitionCost,groupCost,offsetCost,repairCost,
      samplerCost,hsampler,hchecked,hcharges,hsamCost,hsamInput,hsamFrame,houtcome⟩ :=
    completeSamplerSource_run R S hretryCap (by have := R.hnB; omega) hbudget
      hCnonempty (by omega : refinedCutoffK c < A.card) (by omega : 0<c) rfl rfl
  have heq : σa = σs := by
    obtain ⟨_,_,hh⟩ := hsampler
    exact (BigStep.unique hh.bigStep hs.bigStep).1
  subst σa
  have hlen : n ≤ x.length := by have := R.I.hx.length_eq; omega
  have bound {υ : Env} {K : ℕ} (hr : Run B preparedRefinedRoundSource σ υ K)
      (hK : K ≤ ks+1946*(x.length+1)) : cost ≤ ks+1946*(x.length+1) := by
    obtain ⟨j,hj,hr⟩ := hr
    have he := (BigStep.unique ha.bigStep hr.bigStep).2
    omega
  rcases houtcome with hsuccess | hfailInitial | hfailRepair
  · obtain ⟨W,packed,hstatus2,hflags,hord,hprefix,hcount,hsample,
      σpre,consumed,hpre,hinp,hused,haccepted⟩ := hsuccess
    obtain ⟨choice,q,L,Lfinal,steps,initialPacked,phaseTwoPacked,
      hprestatus,hstatus1,hrest⟩ := haccepted
    obtain ⟨τout,Rnum,Snum,partCostB,partCostA,hwhole,hinputFrame,hdata,
      hstored,hboundedOut,hroundOut,hacountOut,hcapOut,hshrink,hpartCost,hrest⟩ :=
      accepted_prepared_round D hstore hbounded hcapacity hround hG hc hCsub
        R S hprep hCarray hrs hsamFrame hstatus1 hstatus2
        ⟨packed,hord,hprefix⟩ hcount hsample hC
    apply bound hwhole
    simp only [Cond.size,Expr.size]
    omega
  · have hfail := failed_initial_round_run hrs hfailInitial
      (by have := R.hnB; omega : 3<B)
    have hwhole := hprep.seq hfail
    apply bound hwhole
    simp only [Cond.size,Expr.size]
    omega
  · by_cases hinit : σs.vars "initialRetryStatus" = 1
    · have hfail := failed_repair_round_run hrs hinit hfailRepair
        (by have := R.hnB; omega : 3<B)
      apply bound (hprep.seq hfail)
      simp only [Cond.size,Expr.size]
      omega
    · have hbR := run_preserves hprep hbounded
      have hbS := run_preserves hrs hbR
      have hfail := failed_initial_ne hrs (hbS.vars "initialRetryStatus") hinit R.I.honeB
      apply bound (hprep.seq hfail)
      simp only [Cond.size,Expr.size]
      omega

/-- The same deterministic preparation feeds the sampler on every fair suffix.
All recorded round costs are compared to the actual sampler costs. -/
lemma actual_prepared_family
    {B c n N : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A C : Finset ℕ} {σ : Env}
    (D : RoundData c n x A C σ)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hCsub : C ⊆ Finset.range n) (hC : C.Nonempty)
    (hlarge : 2 * refinedCutoffK c < A.card)
    (hbounded : ValuesBounded B σ) (hstore : Stored G (refinedCutoffK c) σ)
    (hcapacity : σ.vars "removedCount" + A.card ≤ n)
    (hround : σ.vars "round" < n)
    (R : ReadyInput B n A.card n (A.card/(4*c^2)) n n
      (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n) (refinedCutoffK c)
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) G x A)
    (S : RuntimeInput R (64*Nat.clog 2 c) n)
    (hprep : Run B prepareRefinedRound σ R.I.σ (40*n+58))
    (hCarray : R.I.activeB = setFlag C)
    (hretryCap : R.I.σ.vars "initialRetryCap" = n)
    (hbudget : n*attemptBitBudget n A.card (A.card/(4*c^2)) n +
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) *
        (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ N)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (ha : ∀ ρ, BigStepB B preparedRefinedRoundSource
      {σ with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest} (final ρ) (cost ρ)) :
    ∃ samplerFinal : Tape N → Env, ∃ samplerCost : Tape N → ℕ,
      (∀ ρ, BigStepB B completeSamplerSource
        {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest}
        (samplerFinal ρ) (samplerCost ρ)) ∧
      (∀ ρ, cost ρ ≤ samplerCost ρ+1946*(x.length+1)) := by
  classical
  have hn : 1 ≤ n := by
    obtain ⟨a,ha⟩ := R.I.hAnonempty
    have := Finset.mem_range.mp (R.I.hA ha)
    omega
  have hper : attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N :=
    (Nat.le_mul_of_pos_left _ hn).trans (by omega)
  have hin : σ.inp = R.I.σ.inp := (hprep.frame_inp (by decide)).symm
  have hp (ρ : Tape N) : Run B prepareRefinedRound
      {σ with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest}
      {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest} (40*n+58) := by
    simpa only [List.nil_append] using
      StoppedPrefixAveraging.run_replace_consumed_suffix hprep []
        (by simpa using hin) ((List.ofFn ρ).map Bool.toNat ++ R.I.rest)
  have hd (ρ : Tape N) : ∃ σs ks, BigStepB B completeSamplerSource
      {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest} σs ks ∧
      cost ρ ≤ ks+1946*(x.length+1) := by
    let σ' : Env := {σ with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest}
    have D' : RoundData c n x A C σ' :=
      ⟨D.parameter,D.vertices,D.radixSize,D.cutoff,D.logParameter,D.offsets,D.targets,
        D.activeA,D.activeB,D.lengths,D.cleared,D.nextA_bits,D.nextB_bits⟩
    have hb : ValuesBounded B σ' := by
      refine ⟨hbounded.vars,hbounded.arrays,?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hbit | hrest
      · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hbit
        cases b <;> simp <;> have := R.I.honeB <;> omega
      · apply hbounded.input v
        rw [hin,R.I.hinput]
        exact List.mem_append_right _ hrest
    have hs : Stored G (refinedCutoffK c) σ' :=
      hstore.frame rfl rfl rfl rfl rfl rfl rfl rfl
    exact actual_prepared_cost D' hG hc hCsub hC hlarge hb hs hcapacity hround
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper))
      (CompleteSamplerMean.runtime_reinput R S (List.ofFn ρ)
        (by simpa [attemptBitBudget] using hper)) (hp ρ) hCarray hretryCap
      (by simpa only [ReadyInput.reinput_bits,List.length_ofFn] using hbudget) (ha ρ)
  choose samplerFinal samplerCost hr hcost using hd
  exact ⟨samplerFinal,samplerCost,hr,hcost⟩

end Lax457868Proofs.RefinedRoundMean
