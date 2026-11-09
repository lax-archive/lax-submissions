import Lax457868Proofs.CompleteSamplerMean
import Lax457868Proofs.NumericRepairProbability
import Lax457868Proofs.RefinedRepairCharges
import Lax457868Proofs.ExceptionLoopMean
import Lax457868Proofs.InitialRetryMean
import Lax457868Proofs.NumericGraphProbability
import Lax457868Proofs.RefinedRoundInput

/-! Collect the actual sampler costs with the paper's parameter choices. -/
namespace Lax457868Proofs.RefinedSamplerMean
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.InitialRetryMean
open Lax457868Proofs.CompleteSamplerSource
open Lax457868Proofs.CompleteSamplerMean
open Lax457868Proofs.NumericGraphProbability
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult

variable {B c n N : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}

lemma initial_mean
    (R : ReadyInput B n A.card n (A.card/(4*c^2)) n n
      (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n) (refinedCutoffK c)
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) G x A)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G (finSetAsSet A))
      (finSetAsSet (activeVertices n R.I.activeB)))
    (hcap : R.I.σ.vars "initialRetryCap" = n)
    (hbudget : n*attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N)
    (hper : attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B initialSamplerRetriesSource
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)).I.σ
      (final ρ) (cost ρ)) :
    (∑ ρ, (cost ρ : ℚ)) ≤
      ((3966*(x.length+1)+266*A.card*(Nat.clog 2 n+1):ℕ):ℚ)*2^N := by
  have hn : n ≤ x.length := by have := R.I.hx.length_eq; omega
  have hm : A.card ≤ n := by simpa using Finset.card_le_card R.I.hA
  have ht : 2*Lax11.GraphEncoding.edgeCount x ≤ x.length := by
    have := R.I.hx.length_eq; omega
  have hQ : 2^Nat.clog 2 n ≤ 2*n := by
    have hnpos : 0 < n := by
      have hp := Finset.card_pos.mpr R.I.hAnonempty
      omega
    by_cases hn1 : n ≤ 1
    · rw [Nat.clog_of_right_le_one hn1]
      simp
      omega
    · have hl : 0 < Nat.clog 2 n :=
        (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by simp; omega)
      have hp := Nat.pow_pred_clog_lt_self (b := 2) (by decide) (by omega : 1<n)
      simp only [Nat.pred_eq_sub_one] at hp
      rw [show Nat.clog 2 n = Nat.clog 2 n - 1 + 1 by omega,pow_succ]
      omega
  have hmass := numeric_initial_badMass_half hG hc A (activeVertices n R.I.activeB)
    R.I.hA (fun b hb => Finset.mem_range.mpr (mem_activeVertices.mp hb).1)
    R.I.hAnonempty hsep
  have hmean := actual_source_mean R n N hcap (by have := R.hnB; omega)
    hbudget hper hmass final cost hrun
  have hcoef := FullInitialAttemptMean.full_mean_coefficient_le
    (r := A.card/(4*c^2)) (m := A.card) (n := n)
    (targetCap := 2*Lax11.GraphEncoding.edgeCount x) (Q := 2^Nat.clog 2 n)
    x.length (Nat.div_le_self _ _) hm hn ht hQ
  have hbound : retryCoefficient n A.card (A.card/(4*c^2))
        (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n)+8 ≤
      3966*(x.length+1)+266*A.card*(Nat.clog 2 n+1) := by
    unfold retryCoefficient fullCoefficient
    nlinarith
  exact hmean.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hbound) (by positivity))


/-- The degree charge of the representatives stored by the accepted retry
source is at most twice one pass over the adjacency lists. -/
lemma initial_representative_mean
    (R : ReadyInput B n A.card n (A.card/(4*c^2)) n n
      (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n) (refinedCutoffK c)
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) G x A)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G (finSetAsSet A))
      (finSetAsSet (activeVertices n R.I.activeB)))
    (hcap : R.I.σ.vars "initialRetryCap" = n)
    (hbudget : n*attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N)
    (hper : attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B initialSamplerRetriesSource
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)).I.σ
      (final ρ) (cost ρ)) :
    (∑ ρ, if (final ρ).vars "initialRetryStatus" = 1 then
      (∑ b ∈ activeVertices n R.I.activeB,
        (Lax11Proofs.CC.deg x (((final ρ).arrs "repB").getD b 0):ℚ)) else 0) ≤
      (2*(x.length+1):ℚ)*2^N := by
  classical
  have hmass := numeric_initial_badMass_half hG hc A (activeVertices n R.I.activeB)
    R.I.hA (fun b hb => Finset.mem_range.mpr (mem_activeVertices.mp hb).1)
    R.I.hAnonempty hsep
  have hm := actual_source_reward_le R n N hcap (by have := R.hnB; omega)
    hbudget hper hmass (fun b => (Lax11Proofs.CC.deg x b:ℚ)) (fun _ => by positivity)
    final cost hrun
  have hd := Lax11Proofs.CC.sum_deg_le (s := activeVertices n R.I.activeB) R.I.hx
    (fun b hb => (mem_activeVertices.mp hb).1)
  have hlen := R.I.hx.length_eq
  have hbound : (∑ b ∈ activeVertices n R.I.activeB, Lax11Proofs.CC.deg x b) ≤
      x.length+1 := by omega
  have hboundQ : (∑ b ∈ activeVertices n R.I.activeB, (Lax11Proofs.CC.deg x b:ℚ)) ≤
      x.length+1 := by exact_mod_cast hbound
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hboundQ (by norm_num)) (by positivity))

lemma preparation_cost_le_input
    (hx : Lax11.GraphEncoding.EncodesGraph x n G) :
    1229*n+987*(2*Lax11.GraphEncoding.edgeCount x)+64*(2^Nat.clog 2 n)+575 ≤
      2344*(x.length+1) := by
  have hlen := hx.length_eq
  have hQ := ReusedOriginal.Construction.DriverSetup.radix_size_lt n
  omega

/-- Compose actual source costs at the measured initial-retry stopping
prefix. The continuation premise will be supplied by the packed repair mean. -/
lemma actual_mean_of_continuation
    (R : ReadyInput B n A.card n (A.card/(4*c^2)) n n
      (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n) (refinedCutoffK c)
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) G x A)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G (finSetAsSet A))
      (finSetAsSet (activeVertices n R.I.activeB)))
    (hcap : R.I.σ.vars "initialRetryCap" = n)
    (hbudget : n*attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N)
    (hper : attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N)
    (C : ∀ ρ : Tape N, Cut
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)) n)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B completeSamplerSource
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)).I.σ
      (final ρ) (cost ρ))
    (hafter : ∀ ρ : Tape N, ∀ f : Tape (N-(C ρ).used) → Env,
      ∀ d : Tape (N-(C ρ).used) → ℕ,
      (∀ η, BigStepB B afterInitial
        {(C ρ).final with inp := (List.ofFn η).map Bool.toNat ++ R.I.rest}
        (f η) (d η)) →
      (∑ η, (d η:ℚ)) ≤
        (2839*(x.length+1)+435*A.card*(Nat.clog 2 n+1)+
          90*acceptedRepReward n R.I.activeB (fun b => (Lax11Proofs.CC.deg x b:ℚ))
            (C ρ).final)*2^(N-(C ρ).used)) :
    (∑ ρ, (cost ρ:ℚ)) ≤
      ((6985*(x.length+1)+701*A.card*(Nat.clog 2 n+1):ℕ):ℚ)*2^N := by
  classical
  have hd (ρ : Tape N) := actual_decompose
    (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hper)) (C ρ) (hrun ρ)
  choose initialCost tailCost hi ht hcost using hd
  have hm := initial_mean R hG hc hsep hcap hbudget hper
    (fun ρ => (C ρ).final) initialCost hi
  have hw := initial_representative_mean R hG hc hsep hcap hbudget hper
    (fun ρ => (C ρ).final) initialCost hi
  let reward (ρ : Tape N) : ℚ := acceptedRepReward n R.I.activeB
    (fun b => (Lax11Proofs.CC.deg x b:ℚ)) (C ρ).final
  let Y (ρ : Tape N) : ℚ := 2839*(x.length+1)+435*A.card*(Nat.clog 2 n+1)+90*reward ρ
  have hu (ρ : Tape N) : (C ρ).used ≤ N := (C ρ).used_le.trans hbudget
  have hcausal := cut_causal R n N hper hbudget C
  have hY (ρ η : Tape N) (hp : (List.ofFn ρ).take (C ρ).used =
      (List.ofFn η).take (C ρ).used) : Y η = Y ρ := by
    obtain ⟨_,he⟩ := hcausal ρ η hp
    simp only [Y,reward,acceptedRepReward,he]
  have hcond (ρ : Tape N) :
      (∑ η : Tape (N-(C ρ).used),
        (tailCost ((splitEquiv (hu ρ)).symm ((splitEquiv (hu ρ) ρ).1,η)):ℚ)) ≤
        Y ρ*2^(N-(C ρ).used) := by
    let f (η : Tape (N-(C ρ).used)) :=
      (splitEquiv (hu ρ)).symm ((splitEquiv (hu ρ) ρ).1,η)
    apply hafter ρ (fun η => final (f η)) (fun η => tailCost (f η))
    intro η
    have hp : (List.ofFn ρ).take (C ρ).used =
        (List.ofFn (f η)).take (C ρ).used := by
      rw [StoppedPrefixAveraging.prefix_of_split (hu ρ),
        StoppedPrefixAveraging.prefix_of_split (hu ρ)]
      simp [f]
    have he := (hcausal ρ (f η) hp).2
    have hdrop : (List.ofFn (f η)).drop (C ρ).used = List.ofFn η := by
      rw [StoppedPrefixAveraging.boolTape_split (hu ρ) (f η)]
      simp [f]
    have h := ht (f η)
    simpa only [he,hdrop] using h
  have htm := StoppedPrefixAveraging.sum_le_of_stopped_prefix
    (fun ρ => (C ρ).used) hu (fun ρ η hp => (hcausal ρ η hp).1)
    (fun ρ => (tailCost ρ:ℚ)) Y hY hcond
  have hsum : (∑ ρ, (cost ρ:ℚ)) =
      (∑ ρ, (initialCost ρ:ℚ))+(∑ ρ, (tailCost ρ:ℚ)) := by
    simp only [hcost,Nat.cast_add,Finset.sum_add_distrib]
  have hy : (∑ ρ, Y ρ) =
      (2839*(x.length+1)+435*A.card*(Nat.clog 2 n+1):ℚ)*2^N+
      90*(∑ ρ, reward ρ) := by
    simp only [Y,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      card_tape,nsmul_eq_mul,← Finset.mul_sum]
    push_cast
    ring
  change (∑ ρ, reward ρ) ≤ _ at hw
  rw [hy] at htm
  rw [hsum]
  push_cast at hm ⊢
  nlinarith only [hm,htm,hw]

set_option maxRecDepth 2048 in
lemma after_initial_mean
    (R : ReadyInput B n A.card n (A.card/(4*c^2)) n n
      (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n) (refinedCutoffK c)
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) G x A)
    (S : RuntimeInput R (64*Nat.clog 2 c) n)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G (finSetAsSet A))
      (finSetAsSet (activeVertices n R.I.activeB)))
    {attemptCap : ℕ} (C : Cut R attemptCap)
    (hbudget : (A.card/(4*c^2*(64*Nat.clog 2 c+1)))*
      (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ N)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B afterInitial
      {C.final with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest}
      (final ρ) (cost ρ)) :
    (∑ ρ, (cost ρ:ℚ)) ≤
      (2839*(x.length+1)+435*A.card*(Nat.clog 2 n+1)+
        90*acceptedRepReward n R.I.activeB (fun b => (Lax11Proofs.CC.deg x b:ℚ))
          C.final)*2^N := by
  classical
  by_cases hs : C.final.vars "initialRetryStatus" = 1
  · obtain ⟨choice,q,L,repairCost,hr,hcost,hrest,hcap,hrep,hphysical⟩ :=
      accepted_tail_family R S C hs final cost hrun
    have hC : activeVertices n R.I.activeB ⊆ Finset.range n :=
      fun b hb => Finset.mem_range.mpr (mem_activeVertices.mp hb).1
    have hhalf := NumericRepairProbability.accepted_loop_half hG hc choice L hC hsep hrep
    have hseparate := NumericRepairProbability.accepted_loop_separate choice L hC hsep
    have hsize := RefinedRepairCharges.accepted_exception_budget A.card c
      (64*Nat.clog 2 c) (choice.exceptions (refinedCutoffK c)).card (by omega) hcap
    have hcharge := RefinedRepairCharges.repair_mean_charge_le_input L hsize hseparate
    have hm := ExceptionLoopMean.packed_mean L N
      (hc.trans (refinedCutoffK_ge_c c hc))
      ((Nat.mul_le_mul_right _ hcap).trans hbudget) hhalf final repairCost hr
    have hrepSum : (∑ b ∈ choice.exceptions (refinedCutoffK c), Lax11Proofs.CC.deg x (L.rep b)) ≤
        ∑ b ∈ activeVertices n R.I.activeB,
          Lax11Proofs.CC.deg x ((C.final.arrs "repB").getD b 0) := by
      calc
        _ = ∑ b ∈ choice.exceptions (refinedCutoffK c),
            Lax11Proofs.CC.deg x ((C.final.arrs "repB").getD b 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hphysical b (mem_activeVertices.mp (Finset.mem_filter.mp hb).1).1]
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hprep := preparation_cost_le_input R.I.hx
    have hsum := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) =>
      (show (cost ρ:ℚ) ≤ repairCost ρ+(1229*n+987*(2*Lax11.GraphEncoding.edgeCount x)+
        64*(2^Nat.clog 2 n)+575:ℕ) by exact_mod_cast hcost ρ))
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      card_tape,nsmul_eq_mul] at hsum
    have hb : ((23+20*n+∑ b ∈ choice.exceptions (refinedCutoffK c),
        ExceptionLoopMean.meanStepCharge L b)+
        (1229*n+987*(2*Lax11.GraphEncoding.edgeCount x)+64*(2^Nat.clog 2 n)+575):ℕ) ≤
        2839*(x.length+1)+435*A.card*(Nat.clog 2 n+1)+
        90*(∑ b ∈ activeVertices n R.I.activeB,
          Lax11Proofs.CC.deg x ((C.final.arrs "repB").getD b 0)) := by
      change 23+20*n+∑ b ∈ choice.exceptions (refinedCutoffK c),
        ExceptionLoopMean.meanStepCharge L b ≤ _ at hcharge
      omega
    have hbQ : (((23+20*n+∑ b ∈ choice.exceptions (refinedCutoffK c),
        ExceptionLoopMean.meanStepCharge L b)+
        (1229*n+987*(2*Lax11.GraphEncoding.edgeCount x)+64*(2^Nat.clog 2 n)+575):ℕ):ℚ) ≤
        2839*(x.length+1)+435*A.card*(Nat.clog 2 n+1)+
        90*(∑ b ∈ activeVertices n R.I.activeB,
          (Lax11Proofs.CC.deg x ((C.final.arrs "repB").getD b 0):ℚ)) := by exact_mod_cast hb
    simp only [acceptedRepReward,hs,if_true]
    push_cast at hsum hm hbQ
    nlinarith only [hsum,hm,mul_le_mul_of_nonneg_right hbQ (show (0:ℚ) ≤ 2^N by positivity)]
  · have hz (ρ : Tape N) : cost ρ = 5 := actual_nonaccepted_tail
        (σ := {C.final with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest}) hs (hrun ρ)
    simp only [hz,acceptedRepReward,hs,if_false,mul_zero,add_zero,
      Finset.sum_const,Finset.card_univ,card_tape,nsmul_eq_mul]
    push_cast
    rw [mul_comm (2^N:ℚ) 5]
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hz : (0:ℚ) ≤ 435*(A.card:ℚ)*((Nat.clog 2 n:ℚ)+1) := by positivity
    have hx0 : (0:ℚ) ≤ (x.length:ℚ) := Nat.cast_nonneg _
    nlinarith only [hz,hx0]

lemma actual_mean
    (R : ReadyInput B n A.card n (A.card/(4*c^2)) n n
      (2*Lax11.GraphEncoding.edgeCount x) (2^Nat.clog 2 n) (refinedCutoffK c)
      (A.card/(4*c^2*(64*Nat.clog 2 c+1))) G x A)
    (S : RuntimeInput R (64*Nat.clog 2 c) n)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    (hsep : Set.InjOn
      (ReusedOriginal.Construction.NeighborhoodComplexity.neighborhoodTrace G (finSetAsSet A))
      (finSetAsSet (activeVertices n R.I.activeB)))
    (hcap : R.I.σ.vars "initialRetryCap" = n)
    (hbudget : n*attemptBitBudget n A.card (A.card/(4*c^2)) n+
      (A.card/(4*c^2*(64*Nat.clog 2 c+1)))*
        (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ N)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B completeSamplerSource
      {R.I.σ with inp := (List.ofFn ρ).map Bool.toNat ++ R.I.rest}
      (final ρ) (cost ρ)) :
    (∑ ρ, (cost ρ:ℚ)) ≤
      ((6985*(x.length+1)+701*A.card*(Nat.clog 2 n+1):ℕ):ℚ)*2^N := by
  classical
  have hn : 1 ≤ n := by
    obtain ⟨a,ha⟩ := R.I.hAnonempty
    have := Finset.mem_range.mp (R.I.hA ha)
    omega
  have hi : n*attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N := by omega
  have hp : attemptBitBudget n A.card (A.card/(4*c^2)) n ≤ N :=
    (Nat.le_mul_of_pos_left _ hn).trans hi
  let R' (ρ : Tape N) := R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hp)
  have hcuts (ρ : Tape N) : Nonempty (Cut (R' ρ) n) :=
    cut_exists (R' ρ) n hcap (by have := R.hnB; omega)
      (by simpa only [R',ReadyInput.reinput_bits,List.length_ofFn] using hi)
  let C (ρ : Tape N) := Classical.choice (hcuts ρ)
  apply actual_mean_of_continuation R hG hc hsep hcap hi hp C final cost hrun
  intro ρ f d hd
  have hused := (C ρ).used_le
  have hb : (A.card/(4*c^2*(64*Nat.clog 2 c+1)))*
      (n*((64*Nat.clog 2 c)*n*Nat.clog 2 n)) ≤ N-(C ρ).used := by omega
  exact after_initial_mean (R' ρ)
    (runtime_reinput R S (List.ofFn ρ) (by simpa [attemptBitBudget] using hp))
    hG hc hsep (C ρ) hb f d hd

end Lax457868Proofs.RefinedSamplerMean
