import Lax457868Proofs.InitialDrawMean
import Lax457868Proofs.RepresentativeSourceMean
import Lax457868Proofs.InitialFlatLaw

/-! Source-level composition of the initial draw and representative means. -/
namespace Lax457868Proofs.InitialAttemptMean
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.InitialSamplerAttempt
open Lax457868Proofs.InitialDrawSampleSource
open Lax457868Proofs.FullSamplePartition
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.SequentialDraws
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.PartitionLoopSource
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.StoppedPrefixAveraging

variable {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}

/-- The actual state after the draw, and the ready representative command
when the draw succeeds. The intervening partition reads no random bits. -/
structure Cut (I : Input B n m domainCap r t bufferCap targetCap Q G x A) where
  drawFinal : Env
  values : List (Fin m)
  used : ℕ
  failed : Bool
  trace : ∃ tape : BitTape m (r*t), ∃ tail,
    I.bits = tapeBits tape ++ tail ∧
      DrawTrace m I.hmPos t r (List.ofFn tape) values used failed
  drawRun : Run B initialDrawSampleSource (I.σ.setVar "attemptAccepted" 0) drawFinal
    (initialDrawSampleCost n m used (values.length + if failed then 1 else 0)
      values.length failed)
  drawInput : drawFinal.inp = (I.bits.drop (used*Nat.clog 2 m)).map Bool.toNat ++ I.rest
  drawFlag : drawFinal.vars "batchFailed" = (if failed then 1 else 0)
  post : failed = false → ∃ q, ∃ RI : RepresentativeInput B n q Q t,
    RI.bits = I.bits.drop (used*Nat.clog 2 m) ∧ RI.rest = I.rest ∧
    Run B fullSamplePartition drawFinal RI.σ (384*n+324*targetCap+70)

lemma cut_exists (I : Input B n m domainCap r t bufferCap targetCap Q G x A) :
    Nonempty (Cut I) := by
  obtain ⟨σd,σf,tape,tail,values,used,failed,stageCost,hbits,htrace,hfull,
    haccept,hn,hq,hbatch,harr,hvar,hfail,hpass,hdraw,hinp,hflag⟩ :=
    initialSamplerAttempt_run_bits I
  refine ⟨⟨σd,values,used,failed,⟨tape,tail,hbits,htrace⟩,hdraw,hinp,hflag,?_⟩⟩
  intro hf
  obtain ⟨W,ord,sc,σp,q,label,size,xs,sorted,rv,ru,rc,rf,hW,hWA,hWcard,
    hlen,hprefix,hpart,hsizes,hoccupied,hclasses,hrep,hnf,hqf,hscf,hcls,hsize,
    hord,hnodup,hset,hctr,hru,hrf,hrfail,hsf,hinpf,hrpass,hcost,hcert⟩ := hpass hf
  obtain ⟨_,_,_,_,_,_,_,_,RI,hRI,hRIbits,hRIrest⟩ := hcert
  refine ⟨q,RI,hRIbits,hRIrest,?_⟩
  rw [hRI]
  apply hpart.mono
  have hrange : ∀ i < sc, ord i < n := PrefixEnumerates.entry_lt hprefix
    (fun v hv => Finset.mem_range.mp (I.hA (hWA hv)))
  have hsc : sc ≤ n := by
    let f : Fin sc → Fin n := fun i => ⟨ord i,hrange i i.isLt⟩
    have hinj : Function.Injective f := by
      intro i j he
      apply Fin.ext
      exact hprefix.injective_on_prefix i i.isLt j j.isLt (congrArg Fin.val he)
    simpa using Fintype.card_le_of_injective f hinj
  have hwork := refinementWork_le_edgeCount_add I.hx hrange hprefix.injective_on_prefix
  rw [← I.htargetCapEq] at hwork
  simp only [fullSamplePartitionCost, Cond.size, Expr.size]
  omega

def afterDraw : Com := .ite (.eq (.var "batchFailed") (.lit 0))
  (fullSamplePartition.seq initialRepresentativeSelection) .skip

lemma post_mean (I : Input B n m domainCap r t bufferCap targetCap Q G x A)
    (C : Cut I) :
    ∃ (final : Tape (I.bits.length-C.used*Nat.clog 2 m) → Env)
      (cost : Tape (I.bits.length-C.used*Nat.clog 2 m) → ℕ),
      (∀ ρ, Run B afterDraw
        {C.drawFinal with inp := (List.ofFn ρ).map Bool.toNat ++ I.rest}
        (final ρ) (cost ρ)) ∧
      (∑ ρ, cost ρ) ≤ (735*n+324*targetCap+64*Q+171)*
        2^(I.bits.length-C.used*Nat.clog 2 m) := by
  classical
  have hguard (bits : List ℕ) :
      (Cond.eq (.var "batchFailed") (.lit 0)).evalB B
        {C.drawFinal with inp := bits} = some (!C.failed) := by
    cases hf : C.failed <;>
      simp [Cond.evalB, Expr.evalB, fit, C.drawFlag, hf, I.honeB,
        Nat.zero_lt_of_lt I.honeB]
  cases hf : C.failed with
  | true =>
    refine ⟨(fun ρ => {C.drawFinal with inp := (List.ofFn ρ).map Bool.toNat ++ I.rest}),
      (fun _ => 5), ?_, ?_⟩
    · intro ρ
      have hg : (Cond.eq (.var "batchFailed") (.lit 0)).evalB B
          {C.drawFinal with inp := (List.ofFn ρ).map Bool.toNat ++ I.rest} = some false := by
        simpa only [hf, Bool.not_true] using hguard ((List.ofFn ρ).map Bool.toNat ++ I.rest)
      have hr := Run.ite_false (c := fullSamplePartition.seq initialRepresentativeSelection) hg (Run.skip (B := B))
      simpa [afterDraw, Cond.size, Expr.size] using hr
    · simp only [Finset.sum_const, Finset.card_univ, card_tape, nsmul_eq_mul]
      change 2^(I.bits.length-C.used*Nat.clog 2 m)*5 ≤ _
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right
        (2^(I.bits.length-C.used*Nat.clog 2 m))
        (show 5 ≤ 735*n+324*targetCap+64*Q+171 by omega)
  | false =>
    obtain ⟨q,RI,hbits,hrest,hpart⟩ := C.post hf
    have hb : bitBudget RI.size t 0 q ≤ I.bits.length-C.used*Nat.clog 2 m := by
      simpa [hbits] using RI.hbudget
    obtain ⟨final,cost,hrun,hmean⟩ :=
      RepresentativeSourceMean.representative_source_mean RI hb
    refine ⟨final,(fun ρ => 4+(384*n+324*targetCap+70)+cost ρ),?_,?_⟩
    · intro ρ
      let tail := (List.ofFn ρ).map Bool.toNat ++ I.rest
      have hp : Run B fullSamplePartition {C.drawFinal with inp := tail}
          {RI.σ with inp := tail} (384*n+324*targetCap+70) := by
        simpa only [List.nil_append] using run_replace_consumed_suffix hpart []
          (by simpa using (hpart.frame_inp (by decide)).symm) tail
      have hs := hp.seq (by simpa only [hrest] using hrun ρ)
      have hg : (Cond.eq (.var "batchFailed") (.lit 0)).evalB B
          {C.drawFinal with inp := tail} = some true := by
        simpa only [hf, Bool.not_false] using hguard tail
      have hh := Run.ite_true (d := .skip) hg hs
      simpa [afterDraw, tail, Cond.size, Expr.size, Nat.add_assoc] using hh
    · simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        card_tape, nsmul_eq_mul]
      nlinarith

lemma actual_decompose (I : Input B n m domainCap r t bufferCap targetCap Q G x A)
    (C : Cut I) {τ : Env} {k : ℕ}
    (ha : BigStepB B initialSamplerAttempt I.σ τ k) :
    ∃ j, BigStepB B afterDraw C.drawFinal τ j ∧
      k ≤ 2 + initialDrawSampleCost n m C.used
        (C.values.length + if C.failed then 1 else 0) C.values.length C.failed + j := by
  change BigStepB B ((Com.assign "attemptAccepted" (.lit 0)).seq
    (initialDrawSampleSource.seq afterDraw)) I.σ τ k at ha
  cases ha with
  | seq hinit htail =>
    cases hinit with
    | assign heval =>
      rename_i kTail v
      have hv : v = 0 := by
        simpa [Expr.evalB, fit, Nat.zero_lt_of_lt I.honeB] using heval.symm
      subst_vars
      cases htail with
      | seq hdraw hpost =>
        obtain ⟨kd,hkd,hd⟩ := C.drawRun
        have heq := BigStep.unique hdraw.bigStep hd.bigStep
        rcases heq with ⟨heq,hk⟩
        subst_vars
        exact ⟨_,hpost,by simp [Expr.size]; omega⟩

/-- Expected actual machine cost of one complete initial selection,
including the sample-dependent partition and representatives. -/
lemma actual_initial_mean (I : Input B n m domainCap r t bufferCap targetCap Q G x A)
    (N : ℕ) (hb : r*t*Nat.clog 2 m+n*t*Nat.clog 2 n ≤ N)
    (final : Tape N → Env) (cost : Tape N → ℕ)
    (hrun : ∀ ρ, BigStepB B initialSamplerAttempt
      {I.σ with inp := (List.ofFn ρ).map Bool.toNat ++ I.rest} (final ρ) (cost ρ)) :
    (∑ ρ, cost ρ) ≤
      (r*(42*Nat.clog 2 m+133)+12*Nat.clog 2 m+766*n+
        324*targetCap+64*Q+230)*2^N := by
  classical
  let J (ρ : Tape N) := InitialFlatLaw.reinputInitialAttempt I (List.ofFn ρ)
    (by simpa using hb)
  let C (ρ : Tape N) := Classical.choice (cut_exists (J ρ))
  let used (ρ : Tape N) := (C ρ).used * Nat.clog 2 m
  let drawCost (ρ : Tape N) := initialDrawSampleCost n m (C ρ).used
    ((C ρ).values.length+if (C ρ).failed then 1 else 0) (C ρ).values.length (C ρ).failed
  have hu (ρ : Tape N) : used ρ ≤ N := by
    obtain ⟨tape,tail,hbits,htr⟩ := (C ρ).trace
    have hused := (DrawTrace.used_and_calls m (J ρ).hmPos t htr).1
    simp only [List.length_ofFn] at hused
    have hh := Nat.mul_le_mul_right (Nat.clog 2 m) hused
    dsimp [used]
    omega
  have hs (ρ τ : Tape N)
      (hp : (List.ofFn ρ).take (used ρ) = (List.ofFn τ).take (used ρ)) :
      used τ = used ρ ∧ (C τ).drawFinal =
        {(C ρ).drawFinal with inp := (List.ofFn τ).drop (used ρ) |>.map Bool.toNat |>.append I.rest} := by
    exact bool_run_same_prefix (σ := I.σ.setVar "attemptAccepted" 0)
      (List.ofFn ρ) (List.ofFn τ) I.rest
      (C ρ).drawRun (C τ).drawRun (C ρ).drawInput (C τ).drawInput
      (by simpa using hu ρ) (by simpa using hu τ) hp
  have hdec (ρ : Tape N) : ∃ kpost,
      BigStepB B afterDraw (C ρ).drawFinal (final ρ) kpost ∧
      cost ρ ≤ 2+drawCost ρ+kpost := actual_decompose (J ρ) (C ρ) (hrun ρ)
  choose postCost hpost hcost using hdec
  have hpostmean : (∑ ρ : Tape N, (postCost ρ : ℚ)) ≤
      (735*n+324*targetCap+64*Q+171 : ℕ)* (2^N : ℚ) := by
    have hm := sum_le_of_stopped_prefix used hu (fun ρ τ hp => (hs ρ τ hp).1)
      (fun ρ => (postCost ρ : ℚ))
      (fun _ => ((735*n+324*targetCap+64*Q+171 : ℕ) : ℚ))
      (by intros; rfl) (by
        intro ρ
        have hpm := post_mean (J ρ) (C ρ)
        have hlen : (J ρ).bits.length = N := by simp [J, InitialFlatLaw.reinputInitialAttempt]
        rw [hlen] at hpm
        obtain ⟨τs,ks,hrs,hms⟩ := hpm
        have hp (tail : Tape (N-used ρ)) :
            let τ := (splitEquiv (hu ρ)).symm ((splitEquiv (hu ρ) ρ).1,tail)
            postCost τ ≤ ks tail := by
          dsimp only
          let τ := (splitEquiv (hu ρ)).symm ((splitEquiv (hu ρ) ρ).1,tail)
          have hpre : (List.ofFn ρ).take (used ρ) = (List.ofFn τ).take (used ρ) := by
            rw [prefix_of_split (hu ρ), prefix_of_split (hu ρ)]
            simp [τ]
          have hstate := (hs ρ τ hpre).2
          have hdrop : (List.ofFn τ).drop (used ρ) = List.ofFn tail := by
            rw [boolTape_split (hu ρ) τ]
            simp [τ]
          rw [hdrop] at hstate
          have hr : Run B afterDraw (C τ).drawFinal (τs tail) (ks tail) := by
            rw [hstate]
            exact hrs tail
          obtain ⟨kr,hkr,hr⟩ := hr
          have heq := BigStep.unique (hpost τ).bigStep hr.bigStep
          change postCost τ ≤ ks tail
          omega
        have hsum : (∑ tail : Tape (N-used ρ),
            postCost ((splitEquiv (hu ρ)).symm ((splitEquiv (hu ρ) ρ).1,tail))) ≤
            (735*n+324*targetCap+64*Q+171)*2^(N-used ρ) := by
          exact (Finset.sum_le_sum (fun tail _ => hp tail)).trans hms
        exact_mod_cast hsum)
    simpa only [Finset.sum_const, Finset.card_univ, card_tape, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hm
  have hdraw := InitialDrawMean.sum_draw_cost_le n m r t N I.hmPos (by omega)
    (fun ρ => (C ρ).values) (fun ρ => (C ρ).used) (fun ρ => (C ρ).failed)
    (fun ρ => (C ρ).trace)
  have hpostNat : (∑ ρ, postCost ρ) ≤ (735*n+324*targetCap+64*Q+171)*2^N := by
    exact_mod_cast hpostmean
  have hsum := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => hcost ρ)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    card_tape, nsmul_eq_mul] at hsum
  change (∑ ρ, drawCost ρ) ≤ _ at hdraw
  nlinarith

end Lax457868Proofs.InitialAttemptMean



