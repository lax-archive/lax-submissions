import Lax457868Proofs.ClassTraceMean
import Lax457868Proofs.InitialSamplerRetriesSource
import Lax457868Proofs.RepresentativeSourceMean
import Lax457868Proofs.InitialAttemptMean

/-! Failure counting for the actual adaptive flat source selectors. The next
request starts at the unread suffix of the previous capped request, so the
count is taken through a stopped prefix rather than reserved independent
blocks. -/

namespace Lax457868Proofs.InitialAbortProbability

open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.ClassTraceMean
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.FlatTraceLaw
open Lax457868Proofs.StoppingPrefix
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.StoppedPrefixAveraging
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.FullInitialAttempt
open Lax457868Proofs.InitialSamplerAttempt
open Lax457868Proofs.RepresentativeSourceMean
open Lax457868Proofs.InitialAttemptMean
open Lax457868Proofs.FullSamplePartition
open Lax457868Proofs.InitialFlatLaw
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open scoped BigOperators

lemma ClassTrace.append_bits {size : ℕ → ℕ} {t : ℕ}
    {start : ℕ → ℕ} {d r : ℕ} {bits : List Bool}
    {values : List ℕ} {used charge : ℕ} {failed : Bool}
    (h : ClassTrace size t start d r bits values used charge failed)
    (extra : List Bool) :
    ClassTrace size t start d r (bits ++ extra) values used charge failed := by
  induction h with
  | done d bits => exact ClassTrace.done d (bits ++ extra)
  | failed tape tail u hm hsel =>
    simpa [List.append_assoc] using
      (ClassTrace.failed (size := size) (t := t) (start := start)
        tape (tail ++ extra) u hm hsel)
  | accepted tape tail i u hm hsel hnext ih =>
    have ih' := ih
    rw [List.append_assoc] at ih'
    simpa [List.append_assoc, List.drop_append] using
      (ClassTrace.accepted (size := size) (t := t) (start := start)
        tape (tail ++ extra) i u hm hsel ih')

lemma constant_bitBudget (m t d r : ℕ) :
    bitBudget (fun _ => m) t d r = r * t * Nat.clog 2 m := by
  induction r generalizing d with
  | zero => simp [bitBudget]
  | succ r ih => simp [bitBudget, ih, Nat.succ_mul, Nat.add_mul, Nat.mul_assoc, Nat.add_comm]

noncomputable def failedFlag (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r : ℕ) (bits : List Bool) : Bool := by
  classical
  exact if h : ∃ f v u c, ClassTrace size t start d r bits v u c f then
    Classical.choose h else false

lemma failedFlag_eq {size : ℕ → ℕ} {t : ℕ} {start : ℕ → ℕ}
    {d r : ℕ} {bits : List Bool} {v : List ℕ} {u c : ℕ}
    {f : Bool} (h : ClassTrace size t start d r bits v u c f) :
    failedFlag size t start d r bits = f := by
  classical
  have he : ∃ f v u c, ClassTrace size t start d r bits v u c f :=
    ⟨f, v, u, c, h⟩
  simp only [failedFlag, dif_pos he]
  obtain ⟨v', u', c', hh⟩ := Classical.choose_spec he
  exact (classTrace_unique size t start hh h rfl).2.2.2

lemma failedFlag_spec (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    (d r : ℕ) (bits : List Bool)
    (hp : ∀ j, d ≤ j → j < d + r → 0 < size j)
    (hb : bitBudget size t d r ≤ bits.length) :
    ∃ v u c, ClassTrace size t start d r bits v u c
      (failedFlag size t start d r bits) := by
  obtain ⟨v, u, c, f, hh⟩ := trace_exists size t start d r bits hp hb
  exact ⟨v, u, c, by rwa [failedFlag_eq hh]⟩

lemma failedFlag_step_or (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r : ℕ)
    (a : BitTape (size d) t) (tail : List Bool)
    (hm : 0 < size d)
    (hp : ∀ j, d + 1 ≤ j → j < d + 1 + r → 0 < size j)
    (hb : bitBudget size t (d + 1) r ≤ tail.length)
    (hfail : failedFlag size t start d (r + 1) (tapeBits a ++ tail) = true) :
    (selectBitIndexWithCount (size d) hm t a).1 = none ∨
      failedFlag size t start (d + 1) r
        ((tapeBits a ++ tail).drop
          ((selectBitIndexWithCount (size d) hm t a).2 *
            Nat.clog 2 (size d))) = true := by
  rcases hs : selectBitIndexWithCount (size d) hm t a with ⟨o, u⟩
  cases o with
  | none => exact Or.inl rfl
  | some i =>
    right
    have hu : u ≤ t := by
      have hh := firstDecodedWithCount_le_length
        ((List.ofFn a).map (decodeBitIndex (size d) hm))
      change (selectBitIndexWithCount (size d) hm t a).2 ≤ _ at hh
      simpa [hs] using hh
    have hdrop : (tapeBits a ++ tail).drop (u * Nat.clog 2 (size d)) =
        (tapeBits a).drop (u * Nat.clog 2 (size d)) ++ tail := by
      rw [List.drop_append]
      have hle := Nat.mul_le_mul_right (Nat.clog 2 (size d)) hu
      simp [tapeBits_length, Nat.sub_eq_zero_of_le hle]
    obtain ⟨v, used, cost, hnext⟩ :=
      failedFlag_spec size t start (d + 1) r
        ((tapeBits a).drop (u * Nat.clog 2 (size d)) ++ tail)
        hp (by simp only [List.length_append]; omega)
    have hwhole := ClassTrace.accepted a tail i u hm hs hnext
    have heq := failedFlag_eq hwhole
    simpa only [hs, hdrop] using heq.symm.trans hfail

/-- A failed first capped selector occupies at most a `2⁻ᵗ` fraction of
every finite flat tape, with the unused suffix counted freely. -/
lemma first_failure_count {N : ℕ} (m t : ℕ) (hm : 0 < m)
    (h : t * Nat.clog 2 m ≤ N) :
    2 ^ t * ((Finset.univ.filter fun ρ : Tape N =>
      (selectBitIndexWithCount m hm t (firstTape m t h ρ)).1 = none).card) ≤
      2 ^ N := by
  classical
  let E := (splitEquiv h).trans
    (Equiv.prodCongr (LocalFlatLaw.blockTapeBitsEquiv t (Nat.clog 2 m)).symm
      (Equiv.refl (Tape (N - t * Nat.clog 2 m))))
  have hnone (ρ : Tape N) :
      (selectBitIndexWithCount m hm t (firstTape m t h ρ)).1 = none ↔
        (E ρ).1 ∈ allRejectedBitTapes m t := by
    have he : (E ρ).1 = firstTape m t h ρ := rfl
    rw [he, selectBitIndexWithCount_eq]
    exact selectBitIndex_eq_none_iff m hm t _
  have hcount : ((Finset.univ.filter fun ρ : Tape N =>
      (selectBitIndexWithCount m hm t (firstTape m t h ρ)).1 = none).card) =
      (allRejectedBitTapes m t).card * 2 ^ (N - t * Nat.clog 2 m) := by
    rw [Finset.card_filter]
    calc
      (∑ ρ : Tape N,
        if (selectBitIndexWithCount m hm t (firstTape m t h ρ)).1 = none
          then 1 else 0) =
          ∑ pair : BitTape m t × Tape (N - t * Nat.clog 2 m),
            if pair.1 ∈ allRejectedBitTapes m t then 1 else 0 := by
              apply Fintype.sum_equiv E
              intro ρ
              simp only [hnone]
      _ = (allRejectedBitTapes m t).card *
          2 ^ (N - t * Nat.clog 2 m) := by
            rw [Fintype.sum_prod_type]
            calc
              _ = ∑ a : BitTape m t,
                    if a ∈ allRejectedBitTapes m t then
                      2 ^ (N - t * Nat.clog 2 m) else 0 := by
                    apply Finset.sum_congr rfl
                    intro a _
                    split_ifs <;> simp
              _ = _ := by simp
  have htail := failure_tail_bound m hm t
  have hcard : Fintype.card (BitTape m t) *
      2 ^ (N - t * Nat.clog 2 m) = 2 ^ N := by
    have hc := Fintype.card_congr E
    simpa only [Fintype.card_prod, card_tape] using hc.symm
  rw [hcount]
  nlinarith [Nat.mul_le_mul_right (2 ^ (N - t * Nat.clog 2 m)) htail]

/-- Up to `r` adaptive capped selectors fail with total mass at most
`r·2⁻ᵗ`. This applies to the constant-size initial draw stream and to the
variable-size representative stream, including a zero-width size-one class. -/
lemma class_failure_count_bound (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (r : ℕ) : ∀ d N,
    (∀ j, d ≤ j → j < d + r → 0 < size j) →
    bitBudget size t d r ≤ N →
    2 ^ t * ((Finset.univ.filter fun ρ : Tape N =>
      failedFlag size t start d r (List.ofFn ρ) = true).card) ≤
      r * 2 ^ N := by
  classical
  induction r with
  | zero =>
    intro d N hp hb
    have hf (ρ : Tape N) :
        failedFlag size t start d 0 (List.ofFn ρ) = false :=
      failedFlag_eq (ClassTrace.done d (List.ofFn ρ))
    simp [hf]
  | succ r ih =>
    intro d N hp hb
    have hm : 0 < size d := hp d (by omega) (by omega)
    have hhead : t * Nat.clog 2 (size d) ≤ N := by
      simp only [bitBudget] at hb
      omega
    let used (ρ : Tape N) :=
      (selectBitIndexWithCount (size d) hm t
        (firstTape (size d) t hhead ρ)).2 * Nat.clog 2 (size d)
    have hu (ρ : Tape N) : used ρ ≤ t * Nat.clog 2 (size d) :=
      Nat.mul_le_mul_right _ (firstTape_used_le (size d) t hm hhead ρ)
    have huN (ρ : Tape N) : used ρ ≤ N := (hu ρ).trans hhead
    have hc (ρ τ : Tape N) (he : (List.ofFn ρ).take (used ρ) =
        (List.ofFn τ).take (used ρ)) : used τ = used ρ := by
      exact congrArg (fun z => z.2 * Nat.clog 2 (size d))
        (firstTape_causal (size d) t hm hhead ρ τ he)
    let tailFailed (ρ : Tape N) : Prop :=
      failedFlag size t start (d + 1) r
        ((List.ofFn ρ).drop (used ρ)) = true
    have htailCount : 2 ^ t *
        ((Finset.univ.filter tailFailed).card) ≤ r * 2 ^ N := by
      let X (ρ : Tape N) : ℚ := if tailFailed ρ then 1 else 0
      let Y (_ : Tape N) : ℚ := (r : ℚ) / 2 ^ t
      have hmean := sum_le_of_stopped_prefix used huN hc X Y
        (by intros; rfl) (by
          intro ρ
          have hx (tail : Tape (N - used ρ)) :
              X ((splitEquiv (huN ρ)).symm
                ((splitEquiv (huN ρ) ρ).1, tail)) =
                if failedFlag size t start (d + 1) r
                    (List.ofFn tail) = true then 1 else 0 := by
            let τ := (splitEquiv (huN ρ)).symm
              ((splitEquiv (huN ρ) ρ).1, tail)
            have hpre : (List.ofFn ρ).take (used ρ) =
                (List.ofFn τ).take (used ρ) := by
              rw [prefix_of_split (huN ρ), prefix_of_split (huN ρ)]
              simp [τ]
            have he := hc ρ τ hpre
            dsimp [X, tailFailed]
            rw [he, boolTape_split (huN ρ) τ]
            simp [τ]
          simp_rw [hx]
          have hbound : bitBudget size t (d + 1) r ≤ N - used ρ := by
            simp only [bitBudget] at hb
            have hh := hu ρ
            omega
          have hih := ih (d + 1) (N - used ρ)
            (fun j hj hjr => hp j (by omega) (by omega)) hbound
          have hsum : (∑ tail : Tape (N - used ρ),
              if failedFlag size t start (d + 1) r
                  (List.ofFn tail) = true then (1 : ℚ) else 0) =
              (((Finset.univ.filter fun tail : Tape (N - used ρ) =>
                failedFlag size t start (d + 1) r
                  (List.ofFn tail) = true).card : ℕ) : ℚ) := by
            rw [Finset.card_filter]
            push_cast
            rfl
          rw [hsum]
          dsimp [Y]
          rw [div_mul_eq_mul_div]
          have hihQ : (2 ^ t : ℚ) *
              (((Finset.univ.filter fun tail : Tape (N - used ρ) =>
                failedFlag size t start (d + 1) r
                  (List.ofFn tail) = true).card : ℕ) : ℚ) ≤
              (r : ℚ) * 2 ^ (N - used ρ) := by exact_mod_cast hih
          exact (le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ t)).2
            (by simpa [mul_comm, mul_left_comm, mul_assoc] using hihQ))
      have hsumX : (∑ ρ : Tape N, X ρ) =
          ((Finset.univ.filter tailFailed).card : ℚ) := by
        rw [Finset.card_filter]
        push_cast
        rfl
      rw [hsumX] at hmean
      have hsumY : (∑ ρ : Tape N, Y ρ) =
          (r : ℚ) / 2 ^ t * 2 ^ N := by
        simp [Y, mul_comm]
      rw [hsumY] at hmean
      rw [div_mul_eq_mul_div] at hmean
      have hq : (2 ^ t : ℚ) *
          ((Finset.univ.filter tailFailed).card : ℚ) ≤
          (r : ℚ) * 2 ^ N := by
        have hp2 : (0 : ℚ) < 2 ^ t := by positivity
        have hh := (le_div_iff₀ hp2).mp hmean
        simpa [mul_comm, mul_left_comm, mul_assoc] using hh
      exact_mod_cast hq
    let bad : Finset (Tape N) := Finset.univ.filter fun ρ =>
      failedFlag size t start d (r + 1) (List.ofFn ρ) = true
    let headBad : Finset (Tape N) := Finset.univ.filter fun ρ =>
      (selectBitIndexWithCount (size d) hm t
        (firstTape (size d) t hhead ρ)).1 = none
    let tailBad : Finset (Tape N) := Finset.univ.filter tailFailed
    have hsub : bad ⊆ headBad ∪ tailBad := by
      intro ρ hρ
      have hfail : failedFlag size t start d (r + 1)
          (List.ofFn ρ) = true := by simpa [bad] using hρ
      have htailBudget : bitBudget size t (d + 1) r ≤
          (List.ofFn ((splitEquiv hhead ρ).2)).length := by
        simp only [List.length_ofFn]
        simp only [bitBudget] at hb
        omega
      have hs := failedFlag_step_or size t start d r
        (firstTape (size d) t hhead ρ)
        (List.ofFn ((splitEquiv hhead ρ).2)) hm
        (fun j hj hjr => hp j (by omega) (by omega))
        htailBudget (by simpa only [← firstTape_split (size d) t hhead ρ] using hfail)
      rcases hs with hfirst | hnext
      · exact Finset.mem_union_left _ (by simpa [headBad] using hfirst)
      · rw [← firstTape_split (size d) t hhead ρ] at hnext
        exact Finset.mem_union_right _ (by simpa [tailBad, tailFailed, used] using hnext)
    have hbad : bad.card ≤ headBad.card + tailBad.card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hheadCount : 2 ^ t * headBad.card ≤ 2 ^ N := by
      simpa [headBad] using first_failure_count (size d) t hm hhead
    have htailCount' : 2 ^ t * tailBad.card ≤ r * 2 ^ N := by
      simpa [tailBad] using htailCount
    have hgoal : 2 ^ t * bad.card ≤ (r + 1) * 2 ^ N := by
      calc
        _ ≤ 2 ^ t * (headBad.card + tailBad.card) :=
          Nat.mul_le_mul_left _ hbad
        _ = 2 ^ t * headBad.card + 2 ^ t * tailBad.card := by ring
        _ ≤ 2 ^ N + r * 2 ^ N := Nat.add_le_add hheadCount htailCount'
        _ = (r + 1) * 2 ^ N := by ring
    simpa only [bad] using hgoal

/-- The actual full-attempt poststate reports a failed batch selector. -/
def readyAttemptBatchAbort
    {B n m domainCap r t bufferCap targetCap Q k cap N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (hbudget : attemptBitBudget n m r t ≤ N)
    (ρ : Tape N) : Prop :=
  ∃ σa : Env, ∃ q : ℕ,
    Run B fullInitialAttempt
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hbudget)).I.σ
      σa q ∧ σa.vars "batchFailed" = 1

noncomputable def readyAttemptBatchAbortFiber
    {B n m domainCap r t bufferCap targetCap Q k cap N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (hbudget : attemptBitBudget n m r t ≤ N) : Finset (Tape N) := by
  classical
  exact Finset.univ.filter (readyAttemptBatchAbort R hbudget)

/-- A concrete batch abort is the failure of the corresponding adaptive
flat selector trace, including the unread suffix. -/
lemma readyAttemptBatchAbort_failedFlag
    {B n m domainCap r t bufferCap targetCap Q k cap N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (hbudget : attemptBitBudget n m r t ≤ N) (ρ : Tape N)
    (habort : readyAttemptBatchAbort R hbudget ρ) :
    failedFlag (fun _ => m) t (fun _ => 0) 0 r (List.ofFn ρ) = true := by
  let J := R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hbudget)
  obtain ⟨σr, qr, hrunr, hrbatch⟩ := habort
  obtain ⟨σsel, σa, tape, tail, values, used, drawFailed, stageCost,
    hbits, htrace, hselRun, hfull, hbatch, hinpSel, houtSel,
    hoff, htgt, hactiveA, hactiveB, hn, hqpow,
    hdrawFailure, hdrawSuccess⟩ :=
    fullInitialAttempt_run_bits J.I J.hactiveA J.hdegree J.hinter
      J.hneighbors J.hexceptionFlags J.hexceptionList J.hnearBound
      J.hexceptionCap J.hnB J.hkB J.hcapB
  have heq : σr = σa := by
    obtain ⟨_, _, ha⟩ := hrunr
    obtain ⟨_, _, hb⟩ := hfull
    exact (BigStep.unique ha.bigStep hb.bigStep).1
  have hdrawFailed : drawFailed = true := by
    cases drawFailed with
    | true => rfl
    | false => simp [hbatch, heq] at hrbatch
  obtain ⟨charge, hclass⟩ := drawTrace_to_classTrace m J.I.hmPos t 0 htrace
  have hclass' : ClassTrace (fun _ => m) t (fun _ => 0) 0 r
      (List.ofFn ρ) (values.map Fin.val)
      (used * Nat.clog 2 m) charge drawFailed := by
    have hh := ClassTrace.append_bits hclass tail
    change ClassTrace (fun _ => m) t (fun _ => 0) 0 r
      (tapeBits tape ++ tail) (values.map Fin.val)
      (used * Nat.clog 2 m) charge drawFailed at hh
    rw [← hbits] at hh
    simpa [J, ReadyInput.reinput_bits] using hh
  simpa [hdrawFailed] using failedFlag_eq hclass'

/-- At most `r·2⁻ᵗ` of all flat tapes cause an actual batch-selector abort
in one full source attempt. -/
lemma readyAttemptBatchAbort_count
    {B n m domainCap r t bufferCap targetCap Q k cap N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (hbudget : attemptBitBudget n m r t ≤ N) :
    2 ^ t * (readyAttemptBatchAbortFiber R hbudget).card ≤ r * 2 ^ N := by
  classical
  have hsub : readyAttemptBatchAbortFiber R hbudget ⊆
      Finset.univ.filter (fun ρ : Tape N =>
        failedFlag (fun _ => m) t (fun _ => 0) 0 r (List.ofFn ρ) = true) := by
    intro ρ hρ
    have habort : readyAttemptBatchAbort R hbudget ρ := by
      simpa [readyAttemptBatchAbortFiber] using hρ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      readyAttemptBatchAbort_failedFlag R hbudget ρ habort⟩
  have hbudget' : bitBudget (fun _ => m) t 0 r ≤ N := by
    rw [constant_bitBudget]
    unfold attemptBitBudget at hbudget
    omega
  have hcount := class_failure_count_bound (fun _ => m) t (fun _ => 0) r
    0 N (fun _ _ _ => R.I.hmPos) hbudget'
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans hcount

/-- A failed representative flag in the actual initial program agrees with
the class-selector trace at the deterministic post-draw partition state. -/
lemma failedFlag_of_attempt_repFailed
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Input B n m domainCap r t bufferCap targetCap Q G x A)
    (C : Cut I) (hf : C.failed = false)
    (q : ℕ) (RI : RepresentativeInput B n q Q t)
    (hbits : RI.bits = I.bits.drop (C.used * Nat.clog 2 m))
    (hrest : RI.rest = I.rest)
    (hpart : Run B fullSamplePartition C.drawFinal RI.σ
      (384 * n + 324 * targetCap + 70))
    {σsel : Env} {k : ℕ}
    (hrun : Run B initialSamplerAttempt I.σ σsel k)
    (hrep : σsel.vars "repFailed" = 1) :
    failedFlag RI.size t (classStart RI.size) 0 q RI.bits = true := by
  obtain ⟨σrep,xs,sorted,v,u,c,f,hrepRun,hnodup,hset,hlen,htrace,
    hclassSize,hord,hsorted,hclassB,hactiveB,hsampleFlags,hflag,hindex,
    hrepB,hinp,hout,hframe,hfailure,hsuccess⟩ :=
      initialRepresentativeSelection_run_bits RI
  have hs := hpart.seq hrepRun
  have hg : (Cond.eq (.var "batchFailed") (.lit 0)).evalB B C.drawFinal =
      some true := by
    simp [Cond.evalB, Expr.evalB, fit, C.drawFlag, hf, I.honeB,
      Nat.zero_lt_of_lt I.honeB]
  have hafter : Run B afterDraw C.drawFinal σrep
      (4 + (384 * n + 324 * targetCap + 70) +
        (20 * n + 9 + c + 64 * (xs.length + Q + 1) + 104 * n + 24)) := by
    have hh := Run.ite_true (d := .skip) hg hs
    simpa [afterDraw, Cond.size, Expr.size, Nat.add_assoc] using hh
  obtain ⟨_, _, hactualRun⟩ := hrun
  obtain ⟨_, hactual, _⟩ := actual_decompose I C hactualRun
  obtain ⟨_, _, hafterRun⟩ := hafter
  have heq : σsel = σrep := (BigStep.unique hactual.bigStep hafterRun.bigStep).1
  have hf' : f = true := by
    cases f with
    | true => rfl
    | false => simp [hflag, heq] at hrep
  simpa [hf'] using failedFlag_eq htrace

/-- The initial sampler's batch flag is determined by the same actual draw
execution retained in a `Cut`. -/
lemma Cut.batch_flag
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Input B n m domainCap r t bufferCap targetCap Q G x A)
    (C : Cut I) {σa : Env} {k : ℕ}
    (hrun : Run B initialSamplerAttempt I.σ σa k) :
    σa.vars "batchFailed" = (if C.failed then 1 else 0) := by
  obtain ⟨σd,σf,tape,tail,values,used,failed,stageCost,hbits,htrace,hfull,
    haccept,hn,hq,hbatch,harr,hvar,hfail,hpass,hdraw,hinp,hflag⟩ :=
    initialSamplerAttempt_run_bits I
  have hfinal : σa = σf := by
    obtain ⟨_,_,ha⟩ := hrun
    obtain ⟨_,_,hb⟩ := hfull
    exact (BigStep.unique ha.bigStep hb.bigStep).1
  have hdrawEq : C.drawFinal = σd := by
    obtain ⟨_,_,ha⟩ := C.drawRun
    obtain ⟨_,_,hb⟩ := hdraw
    exact (BigStep.unique ha.bigStep hb.bigStep).1
  have hh : (if failed then 1 else 0) = (if C.failed then 1 else 0) := by
    calc
      _ = σd.vars "batchFailed" := hflag.symm
      _ = C.drawFinal.vars "batchFailed" := by rw [hdrawEq]
      _ = _ := C.drawFlag
  have hf : failed = C.failed := by
    cases hf0 : failed <;> cases hc0 : C.failed
    · rfl
    · simp [hf0, hc0] at hh
    · simp [hf0, hc0] at hh
    · rfl
  simpa [hfinal, hf] using hbatch

/-- The second selector's actual failure flag in a complete attempt. -/
def readyAttemptRepresentativeAbort
    {B n m domainCap r t bufferCap targetCap Q k cap N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (hbudget : attemptBitBudget n m r t ≤ N)
    (ρ : Tape N) : Prop :=
  ∃ σa : Env, ∃ q : ℕ,
    Run B fullInitialAttempt
      (R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hbudget)).I.σ
      σa q ∧ σa.vars "batchFailed" = 0 ∧ σa.vars "repFailed" = 1

lemma readyAttemptRepresentativeAbort_cut
    {B n m domainCap r t bufferCap targetCap Q k cap N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    (hbudget : attemptBitBudget n m r t ≤ N) (ρ : Tape N)
    (C : Cut (R.reinput (List.ofFn ρ)
      (by simpa [attemptBitBudget] using hbudget)).I)
    (habort : readyAttemptRepresentativeAbort R hbudget ρ) :
    C.failed = false ∧
      ∃ σsel : Env, ∃ j : ℕ,
        Run B initialSamplerAttempt
          (R.reinput (List.ofFn ρ)
            (by simpa [attemptBitBudget] using hbudget)).I.σ σsel j ∧
        σsel.vars "repFailed" = 1 := by
  let J := R.reinput (List.ofFn ρ) (by simpa [attemptBitBudget] using hbudget)
  obtain ⟨σr, qr, hrunr, hbatch0, hrep1⟩ := habort
  obtain ⟨σsel, σa, tape, tail, values, used, drawFailed, stageCost,
    hbits, htrace, hselRun, hpair, hbatch, hinpSel, houtSel,
    hoff, htgt, hactiveA, hactiveB, hn, hqpow,
    hdrawFailure, hdrawSuccess⟩ :=
    fullInitialAttempt_run_bits_withTail J.I J.hactiveA J.hdegree J.hinter
      J.hneighbors J.hexceptionFlags J.hexceptionList J.hnearBound
      J.hexceptionCap J.hnB J.hkB J.hcapB
  have hwhole := hpair.1
  have hsuffix := hpair.2
  have heq : σr = σa := by
    obtain ⟨_,_,ha⟩ := hrunr
    obtain ⟨_,_,hb⟩ := hwhole
    exact (BigStep.unique ha.bigStep hb.bigStep).1
  have hbatchSel : σsel.vars "batchFailed" = 0 := by
    calc
      _ = σa.vars "batchFailed" := (hsuffix.frame_var "batchFailed" (by decide)).symm
      _ = 0 := by simpa [heq] using hbatch0
  have hrepSel : σsel.vars "repFailed" = 1 := by
    calc
      _ = σa.vars "repFailed" := (hsuffix.frame_var "repFailed" (by decide)).symm
      _ = 1 := by simpa [heq] using hrep1
  have hf := Cut.batch_flag J.I C hselRun
  have hfalse : C.failed = false := by
    cases hC : C.failed
    · rfl
    · simp [hC] at hf
      omega
  exact ⟨hfalse, σsel, _, hselRun, hrepSel⟩

/-- Failed source representative selection from a fixed, factual partition
state. The later initial-attempt proof conditions on its draw prefix to use
this bound when the partition depends on the sample. -/
def representativeAbort
    {B n q Q t N : ℕ} (I : RepresentativeInput B n q Q t)
    (hb : bitBudget I.size t 0 q ≤ N) (ρ : Tape N) : Prop :=
  ∃ σa : Env, ∃ k : ℕ,
    Run B initialRepresentativeSelection
      (reinput I (List.ofFn ρ) (by simpa using hb)).σ σa k ∧
    σa.vars "repFailed" = 1

noncomputable def representativeAbortFiber
    {B n q Q t N : ℕ} (I : RepresentativeInput B n q Q t)
    (hb : bitBudget I.size t 0 q ≤ N) : Finset (Tape N) := by
  classical
  exact Finset.univ.filter (representativeAbort I hb)

lemma representativeAbort_count
    {B n q Q t N : ℕ} (I : RepresentativeInput B n q Q t)
    (hb : bitBudget I.size t 0 q ≤ N) :
    2 ^ t * (representativeAbortFiber I hb).card ≤ q * 2 ^ N := by
  classical
  have hsub : representativeAbortFiber I hb ⊆
      Finset.univ.filter (fun ρ : Tape N =>
        failedFlag I.size t (classStart I.size) 0 q (List.ofFn ρ) = true) := by
    intro ρ hρ
    have habort : representativeAbort I hb ρ := by
      simpa [representativeAbortFiber] using hρ
    obtain ⟨σa, ka, hra, hfailed⟩ := habort
    let J := reinput I (List.ofFn ρ) (by simpa using hb)
    obtain ⟨σb,xs,sorted,v,u,c,f,hrb,hnodup,hset,hlen,htrace,
      hclassSize,hord,hsorted,hclassB,hactiveB,hsampleFlags,hflag,hindex,
      hrepB,hinp,hout,hframe,hfailure,hsuccess⟩ :=
      initialRepresentativeSelection_run_bits J
    have heq : σa = σb := by
      obtain ⟨_,_,ha⟩ := hra
      obtain ⟨_,_,hb⟩ := hrb
      exact (BigStep.unique ha.bigStep hb.bigStep).1
    have hf : f = true := by
      cases f with
      | true => rfl
      | false => simp [hflag, heq] at hfailed
    have hflag' : failedFlag I.size t (classStart I.size) 0 q (List.ofFn ρ) = true := by
      simpa [hf, J, reinput] using failedFlag_eq htrace
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hflag'⟩
  have hcount := class_failure_count_bound I.size t (classStart I.size) q
    0 N (fun j _ hj => I.hoccupied j (by omega)) hb
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans hcount

end Lax457868Proofs.InitialAbortProbability
