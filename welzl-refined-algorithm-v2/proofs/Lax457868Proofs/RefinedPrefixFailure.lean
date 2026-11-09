import Lax457868Proofs.RefinedPrefixMean

/-! Transfer an actual fixed-start prepared-round failure bound through the
physical stopped prefix before each chronological body round. -/
namespace Lax457868Proofs.RefinedPrefixFailure

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax195003.WordRamRandomness
open Lax457868Proofs.RefinedRoundLoop
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundTrace
open Lax457868Proofs.RefinedRoundPrefix
open Lax457868Proofs.RefinedPrefixMean
open Lax457868Proofs.RefinedBodyEstimate
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open scoped BigOperators

set_option maxHeartbeats 2000000

/-- Uniform fixed-start bound for the failure statuses of actual prepared
round runs. Its numerator counts all status failures, so it also covers the
subset recorded as failed chronological events. -/
def FixedPreparedRoundFailure {B c n Fcoef : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} : Prop := by
  classical
  exact
  ∀ (S : Env) (L : ℕ),
    LoopReady B c G x [] S →
    roundGuard.evalB B S = some true →
    S.inp.length = L →
    roundBitReserve c n ≤ L →
    (final : Tape L → Env) → (cost : Tape L → ℕ) →
    (∀ tail, BigStepB B preparedRefinedRoundSource
      {S with inp := (List.ofFn tail).map Bool.toNat}
      (final tail) (cost tail)) →
    2 ^ n * ((Finset.univ.filter fun tail : Tape L =>
      failureStatus (final tail)).card) ≤ Fcoef * 2 ^ L

/-- A failed event on one completion is a failure status of the selected
actual source execution for that completion. -/
private lemma failed_event_status {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env} {N i : ℕ}
    (F : LargeBodyFamily B c n N G x σ) (ρ : Tape N)
    {e : RoundEvent} (he : (F.events ρ)[i]? = some e)
    (hfail : failedAt (F.events ρ) i = true) :
    failureStatus e.exit := by
  obtain ⟨e',he',_,_,hs⟩ := (F.trace ρ).failedAt_status i hfail
  have hsame : e' = e := by simpa [he] using he'.symm
  simpa [hsame] using hs

/-- The body failure fiber at a chronological index inherits the exact
fixed-start bound, including arbitrary unread suffixes and missing events. -/
lemma index_failure_le_of_fixed {B c n N Fcoef : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (F : LargeBodyFamily B c n N G x σ)
    (hfixed : FixedPreparedRoundFailure (B := B) (c := c) (n := n)
      (Fcoef := Fcoef) (G := G) (x := x))
    (hN : n ≤ N) (i : ℕ) :
    ((Finset.univ.filter fun ρ : Tape N =>
      failedAt (F.events ρ) i = true).card) ≤
      Fcoef * 2 ^ (N - n) := by
  classical
  let used : Tape N → ℕ := fun ρ => usedBefore (F.events ρ) i
  have hbound : ∀ ρ, used ρ ≤ N := fun ρ => F.usedBefore_le ρ i
  have hcausal : ∀ ρ η,
      (List.ofFn ρ).take (used ρ) = (List.ofFn η).take (used ρ) →
      used η = used ρ := by
    intro ρ η hp
    exact (body_prefix_causal F ρ η i hp).1
  let X : Tape N → ℚ := fun ρ =>
    if failedAt (F.events ρ) i = true then 1 else 0
  let Y : Tape N → ℚ := fun _ => (Fcoef : ℚ) / 2 ^ n
  have hcond : ∀ ρ,
      (∑ tail : Tape (N - used ρ),
        X ((splitEquiv (hbound ρ)).symm
          ((splitEquiv (hbound ρ) ρ).1, tail))) ≤
        Y ρ * 2 ^ (N - used ρ) := by
    intro ρ
    let S := stateBefore (F.events ρ) (F.quotient ρ) i
    let L := N - used ρ
    let extend : Tape L → Tape N := fun tail =>
      (splitEquiv (hbound ρ)).symm
        ((splitEquiv (hbound ρ) ρ).1, tail)
    have hSlen : S.inp.length = L := by
      have hi := body_prefix_input F ρ i
      simpa [S, L, used, List.length_drop, List.length_ofFn,
        Nat.sub_eq_iff_eq_add (hbound ρ)] using congrArg List.length hi
    by_cases hg : roundGuard.evalB B S = some true
    · obtain ⟨base,hbase⟩ := event_of_guard (F.trace ρ)
        (F.terminal_guard ρ) i hg
      obtain ⟨hentry,hready,_,_,_⟩ :=
        event_at_data (F.trace ρ) i hbase
      have hreadyS : LoopReady B c G x [] S := by simpa [hentry] using hready
      have hreserve := reserve_of_ready_guard hreadyS hg hSlen
      have hinfo (tail : Tape L) :
          ∃ e, (F.events (extend tail))[i]? = some e ∧
            BigStepB B preparedRefinedRoundSource
              {S with inp := (List.ofFn tail).map Bool.toNat}
              e.exit e.cost := by
        have hs := suffix_state F ρ i tail
        have hstate : stateBefore (F.events (extend tail))
            (F.quotient (extend tail)) i =
            {S with inp := (List.ofFn tail).map Bool.toNat} := by
          simpa [S, L, used, extend] using hs.2.1
        have hg' : roundGuard.evalB B
            (stateBefore (F.events (extend tail))
              (F.quotient (extend tail)) i) = some true := by
          simpa [hstate, roundGuard] using hg
        obtain ⟨e,he⟩ := event_of_guard (F.trace (extend tail))
          (F.terminal_guard (extend tail)) i hg'
        obtain ⟨heEntry,_,_,_,heRun⟩ :=
          event_at_data (F.trace (extend tail)) i he
        refine ⟨e,he,?_⟩
        simpa [heEntry,hstate] using heRun
      choose event hevent hrun using hinfo
      have hfixed' := hfixed S L hreadyS hg hSlen hreserve
        (fun tail => (event tail).exit) (fun tail => (event tail).cost) hrun
      have hpoint (tail : Tape L) : X (extend tail) ≤
          (if failureStatus (event tail).exit then (1 : ℚ) else 0) := by
        by_cases hf : failedAt (F.events (extend tail)) i = true
        · have hs := failed_event_status F (extend tail) (hevent tail) hf
          simp [X,hf,hs]
        · simp only [X, hf]
          positivity
      have hsum : (∑ tail : Tape L, X (extend tail)) ≤
          ((Finset.univ.filter fun tail : Tape L =>
            failureStatus (event tail).exit).card : ℚ) := by
        calc
          _ ≤ ∑ tail : Tape L,
              (if failureStatus (event tail).exit then (1 : ℚ) else 0) := by
                apply Finset.sum_le_sum
                intro tail _
                exact hpoint tail
          _ = _ := by simp
      have hfixedQ : (2 ^ n : ℚ) *
          ((Finset.univ.filter fun tail : Tape L =>
            failureStatus (event tail).exit).card : ℚ) ≤
          (Fcoef : ℚ) * 2 ^ L := by exact_mod_cast hfixed'
      have hpow : (0 : ℚ) < 2 ^ n := by positivity
      have hdivide :
          ((Finset.univ.filter fun tail : Tape L =>
            failureStatus (event tail).exit).card : ℚ) ≤
          ((Fcoef : ℚ) / 2 ^ n) * 2 ^ L := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hpow).2
        simpa [mul_comm,mul_left_comm,mul_assoc] using hfixedQ
      change (∑ tail : Tape L, X (extend tail)) ≤ Y ρ * 2 ^ L
      exact hsum.trans hdivide
    · have hzero (tail : Tape L) :
          failedAt (F.events (extend tail)) i = false := by
        have hs := suffix_state F ρ i tail
        have hstate : stateBefore (F.events (extend tail))
            (F.quotient (extend tail)) i =
            {S with inp := (List.ofFn tail).map Bool.toNat} := by
          simpa [S,L,used,extend] using hs.2.1
        cases he : (F.events (extend tail))[i]? with
        | none => simp [failedAt,he]
        | some e =>
            obtain ⟨heEntry,_,hg',_,_⟩ :=
              event_at_data (F.trace (extend tail)) i he
            have hsame : roundGuard.evalB B
                (stateBefore (F.events (extend tail))
                  (F.quotient (extend tail)) i) =
                roundGuard.evalB B S := by
              rw [hstate]
              rfl
            have hgt : roundGuard.evalB B S = some true := by
              rw [heEntry,hsame] at hg'
              exact hg'
            exact False.elim (hg hgt)
      change (∑ tail : Tape L, X (extend tail)) ≤ Y ρ * 2 ^ L
      simp [X,hzero,Y]
      positivity
  have htotal := StoppedPrefixAveraging.sum_le_of_stopped_prefix
    used hbound hcausal X Y (by intros; rfl) hcond
  have hXsum : (∑ ρ : Tape N, X ρ) =
      ((Finset.univ.filter fun ρ : Tape N =>
        failedAt (F.events ρ) i = true).card : ℚ) := by
    simp [X]
  have hYsum : (∑ ρ : Tape N, Y ρ) =
      ((Fcoef : ℚ) / 2 ^ n) * 2 ^ N := by
    simp [Y, Nat.cast_pow, mul_comm]
  rw [hXsum,hYsum] at htotal
  have hpow : (2 ^ N : ℚ) = (2 ^ n : ℚ) * 2 ^ (N - n) := by
    have he : 2 ^ N = 2 ^ n * 2 ^ (N - n) := by
      rw [←pow_add, Nat.add_sub_of_le hN]
    exact_mod_cast he
  have hscale : ((Fcoef : ℚ) / 2 ^ n) * 2 ^ N =
      (Fcoef : ℚ) * 2 ^ (N - n) := by
    rw [hpow]
    have hne : (2 ^ n : ℚ) ≠ 0 := by positivity
    field_simp
  rw [hscale] at htotal
  exact_mod_cast htotal

end Lax457868Proofs.RefinedPrefixFailure
