import Mathlib.Tactic
import Lax457868Proofs.SamplerEpsilonNet
import Lax457868Proofs.SamplerHitCount
import Lax457868Proofs.SamplerTrialBound

/-!
Geometry of the ranges relevant to a phase-three local repair.  A far
exception's phase-two trace class contains only nonexceptional competitors,
and each corresponding distinguishing range occupies a strict majority of
the symmetric-difference draw domain.
-/

namespace Lax457868Proofs.SamplerLocalSuccess

open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerLocalProbability
open Lax457868Proofs.SamplerUniformDraws
open Lax457868Proofs.SamplerEpsilonNet

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The members of `B` that share the phase-two trace of `b`, other than `b`.
-/
def localContenders (N : β → Finset α) (W : Finset α) (V : Finset β)
    (b : β) : Finset β :=
  V.filter fun v => trace N W b = trace N W v ∧ v ≠ b

/-- The distinguishing ranges for the fixed phase-two trace class. -/
def localDistinguishingFamily (N : β → Finset α) (B W : Finset α)
    (V : Finset β) (b : β) : Finset (Finset α) :=
  (localContenders N W V b).image fun v =>
    B ∩ distinguishingRange N b v

/-- The finite set of legal tapes on which a phase-three local repair fails. -/
noncomputable def localTrialFailureSet (N : β → Finset α) (B : Finset β)
    (W : Finset α) (b : β) (X : Finset α) (s : ℕ) : Finset (Tape X s) := by
  classical
  exact Finset.univ.filter fun tape => ¬ localTrialIsolates N B W b tape.toList

/-- Every contender of a far exception is nonexceptional after the complete
phase-two scan, provided full neighborhoods distinguish members of `B`. -/
lemma localContender_not_exception
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r k : ℕ) (choice : InitialChoice A B N r)
    (as : List α) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (hinj : ∀ b ∈ B, ∀ v ∈ B, N b = N v → b = v)
    (b v : β) (hb : b ∈ B) (hv : v ∈ B)
    (hfar : 2 * k < 3 * disagreement N b (choice.representative b))
    (htrace : trace N (phase2Scan N (choice.exceptions k) as choice.sample) b =
      trace N (phase2Scan N (choice.exceptions k) as choice.sample) v)
    (hvb : v ≠ b) : v ∉ choice.exceptions k := by
  intro hvE
  have hbE : b ∈ choice.exceptions k := by
    exact Finset.mem_filter.mpr ⟨hb, by omega⟩
  have hNb := phase2_separates_distinct_neighborhoods A B N as has hasNodup
    (choice.exceptions k) choice.sample hN (Finset.filter_subset _ _)
    b v hbE hvE htrace
  exact hvb (hinj b hb v hv hNb).symm

/-- For a far exception, every contender's distinguishing range contains more
than half of the repair domain. -/
lemma localContender_range_majority
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r k : ℕ) (choice : InitialChoice A B N r)
    (as : List α) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (hinj : ∀ b ∈ B, ∀ v ∈ B, N b = N v → b = v)
    (b v : β) (hb : b ∈ B) (hv : v ∈ B)
    (hfar : 2 * k < 3 * disagreement N b (choice.representative b))
    (htrace : trace N (phase2Scan N (choice.exceptions k) as choice.sample) b =
      trace N (phase2Scan N (choice.exceptions k) as choice.sample) v)
    (hvb : v ≠ b) :
    2 * (((N b \ N (choice.representative b)) ∪
        (N (choice.representative b) \ N b)) ∩
      distinguishingRange N b v).card >
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)).card := by
  have hrepTrace :
      trace N choice.sample b = trace N choice.sample v :=
    trace_eq_of_sample_subset N (phase2Scan_mono N (choice.exceptions k) as
      choice.sample) b v htrace
  have hrepEq : choice.representative b = choice.representative v :=
    (choice.representative_eq_iff_same_trace b v hb hv).2 hrepTrace
  have hvNotE := localContender_not_exception A B N r k choice as has
    hasNodup hN hinj b v hb hv hfar htrace hvb
  have hnear₀ : 3 * disagreement N v (choice.representative v) ≤ k := by
    have hnot : ¬ k < 3 * disagreement N v (choice.representative v) := by
      intro h
      exact hvNotE (Finset.mem_filter.mpr ⟨hv, h⟩)
    omega
  have hnear : 3 * Lax457868Proofs.SamplerDistance.disagreement
      (N v) (N (choice.representative b)) ≤ k := by
    simpa [hrepEq, SamplerPhases.disagreement,
      Lax457868Proofs.SamplerDistance.disagreement] using hnear₀
  simpa [SamplerPhases.disagreement,
    Lax457868Proofs.SamplerDistance.disagreement,
    distinguishingRange] using
    (Lax457868Proofs.SamplerDistance.disagreement_inter_majority
      (N b) (N (choice.representative b)) (N v) k hfar hnear)

/-- All ranges in the local repair family are strict majorities of its draw
domain, using only contenders from the same phase-two trace class. -/
lemma localDistinguishingFamily_majority
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r k : ℕ) (choice : InitialChoice A B N r)
    (as : List α) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (hinj : ∀ b ∈ B, ∀ v ∈ B, N b = N v → b = v)
    (b : β) (hb : b ∈ B)
    (hfar : 2 * k < 3 * disagreement N b (choice.representative b)) :
    ∀ D ∈ localDistinguishingFamily N
        (((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)))
        (phase2Scan N (choice.exceptions k) as choice.sample)
        B b,
      2 * D.card >
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)).card := by
  classical
  intro D hD
  rcases Finset.mem_image.mp hD with ⟨v, hvC, rfl⟩
  rcases Finset.mem_filter.mp hvC with ⟨hvE, hconditions⟩
  rcases hconditions with ⟨htrace, hvb⟩
  have hv := hvE
  exact localContender_range_majority A B N r k choice as has hasNodup
    hN hinj b v hb hv hfar htrace hvb

/-- The trace count of the repair ranges is bounded by the neighborhood
shatter function, since taking symmetric difference with a fixed trace cannot
increase the number of traces. -/
lemma localDistinguishingFamily_trace_bound
    (N : β → Finset α) (B : Finset β) (X Y : Finset α)
    (W : Finset α) (V : Finset β) (b : β) (c : ℕ) (hYX : Y ⊆ X)
    (hC : localContenders N W V b ⊆ B)
    (htrace : (traceClasses N Y B).card ≤ c * Y.card) :
    ((localDistinguishingFamily N X W V b).image fun D => D ∩ Y).card ≤
      c * Y.card := by
  classical
  have himage :
      (localDistinguishingFamily N X W V b).image (fun D => D ∩ Y) =
        (localContenders N W V b).image
          (fun v => (X ∩ distinguishingRange N b v) ∩ Y) := by
    rw [localDistinguishingFamily, Finset.image_image]
    apply Finset.image_congr
    intro v hv
    ext a
    simp only [Function.comp_apply, Finset.mem_inter]
  rw [himage]
  have hsubset :
      (localContenders N W V b).image
          (fun v => (X ∩ distinguishingRange N b v) ∩ Y) ⊆
        B.image (fun v => (X ∩ distinguishingRange N b v) ∩ Y) :=
    by
      intro D hD
      rcases Finset.mem_image.mp hD with ⟨v, hv, rfl⟩
      exact Finset.mem_image.mpr ⟨v, hC hv, rfl⟩
  calc
    _ ≤ (B.image fun v => (X ∩ distinguishingRange N b v) ∩ Y).card :=
      Finset.card_le_card hsubset
    _ ≤ (traceClasses N Y B).card :=
      distinguishingFamily_trace_card_le N X Y B b hYX
    _ ≤ c * Y.card := htrace

/-- A legal tape fails local isolation exactly when it misses one of the
majority ranges in its phase-two trace class. -/
lemma localTrial_failure_iff_missed_majority
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r k s : ℕ) (choice : InitialChoice A B N r)
    (as : List α) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (hinj : ∀ b ∈ B, ∀ v ∈ B, N b = N v → b = v)
    (b : β) (hb : b ∈ B)
    (hfar : 2 * k < 3 * disagreement N b (choice.representative b))
    {X : Finset α}
    (hX : X = (N b \ N (choice.representative b)) ∪
      (N (choice.representative b) \ N b))
    (tape : Tape X s) :
    ¬ localTrialIsolates N B
        (phase2Scan N (choice.exceptions k) as choice.sample) b tape.toList ↔
      missedMajority (localDistinguishingFamily N X
        (phase2Scan N (choice.exceptions k) as choice.sample) B b) X tape := by
  classical
  let W := phase2Scan N (choice.exceptions k) as choice.sample
  let F := localDistinguishingFamily N X W B b
  have hmajority : ∀ D ∈ F, 2 * D.card > X.card := by
    intro D hD
    have h := localDistinguishingFamily_majority A B N r k choice as has hasNodup
      hN hinj b hb hfar D (by simpa [F, W, hX] using hD)
    simpa [hX] using h
  constructor
  · intro hfail
    obtain ⟨v, hv, htrace, hvb, hmiss⟩ :=
      (not_localTrialIsolates_iff_tape_misses_range N B
        (phase2Scan N (choice.exceptions k) as choice.sample) b X s tape).mp hfail
    let D := X ∩ distinguishingRange N b v
    have hvC : v ∈ localContenders N
        (phase2Scan N (choice.exceptions k) as choice.sample) B b := by
      simp [localContenders, htrace, hv, hvb]
    have hD : D ∈ F := by
      exact Finset.mem_image.mpr ⟨v, hvC, rfl⟩
    have hDX : D ⊆ X := Finset.inter_subset_left
    have hmissD : Misses D tape := by
      intro i hi
      exact hmiss i (Finset.mem_inter.mp hi).2
    exact ⟨D, hD, hDX, hmajority D hD, hmissD⟩
  · rintro ⟨D, hD, hDX, hmajorityD, hmissD⟩
    rcases Finset.mem_image.mp hD with ⟨v, hvC, rfl⟩
    rcases Finset.mem_filter.mp hvC with ⟨hv, ⟨htrace, hvb⟩⟩
    have hmiss : Misses (distinguishingRange N b v) tape := by
      intro i hi
      apply hmissD i
      exact Finset.mem_inter.mpr ⟨(tape i).property, hi⟩
    apply (not_localTrialIsolates_iff_tape_misses_range N B
      (phase2Scan N (choice.exceptions k) as choice.sample) b X s tape).mpr
    exact ⟨v, hv, htrace, hvb, hmiss⟩

/-- The number of failed legal local trials inherits the paired-swap epsilon
net bound. The second-sample quarter-hit estimate is supplied by the checked
finite first-moment theorem. -/
lemma card_localTrialFailures_mul_pow_le_eight
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r k s q c : ℕ) (choice : InitialChoice A B N r)
    (as : List α) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (hinj : ∀ b ∈ B, ∀ v ∈ B, N b = N v → b = v)
    (b : β) (hb : b ∈ B)
    (hfar : 2 * k < 3 * disagreement N b (choice.representative b))
    {X : Finset α}
    (hX : X = (N b \ N (choice.representative b)) ∪
      (N (choice.representative b) \ N b))
    (hXnonempty : X.Nonempty) (hs : 0 < s) (hq : q ≤ s) (h4q : 4 * q ≤ s)
    (hshatter : ∀ Y : Finset α, Y ⊆ A → Y.Nonempty →
      (traceClasses N Y B).card ≤ c * Y.card) :
    2 ^ q * (localTrialFailureSet N B
        (phase2Scan N (choice.exceptions k) as choice.sample) b X s).card ≤
      8 * c * s * X.card ^ s := by
  classical
  let W := phase2Scan N (choice.exceptions k) as choice.sample
  let F := localDistinguishingFamily N X W B b
  have hfamilyTrace : ∀ Y : Finset α, Y ⊆ X → Y.Nonempty →
      (F.image fun D => D ∩ Y).card ≤ c * Y.card := by
    intro Y hYX hY
    have hXA : X ⊆ A := by
      intro x hx
      rw [hX] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hN b hb ((Finset.mem_sdiff.mp hx).1)
      · exact hN (choice.representative b)
          (choice.representative_mem b hb) ((Finset.mem_sdiff.mp hx).1)
    have hYA := hYX.trans hXA
    exact localDistinguishingFamily_trace_bound N B X Y W B b c hYX
      (by intro v hv; exact (Finset.mem_filter.mp hv).1) (hshatter Y hYA hY)
  have hsecond : ∀ D ∈ F, D ⊆ X → 2 * D.card > X.card →
      3 * (Finset.univ.filter fun tape : Tape X s =>
        q ≤ Lax457868Proofs.SamplerEpsilonNet.hitCount D tape).card ≥ X.card ^ s := by
    intro D hD hDX hmaj
    exact Lax457868Proofs.SamplerHitCount.majority_hit_tapes_lower_bound
      hDX hXnonempty (by omega) hs h4q
  have hnet := Lax457868Proofs.SamplerEpsilonNet.card_missedMajority_mul_pow_le_eight
    hXnonempty hs hq F hfamilyTrace hsecond
  have hevent :
      (localTrialFailureSet N B W b X s).card =
      (Finset.univ.filter fun tape : Tape X s =>
        Lax457868Proofs.SamplerEpsilonNet.missedMajority F X tape).card := by
    unfold localTrialFailureSet
    congr 1
    ext tape
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact localTrial_failure_iff_missed_majority A B N r k s choice as has
      hasNodup hN hinj b hb hfar hX tape
  simpa [W, F, hevent] using hnet

/-- With the paper's sample size, the paired-swap estimate makes the local
phase-three failure set strictly smaller than half of the uniform tape space.
-/
lemma localTrial_failure_lt_half
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r k c : ℕ) (choice : InitialChoice A B N r)
    (as : List α) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (hinj : ∀ b ∈ B, ∀ v ∈ B, N b = N v → b = v)
    (b : β) (hb : b ∈ B)
    (hfar : 2 * k < 3 * disagreement N b (choice.representative b))
    (hc : 2 ≤ c)
    (hshatter : ∀ Y : Finset α, Y ⊆ A → Y.Nonempty →
      (traceClasses N Y B).card ≤ c * Y.card) :
    2 * (localTrialFailureSet N B
        (phase2Scan N (choice.exceptions k) as choice.sample) b
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b))
        (64 * Nat.clog 2 c)).card <
      ((N b \ N (choice.representative b)) ∪
        (N (choice.representative b) \ N b)).card ^ (64 * Nat.clog 2 c) := by
  classical
  let X := (N b \ N (choice.representative b)) ∪
    (N (choice.representative b) \ N b)
  let s := 64 * Nat.clog 2 c
  let q := 16 * Nat.clog 2 c
  have hL : 1 ≤ Nat.clog 2 c := Nat.clog_pos (by omega) hc
  have hs : 0 < s := by dsimp [s]; omega
  have hq : q ≤ s := by dsimp [q, s]; omega
  have h4q : 4 * q = s := by dsimp [q, s]; omega
  have hXcard : X.card = disagreement N b (choice.representative b) := by
    simp [X, SamplerPhases.disagreement]
  have hdistpos : 0 < disagreement N b (choice.representative b) := by omega
  have hXnonempty : X.Nonempty := Finset.card_pos.mp (by rw [hXcard]; omega)
  have hbound := card_localTrialFailures_mul_pow_le_eight A B N r k s q c
    choice as has hasNodup hN hinj b hb hfar rfl hXnonempty hs hq (by omega) hshatter
  have hcoeff : 16 * c * s < 2 ^ q := by
    have hcPow : c ≤ 2 ^ Nat.clog 2 c := Nat.le_pow_clog (by omega) c
    have hLPow := Lax457868Proofs.SamplerTrialBound.le_two_pow (Nat.clog 2 c)
    have hmul₁ : 16 * c * (64 * Nat.clog 2 c) ≤
        1024 * (2 ^ Nat.clog 2 c) * Nat.clog 2 c := by
      calc
        16 * c * (64 * Nat.clog 2 c) = c * (1024 * Nat.clog 2 c) := by ring
        _ ≤ (2 ^ Nat.clog 2 c) * (1024 * Nat.clog 2 c) :=
          Nat.mul_le_mul_right _ hcPow
        _ = 1024 * (2 ^ Nat.clog 2 c) * Nat.clog 2 c := by ring
    have hmul₂ : 1024 * (2 ^ Nat.clog 2 c) * Nat.clog 2 c ≤
        2 ^ (10 + 2 * Nat.clog 2 c) := by
      calc
        1024 * (2 ^ Nat.clog 2 c) * Nat.clog 2 c ≤
            1024 * (2 ^ Nat.clog 2 c) * (2 ^ Nat.clog 2 c) :=
          by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
              Nat.mul_le_mul_left (1024 * 2 ^ Nat.clog 2 c) hLPow
        _ = 2 ^ (10 + 2 * Nat.clog 2 c) := by
          rw [show 1024 = 2 ^ 10 by norm_num, ← pow_add, ← pow_add]
          congr 1
          omega
    have hexp : 10 + 2 * Nat.clog 2 c < 16 * Nat.clog 2 c := by omega
    have hpow : 2 ^ (10 + 2 * Nat.clog 2 c) <
        2 ^ (16 * Nat.clog 2 c) :=
      Nat.pow_lt_pow_right (by omega) hexp
    dsimp [s, q]
    calc
      16 * c * (64 * Nat.clog 2 c) ≤
          1024 * (2 ^ Nat.clog 2 c) * Nat.clog 2 c := hmul₁
      _ ≤ 2 ^ (10 + 2 * Nat.clog 2 c) := hmul₂
      _ < 2 ^ (16 * Nat.clog 2 c) := hpow
  let bad := (localTrialFailureSet N B
    (phase2Scan N (choice.exceptions k) as choice.sample) b X s).card
  have hscaled : 2 ^ q * (2 * bad) ≤ (16 * c * s) * X.card ^ s := by
    calc
      2 ^ q * (2 * bad) = 2 * (2 ^ q * bad) := by ring
      _ ≤ 2 * (8 * c * s * X.card ^ s) := Nat.mul_le_mul_left 2 hbound
      _ = (16 * c * s) * X.card ^ s := by ring
  have hXpowpos : 0 < X.card ^ s := Nat.pow_pos (Finset.card_pos.mpr hXnonempty)
  have hstrict := Nat.mul_lt_mul_of_pos_right hcoeff hXpowpos
  have hprod : 2 ^ q * (2 * bad) < 2 ^ q * X.card ^ s :=
    hscaled.trans_lt hstrict
  have hbad : 2 * bad < X.card ^ s := by
    by_contra hnot
    have hle : X.card ^ s ≤ 2 * bad := by omega
    have := Nat.mul_le_mul_left (2 ^ q) hle
    omega
  simpa [X, s, bad] using hbad

end Lax457868Proofs.SamplerLocalSuccess
