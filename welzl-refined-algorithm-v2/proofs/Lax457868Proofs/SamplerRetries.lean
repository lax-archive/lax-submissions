import Mathlib.Tactic
import Lax457868Proofs.SamplerPhases

/-!
Finite independent-retry counting for the concrete initial and local selectors.
The hypotheses that a single attempt is bad on at most half of its finite
sample space are stated explicitly: these repetition lemmas do not derive the
paper's geometric or epsilon-net estimate that would establish those bounds.
-/

namespace Lax457868Proofs.SamplerRetries

open Lax457868Proofs.SamplerPhases

/-- A length-`t` independent tape, represented by a function. Repeated values
are allowed, so this is sampling with replacement. -/
abbrev Tape (Ω : Type*) (t : ℕ) := Fin t → Ω

/-- Number of attempts inspected before the first accepted outcome, capped by
the length of the supplied sequence. A rejected outcome recurses; an accepted
one stops immediately. -/
def attemptsUsed {Ω : Type*} (bad : Ω → Bool) : List Ω → ℕ
  | [] => 0
  | outcome :: rest => if bad outcome then attemptsUsed bad rest + 1 else 1

/-- Generic first-passing selector: inspect outcomes from left to right and
return the first one satisfying `accept`. -/
def firstPassing {Ω : Type*} (accept : Ω → Bool) : List Ω → Option Ω
  | [] => none
  | outcome :: rest =>
      if accept outcome then some outcome else firstPassing accept rest

/-- Run the first-passing selector while also counting inspected outcomes. -/
def firstPassingWithCount {Ω : Type*} (accept : Ω → Bool) :
    List Ω → Option Ω × ℕ
  | [] => (none, 0)
  | outcome :: rest =>
      if accept outcome then (some outcome, 1)
      else
        let (winner, count) := firstPassingWithCount accept rest
        (winner, count + 1)

/-- The scan's second component is exactly the recursive attempt count. -/
lemma firstPassingWithCount_eq {Ω : Type*} (accept : Ω → Bool)
    (outcomes : List Ω) :
    firstPassingWithCount accept outcomes =
      (firstPassing accept outcomes,
        attemptsUsed (fun x => !accept x) outcomes) := by
  induction outcomes with
  | nil => rfl
  | cons outcome rest ih =>
      by_cases h : accept outcome <;>
        simp [firstPassingWithCount, firstPassing, attemptsUsed, h, ih]

/-- The actual number of attempts consumed by the selector over a finite tape
when exactly the outcomes in `R` are rejected. -/
def tapeAttemptsUsed {Ω : Type*} [DecidableEq Ω]
    (R : Finset Ω) {t : ℕ} (tape : Tape Ω t) : ℕ :=
  attemptsUsed (fun x => decide (x ∈ R)) (List.ofFn tape)

/-- Sum of actual consumed-attempt counts over every length-`t` tape. -/
def sumTapeAttemptsUsed {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : Finset Ω) (t : ℕ) : ℕ :=
  ∑ tape : Tape Ω t, tapeAttemptsUsed R tape

/-- Splitting a tape into its first outcome and its remaining independent tape
shows that total consumed attempts satisfy the exact recurrence
`S_(t+1) = |Ω|^(t+1) + |R| * S_t`. -/
lemma sumTapeAttemptsUsed_succ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : Finset Ω) (t : ℕ) :
    sumTapeAttemptsUsed R (t + 1) = Fintype.card Ω ^ (t + 1) +
      R.card * sumTapeAttemptsUsed R t := by
  classical
  let e : Ω × Tape Ω t ≃ Tape Ω (t + 1) :=
    Fin.consEquiv (fun _ : Fin (t + 1) => Ω)
  have hpoint (a : Ω) (tail : Tape Ω t) :
      tapeAttemptsUsed R (e (a, tail)) =
        (if a ∈ R then tapeAttemptsUsed R tail else 0) + 1 := by
    by_cases h : a ∈ R <;>
      simp [tapeAttemptsUsed, attemptsUsed, e, Fin.consEquiv, List.ofFn_succ, h]
  calc
    sumTapeAttemptsUsed R (t + 1) =
        ∑ pair : Ω × Tape Ω t, tapeAttemptsUsed R (e pair) := by
          unfold sumTapeAttemptsUsed
          exact (Fintype.sum_equiv e.symm _ _ (by intro tape; simp only [Equiv.apply_symm_apply]))
    _ = ∑ a : Ω, ∑ tail : Tape Ω t,
        ((if a ∈ R then tapeAttemptsUsed R tail else 0) + 1) := by
          rw [Fintype.sum_prod_type]
          apply Fintype.sum_congr
          intro a
          apply Fintype.sum_congr
          intro tail
          exact hpoint a tail
    _ = Fintype.card Ω ^ (t + 1) +
        R.card * sumTapeAttemptsUsed R t := by
          simp [sumTapeAttemptsUsed, Finset.sum_add_distrib]
          rw [pow_succ]
          ac_rfl

/-- Actual capped attempt counts over all length-`t` independent tapes total
at most twice the number of tapes whenever at most half of one-attempt outcomes
are rejected. -/
lemma sumTapeAttemptsUsed_le_two {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : Finset Ω) (t : ℕ)
    (hhalf : 2 * R.card ≤ Fintype.card Ω) :
    sumTapeAttemptsUsed R t ≤ 2 * Fintype.card Ω ^ t := by
  induction t with
  | zero => simp [sumTapeAttemptsUsed, tapeAttemptsUsed, attemptsUsed]
  | succ t ih =>
      rw [sumTapeAttemptsUsed_succ]
      have hmul : R.card * sumTapeAttemptsUsed R t ≤
          R.card * (2 * Fintype.card Ω ^ t) := Nat.mul_le_mul_left _ ih
      have hbound : Fintype.card Ω ^ (t + 1) +
          R.card * (2 * Fintype.card Ω ^ t) ≤
          2 * Fintype.card Ω ^ (t + 1) := by
        rw [pow_succ]
        nlinarith [hhalf]
      calc
        Fintype.card Ω ^ (t + 1) + R.card * sumTapeAttemptsUsed R t ≤
            Fintype.card Ω ^ (t + 1) +
              R.card * (2 * Fintype.card Ω ^ t) := Nat.add_le_add_left hmul _
        _ ≤ 2 * Fintype.card Ω ^ (t + 1) := hbound

/-- For the initial selector, this recursion counts exactly the attempts
inspected by its first-passing search: its exception-cap check determines
whether the selector recurses to the tail. -/
lemma attemptsUsed_initial_cons
    {α β Ω : Type*} [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r : ℕ}
    (decode : Ω → InitialChoice A B N r) (threshold cap : ℕ)
    (ω : Ω) (rest : List Ω) :
    attemptsUsed (fun x => decide
      (cap < ((decode x).exceptions threshold).card)) (ω :: rest) =
      if cap < ((decode ω).exceptions threshold).card then
        attemptsUsed (fun x => decide
          (cap < ((decode x).exceptions threshold).card)) rest + 1
      else 1 := by
  simp [attemptsUsed]

lemma attemptsUsed_local_cons
    {α β Ω : Type*} [DecidableEq α] [DecidableEq β]
    {X : Finset α} {s : ℕ}
    (decode : Ω → LocalTrial X s) (N : β → Finset α)
    (B : Finset β) (W : Finset α) (b : β)
    (ω : Ω) (rest : List Ω) :
    attemptsUsed (fun x => decide
      (localTrialIsolatesB N B W b (decode x).draws = false)) (ω :: rest) =
      if localTrialIsolatesB N B W b (decode ω).draws = false then
        attemptsUsed (fun x => decide
          (localTrialIsolatesB N B W b (decode x).draws = false)) rest + 1
      else 1 := by
  simp [attemptsUsed]

/-- Tapes on which every one of the `t` independent outcomes is bad. -/
def allBadTapes {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : Finset Ω) (t : ℕ) : Finset (Tape Ω t) :=
  Finset.univ.filter fun tape => ∀ i, tape i ∈ R

/-- The exact number of length-`t` tapes whose every draw lies in `R` is
`|R|^t`. -/
lemma card_allBadTapes {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : Finset Ω) (t : ℕ) : (allBadTapes R t).card = R.card ^ t := by
  classical
  let e : {tape : Tape Ω t // tape ∈ allBadTapes R t} ≃
      (Fin t → {x : Ω // x ∈ R}) := {
    toFun := fun (tape : {tape : Tape Ω t // tape ∈ allBadTapes R t}) i =>
      ⟨tape.val i, (Finset.mem_filter.mp tape.property).2 i⟩
    invFun := fun (f : Fin t → {x : Ω // x ∈ R}) =>
      ⟨fun i => (f i).val, Finset.mem_filter.mpr ⟨by simp, fun i => (f i).property⟩⟩
    left_inv := fun tape => by
      apply Subtype.ext
      funext i
      rfl
    right_inv := fun f => by
      funext i
      apply Subtype.ext
      rfl
  }
  calc
    (allBadTapes R t).card = Fintype.card {tape : Tape Ω t // tape ∈ allBadTapes R t} := by
      rw [Fintype.card_coe]
    _ = Fintype.card (Fin t → {x : Ω // x ∈ R}) := Fintype.card_congr e
    _ = Fintype.card {x : Ω // x ∈ R} ^ t := by simp
    _ = R.card ^ t := by simp

/-- The total number of length-`t` independent tapes over `Ω`. -/
lemma card_tapes (Ω : Type*) [Fintype Ω] (t : ℕ) :
    Fintype.card (Tape Ω t) = Fintype.card Ω ^ t := by
  simp [Tape]

/-- The actual expected attempt count over a uniform finite tape is the sum
of its pointwise consumed-attempt counts divided by the number of tapes. -/
def actualFiniteMeanAttempts {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : Finset Ω) (t : ℕ) : ℚ :=
  (sumTapeAttemptsUsed R t : ℚ) / Fintype.card (Tape Ω t)

/-- The actual finite-tape expected number of attempts is at most two under the
single-attempt half-rejection bound. -/
lemma actualFiniteMeanAttempts_le_two {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : Finset Ω) (t : ℕ) (hne : 0 < Fintype.card Ω)
    (hhalf : 2 * R.card ≤ Fintype.card Ω) :
    actualFiniteMeanAttempts R t ≤ 2 := by
  have htapes : (0 : ℚ) < Fintype.card (Tape Ω t) := by
    rw [card_tapes]
    exact_mod_cast Nat.pow_pos hne
  have hsum : (sumTapeAttemptsUsed R t : ℚ) ≤
      2 * Fintype.card (Tape Ω t) := by
    rw [card_tapes]
    exact_mod_cast (sumTapeAttemptsUsed_le_two R t hhalf)
  unfold actualFiniteMeanAttempts
  rw [div_le_iff₀ htapes]
  nlinarith


/-- If one attempt's bad set occupies at most half the finite sample space,
then the exact all-bad tape count is at most a `2^t` fraction of all tapes.
This is a counting theorem; no probability-law axiom is used. -/
lemma allBad_tape_count_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : Finset Ω) (t : ℕ)
    (hhalf : 2 * R.card ≤ Fintype.card Ω) :
    2 ^ t * (allBadTapes R t).card ≤ Fintype.card (Tape Ω t) := by
  rw [card_allBadTapes, card_tapes]
  have hp := Nat.pow_le_pow_left hhalf t
  rw [Nat.mul_pow] at hp
  simpa [Nat.mul_comm] using hp

/-- The geometric-series expression for the expected attempts in a retry
process capped after `t` attempts, when each independent attempt fails with
probability `p`. The actual finite tape expectation is separately defined and
proved below through `sumTapeAttemptsUsed`; its connection to this expression
is the familiar tail-probability interpretation. -/
def truncatedExpectedAttempts (p : ℚ) (t : ℕ) : ℚ :=
  ∑ j ∈ Finset.range t, p ^ j

lemma half_geometric_sum_eq (t : ℕ) :
    (∑ j ∈ Finset.range t, (1 / 2 : ℚ) ^ j) = 2 - 2 * (1 / 2 : ℚ) ^ t := by
  induction t with
  | zero => norm_num [truncatedExpectedAttempts]
  | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      rw [pow_succ]
      ring

/-- A truncated independent retry process whose per-attempt failure
probability is at most one half has expected attempt count at most two. -/
lemma truncatedExpectedAttempts_le_two {p : ℚ} (t : ℕ)
    (hp0 : 0 ≤ p) (hp : 2 * p ≤ 1) :
    truncatedExpectedAttempts p t ≤ 2 := by
  unfold truncatedExpectedAttempts
  have hple : p ≤ (1 / 2 : ℚ) := by nlinarith
  calc
    (∑ j ∈ Finset.range t, p ^ j) ≤
        ∑ j ∈ Finset.range t, (1 / 2 : ℚ) ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          exact pow_le_pow_left₀ hp0 hple j
    _ = 2 - 2 * (1 / 2 : ℚ) ^ t := half_geometric_sum_eq t
    _ ≤ 2 := by nlinarith [pow_nonneg (show (0 : ℚ) ≤ 1 / 2 by norm_num) t]

/-- Specialization to a finite uniform single-attempt space. The hypothesis
`2 * |R| ≤ |Ω|` is still an input: deriving it for either sampler phase is the
separate geometric/epsilon-net argument. -/
lemma finiteUniform_truncatedExpectedAttempts_le_two
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (R : Finset Ω) (t : ℕ) (hne : 0 < Fintype.card Ω)
    (hhalf : 2 * R.card ≤ Fintype.card Ω) :
    truncatedExpectedAttempts
      ((R.card : ℚ) / (Fintype.card Ω : ℚ)) t ≤ 2 := by
  apply truncatedExpectedAttempts_le_two
  · positivity
  · have hcard : (0 : ℚ) < Fintype.card Ω := by exact_mod_cast hne
    have hhalfQ : 2 * (R.card : ℚ) ≤ (Fintype.card Ω : ℚ) := by
      exact_mod_cast hhalf
    have hratio : (R.card : ℚ) / (Fintype.card Ω : ℚ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hcard]
      nlinarith
    nlinarith

/-- The initial selector is the generic first-passing search for its actual
exception-cap acceptance predicate. -/
lemma chooseInitialAttempt_eq_firstPassing
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r : ℕ}
    (attempts : List (InitialChoice A B N r)) (threshold cap : ℕ) :
    chooseInitialAttempt attempts threshold cap =
      firstPassing (fun attempt =>
        decide ((attempt.exceptions threshold).card ≤ cap)) attempts := by
  induction attempts with
  | nil => rfl
  | cons attempt rest ih =>
      by_cases hcap : (attempt.exceptions threshold).card ≤ cap <;>
        simp [chooseInitialAttempt, firstPassing, hcap, ih]

/-- The initial selector fails exactly when every supplied attempt exceeds its
acceptance cap. This identifies the concrete code-level rejection predicate. -/
lemma chooseInitialAttempt_eq_none_iff
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r : ℕ}
    (attempts : List (InitialChoice A B N r)) (threshold cap : ℕ) :
    chooseInitialAttempt attempts threshold cap = none ↔
      ∀ attempt ∈ attempts, cap < (attempt.exceptions threshold).card := by
  induction attempts with
  | nil => simp [chooseInitialAttempt]
  | cons attempt rest ih =>
      by_cases hcap : (attempt.exceptions threshold).card ≤ cap
      · simp [chooseInitialAttempt, hcap]
      · simp [chooseInitialAttempt, hcap, ih]
        omega

/-- The local selector is the generic first-passing search for the concrete
Boolean isolation check, with a successful trial converted to its draw set. -/
lemma firstIsolatingTrial_eq_firstPassing
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (N : β → Finset α) (B : Finset β) (W : Finset α) (b : β)
    {X : Finset α} {s : ℕ} (trials : List (LocalTrial X s)) :
    firstIsolatingTrial N B W b X s trials =
      (firstPassing (fun trial =>
        localTrialIsolatesB N B W b trial.draws) trials).map
          (fun trial => trial.draws.toFinset) := by
  induction trials with
  | nil => rfl
  | cons trial rest ih =>
      by_cases hok : localTrialIsolatesB N B W b trial.draws = true <;>
        simp [firstIsolatingTrial, firstPassing, hok, ih]

/-- The local selector fails exactly when every supplied trial fails its
executable isolation check. -/
lemma firstIsolatingTrial_eq_none_iff
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (N : β → Finset α) (B : Finset β) (W : Finset α) (b : β)
    (X : Finset α) (s : ℕ) (trials : List (LocalTrial X s)) :
    firstIsolatingTrial N B W b X s trials = none ↔
      ∀ trial ∈ trials, localTrialIsolatesB N B W b trial.draws = false := by
  induction trials with
  | nil => simp [firstIsolatingTrial]
  | cons trial rest ih =>
      by_cases hok : localTrialIsolatesB N B W b trial.draws = true
      · simp [firstIsolatingTrial, hok]
      · simp [firstIsolatingTrial, hok, ih]

/-- A finite tape determines a concrete list of initial attempts by a supplied
outcome decoder. The selector fails exactly when every decoded attempt fails
its actual exception-cap check. -/
lemma initialTape_selector_failure_iff
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r t : ℕ}
    (decode : Ω → InitialChoice A B N r) (tape : Tape Ω t)
    (threshold cap : ℕ) :
    chooseInitialAttempt (List.ofFn fun i : Fin t => decode (tape i))
      threshold cap = none ↔
      ∀ i, cap < ((decode (tape i)).exceptions threshold).card := by
  rw [chooseInitialAttempt_eq_none_iff]
  simp

/-- A finite tape determines a concrete list of local trials by a supplied
outcome decoder. Failure is precisely the conjunction of the code's local
isolation checks on those outcomes. -/
lemma localTape_selector_failure_iff
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {X : Finset α} {s t : ℕ}
    (decode : Ω → LocalTrial X s) (tape : Tape Ω t)
    (N : β → Finset α) (B : Finset β) (W : Finset α) (b : β) :
    firstIsolatingTrial N B W b X s
      (List.ofFn fun i : Fin t => decode (tape i)) = none ↔
      ∀ i, localTrialIsolatesB N B W b (decode (tape i)).draws = false := by
  rw [firstIsolatingTrial_eq_none_iff]
  simp

/-- Initial-attempt outcomes rejected by the actual exception-cap test. -/
def initialRejectedOutcomes
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r : ℕ}
    (decode : Ω → InitialChoice A B N r) (threshold cap : ℕ) : Finset Ω :=
  Finset.univ.filter fun ω =>
    cap < ((decode ω).exceptions threshold).card

/-- The finite tapes on which the concrete initial selector returns `none`. -/
def initialFailureTapes
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r t : ℕ}
    (decode : Ω → InitialChoice A B N r) (threshold cap : ℕ) :
    Finset (Tape Ω t) :=
  Finset.univ.filter fun tape =>
    chooseInitialAttempt (List.ofFn fun i : Fin t => decode (tape i))
      threshold cap = none

/-- The initial selector's failure tapes are exactly the all-rejected tapes
for its own exception-cap predicate; hence their exact count is the rejection
set size raised to the number of independent attempts. -/
lemma card_initialFailureTapes
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r t : ℕ}
    (decode : Ω → InitialChoice A B N r) (threshold cap : ℕ) :
    (initialFailureTapes (t := t) decode threshold cap).card =
      (initialRejectedOutcomes decode threshold cap).card ^ t := by
  have heq : initialFailureTapes (t := t) decode threshold cap =
      allBadTapes (initialRejectedOutcomes decode threshold cap) t := by
    ext tape
    simp only [initialFailureTapes, initialRejectedOutcomes, allBadTapes,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [initialTape_selector_failure_iff]
  rw [heq, card_allBadTapes]

/-- Local-trial outcomes rejected by the actual executable isolation check. -/
def localRejectedOutcomes
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {X : Finset α} {s : ℕ}
    (decode : Ω → LocalTrial X s) (N : β → Finset α)
    (B : Finset β) (W : Finset α) (b : β) : Finset Ω :=
  Finset.univ.filter fun ω =>
    localTrialIsolatesB N B W b (decode ω).draws = false

/-- The finite tapes on which the concrete local selector returns `none`. -/
def localFailureTapes
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {X : Finset α} {s t : ℕ}
    (decode : Ω → LocalTrial X s) (N : β → Finset α)
    (B : Finset β) (W : Finset α) (b : β) : Finset (Tape Ω t) :=
  Finset.univ.filter fun tape =>
    firstIsolatingTrial N B W b X s
      (List.ofFn fun i : Fin t => decode (tape i)) = none

/-- The local selector's failure tapes are exactly the all-rejected tapes for
its own Boolean isolation check, giving the exact retry count. -/
lemma card_localFailureTapes
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {X : Finset α} {s t : ℕ}
    (decode : Ω → LocalTrial X s) (N : β → Finset α)
    (B : Finset β) (W : Finset α) (b : β) :
    (localFailureTapes (t := t) decode N B W b).card =
      (localRejectedOutcomes decode N B W b).card ^ t := by
  have heq : localFailureTapes (t := t) decode N B W b =
      allBadTapes (localRejectedOutcomes decode N B W b) t := by
    ext tape
    simp only [localFailureTapes, localRejectedOutcomes, allBadTapes,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [localTape_selector_failure_iff]
  rw [heq, card_allBadTapes]

/-- If the initial selector's exception-cap rejection set has size at most
half of its finite attempt space, the exact number of failing `t`-tapes is at
most a `2^t` fraction of all tapes. -/
lemma initialFailure_tape_count_le
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r t : ℕ}
    (decode : Ω → InitialChoice A B N r) (threshold cap : ℕ)
    (hhalf : 2 * (initialRejectedOutcomes decode threshold cap).card ≤
      Fintype.card Ω) :
    2 ^ t * (initialFailureTapes (t := t) decode threshold cap).card ≤
      Fintype.card (Tape Ω t) := by
  rw [card_initialFailureTapes]
  simpa [card_allBadTapes] using allBad_tape_count_le
    (initialRejectedOutcomes decode threshold cap) t hhalf

/-- If the local selector's executable isolation check rejects at most half of
a finite attempt space, its exact `t`-retry failure count is bounded by `2^t`.
The geometric premise about the rejection set remains separate. -/
lemma localFailure_tape_count_le
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {X : Finset α} {s t : ℕ}
    (decode : Ω → LocalTrial X s) (N : β → Finset α)
    (B : Finset β) (W : Finset α) (b : β)
    (hhalf : 2 * (localRejectedOutcomes decode N B W b).card ≤
      Fintype.card Ω) :
    2 ^ t * (localFailureTapes (t := t) decode N B W b).card ≤
      Fintype.card (Tape Ω t) := by
  rw [card_localFailureTapes]
  simpa [card_allBadTapes] using
    allBad_tape_count_le (localRejectedOutcomes decode N B W b) t hhalf

/-- The finite-uniform expected retry count for the concrete initial selector
is at most two whenever its exception-cap rejection set occupies at most half
the attempt space. -/
lemma initialFailure_expected_attempts_le_two
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r t : ℕ}
    (decode : Ω → InitialChoice A B N r) (threshold cap : ℕ)
    (hne : 0 < Fintype.card Ω)
    (hhalf : 2 * (initialRejectedOutcomes decode threshold cap).card ≤
      Fintype.card Ω) :
    truncatedExpectedAttempts
      ((initialRejectedOutcomes decode threshold cap).card / Fintype.card Ω) t ≤ 2 := by
  exact finiteUniform_truncatedExpectedAttempts_le_two
    (initialRejectedOutcomes decode threshold cap) t hne hhalf

/-- The finite-uniform expected retry count for the concrete local selector
is at most two whenever its executable isolation check rejects at most half of
the attempt space. -/
lemma localFailure_expected_attempts_le_two
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {X : Finset α} {s : ℕ}
    (decode : Ω → LocalTrial X s) (N : β → Finset α)
    (B : Finset β) (W : Finset α) (b : β) (t : ℕ)
    (hne : 0 < Fintype.card Ω)
    (hhalf : 2 * (localRejectedOutcomes decode N B W b).card ≤
      Fintype.card Ω) :
    truncatedExpectedAttempts
      ((localRejectedOutcomes decode N B W b).card / Fintype.card Ω) t ≤ 2 := by
  exact finiteUniform_truncatedExpectedAttempts_le_two
    (localRejectedOutcomes decode N B W b) t hne hhalf

/-- The actual uniform-tape expectation of attempts inspected by the initial
selector is at most two whenever its exception-cap test rejects at most half
of the finite outcome space. -/
lemma initialActualFiniteMeanAttempts_le_two
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r t : ℕ}
    (decode : Ω → InitialChoice A B N r) (threshold cap : ℕ)
    (hne : 0 < Fintype.card Ω)
    (hhalf : 2 * (initialRejectedOutcomes decode threshold cap).card ≤
      Fintype.card Ω) :
    actualFiniteMeanAttempts
      (initialRejectedOutcomes decode threshold cap) t ≤ 2 := by
  exact actualFiniteMeanAttempts_le_two
    (initialRejectedOutcomes decode threshold cap) t hne hhalf

/-- The actual uniform-tape expectation of attempts inspected by the local
selector is at most two whenever its executable isolation check rejects at
most half of the finite outcome space. -/
lemma localActualFiniteMeanAttempts_le_two
    {Ω α β : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq α] [DecidableEq β]
    {X : Finset α} {s t : ℕ}
    (decode : Ω → LocalTrial X s) (N : β → Finset α)
    (B : Finset β) (W : Finset α) (b : β)
    (hne : 0 < Fintype.card Ω)
    (hhalf : 2 * (localRejectedOutcomes decode N B W b).card ≤
      Fintype.card Ω) :
    actualFiniteMeanAttempts (localRejectedOutcomes decode N B W b) t ≤ 2 := by
  exact actualFiniteMeanAttempts_le_two
    (localRejectedOutcomes decode N B W b) t hne hhalf

/-- The initial exception set obeys the exact pointwise charging estimate:
each counted exception contributes more than `k/3` disagreement from its
representative. No bound on the sum of those disagreements is assumed. -/
lemma initialExceptions_distance_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r k : ℕ}
    (choice : InitialChoice A B N r) :
    k * (choice.exceptions k).card ≤
      3 * ∑ b ∈ B, disagreement N b (choice.representative b) := by
  classical
  let E := choice.exceptions k
  have hcharge (b : β) (hb : b ∈ E) :
      k ≤ 3 * disagreement N b (choice.representative b) := by
    have h := (Finset.mem_filter.mp hb).2
    exact Nat.le_of_lt h
  calc
    k * E.card = ∑ b ∈ E, k := by simp [mul_comm]
    _ ≤ ∑ b ∈ E, 3 * disagreement N b (choice.representative b) :=
      Finset.sum_le_sum fun b hb => hcharge b hb
    _ = 3 * ∑ b ∈ E, disagreement N b (choice.representative b) := by
      simp [Finset.mul_sum]
    _ ≤ 3 * ∑ b ∈ B, disagreement N b (choice.representative b) := by
      apply Nat.mul_le_mul_left
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end Lax457868Proofs.SamplerRetries
