import Mathlib.Tactic
import Lax457868.RefinedSample

/-!
Finite deterministic phases for the refined sampler of Lemma 18. Randomness is
represented by supplied finite choices; the probability law and machine
implementation are separate layers.
-/

namespace Lax457868Proofs.SamplerPhases

variable {α β : Type*} [DecidableEq α]

/-- The number of ground-set elements on which two neighborhoods disagree. -/
def disagreement (N : β → Finset α) (b b' : β) : ℕ :=
  ((N b \ N b') ∪ (N b' \ N b)).card

/-- The trace of a neighborhood on a finite sample. -/
def trace (N : β → Finset α) (W : Finset α) (b : β) : Finset α :=
  N b ∩ W

/-- The finite set of distinct traces represented by `B` on `W`. -/
def traceClasses (N : β → Finset α) (W : Finset α) (B : Finset β) :
    Finset (Finset α) :=
  B.image (trace N W)

/-- A supplied legal choice of initial draws and one representative for each
trace class. `representative_constant` says that equal-trace vertices receive
the same selected representative; it does not assert a sampler outcome. -/
structure InitialChoice (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ) where
  draws : List α
  draws_length : draws.length = r
  draws_mem : ∀ a ∈ draws, a ∈ A
  representative : β → β
  representative_mem : ∀ b ∈ B, representative b ∈ B
  representative_trace : ∀ b ∈ B,
    trace N draws.toFinset (representative b) = trace N draws.toFinset b
  representative_constant : ∀ b ∈ B, ∀ b' ∈ B,
    trace N draws.toFinset b = trace N draws.toFinset b' →
      representative b = representative b'

/-- The underlying set of the supplied initial draws. -/
def InitialChoice.sample {A : Finset α} {B : Finset β} {N : β → Finset α}
    {r : ℕ} (choice : InitialChoice A B N r) : Finset α :=
  choice.draws.toFinset

/-- The chosen representatives identify exactly the initial trace classes. -/
theorem InitialChoice.representative_eq_iff_same_trace
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r : ℕ}
    (choice : InitialChoice A B N r) (b b' : β)
    (hb : b ∈ B) (hb' : b' ∈ B) :
    choice.representative b = choice.representative b' ↔
      trace N choice.sample b = trace N choice.sample b' := by
  constructor
  · intro heq
    calc
      trace N choice.sample b = trace N choice.sample (choice.representative b) :=
        (choice.representative_trace b hb).symm
      _ = trace N choice.sample (choice.representative b') := by rw [heq]
      _ = trace N choice.sample b' := choice.representative_trace b' hb'
  · exact choice.representative_constant b hb b' hb'

/-- Vertices farther than the exceptional threshold from their chosen initial
representative. -/
def InitialChoice.exceptions {A : Finset α} {B : Finset β}
    {N : β → Finset α} {r : ℕ} (choice : InitialChoice A B N r)
    (threshold : ℕ) : Finset β :=
  B.filter fun b => threshold < 3 * disagreement N b (choice.representative b)

/-- Use the first supplied initial attempt whose exception count is within the
acceptance cap. Exhausting the finite attempt list returns `none`. -/
def chooseInitialAttempt {A : Finset α} {B : Finset β} {N : β → Finset α}
    {r : ℕ} (attempts : List (InitialChoice A B N r))
    (threshold cap : ℕ) : Option (InitialChoice A B N r) :=
  match attempts with
  | [] => none
  | attempt :: rest =>
      if (attempt.exceptions threshold).card ≤ cap then some attempt
      else chooseInitialAttempt rest threshold cap

/-- Any returned initial attempt passed the explicit exception-count check. -/
theorem chooseInitialAttempt_sound {A : Finset α} {B : Finset β}
    {N : β → Finset α} {r : ℕ}
    (attempts : List (InitialChoice A B N r)) (threshold cap : ℕ)
    (chosen : InitialChoice A B N r)
    (h : chooseInitialAttempt attempts threshold cap = some chosen) :
    (chosen.exceptions threshold).card ≤ cap := by
  induction attempts with
  | nil => simp [chooseInitialAttempt] at h
  | cons attempt rest ih =>
      by_cases hcap : (attempt.exceptions threshold).card ≤ cap
      · simp [chooseInitialAttempt, hcap] at h
        cases h
        exact hcap
      · have hrest : chooseInitialAttempt rest threshold cap = some chosen := by
          simpa [chooseInitialAttempt, hcap] using h
        exact ih hrest

/-- Whether adding `a` splits a pair of currently equal-trace exceptions. -/
def splitsExceptionPair (N : β → Finset α) (E : Finset β)
    (W : Finset α) (a : α) : Prop :=
  ∃ b b', b ∈ E ∧ b' ∈ E ∧ trace N W b = trace N W b' ∧
    ((a ∈ N b ∧ a ∉ N b') ∨ (a ∉ N b ∧ a ∈ N b'))

/-- Executable finite search for a pair split by `a`. -/
noncomputable def splitsExceptionPairB (N : β → Finset α) (E : Finset β)
    (W : Finset α) (a : α) : Bool :=
  E.toList.any fun b => E.toList.any fun b' =>
    decide (trace N W b = trace N W b' ∧
      ((a ∈ N b ∧ a ∉ N b') ∨ (a ∉ N b ∧ a ∈ N b')))

/-- The finite Boolean search succeeds exactly when an exception pair is split.
-/
lemma splitsExceptionPairB_eq_true_iff (N : β → Finset α) (E : Finset β)
    (W : Finset α) (a : α) :
    splitsExceptionPairB N E W a = true ↔ splitsExceptionPair N E W a := by
  simp [splitsExceptionPairB, splitsExceptionPair, List.any_eq_true]

/-- One phase-two update: include the scanned vertex exactly when it splits an
equal-trace pair of current exceptions. -/
noncomputable def phase2Step (N : β → Finset α) (E : Finset β)
    (W : Finset α) (a : α) : Finset α :=
  if splitsExceptionPairB N E W a then insert a W else W

/-- Scan a finite list of ground vertices from left to right, refining the
sample whenever the current exceptions contain a pair that the vertex splits.
-/
noncomputable def phase2Scan (N : β → Finset α) (E : Finset β) :
    List α → Finset α → Finset α
  | [], W => W
  | a :: rest, W => phase2Scan N E rest (phase2Step N E W a)

/-- A supplied length-`s` local-repair trial drawn from one symmetric
difference. -/
structure LocalTrial (X : Finset α) (s : ℕ) where
  draws : List α
  draws_length : draws.length = s
  draws_mem : ∀ a ∈ draws, a ∈ X

/-- A trial isolates `b` from every other vertex that shared its phase-two
trace. -/
def localTrialIsolates (N : β → Finset α) (B : Finset β)
    (W : Finset α) (b : β) (draws : List α) : Prop :=
  ∀ v ∈ B, trace N W b = trace N W v → v ≠ b →
    trace N (W ∪ draws.toFinset) b ≠ trace N (W ∪ draws.toFinset) v

/-- Find the first supplied trial that passes the phase-three isolation check.
Failure is explicit when all supplied trials fail. -/
noncomputable def firstIsolatingTrial (N : β → Finset α) (B : Finset β)
    (W : Finset α) (b : β) (X : Finset α) (s : ℕ) :
    List (LocalTrial X s) → Option (Finset α)
  | [] => none
  | trial :: rest => by
      classical
      exact if localTrialIsolates N B W b trial.draws then
        some trial.draws.toFinset
      else firstIsolatingTrial N B W b X s rest

/-- Every returned local trial passed the stated phase-three isolation check.
-/
theorem firstIsolatingTrial_sound (N : β → Finset α) (B : Finset β)
    (W : Finset α) (b : β) (X : Finset α) (s : ℕ)
    (trials : List (LocalTrial X s)) (drawSet : Finset α)
    (h : firstIsolatingTrial N B W b X s trials = some drawSet) :
    ∃ trial ∈ trials, trial.draws.toFinset = drawSet ∧
      localTrialIsolates N B W b trial.draws := by
  classical
  induction trials with
  | nil => simp [firstIsolatingTrial] at h
  | cons trial rest ih =>
      by_cases hok : localTrialIsolates N B W b trial.draws
      · simp [firstIsolatingTrial, hok] at h
        cases h
        exact ⟨trial, by simp, rfl, hok⟩
      · have hrest : firstIsolatingTrial N B W b X s rest = some drawSet := by
          simpa [firstIsolatingTrial, hok] using h
        obtain ⟨other, hother, heq, hiso⟩ := ih hrest
        exact ⟨other, by simp [hother], heq, hiso⟩

/-- Phase three repairs one exception when its distance from the initial
representative exceeds `2k/3`. Every attempted draw is supplied from the
relevant symmetric difference; only a trial that passes the local isolation
check is added. -/
noncomputable def phase3Repair (N : β → Finset α) (B : Finset β)
    (W : Finset α) (b rep : β) (k s : ℕ)
    (trials : List (LocalTrial
      ((N b \ N rep) ∪ (N rep \ N b)) s)) : Option (Finset α) :=
  if 2 * k < 3 * disagreement N b rep then
    match firstIsolatingTrial N B W b
      ((N b \ N rep) ∪ (N rep \ N b)) s trials with
    | none => none
    | some drawSet => some (W ∪ drawSet)
  else some W

/-- A returned repair for a far exception separates it from every member of
its phase-two trace class. -/
theorem phase3Repair_sound (N : β → Finset α) (B : Finset β)
    (W W' : Finset α) (b rep : β) (k s : ℕ)
    (trials : List (LocalTrial
      ((N b \ N rep) ∪ (N rep \ N b)) s))
    (hfar : 2 * k < 3 * disagreement N b rep)
    (hret : phase3Repair N B W b rep k s trials = some W') :
    ∀ v ∈ B, trace N W b = trace N W v → v ≠ b →
      trace N W' b ≠ trace N W' v := by
  classical
  let X := (N b \ N rep) ∪ (N rep \ N b)
  cases htrial : firstIsolatingTrial N B W b X s trials with
  | none => simp [phase3Repair, hfar, X, htrial] at hret
  | some drawSet =>
      simp [phase3Repair, hfar, X, htrial] at hret
      cases hret
      obtain ⟨trial, _, hdraw, hisolate⟩ :=
        firstIsolatingTrial_sound N B W b X s trials drawSet htrial
      intro v hv htrace hvb
      simpa [hdraw] using hisolate v hv htrace hvb

/-- Run local repairs in the supplied order of exceptions. Each exception has
its own finite list of legal length-`s` trials; exhaustion at a far exception
returns `none`. -/
noncomputable def phase3Scan (N : β → Finset α) (B : Finset β)
    (representative : β → β) (k s : ℕ)
    (trials : ∀ b : β, List (LocalTrial
      ((N b \ N (representative b)) ∪
        (N (representative b) \ N b)) s)) :
    List β → Finset α → Option (Finset α)
  | [], W => some W
  | b :: rest, W =>
      match phase3Repair N B W b (representative b) k s (trials b) with
      | none => none
      | some W' => phase3Scan N B representative k s trials rest W'

/-- Execute the three finite phases from explicit initial attempts and local
trial lists. The result is `none` exactly when the supplied initial attempts
or a required local-repair list are exhausted. -/
noncomputable def runThreePhases (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r threshold cap k s : ℕ)
    (initialAttempts : List (InitialChoice A B N r))
    (repairTrials : ∀ choice : InitialChoice A B N r, ∀ b : β,
      List (LocalTrial
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)) s)) :
    Option (Finset α) :=
  match chooseInitialAttempt initialAttempts threshold cap with
  | none => none
  | some choice =>
      let E := choice.exceptions threshold
      let W₂ := phase2Scan N E A.toList choice.sample
      phase3Scan N B choice.representative k s (repairTrials choice)
        E.toList W₂

/-- The phase-two scan never removes a previously sampled vertex. -/
lemma phase2Scan_mono (N : β → Finset α) (E : Finset β)
    (as : List α) (W : Finset α) : W ⊆ phase2Scan N E as W := by
  induction as generalizing W with
  | nil => simp [phase2Scan]
  | cons a rest ih =>
      calc
        W ⊆ phase2Step N E W a := by
          by_cases hs : splitsExceptionPairB N E W a = true
          · simp [phase2Step, hs]
          · simp [phase2Step, hs]
        _ ⊆ phase2Scan N E rest (phase2Step N E W a) := ih _

/-- Trace equality descends to any smaller sample. -/
lemma trace_eq_of_sample_subset (N : β → Finset α) {U V : Finset α}
    (hUV : U ⊆ V) (b b' : β)
    (h : trace N V b = trace N V b') : trace N U b = trace N U b' := by
  ext a
  have hmem := congrArg (fun T : Finset α => a ∈ T) h
  simp only [trace, Finset.mem_inter] at hmem ⊢
  constructor
  · rintro ⟨hab, haU⟩
    exact ⟨(hmem.mp ⟨hab, hUV haU⟩).1, haU⟩
  · rintro ⟨hab', haU⟩
    exact ⟨(hmem.mpr ⟨hab', hUV haU⟩).1, haU⟩

/-- A scan over a list separates any two exceptions whose distinct
neighborhoods are contained in the scanned ground set. -/
theorem phase2Scan_separates
    (N : β → Finset α) (E : Finset β) (b b' : β)
    (hb : b ∈ E) (hb' : b' ∈ E) :
    ∀ (as : List α) (W : Finset α),
      trace N (phase2Scan N E as W) b =
        trace N (phase2Scan N E as W) b' →
      ∀ a ∈ as.toFinset, (a ∈ N b ↔ a ∈ N b') := by
  classical
  intro as
  induction as with
  | nil =>
      intro W _ a ha
      simp at ha
  | cons a rest ih =>
      intro W hfinal x hx
      let W₁ := phase2Step N E W a
      have htail : trace N (phase2Scan N E rest W₁) b =
          trace N (phase2Scan N E rest W₁) b' := hfinal
      have hW₁sub : W₁ ⊆ phase2Scan N E rest W₁ :=
        phase2Scan_mono N E rest W₁
      have hW₁ : trace N W₁ b = trace N W₁ b' :=
        trace_eq_of_sample_subset N hW₁sub b b' htail
      have hWsub : W ⊆ W₁ := by
        by_cases hs : splitsExceptionPairB N E W a = true
        · simp [W₁, phase2Step, hs]
        · simp [W₁, phase2Step, hs]
      have hW : trace N W b = trace N W b' :=
        trace_eq_of_sample_subset N hWsub b b' hW₁
      have ha_same : (a ∈ N b ↔ a ∈ N b') := by
        by_contra h
        have hsplit : (a ∈ N b ∧ a ∉ N b') ∨ (a ∉ N b ∧ a ∈ N b') := by
          tauto
        have hs : splitsExceptionPair N E W a := ⟨b, b', hb, hb', hW, hsplit⟩
        have hsB : splitsExceptionPairB N E W a = true :=
          splitsExceptionPairB_eq_true_iff N E W a |>.2 hs
        have haW₁ : a ∈ W₁ := by simp [W₁, phase2Step, hsB]
        have hmem := congrArg (fun T : Finset α => a ∈ T) hW₁
        have hEq : (a ∈ N b ↔ a ∈ N b') := by
          simpa [trace, haW₁] using hmem
        have : False := by rcases hsplit with hs | hs <;> simp_all
        exact this.elim
      have hxcons : x = a ∨ x ∈ rest := by simpa using hx
      rcases hxcons with rfl | hxrest
      · exact ha_same
      · exact ih W₁ htail x (List.mem_toFinset.mpr hxrest)

/-- After the complete ground-set scan, two exceptional vertices with
identical traces have identical full neighborhoods. -/
theorem phase2_separates_distinct_neighborhoods
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (E : Finset β) (W : Finset α)
    (hN : ∀ b ∈ B, N b ⊆ A) (hE : E ⊆ B)
    (b b' : β) (hb : b ∈ E) (hb' : b' ∈ E)
    (hfinal : trace N (phase2Scan N E A.toList W) b =
      trace N (phase2Scan N E A.toList W) b') :
    N b = N b' := by
  classical
  have hagree := phase2Scan_separates N E b b' hb hb' A.toList W hfinal
  ext a
  by_cases ha : a ∈ A
  · have h := hagree a (by simpa using ha)
    exact h
  · have hNb := hN b (hE hb)
    have hNb' := hN b' (hE hb')
    have : a ∉ N b ∧ a ∉ N b' := ⟨fun hn => ha (hNb hn), fun hn => ha (hNb' hn)⟩
    simp [this]

end Lax457868Proofs.SamplerPhases
