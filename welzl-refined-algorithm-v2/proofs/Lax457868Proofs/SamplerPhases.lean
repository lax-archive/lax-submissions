import Mathlib.Tactic
import Lax457868.RefinedSample
import Lax457868Proofs.SamplerDistance

/-!
Finite deterministic phases for the refined sampler of Lemma 18. Randomness is
represented by supplied finite choices; the probability law and machine
implementation are separate layers.
-/

namespace Lax457868Proofs.SamplerPhases

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

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
lemma InitialChoice.representative_eq_iff_same_trace
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
lemma chooseInitialAttempt_sound {A : Finset α} {B : Finset β}
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
def splitsExceptionPairB (N : β → Finset α) (E : Finset β)
    (W : Finset α) (a : α) : Bool :=
  decide ((E.filter fun b =>
    (E.filter fun b' => decide (trace N W b = trace N W b' ∧
      ((a ∈ N b ∧ a ∉ N b') ∨ (a ∉ N b ∧ a ∈ N b')))).Nonempty).Nonempty)

/-- The finite Boolean search succeeds exactly when an exception pair is split.
-/
lemma splitsExceptionPairB_eq_true_iff (N : β → Finset α) (E : Finset β)
    (W : Finset α) (a : α) :
    splitsExceptionPairB N E W a = true ↔ splitsExceptionPair N E W a := by
  simp [splitsExceptionPairB, splitsExceptionPair, Finset.Nonempty]

/-- One phase-two update: include the scanned vertex exactly when it splits an
equal-trace pair of current exceptions. -/
def phase2Step (N : β → Finset α) (E : Finset β)
    (W : Finset α) (a : α) : Finset α :=
  if splitsExceptionPairB N E W a then insert a W else W

/-- Scan a finite list of ground vertices from left to right, refining the
sample whenever the current exceptions contain a pair that the vertex splits.
-/
def phase2Scan (N : β → Finset α) (E : Finset β) :
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

/-- Executable finite check for phase-three isolation. -/
def localTrialIsolatesB (N : β → Finset α) (B : Finset β)
    (W : Finset α) (b : β) (draws : List α) : Bool :=
  decide (¬ (B.filter fun v => decide
    (trace N W b = trace N W v ∧ v ≠ b ∧
      trace N (W ∪ draws.toFinset) b = trace N (W ∪ draws.toFinset) v)).Nonempty)

/-- The finite Boolean check is equivalent to the local isolation predicate. -/
lemma localTrialIsolatesB_eq_true_iff (N : β → Finset α) (B : Finset β)
    (W : Finset α) (b : β) (draws : List α) :
    localTrialIsolatesB N B W b draws = true ↔
      localTrialIsolates N B W b draws := by
  simp [localTrialIsolatesB, localTrialIsolates, Finset.Nonempty]

/-- Find the first supplied trial that passes the phase-three isolation check.
Failure is explicit when all supplied trials fail. -/
def firstIsolatingTrial (N : β → Finset α) (B : Finset β)
    (W : Finset α) (b : β) (X : Finset α) (s : ℕ) :
    List (LocalTrial X s) → Option (Finset α)
  | [] => none
  | trial :: rest =>
      if localTrialIsolatesB N B W b trial.draws then
        some trial.draws.toFinset
      else firstIsolatingTrial N B W b X s rest

/-- Every returned local trial passed the stated phase-three isolation check.
-/
lemma firstIsolatingTrial_sound (N : β → Finset α) (B : Finset β)
    (W : Finset α) (b : β) (X : Finset α) (s : ℕ)
    (trials : List (LocalTrial X s)) (drawSet : Finset α)
    (h : firstIsolatingTrial N B W b X s trials = some drawSet) :
    ∃ trial ∈ trials, trial.draws.toFinset = drawSet ∧
      localTrialIsolates N B W b trial.draws := by
  induction trials with
  | nil => simp [firstIsolatingTrial] at h
  | cons trial rest ih =>
      by_cases hok : localTrialIsolatesB N B W b trial.draws = true
      · simp [firstIsolatingTrial, hok] at h
        cases h
        exact ⟨trial, by simp, rfl,
          (localTrialIsolatesB_eq_true_iff N B W b trial.draws).mp hok⟩
      · have hrest : firstIsolatingTrial N B W b X s rest = some drawSet := by
          simpa [firstIsolatingTrial, hok] using h
        obtain ⟨other, hother, heq, hiso⟩ := ih hrest
        exact ⟨other, by simp [hother], heq, hiso⟩

/-- Trace equality on a larger sample implies equality on a smaller sample. -/
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

/-- Trace inequality persists when the sample is enlarged. -/
lemma trace_ne_of_sample_subset (N : β → Finset α) {U V : Finset α}
    (hUV : U ⊆ V) (b b' : β)
    (h : trace N U b ≠ trace N U b') : trace N V b ≠ trace N V b' := by
  intro hV
  exact h (trace_eq_of_sample_subset N hUV b b' hV)

/-- Phase three repairs one exception when its distance from the initial
representative exceeds `2k/3`. Every attempted draw is supplied from the
relevant symmetric difference; only a trial that passes the local isolation
check is added. -/
def phase3Repair (N : β → Finset α) (B : Finset β)
    (phaseTwoW accumulator : Finset α) (b rep : β) (k s : ℕ)
    (trials : List (LocalTrial
      ((N b \ N rep) ∪ (N rep \ N b)) s)) : Option (Finset α) :=
  if 2 * k < 3 * disagreement N b rep then
    match firstIsolatingTrial N B phaseTwoW b
      ((N b \ N rep) ∪ (N rep \ N b)) s trials with
    | none => none
    | some drawSet => some (accumulator ∪ drawSet)
  else some accumulator

/-- A returned repair for a far exception separates it from every member of
its phase-two trace class. -/
lemma phase3Repair_sound (N : β → Finset α) (B : Finset β)
    (phaseTwoW accumulator W' : Finset α) (b rep : β) (k s : ℕ)
    (trials : List (LocalTrial
      ((N b \ N rep) ∪ (N rep \ N b)) s))
    (hfar : 2 * k < 3 * disagreement N b rep)
    (hbase : phaseTwoW ⊆ accumulator)
    (hret : phase3Repair N B phaseTwoW accumulator b rep k s trials = some W') :
    ∀ v ∈ B, trace N phaseTwoW b = trace N phaseTwoW v → v ≠ b →
      trace N W' b ≠ trace N W' v := by
  classical
  let X := (N b \ N rep) ∪ (N rep \ N b)
  cases htrial : firstIsolatingTrial N B phaseTwoW b X s trials with
  | none => simp [phase3Repair, hfar, X, htrial] at hret
  | some drawSet =>
      simp [phase3Repair, hfar, X, htrial] at hret
      cases hret
      obtain ⟨trial, _, hdraw, hisolate⟩ :=
        firstIsolatingTrial_sound N B phaseTwoW b X s trials drawSet htrial
      have hsubset : phaseTwoW ∪ trial.draws.toFinset ⊆ accumulator ∪ drawSet := by
        rw [hdraw]
        exact Finset.union_subset_union hbase (by intro x hx; exact hx)
      intro v hv htrace hvb
      exact trace_ne_of_sample_subset N hsubset b v (hisolate v hv htrace hvb)

/-- A successful local repair never removes the current accumulator. -/
lemma phase3Repair_extends (N : β → Finset α) (B : Finset β)
    (phaseTwoW accumulator result : Finset α) (b rep : β) (k s : ℕ)
    (trials : List (LocalTrial
      ((N b \ N rep) ∪ (N rep \ N b)) s))
    (hret : phase3Repair N B phaseTwoW accumulator b rep k s trials =
      some result) : accumulator ⊆ result := by
  by_cases hfar : 2 * k < 3 * disagreement N b rep
  · simp [phase3Repair, hfar] at hret
    cases htrial : firstIsolatingTrial N B phaseTwoW b
      ((N b \ N rep) ∪ (N rep \ N b)) s trials with
    | none => simp [htrial] at hret
    | some drawSet =>
        simp [htrial] at hret
        cases hret
        exact Finset.subset_union_left
  · simp [phase3Repair, hfar] at hret
    cases hret
    exact by intro x hx; exact hx

/-- Run local repairs in the supplied order of exceptions. Each exception has
its own finite list of legal length-`s` trials; exhaustion at a far exception
returns `none`. -/
def phase3Scan (N : β → Finset α) (B : Finset β)
    (representative : β → β) (k s : ℕ)
    (trials : ∀ b : β, List (LocalTrial
      ((N b \ N (representative b)) ∪
        (N (representative b) \ N b)) s)) :
    List β → Finset α → Finset α → Option (Finset α)
  | [], _, accumulator => some accumulator
  | b :: rest, phaseTwoW, accumulator =>
      match phase3Repair N B phaseTwoW accumulator b (representative b) k s (trials b) with
      | none => none
      | some W' => phase3Scan N B representative k s trials rest phaseTwoW W'

/-- A successful phase-three scan retains its phase-two sample and every
previously accumulated repair draw. -/
lemma phase3Scan_extends (N : β → Finset α) (B : Finset β)
    (representative : β → β) (k s : ℕ)
    (trials : ∀ b : β, List (LocalTrial
      ((N b \ N (representative b)) ∪
        (N (representative b) \ N b)) s)) :
    ∀ (order : List β) (phaseTwoW accumulator result : Finset α),
      phaseTwoW ⊆ accumulator →
      phase3Scan N B representative k s trials order phaseTwoW accumulator =
        some result → accumulator ⊆ result := by
  intro order
  induction order with
  | nil =>
      intro phaseTwoW accumulator result _ hret
      simp [phase3Scan] at hret
      cases hret
      exact by intro x hx; exact hx
  | cons b rest ih =>
      intro phaseTwoW accumulator result hbase hret
      cases hrep : phase3Repair N B phaseTwoW accumulator b
          (representative b) k s (trials b) with
      | none => simp [phase3Scan, hrep] at hret
      | some accumulator' =>
          have hret' : phase3Scan N B representative k s trials rest
              phaseTwoW accumulator' = some result := by
            simpa [phase3Scan, hrep] using hret
          have hacc : accumulator ⊆ accumulator' :=
            phase3Repair_extends N B phaseTwoW accumulator accumulator' b
              (representative b) k s (trials b) hrep
          exact hacc.trans (ih phaseTwoW accumulator' result
            (hbase.trans hacc) hret')

/-- Every far exception in the supplied phase-three order is isolated from its
fixed phase-two trace class in any returned sample. -/
lemma phase3Scan_far_isolated (N : β → Finset α) (B : Finset β)
    (representative : β → β) (k s : ℕ)
    (trials : ∀ b : β, List (LocalTrial
      ((N b \ N (representative b)) ∪
        (N (representative b) \ N b)) s)) :
    ∀ (order : List β) (phaseTwoW accumulator result : Finset α)
      (b : β), phaseTwoW ⊆ accumulator →
      phase3Scan N B representative k s trials order phaseTwoW accumulator =
        some result → b ∈ order →
      2 * k < 3 * disagreement N b (representative b) →
      ∀ v ∈ B, trace N phaseTwoW b = trace N phaseTwoW v → v ≠ b →
        trace N result b ≠ trace N result v := by
  intro order
  induction order with
  | nil => simp
  | cons head rest ih =>
      intro phaseTwoW accumulator result b hbase hret hb hfar
      cases hrep : phase3Repair N B phaseTwoW accumulator head
          (representative head) k s (trials head) with
      | none => simp [phase3Scan, hrep] at hret
      | some accumulator' =>
          have hret' : phase3Scan N B representative k s trials rest
              phaseTwoW accumulator' = some result := by
            simpa [phase3Scan, hrep] using hret
          have hacc : accumulator ⊆ accumulator' :=
            phase3Repair_extends N B phaseTwoW accumulator accumulator' head
              (representative head) k s (trials head) hrep
          have hbase' : phaseTwoW ⊆ accumulator' := hbase.trans hacc
          rcases List.mem_cons.mp hb with hbh | hbr
          · subst head
            have hnow := phase3Repair_sound N B phaseTwoW accumulator accumulator'
              b (representative b) k s (trials b) hfar hbase hrep
            have hfinal : accumulator' ⊆ result :=
              phase3Scan_extends N B representative k s trials rest
                phaseTwoW accumulator' result hbase' hret'
            intro v hv htrace hvb
            exact trace_ne_of_sample_subset N hfinal b v
              (hnow v hv htrace hvb)
          · exact ih phaseTwoW accumulator' result b hbase' hret' hbr hfar

/-- Execute the three finite phases from explicit initial attempts and local
trial lists. The result is `none` exactly when the supplied initial attempts
or a required local-repair list are exhausted. -/
def runThreePhases (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r cap k s : ℕ)
    (initialAttempts : List (InitialChoice A B N r))
    (groundOrder : List α) (_groundOrder_finset : groundOrder.toFinset = A)
    (_groundOrder_nodup : groundOrder.Nodup)
    (repairTrials : ∀ choice : InitialChoice A B N r, ∀ b : β,
      List (LocalTrial
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)) s))
    (exceptionOrder : ∀ choice : InitialChoice A B N r, List β)
    (_exceptionOrder_finset : ∀ choice,
      (exceptionOrder choice).toFinset = choice.exceptions k)
    (_exceptionOrder_nodup : ∀ choice, (exceptionOrder choice).Nodup) :
    Option (Finset α) :=
  match chooseInitialAttempt initialAttempts k cap with
  | none => none
  | some choice =>
      let E := choice.exceptions k
      let W₂ := phase2Scan N E groundOrder choice.sample
      phase3Scan N B choice.representative k s (repairTrials choice)
        (exceptionOrder choice) W₂ W₂

/-- The full finite-choice algorithm includes Lemma 18's immediate-output
branches. When the ground set already has at most `k` elements, or there are
no vertices to distinguish, the empty sample is returned. Otherwise the
three nontrivial phases are run on the supplied legal finite choices. -/
def refinedSampler (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r cap k s : ℕ)
    (initialAttempts : List (InitialChoice A B N r))
    (groundOrder : List α) (_groundOrder_finset : groundOrder.toFinset = A)
    (_groundOrder_nodup : groundOrder.Nodup)
    (repairTrials : ∀ choice : InitialChoice A B N r, ∀ b : β,
      List (LocalTrial
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)) s))
    (exceptionOrder : ∀ choice : InitialChoice A B N r, List β)
    (_exceptionOrder_finset : ∀ choice,
      (exceptionOrder choice).toFinset = choice.exceptions k)
    (_exceptionOrder_nodup : ∀ choice, (exceptionOrder choice).Nodup) :
    Option (Finset α) :=
  if A.card ≤ k ∨ B = ∅ then some ∅
  else runThreePhases A B N r cap k s initialAttempts groundOrder
    _groundOrder_finset _groundOrder_nodup repairTrials exceptionOrder
    _exceptionOrder_finset _exceptionOrder_nodup


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

/-- A scan over a list separates any two exceptions whose distinct
neighborhoods are contained in the scanned ground set. -/
lemma phase2Scan_separates
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
lemma phase2_separates_distinct_neighborhoods
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (as : List α) (has : as.toFinset = A) (_as_nodup : as.Nodup)
    (E : Finset β) (W : Finset α)
    (hN : ∀ b ∈ B, N b ⊆ A) (hE : E ⊆ B)
    (b b' : β) (hb : b ∈ E) (hb' : b' ∈ E)
    (hfinal : trace N (phase2Scan N E as W) b =
      trace N (phase2Scan N E as W) b') :
    N b = N b' := by
  classical
  have hagree := phase2Scan_separates N E b b' hb hb' as W hfinal
  ext a
  by_cases ha : a ∈ A
  · have h : a ∈ as.toFinset := by rw [has]; exact ha
    have h := hagree a h
    exact h
  · have hNb := hN b (hE hb)
    have hNb' := hN b' (hE hb')
    have : a ∉ N b ∧ a ∉ N b' := ⟨fun hn => ha (hNb hn), fun hn => ha (hNb' hn)⟩
    simp [this]

/-- A successful three-phase scan has pairwise `k`-close neighborhoods
whenever their final traces agree. -/
lemma phase3Scan_pairwise_correct
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r k s : ℕ) (choice : InitialChoice A B N r)
    (as : List α) (has : as.toFinset = A) (_as_nodup : as.Nodup)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (order : List β) (horder : order.toFinset = choice.exceptions k)
    (_order_nodup : order.Nodup)
    (trials : ∀ b : β, List (LocalTrial
      ((N b \ N (choice.representative b)) ∪
        (N (choice.representative b) \ N b)) s))
    (result : Finset α)
    (hret : phase3Scan N B choice.representative k s trials order
      (phase2Scan N (choice.exceptions k) as choice.sample)
      (phase2Scan N (choice.exceptions k) as choice.sample) = some result) :
    ∀ b ∈ B, ∀ b' ∈ B,
      trace N result b = trace N result b' →
        disagreement N b b' ≤ k := by
  classical
  let W₂ := phase2Scan N (choice.exceptions k) as choice.sample
  let E := choice.exceptions k
  have hsample : choice.sample ⊆ W₂ := phase2Scan_mono N E as choice.sample
  have hbase : W₂ ⊆ result :=
    phase3Scan_extends N B choice.representative k s trials order W₂ W₂
      result (by intro x hx; exact hx) hret
  intro b hb b' hb' htrace
  change SamplerDistance.disagreement (N b) (N b') ≤ k
  have htrace₂ : trace N W₂ b = trace N W₂ b' :=
    trace_eq_of_sample_subset N hbase b b' htrace
  have htrace₀ : trace N choice.sample b = trace N choice.sample b' :=
    trace_eq_of_sample_subset N hsample b b' htrace₂
  have hrep : choice.representative b = choice.representative b' :=
    (choice.representative_eq_iff_same_trace b b' hb hb').2 htrace₀
  have hfar_isolated (x : β) (hx : x ∈ E)
      (hfar : 2 * k < 3 * disagreement N x (choice.representative x)) :
      ∀ y ∈ B, trace N W₂ x = trace N W₂ y → y ≠ x →
        trace N result x ≠ trace N result y := by
    have hxorder : x ∈ order := by
      have hx' : x ∈ order.toFinset := by rw [horder]; exact hx
      exact List.mem_toFinset.mp hx'
    exact phase3Scan_far_isolated N B choice.representative k s trials
      order W₂ W₂ result x (by intro z hz; exact hz) hret hxorder hfar
  have hnonexc (x : β) (hx : x ∈ B) (hne : x ∉ E) :
      3 * disagreement N x (choice.representative x) ≤ k := by
    have hmem : ¬ k < 3 * disagreement N x (choice.representative x) := by
      intro h
      apply hne
      exact Finset.mem_filter.mpr ⟨hx, h⟩
    omega
  have hE : E ⊆ B := Finset.filter_subset _ _
  have hmild (x : β) (hx : x ∈ E)
      (hnotfar : ¬ 2 * k < 3 * disagreement N x (choice.representative x)) :
      3 * disagreement N x (choice.representative x) ≤ 2 * k := by omega
  by_cases hbE : b ∈ E <;> by_cases hb'E : b' ∈ E
  · have hNeq : N b = N b' :=
      phase2_separates_distinct_neighborhoods A B N as has _as_nodup E choice.sample hN hE
        b b' hbE hb'E (by simpa [W₂] using htrace₂)
    simpa [SamplerDistance.disagreement, disagreement, hNeq]
  · by_cases hfar : 2 * k < 3 * disagreement N b (choice.representative b)
    · have hvertex : b ≠ b' := by
        intro heq
        subst b'
        exact hb'E hbE
      have hsep := hfar_isolated b hbE hfar b' hb' htrace₂ (Ne.symm hvertex)
      exact False.elim (hsep htrace)
    · have hX0 := hmild b hbE hfar
      have hX : 3 * SamplerDistance.disagreement (N b) (N (choice.representative b)) ≤ 2 * k := by
        simpa [disagreement, SamplerDistance.disagreement] using hX0
      have hY0 := hnonexc b' hb' hb'E
      have hY : 3 * SamplerDistance.disagreement (N b') (N (choice.representative b)) ≤ k := by
        simpa [disagreement, SamplerDistance.disagreement, hrep] using hY0
      exact SamplerDistance.disagreement_le_of_mild_exception_bounds
        (N b) (N b') (N (choice.representative b)) k hX hY
  · by_cases hfar : 2 * k < 3 * disagreement N b' (choice.representative b')
    · have hvertex : b' ≠ b := by
        intro heq
        subst b'
        exact hbE hb'E
      have hsep := hfar_isolated b' hb'E hfar b hb htrace₂.symm (Ne.symm hvertex)
      exact False.elim (hsep htrace.symm)
    · have hX0 := hnonexc b hb hbE
      have hX : 3 * SamplerDistance.disagreement (N b) (N (choice.representative b)) ≤ k := by
        simpa [disagreement, SamplerDistance.disagreement] using hX0
      have hY0 := hmild b' hb'E hfar
      have hY : 3 * SamplerDistance.disagreement (N b') (N (choice.representative b)) ≤ 2 * k := by
        simpa [disagreement, SamplerDistance.disagreement, hrep] using hY0
      rw [SamplerDistance.disagreement_symm]
      exact SamplerDistance.disagreement_le_of_mild_exception_bounds
        (N b') (N b) (N (choice.representative b)) k hY hX
  · have hX0 := hnonexc b hb hbE
    have hX : 3 * SamplerDistance.disagreement (N b) (N (choice.representative b)) ≤ k := by
      simpa [disagreement, SamplerDistance.disagreement] using hX0
    have hY0 := hnonexc b' hb' hb'E
    have hY : 3 * SamplerDistance.disagreement (N b') (N (choice.representative b)) ≤ k := by
      simpa [disagreement, SamplerDistance.disagreement, hrep] using hY0
    exact SamplerDistance.disagreement_le_of_third_bounds
      (N b) (N b') (N (choice.representative b)) k hX hY

/-- The full finite-choice sampler, including the empty-sample branches, is
pairwise `k`-close on every successful run. -/
lemma refinedSampler_pairwise_correct
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r cap k s : ℕ) (initialAttempts : List (InitialChoice A B N r))
    (groundOrder : List α) (hground : groundOrder.toFinset = A)
    (hground_nodup : groundOrder.Nodup)
    (repairTrials : ∀ choice : InitialChoice A B N r, ∀ b : β,
      List (LocalTrial
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)) s))
    (exceptionOrder : ∀ choice : InitialChoice A B N r, List β)
    (hexceptions : ∀ choice,
      (exceptionOrder choice).toFinset = choice.exceptions k)
    (hexceptions_nodup : ∀ choice, (exceptionOrder choice).Nodup)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (result : Finset α)
    (hret : refinedSampler A B N r cap k s initialAttempts groundOrder hground
      hground_nodup repairTrials exceptionOrder hexceptions hexceptions_nodup =
        some result) :
    ∀ b ∈ B, ∀ b' ∈ B, trace N result b = trace N result b' →
      disagreement N b b' ≤ k := by
  classical
  by_cases hearly : A.card ≤ k ∨ B = ∅
  · have hresult : result = ∅ := by
      simpa [refinedSampler, hearly] using hret.symm
    subst result
    intro b hb b' hb' _
    rcases hearly with hsmall | hempty
    · apply Nat.le_trans ?_ hsmall
      apply Finset.card_le_card
      intro a ha
      rcases Finset.mem_union.mp ha with h | h
      · exact hN b hb (Finset.mem_sdiff.mp h).1
      · exact hN b' hb' (Finset.mem_sdiff.mp h).1
    · rw [hempty] at hb
      simp at hb
  · have hrun : runThreePhases A B N r cap k s initialAttempts groundOrder hground
        hground_nodup repairTrials exceptionOrder hexceptions hexceptions_nodup =
        some result := by
      simpa [refinedSampler, hearly] using hret
    cases hchoose : chooseInitialAttempt initialAttempts k cap with
    | none => simp [runThreePhases, hchoose] at hrun
    | some choice =>
        have hscan : phase3Scan N B choice.representative k s
            (repairTrials choice) (exceptionOrder choice)
            (phase2Scan N (choice.exceptions k) groundOrder choice.sample)
            (phase2Scan N (choice.exceptions k) groundOrder choice.sample) =
              some result := by
          simpa [runThreePhases, hchoose] using hrun
        exact phase3Scan_pairwise_correct A B N r k s choice groundOrder
          hground hground_nodup hN (exceptionOrder choice) (hexceptions choice)
          (hexceptions_nodup choice) (repairTrials choice) result hscan


end Lax457868Proofs.SamplerPhases
