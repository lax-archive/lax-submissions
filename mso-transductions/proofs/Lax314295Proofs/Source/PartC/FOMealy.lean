/-
First-order definable Mealy machines, and the implication
"aperiodic dfa ⇒ first-order definable" of Theorem `thm:logic-aperiodic` of *Transducers*
(M. Bojańczyk).

The book's argument: a language recognised by an aperiodic dfa is computed by an
aperiodic Mealy machine, which by the aperiodic Krohn-Rhodes Theorem `thm:aperiodic-mealy` is a
composition of flip-flops; flip-flop machines are first-order definable, and
first-order definable Mealy machines are closed under composition, by
substitution of formulas.  Here the passage through Theorem `thm:aperiodic-mealy` is direct:
the Mealy machine attached to the dfa has the transition function of the dfa,
so the aperiodicity hypothesis is literally the hypothesis
`Mealy.TransStabilises` of `Transducers.krohn_rhodes_flipFlop`.

A machine is *first-order definable* (`FODefMealy`) when, for every output
letter `b`, the language of inputs whose output ends with `b` is first-order
definable.  Besides that, the definition records the two properties that make
the substitution argument work: the function is length preserving and the
`n`-th output letter depends only on the first `n` input letters
(`PrefixDetermined`), both of which hold for every Mealy machine.

For the flip-flop case, each letter either does not change the state or resets
it to a fixed state, so the state reached after the positions before `x` is the
target of the last resetting letter before `x`, and the initial state if there
is none (`Transducers.Mealy.trans_take_eq_iff`); this is expressed by a
first-order formula, using finite disjunctions over the (finitely many) letters
of the input alphabet and states of the machine.  The last output letter is then
read off from the state before the last position and from the letter there.
-/
import Lax314295Proofs.Source.PartC.FOSubstRel
import Lax314295Proofs.Source.PartC.FOFlipFlop
import Lax765601Proofs.Source.PartA.Statements
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

open MSO

variable {A B C : Type}

/-! ## Mealy machines are length preserving and prefix determined -/

lemma Mealy.eval_take {Q : Type} (M : Mealy A B Q) (w : List A) (n : ℕ) :
    (M.eval w).take n = M.eval (w.take n) := by
  by_cases hn : n ≤ w.length
  · conv_lhs => rw [← List.take_append_drop n w]
    rw [M.eval_append, List.take_append]
    have hlen : (M.eval (w.take n)).length = n := by
      rw [M.eval_length, List.length_take]
      omega
    rw [hlen, Nat.sub_self, List.take_zero, List.append_nil,
      List.take_of_length_le (le_of_eq hlen)]
  · rw [List.take_of_length_le (by rw [M.eval_length]; omega),
      List.take_of_length_le (by omega)]

/-- Every Mealy machine is prefix determined. -/
lemma Mealy.prefixDetermined {Q : Type} (M : Mealy A B Q) : PrefixDetermined M.eval := by
  intro w v n h
  rw [Mealy.eval_take M, Mealy.eval_take M, h]

/-! ## First-order definable Mealy machines -/

/-- A string-to-string function is a *first-order definable Mealy machine* if it
is length preserving, its `n`-th output letter depends only on the first `n`
input letters, and, for every output letter `b`, the language of inputs whose
output ends with `b` is first-order definable. -/
def FODefMealy (f : List A → List B) : Prop :=
  LengthPreserving f ∧ PrefixDetermined f ∧
    ∀ b : B, FODefinable {w : List A | (f w).getLast? = some b}

/-- The letter produced at a position, in terms of the languages of a
first-order definable Mealy machine. -/
lemma FODefMealy.getElem?_eq {f : List A → List B} (hlen : LengthPreserving f)
    (hpd : PrefixDetermined f) (w : List A) (p : ℕ) (hp : p < w.length) (b : B) :
    (f w)[p]? = some b ↔ (f (w.take (p + 1))).getLast? = some b := by
  have hlen' : (f (w.take (p + 1))).length = p + 1 := by
    rw [hlen, List.length_take]
    omega
  have htake : (f w).take (p + 1) = f (w.take (p + 1)) := by
    have h := hpd w (w.take (p + 1)) (p + 1) (by simp)
    rw [h, List.take_of_length_le (le_of_eq hlen')]
  have hlast : (f (w.take (p + 1))).getLast? = (f (w.take (p + 1)))[p]? := by
    rw [List.getLast?_eq_getElem?, hlen']
    norm_num
  rw [hlast, ← htake, List.getElem?_take_of_lt (Nat.lt_succ_self p)]

/-! ## The last position of a string -/

/-- The formula saying that the variable `x₀` is the last position and carries
the letter `b`. -/
def lastLab (b : A) : MSO A :=
  MSO.exFO 0 (MSO.and (MSO.lab b 0) (MSO.not (MSO.exFO 1 (MSO.not (MSO.le 1 0)))))

lemma isFO_lastLab (b : A) : (lastLab b).IsFO := ⟨trivial, trivial⟩

lemma sat_lastLab (b : A) (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (lastLab b) ↔ w.getLast? = some b := by
  constructor
  · rintro ⟨p, hp, hlab, hlast⟩
    have hlab' : w[p]? = some b := by
      have : w[Function.update fo 0 p 0]? = some b := hlab
      rwa [Function.update_self] at this
    have hmax : ∀ q, q < w.length → q ≤ p := by
      intro q hq
      by_contra hlt
      refine hlast ⟨q, hq, ?_⟩
      show ¬ (Function.update (Function.update fo 0 p) 1 q 1
        ≤ Function.update (Function.update fo 0 p) 1 q 0)
      rw [Function.update_self, Function.update_of_ne (by omega), Function.update_self]
      omega
    have hpe : p = w.length - 1 := by
      have := hmax (w.length - 1) (by omega)
      omega
    rw [List.getLast?_eq_getElem?, ← hpe]
    exact hlab'
  · intro hlast
    have hne : w ≠ [] := by
      intro h
      rw [h] at hlast
      simp at hlast
    have hpos : 0 < w.length := by
      cases w with
      | nil => exact absurd rfl hne
      | cons a u => simp
    refine ⟨w.length - 1, by omega, ?_, ?_⟩
    · show w[Function.update fo 0 (w.length - 1) 0]? = some b
      rw [Function.update_self, ← List.getLast?_eq_getElem?]
      exact hlast
    · rintro ⟨q, hq, hqlt⟩
      have : ¬ (Function.update (Function.update fo 0 (w.length - 1)) 1 q 1
          ≤ Function.update (Function.update fo 0 (w.length - 1)) 1 q 0) := hqlt
      rw [Function.update_self, Function.update_of_ne (by omega), Function.update_self] at this
      omega

/-- The identity is a first-order definable Mealy machine. -/
lemma foDefMealy_id : FODefMealy (id : List A → List A) := by
  refine ⟨fun w => rfl, fun w v n h => h, fun b => ⟨lastLab b, isFO_lastLab b, ?_⟩⟩
  intro w fo so
  exact sat_lastLab b w fo so

/-! ## Closure under composition -/

/-- The existential closure of all the variables of a formula.  It is a
sentence, and it is equivalent to the formula itself as soon as the formula
defines a language that does not contain the empty string. -/
def MSO.closeSelf (φ : MSO A) : MSO A := MSO.closeFO φ φ.foVars

lemma MSO.isFO_closeSelf {φ : MSO A} (h : φ.IsFO) : (MSO.closeSelf φ).IsFO := by
  rw [MSO.closeSelf, MSO.closeFO]
  revert h
  generalize φ.foVars = is
  induction is with
  | nil => exact fun h => h
  | cons i is ih => exact fun h => ih h

lemma MSO.freeFO_closeSelf (φ : MSO A) : (MSO.closeSelf φ).freeFO = ∅ := by
  refine Set.eq_empty_of_subset_empty ?_
  intro x hx
  obtain ⟨h1, h2⟩ := MSO.freeFO_closeFO φ φ.foVars hx
  exact h2 (MSO.freeFO_subset_foVars φ h1)

lemma MSO.sat_closeSelf {L : Language A} {φ : MSO A}
    (hsat : ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), Sat w fo so φ ↔ w ∈ L)
    (hnil : [] ∉ L) (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (MSO.closeSelf φ) ↔ w ∈ L := by
  constructor
  · intro h
    obtain ⟨fo', hfo'⟩ := MSO.exists_sat_of_sat_closeFO φ.foVars fo so h
    exact (hsat w fo' so).mp hfo'
  · intro hw
    have hne : w ≠ [] := by
      rintro rfl
      exact hnil hw
    exact MSO.sat_closeFO_of_forall hne (fun fo' so' => (hsat w fo' so').mpr hw) _ _ _

/-- First-order definable Mealy machines are closed under composition: the
formulas of the second machine are pulled back along the first one by
substituting, for the label tests, the formulas describing the letters it
produces. -/
lemma foDefMealy_comp {f : List A → List B} {g : List B → List C}
    (hf : FODefMealy f) (hg : FODefMealy g) : FODefMealy (g ∘ f) := by
  obtain ⟨hflen, hfpd, hfdef⟩ := hf
  obtain ⟨hglen, hgpd, hgdef⟩ := hg
  have hlen : LengthPreserving (g ∘ f) := fun w => by
    show (g (f w)).length = w.length
    rw [hglen, hflen]
  refine ⟨hlen, ?_, ?_⟩
  · intro w v n h
    exact hgpd (f w) (f v) n (hfpd w v n h)
  · intro c
    obtain ⟨ψ₀, hψ₀fo, hψ₀sat⟩ := hgdef c
    -- a sentence over `B` defining the same language
    set ψ := MSO.closeSelf ψ₀ with hψdef
    have hψfo : ψ.IsFO := MSO.isFO_closeSelf hψ₀fo
    have hψsat : ∀ (v : List B) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
        Sat v fo so ψ ↔ (g v).getLast? = some c := by
      refine MSO.sat_closeSelf hψ₀sat ?_
      show ¬ ((g []).getLast? = some c)
      have : g [] = [] := by
        have := hglen []
        simpa using this
      rw [this]
      simp
    -- the sentences over `A` describing the letters produced by `f`
    have hχ : ∀ b : B, ∃ χ : MSO A, χ.IsFO ∧ χ.freeFO = ∅ ∧
        (∀ i ∈ ψ.foVars, i ∉ χ.foVars) ∧
        ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
          (Sat w fo so χ ↔ (f w).getLast? = some b) := by
      intro b
      obtain ⟨φ₀, hφ₀fo, hφ₀sat⟩ := hfdef b
      have hφsat : ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
          Sat w fo so (MSO.closeSelf φ₀) ↔ (f w).getLast? = some b := by
        refine MSO.sat_closeSelf hφ₀sat ?_
        show ¬ ((f []).getLast? = some b)
        have : f [] = [] := by
          have := hflen []
          simpa using this
        rw [this]
        simp
      refine ⟨MSO.shiftUp (MSO.maxVar ψ) (MSO.closeSelf φ₀),
        MSO.isFO_shiftUp _ (MSO.isFO_closeSelf hφ₀fo),
        MSO.freeFO_shiftUp_eq_empty _ (MSO.freeFO_closeSelf φ₀), ?_, ?_⟩
      · intro i hi hmem
        have h1 : i < MSO.maxVar ψ := MSO.mem_foVars_lt_maxVar ψ hi
        have h2 : MSO.maxVar ψ ≤ i := MSO.le_of_mem_foVars_shiftUp _ _ hmem
        omega
      · intro w fo so
        rw [MSO.sat_shiftUp_sentence (MSO.isFO_closeSelf hφ₀fo)
          (MSO.freeFO_closeSelf φ₀) _ w fo (fun _ => 0) so (fun _ => ∅)]
        exact hφsat w _ _
    choose χ hχfo hχfree hχfresh hχsat using hχ
    refine ⟨MSO.substRel χ ψ, MSO.isFO_substRel hχfo ψ hψfo, ?_⟩
    intro w fo so
    have hsub := MSO.sat_substRel hχfo hχfree hflen
      (fun b u p hp => by
        rw [hχsat b (u.take (p + 1)) (fun _ => 0) (fun _ => ∅)]
        exact ((FODefMealy.getElem?_eq hflen hfpd u p hp b).symm))
      ψ hψfo (fun i hi b => hχfresh b i hi) w fo so
      (by
        intro i hi
        rw [MSO.freeFO_closeSelf ψ₀] at hi
        exact hi.elim)
    rw [← hsub, hψsat (f w) fo so]
    rfl

/-! ## Flip-flop machines -/

section FlipFlop

variable {Q : Type}

open scoped Classical in
/-- The formula saying that the letter at the position `x_v` resets the
machine. -/
noncomputable def resetAtF [Fintype A] (M : Mealy A B Q) (v : ℕ) : MSO A :=
  bigOr ((Finset.univ : Finset A).toList.map
    (fun a => if (Mealy.resetTo M a).isSome then MSO.lab a v else MSO.ff))

lemma isFO_resetAtF [Fintype A] (M : Mealy A B Q) (v : ℕ) : (resetAtF M v).IsFO := by
  refine isFO_bigOr _ ?_
  intro φ hφ
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hφ
  by_cases h : (Mealy.resetTo M a).isSome <;> simp [h, MSO.ff, MSO.tt, MSO.IsFO]

lemma sat_resetAtF [Fintype A] (M : Mealy A B Q) (v : ℕ) (w : List A) (fo : ℕ → ℕ)
    (so : ℕ → Set ℕ) :
    Sat w fo so (resetAtF M v) ↔ ∃ a, w[fo v]? = some a ∧ (Mealy.resetTo M a).isSome := by
  rw [resetAtF, sat_bigOr]
  constructor
  · rintro ⟨φ, hφ, hsat⟩
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hφ
    by_cases h : (Mealy.resetTo M a).isSome
    · rw [if_pos h] at hsat
      exact ⟨a, hsat, h⟩
    · rw [if_neg h] at hsat
      exact absurd hsat (sat_ff w fo so)
  · rintro ⟨a, ha, hs⟩
    refine ⟨MSO.lab a v, ?_, ha⟩
    refine List.mem_map.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), ?_⟩
    rw [if_pos hs]

open scoped Classical in
/-- The formula saying that the state of the machine before the position `x₀` is
`q`: either the last resetting letter before `x₀` resets to `q`, or there is no
resetting letter before `x₀` and `q` is the initial state. -/
noncomputable def stateF [Fintype A] (M : Mealy A B Q) (q : Q) : MSO A :=
  MSO.or
    (bigOr ((Finset.univ : Finset A).toList.map
      (fun a => if Mealy.resetTo M a = some q then
        MSO.exFO 1 (MSO.and (ltVar 1 0) (MSO.and (MSO.lab a 1)
          (MSO.not (MSO.exFO 2 (MSO.and (ltVar 1 2)
            (MSO.and (ltVar 2 0) (resetAtF M 2)))))))
        else MSO.ff)))
    (if q = M.init then MSO.not (MSO.exFO 1 (MSO.and (ltVar 1 0) (resetAtF M 1))) else MSO.ff)

lemma isFO_stateF [Fintype A] (M : Mealy A B Q) (q : Q) : (stateF M q).IsFO := by
  refine ⟨isFO_bigOr _ ?_, ?_⟩
  · intro φ hφ
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hφ
    by_cases h : Mealy.resetTo M a = some q
    · rw [if_pos h]
      exact ⟨isFO_ltVar _ _, trivial, ⟨isFO_ltVar _ _, isFO_ltVar _ _, isFO_resetAtF M 2⟩⟩
    · rw [if_neg h]
      exact trivial
  · by_cases h : q = M.init
    · rw [if_pos h]
      exact ⟨isFO_ltVar _ _, isFO_resetAtF M 1⟩
    · rw [if_neg h]
      exact trivial

/-- The formula `stateF` says that the state before the position `x₀` is `q`. -/
lemma sat_stateF [Fintype A] (M : Mealy A B Q) (hM : M.FlipFlop) (q : Q) (w : List A)
    (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (stateF M q) ↔ M.trans (w.take (fo 0)) M.init = q := by
  rw [Mealy.trans_take_eq_iff hM]
  constructor
  · rintro (hleft | hright)
    · -- the last resetting letter
      rw [sat_bigOr] at hleft
      obtain ⟨φ, hφ, hsat⟩ := hleft
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hφ
      by_cases hres : Mealy.resetTo M a = some q
      · rw [if_pos hres] at hsat
        obtain ⟨j, hj, hjlt, hlab, hno⟩ := hsat
        have hfo1 : Function.update fo 1 j 1 = j := Function.update_self _ _ _
        have hfo0 : Function.update fo 1 j 0 = fo 0 := Function.update_of_ne (by omega) _ _
        have hjlt' : j < fo 0 := by
          have := (sat_ltVar w (Function.update fo 1 j) so 1 0).mp hjlt
          rwa [hfo1, hfo0] at this
        have hlab' : w[j]? = some a := by
          have : w[Function.update fo 1 j 1]? = some a := hlab
          rwa [hfo1] at this
        refine Or.inl ⟨j, hjlt', a, hlab', hres, ?_⟩
        intro z a' hz1 hz2 hwz
        by_contra hne
        refine hno ⟨z, ?_, ?_, ?_, ?_⟩
        · exact List.getElem?_eq_some_iff.mp hwz |>.fst
        · rw [sat_ltVar, Function.update_self, Function.update_of_ne (by omega), hfo1]
          exact hz1
        · rw [sat_ltVar, Function.update_self, Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hz2
        · rw [sat_resetAtF, Function.update_self]
          refine ⟨a', hwz, ?_⟩
          cases hr : Mealy.resetTo M a' with
          | none => exact absurd hr hne
          | some q' => rfl
      · rw [if_neg hres] at hsat
        exact absurd hsat (sat_ff _ _ _)
    · -- no resetting letter at all
      by_cases hq : q = M.init
      · rw [if_pos hq] at hright
        refine Or.inr ⟨hq, ?_⟩
        intro z a' hz hwz
        by_contra hne
        refine absurd ?_ hright
        refine ⟨z, List.getElem?_eq_some_iff.mp hwz |>.fst, ?_, ?_⟩
        · rw [sat_ltVar, Function.update_self, Function.update_of_ne (by omega)]
          exact hz
        · rw [sat_resetAtF, Function.update_self]
          refine ⟨a', hwz, ?_⟩
          cases hr : Mealy.resetTo M a' with
          | none => exact absurd hr hne
          | some q' => rfl
      · rw [if_neg hq] at hright
        exact absurd hright (sat_ff _ _ _)
  · rintro (⟨j, hj, a, hwj, hres, hlast⟩ | ⟨rfl, hnone⟩)
    · refine Or.inl ?_
      rw [sat_bigOr]
      refine ⟨_, List.mem_map.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), rfl⟩, ?_⟩
      rw [if_pos hres]
      have hjw : j < w.length := List.getElem?_eq_some_iff.mp hwj |>.fst
      have hfo1 : Function.update fo 1 j 1 = j := Function.update_self _ _ _
      have hfo0 : Function.update fo 1 j 0 = fo 0 := Function.update_of_ne (by omega) _ _
      refine ⟨j, hjw, ?_, ?_, ?_⟩
      · rw [sat_ltVar, hfo1, hfo0]
        exact hj
      · show w[Function.update fo 1 j 1]? = some a
        rw [hfo1]
        exact hwj
      · rintro ⟨z, hz, hz1, hz2, hz3⟩
        have e1 : Function.update (Function.update fo 1 j) 2 z 2 = z :=
          Function.update_self _ _ _
        have e2 : Function.update (Function.update fo 1 j) 2 z 1 = j := by
          rw [Function.update_of_ne (by omega), hfo1]
        have e3 : Function.update (Function.update fo 1 j) 2 z 0 = fo 0 := by
          rw [Function.update_of_ne (by omega), hfo0]
        have hz1' : j < z := by
          have := (sat_ltVar w (Function.update (Function.update fo 1 j) 2 z) so 1 2).mp hz1
          rwa [e1, e2] at this
        have hz2' : z < fo 0 := by
          have := (sat_ltVar w (Function.update (Function.update fo 1 j) 2 z) so 2 0).mp hz2
          rwa [e1, e3] at this
        rw [sat_resetAtF, e1] at hz3
        obtain ⟨a', hwz, hsome⟩ := hz3
        rw [hlast z a' hz1' hz2' hwz] at hsome
        exact absurd hsome (by simp)
    · refine Or.inr ?_
      rw [if_pos rfl]
      rintro ⟨z, hz, hz1, hz2⟩
      have e1 : Function.update fo 1 z 1 = z := Function.update_self _ _ _
      have e2 : Function.update fo 1 z 0 = fo 0 := Function.update_of_ne (by omega) _ _
      have hz1' : z < fo 0 := by
        have := (sat_ltVar w (Function.update fo 1 z) so 1 0).mp hz1
        rwa [e1, e2] at this
      rw [sat_resetAtF, e1] at hz2
      obtain ⟨a', hwz, hsome⟩ := hz2
      rw [hnone z a' hz1' hwz] at hsome
      exact absurd hsome (by simp)

open scoped Classical in
/-- The formula saying that the last letter produced by the flip-flop machine is
`b`. -/
noncomputable def outF [Fintype A] [Fintype Q] (M : Mealy A B Q) (b : B) : MSO A :=
  MSO.exFO 0 (MSO.and (MSO.not (MSO.exFO 1 (MSO.not (MSO.le 1 0))))
    (bigOr (((Finset.univ : Finset Q) ×ˢ (Finset.univ : Finset A)).toList.map
      (fun qa => if (M.step qa.1 qa.2).2 = b then
        MSO.and (stateF M qa.1) (MSO.lab qa.2 0) else MSO.ff))))

lemma isFO_outF [Fintype A] [Fintype Q] (M : Mealy A B Q) (b : B) : (outF M b).IsFO := by
  refine ⟨trivial, isFO_bigOr _ ?_⟩
  intro φ hφ
  obtain ⟨qa, -, rfl⟩ := List.mem_map.mp hφ
  by_cases h : (M.step qa.1 qa.2).2 = b
  · rw [if_pos h]
    exact ⟨isFO_stateF M qa.1, trivial⟩
  · rw [if_neg h]
    exact trivial

/-- The last letter of the run of a Mealy machine. -/
lemma Mealy.getLast?_eval {Q : Type} (M : Mealy A B Q) (w : List A) (p : ℕ)
    (hp : p + 1 = w.length) (a : A) (ha : w[p]? = some a) :
    (M.eval w).getLast? = some (M.step (M.trans (w.take p) M.init) a).2 := by
  have hpw : p < w.length := by omega
  have hsplit : w = w.take p ++ [a] := by
    have h1 : w.take (p + 1) = w.take p ++ [a] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hpw]
      have : w[p] = a := (List.getElem?_eq_some_iff.mp ha).2
      rw [this]
      rfl
    rw [← h1, hp, List.take_length]
  conv_lhs => rw [hsplit]
  rw [M.eval_append]
  show ((M.eval (w.take p)) ++ M.run (M.trans (w.take p) M.init) [a]).getLast? = _
  rw [show M.run (M.trans (w.take p) M.init) [a]
    = [(M.step (M.trans (w.take p) M.init) a).2] from rfl]
  simp

/-- Flip-flop machines are first-order definable. -/
lemma foDefMealy_flipFlop [Fintype A] [Fintype Q] (M : Mealy A B Q)
    (hM : M.FlipFlop) : FODefMealy M.eval := by
  refine ⟨fun w => M.eval_length w, Mealy.prefixDetermined M, fun b => ⟨outF M b, isFO_outF M b, ?_⟩⟩
  intro w fo so
  show Sat w fo so (outF M b) ↔ (M.eval w).getLast? = some b
  constructor
  · rintro ⟨p, hp, hlast, hbig⟩
    -- `p` is the last position
    have hple : ∀ q, q < w.length → q ≤ p := by
      intro q hq
      by_contra hlt
      refine hlast ⟨q, hq, ?_⟩
      show ¬ (Function.update (Function.update fo 0 p) 1 q 1
        ≤ Function.update (Function.update fo 0 p) 1 q 0)
      rw [Function.update_self, Function.update_of_ne (by omega), Function.update_self]
      omega
    have hpe : p + 1 = w.length := by
      have := hple (w.length - 1) (by omega)
      omega
    rw [sat_bigOr] at hbig
    obtain ⟨φ, hφ, hsat⟩ := hbig
    obtain ⟨qa, -, rfl⟩ := List.mem_map.mp hφ
    by_cases hb : (M.step qa.1 qa.2).2 = b
    · rw [if_pos hb] at hsat
      obtain ⟨hst, hlab⟩ := hsat
      have hfo0 : Function.update fo 0 p 0 = p := Function.update_self _ _ _
      have hlab' : w[p]? = some qa.2 := by
        have : w[Function.update fo 0 p 0]? = some qa.2 := hlab
        rwa [hfo0] at this
      rw [sat_stateF M hM, hfo0] at hst
      rw [Mealy.getLast?_eval M w p hpe qa.2 hlab', hst, hb]
    · rw [if_neg hb] at hsat
      exact absurd hsat (sat_ff _ _ _)
  · intro hb
    have hne : w ≠ [] := by
      rintro rfl
      simp [Mealy.eval] at hb
    have hpos : 0 < w.length := by
      cases w with
      | nil => exact absurd rfl hne
      | cons c u => simp
    set p := w.length - 1 with hpdef
    have hpe : p + 1 = w.length := by omega
    obtain ⟨a, ha⟩ : ∃ a : A, w[p]? = some a :=
      ⟨w[p]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    set q := M.trans (w.take p) M.init with hq
    have hout : (M.step q a).2 = b := by
      have := Mealy.getLast?_eval M w p hpe a ha
      rw [hb] at this
      exact (Option.some.inj this).symm
    refine ⟨p, by omega, ?_, ?_⟩
    · rintro ⟨z, hz, hzlt⟩
      have : ¬ (Function.update (Function.update fo 0 p) 1 z 1
          ≤ Function.update (Function.update fo 0 p) 1 z 0) := hzlt
      rw [Function.update_self, Function.update_of_ne (by omega), Function.update_self] at this
      omega
    · rw [sat_bigOr]
      refine ⟨_, List.mem_map.mpr ⟨(q, a), ?_, rfl⟩, ?_⟩
      · simp
      · rw [if_pos hout]
        refine ⟨?_, ?_⟩
        · rw [sat_stateF M hM, Function.update_self]
        · show w[Function.update fo 0 p 0]? = some a
          rw [Function.update_self]
          exact ha

end FlipFlop

/-- A composition of flip-flop machines is first-order definable. -/
theorem foDefMealy_of_flipFlopComp : ∀ {A B : Type} {f : List A → List B},
    CompClosure FlipFlopFam A B f → Finite A → FODefMealy f := by
  intro A B f h
  induction h with
  | @base A' B' f' hf =>
      intro hA
      obtain ⟨Q, hQ, M, rfl, hM⟩ := hf
      haveI := hA
      haveI := hQ
      haveI := Fintype.ofFinite A'
      haveI := Fintype.ofFinite Q
      exact foDefMealy_flipFlop M hM
  | id A' => intro _; exact foDefMealy_id
  | @comp A' B' C' instB f' g' hf hg ihf ihg =>
      intro hA
      exact foDefMealy_comp (ihf hA) (ihg instB)

/-! ## The Mealy machine of a dfa -/

open scoped Classical in
/-- The Mealy machine attached to a dfa: it outputs, at every position, whether
the prefix read so far is accepted. -/
noncomputable def dfaMealy {σ : Type} (M : DFA A σ) : Mealy A Bool σ where
  init := M.start
  step := fun q a => (M.step q a, decide (M.step q a ∈ M.accept))

/-- The last output letter of the Mealy machine of a dfa tells whether the input
is accepted. -/
lemma dfaMealy_getLast? {σ : Type} (M : DFA A σ) (w : List A) (hw : w ≠ []) :
    (((dfaMealy M).eval w).getLast? = some true ↔ w ∈ M.accepts) ∧
      (((dfaMealy M).eval w).getLast? = some false ↔ w ∉ M.accepts) := by
  classical
  obtain ⟨u, a, rfl⟩ : ∃ (u : List A) (a : A), w = u ++ [a] := by
    rcases List.eq_nil_or_concat w with rfl | ⟨u, a, rfl⟩
    · exact absurd rfl hw
    · exact ⟨u, a, List.concat_eq_append⟩
  have htrans : (dfaMealy M).trans u (dfaMealy M).init = M.eval u := by
    show strTrans (dfaMealy M).transFun u M.start = List.foldl M.step M.start u
    rfl
  have hlast : ((dfaMealy M).eval (u ++ [a])).getLast?
      = some (decide (M.step (M.eval u) a ∈ M.accept)) := by
    rw [Mealy.eval_append, htrans]
    show ((dfaMealy M).eval u ++ [((dfaMealy M).step (M.eval u) a).2]).getLast? = _
    simp [dfaMealy]
  have haccept : (u ++ [a]) ∈ M.accepts ↔ M.step (M.eval u) a ∈ M.accept := by
    show M.eval (u ++ [a]) ∈ M.accept ↔ _
    rw [show M.eval (u ++ [a]) = M.step (M.eval u) a from by
      simp [DFA.eval, DFA.evalFrom]]
  rw [hlast, haccept]
  constructor
  · simp
  · simp

/-- **The hard implication of Theorem `thm:logic-aperiodic`.**  A language recognised by an
aperiodic dfa is first-order definable. -/
theorem foDefinable_of_aperiodic_dfa {σ : Type} [Finite A] [Finite σ] (M : DFA A σ)
    (h : TransAperiodic M.step) : FODefinable M.accepts := by
  have hstab : (dfaMealy M).TransStabilises := h
  have hcc : CompClosure FlipFlopFam A Bool (dfaMealy M).eval :=
    krohn_rhodes_flipFlop (dfaMealy M) hstab
  obtain ⟨-, -, hdef⟩ := foDefMealy_of_flipFlopComp hcc inferInstance
  obtain ⟨φ, hφfo, hφsat⟩ := hdef true
  have hφ : ∀ (w : List A), w ≠ [] →
      ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ), (Sat w fo so φ ↔ w ∈ M.accepts) := by
    intro w hw fo so
    rw [hφsat w fo so]
    exact (dfaMealy_getLast? M w hw).1
  have hnil : ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ), ¬ Sat ([] : List A) fo so φ := by
    intro fo so
    rw [hφsat [] fo so]
    show ¬ (((dfaMealy M).eval []).getLast? = some true)
    simp [Mealy.eval]
  -- the empty string has to be added or removed by hand
  by_cases hstart : [] ∈ M.accepts
  · refine ⟨MSO.or φ (MSO.not (MSO.exFO 0 (MSO.le 0 0))), ⟨hφfo, trivial⟩, ?_⟩
    intro w fo so
    show (Sat w fo so φ ∨ ¬ Sat w fo so (MSO.exFO 0 (MSO.le 0 0))) ↔ w ∈ M.accepts
    by_cases hw : w = []
    · subst hw
      constructor
      · intro _; exact hstart
      · intro _
        refine Or.inr ?_
        rintro ⟨p, hp, -⟩
        simp at hp
    · have hnonempty : 0 < w.length := by
        cases w with
        | nil => exact absurd rfl hw
        | cons c u => simp
      constructor
      · rintro (hs | hs)
        · exact (hφ w hw fo so).mp hs
        · exact absurd ⟨0, hnonempty, le_rfl⟩ hs
      · intro hwacc
        exact Or.inl ((hφ w hw fo so).mpr hwacc)
  · refine ⟨φ, hφfo, ?_⟩
    intro w fo so
    by_cases hw : w = []
    · subst hw
      constructor
      · intro hs; exact absurd hs (hnil fo so)
      · intro hs; exact absurd hs hstart
    · exact hφ w hw fo so

end Lax314295Proofs.Transducers
