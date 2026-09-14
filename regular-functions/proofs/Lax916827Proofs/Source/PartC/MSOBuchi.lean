/-
Theorem `thm:mso-logic-languages` of *Transducers* (M. Bojańczyk), the Büchi-Elgot-Trakhtenbrot
theorem: a language of finite strings is regular if and only if it is definable
in monadic second-order logic.

The two implications are proved separately.

* From logic to automata (`isRegular_of_msoDefinable`).  This is the special case of Lemma
  `lem:mso-free-variables` (`RequestProject/PartC/MSOAnnot.lean`) with no free variables: a
  formula whose truth value does not depend on the valuation is first turned into a sentence by
  existentially quantifying all its variables (`MSO.closeFO`, `MSO.closeSO`), and the language of a
  sentence is the inverse image, under the letter-to-letter map `a ↦ (a, (), ())`, of the language
  of annotated strings of Lemma `lem:mso-free-variables` for `k = l = 0`.  The existential
  closure is false on the empty string as soon as the formula has a quantifier, so the empty string
  is treated separately.

* From automata to logic (`msoDefinable_of_isRegular`).  The formula guesses the
  run of a deterministic automaton as a tuple of second-order variables, one for
  each state: it says that the sets `X_q` partition the positions, that they are
  consistent with the initial state and with the transition function, and that
  the last position belongs to `X_q` for an accepting state `q`.  Again the
  empty string is treated separately.
-/
import Lax916827Proofs.Source.PartC.MSOAnnot
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers
namespace MSOBuchi

open MSO RegAut

/-! ## Sentences define regular languages -/

section FromFormula

variable {A : Type}

/-- The letter-to-letter map annotating a string by the empty tuple of
variables. -/
def annNil (a : A) : A × (Fin 0 → Bool) × (Fin 0 → Bool) := (a, Fin.elim0, Fin.elim0)

lemma annNil_injective : Function.Injective (annNil (A := A)) :=
  fun _ _ h => congrArg Prod.fst h

open scoped Classical in
lemma annotate_zero (w : List A) (fo : Fin 0 → ℕ) (so : Fin 0 → Set ℕ) :
    annotate 0 0 w fo so = w.map annNil := by
  apply List.ext_getElem?
  intro q
  rw [MSOAnnot.annotate_getElem?]
  simp only [List.getElem?_map]
  rcases hq : w[q]? with - | a
  · rfl
  · simp only [Option.map_some]
    have h1 : (fun i : Fin 0 => decide (fo i = q)) = (Fin.elim0 : Fin 0 → Bool) :=
      funext (fun i => i.elim0)
    have h2 : (fun j : Fin 0 => decide (q ∈ so j)) = (Fin.elim0 : Fin 0 → Bool) :=
      funext (fun j => j.elim0)
    rw [h1, h2]
    rfl

lemma extFO_zero (fo : Fin 0 → ℕ) : extFO 0 fo = fun _ => 0 := by
  funext i; simp [extFO]

lemma extSO_zero (so : Fin 0 → Set ℕ) : extSO 0 so = fun _ => (∅ : Set ℕ) := by
  funext j; simp [extSO]

/-- The language defined by a sentence is regular.  This is Lemma `lem:mso-free-variables`
with no free variables. -/
lemma isRegular_satLang (φ : MSO A) (hfo : φ.freeFO = ∅) (hso : φ.freeSO = ∅)
    (fo₀ : ℕ → ℕ) (so₀ : ℕ → Set ℕ) :
    Language.IsRegular {w : List A | Sat w fo₀ so₀ φ} := by
  classical
  have hann := MSOAnnot.mso_annotated_regular_aux φ 0 0
    (by rw [hfo]; exact Set.empty_subset _) (by rw [hso]; exact Set.empty_subset _)
  have hcom := isRegular_comap (annNil (A := A)) hann
  refine isRegular_of_eq hcom (fun w => ?_)
  have hcongr : ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ), Sat w fo so φ ↔ Sat w fo₀ so₀ φ := by
    intro fo so
    refine sat_congr w φ fo fo₀ so so₀ (fun i hi => ?_) (fun j hj => ?_)
    · rw [hfo] at hi; exact hi.elim
    · rw [hso] at hj; exact hj.elim
  constructor
  · intro hw
    refine ⟨w, Fin.elim0, Fin.elim0, (fun i => i.elim0), (fun j => j.elim0),
      (annotate_zero w _ _).symm, ?_⟩
    rw [extFO_zero, extSO_zero]
    exact (hcongr _ _).2 hw
  · rintro ⟨w', fo', so', -, -, hmap, hsat⟩
    rw [annotate_zero] at hmap
    have hww : w = w' := List.map_injective_iff.2 annNil_injective hmap
    subst hww
    rw [extFO_zero, extSO_zero] at hsat
    exact (hcongr _ _).1 hsat

/-- **Theorem `thm:mso-logic-languages`**, the implication from logic to automata. -/
theorem isRegular_of_msoDefinable {L : Language A} (h : MSODefinable L) : L.IsRegular := by
  classical
  obtain ⟨φ, hφ⟩ := h
  set χ : MSO A := closeFO φ φ.foVars with hχdef
  set ψ : MSO A := closeSO χ χ.soVars with hψdef
  have hχfo : χ.freeFO = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 (fun x hx => ?_)
    have := freeFO_closeFO φ φ.foVars hx
    exact this.2 (freeFO_subset_foVars φ this.1)
  have hfree1 : ψ.freeFO = ∅ := by
    rw [hψdef, freeFO_closeSO, hχfo]
  have hfree2 : ψ.freeSO = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 (fun x hx => ?_)
    have := freeSO_closeSO χ χ.soVars hx
    exact this.2 (freeSO_subset_soVars χ this.1)
  have hreg := isRegular_satLang ψ hfree1 hfree2 (fun _ => 0) (fun _ => (∅ : Set ℕ))
  -- on nonempty strings, the sentence `ψ` defines `L`
  have hkey : ∀ w : List A, w ≠ [] → (Sat w (fun _ => 0) (fun _ => (∅ : Set ℕ)) ψ ↔ w ∈ L) := by
    intro w hne
    constructor
    · intro hsat
      obtain ⟨so', hso'⟩ := exists_sat_of_sat_closeSO χ.soVars _ _ hsat
      obtain ⟨fo', hfo'⟩ := exists_sat_of_sat_closeFO φ.foVars _ _ hso'
      exact (hφ w fo' so').1 hfo'
    · intro hw
      have hall : ∀ fo so, Sat w fo so φ := fun fo so => (hφ w fo so).2 hw
      exact sat_closeSO_of_forall (fun fo so => sat_closeFO_of_forall hne hall _ fo so) _ _ _
  by_cases h0 : [] ∈ L
  · refine isRegular_of_eq (isRegular_or hreg (isRegular_eq_nil (Γ := A))) (fun w => ?_)
    constructor
    · intro hw
      by_cases hne : w = []
      · exact Or.inr hne
      · exact Or.inl ((hkey w hne).2 hw)
    · rintro (hw | rfl)
      · by_cases hne : w = []
        · rw [hne]; exact h0
        · exact (hkey w hne).1 hw
      · exact h0
  · refine isRegular_of_eq (isRegular_and hreg (isRegular_not (isRegular_eq_nil (Γ := A))))
      (fun w => ?_)
    constructor
    · intro hw
      have hne : w ≠ [] := by rintro rfl; exact h0 hw
      exact ⟨(hkey w hne).2 hw, hne⟩
    · rintro ⟨hw, hne⟩
      exact (hkey w hne).1 hw

end FromFormula

/-! ## Automata define mso-definable languages -/

section Semantics

variable {A : Type}

lemma satLe (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (i j : ℕ) :
    Sat w fo so (MSO.le i j) ↔ fo i ≤ fo j := Iff.rfl

lemma satLab (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (a : A) (i : ℕ) :
    Sat w fo so (MSO.lab a i) ↔ w[fo i]? = some a := Iff.rfl

lemma satMem (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (i j : ℕ) :
    Sat w fo so (MSO.mem i j) ↔ fo i ∈ so j := Iff.rfl

lemma satNot (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (φ : MSO A) :
    Sat w fo so (MSO.not φ) ↔ ¬ Sat w fo so φ := Iff.rfl

lemma satAnd (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (φ ψ : MSO A) :
    Sat w fo so (MSO.and φ ψ) ↔ (Sat w fo so φ ∧ Sat w fo so ψ) := Iff.rfl

lemma satOr (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (φ ψ : MSO A) :
    Sat w fo so (MSO.or φ ψ) ↔ (Sat w fo so φ ∨ Sat w fo so ψ) := Iff.rfl

lemma satExFO (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (i : ℕ) (φ : MSO A) :
    Sat w fo so (MSO.exFO i φ) ↔ ∃ p < w.length, Sat w (Function.update fo i p) so φ := Iff.rfl

lemma sat_bigOr_map {ι : Type} (f : ι → MSO A) (l : List ι) (w : List A)
    (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (bigOr (l.map f)) ↔ ∃ x ∈ l, Sat w fo so (f x) := by
  rw [sat_bigOr]
  constructor
  · rintro ⟨ψ, hψ, h⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hψ
    exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨f x, List.mem_map.2 ⟨x, hx, rfl⟩, h⟩

lemma sat_bigAnd_map {ι : Type} (f : ι → MSO A) (l : List ι) (w : List A)
    (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (bigAnd (l.map f)) ↔ ∀ x ∈ l, Sat w fo so (f x) := by
  rw [sat_bigAnd]
  constructor
  · intro h x hx
    exact h (f x) (List.mem_map.2 ⟨x, hx, rfl⟩)
  · intro h ψ hψ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hψ
    exact h x hx

end Semantics

section FromAutomaton

variable {A σ : Type} {n : ℕ}

/-- The second-order variable guessing the set of positions at which the run is
in the state `q`. -/
def stIdx (e : σ ≃ Fin n) (q : σ) : ℕ := (e q : ℕ)

lemma stIdx_lt (e : σ ≃ Fin n) (q : σ) : stIdx e q < n := (e q).isLt

/-- The state of the run of `D` on `w` after reading the first `p + 1`
letters. -/
def runState (D : DFA A σ) (w : List A) (p : ℕ) : σ := (w.take (p + 1)).foldl D.step D.start

lemma runState_zero (D : DFA A σ) {w : List A} (h : 0 < w.length) :
    runState D w 0 = D.step D.start w[0] := by
  rw [runState, List.take_succ_eq_append_getElem h]
  simp

lemma runState_succ (D : DFA A σ) {w : List A} {p : ℕ} (h : p + 1 < w.length) :
    runState D w (p + 1) = D.step (runState D w p) w[p + 1] := by
  rw [runState, runState, List.take_succ_eq_append_getElem h, List.foldl_append]
  simp

lemma runState_last (D : DFA A σ) {w : List A} {p : ℕ} (h : p + 1 = w.length) :
    runState D w p = D.eval w := by
  rw [runState, h, List.take_length]
  rfl

/-- The conditions expressing that a family of sets of positions is the
(accepting) run of the automaton `D` on `w`. -/
structure IsRun (D : DFA A σ) (w : List A) (S : σ → Set ℕ) : Prop where
  /-- every position is in some `S q` -/
  cover : ∀ p < w.length, ∃ q, p ∈ S q
  /-- no position is in two different `S q` -/
  excl : ∀ p < w.length, ∀ q q', p ∈ S q → p ∈ S q' → q = q'
  /-- the first position is consistent with the initial state -/
  init : ∀ a, w[0]? = some a → 0 ∈ S (D.step D.start a)
  /-- consecutive positions are consistent with the transition function -/
  next : ∀ (p : ℕ) (q : σ) (a : A), p ∈ S q → w[p + 1]? = some a → p + 1 ∈ S (D.step q a)
  /-- the last position is in an accepting set -/
  acc : ∃ p, p + 1 = w.length ∧ ∃ q ∈ D.accept, p ∈ S q

/-- A guessed accepting run witnesses acceptance. -/
lemma accepts_of_isRun (D : DFA A σ) {w : List A} {S : σ → Set ℕ} (h : IsRun D w S) :
    w ∈ D.accepts := by
  have key : ∀ p, p < w.length → p ∈ S (runState D w p) := by
    intro p
    induction p with
    | zero =>
      intro hp
      have h0 := h.init w[0] (List.getElem?_eq_getElem hp)
      rwa [← runState_zero D hp] at h0
    | succ p ih =>
      intro hp
      have hp' : p < w.length := by omega
      have hstep := h.next p (runState D w p) w[p + 1] (ih hp') (List.getElem?_eq_getElem hp)
      rwa [← runState_succ D hp] at hstep
  obtain ⟨p, hp, q, hq, hmem⟩ := h.acc
  have hplt : p < w.length := by omega
  have heq := h.excl p hplt q (runState D w p) hmem (key p hplt)
  rw [DFA.mem_accepts, ← runState_last D hp, ← heq]
  exact hq

/-- The run of `D` on a nonempty accepted string is a guessed accepting run. -/
lemma isRun_runState (D : DFA A σ) {w : List A} (hne : w ≠ []) (hacc : w ∈ D.accepts) :
    IsRun D w (fun q => {p | p < w.length ∧ runState D w p = q}) := by
  have h0 : 0 < w.length := by
    cases w with
    | nil => exact absurd rfl hne
    | cons a t => simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; exact ⟨runState D w p, hp, rfl⟩
  · rintro p hp q q' ⟨-, rfl⟩ ⟨-, rfl⟩; rfl
  · intro a ha
    have hwa : w[0] = a := by
      rw [List.getElem?_eq_getElem h0] at ha; exact Option.some.inj ha
    exact ⟨h0, by rw [runState_zero D h0, hwa]⟩
  · rintro p q a ⟨hp, rfl⟩ ha
    obtain ⟨hlt, hwa⟩ := List.getElem?_eq_some_iff.1 ha
    exact ⟨hlt, by rw [runState_succ D hlt, hwa]⟩
  · refine ⟨w.length - 1, by omega, D.eval w, hacc, by omega, runState_last D (by omega)⟩

/-! ### The formula guessing the run -/

/-- `x₀` is the first position. -/
def isFirstF (A : Type) : MSO A := allF 1 (MSO.le 0 1)

/-- `x₀` is the last position. -/
def isLastF (A : Type) : MSO A := allF 1 (MSO.le 1 0)

/-- `x₁` is the successor of `x₀`. -/
def isSuccF (A : Type) : MSO A :=
  MSO.and (MSO.and (MSO.le 0 1) (MSO.not (MSO.le 1 0)))
    (allF 2 (MSO.or (MSO.le 2 0) (MSO.le 1 2)))

/-- Every position belongs to one of the guessed sets. -/
def coverF (A : Type) (e : σ ≃ Fin n) (qs : List σ) : MSO A :=
  allF 0 (bigOr (qs.map (fun q => MSO.mem 0 (stIdx e q))))

/-- No position belongs to two of the guessed sets. -/
def exclF (A : Type) (e : σ ≃ Fin n) (prs : List (σ × σ)) : MSO A :=
  allF 0 (bigAnd (prs.map (fun z =>
    MSO.not (MSO.and (MSO.mem 0 (stIdx e z.1)) (MSO.mem 0 (stIdx e z.2))))))

/-- The first position is consistent with the initial state. -/
def initF (D : DFA A σ) (e : σ ≃ Fin n) (ls : List A) : MSO A :=
  allF 0 (impF (isFirstF A) (bigOr (ls.map (fun a =>
    MSO.and (MSO.lab a 0) (MSO.mem 0 (stIdx e (D.step D.start a)))))))

/-- Consecutive positions are consistent with the transition function. -/
def nextF (D : DFA A σ) (e : σ ≃ Fin n) (qas : List (σ × A)) : MSO A :=
  allF 0 (allF 1 (impF (isSuccF A) (bigAnd (qas.map (fun z =>
    impF (MSO.and (MSO.mem 0 (stIdx e z.1)) (MSO.lab z.2 1))
      (MSO.mem 1 (stIdx e (D.step z.1 z.2))))))))

/-- The last position belongs to an accepting set. -/
def accF (A : Type) (e : σ ≃ Fin n) (accs : List σ) : MSO A :=
  MSO.exFO 0 (MSO.and (isLastF A) (bigOr (accs.map (fun q => MSO.mem 0 (stIdx e q)))))

/-- The formula describing an accepting run, before the second-order
quantification. -/
def coreF (D : DFA A σ) (e : σ ≃ Fin n) (ls : List A) (qs : List σ)
    (prs : List (σ × σ)) (qas : List (σ × A)) (accs : List σ) : MSO A :=
  MSO.and (coverF A e qs) (MSO.and (exclF A e prs)
    (MSO.and (initF D e ls) (MSO.and (nextF D e qas) (accF A e accs))))

/-- The formula that guesses an accepting run of `D`. -/
def runF (D : DFA A σ) (e : σ ≃ Fin n) (ls : List A) (qs : List σ)
    (prs : List (σ × σ)) (qas : List (σ × A)) (accs : List σ) : MSO A :=
  closeSO (coreF D e ls qs prs qas accs) (List.range n)

/-- The formula stating that the string is empty. -/
def emptyF (A : Type) : MSO A := MSO.not (MSO.exFO 0 (tt : MSO A))

lemma sat_emptyF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (emptyF A) ↔ w = [] := by
  rw [emptyF, satNot, satExFO]
  constructor
  · intro h
    by_contra hne
    have h0 : 0 < w.length := by
      cases w with
      | nil => exact absurd rfl hne
      | cons a t => simp
    exact h ⟨0, h0, by simp⟩
  · rintro rfl ⟨p, hp, -⟩
    simp at hp

lemma sat_isFirstF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (isFirstF A) ↔ ∀ p < w.length, fo 0 ≤ p := by
  rw [isFirstF, sat_allF]
  simp [satLe]

lemma sat_isLastF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (isLastF A) ↔ ∀ p < w.length, p ≤ fo 0 := by
  rw [isLastF, sat_allF]
  simp [satLe]

lemma sat_isSuccF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ)
    (h0 : fo 0 < w.length) (h1 : fo 1 < w.length) :
    Sat w fo so (isSuccF A) ↔ fo 1 = fo 0 + 1 := by
  rw [isSuccF, satAnd, satAnd, satLe, satNot, satLe, sat_allF]
  simp only [satOr, satLe, Function.update_apply]
  constructor
  · rintro ⟨⟨hle, hlt⟩, hz⟩
    by_contra hne
    have hgt : fo 0 + 1 < fo 1 := by omega
    have := hz (fo 0 + 1) (by omega)
    simp at this
    omega
  · rintro h
    refine ⟨⟨by omega, by omega⟩, fun z hz => ?_⟩
    simp
    omega

lemma sat_coverF (e : σ ≃ Fin n) (qs : List σ) (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (coverF A e qs) ↔ ∀ p < w.length, ∃ q ∈ qs, p ∈ so (stIdx e q) := by
  rw [coverF, sat_allF]
  constructor
  · intro h p hp
    obtain ⟨q, hq, hs⟩ := (sat_bigOr_map _ _ _ _ _).1 (h p hp)
    refine ⟨q, hq, ?_⟩
    rw [satMem, Function.update_self] at hs
    exact hs
  · intro h p hp
    obtain ⟨q, hq, hs⟩ := h p hp
    refine (sat_bigOr_map _ _ _ _ _).2 ⟨q, hq, ?_⟩
    rw [satMem, Function.update_self]
    exact hs

lemma sat_exclF (e : σ ≃ Fin n) (prs : List (σ × σ)) (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (exclF A e prs) ↔
      ∀ p < w.length, ∀ z ∈ prs, ¬ (p ∈ so (stIdx e z.1) ∧ p ∈ so (stIdx e z.2)) := by
  rw [exclF, sat_allF]
  constructor
  · intro h p hp z hz
    have := (sat_bigAnd_map _ _ _ _ _).1 (h p hp) z hz
    rw [satNot, satAnd, satMem, satMem, Function.update_self] at this
    exact this
  · intro h p hp
    refine (sat_bigAnd_map _ _ _ _ _).2 (fun z hz => ?_)
    rw [satNot, satAnd, satMem, satMem, Function.update_self]
    exact h p hp z hz

lemma sat_initF (D : DFA A σ) (e : σ ≃ Fin n) (ls : List A) (w : List A)
    (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (initF D e ls) ↔
      ∀ p < w.length, (∀ p' < w.length, p ≤ p') →
        ∃ a ∈ ls, w[p]? = some a ∧ p ∈ so (stIdx e (D.step D.start a)) := by
  rw [initF, sat_allF]
  refine forall_congr' (fun p => forall_congr' (fun _ => ?_))
  rw [sat_impF, sat_isFirstF, Function.update_self]
  refine imp_congr Iff.rfl ?_
  rw [sat_bigOr_map]
  refine exists_congr (fun a => and_congr_right (fun _ => ?_))
  rw [satAnd, satLab, satMem, Function.update_self]

lemma sat_nextF (D : DFA A σ) (e : σ ≃ Fin n) (qas : List (σ × A)) (w : List A)
    (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (nextF D e qas) ↔
      ∀ x < w.length, ∀ y < w.length, y = x + 1 →
        ∀ z ∈ qas, (x ∈ so (stIdx e z.1) ∧ w[y]? = some z.2) →
          y ∈ so (stIdx e (D.step z.1 z.2)) := by
  rw [nextF, sat_allF]
  refine forall_congr' (fun x => forall_congr' (fun hx => ?_))
  rw [sat_allF]
  refine forall_congr' (fun y => forall_congr' (fun hy => ?_))
  have h0 : (Function.update (Function.update fo 0 x) 1 y) 0 = x := by
    rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 1), Function.update_self]
  have h1 : (Function.update (Function.update fo 0 x) 1 y) 1 = y := Function.update_self _ _ _
  rw [sat_impF, sat_isSuccF _ _ _ (by rw [h0]; exact hx) (by rw [h1]; exact hy), h0, h1]
  refine imp_congr Iff.rfl ?_
  rw [sat_bigAnd_map]
  refine forall_congr' (fun z => forall_congr' (fun _ => ?_))
  rw [sat_impF, satAnd, satMem, satLab, satMem, h0, h1]

lemma sat_accF (e : σ ≃ Fin n) (accs : List σ) (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (accF A e accs) ↔
      ∃ p < w.length, (∀ p' < w.length, p' ≤ p) ∧ ∃ q ∈ accs, p ∈ so (stIdx e q) := by
  rw [accF, satExFO]
  refine exists_congr (fun p => and_congr_right (fun _ => ?_))
  rw [satAnd, sat_isLastF, Function.update_self]
  refine and_congr_right (fun _ => ?_)
  rw [sat_bigOr_map]
  refine exists_congr (fun q => and_congr_right (fun _ => ?_))
  rw [satMem, Function.update_self]

variable (D : DFA A σ) (e : σ ≃ Fin n) (ls : List A) (qs : List σ)
  (prs : List (σ × σ)) (qas : List (σ × A)) (accs : List σ)

/-- The core formula holds exactly for the guessed accepting runs. -/
lemma sat_coreF_iff (hls : ∀ a : A, a ∈ ls) (hqs : ∀ q : σ, q ∈ qs)
    (hprs : ∀ q q' : σ, q ≠ q' → (q, q') ∈ prs) (hprs' : ∀ z ∈ prs, z.1 ≠ z.2)
    (hqas : ∀ (q : σ) (a : A), (q, a) ∈ qas) (haccs : ∀ q : σ, q ∈ accs ↔ q ∈ D.accept)
    (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (coreF D e ls qs prs qas accs) ↔ IsRun D w (fun q => so (stIdx e q)) := by
  rw [coreF, satAnd, satAnd, satAnd, satAnd, sat_coverF, sat_exclF, sat_initF, sat_nextF,
    sat_accF]
  constructor
  · rintro ⟨hcover, hexcl, hinit, hnext, hacc⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, -, hq⟩ := hcover p hp
      exact ⟨q, hq⟩
    · intro p hp q q' hq hq'
      by_contra hne
      exact hexcl p hp (q, q') (hprs q q' hne) ⟨hq, hq'⟩
    · intro a ha
      obtain ⟨h0, -⟩ := List.getElem?_eq_some_iff.1 ha
      obtain ⟨a', -, ha', hmem⟩ := hinit 0 h0 (fun p' _ => Nat.zero_le p')
      rw [ha] at ha'
      cases Option.some.inj ha'
      exact hmem
    · intro p q a hq ha
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ha
      exact hnext p (by omega) (p + 1) hlt rfl (q, a) (hqas q a) ⟨hq, ha⟩
    · obtain ⟨p, hp, hlast, q, hq, hmem⟩ := hacc
      exact ⟨p, by have := hlast (w.length - 1) (by omega); omega,
        q, (haccs q).1 hq, hmem⟩
  · intro hrun
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq⟩ := hrun.cover p hp
      exact ⟨q, hqs q, hq⟩
    · rintro p hp z hz ⟨h1, h2⟩
      exact hprs' z hz (hrun.excl p hp z.1 z.2 h1 h2)
    · intro p hp hfirst
      have hp0 : p = 0 := Nat.le_antisymm (hfirst 0 (by omega)) (Nat.zero_le p)
      subst hp0
      have h0 : w[0]? = some w[0] := List.getElem?_eq_getElem hp
      exact ⟨w[0], hls _, h0, hrun.init w[0] h0⟩
    · rintro x hx y hy rfl z hz ⟨h1, h2⟩
      exact hrun.next x z.1 z.2 h1 h2
    · obtain ⟨p, hp, q, hq, hmem⟩ := hrun.acc
      exact ⟨p, by omega, fun p' hp' => by omega, q, (haccs q).2 hq, hmem⟩

/-- The formula `runF` defines the language of `D`, minus the empty string. -/
lemma sat_runF_iff (hls : ∀ a : A, a ∈ ls) (hqs : ∀ q : σ, q ∈ qs)
    (hprs : ∀ q q' : σ, q ≠ q' → (q, q') ∈ prs) (hprs' : ∀ z ∈ prs, z.1 ≠ z.2)
    (hqas : ∀ (q : σ) (a : A), (q, a) ∈ qas) (haccs : ∀ q : σ, q ∈ accs ↔ q ∈ D.accept)
    (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (runF D e ls qs prs qas accs) ↔ (w ≠ [] ∧ w ∈ D.accepts) := by
  classical
  constructor
  · intro hsat
    obtain ⟨so', hso'⟩ := exists_sat_of_sat_closeSO (List.range n) fo so hsat
    have hrun := (sat_coreF_iff D e ls qs prs qas accs hls hqs hprs hprs' hqas haccs
      w fo so').1 hso'
    obtain ⟨p, hp, -⟩ := hrun.acc
    refine ⟨?_, accepts_of_isRun D hrun⟩
    intro hnil
    rw [hnil] at hp
    simp at hp
  · rintro ⟨hne, hacc⟩
    set so' : ℕ → Set ℕ := fun j =>
      if h : j < n then {p | p < w.length ∧ runState D w p = e.symm ⟨j, h⟩} else so j with hso'def
    have hval : ∀ q : σ, so' (stIdx e q) = {p | p < w.length ∧ runState D w p = q} := by
      intro q
      rw [hso'def]
      simp only [stIdx, dif_pos (e q).isLt]
      congr 1
      simp
    refine sat_closeSO_of_exists (List.range n) fo so so' (fun j hj => ?_) (fun j hj => ?_) ?_
    · rw [List.mem_range] at hj
      rw [hso'def]
      simp only [dif_pos hj]
      rintro p ⟨hp, -⟩
      exact hp
    · rw [List.mem_range] at hj
      rw [hso'def]
      simp only [dif_neg hj]
    · refine (sat_coreF_iff D e ls qs prs qas accs hls hqs hprs hprs' hqas haccs w fo so').2 ?_
      have := isRun_runState D hne hacc
      have heq : (fun q => so' (stIdx e q)) = (fun q => {p | p < w.length ∧ runState D w p = q}) :=
        funext hval
      rw [heq]
      exact this

end FromAutomaton

/-- **Theorem `thm:mso-logic-languages`**, the implication from automata to logic. -/
theorem msoDefinable_of_isRegular {A : Type} [Finite A] {L : Language A} (h : L.IsRegular) :
    MSODefinable L := by
  classical
  obtain ⟨σ, hσ, D, rfl⟩ := h
  letI : Fintype A := Fintype.ofFinite A
  set n := Fintype.card σ with hn
  set e : σ ≃ Fin n := Fintype.equivFin σ with he
  set ls : List A := (Finset.univ : Finset A).toList with hlsdef
  set qs : List σ := (Finset.univ : Finset σ).toList with hqsdef
  set prs : List (σ × σ) :=
    ((Finset.univ : Finset (σ × σ)).toList).filter (fun z => decide (z.1 ≠ z.2)) with hprsdef
  set qas : List (σ × A) := (Finset.univ : Finset (σ × A)).toList with hqasdef
  set accs : List σ :=
    ((Finset.univ : Finset σ).toList).filter (fun q => decide (q ∈ D.accept)) with haccsdef
  have hls : ∀ a : A, a ∈ ls := fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  have hqs : ∀ q : σ, q ∈ qs := fun q => Finset.mem_toList.2 (Finset.mem_univ q)
  have hprs : ∀ q q' : σ, q ≠ q' → (q, q') ∈ prs := by
    intro q q' hne
    rw [hprsdef, List.mem_filter]
    exact ⟨Finset.mem_toList.2 (Finset.mem_univ _), by simpa using hne⟩
  have hprs' : ∀ z ∈ prs, z.1 ≠ z.2 := by
    intro z hz
    rw [hprsdef, List.mem_filter] at hz
    simpa using hz.2
  have hqas : ∀ (q : σ) (a : A), (q, a) ∈ qas :=
    fun q a => Finset.mem_toList.2 (Finset.mem_univ _)
  have haccs : ∀ q : σ, q ∈ accs ↔ q ∈ D.accept := by
    intro q
    rw [haccsdef, List.mem_filter]
    simp
  by_cases hstart : D.start ∈ D.accept
  · refine ⟨MSO.or (runF D e ls qs prs qas accs) (emptyF A), fun w fo so => ?_⟩
    rw [satOr, sat_runF_iff D e ls qs prs qas accs hls hqs hprs hprs' hqas haccs,
      sat_emptyF]
    constructor
    · rintro (⟨-, hacc⟩ | rfl)
      · exact hacc
      · rw [DFA.mem_accepts, DFA.eval_nil]
        exact hstart
    · intro hacc
      by_cases hne : w = []
      · exact Or.inr hne
      · exact Or.inl ⟨hne, hacc⟩
  · refine ⟨runF D e ls qs prs qas accs, fun w fo so => ?_⟩
    rw [sat_runF_iff D e ls qs prs qas accs hls hqs hprs hprs' hqas haccs]
    constructor
    · rintro ⟨-, hacc⟩; exact hacc
    · intro hacc
      refine ⟨?_, hacc⟩
      rintro rfl
      rw [DFA.mem_accepts, DFA.eval_nil] at hacc
      exact hstart hacc

/-- **Theorem `thm:mso-logic-languages`** (Büchi-Elgot-Trakhtenbrot).  A language of finite strings
is regular if and only if it is definable in monadic second-order logic. -/
theorem regular_iff_msoDefinable_aux {A : Type} [Finite A] (L : Language A) :
    L.IsRegular ↔ MSODefinable L :=
  ⟨msoDefinable_of_isRegular, isRegular_of_msoDefinable⟩

end MSOBuchi

export MSOBuchi (regular_iff_msoDefinable_aux)

end Lax916827Proofs.Transducers
