/-
Elementary syntactic facts about the monadic second-order formulas of
Section *Logic* of *Transducers* (M. Bojańczyk):

* satisfaction depends on the valuation only through the free variables
  (`MSO.sat_congr`);
* the syntactic list of variables of a formula, which bounds its free variables
  (`MSO.freeFO_lt_foBound`, `MSO.freeSO_lt_soBound`);
* finite conjunctions and disjunctions (`MSO.bigAnd`, `MSO.bigOr`);
* the existential closure of a formula (`MSO.closeFO`, `MSO.closeSO`), used to
  turn a formula whose truth value does not depend on the valuation into a
  sentence.
-/
import Lax916827Proofs.Source.PartC.MSODef
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers
namespace MSO

variable {A : Type}

/-! ## Satisfaction depends only on the free variables -/

lemma sat_congr (w : List A) : ∀ (φ : MSO A) (fo fo' : ℕ → ℕ) (so so' : ℕ → Set ℕ),
    (∀ i ∈ φ.freeFO, fo i = fo' i) → (∀ j ∈ φ.freeSO, so j = so' j) →
    (Sat w fo so φ ↔ Sat w fo' so' φ) := by
  intro φ
  induction φ with
  | le i j =>
    intro fo fo' so so' hfo _
    have h1 : fo i = fo' i := hfo i (by simp [freeFO])
    have h2 : fo j = fo' j := hfo j (by simp [freeFO])
    simp [Sat, h1, h2]
  | lab a i =>
    intro fo fo' so so' hfo _
    have h1 : fo i = fo' i := hfo i (by simp [freeFO])
    simp [Sat, h1]
  | mem i j =>
    intro fo fo' so so' hfo hso
    have h1 : fo i = fo' i := hfo i (by simp [freeFO])
    have h2 : so j = so' j := hso j (by simp [freeSO])
    simp [Sat, h1, h2]
  | not φ ih =>
    intro fo fo' so so' hfo hso
    simp only [Sat]
    rw [ih fo fo' so so' hfo hso]
  | and φ ψ ihφ ihψ =>
    intro fo fo' so so' hfo hso
    simp only [Sat]
    rw [ihφ fo fo' so so' (fun i hi => hfo i (Or.inl hi)) (fun j hj => hso j (Or.inl hj)),
      ihψ fo fo' so so' (fun i hi => hfo i (Or.inr hi)) (fun j hj => hso j (Or.inr hj))]
  | or φ ψ ihφ ihψ =>
    intro fo fo' so so' hfo hso
    simp only [Sat]
    rw [ihφ fo fo' so so' (fun i hi => hfo i (Or.inl hi)) (fun j hj => hso j (Or.inl hj)),
      ihψ fo fo' so so' (fun i hi => hfo i (Or.inr hi)) (fun j hj => hso j (Or.inr hj))]
  | exFO i φ ih =>
    intro fo fo' so so' hfo hso
    simp only [Sat]
    refine exists_congr fun p => and_congr_right fun _ => ?_
    refine ih _ _ _ _ ?_ hso
    intro x hx
    by_cases hxi : x = i
    · subst hxi
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hxi, Function.update_of_ne hxi]
      exact hfo x ⟨hx, hxi⟩
  | exSO j φ ih =>
    intro fo fo' so so' hfo hso
    simp only [Sat]
    refine exists_congr fun S => and_congr_right fun _ => ?_
    refine ih _ _ _ _ hfo ?_
    intro x hx
    by_cases hxj : x = j
    · subst hxj
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hxj, Function.update_of_ne hxj]
      exact hso x ⟨hx, hxj⟩

/-! ## The syntactic variables of a formula -/

/-- All first-order variables occurring in a formula. -/
def foVars : MSO A → List ℕ
  | le i j => [i, j]
  | lab _ i => [i]
  | mem i _ => [i]
  | not φ => foVars φ
  | and φ ψ => foVars φ ++ foVars ψ
  | or φ ψ => foVars φ ++ foVars ψ
  | exFO i φ => i :: foVars φ
  | exSO _ φ => foVars φ

/-- All second-order variables occurring in a formula. -/
def soVars : MSO A → List ℕ
  | le _ _ => []
  | lab _ _ => []
  | mem _ j => [j]
  | not φ => soVars φ
  | and φ ψ => soVars φ ++ soVars ψ
  | or φ ψ => soVars φ ++ soVars ψ
  | exFO _ φ => soVars φ
  | exSO j φ => j :: soVars φ

lemma freeFO_subset_foVars (φ : MSO A) : φ.freeFO ⊆ {i | i ∈ φ.foVars} := by
  induction φ with
  | le i j => intro x hx; rcases hx with rfl | rfl <;> simp [foVars]
  | lab a i => intro x hx; simp only [freeFO, Set.mem_singleton_iff] at hx; simp [foVars, hx]
  | mem i j => intro x hx; simp only [freeFO, Set.mem_singleton_iff] at hx; simp [foVars, hx]
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ =>
    intro x hx
    rcases hx with hx | hx
    · simpa [foVars] using Or.inl (ihφ hx)
    · simpa [foVars] using Or.inr (ihψ hx)
  | or φ ψ ihφ ihψ =>
    intro x hx
    rcases hx with hx | hx
    · simpa [foVars] using Or.inl (ihφ hx)
    · simpa [foVars] using Or.inr (ihψ hx)
  | exFO i φ ih => intro x hx; simpa [foVars] using Or.inr (ih hx.1)
  | exSO j φ ih => intro x hx; simpa [foVars] using ih hx

lemma freeSO_subset_soVars (φ : MSO A) : φ.freeSO ⊆ {j | j ∈ φ.soVars} := by
  induction φ with
  | le i j => intro x hx; simp [freeSO] at hx
  | lab a i => intro x hx; simp [freeSO] at hx
  | mem i j => intro x hx; simp only [freeSO, Set.mem_singleton_iff] at hx; simp [soVars, hx]
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ =>
    intro x hx
    rcases hx with hx | hx
    · simpa [soVars] using Or.inl (ihφ hx)
    · simpa [soVars] using Or.inr (ihψ hx)
  | or φ ψ ihφ ihψ =>
    intro x hx
    rcases hx with hx | hx
    · simpa [soVars] using Or.inl (ihφ hx)
    · simpa [soVars] using Or.inr (ihψ hx)
  | exFO i φ ih => intro x hx; simpa [soVars] using ih hx
  | exSO j φ ih => intro x hx; simpa [soVars] using Or.inr (ih hx.1)

private lemma le_foldr_max (l : List ℕ) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · have := ih x hx
      simp only [List.foldr_cons]
      omega

/-- A bound on the first-order variables of a formula. -/
def foBound (φ : MSO A) : ℕ := (φ.foVars).foldr max 0 + 1

/-- A bound on the second-order variables of a formula. -/
def soBound (φ : MSO A) : ℕ := (φ.soVars).foldr max 0 + 1

lemma freeFO_lt_foBound (φ : MSO A) : φ.freeFO ⊆ {i | i < φ.foBound} := by
  intro x hx
  have := le_foldr_max _ x (freeFO_subset_foVars φ hx)
  simp only [Set.mem_setOf_eq, foBound]
  omega

lemma freeSO_lt_soBound (φ : MSO A) : φ.freeSO ⊆ {j | j < φ.soBound} := by
  intro x hx
  have := le_foldr_max _ x (freeSO_subset_soVars φ hx)
  simp only [Set.mem_setOf_eq, soBound]
  omega

/-! ## Finite conjunctions and disjunctions -/

/-- A formula that is always true. -/
def tt : MSO A := MSO.le 0 0

/-- A formula that is always false. -/
def ff : MSO A := MSO.not tt

@[simp] lemma sat_tt (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) : Sat w fo so tt := by
  simp [tt, Sat]

@[simp] lemma sat_ff (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) : ¬ Sat w fo so ff := by
  simp [ff, Sat]

/-- The conjunction of a list of formulas. -/
def bigAnd (l : List (MSO A)) : MSO A := l.foldr MSO.and tt

/-- The disjunction of a list of formulas. -/
def bigOr (l : List (MSO A)) : MSO A := l.foldr MSO.or ff

lemma sat_bigAnd (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (l : List (MSO A)) :
    Sat w fo so (bigAnd l) ↔ ∀ φ ∈ l, Sat w fo so φ := by
  induction l with
  | nil => simp [bigAnd]
  | cons φ l ih =>
    have hcons : Sat w fo so (bigAnd (φ :: l))
        ↔ (Sat w fo so φ ∧ Sat w fo so (bigAnd l)) := Iff.rfl
    rw [hcons, ih]
    constructor
    · rintro ⟨h1, h2⟩ ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact h1
      · exact h2 ψ hψ
    · intro h
      exact ⟨h φ (by simp), fun ψ hψ => h ψ (by simp [hψ])⟩

lemma sat_bigOr (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (l : List (MSO A)) :
    Sat w fo so (bigOr l) ↔ ∃ φ ∈ l, Sat w fo so φ := by
  induction l with
  | nil => simp [bigOr]
  | cons φ l ih =>
    have hcons : Sat w fo so (bigOr (φ :: l))
        ↔ (Sat w fo so φ ∨ Sat w fo so (bigOr l)) := Iff.rfl
    rw [hcons, ih]
    constructor
    · rintro (h1 | ⟨ψ, hψ, h2⟩)
      · exact ⟨φ, by simp, h1⟩
      · exact ⟨ψ, by simp [hψ], h2⟩
    · rintro ⟨ψ, hψ, h⟩
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hψ, h⟩

/-! ## Existential closure -/

/-- Existentially quantify a list of first-order variables. -/
def closeFO (φ : MSO A) (is : List ℕ) : MSO A := is.foldr MSO.exFO φ

/-- Existentially quantify a list of second-order variables. -/
def closeSO (φ : MSO A) (js : List ℕ) : MSO A := js.foldr MSO.exSO φ

lemma freeFO_closeFO (φ : MSO A) (is : List ℕ) :
    (closeFO φ is).freeFO ⊆ φ.freeFO \ {i | i ∈ is} := by
  induction is with
  | nil => simp [closeFO]
  | cons i is ih =>
    intro x hx
    have hx' : x ∈ (closeFO φ is).freeFO ∧ x ≠ i := hx
    have := ih hx'.1
    refine ⟨this.1, ?_⟩
    simp only [Set.mem_setOf_eq, List.mem_cons, not_or]
    exact ⟨hx'.2, this.2⟩

lemma freeSO_closeFO (φ : MSO A) (is : List ℕ) : (closeFO φ is).freeSO = φ.freeSO := by
  induction is with
  | nil => rfl
  | cons i is ih => simpa [closeFO, freeSO] using ih

lemma freeSO_closeSO (φ : MSO A) (js : List ℕ) :
    (closeSO φ js).freeSO ⊆ φ.freeSO \ {j | j ∈ js} := by
  induction js with
  | nil => simp [closeSO]
  | cons j js ih =>
    intro x hx
    have hx' : x ∈ (closeSO φ js).freeSO ∧ x ≠ j := hx
    have := ih hx'.1
    refine ⟨this.1, ?_⟩
    simp only [Set.mem_setOf_eq, List.mem_cons, not_or]
    exact ⟨hx'.2, this.2⟩

lemma freeFO_closeSO (φ : MSO A) (js : List ℕ) : (closeSO φ js).freeFO = φ.freeFO := by
  induction js with
  | nil => rfl
  | cons j js ih => simpa [closeSO, freeFO] using ih

lemma sat_closeFO_of_forall {w : List A} {φ : MSO A} (hne : w ≠ [])
    (h : ∀ fo so, Sat w fo so φ) (is : List ℕ) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (closeFO φ is) := by
  induction is generalizing fo with
  | nil => exact h fo so
  | cons i is ih =>
    refine ⟨0, ?_, ih _⟩
    cases w with
    | nil => exact absurd rfl hne
    | cons a w => simp

lemma exists_sat_of_sat_closeFO {w : List A} {φ : MSO A} (is : List ℕ) :
    ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ), Sat w fo so (closeFO φ is) → ∃ fo', Sat w fo' so φ := by
  induction is with
  | nil => intro fo so h; exact ⟨fo, h⟩
  | cons i is ih =>
    intro fo so h
    obtain ⟨p, _, hp⟩ := h
    exact ih _ so hp

lemma sat_closeSO_of_forall {w : List A} {φ : MSO A}
    (h : ∀ fo so, Sat w fo so φ) (js : List ℕ) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (closeSO φ js) := by
  induction js generalizing so with
  | nil => exact h fo so
  | cons j js ih => exact ⟨∅, by simp, ih _⟩

lemma exists_sat_of_sat_closeSO {w : List A} {φ : MSO A} (js : List ℕ) :
    ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ), Sat w fo so (closeSO φ js) → ∃ so', Sat w fo so' φ := by
  induction js with
  | nil => intro fo so h; exact ⟨so, h⟩
  | cons j js ih =>
    intro fo so h
    obtain ⟨S, _, hS⟩ := h
    exact ih fo _ hS

/-! ## Universal quantification and implication -/

/-- Universal quantification, as an abbreviation. -/
def allF (i : ℕ) (φ : MSO A) : MSO A := MSO.not (MSO.exFO i (MSO.not φ))

/-- Implication, as an abbreviation. -/
def impF (φ ψ : MSO A) : MSO A := MSO.or (MSO.not φ) ψ

lemma sat_allF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (i : ℕ) (φ : MSO A) :
    Sat w fo so (allF i φ) ↔ ∀ p < w.length, Sat w (Function.update fo i p) so φ := by
  classical
  simp only [allF, Sat, not_exists, not_and, not_not]

lemma sat_impF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (φ ψ : MSO A) :
    Sat w fo so (impF φ ψ) ↔ (Sat w fo so φ → Sat w fo so ψ) := by
  classical
  simp only [impF, Sat]
  tauto

/-- The existential closure of a list of second-order variables holds as soon as
the variables of the list can be given values making the formula true. -/
lemma sat_closeSO_of_exists {w : List A} {φ : MSO A} (js : List ℕ) :
    ∀ (fo : ℕ → ℕ) (so so' : ℕ → Set ℕ), (∀ j ∈ js, so' j ⊆ {p | p < w.length}) →
      (∀ j, j ∉ js → so' j = so j) → Sat w fo so' φ → Sat w fo so (closeSO φ js) := by
  induction js with
  | nil =>
    intro fo so so' _ hout hsat
    have : so' = so := funext fun j => hout j (by simp)
    rwa [this] at hsat
  | cons j js ih =>
    intro fo so so' hsub hout hsat
    refine ⟨so' j, hsub j (by simp), ?_⟩
    refine ih fo (Function.update so j (so' j)) so' (fun m hm => hsub m (by simp [hm]))
      (fun m hm => ?_) hsat
    by_cases hmj : m = j
    · subst hmj; rw [Function.update_self]
    · rw [Function.update_of_ne hmj]
      exact hout m (by simp [hmj, hm])

end MSO
end Lax916827Proofs.Transducers
