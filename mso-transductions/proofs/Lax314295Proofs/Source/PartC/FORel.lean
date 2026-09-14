/-
Relativisation of a first-order formula to a prefix or to a suffix of the input
string, used in Section *The first-order fragment* of *Transducers* (M. Bojańczyk).

The book's proof of Lemma `lem:k-types-fo-equivalence` ("the formulas from the induction
assumption need to have their quantification restricted to positions that are `< x` for `w₁` and `>
x` for `w₂`, but this does not affect the quantifier rank") and the proof of the implication
"aperiodic ⇒ first-order definable" of Theorem `thm:logic-aperiodic` both need to say, inside a
formula, that another formula holds in a prefix or in a suffix of the input string.

`MSO.relGuard g φ` relativises every quantifier of `φ` by the guard `g`: the
quantifier `∃ x_i` becomes `∃ x_i (g i ∧ ⋯)`.  The three instances used are
`relLt v` (positions `< x_v`), `relLe v` (positions `≤ x_v`) and `relGt v`
(positions `> x_v`).  Relativisation does not change the quantifier rank and
preserves first-orderness.
-/
import Lax916827Proofs.Source.PartC.MSOSyntax
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace MSO
export Lax916827Proofs.Transducers.MSO (le lab mem not and or exFO exSO Sat freeFO freeSO foVars qrank bigAnd bigOr tt ff)

variable {A : Type}

/-! ## Guarded relativisation -/

/-- The formula `x_i < x_j`. -/
def ltVar (i j : ℕ) : MSO A := and (le i j) (not (le j i))

lemma sat_ltVar (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (i j : ℕ) :
    Sat w fo so (ltVar (A := A) i j) ↔ fo i < fo j := by
  show (fo i ≤ fo j ∧ ¬ fo j ≤ fo i) ↔ _
  omega

@[simp] lemma qrank_ltVar (i j : ℕ) : (ltVar (A := A) i j).qrank = 0 := rfl

@[simp] lemma isFO_ltVar (i j : ℕ) : (ltVar (A := A) i j).IsFO := ⟨trivial, trivial⟩

lemma freeFO_ltVar (i j : ℕ) : (ltVar (A := A) i j).freeFO = {i, j} := by
  show ({i, j} ∪ {j, i} : Set ℕ) = {i, j}
  ext x; simp

/-- Relativise every quantifier of a formula by the guard `g`. -/
def relGuard (g : ℕ → MSO A) : MSO A → MSO A
  | le i j => le i j
  | lab a i => lab a i
  | mem i j => mem i j
  | not φ => not (relGuard g φ)
  | and φ ψ => and (relGuard g φ) (relGuard g ψ)
  | or φ ψ => or (relGuard g φ) (relGuard g ψ)
  | exFO i φ => exFO i (and (g i) (relGuard g φ))
  | exSO i φ => exSO i (relGuard g φ)

/-- Relativisation to the positions strictly before `x_v`. -/
def relLt (v : ℕ) (φ : MSO A) : MSO A := relGuard (fun i => ltVar i v) φ

/-- Relativisation to the positions up to and including `x_v`. -/
def relLe (v : ℕ) (φ : MSO A) : MSO A := relGuard (fun i => le i v) φ

/-- Relativisation to the positions strictly after `x_v`. -/
def relGt (v : ℕ) (φ : MSO A) : MSO A := relGuard (fun i => ltVar v i) φ

/-! ## Syntactic properties -/

lemma qrank_relGuard {g : ℕ → MSO A} (hg : ∀ i, (g i).qrank = 0) :
    ∀ φ : MSO A, (relGuard g φ).qrank = φ.qrank := by
  intro φ
  induction φ with
  | le i j => rfl
  | lab a i => rfl
  | mem i j => rfl
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => simp [relGuard, qrank, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [relGuard, qrank, ihφ, ihψ]
  | exFO i φ ih => simp [relGuard, qrank, ih, hg i]
  | exSO i φ ih => simp [relGuard, qrank, ih]

lemma isFO_relGuard {g : ℕ → MSO A} (hg : ∀ i, (g i).IsFO) :
    ∀ φ : MSO A, φ.IsFO → (relGuard g φ).IsFO := by
  intro φ
  induction φ with
  | le i j => exact fun _ => trivial
  | lab a i => exact fun _ => trivial
  | mem i j => exact fun h => h.elim
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | or φ ψ ihφ ihψ => exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | exFO i φ ih => exact fun h => ⟨hg i, ih h⟩
  | exSO i φ _ => exact fun h => h.elim

lemma freeFO_relGuard {g : ℕ → MSO A} {v : ℕ} (hg : ∀ i, (g i).freeFO ⊆ {i, v}) :
    ∀ φ : MSO A, (relGuard g φ).freeFO ⊆ φ.freeFO ∪ {v} := by
  intro φ
  induction φ with
  | le i j => intro x hx; exact Or.inl hx
  | lab a i => intro x hx; exact Or.inl hx
  | mem i j => intro x hx; exact Or.inl hx
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ =>
      intro x hx
      rcases hx with hx | hx
      · rcases ihφ hx with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihψ hx with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | or φ ψ ihφ ihψ =>
      intro x hx
      rcases hx with hx | hx
      · rcases ihφ hx with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihψ hx with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | exFO i φ ih =>
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases hx1 with hx1 | hx1
      · rcases hg i hx1 with h | h
        · exact absurd h hx2
        · exact Or.inr h
      · rcases ih hx1 with h | h
        · exact Or.inl ⟨h, hx2⟩
        · exact Or.inr h
  | exSO i φ ih => exact ih

@[simp] lemma qrank_relLt (v : ℕ) (φ : MSO A) : (relLt v φ).qrank = φ.qrank := by
  show (relGuard (fun i => ltVar i v) φ).qrank = _
  exact qrank_relGuard (g := fun i => ltVar i v) (fun _ => rfl) φ

@[simp] lemma qrank_relLe (v : ℕ) (φ : MSO A) : (relLe v φ).qrank = φ.qrank := by
  show (relGuard (fun i => le i v) φ).qrank = _
  exact qrank_relGuard (g := fun i => le i v) (fun _ => rfl) φ

@[simp] lemma qrank_relGt (v : ℕ) (φ : MSO A) : (relGt v φ).qrank = φ.qrank := by
  show (relGuard (fun i => ltVar v i) φ).qrank = _
  exact qrank_relGuard (g := fun i => ltVar v i) (fun _ => rfl) φ

lemma isFO_relLt (v : ℕ) {φ : MSO A} (h : φ.IsFO) : (relLt v φ).IsFO := by
  show (relGuard (fun i => ltVar i v) φ).IsFO
  exact isFO_relGuard (g := fun i => ltVar i v) (fun _ => isFO_ltVar _ _) φ h

lemma isFO_relLe (v : ℕ) {φ : MSO A} (h : φ.IsFO) : (relLe v φ).IsFO := by
  show (relGuard (fun i => le i v) φ).IsFO
  exact isFO_relGuard (g := fun i => le i v) (fun _ => trivial) φ h

lemma isFO_relGt (v : ℕ) {φ : MSO A} (h : φ.IsFO) : (relGt v φ).IsFO := by
  show (relGuard (fun i => ltVar v i) φ).IsFO
  exact isFO_relGuard (g := fun i => ltVar v i) (fun _ => isFO_ltVar _ _) φ h

lemma freeFO_relLt (v : ℕ) (φ : MSO A) : (relLt v φ).freeFO ⊆ φ.freeFO ∪ {v} := by
  show (relGuard (fun i => ltVar i v) φ).freeFO ⊆ _
  exact freeFO_relGuard (g := fun i => ltVar i v) (v := v) (fun i => by rw [freeFO_ltVar]) φ

lemma freeFO_relLe (v : ℕ) (φ : MSO A) : (relLe v φ).freeFO ⊆ φ.freeFO ∪ {v} := by
  show (relGuard (fun i => le i v) φ).freeFO ⊆ _
  exact freeFO_relGuard (g := fun i => le i v) (v := v) (fun i => by intro x hx; exact hx) φ

lemma freeFO_relGt (v : ℕ) (φ : MSO A) : (relGt v φ).freeFO ⊆ φ.freeFO ∪ {v} := by
  show (relGuard (fun i => ltVar v i) φ).freeFO ⊆ _
  refine freeFO_relGuard (g := fun i => ltVar v i) (v := v) (fun i => ?_) φ
  rw [freeFO_ltVar]
  intro x hx
  rcases hx with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## Semantics -/

/-- Relativisation to the positions before `x_v` says that the formula holds in
the prefix of the input that ends just before the position `x_v`. -/
lemma sat_relLt (w : List A) (v : ℕ) : ∀ (φ : MSO A), φ.IsFO → v ∉ φ.foVars →
    ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ), (∀ i ∈ φ.freeFO, fo i < fo v) →
      (Sat w fo so (relLt v φ) ↔ Sat (w.take (fo v)) fo so φ) := by
  intro φ
  induction φ with
  | le i j => intro _ _ fo so _; exact Iff.rfl
  | lab a i =>
      intro _ _ fo so hfree
      have h : fo i < fo v := hfree i rfl
      show (w[fo i]? = some a) ↔ ((w.take (fo v))[fo i]? = some a)
      rw [List.getElem?_take_of_lt h]
  | mem i j => intro h; exact h.elim
  | not φ ih =>
      intro hfo hv fo so hfree
      show ¬ Sat w fo so (relLt v φ) ↔ ¬ Sat (w.take (fo v)) fo so φ
      rw [ih hfo hv fo so hfree]
  | and φ ψ ihφ ihψ =>
      intro hfo hv fo so hfree
      have hv1 : v ∉ φ.foVars := fun h => hv (by simp [foVars, h])
      have hv2 : v ∉ ψ.foVars := fun h => hv (by simp [foVars, h])
      show (Sat w fo so (relLt v φ) ∧ Sat w fo so (relLt v ψ)) ↔ _
      rw [ihφ hfo.1 hv1 fo so (fun i hi => hfree i (Or.inl hi)),
        ihψ hfo.2 hv2 fo so (fun i hi => hfree i (Or.inr hi))]
      exact Iff.rfl
  | or φ ψ ihφ ihψ =>
      intro hfo hv fo so hfree
      have hv1 : v ∉ φ.foVars := fun h => hv (by simp [foVars, h])
      have hv2 : v ∉ ψ.foVars := fun h => hv (by simp [foVars, h])
      show (Sat w fo so (relLt v φ) ∨ Sat w fo so (relLt v ψ)) ↔ _
      rw [ihφ hfo.1 hv1 fo so (fun i hi => hfree i (Or.inl hi)),
        ihψ hfo.2 hv2 fo so (fun i hi => hfree i (Or.inr hi))]
      exact Iff.rfl
  | exFO i φ ih =>
      intro hfo hv fo so hfree
      have hiv : i ≠ v := fun h => hv (by simp [foVars, h])
      have hv' : v ∉ φ.foVars := fun h => hv (by simp [foVars, h])
      show (∃ p < w.length, Sat w (Function.update fo i p) so
          (MSO.and (ltVar i v) (relLt v φ))) ↔
        (∃ p < (w.take (fo v)).length, Sat (w.take (fo v)) (Function.update fo i p) so φ)
      have hup : ∀ p : ℕ, Function.update fo i p v = fo v :=
        fun p => Function.update_of_ne (Ne.symm hiv) _ _
      constructor
      · rintro ⟨p, hp, hlt, hsat⟩
        rw [sat_ltVar] at hlt
        rw [Function.update_self, hup p] at hlt
        refine ⟨p, ?_, ?_⟩
        · rw [List.length_take]; omega
        · have := (ih hfo hv' (Function.update fo i p) so ?_).mp hsat
          · rwa [hup p] at this
          · intro j hj
            rw [hup p]
            by_cases hji : j = i
            · subst hji; rw [Function.update_self]; exact hlt
            · rw [Function.update_of_ne hji]
              exact hfree j ⟨hj, hji⟩
      · rintro ⟨p, hp, hsat⟩
        rw [List.length_take] at hp
        have hplt : p < fo v := by omega
        have hpw : p < w.length := by omega
        refine ⟨p, hpw, ?_, ?_⟩
        · rw [sat_ltVar, Function.update_self, hup p]; exact hplt
        · refine (ih hfo hv' (Function.update fo i p) so ?_).mpr ?_
          · intro j hj
            rw [hup p]
            by_cases hji : j = i
            · subst hji; rw [Function.update_self]; exact hplt
            · rw [Function.update_of_ne hji]
              exact hfree j ⟨hj, hji⟩
          · rwa [hup p]
  | exSO i φ _ => intro h; exact h.elim

/-- Relativisation to the positions up to `x_v` says that the formula holds in
the prefix of the input that ends at the position `x_v`. -/
lemma sat_relLe (w : List A) (v : ℕ) : ∀ (φ : MSO A), φ.IsFO → v ∉ φ.foVars →
    ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ), (∀ i ∈ φ.freeFO, fo i ≤ fo v) →
      (Sat w fo so (relLe v φ) ↔ Sat (w.take (fo v + 1)) fo so φ) := by
  intro φ
  induction φ with
  | le i j => intro _ _ fo so _; exact Iff.rfl
  | lab a i =>
      intro _ _ fo so hfree
      have h : fo i < fo v + 1 := Nat.lt_succ_of_le (hfree i rfl)
      show (w[fo i]? = some a) ↔ ((w.take (fo v + 1))[fo i]? = some a)
      rw [List.getElem?_take_of_lt h]
  | mem i j => intro h; exact h.elim
  | not φ ih =>
      intro hfo hv fo so hfree
      show ¬ Sat w fo so (relLe v φ) ↔ ¬ Sat (w.take (fo v + 1)) fo so φ
      rw [ih hfo hv fo so hfree]
  | and φ ψ ihφ ihψ =>
      intro hfo hv fo so hfree
      have hv1 : v ∉ φ.foVars := fun h => hv (by simp [foVars, h])
      have hv2 : v ∉ ψ.foVars := fun h => hv (by simp [foVars, h])
      show (Sat w fo so (relLe v φ) ∧ Sat w fo so (relLe v ψ)) ↔ _
      rw [ihφ hfo.1 hv1 fo so (fun i hi => hfree i (Or.inl hi)),
        ihψ hfo.2 hv2 fo so (fun i hi => hfree i (Or.inr hi))]
      exact Iff.rfl
  | or φ ψ ihφ ihψ =>
      intro hfo hv fo so hfree
      have hv1 : v ∉ φ.foVars := fun h => hv (by simp [foVars, h])
      have hv2 : v ∉ ψ.foVars := fun h => hv (by simp [foVars, h])
      show (Sat w fo so (relLe v φ) ∨ Sat w fo so (relLe v ψ)) ↔ _
      rw [ihφ hfo.1 hv1 fo so (fun i hi => hfree i (Or.inl hi)),
        ihψ hfo.2 hv2 fo so (fun i hi => hfree i (Or.inr hi))]
      exact Iff.rfl
  | exFO i φ ih =>
      intro hfo hv fo so hfree
      have hiv : i ≠ v := fun h => hv (by simp [foVars, h])
      have hv' : v ∉ φ.foVars := fun h => hv (by simp [foVars, h])
      show (∃ p < w.length, Sat w (Function.update fo i p) so
          (MSO.and (MSO.le i v) (relLe v φ))) ↔
        (∃ p < (w.take (fo v + 1)).length, Sat (w.take (fo v + 1)) (Function.update fo i p) so φ)
      have hup : ∀ p : ℕ, Function.update fo i p v = fo v :=
        fun p => Function.update_of_ne (Ne.symm hiv) _ _
      constructor
      · rintro ⟨p, hp, hlt, hsat⟩
        have hlt' : p ≤ fo v := by
          have : Function.update fo i p i ≤ Function.update fo i p v := hlt
          rwa [Function.update_self, hup p] at this
        refine ⟨p, ?_, ?_⟩
        · rw [List.length_take]; omega
        · have := (ih hfo hv' (Function.update fo i p) so ?_).mp hsat
          · rwa [hup p] at this
          · intro j hj
            rw [hup p]
            by_cases hji : j = i
            · subst hji; rw [Function.update_self]; exact hlt'
            · rw [Function.update_of_ne hji]
              exact hfree j ⟨hj, hji⟩
      · rintro ⟨p, hp, hsat⟩
        rw [List.length_take] at hp
        have hple : p ≤ fo v := by omega
        have hpw : p < w.length := by omega
        refine ⟨p, hpw, ?_, ?_⟩
        · show Function.update fo i p i ≤ Function.update fo i p v
          rw [Function.update_self, hup p]; exact hple
        · refine (ih hfo hv' (Function.update fo i p) so ?_).mpr ?_
          · intro j hj
            rw [hup p]
            by_cases hji : j = i
            · subst hji; rw [Function.update_self]; exact hple
            · rw [Function.update_of_ne hji]
              exact hfree j ⟨hj, hji⟩
          · rwa [hup p]
  | exSO i φ _ => intro h; exact h.elim

/-- Relativisation to the positions after `x_v` says that the formula holds in
the suffix of the input that starts just after the position `x_v`; the
valuation of the free variables is shifted accordingly. -/
lemma sat_relGt (w : List A) (v : ℕ) : ∀ (φ : MSO A), φ.IsFO → v ∉ φ.foVars →
    ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ), (∀ i ∈ φ.freeFO, fo v < fo i) →
      (Sat w fo so (relGt v φ) ↔
        Sat (w.drop (fo v + 1)) (fun i => fo i - (fo v + 1)) so φ) := by
  intro φ
  induction φ with
  | le i j =>
      intro _ _ fo so hfree
      have h1 : fo v < fo i := hfree i (Or.inl rfl)
      have h2 : fo v < fo j := hfree j (Or.inr rfl)
      show (fo i ≤ fo j) ↔ (fo i - (fo v + 1) ≤ fo j - (fo v + 1))
      omega
  | lab a i =>
      intro _ _ fo so hfree
      have h : fo v < fo i := hfree i rfl
      show (w[fo i]? = some a) ↔ ((w.drop (fo v + 1))[fo i - (fo v + 1)]? = some a)
      rw [List.getElem?_drop, show fo v + 1 + (fo i - (fo v + 1)) = fo i by omega]
  | mem i j => intro h; exact h.elim
  | not φ ih =>
      intro hfo hv fo so hfree
      show ¬ Sat w fo so (relGt v φ) ↔ ¬ Sat (w.drop (fo v + 1)) _ so φ
      rw [ih hfo hv fo so hfree]
  | and φ ψ ihφ ihψ =>
      intro hfo hv fo so hfree
      have hv1 : v ∉ φ.foVars := fun h => hv (by simp [foVars, h])
      have hv2 : v ∉ ψ.foVars := fun h => hv (by simp [foVars, h])
      show (Sat w fo so (relGt v φ) ∧ Sat w fo so (relGt v ψ)) ↔ _
      rw [ihφ hfo.1 hv1 fo so (fun i hi => hfree i (Or.inl hi)),
        ihψ hfo.2 hv2 fo so (fun i hi => hfree i (Or.inr hi))]
      exact Iff.rfl
  | or φ ψ ihφ ihψ =>
      intro hfo hv fo so hfree
      have hv1 : v ∉ φ.foVars := fun h => hv (by simp [foVars, h])
      have hv2 : v ∉ ψ.foVars := fun h => hv (by simp [foVars, h])
      show (Sat w fo so (relGt v φ) ∨ Sat w fo so (relGt v ψ)) ↔ _
      rw [ihφ hfo.1 hv1 fo so (fun i hi => hfree i (Or.inl hi)),
        ihψ hfo.2 hv2 fo so (fun i hi => hfree i (Or.inr hi))]
      exact Iff.rfl
  | exFO i φ ih =>
      intro hfo hv fo so hfree
      have hiv : i ≠ v := fun h => hv (by simp [foVars, h])
      have hv' : v ∉ φ.foVars := fun h => hv (by simp [foVars, h])
      show (∃ r < w.length, Sat w (Function.update fo i r) so
          (MSO.and (ltVar v i) (relGt v φ))) ↔
        (∃ s < (w.drop (fo v + 1)).length,
          Sat (w.drop (fo v + 1)) (Function.update (fun j => fo j - (fo v + 1)) i s) so φ)
      have hup : ∀ r : ℕ, Function.update fo i r v = fo v :=
        fun r => Function.update_of_ne (Ne.symm hiv) _ _
      have hshift : ∀ r : ℕ, (fun j => Function.update fo i r j - (fo v + 1))
          = Function.update (fun j => fo j - (fo v + 1)) i (r - (fo v + 1)) := by
        intro r
        funext j
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
      have hfree' : ∀ (r : ℕ), fo v < r → ∀ j ∈ φ.freeFO,
          Function.update fo i r v < Function.update fo i r j := by
        intro r hr j hj
        rw [hup r]
        by_cases hji : j = i
        · subst hji; rw [Function.update_self]; exact hr
        · rw [Function.update_of_ne hji]; exact hfree j ⟨hj, hji⟩
      constructor
      · rintro ⟨r, hr, hlt, hsat⟩
        rw [sat_ltVar, Function.update_self, hup r] at hlt
        have := (ih hfo hv' (Function.update fo i r) so (hfree' r hlt)).mp hsat
        rw [hup r, hshift r] at this
        exact ⟨r - (fo v + 1), by rw [List.length_drop]; omega, this⟩
      · rintro ⟨s, hs, hsat⟩
        rw [List.length_drop] at hs
        refine ⟨s + (fo v + 1), by omega, ?_, ?_⟩
        · rw [sat_ltVar, Function.update_self, hup]; omega
        · refine (ih hfo hv' (Function.update fo i (s + (fo v + 1))) so
            (hfree' _ (by omega))).mpr ?_
          rw [hup, hshift, show s + (fo v + 1) - (fo v + 1) = s by omega]
          exact hsat
  | exSO i φ _ => intro h; exact h.elim

/-! ## Sentences -/

/-- A first-order formula has no free set variables. -/
lemma freeSO_eq_empty_of_isFO : ∀ φ : MSO A, φ.IsFO → φ.freeSO = ∅ := by
  intro φ
  induction φ with
  | le i j => intro _; rfl
  | lab a i => intro _; rfl
  | mem i j => intro h; exact h.elim
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => intro h; rw [freeSO, ihφ h.1, ihψ h.2]; simp
  | or φ ψ ihφ ihψ => intro h; rw [freeSO, ihφ h.1, ihψ h.2]; simp
  | exFO i φ ih => exact ih
  | exSO i φ _ => intro h; exact h.elim

/-- The truth value of a first-order sentence does not depend on the
valuation. -/
lemma sat_sentence_congr {φ : MSO A} (hfo : φ.IsFO) (hfree : φ.freeFO = ∅) (w : List A)
    (fo fo' : ℕ → ℕ) (so so' : ℕ → Set ℕ) : Sat w fo so φ ↔ Sat w fo' so' φ :=
  MSO.sat_congr w φ fo fo' so so' (fun i hi => absurd (hfree ▸ hi) (Set.notMem_empty i))
    (fun j hj => absurd ((freeSO_eq_empty_of_isFO φ hfo) ▸ hj) (Set.notMem_empty j))

end MSO
end Lax314295Proofs.Transducers
