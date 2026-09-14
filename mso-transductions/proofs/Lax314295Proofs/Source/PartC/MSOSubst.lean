/-
A small hygiene toolkit for the mso formulas of `RequestProject/PartC/MSODef.lean`.

The semantics of `MSO.Sat` evaluates a formula in a valuation of *all* variables,
and the formulas of an mso transduction (Definition `def:mso-transduction`) are used with the two
special valuations

  `fun _ => x`                          (one free variable)
  `fun i => if i = 0 then x else y`     (two free variables).

In order to build compound formulas -- "`x` is the first element of the output
order", "the successor of `x` is to the left", and so on -- one has to plug such
a formula in under a quantifier, with the free variables bound to chosen
variables of the ambient formula.  This file provides the two combinators that
do that:

* `MSO.atv v φ`, whose value is the value of `φ` under the valuation
  `fun _ => x_v`, and
* `MSO.atv2 v₀ v₁ φ`, whose value is the value of `φ` under the valuation
  `fun i => if i = 0 then x_{v₀} else x_{v₁}`,

both for an arbitrary ambient valuation, and both under the sole assumption that
the values of the variables `v`, resp. `v₀` and `v₁`, are positions of the input
string.  They are built from an injective renaming of *all* variables (which
moves the formula out of the way of the ambient ones) followed by existential
quantifications that pin the moved variables to the chosen ones.
-/
import Lax916827Proofs.Source.PartC.MSODef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace MSO
export Lax916827Proofs.Transducers.MSO (le lab mem not and or exFO exSO Sat IsFO qrank freeFO freeSO)

variable {A : Type}

/-! ## Renaming all variables -/

/-- Rename every variable occurrence, free or bound, by `r`. -/
def rename (r : ℕ → ℕ) : MSO A → MSO A
  | le i j => le (r i) (r j)
  | lab a i => lab a (r i)
  | mem i j => mem (r i) (r j)
  | not φ => not (rename r φ)
  | and φ ψ => and (rename r φ) (rename r ψ)
  | or φ ψ => or (rename r φ) (rename r ψ)
  | exFO i φ => exFO (r i) (rename r φ)
  | exSO i φ => exSO (r i) (rename r φ)

lemma update_comp_of_injective {r : ℕ → ℕ} (hr : Function.Injective r) (fo : ℕ → ℕ) (i p : ℕ) :
    (Function.update fo (r i) p) ∘ r = Function.update (fo ∘ r) i p := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · have : r j ≠ r i := fun hc => h (hr hc)
    simp [Function.update_of_ne, h, this]

lemma update_comp_of_injective' {r : ℕ → ℕ} (hr : Function.Injective r) (so : ℕ → Set ℕ)
    (i : ℕ) (S : Set ℕ) :
    (Function.update so (r i) S) ∘ r = Function.update (so ∘ r) i S := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · have : r j ≠ r i := fun hc => h (hr hc)
    simp [Function.update_of_ne, h, this]

/-- Renaming all variables by an injective map does not change the meaning of a
formula, up to composing the valuations with the renaming. -/
lemma sat_rename {r : ℕ → ℕ} (hr : Function.Injective r) (w : List A) :
    ∀ (φ : MSO A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      Sat w fo so (rename r φ) ↔ Sat w (fo ∘ r) (so ∘ r) φ := by
  intro φ
  induction φ with
  | le i j => intro fo so; rfl
  | lab a i => intro fo so; rfl
  | mem i j => intro fo so; rfl
  | not φ ih => intro fo so; simp only [rename, Sat, ih]
  | and φ ψ ihφ ihψ => intro fo so; simp only [rename, Sat, ihφ, ihψ]
  | or φ ψ ihφ ihψ => intro fo so; simp only [rename, Sat, ihφ, ihψ]
  | exFO i φ ih =>
      intro fo so
      simp only [rename, Sat, ih]
      constructor
      · rintro ⟨p, hp, h⟩
        exact ⟨p, hp, by rwa [update_comp_of_injective hr] at h⟩
      · rintro ⟨p, hp, h⟩
        exact ⟨p, hp, by rwa [update_comp_of_injective hr]⟩
  | exSO i φ ih =>
      intro fo so
      simp only [rename, Sat, ih]
      constructor
      · rintro ⟨S, hS, h⟩
        exact ⟨S, hS, by rwa [update_comp_of_injective' hr] at h⟩
      · rintro ⟨S, hS, h⟩
        exact ⟨S, hS, by rwa [update_comp_of_injective' hr]⟩

/-! ## A bound on the variables -/

/-- A bound on all variable indices occurring in a formula. -/
def maxVar : MSO A → ℕ
  | le i j => max i j + 1
  | lab _ i => i + 1
  | mem i j => max i j + 1
  | not φ => maxVar φ
  | and φ ψ => max (maxVar φ) (maxVar ψ)
  | or φ ψ => max (maxVar φ) (maxVar ψ)
  | exFO i φ => max (i + 1) (maxVar φ)
  | exSO i φ => max (i + 1) (maxVar φ)

lemma freeFO_lt_maxVar : ∀ (φ : MSO A) {i : ℕ}, i ∈ φ.freeFO → i < (MSO.maxVar φ) := by
  intro φ
  induction φ with
  | le a b => intro i hi; rcases hi with h | h <;> subst h <;> simp [maxVar]
  | lab a b => intro i hi; rw [show i = b from hi]; simp [maxVar]
  | mem a b => intro i hi; rw [show i = a from hi]; simp [maxVar]
  | not φ ih => intro i hi; exact ih hi
  | and φ ψ ihφ ihψ =>
      intro i hi
      rcases hi with h | h
      · exact lt_of_lt_of_le (ihφ h) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihψ h) (le_max_right _ _)
  | or φ ψ ihφ ihψ =>
      intro i hi
      rcases hi with h | h
      · exact lt_of_lt_of_le (ihφ h) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihψ h) (le_max_right _ _)
  | exFO j φ ih =>
      intro i hi
      exact lt_of_lt_of_le (ih hi.1) (le_max_right _ _)
  | exSO j φ ih =>
      intro i hi
      exact lt_of_lt_of_le (ih hi) (le_max_right _ _)

lemma freeSO_lt_maxVar : ∀ (φ : MSO A) {i : ℕ}, i ∈ φ.freeSO → i < (MSO.maxVar φ) := by
  intro φ
  induction φ with
  | le a b => intro i hi; exact absurd hi (by simp [freeSO])
  | lab a b => intro i hi; exact absurd hi (by simp [freeSO])
  | mem a b => intro i hi; rw [show i = b from hi]; simp [maxVar]
  | not φ ih => intro i hi; exact ih hi
  | and φ ψ ihφ ihψ =>
      intro i hi
      rcases hi with h | h
      · exact lt_of_lt_of_le (ihφ h) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihψ h) (le_max_right _ _)
  | or φ ψ ihφ ihψ =>
      intro i hi
      rcases hi with h | h
      · exact lt_of_lt_of_le (ihφ h) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihψ h) (le_max_right _ _)
  | exFO j φ ih =>
      intro i hi
      exact lt_of_lt_of_le (ih hi) (le_max_right _ _)
  | exSO j φ ih =>
      intro i hi
      exact lt_of_lt_of_le (ih hi.1) (le_max_right _ _)

/-- Satisfaction only depends on the values of the free variables. -/
lemma sat_congr (w : List A) :
    ∀ (φ : MSO A) (fo fo' : ℕ → ℕ) (so so' : ℕ → Set ℕ),
      (∀ i ∈ φ.freeFO, fo i = fo' i) → (∀ j ∈ φ.freeSO, so j = so' j) →
      (Sat w fo so φ ↔ Sat w fo' so' φ) := by
  intro φ
  induction φ with
  | le a b =>
      intro fo fo' so so' hf _
      have h1 : fo a = fo' a := hf a (by simp [freeFO])
      have h2 : fo b = fo' b := hf b (by simp [freeFO])
      show fo a ≤ fo b ↔ fo' a ≤ fo' b
      rw [h1, h2]
  | lab c b =>
      intro fo fo' so so' hf _
      have h2 : fo b = fo' b := hf b (by simp [freeFO])
      show w[fo b]? = some c ↔ w[fo' b]? = some c
      rw [h2]
  | mem a b =>
      intro fo fo' so so' hf hs
      have h1 : fo a = fo' a := hf a (by simp [freeFO])
      have h2 : so b = so' b := hs b (by simp [freeSO])
      show fo a ∈ so b ↔ fo' a ∈ so' b
      rw [h1, h2]
  | not φ ih =>
      intro fo fo' so so' hf hs
      show ¬ _ ↔ ¬ _
      rw [ih fo fo' so so' hf hs]
  | and φ ψ ihφ ihψ =>
      intro fo fo' so so' hf hs
      show _ ∧ _ ↔ _ ∧ _
      rw [ihφ fo fo' so so' (fun i hi => hf i (Or.inl hi)) (fun j hj => hs j (Or.inl hj)),
        ihψ fo fo' so so' (fun i hi => hf i (Or.inr hi)) (fun j hj => hs j (Or.inr hj))]
  | or φ ψ ihφ ihψ =>
      intro fo fo' so so' hf hs
      show _ ∨ _ ↔ _ ∨ _
      rw [ihφ fo fo' so so' (fun i hi => hf i (Or.inl hi)) (fun j hj => hs j (Or.inl hj)),
        ihψ fo fo' so so' (fun i hi => hf i (Or.inr hi)) (fun j hj => hs j (Or.inr hj))]
  | exFO k φ ih =>
      intro fo fo' so so' hf hs
      show (∃ p < w.length, _) ↔ (∃ p < w.length, _)
      refine exists_congr fun p => and_congr_right fun _ => ?_
      refine ih _ _ _ _ (fun i hi => ?_) hs
      by_cases hik : i = k
      · subst hik; simp
      · rw [Function.update_of_ne hik, Function.update_of_ne hik]
        exact hf i ⟨hi, hik⟩
  | exSO k φ ih =>
      intro fo fo' so so' hf hs
      show (∃ S : Set ℕ, S ⊆ _ ∧ _) ↔ (∃ S : Set ℕ, S ⊆ _ ∧ _)
      refine exists_congr fun S => and_congr_right fun _ => ?_
      refine ih _ _ _ _ hf (fun j hj => ?_)
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
        exact hs j ⟨hj, hjk⟩

/-! ## Pinning variables -/

/-- The formula `x_a = x_b`. -/
def eqVar (a b : ℕ) : MSO A := and (le a b) (le b a)

lemma sat_eqVar (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (a b : ℕ) :
    Sat w fo so (eqVar (A := A) a b) ↔ fo a = fo b := by
  show (fo a ≤ fo b ∧ fo b ≤ fo a) ↔ _
  omega

/-- Bind the variable `u` to the value of the variable `src`. -/
def bindTo (src u : ℕ) (φ : MSO A) : MSO A := exFO u (and (eqVar src u) φ)

lemma sat_bindTo (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) {src u : ℕ} (hne : u ≠ src)
    (hlt : fo src < w.length) (φ : MSO A) :
    Sat w fo so (bindTo src u φ) ↔ Sat w (Function.update fo u (fo src)) so φ := by
  show (∃ p < w.length, Sat w (Function.update fo u p) so (and (eqVar src u) φ)) ↔ _
  constructor
  · rintro ⟨p, hp, heq, hφ⟩
    rw [sat_eqVar] at heq
    rw [Function.update_of_ne (Ne.symm hne), Function.update_self] at heq
    rw [heq]
    exact hφ
  · intro h
    refine ⟨fo src, hlt, ?_, h⟩
    rw [sat_eqVar, Function.update_of_ne (Ne.symm hne), Function.update_self]

/-- Bind the variables `d, d+1, …, d+k-1` to the value of the variable `src`. -/
def bindRange (src d : ℕ) : ℕ → MSO A → MSO A
  | 0, φ => φ
  | k + 1, φ => bindTo src (d + k) (bindRange src d k φ)

lemma sat_bindRange (w : List A) {src d : ℕ} (hsd : src < d) :
    ∀ (k : ℕ) (φ : MSO A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), fo src < w.length →
      (Sat w fo so (bindRange src d k φ) ↔
        Sat w (fun i => if d ≤ i ∧ i < d + k then fo src else fo i) so φ) := by
  intro k
  induction k with
  | zero =>
      intro φ fo so _
      show _ ↔ Sat w (fun i => if d ≤ i ∧ i < d + 0 then fo src else fo i) so φ
      have : (fun i => if d ≤ i ∧ i < d + 0 then fo src else fo i) = fo := by
        funext i; rw [if_neg (by omega)]
      rw [this]
      rfl
  | succ k ih =>
      intro φ fo so hlt
      have hne : d + k ≠ src := by omega
      rw [show bindRange src d (k + 1) φ = bindTo src (d + k) (bindRange src d k φ) from rfl,
        sat_bindTo w fo so hne hlt]
      have hsrc : Function.update fo (d + k) (fo src) src = fo src :=
        Function.update_of_ne (by omega) _ _
      rw [ih φ _ so (by rw [hsrc]; exact hlt), hsrc]
      rw [show (fun i => if d ≤ i ∧ i < d + k then fo src
            else Function.update fo (d + k) (fo src) i)
          = (fun i => if d ≤ i ∧ i < d + (k + 1) then fo src else fo i) from ?_]
      funext i
      by_cases h2 : i = d + k
      · subst h2
        rw [if_neg (by omega), Function.update_self, if_pos (by omega)]
      · by_cases h1 : d ≤ i ∧ i < d + k
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, Function.update_of_ne h2, if_neg (by omega)]

/-- The formula saying that the set variable `X_u` is empty. -/
def emptySet (u : ℕ) : MSO A := not (exFO 0 (mem 0 u))

lemma soUpd_eq (so : ℕ → Set ℕ) (d k : ℕ) :
    (fun j => if d ≤ j ∧ j < d + (k + 1) then (∅ : Set ℕ) else so j)
      = (fun j => if d ≤ j ∧ j < d + k then ∅ else Function.update so (d + k) ∅ j) := by
  funext j
  by_cases h2 : j = d + k
  · subst h2
    rw [if_pos (by omega), if_neg (by omega), Function.update_self]
  · by_cases h1 : d ≤ j ∧ j < d + k
    · rw [if_pos (by omega), if_pos h1]
    · rw [if_neg (by omega), if_neg h1, Function.update_of_ne h2]

/-- Bind the set variables `X_d, …, X_{d+k-1}` to the empty set. -/
def bindSO (d : ℕ) : ℕ → MSO A → MSO A
  | 0, φ => φ
  | k + 1, φ => exSO (d + k) (and (emptySet (d + k)) (bindSO d k φ))

lemma sat_bindSO (w : List A) (d : ℕ) :
    ∀ (k : ℕ) (φ : MSO A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      (Sat w fo so (bindSO d k φ) ↔
        Sat w fo (fun j => if d ≤ j ∧ j < d + k then ∅ else so j) φ) := by
  intro k
  induction k with
  | zero =>
      intro φ fo so
      have : (fun j => if d ≤ j ∧ j < d + 0 then (∅ : Set ℕ) else so j) = so := by
        funext j; rw [if_neg (by omega)]
      rw [this]
      rfl
  | succ k ih =>
      intro φ fo so
      show (∃ S ⊆ {p | p < w.length},
        Sat w fo (Function.update so (d + k) S) (and (emptySet (d + k)) (bindSO d k φ))) ↔ _
      have key : ∀ S : Set ℕ, S ⊆ {p | p < w.length} →
          (Sat w fo (Function.update so (d + k) S) (emptySet (A := A) (d + k)) ↔ S = ∅) := by
        intro S hS
        show (¬ ∃ p < w.length,
          (Function.update fo 0 p) 0 ∈ (Function.update so (d + k) S) (d + k)) ↔ _
        simp only [Function.update_self]
        constructor
        · intro h
          ext p
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hp
          exact h ⟨p, hS hp, hp⟩
        · rintro rfl
          rintro ⟨p, -, hp⟩
          exact hp
      constructor
      · rintro ⟨S, hS, he, hrest⟩
        rw [key S hS] at he
        subst he
        rw [ih φ fo _] at hrest
        rw [soUpd_eq so d k]
        exact hrest
      · intro h
        refine ⟨∅, by simp, ?_, ?_⟩
        · rw [key ∅ (by simp)]
        · rw [ih φ fo _, ← soUpd_eq so d k]
          exact h

/-! ## Shifting -/

/-- Move all variables of a formula above `d`. -/
def shiftUp (d : ℕ) (φ : MSO A) : MSO A := rename (· + d) φ

lemma maxVar_rename_add (d : ℕ) :
    ∀ φ : MSO A, (MSO.maxVar (rename (· + d) φ)) = (MSO.maxVar φ) + d := by
  intro φ
  induction φ with
  | le a b => show max (a + d) (b + d) + 1 = max a b + 1 + d; omega
  | lab a b => show (b + d) + 1 = b + 1 + d; omega
  | mem a b => show max (a + d) (b + d) + 1 = max a b + 1 + d; omega
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => show max _ _ = max _ _ + d; rw [ihφ, ihψ]; omega
  | or φ ψ ihφ ihψ => show max _ _ = max _ _ + d; rw [ihφ, ihψ]; omega
  | exFO j φ ih => show max ((j + d) + 1) _ = max (j + 1) _ + d; rw [ih]; omega
  | exSO j φ ih => show max ((j + d) + 1) _ = max (j + 1) _ + d; rw [ih]; omega

lemma maxVar_shiftUp (d : ℕ) (φ : MSO A) : (MSO.maxVar (shiftUp d φ)) = (MSO.maxVar φ) + d :=
  maxVar_rename_add d φ

lemma sat_shiftUp (w : List A) (d : ℕ) (φ : MSO A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (shiftUp d φ) ↔ Sat w (fun i => fo (i + d)) (fun j => so (j + d)) φ :=
  sat_rename (fun _ _ h => by omega) w φ fo so

/-! ## The two combinators -/

/-- `atv v φ` says that `φ` holds under the valuation that maps every
first-order variable to the value of `x_v` and every set variable to `∅`. -/
def atv (v : ℕ) (φ : MSO A) : MSO A :=
  bindSO (v + 1) (MSO.maxVar (shiftUp (v + 1) φ))
    (bindRange v (v + 1) (MSO.maxVar (shiftUp (v + 1) φ)) (shiftUp (v + 1) φ))

lemma sat_atv (w : List A) (v : ℕ) (φ : MSO A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ)
    (hv : fo v < w.length) :
    Sat w fo so (atv v φ) ↔ Sat w (fun _ => fo v) (fun _ => ∅) φ := by
  set d := v + 1 with hd
  set ψ := shiftUp d φ with hψ
  set k := (MSO.maxVar ψ) with hk
  rw [show atv v φ = bindSO d k (bindRange v d k ψ) from rfl, sat_bindSO w d k, ]
  rw [sat_bindRange w (by omega) k ψ fo _ hv, sat_shiftUp]
  refine sat_congr w φ _ _ _ _ (fun i hi => ?_) (fun j hj => ?_)
  · have h1 : i < MSO.maxVar φ := freeFO_lt_maxVar φ hi
    have h2 : MSO.maxVar φ ≤ k := by rw [hk, hψ, maxVar_shiftUp]; omega
    rw [if_pos (by omega)]
  · have h1 : j < MSO.maxVar φ := freeSO_lt_maxVar φ hj
    have h2 : MSO.maxVar φ ≤ k := by rw [hk, hψ, maxVar_shiftUp]; omega
    rw [if_pos (by omega)]

/-- `atv2 v₀ v₁ φ` says that `φ` holds under the valuation that maps the
variable `x₀` to the value of `x_{v₀}`, every other first-order variable to the
value of `x_{v₁}`, and every set variable to `∅`. -/
def atv2 (v₀ v₁ : ℕ) (φ : MSO A) : MSO A :=
  let d := max v₀ v₁ + 1
  bindSO d (MSO.maxVar (shiftUp d φ))
    (bindTo v₀ d (bindRange v₁ (d + 1) (MSO.maxVar (shiftUp d φ)) (shiftUp d φ)))

lemma sat_atv2 (w : List A) (v₀ v₁ : ℕ) (φ : MSO A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ)
    (h0 : fo v₀ < w.length) (h1 : fo v₁ < w.length) :
    Sat w fo so (atv2 v₀ v₁ φ) ↔
      Sat w (fun i => if i = 0 then fo v₀ else fo v₁) (fun _ => ∅) φ := by
  set d := max v₀ v₁ + 1 with hd
  set ψ := shiftUp d φ with hψ
  set k := (MSO.maxVar ψ) with hk
  rw [show atv2 v₀ v₁ φ = bindSO d k (bindTo v₀ d (bindRange v₁ (d + 1) k ψ)) from rfl,
    sat_bindSO w d k, sat_bindTo w _ _ (by omega) h0]
  have hup : Function.update fo d (fo v₀) v₁ = fo v₁ := Function.update_of_ne (by omega) _ _
  rw [sat_bindRange w (show v₁ < d + 1 by omega) k ψ _ _ (by rw [hup]; exact h1), hup,
    sat_shiftUp]
  refine sat_congr w φ _ _ _ _ (fun i hi => ?_) (fun j hj => ?_)
  · have hlt : i < MSO.maxVar φ := freeFO_lt_maxVar φ hi
    have hle : MSO.maxVar φ ≤ k := by rw [hk, hψ, maxVar_shiftUp]; omega
    by_cases h : i = 0
    · subst h
      rw [if_neg (by omega), Nat.zero_add, Function.update_self, if_pos rfl]
    · rw [if_pos (by omega), if_neg h]
  · have hlt : j < MSO.maxVar φ := freeSO_lt_maxVar φ hj
    have hle : MSO.maxVar φ ≤ k := by rw [hk, hψ, maxVar_shiftUp]; omega
    rw [if_pos (by omega)]

end MSO

end Lax314295Proofs.Transducers
