/-
First-order plugging combinators.

`RequestProject/PartC/MSOSubst.lean` provides the combinators `MSO.atv` and
`MSO.atv2`, which evaluate a formula with one, resp. two, free variables at
chosen variables of an ambient formula.  They bind the set variables of the
plugged formula with `MSO.bindSO`, which uses *second-order* quantification, and
are therefore unusable inside a first-order formula.

This file provides the first-order variants `MSO.atvF` and `MSO.atv2F`: since
the satisfaction of a first-order formula does not depend on the valuation of
the set variables at all, the second-order binding can simply be dropped.

It also provides `MSO.atZeroF φ`, a first-order formula whose truth value is the
truth value of `φ` under the valuation that sends *every* variable to the
position `0`, which is how the formulas of the "extra" elements of an mso
transduction (Definition `def:mso-transduction`) are evaluated.  On a non-empty string this is
`atvF` at the first position; on the empty string the truth value of `φ` is a
constant, and the formula is the corresponding truth value guarded by
"the input string is empty".
-/
import Lax314295Proofs.Source.PartC.FORename
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace MSO

variable {A : Type}

/-! ## First-orderness of the plugging machinery -/

@[simp] lemma isFO_tt : (tt : MSO A).IsFO := trivial

@[simp] lemma isFO_ff : (ff : MSO A).IsFO := trivial

@[simp] lemma isFO_eqVar (a b : ℕ) : (eqVar (A := A) a b).IsFO := ⟨trivial, trivial⟩

lemma isFO_bindTo (src u : ℕ) {φ : MSO A} (h : φ.IsFO) : (bindTo src u φ).IsFO :=
  ⟨isFO_eqVar _ _, h⟩

lemma isFO_bindRange (src d : ℕ) : ∀ (k : ℕ) {φ : MSO A}, φ.IsFO → (bindRange src d k φ).IsFO := by
  intro k
  induction k with
  | zero => exact fun h => h
  | succ k ih => exact fun h => isFO_bindTo _ _ (ih h)

/-! ## Plugging a first-order formula at a variable -/

/-- `atvF v φ` says that `φ` holds under the valuation that maps every
first-order variable to the value of `x_v`.  This is the first-order variant of
`MSO.atv`: the set variables are not bound, which is harmless for a first-order
`φ`. -/
def atvF (v : ℕ) (φ : MSO A) : MSO A :=
  bindRange v (v + 1) (MSO.maxVar (shiftUp (v + 1) φ)) (shiftUp (v + 1) φ)

lemma isFO_atvF (v : ℕ) {φ : MSO A} (h : φ.IsFO) : (atvF v φ).IsFO :=
  isFO_bindRange _ _ _ (isFO_shiftUp _ h)

lemma sat_atvF (w : List A) (v : ℕ) {φ : MSO A} (hfo : φ.IsFO) (fo : ℕ → ℕ) (so : ℕ → Set ℕ)
    (hv : fo v < w.length) :
    Sat w fo so (atvF v φ) ↔ Sat w (fun _ => fo v) (fun _ => ∅) φ := by
  set d := v + 1 with hd
  set ψ := shiftUp d φ with hψ
  set k := MSO.maxVar ψ with hk
  rw [show atvF v φ = bindRange v d k ψ from rfl]
  rw [sat_bindRange w (by omega) k ψ fo so hv, sat_shiftUp]
  refine sat_congr w φ _ _ _ _ (fun i hi => ?_) (fun j hj => ?_)
  · have h1 : i < MSO.maxVar φ := freeFO_lt_maxVar φ hi
    have h2 : MSO.maxVar φ ≤ k := by rw [hk, hψ, maxVar_shiftUp]; omega
    rw [if_pos (by omega)]
  · rw [freeSO_eq_empty_of_isFO φ hfo] at hj
    exact absurd hj (Set.notMem_empty _)

/-- `atv2F v₀ v₁ φ` says that `φ` holds under the valuation that maps the
variable `x₀` to the value of `x_{v₀}` and every other first-order variable to
the value of `x_{v₁}`.  First-order variant of `MSO.atv2`. -/
def atv2F (v₀ v₁ : ℕ) (φ : MSO A) : MSO A :=
  bindTo v₀ (max v₀ v₁ + 1)
    (bindRange v₁ (max v₀ v₁ + 2) (MSO.maxVar (shiftUp (max v₀ v₁ + 1) φ))
      (shiftUp (max v₀ v₁ + 1) φ))

lemma isFO_atv2F (v₀ v₁ : ℕ) {φ : MSO A} (h : φ.IsFO) : (atv2F v₀ v₁ φ).IsFO :=
  isFO_bindTo _ _ (isFO_bindRange _ _ _ (isFO_shiftUp _ h))

lemma sat_atv2F (w : List A) (v₀ v₁ : ℕ) {φ : MSO A} (hfo : φ.IsFO) (fo : ℕ → ℕ) (so : ℕ → Set ℕ)
    (h0 : fo v₀ < w.length) (h1 : fo v₁ < w.length) :
    Sat w fo so (atv2F v₀ v₁ φ) ↔
      Sat w (fun i => if i = 0 then fo v₀ else fo v₁) (fun _ => ∅) φ := by
  set d := max v₀ v₁ + 1 with hd
  set ψ := shiftUp d φ with hψ
  set k := MSO.maxVar ψ with hk
  rw [show atv2F v₀ v₁ φ = bindTo v₀ d (bindRange v₁ (d + 1) k ψ) from rfl,
    sat_bindTo w fo so (by omega) h0]
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
  · rw [freeSO_eq_empty_of_isFO φ hfo] at hj
    exact absurd hj (Set.notMem_empty _)

/-! ## Evaluating a formula at the position `0` -/

/-- "The input string is empty." -/
def emptyF (A : Type) : MSO A := not (exFO 0 (le 0 0))

@[simp] lemma isFO_emptyF : (emptyF A).IsFO := trivial

lemma sat_emptyF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (emptyF A) ↔ w = [] := by
  constructor
  · intro h
    rcases List.eq_nil_or_concat w with rfl | ⟨u, a, rfl⟩
    · rfl
    · exact absurd ⟨0, by simp, le_refl _⟩ h
  · rintro rfl
    rintro ⟨p, hp, -⟩
    simp at hp

/-- "The variable `x_v` denotes the first position of the string." -/
def firstF (v : ℕ) : MSO A := not (exFO (v + 1) (ltVar (v + 1) v))

@[simp] lemma isFO_firstF (v : ℕ) : (firstF (A := A) v).IsFO := by
  simp [firstF, IsFO, isFO_ltVar]

lemma sat_firstF (w : List A) (v : ℕ) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (hv : fo v < w.length) :
    Sat w fo so (firstF (A := A) v) ↔ fo v = 0 := by
  show (¬ ∃ p < w.length, Sat w (Function.update fo (v + 1) p) so (ltVar (v + 1) v)) ↔ _
  have hupd : ∀ p : ℕ, Sat w (Function.update fo (v + 1) p) so (ltVar (A := A) (v + 1) v) ↔
      p < fo v := by
    intro p
    rw [sat_ltVar, Function.update_self, Function.update_of_ne (by omega)]
  constructor
  · intro h
    by_contra hne
    exact h ⟨0, by omega, (hupd 0).2 (by omega)⟩
  · rintro h ⟨p, hp, hlt⟩
    rw [hupd p] at hlt
    omega

open scoped Classical in
/-- `atZeroF φ` is a first-order formula whose truth value is the truth value of
`φ` under the valuation sending every variable to the position `0` (and every
set variable to `∅`), on every input string, including the empty one. -/
noncomputable def atZeroF (φ : MSO A) : MSO A :=
  or (exFO 0 (and (firstF 0) (atvF 0 φ)))
    (and (emptyF A) (if Sat ([] : List A) (fun _ => 0) (fun _ => ∅) φ then tt else ff))

lemma isFO_atZeroF {φ : MSO A} (h : φ.IsFO) : (atZeroF φ).IsFO := by
  refine ⟨⟨isFO_firstF 0, isFO_atvF 0 h⟩, ⟨isFO_emptyF, ?_⟩⟩
  by_cases hc : Sat ([] : List A) (fun _ => 0) (fun _ => ∅) φ <;> simp [hc]

lemma sat_atZeroF (w : List A) {φ : MSO A} (hfo : φ.IsFO) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (atZeroF φ) ↔ Sat w (fun _ => 0) (fun _ => ∅) φ := by
  rcases Nat.eq_zero_or_pos w.length with h0 | hlen
  · have hnil : w = [] := List.length_eq_zero_iff.mp h0
    subst hnil
    constructor
    · rintro (⟨p, hp, -⟩ | ⟨-, hc⟩)
      · simp at hp
      · by_cases h : Sat ([] : List A) (fun _ => 0) (fun _ => ∅) φ
        · exact h
        · rw [if_neg h] at hc
          exact absurd (le_refl (fo 0)) hc
    · intro h
      refine Or.inr ⟨(sat_emptyF _ fo so).2 rfl, ?_⟩
      rw [if_pos h]
      exact le_refl _
  · have hne : w ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen
    constructor
    · rintro (⟨p, hp, hfirst, hsat⟩ | ⟨he, -⟩)
      · have hup : Function.update fo 0 p 0 = p := Function.update_self _ _ _
        have hp0 : p = 0 := by
          have := (sat_firstF w 0 (Function.update fo 0 p) so (by rw [hup]; exact hp)).1 hfirst
          rw [hup] at this
          exact this
        subst hp0
        have := (sat_atvF w 0 hfo (Function.update fo 0 0) so (by rw [hup]; exact hp)).1 hsat
        rw [hup] at this
        exact this
      · exact absurd ((sat_emptyF w fo so).1 he) hne
    · intro h
      have hup : Function.update fo 0 0 0 = 0 := Function.update_self _ _ _
      refine Or.inl ⟨0, hlen, ?_, ?_⟩
      · rw [sat_firstF w 0 _ so (by rw [hup]; exact hlen), hup]
      · rw [sat_atvF w 0 hfo _ so (by rw [hup]; exact hlen), hup]
        exact h

end MSO
end Lax314295Proofs.Transducers
