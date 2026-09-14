/-
First-order formulas describing the blocks of a string over `A + 1`.

`Transducers.sepF v` says that the position `x_v` carries the separator, and
`Transducers.sameBlkF v₀ v₁ v₂` says that no position between `x_{v₀}` and
`x_{v₁}` carries the separator, i.e. that `Transducers.SameBlk` holds of the two
positions (the variable `v₂` is used for the quantifier and has to be distinct
from the other two).  Both formulas are first-order.

These are the formulas used by the first-order transductions computing
`mapReverse` and `mapDuplicate`.
-/
import Lax314295Proofs.Source.PartC.BlockPos
import Lax314295Proofs.Source.PartC.FOPlug
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

variable {A : Type}

/-- The position `x_v` carries the separator. -/
def sepF (A : Type) (v : ℕ) : MSO (Option A) := MSO.lab none v

@[simp] lemma isFO_sepF (v : ℕ) : (sepF A v).IsFO := trivial

lemma sat_sepF (w : List (Option A)) (v : ℕ) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    MSO.Sat w fo so (sepF A v) ↔ SepAt w (fo v) := Iff.rfl

/-- `x_{v₂}` lies between `x_{v₀}` and `x_{v₁}` (in either order, endpoints
included). -/
def betweenF (A : Type) (v₀ v₁ v₂ : ℕ) : MSO (Option A) :=
  MSO.or (MSO.and (MSO.le v₀ v₂) (MSO.le v₂ v₁)) (MSO.and (MSO.le v₁ v₂) (MSO.le v₂ v₀))

@[simp] lemma isFO_betweenF (v₀ v₁ v₂ : ℕ) : (betweenF A v₀ v₁ v₂).IsFO :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

lemma sat_betweenF (w : List (Option A)) (v₀ v₁ v₂ : ℕ) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    MSO.Sat w fo so (betweenF A v₀ v₁ v₂) ↔
      min (fo v₀) (fo v₁) ≤ fo v₂ ∧ fo v₂ ≤ max (fo v₀) (fo v₁) := by
  simp only [betweenF, MSO.Sat]
  omega

/-- No position between `x_{v₀}` and `x_{v₁}` carries the separator. -/
def sameBlkF (A : Type) (v₀ v₁ v₂ : ℕ) : MSO (Option A) :=
  MSO.not (MSO.exFO v₂ (MSO.and (betweenF A v₀ v₁ v₂) (sepF A v₂)))

@[simp] lemma isFO_sameBlkF (v₀ v₁ v₂ : ℕ) : (sameBlkF A v₀ v₁ v₂).IsFO :=
  ⟨isFO_betweenF v₀ v₁ v₂, trivial⟩

lemma sat_sameBlkF (w : List (Option A)) {v₀ v₁ v₂ : ℕ} (h₀ : v₂ ≠ v₀) (h₁ : v₂ ≠ v₁)
    (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (hp : fo v₀ < w.length) (hq : fo v₁ < w.length) :
    MSO.Sat w fo so (sameBlkF A v₀ v₁ v₂) ↔ SameBlk w (fo v₀) (fo v₁) := by
  have hupd : ∀ r : ℕ, (Function.update fo v₂ r) v₀ = fo v₀ := fun r =>
    Function.update_of_ne (Ne.symm h₀) _ _
  have hupd' : ∀ r : ℕ, (Function.update fo v₂ r) v₁ = fo v₁ := fun r =>
    Function.update_of_ne (Ne.symm h₁) _ _
  have hupd2 : ∀ r : ℕ, (Function.update fo v₂ r) v₂ = r := fun r =>
    Function.update_self _ _ _
  show (¬ ∃ r < w.length, MSO.Sat w (Function.update fo v₂ r) so (betweenF A v₀ v₁ v₂) ∧
      MSO.Sat w (Function.update fo v₂ r) so (sepF A v₂)) ↔ _
  constructor
  · intro h
    refine ⟨hp, hq, fun r hr₁ hr₂ hsep => h ⟨r, by omega, ?_, ?_⟩⟩
    · rw [sat_betweenF, hupd, hupd', hupd2]
      exact ⟨hr₁, hr₂⟩
    · rw [sat_sepF, hupd2]
      exact hsep
  · rintro ⟨-, -, h⟩ ⟨r, -, hb, hs⟩
    rw [sat_betweenF, hupd, hupd', hupd2] at hb
    rw [sat_sepF, hupd2] at hs
    exact h r hb.1 hb.2 hs

end Lax314295Proofs.Transducers
