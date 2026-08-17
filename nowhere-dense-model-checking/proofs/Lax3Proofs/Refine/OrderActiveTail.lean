import Lax3Proofs.RamDriverOrder

/-!
# The inactive scratch tail of the active ordering phase

The ordering engines address their scratch arrays only through the compact
carrier `mm`.  `OrderMem`, however, owns carrier-sized arrays and requires
eight of them to be zero everywhere.  This file names the exact tail that
must survive an active ordering call.  The phase can then re-zero only the
live prefix and recover the carrier-wide invariant without a carrier scan.
-/

namespace Lax3Proofs.Refine.OrderActiveTail

open Lax13Proofs.Reasoning
open Lax13Proofs.Imp

/-- The arrays whose carrier-wide zero clauses belong to `OrderMem`. -/
def activeZeroNames : List String :=
  ["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"]

/-- Five scratch arrays are vertex-indexed and three are offset-indexed. -/
def activeZeroLen (mm : ℕ) (a : String) : ℕ :=
  if a = "bh" ∨ a = "ooff" ∨ a = "noff" then mm + 1 else mm

@[simp] theorem activeZeroLen_elm (mm : ℕ) : activeZeroLen mm "elm" = mm := by
  simp [activeZeroLen]

@[simp] theorem activeZeroLen_bh (mm : ℕ) : activeZeroLen mm "bh" = mm + 1 := by
  simp [activeZeroLen]

@[simp] theorem activeZeroLen_ooff (mm : ℕ) : activeZeroLen mm "ooff" = mm + 1 := by
  simp [activeZeroLen]

@[simp] theorem activeZeroLen_noff (mm : ℕ) : activeZeroLen mm "noff" = mm + 1 := by
  simp [activeZeroLen]

@[simp] theorem activeZeroLen_stf (mm : ℕ) : activeZeroLen mm "stf" = mm := by
  simp [activeZeroLen]

@[simp] theorem activeZeroLen_sta (mm : ℕ) : activeZeroLen mm "sta" = mm := by
  simp [activeZeroLen]

@[simp] theorem activeZeroLen_std (mm : ℕ) : activeZeroLen mm "std" = mm := by
  simp [activeZeroLen]

@[simp] theorem activeZeroLen_ste (mm : ℕ) : activeZeroLen mm "ste" = mm := by
  simp [activeZeroLen]

/-- Every inactive cell of the eight zeroed scratch arrays is unchanged. -/
def ActiveZeroTail (mm : ℕ) (before after : Env) : Prop :=
  ∀ a ∈ activeZeroNames,
    (after.arrs a).drop (activeZeroLen mm a) =
      (before.arrs a).drop (activeZeroLen mm a)

namespace ActiveZeroTail

theorem refl (mm : ℕ) (σ : Env) : ActiveZeroTail mm σ σ := by
  intro _ _
  rfl

theorem trans {mm : ℕ} {σ₀ σ₁ σ₂ : Env}
    (h₀₁ : ActiveZeroTail mm σ₀ σ₁)
    (h₁₂ : ActiveZeroTail mm σ₁ σ₂) : ActiveZeroTail mm σ₀ σ₂ := by
  intro a ha
  exact (h₁₂ a ha).trans (h₀₁ a ha)

theorem of_frame {mm : ℕ} {σ σ' : Env}
    (h : ∀ a ∈ activeZeroNames, σ'.arrs a = σ.arrs a) :
    ActiveZeroTail mm σ σ' := by
  intro a ha
  rw [h a ha]

end ActiveZeroTail

/-- Pointwise agreement above a cut gives equality of the corresponding
`arrOf` tails.  This is the list-level form returned by the prefix-fill kit. -/
theorem drop_arrOf_congr {N Nd : ℕ} {f g : ℕ → ℕ} (hN : N ≤ Nd)
    (h : ∀ k, N ≤ k → k < Nd → f k = g k) :
    (arrOf Nd f).drop N = (arrOf Nd g).drop N := by
  apply List.ext_get
  · simp [length_arrOf]
  · intro i hi hi'
    have hik : N + i < Nd := by
      simp only [List.length_drop, length_arrOf] at hi
      omega
    simp only [List.get_eq_getElem, List.getElem_drop]
    simp [arrOf, hik, h (N + i) (by omega) hik]

/-! ## Axioms -/

#print axioms ActiveZeroTail.trans
#print axioms drop_arrOf_congr

end Lax3Proofs.Refine.OrderActiveTail
