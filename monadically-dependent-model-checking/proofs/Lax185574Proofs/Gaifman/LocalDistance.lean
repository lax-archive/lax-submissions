import Lax185574Proofs.Gaifman.DistanceFormula

/-!
Bounded distance as a derived local formula.  The correctness theorem records
the budget condition ensuring that relativizing the internal path witnesses to
the ambient local ball is lossless.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/LocalDistance.lean`.
-/

namespace Lax185574Proofs.Gaifman.LocalDistance

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.Relativize Lax185574Proofs.Gaifman.DistanceFormula

/-- The two-entry substitution sending variable `0` to `left` and variable
`1` to `right`. -/
def pairTerms {σ : Vocabulary} {k b : ℕ}
    (left right : LocalTerm σ k b) : Fin 2 → LocalTerm σ k b :=
  Fin.cases left (fun _ => right)

@[simp] theorem pairTerms_zero {σ : Vocabulary} {k b : ℕ}
    (left right : LocalTerm σ k b) : pairTerms left right 0 = left := rfl

@[simp] theorem pairTerms_one {σ : Vocabulary} {k b : ℕ}
    (left right : LocalTerm σ k b) : pairTerms left right 1 = right := rfl

/-- Substitute two local terms into the bounded-distance formula and
relativize all of its internal witnesses to the ambient radius `R`. -/
noncomputable def localDistance {σ : Vocabulary} {k b : ℕ} (R d : ℕ)
    (left right : LocalTerm σ k b) : LocalFormula σ k R b :=
  relativize R (pairTerms left right) (distanceFormula σ d)

/-- Correctness of the derived local distance formula when its left endpoint
has enough remaining radius budget. -/
theorem sat_localDistance {σ : Vocabulary} {M : Type*} {k b R d s : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (left right : LocalTerm σ k b)
    (hleft : inBallAround A s anchors (left.eval A anchors bound))
    (hbudget : s + d ≤ R) :
    (localDistance R d left right).Sat A anchors bound ↔
      distanceAtMost A d (left.eval A anchors bound)
        (right.eval A anchors bound) := by
  rw [localDistance, sat_relativize]
  have h := satRestricted_distanceFormula_of_ball A anchors
    (fun i : Fin 2 => (pairTerms left right i).eval A anchors bound)
    hleft hbudget
  simpa using h

/-- The specialized form with an anchor as the left endpoint. -/
theorem sat_localDistance_anchor {σ : Vocabulary} {M : Type*}
    {k b R d : ℕ} (A : Structure σ M) (anchors : Fin k → M)
    (bound : Fin b → M) (i : Fin k) (right : LocalTerm σ k b)
    (hbudget : d ≤ R) :
    (localDistance R d (.anchor i) right).Sat A anchors bound ↔
      distanceAtMost A d (anchors i) (right.eval A anchors bound) := by
  apply sat_localDistance A anchors bound (.anchor i) right
    (s := 0) (Or.inl ⟨i, rfl⟩)
  simpa using hbudget

/-- The specialized form with a vocabulary constant as the left endpoint. -/
theorem sat_localDistance_const {σ : Vocabulary} {M : Type*}
    {k b R d : ℕ} (A : Structure σ M) (anchors : Fin k → M)
    (bound : Fin b → M) (c : σ.Constant) (right : LocalTerm σ k b)
    (hbudget : d ≤ R) :
    (localDistance R d (.const c) right).Sat A anchors bound ↔
      distanceAtMost A d (A.constant c) (right.eval A anchors bound) := by
  apply sat_localDistance A anchors bound (.const c) right
    (s := 0) (Or.inr ⟨c, rfl⟩)
  simpa using hbudget

end Lax185574Proofs.Gaifman.LocalDistance
