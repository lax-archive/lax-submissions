import Lax185574Proofs.Gaifman.NeighborhoodFormula

/-!
Changing the ambient radius of a local formula without changing its meaning.
The old quantifier guard is retained explicitly inside the larger ball.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/RadiusChange.lean`.
-/

namespace Lax185574Proofs.Gaifman.RadiusChange

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.NormalFormOps Lax185574Proofs.Gaifman.NeighborhoodFormula

/-- Regard an `r`-local formula as an `R`-local formula.  Every quantifier
keeps an explicit radius-`r` guard, so its semantics is unchanged when
`r ≤ R`. -/
noncomputable def enlarge {σ : Vocabulary} {k r b : ℕ} (R : ℕ) :
    LocalFormula σ k r b → LocalFormula σ k R b
  | .rel Q args => .rel Q args
  | .eq left right => .eq left right
  | .not φ => .not (enlarge R φ)
  | .or φ ψ => .or (enlarge R φ) (enlarge R ψ)
  | .ex φ =>
      .ex (LocalFormula.conjunction
        (nearCenters R r (.bound (Fin.last b))) (enlarge R φ))

/-- Enlarging the ambient radius preserves satisfaction. -/
theorem sat_enlarge {σ : Vocabulary} {M : Type*} {k r R b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (φ : LocalFormula σ k r b) (hr : r ≤ R) :
    (enlarge R φ).Sat A anchors bound ↔ φ.Sat A anchors bound := by
  induction φ with
  | rel Q args => rfl
  | eq left right => rfl
  | not φ ih =>
      simp only [enlarge, LocalFormula.Sat]
      exact not_congr (ih bound)
  | or φ ψ ihφ ihψ =>
      simp only [enlarge, LocalFormula.Sat]
      exact or_congr (ihφ bound) (ihψ bound)
  | ex φ ih =>
      simp only [enlarge, LocalFormula.Sat, LocalFormula.sat_conjunction]
      constructor
      · rintro ⟨x, hxR, hxNear, hxφ⟩
        have hx : inBallAround A r anchors x := by
          have h := (sat_nearCenters A anchors (Fin.snoc bound x)
            (.bound (Fin.last _)) hr).mp hxNear
          simpa [LocalTerm.eval] using h
        exact ⟨x, hx, (ih (Fin.snoc bound x)).mp hxφ⟩
      · rintro ⟨x, hxr, hxφ⟩
        have hxR : inBallAround A R anchors x :=
          Lax185574Proofs.Gaifman.Distance.inBallAround_mono A hr anchors hxr
        refine ⟨x, hxR, ?_, (ih (Fin.snoc bound x)).mpr hxφ⟩
        apply (sat_nearCenters A anchors (Fin.snoc bound x)
          (.bound (Fin.last _)) hr).mpr
        simpa [LocalTerm.eval] using hxr

/-- A true local formula whenever the anchor context is nonempty. -/
def truth {σ : Vocabulary} {k R b : ℕ} (i : Fin k) :
    LocalFormula σ k R b :=
  .eq (.anchor i) (.anchor i)

@[simp] theorem sat_truth {σ : Vocabulary} {M : Type*} {k R b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (i : Fin k) : (truth (R := R) (b := b) i).Sat A anchors bound :=
  rfl

end Lax185574Proofs.Gaifman.RadiusChange
