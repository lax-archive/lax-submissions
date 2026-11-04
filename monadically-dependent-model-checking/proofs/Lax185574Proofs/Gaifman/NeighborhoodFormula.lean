import Lax185574Proofs.Gaifman.LocalDistance
import Lax185574Proofs.Gaifman.Scatter

/-!
Local formulas expressing membership in balls around the free anchor tuple, or
around the anchors together with all vocabulary constants.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/NeighborhoodFormula.lean`.
-/

namespace Lax185574Proofs.Gaifman.NeighborhoodFormula

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.LocalDistance Lax185574Proofs.Gaifman.NormalFormOps
open Lax185574Proofs.Gaifman.Scatter

/-- The disjunction saying that `term` lies within distance `d` of one of the
free anchors. -/
noncomputable def nearAnchors {σ : Vocabulary} {k b : ℕ} (R d : ℕ)
    (term : LocalTerm σ k b) : LocalFormula σ k R b :=
  LocalFormula.disjunctions (LocalFormula.falsity term)
    (List.ofFn fun i : Fin k => localDistance R d (.anchor i) term)

/-- The disjunction saying that `term` lies within distance `d` of one of the
vocabulary constants. -/
noncomputable def nearConstants {σ : Vocabulary} {k b : ℕ} (R d : ℕ)
    (term : LocalTerm σ k b) : LocalFormula σ k R b :=
  LocalFormula.disjunctions (LocalFormula.falsity term)
    (List.ofFn fun c : σ.Constant => localDistance R d (.const c) term)

/-- The disjunction saying that `term` lies within distance `d` of an anchor
or a vocabulary constant. -/
noncomputable def nearCenters {σ : Vocabulary} {k b : ℕ} (R d : ℕ)
    (term : LocalTerm σ k b) : LocalFormula σ k R b :=
  LocalFormula.disjunctions (LocalFormula.falsity term)
    ((List.ofFn fun i : Fin k => localDistance R d (.anchor i) term) ++
      (List.ofFn fun c : σ.Constant => localDistance R d (.const c) term))

theorem sat_nearAnchors {σ : Vocabulary} {M : Type*} {k b R d : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (term : LocalTerm σ k b) (hbudget : d ≤ R) :
    (nearAnchors R d term).Sat A anchors bound ↔
      NearTuple A d anchors (term.eval A anchors bound) := by
  rw [nearAnchors, LocalFormula.sat_disjunctions A anchors bound
    (LocalFormula.falsity term) (LocalFormula.not_sat_falsity A anchors bound term)]
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨φ, ⟨i, rfl⟩, hφ⟩
    exact ⟨i, (sat_localDistance_anchor A anchors bound i term hbudget).mp hφ⟩
  · rintro ⟨i, hi⟩
    exact ⟨localDistance R d (.anchor i) term, ⟨i, rfl⟩,
      (sat_localDistance_anchor A anchors bound i term hbudget).mpr hi⟩

theorem sat_nearConstants {σ : Vocabulary} {M : Type*} {k b R d : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (term : LocalTerm σ k b) (hbudget : d ≤ R) :
    (nearConstants R d term).Sat A anchors bound ↔
      ∃ c : σ.Constant,
        distanceAtMost A d (A.constant c) (term.eval A anchors bound) := by
  rw [nearConstants, LocalFormula.sat_disjunctions A anchors bound
    (LocalFormula.falsity term) (LocalFormula.not_sat_falsity A anchors bound term)]
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨φ, ⟨c, rfl⟩, hφ⟩
    exact ⟨c, (sat_localDistance_const A anchors bound c term hbudget).mp hφ⟩
  · rintro ⟨c, hc⟩
    exact ⟨localDistance R d (.const c) term, ⟨c, rfl⟩,
      (sat_localDistance_const A anchors bound c term hbudget).mpr hc⟩

theorem sat_nearCenters {σ : Vocabulary} {M : Type*} {k b R d : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (term : LocalTerm σ k b) (hbudget : d ≤ R) :
    (nearCenters R d term).Sat A anchors bound ↔
      inBallAround A d anchors (term.eval A anchors bound) := by
  rw [nearCenters, LocalFormula.sat_disjunctions A anchors bound
    (LocalFormula.falsity term) (LocalFormula.not_sat_falsity A anchors bound term)]
  simp only [List.mem_append, List.mem_ofFn]
  constructor
  · rintro ⟨φ, hmem, hφ⟩
    rcases hmem with ⟨i, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨i,
        (sat_localDistance_anchor A anchors bound i term hbudget).mp hφ⟩
    · exact Or.inr ⟨c,
        (sat_localDistance_const A anchors bound c term hbudget).mp hφ⟩
  · rintro (⟨i, hi⟩ | ⟨c, hc⟩)
    · exact ⟨localDistance R d (.anchor i) term, Or.inl ⟨i, rfl⟩,
        (sat_localDistance_anchor A anchors bound i term hbudget).mpr hi⟩
    · exact ⟨localDistance R d (.const c) term, Or.inr ⟨c, rfl⟩,
        (sat_localDistance_const A anchors bound c term hbudget).mpr hc⟩

end Lax185574Proofs.Gaifman.NeighborhoodFormula
