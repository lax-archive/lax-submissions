import Lax185574Proofs.Gaifman.Separation

/-!
Re-centering a local formula inside a larger ambient neighborhood.  The old
anchor tuple is represented by local terms in the new context, and every old
quantifier guard is retained explicitly.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/Recenter.lean`.
-/

namespace Lax185574Proofs.Gaifman.Recenter

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.Distance Lax185574Proofs.Gaifman.LocalSyntax
open Lax185574Proofs.Gaifman.LocalDistance Lax185574Proofs.Gaifman.NormalFormOps

noncomputable section

/-- Substitute local terms for the anchors and locally bound variables of a
local term. -/
def substTerm {σ : Vocabulary} {k b k' b' : ℕ}
    (anchors : Fin k → LocalTerm σ k' b')
    (bound : Fin b → LocalTerm σ k' b') :
    LocalTerm σ k b → LocalTerm σ k' b'
  | .anchor i => anchors i
  | .bound i => bound i
  | .const c => .const c

@[simp] theorem eval_substTerm {σ : Vocabulary} {M : Type*}
    {k b k' b' : ℕ} (A : Structure σ M)
    (newAnchors : Fin k' → M) (newBound : Fin b' → M)
    (anchors : Fin k → LocalTerm σ k' b')
    (bound : Fin b → LocalTerm σ k' b') (t : LocalTerm σ k b) :
    (substTerm anchors bound t).eval A newAnchors newBound =
      t.eval A
        (fun i => (anchors i).eval A newAnchors newBound)
        (fun i => (bound i).eval A newAnchors newBound) := by
  cases t <;> rfl

/-- Lift a local-term substitution beneath one new output binder. -/
def liftTerms {σ : Vocabulary} {n k b : ℕ}
    (terms : Fin n → LocalTerm σ k b) :
    Fin n → LocalTerm σ k (b + 1) :=
  fun i => LocalSyntax.LocalTerm.weakenBound (terms i)

/-- Extend a source-bound substitution by the new last variable. -/
def extendBoundTerms {σ : Vocabulary} {n k b : ℕ}
    (terms : Fin n → LocalTerm σ k b) :
    Fin (n + 1) → LocalTerm σ k (b + 1) :=
  Fin.snoc (liftTerms terms) (.bound (Fin.last b))

theorem eval_liftTerms {σ : Vocabulary} {M : Type*} {n k b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (x : M) (terms : Fin n → LocalTerm σ k b) :
    (fun i => (liftTerms terms i).eval A anchors (Fin.snoc bound x)) =
      fun i => (terms i).eval A anchors bound := by
  funext i
  simp [liftTerms, LocalSyntax.LocalTerm.eval_weakenBound]

theorem eval_extendBoundTerms {σ : Vocabulary} {M : Type*} {n k b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (x : M) (terms : Fin n → LocalTerm σ k b) :
    (fun i => (extendBoundTerms terms i).eval A anchors (Fin.snoc bound x)) =
      Fin.snoc (fun i => (terms i).eval A anchors bound) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendBoundTerms, LocalTerm.eval]
  · simp [extendBoundTerms, liftTerms,
      LocalSyntax.LocalTerm.eval_weakenBound]

/-- Formula saying that `target` is within distance `d` of one of the
represented source anchors or of a vocabulary constant. -/
def nearTerms {σ : Vocabulary} {n k b : ℕ} (S d : ℕ)
    (anchors : Fin n → LocalTerm σ k b) (target : LocalTerm σ k b) :
    LocalFormula σ k S b :=
  LocalFormula.disjunctions (LocalFormula.falsity target)
    ((List.ofFn fun i : Fin n => localDistance S d (anchors i) target) ++
      (List.ofFn fun c : σ.Constant => localDistance S d (.const c) target))

theorem sat_nearTerms {σ : Vocabulary} {M : Type*} {n k b S d t : ℕ}
    (A : Structure σ M) (newAnchors : Fin k → M) (newBound : Fin b → M)
    (anchors : Fin n → LocalTerm σ k b) (target : LocalTerm σ k b)
    (hanchors : ∀ i, inBallAround A t newAnchors
      ((anchors i).eval A newAnchors newBound))
    (hbudget : t + d ≤ S) :
    (nearTerms S d anchors target).Sat A newAnchors newBound ↔
      inBallAround A d
        (fun i => (anchors i).eval A newAnchors newBound)
        (target.eval A newAnchors newBound) := by
  rw [nearTerms, LocalFormula.sat_disjunctions A newAnchors newBound
    (LocalFormula.falsity target)
    (LocalFormula.not_sat_falsity A newAnchors newBound target)]
  simp only [List.mem_append, List.mem_ofFn]
  constructor
  · rintro ⟨formula, hmem, hformula⟩
    rcases hmem with ⟨i, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨i, (sat_localDistance A newAnchors newBound
        (anchors i) target (hanchors i) hbudget).mp hformula⟩
    · exact Or.inr ⟨c, (sat_localDistance A newAnchors newBound
        (.const c) target (s := 0) (Or.inr ⟨c, rfl⟩) (by omega)).mp hformula⟩
  · rintro (⟨i, hi⟩ | ⟨c, hc⟩)
    · exact ⟨localDistance S d (anchors i) target, Or.inl ⟨i, rfl⟩,
        (sat_localDistance A newAnchors newBound (anchors i) target
          (hanchors i) hbudget).mpr hi⟩
    · exact ⟨localDistance S d (.const c) target, Or.inr ⟨c, rfl⟩,
        (sat_localDistance A newAnchors newBound (.const c) target
          (s := 0) (Or.inr ⟨c, rfl⟩) (by omega)).mpr hc⟩

/-- Re-center a source local formula in a new local context. -/
def recenter {σ : Vocabulary} {k r b k' b' : ℕ} (S : ℕ)
    (anchors : Fin k → LocalTerm σ k' b')
    (bound : Fin b → LocalTerm σ k' b') :
    LocalFormula σ k r b → LocalFormula σ k' S b'
  | .rel Q args => .rel Q (fun i => substTerm anchors bound (args i))
  | .eq left right => .eq (substTerm anchors bound left)
      (substTerm anchors bound right)
  | .not φ => .not (recenter S anchors bound φ)
  | .or φ ψ => .or (recenter S anchors bound φ)
      (recenter S anchors bound ψ)
  | .ex φ => .ex (LocalFormula.conjunction
      (nearTerms S r (liftTerms anchors) (.bound (Fin.last b')))
      (recenter S (liftTerms anchors) (extendBoundTerms bound) φ))

/-- Correctness of re-centering.  `t` bounds how far the represented source
anchors lie from the new anchor tuple. `t+r ≤ S` makes every old local witness
legal in the new ambient ball. -/
theorem sat_recenter {σ : Vocabulary} {M : Type*}
    {k r b k' b' S t : ℕ} (A : Structure σ M)
    (newAnchors : Fin k' → M) (newBound : Fin b' → M)
    (anchors : Fin k → LocalTerm σ k' b')
    (bound : Fin b → LocalTerm σ k' b')
    (φ : LocalFormula σ k r b)
    (hanchors : ∀ i, inBallAround A t newAnchors
      ((anchors i).eval A newAnchors newBound))
    (hbudget : t + r ≤ S) :
    (recenter S anchors bound φ).Sat A newAnchors newBound ↔
      φ.Sat A
        (fun i => (anchors i).eval A newAnchors newBound)
        (fun i => (bound i).eval A newAnchors newBound) := by
  induction φ generalizing b' with
  | rel Q args =>
      simp only [recenter, LocalFormula.Sat, eval_substTerm]
  | eq left right =>
      simp only [recenter, LocalFormula.Sat, eval_substTerm]
  | not φ ih =>
      simp only [recenter, LocalFormula.Sat]
      exact not_congr (ih newBound anchors bound hanchors)
  | or φ ψ ihφ ihψ =>
      simp only [recenter, LocalFormula.Sat]
      exact or_congr (ihφ newBound anchors bound hanchors)
        (ihψ newBound anchors bound hanchors)
  | ex φ ih =>
      simp only [recenter, LocalFormula.Sat, LocalFormula.sat_conjunction]
      constructor
      · rintro ⟨x, -, hnear, hφ⟩
        have hanchors' : ∀ i, inBallAround A t newAnchors
            ((liftTerms anchors i).eval A newAnchors (Fin.snoc newBound x)) := by
          intro i
          simpa [liftTerms, LocalSyntax.LocalTerm.eval_weakenBound] using hanchors i
        have hOldBall := (sat_nearTerms A newAnchors (Fin.snoc newBound x)
          (liftTerms anchors) (.bound (Fin.last b')) hanchors' (by omega)).mp hnear
        have hbody := (ih (Fin.snoc newBound x) (liftTerms anchors)
          (extendBoundTerms bound) hanchors').mp hφ
        rw [eval_liftTerms A newAnchors newBound x anchors] at hOldBall hbody
        have hOldBall' : inBallAround A r
            (fun i => (anchors i).eval A newAnchors newBound) x := by
          simpa [LocalTerm.eval] using hOldBall
        rw [eval_extendBoundTerms A newAnchors newBound x bound] at hbody
        exact ⟨x, hOldBall', hbody⟩
      · rintro ⟨x, hOldBall, hφ⟩
        have hxS : inBallAround A S newAnchors x := by
          rcases hOldBall with ⟨i, hi⟩ | ⟨c, hc⟩
          · have hx := inBallAround_of_distance A newAnchors (hanchors i) hi
            exact inBallAround_mono A hbudget newAnchors hx
          · exact inBallAround_mono A (by omega) newAnchors
              (Or.inr ⟨c, hc⟩)
        have hanchors' : ∀ i, inBallAround A t newAnchors
            ((liftTerms anchors i).eval A newAnchors (Fin.snoc newBound x)) := by
          intro i
          simpa [liftTerms, LocalSyntax.LocalTerm.eval_weakenBound] using hanchors i
        refine ⟨x, hxS, ?_, ?_⟩
        · apply (sat_nearTerms A newAnchors (Fin.snoc newBound x)
            (liftTerms anchors) (.bound (Fin.last b')) hanchors' (by omega)).mpr
          rw [eval_liftTerms]
          simpa [LocalTerm.eval] using hOldBall
        · apply (ih (Fin.snoc newBound x) (liftTerms anchors)
            (extendBoundTerms bound) hanchors').mpr
          rw [eval_liftTerms, eval_extendBoundTerms]
          exact hφ

end

end Lax185574Proofs.Gaifman.Recenter
