import Lax185574Proofs.Gaifman.Recenter

/-!
Finite conjunctions and blocks of restricted existential quantifiers for
local formulas.  These are used to reify finite scattered tuples.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/LocalTuples.lean`.
-/

namespace Lax185574Proofs.Gaifman.LocalTuples

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.NormalFormOps

/-- A finite conjunction, using a supplied true formula as the empty case. -/
def conjunctions {σ : Vocabulary} {k R b : ℕ}
    (trueFormula : LocalFormula σ k R b) :
    List (LocalFormula σ k R b) → LocalFormula σ k R b
  | [] => trueFormula
  | φ :: φs => LocalFormula.conjunction φ (conjunctions trueFormula φs)

theorem sat_conjunctions {σ : Vocabulary} {M : Type*} {k R b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (trueFormula : LocalFormula σ k R b)
    (htrue : trueFormula.Sat A anchors bound)
    (formulas : List (LocalFormula σ k R b)) :
    (conjunctions trueFormula formulas).Sat A anchors bound ↔
      ∀ φ ∈ formulas, φ.Sat A anchors bound := by
  induction formulas with
  | nil => simp [conjunctions, htrue]
  | cons φ formulas ih =>
      simp [conjunctions, LocalFormula.sat_conjunction, ih]

/-- Add `n` local existential quantifiers at the last `n` bound-variable
levels. -/
def exN {σ : Vocabulary} {k R : ℕ} : (n : ℕ) → {b : ℕ} →
    LocalFormula σ k R (b + n) → LocalFormula σ k R b
  | 0, _, φ => φ
  | n + 1, b, φ => exN n (.ex (Nat.add_succ b n ▸ φ))

/-- Concatenation of the already-bound environment and a new tuple. -/
def appendBound {M : Type*} {b n : ℕ} (bound : Fin b → M)
    (xs : Fin n → M) : Fin (b + n) → M :=
  Fin.append bound xs

/-- Satisfaction of a local existential block is tuple-existence with every
new entry in the fixed ambient ball. -/
theorem sat_exN {σ : Vocabulary} {M : Type*} {k R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) :
    ∀ (n : ℕ) {b : ℕ} (φ : LocalFormula σ k R (b + n))
      (bound : Fin b → M),
      (exN n φ).Sat A anchors bound ↔
        ∃ xs : Fin n → M,
          (∀ i, inBallAround A R anchors (xs i)) ∧
            φ.Sat A anchors (appendBound bound xs) := by
  intro n
  induction n with
  | zero =>
      intro b φ bound
      constructor
      · intro h
        exact ⟨Fin.elim0, fun i => Fin.elim0 i,
          by simpa [exN, appendBound] using h⟩
      · rintro ⟨xs, -, h⟩
        simpa [exN, appendBound, Subsingleton.elim xs Fin.elim0] using h
  | succ n ih =>
      intro b φ bound
      simp only [exN, LocalFormula.Sat]
      rw [ih]
      constructor
      · rintro ⟨xs, hxs, x, hx, hφ⟩
        refine ⟨Fin.snoc xs x, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hx
          · simpa using hxs j
        · change φ.Sat A anchors
            (Fin.append bound (Fin.snoc xs x))
          rw [Fin.append_snoc]
          exact hφ
      · rintro ⟨xs, hxs, hφ⟩
        refine ⟨Fin.init xs, ?_, xs (Fin.last n), hxs (Fin.last n), ?_⟩
        · intro i
          change inBallAround A R anchors (xs i.castSucc)
          exact hxs i.castSucc
        · change φ.Sat A anchors
            (Fin.snoc (Fin.append bound (Fin.init xs)) (xs (Fin.last n)))
          rw [← Fin.append_snoc, Fin.snoc_init_self]
          exact hφ

/-- Close a formula whose entire bound-variable context is a tuple. -/
def closeExists {σ : Vocabulary} {k R : ℕ} :
    (n : ℕ) → LocalFormula σ k R n → LocalFormula σ k R 0
  | 0, φ => φ
  | n + 1, φ => closeExists n (.ex φ)

theorem sat_closeExists {σ : Vocabulary} {M : Type*} {k R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) :
    ∀ (n : ℕ) (φ : LocalFormula σ k R n),
      (closeExists n φ).Sat A anchors Fin.elim0 ↔
        ∃ xs : Fin n → M,
          (∀ i, inBallAround A R anchors (xs i)) ∧
            φ.Sat A anchors xs := by
  intro n
  induction n with
  | zero =>
      intro φ
      constructor
      · intro h
        exact ⟨Fin.elim0, fun i => Fin.elim0 i,
          by simpa [closeExists] using h⟩
      · rintro ⟨xs, -, h⟩
        simpa [closeExists, Subsingleton.elim xs Fin.elim0] using h
  | succ n ih =>
      intro φ
      rw [show closeExists (n + 1) φ = closeExists n (.ex φ) from rfl, ih]
      simp only [LocalFormula.Sat]
      constructor
      · rintro ⟨xs, hxs, x, hx, hφ⟩
        refine ⟨Fin.snoc xs x, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hx
          · simpa using hxs j
        · exact hφ
      · rintro ⟨xs, hxs, hφ⟩
        refine ⟨Fin.init xs, ?_, xs (Fin.last n), hxs (Fin.last n), ?_⟩
        · intro i
          change inBallAround A R anchors (xs i.castSucc)
          exact hxs i.castSucc
        · simpa [Fin.snoc_init_self] using hφ

end Lax185574Proofs.Gaifman.LocalTuples
