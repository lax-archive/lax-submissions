import Lax185574Proofs.Gaifman.FormulaUtils

/-!
Relativization of an arbitrary first-order formula to the fixed Gaifman ball
of a local formula.  A variable substitution into local terms is carried
through binders using the level convention (`Fin.snoc`).

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/Relativize.lean`.
-/

namespace Lax185574Proofs.Gaifman.Relativize

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.FirstOrder
open Lax185574Proofs.Gaifman.Locality Lax185574Proofs.Gaifman.LocalSyntax

namespace LocalTerm

/-- Substitute local terms for all variables of a first-order term. -/
def ofTermWith {σ : Vocabulary} {n k b : ℕ}
    (f : Fin n → Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b) :
    Term σ n → Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b
  | .var i => f i
  | .const c => .const c

@[simp] theorem eval_ofTermWith {σ : Vocabulary} {M : Type*} {n k b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (f : Fin n → Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b) (t : Term σ n) :
    (ofTermWith f t).eval A anchors bound =
      t.eval A (fun i => (f i).eval A anchors bound) := by
  cases t <;> rfl

/-- Lift a local-term substitution under one new last bound variable. -/
def liftSubst {σ : Vocabulary} {n k b : ℕ}
    (f : Fin n → Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b) :
    Fin (n + 1) → Lax185574Proofs.Gaifman.Locality.LocalTerm σ k (b + 1) :=
  Fin.snoc (fun i => LocalSyntax.LocalTerm.weakenBound (f i))
    (.bound (Fin.last b))

@[simp] theorem eval_liftSubst {σ : Vocabulary} {M : Type*} {n k b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (x : M) (f : Fin n → Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b) :
    (fun i => (liftSubst f i).eval A anchors (Fin.snoc bound x)) =
      Fin.snoc (fun i => (f i).eval A anchors bound) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [liftSubst, Lax185574Proofs.Gaifman.Locality.LocalTerm.eval]
  · simp [liftSubst, LocalSyntax.LocalTerm.eval_weakenBound]

end LocalTerm

/-- Satisfaction with every existential quantifier restricted to a fixed
domain predicate `D`. -/
def SatRestricted {σ : Vocabulary} {M : Type*} (A : Structure σ M)
    (D : M → Prop) : {n : ℕ} → Formula σ n → (Fin n → M) → Prop
  | _, .rel R args, env => A.relation R (fun i => (args i).eval A env)
  | _, .eq left right, env => left.eval A env = right.eval A env
  | _, .not φ, env => ¬ SatRestricted A D φ env
  | _, .or φ ψ, env => SatRestricted A D φ env ∨ SatRestricted A D ψ env
  | _, .ex φ, env => ∃ x, D x ∧ SatRestricted A D φ (Fin.snoc env x)

theorem satRestricted_rename {σ : Vocabulary} {M : Type*}
    (A : Structure σ M) (D : M → Prop) {n n' : ℕ}
    (env : Fin n' → M) (f : Fin n → Fin n') (φ : Formula σ n) :
    SatRestricted A D (FormulaUtils.Formula.rename f φ) env ↔
      SatRestricted A D φ (env ∘ f) := by
  induction φ generalizing n' with
  | rel R args =>
      simp only [FormulaUtils.Formula.rename, SatRestricted,
        FormulaUtils.Term.eval_rename]
  | eq left right =>
      simp only [FormulaUtils.Formula.rename, SatRestricted,
        FormulaUtils.Term.eval_rename]
  | not φ ih =>
      simp only [FormulaUtils.Formula.rename, SatRestricted]
      exact not_congr (ih env f)
  | or φ ψ ihφ ihψ =>
      simp only [FormulaUtils.Formula.rename, SatRestricted]
      exact or_congr (ihφ env f) (ihψ env f)
  | ex φ ih =>
      simp only [FormulaUtils.Formula.rename, SatRestricted]
      apply exists_congr
      intro x
      apply and_congr_right
      intro _
      rw [ih (Fin.snoc env x) (LocalSyntax.liftFin f)]
      have henv : Fin.snoc env x ∘ LocalSyntax.liftFin f =
          Fin.snoc (env ∘ f) x := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [LocalSyntax.liftFin]
      rw [henv]

@[simp] theorem satRestricted_conjunction {σ : Vocabulary} {M : Type*}
    (A : Structure σ M) (D : M → Prop) {n : ℕ}
    (φ ψ : Formula σ n) (env : Fin n → M) :
    SatRestricted A D (FormulaUtils.Formula.conjunction φ ψ) env ↔
      SatRestricted A D φ env ∧ SatRestricted A D ψ env := by
  simp only [FormulaUtils.Formula.conjunction, SatRestricted]
  tauto

theorem satRestricted_disjunctions {σ : Vocabulary} {M : Type*}
    (A : Structure σ M) (D : M → Prop) {n : ℕ}
    (env : Fin n → M) (falseFormula : Formula σ n)
    (hfalse : ¬ SatRestricted A D falseFormula env)
    (formulas : List (Formula σ n)) :
    SatRestricted A D
        (FormulaUtils.Formula.disjunctions falseFormula formulas) env ↔
      ∃ φ ∈ formulas, SatRestricted A D φ env := by
  induction formulas with
  | nil => simp [FormulaUtils.Formula.disjunctions, hfalse]
  | cons φ formulas ih =>
      simp only [FormulaUtils.Formula.disjunctions, SatRestricted, ih]
      aesop

/-- Restricted satisfaction of a block of existential quantifiers. -/
theorem satRestricted_exN {σ : Vocabulary} {M : Type*}
    (A : Structure σ M) (D : M → Prop) :
    ∀ (m : ℕ) {n : ℕ} (φ : Formula σ (n + m)) (env : Fin n → M),
      SatRestricted A D (FormulaUtils.Formula.exN m φ) env ↔
        ∃ xs : Fin m → M, (∀ i, D (xs i)) ∧
          SatRestricted A D φ (FormulaUtils.Formula.appendEnv env xs) := by
  intro m
  induction m with
  | zero =>
      intro n φ env
      constructor
      · intro h
        exact ⟨Fin.elim0, (fun i => i.elim0), by simpa [FormulaUtils.Formula.exN,
          FormulaUtils.Formula.appendEnv] using h⟩
      · rintro ⟨xs, _, h⟩
        simpa [FormulaUtils.Formula.exN, FormulaUtils.Formula.appendEnv,
          Subsingleton.elim xs Fin.elim0] using h
  | succ m ih =>
      intro n φ env
      simp only [FormulaUtils.Formula.exN, SatRestricted]
      rw [ih]
      constructor
      · rintro ⟨xs, hxs, x, hx, hφ⟩
        refine ⟨Fin.snoc xs x, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hx
          · simpa using hxs j
        · change SatRestricted A D φ
            (Fin.append env (Fin.snoc xs x))
          rw [Fin.append_snoc]
          exact hφ
      · rintro ⟨xs, hxs, hφ⟩
        refine ⟨Fin.init xs, fun i => hxs i.castSucc,
          xs (Fin.last m), hxs (Fin.last m), ?_⟩
        change SatRestricted A D φ
          (Fin.snoc (Fin.append env (Fin.init xs)) (xs (Fin.last m)))
        rw [← Fin.append_snoc, Fin.snoc_init_self]
        exact hφ

/-- Relativize every quantifier of a first-order formula to the ball of a local
formula, while substituting local terms for its free variables. -/
def relativize {σ : Vocabulary} {n k b : ℕ} (r : ℕ)
    (f : Fin n → Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b) :
    Formula σ n → Lax185574Proofs.Gaifman.Locality.LocalFormula σ k r b
  | .rel R args => .rel R (fun i => LocalTerm.ofTermWith f (args i))
  | .eq left right => .eq (LocalTerm.ofTermWith f left)
      (LocalTerm.ofTermWith f right)
  | .not φ => .not (relativize r f φ)
  | .or φ ψ => .or (relativize r f φ) (relativize r f ψ)
  | .ex φ => .ex (relativize r (LocalTerm.liftSubst f) φ)

/-- Correctness of syntactic relativization. -/
theorem sat_relativize {σ : Vocabulary} {M : Type*} {n k b r : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (f : Fin n → Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b) (φ : Formula σ n) :
    (relativize r f φ).Sat A anchors bound ↔
      SatRestricted A (inBallAround A r anchors) φ
        (fun i => (f i).eval A anchors bound) := by
  induction φ generalizing b with
  | rel R args =>
      simp only [relativize, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat,
        SatRestricted, LocalTerm.eval_ofTermWith]
  | eq left right =>
      simp only [relativize, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat,
        SatRestricted, LocalTerm.eval_ofTermWith]
  | not φ ih =>
      simp only [relativize, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat, SatRestricted]
      exact not_congr (ih bound f)
  | or φ ψ ihφ ihψ =>
      simp only [relativize, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat, SatRestricted]
      exact or_congr (ihφ bound f) (ihψ bound f)
  | ex φ ih =>
      simp only [relativize, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat, SatRestricted]
      apply exists_congr
      intro x
      apply and_congr_right
      intro _
      rw [ih (Fin.snoc bound x) (LocalTerm.liftSubst f)]
      rw [LocalTerm.eval_liftSubst]

end Lax185574Proofs.Gaifman.Relativize
