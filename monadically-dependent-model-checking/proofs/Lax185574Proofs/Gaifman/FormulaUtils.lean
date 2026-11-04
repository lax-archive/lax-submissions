import Lax185574Proofs.Gaifman.LocalSyntax

/-!
Small first-order syntax combinators used to spell out Gaifman adjacency and
bounded distance inside local formulas.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/FormulaUtils.lean`.
-/

namespace Lax185574Proofs.Gaifman.FormulaUtils

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.FirstOrder
open Lax185574Proofs.Gaifman.LocalSyntax

namespace Term

/-- Rename the variables of a first-order term. -/
def rename {σ : Vocabulary} {k k' : ℕ} (f : Fin k → Fin k') :
    Term σ k → Term σ k'
  | .var i => .var (f i)
  | .const c => .const c

@[simp] theorem eval_rename {σ : Vocabulary} {M : Type*} {k k' : ℕ}
    (A : Structure σ M) (env : Fin k' → M) (f : Fin k → Fin k')
    (t : Term σ k) :
    (rename f t).eval A env = t.eval A (env ∘ f) := by
  cases t <;> rfl

/-- Simultaneously substitute a term for each variable. -/
def subst {σ : Vocabulary} {k k' : ℕ} (s : Fin k → Term σ k') :
    Term σ k → Term σ k'
  | .var i => s i
  | .const c => .const c

@[simp] theorem eval_subst {σ : Vocabulary} {M : Type*} {k k' : ℕ}
    (A : Structure σ M) (env : Fin k' → M) (s : Fin k → Term σ k')
    (t : Term σ k) :
    (subst s t).eval A env = t.eval A (fun i => (s i).eval A env) := by
  cases t <;> rfl

/-- Lift a simultaneous substitution under one new last variable. -/
def liftSubst {σ : Vocabulary} {k k' : ℕ} (s : Fin k → Term σ k') :
    Fin (k + 1) → Term σ (k' + 1) :=
  Fin.snoc (fun i => rename Fin.castSucc (s i)) (.var (Fin.last k'))

@[simp] theorem eval_liftSubst_castSucc {σ : Vocabulary} {M : Type*}
    {k k' : ℕ} (A : Structure σ M) (env : Fin k' → M) (x : M)
    (s : Fin k → Term σ k') (i : Fin k) :
    (liftSubst s i.castSucc).eval A (Fin.snoc env x) = (s i).eval A env := by
  simp [liftSubst]

@[simp] theorem eval_liftSubst_last {σ : Vocabulary} {M : Type*}
    {k k' : ℕ} (A : Structure σ M) (env : Fin k' → M) (x : M)
    (s : Fin k → Term σ k') :
    (liftSubst s (Fin.last k)).eval A (Fin.snoc env x) = x := by
  simp only [liftSubst, Fin.snoc_last, Term.eval]

end Term

namespace Formula

/-- Rename free variables. Under a binder, the new last variable stays last. -/
def rename {σ : Vocabulary} {k k' : ℕ} (f : Fin k → Fin k') :
    Formula σ k → Formula σ k'
  | .rel R args => .rel R (fun i => Term.rename f (args i))
  | .eq left right => .eq (Term.rename f left) (Term.rename f right)
  | .not φ => .not (rename f φ)
  | .or φ ψ => .or (rename f φ) (rename f ψ)
  | .ex φ => .ex (rename (liftFin f) φ)

/-- Renaming commutes with first-order satisfaction. -/
theorem sat_rename {σ : Vocabulary} {M : Type*} {k k' : ℕ}
    (A : Structure σ M) (env : Fin k' → M) (f : Fin k → Fin k')
    (φ : Formula σ k) :
    Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A (rename f φ) env ↔
      Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A φ (env ∘ f) := by
  induction φ generalizing k' with
  | rel R args =>
      simp only [rename, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat, Term.eval_rename]
  | eq left right =>
      simp only [rename, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat, Term.eval_rename]
  | not φ ih =>
      simp only [rename, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat]
      exact not_congr (ih env f)
  | or φ ψ ihφ ihψ =>
      simp only [rename, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat]
      exact or_congr (ihφ env f) (ihψ env f)
  | ex φ ih =>
      simp only [rename, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat]
      apply exists_congr
      intro x
      rw [ih (Fin.snoc env x) (liftFin f)]
      have henv : Fin.snoc env x ∘ liftFin f = Fin.snoc (env ∘ f) x := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftFin]
      rw [henv]

/-- Simultaneously substitute terms for the free variables of a formula. -/
def subst {σ : Vocabulary} {k k' : ℕ} (s : Fin k → Term σ k') :
    Formula σ k → Formula σ k'
  | .rel R args => .rel R (fun i => Term.subst s (args i))
  | .eq left right => .eq (Term.subst s left) (Term.subst s right)
  | .not φ => .not (subst s φ)
  | .or φ ψ => .or (subst s φ) (subst s ψ)
  | .ex φ => .ex (subst (Term.liftSubst s) φ)

/-- Substitution commutes with first-order satisfaction. -/
theorem sat_subst {σ : Vocabulary} {M : Type*} {k k' : ℕ}
    (A : Structure σ M) (env : Fin k' → M) (s : Fin k → Term σ k')
    (φ : Formula σ k) :
    Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A (subst s φ) env ↔
      Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A φ
        (fun i => (s i).eval A env) := by
  induction φ generalizing k' with
  | rel R args =>
      simp only [subst, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat, Term.eval_subst]
  | eq left right =>
      simp only [subst, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat, Term.eval_subst]
  | not φ ih =>
      simp only [subst, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat]
      exact not_congr (ih env s)
  | or φ ψ ihφ ihψ =>
      simp only [subst, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat]
      exact or_congr (ihφ env s) (ihψ env s)
  | ex φ ih =>
      simp only [subst, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat]
      apply exists_congr
      intro x
      rw [ih (Fin.snoc env x) (Term.liftSubst s)]
      have henv : (fun i =>
          (Term.liftSubst s i).eval A (Fin.snoc env x)) =
          Fin.snoc (fun i => (s i).eval A env) x := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp
      rw [henv]

/-- Conjunction in the primitive `not`/`or` syntax. -/
def conjunction {σ : Vocabulary} {k : ℕ} (φ ψ : Formula σ k) : Formula σ k :=
  .not (.or (.not φ) (.not ψ))

@[simp] theorem sat_conjunction {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (φ ψ : Formula σ k) :
    Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A (conjunction φ ψ) env ↔
      Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A φ env ∧
        Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A ψ env := by
  simp only [conjunction, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat]
  tauto

/-- A tautology in any context containing at least one variable. -/
def truth {σ : Vocabulary} {k : ℕ} (i : Fin k) : Formula σ k :=
  .eq (.var i) (.var i)

/-- A contradiction in any context containing at least one variable. -/
def falsity {σ : Vocabulary} {k : ℕ} (i : Fin k) : Formula σ k :=
  .not (truth i)

@[simp] theorem sat_truth {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (i : Fin k) :
    Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A (truth i) env :=
  rfl

@[simp] theorem not_sat_falsity {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (i : Fin k) :
    ¬ Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A (falsity i) env := by
  simp [falsity, truth, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat]

/-- Finite disjunction, with an explicit false formula for the empty list. -/
def disjunctions {σ : Vocabulary} {k : ℕ} (falseFormula : Formula σ k) :
    List (Formula σ k) → Formula σ k
  | [] => falseFormula
  | φ :: φs => .or φ (disjunctions falseFormula φs)

@[simp] theorem sat_disjunctions {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M)
    (falseFormula : Formula σ k)
    (hfalse : ¬ Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A falseFormula env)
    (formulas : List (Formula σ k)) :
    Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A
        (disjunctions falseFormula formulas) env ↔
      ∃ φ ∈ formulas, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A φ env := by
  induction formulas with
  | nil => simp [disjunctions, hfalse]
  | cons φ formulas ih =>
      simp only [disjunctions, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat, ih]
      aesop

/-- Add `n` existential quantifiers at the last `n` variable levels. -/
def exN {σ : Vocabulary} : (n : ℕ) → {k : ℕ} →
    Formula σ (k + n) → Formula σ k
  | 0, _, φ => φ
  | n + 1, k, φ =>
      exN n (.ex (Nat.add_succ k n ▸ φ))

/-- Concatenation of an environment and a tuple. -/
def appendEnv {M : Type*} {k n : ℕ} (env : Fin k → M) (xs : Fin n → M) :
    Fin (k + n) → M :=
  Fin.append env xs

/-- Satisfaction of `exN` is existential quantification over a finite tuple. -/
theorem sat_exN {σ : Vocabulary} {M : Type*} (A : Structure σ M) :
    ∀ (n : ℕ) {k : ℕ} (φ : Formula σ (k + n)) (env : Fin k → M),
      Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A (exN n φ) env ↔
        ∃ xs : Fin n → M,
          Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A φ (appendEnv env xs) := by
  intro n
  induction n with
  | zero =>
      intro k φ env
      constructor
      · intro h
        exact ⟨Fin.elim0, by simpa [exN, appendEnv] using h⟩
      · rintro ⟨xs, h⟩
        simpa [exN, appendEnv, Subsingleton.elim xs Fin.elim0] using h
  | succ n ih =>
      intro k φ env
      simp only [exN, Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat]
      rw [ih]
      constructor
      · rintro ⟨xs, x, h⟩
        refine ⟨Fin.snoc xs x, ?_⟩
        change Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A φ
          (Fin.append env (Fin.snoc xs x))
        rw [Fin.append_snoc]
        exact h
      · rintro ⟨xs, h⟩
        refine ⟨Fin.init xs, xs (Fin.last n), ?_⟩
        change Lax185574Proofs.Gaifman.FirstOrder.Formula.Sat A φ
          (Fin.snoc (Fin.append env (Fin.init xs)) (xs (Fin.last n)))
        rw [← Fin.append_snoc, Fin.snoc_init_self]
        exact h

end Formula

end Lax185574Proofs.Gaifman.FormulaUtils
