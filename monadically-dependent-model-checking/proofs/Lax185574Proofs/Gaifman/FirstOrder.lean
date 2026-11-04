import Lax185574Proofs.Gaifman.RelationalStructures

/-!
First-order logic over a relational vocabulary.

First-order terms are variables or constants. Formulas are relation atoms,
equalities, negations, disjunctions, and existential quantifications. The
satisfaction relation gives these constructors their usual semantics, and the
quantifier rank is the greatest nesting depth of quantifiers.

# Formalization notes

`Formula σ k` has exactly `k` available free variables. Variables are finite
levels: an existential quantifier adds the new last variable, and satisfaction
extends an environment with `Fin.snoc`. Consequently a sentence has type
`Formula σ 0`. Closedness is enforced by the type rather than checked by a
separate predicate. Conjunction and universal quantification are definable from
the chosen constructors and do not need additional semantic cases.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`concepts/Lax512892/FirstOrder.lean`.
-/

namespace Lax185574Proofs.Gaifman.FirstOrder

open Lax185574Proofs.Gaifman.RelationalStructures

/-- Terms over `σ` with `k` available variables. -/
inductive Term (σ : Vocabulary) (k : ℕ) : Type
  /-- A variable. -/
  | var (i : Fin k)
  /-- A constant of the vocabulary. -/
  | const (c : σ.Constant)

/-- First-order formulas over `σ` with `k` available free variables. -/
inductive Formula (σ : Vocabulary) : ℕ → Type
  /-- A relation atom. -/
  | rel {k : ℕ} (R : σ.Relation) (args : Fin (σ.arity R) → Term σ k) : Formula σ k
  /-- Equality of terms. -/
  | eq {k : ℕ} (left right : Term σ k) : Formula σ k
  /-- Negation. -/
  | not {k : ℕ} (φ : Formula σ k) : Formula σ k
  /-- Disjunction. -/
  | or {k : ℕ} (φ ψ : Formula σ k) : Formula σ k
  /-- Existential quantification, binding the new last variable. -/
  | ex {k : ℕ} (φ : Formula σ (k + 1)) : Formula σ k

namespace Term

/-- Interpretation of a term in a structure under an environment. -/
def eval {σ : Vocabulary} {M : Type*} {k : ℕ} (A : Structure σ M)
    (env : Fin k → M) : Term σ k → M
  | .var i => env i
  | .const c => A.constant c

end Term

namespace Formula

/-- Satisfaction of a formula in a structure under an environment for its free
variables. -/
def Sat {σ : Vocabulary} {M : Type*} (A : Structure σ M) :
    {k : ℕ} → Formula σ k → (Fin k → M) → Prop
  | _, .rel R args, env => A.relation R (fun i => (args i).eval A env)
  | _, .eq left right, env => left.eval A env = right.eval A env
  | _, .not φ, env => ¬ Sat A φ env
  | _, .or φ ψ, env => Sat A φ env ∨ Sat A ψ env
  | _, .ex φ, env => ∃ x : M, Sat A φ (Fin.snoc env x)

/-- The quantifier rank of a formula. -/
def quantifierRank {σ : Vocabulary} : {k : ℕ} → Formula σ k → ℕ
  | _, .rel _ _ => 0
  | _, .eq _ _ => 0
  | _, .not φ => quantifierRank φ
  | _, .or φ ψ => max (quantifierRank φ) (quantifierRank ψ)
  | _, .ex φ => quantifierRank φ + 1

end Formula

end Lax185574Proofs.Gaifman.FirstOrder
