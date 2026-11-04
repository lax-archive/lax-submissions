import Lax185574.GaifmanGraph
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Logic.Equiv.Fin.Basic

/-!
---
title: Local formulas and basic local sentences
type: definition
---
Fix a finite relational signature σ of arity α. Two σ-formulas φ(x̄)
and ψ(x̄) are *equivalent* if for every σ-structure A and every tuple
ā ∈ V(A)^{|x̄|}, A ⊨ φ(ā) if and only if A ⊨ ψ(ā).

The formula adj_σ(x₁, x₂) tests whether x₁ and x₂ are adjacent in the
Gaifman graph. For every relation R ∈ σ of arity β ≤ α it tests whether
there are elements x₃, …, x_β such that some permutation of x₁, …, x_β
satisfies R. Its quantifier rank is at most α − 2. From it one derives
the formula dist(x₁, x₂) ≤ r, which checks whether x₁ and x₂ have
distance at most r in the Gaifman graph. It quantifies the candidate
vertices of a path and checks the required adjacencies in parallel, so
its quantifier rank is at most r + α.

A σ-formula φ(x̄) is *r-local* if every quantifier appearing in φ(x̄) is
of the form ∀y ∈ Ball_s(x̄) or ∃y ∈ Ball_s(x̄) for some s ≤ r, where the
ball checks are implemented using the dist formulas, which are exempt
from this condition. A sentence ψ is *basic r-local* if there is some
r' ≤ r such that ψ is of the form

  ∃x₁, …, x_m ( ⋀_{1 ≤ i < j ≤ m} dist(xᵢ, xⱼ) > 2r' ∧ ⋀_{1 ≤ i ≤ m} φ(xᵢ) )

for an r'-local formula φ.

# Formalization notes

Formulas are mathlib's, `L.Formula (Fin k)` for formulas with free
variables x₁, …, x_k, and `L.BoundedFormula (Fin k) n` for their
subformulas with n further bound variables. A finite relational
signature is a relational language with finitely many relation symbols
in total. The arity bound α plays no role in the definitions.

Equivalence quantifies over all structures whose domain lies in one
universe, which is an explicit parameter of the definition. The domains
may be empty or infinite.

adj_σ is the conjunction of x₁ ≠ x₂ with the disjunction, over the
relation symbols R of arity β ≥ 2, of ∃x₃ … ∃x_β ⋁_π R(x_{π(1)}, …,
x_{π(β)}), where π ranges over the permutations of the β positions. The
quantified variables may coincide with x₁, x₂ or each other, so this is
exactly adjacency in the Gaifman graph. Symbols of arity at most one
contribute nothing. Its quantifier rank is at most α − 2.

dist(x₁, x₂) ≤ r quantifies the r vertices v₁, …, v_r of a walk
x₁ = v₀, v₁, …, v_r, requires v_r = x₂, and requires every step to be
an equality or an adjacency. So it holds exactly if a walk of length at
most r joins x₁ and x₂, as in `GaifmanGraph.WithinDist`. Its quantifier
rank is at most r plus that of adj_σ, so at most r + α. For r = 0 it is
equivalent to the equality x₁ = x₂.

Finite disjunctions and conjunctions are mathlib's `iSup` and `iInf`.
They fix some order of the members, which affects neither the meaning
nor the quantifier rank. A formula over the variables x₁, x₂ is placed
at given terms by substitution.

The guard of a quantifier over Ball_s(x̄) is the disjunction over i of
dist(xᵢ, y) ≤ s, where y is the newly bound variable. For a formula
without free variables, the ball is empty and the guard is falsum. A
local formula is built from atoms by falsum and implication, which give
all Boolean connectives, and by the guarded quantifiers
∀y (guard → φ) and ∃y (guard ∧ φ). The inner formulas of a local
formula may have more free variables than x̄, namely the bound
variables, but the balls are always taken around x̄. The dist formulas
inside the guards are exempt, exactly as in the paper.

In a basic local sentence the m witnesses are the m bound variables of
an existential block, and "dist(xᵢ, xⱼ) > 2r'" is the negation of the
dist formula of radius 2r'. The case m = 0 is allowed and gives a true
sentence.
-/

namespace Lax185574.LocalFormulas

open FirstOrder FirstOrder.Language

universe u v w a

variable {L : Language.{u, v}}

/-- Two formulas are *equivalent* if they hold of the same tuples in
every structure whose domain lies in the universe `w`. -/
def Equivalent {α : Type a} (φ ψ : L.Formula α) : Prop :=
  ∀ (M : Type w) [L.Structure M] (x : α → M), φ.Realize x ↔ ψ.Realize x

/-- Two formulas are *equivalent on finite structures* if they hold of
the same tuples in every finite structure whose domain lies in the
universe `w`. -/
def FinitelyEquivalent {α : Type a} (φ ψ : L.Formula α) : Prop :=
  ∀ (M : Type w) [Finite M] [L.Structure M] (x : α → M), φ.Realize x ↔ ψ.Realize x

/-- The formula `φ(x₁, …, x_j)` with each `xᵢ` replaced by the term
`t i`, as a subformula with `n` bound variables in scope. -/
def instantiate {β : Type*} {j n : ℕ} (φ : L.Formula (Fin j))
    (t : Fin j → L.Term (β ⊕ Fin n)) : L.BoundedFormula β n :=
  (φ.subst t).relabel id

/-- The variable term in position `m` of a relation atom in `adj_σ`:
positions `0` and `1` are `x₁` and `x₂`, and position `m ≥ 2` is the
bound variable `x_{m+1}`. -/
def adjSlot {l : ℕ} (m : Fin l) : L.Term (Fin 2 ⊕ Fin (l - 2)) :=
  if h : m.val < 2 then Term.var (Sum.inl ⟨m.val, h⟩)
  else Term.var (Sum.inr ⟨m.val - 2, by omega⟩)

/-- The part of `adj_σ` for one relation symbol `R` of arity `l`:
`∃x₃ … ∃x_l ⋁_π R(x_{π(1)}, …, x_{π(l)})` if `l ≥ 2`, and falsum
otherwise. -/
noncomputable def adjVia {l : ℕ} (R : L.Relations l) : L.Formula (Fin 2) :=
  if 2 ≤ l then
    BoundedFormula.exs
      (BoundedFormula.iSup fun π : Equiv.Perm (Fin l) =>
        BoundedFormula.rel R fun m => adjSlot (π m))
  else ⊥

variable (L) in
/-- `adj_σ(x₁, x₂)`: the formula stating that `x₁` and `x₂` are adjacent
in the Gaifman graph. -/
noncomputable def adjFormula [Finite (Σ l, L.Relations l)] : L.Formula (Fin 2) :=
  ∼((Term.var (Sum.inl 0)).bdEqual (Term.var (Sum.inl 1))) ⊓
    BoundedFormula.iSup fun R : Σ l, L.Relations l => adjVia R.2

/-- The vertex `v_i` of the walk quantified in `dist(x₁, x₂) ≤ r`:
`v₀ = x₁`, and `v_i` for `i ≥ 1` is the `i`-th bound variable. -/
def walkVertex {r : ℕ} (i : Fin (r + 1)) : L.Term (Fin 2 ⊕ Fin r) :=
  Fin.cases (motive := fun _ => L.Term (Fin 2 ⊕ Fin r))
    (Term.var (Sum.inl 0)) (fun j => Term.var (Sum.inr j)) i

variable (L) in
/-- `dist(x₁, x₂) ≤ r`: there are `v₁, …, v_r` with `v_r = x₂` such that
each step of `x₁ = v₀, v₁, …, v_r` is an equality or an adjacency. -/
noncomputable def distFormula [Finite (Σ l, L.Relations l)] (r : ℕ) :
    L.Formula (Fin 2) :=
  BoundedFormula.exs
    (((walkVertex (L := L) (Fin.last r)).bdEqual (Term.var (Sum.inl 1))) ⊓
      BoundedFormula.iInf fun i : Fin r =>
        ((walkVertex (L := L) i.castSucc).bdEqual (walkVertex i.succ)) ⊔
          instantiate (adjFormula L) ![walkVertex i.castSucc, walkVertex i.succ])

variable (L) in
/-- The guard `y ∈ Ball_s(x̄)` of a local quantifier, where `x̄` are the
`k` free variables and `y` is the newly bound variable: the disjunction
over `i` of `dist(xᵢ, y) ≤ s`. -/
noncomputable def ballGuard [Finite (Σ l, L.Relations l)] (k s n : ℕ) :
    L.BoundedFormula (Fin k) (n + 1) :=
  BoundedFormula.iSup fun i : Fin k =>
    instantiate (distFormula L s) ![Term.var (Sum.inl i), Term.var (Sum.inr (Fin.last n))]

/-- `IsLocal r φ`: the formula `φ` with free variables `x̄ = x₁, …, x_k`
and `n` further bound variables in scope is `r`-local. It is built from
atoms by falsum, implication and quantifiers guarded by `Ball_s(x̄)` for
some `s ≤ r`. -/
inductive IsLocal [Finite (Σ l, L.Relations l)] (r : ℕ) {k : ℕ} :
    {n : ℕ} → L.BoundedFormula (Fin k) n → Prop
  /-- Falsum is local. -/
  | falsum {n : ℕ} : IsLocal r (BoundedFormula.falsum : L.BoundedFormula (Fin k) n)
  /-- Equality atoms are local. -/
  | equal {n : ℕ} (t₁ t₂ : L.Term (Fin k ⊕ Fin n)) :
      IsLocal r (BoundedFormula.equal t₁ t₂)
  /-- Relation atoms are local. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (Fin k ⊕ Fin n)) :
      IsLocal r (BoundedFormula.rel R ts)
  /-- Implications of local formulas are local. -/
  | imp {n : ℕ} {φ ψ : L.BoundedFormula (Fin k) n} :
      IsLocal r φ → IsLocal r ψ → IsLocal r (φ.imp ψ)
  /-- `∀y ∈ Ball_s(x̄) φ`, that is `∀y (y ∈ Ball_s(x̄) → φ)`, for `s ≤ r`. -/
  | all {n s : ℕ} {φ : L.BoundedFormula (Fin k) (n + 1)} :
      s ≤ r → IsLocal r φ → IsLocal r (∀' (ballGuard L k s n ⟹ φ))
  /-- `∃y ∈ Ball_s(x̄) φ`, that is `∃y (y ∈ Ball_s(x̄) ∧ φ)`, for `s ≤ r`. -/
  | ex {n s : ℕ} {φ : L.BoundedFormula (Fin k) (n + 1)} :
      s ≤ r → IsLocal r φ → IsLocal r (∃' (ballGuard L k s n ⊓ φ))

variable (L) in
/-- The sentence `∃x₁, …, x_m (⋀_{i < j} dist(xᵢ, xⱼ) > 2r' ∧ ⋀_i φ(xᵢ))`. -/
noncomputable def basicLocalSentence [Finite (Σ l, L.Relations l)] (r' m : ℕ)
    (φ : L.Formula (Fin 1)) : L.Sentence :=
  BoundedFormula.exs
    ((BoundedFormula.iInf fun p : {p : Fin m × Fin m // p.1 < p.2} =>
        ∼(instantiate (distFormula L (2 * r'))
          ![Term.var (Sum.inr p.1.1), Term.var (Sum.inr p.1.2)])) ⊓
      BoundedFormula.iInf fun i : Fin m => instantiate φ ![Term.var (Sum.inr i)])

/-- `IsBasicLocal r ψ`: the sentence `ψ` is basic `r`-local. -/
def IsBasicLocal [Finite (Σ l, L.Relations l)] (r : ℕ) (ψ : L.Sentence) : Prop :=
  ∃ r' ≤ r, ∃ (m : ℕ) (φ : L.Formula (Fin 1)),
    IsLocal r' φ ∧ ψ = basicLocalSentence L r' m φ

end Lax185574.LocalFormulas
