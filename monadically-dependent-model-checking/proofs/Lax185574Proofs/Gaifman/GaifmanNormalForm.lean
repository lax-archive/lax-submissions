import Lax185574Proofs.Gaifman.Locality
import Mathlib.Data.Fintype.Basic

/-!
Gaifman normal forms.

A Gaifman normal form for a formula with `k` free variables is a Boolean
combination of formulas local around the `k` free variables and of basic
local sentences. At radius `r`, a basic local sentence asserts that there
are `s` witnesses, pairwise at Gaifman distance greater than `2r`, all
satisfying the same one-variable `r`-local formula. The syntax is reified,
and every atom records its own radius. The case `s = 0` is allowed and is
vacuously true. Pairwise separation is imposed only for distinct witness
indices.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`concepts/Lax512892/GaifmanNormalForm.lean`.
-/

namespace Lax185574Proofs.Gaifman.GaifmanNormalForm

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.FirstOrder Lax185574Proofs.Gaifman.Locality

universe u

/-- Boolean combinations of atoms of type `α`. -/
inductive BooleanCombination (α : Type u) : Type u
  /-- An atomic constituent. -/
  | atom (a : α)
  /-- Truth, serving also as the empty Boolean combination. -/
  | truth
  /-- Negation. -/
  | not (b : BooleanCombination α)
  /-- Conjunction. -/
  | and (b c : BooleanCombination α)

namespace BooleanCombination

/-- Evaluation of a Boolean combination from an interpretation of its atoms. -/
def eval {α : Type u} (value : α → Prop) : BooleanCombination α → Prop
  | .atom a => value a
  | .truth => True
  | .not b => ¬ b.eval value
  | .and b c => b.eval value ∧ c.eval value

/-- The atoms occurring in a Boolean combination, with multiplicity. -/
def atoms {α : Type u} : BooleanCombination α → List α
  | .atom a => [a]
  | .truth => []
  | .not b => b.atoms
  | .and b c => b.atoms ++ c.atoms

end BooleanCombination

/-- A basic local sentence at radius `r`: `witnessCount` pairwise far-apart
witnesses all satisfy the same one-variable local formula `property`. -/
structure BasicLocalSentence (σ : Vocabulary) (r : ℕ) where
  /-- The number of witnesses. -/
  witnessCount : ℕ
  /-- The uniform local property required of every witness. -/
  property : LocalFormula σ 1 r 0

namespace BasicLocalSentence

/-- Semantics of a basic local sentence. -/
def Sat {σ : Vocabulary} {M : Type*} {r : ℕ} (A : Structure σ M)
    (β : BasicLocalSentence σ r) : Prop :=
  ∃ witnesses : Fin β.witnessCount → M,
    (∀ i, β.property.Sat A (fun _ => witnesses i) Fin.elim0) ∧
      ∀ i j, i ≠ j →
        ¬ distanceAtMost A (2 * r) (witnesses i) (witnesses j)

end BasicLocalSentence

/-- An atom of a Gaifman normal form. Each atom carries its own locality
radius. -/
inductive NormalAtom (σ : Vocabulary) (k : ℕ) : Type
  /-- A formula local around the `k` free variables. -/
  | local (r : ℕ) (formula : LocalFormula σ k r 0)
  /-- A basic local sentence. -/
  | basic (r : ℕ) (sentence : BasicLocalSentence σ r)

/-- A Gaifman normal form for a formula with `k` free variables. -/
structure NormalForm (σ : Vocabulary) (k : ℕ) where
  /-- A Boolean combination of local formulas and basic local sentences. -/
  body : BooleanCombination (NormalAtom σ k)

namespace NormalForm

/-- Satisfaction of a normal form under an environment for its free variables. -/
def Sat {σ : Vocabulary} {M : Type*} {k : ℕ} (A : Structure σ M)
    (env : Fin k → M) (nf : NormalForm σ k) : Prop :=
  nf.body.eval fun atom =>
    match atom with
    | .local _ ψ => ψ.Sat A env Fin.elim0
    | .basic _ basic => basic.Sat A

/-- Every constituent occurring in `nf` has radius at most `bound`. -/
def RadiiBounded {σ : Vocabulary} {k : ℕ}
    (nf : NormalForm σ k) (bound : ℕ) : Prop :=
  ∀ atom : NormalAtom σ k, atom ∈ nf.body.atoms →
    match atom with
    | .local r _ => r ≤ bound
    | .basic r _ => r ≤ bound

/-- Every basic local sentence occurring in `nf` uses at most `bound`
witnesses. -/
def WitnessesBounded {σ : Vocabulary} {k : ℕ}
    (nf : NormalForm σ k) (bound : ℕ) : Prop :=
  ∀ (r : ℕ) (basic : BasicLocalSentence σ r),
    NormalAtom.basic r basic ∈ nf.body.atoms → basic.witnessCount ≤ bound

end NormalForm

end Lax185574Proofs.Gaifman.GaifmanNormalForm
