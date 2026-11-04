import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Set.Card

/-!
---
title: Types of bounded quantifier rank
type: definition
---
Let A be a structure and W a set of its elements. A formula with
parameters from W is a formula in the signature of A expanded by a
constant for every element of W. For a tuple v̄ ∈ V(A)^k and q ∈ ℕ, the
*type of quantifier rank q of v̄ over W*, written tp_q(v̄/W), is the set
of all formulas φ(x₁, …, x_k) with parameters from W and of quantifier
rank at most q such that A ⊨ φ(v̄).

For sets X, Y of elements,
Types_{k,q}(X/Y) = { tp_q(v̄/Y) : v̄ ∈ X^k }
is the set of types realized by k-tuples from X. The notation omits /Y
when Y is empty, and then the types are those without parameters,
tp_q(v̄) and Types_{k,q}(X). The number of realized types |Types_{k,q}(X/Y)| is the
quantity that the paper bounds throughout.

# Formalization notes

Types without parameters, `rankType` and `types`, are defined separately
from types over a parameter set, `rankTypeOver` and `typesOver`. Over
the empty set the two agree up to the evident bijection of formulas.
The separate version is needed because the formula type of the
parameterized version depends on the parameter set, so it would not
let one compare types in different structures, such as two induced
substructures.

Formulas are those of mathlib's first-order logic, `L.Formula α`, where
`α` indexes the free variables. A parameter from `W` is a free variable
of the right summand of `Fin k ⊕ W`, and it is always assigned the
element that it names. This is the same as adjoining a constant for each
element of `W`, and it does not change the quantifier rank. The type is
literally the set of formulas, as in the paper, and the count is the
cardinality of the set of realized types. It is finite whenever `X` is
finite, since it is the image of `X^k`.

The count `typeCountOver` takes the structure as an explicit argument,
because it is applied to structures that are not instances, such as the
expansion of a graph by colors.

Mathlib's formulas are built from falsum, equality, relations,
implication and universal quantification. The quantifier rank is the
nesting depth of the universal quantifier. Every formula of the usual
syntax with ¬, ∧, ∨, ∃ and ∀ translates into this syntax without
changing its quantifier rank, so the types are the usual ones.
-/

namespace Lax185574.FirstOrderTypes

open FirstOrder FirstOrder.Language

universe u v w z

variable {L : Language.{u, v}}

/-- The quantifier rank of a formula: the nesting depth of its
quantifiers. -/
def quantifierRank {α : Type w} : {n : ℕ} → L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (quantifierRank φ) (quantifierRank ψ)
  | _, .all φ => quantifierRank φ + 1

variable {V : Type z}

section

variable [L.Structure V]

/-- The type `tp_q(v̄)` of quantifier rank `q` of the tuple `v`: the
formulas of quantifier rank at most `q`, without parameters, that hold
of `v`. -/
def rankType (q : ℕ) {k : ℕ} (v : Fin k → V) : Set (L.Formula (Fin k)) :=
  {φ | quantifierRank φ ≤ q ∧ φ.Realize v}

/-- `Types_{k,q}(X)`: the types of quantifier rank `q` of the `k`-tuples
from `X`. -/
def types (k q : ℕ) (X : Set V) : Set (Set (L.Formula (Fin k))) :=
  rankType q '' {v : Fin k → V | ∀ i, v i ∈ X}

/-- `|Types_{k,q}(X)|`: the number of types of quantifier rank `q`
realized by `k`-tuples from `X`. -/
noncomputable def typeCount (k q : ℕ) (X : Set V) : ℕ :=
  (types (L := L) k q X).ncard

/-- The type `tp_q(v̄/W)` of quantifier rank `q` of the tuple `v` over
the parameter set `W`: the formulas of quantifier rank at most `q` with
parameters from `W` that hold of `v`. -/
def rankTypeOver (q : ℕ) (W : Set V) {k : ℕ} (v : Fin k → V) :
    Set (L.Formula (Fin k ⊕ W)) :=
  {φ | quantifierRank φ ≤ q ∧ φ.Realize (Sum.elim v Subtype.val)}

/-- `Types_{k,q}(X/Y)`: the types of quantifier rank `q` over `Y` of the
`k`-tuples from `X`. -/
def typesOver (k q : ℕ) (X Y : Set V) : Set (Set (L.Formula (Fin k ⊕ Y))) :=
  rankTypeOver q Y '' {v : Fin k → V | ∀ i, v i ∈ X}

end

/-- `|Types_{k,q}(X/Y)|`: the number of types of quantifier rank `q` over
`Y` realized by `k`-tuples from `X`, in the structure `M`. -/
noncomputable def typeCountOver (M : L.Structure V) (k q : ℕ) (X Y : Set V) : ℕ :=
  (@typesOver L V M k q X Y).ncard

end Lax185574.FirstOrderTypes
