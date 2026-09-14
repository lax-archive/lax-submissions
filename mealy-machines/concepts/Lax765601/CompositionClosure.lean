import Mathlib.Data.Finite.Defs

/-!
---
title: Closure of a family of functions under composition
type: definition
---
The transducer classes of the book are described by *decomposition into primes*:
a class is the set of all finite compositions
$$A_0^* \xrightarrow{f_1} A_1^* \xrightarrow{f_2} \cdots \xrightarrow{f_n} A_n^*$$
of functions taken from some family of *prime* functions, with the intermediate
alphabets finite. The book writes $P^*$ for this closure of a family $P$ under
composition — the Kleene star of the family — as in
$\mathrm{Mealy} = (\mathrm{Reversible} \cup \mathrm{Flip\text{-}flop})^*$, the
Krohn–Rhodes theorem (Theorem A.2.2). The same idiom defines the rational
functions from their primes (Theorem B.2.6), the regular functions (Definition
C.0.1) and the polyregular functions (Definition D.0.1).

# Formalization notes

A *family* is a predicate on string-to-string functions indexed by the input and
output alphabets, `∀ (A B : Type), (List A → List B) → Prop`. The closure
`CompClosure P` is the least family containing `P`, the identity on every
alphabet, and closed under composition through a *finite* intermediate alphabet;
that finiteness is the constructor's instance argument `[Finite B]`, so that
"composition of primes" never passes through an infinite alphabet. Because the
closure is inductively defined, every statement of the form "every composition of
primes has property X" is proved by induction on the composition tree, and the
theorems of the book about a class defined this way are statements about the
closure, not about a syntactic list of factors.
-/

namespace Lax765601.CompositionClosure

/-- A family of string-to-string functions, indexed by the input and the output
alphabet. -/
abbrev Family : Type 1 := ∀ (A B : Type), (List A → List B) → Prop

/-- The closure `P*` of a family `P` under composition: the identity functions, the
members of `P`, and the compositions `g ∘ f` of two members of the closure through
a finite intermediate alphabet. -/
inductive CompClosure (P : Family) : Family
  /-- A prime function belongs to the closure. -/
  | base {A B : Type} {f : List A → List B} : P A B f → CompClosure P A B f
  /-- The identity on every alphabet belongs to the closure. -/
  | protected id (A : Type) : CompClosure P A A _root_.id
  /-- The closure is closed under composition through a finite alphabet. -/
  | comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C} :
      CompClosure P A B f → CompClosure P B C g → CompClosure P A C (g ∘ f)

/-- The union of two families. -/
def FamUnion (P Q : Family) : Family := fun A B f => P A B f ∨ Q A B f

end Lax765601.CompositionClosure
