import Lax132576.RationalFunctions
import Lax916827.RegularFunctions
import Lax709149.Types

/-!
---
title: Regular functions on types under string representation
type: definition
---
A type-to-type function $f : A \to B$ is *regular under string representation*
(Definition C.5.2 of *Transducers*) if there is a regular string-to-string
function $f'$ over the eight-letter alphabet making the square commute: $f'$
maps the representation of $a$ to the representation of $f(a)$, for every
$a \in A$. Rational functions between types are defined in the same way. Nothing
is required of $f'$ on the strings that represent no element.

# Formalization notes

`IsRegularUnderRepr f` asks for a regular `f' : List Sym8 → List Sym8` with
`f' (A.repr a) = B.repr (f a)` for all `a`; `IsRationalUnderRepr` for a rational
one.
-/

namespace Lax709149.RegularUnderRepresentation

open Lax132576.RationalFunctions Lax916827.RegularFunctions Lax709149.Types

/-- A type-to-type function is regular under string representation if a regular
string-to-string function maps the representation of `a` to the representation
of `f a`. -/
def IsRegularUnderRepr {A B : Ty} (f : A.Elt → B.Elt) : Prop :=
  ∃ f' : List Sym8 → List Sym8, IsRegularFun f' ∧ ∀ a : A.Elt, f' (A.repr a) = B.repr (f a)

/-- A type-to-type function is rational under string representation. -/
def IsRationalUnderRepr {A B : Ty} (f : A.Elt → B.Elt) : Prop :=
  ∃ f' : List Sym8 → List Sym8, IsRationalFun f' ∧ ∀ a : A.Elt, f' (A.repr a) = B.repr (f a)

end Lax709149.RegularUnderRepresentation
