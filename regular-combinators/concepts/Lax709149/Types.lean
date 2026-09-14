import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
---
title: Types and their string representation
type: definition
---
The *types* of Section C.5 of *Transducers* (Definition C.5.1) are the
expressions built from the unit type $\mathbb{1}$, which has the unique element
$1$, by the product $A \times B$, the co-product $A + B$ and the list type
$A^*$. Every element of a type has a *string representation* over a fixed
alphabet with eight letters
$$( \quad ) \quad [ \quad ] \quad , \quad 1 \quad L \quad R,$$
defined by induction on the type: the unique element of $\mathbb{1}$ is $1$, an
element of $A + B$ is $L\,a$ or $R\,b$, a pair is $(a, b)$, and a list is
$[a_1, \ldots, a_n]$. Through this representation, type-to-type functions can
be computed by string-to-string transducers (Definition C.5.2).

# Formalization notes

`Ty.Elt` interprets a type as a Lean type — `Unit`, products, sums and lists —
and `Ty.repr` is the representation, a string over the eight-letter alphabet
`Sym8`, the same alphabet for all types. Lists are written with the separating
commas of the book and no trailing separator.
-/

namespace Lax709149.Types

/-- A type: built from the unit type by product, co-product and list. -/
inductive Ty : Type
  | one : Ty
  | prod : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  | list : Ty → Ty
  deriving DecidableEq

/-- The set of elements of a type. -/
def Ty.Elt : Ty → Type
  | .one => Unit
  | .prod A B => A.Elt × B.Elt
  | .sum A B => A.Elt ⊕ B.Elt
  | .list A => List A.Elt

/-- The alphabet with eight letters `(`, `)`, `[`, `]`, `,`, `1`, `L`, `R`. -/
inductive Sym8 : Type
  | lpar | rpar | lbrack | rbrack | comma | one | left | right
  deriving DecidableEq, Fintype

/-- The entries of a list representation, separated by commas. -/
def joinSep : List (List Sym8) → List Sym8
  | [] => []
  | [x] => x
  | x :: xs => x ++ Sym8.comma :: joinSep xs

/-- The string representation of an element: `1` for the unit, `L a` and `R b` for
the co-product, `(a,b)` for a pair, `[a₁,…,aₙ]` for a list. -/
def Ty.repr : (t : Ty) → t.Elt → List Sym8
  | .one, _ => [Sym8.one]
  | .prod A B, x => Sym8.lpar :: (A.repr x.1 ++ Sym8.comma :: (B.repr x.2 ++ [Sym8.rpar]))
  | .sum A B, x => Sum.elim (fun a => Sym8.left :: A.repr a) (fun b => Sym8.right :: B.repr b) x
  | .list A, l => Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack])

end Lax709149.Types
