import Mathlib.Data.List.Basic

/-!
---
title: Map lifting
type: definition
---
Let $f : A^* \to B^*$ be a string-to-string function. Its *map lifting*
(Definition A.2.3 of *Transducers*) is the function
$$\mathsf{map}\, f : (A + 1)^* \to (B + 1)^*$$
over the alphabets extended by a fresh separator letter $\#$, which applies $f$ to
every block of the input delimited by the separator:
$$w_1 \# w_2 \# \cdots \# w_n \quad\mapsto\quad f(w_1) \# f(w_2) \# \cdots \# f(w_n),$$
where the strings $w_1, \ldots, w_n$ do not use the separator. The map lifting
is the construction by which a transducer is applied to a list of input strings
in parallel; it is used many times in the book, first in the proof of the
Krohn–Rhodes theorem (Lemma A.2.4), and the prime regular functions of Part C
are map liftings.

# Formalization notes

The alphabet `A + 1` is `Option A`, the separator being `none`. `splitSep` cuts a
string over `Option A` into its maximal separator-free blocks, always producing
one block more than there are separators — the empty string is the one block
`[]`, and `w #` ends with an empty block — so that `mapLift f` is the
concatenation of the images of the blocks with the separator put back between
them, exactly as displayed. With this reading the map lifting is defined on
*every* string over `Option A`, including those beginning or ending with a
separator or with consecutive separators, which then delimit empty blocks.
-/

namespace Lax765601.MapLifting

/-- Cut a string over `A + 1` (the separator being `none`) into its maximal blocks
without the separator; there is always one block more than there are separators.
-/
def splitSep {A : Type} : List (Option A) → List (List A)
  | [] => [[]]
  | none :: w => [] :: splitSep w
  | some a :: w =>
      match splitSep w with
      | [] => [[a]]
      | u :: us => (a :: u) :: us

/-- The map lifting of `f`: apply `f` to every block delimited by the separator,
`w₁ # ⋯ # wₙ ↦ f w₁ # ⋯ # f wₙ`. -/
def mapLift {A B : Type} (f : List A → List B) (w : List (Option A)) : List (Option B) :=
  List.intercalate [none] ((splitSep w).map (fun u => (f u).map some))

end Lax765601.MapLifting
