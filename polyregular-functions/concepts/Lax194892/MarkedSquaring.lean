import Mathlib.Data.List.Basic

/-!
---
title: Marked squaring
type: definition
---
The *marked squaring* function (Example 33 of *Transducers*) copies an input
string of length $n$ exactly $n$ times, underlining the first $i$ letters of the
$i$-th copy:
$$1234 \mapsto \underline{1}234\;\underline{12}34\;\underline{123}4\;\underline{1234}.$$
The output has length $n^2$ over the alphabet $A + A$, one copy of the input
alphabet underlined and one plain. It is the one prime function of quadratic
growth that, added to the regular functions, generates the polyregular
functions (Definition D.0.1).

# Formalization notes

Underlined letters are `Sum.inl`, plain ones `Sum.inr`; the `i`-th copy is
`(w.take (i+1)).map Sum.inl ++ (w.drop (i+1)).map Sum.inr`. Marked squaring is a
family of functions, one for each alphabet.
-/

namespace Lax194892.MarkedSquaring

/-- Marked squaring: `n` copies of an input of length `n`, the first `i` letters
of the `i`-th copy underlined. -/
def markedSquare (A : Type) (w : List A) : List (A ⊕ A) :=
  ((List.range w.length).map
    (fun i => (w.take (i + 1)).map Sum.inl ++ (w.drop (i + 1)).map Sum.inr)).flatten

end Lax194892.MarkedSquaring
