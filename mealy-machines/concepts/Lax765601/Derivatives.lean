import Mathlib.Data.List.Basic

/-!
---
title: Derivatives of a string-to-string function
type: definition
---
A *derivative* of a length preserving string-to-string function $f : A^* \to B^*$
is a function of the form
$$f(w\_) \;:\; v \;\mapsto\; f(wv) \text{ with the first } |w| \text{ letters of the output removed},$$
for some input string $w$ (Section A.2.3 of *Transducers*). The derivative is the
output that $f$ still produces *after* having read $w$; for a function computed
by a Mealy machine it is determined by the state reached after reading $w$, which
is the observation behind the Myhill–Nerode lemma for Mealy machines (Lemma
A.2.10): a function is computed by a Mealy machine if and only if it is
letter-to-letter, its $n$-th output letter depends only on the first $n$ input
letters, and it has finitely many derivatives. The minimal Mealy machine of such
a function has the derivatives as its states.

# Formalization notes

`deriv f w v` drops the first `w.length` letters of `f (w ++ v)`. An earlier
edition of the book wrote `f(w\_)(v) = f(wv)` without removing the output
produced while reading `w`; with that reading even the identity function has
infinitely many derivatives and Lemma A.2.10 fails, so the definition above is
the one the book now prints and the one its proof uses. No length preservation
is required of `f` for the definition to make sense.
-/

namespace Lax765601.Derivatives

/-- The derivative `f(w_)` of `f`: the output `f` produces after having read `w`,
namely `v ↦ f (w v)` with the first `|w|` letters of the output removed. -/
def deriv {A B : Type} (f : List A → List B) (w : List A) : List A → List B :=
  fun v => (f (w ++ v)).drop w.length

end Lax765601.Derivatives
