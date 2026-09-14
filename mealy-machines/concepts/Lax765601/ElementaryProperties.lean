import Mathlib.Data.List.Infix

/-!
---
title: Prefix preservation and length preservation
type: definition
---
Three elementary properties of a string-to-string function $f : A^* \to B^*$ that
the characterisation theorems of the book are stated with.

* $f$ is *prefix preserving* if $w \sqsubseteq v$ implies $f(w) \sqsubseteq f(v)$,
  where $\sqsubseteq$ is the prefix order on strings.
* $f$ is *length preserving*, or *letter-to-letter*, if $|f(w)| = |w|$ for every
  input string $w$.
* $f$ is *prefix determined* if the first $n$ output letters depend only on the
  first $n$ input letters: input strings that agree on their first $n$ letters
  have outputs that agree on their first $n$ letters.

For a letter-to-letter function, being prefix determined says exactly that the
$n$-th output letter depends only on the first $n$ input letters, which is
condition (3) of the Myhill–Nerode lemma for Mealy machines (Lemma A.2.10), and
it is the determinism condition of Theorem B.2.7; prefix preservation and length
preservation together are the shape of the machine-independent characterisation
of Mealy machines (Theorem B.4.1).

# Formalization notes

`<+:` is mathlib's prefix relation on lists. The three definitions quantify over
all strings of the input alphabet and carry no finiteness hypothesis.
-/

namespace Lax765601.ElementaryProperties

/-- `f` is prefix preserving: `w ⊑ v` implies `f w ⊑ f v`. -/
def PrefixPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w v : List A, w <+: v → f w <+: f v

/-- `f` is length preserving, i.e. letter-to-letter: the output has the length of
the input. -/
def LengthPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w : List A, (f w).length = w.length

/-- `f` is prefix determined: the first `n` output letters depend only on the
first `n` input letters. -/
def PrefixDetermined {A B : Type} (f : List A → List B) : Prop :=
  ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n

end Lax765601.ElementaryProperties
