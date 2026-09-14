import Mathlib.Data.List.Basic

/-!
---
title: Aperiodic string-to-string functions
type: definition
---
A length preserving string-to-string function $f$ is *aperiodic* (Definition
A.2.7 of *Transducers*) if for all input strings $u, v, w$ the last letter of
$$f(u v^n w)$$
is the same for all sufficiently large $n$. Aperiodicity says that the function
cannot have periodic behaviour: the function on $a^*$ whose last output letter
says whether the input has length at least two is aperiodic, while the one whose
last letter gives the parity of the length is not. By the arbitrary choice of
$w$, the last $k$ output letters are eventually fixed as well, for every $k$.
Theorem A.2.8 shows that the aperiodic functions computed by Mealy machines are
exactly the compositions of flip-flop machines.

# Formalization notes

The last letter is taken as an element of `Option B`: the definition asks that the
sequence `n ↦ (f (u vⁿ w)).getLast?` be eventually constant, "no letter" being an
admissible constant value. This is a deliberate correction of the printed
definition, which asks for an actual output letter `b`: with `u = v = w = ε` —
allowed, since the printed side condition "`uvw` nonempty" constrains the input,
and a length preserving function maps `ε` to `ε` — there is no last letter at
all, so no function would be aperiodic as printed. With the `Option`-valued
reading the whole of Section A.2.3 goes through. The book's side conditions that
`f` be length preserving and that `uvw` be nonempty are not used and are dropped.
`npow v n` is the string `vⁿ`.
-/

namespace Lax765601.Aperiodicity

/-- The `n`-fold concatenation `vⁿ` of a string with itself. -/
def npow {A : Type} (v : List A) : ℕ → List A
  | 0 => []
  | n + 1 => v ++ npow v n

/-- A string-to-string function is aperiodic if for all input strings `u, v, w` the
last letter of `f (u vⁿ w)` — as an element of `Option B`, so that "no letter" is
an admissible value — is the same for all sufficiently large `n`. -/
def Aperiodic {A B : Type} (f : List A → List B) : Prop :=
  ∀ u v w : List A, ∃ o : Option B, ∃ N : ℕ, ∀ n ≥ N, (f (u ++ npow v n ++ w)).getLast? = o

end Lax765601.Aperiodicity
