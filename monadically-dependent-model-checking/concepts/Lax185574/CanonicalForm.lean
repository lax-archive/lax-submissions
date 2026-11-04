import Lax185574.Algorithms

/-!
---
title: Canonical form
type: observation
---
A type tree given by a representation whose sets need not be sorted or
duplicate-free can be brought into canonical form in polynomial time.

# Formalization notes

The statement is made for one set: a list of elements of an encoded
type, possibly unsorted and with repetitions, is turned into the finite
set of its entries, whose encoding is the sorted duplicate-free list of
the encodings of the elements. The algorithm receives the list of the
encodings of the elements, so every element is preceded by its length,
and it can find the boundaries of the elements without knowing their
type. One algorithm works for all types. A type tree is brought into
canonical form by applying this at every node, from the leaves up. That
step is part of the proofs that use it.

The algorithm is an algorithm in the sense of `Lax185574.Algorithms`.
Polynomial time means time `O((N + 1)^a)` on an input of length `N`.
The finite set `l.toFinset` needs decidable equality of the elements,
which every type has classically.
-/

namespace Lax185574.CanonicalForm

open Lax185574.Encoding Lax185574.Algorithms

/-- **Canonical form.** One algorithm turns a list of elements, given by
their encodings, into the finite set of its entries, in polynomial time.
It sorts the encodings and removes duplicates. -/
axiom exists_program_canonical :
    ∃ (A : Algorithm) (c a : ℕ), ∀ (α : Type) [Encode α] [DecidableEq α] (l : List α),
      A.Computes c (l.map encode) l.toFinset (((encode (l.map encode)).length + 1) ^ a)

end Lax185574.CanonicalForm
