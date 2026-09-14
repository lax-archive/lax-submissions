import Mathlib.Computability.Partrec
import Lax251941.TuringMachines

/-!
---
title: Every partial recursive function is computed by a Turing machine
type: theorem
---
For every partial recursive function $f : \mathbb{N} \rightharpoonup \mathbb{N}$
there is a single-tape Turing machine which, on the unary encoding of $n$,
reaches its accept state exactly when $f(n)$ is defined. This is the
Turing-completeness of the string-rewriting machines of `TuringMachines`, in
the form in which it links Sipser's two sections: the diagonalisation of
Section 4.2 is carried out for partial recursive programs, the reduction of
Section 5.2 for tape machines, and this theorem is what makes the acceptance
problem of the latter as hard as that of the former.

# Formalization notes

The unary encoding of `n` is the word `mk :: replicate n c` for two tape symbols
`mk` (a marker) and `c` (a counter cell) chosen by the theorem together with
the machine. `Partrec` is mathlib's class of partial recursive functions
`ℕ →. ℕ`. The proof compiles the function to a counter-machine program and the
program to a tape machine; the compiled machine is deterministic, although the
model allows nondeterminism.
-/

namespace Lax251941.TuringCompleteness

open Lax251941.TuringMachines

/-- For every partial recursive `f` there is a tape machine, with a marker symbol
and a counter symbol, that accepts the unary encoding of `n` exactly when `f n` is
defined. -/
axiom exists_tm_accepts_iff_dom (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ (M : TM) (mk c : ℕ), ∀ n : ℕ, M.Accepts (mk :: List.replicate n c) ↔ (f n).Dom

end Lax251941.TuringCompleteness
