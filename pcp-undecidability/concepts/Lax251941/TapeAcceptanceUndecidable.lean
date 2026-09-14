import Mathlib.Computability.Halting
import Lax251941.TuringMachines

/-!
---
title: The acceptance problem for Turing machines is undecidable
type: theorem
---
No algorithm decides, given a single-tape Turing machine $M$ and an input word
$w$, whether $M$ accepts $w$. This is Sipser's Theorem 4.11 for the tape
machines of Section 5.2: a decision procedure for their acceptance problem
would, through the Turing-completeness of the tape machines
(`TuringCompleteness`), decide the acceptance problem $A_{TM}$ of
`Acceptance`, which the diagonalisation argument rules out. One simulation
suffices, since a decision procedure is uniform in the machine: the machine
simulating a fixed universal function is held fixed and only its input varies.

# Formalization notes

Decidability of a problem on pairs `(M, w)` is mathlib's `ComputablePred` on the
type `TM × List ℕ`, with machines encoded by their tables (the `Primcodable`
instance of `TuringMachines`).
-/

namespace Lax251941.TapeAcceptanceUndecidable

open Lax251941.TuringMachines

/-- The acceptance problem for single-tape Turing machines is undecidable. -/
axiom not_computablePred_accepts :
    ¬ ComputablePred fun p : TM × List ℕ => p.1.Accepts p.2

end Lax251941.TapeAcceptanceUndecidable
