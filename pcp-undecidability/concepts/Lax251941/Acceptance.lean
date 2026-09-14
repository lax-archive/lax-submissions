import Mathlib.Computability.PartrecCode

/-!
---
title: The acceptance problem for machines
type: definition
---
Following Sipser's *Introduction to the Theory of Computation*, Section 4.2, a
*machine* $M$ run on an input $w$ either accepts, rejects, or loops; $M$
*recognises* the language $A$ if it accepts exactly the words of $A$, and
*decides* $A$ if moreover it halts on every input, accepting or rejecting. A
language is *Turing-recognisable* if some machine recognises it and *decidable*
if some machine decides it. The *acceptance problem* is the language
$$A_{TM} = \{\langle M, w\rangle \mid M \text{ is a machine and } M \text{ accepts } w\},$$
where $\langle M, w \rangle$ encodes a machine together with an input word.

# Formalization notes

Sipser's argument is about an arbitrary universal model of computation; the
machines here are mathlib's partial recursive programs `Nat.Partrec.Code`, which
supply exactly the two ingredients his proof needs — a universal machine
(`Nat.Partrec.Code.eval_part`: evaluation is itself computable) and the ability
to program every partial recursive function as a machine
(`Nat.Partrec.Code.exists_code`). Inputs and outputs are natural numbers, which
play the role of strings; a machine *accepts* by halting with output `1` and
*rejects* by halting with output `0`, so that accepting, rejecting and looping
are the three mutually exclusive outcomes of Sipser's definition. The pair
$\langle M, w\rangle$ is the Cantor pairing of the code of `M` (mathlib's
`Encodable.encode`, under which the programs are `Denumerable`) with `w`.
Turing machines in the literal sense, with a tape, appear in `TuringMachines`;
they are where the reduction to the Post correspondence problem lives.
-/

namespace Lax251941.Acceptance

/-- A machine: a partial recursive program. -/
abbrev Machine := Nat.Partrec.Code

/-- `M` accepts `w` if it halts on `w` with output `1`. -/
def Accepts (M : Machine) (w : ℕ) : Prop := M.eval w = Part.some 1

/-- `M` rejects `w` if it halts on `w` with output `0`. -/
def Rejects (M : Machine) (w : ℕ) : Prop := M.eval w = Part.some 0

/-- A machine is a decider if it accepts or rejects every input, i.e. never loops.
-/
def IsDecider (M : Machine) : Prop := ∀ w, Accepts M w ∨ Rejects M w

/-- `M` recognises the language `A` if it accepts exactly the words of `A`. -/
def Recognizes (M : Machine) (A : Set ℕ) : Prop := ∀ w, w ∈ A ↔ Accepts M w

/-- `M` decides `A` if it is a decider that recognises `A`. -/
def Decides (M : Machine) (A : Set ℕ) : Prop := IsDecider M ∧ Recognizes M A

/-- A language is Turing-recognisable if some machine recognises it. -/
def TuringRecognizable (A : Set ℕ) : Prop := ∃ M, Recognizes M A

/-- A language is decidable if some machine decides it. -/
def TuringDecidable (A : Set ℕ) : Prop := ∃ M, Decides M A

/-- The acceptance problem `A_TM`: the pairs `⟨M, w⟩`, encoded by Cantor pairing
of the code of `M` with `w`, such that `M` accepts `w`. -/
def ATM : Set ℕ := {n | Accepts (Denumerable.ofNat Machine n.unpair.1) n.unpair.2}

end Lax251941.Acceptance
