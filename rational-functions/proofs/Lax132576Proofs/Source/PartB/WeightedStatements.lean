/-
Part B: Weighted automata and machine independent characterisations
  (Sections *Rational relations and weighted automata* and *Machine independent characterisations*)
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Sections *Rational relations and weighted automata* to
*Machine independent characterisations* and the statements of their theorems, lemmas and claims.
The proofs are in the supporting files (`MealyChar.lean`, `Typing.lean`, `LenNormalForm.lean`,
`SeqChar.lean`).  Every result of these sections is proved; four of them are proved from the
effectivity hypothesis `Transducers.EffectiveWeightedEvalEq`, which is now itself proved (in
`RequestProject/PartB/WCodePrimrec.lean`), so that every result of Part B is unconditional.  No file
of Part B contains a `sorry`.

Not stated here: Claims `claim:bounded-extensions` to `claim:eliminating-negative-letters`, which
are internal steps of the proof of Theorem `thm:subsequential-functions`.  They speak about the
branching and non-branching parts of the outputs of a subsequential function, auxiliary notions used
only inside that proof; each of them is formalised there, in the `Subseq*.lean` files
(`Transducers.Subseq.delay_bound`, `Transducers.Subseq.key_drop`, `Transducers.Subseq.incr_congr`
and `Transducers.Subseq.exists_deletion_bound`), in the reorganised form recorded in
`THEOREMS.md`. -/
import Lax132576Proofs.Source.PartB.RationalStatements
import Lax132576Proofs.Source.PartB.Typing
import Lax132576Proofs.Source.PartB.SeqChar
import Lax132576Proofs.Source.PartB.LenNormalForm
import Lax132576Proofs.Source.PartB.WeightedPrecomp
import Lax132576Proofs.Source.PartB.WeightedRegular
import Lax132576Proofs.Source.PartB.SubseqChar
import Lax132576Proofs.Source.PartB.RatIndex
import Lax132576Proofs.Source.PartB.RatAnnot
import Lax132576Proofs.Source.PartB.LenDec
import Lax132576Proofs.Source.PartB.WeightedDec
import Lax132576Proofs.Source.PartB.RatEqDec
import Lax132576Proofs.Source.PartB.MealyDec
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-! ## Rational relations and weighted automata

**Definition `def:semiring` (Semiring)** is Mathlib's `Semiring`. -/

/-! **Definition `def:weighted-automaton` (Weighted automaton).**  The weight of a path
(`LabAut.weightOf`), the semantics of a weighted automaton (`LabAut.wEval`),
the requirement that every input has finitely many accepting runs
(`LabAut.FinitelyManyRuns`) and the functions computed by weighted automata
(`IsWeighted`) are defined in `RequestProject/PartB/LabAut.lean`, so that the
constructions used in the proofs below can be developed before the statements of
the numbered results. -/

/-! ### Decidable equivalence

As in Section *Undecidable equivalence*, decidability statements are formalised through computable
functions on finite descriptions (codes).  A weighted automaton over the field
of rationals is coded by a list of transitions whose weights are given by a pair
`(p, q) : ℤ × ℕ` representing the rational number `p / q`. -/

/-! The code of a weighted automaton over `ℚ` (`WCode`), the automaton that it
describes (`wcodeAut`), the function that it computes (`wcodeEval`) and the
promise that it is a genuine weighted automaton (`WCodeValid`) are defined in
`RequestProject/PartB/WCodes.lean`, so that the decision procedures used below
can be developed before the statements of the numbered results. -/

/-- **Theorem `thm:equivalence-weighted-automata`.**  Given two weighted automata over the field of
rationals, it is decidable whether they compute the same function.

The decision procedure combines Schützenberger's criterion in its effective form
(`Transducers.effectiveWeightedBound`, in `RequestProject/PartB/WeightedBound.lean`) with the
computable equality test `Transducers.EffectiveWeightedEvalEq` for the values of two coded weighted
automata over `ℚ` (proved in `RequestProject/PartB/WCodePrimrec.lean`). -/
theorem weighted_equivalence_decidable :
    DecidableUnderPromise (fun p : WCode × WCode => WCodeValid p.1 ∧ WCodeValid p.2)
      (fun p => wcodeEval p.1 = wcodeEval p.2) :=
  weighted_equivalence_decidable_aux

/-- **Theorem `thm:equivalence-rational-functions`.**  The equivalence problem `f = g` is decidable
for rational functions.

Proved by the reduction of the book to Theorem `thm:equivalence-weighted-automata`: the two coded
functions are turned into two weighted automata over `ℚ` whose values are the numerical encodings of
the outputs, multiplied by the numbers of accepting runs of the two automata, which are the same for
both. -/
theorem rationalFun_equivalence_decidable :
    DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => codeRel p.1 = codeRel p.2) :=
  rationalFun_equivalence_decidable_aux

/-- **Lemma `lem:closure-weighted-automata-precomposition`.**  Weighted automata (over any semiring)
are closed under pre-composition with rational functions. -/
theorem weighted_precomp_rational {A B S : Type} [Finite A] [Finite B] [Semiring S]
    {f : List A → List B} {h : List B → S}
    (hf : IsRationalFun f) (hh : IsWeighted h) : IsWeighted (h ∘ f) :=
  weighted_precomp_rational_aux hf hh

/-- **Theorem `thm:characterisation-rational-functions-weighted-automata`.**  A string-to-string
function is rational if and only if weighted automata are closed under pre-composition with it. -/
theorem rational_iff_weighted_precomp {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔
      ∀ (S : Type) (_ : Semiring S) (h : List B → S), IsWeighted h → IsWeighted (h ∘ f) :=
  rational_iff_weighted_precomp_aux f

/-- **Theorem `thm:zeroness-weighted-automata`.**  The zeroness problem is decidable for weighted
automata over the field of rationals.  (The same proof works for any computable field.)

Proved as the special case of Theorem `thm:equivalence-weighted-automata` in which the second
automaton is the empty one. -/
theorem weighted_zeroness_decidable :
    DecidableUnderPromise WCodeValid (fun c => wcodeEval c = 0) :=
  weighted_zeroness_decidable_aux

/-! ## Machine independent characterisations -/

/-! ### Mealy machines -/

/-- **Theorem `thm:mealy-machine-independent`.**  A function is computed by a Mealy machine if and
only if it is continuous, prefix preserving and length preserving. -/
theorem isMealy_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsMealy f ↔ (Continuous f ∧ PrefixPreserving f ∧ LengthPreserving f) :=
  isMealy_iff_aux f

/-  The original formalisation of Theorem `thm:decide-if-mealy` was

theorem rationalFun_isMealy_decidable :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ, (∀ w v, codeRel c w v ↔ v = f w) ∧ IsMealy f) := by
  sorry

It is *degenerate*: the ambient alphabet is `ℕ`, while a code has only finitely
many transitions and therefore reads only finitely many letters, so no code can
satisfy `∀ w v, codeRel c w v ↔ v = f w` for a total `f` (compare
`Transducers.not_codeTotalFunctional`).  The property inside the promise is
therefore false for every code, and the statement would be provable with the
constant procedure `fun _ => false`.  The statement below relativises both the
promise and the property to strings over the alphabet of the code. -/

/-- **Theorem `thm:decide-if-mealy`.**  One can decide if a rational function is computed by a
Mealy machine.

The relation described by the code and the Mealy machine are compared on the
strings over the alphabet of the code (`CodeWord`); see the comment above the
original statement for why the unrelativised statement is degenerate.

The proof reduces prefix preservation to the equality of two rational functions
(`RequestProject/PartB/PrefixCodes.lean`), which is decided by Theorem
`thm:equivalence-rational-functions`. -/
theorem rationalFun_isMealy_decidable :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f) :=
  rationalFun_isMealy_decidable_aux

/-- **Lemma `lem:decide-if-length-preserving`.**  One can decide if a rational function is
length-preserving.

The decision procedure (in `RequestProject/PartB/LenDec.lean`) is correct for
*every* code, so the promise that the coded relation is a function is not
needed.  It enumerates all transition sequences of length at most `3n`, where
`n` bounds the number of states of the coded automaton, and checks that the
accepting ones read and write strings of the same length; a pumping argument
shows that this bound is sufficient. -/
theorem rationalFun_lengthPreserving_decidable :
    DecidableUnderPromise CodeFunctional
      (fun c => ∀ w v, codeRel c w v → v.length = w.length) :=
  ⟨LenDec.lenDec, LenDec.computable_lenDec, fun c _ => LenDec.lenDec_iff c⟩

/-! The notion of a *productive* state (a state that appears in some accepting
run) is defined in `RequestProject/PartB/LabAut.lean`. -/

/-- **Claim `claim:typing-length-preserving`.**  For an nfa with output whose states are all
productive, the computed function is length-preserving if and only if a typing `τ : Q → ℤ` exists
(i.e. every run from an initial state to `q` satisfies `|output| = |input| + τ q`) and all accepting
states are mapped to zero. -/
theorem lengthPreserving_iff_typing {A B Q : Type} (M : NFAO A B Q)
    (hprod : ∀ q, Productive M q) {f : List A → List B} (hM : ∀ w v, M.rel w v ↔ v = f w) :
    LengthPreserving f ↔
      ∃ τ : Q → ℤ,
        (∀ q ∈ M.init, ∀ ts p, M.Path q ts p →
          ((NFAO.outputOf ts).length : ℤ) = (LabAut.inputOf ts).length + τ p) ∧
        ∀ p ∈ M.final, τ p = 0 :=
  lengthPreserving_iff_typing_aux M hprod hM

/-- **Lemma `lem:characterisation-length-preserving`.**  If a rational function is
length-preserving, then it is computed by an nfa with output in which the input and output strings
of every transition have the same length. -/
theorem lengthPreserving_rational_normal_form {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) (hlen : LengthPreserving f) :
    ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q),
      (∀ t ∈ M.δ, t.2.1.length = t.2.2.1.length) ∧ ∀ w v, M.rel w v ↔ v = f w :=
  lengthPreserving_rational_normal_form_aux hf hlen

/-! ### Sequential functions -/

/-! The definition of a sequential transducer (`Sequential`) and of the functions that they compute
(`IsSequential`) is in `RequestProject/PartB/SeqChar.lean`, together with the proof of Theorem
`thm:sequential-function-independent`. -/

/-  An earlier edition of the book stated **Theorem `thm:sequential-function-independent`** without
the condition `f [] = []`, and in that form it is *false*: a sequential transducer produces no
output before reading any input, so a sequential function satisfies `f [] = []`, while the three
remaining conditions are satisfied for instance by the function `aⁿ ↦ aⁿ⁺¹`.  The sources now list
that condition as item (c) of the theorem, so the statement below is faithful; the earlier version
is kept here, commented out, as a record.

theorem isSequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSequential f ↔
      (Continuous f ∧ PrefixPreserving f ∧
        ∃ K : ℕ, ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K) := by
  sorry
-/

/-- **Theorem `thm:sequential-function-independent`.**  A function is sequential if and only if it
maps the empty input to the empty output and it is continuous, prefix preserving, and has the
bounded increase property: the increase in output length caused by extending the input by one letter
is bounded.

The conjunct `f [] = []` is item (c) of the theorem in the book ("outputs ε when the input is
ε"); an earlier edition omitted it, and without it the statement is false, since a sequential
transducer produces no output before reading any input. -/
theorem isSequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSequential f ↔
      (f [] = [] ∧ Continuous f ∧ PrefixPreserving f ∧
        ∃ K : ℕ, ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K) :=
  isSequential_iff_aux f

/-! ### Subsequential functions -/

/-! The definition of a subsequential transducer (`Subsequential`) and of the
partial functions that they compute (`IsSubsequential`) is in
`RequestProject/PartB/SubseqDef.lean`, together with the easy implication of
Theorem `thm:subsequential-functions`; the construction proving the other implication is in
`SubseqAlpha.lean`, `SubseqState.lean`, `SubseqBound.lean` and
`SubseqChar.lean`. -/

/-- **Theorem `thm:subsequential-functions`.**  A partial function is subsequential if and only if
it is continuous and has bounded variation: for all `w₁, w₂` the left distances `‖f (w w₁), f (w
w₂)‖` are bounded, where `w` ranges over strings for which both outputs are defined. -/
theorem isSubsequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → Option (List B)) :
    IsSubsequential f ↔
      (PartialContinuous f ∧
        ∀ w₁ w₂ : List A, ∃ K : ℕ, ∀ (w : List A) (v₁ v₂ : List B),
          f (w ++ w₁) = some v₁ → f (w ++ w₂) = some v₂ → leftDist v₁ v₂ ≤ K) :=
  isSubsequential_iff_aux f

/-! ### Rational functions -/

/-! The equivalence relation `BoundedVarRel` on input strings used in Theorem
`thm:machine-independent-rational-functions` (`w₁ ∼ w₂` if the left distances `‖f (w w₁), f (w w₂)‖`
are bounded uniformly in `w`) is defined in `RequestProject/PartB/RatIndex.lean`, together with the
proof that it is an equivalence relation and a left congruence and the easy implication of the
theorem; the converse implication is proved in `RequestProject/PartB/RatAnnot.lean`. -/

/-- **Theorem `thm:machine-independent-rational-functions`.**  A function is rational if and only if
it is continuous and the equivalence relation `BoundedVarRel f` has finite index. -/
theorem isRationalFun_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsRationalFun f ↔
      (Continuous f ∧
        {C : Set (List A) | ∃ w₁, C = {w₂ | BoundedVarRel f w₁ w₂}}.Finite) :=
  isRationalFun_iff_aux f

end Lax132576Proofs.Transducers
