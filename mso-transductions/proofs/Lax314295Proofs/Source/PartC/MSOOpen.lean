/-
Part C, Section *Logic*: Logic
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file used to hold the numbered results of Section *Logic* whose proofs were
still left as `sorry`, so that `RequestProject/PartC/MSO.lean`, which collects
the results of Section *Logic* that *are* proved, contains no `sorry`.

The last such result was Theorem `nolabel:thm-fo-transduction-into-primes`, which **has been removed
from the formalised theorems at the user's request**; its statement is kept below, only as a
comment, and no longer exists as a Lean declaration.  Nothing in Section *Logic* is left unproved:
the file now contains no declaration at all, and is kept only for the pointers below.
`RequestProject/PartC/MSO.lean` imports this file, so all remaining names are unchanged and are
still available to anything importing `RequestProject.PartC.MSO`.

Theorem `thm:logic-rational-functions`, Lemma `lem:logic-precomputation`, Theorem
`thm:logic-regular-functions`, Theorem `thm:logic-aperiodic` and Lemma
`lem:k-types-fo-equivalence` used to be stated here as well; they are now proved, and
their statements have moved back to `RequestProject/PartC/MSO.lean`.

Not stated as numbered results: Claim `claim:transition-formula`, Lemma
`lem:logic-reduction-to-type-n` and Claim `claim:fo-composition-quantifier-rank`, which are internal
steps of the proofs of Theorems `thm:logic-rational-functions`, `thm:logic-regular-functions` and
Lemma `lem:k-types-fo-equivalence`.  All three are formalised inside those proofs, as
`Transducers.RatRelab.exists_form`, `Transducers.MSOTransduction.exists_norm` and
`Transducers.sat_iff_of_kEquiv`. -/
import Lax314295Proofs.Source.PartC.FOTransPrimeComp
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

/-! ## Rational functions in terms of logic -/

/-! Theorem `thm:logic-rational-functions` (`rational_iff_msoRelabelling`) is now proved; it lives
in `RequestProject/PartC/MSO.lean`, with its proof in `RequestProject/PartC/MSORatRelab.lean`. -/

/-! Lemma `lem:logic-precomputation` (`mso_formulas_via_rational`) is now proved; it lives in
`RequestProject/PartC/MSO.lean`, with its proof in
`RequestProject/PartC/MSOPrecomp.lean`. -/

/-! ## Regular functions in terms of logic -/

/-! Theorem `thm:logic-regular-functions` (`msoTransduction_iff_regular`) is now proved; it lives in
`RequestProject/PartC/MSO.lean`, with its proof in
`RequestProject/PartC/MSOReg.lean` (from mso transductions to regular functions)
and `RequestProject/PartC/TwoWayMSO.lean` (the converse). -/

/-! ## The first-order fragment -/

/-! Theorem `thm:logic-aperiodic` (`foDefinable_iff_aperiodic_dfa`) and Lemma
`lem:k-types-fo-equivalence` (`tp_eq_iff_fo_equiv`) are now proved; they live in
`RequestProject/PartC/MSO.lean`, with their proofs in `RequestProject/PartC/FOComp.lean` and
`RequestProject/PartC/FOHintikka.lean` (Lemma `lem:k-types-fo-equivalence`) and in
`RequestProject/PartC/FOTypeDFA.lean` and `RequestProject/PartC/FOMealy.lean` (Theorem
`thm:logic-aperiodic`). -/

/-! Theorem `thm:fo-rational-functions` (`foRelabelling_iff_aperiodicBimachine`) is now proved; it
lives in `RequestProject/PartC/MSO.lean`, with its proof in
`RequestProject/PartC/FORelabBimach.lean` (from first-order relabellings to
aperiodic bimachines) and `RequestProject/PartC/FOBimachRelab.lean` (the
converse). -/

/-! The family `Transducers.FORegularFam` of prime first-order regular
functions used to be defined here; it has moved to
`RequestProject/PartC/FOPrimeFam.lean`, which this file imports.  Its easy
inclusion into the first-order transductions is proved, independently of
anything below, in `RequestProject/PartC/FOTransPrimeComp.lean`
(`Transducers.isFOTransduction_of_compClosure`). -/

/-!
### Theorem `nolabel:thm-fo-transduction-into-primes` has been removed from the formalised theorems

At the user's request, Theorem `nolabel:thm-fo-transduction-into-primes` and its open half are no
longer part of this formalisation.  They are kept here, commented out, for the record only. The book
itself states Theorem `nolabel:thm-fo-transduction-into-primes` without a proof (it leaves the proof
for a future edition of the notes), and the direction from first-order transductions to compositions
of primes was the only `sorry` of Section *Logic*.  The inclusion that *is* proved survives
untouched as `Transducers.isFOTransduction_of_compClosure` in
`RequestProject/PartC/FOTransPrimeComp.lean`. -/

/- /-- **The open half of Theorem `nolabel:thm-fo-transduction-into-primes`.**  Every first-order
transduction is a composition of first-order relabellings, map reverse and map duplicate.

**Still open in this formalisation**, and the only part of Theorem
`nolabel:thm-fo-transduction-into-primes` that is.  The book states Theorem
`nolabel:thm-fo-transduction-into-primes` without a proof (it leaves the proof for a future edition
of the notes), and sketches what this direction would need: first-order variants of (1) the lemma
saying that a string representation of the configuration graph of a two-way transducer can be
computed, and (2) the main step in the decomposition of two-way transducers into primes, saying that
the output string can be read off the configuration graph by a composition of primes -- the second
one being, in the words of the book, more technical.  In this project those two ingredients are the
contents of the many files behind Theorem `thm:logic-regular-functions`, and their aperiodic
counterparts are not available. -/
theorem compClosure_of_isFOTransduction {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsFOTransduction f) : CompClosure FORegularFam A B f := by
  sorry
-/

/- /-- **Theorem `nolabel:thm-fo-transduction-into-primes`.**  A string-to-string function is a
first-order transduction if and only if it can be obtained by composing map reverse, map duplicate
and first-order rational functions.

**Still open in this formalisation.**  The book states this theorem without a proof (it leaves the
proof for a future edition of the notes), and sketches what the proof would need: first-order
variants of (1) the lemma saying that a string representation of the configuration graph of a
two-way transducer can be computed, and (2) the main step in the decomposition of two-way
transducers into primes, saying that the output string can be read off the configuration graph by a
composition of primes -- the second one being, in the words of the book, more technical.  In this
project those two ingredients are the contents of the many files behind Theorem
`thm:logic-regular-functions`, and their aperiodic counterparts are not available. The easy
inclusion (from compositions of primes to first-order transductions) additionally needs closure of
first-order transductions under composition, which in the mso case is obtained *through* Theorem
`thm:logic-regular-functions` and so does not transfer directly either; it is proved here by
substituting formulas, in `RequestProject/PartC/FOTransTr.lean` and
`RequestProject/PartC/FOTransComp.lean`.

**Status.**  The inclusion from right to left (compositions of primes are
first-order transductions) is proved, in
`RequestProject/PartC/FOTransPrimeComp.lean`.  The inclusion from left to right
is the still open `Transducers.compClosure_of_isFOTransduction` above. -/
theorem foTransduction_iff_prime_composition {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsFOTransduction f ↔ CompClosure FORegularFam A B f :=
  ⟨compClosure_of_isFOTransduction, isFOTransduction_of_compClosure⟩
-/

end Lax314295Proofs.Transducers
