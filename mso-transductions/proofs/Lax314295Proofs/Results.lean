import Lax314295.RegularOfMSODefinable
import Lax314295.MSODefinableOfRegular
import Lax314295.BuchiTheorem
import Lax314295.MSOFreeVariables
import Lax314295.RationalOfRelabelling
import Lax314295.RelabellingOfRational
import Lax314295.RationalIffRelabelling
import Lax314295.MSOAnnotationRegular
import Lax314295.RegularOfMSOTransduction
import Lax314295.MSOTransductionOfRegular
import Lax314295.MSOTransductionIffRegular
import Lax314295.LogicPrecomputation
import Lax314295.AperiodicOfFO
import Lax314295.FOOfAperiodic
import Lax314295.FOIffAperiodic
import Lax314295.KTypesFOEquivalence
import Lax314295.KTypesRefinement
import Lax314295.KTypesCongruence
import Lax314295.KTypesAperiodicity
import Lax314295.AperiodicBimachineOfFORelabelling
import Lax314295.FORelabellingOfAperiodicBimachine
import Lax314295.FORelabellingIffAperiodicBimachine
import Lax314295Proofs.Bridge

/-!
The numbered results of Part C §4 of *Transducers*, transported from the
ported source development through `Lax314295Proofs.Bridge` (and the bridges
of Parts A, B and C §1–3 for the notions of those parts).
-/

namespace Lax314295Proofs.Results

open Lax765601Proofs Lax132576Proofs Lax916827Proofs
open Lax765601.StateTransformations Lax765601.ElementaryProperties Lax765601.Aperiodicity
open Lax132576.RationalFunctions Lax132576.Bimachines
open Lax916827.RegularFunctions
open Lax314295.MSOLogic Lax314295.MSORelabellings Lax314295.MSOTransductions Lax314295.KTypes
open Lax314295Proofs.Bridge

/-! ## Monadic second-order logic -/

/--
---
conclusion: Lax314295.RegularOfMSODefinable.isRegular_of_msoDefinable
---
An mso-definable language is regular (Theorem C.4.1, Büchi's theorem, the easy
implication): the automaton of a sentence, by induction on the formula
(`Transducers.regular_iff_msoDefinable`, right to left).

# Proof strategy

The source builds, for every formula, the automaton of the annotated strings that
satisfy it (Lemma C.4.2, `PartC/MSOAnnot.lean`) and projects the annotation
away for a sentence (`PartC/MSOBuchi.lean`). The concept's formulas are the
source's through the bijection `toSrc`/`ofSrc`, along which satisfaction is
transported (`sat_toSrc`), so `MSODefinable` transfers by `msoDefinable_iff`.

# Attribution

Theorem C.4.1 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/MSOBuchi.lean`, `PartC/MSO.lean`.
-/
theorem isRegular_of_msoDefinable {A : Type} [Finite A] {L : Language A}
    (hL : MSODefinable L) : L.IsRegular :=
  (Transducers.regular_iff_msoDefinable L).2 ((msoDefinable_iff L).1 hL)

/--
---
conclusion: Lax314295.MSODefinableOfRegular.msoDefinable_of_isRegular
---
A regular language is mso-definable (Theorem C.4.1, Büchi's theorem, the
converse implication): the sentence guessing an accepting run of a dfa as a
tuple of sets of positions (`Transducers.regular_iff_msoDefinable`, left to
right).

# Proof strategy

The source writes down the sentence "there are sets `X_q`, one per state,
partitioning the positions, consistent with the transition function at every
step and accepting at the end" (`PartC/MSOBuchi.lean`); the bridge transports
`MSODefinable` along `ofSrc` (`msoDefinable_iff`).

# Attribution

Theorem C.4.1 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/MSOBuchi.lean`, `PartC/MSO.lean`.
-/
theorem msoDefinable_of_isRegular {A : Type} [Finite A] {L : Language A} (hL : L.IsRegular) :
    MSODefinable L :=
  (msoDefinable_iff L).2 ((Transducers.regular_iff_msoDefinable L).1 hL)

/--
---
conclusion: Lax314295.BuchiTheorem.isRegular_iff_msoDefinable
---
Büchi's theorem (Theorem C.4.1) as a biconditional, glued from its two halves
taken as assumptions.
-/
theorem isRegular_iff_msoDefinable {A : Type} [Finite A] (L : Language A) :
    L.IsRegular ↔ MSODefinable L :=
  ⟨Lax314295.MSODefinableOfRegular.msoDefinable_of_isRegular,
    Lax314295.RegularOfMSODefinable.isRegular_of_msoDefinable⟩

/--
---
conclusion: Lax314295.MSOFreeVariables.isRegular_annotated
---
The annotated strings satisfying a formula with free variables form a regular
language (Lemma C.4.2): induction on the formula, with projection for the
quantifiers (`Transducers.mso_annotated_regular`).

# Proof strategy

The concept's `annotate`, `extFO` and `extSO` are the source's by `rfl`; the
formula is transported along `toSrc`, which preserves the free variables
(`freeFO_toSrc`, `freeSO_toSrc`) and satisfaction (`sat_toSrc`), so the two
languages are equal by extensionality.

# Attribution

Lemma C.4.2 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/MSOAnnot.lean`, `PartC/MSO.lean`.
-/
theorem isRegular_annotated {A : Type} [Finite A] (φ : MSO A) (k l : ℕ)
    (hfo : φ.freeFO ⊆ {i | i < k}) (hso : φ.freeSO ⊆ {j | j < l}) :
    Language.IsRegular
      {u : List (A × (Fin k → Bool) × (Fin l → Bool)) |
        ∃ (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate k l w fo so ∧ MSO.Sat w (extFO k fo) (extSO l so) φ} := by
  have h := Transducers.mso_annotated_regular (toSrc φ) k l
    (by rw [freeFO_toSrc]; exact hfo) (by rw [freeSO_toSrc]; exact hso)
  simpa only [annotate_eq, extFO_eq, extSO_eq, sat_toSrc] using h

/-! ## Rational functions in terms of logic -/

/--
---
conclusion: Lax314295.RationalOfRelabelling.isRationalFun_of_isMSORelabelling
---
A function defined by an mso relabelling is rational (Theorem C.4.4, the easy
implication): a bimachine reading, at every position, the answers of the
formulas (`Transducers.rational_iff_msoRelabelling`, right to left).

# Proof strategy

The source evaluates the formulas of the relabelling by the automata of
Lemma C.4.2 run from both ends (`PartC/MarkBimach.lean`, `PartC/MSORatRelab.lean`)
and concludes by Theorem B.2.3 on bimachines. The concept's relabelling is the
source's through `toSrcRel` with its graph `Relabels` (`isMSORelabelling_iff`);
rational functions come from Part B's bridge.

# Attribution

Theorem C.4.4 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/MSORatRelab.lean`, `PartC/MSO.lean`.
-/
theorem isRationalFun_of_isMSORelabelling {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMSORelabelling f) : IsRationalFun f :=
  (Lax132576Proofs.Bridge.isRationalFun_iff f).2
    ((Transducers.rational_iff_msoRelabelling f).2 ((isMSORelabelling_iff f).1 hf))

/--
---
conclusion: Lax314295.RelabellingOfRational.isMSORelabelling_of_isRationalFun
---
A rational function is defined by an mso relabelling (Theorem C.4.4, the
converse implication): the transition formulas of a bimachine
(`Transducers.rational_iff_msoRelabelling`, left to right).

# Proof strategy

The source takes a bimachine for `f` (Theorem B.2.3) and writes, for every pair
of a left and a right state, the formula "the left automaton reaches this
state before `x` and the right automaton that state after `x`" (Claim C.4.5,
`Transducers.RatRelab.exists_form`); these formulas form a relabelling
computing `f`. The bridge transports the relabelling along `ofSrcRel`.

# Attribution

Theorem C.4.4 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/MSORatRelab.lean`, `PartC/MarkLogic.lean`, `PartC/MSO.lean`.
-/
theorem isMSORelabelling_of_isRationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) : IsMSORelabelling f :=
  (isMSORelabelling_iff f).2
    ((Transducers.rational_iff_msoRelabelling f).1 ((Lax132576Proofs.Bridge.isRationalFun_iff f).1 hf))

/--
---
conclusion: Lax314295.RationalIffRelabelling.isRationalFun_iff_isMSORelabelling
---
Theorem C.4.4 as a biconditional, glued from its two halves taken as
assumptions.
-/
theorem isRationalFun_iff_isMSORelabelling {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRationalFun f ↔ IsMSORelabelling f :=
  ⟨Lax314295.RelabellingOfRational.isMSORelabelling_of_isRationalFun,
    Lax314295.RationalOfRelabelling.isRationalFun_of_isMSORelabelling⟩

/--
---
conclusion: Lax314295.MSOAnnotationRegular.isRegular_annotation
---
For an mso relabelling, the strings annotated at every position with a formula
true there form a regular language (Claim C.4.6): the intersection, over the
formulas, of the complements of the languages "some position carries a formula
that fails there", each regular by Lemma C.4.2
(`Transducers.msoRelabelling_annotation_regular`).

# Proof strategy

The concept's relabelling `R` is sent to `toSrcRel R`, whose index type is
`R.Idx` and whose formulas are `toSrc (R.form i)`; the two languages are equal
by extensionality and `sat_toSrc`.

# Attribution

Claim C.4.6 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/MSORelab.lean`, `PartC/MSO.lean`.
-/
theorem isRegular_annotation {A B : Type} [Finite A] (R : MSORelabelling A B) :
    Language.IsRegular
      {u : List (A × R.Idx) | ∀ (p : ℕ) (hp : p < u.length),
        MSO.Sat (u.map Prod.fst) (fun _ => p) (fun _ => ∅) (R.form (u.get ⟨p, hp⟩).2)} := by
  have h := Transducers.msoRelabelling_annotation_regular (toSrcRel R)
  simpa only [toSrcRel_form, sat_toSrc] using h

/-! ## Regular functions in terms of logic -/

/--
---
conclusion: Lax314295.RegularOfMSOTransduction.isRegularFun_of_isMSOTransduction
---
A function defined by an mso transduction is regular (Theorem C.4.8, the hard
implication): a two-way transducer walking the output order
(`Transducers.msoTransduction_iff_regular`, left to right).

# Proof strategy

The source normalises the type of the transduction to `k · n` (Lemma C.4.9,
`PartC/MSONorm.lean`), precomputes the answers of the universe, letter and order
formulas by a letter-to-letter rational function (Lemma C.4.10,
`PartC/MSOPrecomp.lean`), and builds a two-way transducer that visits the
selected elements in the order of the order formula, reading the precomputed
answers (`PartC/WalkAut.lean`, `PartC/MSOWalk*.lean`, `PartC/MSOReg.lean`);
the composition is regular by Theorem C.2.9. The concept's transduction is the
source's through `toSrcT`, with `Proper` and `Outputs` transported
(`isMSOTransduction_iff`); regular functions come from Part C §1–3's bridge.

# Attribution

Theorem C.4.8 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/MSOReg.lean`, `PartC/MSO.lean`.
-/
theorem isRegularFun_of_isMSOTransduction {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMSOTransduction f) : IsRegularFun f :=
  (Lax916827Proofs.Bridge.isRegularFun_iff f).2
    ((Transducers.msoTransduction_iff_regular f).1 ((isMSOTransduction_iff f).1 hf))

/--
---
conclusion: Lax314295.MSOTransductionOfRegular.isMSOTransduction_of_isRegularFun
---
A regular function is defined by an mso transduction (Theorem C.4.8, the
converse implication): the formulas describing the run of a two-way transducer
(`Transducers.msoTransduction_iff_regular`, right to left).

# Proof strategy

The source takes a two-way transducer for `f` (Theorem C.2.9) and, with one
copy of the positions per state and direction, writes mso formulas saying that
a configuration is visited by the run, which letter it outputs and which of two
visited configurations comes first — the runs being described in mso through
Büchi's theorem (`PartC/TwoWayMSO.lean`). The bridge transports the transduction
along `ofSrcT`.

# Attribution

Theorem C.4.8 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/TwoWayMSO.lean`, `PartC/MSO.lean`.
-/
theorem isMSOTransduction_of_isRegularFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRegularFun f) : IsMSOTransduction f :=
  (isMSOTransduction_iff f).2
    ((Transducers.msoTransduction_iff_regular f).2 ((Lax916827Proofs.Bridge.isRegularFun_iff f).1 hf))

/--
---
conclusion: Lax314295.MSOTransductionIffRegular.isMSOTransduction_iff_isRegularFun
---
Theorem C.4.8 as a biconditional, glued from its two halves taken as
assumptions.
-/
theorem isMSOTransduction_iff_isRegularFun {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsMSOTransduction f ↔ IsRegularFun f :=
  ⟨Lax314295.RegularOfMSOTransduction.isRegularFun_of_isMSOTransduction,
    Lax314295.MSOTransductionOfRegular.isMSOTransduction_of_isRegularFun⟩

/--
---
conclusion: Lax314295.LogicPrecomputation.exists_rational_precomputation
---
The answers of finitely many mso formulas with one or two free variables are
read off a letter-to-letter rational function (Lemma C.4.10): a product of
the automata of Lemma C.4.2 run from both ends, as a bimachine
(`Transducers.mso_formulas_via_rational`).

# Proof strategy

The source's statement is about finite sets of source formulas; the concept's
sets `Φ₁`, `Φ₂` are sent to their images under `toSrc`, finite by
`Set.Finite.image`, and the answers are transported back along `sat_toSrc`.
Rational functions come from Part B's bridge; `LengthPreserving` unfolds
identically.

# Attribution

Lemma C.4.10 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/MSOPrecomp.lean`, `PartC/MarkBimach.lean`, `PartC/MSO.lean`.
-/
theorem exists_rational_precomputation {A : Type} [Finite A]
    (Φ₁ Φ₂ : Set (MSO A)) (hΦ₁ : Φ₁.Finite) (hΦ₂ : Φ₂.Finite) :
    ∃ (C : Type) (_ : Finite C) (f : List A → List C),
      IsRationalFun f ∧ LengthPreserving f ∧
      (∀ φ ∈ Φ₁, ∃ F : Set C, ∀ (w : List A) (x : ℕ), x < w.length →
        (MSO.Sat w (fun _ => x) (fun _ => ∅) φ ↔ ∃ c ∈ F, (f w)[x]? = some c)) ∧
      (∀ φ ∈ Φ₂, ∃ L : Language C, L.IsRegular ∧ ∀ (w : List A) (x y : ℕ),
        x ≤ y → y < w.length →
        (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅) φ ↔
          ((f w).drop x).take (y - x + 1) ∈ L)) := by
  obtain ⟨C, hC, f, hf, hlen, h₁, h₂⟩ :=
    Transducers.mso_formulas_via_rational (toSrc '' Φ₁) (toSrc '' Φ₂) (hΦ₁.image _) (hΦ₂.image _)
  refine ⟨C, hC, f, (Lax132576Proofs.Bridge.isRationalFun_iff f).2 hf, hlen, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨F, hF⟩ := h₁ (toSrc φ) ⟨φ, hφ, rfl⟩
    exact ⟨F, fun w x hx => (sat_toSrc w φ _ _).trans (hF w x hx)⟩
  · intro φ hφ
    obtain ⟨L, hL, hLφ⟩ := h₂ (toSrc φ) ⟨φ, hφ, rfl⟩
    exact ⟨L, hL, fun w x y hxy hy => (sat_toSrc w φ _ _).trans (hLφ w x y hxy hy)⟩

/-! ## The first-order fragment -/

/--
---
conclusion: Lax314295.AperiodicOfFO.exists_aperiodic_dfa_of_foDefinable
---
A first-order definable language is recognised by an aperiodic dfa
(Theorem C.4.11, the first implication): the automaton of `k`-types
(`Transducers.foDefinable_iff_aperiodic_dfa`, left to right).

# Proof strategy

The source takes a first-order sentence of quantifier rank `k` defining `L`,
recognises `L` by the dfa whose states are the `k`-types (Lemma C.4.13 says
the type determines satisfaction, Lemma C.4.15 that the types form an
aperiodic congruence, `PartC/FOTypeDFA.lean`). The bridge transports
`FODefinable` along `toSrc`; `TransAperiodic` unfolds identically.

# Attribution

Theorem C.4.11 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/FOTypeDFA.lean`, `PartC/FOComp.lean`, `PartC/MSO.lean`.
-/
theorem exists_aperiodic_dfa_of_foDefinable {A : Type} [Finite A] {L : Language A}
    (hL : FODefinable L) :
    ∃ (σ : Type) (_ : Finite σ) (M : DFA A σ), TransAperiodic M.step ∧ M.accepts = L := by
  obtain ⟨σ, hσ, M, hM, hL'⟩ :=
    (Transducers.foDefinable_iff_aperiodic_dfa L).1 ((foDefinable_iff L).1 hL)
  exact ⟨σ, hσ, M, (transAperiodic_iff M.step).2 hM, hL'⟩

/--
---
conclusion: Lax314295.FOOfAperiodic.foDefinable_of_aperiodic_dfa
---
The language of an aperiodic dfa is first-order definable (Theorem C.4.11, the
converse implication): the aperiodic Krohn–Rhodes decomposition into flip-flops
(`Transducers.foDefinable_iff_aperiodic_dfa`, right to left).

# Proof strategy

The source turns the dfa into an aperiodic Mealy machine, decomposes it by
Theorem A.2.13 into flip-flops and letter-to-letter maps, describes each prime
in first-order logic and composes the descriptions by substitution of formulas
(`PartC/FOFlipFlop.lean`, `PartC/FOMealy.lean`). The bridge transports
`FODefinable` along `ofSrc`.

# Attribution

Theorem C.4.11 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/FOMealy.lean`, `PartC/FOFlipFlop.lean`, `PartC/MSO.lean`.
-/
theorem foDefinable_of_aperiodic_dfa {A σ : Type} [Finite A] [Finite σ] (M : DFA A σ)
    (hM : TransAperiodic M.step) : FODefinable M.accepts :=
  (foDefinable_iff _).2 ((Transducers.foDefinable_iff_aperiodic_dfa M.accepts).2
    ⟨σ, inferInstance, M, (transAperiodic_iff M.step).1 hM, rfl⟩)

/--
---
conclusion: Lax314295.FOIffAperiodic.foDefinable_iff_aperiodic_dfa
---
Theorem C.4.11 as a biconditional, glued from its two halves taken as
assumptions.
-/
theorem foDefinable_iff_aperiodic_dfa {A : Type} [Finite A] (L : Language A) :
    FODefinable L ↔
      ∃ (σ : Type) (_ : Finite σ) (M : DFA A σ), TransAperiodic M.step ∧ M.accepts = L := by
  refine ⟨Lax314295.AperiodicOfFO.exists_aperiodic_dfa_of_foDefinable, ?_⟩
  rintro ⟨σ, hσ, M, hM, rfl⟩
  exact Lax314295.FOOfAperiodic.foDefinable_of_aperiodic_dfa M hM

/--
---
conclusion: Lax314295.KTypesFOEquivalence.tp_eq_iff_fo_equiv
---
Two strings have the same `k`-type if and only if they satisfy the same
first-order sentences of quantifier rank at most `k` (Lemma C.4.13):
compositionality of first-order logic for the direction from types to
sentences, and Hintikka sentences describing the `k`-type for the converse
(`Transducers.tp_eq_iff_fo_equiv`).

# Proof strategy

The concept's `k`-types are the source's through the bijection `tpEquiv`
(`tp_eq_iff`); the quantification over concept sentences is turned into one
over source sentences along `toSrc`/`ofSrc`, which preserve the first-order
fragment, the free variables, the quantifier rank and satisfaction.

# Attribution

Lemma C.4.13 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/FOComp.lean`, `PartC/FOHintikka.lean`, `PartC/MSO.lean`.
-/
theorem tp_eq_iff_fo_equiv {A : Type} [Finite A] (k : ℕ) (w v : List A) :
    tp k w = tp k v ↔
      ∀ φ : MSO A, φ.IsFO → φ.freeFO = ∅ → φ.qrank ≤ k →
        ((∀ fo so, MSO.Sat w fo so φ) ↔ (∀ fo so, MSO.Sat v fo so φ)) := by
  rw [tp_eq_iff, Transducers.tp_eq_iff_fo_equiv]
  constructor
  · intro h φ hfo hfree hq
    have := h (toSrc φ) ((isFO_toSrc φ).2 hfo) (by rw [freeFO_toSrc]; exact hfree)
      (by rw [qrank_toSrc]; exact hq)
    simpa only [sat_toSrc] using this
  · intro h φ hfo hfree hq
    have := h (ofSrc φ) ((isFO_ofSrc φ).2 hfo) (by rw [freeFO_ofSrc]; exact hfree)
      (by rw [qrank_ofSrc]; exact hq)
    simpa only [sat_ofSrc] using this

/--
---
conclusion: Lax314295.KTypesRefinement.tp_eq_of_tp_succ_eq
---
Equal `(k+1)`-types have equal `k`-types (Lemma C.4.15, refinement): induction
on `k` (`Transducers.tp_properties`, first conjunct).

# Attribution

Lemma C.4.15 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/KTypes.lean`, `PartC/MSO.lean`.
-/
theorem tp_eq_of_tp_succ_eq {A : Type} (k : ℕ) (w v : List A) (h : tp (k + 1) w = tp (k + 1) v) :
    tp k w = tp k v :=
  (tp_eq_iff k w v).2 ((Transducers.tp_properties k).1 w v ((tp_eq_iff (k + 1) w v).1 h))

/--
---
conclusion: Lax314295.KTypesCongruence.tp_append_congr
---
The `k`-type of a concatenation is determined by the `k`-types of the parts
(Lemma C.4.15, congruence): induction on `k`, a factorisation of `w ++ v`
around a letter being a factorisation of `w` or of `v`
(`Transducers.tp_properties`, second conjunct).

# Attribution

Lemma C.4.15 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/KTypes.lean`, `PartC/MSO.lean`.
-/
theorem tp_append_congr {A : Type} (k : ℕ) (w w' v v' : List A)
    (hw : tp k w = tp k w') (hv : tp k v = tp k v') : tp k (w ++ v) = tp k (w' ++ v') :=
  (tp_eq_iff k _ _).2 ((Transducers.tp_properties k).2.1 w w' v v'
    ((tp_eq_iff k w w').1 hw) ((tp_eq_iff k v v').1 hv))

/--
---
conclusion: Lax314295.KTypesAperiodicity.exists_tp_npow_eq
---
The `k`-types of the powers of a string eventually stabilise (Lemma C.4.15,
aperiodicity): an explicit bound `tpBound k` from which on the `k`-types of
`wⁿ` are constant (`Transducers.tp_properties`, third conjunct).

# Proof strategy

Part A's bridge identifies the concept's `npow` with the source's
(`Lax765601Proofs.Bridge.npow_eq`), and `tp_eq_iff` transports the equality of
`k`-types.

# Attribution

Lemma C.4.15 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/KTypes.lean`, `PartC/MSO.lean`.
-/
theorem exists_tp_npow_eq {A : Type} (k : ℕ) (w : List A) :
    ∃ N : ℕ, ∀ n ≥ N, tp k (npow w n) = tp k (npow w N) := by
  obtain ⟨N, hN⟩ := (Transducers.tp_properties k).2.2 w
  refine ⟨N, fun n hn => (tp_eq_iff k _ _).2 ?_⟩
  rw [Lax765601Proofs.Bridge.npow_eq, Lax765601Proofs.Bridge.npow_eq]
  exact hN n hn

/-! ## First-order relabellings and aperiodic bimachines -/

/--
---
conclusion: Lax314295.AperiodicBimachineOfFORelabelling.isAperiodicBimachine_of_isFORelabelling
---
A first-order relabelling is computed by an aperiodic bimachine (Theorem C.4.16,
the first implication): aperiodic automata for the formulas run from both ends
(`Transducers.foRelabelling_iff_aperiodicBimachine`, left to right).

# Proof strategy

The source turns every formula of the relabelling, with its free variable
replaced by a marked position, into a first-order sentence, recognises it by an
aperiodic dfa (Theorem C.4.11) and by its reverse, and assembles the products
into a bimachine whose left and right automata are aperiodic
(`PartC/FORev.lean`, `PartC/FOPos.lean`, `PartC/FORelabBimach.lean`). The bridge
transports the relabelling along `toSrcRel` with `AllFO`; aperiodic bimachines
come from Part B's bridge.

# Attribution

Theorem C.4.16 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/FORelabBimach.lean`, `PartC/MSO.lean`.
-/
theorem isAperiodicBimachine_of_isFORelabelling {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsFORelabelling f) : IsAperiodicBimachine f :=
  (Lax132576Proofs.Bridge.isAperiodicBimachine_iff f).2
    ((Transducers.foRelabelling_iff_aperiodicBimachine f).1 ((isFORelabelling_iff f).1 hf))

/--
---
conclusion: Lax314295.FORelabellingOfAperiodicBimachine.isFORelabelling_of_isAperiodicBimachine
---
A function computed by an aperiodic bimachine is a first-order relabelling
(Theorem C.4.16, the converse implication): the runs of an aperiodic automaton
are first-order describable (`Transducers.foRelabelling_iff_aperiodicBimachine`,
right to left).

# Proof strategy

The source describes, by Theorem C.4.11 relativised to the positions before
and after `x`, the states of the left and right automata of the bimachine at
`x` in first-order logic; the formulas "left state `p`, letter `a`, right state
`s` at `x`" form a first-order relabelling computing `f`
(`PartC/FOBimachRelab.lean`). The bridge transports the relabelling along
`ofSrcRel`.

# Attribution

Theorem C.4.16 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/FOBimachRelab.lean`, `PartC/MSO.lean`.
-/
theorem isFORelabelling_of_isAperiodicBimachine {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsAperiodicBimachine f) : IsFORelabelling f :=
  (isFORelabelling_iff f).2 ((Transducers.foRelabelling_iff_aperiodicBimachine f).2
    ((Lax132576Proofs.Bridge.isAperiodicBimachine_iff f).1 hf))

/--
---
conclusion: Lax314295.FORelabellingIffAperiodicBimachine.isFORelabelling_iff_isAperiodicBimachine
---
Theorem C.4.16 as a biconditional, glued from its two halves taken as
assumptions.
-/
theorem isFORelabelling_iff_isAperiodicBimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsFORelabelling f ↔ IsAperiodicBimachine f :=
  ⟨Lax314295.AperiodicBimachineOfFORelabelling.isAperiodicBimachine_of_isFORelabelling,
    Lax314295.FORelabellingOfAperiodicBimachine.isFORelabelling_of_isAperiodicBimachine⟩

end Lax314295Proofs.Results
