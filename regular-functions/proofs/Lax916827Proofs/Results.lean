import Lax916827.RegularContinuity
import Lax916827.RegularComposition
import Lax916827.ReversalContinuous
import Lax916827.DuplicationContinuous
import Lax916827.MapLiftingContinuity
import Lax916827.RegularEquivalenceDecidable
import Lax916827.TwoWayContinuity
import Lax916827.ConfigurationGraphRational
import Lax916827.ConfigurationGraphOutput
import Lax916827.TwoWayComposition
import Lax916827.TwoWayMealyPrecomposition
import Lax916827.TwoWayRationalPrecomposition
import Lax916827.TwoWayOfRegular
import Lax916827.RegularOfTwoWay
import Lax916827.TwoWayIffRegular
import Lax916827.RegularMapLifting
import Lax916827.RegularConcatenation
import Lax916827.RegularConditional
import Lax916827.RegularSum
import Lax916827.SnakeLemma
import Lax916827.SSTOfRegular
import Lax916827.RegularOfSST
import Lax916827.SSTIffRegular
import Lax916827Proofs.Bridge

/-!
The numbered results of Part C §1–3 of *Transducers*, transported from the
ported source development through `Lax916827Proofs.Bridge` (and the bridges
of Parts A and B for the notions of those parts).
-/

namespace Lax916827Proofs.Results

open Lax765601Proofs Lax132576Proofs
open Lax765601.Continuity Lax765601.MapLifting Lax765601.CompositionClosure
  Lax765601.MealyMachine
open Lax132576.RationalFunctions Lax132576.TransducerCodes
open Lax916827.RegularFunctions Lax916827.TwoWayTransducers Lax916827.ConfigurationGraphs
  Lax916827.TwoWayCodes Lax916827.StreamingStringTransducers Lax916827.SnakeGraphs
open Lax916827Proofs.Bridge

/-! ## The prime regular functions -/

/--
---
conclusion: Lax916827.RegularContinuity.continuous_of_isRegularFun
---
Regular functions are continuous (Theorem C.1.1, the continuity half):
induction on the composition tree, with Theorem B.1.5 for the rational primes
and Lemmas C.1.2–C.1.3 for map reverse and map duplicate
(`Transducers.regular_continuous`).

# Proof strategy

The concept's `IsRegularFun` is the source's through `isRegularFun_iff` (Part
A's `compClosure_iff` on the family, Part B's `isRationalFun_iff` and the map
lifting bridge for the primes); `Continuous` unfolds identically.

# Attribution

Theorem C.1.1 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/Statements.lean`, `PartC/ContAux.lean`.
-/
theorem continuous_of_isRegularFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : Continuous f :=
  Transducers.regular_continuous ((isRegularFun_iff f).1 hf)

/--
---
conclusion: Lax916827.RegularComposition.isRegularFun_comp
---
Regular functions are closed under composition (Theorem C.1.1, the composition
half): the composition rule of the closure (`Transducers.regular_comp`).

# Attribution

Theorem C.1.1 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/Statements.lean`.
-/
theorem isRegularFun_comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C}
    (hf : IsRegularFun f) (hg : IsRegularFun g) : IsRegularFun (g ∘ f) :=
  (isRegularFun_iff _).2 (Transducers.regular_comp ((isRegularFun_iff f).1 hf) ((isRegularFun_iff g).1 hg))

/--
---
conclusion: Lax916827.ReversalContinuous.continuous_reverse
---
String reversal is continuous (Lemma C.1.2, first half): the reversed
automaton (`Transducers.reverse_duplicate_continuous`, first conjunct).

# Attribution

Lemma C.1.2 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/ContAux.lean`.
-/
theorem continuous_reverse {A : Type} [Finite A] : Continuous (List.reverse : List A → List A) :=
  (Transducers.reverse_duplicate_continuous (A := A)).1

/--
---
conclusion: Lax916827.DuplicationContinuous.continuous_duplicate
---
String duplication is continuous (Lemma C.1.2, second half): the product of an
automaton with its transition monoid (`Transducers.reverse_duplicate_continuous`,
second conjunct).

# Attribution

Lemma C.1.2 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/ContAux.lean`.
-/
theorem continuous_duplicate {A : Type} [Finite A] : Continuous (fun w : List A => w ++ w) :=
  (Transducers.reverse_duplicate_continuous (A := A)).2

/--
---
conclusion: Lax916827.MapLiftingContinuity.continuous_mapLift
---
The map lifting of a continuous function is continuous (Lemma C.1.3): the
block automaton guessing the states at the ends of every block
(`Transducers.mapLift_continuous`), through Part A's `mapLift_eq`.

# Attribution

Lemma C.1.3 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/ContAux.lean`.
-/
theorem continuous_mapLift {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : Continuous f) : Continuous (mapLift f) := by
  rw [Lax765601Proofs.Bridge.mapLift_eq]
  exact Transducers.mapLift_continuous hf

/--
---
conclusion: Lax916827.RegularEquivalenceDecidable.decidable_twoWayCodeRel_eq
---
Equivalence of total coded two-way transducers is decidable (Theorem C.1.4),
`Transducers.regular_equivalence_decidable` of the source.

# Proof strategy

The source bounds the length of a shortest distinguishing input by an explicit
arithmetic expression in the two codes (`Transducers.RegDec.codeBound`, from
the crossing-sequence decomposition of a two-way run and Schützenberger's rank
criterion, `PartC/Reg*.lean`) and compares the two coded transducers on all
inputs up to that bound over the letters of the codes and one fresh letter
(`PartC/RegEqDec.lean`, `PartC/TwoWaySimPrimrec.lean`). The concept's codes are
the same lists as the source's; the bridge identifies the coded transducers
(`twoWayCodeAut_toSrc`), their relations and the totality promise, and
`DecidableUnderPromise` unfolds identically.

# Attribution

Theorem C.1.4 of *Transducers*, Part C; formalised by Aristotle (Harmonic).
-/
theorem decidable_twoWayCodeRel_eq :
    DecidableUnderPromise
      (fun p : TwoWayCode × TwoWayCode => TwoWayCodeTotal p.1 ∧ TwoWayCodeTotal p.2)
      (fun p => twoWayCodeRel p.1 = twoWayCodeRel p.2) := by
  rw [decidableUnderPromise_iff]
  simp only [twoWayCodeTotal_iff, twoWayCodeRel_eq]
  exact Transducers.regular_equivalence_decidable

/-! ## Two-way transducers -/

/--
---
conclusion: Lax916827.TwoWayContinuity.continuous_of_isTwoWay
---
Two-way transducers are continuous (Theorem C.2.2): the source runs a
deterministic automaton for the output language inside the transducer and
appeals to Shepherdson's theorem (`Transducers.twoWay_continuous`).

# Attribution

Theorem C.2.2 of *Transducers*, Part C (Rabin–Scott, Shepherdson); formalised
by Aristotle (Harmonic), `PartC/TwoWayCont.lean`, `PartC/TwoDFA.lean`.
-/
theorem continuous_of_isTwoWay {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : Continuous f :=
  Transducers.twoWay_continuous ((isTwoWay_iff f).1 hf)

/--
---
conclusion: Lax916827.ConfigurationGraphRational.isRationalFun_enc
---
The string representation of the reachable configuration graph is a rational
function of the input (Lemma C.2.3), `Transducers.twoWay_isRationalFun_enc`.

# Proof strategy

The concept's alphabet `C` is a distinct inductive type from the source's; the
bridge's `enc_toSrc` shows the two representations equal up to the bijection
`cletEquiv M` of the alphabets, and the source's rational function is
post-composed with the inverse letter-to-letter map
(`Transducers.isRationalFun_map`, `Transducers.isRationalFun_comp`).

# Attribution

Lemma C.2.3 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/ConfGraph*.lean`.
-/
theorem isRationalFun_enc {A B Q : Type} [Finite A] [Finite Q] (M : TwoWay A B Q) :
    IsRationalFun (TwoWay.enc M) := by
  rw [Lax132576Proofs.Bridge.isRationalFun_iff]
  have h := Transducers.isRationalFun_comp (Transducers.twoWay_isRationalFun_enc (toSrcTW M))
    (Transducers.isRationalFun_map (cletEquiv M).symm)
  have e : TwoWay.enc M =
      fun w => (Transducers.TwoWay.enc (toSrcTW M) w).map (cletEquiv M).symm := by
    funext w
    simp [enc_toSrc, List.map_map, Function.comp_def]
  rw [e]
  exact h

/--
---
conclusion: Lax916827.ConfigurationGraphOutput.isRegular_encOutputLang
---
The representations whose output lies in a regular language form a regular
language (Lemma C.2.4), `Transducers.twoWay_encOutputLang_isRegular`.

# Proof strategy

The concept's language is the inverse image of the source's under the
letter-to-letter bijection `cletToSrc M` (`enc_toSrc`, `computes_pathTrans` of
the bridge), and inverse images under letter-to-letter maps preserve regularity
(`isRegular_map`, the source's `continuous_map`).

# Attribution

Lemma C.2.4 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/ConfGraphReg.lean`, `PartC/ConfGraphRun.lean`.
-/
theorem isRegular_encOutputLang {A B Q : Type} [Finite A] [Finite Q] (M : TwoWay A B Q)
    {f : List A → List B} (hM : ∀ w, M.Computes w (f w)) {L : Language B} (hL : L.IsRegular) :
    Language.IsRegular {u : List (CLet Q (TwoWay.Lab M)) |
      (∃ w, u = TwoWay.enc M w) ∧ ∃ v, (TwoWay.pathTrans M).Computes u v ∧ v ∈ L} := by
  have h := Transducers.twoWay_encOutputLang_isRegular (toSrcTW M)
    (fun w => (computes_toSrc M w _).1 (hM w)) hL
  have h2 := isRegular_map (cletToSrc M) h
  convert h2 using 1
  ext u
  change ((∃ w, u = TwoWay.enc M w) ∧ ∃ v, (TwoWay.pathTrans M).Computes u v ∧ v ∈ L) ↔
    ((∃ w, u.map (cletToSrc M) = Transducers.TwoWay.enc (toSrcTW M) w) ∧
      ∃ v, (Transducers.TwoWay.pathTrans (toSrcTW M)).Computes (u.map (cletToSrc M)) v ∧ v ∈ L)
  simp only [enc_toSrc, computes_pathTrans, (List.map_injective_iff.2 (cletToSrc_injective M)).eq_iff]

/--
---
conclusion: Lax916827.TwoWayComposition.isTwoWay_comp
---
Two-way transducers are closed under composition (Theorem C.2.5),
`Transducers.twoWay_comp`: the second transducer is simulated on the run of the
first, walking backwards along the run when it moves left.

# Attribution

Theorem C.2.5 of *Transducers*, Part C (Chytil and Jákl); formalised by
Aristotle (Harmonic), `PartC/TwoWayComp*.lean`.
-/
theorem isTwoWay_comp {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C} (hf : IsTwoWay f) (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f) :=
  (isTwoWay_iff _).2 (Transducers.twoWay_comp ((isTwoWay_iff f).1 hf) ((isTwoWay_iff g).1 hg))

/--
---
conclusion: Lax916827.TwoWayMealyPrecomposition.isTwoWay_comp_isMealy
---
Two-way transducers are closed under pre-composition with Mealy machines (Lemma
C.2.6): the Krohn–Rhodes decomposition of Part A reduces to reversible and
flip-flop machines (`Transducers.twoWay_precomp_mealy`); Part A's bridge
transports `IsMealy`.

# Attribution

Lemma C.2.6 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/TwoWayPrecomp.lean`.
-/
theorem isTwoWay_comp_isMealy {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C} (hf : IsMealy f) (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f) :=
  (isTwoWay_iff _).2 (Transducers.twoWay_precomp_mealy
    ((Lax765601Proofs.Bridge.isMealy_iff f).1 hf) ((isTwoWay_iff g).1 hg))

/--
---
conclusion: Lax916827.TwoWayRationalPrecomposition.isTwoWay_comp_isRationalFun
---
Two-way transducers are closed under pre-composition with rational functions
(Corollary C.2.7), through the prime decomposition of Theorem B.2.6
(`Transducers.twoWay_precomp_rational`); Part B's bridge transports
`IsRationalFun`.

# Attribution

Corollary C.2.7 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/TwoWayRat.lean`, `PartC/TwoWayHom.lean`.
-/
theorem isTwoWay_comp_isRationalFun {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C} (hf : IsRationalFun f) (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f) :=
  (isTwoWay_iff _).2 (Transducers.twoWay_precomp_rational
    ((Lax132576Proofs.Bridge.isRationalFun_iff f).1 hf) ((isTwoWay_iff g).1 hg))

/--
---
conclusion: Lax916827.TwoWayOfRegular.isTwoWay_of_isRegularFun
---
Every regular function is computed by a two-way transducer (Corollary C.2.8):
induction on the composition tree with Theorem C.2.5 and Corollary C.2.7, and
explicit two-way transducers for map reverse and map duplicate
(`Transducers.regularFun_isTwoWay`).

# Attribution

Corollary C.2.8 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/Statements.lean`, `PartC/TwoWaySweep.lean`.
-/
theorem isTwoWay_of_isRegularFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsTwoWay f :=
  (isTwoWay_iff f).2 (Transducers.regularFun_isTwoWay ((isRegularFun_iff f).1 hf))

/--
---
conclusion: Lax916827.RegularOfTwoWay.isRegularFun_of_isTwoWay
---
Every two-way transducer computes a regular function (Theorem C.2.9, the hard
implication), `Transducers.twoWay_isRegular`.

# Proof strategy

The source reduces to the snake lemma in its general form
(`Transducers.boundedWidth_isRegular`, `PartC/SnakeReg.lean`): a halting run
visits every column at most `|Q|` times, so the function is its own
width-`|Q|` output function, and the width-`k` output function is regular by
induction on `k`, cutting the run at the record-breaking columns into looping
and progressing parts of smaller width (`PartC/SnakeWalk.lean`,
`PartC/SnakeRec.lean`, `PartC/SnakeLoop.lean`, the `PartC/SnakeChk*.lean`
family) and gluing them with Lemma C.2.10.

# Attribution

Theorem C.2.9 of *Transducers*, Part C; formalised by Aristotle (Harmonic).
-/
theorem isRegularFun_of_isTwoWay {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : IsRegularFun f :=
  (isRegularFun_iff f).2 (Transducers.twoWay_isRegular ((isTwoWay_iff f).1 hf))

/--
---
conclusion: Lax916827.TwoWayIffRegular.isTwoWay_iff_isRegularFun
---
Theorem C.2.9 as a biconditional, glued from its two halves taken as
assumptions.
-/
theorem isTwoWay_iff_isRegularFun {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsTwoWay f ↔ IsRegularFun f :=
  ⟨Lax916827.RegularOfTwoWay.isRegularFun_of_isTwoWay,
    Lax916827.TwoWayOfRegular.isTwoWay_of_isRegularFun⟩

/-! ## Closure properties -/

/--
---
conclusion: Lax916827.RegularMapLifting.isRegularFun_mapLift
---
Regular functions are closed under map lifting (Lemma C.2.10, first item):
map lifting commutes with composition and the primes lift
(`Transducers.regular_closure_properties`, first conjunct), through Part A's
`mapLift_eq`.

# Attribution

Lemma C.2.10 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/RegMapLift.lean`, `PartC/MapLift*.lean`.
-/
theorem isRegularFun_mapLift {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsRegularFun (mapLift f) := by
  rw [Lax765601Proofs.Bridge.mapLift_eq, isRegularFun_iff]
  exact (Transducers.regular_closure_properties ((isRegularFun_iff f).1 hf)
    ((isRegularFun_iff f).1 hf)).1

/--
---
conclusion: Lax916827.RegularConcatenation.isRegularFun_concat
---
Regular functions are closed under concatenation (Lemma C.2.10, second item):
map duplicate and the map liftings of the two functions on the two copies
(`Transducers.regular_closure_properties`, second conjunct).

# Attribution

Lemma C.2.10 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/RegClosure.lean`.
-/
theorem isRegularFun_concat {A B : Type} [Finite A] [Finite B] {f g : List A → List B}
    (hf : IsRegularFun f) (hg : IsRegularFun g) : IsRegularFun (fun w => f w ++ g w) :=
  (isRegularFun_iff _).2 (Transducers.regular_closure_properties ((isRegularFun_iff f).1 hf)
    ((isRegularFun_iff g).1 hg)).2.1

open scoped Classical in
/--
---
conclusion: Lax916827.RegularConditional.isRegularFun_ite
---
Regular functions are closed under conditionals over regular languages (Lemma
C.2.10, third item): a rational marking of the input with its membership in
`L` and the sum of Claim C.2.11 (`Transducers.regular_closure_properties`,
third conjunct).

# Attribution

Lemma C.2.10 of *Transducers*, Part C; formalised by Aristotle (Harmonic),
`PartC/RegClosure.lean`.
-/
theorem isRegularFun_ite {A B : Type} [Finite A] [Finite B] {f g : List A → List B}
    (hf : IsRegularFun f) (hg : IsRegularFun g) (L : Language A) (hL : L.IsRegular) :
    IsRegularFun (fun w => if w ∈ L then f w else g w) :=
  (isRegularFun_iff _).2 ((Transducers.regular_closure_properties ((isRegularFun_iff f).1 hf)
    ((isRegularFun_iff g).1 hg)).2.2 L hL)

/--
---
conclusion: Lax916827.RegularSum.exists_isRegularFun_sum
---
The sum of two regular functions on disjoint alphabets is regular (Claim
C.2.11, corrected on the empty input), `Transducers.sum_of_regular`.

# Proof strategy

The source's `sum_of_regular_aux` (`PartC/SumReg.lean`, `PartC/SumPrime.lean`,
`PartC/SumShape.lean`) builds the sum prime by prime; the claim as printed is
refuted on the empty input by `Transducers.not_sum_of_regular_nil`, hence the
two clauses on nonempty inputs only.

# Attribution

Claim C.2.11 of *Transducers*, Part C; formalised by Aristotle (Harmonic).
-/
theorem exists_isRegularFun_sum {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    [Nonempty B₁] [Nonempty B₂] {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (hf₁ : IsRegularFun f₁) (hf₂ : IsRegularFun f₂) :
    ∃ (bot : List (B₁ ⊕ B₂)) (F : List (A₁ ⊕ A₂) → List (B₁ ⊕ B₂)),
      (∃ b₁, Sum.inl b₁ ∈ bot) ∧ (∃ b₂, Sum.inr b₂ ∈ bot) ∧
      IsRegularFun F ∧
      (∀ u : List A₁, u ≠ [] → F (u.map Sum.inl) = (f₁ u).map Sum.inl) ∧
      (∀ u : List A₂, u ≠ [] → F (u.map Sum.inr) = (f₂ u).map Sum.inr) ∧
      (∀ w, (¬ ∃ u : List A₁, w = u.map Sum.inl) → (¬ ∃ u : List A₂, w = u.map Sum.inr) →
        F w = bot) := by
  obtain ⟨bot, F, h1, h2, hF, h4, h5, h6⟩ :=
    Transducers.sum_of_regular ((isRegularFun_iff f₁).1 hf₁) ((isRegularFun_iff f₂).1 hf₂)
  exact ⟨bot, F, h1, h2, (isRegularFun_iff F).2 hF, h4, h5, h6⟩

/--
---
conclusion: Lax916827.SnakeLemma.isRegularFun_snakeOut
---
The snake lemma (Lemma C.2.12): the output of a snake graph of width at most
`k`, read off its string representation, is a regular function
(`Transducers.SnakeGraph.snakeOut_isRegular`).

# Proof strategy

The source reads the snake letters through the two-way transducer
`snakeTrans` that walks along a snake graph (`PartC/SnakeAlph*.lean`) and
applies the general snake lemma `Transducers.boundedWidth_isRegular` for the
width-`k` output function of a two-way transducer on the regular language of
strings representing a snake graph of width at most `k`. The concept's snake
graphs are defined by the same formulas as the source's; `snakeOut_eq` of the
bridge identifies the two output functions.

# Attribution

Lemma C.2.12 of *Transducers*, Part C; formalised by Aristotle (Harmonic).
-/
theorem isRegularFun_snakeOut {Q B : Type} [Finite Q] [Finite B] (k : ℕ) :
    IsRegularFun (snakeOut (Q := Q) (B := B) k) := by
  rw [isRegularFun_iff, snakeOut_eq']
  exact Transducers.SnakeGraph.snakeOut_isRegular k

/-! ## Streaming string transducers -/

/--
---
conclusion: Lax916827.SSTOfRegular.isSST_of_isRegularFun
---
Every regular function is computed by a streaming string transducer (Theorem
C.3.2, from regular to sst): ssts are closed under post-composition with every
prime regular function (`Transducers.sst_iff_regular`, right to left,
`PartC/SSTRegular.lean`, `PartC/SSTMealy*.lean`, `PartC/SSTMap*.lean`).

# Attribution

Theorem C.3.2 of *Transducers*, Part C; formalised by Aristotle (Harmonic).
-/
theorem isSST_of_isRegularFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsSST f :=
  (isSST_iff f).2 ((Transducers.sst_iff_regular f).2 ((isRegularFun_iff f).1 hf))

/--
---
conclusion: Lax916827.RegularOfSST.isRegularFun_of_isSST
---
Every streaming string transducer computes a regular function (Theorem C.3.2,
from sst to regular): the sst is normalised and simulated by a two-way
transducer expanding the final output depth-first
(`PartC/SSTNorm.lean`, `PartC/SSTTwoWay.lean`), and two-way transducers compute
regular functions (Theorem C.2.9); `Transducers.sst_iff_regular`, left to
right.

# Attribution

Theorem C.3.2 of *Transducers*, Part C; formalised by Aristotle (Harmonic).
-/
theorem isRegularFun_of_isSST {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsSST f) : IsRegularFun f :=
  (isRegularFun_iff f).2 ((Transducers.sst_iff_regular f).1 ((isSST_iff f).1 hf))

/--
---
conclusion: Lax916827.SSTIffRegular.isSST_iff_isRegularFun
---
Theorem C.3.2 as a biconditional, glued from its two halves taken as
assumptions.
-/
theorem isSST_iff_isRegularFun {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSST f ↔ IsRegularFun f :=
  ⟨Lax916827.RegularOfSST.isRegularFun_of_isSST, Lax916827.SSTOfRegular.isSST_of_isRegularFun⟩

end Lax916827Proofs.Results
