/- Part C: Regular functions (Sections *The prime regular functions*, *Two-way transducers* and
*Streaming string transducers*)
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Sections *The prime regular functions* to *Streaming string
transducers* and the statements of their theorems, lemmas and claims.  All of them are proved, in
the supporting files of `RequestProject/PartC/`, and none of them takes a hypothesis: the two
effectivity statements of `RequestProject/PartC/EffectiveReg.lean` used by Theorem
`thm:decidable-equivalence-regular` are both proved (`Transducers.EffectiveTwoWayEvalEq` and
`Transducers.effectiveTwoWayBound`).  No file of Part C contains a `sorry`.

Lemmas `lem:compute-configuration-graph` and
`lem:check-if-output-string-of-configuration-graph-belongs-to-L`, which speak about the string
representation of the reachable configuration graph of a two-way transducer, are proved in
`RequestProject/PartC/ConfGraphReg.lean` and restated below.  The proofs of Theorems
`thm:continuity-2dfas` and `thm:composition-of-two-way-transducers` given here do not go through
that representation -- they work with the run semantics of `RequestProject/PartC/TwoWayRun.lean`
directly -- but the representation and the run semantics are proved to agree
(`Transducers.TwoWay.computes_enc`).

Lemma `lem:output-of-snake-graph-is-regular`, the book's snake lemma, is formalised twice: in the
form the book states it, over the alphabet of snake letters, as
`Transducers.SnakeGraph.snakeOut_isRegular` in `RequestProject/PartC/SnakeAlphReg.lean`, and in the
general form it is proved from, for the width-`k` output function of a two-way transducer, as
`Transducers.boundedWidth_isRegular` in `RequestProject/PartC/SnakeReg.lean`.  The latter is the
step through which Theorem `thm:2dfa-decomposition-into-primes` is proved. -/
import Lax132576Proofs.Source.PartB.WeightedStatements
import Lax916827Proofs.Source.PartC.ContAux
import Lax916827Proofs.Source.PartC.TwoWayCont
import Lax916827Proofs.Source.PartC.ConfGraphReg
import Lax916827Proofs.Source.PartC.TwoWayPrecomp
import Lax916827Proofs.Source.PartC.TwoWayRat
import Lax916827Proofs.Source.PartC.TwoWayCompFinal
import Lax916827Proofs.Source.PartC.TwoWayRegular
import Lax916827Proofs.Source.PartC.RegClosure
import Lax916827Proofs.Source.PartC.SnakeReg
import Lax916827Proofs.Source.PartC.SSTRegular
import Lax916827Proofs.Source.PartC.SSTTwoWay
import Lax916827Proofs.Source.PartC.WeightedRegClosure
import Lax916827Proofs.Source.PartC.RegEqDec
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## The prime regular functions (Definition `def:regular-functions`)

The definitions `Transducers.mapReverse`, `Transducers.mapDuplicate`, `Transducers.RegularFam` and
`Transducers.IsRegularFun` (Definition `def:regular-functions`) used to be given here; they have
been moved, unchanged, to `RequestProject/PartC/RegularDef.lean`, which this file imports, so that
the constructions used in the proofs of Lemma `lem:regular-closure-properties` and Claim
`claim:conditional` could be developed before this file. -/

/-! ## The prime regular functions -/

/-- The map reverse function is continuous. -/
lemma continuous_mapReverse (A : Type) : Continuous (mapReverse A) :=
  continuous_mapLift continuous_reverse

/-- The map duplicate function is continuous. -/
lemma continuous_mapDuplicate (A : Type) : Continuous (mapDuplicate A) :=
  continuous_mapLift continuous_dup

/-- Regular functions are continuous (Theorem
`thm:regular-functions-are-continuous-and-closed-under-composition`; no finiteness assumption on the
alphabets is needed, since the prime regular functions are continuous over any alphabets). -/
theorem continuous_of_isRegularFun {A B : Type} {f : List A → List B}
    (hf : IsRegularFun f) : Continuous f := by
  induction hf with
  | base h =>
      rcases h with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact continuous_of_isRationalFun hrat
      · exact Continuous.congr
          (Continuous.comp (continuous_map (e'.symm : Option A₀ → _))
            (Continuous.comp (continuous_mapReverse A₀) (continuous_map (e : _ → Option A₀))))
          (fun w => (hfe w).symm)
      · exact Continuous.congr
          (Continuous.comp (continuous_map (e'.symm : Option A₀ → _))
            (Continuous.comp (continuous_mapDuplicate A₀) (continuous_map (e : _ → Option A₀))))
          (fun w => (hfe w).symm)
  | id A => exact continuous_id
  | comp _ _ ihf ihg => exact Continuous.comp ihg ihf

/-- **Theorem `thm:regular-functions-are-continuous-and-closed-under-composition` (continuity).**  Regular functions are continuous. -/
theorem regular_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : Continuous f :=
  continuous_of_isRegularFun hf

/-- **Theorem `thm:regular-functions-are-continuous-and-closed-under-composition` (composition).**
Regular functions are closed under composition. -/
theorem regular_comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C}
    (hf : IsRegularFun f) (hg : IsRegularFun g) : IsRegularFun (g ∘ f) :=
  CompClosure.comp hf hg

/-- **Lemma `lem:reversal-duplication-continuous`.**  String reversal and string duplication are continuous. -/
theorem reverse_duplicate_continuous {A : Type} [Finite A] :
    Continuous (List.reverse : List A → List A) ∧
      Continuous (fun w : List A => w ++ w) :=
  ⟨continuous_reverse, continuous_dup⟩

/-- **Lemma `lem:map-lifting-continuous`.**  If a string-to-string function is continuous, then the
same is true for its map lifting. -/
theorem mapLift_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : Continuous f) : Continuous (mapLift f) :=
  continuous_mapLift hf

/-! ### Equivalence (Theorem `thm:decidable-equivalence-regular`)

The book proves Theorem `thm:decidable-equivalence-regular` by a reduction to zeroness --
equivalently, to equivalence -- of weighted automata over the field of rationals, and the reduction
uses the *prime decomposition* of a regular function: the class of functions that can be
post-composed with weighted automata is closed under composition, contains the rational functions by
Lemma `lem:closure-weighted-automata-precomposition` (`Transducers.weighted_precomp_rational`), and
contains map reverse and map duplicate, for which the book gives the two constructions with triples
of states.

That proof is formalised in `RequestProject/PartC/WeightedRegClosure.lean` and
`RequestProject/PartC/WeightedMapLift.lean`, on linear representations of
weighted automata rather than on the automata themselves:

* `Transducers.isWeighted_comp_mapReverse` -- the map reverse construction,
  where running a block backwards is transposition of the matrices of the
  representation (this is where commutativity of the semiring is used, as the
  book points out);
* `Transducers.isWeighted_comp_mapDuplicate` -- the map duplicate construction,
  where the weight of a transition of the new automaton is a product of the
  weights of two transitions of the original one, realised by the Kronecker
  square of the matrices;
* `Transducers.isWeighted_comp_regular` -- the induction on the prime
  decomposition, i.e. the statement that weighted automata are closed under
  pre-composition with regular functions;
* `Transducers.exists_injective_weighted` -- observation (a) of the book:
  output strings are represented injectively by rational numbers, by a weighted
  automaton;
* `Transducers.regularFun_eq_iff_weighted_eq` -- the reduction itself: two
  regular functions are equal if and only if the two weighted automata over `ℚ`
  obtained by post-composing them with the injective automaton are equal;
* `Transducers.regularFun_eq_of_short` -- the resulting decision procedure in
  semantic form: two regular functions over finite alphabets are equal as soon
  as they agree on the finitely many inputs of length at most a bound supplied
  by the zeroness criterion for weighted automata over a field
  (`Transducers.weighted_eq_of_short`, the mathematical content of
  Theorems `thm:equivalence-weighted-automata` and `thm:zeroness-weighted-automata`).

The statement of the decidability on *finite descriptions* of transducers is
`Transducers.regular_equivalence_decidable` in Section *Decidability of equivalence* below; see its
docstring. -/

/-! ## Two-way transducers -/

/-! **Definition `def:two-way-transducer` (two-way transducers)** (`TwoWay`, `Cfg`,
`TwoWay.stepCfg`, `TwoWay.Reaches`, `TwoWay.Computes` and `IsTwoWay`) is in
`RequestProject/PartC/TwoWayCont.lean`, together with the proof of
Theorem `thm:continuity-2dfas` below. -/

/-! ### Continuity -/

/-- **Theorem `thm:continuity-2dfas`.**  Every function computed by a two-way transducer is
continuous. -/
theorem twoWay_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : Continuous f :=
  twoWay_continuous_aux hf

/-! ### The string representation of the reachable configuration graph

The book proves Theorem `thm:continuity-2dfas` in two steps, through the string representation of
the reachable configuration graph of the transducer over the alphabet `C` of the book: the two
lemmas below.  The alphabet `C` (`Transducers.CLet`), the representation (`TwoWay.enc`) and the
transducer `TwoWay.pathTrans` that reads the output string off a representation are defined in
`RequestProject/PartC/ConfGraph.lean`; that the representation describes the same runs as the run
semantics of `RequestProject/PartC/TwoWayRun.lean` is `TwoWay.computes_enc` and
`TwoWay.computes_enc_iff`.  The proof of Theorem `thm:continuity-2dfas` above does not go through
them: it runs a deterministic automaton for the output language inside the transducer and appeals to
Shepherdson's Theorem. -/

/-- **The main observation** in the proof of Lemma `lem:compute-configuration-graph`: the strings
over the alphabet `C` that represent a reachable configuration graph of a two-way transducer form a
regular language. -/
theorem twoWay_encLang_isRegular {A B Q : Type} [Finite A] [Finite Q] (M : TwoWay A B Q) :
    Language.IsRegular {u : List (CLet Q (TwoWay.Lab M)) | ∃ w, u = TwoWay.enc M w} :=
  TwoWay.encLang_isRegular M

/-- **Lemma `lem:compute-configuration-graph`.**  The function which maps an input string to the
string representation of its reachable configuration graph is rational. -/
theorem twoWay_isRationalFun_enc {A B Q : Type} [Finite A] [Finite Q] (M : TwoWay A B Q) :
    IsRationalFun (TwoWay.enc M) :=
  TwoWay.isRationalFun_enc M

/-- **Lemma `lem:check-if-output-string-of-configuration-graph-belongs-to-L`.**  For a regular
language `L`, the strings over the alphabet `C` which represent a reachable configuration graph
whose output string belongs to `L` form a regular language.  The output string of a representation
is the string printed by the transducer `TwoWay.pathTrans M`, which walks along the represented
graph; on the representation of the graph of `M` on `w` it is the output of `M` on `w`
(`TwoWay.computes_enc`).  As in the book, the transducer is assumed to compute a (total)
function. -/
theorem twoWay_encOutputLang_isRegular {A B Q : Type} [Finite A] [Finite Q] (M : TwoWay A B Q)
    {f : List A → List B} (hM : ∀ w, M.Computes w (f w)) {L : Language B} (hL : L.IsRegular) :
    Language.IsRegular {u : List (CLet Q (TwoWay.Lab M)) |
      (∃ w, u = TwoWay.enc M w) ∧ ∃ v, (TwoWay.pathTrans M).Computes u v ∧ v ∈ L} :=
  TwoWay.encOutputLang_isRegular M hM hL

/-! ### Closure under composition -/

/-- **Lemma `lem:2dfa-precomposition-with-mealy`.**  Functions computed by two-way transducers are
closed under pre-composition with Mealy machines. -/
theorem twoWay_precomp_mealy {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C}
    (hf : IsMealy f) (hg : IsTwoWay g) : IsTwoWay (g ∘ f) :=
  isTwoWay_comp_compClosure (krohn_rhodes hf) hg

/-- **Corollary `cor:2dfa-closure-under-composition`.**  Functions computed by two-way transducers
are closed under pre-composition with rational functions. -/
theorem twoWay_precomp_rational {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C}
    (hf : IsRationalFun f) (hg : IsTwoWay g) : IsTwoWay (g ∘ f) :=
  isTwoWay_comp_rational hf hg

/-- **Theorem `thm:composition-of-two-way-transducers`.**  Functions computed by two-way transducers
are closed under composition. -/
theorem twoWay_comp {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C}
    (hf : IsTwoWay f) (hg : IsTwoWay g) : IsTwoWay (g ∘ f) :=
  isTwoWay_comp_twoWay hf hg

/-! **Corollary `cor:2dfa-computes-all-regular-functions`.**  The book states it as "Every regular
function is computed by a two-way transducer", which is what is formalised immediately below, as
`Transducers.isTwoWay_of_isRegularFun` and `Transducers.regularFun_isTwoWay`, and proved in full.

An earlier edition printed the corollary the other way round, as `two-way ⊆ regular`, which is
the opposite of what its proof establishes; that discrepancy no longer exists.  The inclusion
`two-way ⊆ regular` is the hard half of Theorem `thm:2dfa-decomposition-into-primes`; it is
stated (and proved) below as `Transducers.twoWay_isRegular`, the left-to-right implication of
`Transducers.twoWay_iff_regular`, and is therefore not duplicated here. -/

/-- **Corollary `cor:2dfa-computes-all-regular-functions`**: every regular function is
computed by a two-way transducer.

The auxiliary form carries the finiteness of the two alphabets as explicit
hypotheses, so that the induction on the composition tree has access to the
finiteness of the intermediate alphabets. -/
theorem isTwoWay_of_isRegularFun {A B : Type} {f : List A → List B}
    (hf : IsRegularFun f) : Finite A → Finite B → IsTwoWay f := by
  induction hf with
  | @base A B f h =>
      intro hA hB
      haveI := hA; haveI := hB
      rcases h with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact isTwoWay_of_rational hrat
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 : IsTwoWay (mapReverse A₀) := isTwoWay_mapLift_reverse A₀
        have h3 := isTwoWay_precomp_map (isTwoWay_postMap h1 (e'.symm : Option A₀ → B))
          (e : A → Option A₀)
        exact (funext hfe : f = _) ▸ h3
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 : IsTwoWay (mapDuplicate A₀) := isTwoWay_mapLift_dup A₀
        have h3 := isTwoWay_precomp_map (isTwoWay_postMap h1 (e'.symm : Option A₀ → B))
          (e : A → Option A₀)
        exact (funext hfe : f = _) ▸ h3
  | id A => intro hA _; exact isTwoWay_id
  | @comp A B C hB f g _ _ ihf ihg =>
      intro hA hC
      haveI := hA; haveI := hB; haveI := hC
      exact isTwoWay_comp_twoWay (ihf hA hB) (ihg hB hC)

/-- **Corollary `cor:2dfa-computes-all-regular-functions`**: every regular function is
computed by a two-way transducer. -/
theorem regularFun_isTwoWay {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsTwoWay f :=
  isTwoWay_of_isRegularFun hf ‹_› ‹_›

/-! ### Decidability of equivalence

Equivalence of regular functions (Theorem `thm:decidable-equivalence-regular`) is decidable; the
algorithm can be run directly on two-way transducers.  A two-way transducer over the alphabet `ℕ` is
coded by a finite lookup table for its transition function, transitions that are absent from the
table halting with empty output. -/

/-  The definitions `Transducers.TwoWayCode`, `Transducers.twoWayCodeAut`,
`Transducers.twoWayCodeRel` and `Transducers.TwoWayCodeTotal` used to be given
here; they have been moved, unchanged, to
`RequestProject/PartC/RegCodeSan.lean`, which this file imports, so that the
decision procedure below could be developed before this file. -/

/-  Theorem `thm:decidable-equivalence-regular` is now unconditional.

The mathematical content of the book's proof -- the reduction to equivalence of weighted automata
over the field of rationals through the prime decomposition, including the constructions for map
reverse and map duplicate -- is proved in `RequestProject/PartC/WeightedRegClosure.lean`; see the
note at the end of Section *The prime regular functions* above, and in particular
`Transducers.regularFun_eq_of_short`, which reduces the equivalence of two regular functions to a
finite check.

Both effectivity ingredients of the decision procedure on codes are proved.

* The comparison of two coded two-way transducers on a given input is
  `Transducers.EffectiveTwoWayEvalEq` in `RequestProject/PartC/TwoWaySimPrimrec.lean`, by
  simulating the run with the bound on its length of `Transducers.RegDec.halt_time_lt_fuel`.
* The equivalence bound is computed from the two codes by `Transducers.RegDec.codeBound`
  (`RequestProject/PartC/RegEffBound.lean`), which discharges what used to be the hypothesis
  `Transducers.EffectiveTwoWayBound` of `RequestProject/PartC/EffectiveReg.lean`.  The bound is an
  explicit arithmetic expression in the sizes of the two codes; it comes from
  `Transducers.RegHankel.twoWay_eq_of_short` (`RequestProject/PartC/RegShort.lean`), an
  explicit-rank form of Schützenberger's criterion applied to the crossing-sequence decomposition
  of a two-way run (`RequestProject/PartC/RegPos.lean`, `RegBlock.lean`, `RegCross.lean`,
  `RegProfile.lean`, `RegVal.lean`, `RegHankel.lean`), which replaces the chain of existentials
  over abstract finite types that made `Transducers.exists_twoWayCode_bound` non-effective.

Everything else -- that the finitely many inputs to be tested may be taken over the letters of the
two codes together with one fresh letter, and the assembly of the decision procedure -- is
discharged in full in `RequestProject/PartC/RegEqDec.lean`. -/

/-- **Theorem `thm:decidable-equivalence-regular`.**  Equivalence is decidable for regular functions
(here: for the two-way transducers that compute them, cf. Theorem
`thm:2dfa-decomposition-into-primes`).

Unconditional; see the comment above. -/
theorem regular_equivalence_decidable :
    DecidableUnderPromise
      (fun p : TwoWayCode × TwoWayCode => TwoWayCodeTotal p.1 ∧ TwoWayCodeTotal p.2)
      (fun p => twoWayCodeRel p.1 = twoWayCodeRel p.2) :=
  regular_equivalence_decidable_aux

/-! ### Decomposition into prime functions -/

/-- **Theorem `thm:2dfa-decomposition-into-primes`, left-to-right implication** (equivalently, the
inclusion as it is *printed* in Corollary `cor:2dfa-computes-all-regular-functions`): every function
computed by a two-way transducer is regular, i.e. it can be decomposed into prime functions.

This is the hard half of Theorem `thm:2dfa-decomposition-into-primes`.  It is reduced, in
`RequestProject/PartC/SnakeReg.lean`, to the book's snake lemma
`Transducers.boundedWidth_isRegular`, whose base cases `k = 0` and `k = 1` are
proved in `RequestProject/PartC/SnakeBase.lean` and whose induction step
`Transducers.boundedWidth_isRegular_step` is proved in
`RequestProject/PartC/SnakeReg.lean`: a run that halts visits every column at most `|Q|` times
(`TwoWay.widthLe_card`), so the function computed by a two-way transducer with
state set `Q` is its own width-`|Q|` output function `TwoWay.widthOut M |Q|`,
and it remains to see that the width-`k` output function of a two-way transducer
is regular for every `k`.

The book proves the snake lemma by induction on the width, decomposing a run of width `k` into
*looping* parts and *progressing* parts along the *record-breaking* columns; the parts have width at
most `k - 1`, they are cut out of the input by rational functions, and they are glued back together
with the three closure properties of `regular_closure_properties` (Lemma
`lem:regular-closure-properties`) below.  The two closure ingredients that the book's argument rests
on (Lemma `lem:regular-closure-properties` and Claim `claim:conditional`) are proved, as is the
reduction to snakes and the combinatorics of the width induction:
`RequestProject/PartC/SnakeWalk.lean`, `RequestProject/PartC/SnakeRec.lean` and
`RequestProject/PartC/SnakeLoop.lean` prove that a halting run of width at most `k ≥ 2` splits into
finitely many consecutive pieces of width at most `k - 1` whose outputs concatenate to the output of
the run (`TwoWay.runOutput_splits`).  The machine-theoretic half of the induction step -- that the
output of such a piece is the value of a width-`(k-1)` snake function on a factor of the input cut
out by a rational function -- is supplied by the `RequestProject/PartC/SnakeChk*.lean` family, which
builds the rational annotation marking the record-breaking columns. -/
theorem twoWay_isRegular {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : IsRegularFun f :=
  isRegularFun_of_isTwoWay hf

/-- **Theorem `thm:2dfa-decomposition-into-primes`.**  Two-way transducers compute exactly the
regular functions.

The right-to-left implication is Corollary `cor:2dfa-computes-all-regular-functions`
(`regularFun_isTwoWay`, proved above).  The left-to-right implication is `twoWay_isRegular` above,
the hard half; see the discussion in its docstring. -/
theorem twoWay_iff_regular {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsTwoWay f ↔ IsRegularFun f :=
  ⟨fun hf => twoWay_isRegular hf, fun hf => regularFun_isTwoWay hf⟩

open scoped Classical in
/-- **Lemma `lem:regular-closure-properties`.**  Regular functions are closed under map lifting,
concatenation, and conditionals over a regular language. -/
theorem regular_closure_properties {A B : Type} [Finite A] [Finite B]
    {f g : List A → List B} (hf : IsRegularFun f) (hg : IsRegularFun g) :
    IsRegularFun (mapLift f) ∧
      IsRegularFun (fun w => f w ++ g w) ∧
      ∀ L : Language A, L.IsRegular →
        IsRegularFun (fun w => if w ∈ L then f w else g w) :=
  ⟨isRegularFun_mapLift hf, isRegularFun_concat hf hg,
    fun _ hL => isRegularFun_cond hf hg hL⟩

/-  **Claim `claim:conditional`** as printed in the book is *false* on the empty input: the empty
string uses only letters of `A₁` and, at the same time, only letters of `A₂`, so the first two
requirements below conflict on it unless `f₁ ε` and `f₂ ε` are both empty (see
`Transducers.not_sum_of_regular_nil`, a counterexample with `f₁` constant and `f₂` the identity).
The original statement is kept here, commented out, and the corrected statement -- which asks for
the two requirements on *nonempty* inputs only, and leaves the value on the empty input unspecified
-- follows it.  The correction is harmless for the use made of the claim in the book: in the proof
of Lemma `lem:regular-closure-properties` the blocks that the sum is applied to are always nonempty.

theorem sum_of_regular {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (hf₁ : IsRegularFun f₁) (hf₂ : IsRegularFun f₂) :
    ∃ (bot : List (B₁ ⊕ B₂)) (F : List (A₁ ⊕ A₂) → List (B₁ ⊕ B₂)),
      (∃ b₁, Sum.inl b₁ ∈ bot) ∧ (∃ b₂, Sum.inr b₂ ∈ bot) ∧
      IsRegularFun F ∧
      (∀ u : List A₁, F (u.map Sum.inl) = (f₁ u).map Sum.inl) ∧
      (∀ u : List A₂, F (u.map Sum.inr) = (f₂ u).map Sum.inr) ∧
      (∀ w, (¬ ∃ u : List A₁, w = u.map Sum.inl) → (¬ ∃ u : List A₂, w = u.map Sum.inr) →
        F w = bot) := by
  sorry
-/

/-- **Claim `claim:conditional`** (corrected on the empty input; see the note above).  For
regular functions `f₁ : A₁* → B₁*` and `f₂ : A₂* → B₂*` with disjoint input and
output alphabets, the function `f₁ + f₂` is regular: it applies `f₁` to the
nonempty inputs using only letters of `A₁`, `f₂` to the nonempty inputs using
only letters of `A₂`, and returns a fixed string `⊥` using both output alphabets
otherwise.  The output alphabets are assumed to be nonempty, as they must be for
`⊥` to exist. -/
theorem sum_of_regular {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    [Nonempty B₁] [Nonempty B₂]
    {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (hf₁ : IsRegularFun f₁) (hf₂ : IsRegularFun f₂) :
    ∃ (bot : List (B₁ ⊕ B₂)) (F : List (A₁ ⊕ A₂) → List (B₁ ⊕ B₂)),
      (∃ b₁, Sum.inl b₁ ∈ bot) ∧ (∃ b₂, Sum.inr b₂ ∈ bot) ∧
      IsRegularFun F ∧
      (∀ u : List A₁, u ≠ [] → F (u.map Sum.inl) = (f₁ u).map Sum.inl) ∧
      (∀ u : List A₂, u ≠ [] → F (u.map Sum.inr) = (f₂ u).map Sum.inr) ∧
      (∀ w, (¬ ∃ u : List A₁, w = u.map Sum.inl) → (¬ ∃ u : List A₂, w = u.map Sum.inr) →
        F w = bot) :=
  sum_of_regular_aux hf₁ hf₂

/-! ## Streaming string transducers -/

/-! The definitions `Transducers.Copyless`, `Transducers.SST` (Definition `def:sst`),
its semantics `Transducers.SST.subst`, `Transducers.SST.stepConfig`,
`Transducers.SST.runConfig`, `Transducers.SST.eval` and `Transducers.IsSST` used
to be given here; they have been moved, unchanged, to
`RequestProject/PartC/SSTDef.lean`, which this file imports (through
`RequestProject/PartC/SSTRegular.lean`), so that the constructions used in the
proof of Theorem `theorem:sst-two-way-equivalence` could be developed before this file. -/

/-- **Theorem `theorem:sst-two-way-equivalence`.**  Streaming string transducers compute exactly the
regular functions.

The right-to-left implication is `isSST_of_isRegularFun`
(`RequestProject/PartC/SSTRegular.lean`): sst's are closed under
post-composition with the prime regular functions, so they contain every
composition of primes.  The left-to-right implication goes through
Theorem `thm:2dfa-decomposition-into-primes`: an sst is simulated by a two-way transducer
(`isTwoWay_of_isSST`, `RequestProject/PartC/SSTTwoWay.lean`), and a two-way
transducer computes a regular function (`twoWay_isRegular`). -/
theorem sst_iff_regular {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSST f ↔ IsRegularFun f :=
  ⟨fun hf => twoWay_isRegular (isTwoWay_of_isSST hf), fun hf => isSST_of_isRegularFun hf⟩

end Lax916827Proofs.Transducers
