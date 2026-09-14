import Lax194892.PolyregularContinuity
import Lax194892.ForOfPolyregular
import Lax194892.PolyregularOfFor
import Lax194892.ForIffPolyregular
import Lax194892.PrenexNormalForm
import Lax194892.ForComposition
import Lax194892.PebbleContinuity
import Lax194892.PebbleReachability
import Lax194892.BalancedRunReachability
import Lax194892.ForOfPebble
import Lax194892.PebbleOfFor
import Lax194892.PebbleIffFor
import Lax194892.ChildrenOfConfiguration
import Lax194892.ChildGraphOfConfiguration
import Lax194892.ChildrenOfChildGraph
import Lax194892Proofs.Bridge

/-!
The numbered results of Part D of *Transducers*, transported from the ported
source development through `Lax194892Proofs.Bridge` (and the bridges of Parts
A and C for the notions of those parts).
-/

namespace Lax194892Proofs.Results

open Lax765601Proofs Lax132576Proofs Lax916827Proofs
open Lax765601.Continuity Lax765601.CompositionClosure
open Lax916827.RegularFunctions
open Lax194892.MarkedSquaring Lax194892.PolyregularFunctions Lax194892.ForTransducers
  Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding
  Lax194892.ChildConfigurationGraphs
open Lax194892Proofs.Bridge

/-! ## Polyregular functions -/

/--
---
conclusion: Lax194892.PolyregularContinuity.continuous_of_isPolyregular
---
Polyregular functions are continuous (Theorem D.0.2): induction on the
composition tree, with Theorem C.1.1 for the regular primes and a direct
automaton for marked squaring (`Transducers.polyregular_continuous`).

# Proof strategy

The concept's `IsPolyregular` is the source's through `isPolyregular_iff` (Part
A's `compClosure_iff` on the family, whose regular half goes through Part C's
`isRegularFun_iff` and whose marked squaring unfolds identically); `Continuous`
unfolds identically. The source proves marked squaring continuous by running
the input backwards through a deterministic automaton for the output language
and reading off the states of the blocks (`PartD/MarkedSquare.lean`).

# Attribution

Theorem D.0.2 of *Transducers*, Part D; formalised by Aristotle (Harmonic),
`PartD/Statements.lean`, `PartD/MarkedSquare.lean`.
-/
theorem continuous_of_isPolyregular {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPolyregular f) : Continuous f :=
  Transducers.polyregular_continuous ((isPolyregular_iff f).1 hf)

/-! ## For-transducers -/

/--
---
conclusion: Lax194892.ForOfPolyregular.isForTransducer_of_isPolyregular
---
Every polyregular function is computed by a for-transducer (Theorem D.1.1,
from polyregular to for-transducers): for-transducers for the regular primes
through their two-way transducers (Corollary C.2.8), a for-transducer for
marked squaring, and Lemma D.1.4 for the composition
(`Transducers.isForTransducer_of_isPolyregular`).

# Proof strategy

The concept's for-transducer syntax is a distinct inductive type from the
source's; the bridge's `toSrcProg`/`ofSrcProg` are mutually inverse and
preserve the semantics (`exec_toSrcProg`, by induction on the program), which
gives `isForTransducer_iff`; `isPolyregular_iff` transports the hypothesis.

# Attribution

Theorem D.1.1 of *Transducers*, Part D; formalised by Aristotle (Harmonic),
`PartD/PolyFor.lean`, `PartD/PolyStep*.lean`, `PartD/TwoWayTotal.lean`.
-/
theorem isForTransducer_of_isPolyregular {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsPolyregular f) : IsForTransducer f :=
  (isForTransducer_iff f).2
    ((Transducers.polyregular_iff_forTransducer f).1 ((isPolyregular_iff f).1 hf))

/--
---
conclusion: Lax194892.PolyregularOfFor.isPolyregular_of_isForTransducer
---
Every for-transducer computes a polyregular function (Theorem D.1.1, from
for-transducers to polyregular): the prenex form of Lemma D.1.3, whose loop
block is simulated by iterated marked squarings and a regular function
enumerating the tuples of positions in loop order, and whose loop-free body is
a regular function of the enumeration (`Transducers.PolyEnum.isPolyregular_of_isForTransducer`).

# Attribution

Theorem D.1.1 of *Transducers*, Part D; formalised by Aristotle (Harmonic),
`PartD/PolyEnum*.lean`, `PartD/PolyScan*.lean`, `PartD/ForPrenex*.lean`.
-/
theorem isPolyregular_of_isForTransducer {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsForTransducer f) : IsPolyregular f :=
  (isPolyregular_iff f).2
    ((Transducers.polyregular_iff_forTransducer f).2 ((isForTransducer_iff f).1 hf))

/--
---
conclusion: Lax194892.ForIffPolyregular.isPolyregular_iff_isForTransducer
---
Theorem D.1.1 as a biconditional, glued from its two halves taken as
assumptions.
-/
theorem isPolyregular_iff_isForTransducer {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsPolyregular f ↔ IsForTransducer f :=
  ⟨Lax194892.ForOfPolyregular.isForTransducer_of_isPolyregular,
    Lax194892.PolyregularOfFor.isPolyregular_of_isForTransducer⟩

/--
---
conclusion: Lax194892.PrenexNormalForm.exists_prenexForm
---
Every for-transducer is equivalent to one in prenex form (Lemma D.1.3),
`Transducers.forTransducer_prenex`.

# Proof strategy

The source pulls the loops to the front one at a time, replacing a loop nested
under a conditional or followed by further code by a loop whose body tests a
Boolean flag recording the position in the original control flow
(`PartD/ForPrenex.lean`, `PartD/ForNest.lean`, `PartD/ForMerge.lean`). The
concept's prenex form is transported through `prenexForm_toSrcProg`: loop
freedom, nesting of loops and the one-output bound all commute with
`toSrcProg`, so the source's prenex program comes back as `ofSrcProg` of it,
with the same semantics by `eval_ofSrcProg`.

# Attribution

Lemma D.1.3 of *Transducers*, Part D; formalised by Aristotle (Harmonic).
-/
theorem exists_prenexForm {A B : Type} (P : ForProg A B) :
    ∃ P' : ForProg A B, P'.PrenexForm ∧ ∀ w, P'.eval w = P.eval w := by
  obtain ⟨P', hP', heval⟩ := Transducers.forTransducer_prenex (toSrcProg P)
  refine ⟨ofSrcProg P', ?_, fun w => ?_⟩
  · rw [← prenexForm_toSrcProg, toSrcProg_ofSrcProg]
    exact hP'
  · rw [eval_ofSrcProg, heval, eval_toSrcProg]

/--
---
conclusion: Lax194892.ForComposition.isForTransducer_comp
---
Functions computed by for-transducers are closed under composition (Lemma
D.1.4), `Transducers.forTransducer_comp`.

# Proof strategy

The source simulates the second program on the output of the first: each
position variable of the second program ranging over the output is replaced by
the tuple of loop variables of the first program at which that output letter
is produced, and the tests on output positions become tests on these tuples,
evaluated by re-running the first program (`PartD/ForComp*.lean`,
`PartD/ForResim.lean`, `PartD/ForTrace.lean`). `isForTransducer_iff` transports
both hypotheses and the conclusion.

# Attribution

Lemma D.1.4 of *Transducers*, Part D; formalised by Aristotle (Harmonic).
-/
theorem isForTransducer_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsForTransducer f) (hg : IsForTransducer g) : IsForTransducer (g ∘ f) :=
  (isForTransducer_iff _).2
    (Transducers.forTransducer_comp ((isForTransducer_iff f).1 hf) ((isForTransducer_iff g).1 hg))

/-! ## Pebble transducers -/

/--
---
conclusion: Lax194892.PebbleContinuity.continuous_of_isPebbleTransducer
---
Pebble transducers compute continuous functions (Theorem D.2.1),
`Transducers.pebble_continuous`.

# Proof strategy

The source proves the regularity of the languages recognised by pebble
automata (a pebble transducer whose output is a single accepting bit) by
induction on the number of pebbles, the top pebble being eliminated by a
two-way automaton that guesses the run of the automaton below it
(`PartD/PebbleLev1.lean`, `PartD/PebbleAut.lean`, `PartD/PebbleReg.lean`); the
inverse image of a regular language under the transducer is then recognised by
a pebble automaton. The concept's pebble transducers are transported by
`toSrcPeb`, whose configuration graph is that of the concept's transducer
(`stepCfg_toSrcPeb`, `reaches_toSrcPeb`), giving `isPebbleTransducer_iff`.

# Attribution

Theorem D.2.1 of *Transducers*, Part D; formalised by Aristotle (Harmonic).
-/
theorem continuous_of_isPebbleTransducer {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPebbleTransducer f) : Continuous f :=
  Transducers.pebble_continuous ((isPebbleTransducer_iff f).1 hf)

/--
---
conclusion: Lax194892.PebbleReachability.exists_regular_reachLang
---
The string representations of pairs of configurations connected by a run form
a regular language (Lemma D.2.2), `Transducers.reachability_pebble_automaton`.

# Proof strategy

The source builds a pebble automaton that reads the pair of configurations off
its input, places its pebbles on the source configuration and simulates the
transducer until it reaches the target (`PartD/PebReachAut.lean`,
`PartD/PebReachSim.lean`, `PartD/PebReachRun.lean`); the language is regular
by the regularity of pebble automata behind Theorem D.2.1. The encodings unfold
identically (`pairEnc_eq`) and reachability is transported by
`reaches_toSrcPeb`.

# Attribution

Lemma D.2.2 of *Transducers*, Part D; formalised by Aristotle (Harmonic),
`PartD/PebReach.lean`.
-/
theorem exists_regular_reachLang {A B Q : Type} {k : ℕ} [Finite A] [Finite Q]
    (M : Pebble A B Q k) :
    ∃ L : Language (PairLetter A Q k), L.IsRegular ∧
      ∀ (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A),
        (∀ p ∈ sts, p ≤ w.length) → (∀ p ∈ stt, p ≤ w.length) →
        sts.length ≤ k → stt.length ≤ k →
        (pairEnc q₁ q₂ sts stt w ∈ L ↔
          ∃ v, M.Reaches w (PebbleCfg.conf q₁ sts) v (PebbleCfg.conf q₂ stt)) := by
  obtain ⟨L, hL, hspec⟩ := Transducers.reachability_pebble_automaton (toSrcPeb M)
  refine ⟨L, hL, fun q₁ q₂ sts stt w h₁ h₂ h₃ h₄ => ?_⟩
  rw [pairEnc_eq, hspec q₁ q₂ sts stt w h₁ h₂ h₃ h₄]
  exact exists_congr fun v =>
    reaches_toSrcPeb M w (PebbleCfg.conf q₁ sts) v (PebbleCfg.conf q₂ stt)

/--
---
conclusion: Lax194892.BalancedRunReachability.exists_regular_balancedLang
---
For every height `ℓ ∈ {1, …, k}`, the string representations of pairs of
configurations of height `ℓ` connected by a balanced run form a regular
language (Claim D.2.3), `Transducers.reachability_basic_run`.

# Proof strategy

The same pebble automaton as for Lemma D.2.2, restricted to runs that never pop
below height `ℓ` (`Transducers.PebEnc.reachLang M ℓ`); the concept's balanced
run is the source's restricted reachability, transported by
`balancedRun_toSrcPeb`.

# Attribution

Claim D.2.3 of *Transducers*, Part D; formalised by Aristotle (Harmonic),
`PartD/PebReach.lean`.
-/
theorem exists_regular_balancedLang {A B Q : Type} {k : ℕ} [Finite A] [Finite Q]
    (M : Pebble A B Q k) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ k) :
    ∃ L : Language (PairLetter A Q k), L.IsRegular ∧
      ∀ (q₁ q₂ : Q) (x : List ℕ) (p₁ p₂ : ℕ) (w : List A),
        (∀ p ∈ x, p ≤ w.length) → p₁ ≤ w.length → p₂ ≤ w.length → x.length = ℓ - 1 →
        (pairEnc q₁ q₂ (x ++ [p₁]) (x ++ [p₂]) w ∈ L ↔
          BalancedRun M w ℓ (PebbleCfg.conf q₁ (x ++ [p₁])) (PebbleCfg.conf q₂ (x ++ [p₂]))) := by
  obtain ⟨L, hL, hspec⟩ := Transducers.reachability_basic_run (toSrcPeb M) ℓ hℓ1 hℓk
  refine ⟨L, hL, fun q₁ q₂ x p₁ p₂ w h₁ h₂ h₃ h₄ => ?_⟩
  rw [pairEnc_eq, hspec q₁ q₂ x p₁ p₂ w h₁ h₂ h₃ h₄]
  exact balancedRun_toSrcPeb M w ℓ (PebbleCfg.conf q₁ (x ++ [p₁])) (PebbleCfg.conf q₂ (x ++ [p₂]))

/--
---
conclusion: Lax194892.ForOfPebble.isForTransducer_of_isPebbleTransducer
---
Every pebble transducer computes a function of a for-transducer (Theorem
D.2.4, from pebble transducers to for-transducers).

# Proof strategy

The source proves by induction on the number of pebbles that a pebble
transducer computes a polyregular function: the run of the top pebble between
two consecutive configurations of the pebble below is a two-way transducer on
the string representation of that configuration, and the sequence of those
configurations is a marked squaring followed by a regular function
(`PartD/PebblePoly.lean`, `PartD/PebbleSquare*.lean`, `PartD/PebbleTwoWay.lean`);
Theorem D.1.1 then gives a for-transducer (`Transducers.pebble_iff_forTransducer`,
left to right). `isPebbleTransducer_iff` and `isForTransducer_iff` transport
hypothesis and conclusion.

# Attribution

Theorem D.2.4 of *Transducers*, Part D; formalised by Aristotle (Harmonic).
-/
theorem isForTransducer_of_isPebbleTransducer {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsPebbleTransducer f) : IsForTransducer f :=
  (isForTransducer_iff f).2
    ((Transducers.pebble_iff_forTransducer f).1 ((isPebbleTransducer_iff f).1 hf))

/--
---
conclusion: Lax194892.PebbleOfFor.isPebbleTransducer_of_isForTransducer
---
Every for-transducer is simulated by a pebble transducer (Theorem D.2.4, from
for-transducers to pebble transducers): the loop variables become the pebbles,
in nesting order, and the Boolean variables are kept in the state
(`Transducers.PebFor.isPebbleTransducer_of_isForTransducer`,
`PartD/PebbleFor*.lean`).

# Attribution

Theorem D.2.4 of *Transducers*, Part D; formalised by Aristotle (Harmonic).
-/
theorem isPebbleTransducer_of_isForTransducer {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsForTransducer f) : IsPebbleTransducer f :=
  (isPebbleTransducer_iff f).2
    ((Transducers.pebble_iff_forTransducer f).2 ((isForTransducer_iff f).1 hf))

/--
---
conclusion: Lax194892.PebbleIffFor.isPebbleTransducer_iff_isForTransducer
---
Theorem D.2.4 as a biconditional, glued from its two halves taken as
assumptions.
-/
theorem isPebbleTransducer_iff_isForTransducer {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsPebbleTransducer f ↔ IsForTransducer f :=
  ⟨Lax194892.ForOfPebble.isForTransducer_of_isPebbleTransducer,
    Lax194892.PebbleOfFor.isPebbleTransducer_of_isForTransducer⟩

/-! ## Children of a configuration -/

/--
---
conclusion: Lax194892.ChildrenOfConfiguration.exists_forTransducer_children
---
A for-transducer maps the string representation of a configuration to the
concatenation of the representations of its children (Lemma D.2.5),
`Transducers.children_of_configuration_in_pebble_run`: the composition (Lemma
D.1.4) of the for-transducers of Claims D.2.6 and D.2.7.

# Proof strategy

The source states the lemma after Theorems D.1.1 and D.2.4, from which the
for-transducers of the two claims are obtained. The concept's children are the
source's through `isChildSeq_toSrcPeb` (runs staying above a height are
transported by `strictAbove_toSrcPeb`), and the representation of a
configuration unfolds identically (`confEnc_eq`).

# Attribution

Lemma D.2.5 of *Transducers*, Part D; formalised by Aristotle (Harmonic),
`PartD/CGFor.lean`.
-/
theorem exists_forTransducer_children {A B Q : Type} [Finite A] [Finite Q] {k : ℕ}
    (M : Pebble A B Q k) :
    ∃ f : List (ConfLetter A Q k) → List (ConfLetter A Q k), IsForTransducer f ∧
      ∀ (q₀ : Q) (st : List ℕ) (w : List A) (ch : ℕ → Vtx Q) (m : ℕ),
        (∀ p, p ∈ st → p ≤ w.length) → st.length < k →
        IsChildSeq M w q₀ st ch m →
        f (confEnc q₀ st w)
          = ((List.range (m + 1)).map fun t => confEnc (ch t).1 (st ++ [(ch t).2]) w).flatten := by
  obtain ⟨f, hf, hspec⟩ := Transducers.children_of_configuration_in_pebble_run (toSrcPeb M)
  refine ⟨f, (isForTransducer_iff f).2 hf, fun q₀ st w ch m hstb hstk hseq => ?_⟩
  simp only [confEnc_eq]
  exact hspec q₀ st w ch m hstb hstk ((isChildSeq_toSrcPeb M w q₀ st ch m).2 hseq)

/--
---
conclusion: Lax194892.ChildGraphOfConfiguration.exists_forTransducer_childGraph
---
A for-transducer maps the string representation of a configuration to the
representation of its child configuration graph (Claim D.2.6),
`Transducers.from_configuration_to_child_configuration_graph`.

# Proof strategy

The source computes every letter of the child configuration graph by a
rational function: each of its finitely many components — the fixed pebbles,
the first child in the column, and the outgoing and incoming edges of every
state — is a regular property of the input marked at the gap, decided by the
regular languages of Claim D.2.3 (`PartD/CGLang.lean`, `PartD/CGAtom.lean`,
`PartD/CGSem.lean`), and a rational function is a for-transducer by Theorem
D.1.1. The concept's letters form a distinct structure from the source's; the
source's for-transducer is post-composed with the letter-to-letter bijection
`cgLetterOfSrc`, itself a for-transducer (`isForTransducer_map`), and the two
representations agree under the bijection (`cgOfChildren_toSrc`).

# Attribution

Claim D.2.6 of *Transducers*, Part D; formalised by Aristotle (Harmonic),
`PartD/CGFor.lean`.
-/
theorem exists_forTransducer_childGraph {A B Q : Type} [Finite A] [Finite Q] {k : ℕ}
    (M : Pebble A B Q k) :
    ∃ f : List (ConfLetter A Q k) → List (CGLetter A Q k), IsForTransducer f ∧
      ∀ (q₀ : Q) (st : List ℕ) (w : List A) (ch : ℕ → Vtx Q) (m : ℕ) (nid : Fin k),
        (∀ p, p ∈ st → p ≤ w.length) → st.length < k → (nid : ℕ) = st.length →
        IsChildSeq M w q₀ st ch m →
        f (confEnc q₀ st w) = cgOfChildren w st nid ch m := by
  obtain ⟨f, hf, hspec⟩ := Transducers.from_configuration_to_child_configuration_graph (toSrcPeb M)
  refine ⟨fun u => (f u).map cgLetterOfSrc, ?_, fun q₀ st w ch m nid hstb hstk hnid hseq => ?_⟩
  · exact (isForTransducer_iff _).2
      (Transducers.forTransducer_comp hf (isForTransducer_map cgLetterOfSrc))
  · rw [cgOfChildren_eq_map_ofSrc,
      ← hspec q₀ st w ch m nid hstb hstk hnid ((isChildSeq_toSrcPeb M w q₀ st ch m).2 hseq)]
    rfl

/--
---
conclusion: Lax194892.ChildrenOfChildGraph.exists_forTransducer_cgOut
---
A for-transducer maps the string representation of a child configuration graph
to the concatenation of the representations of the children (Claim D.2.7),
`Transducers.from_child_configuration_graph_to_children`.

# Proof strategy

The source's for-transducer is a one-pebble transducer that follows the
recorded edges from the first child, outputting the representation of the
current child at every vertex (`PartD/ChildGraphAut.lean`,
`PartD/ChildGraphRun.lean`), and Theorem D.2.4 makes it a for-transducer; its
correctness rests on a string representing at most one run of children
(`PartD/ChildGraph.lean`). The concept's graphs are transported along the
bijection `cgLetterToSrc` of the alphabets: the local consistency test, the
recorded edges and the output commute with the bijection (`cgOutIs_map_toSrc`),
and the source's for-transducer is pre-composed with it (`isForTransducer_map`).

# Attribution

Claim D.2.7 of *Transducers*, Part D; formalised by Aristotle (Harmonic),
`PartD/ChildGraphFor.lean`.
-/
theorem exists_forTransducer_cgOut {A Q : Type} [Finite A] [Finite Q] (k : ℕ) :
    ∃ f : List (CGLetter A Q k) → List (ConfLetter A Q k),
      IsForTransducer f ∧ ∀ u v, CGOutIs u v → f u = v := by
  obtain ⟨f, hf, hspec⟩ :=
    Transducers.from_child_configuration_graph_to_children (A := A) (Q := Q) k
  refine ⟨fun u => f (u.map cgLetterToSrc), ?_, fun u v huv => ?_⟩
  · exact (isForTransducer_iff _).2
      (Transducers.forTransducer_comp (isForTransducer_map cgLetterToSrc) hf)
  · exact hspec _ v ((cgOutIs_map_toSrc u v).2 huv)

end Lax194892Proofs.Results
