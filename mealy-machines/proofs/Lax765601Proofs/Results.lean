import Lax765601.MealyEquivalenceBound
import Lax765601.MealyComposition
import Lax765601.MealyContinuity
import Lax765601.KrohnRhodes
import Lax765601.MapLiftingDecomposition
import Lax765601.StateTransformationDecomposition
import Lax765601.ReversibleComposition
import Lax765601.AperiodicOfFlipFlops
import Lax765601.FlipFlopsOfAperiodic
import Lax765601.AperiodicMealy
import Lax765601.AperiodicPumping
import Lax765601.MealyDerivatives
import Lax765601.AperiodicityMinimalMachine
import Lax765601Proofs.Bridge

/-!
The numbered results of Part A of *Transducers*, each transported from the
ported source development through the bridge of `Lax765601Proofs.Bridge`.
-/

namespace Lax765601Proofs.Results

open Lax765601.Continuity Lax765601.ElementaryProperties Lax765601.CompositionClosure
  Lax765601.MealyMachine Lax765601.StateTransformations Lax765601.PrimeMealyMachines
  Lax765601.MapLifting Lax765601.Aperiodicity Lax765601.Derivatives
open Lax765601Proofs.Bridge

/--
---
conclusion: Lax765601.MealyEquivalenceBound.eval_eq_iff_short
---
Two Mealy machines are equivalent if and only if they agree on all inputs of
length at most the product of their numbers of states (Theorem A.1.2).

# Proof strategy

The source theorem `Transducers.mealy_equiv_iff_bounded` proves the finite
check for `Fintype` state spaces and `Fintype.card`: a pair of runs of the two
machines that repeats a pair of states can be shortened by cutting out the loop
without removing a disagreement, so a shortest disagreeing input has length at
most `|Q₁|·|Q₂|`. The bridge moves between the concept machine and the source
machine (`eval_toSrc`) and between `Nat.card` and `Fintype.card`.

# Attribution

Theorem A.1.2 of *Transducers* (M. Bojańczyk); the Lean proof is Aristotle's,
in `RequestProject/PartA/Statements.lean`.
-/
theorem eval_eq_iff_short {A B Q₁ Q₂ : Type} [Finite Q₁] [Finite Q₂]
    (M : Mealy A B Q₁) (N : Mealy A B Q₂) :
    M.eval = N.eval ↔
      ∀ w : List A, w.length ≤ Nat.card Q₁ * Nat.card Q₂ → M.eval w = N.eval w := by
  letI := Fintype.ofFinite Q₁
  letI := Fintype.ofFinite Q₂
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h := Transducers.mealy_equiv_iff_bounded (toSrc M) (toSrc N)
  simpa only [eval_toSrc] using h

/--
---
conclusion: Lax765601.MealyComposition.isMealy_comp
---
Mealy machines are closed under composition (Theorem A.1.3), by the product
construction `Transducers.Mealy.compose` of the source, transported through
`isMealy_iff`.

# Attribution

Theorem A.1.3 of *Transducers*; Lean proof by Aristotle
(`Transducers.mealy_comp`).
-/
theorem isMealy_comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C}
    (hf : IsMealy f) (hg : IsMealy g) : IsMealy (g ∘ f) :=
  (isMealy_iff _).2 (Transducers.mealy_comp ((isMealy_iff f).1 hf) ((isMealy_iff g).1 hg))

/--
---
conclusion: Lax765601.MealyContinuity.continuous_of_isMealy
---
Mealy machines are continuous (Theorem A.1.4): the product of the machine with a
deterministic automaton for the output language recognises the inverse image
(`Transducers.Mealy.dfaComp` in the source).

# Attribution

Theorem A.1.4 of *Transducers*; Lean proof by Aristotle
(`Transducers.mealy_continuous`).
-/
theorem continuous_of_isMealy {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsMealy f) : Continuous f :=
  Transducers.mealy_continuous ((isMealy_iff f).1 hf)

/--
---
conclusion: Lax765601.KrohnRhodes.compClosure_primeMealy_of_isMealy
---
The Krohn–Rhodes theorem (Theorem A.2.2): every Mealy machine is a composition
of reversible and flip-flop machines.

# Proof strategy

The source follows the book: the state transformations of the prefixes of the
input are computed by a composition of primes (Lemma A.2.5,
`Transducers.stateTransTransducer_prime_decomposition`, an induction on the
number of states and on the number of letters whose state transformation is not
a permutation, the letter `a` of the induction step being made to act as the
identity rather than removed from the alphabet), they are paired with the input
letters, and the output is produced by a flip-flop delay machine. The bridge
transports the family of primes and the composition closure
(`compClosure_iff`).

# Attribution

Theorem A.2.2 of *Transducers* (the Krohn–Rhodes theorem, in the form the book
proves); Lean proof by Aristotle (`Transducers.krohn_rhodes`,
`RequestProject/PartA/StateTrans.lean`).
-/
theorem compClosure_primeMealy_of_isMealy {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMealy f) : CompClosure PrimeMealyFam A B f :=
  (compClosure_iff primeMealyFam_iff).2 (Transducers.krohn_rhodes ((isMealy_iff f).1 hf))

/--
---
conclusion: Lax765601.MapLiftingDecomposition.compClosure_mapLift
---
Map lifting preserves decompositions into primes (Lemma A.2.4): the source proves
it for a single prime — a flip-flop is reset at the separator, a reversible
machine goes through the cancellation law of the book — and extends it along the
composition tree.

# Attribution

Lemma A.2.4 of *Transducers*; Lean proof by Aristotle
(`Transducers.mapLift_prime_decomposition`, `RequestProject/PartA/MapLift.lean`).
-/
theorem compClosure_mapLift {A B : Type} [Finite A] {f : List A → List B}
    (hf : CompClosure PrimeMealyFam A B f) :
    CompClosure PrimeMealyFam (Option A) (Option B) (mapLift f) := by
  rw [mapLift_eq]
  exact (compClosure_iff primeMealyFam_iff).2
    (Transducers.mapLift_prime_decomposition ((compClosure_iff primeMealyFam_iff).1 hf))

/--
---
conclusion: Lax765601.StateTransformationDecomposition.compClosure_stateTransTransducer
---
The state transformation transducer of a pre-automaton is a composition of
primes (Lemma A.2.5): the induction of the book on the number of states and,
for a tie, on the number of letters whose state transformation is not a
permutation, with the tripartite decomposition of the input into the first
`a`-block, the middle blocks and the `a`-free suffix.

# Attribution

Lemma A.2.5 of *Transducers*; Lean proof by Aristotle
(`Transducers.stateTransTransducer_prime_decomposition`,
`RequestProject/PartA/StateTrans.lean`).
-/
theorem compClosure_stateTransTransducer {A Q : Type} [Finite A] [Finite Q] (δ : Q → A → Q) :
    CompClosure PrimeMealyFam A (Q → Q) (stateTransTransducer δ).eval := by
  rw [← eval_toSrc]
  exact (compClosure_iff primeMealyFam_iff).2
    (Transducers.stateTransTransducer_prime_decomposition δ)

/--
---
conclusion: Lax765601.ReversibleComposition.isReversibleMealy_comp
---
Reversible Mealy machines are closed under composition (Lemma A.2.6): the
product machine is reversible in each coordinate.

# Attribution

Lemma A.2.6 of *Transducers*; Lean proof by Aristotle
(`Transducers.reversible_comp`).
-/
theorem isReversibleMealy_comp {A B C : Type} [Finite B]
    {f : List A → List B} {g : List B → List C}
    (hf : IsReversibleMealy f) (hg : IsReversibleMealy g) : IsReversibleMealy (g ∘ f) :=
  (isReversibleMealy_iff _).2
    (Transducers.reversible_comp ((isReversibleMealy_iff f).1 hf) ((isReversibleMealy_iff g).1 hg))

/--
---
conclusion: Lax765601.AperiodicOfFlipFlops.aperiodic_of_compClosure_flipFlop
---
A composition of flip-flops is aperiodic (the easy half of Theorem A.2.8): a
flip-flop satisfies the stabilisation condition, hence the pumping property of
Claim A.2.9, and the pumping property is preserved by composition.

# Attribution

Theorem A.2.8 of *Transducers*, right-to-left; Lean proof by Aristotle
(`Transducers.flipflop_composition_aperiodic`).
-/
theorem aperiodic_of_compClosure_flipFlop {A B : Type} {f : List A → List B}
    (hf : CompClosure FlipFlopFam A B f) : Aperiodic f :=
  (aperiodic_iff f).2
    (Transducers.flipflop_composition_aperiodic ((compClosure_iff flipFlopFam_iff).1 hf))

/--
---
conclusion: Lax765601.FlipFlopsOfAperiodic.compClosure_flipFlop_of_aperiodic
---
An aperiodic Mealy function is a composition of flip-flops (the hard half of
Theorem A.2.8): by Lemma A.2.11 some machine computing it satisfies the
stabilisation condition (*), and the Krohn–Rhodes construction run for that
machine only produces flip-flops (`Transducers.krohn_rhodes_flipFlop`, from
`RequestProject/PartA/StateTransAperiodic.lean`).

# Attribution

Theorem A.2.8 of *Transducers*, left-to-right; Lean proof by Aristotle
(`Transducers.aperiodic_iff_flipflop_composition`).
-/
theorem compClosure_flipFlop_of_aperiodic {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMealy f) (ha : Aperiodic f) :
    CompClosure FlipFlopFam A B f :=
  (compClosure_iff flipFlopFam_iff).2
    ((Transducers.aperiodic_iff_flipflop_composition ((isMealy_iff f).1 hf)).1
      ((aperiodic_iff f).1 ha))

/--
---
conclusion: Lax765601.AperiodicMealy.aperiodic_iff_compClosure_flipFlop
---
Theorem A.2.8 as a biconditional, glued from its two halves: the statements
`FlipFlopsOfAperiodic` and `AperiodicOfFlipFlops` are its assumptions.
-/
theorem aperiodic_iff_compClosure_flipFlop {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔ CompClosure FlipFlopFam A B f :=
  ⟨fun ha => Lax765601.FlipFlopsOfAperiodic.compClosure_flipFlop_of_aperiodic hf ha,
    Lax765601.AperiodicOfFlipFlops.aperiodic_of_compClosure_flipFlop⟩

/--
---
conclusion: Lax765601.AperiodicPumping.aperiodic_iff_pumping
---
Aperiodicity of a Mealy function is the pumping property of Claim A.2.9. The
source proves the pumping property from the stabilisation condition of Lemma
A.2.11 (`Transducers.transStabilises_pumping`) and the converse directly.

# Attribution

Claim A.2.9 of *Transducers*; Lean proof by Aristotle
(`Transducers.aperiodic_iff_pumping`).
-/
theorem aperiodic_iff_pumping {A B : Type} {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔
      ∀ u v w : List A, ∃ (x y z : List B) (k : ℕ), ∀ n > 0,
        f (u ++ npow v (n + k) ++ w) = x ++ npow y n ++ z := by
  rw [aperiodic_iff]
  simp only [npow_eq]
  exact Transducers.aperiodic_iff_pumping ((isMealy_iff f).1 hf)

/--
---
conclusion: Lax765601.MealyDerivatives.isMealy_iff
---
The Myhill–Nerode lemma for Mealy machines (Lemma A.2.10). From a machine, the
derivative after `w` is the run from the state reached after `w`; conversely the
source builds the minimal machine `Transducers.derivMealy` on the finitely many
derivatives, its transition from `f(w_)` on `a` outputting the first letter of
`f(w_)(a)` and moving to `f(wa_)`.

# Attribution

Lemma A.2.10 of *Transducers*; Lean proof by Aristotle
(`Transducers.myhill_nerode_mealy`).
-/
theorem isMealy_iff_derivatives {A B : Type} (f : List A → List B) :
    IsMealy f ↔ (Set.range (deriv f)).Finite ∧ LengthPreserving f ∧ PrefixDetermined f := by
  rw [isMealy_iff, Transducers.myhill_nerode_mealy, range_deriv_eq]
  exact Iff.rfl

/--
---
conclusion: Lax765601.AperiodicityMinimalMachine.aperiodic_iff_transAperiodic
---
A Mealy function is aperiodic if and only if some machine computing it satisfies
the stabilisation condition (*) (Lemma A.2.11). The source constructs the
minimal machine on the derivatives and shows that aperiodicity makes its
state transformations stabilise; conversely (*) gives the pumping property.

# Attribution

Lemma A.2.11 of *Transducers*; Lean proof by Aristotle
(`Transducers.aperiodic_iff_transStabilises`).
-/
theorem aperiodic_iff_transAperiodic {A B : Type} {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔
      ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ TransAperiodic M.transFun := by
  rw [aperiodic_iff]
  constructor
  · intro h
    obtain ⟨Q, hQ, M, hM, hs⟩ :=
      (Transducers.aperiodic_iff_transStabilises ((isMealy_iff f).1 hf)).1 h
    exact ⟨Q, hQ, ofSrc M, by rw [eval_ofSrc, hM], hs⟩
  · rintro ⟨Q, hQ, M, hM, hs⟩
    exact (Transducers.aperiodic_iff_transStabilises ((isMealy_iff f).1 hf)).2
      ⟨Q, hQ, toSrc M, by rw [eval_toSrc, hM], hs⟩

end Lax765601Proofs.Results
