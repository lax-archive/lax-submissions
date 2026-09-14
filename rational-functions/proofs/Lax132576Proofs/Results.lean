import Lax132576.RationalComposition
import Lax132576.RationalContinuity
import Lax132576.RationalEquivalenceUndecidable
import Lax132576.HomomorphismComplement
import Lax132576.UnambiguousOfRational
import Lax132576.BimachineOfRational
import Lax132576.RationalOfBimachine
import Lax132576.RationalUnambiguousBimachine
import Lax132576.EpsilonEliminationExtended
import Lax132576.EpsilonEliminationFinite
import Lax132576.Uniformisation
import Lax132576.PrimesOfRational
import Lax132576.RationalOfPrimes
import Lax132576.RationalPrimes
import Lax132576.RationalMealyCharacterisation
import Lax132576.WeightedEquivalenceDecidable
import Lax132576.RationalEquivalenceDecidable
import Lax132576.WeightedPrecomposition
import Lax132576.RationalOfWeightedPrecomposition
import Lax132576.RationalViaWeighted
import Lax132576.WeightedZeronessDecidable
import Lax132576.MealyMachineIndependent
import Lax132576.MealyDecidable
import Lax132576.LengthPreservingDecidable
import Lax132576.LengthPreservingTyping
import Lax132576.LengthPreservingNormalForm
import Lax132576.SequentialCharacterisation
import Lax132576.SubsequentialCharacterisation
import Lax132576.RationalMachineIndependent
import Lax132576Proofs.Bridge

/-!
The numbered results of Part B of *Transducers*, transported from the ported
source development through `Lax132576Proofs.Bridge` (and Part A's bridge for
the notions of Part A).
-/

namespace Lax132576Proofs.Results

open Lax765601Proofs
open Lax765601.Continuity Lax765601.ElementaryProperties Lax765601.CompositionClosure
  Lax765601.MealyMachine
open Lax132576.LabelledAutomata Lax132576.RationalRelations Lax132576.RationalFunctions
  Lax132576.StringHomomorphisms Lax132576.Bimachines Lax132576.PrimeRationalFunctions
  Lax132576.TransducerCodes Lax132576.WeightedAutomata Lax132576.WeightedCodes
  Lax132576.SequentialTransducers Lax132576.SubsequentialTransducers
  Lax132576.LeftDistance Lax132576.EpsilonFreeAutomata
open Lax132576Proofs.Bridge

/-- The source's Part A bridge, for the notions of Part A. -/
local notation "isMealyA" => Lax765601Proofs.Bridge.isMealy_iff

/--
---
conclusion: Lax132576.RationalComposition.isRationalRel_comp
---
Rational relations are closed under composition (Theorem B.1.4): the product
construction on ε-normalised automata (`Transducers.rationalRel_comp`).

# Attribution

Theorem B.1.4 of *Transducers*; Lean proof by Aristotle (`PartB/RatComp.lean`).
-/
theorem isRationalRel_comp {A B C : Type}
    {R : List A → List B → Prop} {S : List B → List C → Prop}
    (hR : IsRationalRel R) (hS : IsRationalRel S) :
    IsRationalRel (fun w v => ∃ u, R w u ∧ S u v) :=
  (isRationalRel_iff _).2
    (Transducers.rationalRel_comp ((isRationalRel_iff R).1 hR) ((isRationalRel_iff S).1 hS))

/--
---
conclusion: Lax132576.RationalContinuity.relContinuous_of_isRationalRel
---
Rational relations are continuous (Theorem B.1.5), by composition with the
relation of a regular language (`Transducers.rationalRel_continuous`).

# Attribution

Theorem B.1.5 of *Transducers*; Lean proof by Aristotle (`PartB/RatCont.lean`).
-/
theorem relContinuous_of_isRationalRel {A B : Type} {R : List A → List B → Prop}
    (hR : IsRationalRel R) : RelContinuous R :=
  Transducers.rationalRel_continuous ((isRationalRel_iff R).1 hR)

/--
---
conclusion: Lax132576.RationalEquivalenceUndecidable.not_computablePred_codeRel_eq
---
Equivalence of rational relations is undecidable (Theorem B.1.6).

# Proof strategy

The source reduces the Post correspondence problem in index form to the
equality of two coded rational relations (`Transducers.PCP.equivalence_undecidable`,
`PartB/PCPRed.lean`: the two codes describe the complements of the two
homomorphisms of an instance, and are equal exactly when the instance has no
solution). The undecidability of the Post correspondence problem is the
archive statement `Lax251941.PostCorrespondenceIndexUndecidable.not_computablePred_solvable`,
an assumption of this proof. The concept's codes are named structures; the
bridge `relCodeEquiv₂` moves the decision procedure across.

# Attribution

Theorem B.1.6 of *Transducers* (Griffiths); Lean proof by Aristotle.
-/
theorem not_computablePred_codeRel_eq :
    ¬ ComputablePred (fun p : RelCode × RelCode => codeRel p.1 = codeRel p.2) := by
  intro h
  apply Transducers.rationalRel_equivalence_undecidable
  have h' := computablePred_comp h primrec_relCodeEquiv₂_symm.to_comp
  refine h'.of_eq fun p => ?_
  simp only [codeRel_eq, toSrcCode, relCodeEquiv₂, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map, Equiv.apply_symm_apply]

/--
---
conclusion: Lax132576.HomomorphismComplement.isRationalRel_ne_homOf
---
The complement of a homomorphism is rational (Claim B.1.7).

# Attribution

Claim B.1.7 of *Transducers*; Lean proof by Aristotle (`PartB/HomComplement.lean`).
-/
theorem isRationalRel_ne_homOf {A B : Type} [Finite A] [Finite B] (φ : A → List B) :
    IsRationalRel (fun (w : List A) (v : List B) => v ≠ homOf φ w) :=
  (isRationalRel_iff _).2 (Transducers.hom_complement_rational φ)

/--
---
conclusion: Lax132576.UnambiguousOfRational.isUnambiguousRel_of_isRationalFun
---
A rational function is computed by an unambiguous automaton (Theorem B.2.3,
(1) ⇒ (2)), from the uniformisation construction of the source.

# Attribution

Theorem B.2.3 of *Transducers* (Eilenberg); Lean proof by Aristotle
(`PartB/Unambig.lean`, `PartB/Uniform.lean`).
-/
theorem isUnambiguousRel_of_isRationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) : IsUnambiguousRel (fun w v => v = f w) :=
  (isUnambiguousRel_iff _).2
    ((Transducers.rational_iff_unambiguous_iff_bimachine f).out 0 1 |>.1 ((isRationalFun_iff f).1 hf))

/--
---
conclusion: Lax132576.BimachineOfRational.isBimachine_of_isRationalFun
---
A rational function is computed by a bimachine (Theorem B.2.3, (1) ⇒ (3)).

# Attribution

Theorem B.2.3 of *Transducers* (Eilenberg); Lean proof by Aristotle
(`PartB/RatBimach.lean`).
-/
theorem isBimachine_of_isRationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) : IsBimachine f :=
  (isBimachine_iff f).2
    ((Transducers.rational_iff_unambiguous_iff_bimachine f).out 0 2 |>.1 ((isRationalFun_iff f).1 hf))

/--
---
conclusion: Lax132576.RationalOfBimachine.isRationalFun_of_isBimachine
---
A bimachine computes a rational function (Theorem B.2.3, (3) ⇒ (1)).

# Attribution

Theorem B.2.3 of *Transducers*; Lean proof by Aristotle (`PartB/Bimachine.lean`).
-/
theorem isRationalFun_of_isBimachine {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsBimachine f) : IsRationalFun f :=
  (isRationalFun_iff f).2
    ((Transducers.rational_iff_unambiguous_iff_bimachine f).out 2 0 |>.1 ((isBimachine_iff f).1 hf))

/--
---
conclusion: Lax132576.RationalUnambiguousBimachine.tfae_rational_unambiguous_bimachine
---
Eilenberg's theorem as a `TFAE`, glued from the three implications with content,
taken as assumptions, and the trivial (2) ⇒ (1).
-/
theorem tfae_rational_unambiguous_bimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    [IsRationalFun f, IsUnambiguousRel (fun w v => v = f w), IsBimachine f].TFAE := by
  tfae_have 1 → 2 := Lax132576.UnambiguousOfRational.isUnambiguousRel_of_isRationalFun
  tfae_have 2 → 1 := by
    rintro ⟨Q, hQ, M, -, hM⟩
    exact ⟨Q, hQ, M, hM⟩
  tfae_have 1 → 3 := Lax132576.BimachineOfRational.isBimachine_of_isRationalFun
  tfae_have 3 → 1 := Lax132576.RationalOfBimachine.isRationalFun_of_isBimachine
  tfae_finish

/--
---
conclusion: Lax132576.EpsilonEliminationExtended.exists_extended_epsilonFree
---
Elimination of ε-transitions with extended transitions (Lemma B.2.4, first
sentence), the first conjunct of the source's `Transducers.epsilon_elimination`.

# Attribution

Lemma B.2.4 of *Transducers*; Lean proof by Aristotle (`PartB/EpsElim.lean`).
-/
theorem exists_extended_epsilonFree {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) :
    ∃ (Q : Type) (_ : Finite Q) (M : LabAut A (Language B) Q),
      IsExtendedNFAO M ∧ EpsilonFree M ∧ ∀ w v, R w v ↔ extRel M w v := by
  obtain ⟨Q, hQ, M, hext, hfree, hM⟩ :=
    (Transducers.epsilon_elimination ((isRationalRel_iff R).1 hR)).1
  refine ⟨Q, hQ, ofSrc M, ?_, ?_, fun w v => ?_⟩
  · exact (isExtendedNFAO_iff (ofSrc M)).2 hext
  · exact (epsilonFree_iff (ofSrc M)).2 hfree
  · rw [extRel_iff, toSrc_ofSrc]; exact hM w v

/--
---
conclusion: Lax132576.EpsilonEliminationFinite.exists_nfao_epsilonFree
---
Elimination of ε-transitions for finitely valued relations (Lemma B.2.4,
second sentence), the second conjunct of the source's
`Transducers.epsilon_elimination`.

# Attribution

Lemma B.2.4 of *Transducers*; Lean proof by Aristotle (`PartB/EpsElim.lean`).
-/
theorem exists_nfao_epsilonFree {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (hfin : ∀ w, {v | R w v}.Finite) :
    ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), EpsilonFree M ∧ ∀ w v, R w v ↔ M.rel w v := by
  obtain ⟨Q, hQ, M, hfree, hM⟩ :=
    (Transducers.epsilon_elimination ((isRationalRel_iff R).1 hR)).2 hfin
  refine ⟨Q, hQ, ofSrc M, (epsilonFree_iff (ofSrc M)).2 hfree, fun w v => ?_⟩
  rw [rel_iff, toSrc_ofSrc]; exact hM w v

/--
---
conclusion: Lax132576.Uniformisation.exists_isUnambiguousRel_le
---
Uniformisation of total rational relations (Lemma B.2.5): the lexicographically
minimal run of the source's construction.

# Attribution

Lemma B.2.5 of *Transducers*; Lean proof by Aristotle (`PartB/Uniform.lean`).
-/
theorem exists_isUnambiguousRel_le {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (htotal : ∀ w, ∃ v, R w v) :
    ∃ S : List A → List B → Prop, (∀ w v, S w v → R w v) ∧ IsUnambiguousRel S := by
  obtain ⟨S, hle, hS⟩ := Transducers.uniformisation ((isRationalRel_iff R).1 hR) htotal
  exact ⟨S, hle, (isUnambiguousRel_iff S).2 hS⟩

/--
---
conclusion: Lax132576.PrimesOfRational.compClosure_primeRational_of_isRationalFun
---
A rational function decomposes into prime rational functions (Theorem B.2.6,
⇒): the bimachine is run as a separator, two Mealy machines (one right to
left) and a homomorphism (`Transducers.compClosure_of_isBimachine`).

# Attribution

Theorem B.2.6 of *Transducers*; Lean proof by Aristotle (`PartB/BimachPrime.lean`).
-/
theorem compClosure_primeRational_of_isRationalFun {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) : CompClosure PrimeRationalFam A B f :=
  (Lax765601Proofs.Bridge.compClosure_iff primeRationalFam_iff).2
    ((Transducers.rational_iff_prime_composition f).1 ((isRationalFun_iff f).1 hf))

/--
---
conclusion: Lax132576.RationalOfPrimes.isRationalFun_of_compClosure_primeRational
---
A composition of prime rational functions is rational (Theorem B.2.6, ⇐).

# Attribution

Theorem B.2.6 of *Transducers*; Lean proof by Aristotle (`PartB/PrimeRat.lean`).
-/
theorem isRationalFun_of_compClosure_primeRational {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : CompClosure PrimeRationalFam A B f) : IsRationalFun f :=
  (isRationalFun_iff f).2 ((Transducers.rational_iff_prime_composition f).2
    ((Lax765601Proofs.Bridge.compClosure_iff primeRationalFam_iff).1 hf))

/--
---
conclusion: Lax132576.RationalPrimes.isRationalFun_iff_compClosure_primeRational
---
Theorem B.2.6 as a biconditional, glued from its two halves taken as
assumptions.
-/
theorem isRationalFun_iff_compClosure_primeRational {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRationalFun f ↔ CompClosure PrimeRationalFam A B f :=
  ⟨Lax132576.PrimesOfRational.compClosure_primeRational_of_isRationalFun,
    Lax132576.RationalOfPrimes.isRationalFun_of_compClosure_primeRational⟩

/--
---
conclusion: Lax132576.RationalMealyCharacterisation.isMealy_iff_of_isRationalFun
---
Which rational functions are Mealy machines (Theorem B.2.7), through the
machine-independent characterisation of Theorem B.4.1
(`Transducers.rational_isMealy_iff`).

# Attribution

Theorem B.2.7 of *Transducers*; Lean proof by Aristotle
(`PartB/RationalStatements.lean`).
-/
theorem isMealy_iff_of_isRationalFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) : IsMealy f ↔ LengthPreserving f ∧ PrefixDetermined f := by
  rw [isMealyA]
  exact Transducers.rational_isMealy_iff ((isRationalFun_iff f).1 hf)

/-- Transport of a decision procedure on pairs of weighted codes. -/
private lemma wcode_pair_transport (promise P : Transducers.WCode × Transducers.WCode → Prop) :
    DecidableUnderPromise (fun p : WCode × WCode => promise (wcodeEquiv₂ p))
        (fun p => P (wcodeEquiv₂ p)) ↔
      Transducers.DecidableUnderPromise promise P :=
  decidableUnderPromise_equiv wcodeEquiv₂ primrec_wcodeEquiv₂ primrec_wcodeEquiv₂_symm promise P

/-- Transport of a decision procedure on pairs of codes. -/
private lemma relcode_pair_transport (promise P : Transducers.RelCode × Transducers.RelCode → Prop) :
    DecidableUnderPromise (fun p : RelCode × RelCode => promise (relCodeEquiv₂ p))
        (fun p => P (relCodeEquiv₂ p)) ↔
      Transducers.DecidableUnderPromise promise P :=
  decidableUnderPromise_equiv relCodeEquiv₂ primrec_relCodeEquiv₂ primrec_relCodeEquiv₂_symm
    promise P

/--
---
conclusion: Lax132576.WeightedEquivalenceDecidable.decidable_wcodeEval_eq
---
Decidable equivalence of weighted automata over `ℚ` (Theorem B.3.3): the
effective Schützenberger bound (`Transducers.effectiveWeightedBound`) and the
primitive recursive evaluation of a coded automaton
(`Transducers.EffectiveWeightedEvalEq`), assembled in
`Transducers.weighted_equivalence_decidable`; the concept's codes are moved to
the source's tuples by `wcodeEquiv₂`.

# Attribution

Theorem B.3.3 of *Transducers* (Schützenberger); Lean proof by Aristotle
(`PartB/WeightedDec.lean`, `PartB/WeightedBound.lean`, `PartB/WCodePrimrec.lean`).
-/
theorem decidable_wcodeEval_eq :
    DecidableUnderPromise (fun p : WCode × WCode => WCodeValid p.1 ∧ WCodeValid p.2)
      (fun p => wcodeEval p.1 = wcodeEval p.2) := by
  have h := (wcode_pair_transport _ _).2 Transducers.weighted_equivalence_decidable
  simpa only [wcodeValid_iff, wcodeEval_eq] using h

/--
---
conclusion: Lax132576.RationalEquivalenceDecidable.decidable_codeRel_eq
---
Decidable equivalence of rational functions (Theorem B.3.4), by the book's
reduction to Theorem B.3.3 (`Transducers.rationalFun_equivalence_decidable`).

# Attribution

Theorem B.3.4 of *Transducers*; Lean proof by Aristotle (`PartB/RatEqDec.lean`,
`PartB/PairWeighted*.lean`).
-/
theorem decidable_codeRel_eq :
    DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => codeRel p.1 = codeRel p.2) := by
  have h := (relcode_pair_transport _ _).2 Transducers.rationalFun_equivalence_decidable
  simpa only [codeFunctional_iff, codeRel_eq] using h

/--
---
conclusion: Lax132576.WeightedPrecomposition.isWeighted_comp_of_isRationalFun
---
Weighted automata are closed under pre-composition with rational functions
(Lemma B.3.5), by the product with an unambiguous ε-free automaton
(`Transducers.weighted_precomp_rational`).

# Attribution

Lemma B.3.5 of *Transducers*; Lean proof by Aristotle (`PartB/WeightedPrecomp.lean`).
-/
theorem isWeighted_comp_of_isRationalFun {A B S : Type} [Finite A] [Finite B] [Semiring S]
    {f : List A → List B} {h : List B → S} (hf : IsRationalFun f) (hh : IsWeighted h) :
    IsWeighted (h ∘ f) :=
  (isWeighted_iff _).2
    (Transducers.weighted_precomp_rational ((isRationalFun_iff f).1 hf) ((isWeighted_iff h).1 hh))

/--
---
conclusion: Lax132576.RationalOfWeightedPrecomposition.isRationalFun_of_weighted_precomp
---
A function with which every weighted automaton can be pre-composed is rational
(Theorem B.3.6, ⇐), from the source's `Transducers.rational_iff_weighted_precomp`
applied over the semiring of regular languages.

# Attribution

Theorem B.3.6 of *Transducers*; Lean proof by Aristotle (`PartB/WeightedRegular.lean`).
-/
theorem isRationalFun_of_weighted_precomp {A B : Type} [Finite A] [Finite B]
    (f : List A → List B)
    (h : ∀ (S : Type) (_ : Semiring S) (h : List B → S), IsWeighted h → IsWeighted (h ∘ f)) :
    IsRationalFun f :=
  (isRationalFun_iff f).2 ((Transducers.rational_iff_weighted_precomp f).2 fun S inst g hg =>
    (isWeighted_iff _).1 (h S inst g ((isWeighted_iff g).2 hg)))

/--
---
conclusion: Lax132576.RationalViaWeighted.isRationalFun_iff_weighted_precomp
---
Theorem B.3.6 as a biconditional, glued from Lemma B.3.5 and its converse taken
as assumptions.
-/
theorem isRationalFun_iff_weighted_precomp {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔
      ∀ (S : Type) (_ : Semiring S) (h : List B → S), IsWeighted h → IsWeighted (h ∘ f) :=
  ⟨fun hf _ _ _ hh => Lax132576.WeightedPrecomposition.isWeighted_comp_of_isRationalFun hf hh,
    Lax132576.RationalOfWeightedPrecomposition.isRationalFun_of_weighted_precomp f⟩

/--
---
conclusion: Lax132576.WeightedZeronessDecidable.decidable_wcodeEval_eq_zero
---
Decidable zeroness of weighted automata over `ℚ` (Theorem B.3.7), the special
case of equivalence with the empty automaton
(`Transducers.weighted_zeroness_decidable`).

# Attribution

Theorem B.3.7 of *Transducers*; Lean proof by Aristotle (`PartB/WeightedDec.lean`).
-/
theorem decidable_wcodeEval_eq_zero :
    DecidableUnderPromise WCodeValid (fun c => wcodeEval c = 0) := by
  have h := (decidableUnderPromise_equiv wcodeEquiv primrec_toSrcWCode primrec_wcodeEquiv_symm
    _ _).2 Transducers.weighted_zeroness_decidable
  have e1 : (fun a : WCode => Transducers.WCodeValid (wcodeEquiv a)) = WCodeValid :=
    funext fun c => propext (wcodeValid_iff c).symm
  have e2 : (fun a : WCode => Transducers.wcodeEval (wcodeEquiv a) = 0) =
      fun c => wcodeEval c = 0 := by
    funext c
    rw [wcodeEval_eq]
    rfl
  rw [e1, e2] at h
  exact h

/--
---
conclusion: Lax132576.MealyMachineIndependent.isMealy_iff
---
The machine-independent characterisation of Mealy machines (Theorem B.4.1),
`Transducers.isMealy_iff` of the source, through Part A's bridge for `IsMealy`.

# Attribution

Theorem B.4.1 of *Transducers*; Lean proof by Aristotle (`PartB/MealyChar.lean`).
-/
theorem isMealy_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsMealy f ↔ Continuous f ∧ PrefixPreserving f ∧ LengthPreserving f := by
  rw [isMealyA]
  exact Transducers.isMealy_iff f

/--
---
conclusion: Lax132576.MealyDecidable.decidable_isMealy
---
Deciding whether a rational function is a Mealy machine (Theorem B.4.2):
prefix preservation is reduced to the equality of two rational functions
(`PartB/PrefixCodes.lean`), decided by Theorem B.3.4
(`Transducers.rationalFun_isMealy_decidable`).

# Attribution

Theorem B.4.2 of *Transducers*; Lean proof by Aristotle (`PartB/MealyDec.lean`).
-/
theorem decidable_isMealy :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f) := by
  have h := (decidableUnderPromise_equiv relCodeEquiv primrec_toSrcCode primrec_relCodeEquiv_symm
    _ _).2 Transducers.rationalFun_isMealy_decidable
  have e1 : (fun a : RelCode => Transducers.CodeFunctional (relCodeEquiv a)) = CodeFunctional :=
    funext fun c => propext (codeFunctional_iff c).symm
  have e2 : (fun a : RelCode => ∃ f : List ℕ → List ℕ,
      (∀ w, Transducers.CodeWord (relCodeEquiv a) w →
        ∀ v, (Transducers.codeRel (relCodeEquiv a) w v ↔ v = f w)) ∧ Transducers.IsMealy f) =
      fun c => ∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f := by
    funext c
    simp only [codeWord_iff, codeRel_iff, isMealyA, toSrcCode]
  rw [e1, e2] at h
  exact h

/--
---
conclusion: Lax132576.LengthPreservingDecidable.decidable_lengthPreserving
---
Deciding length preservation (Lemma B.4.3): the bounded enumeration of runs of
`PartB/LenDec.lean` (`Transducers.rationalFun_lengthPreserving_decidable`).

# Attribution

Lemma B.4.3 of *Transducers*; Lean proof by Aristotle (`PartB/LenDec.lean`).
-/
theorem decidable_lengthPreserving :
    DecidableUnderPromise CodeFunctional
      (fun c => ∀ w v, codeRel c w v → v.length = w.length) := by
  have h := (decidableUnderPromise_equiv relCodeEquiv primrec_toSrcCode primrec_relCodeEquiv_symm
    _ _).2 Transducers.rationalFun_lengthPreserving_decidable
  have e1 : (fun a : RelCode => Transducers.CodeFunctional (relCodeEquiv a)) = CodeFunctional :=
    funext fun c => propext (codeFunctional_iff c).symm
  have e2 : (fun a : RelCode => ∀ w v, Transducers.codeRel (relCodeEquiv a) w v → v.length = w.length)
      = fun c => ∀ w v, codeRel c w v → v.length = w.length := by
    funext c
    simp only [codeRel_iff, toSrcCode]
  rw [e1, e2] at h
  exact h

/--
---
conclusion: Lax132576.LengthPreservingTyping.lengthPreserving_iff_typing
---
Length preservation through a typing (Claim B.4.4),
`Transducers.lengthPreserving_iff_typing` of the source.

# Attribution

Claim B.4.4 of *Transducers*; Lean proof by Aristotle (`PartB/Typing.lean`).
-/
theorem lengthPreserving_iff_typing {A B Q : Type} (M : NFAO A B Q)
    (hprod : ∀ q, M.Productive q) {f : List A → List B} (hM : ∀ w v, M.rel w v ↔ v = f w) :
    LengthPreserving f ↔
      ∃ τ : Q → ℤ,
        (∀ q ∈ M.init, ∀ ts p, M.Path q ts p →
          ((NFAO.outputOf ts).length : ℤ) = (LabAut.inputOf ts).length + τ p) ∧
        ∀ p ∈ M.final, τ p = 0 := by
  have h := Transducers.lengthPreserving_iff_typing (toSrc M)
    (fun q => (productive_iff M q).1 (hprod q)) (fun w v => ((rel_iff M w v).symm.trans (hM w v)))
  simpa only [path_iff, inputOf_eq, outputOf_eq] using h

/--
---
conclusion: Lax132576.LengthPreservingNormalForm.exists_nfao_length_eq
---
Length preserving rational functions have length preserving automata (Lemma
B.4.5), the free-group construction of the source
(`Transducers.lengthPreserving_rational_normal_form`).

# Attribution

Lemma B.4.5 of *Transducers*; Lean proof by Aristotle (`PartB/LenNormalForm.lean`).
-/
theorem exists_nfao_length_eq {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) (hlen : LengthPreserving f) :
    ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q),
      (∀ t ∈ M.δ, t.2.1.length = t.2.2.1.length) ∧ ∀ w v, M.rel w v ↔ v = f w := by
  obtain ⟨Q, hQ, M, hlen', hM⟩ :=
    Transducers.lengthPreserving_rational_normal_form ((isRationalFun_iff f).1 hf) hlen
  exact ⟨Q, hQ, ofSrc M, hlen', fun w v => by rw [rel_iff, toSrc_ofSrc]; exact hM w v⟩

/--
---
conclusion: Lax132576.SequentialCharacterisation.isSequential_iff
---
The characterisation of sequential functions (Theorem B.4.6),
`Transducers.isSequential_iff` of the source through `isSequential_iff` of
the bridge.

# Attribution

Theorem B.4.6 of *Transducers* (Ginsburg and Rose); Lean proof by Aristotle
(`PartB/SeqChar.lean`).
-/
theorem isSequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSequential f ↔
      f [] = [] ∧ Continuous f ∧ PrefixPreserving f ∧
        ∃ K : ℕ, ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K := by
  rw [Bridge.isSequential_iff]
  exact Transducers.isSequential_iff f

/--
---
conclusion: Lax132576.SubsequentialCharacterisation.isSubsequential_iff
---
The characterisation of subsequential functions (Theorem B.4.8),
`Transducers.isSubsequential_iff` of the source.

# Attribution

Theorem B.4.8 of *Transducers* (Choffrut); Lean proof by Aristotle
(`PartB/Subseq*.lean`).
-/
theorem isSubsequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → Option (List B)) :
    IsSubsequential f ↔ PartialContinuous f ∧ BoundedVariation f := by
  rw [Bridge.isSubsequential_iff]
  exact Transducers.isSubsequential_iff f

/--
---
conclusion: Lax132576.RationalMachineIndependent.isRationalFun_iff
---
The machine-independent characterisation of rational functions (Theorem
B.4.13), `Transducers.isRationalFun_iff` of the source.

# Attribution

Theorem B.4.13 of *Transducers* (Reutenauer and Schützenberger); Lean proof by
Aristotle (`PartB/RatIndex.lean`, `PartB/RatAnnot.lean`).
-/
theorem isRationalFun_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsRationalFun f ↔
      Continuous f ∧ {C : Set (List A) | ∃ w₁, C = {w₂ | BoundedVarRel f w₁ w₂}}.Finite := by
  rw [Bridge.isRationalFun_iff]
  exact Transducers.isRationalFun_iff f

end Lax132576Proofs.Results
