/- Part B: Rational relations and rational functions (Sections *Rational relations* and *Rational
functions*)
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Sections *Rational relations* to *Rational functions* and the
statements of their theorems, lemmas and claims.  The proofs are in the supporting files
(`RatComp.lean`, `RatCont.lean`, `HomComplement.lean`, `EpsElim.lean`, `Unambig.lean`,
`Uniform.lean`, `Bimachine.lean`, `RatBimach.lean`, `PrimeRat.lean`, `BimachPrime.lean`, ...).
Every result of these sections is proved; Theorem `thm:undecidable-equivalence-rational-relations`
is proved from the undecidability of the Post correspondence problem, which it takes as an explicit
argument, and `THEOREMS.md` records that.  No file of Part B contains a `sorry`. -/
import Lax765601Proofs.Source.PartA.Statements
import Lax132576Proofs.Source.PCP.Index
import Lax132576Proofs.Source.PartB.RatComp
import Lax132576Proofs.Source.PartB.RatCont
import Lax132576Proofs.Source.PartB.HomComplement
import Lax132576Proofs.Source.PartB.MealyChar
import Lax132576Proofs.Source.PartB.EpsElim
import Lax132576Proofs.Source.PartB.Uniform
import Lax132576Proofs.Source.PartB.Bimachine
import Lax132576Proofs.Source.PartB.RatBimach
import Lax132576Proofs.Source.PartB.BimachPrime
import Lax132576Proofs.Source.PartB.PCPRed
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-! ## Automata with labelled transitions

The definitions of automata with labelled transitions (`LabAut`), of nondeterministic automata with
output (Definition `def:nfa-with-output`, `NFAO`), of rational relations (Definition
`def:rational-relation`) and of rational functions (Definition `def:rational-function`) are
in `RequestProject/PartB/LabAut.lean`, so that the constructions used in the proofs below can be
developed before the statements of the numbered results. -/

/-! ### Composition and continuity -/

/-- **Theorem `thm:composition-rational-relations`.**  Rational relations are closed under
relational composition. -/
theorem rationalRel_comp {A B C : Type}
    {R : List A → List B → Prop} {S : List B → List C → Prop}
    (hR : IsRationalRel R) (hS : IsRationalRel S) :
    IsRationalRel (fun w v => ∃ u, R w u ∧ S u v) :=
  rationalRel_comp_aux hR hS

/-- **Theorem `thm:continuity-rational-relations`.**  The inverse image of a regular language under
a rational relation is regular; that is, rational relations are continuous. -/
theorem rationalRel_continuous {A B : Type}
    {R : List A → List B → Prop} (hR : IsRationalRel R) : RelContinuous R :=
  rationalRel_continuous_aux hR

/-! ### Undecidable equivalence

Decidability statements are formalised by means of Mathlib's notion of a
computable function.  A rational relation over the alphabet `ℕ` (every relation
over a finite alphabet can be presented this way) is described by a *code*: a
finite list of transitions together with the lists of initial and final
states. -/

/-! The code of an automaton (`RelCode`), the automaton and the relation that it
describes (`codeAut`, `codeRel`), the promise that this relation is a function
(`CodeFunctional`, totality on the strings over the alphabet of the code: see
`not_codeTotalFunctional` for why totality on all of `ℕ*` cannot be used) and
the formalisation of decidability under a promise
(`DecidableUnderPromise`) are defined in `RequestProject/PartB/Codes.lean`, so
that the reduction from the Post correspondence problem
(`RequestProject/PartB/PCPRed.lean`) can be developed before the statements of
the numbered results. -/

/-- **Theorem `thm:undecidable-equivalence-rational-relations`.**  The equivalence problem `R = S`
is undecidable for rational relations.

As is customary, undecidability is proved by a reduction from the Post
correspondence problem: no algorithm decides, given a finite list of pairs of
strings, whether some nonempty sequence of indices makes the two concatenations
equal (`Transducers.PCP.Solvable`).  That undecidability used to be taken here as
an explicit hypothesis; it is now itself proved, as
`Transducers.PCP.solvable_not_computablePred`
(`RequestProject/PCP/Index.lean`), so this theorem is unconditional.  The
reduction proper is `PCP.equivalence_undecidable`, which still takes the
undecidability of the Post correspondence problem as an argument, since that is
what a reduction is. -/
theorem rationalRel_equivalence_undecidable :
    ¬ ComputablePred (fun p : RelCode × RelCode => codeRel p.1 = codeRel p.2) :=
  PCP.equivalence_undecidable PCP.solvable_not_computablePred

/-- **Claim `claim:homomorphism-complement-rational`.**  If `h : A* → B*` is a homomorphism, then
its complement `{(w, v) | v ≠ h w}` is a rational relation. -/
theorem hom_complement_rational {A B : Type} [Finite A] [Finite B] (φ : A → List B) :
    IsRationalRel (fun (w : List A) (v : List B) => v ≠ homOf φ w) :=
  hom_complement_rational_aux φ

/-! ## Rational functions -/

/-! ### Bimachines -/

/-! **Definition `def:bimachine` (Bimachine).**  The definition of a bimachine
(`Bimachine`), of its semantics (`Bimachine.eval`) and of the functions that
bimachines compute (`IsBimachine`, `IsAperiodicBimachine`) is in
`RequestProject/PartB/Bimachine.lean`, together with the proof that these functions are
rational. -/

/-- **Theorem `thm:bimachines`.**  For a string-to-string function the following are
equivalent: (1) it is a rational relation which happens to be functional;
(2) it is computed by an unambiguous nfa with output; (3) it is computed by a
bimachine. -/
theorem rational_iff_unambiguous_iff_bimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    [IsRationalFun f,
     IsUnambiguousRel (fun w v => v = f w),
     IsBimachine f].TFAE := by
  tfae_have 1 → 2 := by
    intro hf
    obtain ⟨P, hP, N, hunamb, -, hrel⟩ := exists_unambiguous_aut_of_rationalFun hf
    exact ⟨P, hP, N, hunamb, fun w v => (hrel w v).symm⟩
  tfae_have 2 → 1 := by
    rintro ⟨P, hP, N, -, hrel⟩
    exact ⟨P, hP, N, hrel⟩
  tfae_have 1 → 3 := isBimachine_of_rationalFun
  tfae_have 3 → 1 := rationalFun_of_isBimachine
  tfae_finish

/-- An automaton with *extended transitions*: transitions are labelled by an input string and a
regular language of output strings (used in Lemma `lemma:eliminate-epsilon-transitions`). -/
def IsExtendedNFAO {A B Q : Type} (M : LabAut A (Language B) Q) : Prop :=
  ∀ t ∈ M.δ, Language.IsRegular t.2.2.1

/-- The relation computed by an automaton with extended transitions: the output
is any string in the concatenation of the languages along an accepting path. -/
def extRel {A B Q : Type} (M : LabAut A (Language B) Q) (w : List A) (v : List B) : Prop :=
  ∃ ts, M.Accepting ts ∧ LabAut.inputOf ts = w ∧ v ∈ (LabAut.labelsOf ts).prod

/-- The normal form of Lemma `lemma:eliminate-epsilon-transitions`: in every accepting run, either
the input is nonempty and each transition inputs exactly one letter, or the input is empty and the
run consists of exactly one transition. -/
def EpsilonFree {A L Q : Type} (M : LabAut A L Q) : Prop :=
  ∀ ts, M.Accepting ts →
    (LabAut.inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧
    (LabAut.inputOf ts = [] → ts.length = 1)

/-- **Lemma `lemma:eliminate-epsilon-transitions` (Elimination of ε-transitions).**  Every rational
relation can be computed by an nfa with output and extended transitions in which every accepting run
is in the normal form described by `EpsilonFree`.  Furthermore, if every input string has finitely
many outputs, then extended transitions are not needed. -/
theorem epsilon_elimination {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) :
    (∃ (Q : Type) (_ : Finite Q) (M : LabAut A (Language B) Q),
        IsExtendedNFAO M ∧ EpsilonFree M ∧ ∀ w v, R w v ↔ extRel M w v) ∧
      ((∀ w, {v | R w v}.Finite) →
        ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q),
          EpsilonFree M ∧ ∀ w v, R w v ↔ M.rel w v) :=
  epsilon_elimination_aux hR

/-- **Lemma `lem:uniformisation` (Uniformisation).**  If a rational relation is total, then it
contains an unambiguous rational relation. -/
theorem uniformisation {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (htotal : ∀ w, ∃ v, R w v) :
    ∃ S : List A → List B → Prop, (∀ w v, S w v → R w v) ∧ IsUnambiguousRel S :=
  uniformisation_aux hR htotal

/-! ### Decomposition into primes -/

/-! The family of **prime rational functions** `PrimeRationalFam`
(Theorem `thm:rational-primes`) — prime Mealy machines, their right-to-left variants, string
homomorphisms, and the function `w ↦ w#` appending a fresh separator — is
defined in `RequestProject/PartB/PrimeRat.lean`. -/

/-- **Theorem `thm:rational-primes`.**  A string-to-string function is rational if and only if
it can be obtained by composing prime rational functions. -/
theorem rational_iff_prime_composition {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔ CompClosure PrimeRationalFam A B f := by
  constructor
  · intro hf
    exact compClosure_of_isBimachine (isBimachine_of_rationalFun hf)
  · intro hf
    exact PrimeRat.rationalFun_of_compClosure hf inferInstance inferInstance

/-! ### Mealy machines as a subset of the rational functions -/

/-- A rational function is continuous, by Theorem `thm:continuity-rational-relations`. -/
lemma continuous_of_isRationalFun {A B : Type} {f : List A → List B} (hf : IsRationalFun f) :
    Continuous f := by
  intro L hL
  have h := rationalRel_continuous hf L hL
  convert h using 2 with w
  simp

/-- For a prefix and length preserving function, the first `n` letters of the
output only depend on the first `n` letters of the input. -/
lemma take_eq_take_of_prefix {A B : Type} {f : List A → List B} (hpre : PrefixPreserving f)
    (hlen : LengthPreserving f) (w : List A) (n : ℕ) :
    (f (w.take n)).take n = (f w).take n := by
  have hprefix : w.take n <+: w := List.take_prefix n w
  have hprefix' : f (w.take n) <+: f w := hpre _ _ hprefix
  have hlen' : (f (w.take n)).length = (w.take n).length := hlen _
  -- Case split on whether n ≤ w.length
  by_cases h : n ≤ w.length
  · -- Case n ≤ w.length: (w.take n).length = n
    have hlen'' : (w.take n).length = n := List.length_take_of_le h
    have hlen''' : (f (w.take n)).length = n := by rw [hlen, hlen'']
    -- Left side: (f (w.take n)).take n = f (w.take n) since length = n
    have lhs : (f (w.take n)).take n = f (w.take n) := by
      have : (f (w.take n)).length ≤ n := hlen'''.le
      rw [List.take_of_length_le this]
    rw [lhs]
    -- Right side: (f w).take n = f (w.take n) since f (w.take n) <+: f w and length = n
    have rhs : (f w).take n = f (w.take n) := by
      rcases hprefix' with ⟨t, ht⟩
      have h : (f w).take (f (w.take n)).length = f (w.take n) := by
        rw [← ht]
        simp
      rwa [hlen'''] at h
    rw [rhs]
  · -- Case n > w.length: w.take n = w
    push_neg at h
    have hw : w.take n = w := by simp [le_of_lt h]
    rw [hw]

/-- Length preservation together with the determinism condition of
Theorem `thm:rational-is-mealy-characterisation` implies prefix preservation. -/
lemma prefixPreserving_of_take {A B : Type} {f : List A → List B} (hlen : LengthPreserving f)
    (htake : ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n) :
    PrefixPreserving f := by
  intro w v hwv
  have hlenw : (f w).length = w.length := hlen w
  rcases hwv with ⟨t, rfl⟩
  have htake_eq : w.take w.length = (w ++ t).take w.length := by simp
  have h := htake w (w ++ t) w.length htake_eq
  rw [← hlenw] at h
  have h1 : (f w).take (f w).length = f w := List.take_length (l := f w)
  rw [h1] at h
  exact h.symm ▸ List.take_prefix (l := f (w ++ t)) (i := (f w).length)

/-- **Theorem `thm:rational-is-mealy-characterisation`.**  A rational function is computed by a
Mealy machine if and only if it is length preserving and deterministic in the sense that input
strings agreeing on the first `n` letters have outputs agreeing on the first `n` letters. -/
theorem rational_isMealy_iff {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) :
    IsMealy f ↔
      (LengthPreserving f ∧
        ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n) := by
  have hchar := isMealy_iff_aux (A := A) (B := B) f
  constructor
  · intro hM
    obtain ⟨hcont, hpre, hlen⟩ := hchar.1 hM
    refine ⟨hlen, fun w v n hwv => ?_⟩
    rw [← take_eq_take_of_prefix hpre hlen w n, ← take_eq_take_of_prefix hpre hlen v n, hwv]
  · rintro ⟨hlen, htake⟩
    exact hchar.2
      ⟨continuous_of_isRationalFun hf, prefixPreserving_of_take hlen htake, hlen⟩

end Lax132576Proofs.Transducers
