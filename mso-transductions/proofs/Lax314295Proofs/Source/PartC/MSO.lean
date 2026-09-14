/-
Part C, Section *Logic*: Logic
  from *Transducers* (M. Bojańczyk, June 25, 2026).

The numbered results of Section *Logic* that are proved: Theorem `thm:mso-logic-languages`, Lemma
`lem:mso-free-variables`, Theorem `thm:logic-rational-functions`, Claim
`claim:mso-annotation-regular`, Theorem `thm:logic-regular-functions`, Lemma
`lem:logic-precomputation`, Theorem `thm:logic-aperiodic`, Lemma
`lem:k-types-fo-equivalence`, Lemma `lem:k-types-properties` and Theorem
`thm:fo-rational-functions`.  Every proof in this file is complete.

The definitions they speak about (monadic second-order logic, mso relabellings,
mso transductions and the first-order fragment) are in
`RequestProject/PartC/MSODef.lean`, the constructions used in their proofs in
`RequestProject/PartC/MSOSyntax.lean`, `RequestProject/PartC/RegAut.lean`,
`RequestProject/PartC/MSOAnnot.lean`, `RequestProject/PartC/MSOBuchi.lean`,
`RequestProject/PartC/MSORelab.lean`, `RequestProject/PartC/KTypes.lean`,
`RequestProject/PartC/MarkStr.lean`, `RequestProject/PartC/MarkLogic.lean`,
`RequestProject/PartC/MarkBimach.lean`, `RequestProject/PartC/MarkDelay.lean`,
`RequestProject/PartC/MSORatRelab.lean` and
`RequestProject/PartC/MSOPrecomp.lean`.

Theorem `thm:logic-aperiodic` and Lemma `lem:k-types-fo-equivalence` are proved below,
out of `RequestProject/PartC/FORel.lean`, `RequestProject/PartC/FOSeg.lean`,
`RequestProject/PartC/FOComp.lean`, `RequestProject/PartC/FORename.lean`,
`RequestProject/PartC/FOHintikka.lean`, `RequestProject/PartC/FOTypeDFA.lean`,
`RequestProject/PartC/FOSubstRel.lean`, `RequestProject/PartC/FOFlipFlop.lean` and
`RequestProject/PartC/FOMealy.lean`.

Theorem `thm:fo-rational-functions` is proved below, out of `RequestProject/PartC/FORev.lean`,
`RequestProject/PartC/FOPos.lean`, `RequestProject/PartC/FORelabBimach.lean`
(first-order relabellings are computed by aperiodic bimachines) and
`RequestProject/PartC/FOBimachRelab.lean` (the converse).

Theorem `nolabel:thm-fo-transduction-into-primes` has been removed from the formalised theorems at
the user's request; its statement is kept only as a comment in `RequestProject/PartC/MSOOpen.lean`,
which this file still imports.  No result of Section *Logic* is left unproved.

Claim `claim:transition-formula`, Lemma `lem:logic-reduction-to-type-n` and Claim
`claim:fo-composition-quantifier-rank` are internal steps of the proofs of Theorems
`thm:logic-rational-functions`, `thm:logic-regular-functions` and Lemma
`lem:k-types-fo-equivalence`, so they are not stated here as numbered results of their own; each of
them is nevertheless formalised, as `Transducers.RatRelab.exists_form`
(`RequestProject/PartC/MSORatRelab.lean`), `Transducers.MSOTransduction.exists_norm`
(`RequestProject/PartC/MSONorm.lean`) and `Transducers.sat_iff_of_kEquiv`
(`RequestProject/PartC/FOComp.lean`). -/
import Lax916827Proofs.Source.PartC.Statements
import Lax916827Proofs.Source.PartC.MSOBuchi
import Lax314295Proofs.Source.PartC.MSORelab
import Lax314295Proofs.Source.PartC.MSOOpen
import Lax314295Proofs.Source.PartC.MSORatRelab
import Lax314295Proofs.Source.PartC.MSOPrecomp
import Lax314295Proofs.Source.PartC.MSOReg
import Lax314295Proofs.Source.PartC.FOHintikka
import Lax314295Proofs.Source.PartC.FOTypeDFA
import Lax314295Proofs.Source.PartC.FOMealy
import Lax314295Proofs.Source.PartC.FORelabBimach
import Lax314295Proofs.Source.PartC.FOBimachRelab
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

/-! ## Monadic second-order logic -/

/-- **Theorem `thm:mso-logic-languages`.**  A language is regular if and only if it is definable in
monadic second-order logic. -/
theorem regular_iff_msoDefinable {A : Type} [Finite A] (L : Language A) :
    L.IsRegular ↔ MSODefinable L :=
  regular_iff_msoDefinable_aux L

/-- **Lemma `lem:mso-free-variables`.**  For an mso formula whose free variables are among
`x₁, …, x_k, X₁, …, X_l`, the set of annotated strings that satisfy it is a
regular language over the alphabet `A × 2^{k+l}`. -/
theorem mso_annotated_regular {A : Type} [Finite A] (φ : MSO A) (k l : ℕ)
    (hfo : φ.freeFO ⊆ {i | i < k}) (hso : φ.freeSO ⊆ {j | j < l}) :
    Language.IsRegular
      {u : List (A × (Fin k → Bool) × (Fin l → Bool)) |
        ∃ (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate k l w fo so ∧ MSO.Sat w (extFO k fo) (extSO l so) φ} :=
  mso_annotated_regular_aux φ k l hfo hso

/-! ## Rational functions in terms of logic -/

/-- **Theorem `thm:logic-rational-functions`.**  A string-to-string function is rational if and only
if it is definable by an mso relabelling. -/
theorem rational_iff_msoRelabelling {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRationalFun f ↔ IsMSORelabelling f :=
  rational_iff_msoRelabelling_aux f

/-- **Lemma `lem:logic-precomputation`.**  For a finite set of mso formulas with one or two free
first-order variables there is a letter-to-letter rational function `f : A* → C*`
such that the formulas with one free variable correspond to sets of letters of
the output, and the formulas with two free variables correspond to regular
languages of infixes of the output. -/
theorem mso_formulas_via_rational {A : Type} [Finite A]
    (Φ₁ Φ₂ : Set (MSO A)) (hΦ₁ : Φ₁.Finite) (hΦ₂ : Φ₂.Finite) :
    ∃ (C : Type) (_ : Finite C) (f : List A → List C),
      IsRationalFun f ∧ LengthPreserving f ∧
      (∀ φ ∈ Φ₁, ∃ F : Set C, ∀ (w : List A) (x : ℕ), x < w.length →
        (MSO.Sat w (fun _ => x) (fun _ => ∅) φ ↔ ∃ c ∈ F, (f w)[x]? = some c)) ∧
      (∀ φ ∈ Φ₂, ∃ L : Language C, L.IsRegular ∧ ∀ (w : List A) (x y : ℕ),
        x ≤ y → y < w.length →
        (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅) φ ↔
          ((f w).drop x).take (y - x + 1) ∈ L)) :=
  mso_formulas_via_rational_aux Φ₁ Φ₂ hΦ₁ hΦ₂

/-! ## Regular functions in terms of logic -/

/-- **Theorem `thm:logic-regular-functions`.**  String-to-string mso transductions define exactly
the regular functions. -/
theorem msoTransduction_iff_regular {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsMSOTransduction f ↔ IsRegularFun f :=
  ⟨fun h => isRegularFun_of_isMSOTransduction h,
    fun h => isMSOTransduction_of_isTwoWay (regularFun_isTwoWay h)⟩

/-- **Claim `claim:mso-annotation-regular`.**  For an mso relabelling, the language of
strings over the alphabet `A × Φ` in which every position is labelled by a formula that holds in
that position is regular. -/
theorem msoRelabelling_annotation_regular {A B : Type} [Finite A] (R : MSORelabelling A B) :
    Language.IsRegular
      {u : List (A × R.Idx) | ∀ (p : ℕ) (hp : p < u.length),
        MSO.Sat (u.map Prod.fst) (fun _ => p) (fun _ => ∅) (R.form (u.get ⟨p, hp⟩).2)} :=
  msoRelabelling_annotation_regular_aux R

/-! ## The first-order fragment

**Definition `def:k-types` (k-types)** (`TpType` and `tp`) is in
`RequestProject/PartC/KTypes.lean`, together with the proof of Lemma
`lem:k-types-properties` below. -/

/-- **Theorem `thm:logic-aperiodic`.**  A language is definable in first-order logic if and
only if it is recognised by an aperiodic dfa. -/
theorem foDefinable_iff_aperiodic_dfa {A : Type} [Finite A] (L : Language A) :
    FODefinable L ↔
      ∃ (σ : Type) (_ : Finite σ) (M : DFA A σ), TransAperiodic M.step ∧ M.accepts = L := by
  refine ⟨aperiodic_dfa_of_foDefinable L, ?_⟩
  rintro ⟨σ, hσ, M, hap, rfl⟩
  haveI := hσ
  exact foDefinable_of_aperiodic_dfa M hap

/-- **Lemma `lem:k-types-fo-equivalence`.**  Two strings have the same `k`-type if and
only if they satisfy the same first-order sentences of quantifier rank at most `k`. -/
theorem tp_eq_iff_fo_equiv {A : Type} [Finite A] (k : ℕ) (w v : List A) :
    tp k w = tp k v ↔
      ∀ φ : MSO A, φ.IsFO → φ.freeFO = ∅ → φ.qrank ≤ k →
        ((∀ fo so, MSO.Sat w fo so φ) ↔ (∀ fo so, MSO.Sat v fo so φ)) := by
  constructor
  · intro h φ hfo hfree hq
    constructor
    · intro hw fo so
      exact (sat_iff_of_tp_eq h φ hfo hq hfree (fun _ => 0) fo (fun _ => ∅) so).mp
        (hw (fun _ => 0) (fun _ => ∅))
    · intro hv fo so
      exact (sat_iff_of_tp_eq h.symm φ hfo hq hfree (fun _ => 0) fo (fun _ => ∅) so).mp
        (hv (fun _ => 0) (fun _ => ∅))
  · intro h
    refine tp_eq_of_fo_equiv k w v (fun φ hfo hfree hq => ?_)
    have hw : (∀ fo so, MSO.Sat w fo so φ) ↔ MSO.Sat w (fun _ => 0) (fun _ => ∅) φ :=
      ⟨fun hs => hs _ _, fun hs fo so => (MSO.sat_sentence_congr hfo hfree w _ _ _ _).mp hs⟩
    have hv : (∀ fo so, MSO.Sat v fo so φ) ↔ MSO.Sat v (fun _ => 0) (fun _ => ∅) φ :=
      ⟨fun hs => hs _ _, fun hs fo so => (MSO.sat_sentence_congr hfo hfree v _ _ _ _).mp hs⟩
    exact hw.symm.trans ((h φ hfo hfree hq).trans hv)

/-- **Theorem `thm:fo-rational-functions`.**  A string-to-string function is a first-order
relabelling if and only if it is computed by an aperiodic bimachine. -/
theorem foRelabelling_iff_aperiodicBimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsFORelabelling f ↔ IsAperiodicBimachine f :=
  ⟨isAperiodicBimachine_of_isFORelabelling, isFORelabelling_of_isAperiodicBimachine⟩

/-- **Lemma `lem:k-types-properties`.**  Refinement, congruence and aperiodicity of `k`-types. -/
theorem tp_properties {A : Type} (k : ℕ) :
    (∀ w v : List A, tp (k + 1) w = tp (k + 1) v → tp k w = tp k v) ∧
    (∀ w w' v v' : List A, tp k w = tp k w' → tp k v = tp k v' →
      tp k (w ++ v) = tp k (w' ++ v')) ∧
    (∀ w : List A, ∃ N : ℕ, ∀ n ≥ N, tp k (npow w n) = tp k (npow w N)) :=
  tp_properties_aux k

end Lax314295Proofs.Transducers
