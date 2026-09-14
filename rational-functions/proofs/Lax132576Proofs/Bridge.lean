import Lax132576.LabelledAutomata
import Lax132576.RationalRelations
import Lax132576.RationalFunctions
import Lax132576.StringHomomorphisms
import Lax132576.Bimachines
import Lax132576.PrimeRationalFunctions
import Lax132576.TransducerCodes
import Lax132576.WeightedAutomata
import Lax132576.WeightedCodes
import Lax132576.SequentialTransducers
import Lax132576.SubsequentialTransducers
import Lax132576.LeftDistance
import Lax132576.EpsilonFreeAutomata
import Lax765601Proofs.Bridge
import Lax132576Proofs.Source.PartB.WeightedStatements

/-!
The bridge between the concept package of Part B and the ported source
development: every concept definition is shown equal or equivalent to its
source counterpart. Structures (`LabAut`, `Bimachine`, `Sequential`,
`Subsequential`, the two kinds of codes) are related by `toSrc`/`ofSrc`;
predicates defined by the same formula are related by `Iff.rfl`; the
composition closure and the prime Mealy machines come from Part A's bridge.
-/

namespace Lax132576Proofs.Bridge

open Lax765601Proofs
open Lax132576.LabelledAutomata Lax132576.RationalRelations Lax132576.RationalFunctions
  Lax132576.StringHomomorphisms Lax132576.Bimachines Lax132576.PrimeRationalFunctions
  Lax132576.TransducerCodes Lax132576.WeightedAutomata Lax132576.WeightedCodes
  Lax132576.SequentialTransducers Lax132576.SubsequentialTransducers
  Lax132576.LeftDistance Lax132576.EpsilonFreeAutomata

/-! ## Labelled automata -/

section LabAut

variable {A L Q : Type}

/-- A concept automaton as a source automaton. -/
def toSrc (M : LabAut A L Q) : Transducers.LabAut A L Q := ⟨M.init, M.final, M.δ, M.δ_finite⟩

/-- A source automaton as a concept automaton. -/
def ofSrc (M : Transducers.LabAut A L Q) : LabAut A L Q := ⟨M.init, M.final, M.δ, M.δ_finite⟩

@[simp] lemma toSrc_ofSrc (M : Transducers.LabAut A L Q) : toSrc (ofSrc M) = M := rfl

@[simp] lemma ofSrc_toSrc (M : LabAut A L Q) : ofSrc (toSrc M) = M := rfl

lemma path_iff (M : LabAut A L Q) (q : Q) (ts : List (Q × List A × L × Q)) (p : Q) :
    M.Path q ts p ↔ (toSrc M).Path q ts p := by
  constructor
  · intro h
    induction h with
    | nil q => exact Transducers.LabAut.Path.nil q
    | cons ht _ ih => exact Transducers.LabAut.Path.cons ht ih
  · intro h
    induction h with
    | nil q => exact LabAut.Path.nil q
    | cons ht _ ih => exact LabAut.Path.cons ht ih

lemma inputOf_eq (ts : List (Q × List A × L × Q)) :
    LabAut.inputOf ts = Transducers.LabAut.inputOf ts := rfl

lemma labelsOf_eq (ts : List (Q × List A × L × Q)) :
    LabAut.labelsOf ts = Transducers.LabAut.labelsOf ts := rfl

lemma accepting_iff (M : LabAut A L Q) (ts : List (Q × List A × L × Q)) :
    M.Accepting ts ↔ (toSrc M).Accepting ts := by
  simp only [LabAut.Accepting, Transducers.LabAut.Accepting, path_iff]
  exact Iff.rfl

lemma acceptingOn_eq (M : LabAut A L Q) (w : List A) :
    M.acceptingOn w = (toSrc M).acceptingOn w := by
  ext ts
  simp only [LabAut.acceptingOn, Transducers.LabAut.acceptingOn, Set.mem_setOf_eq,
    accepting_iff, inputOf_eq]

end LabAut

/-! ## Rational relations and functions -/

section Rational

variable {A B Q : Type}

lemma outputOf_eq (ts : List (Q × List A × List B × Q)) :
    NFAO.outputOf ts = Transducers.NFAO.outputOf ts := rfl

lemma rel_iff (M : NFAO A B Q) (w : List A) (v : List B) :
    M.rel w v ↔ Transducers.NFAO.rel (toSrc M) w v := by
  simp only [NFAO.rel, Transducers.NFAO.rel, accepting_iff, inputOf_eq, outputOf_eq]

lemma unambiguous_iff (M : NFAO A B Q) : M.Unambiguous ↔ Transducers.NFAO.Unambiguous (toSrc M) := by
  simp only [NFAO.Unambiguous, Transducers.NFAO.Unambiguous, accepting_iff, inputOf_eq]

lemma productive_iff (M : NFAO A B Q) (q : Q) :
    M.Productive q ↔ Transducers.Productive (toSrc M) q := by
  simp only [NFAO.Productive, Transducers.Productive, path_iff]
  exact Iff.rfl

lemma isRationalRel_iff (R : List A → List B → Prop) :
    IsRationalRel R ↔ Transducers.IsRationalRel R := by
  constructor
  · rintro ⟨Q, hQ, M, hM⟩
    exact ⟨Q, hQ, toSrc M, fun w v => (hM w v).trans (rel_iff M w v)⟩
  · rintro ⟨Q, hQ, M, hM⟩
    exact ⟨Q, hQ, ofSrc M, fun w v => (hM w v).trans (rel_iff (ofSrc M) w v).symm⟩

lemma isUnambiguousRel_iff (R : List A → List B → Prop) :
    IsUnambiguousRel R ↔ Transducers.IsUnambiguousRel R := by
  constructor
  · rintro ⟨Q, hQ, M, hu, hM⟩
    exact ⟨Q, hQ, toSrc M, (unambiguous_iff M).1 hu, fun w v => (hM w v).trans (rel_iff M w v)⟩
  · rintro ⟨Q, hQ, M, hu, hM⟩
    exact ⟨Q, hQ, ofSrc M, (unambiguous_iff (ofSrc M)).2 hu,
      fun w v => (hM w v).trans (rel_iff (ofSrc M) w v).symm⟩

lemma isRationalFun_iff (f : List A → List B) :
    IsRationalFun f ↔ Transducers.IsRationalFun f :=
  isRationalRel_iff _

lemma homOf_eq (φ : A → List B) : homOf φ = Transducers.homOf φ := rfl

end Rational

/-! ## Bimachines and the prime rational functions -/

section Bimachine

variable {A B P S : Type}

/-- A concept bimachine as a source bimachine. -/
def toSrcBim (M : Bimachine A B P S) : Transducers.Bimachine A B P S :=
  ⟨M.prefixInit, M.prefixStep, M.suffixInit, M.suffixStep, M.out⟩

/-- A source bimachine as a concept bimachine. -/
def ofSrcBim (M : Transducers.Bimachine A B P S) : Bimachine A B P S :=
  ⟨M.prefixInit, M.prefixStep, M.suffixInit, M.suffixStep, M.out⟩

lemma eval_toSrcBim (M : Bimachine A B P S) : (toSrcBim M).eval = M.eval := rfl

lemma isBimachine_iff (f : List A → List B) : IsBimachine f ↔ Transducers.IsBimachine f := by
  constructor
  · rintro ⟨P, S, hP, hS, M, hM⟩
    exact ⟨P, S, hP, hS, toSrcBim M, by rw [eval_toSrcBim, hM]⟩
  · rintro ⟨P, S, hP, hS, M, hM⟩
    exact ⟨P, S, hP, hS, ofSrcBim M, hM⟩

lemma isAperiodicBimachine_iff (f : List A → List B) :
    IsAperiodicBimachine f ↔ Transducers.IsAperiodicBimachine f := by
  constructor
  · rintro ⟨P, S, hP, hS, M, hM, h1, h2⟩
    exact ⟨P, S, hP, hS, toSrcBim M, by rw [eval_toSrcBim, hM], h1, h2⟩
  · rintro ⟨P, S, hP, hS, M, hM, h1, h2⟩
    exact ⟨P, S, hP, hS, ofSrcBim M, hM, h1, h2⟩

lemma primeRationalFam_iff (A B : Type) (f : List A → List B) :
    PrimeRationalFam A B f ↔ Transducers.PrimeRationalFam A B f := by
  simp only [PrimeRationalFam, Transducers.PrimeRationalFam, Lax765601Proofs.Bridge.primeMealyFam_iff,
    homOf_eq]

end Bimachine

/-! ## Codes and decidability under a promise -/

section Codes

/-- A concept code as a source code (the tuple). -/
def toSrcCode (c : RelCode) : Transducers.RelCode := relCodeEquiv c

lemma primrec_toSrcCode : Primrec toSrcCode := Primrec.of_equiv

lemma primrec_relCodeEquiv_symm : Primrec relCodeEquiv.symm := Primrec.of_equiv_symm

lemma codeAut_eq (c : RelCode) : toSrc (codeAut c) = Transducers.codeAut (toSrcCode c) := rfl

lemma codeRel_iff (c : RelCode) (w v : List ℕ) :
    codeRel c w v ↔ Transducers.codeRel (toSrcCode c) w v := by
  show (codeAut c).rel w v ↔ Transducers.NFAO.rel (Transducers.codeAut (toSrcCode c)) w v
  rw [rel_iff, codeAut_eq]

lemma codeRel_eq (c : RelCode) : codeRel c = Transducers.codeRel (toSrcCode c) := by
  funext w v
  exact propext (codeRel_iff c w v)

lemma codeAlphabet_eq (c : RelCode) : codeAlphabet c = Transducers.codeAlphabet (toSrcCode c) := rfl

lemma codeWord_iff (c : RelCode) (w : List ℕ) :
    CodeWord c w ↔ Transducers.CodeWord (toSrcCode c) w := Iff.rfl

lemma codeFunctional_iff (c : RelCode) :
    CodeFunctional c ↔ Transducers.CodeFunctional (toSrcCode c) := by
  simp only [CodeFunctional, Transducers.CodeFunctional, codeWord_iff, codeRel_iff]

/-- Precomposing a computable predicate with a computable map. -/
lemma computablePred_comp {α β : Type} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : ComputablePred p) {g : α → β} (hg : Computable g) : ComputablePred fun a => p (g a) := by
  obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.1 hp
  exact ComputablePred.computable_iff.2 ⟨fun a => f (g a), hf.comp hg, rfl⟩

/-- Decidability under a promise transports along a primitive recursive bijection of
the inputs. -/
lemma decidableUnderPromise_equiv {α β : Type} [Primcodable α] [Primcodable β] (e : α ≃ β)
    (he : Primrec e) (he' : Primrec e.symm) (promise P : β → Prop) :
    DecidableUnderPromise (fun a => promise (e a)) (fun a => P (e a)) ↔
      Transducers.DecidableUnderPromise promise P := by
  constructor
  · rintro ⟨D, hD, hspec⟩
    refine ⟨fun b => D (e.symm b), hD.comp he'.to_comp, fun b hb => ?_⟩
    simpa using hspec (e.symm b) (by simpa using hb)
  · rintro ⟨D, hD, hspec⟩
    exact ⟨fun a => D (e a), hD.comp he.to_comp, fun a ha => hspec (e a) ha⟩

/-- The bijection of pairs of codes. -/
def relCodeEquiv₂ : RelCode × RelCode ≃ Transducers.RelCode × Transducers.RelCode :=
  relCodeEquiv.prodCongr relCodeEquiv

lemma primrec_relCodeEquiv₂ : Primrec relCodeEquiv₂ :=
  (primrec_toSrcCode.comp Primrec.fst).pair (primrec_toSrcCode.comp Primrec.snd)

lemma primrec_relCodeEquiv₂_symm : Primrec relCodeEquiv₂.symm :=
  (primrec_relCodeEquiv_symm.comp Primrec.fst).pair (primrec_relCodeEquiv_symm.comp Primrec.snd)

/-- A concept weighted code as a source weighted code. -/
def toSrcWCode (c : WCode) : Transducers.WCode := wcodeEquiv c

lemma primrec_toSrcWCode : Primrec toSrcWCode := Primrec.of_equiv

lemma primrec_wcodeEquiv_symm : Primrec wcodeEquiv.symm := Primrec.of_equiv_symm

lemma wcodeAut_eq (c : WCode) : toSrc (wcodeAut c) = Transducers.wcodeAut (toSrcWCode c) := rfl

lemma weightOf_eq {A S Q : Type} [Semiring S] (ts : List (Q × List A × S × Q)) :
    weightOf ts = Transducers.LabAut.weightOf ts := rfl

lemma wEval_eq {A S Q : Type} [Semiring S] (M : LabAut A S Q) :
    wEval M = (toSrc M).wEval := by
  funext w
  simp only [wEval, Transducers.LabAut.wEval, acceptingOn_eq, weightOf_eq]

lemma finitelyManyRuns_iff {A S Q : Type} [Semiring S] (M : LabAut A S Q) :
    FinitelyManyRuns M ↔ (toSrc M).FinitelyManyRuns := by
  simp only [FinitelyManyRuns, Transducers.LabAut.FinitelyManyRuns, acceptingOn_eq]

lemma isWeighted_iff {A S : Type} [Semiring S] (f : List A → S) :
    IsWeighted f ↔ Transducers.IsWeighted f := by
  constructor
  · rintro ⟨Q, hQ, M, hfin, hM⟩
    exact ⟨Q, hQ, toSrc M, (finitelyManyRuns_iff M).1 hfin, by rw [← wEval_eq, hM]⟩
  · rintro ⟨Q, hQ, M, hfin, hM⟩
    exact ⟨Q, hQ, ofSrc M, (finitelyManyRuns_iff (ofSrc M)).2 hfin, by rw [wEval_eq]; exact hM⟩

lemma wcodeEval_eq (c : WCode) : wcodeEval c = Transducers.wcodeEval (toSrcWCode c) := by
  show wEval (wcodeAut c) = (Transducers.wcodeAut (toSrcWCode c)).wEval
  rw [wEval_eq, wcodeAut_eq]

lemma wcodeValid_iff (c : WCode) : WCodeValid c ↔ Transducers.WCodeValid (toSrcWCode c) := by
  show FinitelyManyRuns (wcodeAut c) ↔ (Transducers.wcodeAut (toSrcWCode c)).FinitelyManyRuns
  rw [finitelyManyRuns_iff, wcodeAut_eq]

/-- The bijection of pairs of weighted codes. -/
def wcodeEquiv₂ : WCode × WCode ≃ Transducers.WCode × Transducers.WCode :=
  wcodeEquiv.prodCongr wcodeEquiv

lemma primrec_wcodeEquiv₂ : Primrec wcodeEquiv₂ :=
  (primrec_toSrcWCode.comp Primrec.fst).pair (primrec_toSrcWCode.comp Primrec.snd)

lemma primrec_wcodeEquiv₂_symm : Primrec wcodeEquiv₂.symm :=
  (primrec_wcodeEquiv_symm.comp Primrec.fst).pair (primrec_wcodeEquiv_symm.comp Primrec.snd)

end Codes

/-! ## Sequential and subsequential transducers -/

section Sequential

variable {A B Q : Type}

/-- A concept sequential transducer as a source one. -/
def toSrcSeq (T : Sequential A B Q) : Transducers.Sequential A B Q := ⟨T.init, T.step⟩

/-- A source sequential transducer as a concept one. -/
def ofSrcSeq (T : Transducers.Sequential A B Q) : Sequential A B Q := ⟨T.init, T.step⟩

lemma run_toSrcSeq (T : Sequential A B Q) (q : Q) (w : List A) :
    (toSrcSeq T).run q w = T.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      show (T.step q a).2 ++ (toSrcSeq T).run (T.step q a).1 w = (T.step q a).2 ++ T.run _ w
      rw [ih]

lemma eval_toSrcSeq (T : Sequential A B Q) : (toSrcSeq T).eval = T.eval := by
  funext w
  exact run_toSrcSeq T T.init w

lemma isSequential_iff (f : List A → List B) : IsSequential f ↔ Transducers.IsSequential f := by
  constructor
  · rintro ⟨Q, hQ, T, hT⟩
    exact ⟨Q, hQ, toSrcSeq T, by rw [eval_toSrcSeq, hT]⟩
  · rintro ⟨Q, hQ, T, hT⟩
    exact ⟨Q, hQ, ofSrcSeq T, by rw [← hT, ← eval_toSrcSeq]; rfl⟩

/-- A concept subsequential transducer as a source one. -/
def toSrcSub (T : Subsequential A B Q) : Transducers.Subsequential A B Q :=
  ⟨toSrcSeq T.toSequential, T.endOfInput⟩

/-- A source subsequential transducer as a concept one. -/
def ofSrcSub (T : Transducers.Subsequential A B Q) : Subsequential A B Q :=
  ⟨ofSrcSeq T.toSequential, T.endOfInput⟩

lemma eval_toSrcSub (T : Subsequential A B Q) : (toSrcSub T).eval = T.eval := by
  funext w
  simp only [Transducers.Subsequential.eval, Subsequential.eval, toSrcSub, eval_toSrcSeq]
  rfl

lemma isSubsequential_iff (f : List A → Option (List B)) :
    IsSubsequential f ↔ Transducers.IsSubsequential f := by
  constructor
  · rintro ⟨Q, hQ, T, hT⟩
    exact ⟨Q, hQ, toSrcSub T, by rw [eval_toSrcSub, hT]⟩
  · rintro ⟨Q, hQ, T, hT⟩
    exact ⟨Q, hQ, ofSrcSub T, by rw [← hT, ← eval_toSrcSub]; rfl⟩

end Sequential

/-! ## Left distance -/

lemma leftDist_eq {B : Type} (w₁ w₂ : List B) : leftDist w₁ w₂ = Transducers.leftDist w₁ w₂ := rfl

lemma boundedVarRel_iff {A B : Type} (f : List A → List B) (w₁ w₂ : List A) :
    BoundedVarRel f w₁ w₂ ↔ Transducers.BoundedVarRel f w₁ w₂ := Iff.rfl

lemma boundedVariation_iff {A B : Type} (f : List A → Option (List B)) :
    BoundedVariation f ↔ Transducers.BoundedVariation f := Iff.rfl

/-! ## Extended transitions -/

section Extended

variable {A B Q : Type}

lemma isExtendedNFAO_iff (M : LabAut A (Language B) Q) :
    IsExtendedNFAO M ↔ Transducers.IsExtendedNFAO (toSrc M) := Iff.rfl

lemma extRel_iff (M : LabAut A (Language B) Q) (w : List A) (v : List B) :
    extRel M w v ↔ Transducers.extRel (toSrc M) w v := by
  simp only [extRel, Transducers.extRel, accepting_iff, inputOf_eq, labelsOf_eq]

lemma epsilonFree_iff {L : Type} (M : LabAut A L Q) :
    EpsilonFree M ↔ Transducers.EpsilonFree (toSrc M) := by
  simp only [EpsilonFree, Transducers.EpsilonFree, accepting_iff, inputOf_eq]

end Extended

end Lax132576Proofs.Bridge
