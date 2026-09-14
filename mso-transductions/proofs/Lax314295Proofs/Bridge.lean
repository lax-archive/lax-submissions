import Lax314295.MSOLogic
import Lax314295.MSORelabellings
import Lax314295.MSOTransductions
import Lax314295.KTypes
import Lax765601Proofs.Bridge
import Lax132576Proofs.Bridge
import Lax916827Proofs.Bridge
import Lax314295Proofs.Source.PartC.MSO

/-!
The bridge between the concept package of Part C §4 and the ported source
development: every concept definition is shown equal or equivalent to its
source counterpart. The formulas of monadic second-order logic are an
inductive type on both sides, related by the bijection `toSrc`/`ofSrc`, along
which satisfaction, the first-order fragment, the quantifier rank and the free
variables are transported by induction on the syntax; mso relabellings and mso
transductions are structures over the formulas, related field by field by
`toSrcRel`/`ofSrcRel` and `toSrcT`/`ofSrcT` together with their semantics;
the `k`-types are related by a bijection of the types of `k`-types, defined
by induction on `k`; the remaining notions (annotations, valuations, length
preservation, aperiodicity of a transition function) are defined by the same
formulas and are related by `rfl` or `Iff.rfl`. The notions of the earlier
parts (rational functions, aperiodic bimachines, regular functions, powers of
a string) come from the bridges of Parts A, B and C §1–3.
-/

namespace Lax314295Proofs.Bridge

open Lax765601Proofs Lax132576Proofs Lax916827Proofs
open Lax765601.StateTransformations Lax765601.ElementaryProperties Lax765601.Aperiodicity
open Lax132576.RationalFunctions Lax132576.Bimachines
open Lax916827.RegularFunctions
open Lax314295.MSOLogic Lax314295.MSORelabellings Lax314295.MSOTransductions Lax314295.KTypes

/-! ## Monadic second-order logic -/

section Logic

variable {A : Type}

/-- A concept formula as a source formula. -/
def toSrc : MSO A → Transducers.MSO A
  | MSO.le i j => Transducers.MSO.le i j
  | MSO.lab a i => Transducers.MSO.lab a i
  | MSO.mem i j => Transducers.MSO.mem i j
  | MSO.not φ => Transducers.MSO.not (toSrc φ)
  | MSO.and φ ψ => Transducers.MSO.and (toSrc φ) (toSrc ψ)
  | MSO.or φ ψ => Transducers.MSO.or (toSrc φ) (toSrc ψ)
  | MSO.exFO i φ => Transducers.MSO.exFO i (toSrc φ)
  | MSO.exSO i φ => Transducers.MSO.exSO i (toSrc φ)

/-- A source formula as a concept formula. -/
def ofSrc : Transducers.MSO A → MSO A
  | Transducers.MSO.le i j => MSO.le i j
  | Transducers.MSO.lab a i => MSO.lab a i
  | Transducers.MSO.mem i j => MSO.mem i j
  | Transducers.MSO.not φ => MSO.not (ofSrc φ)
  | Transducers.MSO.and φ ψ => MSO.and (ofSrc φ) (ofSrc ψ)
  | Transducers.MSO.or φ ψ => MSO.or (ofSrc φ) (ofSrc ψ)
  | Transducers.MSO.exFO i φ => MSO.exFO i (ofSrc φ)
  | Transducers.MSO.exSO i φ => MSO.exSO i (ofSrc φ)

@[simp] lemma toSrc_ofSrc : ∀ φ : Transducers.MSO A, toSrc (ofSrc φ) = φ
  | Transducers.MSO.le _ _ => rfl
  | Transducers.MSO.lab _ _ => rfl
  | Transducers.MSO.mem _ _ => rfl
  | Transducers.MSO.not φ => by simp only [ofSrc, toSrc, toSrc_ofSrc φ]
  | Transducers.MSO.and φ ψ => by simp only [ofSrc, toSrc, toSrc_ofSrc φ, toSrc_ofSrc ψ]
  | Transducers.MSO.or φ ψ => by simp only [ofSrc, toSrc, toSrc_ofSrc φ, toSrc_ofSrc ψ]
  | Transducers.MSO.exFO _ φ => by simp only [ofSrc, toSrc, toSrc_ofSrc φ]
  | Transducers.MSO.exSO _ φ => by simp only [ofSrc, toSrc, toSrc_ofSrc φ]

@[simp] lemma ofSrc_toSrc : ∀ φ : MSO A, ofSrc (toSrc φ) = φ
  | MSO.le _ _ => rfl
  | MSO.lab _ _ => rfl
  | MSO.mem _ _ => rfl
  | MSO.not φ => by simp only [ofSrc, toSrc, ofSrc_toSrc φ]
  | MSO.and φ ψ => by simp only [ofSrc, toSrc, ofSrc_toSrc φ, ofSrc_toSrc ψ]
  | MSO.or φ ψ => by simp only [ofSrc, toSrc, ofSrc_toSrc φ, ofSrc_toSrc ψ]
  | MSO.exFO _ φ => by simp only [ofSrc, toSrc, ofSrc_toSrc φ]
  | MSO.exSO _ φ => by simp only [ofSrc, toSrc, ofSrc_toSrc φ]

/-- The bijection between the concept's and the source's formulas. -/
def msoEquiv (A : Type) : MSO A ≃ Transducers.MSO A :=
  ⟨toSrc, ofSrc, ofSrc_toSrc, toSrc_ofSrc⟩

lemma toSrc_injective : Function.Injective (toSrc : MSO A → Transducers.MSO A) :=
  (msoEquiv A).injective

/-- Satisfaction is transported along `toSrc`. -/
lemma sat_toSrc (w : List A) : ∀ (φ : MSO A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
    MSO.Sat w fo so φ ↔ Transducers.MSO.Sat w fo so (toSrc φ)
  | MSO.le _ _, _, _ => Iff.rfl
  | MSO.lab _ _, _, _ => Iff.rfl
  | MSO.mem _ _, _, _ => Iff.rfl
  | MSO.not φ, fo, so => by
      simp only [MSO.Sat, Transducers.MSO.Sat, toSrc, sat_toSrc w φ]
  | MSO.and φ ψ, fo, so => by
      simp only [MSO.Sat, Transducers.MSO.Sat, toSrc, sat_toSrc w φ, sat_toSrc w ψ]
  | MSO.or φ ψ, fo, so => by
      simp only [MSO.Sat, Transducers.MSO.Sat, toSrc, sat_toSrc w φ, sat_toSrc w ψ]
  | MSO.exFO _ φ, fo, so => by
      simp only [MSO.Sat, Transducers.MSO.Sat, toSrc, sat_toSrc w φ]
  | MSO.exSO _ φ, fo, so => by
      simp only [MSO.Sat, Transducers.MSO.Sat, toSrc, sat_toSrc w φ]

/-- Satisfaction is transported along `ofSrc`. -/
lemma sat_ofSrc (w : List A) (φ : Transducers.MSO A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Transducers.MSO.Sat w fo so φ ↔ MSO.Sat w fo so (ofSrc φ) := by
  rw [sat_toSrc, toSrc_ofSrc]

lemma isFO_toSrc : ∀ φ : MSO A, Transducers.MSO.IsFO (toSrc φ) ↔ MSO.IsFO φ
  | MSO.le _ _ => Iff.rfl
  | MSO.lab _ _ => Iff.rfl
  | MSO.mem _ _ => Iff.rfl
  | MSO.not φ => by simp only [MSO.IsFO, Transducers.MSO.IsFO, toSrc, isFO_toSrc φ]
  | MSO.and φ ψ => by
      simp only [MSO.IsFO, Transducers.MSO.IsFO, toSrc, isFO_toSrc φ, isFO_toSrc ψ]
  | MSO.or φ ψ => by
      simp only [MSO.IsFO, Transducers.MSO.IsFO, toSrc, isFO_toSrc φ, isFO_toSrc ψ]
  | MSO.exFO _ φ => by simp only [MSO.IsFO, Transducers.MSO.IsFO, toSrc, isFO_toSrc φ]
  | MSO.exSO _ _ => Iff.rfl

lemma isFO_ofSrc (φ : Transducers.MSO A) : MSO.IsFO (ofSrc φ) ↔ Transducers.MSO.IsFO φ := by
  rw [← isFO_toSrc, toSrc_ofSrc]

lemma qrank_toSrc : ∀ φ : MSO A, Transducers.MSO.qrank (toSrc φ) = MSO.qrank φ
  | MSO.le _ _ => rfl
  | MSO.lab _ _ => rfl
  | MSO.mem _ _ => rfl
  | MSO.not φ => by simp only [MSO.qrank, Transducers.MSO.qrank, toSrc, qrank_toSrc φ]
  | MSO.and φ ψ => by
      simp only [MSO.qrank, Transducers.MSO.qrank, toSrc, qrank_toSrc φ, qrank_toSrc ψ]
  | MSO.or φ ψ => by
      simp only [MSO.qrank, Transducers.MSO.qrank, toSrc, qrank_toSrc φ, qrank_toSrc ψ]
  | MSO.exFO _ φ => by simp only [MSO.qrank, Transducers.MSO.qrank, toSrc, qrank_toSrc φ]
  | MSO.exSO _ φ => by simp only [MSO.qrank, Transducers.MSO.qrank, toSrc, qrank_toSrc φ]

lemma qrank_ofSrc (φ : Transducers.MSO A) : MSO.qrank (ofSrc φ) = Transducers.MSO.qrank φ := by
  rw [← qrank_toSrc, toSrc_ofSrc]

lemma freeFO_toSrc : ∀ φ : MSO A, Transducers.MSO.freeFO (toSrc φ) = MSO.freeFO φ
  | MSO.le _ _ => rfl
  | MSO.lab _ _ => rfl
  | MSO.mem _ _ => rfl
  | MSO.not φ => by simp only [MSO.freeFO, Transducers.MSO.freeFO, toSrc, freeFO_toSrc φ]
  | MSO.and φ ψ => by
      simp only [MSO.freeFO, Transducers.MSO.freeFO, toSrc, freeFO_toSrc φ, freeFO_toSrc ψ]
  | MSO.or φ ψ => by
      simp only [MSO.freeFO, Transducers.MSO.freeFO, toSrc, freeFO_toSrc φ, freeFO_toSrc ψ]
  | MSO.exFO _ φ => by simp only [MSO.freeFO, Transducers.MSO.freeFO, toSrc, freeFO_toSrc φ]
  | MSO.exSO _ φ => by simp only [MSO.freeFO, Transducers.MSO.freeFO, toSrc, freeFO_toSrc φ]

lemma freeFO_ofSrc (φ : Transducers.MSO A) :
    MSO.freeFO (ofSrc φ) = Transducers.MSO.freeFO φ := by
  rw [← freeFO_toSrc, toSrc_ofSrc]

lemma freeSO_toSrc : ∀ φ : MSO A, Transducers.MSO.freeSO (toSrc φ) = MSO.freeSO φ
  | MSO.le _ _ => rfl
  | MSO.lab _ _ => rfl
  | MSO.mem _ _ => rfl
  | MSO.not φ => by simp only [MSO.freeSO, Transducers.MSO.freeSO, toSrc, freeSO_toSrc φ]
  | MSO.and φ ψ => by
      simp only [MSO.freeSO, Transducers.MSO.freeSO, toSrc, freeSO_toSrc φ, freeSO_toSrc ψ]
  | MSO.or φ ψ => by
      simp only [MSO.freeSO, Transducers.MSO.freeSO, toSrc, freeSO_toSrc φ, freeSO_toSrc ψ]
  | MSO.exFO _ φ => by simp only [MSO.freeSO, Transducers.MSO.freeSO, toSrc, freeSO_toSrc φ]
  | MSO.exSO _ φ => by simp only [MSO.freeSO, Transducers.MSO.freeSO, toSrc, freeSO_toSrc φ]

lemma freeSO_ofSrc (φ : Transducers.MSO A) :
    MSO.freeSO (ofSrc φ) = Transducers.MSO.freeSO φ := by
  rw [← freeSO_toSrc, toSrc_ofSrc]

lemma msoDefinable_iff (L : Language A) : MSODefinable L ↔ Transducers.MSODefinable L := by
  constructor
  · rintro ⟨φ, h⟩
    exact ⟨toSrc φ, fun w fo so => (sat_toSrc w φ fo so).symm.trans (h w fo so)⟩
  · rintro ⟨φ, h⟩
    exact ⟨ofSrc φ, fun w fo so => (sat_ofSrc w φ fo so).symm.trans (h w fo so)⟩

lemma foDefinable_iff (L : Language A) : FODefinable L ↔ Transducers.FODefinable L := by
  constructor
  · rintro ⟨φ, hφ, h⟩
    exact ⟨toSrc φ, (isFO_toSrc φ).2 hφ,
      fun w fo so => (sat_toSrc w φ fo so).symm.trans (h w fo so)⟩
  · rintro ⟨φ, hφ, h⟩
    exact ⟨ofSrc φ, (isFO_ofSrc φ).2 hφ,
      fun w fo so => (sat_ofSrc w φ fo so).symm.trans (h w fo so)⟩

lemma annotate_eq (k l : ℕ) (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ) :
    annotate k l w fo so = Transducers.annotate k l w fo so := rfl

lemma extFO_eq (k : ℕ) (fo : Fin k → ℕ) : extFO k fo = Transducers.extFO k fo := rfl

lemma extSO_eq (l : ℕ) (so : Fin l → Set ℕ) : extSO l so = Transducers.extSO l so := rfl

end Logic

/-! ## Notions of the earlier parts defined by the same formulas -/

section Earlier

variable {A B Q : Type}

lemma lengthPreserving_iff (f : List A → List B) :
    LengthPreserving f ↔ Transducers.LengthPreserving f := Iff.rfl

lemma transAperiodic_iff (δ : Q → A → Q) :
    TransAperiodic δ ↔ Transducers.TransAperiodic δ := Iff.rfl

end Earlier

/-! ## MSO relabellings -/

section Relabellings

variable {A B : Type}

/-- A concept mso relabelling as a source one. -/
def toSrcRel (R : MSORelabelling A B) : Transducers.MSORelabelling A B where
  Idx := R.Idx
  finIdx := R.finIdx
  form i := toSrc (R.form i)
  out := R.out
  emptyOut := R.emptyOut
  unique w p hp := by
    have := R.unique w p hp
    exact existsUnique_congr (fun i => sat_toSrc w (R.form i) _ _) |>.1 this

/-- A source mso relabelling as a concept one. -/
def ofSrcRel (R : Transducers.MSORelabelling A B) : MSORelabelling A B where
  Idx := R.Idx
  finIdx := R.finIdx
  form i := ofSrc (R.form i)
  out := R.out
  emptyOut := R.emptyOut
  unique w p hp := by
    have := R.unique w p hp
    exact existsUnique_congr (fun i => sat_ofSrc w (R.form i) _ _) |>.1 this

@[simp] lemma toSrcRel_form (R : MSORelabelling A B) (i : R.Idx) :
    (toSrcRel R).form i = toSrc (R.form i) := rfl

@[simp] lemma toSrcRel_ofSrcRel (R : Transducers.MSORelabelling A B) :
    toSrcRel (ofSrcRel R) = R := by
  cases R
  simp only [toSrcRel, ofSrcRel, toSrc_ofSrc]

@[simp] lemma ofSrcRel_toSrcRel (R : MSORelabelling A B) : ofSrcRel (toSrcRel R) = R := by
  cases R
  simp only [toSrcRel, ofSrcRel, ofSrc_toSrc]

lemma relabels_toSrcRel (R : MSORelabelling A B) (w : List A) (v : List B) :
    R.Relabels w v ↔ (toSrcRel R).Relabels w v := by
  unfold MSORelabelling.Relabels Transducers.MSORelabelling.Relabels
  refine or_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun g => and_congr ?_ Iff.rfl))
  exact forall_congr' fun p => forall_congr' fun _ => sat_toSrc w _ _ _

lemma relabels_ofSrcRel (R : Transducers.MSORelabelling A B) (w : List A) (v : List B) :
    R.Relabels w v ↔ (ofSrcRel R).Relabels w v := by
  rw [relabels_toSrcRel, toSrcRel_ofSrcRel]

lemma allFO_toSrcRel (R : MSORelabelling A B) : (toSrcRel R).AllFO ↔ R.AllFO := by
  unfold MSORelabelling.AllFO Transducers.MSORelabelling.AllFO
  exact forall_congr' fun i => isFO_toSrc _

lemma allFO_ofSrcRel (R : Transducers.MSORelabelling A B) : (ofSrcRel R).AllFO ↔ R.AllFO := by
  rw [← allFO_toSrcRel, toSrcRel_ofSrcRel]

lemma isMSORelabelling_iff (f : List A → List B) :
    IsMSORelabelling f ↔ Transducers.IsMSORelabelling f := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨toSrcRel R, fun w => (relabels_toSrcRel R w _).1 (hR w)⟩
  · rintro ⟨R, hR⟩
    exact ⟨ofSrcRel R, fun w => (relabels_ofSrcRel R w _).1 (hR w)⟩

lemma isFORelabelling_iff (f : List A → List B) :
    IsFORelabelling f ↔ Transducers.IsFORelabelling f := by
  constructor
  · rintro ⟨R, hfo, hR⟩
    exact ⟨toSrcRel R, (allFO_toSrcRel R).2 hfo, fun w => (relabels_toSrcRel R w _).1 (hR w)⟩
  · rintro ⟨R, hfo, hR⟩
    exact ⟨ofSrcRel R, (allFO_ofSrcRel R).2 hfo, fun w => (relabels_ofSrcRel R w _).1 (hR w)⟩

end Relabellings

/-! ## MSO transductions -/

section Transductions

variable {A B : Type}

/-- A concept mso transduction as a source one. -/
def toSrcT (T : MSOTransduction A B) : Transducers.MSOTransduction A B where
  copies := T.copies
  extra := T.extra
  univP i := toSrc (T.univP i)
  univC j := toSrc (T.univC j)
  labP i b := toSrc (T.labP i b)
  labC j b := toSrc (T.labC j b)
  ordPP i i' := toSrc (T.ordPP i i')
  ordPC i j := toSrc (T.ordPC i j)
  ordCP j i := toSrc (T.ordCP j i)
  ordCC j j' := toSrc (T.ordCC j j')

/-- A source mso transduction as a concept one. -/
def ofSrcT (T : Transducers.MSOTransduction A B) : MSOTransduction A B where
  copies := T.copies
  extra := T.extra
  univP i := ofSrc (T.univP i)
  univC j := ofSrc (T.univC j)
  labP i b := ofSrc (T.labP i b)
  labC j b := ofSrc (T.labC j b)
  ordPP i i' := ofSrc (T.ordPP i i')
  ordPC i j := ofSrc (T.ordPC i j)
  ordCP j i := ofSrc (T.ordCP j i)
  ordCC j j' := ofSrc (T.ordCC j j')

@[simp] lemma toSrcT_ofSrcT (T : Transducers.MSOTransduction A B) : toSrcT (ofSrcT T) = T := by
  cases T
  simp only [toSrcT, ofSrcT, toSrc_ofSrc]

@[simp] lemma ofSrcT_toSrcT (T : MSOTransduction A B) : ofSrcT (toSrcT T) = T := by
  cases T
  simp only [toSrcT, ofSrcT, ofSrc_toSrc]

variable (T : MSOTransduction A B) (w : List A)

lemma selected_toSrcT (x : T.Elt) : (toSrcT T).selected w x ↔ T.selected w x := by
  rcases x with ⟨i, p⟩ | j
  · exact and_congr Iff.rfl (sat_toSrc w (T.univP i) _ _).symm
  · exact (sat_toSrc w (T.univC j) _ _).symm

lemma ordRel_toSrcT (x y : T.Elt) : (toSrcT T).ordRel w x y ↔ T.ordRel w x y := by
  rcases x with ⟨i, p⟩ | j <;> rcases y with ⟨i', p'⟩ | j'
  · exact (sat_toSrc w (T.ordPP i i') _ _).symm
  · exact (sat_toSrc w (T.ordPC i j') _ _).symm
  · exact (sat_toSrc w (T.ordCP j i') _ _).symm
  · exact (sat_toSrc w (T.ordCC j j') _ _).symm

lemma labRel_toSrcT (x : T.Elt) (b : B) : (toSrcT T).labRel w x b ↔ T.labRel w x b := by
  rcases x with ⟨i, p⟩ | j
  · exact (sat_toSrc w (T.labP i b) _ _).symm
  · exact (sat_toSrc w (T.labC j b) _ _).symm

lemma outputs_toSrcT (v : List B) : (toSrcT T).Outputs w v ↔ T.Outputs w v := by
  unfold MSOTransduction.Outputs Transducers.MSOTransduction.Outputs
  refine exists_congr fun es => and_congr Iff.rfl (and_congr ?_ (and_congr ?_ (and_congr Iff.rfl ?_)))
  · exact forall_congr' fun x => iff_congr Iff.rfl (selected_toSrcT T w x)
  · exact forall_congr' fun i => forall_congr' fun j => forall_congr' fun hi =>
      forall_congr' fun hj => imp_congr Iff.rfl (ordRel_toSrcT T w _ _)
  · exact forall_congr' fun i => forall_congr' fun hi => forall_congr' fun hi' =>
      labRel_toSrcT T w _ _

lemma proper_toSrcT : (toSrcT T).Proper ↔ T.Proper := by
  unfold MSOTransduction.Proper Transducers.MSOTransduction.Proper
  refine forall_congr' fun w => and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · exact forall_congr' fun x => imp_congr (selected_toSrcT T w x)
      (existsUnique_congr fun b => labRel_toSrcT T w x b)
  · exact forall_congr' fun x => imp_congr (selected_toSrcT T w x) (ordRel_toSrcT T w x x)
  · exact forall_congr' fun x => forall_congr' fun y => imp_congr (selected_toSrcT T w x)
      (imp_congr (selected_toSrcT T w y) (imp_congr (ordRel_toSrcT T w x y)
        (imp_congr (ordRel_toSrcT T w y x) Iff.rfl)))
  · exact forall_congr' fun x => forall_congr' fun y => forall_congr' fun z =>
      imp_congr (selected_toSrcT T w x) (imp_congr (selected_toSrcT T w y)
        (imp_congr (selected_toSrcT T w z) (imp_congr (ordRel_toSrcT T w x y)
          (imp_congr (ordRel_toSrcT T w y z) (ordRel_toSrcT T w x z)))))
  · exact forall_congr' fun x => forall_congr' fun y => imp_congr (selected_toSrcT T w x)
      (imp_congr (selected_toSrcT T w y)
        (or_congr (ordRel_toSrcT T w x y) (ordRel_toSrcT T w y x)))

lemma allFO_toSrcT : (toSrcT T).AllFO ↔ T.AllFO := by
  unfold MSOTransduction.AllFO Transducers.MSOTransduction.AllFO
  refine and_congr (forall_congr' fun i => isFO_toSrc _)
    (and_congr (forall_congr' fun j => isFO_toSrc _)
      (and_congr (forall_congr' fun i => forall_congr' fun b => isFO_toSrc _)
        (and_congr (forall_congr' fun j => forall_congr' fun b => isFO_toSrc _)
          (and_congr (forall_congr' fun i => forall_congr' fun i' => isFO_toSrc _)
            (and_congr (forall_congr' fun i => forall_congr' fun j => isFO_toSrc _)
              (and_congr (forall_congr' fun j => forall_congr' fun i => isFO_toSrc _)
                (forall_congr' fun j => forall_congr' fun j' => isFO_toSrc _)))))))

lemma outputs_ofSrcT (T : Transducers.MSOTransduction A B) (w : List A) (v : List B) :
    (ofSrcT T).Outputs w v ↔ T.Outputs w v := by
  rw [← outputs_toSrcT, toSrcT_ofSrcT]

lemma proper_ofSrcT (T : Transducers.MSOTransduction A B) : (ofSrcT T).Proper ↔ T.Proper := by
  rw [← proper_toSrcT, toSrcT_ofSrcT]

lemma allFO_ofSrcT (T : Transducers.MSOTransduction A B) : (ofSrcT T).AllFO ↔ T.AllFO := by
  rw [← allFO_toSrcT, toSrcT_ofSrcT]

lemma isMSOTransduction_iff (f : List A → List B) :
    IsMSOTransduction f ↔ Transducers.IsMSOTransduction f := by
  constructor
  · rintro ⟨T, hp, hT⟩
    exact ⟨toSrcT T, (proper_toSrcT T).2 hp, fun w => (outputs_toSrcT T w _).2 (hT w)⟩
  · rintro ⟨T, hp, hT⟩
    exact ⟨ofSrcT T, (proper_ofSrcT T).2 hp, fun w => (outputs_ofSrcT T w _).2 (hT w)⟩

lemma isFOTransduction_iff (f : List A → List B) :
    IsFOTransduction f ↔ Transducers.IsFOTransduction f := by
  constructor
  · rintro ⟨T, hp, hfo, hT⟩
    exact ⟨toSrcT T, (proper_toSrcT T).2 hp, (allFO_toSrcT T).2 hfo,
      fun w => (outputs_toSrcT T w _).2 (hT w)⟩
  · rintro ⟨T, hp, hfo, hT⟩
    exact ⟨ofSrcT T, (proper_ofSrcT T).2 hp, (allFO_ofSrcT T).2 hfo,
      fun w => (outputs_ofSrcT T w _).2 (hT w)⟩

end Transductions

/-! ## `k`-types -/

section KTypes

variable {A : Type}

/-- The bijection between the concept's and the source's types of `k`-types, by induction
on `k`: the identity of `Unit` for `k = 0`, and the induced bijection of the sets of
triples for `k + 1`. -/
def tpEquiv (A : Type) : (k : ℕ) → TpType A k ≃ Transducers.TpType A k
  | 0 => Equiv.refl Unit
  | k + 1 => Equiv.Set.congr ((tpEquiv A k).prodCongr ((Equiv.refl A).prodCongr (tpEquiv A k)))

/-- The `k`-type of a string is transported along `tpEquiv`. -/
lemma tpEquiv_tp : ∀ (k : ℕ) (w : List A), tpEquiv A k (tp k w) = Transducers.tp k w
  | 0, _ => rfl
  | k + 1, w => by
    apply Set.ext
    rintro ⟨t₁, a, t₂⟩
    simp only [tpEquiv, tp, Transducers.tp, Equiv.Set.congr]
    constructor
    · rintro ⟨x, ⟨w₁, a', w₂, rfl, rfl⟩, hx⟩
      refine ⟨w₁, a', w₂, rfl, ?_⟩
      rw [← hx]
      simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, tpEquiv_tp k]
    · rintro ⟨w₁, a', w₂, rfl, h⟩
      refine ⟨(tp k w₁, a', tp k w₂), ⟨w₁, a', w₂, rfl, rfl⟩, ?_⟩
      rw [h]
      simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, tpEquiv_tp k]

lemma tp_eq_iff (k : ℕ) (w v : List A) :
    tp k w = tp k v ↔ Transducers.tp k w = Transducers.tp k v := by
  rw [← tpEquiv_tp, ← tpEquiv_tp]
  exact (tpEquiv A k).injective.eq_iff.symm

end KTypes

end Lax314295Proofs.Bridge
