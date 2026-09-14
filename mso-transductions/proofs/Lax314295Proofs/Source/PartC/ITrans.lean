/-
Mso transductions with arbitrary finite index sets.

Definition `def:mso-transduction` presents the output universe of an mso transduction by the
linear type `τ = k · n + c`, and accordingly `Transducers.MSOTransduction`
indexes its formulas by `Fin k` and `Fin c`.  The transductions that are built
in `RequestProject/PartC/FOTransComp.lean` (the composition of two
transductions) and in `RequestProject/PartC/FOTransPrimeComp.lean` (the prime
functions) have index sets that are naturally *products* and *sums* of such
types, and threading the bijections `Fin k × Fin l ≃ Fin (k * l)` through every
construction is pure noise.

This file therefore introduces `Transducers.ITrans`, the same notion with two
arbitrary *finite* index types, together with the transport theorem
`Transducers.ITrans.isFOTransduction`: a proper, first-order `ITrans` computing
`f` witnesses `IsFOTransduction f`.
-/
import Lax916827Proofs.Source.PartC.MSODef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

/-- An mso transduction (Definition `def:mso-transduction`) whose copies and extra elements are
indexed by arbitrary finite types. -/
structure ITrans (A B : Type) where
  /-- The index type of the copies of the input positions. -/
  P : Type
  /-- The index type of the extra elements. -/
  E : Type
  /-- The copies are finitely many. -/
  finP : Finite P
  /-- The extra elements are finitely many. -/
  finE : Finite E
  /-- Universe formulas for the copies of the positions; free variable `x₀`. -/
  univP : P → MSO A
  /-- Universe formulas for the extra elements; evaluated at the position `0`. -/
  univC : E → MSO A
  /-- Letter formulas for the copies of the positions; free variable `x₀`. -/
  labP : P → B → MSO A
  /-- Letter formulas for the extra elements; evaluated at the position `0`. -/
  labC : E → B → MSO A
  /-- Order formulas between two copies of positions; free variables `x₀, x₁`. -/
  ordPP : P → P → MSO A
  /-- Order formulas between a copy of a position and an extra element. -/
  ordPC : P → E → MSO A
  /-- Order formulas between an extra element and a copy of a position. -/
  ordCP : E → P → MSO A
  /-- Order formulas between two extra elements. -/
  ordCC : E → E → MSO A

namespace ITrans

variable {A B : Type}

/-- The elements of the output universe, before selection. -/
abbrev Elt (T : ITrans A B) : Type := (T.P × ℕ) ⊕ T.E

/-- The elements selected by the universe formulas. -/
def selected (T : ITrans A B) (w : List A) : T.Elt → Prop
  | Sum.inl (i, p) => p < w.length ∧ MSO.Sat w (fun _ => p) (fun _ => ∅) (T.univP i)
  | Sum.inr j => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.univC j)

/-- The order defined by the order formulas. -/
def ordRel (T : ITrans A B) (w : List A) : T.Elt → T.Elt → Prop
  | Sum.inl (i, p), Sum.inl (i', p') =>
      MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅) (T.ordPP i i')
  | Sum.inl (i, p), Sum.inr j => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordPC i j)
  | Sum.inr j, Sum.inl (i, p) => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordCP j i)
  | Sum.inr j, Sum.inr j' => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.ordCC j j')

/-- The labelling defined by the letter formulas. -/
def labRel (T : ITrans A B) (w : List A) : T.Elt → B → Prop
  | Sum.inl (i, p), b => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.labP i b)
  | Sum.inr j, b => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.labC j b)

/-- The semantics: the output string consists of the selected elements, ordered
by the order formulas and labelled by the letter formulas. -/
def Outputs (T : ITrans A B) (w : List A) (v : List B) : Prop :=
  ∃ es : List T.Elt,
    es.Nodup ∧
    (∀ x, x ∈ es ↔ T.selected w x) ∧
    (∀ (i j : ℕ) (hi : i < es.length) (hj : j < es.length),
      i < j → T.ordRel w (es.get ⟨i, hi⟩) (es.get ⟨j, hj⟩)) ∧
    es.length = v.length ∧
    ∀ (i : ℕ) (hi : i < es.length) (hi' : i < v.length),
      T.labRel w (es.get ⟨i, hi⟩) (v.get ⟨i, hi'⟩)

/-- The requirements of Definition `def:mso-transduction`. -/
def Proper (T : ITrans A B) : Prop :=
  ∀ w : List A,
    (∀ x, T.selected w x → ∃! b, T.labRel w x b) ∧
    (∀ x, T.selected w x → T.ordRel w x x) ∧
    (∀ x y, T.selected w x → T.selected w y →
      T.ordRel w x y → T.ordRel w y x → x = y) ∧
    (∀ x y z, T.selected w x → T.selected w y → T.selected w z →
      T.ordRel w x y → T.ordRel w y z → T.ordRel w x z) ∧
    (∀ x y, T.selected w x → T.selected w y → T.ordRel w x y ∨ T.ordRel w y x)

/-- All formulas of the transduction are first-order. -/
def AllFO (T : ITrans A B) : Prop :=
  (∀ i, (T.univP i).IsFO) ∧ (∀ j, (T.univC j).IsFO) ∧
  (∀ i b, (T.labP i b).IsFO) ∧ (∀ j b, (T.labC j b).IsFO) ∧
  (∀ i i', (T.ordPP i i').IsFO) ∧ (∀ i j, (T.ordPC i j).IsFO) ∧
  (∀ j i, (T.ordCP j i).IsFO) ∧ (∀ j j', (T.ordCC j j').IsFO)

/-! ## Transport to `MSOTransduction` -/

/-- The `MSOTransduction` obtained by re-indexing an `ITrans` along two
bijections with `Fin`. -/
def toMSO (T : ITrans A B) {np ne : ℕ} (eP : T.P ≃ Fin np) (eE : T.E ≃ Fin ne) :
    MSOTransduction A B where
  copies := np
  extra := ne
  univP := fun i => T.univP (eP.symm i)
  univC := fun j => T.univC (eE.symm j)
  labP := fun i b => T.labP (eP.symm i) b
  labC := fun j b => T.labC (eE.symm j) b
  ordPP := fun i i' => T.ordPP (eP.symm i) (eP.symm i')
  ordPC := fun i j => T.ordPC (eP.symm i) (eE.symm j)
  ordCP := fun j i => T.ordCP (eE.symm j) (eP.symm i)
  ordCC := fun j j' => T.ordCC (eE.symm j) (eE.symm j')

variable (T : ITrans A B) {np ne : ℕ} (eP : T.P ≃ Fin np) (eE : T.E ≃ Fin ne)

/-- The bijection between the elements of `T.toMSO` and the elements of `T`. -/
def eltEquiv : (T.toMSO eP eE).Elt ≃ T.Elt :=
  (Equiv.sumCongr (Equiv.prodCongr eP.symm (Equiv.refl ℕ)) eE.symm)

@[simp] lemma eltEquiv_inl (i : Fin np) (p : ℕ) :
    T.eltEquiv eP eE (Sum.inl (i, p)) = Sum.inl (eP.symm i, p) := rfl

@[simp] lemma eltEquiv_inr (j : Fin ne) :
    T.eltEquiv eP eE (Sum.inr j) = Sum.inr (eE.symm j) := rfl

lemma selected_toMSO (w : List A) (x : (T.toMSO eP eE).Elt) :
    (T.toMSO eP eE).selected w x ↔ T.selected w (T.eltEquiv eP eE x) := by
  rcases x with ⟨i, p⟩ | j <;> exact Iff.rfl

lemma ordRel_toMSO (w : List A) (x y : (T.toMSO eP eE).Elt) :
    (T.toMSO eP eE).ordRel w x y ↔ T.ordRel w (T.eltEquiv eP eE x) (T.eltEquiv eP eE y) := by
  rcases x with ⟨i, p⟩ | j <;> rcases y with ⟨i', p'⟩ | j' <;> exact Iff.rfl

lemma labRel_toMSO (w : List A) (x : (T.toMSO eP eE).Elt) (b : B) :
    (T.toMSO eP eE).labRel w x b ↔ T.labRel w (T.eltEquiv eP eE x) b := by
  rcases x with ⟨i, p⟩ | j <;> exact Iff.rfl

lemma proper_toMSO (hP : T.Proper) : (T.toMSO eP eE).Proper := by
  intro w
  obtain ⟨hlab, hrefl, hanti, htrans, htot⟩ := hP w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb, hu⟩ := hlab _ ((T.selected_toMSO eP eE w x).1 hx)
    exact ⟨b, (T.labRel_toMSO eP eE w x b).2 hb,
      fun b' hb' => hu b' ((T.labRel_toMSO eP eE w x b').1 hb')⟩
  · intro x hx
    exact (T.ordRel_toMSO eP eE w x x).2 (hrefl _ ((T.selected_toMSO eP eE w x).1 hx))
  · intro x y hx hy hxy hyx
    have := hanti _ _ ((T.selected_toMSO eP eE w x).1 hx) ((T.selected_toMSO eP eE w y).1 hy)
      ((T.ordRel_toMSO eP eE w x y).1 hxy) ((T.ordRel_toMSO eP eE w y x).1 hyx)
    exact (T.eltEquiv eP eE).injective this
  · intro x y z hx hy hz hxy hyz
    exact (T.ordRel_toMSO eP eE w x z).2
      (htrans _ _ _ ((T.selected_toMSO eP eE w x).1 hx) ((T.selected_toMSO eP eE w y).1 hy)
        ((T.selected_toMSO eP eE w z).1 hz) ((T.ordRel_toMSO eP eE w x y).1 hxy)
        ((T.ordRel_toMSO eP eE w y z).1 hyz))
  · intro x y hx hy
    rcases htot _ _ ((T.selected_toMSO eP eE w x).1 hx) ((T.selected_toMSO eP eE w y).1 hy) with
      h | h
    · exact Or.inl ((T.ordRel_toMSO eP eE w x y).2 h)
    · exact Or.inr ((T.ordRel_toMSO eP eE w y x).2 h)

lemma allFO_toMSO (hFO : T.AllFO) : (T.toMSO eP eE).AllFO :=
  ⟨fun _ => hFO.1 _, fun _ => hFO.2.1 _, fun _ _ => hFO.2.2.1 _ _, fun _ _ => hFO.2.2.2.1 _ _,
    fun _ _ => hFO.2.2.2.2.1 _ _, fun _ _ => hFO.2.2.2.2.2.1 _ _,
    fun _ _ => hFO.2.2.2.2.2.2.1 _ _, fun _ _ => hFO.2.2.2.2.2.2.2 _ _⟩

lemma outputs_toMSO {w : List A} {v : List B} (h : T.Outputs w v) :
    (T.toMSO eP eE).Outputs w v := by
  obtain ⟨es, hnd, hmem, hord, hlen, hlab⟩ := h
  refine ⟨es.map (T.eltEquiv eP eE).symm, ?_, ?_, ?_, ?_, ?_⟩
  · exact hnd.map (T.eltEquiv eP eE).symm.injective
  · intro x
    rw [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [T.selected_toMSO eP eE, Equiv.apply_symm_apply]
      exact (hmem y).1 hy
    · intro hx
      refine ⟨T.eltEquiv eP eE x, (hmem _).2 ((T.selected_toMSO eP eE w x).1 hx), ?_⟩
      simp
  · intro i j hi hj hij
    simp only [List.get_eq_getElem, List.getElem_map]
    rw [T.ordRel_toMSO eP eE, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simp only [List.length_map] at hi hj
    exact hord i j hi hj hij
  · rw [List.length_map]; exact hlen
  · intro i hi hi'
    simp only [List.get_eq_getElem, List.getElem_map]
    rw [T.labRel_toMSO eP eE, Equiv.apply_symm_apply]
    simp only [List.length_map] at hi
    exact hlab i hi hi'

/-- A proper first-order `ITrans` computing `f` witnesses that `f` is a
first-order transduction. -/
theorem isFOTransduction {f : List A → List B} (hP : T.Proper) (hFO : T.AllFO)
    (hf : ∀ w, T.Outputs w (f w)) : IsFOTransduction f := by
  haveI := T.finP
  haveI := T.finE
  obtain ⟨np, ⟨eP⟩⟩ := Finite.exists_equiv_fin T.P
  obtain ⟨ne, ⟨eE⟩⟩ := Finite.exists_equiv_fin T.E
  exact ⟨T.toMSO eP eE, T.proper_toMSO eP eE hP, T.allFO_toMSO eP eE hFO,
    fun w => T.outputs_toMSO eP eE (hf w)⟩

end ITrans

/-! ## From `MSOTransduction` to `ITrans` -/

namespace MSOTransduction

variable {A B : Type}

/-- Every mso transduction is an `ITrans`, with the copies indexed by
`Fin copies` and the extra elements by `Fin extra`. -/
def toI (T : MSOTransduction A B) : ITrans A B where
  P := Fin T.copies
  E := Fin T.extra
  finP := inferInstance
  finE := inferInstance
  univP := T.univP
  univC := T.univC
  labP := T.labP
  labC := T.labC
  ordPP := T.ordPP
  ordPC := T.ordPC
  ordCP := T.ordCP
  ordCC := T.ordCC

variable (T : MSOTransduction A B)

lemma selected_toI (w : List A) (x : T.Elt) : (MSOTransduction.toI T).selected w x ↔ T.selected w x := by
  rcases x with ⟨i, p⟩ | j <;> exact Iff.rfl

lemma ordRel_toI (w : List A) (x y : T.Elt) : (MSOTransduction.toI T).ordRel w x y ↔ T.ordRel w x y := by
  rcases x with ⟨i, p⟩ | j <;> rcases y with ⟨i', p'⟩ | j' <;> exact Iff.rfl

lemma labRel_toI (w : List A) (x : T.Elt) (b : B) : (MSOTransduction.toI T).labRel w x b ↔ T.labRel w x b := by
  rcases x with ⟨i, p⟩ | j <;> exact Iff.rfl

lemma outputs_toI {w : List A} {v : List B} (h : T.Outputs w v) : (MSOTransduction.toI T).Outputs w v := by
  obtain ⟨es, hnd, hmem, hord, hlen, hlab⟩ := h
  refine ⟨es, hnd, fun x => ?_, fun i j hi hj hij => ?_, hlen, fun i hi hi' => ?_⟩
  · rw [MSOTransduction.selected_toI T w x]; exact hmem x
  · rw [MSOTransduction.ordRel_toI T w _ _]; exact hord i j hi hj hij
  · rw [MSOTransduction.labRel_toI T w _ _]; exact hlab i hi hi'

lemma proper_toI (h : T.Proper) : (MSOTransduction.toI T).Proper := by
  intro w
  obtain ⟨hlab, hrefl, hanti, htrans, htot⟩ := h w
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x y hx hy hxy hyx => ?_,
    fun x y z hx hy hz hxy hyz => ?_, fun x y hx hy => ?_⟩
  · obtain ⟨b, hb, hu⟩ := hlab x ((MSOTransduction.selected_toI T w x).1 hx)
    exact ⟨b, (MSOTransduction.labRel_toI T w x b).2 hb, fun b' hb' => hu b' ((MSOTransduction.labRel_toI T w x b').1 hb')⟩
  · exact (MSOTransduction.ordRel_toI T w x x).2 (hrefl x ((MSOTransduction.selected_toI T w x).1 hx))
  · exact hanti x y ((MSOTransduction.selected_toI T w x).1 hx) ((MSOTransduction.selected_toI T w y).1 hy)
      ((MSOTransduction.ordRel_toI T w x y).1 hxy) ((MSOTransduction.ordRel_toI T w y x).1 hyx)
  · exact (MSOTransduction.ordRel_toI T w x z).2 (htrans x y z ((MSOTransduction.selected_toI T w x).1 hx)
      ((MSOTransduction.selected_toI T w y).1 hy) ((MSOTransduction.selected_toI T w z).1 hz)
      ((MSOTransduction.ordRel_toI T w x y).1 hxy) ((MSOTransduction.ordRel_toI T w y z).1 hyz))
  · rcases htot x y ((MSOTransduction.selected_toI T w x).1 hx) ((MSOTransduction.selected_toI T w y).1 hy) with h' | h'
    · exact Or.inl ((MSOTransduction.ordRel_toI T w x y).2 h')
    · exact Or.inr ((MSOTransduction.ordRel_toI T w y x).2 h')

lemma allFO_toI (h : T.AllFO) : (MSOTransduction.toI T).AllFO :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2⟩

end MSOTransduction

/-- An `ITrans` presentation of a first-order transduction. -/
theorem exists_itrans_of_isFOTransduction {A B : Type} {f : List A → List B}
    (hf : IsFOTransduction f) :
    ∃ T : ITrans A B, T.Proper ∧ T.AllFO ∧ ∀ w, T.Outputs w (f w) := by
  obtain ⟨T, hP, hFO, hO⟩ := hf
  exact ⟨(MSOTransduction.toI T), (MSOTransduction.proper_toI T) hP, (MSOTransduction.allFO_toI T) hFO, fun w => (MSOTransduction.outputs_toI T) (hO w)⟩

end Lax314295Proofs.Transducers
