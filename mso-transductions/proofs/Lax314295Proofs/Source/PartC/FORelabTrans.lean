/-
From first-order relabellings to first-order transductions.

An mso relabelling (Definition `def:mso-relabeling`) outputs, at every position of the input,
the string `out i` attached to the unique formula `form i` that holds at that
position (and the fixed string `emptyOut` on the empty input).  This is the
special case of an mso transduction (Definition `def:mso-transduction`) in which the copies of a
position are indexed by the pairs `(i, m)` with `i` an index of the relabelling
and `m` a position of `out i`, the extra elements are the positions of
`emptyOut`, and the order is the lexicographic order.  If the relabelling is
first-order, so is the resulting transduction.

This is the first ingredient of the easy inclusion of Theorem
`nolabel:thm-fo-transduction-into-primes`. -/
import Lax314295Proofs.Source.PartC.ITransBuild
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace FORelab

variable {A B : Type}

/-- A formula that is true or false according to a decidable condition. -/
lemma sat_ite (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (c : Prop) [Decidable c] :
    MSO.Sat w fo so (if c then MSO.tt else MSO.ff) ↔ c := by
  by_cases h : c <;> simp [h]

lemma isFO_ite (c : Prop) [Decidable c] : (if c then (MSO.tt : MSO A) else MSO.ff).IsFO := by
  by_cases h : c
  · rw [if_pos h]; trivial
  · rw [if_neg h]; trivial

open scoped Classical in
/-- The mso transduction attached to an mso relabelling: the copies of a
position `p` are the pairs `(i, m)` with `m` a position of the output string
`out i`, and the copy `(i, m)` is selected at `p` when the formula `form i`
holds at `p`.  The extra elements are the positions of `emptyOut`, selected only
when the input is empty. -/
noncomputable def trans (R : MSORelabelling A B) : ITrans A B where
  P := Σ i : R.Idx, Fin (R.out i).length
  E := Fin R.emptyOut.length
  finP := by haveI := R.finIdx; infer_instance
  finE := inferInstance
  univP := fun im => R.form im.1
  univC := fun _ => MSO.emptyF A
  labP := fun im b => if (R.out im.1).get im.2 = b then MSO.tt else MSO.ff
  labC := fun j b => if R.emptyOut.get j = b then MSO.tt else MSO.ff
  ordPP := fun im im' => MSO.or (MSO.not (MSO.le 1 0))
      (MSO.and (MSO.eqVar 0 1) (if (im.2 : ℕ) ≤ (im'.2 : ℕ) then MSO.tt else MSO.ff))
  ordPC := fun _ _ => MSO.tt
  ordCP := fun _ _ => MSO.tt
  ordCC := fun j j' => if (j : ℕ) ≤ (j' : ℕ) then MSO.tt else MSO.ff

variable (R : MSORelabelling A B)

lemma selected_inl_iff (w : List A) (i : R.Idx) (m : Fin (R.out i).length) (p : ℕ) :
    (trans R).selected w (Sum.inl (⟨i, m⟩, p)) ↔
      p < w.length ∧ MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form i) := Iff.rfl

lemma selected_inr_iff (w : List A) (j : Fin R.emptyOut.length) :
    (trans R).selected w (Sum.inr j) ↔ w = [] := by
  show MSO.Sat w (fun _ => 0) (fun _ => ∅) (MSO.emptyF A) ↔ w = []
  exact MSO.sat_emptyF w _ _

/-- A copy of a position and an extra element are never selected together. -/
lemma not_selected_both {w : List A} {i : R.Idx} {m : Fin (R.out i).length} {p : ℕ}
    {j : Fin R.emptyOut.length} (hx : (trans R).selected w (Sum.inl (⟨i, m⟩, p)))
    (hy : (trans R).selected w (Sum.inr j)) : False := by
  rw [(selected_inr_iff R w j).1 hy] at hx
  exact absurd hx.1 (by simp)

open scoped Classical in
lemma ordRel_inl_iff (w : List A) (i : R.Idx) (m : Fin (R.out i).length) (i' : R.Idx)
    (m' : Fin (R.out i').length) (p p' : ℕ) :
    (trans R).ordRel w (Sum.inl (⟨i, m⟩, p)) (Sum.inl (⟨i', m'⟩, p')) ↔
      (p < p' ∨ (p = p' ∧ (m : ℕ) ≤ (m' : ℕ))) := by
  rw [show (trans R).ordRel w (Sum.inl (⟨i, m⟩, p)) (Sum.inl (⟨i', m'⟩, p')) ↔
      (¬ MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅) (MSO.le 1 0)) ∨
      (MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅) (MSO.eqVar 0 1) ∧
        MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅)
          (if (m : ℕ) ≤ (m' : ℕ) then MSO.tt else MSO.ff)) from Iff.rfl]
  rw [sat_ite, MSO.sat_eqVar]
  simp only [MSO.Sat]
  norm_num

open scoped Classical in
lemma ordRel_inr_iff (w : List A) (j j' : Fin R.emptyOut.length) :
    (trans R).ordRel w (Sum.inr j) (Sum.inr j') ↔ (j : ℕ) ≤ (j' : ℕ) := by
  rw [show (trans R).ordRel w (Sum.inr j) (Sum.inr j') ↔
      MSO.Sat w (fun _ => 0) (fun _ => ∅)
        (if (j : ℕ) ≤ (j' : ℕ) then MSO.tt else MSO.ff) from Iff.rfl]
  exact sat_ite _ _ _ _

open scoped Classical in
lemma labRel_inl_iff (w : List A) (i : R.Idx) (m : Fin (R.out i).length) (p : ℕ) (b : B) :
    (trans R).labRel w (Sum.inl (⟨i, m⟩, p)) b ↔ (R.out i).get m = b := by
  rw [show (trans R).labRel w (Sum.inl (⟨i, m⟩, p)) b ↔
      MSO.Sat w (fun _ => p) (fun _ => ∅)
        (if (R.out i).get m = b then MSO.tt else MSO.ff) from Iff.rfl]
  exact sat_ite _ _ _ _

open scoped Classical in
lemma labRel_inr_iff (w : List A) (j : Fin R.emptyOut.length) (b : B) :
    (trans R).labRel w (Sum.inr j) b ↔ R.emptyOut.get j = b := by
  rw [show (trans R).labRel w (Sum.inr j) b ↔
      MSO.Sat w (fun _ => 0) (fun _ => ∅)
        (if R.emptyOut.get j = b then MSO.tt else MSO.ff) from Iff.rfl]
  exact sat_ite _ _ _ _

/-- At every position exactly one formula of the relabelling holds. -/
lemma unique_index {w : List A} {p : ℕ} (hp : p < w.length) {i i' : R.Idx}
    (h : MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form i))
    (h' : MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form i')) : i = i' := by
  obtain ⟨i₀, -, hu⟩ := R.unique w p hp
  rw [hu i h, hu i' h']

lemma proper : (trans R).Proper := by
  intro w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (⟨⟨i, m⟩, p⟩ | j) _
    · exact ⟨(R.out i).get m, (labRel_inl_iff R w i m p _).2 rfl,
        fun b hb => ((labRel_inl_iff R w i m p b).1 hb).symm⟩
    · exact ⟨R.emptyOut.get j, (labRel_inr_iff R w j _).2 rfl,
        fun b hb => ((labRel_inr_iff R w j b).1 hb).symm⟩
  · rintro (⟨⟨i, m⟩, p⟩ | j) _
    · exact (ordRel_inl_iff R w i m i m p p).2 (Or.inr ⟨rfl, le_refl _⟩)
    · exact (ordRel_inr_iff R w j j).2 (le_refl _)
  · rintro (⟨⟨i, m⟩, p⟩ | j) (⟨⟨i', m'⟩, p'⟩ | j') hx hy h₁ h₂
    · rw [ordRel_inl_iff] at h₁ h₂
      have hpp : p = p' := by omega
      subst hpp
      have hii : i = i' := unique_index R hx.1 hx.2 hy.2
      subst hii
      have : m = m' := Fin.ext (by omega)
      subst this
      rfl
    · exact (not_selected_both R hx hy).elim
    · exact (not_selected_both R hy hx).elim
    · rw [ordRel_inr_iff] at h₁ h₂
      have : j = j' := Fin.ext (le_antisymm h₁ h₂)
      rw [this]
  · rintro (⟨⟨i, m⟩, p⟩ | j) (⟨⟨i', m'⟩, p'⟩ | j') (⟨⟨i'', m''⟩, p''⟩ | j'') hx hy hz h₁ h₂
    · rw [ordRel_inl_iff] at h₁ h₂ ⊢
      omega
    · exact (not_selected_both R hx hz).elim
    · exact (not_selected_both R hx hy).elim
    · exact (not_selected_both R hx hy).elim
    · exact (not_selected_both R hy hx).elim
    · exact (not_selected_both R hy hx).elim
    · exact (not_selected_both R hz hx).elim
    · rw [ordRel_inr_iff] at h₁ h₂ ⊢
      omega
  · rintro (⟨⟨i, m⟩, p⟩ | j) (⟨⟨i', m'⟩, p'⟩ | j') hx hy
    · rw [ordRel_inl_iff, ordRel_inl_iff]
      rcases lt_trichotomy p p' with h | h | h
      · exact Or.inl (Or.inl h)
      · rcases le_total (m : ℕ) (m' : ℕ) with hm | hm
        · exact Or.inl (Or.inr ⟨h, hm⟩)
        · exact Or.inr (Or.inr ⟨h.symm, hm⟩)
      · exact Or.inr (Or.inl h)
    · exact (not_selected_both R hx hy).elim
    · exact (not_selected_both R hy hx).elim
    · rw [ordRel_inr_iff, ordRel_inr_iff]
      exact le_total _ _

open scoped Classical in
lemma allFO (hFO : R.AllFO) : (trans R).AllFO := by
  refine ⟨fun im => hFO im.1, fun _ => MSO.isFO_emptyF, fun im b => isFO_ite _,
    fun j b => isFO_ite _, fun im im' => ⟨trivial, MSO.isFO_eqVar 0 1, isFO_ite _⟩,
    fun _ _ => trivial, fun _ _ => trivial, fun j j' => isFO_ite _⟩

/-- The output of the transduction on the empty input. -/
lemma outputs_nil : (trans R).Outputs [] R.emptyOut := by
  refine (trans R).outputs_of_forall₂
    (List.ofFn (fun j : Fin R.emptyOut.length => Sum.inr j)) ?_ ?_ ?_ ?_
  · rw [List.nodup_ofFn]
    intro j j' h
    simpa using h
  · rintro (⟨⟨i, m⟩, p⟩ | j)
    · constructor
      · intro hx
        rw [List.mem_ofFn] at hx
        obtain ⟨j, hj⟩ := hx
        exact absurd hj (by simp)
      · intro hx
        exact absurd hx.1 (by simp)
    · exact ⟨fun _ => (selected_inr_iff R [] j).2 rfl, fun _ => List.mem_ofFn.2 ⟨j, rfl⟩⟩
  · rw [List.pairwise_ofFn]
    intro j j' hjj
    exact (ordRel_inr_iff R [] j j').2 (le_of_lt hjj)
  · rw [List.forall₂_iff_get]
    refine ⟨by simp, fun k h₁ h₂ => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact (labRel_inr_iff R [] _ _).2 rfl

/-- The output of the transduction on a nonempty input. -/
lemma outputs_cons {w : List A} (hw : w ≠ []) {g : ℕ → R.Idx}
    (hg : ∀ p < w.length, MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form (g p))) :
    (trans R).Outputs w (((List.range w.length).map (fun p => R.out (g p))).flatten) := by
  classical
  set es : List ((trans R).Elt) :=
    (List.range w.length).flatMap
      (fun p => List.ofFn (fun m : Fin (R.out (g p)).length =>
        (Sum.inl (⟨⟨g p, m⟩, p⟩) : (trans R).Elt))) with hes
  have hmemp : ∀ (i : R.Idx) (m : Fin (R.out i).length) (p : ℕ),
      (Sum.inl (⟨⟨i, m⟩, p⟩) : (trans R).Elt) ∈ es ↔ p < w.length ∧ i = g p := by
    intro i m p
    rw [hes, List.mem_flatMap]
    constructor
    · rintro ⟨q, hq, hmem⟩
      rw [List.mem_ofFn] at hmem
      obtain ⟨m', hm'⟩ := hmem
      rw [List.mem_range] at hq
      have h1 : q = p := by
        have := congrArg (fun x => (Sum.getLeft? x).map Prod.snd) hm'
        simpa using this
      subst h1
      have h2 : g q = i := by
        have := congrArg (fun x => (Sum.getLeft? x).map (fun y => y.1.1)) hm'
        simpa using this
      exact ⟨hq, h2.symm⟩
    · rintro ⟨hp, rfl⟩
      exact ⟨p, List.mem_range.2 hp, List.mem_ofFn.2 ⟨m, rfl⟩⟩
  refine (trans R).outputs_of_forall₂ es ?_ ?_ ?_ ?_
  · rw [hes, List.nodup_flatMap]
    constructor
    · intro p _
      rw [List.nodup_ofFn]
      intro m m' h
      have hval := congrArg (fun x : (trans R).Elt =>
        match x with
        | Sum.inl (im, _) => (im.2 : ℕ)
        | Sum.inr _ => 0) h
      exact Fin.ext (by simpa using hval)
    · rw [List.pairwise_iff_getElem]
      intro a b ha hb hab x hx hx'
      simp only [List.mem_ofFn] at hx hx'
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨m', hm'⟩ := hx'
      have hq : (List.range w.length)[a] = (List.range w.length)[b] := by
        have := congrArg (fun x => (Sum.getLeft? x).map Prod.snd) hm'
        simpa using this.symm
      simp only [List.getElem_range] at hq
      omega
  · rintro (⟨⟨i, m⟩, p⟩ | j)
    · rw [hmemp, selected_inl_iff]
      constructor
      · rintro ⟨hp, rfl⟩
        exact ⟨hp, hg p hp⟩
      · rintro ⟨hp, hsat⟩
        exact ⟨hp, unique_index R hp hsat (hg p hp)⟩
    · constructor
      · intro hx
        rw [hes, List.mem_flatMap] at hx
        obtain ⟨q, -, hmem⟩ := hx
        rw [List.mem_ofFn] at hmem
        obtain ⟨m, hm⟩ := hmem
        exact absurd hm (by simp)
      · intro hx
        exact absurd ((selected_inr_iff R w j).1 hx) hw
  · rw [hes, List.pairwise_flatMap]
    constructor
    · intro p _
      rw [List.pairwise_ofFn]
      intro m m' hmm
      exact (ordRel_inl_iff R w _ _ _ _ p p).2 (Or.inr ⟨rfl, le_of_lt hmm⟩)
    · rw [List.pairwise_iff_getElem]
      intro a b ha hb hab x hx y hy
      simp only [List.mem_ofFn] at hx hy
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨m', rfl⟩ := hy
      simp only [List.length_range] at ha hb
      rw [ordRel_inl_iff]
      simp only [List.getElem_range]
      exact Or.inl hab
  · rw [show ((List.range w.length).map (fun p => R.out (g p))).flatten =
      (List.range w.length).flatMap (fun p => R.out (g p)) from (List.flatMap_def).symm]
    rw [hes]
    refine forall₂_flatMap _ (fun p _ => ?_)
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun k h₁ h₂ => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    rw [labRel_inl_iff]
    simp

end FORelab

/-- **A first-order relabelling is a first-order transduction.** -/
theorem isFOTransduction_of_isFORelabelling {A B : Type} {f : List A → List B}
    (hf : IsFORelabelling f) : IsFOTransduction f := by
  obtain ⟨R, hFO, hR⟩ := hf
  refine (FORelab.trans R).isFOTransduction (FORelab.proper R) (FORelab.allFO R hFO) ?_
  intro w
  rcases hR w with ⟨hnil, hout⟩ | ⟨hne, g, hg, hout⟩
  · subst hnil
    rw [hout]
    exact FORelab.outputs_nil R
  · rw [hout]
    exact FORelab.outputs_cons R hne hg

end Lax314295Proofs.Transducers
