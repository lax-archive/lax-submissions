/- Claim `claim:mso-annotation-regular` of *Transducers* (M. Bojańczyk): for an mso
relabelling, the set of strings over the alphabet `A × Φ` in which every position is labelled by a
formula that holds in that position is a regular language.

The construction is a corollary of Lemma `lem:mso-free-variables`
(`RequestProject/PartC/MSOAnnot.lean`).  For a fixed formula `φ` the set of
strings over `Γ × 2` in which exactly one position is marked and in which `φ`
holds at the marked position is regular (`isRegular_markedSat`): it is the
inverse image, under a letter-to-letter map, of the language of annotated
strings of Lemma `lem:mso-free-variables`, all first-order variables being sent to the marked
position and all second-order variables to the empty set.

The complement of the language of Claim `claim:mso-annotation-regular` is, for a fixed
index `x`, the projection of that language (for the formula `¬ φ_x`), intersected with the condition
that the marked position carries the index `x`; the language of the claim is then the intersection
over the finitely many indices `x`. -/
import Lax916827Proofs.Source.PartC.MSOAnnot
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace MSORelab

open MSO RegAut MSOAnnot

/-! ## Strings with one marked position -/

section Marked

variable {A Γ : Type}

/-- The marked position of a string over `Γ × 2`. -/
def markPos (z : List (Γ × Bool)) : ℕ := z.findIdx (fun y => y.2)

/-- The strings over `Γ × 2` with exactly one marked position, in which `φ`
holds at the marked position. -/
def MarkedSat (lett : Γ → A) (φ : MSO A) : Language (Γ × Bool) :=
  {z | MarksOnce (fun y => y.2) z ∧
    MSO.Sat ((z.map Prod.fst).map lett) (fun _ => markPos z) (fun _ => ∅) φ}

/-- The letter-to-letter map sending a marked letter to the annotated letter in
which every first-order variable is placed at the marked position and every
second-order variable is empty. -/
def annMark (lett : Γ → A) (k l : ℕ) : (Γ × Bool) → MSOAnnot.Ann A k l :=
  fun y => (lett y.1, fun _ => y.2, fun _ => false)

variable (lett : Γ → A) (k l : ℕ)

lemma markedAt_annMark (i : Fin k) (z : List (Γ × Bool)) (q : ℕ) :
    MarkedAt (MSOAnnot.foBit (A := A) (l := l) i) (z.map (annMark lett k l)) q ↔
      MarkedAt (fun y : Γ × Bool => y.2) z q :=
  (markedAt_map (f := annMark lett k l) (P := fun y : Γ × Bool => y.2)
    (Q := MSOAnnot.foBit (A := A) (l := l) i) (fun _ => rfl) z q).symm

lemma not_markedAt_annMark (j : Fin l) (z : List (Γ × Bool)) (q : ℕ) :
    ¬ MarkedAt (MSOAnnot.soBit (A := A) (k := k) j) (z.map (annMark lett k l)) q := by
  rintro ⟨y, hy, hby⟩
  rw [List.getElem?_map] at hy
  obtain ⟨y', -, rfl⟩ := Option.map_eq_some_iff.1 hy
  simp [MSOAnnot.soBit, annMark] at hby

lemma valid_annMark_iff (hk : 0 < k) (z : List (Γ × Bool)) :
    MSOAnnot.Valid (z.map (annMark lett k l)) ↔ MarksOnce (fun y : Γ × Bool => y.2) z := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h ⟨0, hk⟩
    exact ⟨p, fun q => (markedAt_annMark lett k l ⟨0, hk⟩ z q).symm.trans (hp q)⟩
  · rintro ⟨p, hp⟩ i
    exact ⟨p, fun q => (markedAt_annMark lett k l i z q).trans (hp q)⟩

lemma foOf_annMark {z : List (Γ × Bool)} (hz : MarksOnce (fun y : Γ × Bool => y.2) z)
    {m : ℕ} (hm : m < k) :
    MSOAnnot.foOf (z.map (annMark lett k l)) m = markPos z := by
  obtain ⟨p, hp⟩ := hz
  rw [MSOAnnot.foOf_of_lt _ hm]
  rw [findIdx_eq_of_marksOnce (P := MSOAnnot.foBit (A := A) (l := l) ⟨m, hm⟩)
    (fun q => (markedAt_annMark lett k l ⟨m, hm⟩ z q).trans (hp q))]
  exact (findIdx_eq_of_marksOnce hp).symm

lemma soOf_annMark (z : List (Γ × Bool)) (m : ℕ) :
    MSOAnnot.soOf (z.map (annMark lett k l)) m = (∅ : Set ℕ) := by
  by_cases hm : m < l
  · rw [MSOAnnot.soOf_of_lt _ hm]
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_markedAt_annMark lett k l ⟨m, hm⟩ z q
  · exact MSOAnnot.soOf_of_not_lt _ hm

/-- The language of strings with one marked position at which `φ` holds is
regular. -/
lemma isRegular_markedSat (lett : Γ → A) (φ : MSO A) : (MarkedSat lett φ).IsRegular := by
  classical
  set k := φ.foBound with hk
  set l := φ.soBound with hl
  have hkpos : 0 < k := by rw [hk, MSO.foBound]; omega
  have hann := MSOAnnot.isRegular_annLang φ k l (MSO.freeFO_lt_foBound φ)
    (MSO.freeSO_lt_soBound φ)
  have hcom := isRegular_comap (annMark (A := A) lett k l) hann
  refine isRegular_of_eq hcom (fun z => ?_)
  have hfst : ((z.map (annMark (A := A) lett k l)).map Prod.fst) = (z.map Prod.fst).map lett := by
    simp [List.map_map, Function.comp_def, annMark]
  constructor
  · rintro ⟨hmark, hsat⟩
    refine ⟨(valid_annMark_iff lett k l hkpos z).2 hmark, ?_⟩
    rw [hfst]
    refine (MSO.sat_congr _ φ (fun _ => markPos z)
      (MSOAnnot.foOf (z.map (annMark (A := A) lett k l)))
      (fun _ => ∅) (MSOAnnot.soOf (z.map (annMark (A := A) lett k l)))
      (fun i hi => ?_) (fun j _ => ?_)).1 hsat
    · exact (foOf_annMark lett k l hmark (MSO.freeFO_lt_foBound φ hi)).symm
    · exact (soOf_annMark lett k l z j).symm
  · rintro ⟨hvalid, hsat⟩
    have hmark := (valid_annMark_iff lett k l hkpos z).1 hvalid
    refine ⟨hmark, ?_⟩
    rw [hfst] at hsat
    refine (MSO.sat_congr _ φ (MSOAnnot.foOf (z.map (annMark (A := A) lett k l)))
      (fun _ => markPos z) (MSOAnnot.soOf (z.map (annMark (A := A) lett k l)))
      (fun _ => ∅) (fun i hi => ?_) (fun j _ => ?_)).1 hsat
    · exact foOf_annMark lett k l hmark (MSO.freeFO_lt_foBound φ hi)
    · exact soOf_annMark lett k l z j

end Marked

/-! ## Claim `claim:mso-annotation-regular` -/

section Relabelling

variable {A B : Type}

open scoped Classical in
/-- The strings over `(A × Φ) × 2` with one marked position, carrying the index
`x`, at which the formula `φ_x` fails. -/
noncomputable def BadSrc (R : MSORelabelling A B) (x : R.Idx) : Language ((A × R.Idx) × Bool) :=
  {z | z ∈ MarkedSat (Prod.fst : A × R.Idx → A) (MSO.not (R.form x)) ∧
    ∃ y, z[z.findIdx (fun y : (A × R.Idx) × Bool => y.2)]? = some y ∧
      (decide (y.1.2 = x)) = true}

open scoped Classical in
lemma isRegular_badSrc (R : MSORelabelling A B) (x : R.Idx) : (BadSrc R x).IsRegular :=
  isRegular_and (isRegular_markedSat _ _)
    (isRegular_scan (fun y : (A × R.Idx) × Bool => y.2) (fun y => decide (y.1.2 = x)))

/-- The strings in which some position carrying the index `x` fails the formula
`φ_x`.  It is the projection of `BadSrc R x`. -/
def Bad (R : MSORelabelling A B) (x : R.Idx) : Language (A × R.Idx) :=
  {u | ∃ p y, u[p]? = some y ∧ y.2 = x ∧
    ¬ MSO.Sat (u.map Prod.fst) (fun _ => p) (fun _ => ∅) (R.form x)}

open scoped Classical in
lemma bad_eq_image (R : MSORelabelling A B) (x : R.Idx) :
    Bad R x = {u : List (A × R.Idx) | ∃ z, z ∈ BadSrc R x ∧ z.map Prod.fst = u} := by
  ext u
  constructor
  · rintro ⟨p, y, hy, hyx, hsat⟩
    obtain ⟨hp, -⟩ := List.getElem?_eq_some_iff.1 hy
    set g : (A × R.Idx) → Bool → ((A × R.Idx) × Bool) := fun y b => (y, b) with hg
    set z : List ((A × R.Idx) × Bool) := markWith g (fun q => decide (q = p)) u with hz
    have hzmap : z.map Prod.fst = u := by
      rw [hz, map_markWith g _ u Prod.fst id (fun x c => rfl), List.map_id]
    have hmarked : ∀ q, MarkedAt (fun y : (A × R.Idx) × Bool => y.2) z q ↔ q = p := by
      intro q
      rw [hz, markedAt_markWith_mark g _ u (fun y => y.2) (fun x c => rfl) q]
      constructor
      · rintro ⟨-, hq⟩; simpa using hq
      · rintro rfl; exact ⟨hp, by simp⟩
    have hmark : MarksOnce (fun y : (A × R.Idx) × Bool => y.2) z := ⟨p, hmarked⟩
    have hpos : markPos z = p := findIdx_eq_of_marksOnce hmarked
    refine ⟨z, ⟨⟨hmark, ?_⟩, ?_⟩, hzmap⟩
    · rw [hpos, hzmap]
      simpa [MSO.Sat] using hsat
    · refine ⟨(y, true), ?_, by simpa using hyx⟩
      have : z.findIdx (fun y : (A × R.Idx) × Bool => y.2) = p := hpos
      rw [this, hz, markWith_getElem? g _ u p, hy]
      simp [hg]
  · rintro ⟨z, ⟨⟨hmark, hsat⟩, y, hy, hyx⟩, rfl⟩
    obtain ⟨p, hp⟩ := hmark
    have hpos : markPos z = p := findIdx_eq_of_marksOnce hp
    have hplt : p < z.length := marksOnce_lt_length hp
    refine ⟨p, y.1, ?_, by simpa using hyx, ?_⟩
    · rw [List.getElem?_map]
      have hzp : z[p]? = some y := by
        rw [← hpos]
        exact hy
      rw [hzp]
      rfl
    · rw [hpos] at hsat
      simpa [MSO.Sat] using hsat

open scoped Classical in
lemma isRegular_bad (R : MSORelabelling A B) (x : R.Idx) : (Bad R x).IsRegular := by
  rw [bad_eq_image]
  exact isRegular_image Prod.fst (isRegular_badSrc R x)

open scoped Classical in
/-- **Claim `claim:mso-annotation-regular`.**  For an mso relabelling, the language of
strings over the alphabet `A × Φ` in which every position is labelled by a formula that holds in
that position is regular. -/
theorem msoRelabelling_annotation_regular_aux {A B : Type} [Finite A]
    (R : MSORelabelling A B) :
    Language.IsRegular
      {u : List (A × R.Idx) | ∀ (p : ℕ) (hp : p < u.length),
        MSO.Sat (u.map Prod.fst) (fun _ => p) (fun _ => ∅) (R.form (u.get ⟨p, hp⟩).2)} := by
  haveI := R.finIdx
  letI : Fintype R.Idx := Fintype.ofFinite R.Idx
  have hall := isRegular_forall_list (fun x : R.Idx => {u : List (A × R.Idx) | u ∉ Bad R x})
    (Finset.univ : Finset R.Idx).toList (fun x _ => isRegular_not (isRegular_bad R x))
  refine isRegular_of_eq hall (fun u => ?_)
  constructor
  · intro hu x _
    rintro ⟨p, y, hy, rfl, hsat⟩
    obtain ⟨hp, hyy⟩ := List.getElem?_eq_some_iff.1 hy
    exact hsat (by simpa [hyy] using hu p hp)
  · intro hu p hp
    by_contra hsat
    refine hu (u.get ⟨p, hp⟩).2 (Finset.mem_toList.2 (Finset.mem_univ _))
      ⟨p, u[p], List.getElem?_eq_getElem hp, rfl, hsat⟩

end Relabelling

end MSORelab

export MSORelab (msoRelabelling_annotation_regular_aux)

end Lax314295Proofs.Transducers
