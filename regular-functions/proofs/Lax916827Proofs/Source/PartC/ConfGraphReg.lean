/-
The two lemmas of Section *Continuity* of *Transducers* (M. Bojańczyk) about the string encoding of
the reachable configuration graph of a two-way transducer, and the "main observation" they rest on.

* `TwoWay.encLang_isRegular` -- the main observation: the strings over the alphabet `C` that
  represent a reachable configuration graph form a regular language.  The book checks local
  consistency of the letters with the transition function and reachability of the arrows; here both
  are packed into the local consistency of the annotation of `TwoWayAnnot.lean`, whose letters
  already know which configurations are reachable, and which is a regular condition
  (`TwoWay.validLang_isRegular`).
* Lemma `lem:compute-configuration-graph` (`TwoWay.isRationalFun_enc`) -- the function taking an
  input string to the string representation of its reachable configuration graph is rational.  It is
  the annotation, which is a bimachine and hence rational, followed by a letter-to-letter map, with
  the book's special letter for the empty input.
* Lemma `lem:check-if-output-string-of-configuration-graph-belongs-to-L`
  (`TwoWay.encOutputLang_isRegular`) -- for a regular language `L`, the strings over `C` that
  represent a reachable configuration graph whose output string belongs to `L` form a regular
  language.
-/
import Lax916827Proofs.Source.PartC.ConfGraphAnnot
import Lax916827Proofs.Source.PartC.ConfGraphRun
import Lax916827Proofs.Source.PartC.TwoWayAnnotBim
import Lax916827Proofs.Source.PartC.RatTools
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open scoped Classical

variable {A B Q : Type}

/-! ## Two small regular languages -/

/-- The language of the strings of length one over a fixed letter. -/
lemma isRegular_singleton {Γ : Type} (x : Γ) : Language.IsRegular {u : List Γ | u = [x]} := by
  classical
  set step : Option Bool → Γ → Option Bool := fun s c =>
    match s with
    | some false => if c = x then some true else none
    | _ => none with hstep
  have habs : ∀ u : List Γ, u.foldl step none = none := by
    intro u
    induction u with
    | nil => rfl
    | cons c rest ih => simpa [hstep] using ih
  have habs' : ∀ u : List Γ, u.foldl step (some true) = if u = [] then some true else none := by
    intro u
    cases u with
    | nil => rfl
    | cons c rest => simpa [hstep] using habs rest
  have h := RegAut.isRegular_foldl step (some false) ({some true} : Set (Option Bool))
  refine RegAut.isRegular_of_eq h (fun u => ?_)
  show u = [x] ↔ List.foldl step (some false) u ∈ ({some true} : Set (Option Bool))
  rw [Set.mem_singleton_iff]
  cases u with
  | nil => simp [hstep]
  | cons c rest =>
      rw [List.foldl_cons]
      by_cases hc : c = x
      · subst hc
        rw [show step (some false) c = some true by simp [hstep], habs']
        cases rest with
        | nil => simp
        | cons d rest' => simp
      · rw [show step (some false) c = none by simp [hstep, hc], habs]
        simp [hc]

/-- The language of non-empty strings. -/
lemma isRegular_ne_nil {Γ : Type} : Language.IsRegular {u : List Γ | u ≠ []} := by
  have h := RegAut.isRegular_foldl (Γ := Γ) (fun _ _ => true) false ({true} : Set Bool)
  refine RegAut.isRegular_of_eq h (fun u => ?_)
  show u ≠ [] ↔ List.foldl (fun _ _ => true) false u ∈ ({true} : Set Bool)
  rw [Set.mem_singleton_iff]
  cases u with
  | nil => simp
  | cons c rest =>
      have : ∀ (v : List Γ), v.foldl (fun _ _ => true) true = true := by
        intro v; induction v with
        | nil => rfl
        | cons d v ih => simpa using ih
      simp [this]

/-- The empty language. -/
lemma isRegular_empty {Γ : Type} : Language.IsRegular {_u : List Γ | False} := by
  have h := RegAut.isRegular_foldl (Γ := Γ) (fun _ _ => ()) () (∅ : Set Unit)
  refine RegAut.isRegular_of_eq h (fun _u => ?_)
  simp

/-! ## The main observation -/

variable (M : TwoWay A B Q) [Finite A] [Finite Q]
/-- **The main observation** of the proof of Lemma `lem:compute-configuration-graph`, in the form
that is used for the two lemmas: for a regular language `K` of inputs, the strings over the alphabet
`C` that represent the reachable configuration graph of an input in `K` form a regular language. -/
theorem encImage_isRegular {K : Language A} (hK : K.IsRegular) :
    Language.IsRegular {u : List (CLet Q (Lab M)) | ∃ w ∈ K, u = enc M w} := by
  classical
  obtain ⟨σ, hσ, D, hD⟩ := visitLang_isRegular M
  haveI : Finite σ := hσ.finite
  set h : AnnLet A σ → CLet Q (Lab M) := fun c => Sum.inl (sliceOfAnn D M c) with hh
  -- the valid annotations of a non-empty input in `K`
  have hZ : Language.IsRegular {z : List (AnnLet A σ) |
      Valid D z ∧ z ≠ [] ∧ z.map AnnLet.letter ∈ K} :=
    RegAut.isRegular_and (validLang_isRegular D)
      (RegAut.isRegular_and isRegular_ne_nil (RegAut.isRegular_comap AnnLet.letter hK))
  have himg := RegAut.isRegular_image h hZ
  -- the special letter for the empty input
  have hE : Language.IsRegular
      {u : List (CLet Q (Lab M)) | u = [Sum.inr (emptyOut M)] ∧ [] ∈ K} := by
    by_cases hnil : ([] : List A) ∈ K
    · refine RegAut.isRegular_of_eq (isRegular_singleton (Sum.inr (emptyOut M))) (fun u => ?_)
      simp [hnil]
    · refine RegAut.isRegular_of_eq (isRegular_empty (Γ := CLet Q (Lab M))) (fun u => ?_)
      simp [hnil]
  refine RegAut.isRegular_of_eq (RegAut.isRegular_or hE himg) (fun u => ?_)
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hwnil : w with _ | ⟨a, w'⟩
    · subst hwnil
      exact Or.inl ⟨rfl, hw⟩
    · subst hwnil
      refine Or.inr ⟨annot D (a :: w'), ⟨valid_annot D _, ?_, ?_⟩, ?_⟩
      · intro hcon
        have := annot_length D (a :: w')
        rw [hcon] at this
        simp at this
      · rw [annot_map_letter]; exact hw
      · rw [← enc_eq_map_annot D M hD (by simp)]
  · rintro (⟨rfl, hnil⟩ | ⟨z, ⟨hvalid, hzne, hzK⟩, rfl⟩)
    · exact ⟨[], hnil, rfl⟩
    · refine ⟨z.map AnnLet.letter, hzK, ?_⟩
      have hz : z = annot D (z.map AnnLet.letter) := annot_of_valid D hvalid
      have hwne : z.map AnnLet.letter ≠ [] := by
        intro hcon
        exact hzne (by simpa using congrArg List.length hcon)
      rw [enc_eq_map_annot D M hD hwne, ← hz]

/-- **The main observation** of the proof of Lemma `lem:compute-configuration-graph`: the strings
over the alphabet `C` that represent a reachable configuration graph of the two-way transducer `M`
form a regular language. -/
theorem encLang_isRegular :
    Language.IsRegular {u : List (CLet Q (Lab M)) | ∃ w, u = enc M w} := by
  refine RegAut.isRegular_of_eq (encImage_isRegular M (RegAut.isRegular_univ (Γ := A)))
    (fun u => ?_)
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, Set.mem_univ w, hw⟩
  · rintro ⟨w, -, hw⟩
    exact ⟨w, hw⟩

/-! ## Lemma `lem:compute-configuration-graph` -/

/-- **Lemma `lem:compute-configuration-graph`.**  The function which maps an input string to the
string representation of its reachable configuration graph is rational. -/
theorem isRationalFun_enc : IsRationalFun (enc M) := by
  classical
  obtain ⟨σ, hσ, D, hD⟩ := visitLang_isRegular M
  haveI : Finite σ := hσ.finite
  -- on non-empty inputs, the encoding is the annotation followed by a letter-to-letter map
  have hg : IsRationalFun (fun w : List A =>
      (annot D w).map (fun c => Sum.inl (sliceOfAnn D M c) : AnnLet A σ → CLet Q (Lab M))) :=
    isRationalFun_comp (isRationalFun_annot D)
      (isRationalFun_map (fun c : AnnLet A σ => (Sum.inl (sliceOfAnn D M c) : CLet Q (Lab M))))
  have hc : IsRationalFun (fun _ : List A => ([Sum.inr (emptyOut M)] : List (CLet Q (Lab M)))) :=
    isRationalFun_const _
  have hite := isRationalFun_ite (A := A) (B := CLet Q (Lab M)) (σ := Bool)
    (fun _ _ => true) false (fun s => s = true) hg hc
  refine IsRationalRel.congr hite (fun w v => ?_)
  have htrue : ∀ u : List A, u.foldl (fun (_ : Bool) (_ : A) => true) true = true := by
    intro u
    induction u with
    | nil => rfl
    | cons b u ih => simpa using ih
  have heq : (if (strTrans (fun (_ : Bool) (_ : A) => true) w false) = true then
      (annot D w).map (fun c => Sum.inl (sliceOfAnn D M c) : AnnLet A σ → CLet Q (Lab M))
      else [Sum.inr (emptyOut M)]) = enc M w := by
    cases w with
    | nil =>
        rw [if_neg (by simp [strTrans])]
        rw [enc_nil]
    | cons a w' =>
        have hcond : strTrans (fun (_ : Bool) (_ : A) => true) (a :: w') false = true := by
          show (a :: w').foldl (fun (_ : Bool) (_ : A) => true) false = true
          rw [List.foldl_cons]
          exact htrue w'
        rw [if_pos hcond]
        exact (enc_eq_map_annot D M hD (by simp)).symm
  show v = (if (strTrans (fun (_ : Bool) (_ : A) => true) w false) = true then
      (annot D w).map (fun c => Sum.inl (sliceOfAnn D M c) : AnnLet A σ → CLet Q (Lab M))
      else [Sum.inr (emptyOut M)]) ↔ v = enc M w
  rw [heq]

/-! ## Lemma `lem:check-if-output-string-of-configuration-graph-belongs-to-L` -/

/-- **Lemma `lem:check-if-output-string-of-configuration-graph-belongs-to-L`.**  For a regular
language `L`, the strings over the alphabet `C` which represent a reachable configuration graph of
`M` whose output string belongs to `L` form a regular language.  The output string of an encoded
configuration graph is the string printed by the transducer `pathTrans M` which walks along the
graph; by `TwoWay.computes_enc` it is the output of `M` itself.  As in the book, the transducer `M`
is assumed to compute a (total) function `f`. -/
theorem encOutputLang_isRegular {f : List A → List B} (hM : ∀ w, M.Computes w (f w))
    {L : Language B} (hL : L.IsRegular) :
    Language.IsRegular {u : List (CLet Q (Lab M)) |
      (∃ w, u = enc M w) ∧ ∃ v, (pathTrans M).Computes u v ∧ v ∈ L} := by
  classical
  have hK : Language.IsRegular {w : List A | f w ∈ L} :=
    twoWay_continuous_aux ⟨Q, inferInstance, M, hM⟩ L hL
  refine RegAut.isRegular_of_eq (encImage_isRegular M hK) (fun u => ?_)
  constructor
  · rintro ⟨⟨w, rfl⟩, v, hv, hvL⟩
    have hcomp : (pathTrans M).Computes (enc M w) (f w) := computes_enc M (hM w)
    have hvf : v = f w := computes_unique hv hcomp
    refine ⟨w, ?_, rfl⟩
    show f w ∈ L
    rw [← hvf]
    exact hvL
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, rfl⟩, f w, computes_enc M (hM w), hw⟩

end TwoWay

end Lax916827Proofs.Transducers
