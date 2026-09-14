/-
The combinators of Definition `def:regular-terms` preserve regularity under string representation.
Part of the easy direction of Theorem `thm:regular-terms` of *Transducers* (M. Bojańczyk).

Composition is `Transducers.IsRegularUnderRepr.comp`, in `CombTypes.lean`.  This file has the other
three.

* *Pairing* only has to write the representations of the two components between the brackets and
  the comma of a pair, so it is the pointwise concatenation of five regular functions.

* *Co-pairing* has to look at the first letter of the input, which says whether the input comes
  from the left or from the right summand, and then to run the corresponding function on the rest
  of the input.  Both the test and the removal of the first letter are rational.

* *Map* is the map lifting of Part A, applied to the marking of `CombMark.lean`.  One point needs
  care: the map lifting of `f` applies `f` to *every* block of its input, and the marking of the
  empty list is the empty string, which the map lifting reads as one empty block; so `f` is first
  replaced by the function that agrees with it everywhere except on the empty string, where it
  returns the empty string.  This is a conditional over a regular language, hence regular, and it
  changes nothing on the representations, which are never empty.
-/
import Lax709149Proofs.Source.PartC.CombMark
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-! ## Two regular languages and one rational function -/

/-- The language of the empty string. -/
def emptyLang (A : Type) : Language A := {w | w = []}

/-- The automaton of `emptyLang`: it leaves its initial state at the first letter. -/
def emptyDFA (A : Type) : DFA A Bool where
  step := fun _ _ => false
  start := true
  accept := {true}

lemma emptyDFA_evalFrom_cons (A : Type) (c : A) (w : List A) :
    (emptyDFA A).evalFrom (emptyDFA A).start (c :: w) = false := by
  have hf : ∀ (w : List A), List.foldl (fun (_ : Bool) (_ : A) => false) false w = false := by
    intro w
    induction w with
    | nil => rfl
    | cons c w ih => exact ih
  show List.foldl _ _ (c :: w) = false
  rw [List.foldl_cons]
  exact hf w

lemma emptyDFA_accepts (A : Type) : (emptyDFA A).accepts = emptyLang A := by
  ext w
  cases w with
  | nil =>
      constructor
      · intro _; rfl
      · intro _
        show (emptyDFA A).evalFrom (emptyDFA A).start [] ∈ (emptyDFA A).accept
        rfl
  | cons c w =>
      constructor
      · intro hw
        have h1 : (emptyDFA A).evalFrom (emptyDFA A).start (c :: w) ∈ (emptyDFA A).accept := hw
        rw [emptyDFA_evalFrom_cons] at h1
        exact absurd h1 (by simp [emptyDFA])
      · intro hw
        exact absurd (show c :: w = [] from hw) (by simp)

lemma emptyLang_isRegular (A : Type) [Finite A] : (emptyLang A).IsRegular :=
  ⟨Bool, inferInstance, emptyDFA A, emptyDFA_accepts A⟩

/-- The language of the strings whose first letter is `c`. -/
def headLang (c : Sym8) : Language Sym8 := {w | w.head? = some c}

/-- The automaton of `headLang c`: it decides at the first letter. -/
def headDFA (c : Sym8) : DFA Sym8 (Option Bool) where
  step := fun s c' => match s with
    | none => some (decide (c' = c))
    | some b => some b
  start := none
  accept := {some true}

lemma headDFA_evalFrom_cons (c c' : Sym8) (w : List Sym8) :
    (headDFA c).evalFrom (headDFA c).start (c' :: w) = some (decide (c' = c)) := by
  have hf : ∀ (w : List Sym8) (b : Bool),
      List.foldl (headDFA c).step (some b) w = some b := by
    intro w
    induction w with
    | nil => intro b; rfl
    | cons c'' w ih => intro b; exact ih b
  show List.foldl _ _ (c' :: w) = _
  rw [List.foldl_cons]
  exact hf w _

lemma headDFA_accepts (c : Sym8) : (headDFA c).accepts = headLang c := by
  ext w
  cases w with
  | nil =>
      constructor
      · intro hw
        have h1 : (headDFA c).evalFrom (headDFA c).start [] ∈ (headDFA c).accept := hw
        exact absurd h1 (by simp [headDFA])
      · intro hw
        exact absurd (show ([] : List Sym8).head? = some c from hw) (by simp)
  | cons c' w =>
      constructor
      · intro hw
        have h1 : (headDFA c).evalFrom (headDFA c).start (c' :: w) ∈ (headDFA c).accept := hw
        rw [headDFA_evalFrom_cons] at h1
        have h2 : decide (c' = c) = true := Option.some.inj (by simpa [headDFA] using h1)
        show (c' :: w).head? = some c
        rw [List.head?_cons, of_decide_eq_true h2]
      · intro hw
        have h2 : c' = c := by
          have h3 : (c' :: w).head? = some c := hw
          simpa using h3
        show (headDFA c).evalFrom (headDFA c).start (c' :: w) ∈ (headDFA c).accept
        rw [headDFA_evalFrom_cons, h2]
        simp [headDFA]

lemma headLang_isRegular (c : Sym8) : (headLang c).IsRegular :=
  ⟨Option Bool, inferInstance, headDFA c, headDFA_accepts c⟩

/-- Removing the first letter of a string. -/
lemma isRationalFun_tail {A : Type} [Finite A] : IsRationalFun (fun w : List A => w.tail) := by
  have hid : ∀ w : List A,
      seqEval (fun (_ : Bool) (_ : A) => false)
        (fun m c => if m then [] else [c]) false w = w := by
    intro w
    induction w with
    | nil => rfl
    | cons c w ih => rw [seqEval_cons]; simpa using ih
  have h := isRationalFun_seqEval (fun (_ : Bool) (_ : A) => false) true
    (fun m c => if m then ([] : List A) else [c])
  refine IsRationalRel.congr h (fun w v => ?_)
  cases w with
  | nil => rfl
  | cons c w => rw [seqEval_cons]; simp [hid w]

lemma isRegularFun_tail {A : Type} [Finite A] : IsRegularFun (fun w : List A => w.tail) :=
  IsRegularFun.of_rational isRationalFun_tail

/-! ## Pairing -/

/-- **Pairing preserves regularity under string representation.** -/
theorem IsRegularUnderRepr.pair {A B C : Ty} {f : A.Elt → B.Elt} {g : A.Elt → C.Elt}
    (hf : IsRegularUnderRepr f) (hg : IsRegularUnderRepr g) :
    IsRegularUnderRepr (A := A) (B := Ty.prod B C) (fun a => (f a, g a)) := by
  obtain ⟨f', hf', hfe⟩ := hf
  obtain ⟨g', hg', hge⟩ := hg
  refine ⟨fun w => Sym8.lpar :: (f' w ++ Sym8.comma :: (g' w ++ [Sym8.rpar])), ?_, fun a => ?_⟩
  · have h : IsRegularFun (fun w : List Sym8 =>
        [Sym8.lpar] ++ (f' w ++ ([Sym8.comma] ++ (g' w ++ [Sym8.rpar])))) :=
      isRegularFun_concat (IsRegularFun.of_rational (isRationalFun_const _))
        (isRegularFun_concat hf'
          (isRegularFun_concat (IsRegularFun.of_rational (isRationalFun_const _))
            (isRegularFun_concat hg'
              (IsRegularFun.of_rational (isRationalFun_const _)))))
    exact h.congr (fun w => rfl)
  · dsimp only
    rw [hfe a, hge a, Ty.repr_prod]

/-! ## Co-pairing -/

open scoped Classical in
/-- **Co-pairing preserves regularity under string representation.** -/
theorem IsRegularUnderRepr.copair {A B C : Ty} {f : A.Elt → C.Elt} {g : B.Elt → C.Elt}
    (hf : IsRegularUnderRepr f) (hg : IsRegularUnderRepr g) :
    IsRegularUnderRepr (A := Ty.sum A B) (B := C) (Sum.elim f g) := by
  obtain ⟨f', hf', hfe⟩ := hf
  obtain ⟨g', hg', hge⟩ := hg
  refine ⟨fun w => if w ∈ headLang Sym8.left then f' w.tail else g' w.tail, ?_, fun x => ?_⟩
  · exact isRegularFun_cond (isRegularFun_tail.comp' hf' (fun _ => rfl))
      (isRegularFun_tail.comp' hg' (fun _ => rfl)) (headLang_isRegular _)
  · cases x with
    | inl a =>
        dsimp only
        have hmem : (Ty.sum A B).repr (Sum.inl a) ∈ headLang Sym8.left := by
          show ((Ty.sum A B).repr (Sum.inl a)).head? = some Sym8.left
          rw [Ty.repr_inl]
          rfl
        rw [if_pos hmem, Ty.repr_inl]
        exact hfe a
    | inr b =>
        dsimp only
        have hmem : (Ty.sum A B).repr (Sum.inr b) ∉ headLang Sym8.left := by
          show ¬ (((Ty.sum A B).repr (Sum.inr b)).head? = some Sym8.left)
          rw [Ty.repr_inr]
          simp
        rw [if_neg hmem, Ty.repr_inr]
        exact hge b

/-! ## Map -/

open scoped Classical in
/-- **Map preserves regularity under string representation.** -/
theorem IsRegularUnderRepr.mapList {A B : Ty} {f : A.Elt → B.Elt} (hf : IsRegularUnderRepr f) :
    IsRegularUnderRepr (A := Ty.list A) (B := Ty.list B) (fun l => l.map f) := by
  obtain ⟨f', hf', hfe⟩ := hf
  set f'' : List Sym8 → List Sym8 :=
    fun w => if w ∈ emptyLang Sym8 then [] else f' w with hf''def
  have hf''reg : IsRegularFun f'' :=
    isRegularFun_cond (IsRegularFun.of_rational (isRationalFun_const [])) hf'
      (emptyLang_isRegular Sym8)
  have hf''nil : f'' [] = [] := by
    rw [hf''def]
    exact if_pos rfl
  have hf''repr : ∀ a : A.Elt, f'' (A.repr a) = B.repr (f a) := by
    intro a
    obtain ⟨c, w, hcw, -⟩ := repr_eq_cons A a
    have hne : A.repr a ∉ emptyLang Sym8 := by
      show ¬ (A.repr a = [])
      rw [hcw]
      simp
    rw [hf''def]
    dsimp only
    rw [if_neg hne]
    exact hfe a
  refine ⟨fun w => unmark (mapLift f'' (listMarkMach.run (listMarkN A) .start w)), ?_, fun l => ?_⟩
  · exact ((isRegularFun_listMarkRun A).comp' (isRegularFun_mapLift hf''reg)
      (fun _ => rfl)).comp' isRegularFun_unmark (fun _ => rfl)
  · dsimp only
    rw [listMarkMach_run, mapLift_optBlocks hf''nil, List.map_map]
    rw [show ((f'' ∘ A.repr) : A.Elt → List Sym8) = (B.repr ∘ f) from funext hf''repr,
      ← List.map_map]
    exact unmark_optBlocks B (l.map f)

end Comb
end Lax709149Proofs.Transducers
