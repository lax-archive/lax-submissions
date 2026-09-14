/-
The remaining two items of Lemma `lem:regular-closure-properties` of *Transducers* (M. Bojańczyk):
regular functions are closed under concatenation and under case distinction over
a regular language.

Both are obtained from Claim `claim:conditional` (`sum_of_regular_aux`), following the book.

* For the case distinction, a rational function turns `w` into `# w` recoloured
  by the first or the second copy of the alphabet `A + 1`, according to whether
  `w` belongs to the language.  The marker `#` makes the recoloured string
  nonempty, which is what Claim `claim:conditional` requires; it is deleted again by the two
  summands.  The sum of the two summands is then applied, and a rational
  function forgets the colour of the output.
* For the concatenation, a rational function turns `w` into `# w`, map duplicate
  produces `# w # w`, a sequential rewriting separates the two copies and
  recolours them, the map lifting of the sum applies `f` to the first block and
  `g` to the second one, and a homomorphism erases the separator and the
  colours.

Both proofs treat the case of an empty output alphabet separately, since
Claim `claim:conditional` needs the output alphabets to be nonempty; when `B` is empty both
functions are constant equal to the empty string.
-/
import Lax916827Proofs.Source.PartC.RegSum
import Lax916827Proofs.Source.PartC.RegMapLift
import Lax916827Proofs.Source.PartC.RatSeq
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegCl

variable {A B : Type}

/-- The homomorphism deleting the marker. -/
def del : List (Option A) → List A :=
  homOf (fun x => match x with | none => [] | some a => [a])

lemma del_marked (w : List A) : del (none :: w.map some) = w := by
  have key : ∀ w : List A,
      homOf (fun x : Option A => match x with | none => ([] : List A) | some a => [a])
        (w.map some) = w := by
    intro w
    induction w with
    | nil => rfl
    | cons a w ih => simpa [homOf] using ih
  simpa [del, homOf] using key w

lemma isRegularFun_del [Finite A] : IsRegularFun (del : List (Option A) → List A) :=
  IsRegularFun.of_rational (isRationalFun_homOf _)

/-- The recolouring by the first copy of `A + 1`, with the marker prepended. -/
def colL (w : List A) : List (Option A ⊕ Option A) := (none :: w.map some).map Sum.inl

/-- The recolouring by the second copy of `A + 1`, with the marker prepended. -/
def colR (w : List A) : List (Option A ⊕ Option A) := (none :: w.map some).map Sum.inr

lemma isRationalFun_colL [Finite A] : IsRationalFun (colL : List A → _) := by
  have h := isRationalFun_comp
    (isRationalFun_map (fun a : A => (Sum.inl (some a) : Option A ⊕ Option A)))
    (isRationalFun_cons (Sum.inl none : Option A ⊕ Option A))
  have he : (fun w : List A =>
      (Sum.inl none : Option A ⊕ Option A) :: w.map (fun a => Sum.inl (some a)))
      = (colL : List A → _) := by
    funext w; simp [colL, List.map_map, Function.comp_def]
  rw [← he]
  exact h

lemma isRationalFun_colR [Finite A] : IsRationalFun (colR : List A → _) := by
  have h := isRationalFun_comp
    (isRationalFun_map (fun a : A => (Sum.inr (some a) : Option A ⊕ Option A)))
    (isRationalFun_cons (Sum.inr none : Option A ⊕ Option A))
  have he : (fun w : List A =>
      (Sum.inr none : Option A ⊕ Option A) :: w.map (fun a => Sum.inr (some a)))
      = (colR : List A → _) := by
    funext w; simp [colR, List.map_map, Function.comp_def]
  rw [← he]
  exact h

/-- The output of the two summands is uncoloured by this map. -/
def unCol : (B ⊕ B) → B := Sum.elim id id

lemma map_unCol_inl (l : List B) : (l.map Sum.inl).map (unCol : B ⊕ B → B) = l := by
  simp [unCol, List.map_map, Function.comp_def]

lemma map_unCol_inr (l : List B) : (l.map Sum.inr).map (unCol : B ⊕ B → B) = l := by
  simp [unCol, List.map_map, Function.comp_def]

/-- If the output alphabet is empty, every output is the empty string. -/
lemma eq_nil_of_not_nonempty (hB : ¬ Nonempty B) (l : List B) : l = [] := by
  cases l with
  | nil => rfl
  | cons b _ => exact absurd ⟨b⟩ hB

/-! ## The concatenation -/

/-- The states of the automaton separating the two copies produced by map
duplicate. -/
inductive Cm | m0 | m1 | m2
  deriving DecidableEq, Fintype

/-- Its transition function. -/
def cmStep : Cm → Option (Option A) → Cm
  | Cm.m0, some none => Cm.m1
  | Cm.m1, some none => Cm.m2
  | Cm.m1, some (some _) => Cm.m1
  | _, _ => Cm.m2

/-- The output of the sequential rewriting separating the two copies. -/
def cmOut : Cm → Option (Option A) → List (Option (Option A ⊕ Option A))
  | Cm.m0, some none => [some (Sum.inl none)]
  | Cm.m1, some (some a) => [some (Sum.inl (some a))]
  | Cm.m1, some none => [none, some (Sum.inr none)]
  | Cm.m2, some (some a) => [some (Sum.inr (some a))]
  | _, _ => []

/-- The rational function separating the two copies. -/
def sep2 : List (Option (Option A)) → List (Option (Option A ⊕ Option A)) :=
  seqEval cmStep cmOut Cm.m0

lemma sep2_m1 (w : List A) (Rest : List (Option (Option A))) :
    seqEval cmStep cmOut Cm.m1 (w.map (fun a => some (some a)) ++ Rest)
      = w.map (fun a => some (Sum.inl (some a))) ++ seqEval cmStep cmOut Cm.m1 Rest := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [List.map_cons, List.cons_append, seqEval_cons,
        show cmOut Cm.m1 (some (some a)) = [some (Sum.inl (some a))] from rfl,
        show cmStep Cm.m1 (some (some a)) = Cm.m1 from rfl, ih]
      simp

lemma sep2_m2 (w : List A) :
    seqEval cmStep cmOut Cm.m2 (w.map (fun a => some (some a)))
      = w.map (fun a => some (Sum.inr (some a))) := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [List.map_cons, seqEval_cons,
        show cmOut Cm.m2 (some (some a)) = [some (Sum.inr (some a))] from rfl,
        show cmStep Cm.m2 (some (some a)) = Cm.m2 from rfl, ih]
      simp

lemma isRationalFun_sep2 [Finite A] :
    IsRationalFun (sep2 : List (Option (Option A)) → _) :=
  isRationalFun_seqEval _ _ _

lemma flatten_map_singleton (l : List B) : (l.map (fun b => [b])).flatten = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa using ih

/-- The homomorphism erasing the separator and the colours of the output. -/
def clean : List (Option (B ⊕ B)) → List B :=
  homOf (fun x => match x with
    | none => []
    | some (Sum.inl b) => [b]
    | some (Sum.inr b) => [b])

lemma clean_inl (l : List B) : clean ((l.map Sum.inl).map some) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [clean, homOf] using ih

lemma clean_inr_append (l : List B) (Rest : List (Option (B ⊕ B))) :
    clean ((l.map Sum.inr).map some ++ Rest) = l ++ clean Rest := by
  induction l with
  | nil => simp
  | cons b l ih => simpa [clean, homOf] using ih

lemma clean_append (X Y : List (Option (B ⊕ B))) :
    clean (X ++ Y) = clean X ++ clean Y := by simp [clean, homOf]

lemma isRegularFun_clean [Finite B] : IsRegularFun (clean : List (Option (B ⊕ B)) → List B) :=
  IsRegularFun.of_rational (isRationalFun_homOf _)

end RegCl

open RegCl in
/-- **Lemma `lem:regular-closure-properties` (concatenation).**  If `f` and `g` are regular, then so
is `w ↦ f w · g w`. -/
theorem isRegularFun_concat {A B : Type} [Finite A] [Finite B] {f g : List A → List B}
    (hf : IsRegularFun f) (hg : IsRegularFun g) : IsRegularFun (fun w => f w ++ g w) := by
  classical
  by_cases hB : Nonempty B
  · haveI := hB
    have hf' : IsRegularFun (fun u : List (Option A) => f (del u)) :=
      isRegularFun_del.comp' hf (fun _ => rfl)
    have hg' : IsRegularFun (fun u : List (Option A) => g (del u)) :=
      isRegularFun_del.comp' hg (fun _ => rfl)
    obtain ⟨bot, F, -, -, hFreg, hFL, hFR, -⟩ :=
      sum_of_regular_aux (B₁ := B) (B₂ := B) hf' hg'
    -- the first three rational steps
    have hs : IsRationalFun (fun w : List A =>
        (none :: w.map (some : A → Option A)).map (some : Option A → Option (Option A))) := by
      have h := isRationalFun_comp
        (isRationalFun_map (fun a : A => (some (some a) : Option (Option A))))
        (isRationalFun_cons (some none : Option (Option A)))
      have he : (fun w : List A =>
          (some none : Option (Option A)) :: w.map (fun a => some (some a)))
          = (fun w : List A =>
            (none :: w.map (some : A → Option A)).map (some : Option A → Option (Option A))) := by
        funext w; simp [List.map_map, Function.comp_def]
      rw [← he]; exact h
    have hstep : IsRegularFun (fun w : List A =>
        clean (mapLift F (sep2 (mapDuplicate (Option A)
          ((none :: w.map (some : A → Option A)).map some))))) :=
      ((((IsRegularFun.of_rational hs).comp
        (isRegularFun_mapDuplicate (Option A))).comp
          (IsRegularFun.of_rational isRationalFun_sep2)).comp
        (isRegularFun_mapLift hFreg)).comp' isRegularFun_clean (fun _ => rfl)
    refine hstep.congr (fun w => ?_)
    -- the computation
    set u : List (Option A) := none :: w.map some with hu
    have hune : u ≠ [] := by simp [hu]
    have hdup : mapDuplicate (Option A) (u.map some) = (u ++ u).map some :=
      mapLift_map_some _ u
    have hsep : sep2 ((u ++ u).map some)
        = (u.map Sum.inl).map some ++ none :: (u.map Sum.inr).map some := by
      rw [hu]
      show seqEval cmStep cmOut Cm.m0
          (((none :: w.map some) ++ (none :: w.map some)).map some) = _
      rw [show (((none :: w.map (some : A → Option A)) ++ (none :: w.map some)).map some)
        = (some none : Option (Option A)) :: (w.map (fun a => some (some a))
            ++ ((some none : Option (Option A)) :: w.map (fun a => some (some a))))
        by simp [List.map_map, Function.comp_def]]
      rw [seqEval_cons, show cmOut Cm.m0 (some none) = [some (Sum.inl (none : Option A))] from rfl,
        show cmStep (A := A) Cm.m0 (some none) = Cm.m1 from rfl, sep2_m1, seqEval_cons,
        show cmOut (A := A) Cm.m1 (some none)
          = [none, some (Sum.inr (none : Option A))] from rfl,
        show cmStep (A := A) Cm.m1 (some none) = Cm.m2 from rfl, sep2_m2]
      simp [List.map_map, Function.comp_def]
    have hFu1 : F (u.map Sum.inl) = (f w).map Sum.inl := by
      rw [hFL u hune, hu, del_marked]
    have hFu2 : F (u.map Sum.inr) = (g w).map Sum.inr := by
      rw [hFR u hune, hu, del_marked]
    rw [hdup, hsep, mapLift_map_some_cons_none, mapLift_map_some, hFu1, hFu2,
      clean_append, clean_inl]
    show f w ++ clean (none :: ((g w).map Sum.inr).map some) = f w ++ g w
    rw [show (none :: ((g w).map Sum.inr).map some)
      = ([] : List (Option (B ⊕ B))) ++ none :: ((g w).map Sum.inr).map some from rfl]
    simp only [clean, homOf, List.map_map, Function.comp_def, List.map_cons, List.flatten_cons,
      List.nil_append]
    rw [flatten_map_singleton]
  · have hnil := eq_nil_of_not_nonempty hB
    have he : (fun w : List A => f w ++ g w) = fun _ : List A => ([] : List B) := by
      funext w; rw [hnil (f w), hnil (g w)]; rfl
    rw [he]
    exact IsRegularFun.of_rational (isRationalFun_const [])

open scoped Classical in
open RegCl in
/-- **Lemma `lem:regular-closure-properties` (conditionals).**  If `f` and `g` are regular and `L`
is a regular language, then the function that applies `f` on `L` and `g` outside of `L` is regular.
-/
theorem isRegularFun_cond {A B : Type} [Finite A] [Finite B] {f g : List A → List B}
    (hf : IsRegularFun f) (hg : IsRegularFun g) {L : Language A} (hL : L.IsRegular) :
    IsRegularFun (fun w => if w ∈ L then f w else g w) := by
  classical
  by_cases hB : Nonempty B
  · haveI := hB
    have hf' : IsRegularFun (fun u : List (Option A) => f (del u)) :=
      isRegularFun_del.comp' hf (fun _ => rfl)
    have hg' : IsRegularFun (fun u : List (Option A) => g (del u)) :=
      isRegularFun_del.comp' hg (fun _ => rfl)
    obtain ⟨bot, F, -, -, hFreg, hFL, hFR, -⟩ :=
      sum_of_regular_aux (B₁ := B) (B₂ := B) hf' hg'
    have hr : IsRationalFun (fun w : List A => if w ∈ L then colL w else colR w) :=
      isRationalFun_ite_lang hL isRationalFun_colL isRationalFun_colR
    have hstep : IsRegularFun (fun w : List A =>
        (F (if w ∈ L then colL w else colR w)).map (unCol : B ⊕ B → B)) :=
      ((IsRegularFun.of_rational hr).comp hFreg).comp'
        (isRegularFun_map (unCol : B ⊕ B → B)) (fun _ => rfl)
    refine hstep.congr (fun w => ?_)
    set u : List (Option A) := none :: w.map some with hu
    have hune : u ≠ [] := by simp [hu]
    by_cases hw : w ∈ L
    · rw [if_pos hw, if_pos hw, show colL w = u.map Sum.inl from rfl, hFL u hune, hu,
        del_marked, map_unCol_inl]
    · rw [if_neg hw, if_neg hw, show colR w = u.map Sum.inr from rfl, hFR u hune, hu,
        del_marked, map_unCol_inr]
  · have hnil := eq_nil_of_not_nonempty hB
    have he : (fun w : List A => if w ∈ L then f w else g w) = fun _ : List A => ([] : List B) := by
      funext w
      by_cases hw : w ∈ L
      · rw [if_pos hw, hnil (f w)]
      · rw [if_neg hw, hnil (g w)]
    rw [he]
    exact IsRegularFun.of_rational (isRationalFun_const [])

end Lax916827Proofs.Transducers
