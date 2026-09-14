/- Marked strings, used in the proofs of Theorem `thm:logic-rational-functions` and Lemma
`lem:logic-precomputation` of *Transducers* (M. Bojańczyk).

Both results relate mso formulas with one or two free first-order variables to
automata.  The bridge between the two is the *doubly marked* alphabet
`A × 2 × 2`: a string `w` together with two distinguished positions `x, y` is
encoded by the string `markAt2 w x y`, in which the first Boolean marks the
position `x` and the second one the position `y`.  A formula `φ` with free
variables among `x₀` (interpreted as `x`) and the remaining ones (interpreted as
`y`) then corresponds to the language `markedSat2 φ` of doubly marked strings,
which is regular by Lemma `lem:mso-free-variables`.

The file also contains the decomposition of a doubly marked string into the
part before `x`, the infix `[x..y]` and the part after `y`, which is what turns
the evaluation of an automaton on `markAt2 w x y` into the composition of three
state transformations, as in the proof of Lemma `lem:logic-precomputation` in the book.
-/
import Lax916827Proofs.Source.PartC.MSOAnnot
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers
namespace MarkStr

open RegAut MSOAnnot

variable {A C : Type}

/-! ## Generic annotation by the position -/

/-- The alphabet of strings with two marks. -/
abbrev Mark2 (A : Type) : Type := A × Bool × Bool

/-- Annotation of a string by a function of the letter and of the position, the
positions being counted from `m`. -/
def markGen (g : A → ℕ → C) (w : List A) (m : ℕ) : List C :=
  (w.zipIdx m).map (fun z => g z.1 z.2)

@[simp] lemma markGen_length (g : A → ℕ → C) (w : List A) (m : ℕ) :
    (markGen g w m).length = w.length := by
  simp [markGen]

lemma markGen_getElem? (g : A → ℕ → C) (w : List A) (m j : ℕ) :
    (markGen g w m)[j]? = (w[j]?).map (fun a => g a (m + j)) := by
  simp [markGen, List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Function.comp_def]

lemma markGen_append (g : A → ℕ → C) (u v : List A) (m : ℕ) :
    markGen g (u ++ v) m = markGen g u m ++ markGen g v (m + u.length) := by
  simp [markGen, List.zipIdx_append]

lemma markGen_congr {g g' : A → ℕ → C} {u : List A} {m m' : ℕ}
    (h : ∀ (j : ℕ) (hj : j < u.length), g u[j] (m + j) = g' u[j] (m' + j)) :
    markGen g u m = markGen g' u m' := by
  apply List.ext_getElem?
  intro j
  rw [markGen_getElem?, markGen_getElem?]
  rcases hj : u[j]? with - | a
  · simp
  · obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hj
    simp [h j hlt]

/-! ## Unmarked and marked strings -/

/-- A string with no marks. -/
def unmark2 (w : List A) : List (Mark2 A) := w.map (fun a => (a, false, false))

@[simp] lemma unmark2_length (w : List A) : (unmark2 w).length = w.length := by
  simp [unmark2]

@[simp] lemma unmark2_nil : unmark2 ([] : List A) = [] := rfl

@[simp] lemma unmark2_cons (a : A) (w : List A) :
    unmark2 (a :: w) = (a, false, false) :: unmark2 w := rfl

lemma unmark2_append (u v : List A) : unmark2 (u ++ v) = unmark2 u ++ unmark2 v := by
  simp [unmark2]

lemma unmark2_eq_markGen (u : List A) (m : ℕ) :
    unmark2 u = markGen (fun a _ => (a, false, false)) u m := by
  apply List.ext_getElem?
  intro j
  rw [markGen_getElem?]
  simp [unmark2, List.getElem?_map]

/-- The string `w` with the position `x` marked by the first Boolean and the
position `y` marked by the second one. -/
def markAt2 (w : List A) (x y : ℕ) : List (Mark2 A) :=
  markGen (fun a i => (a, decide (i = x), decide (i = y))) w 0

/-- The infix `[x..y]`, with its first position marked by the first Boolean and
its last position marked by the second one. -/
def midMark (u : List A) : List (Mark2 A) :=
  markGen (fun a i => (a, decide (i = 0), decide (i + 1 = u.length))) u 0

@[simp] lemma markAt2_length (w : List A) (x y : ℕ) : (markAt2 w x y).length = w.length := by
  simp [markAt2]

lemma markAt2_getElem? (w : List A) (x y j : ℕ) :
    (markAt2 w x y)[j]? = (w[j]?).map (fun a => (a, decide (j = x), decide (j = y))) := by
  rw [markAt2, markGen_getElem?]
  simp

lemma map_fst_markAt2 (w : List A) (x y : ℕ) : (markAt2 w x y).map Prod.fst = w := by
  apply List.ext_getElem?
  intro j
  simp [List.getElem?_map, markAt2_getElem?, Option.map_map, Function.comp_def]

@[simp] lemma midMark_length (u : List A) : (midMark u).length = u.length := by
  simp [midMark]

lemma midMark_singleton (a : A) : midMark [a] = [(a, true, true)] := by
  simp [midMark, markGen]

/-- The decomposition of a doubly marked string into the part before the first
mark, the infix between the two marks, and the part after the second mark. -/
lemma markAt2_split (w : List A) (x y : ℕ) (hxy : x ≤ y) (hy : y < w.length) :
    markAt2 w x y =
      unmark2 (w.take x) ++ midMark ((w.drop x).take (y - x + 1)) ++ unmark2 (w.drop (y + 1)) := by
  have hx : x < w.length := lt_of_le_of_lt hxy hy
  have hulen : (w.take x).length = x := by rw [List.length_take]; omega
  have hvlen : ((w.drop x).take (y - x + 1)).length = y - x + 1 := by
    rw [List.length_take, List.length_drop]; omega
  have htdrop : (w.drop x).drop (y - x + 1) = w.drop (y + 1) := by
    rw [List.drop_drop]; congr 1; omega
  have hwsplit : w = w.take x ++ ((w.drop x).take (y - x + 1) ++ (w.drop x).drop (y - x + 1)) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hdef : markAt2 w x y =
      markGen (fun a i => (a, decide (i = x), decide (i = y))) w 0 := rfl
  have p1 : markGen (fun a i => (a, decide (i = x), decide (i = y))) (w.take x) 0
      = unmark2 (w.take x) := by
    rw [unmark2_eq_markGen _ 0]
    refine markGen_congr (fun j hj => ?_)
    rw [hulen] at hj
    simp; omega
  have p2 : markGen (fun a i => (a, decide (i = x), decide (i = y)))
      ((w.drop x).take (y - x + 1)) (0 + (w.take x).length)
      = midMark ((w.drop x).take (y - x + 1)) := by
    rw [midMark]
    refine markGen_congr (fun j hj => ?_)
    rw [hvlen] at hj
    rw [hulen, hvlen]
    have h1 : decide (0 + x + j = x) = decide (0 + j = 0) := by
      apply decide_eq_decide.2; omega
    have h2 : decide (0 + x + j = y) = decide (0 + j + 1 = y - x + 1) := by
      apply decide_eq_decide.2; omega
    rw [h1, h2]
  have p3 : markGen (fun a i => (a, decide (i = x), decide (i = y)))
      ((w.drop x).drop (y - x + 1))
      (0 + (w.take x).length + ((w.drop x).take (y - x + 1)).length)
      = unmark2 ((w.drop x).drop (y - x + 1)) := by
    rw [unmark2_eq_markGen _ (0 + (w.take x).length + ((w.drop x).take (y - x + 1)).length)]
    refine markGen_congr (fun j hj => ?_)
    rw [hulen, hvlen]
    simp; omega
  rw [← htdrop, hdef]
  conv_lhs => rw [hwsplit]
  rw [markGen_append, markGen_append, p1, p2, p3, List.append_assoc]

lemma markAt2_diag (w : List A) (x : ℕ) (hx : x < w.length) :
    markAt2 w x x = unmark2 (w.take x) ++ (w[x], true, true) :: unmark2 (w.drop (x + 1)) := by
  have h := markAt2_split w x x (le_refl x) hx
  rw [h]
  have hmid : (w.drop x).take (x - x + 1) = [w[x]] := by
    have h1 : x - x + 1 = 1 := by omega
    rw [h1, List.take_one, List.head?_drop]
    simp [List.getElem?_eq_getElem hx]
  rw [hmid, midMark_singleton]
  simp

/-! ## The language of a formula, as a language of doubly marked strings -/

/-- The letter-to-letter map from the doubly marked alphabet to the annotated
alphabet: the first-order variable `x₀` is placed at the first mark and all the
other first-order variables at the second mark. -/
def annMark2 (A : Type) (k l : ℕ) : Mark2 A → Ann A k l :=
  fun z => (z.1, fun i => if (i : ℕ) = 0 then z.2.1 else z.2.2, fun _ => false)

lemma map_annMark2_markAt2 (k l : ℕ) (w : List A) (x y : ℕ) :
    (markAt2 w x y).map (annMark2 A k l) =
      annotate k l w (fun i => if (i : ℕ) = 0 then x else y) (fun _ => ∅) := by
  classical
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, markAt2_getElem?, annotate_getElem?, Option.map_map]
  rcases hj : w[j]? with - | a
  · simp
  · simp only [Option.map_some, Function.comp_apply, annMark2]
    refine congrArg some ?_
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      by_cases hi : (i : ℕ) = 0 <;> simp [hi, eq_comm]
    · funext i
      simp

/-- The language of doubly marked strings that satisfy `φ`, the variable `x₀`
being interpreted as the first mark and all the other first-order variables as
the second mark. -/
def markedSat2 (φ : MSO A) : Language (Mark2 A) :=
  {z | z.map (annMark2 A φ.foBound φ.soBound) ∈ AnnLang A φ.foBound φ.soBound φ}

lemma isRegular_markedSat2 [Finite A] (φ : MSO A) : (markedSat2 φ).IsRegular :=
  isRegular_comap (annMark2 A φ.foBound φ.soBound)
    (isRegular_annLang φ φ.foBound φ.soBound (MSO.freeFO_lt_foBound φ) (MSO.freeSO_lt_soBound φ))

lemma markAt2_mem_markedSat2 (φ : MSO A) (w : List A) (x y : ℕ)
    (hx : x < w.length) (hy : y < w.length) :
    markAt2 w x y ∈ markedSat2 φ ↔
      MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅) φ := by
  classical
  set k := φ.foBound
  set l := φ.soBound
  set fo : Fin k → ℕ := fun i => if (i : ℕ) = 0 then x else y with hfo
  have hfolt : ∀ i, fo i < w.length := by
    intro i
    rw [hfo]
    by_cases hi : (i : ℕ) = 0 <;> simp [hi, hx, hy]
  have hso : ∀ j : Fin l, (∅ : Set ℕ) ⊆ {p | p < w.length} := fun _ => Set.empty_subset _
  change List.map (annMark2 A _ _) (markAt2 w x y) ∈ AnnLang A _ _ φ ↔ _
  rw [map_annMark2_markAt2]
  change (Valid _ ∧ MSO.Sat (List.map Prod.fst _) (foOf _) (soOf _) φ) ↔ _
  rw [map_fst_annotate, foOf_annotate hfolt,
    soOf_annotate (fun j => hso j)]
  constructor
  · rintro ⟨-, hsat⟩
    refine (MSO.sat_congr w φ (extFO k fo) (fun i => if i = 0 then x else y)
      (extSO l (fun _ => ∅)) (fun _ => ∅) (fun i hi => ?_) (fun j _ => ?_)).1 hsat
    · have hik : i < k := MSO.freeFO_lt_foBound φ hi
      rw [extFO, dif_pos hik, hfo]
    · rw [extSO]
      split <;> rfl
  · intro hsat
    refine ⟨valid_annotate hfolt, ?_⟩
    refine (MSO.sat_congr w φ (fun i => if i = 0 then x else y) (extFO k fo)
      (fun _ => ∅) (extSO l (fun _ => ∅)) (fun i hi => ?_) (fun j _ => ?_)).1 hsat
    · have hik : i < k := MSO.freeFO_lt_foBound φ hi
      rw [extFO, dif_pos hik, hfo]
    · rw [extSO]
      split <;> rfl

end MarkStr
end Lax916827Proofs.Transducers
