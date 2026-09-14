/-
Concatenation is regular under string representation.  Part of the easy direction of Theorem
`thm:regular-terms` of *Transducers* (M. Bojańczyk).

Concatenation `A** → A*` flattens a list of lists, and under string representation it has to remove
the inner brackets and produce exactly one comma between two consecutive entries of the output --
which is delicate because an inner list may be empty, and because the entry that a comma precedes
may come from another inner list than the entry before it.

The device used here, and again for the split term, is to write *every* entry of the output
preceded by a comma, and to remove the leading comma at the end.  Writing a comma before an entry
needs no lookahead beyond the letter that opens the entry, and removing the first letter of a string
is another sequential machine, so concatenation is a composition of two regular functions.
-/
import Lax709149Proofs.Source.PartC.CombMach
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-! ## The machine that writes the entries, each preceded by a comma -/

/-- The modes of the machine of concatenation: before the outer bracket, between the inner lists,
at the letter that opens an entry (or closes an empty inner list), inside an entry or between the
entries of one inner list, and after the outer closing bracket. -/
inductive ConcatMode | start | outer | pend | inner | dead
  deriving DecidableEq, Fintype

/-- The machine that writes the entries of the flattened list, each preceded by a comma. -/
def concatMach : Mach ConcatMode Sym8 where
  step := fun m e c => match m with
    | .start => .outer
    | .outer => if c = Sym8.lbrack then .pend else if c = Sym8.rbrack then .dead else .outer
    | .pend => if c = Sym8.rbrack then .outer else .inner
    | .inner => if e = 2 ∧ c = Sym8.rbrack then .outer else .inner
    | .dead => .dead
  out := fun m e c => match m with
    | .start => []
    | .outer => []
    | .pend => if c = Sym8.rbrack then [] else [Sym8.comma, c]
    | .inner => if e = 2 ∧ c = Sym8.rbrack then [] else [c]
    | .dead => []
  fin := fun _ _ => []

@[simp] lemma concatMach_out_start (e : ℕ) (c : Sym8) : concatMach.out .start e c = [] := rfl
@[simp] lemma concatMach_step_start (e : ℕ) (c : Sym8) : concatMach.step .start e c = .outer := rfl
@[simp] lemma concatMach_out_outer (e : ℕ) (c : Sym8) : concatMach.out .outer e c = [] := rfl
@[simp] lemma concatMach_step_outer_lbrack (e : ℕ) :
    concatMach.step .outer e Sym8.lbrack = .pend := rfl
@[simp] lemma concatMach_step_outer_rbrack (e : ℕ) :
    concatMach.step .outer e Sym8.rbrack = .dead := rfl
@[simp] lemma concatMach_step_outer_comma (e : ℕ) :
    concatMach.step .outer e Sym8.comma = .outer := rfl
@[simp] lemma concatMach_out_pend_rbrack (e : ℕ) : concatMach.out .pend e Sym8.rbrack = [] := rfl
@[simp] lemma concatMach_step_pend_rbrack (e : ℕ) :
    concatMach.step .pend e Sym8.rbrack = .outer := rfl
@[simp] lemma concatMach_out_inner_rbrack : concatMach.out .inner 2 Sym8.rbrack = [] := rfl
@[simp] lemma concatMach_step_inner_rbrack : concatMach.step .inner 2 Sym8.rbrack = .outer := rfl
@[simp] lemma concatMach_out_dead (e : ℕ) (c : Sym8) : concatMach.out .dead e c = [] := rfl
@[simp] lemma concatMach_step_dead (e : ℕ) (c : Sym8) : concatMach.step .dead e c = .dead := rfl
@[simp] lemma concatMach_fin (m : ConcatMode) (e : ℕ) : concatMach.fin m e = [] := rfl

/-! ## The machine that removes the leading comma and puts the brackets back -/

/-- The modes of the machine that removes the first letter of its input. -/
inductive DropMode | first | later
  deriving DecidableEq, Fintype

/-- The machine that removes the first letter of its input and wraps the rest in brackets.  The
depth plays no role here. -/
def dropFirstMach : Mach DropMode Sym8 where
  step := fun _ _ _ => .later
  out := fun m _ c => match m with
    | .first => [Sym8.lbrack]
    | .later => [c]
  fin := fun m _ => match m with
    | .first => [Sym8.lbrack, Sym8.rbrack]
    | .later => [Sym8.rbrack]

@[simp] lemma dropFirstMach_step (m : DropMode) (e : ℕ) (c : Sym8) :
    dropFirstMach.step m e c = .later := rfl
@[simp] lemma dropFirstMach_out_later (e : ℕ) (c : Sym8) :
    dropFirstMach.out .later e c = [c] := rfl
@[simp] lemma dropFirstMach_out_first (e : ℕ) (c : Sym8) :
    dropFirstMach.out .first e c = [Sym8.lbrack] := rfl

lemma dropFirstMach_later {N : ℕ} (v : List Sym8) (d : Fin (N + 1)) :
    dropFirstMach.runFrom N (DropMode.later, d) v = v ++ [Sym8.rbrack] := by
  induction v generalizing d with
  | nil => rfl
  | cons c v ih =>
      rw [Mach.runFrom_cons]
      simp only [dropFirstMach_step, dropFirstMach_out_later]
      rw [ih]
      rfl

/-- The second machine turns the list of comma-prefixed entries into the representation of a
list. -/
theorem dropFirstMach_run {N : ℕ} (v : List Sym8) :
    dropFirstMach.run N .first v = Sym8.lbrack :: (v.tail ++ [Sym8.rbrack]) := by
  cases v with
  | nil => rfl
  | cons c v =>
      show dropFirstMach.runFrom N (DropMode.first, 0) (c :: v) = _
      rw [Mach.runFrom_cons]
      simp only [dropFirstMach_step, dropFirstMach_out_first]
      rw [dropFirstMach_later]
      rfl

section Concat

variable (A : Ty)

/-- The domain of concatenation. -/
def catDom : Ty := Ty.list (Ty.list A)

lemma catDom_height : (catDom A).height = A.height + 2 := by
  simp [catDom, Ty.height]
  omega

/-- The counter at depth `1`, inside the outer list. -/
def k1 : Fin ((catDom A).height + 1) := ⟨1, by rw [catDom_height]; omega⟩

/-- The counter at depth `2`, inside an inner list. -/
def k2 : Fin ((catDom A).height + 1) := ⟨2, by rw [catDom_height]; omega⟩

@[simp] lemma k1_val : (k1 A).1 = 1 := rfl
@[simp] lemma k2_val : (k2 A).1 = 2 := rfl

lemma dstep_k0_lbrack : dstep (0 : Fin ((catDom A).height + 1)) Sym8.lbrack = k1 A := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by simp only [Fin.val_zero]; rw [catDom_height]; omega)]
  rfl

lemma dstep_k1_lbrack : dstep (k1 A) Sym8.lbrack = k2 A := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by simp only [k1_val]; rw [catDom_height]; omega)]
  rfl

lemma dstep_k2_rbrack : dstep (k2 A) Sym8.rbrack = k1 A := by
  refine Fin.ext ?_
  rw [dstep_close (by simp)]
  rfl

lemma catCap2 : (2 : ℤ) + (A.height : ℤ) ≤ ((catDom A).height : ℤ) := by
  rw [catDom_height]; push_cast; omega

private lemma concat_copies_inner : concatMach.Copies .inner (k2 A).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 2 ∧ c = Sym8.rbrack) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [concatMach, hne, if_false], by simp only [concatMach, hne, if_false]⟩

private lemma concat_comma_inner : concatMach.CopiesComma .inner (k2 A).1 (fun c => [c]) :=
  ⟨rfl, rfl⟩

/-- The run of the first machine through one inner list. -/
theorem concatMach_inner (li : List A.Elt) (rest : List Sym8) :
    concatMach.runFrom ((catDom A).height) (ConcatMode.outer, k1 A) ((Ty.list A).repr li ++ rest)
      = commaBlocks A li
        ++ concatMach.runFrom ((catDom A).height) (ConcatMode.outer, k1 A) rest := by
  rw [Ty.repr_list, List.cons_append, Mach.runFrom_cons]
  simp only [concatMach_out_outer, concatMach_step_outer_lbrack, dstep_k1_lbrack, List.nil_append]
  cases li with
  | nil =>
      simp only [List.map_nil, joinSep_nil, List.nil_append, List.singleton_append]
      rw [Mach.runFrom_cons]
      simp only [concatMach_out_pend_rbrack, concatMach_step_pend_rbrack, dstep_k2_rbrack,
        List.nil_append, commaBlocks_nil]
  | cons a li' =>
      obtain ⟨c, w, hcw, hc⟩ := repr_eq_cons A a
      have hcne : c ≠ Sym8.rbrack := by rintro rfl; simp [transparent] at hc
      rw [joinSep_cons, List.append_assoc, List.append_assoc]
      rw [Mach.runFrom_repr_cons _ _ _ _ (fun c => [c]) A a c w hcw (k2 A) _ (catCap2 A)
        (by simp only [k2_val]; simp only [concatMach, hcne, if_false])
        (concat_copies_inner A)]
      rw [show concatMach.out .pend (k2 A).1 c = [Sym8.comma, c] from by
        simp only [concatMach, hcne, if_false]]
      rw [flatten_map_single]
      rw [Mach.runFrom_joinSepTail _ _ _ (fun c => [c]) A (k2 A) (catCap2 A)
        (concat_copies_inner A) (concat_comma_inner A) li' _]
      rw [joinSepTail_eq_commaBlocks, flatten_map_single]
      rw [List.singleton_append, Mach.runFrom_cons]
      simp only [k2_val, concatMach_out_inner_rbrack, concatMach_step_inner_rbrack,
        dstep_k2_rbrack, List.nil_append]
      rw [commaBlocks_cons, hcw]
      simp

/-- The run of the first machine through the entries of the outer list that follow the first. -/
theorem concatMach_tail (l : List (List A.Elt)) (rest : List Sym8) :
    concatMach.runFrom ((catDom A).height) (ConcatMode.outer, k1 A)
        (joinSepTail (Ty.list A) l ++ rest)
      = commaBlocks A l.flatten
        ++ concatMach.runFrom ((catDom A).height) (ConcatMode.outer, k1 A) rest := by
  induction l with
  | nil => erw [joinSepTail_nil, List.nil_append, List.flatten_nil, commaBlocks_nil,
      List.nil_append]
  | cons li l ih =>
      erw [joinSepTail_cons, joinSep_cons, List.cons_append, Mach.runFrom_cons]
      simp only [concatMach_out_outer, concatMach_step_outer_comma,
        dstep_neutral (by simp : wt Sym8.comma = 0), List.nil_append]
      rw [List.append_assoc, concatMach_inner, ih, List.flatten_cons, commaBlocks_append,
        List.append_assoc]

/-- The run of the first machine through the whole body of the input. -/
theorem concatMach_body (l : List (List A.Elt)) (rest : List Sym8) :
    concatMach.runFrom ((catDom A).height) (ConcatMode.outer, k1 A)
        (joinSep (l.map (Ty.list A).repr) ++ rest)
      = commaBlocks A l.flatten
        ++ concatMach.runFrom ((catDom A).height) (ConcatMode.outer, k1 A) rest := by
  cases l with
  | nil => erw [List.map_nil]; simp
  | cons li l =>
      erw [joinSep_cons, List.append_assoc, concatMach_inner, concatMach_tail, List.flatten_cons,
        commaBlocks_append, List.append_assoc]

theorem concatMach_run (l : List (List A.Elt)) :
    concatMach.run ((catDom A).height) .start ((catDom A).repr l) = commaBlocks A l.flatten := by
  show concatMach.runFrom ((catDom A).height) (ConcatMode.start, 0)
      (Sym8.lbrack :: (joinSep (l.map (Ty.list A).repr) ++ [Sym8.rbrack])) = _
  rw [Mach.runFrom_cons]
  simp only [concatMach_out_start, concatMach_step_start, dstep_k0_lbrack, List.nil_append]
  rw [concatMach_body]
  rw [show concatMach.runFrom ((catDom A).height) (ConcatMode.outer, k1 A) [Sym8.rbrack] = []
      from by
    rw [Mach.runFrom_cons]
    simp only [concatMach_out_outer, concatMach_step_outer_rbrack, List.nil_append]
    rw [Mach.runFrom_nil]
    simp only [concatMach_fin]]
  rw [List.append_nil]

/-- **Concatenation is regular under string representation.** -/
theorem isRegularUnderRepr_concat :
    IsRegularUnderRepr (A := catDom A) (B := Ty.list A) (fun l => l.flatten) := by
  refine ⟨fun w => dropFirstMach.run ((catDom A).height)
      .first (concatMach.run ((catDom A).height) .start w),
    (concatMach.isRegularFun_run _ _).comp' (dropFirstMach.isRegularFun_run _ _) (fun _ => rfl),
    fun l => ?_⟩
  show dropFirstMach.run _ .first (concatMach.run _ ConcatMode.start ((catDom A).repr l)) = _
  rw [concatMach_run, dropFirstMach_run, commaBlocks_tail]
  rfl

end Concat

end Comb
end Lax709149Proofs.Transducers
