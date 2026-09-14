/-
Split is regular under string representation.  Part of the easy direction of Theorem
`thm:regular-terms` of *Transducers* (M. Bojańczyk).

Split `(A + B)* → A* × (B × A*)*` cuts its input at the entries that come from `B`.  Under string
representation it is computed by a single machine of `CombMach.lean`, which needs no lookahead: the
representation of an entry begins with the letter `L` or `R`, which already says whether the entry
opens a new block or extends the current one.

The machine keeps, besides the part of the input it is inside of, two bits: whether an entry from
`B` has already been seen -- that is, whether the output is inside the list of pairs or still
inside the first block -- and whether the block it is currently writing already has an entry, which
is what decides whether the entry it is about to write has to be preceded by a comma.  The
brackets and commas of the output are therefore all written at the letter of the input at which
they become known, and no second pass is needed.
-/
import Lax709149Proofs.Source.PartC.CombMach
import Lax709149Proofs.Source.PartC.CombTerms
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-! ## The machine -/

/-- The part of the input that the machine of split is inside of: before the opening bracket,
between two entries, inside an entry from `A`, inside an entry from `B`, and after the closing
bracket. -/
inductive SplitPhase | start | wait | copyA | copyB | done
  deriving DecidableEq, Fintype

/-- The mode of the machine of split: the part of the input, whether an entry from `B` has been
seen, and whether the block being written already has an entry. -/
abbrev SplitMode := SplitPhase × Bool × Bool

/-- What the machine of split writes at the end of the input: the current block and the pair that
contains it are closed, and so is the list of pairs -- which has to be opened first if no entry
from `B` was ever seen. -/
def splitClose (s : Bool) : List Sym8 :=
  if s then [Sym8.rbrack, Sym8.rpar, Sym8.rbrack, Sym8.rpar]
  else [Sym8.rbrack, Sym8.comma, Sym8.lbrack, Sym8.rbrack, Sym8.rpar]

/-- The machine of split. -/
def splitMach : Mach SplitMode Sym8 where
  step := fun m e c =>
    match m with
    | (.start, s, n) => (.wait, s, n)
    | (.wait, s, n) =>
        if e = 1 ∧ c = Sym8.left then (.copyA, s, true)
        else if e = 1 ∧ c = Sym8.right then (.copyB, true, false)
        else if e = 1 ∧ c = Sym8.rbrack then (.done, s, n)
        else (.wait, s, n)
    | (.copyA, s, n) =>
        if e = 1 ∧ c = Sym8.comma then (.wait, s, n)
        else if e = 1 ∧ c = Sym8.rbrack then (.done, s, n)
        else (.copyA, s, n)
    | (.copyB, s, n) =>
        if e = 1 ∧ c = Sym8.comma then (.wait, s, false)
        else if e = 1 ∧ c = Sym8.rbrack then (.done, s, n)
        else (.copyB, s, n)
    | (.done, s, n) => (.done, s, n)
  out := fun m e c =>
    match m with
    | (.start, _, _) => [Sym8.lpar, Sym8.lbrack]
    | (.wait, s, n) =>
        if e = 1 ∧ c = Sym8.left then (if n then [Sym8.comma] else [])
        else if e = 1 ∧ c = Sym8.right then
          (if s then [Sym8.rbrack, Sym8.rpar, Sym8.comma, Sym8.lpar]
            else [Sym8.rbrack, Sym8.comma, Sym8.lbrack, Sym8.lpar])
        else if e = 1 ∧ c = Sym8.rbrack then splitClose s
        else []
    | (.copyA, s, _) =>
        if e = 1 ∧ c = Sym8.comma then []
        else if e = 1 ∧ c = Sym8.rbrack then splitClose s
        else [c]
    | (.copyB, s, _) =>
        if e = 1 ∧ c = Sym8.comma then [Sym8.comma, Sym8.lbrack]
        else if e = 1 ∧ c = Sym8.rbrack then [Sym8.comma, Sym8.lbrack] ++ splitClose s
        else [c]
    | (.done, _, _) => []
  fin := fun _ _ => []

@[simp] lemma splitMach_out_start (s n : Bool) (e : ℕ) (c : Sym8) :
    splitMach.out (SplitPhase.start, s, n) e c = [Sym8.lpar, Sym8.lbrack] := rfl

@[simp] lemma splitMach_step_start (s n : Bool) (e : ℕ) (c : Sym8) :
    splitMach.step (SplitPhase.start, s, n) e c = (SplitPhase.wait, s, n) := rfl

@[simp] lemma splitMach_out_wait_left (s n : Bool) :
    splitMach.out (SplitPhase.wait, s, n) 1 Sym8.left = (if n then [Sym8.comma] else []) := rfl

@[simp] lemma splitMach_step_wait_left (s n : Bool) :
    splitMach.step (SplitPhase.wait, s, n) 1 Sym8.left = (SplitPhase.copyA, s, true) := rfl

@[simp] lemma splitMach_out_wait_right (s n : Bool) :
    splitMach.out (SplitPhase.wait, s, n) 1 Sym8.right
      = (if s then [Sym8.rbrack, Sym8.rpar, Sym8.comma, Sym8.lpar]
          else [Sym8.rbrack, Sym8.comma, Sym8.lbrack, Sym8.lpar]) := rfl

@[simp] lemma splitMach_step_wait_right (s n : Bool) :
    splitMach.step (SplitPhase.wait, s, n) 1 Sym8.right = (SplitPhase.copyB, true, false) := rfl

@[simp] lemma splitMach_out_wait_rbrack (s n : Bool) :
    splitMach.out (SplitPhase.wait, s, n) 1 Sym8.rbrack = splitClose s := rfl

@[simp] lemma splitMach_step_wait_rbrack (s n : Bool) :
    splitMach.step (SplitPhase.wait, s, n) 1 Sym8.rbrack = (SplitPhase.done, s, n) := rfl

@[simp] lemma splitMach_out_copyA_comma (s n : Bool) :
    splitMach.out (SplitPhase.copyA, s, n) 1 Sym8.comma = [] := rfl

@[simp] lemma splitMach_step_copyA_comma (s n : Bool) :
    splitMach.step (SplitPhase.copyA, s, n) 1 Sym8.comma = (SplitPhase.wait, s, n) := rfl

@[simp] lemma splitMach_out_copyA_rbrack (s n : Bool) :
    splitMach.out (SplitPhase.copyA, s, n) 1 Sym8.rbrack = splitClose s := rfl

@[simp] lemma splitMach_step_copyA_rbrack (s n : Bool) :
    splitMach.step (SplitPhase.copyA, s, n) 1 Sym8.rbrack = (SplitPhase.done, s, n) := rfl

@[simp] lemma splitMach_out_copyB_comma (s n : Bool) :
    splitMach.out (SplitPhase.copyB, s, n) 1 Sym8.comma = [Sym8.comma, Sym8.lbrack] := rfl

@[simp] lemma splitMach_step_copyB_comma (s n : Bool) :
    splitMach.step (SplitPhase.copyB, s, n) 1 Sym8.comma = (SplitPhase.wait, s, false) := rfl

@[simp] lemma splitMach_out_copyB_rbrack (s n : Bool) :
    splitMach.out (SplitPhase.copyB, s, n) 1 Sym8.rbrack
      = [Sym8.comma, Sym8.lbrack] ++ splitClose s := rfl

@[simp] lemma splitMach_step_copyB_rbrack (s n : Bool) :
    splitMach.step (SplitPhase.copyB, s, n) 1 Sym8.rbrack = (SplitPhase.done, s, n) := rfl

@[simp] lemma splitMach_out_done (s n : Bool) (e : ℕ) (c : Sym8) :
    splitMach.out (SplitPhase.done, s, n) e c = [] := rfl

@[simp] lemma splitMach_step_done (s n : Bool) (e : ℕ) (c : Sym8) :
    splitMach.step (SplitPhase.done, s, n) e c = (SplitPhase.done, s, n) := rfl

@[simp] lemma splitMach_fin (m : SplitMode) (e : ℕ) : splitMach.fin m e = [] := rfl

section Split

variable (A B : Ty)

/-- The domain of split. -/
def splitDom : Ty := Ty.list (Ty.sum A B)

lemma splitDom_height : (splitDom A B).height = 1 + max A.height B.height := rfl

/-- The counter at depth `1`, inside the list. -/
def s1 : Fin ((splitDom A B).height + 1) := ⟨1, by rw [splitDom_height]; omega⟩

@[simp] lemma s1_val : (s1 A B).1 = 1 := rfl

lemma dstep_s0_lbrack : dstep (0 : Fin ((splitDom A B).height + 1)) Sym8.lbrack = s1 A B := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by simp only [Fin.val_zero]; rw [splitDom_height]; omega)]
  rfl

lemma splitCap : (1 : ℤ) + ((Ty.sum A B).height : ℤ) ≤ ((splitDom A B).height : ℤ) := by
  rw [splitDom_height]
  show (1 : ℤ) + (max A.height B.height : ℕ) ≤ ((1 + max A.height B.height : ℕ) : ℤ)
  push_cast
  omega

private lemma split_copies_A (s n : Bool) :
    splitMach.Copies (SplitPhase.copyA, s, n) (s1 A B).1 (fun c => [c]) := by
  intro e c he htr
  simp only [s1_val] at he htr
  have h1 : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  have h2 : ¬ (e = 1 ∧ c = Sym8.rbrack) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [splitMach, h1, h2, if_false], by simp only [splitMach, h1, h2, if_false]⟩

private lemma split_copies_B (s n : Bool) :
    splitMach.Copies (SplitPhase.copyB, s, n) (s1 A B).1 (fun c => [c]) := by
  intro e c he htr
  simp only [s1_val] at he htr
  have h1 : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  have h2 : ¬ (e = 1 ∧ c = Sym8.rbrack) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [splitMach, h1, h2, if_false], by simp only [splitMach, h1, h2, if_false]⟩

/-! ## What the machine writes -/

/-- The output of the machine of split, read from a state between two entries. -/
def splitOut : List ((Ty.sum A B).Elt) → Bool → Bool → List Sym8
  | [], s, _ => splitClose s
  | Sum.inl a :: l, s, n =>
      (if n then [Sym8.comma] else []) ++ (A.repr a ++ splitOut l s true)
  | Sum.inr b :: l, s, _ =>
      (if s then [Sym8.rbrack, Sym8.rpar, Sym8.comma, Sym8.lpar]
        else [Sym8.rbrack, Sym8.comma, Sym8.lbrack, Sym8.lpar])
        ++ (B.repr b ++ ([Sym8.comma, Sym8.lbrack] ++ splitOut l true false))

/-- **The machine of split writes `splitOut`.** -/
theorem splitMach_body :
    ∀ (l : List ((Ty.sum A B).Elt)) (s n : Bool),
      splitMach.runFrom ((splitDom A B).height) ((SplitPhase.wait, s, n), s1 A B)
          (joinSep (l.map (Ty.sum A B).repr) ++ [Sym8.rbrack])
        = splitOut A B l s n := by
  intro l
  induction l with
  | nil =>
      intro s n
      rw [List.map_nil, joinSep_nil, List.nil_append, Mach.runFrom_cons]
      simp only [s1_val, splitMach_out_wait_rbrack, splitMach_step_wait_rbrack]
      rw [Mach.runFrom_nil]
      simp only [splitMach_fin, List.append_nil]
      rfl
  | cons x l ih =>
      intro s n
      rw [joinSep_cons, List.append_assoc]
      cases x with
      | inl a =>
          have hx : (Ty.sum A B).repr (Sum.inl a) = Sym8.left :: A.repr a := rfl
          rw [splitMach.runFrom_repr_cons ((splitDom A B).height) (SplitPhase.wait, s, n)
            (SplitPhase.copyA, s, true) (fun c => [c]) (Ty.sum A B) (Sum.inl a) Sym8.left
            (A.repr a) hx (s1 A B) _ (by simpa using splitCap A B) (by simp) (split_copies_A A B _ _)]
          rw [flatten_map_single]
          have htail : splitMach.runFrom ((splitDom A B).height)
              ((SplitPhase.copyA, s, true), s1 A B)
              (joinSepTail (Ty.sum A B) l ++ [Sym8.rbrack]) = splitOut A B l s true := by
            cases l with
            | nil =>
                rw [joinSepTail_nil, List.nil_append, Mach.runFrom_cons]
                simp only [s1_val, splitMach_out_copyA_rbrack, splitMach_step_copyA_rbrack]
                rw [Mach.runFrom_nil]
                simp only [splitMach_fin, List.append_nil]
                rfl
            | cons y l' =>
                rw [joinSepTail_cons, List.cons_append, Mach.runFrom_cons]
                simp only [s1_val, splitMach_out_copyA_comma, splitMach_step_copyA_comma,
                  dstep_neutral (by simp : wt Sym8.comma = 0), List.nil_append]
                exact ih s true
          rw [htail]
          simp only [s1_val, splitMach_out_wait_left]
          rfl
      | inr b =>
          have hx : (Ty.sum A B).repr (Sum.inr b) = Sym8.right :: B.repr b := rfl
          rw [splitMach.runFrom_repr_cons ((splitDom A B).height) (SplitPhase.wait, s, n)
            (SplitPhase.copyB, true, false) (fun c => [c]) (Ty.sum A B) (Sum.inr b) Sym8.right
            (B.repr b) hx (s1 A B) _ (by simpa using splitCap A B) (by simp)
            (split_copies_B A B _ _)]
          rw [flatten_map_single]
          have htail : splitMach.runFrom ((splitDom A B).height)
              ((SplitPhase.copyB, true, false), s1 A B)
              (joinSepTail (Ty.sum A B) l ++ [Sym8.rbrack])
              = [Sym8.comma, Sym8.lbrack] ++ splitOut A B l true false := by
            cases l with
            | nil =>
                rw [joinSepTail_nil, List.nil_append, Mach.runFrom_cons]
                simp only [s1_val, splitMach_out_copyB_rbrack, splitMach_step_copyB_rbrack]
                rw [Mach.runFrom_nil]
                simp only [splitMach_fin, List.append_nil]
                rfl
            | cons y l' =>
                rw [joinSepTail_cons, List.cons_append, Mach.runFrom_cons]
                simp only [s1_val, splitMach_out_copyB_comma, splitMach_step_copyB_comma,
                  dstep_neutral (by simp : wt Sym8.comma = 0)]
                rw [ih true false]
          rw [htail]
          simp only [s1_val, splitMach_out_wait_right]
          rfl

/-- **The run of the machine of split.** -/
theorem splitMach_run (l : List ((Ty.sum A B).Elt)) :
    splitMach.run ((splitDom A B).height) (SplitPhase.start, false, false) ((splitDom A B).repr l)
      = [Sym8.lpar, Sym8.lbrack] ++ splitOut A B l false false := by
  show splitMach.runFrom ((splitDom A B).height) ((SplitPhase.start, false, false), 0)
      (Sym8.lbrack :: (joinSep (l.map (Ty.sum A B).repr) ++ [Sym8.rbrack])) = _
  rw [Mach.runFrom_cons]
  simp only [splitMach_out_start, splitMach_step_start, dstep_s0_lbrack]
  rw [splitMach_body]

/-! ## What the machine writes is the representation of the split -/

/-- The entries of the block that is being written, with the comma that precedes an entry when the
block is not empty yet. -/
def aBody (as : List A.Elt) (n : Bool) : List Sym8 :=
  if n then commaBlocks A as else joinSep (as.map A.repr)

lemma aBody_cons (a : A.Elt) (as : List A.Elt) (n : Bool) :
    aBody A (a :: as) n = (if n then [Sym8.comma] else []) ++ (A.repr a ++ aBody A as true) := by
  cases n with
  | false =>
      simp only [aBody, if_neg (by simp : ¬ (false = true))]
      rw [joinSep_cons, joinSepTail_eq_commaBlocks]
      simp
  | true =>
      simp only [aBody, if_true]
      rw [commaBlocks_cons]
      simp

@[simp] lemma aBody_nil (n : Bool) : aBody A [] n = [] := by
  cases n <;> simp [aBody]

/-- The type of the pairs in the output of split. -/
def pairTy : Ty := Ty.prod B (Ty.list A)

/-- The output of the machine, from a state inside the list of pairs. -/
lemma splitOut_true (l : List ((Ty.sum A B).Elt)) (n : Bool) :
    splitOut A B l true n
      = aBody A (splitList l).1 n
        ++ ([Sym8.rbrack, Sym8.rpar]
          ++ (commaBlocks (pairTy A B) (splitList l).2 ++ [Sym8.rbrack, Sym8.rpar])) := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons x l ih =>
      cases x with
      | inl a =>
          erw [splitOut, splitList_inl, aBody_cons, ih true]
          simp
      | inr b =>
          erw [splitOut, splitList_inr, ih false]
          simp only [aBody_nil, List.nil_append, if_true]
          erw [commaBlocks_cons]
          show _ = [Sym8.rbrack, Sym8.rpar]
            ++ (Sym8.comma :: ((pairTy A B).repr (b, (splitList l).1)
              ++ commaBlocks (pairTy A B) (splitList l).2) ++ [Sym8.rbrack, Sym8.rpar])
          rw [show (pairTy A B).repr (b, (splitList l).1)
              = Sym8.lpar :: (B.repr b ++ Sym8.comma :: ((Ty.list A).repr (splitList l).1
                ++ [Sym8.rpar])) from rfl,
            Ty.repr_list]
          show _ = _
          simp [aBody]

/-- The output of the machine, from a state inside the first block. -/
lemma splitOut_false (l : List ((Ty.sum A B).Elt)) (n : Bool) :
    splitOut A B l false n
      = aBody A (splitList l).1 n
        ++ ([Sym8.rbrack, Sym8.comma, Sym8.lbrack]
          ++ (joinSep ((splitList l).2.map (pairTy A B).repr) ++ [Sym8.rbrack, Sym8.rpar])) := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons x l ih =>
      cases x with
      | inl a =>
          erw [splitOut, splitList_inl, aBody_cons, ih true]
          simp
      | inr b =>
          erw [splitOut, splitList_inr, splitOut_true]
          simp only [aBody_nil, List.nil_append]
          erw [joinSep_cons, joinSepTail_eq_commaBlocks]
          erw [show (pairTy A B).repr (b, (splitList l).1)
              = Sym8.lpar :: (B.repr b ++ Sym8.comma :: ((Ty.list A).repr (splitList l).1
                ++ [Sym8.rpar])) from rfl,
            Ty.repr_list]
          simp [aBody]

/-- **Split is regular under string representation.** -/
theorem isRegularUnderRepr_split :
    IsRegularUnderRepr (A := splitDom A B)
      (B := Ty.prod (Ty.list A) (Ty.list (pairTy A B))) (fun l => splitList l) := by
  refine ⟨splitMach.run ((splitDom A B).height) (SplitPhase.start, false, false),
    splitMach.isRegularFun_run _ _, fun l => ?_⟩
  rw [splitMach_run, splitOut_false]
  simp only [aBody]
  show _ = Sym8.lpar :: ((Ty.list A).repr (splitList l).1
    ++ Sym8.comma :: ((Ty.list (pairTy A B)).repr (splitList l).2 ++ [Sym8.rpar]))
  rw [Ty.repr_list, Ty.repr_list]
  simp

end Split

end Comb
end Lax709149Proofs.Transducers
