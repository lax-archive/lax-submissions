/-
Marking the entries of a list representation, for the easy direction of Theorem
`thm:regular-terms` of *Transducers* (M. Bojańczyk).

Two of the atomic terms -- reverse -- and one of the combinators -- map -- do not read their input
from left to right, and so are not implemented by a machine of `CombMach.lean`.  Both are instead
reduced to the map lifting `Transducers.mapLift` of Part A, which applies a function to every block
of a string that is delimited by a fresh separator.

The reduction goes through the *marking* of a list representation: the outer brackets are removed,
the top-level commas are replaced by the separator (`none` of `Option Sym8`), and every other letter
`c` is kept as `some c`.  The marking of `[a₁,…,aₙ]` is therefore the string

    repr a₁ # ⋯ # repr aₙ

and it is produced by a machine of `CombMach.lean` with output alphabet `Option Sym8` -- the
top-level commas are recognised by the bracket counter exactly as everywhere else.  Its inverse,
which puts the brackets back and turns the separators into commas, is a homomorphism between two
constants, hence rational.

With this, map is `mapLift` of the function on the entries, and reverse is `mapLift` of the string
reverse composed with the string reverse -- reversing the whole marked string reverses both the
order of the blocks and each block, and the second reverse repairs the blocks.
-/
import Lax709149Proofs.Source.PartC.CombMach
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-! ## Blocks separated by the marker -/

/-- The strings `x₁,…,xₙ`, marked and separated by the marker `none`. -/
def optBlocks : List (List Sym8) → List (Option Sym8)
  | [] => []
  | [x] => x.map some
  | x :: xs => x.map some ++ none :: optBlocks xs

/-- The part of `optBlocks` that follows the first block. -/
def optBlocksTail : List (List Sym8) → List (Option Sym8)
  | [] => []
  | x :: xs => none :: optBlocks (x :: xs)

@[simp] lemma optBlocks_nil : optBlocks [] = [] := rfl

@[simp] lemma optBlocks_singleton (x : List Sym8) : optBlocks [x] = x.map some := rfl

@[simp] lemma optBlocksTail_nil : optBlocksTail [] = [] := rfl

lemma optBlocks_cons (x : List Sym8) (xs : List (List Sym8)) :
    optBlocks (x :: xs) = x.map some ++ optBlocksTail xs := by
  cases xs with
  | nil => simp [optBlocksTail]
  | cons y ys => rfl

lemma optBlocksTail_cons (x : List Sym8) (xs : List (List Sym8)) :
    optBlocksTail (x :: xs) = none :: optBlocks (x :: xs) := rfl

/-- The marking is the interleaving of the marked blocks with the separator. -/
lemma intercalate_single {X : Type} (sep x : List X) : List.intercalate sep [x] = x := by
  simp [List.intercalate]

lemma optBlocks_eq_intercalate (xs : List (List Sym8)) :
    optBlocks xs = List.intercalate [none] (xs.map (fun u => u.map (some : Sym8 → Option Sym8))) :=
  by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rw [optBlocks_singleton, List.map_singleton, intercalate_single]
      | cons y ys =>
          have h := intercalate_cons_cons [(none : Option Sym8)] (x.map some)
            ((y :: ys).map (fun u => u.map (some : Sym8 → Option Sym8))) (by simp)
          rw [optBlocks_cons, optBlocksTail_cons, ih,
            show ((x :: y :: ys).map (fun u => u.map (some : Sym8 → Option Sym8)))
              = x.map some :: ((y :: ys).map (fun u => u.map (some : Sym8 → Option Sym8)))
              from rfl, h]
          simp

/-- Splitting the marking at the separators recovers the blocks. -/
lemma splitSep_optBlocks (xs : List (List Sym8)) (hxs : xs ≠ []) :
    splitSep (optBlocks xs) = xs := by
  induction xs with
  | nil => exact absurd rfl hxs
  | cons x xs ih =>
      cases xs with
      | nil =>
          have h := splitSep_map_some_append x ([] : List (Option Sym8)) [] [] rfl
          simpa using h
      | cons y ys =>
          have hrec : splitSep (optBlocks (y :: ys)) = y :: ys := ih (by simp)
          have h := splitSep_map_some_append x (none :: optBlocks (y :: ys)) [] (y :: ys)
            (by rw [show splitSep (none :: optBlocks (y :: ys))
              = [] :: splitSep (optBlocks (y :: ys)) from rfl, hrec])
          rw [optBlocks_cons, optBlocksTail_cons]
          simpa using h

/-- **The map lifting acts on the blocks of a marking.** -/
lemma mapLift_optBlocks {g : List Sym8 → List Sym8} (hg : g [] = []) (xs : List (List Sym8)) :
    mapLift g (optBlocks xs) = optBlocks (xs.map g) := by
  cases hxs : xs with
  | nil => rw [optBlocks_nil, mapLift, show splitSep ([] : List (Option Sym8)) = [[]] from rfl]
           simp [hg, intercalate_single]
  | cons x xs' =>
      rw [mapLift, splitSep_optBlocks _ (by simp), optBlocks_eq_intercalate, List.map_map]
      rfl

/-! ## The letter that the marker stands for -/

/-- The letter that a marked letter stands for: the separator stands for a comma. -/
def unopt : Option Sym8 → Sym8
  | none => Sym8.comma
  | some c => c

@[simp] lemma unopt_some (c : Sym8) : unopt (some c) = c := rfl

@[simp] lemma unopt_none : unopt none = Sym8.comma := rfl

lemma map_unopt_optBlocks (xs : List (List Sym8)) : (optBlocks xs).map unopt = joinSep xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp [List.map_map, Function.comp_def]
      | cons y ys =>
          rw [optBlocks_cons, optBlocksTail_cons, joinSep_cons_cons, List.map_append,
            List.map_cons, ih]
          simp [List.map_map, Function.comp_def]

/-- Unmarking: the brackets are put back and the separators become commas. -/
def unmark (v : List (Option Sym8)) : List Sym8 :=
  Sym8.lbrack :: (v.map unopt ++ [Sym8.rbrack])

lemma unmark_optBlocks (B : Ty) (l : List B.Elt) :
    unmark (optBlocks (l.map B.repr)) = (Ty.list B).repr l := by
  rw [unmark, map_unopt_optBlocks, Ty.repr_list]

lemma isRegularFun_unmark : IsRegularFun unmark := by
  have h : IsRegularFun (fun v : List (Option Sym8) =>
      [Sym8.lbrack] ++ (v.map unopt ++ [Sym8.rbrack])) :=
    isRegularFun_concat (IsRegularFun.of_rational (isRationalFun_const _))
      (isRegularFun_concat (isRegularFun_map unopt)
        (IsRegularFun.of_rational (isRationalFun_const _)))
  exact h.congr (fun v => rfl)

/-! ## The machine that marks a list representation -/

/-- The modes of the marking machine: before the opening bracket, inside the list, and after the
closing bracket. -/
inductive ListMarkMode | start | body | done
  deriving DecidableEq, Fintype

/-- The machine that marks a list representation: it deletes the outer brackets, replaces the
top-level commas by the separator, and marks every other letter. -/
def listMarkMach : Mach ListMarkMode (Option Sym8) where
  step := fun m e c => match m with
    | .start => .body
    | .body => if e = 1 ∧ c = Sym8.rbrack then .done else .body
    | .done => .done
  out := fun m e c => match m with
    | .start => []
    | .body =>
        if e = 1 ∧ c = Sym8.rbrack then []
        else if e = 1 ∧ c = Sym8.comma then [none] else [some c]
    | .done => []
  fin := fun _ _ => []

@[simp] lemma listMarkMach_out_start (e : ℕ) (c : Sym8) : listMarkMach.out .start e c = [] := rfl
@[simp] lemma listMarkMach_step_start (e : ℕ) (c : Sym8) : listMarkMach.step .start e c = .body := rfl
@[simp] lemma listMarkMach_out_body_rbrack : listMarkMach.out .body 1 Sym8.rbrack = [] := rfl
@[simp] lemma listMarkMach_step_body_rbrack : listMarkMach.step .body 1 Sym8.rbrack = .done := rfl
@[simp] lemma listMarkMach_out_body_comma : listMarkMach.out .body 1 Sym8.comma = [none] := rfl
@[simp] lemma listMarkMach_step_body_comma : listMarkMach.step .body 1 Sym8.comma = .body := rfl
@[simp] lemma listMarkMach_out_done (e : ℕ) (c : Sym8) : listMarkMach.out .done e c = [] := rfl
@[simp] lemma listMarkMach_step_done (e : ℕ) (c : Sym8) : listMarkMach.step .done e c = .done := rfl
@[simp] lemma listMarkMach_fin (m : ListMarkMode) (e : ℕ) : listMarkMach.fin m e = [] := rfl

section Mark

variable (A : Ty)

/-- The cap of the marking machine: the height of the type of its input. -/
def listMarkN : ℕ := (Ty.list A).height

lemma listMarkN_eq : listMarkN A = A.height + 1 := by
  simp [listMarkN, Ty.height]; omega

/-- The counter at depth `1`, inside the list. -/
private def m1 : Fin (listMarkN A + 1) := ⟨1, by rw [listMarkN_eq]; omega⟩

@[simp] private lemma m1_val : (m1 A).1 = 1 := rfl

private lemma dstep_m0_lbrack : dstep (0 : Fin (listMarkN A + 1)) Sym8.lbrack = m1 A := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by simp only [Fin.val_zero]; rw [listMarkN_eq]; omega)]
  rfl

private lemma listMarkCap : (1 : ℤ) + (A.height : ℤ) ≤ (listMarkN A : ℤ) := by
  rw [listMarkN_eq]; push_cast; omega

private lemma listMark_copies : listMarkMach.Copies .body (m1 A).1 (fun c => [some c]) := by
  intro e c he htr
  simp only [m1_val] at he htr
  have h1 : ¬ (e = 1 ∧ c = Sym8.rbrack) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  have h2 : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [listMarkMach, h1, if_false],
    by simp only [listMarkMach, h1, h2, if_false]⟩

private lemma flatten_map_some (w : List Sym8) :
    (w.map (fun c => [(some c : Option Sym8)])).flatten = w.map some := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [ih]

/-- The run of the marking machine through the body of the list. -/
private lemma listMarkMach_body :
    ∀ (l : List A.Elt) (rest : List Sym8),
      listMarkMach.runFrom (listMarkN A) (ListMarkMode.body, m1 A) (joinSep (l.map A.repr) ++ rest)
        = optBlocks (l.map A.repr)
          ++ listMarkMach.runFrom (listMarkN A) (ListMarkMode.body, m1 A) rest := by
  intro l
  induction l with
  | nil => intro rest; simp
  | cons a l ih =>
      intro rest
      rw [joinSep_cons, List.append_assoc,
        listMarkMach.runFrom_repr (listMarkN A) _ (fun c => [some c]) A a (m1 A) _
          (by simpa using listMarkCap A) (listMark_copies A),
        flatten_map_some, List.map_cons, optBlocks_cons, List.append_assoc]
      congr 1
      cases l with
      | nil => simp
      | cons b l' =>
          rw [joinSepTail_cons, List.cons_append, Mach.runFrom_cons]
          simp only [m1_val, listMarkMach_out_body_comma, listMarkMach_step_body_comma,
            dstep_neutral (by simp : wt Sym8.comma = 0)]
          rw [show (m1 A) = dstep (m1 A) Sym8.comma from
            (dstep_neutral (by simp : wt Sym8.comma = 0)).symm]
          rw [dstep_neutral (by simp : wt Sym8.comma = 0), ih rest, List.map_cons,
            optBlocksTail_cons]
          rfl

/-- **The marking machine marks the representation of a list.** -/
theorem listMarkMach_run (l : List A.Elt) :
    listMarkMach.run (listMarkN A) .start ((Ty.list A).repr l) = optBlocks (l.map A.repr) := by
  show listMarkMach.runFrom (listMarkN A) (ListMarkMode.start, 0)
      (Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack])) = _
  rw [Mach.runFrom_cons]
  simp only [listMarkMach_out_start, listMarkMach_step_start, dstep_m0_lbrack, List.nil_append]
  rw [listMarkMach_body]
  rw [show listMarkMach.runFrom (listMarkN A) (ListMarkMode.body, m1 A) [Sym8.rbrack] = [] from by
    rw [Mach.runFrom_cons]
    simp only [m1_val, listMarkMach_out_body_rbrack, listMarkMach_step_body_rbrack, List.nil_append]
    rw [Mach.runFrom_nil]
    simp only [listMarkMach_fin]]
  rw [List.append_nil]

/-- The marking is a regular function. -/
theorem isRegularFun_listMarkRun : IsRegularFun (listMarkMach.run (listMarkN A) .start) :=
  listMarkMach.isRegularFun_run _ _

end Mark

/-! ## The reverse of a string is a regular function -/

/-- **The reverse of a string is a regular function.**  It is the map reverse applied to the
one-block encoding of the string. -/
theorem isRegularFun_listReverse (A : Type) [Finite A] :
    IsRegularFun (fun w : List A => w.reverse) := by
  have h1 : IsRegularFun (fun w : List A => (none : Option A) :: w.map some) := by
    have := (IsRegularFun.of_rational (isRationalFun_map (some : A → Option A))).comp'
      (IsRegularFun.of_rational (isRationalFun_cons (none : Option A))) (fun _ => rfl)
    exact this
  have h2 : IsRegularFun (fun w : List A => mapReverse A ((none : Option A) :: w.map some)) :=
    h1.comp' (isRegularFun_mapReverse A) (fun _ => rfl)
  have h3 : IsRegularFun (fun w : List A =>
      RegCl.del (mapReverse A ((none : Option A) :: w.map some))) :=
    h2.comp' RegCl.isRegularFun_del (fun _ => rfl)
  refine h3.congr (fun w => ?_)
  have hsplit : splitSep ((none : Option A) :: w.map some) = [[], w] := by
    rw [splitSep]
    have h := splitSep_map_some_append w ([] : List (Option A)) [] [] rfl
    simpa using h
  rw [mapReverse, mapLift, hsplit]
  show RegCl.del (List.intercalate [none] [([] : List A).reverse.map some, w.reverse.map some]) = _
  rw [show List.intercalate [(none : Option A)]
      [([] : List A).reverse.map some, w.reverse.map some]
      = none :: w.reverse.map some from by
    rw [intercalate_cons_cons _ _ _ (by simp), intercalate_single]
    simp]
  exact RegCl.del_marked _

end Comb
end Lax709149Proofs.Transducers
