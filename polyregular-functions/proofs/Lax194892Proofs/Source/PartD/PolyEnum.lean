/-
Part D: the enumeration of the tuples of positions visited by a nest of for-loops.

This file is the first phase of the proof that a for-transducer computes a polyregular function
(the right-to-left inclusion of Theorem `thm:for-transducers-are-polyregular`).  Following the
book, a for-transducer in prenex form is simulated by a composition of two functions: the first
one writes down, one after the other and in the order in which the nest of loops visits them, all
the tuples of positions of the input string, each one as an annotated copy of the input; the
second one -- in `RequestProject/PartD/PolyScan.lean` -- scans that string and runs the body of
the nest on each copy.

The enumeration is built one variable at a time.  Adding an innermost loop to the nest means
replacing every block of the enumeration by the `|w|` copies of that block in which the new
variable points at each of its positions; this is obtained by *marked squaring*, which produces
all the copies of the whole enumeration with a prefix underlined, followed by a streaming string
transducer which keeps, out of each copy, only the block in which the underlining ends.  Since
marked squaring is a prime polyregular function and a streaming string transducer computes a
regular function (Theorem `theorem:sst-two-way-equivalence`), the enumeration is polyregular.

A position variable is recorded in the annotation not by marking the position it points at, but
by marking all the positions up to it: this is exactly what the underlining of marked squaring
produces, and the position itself is the last marked one.

This file contains the alphabet of the enumeration, the enumeration itself and the elementary
facts about them, together with the decomposition of a marked square into the *segments* of
copies whose underlining ends inside a prescribed factor of the input, which is what makes the
correctness of the transducer of one step (in `RequestProject/PartD/PolyStep.lean`) provable by
induction on the list of tuples.
-/
import Lax194892Proofs.Source.PartD.PolyDef
import Lax194892Proofs.Source.PartD.ForSem
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PolyEnum

/-! ## The alphabet of the enumeration -/

/-- The alphabet of the enumeration of the tuples of `k` position variables: a letter of the
input annotated with, for every variable, whether the position is at most the value of that
variable, a separator between two consecutive tuples, and an end marker. -/
inductive Ann (A : Type) (k : ℕ) : Type
  /-- An annotated letter of the input string. -/
  | letter : A → (Fin k → Bool) → Ann A k
  /-- The separator that follows every copy of the input string. -/
  | sep : Ann A k
  /-- The end marker, which occurs exactly once, at the very end. -/
  | eos : Ann A k

instance {A : Type} {k : ℕ} [Finite A] : Finite (Ann A k) := by
  have h : Function.Injective
      (fun z : Ann A k => match z with
        | Ann.letter a m => some (some (a, m))
        | Ann.sep => some none
        | Ann.eos => (none : Option (Option (A × (Fin k → Bool))))) := by
    intro z z' h
    cases z <;> cases z' <;> simp_all
  exact Finite.of_injective _ h

/-! ## The annotated copies of the input -/

/-- The annotation of the position `i` by the tuple `t`: the variable `j` marks `i` when `i` is
at most the position `t j`. -/
def annOf (k : ℕ) (t : List ℕ) (i : ℕ) : Fin k → Bool :=
  fun j => decide (i ≤ t.getD (j : ℕ) 0)

/-- One copy of the input string annotated by the tuple `t`, starting at the position `i`. -/
def blockFrom {A : Type} (k : ℕ) (t : List ℕ) : ℕ → List A → List (Ann A k)
  | _, [] => []
  | i, a :: rest => Ann.letter a (annOf k t i) :: blockFrom k t (i + 1) rest

/-- One copy of the input string, annotated by the tuple `t`. -/
def blockAt {A : Type} (k : ℕ) (w : List A) (t : List ℕ) : List (Ann A k) := blockFrom k t 0 w

/-- The enumeration of all the tuples of positions visited by the nest of loops `L`: one
annotated copy of the input per tuple, each followed by a separator, and an end marker. -/
def enum {A : Type} (k : ℕ) (L : List (Bool × ℕ)) (w : List A) : List (Ann A k) :=
  ((tuplesOf L w.length).flatMap (fun t => blockAt k w t ++ [Ann.sep])) ++ [Ann.eos]

section Block

variable {A : Type} {k : ℕ}

@[simp] lemma blockFrom_nil (t : List ℕ) (i : ℕ) : blockFrom (A := A) k t i [] = [] := rfl

@[simp] lemma blockFrom_cons (t : List ℕ) (i : ℕ) (a : A) (rest : List A) :
    blockFrom k t i (a :: rest) = Ann.letter a (annOf k t i) :: blockFrom k t (i + 1) rest := rfl

@[simp] lemma blockFrom_length (t : List ℕ) : ∀ (i : ℕ) (w : List A),
    (blockFrom k t i w).length = w.length := by
  intro i w
  induction w generalizing i with
  | nil => rfl
  | cons a w ih => simp [ih]

lemma blockFrom_append (t : List ℕ) : ∀ (i : ℕ) (u v : List A),
    blockFrom k t i (u ++ v) = blockFrom k t i u ++ blockFrom k t (i + u.length) v := by
  intro i u
  induction u generalizing i with
  | nil => intro v; simp
  | cons a u ih => intro v; simp [ih, Nat.add_right_comm, Nat.add_assoc]

lemma blockFrom_take (t : List ℕ) : ∀ (i m : ℕ) (w : List A),
    (blockFrom k t i w).take m = blockFrom k t i (w.take m) := by
  intro i m
  induction m generalizing i with
  | zero => intro w; simp
  | succ m ih =>
      intro w
      cases w with
      | nil => simp
      | cons a w => simp [ih]

lemma blockFrom_drop (t : List ℕ) : ∀ (i m : ℕ) (w : List A),
    (blockFrom k t i w).drop m = blockFrom k t (i + m) (w.drop m) := by
  intro i m
  induction m generalizing i with
  | zero => intro w; simp
  | succ m ih =>
      intro w
      cases w with
      | nil => simp
      | cons a w => simp [ih, Nat.add_comm, Nat.add_left_comm]

@[simp] lemma blockAt_nil (w : List A) : blockAt (A := A) k w [] = blockFrom k [] 0 w := rfl

lemma blockAt_length (w : List A) (t : List ℕ) : (blockAt k w t).length = w.length := by
  simp [blockAt]

/-- Extending a tuple by one more (innermost) position adds one more bit to every annotation. -/
lemma annOf_append_singleton {t : List ℕ} (ht : t.length = k) (p i : ℕ) :
    annOf (k + 1) (t ++ [p]) i = Fin.snoc (annOf k t i) (decide (i ≤ p)) := by
  funext j
  rcases Nat.lt_or_ge (j : ℕ) k with hj | hj
  · have hj' : (j : ℕ) < t.length := by omega
    rw [show j = (Fin.castSucc ⟨(j : ℕ), hj⟩) from Fin.ext (by simp), Fin.snoc_castSucc]
    simp only [annOf, Fin.val_castSucc]
    simp only [List.getD_append t [p] 0 (j : ℕ) hj']
  · have hj' : (j : ℕ) = k := by omega
    rw [show j = (Fin.last k) from Fin.ext (by simpa using hj')]
    rw [Fin.snoc_last]
    simp only [annOf, Fin.val_last]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [ht]

end Block

/-! ## The segments of a marked square

The copies of the marked square of `x ++ y ++ z` in which the underlining ends inside `y`. -/

section Seg

variable {α : Type}

/-- The part of the marked square of `x ++ y ++ z` contributed by the positions of `y`. -/
def msSeg (x y z : List α) : List (α ⊕ α) :=
  ((List.range y.length).map
    (fun i => (x ++ y.take (i + 1)).map Sum.inl ++ (y.drop (i + 1) ++ z).map Sum.inr)).flatten

@[simp] lemma msSeg_nil (x z : List α) : msSeg x [] z = [] := by simp [msSeg]

lemma markedSquare_eq_msSeg (u : List α) :
    markedSquare α u = msSeg ([] : List α) u ([] : List α) := by
  simp [markedSquare, msSeg]

lemma take_append_add (l₁ l₂ : List α) (m : ℕ) :
    (l₁ ++ l₂).take (l₁.length + m) = l₁ ++ l₂.take m := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simpa [Nat.succ_add] using ih

lemma drop_append_add (l₁ l₂ : List α) (m : ℕ) :
    (l₁ ++ l₂).drop (l₁.length + m) = l₂.drop m := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [Nat.succ_add, ih]

lemma msSeg_singleton (x : List α) (a : α) (z : List α) :
    msSeg x [a] z
      = (x ++ [a]).map (Sum.inl : α → α ⊕ α) ++ z.map (Sum.inr : α → α ⊕ α) := by
  simp [msSeg]

lemma msSeg_append (x y₁ y₂ z : List α) :
    msSeg x (y₁ ++ y₂) z = msSeg x y₁ (y₂ ++ z) ++ msSeg (x ++ y₁) y₂ z := by
  simp only [msSeg, List.length_append]
  rw [List.range_add]
  simp only [List.map_append, List.flatten_append, List.map_map]
  congr 1
  · congr 1
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i < y₁.length := by simpa using hi
    rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
    simp
  · congr 1
    refine List.map_congr_left ?_
    intro i _
    simp only [Function.comp_def]
    rw [show y₁.length + i + 1 = y₁.length + (i + 1) by omega,
      take_append_add, drop_append_add]
    simp

end Seg

end PolyEnum

end Lax194892Proofs.Transducers
