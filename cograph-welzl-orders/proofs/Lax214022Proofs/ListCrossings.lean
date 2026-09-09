import Lax195003.WelzlOrders
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.FinCases

/-!
# Changes along finite lists

Welzl crossings are changes in a Boolean membership word.  These elementary
list lemmas isolate the bookkeeping used by both bounds.
-/

namespace Lax214022Proofs.ListCrossings

noncomputable section

/-- The number of changes between consecutive Boolean entries. -/
def changes : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: xs => (if a = b then 0 else 1) + changes (b :: xs)
termination_by xs => xs.length

@[simp] theorem changes_nil : changes [] = 0 := by rw [changes]

@[simp] theorem changes_singleton (a : Bool) : changes [a] = 0 := by rw [changes]

@[simp] theorem changes_cons_cons (a b : Bool) (xs : List Bool) :
    changes (a :: b :: xs) = (if a = b then 0 else 1) + changes (b :: xs) := by
  rw [changes]

theorem changes_append_le (xs ys : List Bool) :
    changes (xs ++ ys) ≤ changes xs + changes ys + 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => simp
          | cons b ys =>
              simp only [List.cons_append, List.nil_append, changes_singleton,
                changes_cons_cons]
              split <;> omega
      | cons b xs =>
          simp only [List.cons_append, changes_cons_cons]
          have h : changes (b :: (xs ++ ys)) ≤
              changes (b :: xs) + changes ys + 1 := by
            simpa only [List.cons_append] using ih
          omega

theorem changes_replicate (n : ℕ) (b : Bool) :
    changes (List.replicate n b) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simp
      | succ n =>
          simpa [List.replicate_succ, changes_cons_cons] using ih

/-- A nonempty constant prefix has the same effect as one copy of its
value. -/
theorem changes_replicate_succ_append (n : ℕ) (b : Bool) (xs : List Bool) :
    changes (List.replicate (n + 1) b ++ xs) = changes (b :: xs) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ,
        List.cons_append, changes_cons_cons]
      simp
      simpa only [List.replicate_succ, List.cons_append] using ih

/-- A nonempty constant suffix has the same effect as one copy of its
value. -/
theorem changes_append_replicate_succ (xs : List Bool) (n : ℕ) (b : Bool) :
    changes (xs ++ List.replicate (n + 1) b) = changes (xs ++ [b]) := by
  induction xs with
  | nil => simp [changes_replicate]
  | cons a xs ih =>
      cases xs with
      | nil =>
          rw [List.singleton_append]
          rw [show List.replicate (n + 1) b = b :: List.replicate n b by
            simp [List.replicate_succ]]
          have hc : changes (b :: List.replicate n b) = 0 := by
            simpa [List.replicate_succ] using changes_replicate (n + 1) b
          simp [changes_cons_cons, hc]
      | cons c xs =>
          simp only [List.cons_append, changes_cons_cons]
          exact congrArg ((if a = c then 0 else 1) + ·) ih

/-- Inserting entries cannot reduce the number of Boolean changes. -/
theorem changes_insert_le (xs : List Bool) (b : Bool) (ys : List Bool) :
    changes (xs ++ ys) ≤ changes (xs ++ b :: ys) := by
  induction xs with
  | nil =>
      cases ys with
      | nil => simp
      | cons c ys =>
          simp only [List.nil_append, changes_cons_cons]
          omega
  | cons a xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => simp
          | cons c ys =>
              simp only [List.cons_append]
              fin_cases a <;> fin_cases b <;> fin_cases c <;> simp <;> omega
      | cons c xs =>
          simp only [List.cons_append, changes_cons_cons]
          exact Nat.add_le_add_left ih _

/-- Change count is monotone under taking a subsequence. -/
theorem changes_sublist_le {xs ys : List Bool} (h : xs.Sublist ys) :
    changes xs ≤ changes ys := by
  have aux : ∀ pre : List Bool, changes (pre ++ xs) ≤ changes (pre ++ ys) := by
    intro pre
    induction h generalizing pre with
    | slnil => simp
    | cons a h ih =>
        exact (ih pre).trans (changes_insert_le pre a _)
    | cons_cons a h ih =>
        simpa [List.append_assoc] using ih (pre ++ [a])
  simpa using aux []

theorem changes_append_cons_cons (xs : List Bool) (a b : Bool)
    (ys : List Bool) :
    changes (xs ++ a :: b :: ys) =
      changes (xs ++ [a]) + (if a = b then 0 else 1) + changes (b :: ys) := by
  induction xs with
  | nil => simp [changes_cons_cons]
  | cons c xs ih =>
      cases xs with
      | nil => simp [changes_cons_cons, Nat.add_assoc]
      | cons d xs =>
          simp only [List.cons_append, changes_cons_cons]
          rw [show changes (d :: (xs ++ a :: b :: ys)) =
              changes (d :: (xs ++ [a])) +
                (if a = b then 0 else 1) + changes (b :: ys) by
            simpa only [List.cons_append] using ih]
          omega

/-- An isolated `true` entry contributes one change beyond any subsequence
obtained from the material on its two sides. -/
theorem changes_isolated_true_gain {A B C D : List Bool}
    (hC : C.Sublist A) (hD : D.Sublist B)
    (hA : A = [] ∨ ∃ A', A = A' ++ [false])
    (hB : B = [] ∨ ∃ B', B = false :: B')
    (hne : C ++ D ≠ []) :
    changes (C ++ D) + 1 ≤ changes (A ++ true :: B) := by
  have hCle := changes_sublist_le hC
  have hDle := changes_sublist_le hD
  rcases hA with rfl | ⟨A, rfl⟩
  · have hCnil : C = [] := List.eq_nil_of_sublist_nil hC
    subst C
    rcases hB with rfl | ⟨B, rfl⟩
    · have hDnil : D = [] := List.eq_nil_of_sublist_nil hD
      simp [hDnil] at hne
    · simp only [List.nil_append, changes_cons_cons,
        Bool.true_eq_false, if_false]
      omega
  · rcases hB with rfl | ⟨B, rfl⟩
    · have hDnil : D = [] := List.eq_nil_of_sublist_nil hD
      subst D
      rw [List.append_nil]
      rw [List.append_assoc]
      change changes C + 1 ≤ changes (A ++ false :: true :: [])
      rw [changes_append_cons_cons A false true []]
      simp only [Bool.false_eq_true, if_false, changes_singleton, Nat.add_zero]
      omega
    · have hCD := changes_append_le C D
      rw [List.append_assoc]
      change changes (C ++ D) + 1 ≤
        changes (A ++ false :: true :: false :: B)
      rw [changes_append_cons_cons A false true (false :: B)]
      simp only [Bool.false_eq_true, Bool.true_eq_false, if_false,
        changes_cons_cons]
      omega

/-- The number of membership changes of a predicate along a list. -/
def crossingCountInList {α : Type} (p : α → Prop) [DecidablePred p]
    (xs : List α) : ℕ :=
  changes (xs.map fun x => decide (p x))

theorem crossingCountInList_append_le {α : Type} (p : α → Prop)
    [DecidablePred p] (xs ys : List α) :
    crossingCountInList p (xs ++ ys) ≤
      crossingCountInList p xs + crossingCountInList p ys + 1 := by
  simpa [crossingCountInList] using
    changes_append_le (xs.map fun x => decide (p x))
      (ys.map fun x => decide (p x))

theorem crossingCountInList_const {α : Type} (p : α → Prop)
    [DecidablePred p] (xs : List α) (b : Bool)
    (h : ∀ x ∈ xs, decide (p x) = b) :
    crossingCountInList p xs = 0 := by
  have hmap : xs.map (fun x => decide (p x)) = List.replicate xs.length b := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp only [List.mem_cons, forall_eq_or_imp] at h
        simp [h.1, ih h.2, List.replicate_succ]
  rw [crossingCountInList, hmap, changes_replicate]

/-- Four consecutive pieces contribute at most three new boundaries beyond
the sum of their internal changes. -/
theorem crossingCountInList_four_le_sum {α : Type} (p : α → Prop)
    [DecidablePred p] (a b c d : List α) :
    crossingCountInList p (a ++ b ++ c ++ d) ≤
      crossingCountInList p a + crossingCountInList p b +
        crossingCountInList p c + crossingCountInList p d + 3 := by
  have hab := crossingCountInList_append_le p a b
  have habc := crossingCountInList_append_le p (a ++ b) c
  have habcd := crossingCountInList_append_le p (a ++ b ++ c) d
  omega

/-- The same change count written as a sum over positions. -/
def boundarySum {n : ℕ} (f : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if h : i.val + 1 < n then
    if f i = f ⟨i.val + 1, h⟩ then 0 else 1
  else 0

theorem changes_ofFn (n : ℕ) (f : Fin n → Bool) :
    changes (List.ofFn f) = boundarySum f := by
  induction n with
  | zero => simp [boundarySum]
  | succ n ih =>
      cases n with
      | zero => simp [boundarySum, List.ofFn_succ]
      | succ n =>
          rw [List.ofFn_succ]
          rw [List.ofFn_succ (f := fun i : Fin (n + 1) => f i.succ)]
          rw [changes_cons_cons, boundarySum,
            Fin.sum_univ_succ]
          simp only [Fin.val_zero, Nat.zero_add, Nat.add_lt_add_iff_right,
            Fin.val_succ]
          have htail := ih (fun i : Fin (n + 1) => f i.succ)
          rw [List.ofFn_succ] at htail
          rw [htail]
          unfold boundarySum
          simp only [Nat.add_lt_add_iff_right]
          rfl

theorem successor_witness_iff {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) [DecidablePred fun u => u ∈ X] (u : Fin n) :
    (∃ v : Fin n, (π v).val = (π u).val + 1 ∧
        (u ∈ X ↔ v ∉ X)) ↔
      ∃ h : (π u).val + 1 < n,
        decide (u ∈ X) ≠
          decide (π.symm ⟨(π u).val + 1, h⟩ ∈ X) := by
  constructor
  · rintro ⟨v, hvpos, hvX⟩
    have hlt : (π u).val + 1 < n := hvpos ▸ (π v).isLt
    refine ⟨hlt, ?_⟩
    have hv : v = π.symm ⟨(π u).val + 1, hlt⟩ := by
      apply π.injective
      apply Fin.ext
      simpa using hvpos
    subst v
    by_cases hu : u ∈ X <;> by_cases hv : π.symm ⟨(π u).val + 1, hlt⟩ ∈ X <;>
      simp_all
  · rintro ⟨hlt, hne⟩
    refine ⟨π.symm ⟨(π u).val + 1, hlt⟩, ?_, ?_⟩
    · simp
    · by_cases hu : u ∈ X <;>
        by_cases hv : π.symm ⟨(π u).val + 1, hlt⟩ ∈ X <;>
        simp_all

theorem crossingCount_eq_sum {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) [DecidablePred fun u => u ∈ X] :
    Lax195003.WelzlOrders.crossingCount π X =
      ∑ u : Fin n, if h : (π u).val + 1 < n then
        if decide (u ∈ X) =
            decide (π.symm ⟨(π u).val + 1, h⟩ ∈ X) then 0 else 1
      else 0 := by
  classical
  unfold Lax195003.WelzlOrders.crossingCount
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
  apply Fintype.sum_congr
  intro u
  by_cases hw : ∃ v : Fin n, (π v).val = (π u).val + 1 ∧
      (u ∈ X ↔ v ∉ X)
  · obtain ⟨hlt, hne⟩ := (successor_witness_iff π X u).mp hw
    simp [hw, hlt, hne]
  · simp only [hw, if_false]
    by_cases hlt : (π u).val + 1 < n
    · have heq : decide (u ∈ X) =
          decide (π.symm ⟨(π u).val + 1, hlt⟩ ∈ X) := by
        by_contra hne
        exact hw ((successor_witness_iff π X u).mpr ⟨hlt, hne⟩)
      simp [hlt, heq]
    · simp [hlt]

theorem crossingCount_eq_crossingCountInList {n : ℕ}
    (π : Equiv.Perm (Fin n)) (X : Set (Fin n))
    [DecidablePred fun u => u ∈ X] :
    Lax195003.WelzlOrders.crossingCount π X =
      crossingCountInList (fun u => u ∈ X)
        (List.ofFn fun i : Fin n => π.symm i) := by
  rw [crossingCount_eq_sum, crossingCountInList, List.map_ofFn,
    changes_ofFn, boundarySum]
  apply Fintype.sum_equiv π
  intro u
  simp

end

end Lax214022Proofs.ListCrossings
