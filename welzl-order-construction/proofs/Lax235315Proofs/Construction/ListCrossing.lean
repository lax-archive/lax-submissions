import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.SymmDiff

/-!
The list form of the "suspend twins" argument (paper, Lemma 2.1).

The RAM constructs an order as a list.  During reconstruction it inserts a
removed vertex immediately after its representative.  If the two vertices
have the same membership in the set under consideration, this insertion
does not alter the number of changes between consecutive list entries.
-/

namespace Lax235315Proofs.Construction.ListCrossing

noncomputable section

open scoped symmDiff

variable {α : Type*}

/-- Whether the pair `(a,b)` crosses the set `X`. -/
def crosses (X : Set α) (a b : α) : Bool :=
  by
    classical
    exact decide (a ∈ X ↔ b ∉ X)

/-- The number of consecutive pairs of `l` crossing `X`. -/
def crossingCount (X : Set α) (l : List α) : ℕ :=
  (l.zip l.tail).countP fun p => crosses X p.1 p.2

/-- The set of first endpoints of the crossing consecutive pairs of `l`. -/
def crossingEndpoints (X : Set α) (l : List α) : Set α :=
  {a | a ∈ ((l.zip l.tail).filter
    (fun p => crosses X p.1 p.2)).map Prod.fst}

/-- Whether a list entry belongs to `D`. -/
def contains (D : Set α) (a : α) : Bool := by
  classical
  exact decide (a ∈ D)

/-- The number of entries of `l` belonging to `D`. -/
def memberCount (D : Set α) (l : List α) : ℕ :=
  l.countP (contains D)

@[simp] theorem crossingCount_nil (X : Set α) : crossingCount X [] = 0 := rfl

@[simp] theorem crossingCount_singleton (X : Set α) (a : α) :
    crossingCount X [a] = 0 := rfl

theorem crossingCount_cons_cons (X : Set α) (a b : α) (l : List α) :
    crossingCount X (a :: b :: l) =
      crossingCount X (b :: l) + if crosses X a b = true then 1 else 0 := by
  simp [crossingCount, List.countP_cons]

/-- A crossing count is at most the length of its list. -/
theorem crossingCount_le_length (X : Set α) (l : List α) :
    crossingCount X l ≤ l.length := by
  unfold crossingCount
  exact List.countP_le_length.trans <| by
    simp [List.length_zip]

/-- Sets agreeing on every listed element have the same list crossing
count. -/
theorem crossingCount_congr_on {X Y : Set α} {l : List α}
    (h : ∀ a ∈ l, (a ∈ X) ↔ (a ∈ Y)) :
    crossingCount X l = crossingCount Y l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases l with
      | nil => rfl
      | cons b l =>
          rw [crossingCount_cons_cons, crossingCount_cons_cons]
          have hab : crosses X a b = crosses Y a b := by
            classical
            have ha := h a (by simp)
            have hb := h b (by simp)
            by_cases hXa : a ∈ X <;> by_cases hXb : b ∈ X <;>
              by_cases hYa : a ∈ Y <;> by_cases hYb : b ∈ Y <;>
                simp_all [crosses]
          rw [hab]
          have htail : crossingCount X (b :: l) = crossingCount Y (b :: l) :=
            ih (fun z hz => h z (by simp [hz]))
          rw [htail]

theorem crossingCount_cons_of_head {X : Set α} {a b : α} {l : List α}
    (h : l.head? = some b) :
    crossingCount X (a :: l) =
      crossingCount X l + if crosses X a b = true then 1 else 0 := by
  cases l with
  | nil => simp at h
  | cons d l =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst d
      exact crossingCount_cons_cons X a b l

theorem crosses_eq_false_of_iff {X : Set α} {a b : α}
    (h : (a ∈ X) ↔ (b ∈ X)) :
    crosses X a b = false := by
  classical
  by_cases ha : a ∈ X <;> by_cases hb : b ∈ X <;> simp_all [crosses]

theorem crosses_congr_left {X : Set α} {a a' b : α}
    (h : (a ∈ X) ↔ (a' ∈ X)) :
    crosses X a b = crosses X a' b := by
  classical
  by_cases ha : a ∈ X <;> by_cases ha' : a' ∈ X <;>
    by_cases hb : b ∈ X <;> simp_all [crosses]

theorem edge_crossing_le (X Y : Set α) (a b : α) :
    (if crosses X a b = true then 1 else 0) ≤
      (if crosses Y a b = true then 1 else 0) +
        (if contains (X ∆ Y) a = true then 1 else 0) +
        (if contains (X ∆ Y) b = true then 1 else 0) := by
  classical
  by_cases hXa : a ∈ X <;> by_cases hXb : b ∈ X <;>
    by_cases hYa : a ∈ Y <;> by_cases hYb : b ∈ Y <;>
      simp_all [crosses, contains, Set.mem_symmDiff]

theorem countPairCrossings_le (X Y : Set α) (ps : List (α × α)) :
    ps.countP (fun p => crosses X p.1 p.2) ≤
      ps.countP (fun p => crosses Y p.1 p.2) +
        (ps.map Prod.fst).countP (contains (X ∆ Y)) +
        (ps.map Prod.snd).countP (contains (X ∆ Y)) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.countP_cons, List.map_cons]
      have hp := edge_crossing_le X Y p.1 p.2
      omega

theorem map_fst_zip_tail_sublist (l : List α) :
    List.Sublist ((l.zip l.tail).map Prod.fst) l := by
  cases l with
  | nil => simp
  | cons a l =>
      cases l with
      | nil => simp
      | cons b l =>
          simp only [List.tail_cons, List.zip_cons_cons, List.map_cons]
          exact List.Sublist.cons_cons a (map_fst_zip_tail_sublist (b :: l))
termination_by l.length
decreasing_by simp_wf

theorem map_snd_zip_tail (l : List α) :
    (l.zip l.tail).map Prod.snd = l.tail := by
  apply List.map_snd_zip
  simp

/-- Consecutive pairs in a duplicate-free list are exactly the pairs whose
second entry has index one greater than the first entry. -/
theorem mem_zip_tail_iff_idxOf_succ [DecidableEq α] {l : List α}
    (hl : l.Nodup) (u v : α) :
    (u, v) ∈ l.zip l.tail ↔
      u ∈ l ∧ v ∈ l ∧ l.idxOf v = l.idxOf u + 1 := by
  constructor
  · intro huv
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp huv
    have hifst : i.val < l.length := by
      have hi' := i.isLt
      simp only [List.length_zip] at hi'
      omega
    have hisnd : i.val < l.tail.length := by
      have hi' := i.isLt
      simp only [List.length_zip] at hi'
      omega
    have hinext : i.val + 1 < l.length := by
      simp only [List.length_tail] at hisnd
      omega
    rw [List.get_eq_getElem, List.getElem_zip, List.getElem_tail] at hi
    have hpair :
        (l.get ⟨i.val, hifst⟩, l.get ⟨i.val + 1, hinext⟩) = (u, v) := hi
    have hu : l.get ⟨i.val, hifst⟩ = u := congrArg Prod.fst hpair
    have hv : l.get ⟨i.val + 1, hinext⟩ = v := congrArg Prod.snd hpair
    refine ⟨?_, ?_, ?_⟩
    · rw [← hu]
      exact List.get_mem l ⟨i.val, hifst⟩
    · rw [← hv]
      exact List.get_mem l ⟨i.val + 1, hinext⟩
    · rw [← hu, ← hv, List.get_idxOf hl, List.get_idxOf hl]
  · rintro ⟨hu_mem, hv_mem, hidx⟩
    have hu_bound : l.idxOf u < l.length :=
      List.idxOf_lt_length_iff.mpr hu_mem
    have hv_bound : l.idxOf v < l.length :=
      List.idxOf_lt_length_iff.mpr hv_mem
    have hu_get : l.get ⟨l.idxOf u, hu_bound⟩ = u := List.idxOf_get hu_bound
    have hv_get : l.get ⟨l.idxOf u + 1, by omega⟩ = v := by
      have := List.idxOf_get hv_bound
      simpa only [hidx] using this
    have htail : l.idxOf u < l.tail.length := by
      simp only [List.length_tail]
      omega
    have hzip : l.idxOf u < (l.zip l.tail).length := by
      simp only [List.length_zip]
      omega
    apply List.mem_iff_get.mpr
    refine ⟨⟨l.idxOf u, hzip⟩, ?_⟩
    rw [List.get_eq_getElem, List.getElem_zip]
    rw [List.getElem_tail]
    exact Prod.ext hu_get hv_get

/-- For a duplicate-free list, counting crossing pairs is the same as
counting their first endpoints. -/
theorem ncard_crossingEndpoints [DecidableEq α] [Finite α]
    (X : Set α) {l : List α} (hl : l.Nodup) :
    (crossingEndpoints X l).ncard = crossingCount X l := by
  classical
  let ps := (l.zip l.tail).filter (fun p => crosses X p.1 p.2)
  have hsub : List.Sublist (ps.map Prod.fst) l :=
    ((List.filter_sublist.map Prod.fst).trans (map_fst_zip_tail_sublist l))
  have hnodup : (ps.map Prod.fst).Nodup := hsub.nodup hl
  unfold crossingEndpoints crossingCount
  rw [List.countP_eq_length_filter]
  change ({a | a ∈ ps.map Prod.fst} : Set α).ncard = ps.length
  calc
    ({a | a ∈ ps.map Prod.fst} : Set α).ncard =
        (ps.map Prod.fst).toFinset.card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext a
      simp
    _ = (ps.map Prod.fst).length := List.toFinset_card_of_nodup hnodup
    _ = ps.length := by simp

theorem mem_crossingEndpoints_iff [DecidableEq α] (X : Set α)
    (l : List α) (u : α) :
    u ∈ crossingEndpoints X l ↔
      ∃ v, (u, v) ∈ l.zip l.tail ∧ (u ∈ X ↔ v ∉ X) := by
  simp [crossingEndpoints, crosses]

/-- Changing membership on `D` changes at most two incident list edges per
occurrence of a member of `D`. -/
theorem crossingCount_le_add_two_mul_memberCount (X Y : Set α) (l : List α) :
    crossingCount X l ≤
      crossingCount Y l + 2 * memberCount (X ∆ Y) l := by
  unfold crossingCount memberCount
  let ps := l.zip l.tail
  have hpair := countPairCrossings_le X Y ps
  have hfst :
      (ps.map Prod.fst).countP (contains (X ∆ Y)) ≤
        l.countP (contains (X ∆ Y)) :=
    (map_fst_zip_tail_sublist l).countP_le
  have hsnd :
      (ps.map Prod.snd).countP (contains (X ∆ Y)) ≤
        l.countP (contains (X ∆ Y)) := by
    rw [map_snd_zip_tail]
    exact (List.tail_sublist l).countP_le
  dsimp only [ps] at hpair hfst hsnd
  omega

/-- On a duplicate-free list, the number of entries in a set is bounded by
the cardinality of that set. -/
theorem memberCount_le_ncard [DecidableEq α] [Finite α]
    (D : Set α) {l : List α} (hl : l.Nodup) :
    memberCount D l ≤ D.ncard := by
  classical
  unfold memberCount
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (hl.filter (contains D))]
  have hsub :
      ((l.filter (contains D)).toFinset : Set α) ⊆ D := by
    intro a ha
    simp [contains] at ha
    exact ha.2
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub

/-- List form of the paper's `2k` near-twin estimate. -/
theorem crossingCount_le_add_two_mul_symmDiff [DecidableEq α] [Finite α]
    (X Y : Set α) {l : List α} (hl : l.Nodup) :
    crossingCount X l ≤ crossingCount Y l + 2 * (X ∆ Y).ncard := by
  exact (crossingCount_le_add_two_mul_memberCount X Y l).trans <| by
    have h := memberCount_le_ncard (X ∆ Y) hl
    omega

/-- Insert `x` immediately after the first occurrence of `a`; if `a` is
absent, leave the list unchanged. -/
def insertAfter [DecidableEq α] (a x : α) : List α → List α
  | [] => []
  | b :: l => if b = a then b :: x :: l else b :: insertAfter a x l

@[simp] theorem insertAfter_nil [DecidableEq α] (a x : α) :
    insertAfter a x [] = [] := rfl

theorem insertAfter_cons [DecidableEq α] (a x b : α) (l : List α) :
    insertAfter a x (b :: l) =
      if b = a then b :: x :: l else b :: insertAfter a x l := rfl

theorem insertAfter_head [DecidableEq α] {a x b : α} {l : List α} :
    (insertAfter a x (b :: l)).head? = some b := by
  rw [insertAfter_cons]
  split <;> simp

/-- Inserting after a present representative adds exactly the new element,
up to permutation. -/
theorem insertAfter_perm [DecidableEq α] {a x : α} {l : List α}
    (ha : a ∈ l) :
    (insertAfter a x l).Perm (x :: l) := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      by_cases hba : b = a
      · subst b
        rw [insertAfter_cons, if_pos rfl]
        exact List.Perm.swap _ _ _
      · have hab : a ≠ b := fun h => hba h.symm
        have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left hab
        rw [insertAfter_cons, if_neg hba]
        exact (ih hal).cons b |>.trans (List.Perm.swap _ _ _)

/-- A twin insertion does not change the list crossing count. -/
theorem crossingCount_insertAfter [DecidableEq α] {X : Set α} {a x : α}
    {l : List α} (ha : a ∈ l) (hax : (a ∈ X) ↔ (x ∈ X)) :
    crossingCount X (insertAfter a x l) = crossingCount X l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      by_cases hba : b = a
      · subst b
        cases l with
        | nil =>
            rw [insertAfter_cons, if_pos rfl, crossingCount_cons_cons]
            simp [crosses_eq_false_of_iff hax]
        | cons d l =>
            rw [insertAfter_cons, if_pos rfl]
            rw [crossingCount_cons_cons, crossingCount_cons_cons,
              crossingCount_cons_cons]
            rw [crosses_eq_false_of_iff hax,
              crosses_congr_left hax.symm]
            simp
      · have hab : a ≠ b := fun h => hba h.symm
        have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left hab
        cases l with
        | nil => simp at hal
        | cons d l =>
            rw [insertAfter_cons, if_neg hba]
            rw [crossingCount_cons_of_head (insertAfter_head (a := a) (x := x))]
            rw [ih hal]
            rw [crossingCount_cons_cons]

/-- Twin insertion preserves duplicate-freeness when the inserted vertex is
new. -/
theorem nodup_insertAfter [DecidableEq α] {a x : α} {l : List α}
    (hl : l.Nodup) (ha : a ∈ l) (hx : x ∉ l) :
    (insertAfter a x l).Nodup := by
  rw [(insertAfter_perm ha).nodup_iff]
  simpa using List.nodup_cons.mpr ⟨hx, hl⟩

/-- Twin insertion preserves all old members and adds the inserted vertex. -/
theorem mem_insertAfter_iff [DecidableEq α] {a x y : α} {l : List α}
    (ha : a ∈ l) :
    y ∈ insertAfter a x l ↔ y = x ∨ y ∈ l := by
  rw [(insertAfter_perm ha).mem_iff]
  simp

end


end Lax235315Proofs.Construction.ListCrossing
