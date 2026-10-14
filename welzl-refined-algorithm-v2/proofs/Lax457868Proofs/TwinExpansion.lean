import Mathlib.Tactic

/-!
List lemmas for expanding a representative into vertices with the same
membership pattern.  The crossing count records consecutive pairs and has no
wraparound edge.
-/

namespace Lax457868Proofs.TwinExpansion

variable {α : Type*}

/-- The contribution of one consecutive pair to the crossing count. -/
def pairCrossing (p : α → Bool) (a b : α) : ℕ :=
  if p a = p b then 0 else 1

/-- Crossings from a fixed preceding element through the given list. -/
def crossingCountFrom (p : α → Bool) (previous : α) : List α → ℕ
  | [] => 0
  | next :: tail => pairCrossing p previous next + crossingCountFrom p next tail

/-- The number of changes of membership along consecutive entries, without a
wraparound pair. -/
def crossingCount (p : α → Bool) : List α → ℕ
  | [] => 0
  | first :: tail => crossingCountFrom p first tail

/-- Insert `new` immediately after the first occurrence of `representative`.
If the representative is absent, the list is unchanged. -/
def insertAfter [DecidableEq α] (representative new : α) : List α → List α
  | [] => []
  | first :: tail =>
      if first = representative then first :: new :: tail
      else first :: insertAfter representative new tail

/-- One recursive equation for insertion after the first matching entry. -/
lemma insertAfter_cons [DecidableEq α] (representative new first : α) (tail : List α) :
    insertAfter representative new (first :: tail) =
      if first = representative then first :: new :: tail
      else first :: insertAfter representative new tail := rfl

/-- Insertion leaves the first membership bit unchanged. -/
lemma crossingCountFrom_congr (p : α → Bool) (a b : α) (tail : List α)
    (h : p a = p b) :
    crossingCountFrom p a tail = crossingCountFrom p b tail := by
  induction tail generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp [crossingCountFrom, pairCrossing, h]

/-- Inserting a membership-equivalent copy after the representative preserves
the crossing count, even if the representative does not occur in the list. -/
lemma crossingCountFrom_insertAfter [DecidableEq α] (p : α → Bool)
    (previous representative new : α)
    (tail : List α) (h : p new = p representative) :
    crossingCountFrom p previous (insertAfter representative new tail) =
      crossingCountFrom p previous tail := by
  induction tail generalizing previous with
  | nil => rfl
  | cons first tail ih =>
      by_cases hfirst : first = representative
      · subst first
        rw [insertAfter_cons, if_pos rfl]
        simp only [crossingCountFrom]
        rw [show pairCrossing p representative new = 0 by simp [pairCrossing, h]]
        simp only [Nat.zero_add]
        rw [crossingCountFrom_congr (p := p) (a := new) (b := representative)
          (tail := tail) h]
      · simp only [insertAfter, if_neg hfirst, crossingCountFrom]
        rw [ih first]

/-- The crossing count is invariant under insertion of an equivalent copy. -/
lemma crossingCount_insertAfter [DecidableEq α] (p : α → Bool)
    (representative new : α)
    (l : List α) (h : p new = p representative) :
    crossingCount p (insertAfter representative new l) = crossingCount p l := by
  cases l with
  | nil => rfl
  | cons first tail =>
      by_cases hfirst : first = representative
      · subst first
        rw [insertAfter_cons, if_pos rfl]
        simp only [crossingCount]
        simp only [crossingCountFrom]
        rw [show pairCrossing p representative new = 0 by simp [pairCrossing, h]]
        simpa using crossingCountFrom_congr (p := p) (a := new) (b := representative)
          (tail := tail) h
      · simp [crossingCount, insertAfter, hfirst,
          crossingCountFrom_insertAfter p first representative new tail h]

/-- Inserting after a present representative permutes the entries into a list
with the inserted element at the front. -/
lemma insertAfter_perm [DecidableEq α] (representative new : α) {l : List α}
    (hrep : representative ∈ l) :
    (insertAfter representative new l).Perm (new :: l) := by
  induction l with
  | nil => simp at hrep
  | cons first tail ih =>
      by_cases hfirst : first = representative
      · subst first
        rw [insertAfter_cons, if_pos rfl]
        exact List.Perm.swap _ _ _
      · have htail : representative ∈ tail := by
          rcases List.mem_cons.mp hrep with heq | hmem
          · exact False.elim (hfirst heq.symm)
          · exact hmem
        rw [insertAfter_cons, if_neg hfirst]
        exact (ih htail).cons first |>.trans (List.Perm.swap _ _ _)

/-- Membership after insertion is exactly old membership or equality with the
inserted element. -/
lemma mem_insertAfter_iff [DecidableEq α] (representative new x : α) (l : List α)
    (hrep : representative ∈ l) :
    x ∈ insertAfter representative new l ↔ x ∈ l ∨ x = new := by
  rw [(insertAfter_perm representative new hrep).mem_iff]
  simp [or_comm]

/-- Inserting after an existing representative adds exactly one list entry. -/
lemma length_insertAfter [DecidableEq α] (representative new : α) (l : List α)
    (hrep : representative ∈ l) :
    (insertAfter representative new l).length = l.length + 1 := by
  have hperm := insertAfter_perm representative new hrep
  rw [hperm.length_eq]
  simp

/-- The underlying finite set after insertion is the old set with `new` added. -/
lemma toFinset_insertAfter [DecidableEq α] (representative new : α) (l : List α)
    (hrep : representative ∈ l) :
    (insertAfter representative new l).toFinset = insert new l.toFinset := by
  ext x
  rw [Finset.mem_insert, List.mem_toFinset, mem_insertAfter_iff representative new x l hrep]
  simp [or_comm]

/-- Inserting a fresh element after an existing representative preserves
duplicate-freeness. -/
lemma nodup_insertAfter [DecidableEq α] (representative new : α) (l : List α)
    (hnodup : l.Nodup) (hnew : new ∉ l) :
    (insertAfter representative new l).Nodup := by
  by_cases hrep : representative ∈ l
  · rw [(insertAfter_perm representative new hrep).nodup_iff]
    exact List.nodup_cons.mpr ⟨hnew, hnodup⟩
  · have hsame : insertAfter representative new l = l := by
      induction l with
      | nil => rfl
      | cons first tail ih =>
          by_cases hfirst : first = representative
          · subst first
            exact False.elim (hrep (List.mem_cons.mpr (Or.inl rfl)))
          · have hrep_tail : representative ∉ tail := by
              intro hmem
              exact hrep (List.mem_cons.mpr (Or.inr hmem))
            simp [insertAfter, hfirst, ih (List.nodup_cons.mp hnodup).2
              (by intro hmem; exact hnew (List.mem_cons.mpr (Or.inr hmem))) hrep_tail]
    simpa [hsame] using hnodup

/-- Reconstruct a list by inserting each removed vertex after its chosen
representative, in the order given by `newVertices`. -/
def insertAllTwins [DecidableEq α] (representativeOf : α → α)
    (order : List α) : List α → List α
  | [] => order
  | new :: rest =>
      insertAllTwins representativeOf
        (insertAfter (representativeOf new) new order) rest

/-- Reconstruction leaves the crossing count unchanged when every added
vertex agrees with its representative on `p`. -/
lemma crossingCount_insertAllTwins [DecidableEq α] (p : α → Bool)
    (representativeOf : α → α) (order additions : List α)
    (hAgree : ∀ new ∈ additions, p new = p (representativeOf new)) :
    crossingCount p (insertAllTwins representativeOf order additions) =
      crossingCount p order := by
  induction additions generalizing order with
  | nil => rfl
  | cons new rest ih =>
      rw [insertAllTwins, ih]
      · exact crossingCount_insertAfter p (representativeOf new) new order
          (hAgree new (List.mem_cons.mpr (Or.inl rfl)))
      · intro x hx
        exact hAgree x (List.mem_cons.mpr (Or.inr hx))

/-- The reconstructed list contains exactly the original entries and the
vertices in `additions`. -/
lemma toFinset_insertAllTwins [DecidableEq α] (representativeOf : α → α)
    (order additions : List α)
    (hRepresentative : ∀ new ∈ additions, representativeOf new ∈ order) :
    (insertAllTwins representativeOf order additions).toFinset =
      order.toFinset ∪ additions.toFinset := by
  induction additions generalizing order with
  | nil => simp [insertAllTwins]
  | cons new rest ih =>
      have hrep : representativeOf new ∈ order :=
        hRepresentative new (List.mem_cons.mpr (Or.inl rfl))
      have hRepresentativeRest : ∀ x ∈ rest,
          representativeOf x ∈ insertAfter (representativeOf new) new order := by
        intro x hx
        exact (mem_insertAfter_iff (representativeOf new) new
          (representativeOf x) order hrep).2
          (Or.inl (hRepresentative x (List.mem_cons.mpr (Or.inr hx))))
      rw [insertAllTwins, ih (insertAfter (representativeOf new) new order) hRepresentativeRest,
        toFinset_insertAfter (representativeOf new) new order hrep]
      simp [Finset.union_comm]

/-- With distinct new vertices disjoint from the original order, reconstruction
preserves duplicate-freeness. -/
lemma nodup_insertAllTwins [DecidableEq α] (representativeOf : α → α)
    (order additions : List α) (hOrder : order.Nodup)
    (hAdditions : additions.Nodup)
    (hFresh : ∀ new ∈ additions, new ∉ order)
    (hRepresentative : ∀ new ∈ additions, representativeOf new ∈ order) :
    (insertAllTwins representativeOf order additions).Nodup := by
  induction additions generalizing order with
  | nil => exact hOrder
  | cons new rest ih =>
      have hrep : representativeOf new ∈ order :=
        hRepresentative new (List.mem_cons.mpr (Or.inl rfl))
      have hnew : new ∉ order := hFresh new (List.mem_cons.mpr (Or.inl rfl))
      have hcurrent : (insertAfter (representativeOf new) new order).Nodup :=
        nodup_insertAfter (representativeOf new) new order hOrder hnew
      have hrestNodup : rest.Nodup := (List.nodup_cons.mp hAdditions).2
      have hRepresentativeRest : ∀ x ∈ rest,
          representativeOf x ∈ insertAfter (representativeOf new) new order := by
        intro x hx
        exact (mem_insertAfter_iff (representativeOf new) new
          (representativeOf x) order hrep).2
          (Or.inl (hRepresentative x (List.mem_cons.mpr (Or.inr hx))))
      have hFreshRest : ∀ x ∈ rest,
          x ∉ insertAfter (representativeOf new) new order := by
        intro x hx hmem
        have hold := (mem_insertAfter_iff (representativeOf new) new x order hrep).mp hmem
        rcases hold with hold | heq
        · exact hFresh x (List.mem_cons.mpr (Or.inr hx)) hold
        · have hnot : new ∉ rest := (List.nodup_cons.mp hAdditions).1
          exact hnot (heq ▸ hx)
      exact ih (insertAfter (representativeOf new) new order)
        hcurrent hrestNodup hFreshRest hRepresentativeRest

/-- The reconstructed list grows by one entry per removed vertex. -/
lemma length_insertAllTwins [DecidableEq α] (representativeOf : α → α)
    (order additions : List α)
    (hRepresentative : ∀ new ∈ additions, representativeOf new ∈ order) :
    (insertAllTwins representativeOf order additions).length =
      order.length + additions.length := by
  induction additions generalizing order with
  | nil => simp [insertAllTwins]
  | cons new rest ih =>
      have hrep : representativeOf new ∈ order :=
        hRepresentative new (List.mem_cons.mpr (Or.inl rfl))
      have hRepresentativeRest : ∀ x ∈ rest,
          representativeOf x ∈ insertAfter (representativeOf new) new order := by
        intro x hx
        exact (mem_insertAfter_iff (representativeOf new) new
          (representativeOf x) order hrep).2
          (Or.inl (hRepresentative x (List.mem_cons.mpr (Or.inr hx))))
      rw [insertAllTwins, ih (insertAfter (representativeOf new) new order) hRepresentativeRest,
        length_insertAfter (representativeOf new) new order hrep]
      simp only [List.length_cons]
      omega

end Lax457868Proofs.TwinExpansion
