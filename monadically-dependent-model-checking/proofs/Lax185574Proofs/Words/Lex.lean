import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

/-!
The lexicographic order on words, as the programs compare them, and the
sorted list of the distinct words of a list, as the programs produce it.

Two words are compared entry by entry from the front. The first entry
where they differ decides, and a proper prefix is smaller. A program
reads the comparison off the first position `k` where the words differ
or one of them ends, and `cmpCode` names its result.

The sorted list of the distinct words of `ws` is `sortedDistinct ws`.
Its entry `t` is the smallest word of `ws` above entry `t - 1`, which is
how a program produces it by repeated selection.
-/

namespace Lax185574Proofs.Words

/-- The result of comparing two words: `0` if the first is smaller, `1`
if they are equal and `2` if the first is larger. -/
def cmpCode (u v : List ℕ) : ℕ := if u < v then 0 else if u = v then 1 else 2

theorem append_lt_append_left (p : List ℕ) {u v : List ℕ} : p ++ u < p ++ v ↔ u < v := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.cons_append]
    rw [List.cons_lt_cons_iff]
    simp [ih]

/-- A word splits at a position below its length. -/
theorem eq_take_append_cons {u : List ℕ} {k : ℕ} (hk : k < u.length) :
    u = u.take k ++ u[k] :: u.drop (k + 1) := by
  conv_lhs => rw [← List.take_append_drop k u]
  rw [List.drop_eq_getElem_cons hk]

/-- The words agree before `k` and differ at `k`. -/
theorem cmpCode_of_lt_at {u v : List ℕ} {k : ℕ} (hu : k < u.length) (hv : k < v.length)
    (hpre : u.take k = v.take k) (hlt : u[k] < v[k]) : cmpCode u v = 0 := by
  have : u < v := by
    rw [eq_take_append_cons hu, eq_take_append_cons hv, hpre, append_lt_append_left,
      List.cons_lt_cons_iff]
    exact Or.inl hlt
  simp [cmpCode, this]

theorem cmpCode_of_gt_at {u v : List ℕ} {k : ℕ} (hu : k < u.length) (hv : k < v.length)
    (hpre : u.take k = v.take k) (hlt : v[k] < u[k]) : cmpCode u v = 2 := by
  have : v < u := by
    rw [eq_take_append_cons hu, eq_take_append_cons hv, hpre, append_lt_append_left,
      List.cons_lt_cons_iff]
    exact Or.inl hlt
  simp [cmpCode, not_lt_of_gt this, ne_of_gt this]

/-- The first word ends at `k`, the second goes on. -/
theorem cmpCode_of_end_left {u v : List ℕ} {k : ℕ} (hu : u.length ≤ k) (hv : k < v.length)
    (hpre : u.take k = v.take k) : cmpCode u v = 0 := by
  have : u < v := by
    have hu' : u = v.take k := by rw [← hpre, List.take_of_length_le hu]
    rw [hu', eq_take_append_cons hv]
    conv_lhs => rw [← List.append_nil (List.take k (List.take k v ++ _))]
    rw [List.take_append_of_le_length (by simp; omega), List.take_take, min_self,
      append_lt_append_left]
    exact List.nil_lt_cons _ _
  simp [cmpCode, this]

/-- The second word ends at `k`, the first goes on. -/
theorem cmpCode_of_end_right {u v : List ℕ} {k : ℕ} (hu : k < u.length) (hv : v.length ≤ k)
    (hpre : u.take k = v.take k) : cmpCode u v = 2 := by
  have : v < u := by
    have hv' : v = u.take k := by rw [hpre, List.take_of_length_le hv]
    rw [hv', eq_take_append_cons hu]
    conv_lhs => rw [← List.append_nil (List.take k (List.take k u ++ _))]
    rw [List.take_append_of_le_length (by simp; omega), List.take_take, min_self,
      append_lt_append_left]
    exact List.nil_lt_cons _ _
  simp [cmpCode, not_lt_of_gt this, ne_of_gt this]

/-- Both words end at `k`. -/
theorem cmpCode_of_end_both {u v : List ℕ} {k : ℕ} (hu : u.length ≤ k) (hv : v.length ≤ k)
    (hpre : u.take k = v.take k) : cmpCode u v = 1 := by
  have : u = v := by rw [← List.take_of_length_le hu, ← List.take_of_length_le hv, hpre]
  simp [cmpCode, this]

theorem cmpCode_eq_zero {u v : List ℕ} : cmpCode u v = 0 ↔ u < v := by
  unfold cmpCode; split_ifs <;> simp_all

theorem cmpCode_eq_two {u v : List ℕ} : cmpCode u v = 2 ↔ v < u := by
  unfold cmpCode
  split_ifs with h1 h2
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd (lt_trans h1 h) (lt_irrefl _)
  · simp [h2]
  · simp only [true_iff]
    rcases lt_trichotomy u v with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h

theorem cmpCode_le_two (u v : List ℕ) : cmpCode u v ≤ 2 := by
  unfold cmpCode; split_ifs <;> omega

/-! ### The sorted list of the distinct words -/

/-- The distinct words of `ws`, sorted. -/
def sortedDistinct (ws : List (List ℕ)) : List (List ℕ) := ws.toFinset.sort (· ≤ ·)

theorem sortedDistinct_sorted (ws : List (List ℕ)) :
    (sortedDistinct ws).Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise

theorem mem_sortedDistinct {ws : List (List ℕ)} {u : List ℕ} :
    u ∈ sortedDistinct ws ↔ u ∈ ws := by
  simp [sortedDistinct]

theorem length_sortedDistinct_le (ws : List (List ℕ)) :
    (sortedDistinct ws).length ≤ ws.length := by
  simp only [sortedDistinct, Finset.length_sort]
  exact List.toFinset_card_le ws

/-- In a strictly increasing list, the order of entries is the order of
positions. -/
theorem getElem_lt_getElem_iff {L : List (List ℕ)} (hL : L.Pairwise (· < ·)) {i j : ℕ}
    (hi : i < L.length) (hj : j < L.length) : L[i] < L[j] ↔ i < j := by
  constructor
  · intro h
    by_contra hji
    rcases (not_lt.mp hji).lt_or_eq with hji | rfl
    · exact absurd h (not_lt_of_gt (List.pairwise_iff_getElem.mp hL j i hj hi hji))
    · exact lt_irrefl _ h
  · intro h; exact List.pairwise_iff_getElem.mp hL i j hi hj h

/-- A candidate of round `t` of the selection: a word of `ws` above the
word selected in round `t - 1`, or any word of `ws` in round `0`. -/
def IsCand (ws : List (List ℕ)) (t : ℕ) (u : List ℕ) : Prop :=
  u ∈ ws ∧ ∀ h : 0 < t, ∀ h' : t - 1 < (sortedDistinct ws).length,
    (sortedDistinct ws)[t - 1] < u

/-- Round `t` of the selection finds a candidate exactly when `t` is a
position of the sorted list, and entry `t` is then the smallest
candidate. -/
theorem cand_exists_iff {ws : List (List ℕ)} {t : ℕ} (ht : t ≤ (sortedDistinct ws).length) :
    (∃ u, IsCand ws t u) ↔ t < (sortedDistinct ws).length := by
  have hL := sortedDistinct_sorted ws
  constructor
  · rintro ⟨u, hu, hgt⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (mem_sortedDistinct.mpr hu)
    by_contra hlt
    have htL : t = (sortedDistinct ws).length := by omega
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · omega
    · have := hgt h0 (by omega)
      rw [getElem_lt_getElem_iff hL (by omega) hj] at this
      omega
  · intro hlt
    refine ⟨(sortedDistinct ws)[t], mem_sortedDistinct.mp (List.getElem_mem _), fun h0 h1 => ?_⟩
    rw [getElem_lt_getElem_iff hL h1 hlt]
    omega

theorem cand_getElem {ws : List (List ℕ)} {t : ℕ} (ht : t < (sortedDistinct ws).length) :
    IsCand ws t (sortedDistinct ws)[t] := by
  refine ⟨mem_sortedDistinct.mp (List.getElem_mem _), fun h0 h1 => ?_⟩
  rw [getElem_lt_getElem_iff (sortedDistinct_sorted ws) h1 ht]
  omega

theorem getElem_le_cand {ws : List (List ℕ)} {t : ℕ} (ht : t < (sortedDistinct ws).length)
    {u : List ℕ} (hu : IsCand ws t u) : (sortedDistinct ws)[t] ≤ u := by
  have hL := sortedDistinct_sorted ws
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (mem_sortedDistinct.mpr hu.1)
  by_contra hlt
  rw [not_le, getElem_lt_getElem_iff hL hj ht] at hlt
  have h0 : 0 < t := by omega
  have := hu.2 h0 (by omega)
  rw [getElem_lt_getElem_iff hL (by omega) hj] at this
  omega

/-- The smallest candidate of round `t` is entry `t` of the sorted
list. -/
theorem eq_getElem_of_min_cand {ws : List (List ℕ)} {t : ℕ} (ht : t < (sortedDistinct ws).length)
    {u : List ℕ} (hu : IsCand ws t u) (hmin : ∀ v, IsCand ws t v → u ≤ v) :
    u = (sortedDistinct ws)[t] :=
  le_antisymm (hmin _ (cand_getElem ht)) (getElem_le_cand ht hu)

end Lax185574Proofs.Words
