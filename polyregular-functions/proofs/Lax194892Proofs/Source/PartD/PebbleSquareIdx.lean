/-
The gaps of the marked square, as seen by a pebble transducer.

This file prepares the reduction of a `(k+1)`-pebble transducer to a `k`-pebble transducer running
on the marked square of the padded input, which is the hard inclusion of Theorem
`thm:pebble-are-for`.  The marked square of a string `u` of length `N` is the concatenation of the
`N` blocks

  `blk u i = (u.take (i+1)).map Sum.inl ++ (u.drop (i+1)).map Sum.inr`,

so a gap of the marked square is either the last gap `N * N` or a pair `(i, j)` of a block `i < N`
and an offset `j < N`, written `i * N + j`.  Two kinds of gaps are visible to a machine that only
sees the two adjacent letters:

* the *marked gap* of the block `i`, at the offset `i + 1`: it is the unique gap of the block whose
  left neighbour is underlined (`Sum.inl`) and whose right neighbour is not (`IsMark`);
* the *start* of a block, at the offset `0`: the beginning of the string, or a gap whose left
  neighbour is not underlined while its right neighbour is (`IsStart`).

The tests `topMark`, `topStart` and `topCoin` are the three tests that the simulating machine
performs on the topmost pebble; the last one asks whether the topmost pebble shares its gap with a
lower one.
-/
import Lax194892Proofs.Source.PartD.SqPad
import Lax194892Proofs.Source.PartD.PebbleDef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebSq

variable {L : Type}

/-! ## Marked gaps and block starts -/

/-- The marked gap of the block `i` of the marked square of a string of length `N`. -/
def IsMark (N x : ℕ) : Prop := ∃ i, i + 1 < N ∧ x = i * N + (i + 1)

/-- The gap at which the block `i` of the marked square of a string of length `N` starts. -/
def IsStart (N x : ℕ) : Prop := ∃ i, i < N ∧ x = i * N

/-- The coordinates of a gap of the marked square are unique. -/
lemma coord_unique {N i j i' j' : ℕ} (hj : j < N) (hj' : j' < N)
    (h : i * N + j = i' * N + j') : i = i' ∧ j = j' := by
  have key : ∀ a b c d : ℕ, c < N → d < N → a < b → a * N + c ≠ b * N + d := by
    intro a b c d hc _ hab hEq
    have h1 : (a + 1) * N ≤ b * N := Nat.mul_le_mul hab le_rfl
    have h2 : (a + 1) * N = a * N + N := by ring
    omega
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd h (key i i' j j' hj hj' hlt)
  · subst heq; exact ⟨rfl, by omega⟩
  · exact absurd h.symm (key i' i j' j hj' hj hgt)

/-- Every gap of the marked square other than the last one has coordinates. -/
lemma exists_coord {N x : ℕ} (hx : x < N * N) : ∃ i j, i < N ∧ j < N ∧ x = i * N + j := by
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
  refine ⟨x / N, x % N, Nat.div_lt_of_lt_mul hx, Nat.mod_lt _ hN, ?_⟩
  rw [Nat.mul_comm]
  exact (Nat.div_add_mod x N).symm

/-- Two marked gaps are at distance at least `N + 1`. -/
lemma mark_spacing {N i p f : ℕ} (h : i * N + (i + 1) = p * N + (p + 1) + f)
    (h1 : 1 ≤ f) (h2 : f ≤ N) : False := by
  rcases Nat.lt_or_ge p i with hip | hip
  swap
  · have h3 : i * N ≤ p * N := Nat.mul_le_mul hip le_rfl
    omega
  · have h3 : (p + 1) * N ≤ i * N := Nat.mul_le_mul hip le_rfl
    have h4 : (p + 1) * N = p * N + N := by ring
    omega

/-- Two block starts are at distance at least `N`. -/
lemma start_spacing {N i p m : ℕ} (h : i * N = p * N + m) (h1 : 1 ≤ m) (h2 : m < N) : False := by
  rcases Nat.lt_or_ge p i with hip | hip
  swap
  · have h3 : i * N ≤ p * N := Nat.mul_le_mul hip le_rfl
    omega
  · have h3 : (p + 1) * N ≤ i * N := Nat.mul_le_mul hip le_rfl
    have h4 : (p + 1) * N = p * N + N := by ring
    omega

/-- The last block of the marked square. -/
lemma pred_mul_add {N : ℕ} : (N - 1) * N + N = N * N := by
  cases N with
  | zero => simp
  | succ n => simp [Nat.succ_mul]

/-- A marked gap is not the last gap. -/
lemma mark_lt {N x : ℕ} (h : IsMark N x) : x < N * N := by
  obtain ⟨i, hi, rfl⟩ := h
  have h1 : (i + 1) * N ≤ (N - 1) * N := Nat.mul_le_mul (by omega) le_rfl
  have h2 : (i + 1) * N = i * N + N := by ring
  have h3 : (N - 1) * N + N = N * N := pred_mul_add
  omega

/-! ## The three tests on the topmost pebble -/

/-- The topmost pebble sits at a marked gap. -/
def isMarkE (e : Option (L ⊕ L) × Option (L ⊕ L)) : Bool :=
  (match e.1 with | some (Sum.inl _) => true | _ => false) &&
    (match e.2 with | some (Sum.inr _) => true | _ => false)

/-- The topmost pebble sits at the start of a block. -/
def isStartE (e : Option (L ⊕ L) × Option (L ⊕ L)) : Bool :=
  match e.1 with
  | none => true
  | some (Sum.inr _) => (match e.2 with | some (Sum.inl _) => true | _ => false)
  | _ => false

/-- The two letters adjacent to the topmost pebble. -/
def topE (V : PebbleView (L ⊕ L)) : Option (Option (L ⊕ L) × Option (L ⊕ L)) :=
  V.getLast?.map Prod.fst

/-- The test "the topmost pebble is at a marked gap". -/
def topMark (V : PebbleView (L ⊕ L)) : Bool := (topE V).elim false isMarkE

/-- The test "the topmost pebble is at the start of a block". -/
def topStart (V : PebbleView (L ⊕ L)) : Bool := (topE V).elim false isStartE

/-- The test "the topmost pebble shares its gap with a lower pebble". -/
def topCoin (V : PebbleView (L ⊕ L)) : Bool :=
  V.getLast?.elim false (fun e => e.2.dropLast.any id)

lemma viewOf_getLast? {A : Type} (w : List A) (st : List ℕ) :
    (viewOf w st).getLast? = st.getLast?.map (fun p =>
      ((if p = 0 then none else w[p - 1]?, w[p]?), st.map (fun q => decide (q = p)))) := by
  simp [viewOf, List.getLast?_map]

lemma topE_append (s : List (L ⊕ L)) (base : List ℕ) (x : ℕ) :
    topE (viewOf s (base ++ [x])) = some ((if x = 0 then none else s[x - 1]?), s[x]?) := by
  simp [topE, viewOf_getLast?]

lemma topCoin_append (s : List (L ⊕ L)) (base : List ℕ) (x : ℕ) :
    topCoin (viewOf s (base ++ [x])) = true ↔ x ∈ base := by
  rw [topCoin, viewOf_getLast?]
  simp only [List.getLast?_concat, Option.map_some, Option.elim_some]
  rw [List.map_append]
  simp only [List.map_cons, List.map_nil, List.dropLast_concat, List.any_eq_true]
  constructor
  · rintro ⟨b, hb, hbt⟩
    simp only [List.mem_map] at hb
    obtain ⟨q, hq, rfl⟩ := hb
    simp only [id_eq, decide_eq_true_eq] at hbt
    exact hbt ▸ hq
  · intro hx
    refine ⟨true, ?_, rfl⟩
    simp only [List.mem_map]
    exact ⟨x, hx, by simp⟩

/-! ## The tests on the marked square -/

section Square

variable {u : List L}

lemma sq_len : (markedSquare L u).length = u.length * u.length := markedSquare_length u

lemma sq_get_none {x : ℕ} (hx : u.length * u.length ≤ x) : (markedSquare L u)[x]? = none := by
  rw [List.getElem?_eq_none]
  rw [sq_len]
  exact hx

/-- The letter to the left of a gap in the interior of a block. -/
lemma sq_prev_in {i j : ℕ} (hi : i < u.length) (hj : j < u.length) (hj0 : 0 < j) :
    (markedSquare L u)[i * u.length + j - 1]? =
      some (if j - 1 ≤ i then Sum.inl u[j - 1] else Sum.inr u[j - 1]) := by
  have h : i * u.length + j - 1 = i * u.length + (j - 1) := by omega
  rw [h]
  exact markedSquare_getElem? hi (by omega)

/-- The letter to the left of the start of a block. -/
lemma sq_prev_start {i : ℕ} (hi : i < u.length) (hi0 : 0 < i) :
    (markedSquare L u)[i * u.length - 1]? =
      some (if u.length - 1 ≤ i - 1 then Sum.inl u[u.length - 1] else Sum.inr u[u.length - 1]) := by
  have hN : 0 < u.length := by omega
  have h : i * u.length - 1 = (i - 1) * u.length + (u.length - 1) := by
    have : i * u.length = (i - 1) * u.length + u.length := by
      cases i with
      | zero => omega
      | succ n => simp [Nat.succ_mul]
    omega
  rw [h]
  exact markedSquare_getElem? (by omega) (by omega)

lemma topMark_iff {base : List ℕ} {x : ℕ} (hx : x ≤ u.length * u.length) :
    topMark (viewOf (markedSquare L u) (base ++ [x])) = true ↔ IsMark u.length x := by
  set N := u.length with hN
  rw [topMark, topE_append]
  simp only [Option.elim_some]
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · constructor
    · intro h; simp [isMarkE] at h
    · rintro ⟨i, hi, hEq⟩; omega
  rcases eq_or_lt_of_le hx with rfl | hxlt
  · -- the last gap
    have hnext : (markedSquare L u)[N * N]? = none := sq_get_none (by omega)
    constructor
    · intro h
      rw [if_neg (by omega), hnext] at h
      simp [isMarkE] at h
    · intro h; exact absurd (mark_lt h) (by omega)
  obtain ⟨i, j, hi, hj, rfl⟩ := exists_coord hxlt
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- the start of a block
    have hi0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with rfl | h
      · omega
      · exact h
    have hprev := sq_prev_start (u := u) hi hi0
    constructor
    · intro h
      rw [if_neg (by simp; omega)] at h
      simp only [Nat.add_zero] at h
      rw [hprev, if_neg (by omega)] at h
      simp [isMarkE] at h
    · rintro ⟨i', hi', hEq⟩
      have := coord_unique (N := N) (show (0:ℕ) < N by omega) (show i' + 1 < N by omega) hEq
      omega
  · have hprev := sq_prev_in (u := u) hi hj hj0
    have hnext := markedSquare_getElem? (u := u) hi hj
    rw [if_neg (by omega), hprev, hnext]
    constructor
    · intro h
      refine ⟨i, ?_, ?_⟩
      · by_cases hji : j ≤ i
        · rw [if_pos hji] at h; simp [isMarkE] at h
        · by_cases hji' : j - 1 ≤ i
          · omega
          · rw [if_neg hji'] at h; simp [isMarkE] at h
      · by_cases hji : j ≤ i
        · rw [if_pos hji] at h; simp [isMarkE] at h
        · by_cases hji' : j - 1 ≤ i
          · congr 1; omega
          · rw [if_neg hji'] at h; simp [isMarkE] at h
    · rintro ⟨i', hi', hEq⟩
      obtain ⟨rfl, hjj⟩ := coord_unique (N := N) hj (by omega) hEq
      subst hjj
      rw [if_pos (by omega), if_neg (by omega)]
      simp [isMarkE]

/-- Whether a gap in the interior of a block is the marked gap of that block, read off from the
two adjacent letters. -/
lemma isMarkE_coord {i j : ℕ} (hi : i < u.length) (hj : j < u.length) (hj0 : 0 < j) :
    isMarkE ((if i * u.length + j = 0 then none
        else (markedSquare L u)[i * u.length + j - 1]?),
      (markedSquare L u)[i * u.length + j]?) = decide (j = i + 1) := by
  rw [if_neg (by omega), sq_prev_in hi hj hj0, markedSquare_getElem? hi hj]
  by_cases hji : j ≤ i
  · have hne : ¬ (j = i + 1) := by omega
    rw [if_pos hji, if_pos (by omega)]
    simp [isMarkE, hne]
  · rw [if_neg hji]
    by_cases h1 : j - 1 ≤ i
    · have heq : j = i + 1 := by omega
      rw [if_pos h1]
      simp [isMarkE, heq]
    · have hne : ¬ (j = i + 1) := by omega
      rw [if_neg h1]
      simp [isMarkE, hne]

lemma topStart_iff {base : List ℕ} {x : ℕ} (hu : 0 < u.length)
    (hx : x ≤ u.length * u.length) :
    topStart (viewOf (markedSquare L u) (base ++ [x])) = true ↔ IsStart u.length x := by
  set N := u.length with hN
  rw [topStart, topE_append]
  simp only [Option.elim_some]
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · rw [if_pos rfl]
    constructor
    · intro _; exact ⟨0, by omega, by simp⟩
    · intro _; simp [isStartE]
  rcases eq_or_lt_of_le hx with rfl | hxlt
  · have hprev : (markedSquare L u)[N * N - 1]? = some (Sum.inl u[N - 1]) := by
      have hidx : N * N - 1 = (N - 1) * N + (N - 1) := by
        have := pred_mul_add (N := N); omega
      rw [hidx, markedSquare_getElem? (u := u) (by omega) (by omega), if_pos le_rfl]
    constructor
    · intro h
      rw [if_neg (by omega), hprev] at h
      simp [isStartE] at h
    · rintro ⟨i, hi, hEq⟩
      have h1 : i * N < N * N := Nat.mul_lt_mul_of_lt_of_le hi le_rfl hu
      omega
  obtain ⟨i, j, hi, hj, rfl⟩ := exists_coord hxlt
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have hi0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with rfl | h
      · omega
      · exact h
    have hprev := sq_prev_start (u := u) hi hi0
    have hnext := markedSquare_getElem? (u := u) hi (by omega : 0 < u.length)
    rw [if_neg (by simp; omega)]
    simp only [Nat.add_zero] at hprev hnext ⊢
    rw [hprev, if_neg (by omega), hnext, if_pos (by omega)]
    constructor
    · intro _; exact ⟨i, hi, rfl⟩
    · intro _; simp [isStartE]
  · have hprev := sq_prev_in (u := u) hi hj hj0
    have hnext := markedSquare_getElem? (u := u) hi hj
    rw [if_neg (by omega), hprev, hnext]
    constructor
    · intro h
      by_cases hji : j - 1 ≤ i
      · rw [if_pos hji] at h; simp [isStartE] at h
      · rw [if_neg hji, if_neg (by omega)] at h; simp [isStartE] at h
    · rintro ⟨i', hi', hEq⟩
      have := coord_unique (N := N) hj (show (0:ℕ) < N by omega)
        (show i * N + j = i' * N + 0 by omega)
      omega

end Square

end PebSq

end Lax194892Proofs.Transducers
