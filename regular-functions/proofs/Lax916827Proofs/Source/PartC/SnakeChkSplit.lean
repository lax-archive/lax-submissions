/-
**Cutting a string into blocks at the marked positions.**

The annotation of stage 1 of the induction step of the book's snake lemma marks
the positions at which the input is cut into the blocks of the record-breaker
decomposition, by a bit `sep` carried by every annotated letter.  This file
turns that bit into the numerical data that the assembly of the annotation
(`RequestProject/PartC/SnakeAssemble.lean`) works with: the index
`Transducers.BlockIdx.blk` of the block containing a position, and the first
position `Transducers.BlockIdx.bstart` of a block.

Nothing here is specific to transducers; the only assumption used in the
statements about `bstart` is that the first letter of the string is marked, so
that the `0`-th block is empty.
-/
import Mathlib.Tactic
import Lax916827Proofs.Source.PartC.RegAut
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace BlockIdx

variable {Γ : Type}

/-- The index of the block containing the position `j`: the number of marked
positions up to and including `j`. -/
def blk (sep : Γ → Bool) (u : List Γ) (j : ℕ) : ℕ := (u.take (j + 1)).countP sep

/-- The number of marked positions, i.e. the index of the last block. -/
def nsep (sep : Γ → Bool) (u : List Γ) : ℕ := u.countP sep

open Classical in
/-- The first position of the `k`-th block, and the length of the string if
there is no `k`-th block. -/
noncomputable def bstart (sep : Γ → Bool) (u : List Γ) (k : ℕ) : ℕ :=
  if h : ∃ j, j < u.length ∧ k ≤ blk sep u j then Nat.find h else u.length

variable {sep : Γ → Bool} {u : List Γ}

lemma blk_le_nsep (j : ℕ) : blk sep u j ≤ nsep sep u :=
  List.Sublist.countP_le (List.take_sublist _ _)

lemma blk_mono {j j' : ℕ} (h : j ≤ j') : blk sep u j ≤ blk sep u j' :=
  List.Sublist.countP_le (List.IsPrefix.sublist
    (List.take_prefix_take_left (show j + 1 ≤ j' + 1 by omega)))

lemma blk_succ {j : ℕ} (hj : j + 1 < u.length) :
    blk sep u (j + 1) = blk sep u j + (if sep u[j + 1] = true then 1 else 0) := by
  rw [blk, blk, List.take_add_one, List.getElem?_eq_getElem hj, List.countP_append]
  simp only [Option.toList_some, List.countP_cons, List.countP_nil, Nat.zero_add]

lemma blk_zero_le_one : blk sep u 0 ≤ 1 :=
  le_trans List.countP_le_length (by simp)

lemma blk_zero_of_sep (hu : 0 < u.length) (h0 : sep u[0] = true) : blk sep u 0 = 1 := by
  simp [blk, List.take_add_one, List.getElem?_eq_getElem hu, h0]

lemma one_le_blk (hu : 0 < u.length) (h0 : sep u[0] = true) (j : ℕ) : 1 ≤ blk sep u j := by
  have := blk_mono (sep := sep) (u := u) (Nat.zero_le j)
  rw [blk_zero_of_sep hu h0] at this
  exact this

lemma blk_last (hu : 0 < u.length) : blk sep u (u.length - 1) = nsep sep u := by
  rw [blk, nsep, show u.length - 1 + 1 = u.length from by omega, List.take_length]

/-! ## The first position of a block -/

lemma bstart_le_length (k : ℕ) : bstart sep u k ≤ u.length := by
  classical
  rw [bstart]
  split
  · rename_i h
    exact le_of_lt (Nat.find_spec h).1
  · exact le_refl _

lemma bstart_spec {k : ℕ} (h : ∃ j, j < u.length ∧ k ≤ blk sep u j) :
    bstart sep u k < u.length ∧ k ≤ blk sep u (bstart sep u k) := by
  classical
  rw [bstart, dif_pos h]
  exact Nat.find_spec h

lemma bstart_min {k j : ℕ} (hj : j < u.length) (hk : k ≤ blk sep u j) :
    bstart sep u k ≤ j := by
  classical
  have h : ∃ j, j < u.length ∧ k ≤ blk sep u j := ⟨j, hj, hk⟩
  rw [bstart, dif_pos h]
  exact Nat.find_min' h ⟨hj, hk⟩

lemma bstart_eq_length {k : ℕ} (h : ¬ ∃ j, j < u.length ∧ k ≤ blk sep u j) :
    bstart sep u k = u.length := by
  classical
  rw [bstart, dif_neg h]

lemma lt_bstart {k j : ℕ} (hj : blk sep u j < k) (hju : j < u.length) : j < bstart sep u k := by
  classical
  by_contra hcon
  push_neg at hcon
  by_cases h : ∃ j, j < u.length ∧ k ≤ blk sep u j
  · obtain ⟨h1, h2⟩ := bstart_spec h
    have := blk_mono (sep := sep) (u := u) hcon
    omega
  · rw [bstart_eq_length h] at hcon
    omega

lemma bstart_mono {k k' : ℕ} (h : k ≤ k') : bstart sep u k ≤ bstart sep u k' := by
  classical
  by_cases hk' : ∃ j, j < u.length ∧ k' ≤ blk sep u j
  · obtain ⟨h1, h2⟩ := bstart_spec hk'
    exact bstart_min h1 (le_trans h h2)
  · rw [bstart_eq_length hk']
    exact bstart_le_length k

lemma bstart_zero : bstart sep u 0 = 0 := by
  classical
  rcases Nat.eq_zero_or_pos u.length with h | h
  · rw [bstart, dif_neg (by rintro ⟨j, hj, -⟩; omega)]
    omega
  · exact Nat.le_zero.1 (bstart_min h (Nat.zero_le _))

lemma bstart_of_gt {k : ℕ} (h : nsep sep u < k) : bstart sep u k = u.length := by
  classical
  rw [bstart, dif_neg]
  rintro ⟨j, -, hj⟩
  have := blk_le_nsep (sep := sep) (u := u) j
  omega

lemma bstart_le_self {j : ℕ} (hj : j < u.length) : bstart sep u (blk sep u j) ≤ j :=
  bstart_min hj (le_refl _)

lemma lt_bstart_succ {j : ℕ} (hj : j < u.length) : j < bstart sep u (blk sep u j + 1) :=
  lt_bstart (by omega) hj

lemma blk_bstart {k : ℕ} (hk : ∃ j, j < u.length ∧ k ≤ blk sep u j) (hk1 : 1 ≤ k) :
    blk sep u (bstart sep u k) = k := by
  classical
  obtain ⟨h1, h2⟩ := bstart_spec hk
  rcases Nat.eq_zero_or_pos (bstart sep u k) with h0 | h0
  · have := blk_zero_le_one (sep := sep) (u := u)
    rw [h0] at h2 ⊢
    omega
  · obtain ⟨i, hi⟩ : ∃ i, bstart sep u k = i + 1 := ⟨bstart sep u k - 1, by omega⟩
    have hiu : i + 1 < u.length := by omega
    have hprev : blk sep u i < k := by
      by_contra hcon2
      have := bstart_min (sep := sep) (u := u) (k := k) (j := i) (by omega) (by omega)
      omega
    have hstep := blk_succ (sep := sep) (u := u) (j := i) hiu
    rw [hi] at h2 ⊢
    split at hstep <;> omega

lemma bstart_lt_succ {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ nsep sep u) (hu : 0 < u.length) :
    bstart sep u k < bstart sep u (k + 1) := by
  classical
  have hex : ∃ j, j < u.length ∧ k ≤ blk sep u j :=
    ⟨u.length - 1, by omega, by rw [blk_last hu]; exact hk⟩
  obtain ⟨h1, -⟩ := bstart_spec hex
  have := blk_bstart hex hk1
  exact lt_bstart (by omega) h1

/-- **A position is marked exactly when it is the first position of its
block.** -/
lemma sep_iff_bstart (h0 : ∀ hu : 0 < u.length, sep u[0] = true) {j : ℕ} (hj : j < u.length) :
    sep u[j] = true ↔ j = bstart sep u (blk sep u j) := by
  cases j with
  | zero =>
      simp only [h0 hj, true_iff]
      exact (Nat.le_zero.1 (bstart_le_self hj)).symm
  | succ i =>
      have hstep := blk_succ (sep := sep) (u := u) (j := i) hj
      have hlow : ∀ j' ≤ i, blk sep u j' ≤ blk sep u i := fun j' hj' =>
        blk_mono (sep := sep) (u := u) hj'
      have hle := bstart_le_self (sep := sep) (u := u) hj
      constructor
      · intro hsep
        rw [if_pos hsep] at hstep
        by_contra hcon
        have hlt : bstart sep u (blk sep u (i + 1)) < i + 1 := by omega
        have h2 := bstart_spec (sep := sep) (u := u) (k := blk sep u (i + 1))
          ⟨i + 1, hj, le_refl _⟩
        have := hlow _ (show bstart sep u (blk sep u (i + 1)) ≤ i by omega)
        omega
      · intro hb
        by_contra hcon
        have hsep : (if sep u[i + 1] = true then 1 else 0) = 0 := by
          rw [if_neg hcon]
        rw [hsep] at hstep
        have := bstart_min (sep := sep) (u := u) (k := blk sep u (i + 1)) (j := i)
          (by omega) (by omega)
        omega

end BlockIdx

end Lax916827Proofs.Transducers
