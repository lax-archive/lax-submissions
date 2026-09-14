/-
**The window condition of the pieces of an accepted annotation.**

The checking automaton of stage 1 of the induction step of the book's snake
lemma carries, in every piece slot and at every letter, the state of a
deterministic automaton for the window conditions
(`Transducers.TwoWay.Chk.WinCond`).  This file shows that this state is what it
claims to be -- the state reached after the window letters read so far
(`Transducers.TwoWay.Chk.ds_eq_foldl`) -- and deduces that the window of every
piece of an accepted annotation satisfies the window condition
(`Transducers.TwoWay.Chk.wcond_of_chkLang`).
-/
import Lax916827Proofs.Source.PartC.SnakeChkStruct
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open BlockIdx RegPair

variable {A B Q S : Type} {K : ℕ}

/-! ## Factors, one letter at a time -/

lemma seg_snoc {Γ : Type} {v : List Γ} {x n : ℕ} (hxn : x ≤ n) (hn : n < v.length) :
    TwoWay.seg v x (n + 1) = TwoWay.seg v x n ++ [v[n]] := by
  rw [← seg_append hxn (Nat.le_succ n)]
  congr 1
  rw [seg_cons (show n < n + 1 by omega) hn, seg_eq_nil (le_refl (n + 1))]

/-- Reading one more letter of a factor truncated at a fixed right end. -/
lemma foldl_seg_min_succ {Γ D : Type} (stp : D → Γ → D) (ini : D) (v : List Γ) (x y n : ℕ)
    (hn : n < v.length) :
    (TwoWay.seg v x (min y (n + 1))).foldl stp ini
      = if x ≤ n ∧ n < y then stp ((TwoWay.seg v x (min y n)).foldl stp ini) v[n]
        else (TwoWay.seg v x (min y n)).foldl stp ini := by
  by_cases h1 : x ≤ n
  · by_cases h2 : n < y
    · rw [if_pos ⟨h1, h2⟩, show min y (n + 1) = n + 1 from by omega,
        show min y n = n from by omega, seg_snoc h1 hn, List.foldl_append]
      rfl
    · rw [if_neg (by omega), show min y (n + 1) = y from by omega,
        show min y n = y from by omega]
  · rw [if_neg (by omega), seg_eq_nil (show min y (n + 1) ≤ x by omega),
      seg_eq_nil (show min y n ≤ x by omega)]

/-! ## The automaton state of a piece slot -/

variable [Inhabited S] {M : TwoWay A B Q} {stp : S → A → S} {ini : S}
  {acc : PieceParam A Q → S → Prop} {u : List (Gam A Q S K)}

omit [Inhabited S] in
lemma length_map_lt (u : List (Gam A Q S K)) : (u.map lt).length = u.length := by
  rw [List.length_map]

omit [Inhabited S] in
lemma getElem_map_lt {j : ℕ} (hj : j < u.length) :
    (u.map lt)[j]'(by rw [length_map_lt]; exact hj) = lt (u[j]'hj) := by
  rw [List.getElem_map]

omit [Inhabited S] in
/-- The role of the first position of a pair of blocks is `false` unless the
left block of the pair is empty. -/
lemma rol_bY_eq_false (h0 : 0 < u.length) {i : ℕ}
    (hi : i ≤ nPair u) (hpos : 0 < bY u i) : rol u i (bY u i) = false := by
  have h1 : 1 ≤ i := by
    by_contra hcon
    have : i = 0 := by omega
    rw [this, bY_zero] at hpos
    omega
  have h2 : bY u i < bY u (i + 1) := bY_blk h0 h1 hi
  rw [rol, decide_eq_false_iff_not]
  omega

/-- **The state of the window-condition automaton carried by a piece slot** is
the state reached after the letters of its window read so far. -/
lemma ds_eq_foldl (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i r : ℕ}
    (hi : i ≤ nPair u) (hr : r < 2 * K + 1) :
    ∀ j, bY u i ≤ j → j < bY u (i + 2) → ∀ hj : j < u.length,
      ds (u[j]'hj) (rol u i j) r
        = (TwoWay.seg (u.map lt) (aCut u i r) (min (bCut u i r) (j + 1))).foldl stp ini := by
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  have hab : bY u i ≤ bY u (i + 2) := bY_mono (by omega)
  have hax : bY u i ≤ aCut u i r := le_cutOf hab
  have hlt2 : bY u i < bY u (i + 2) := bY_lt_two hu h0 hi
  refine pair_prop_induct
    (fun j => ∀ hj : j < u.length,
      ds (u[j]'hj) (rol u i j) r
        = (TwoWay.seg (u.map lt) (aCut u i r) (min (bCut u i r) (j + 1))).foldl stp ini) ?_ ?_
  · -- the first position of the pair
    intro hj0
    have hwb := wb_eq_decide (r := r) hu hj0 (le_refl _) (by omega)
    have hlocal : ds (u[bY u i]'hj0) (rol u i (bY u i)) r
        = (if wb (u[bY u i]'hj0) (rol u i (bY u i)) r
            then stp ini (lt (u[bY u i]'hj0)) else ini) := by
      rcases Nat.eq_zero_or_pos (bY u i) with hz | hpos
      · -- the pair starts at the left end of the input
        have hS := (startOK_at hu h0).2.1 (rol u i (bY u i)) r hr
        have heq : (u[0]'h0) = (u[bY u i]'hj0) := getElem_eq_of_idx_eq (by omega) _ _
        rw [heq] at hS
        exact hS
      · -- the pair starts at a block boundary
        have hrf : rol u i (bY u i) = false := rol_bY_eq_false h0 hi hpos
        have hj1 : bY u i - 1 + 1 < u.length := by omega
        have h1i : 1 ≤ i := by
          by_contra hcon
          have : i = 0 := by omega
          rw [this, bY_zero] at hpos; omega
        have hsb : sb (u[bY u i - 1 + 1]'hj1) = true :=
          sb_at_bY hu (k := i) h1i hj1 (by omega)
        have hadj := adj_at hu hj1
        rw [if_pos hsb] at hadj
        have hS := hadj.2.2.2.2.2.2.2.1 r hr
        have heq : (u[bY u i - 1 + 1]'hj1) = (u[bY u i]'hj0) :=
          getElem_eq_of_idx_eq (by omega) _ _
        rw [heq] at hS
        rw [hrf]
        exact hS
    rw [hlocal, hwb]
    have hmapj : bY u i < (u.map lt).length := by rw [length_map_lt]; exact hj0
    rw [foldl_seg_min_succ stp ini (u.map lt) (aCut u i r) (bCut u i r) (bY u i) hmapj,
      seg_eq_nil (show min (bCut u i r) (bY u i) ≤ aCut u i r by omega),
      getElem_map_lt hj0]
    by_cases hc : aCut u i r ≤ bY u i ∧ bY u i < bCut u i r
    · rw [if_pos hc, decide_eq_true hc, if_pos rfl]
      rfl
    · rw [if_neg hc, decide_eq_false hc, if_neg (by simp)]
      rfl
  · -- one step along the pair
    intro j h1 h2 ih hj1
    have hj : j < u.length := by omega
    obtain ⟨hj1', hcase⟩ := pair_step hu h1 h2
    have hlocal : ds (u[j + 1]'hj1) (rol u i (j + 1)) r
        = (if wb (u[j + 1]'hj1) (rol u i (j + 1)) r
            then stp (ds (u[j]'hj) (rol u i j) r) (lt (u[j + 1]'hj1)) else
            ds (u[j]'hj) (rol u i j) r) := by
      rcases hcase with ⟨hrol, hsame⟩ | ⟨hr0, hr1, hsep⟩
      · have hS := hsame.2.2.2.2.1 (rol u i (j + 1)) r hr
        rw [hrol] at hS ⊢
        exact hS
      · have hS := hsep.2.2.2.2.1 r hr
        rw [hr1, hr0]
        exact hS
    rw [hlocal, ih hj,
      wb_eq_decide (r := r) hu hj1 (by omega) (by omega)]
    have hmapj : j + 1 < (u.map lt).length := by rw [length_map_lt]; exact hj1
    rw [foldl_seg_min_succ stp ini (u.map lt) (aCut u i r) (bCut u i r) (j + 1) hmapj,
      getElem_map_lt hj1]
    by_cases hc : aCut u i r ≤ j + 1 ∧ j + 1 < bCut u i r
    · rw [if_pos hc, decide_eq_true hc, if_pos rfl]
    · rw [if_neg hc, decide_eq_false hc, if_neg (by simp)]

/-! ## The window condition -/

/-- **At the last position of a pair of blocks, the window-condition automaton
of every piece slot of that pair accepts.** -/
lemma acc_pPar (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i r : ℕ}
    (hi : i ≤ nPair u) (hr : r < 2 * K + 1) :
    ∃ hj : bY u (i + 2) - 1 < u.length,
      acc (pPar u i r) (ds (u[bY u (i + 2) - 1]'hj) (rol u i (bY u (i + 2) - 1)) r) := by
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  have hpos2 : 0 < bY u (i + 2) := by
    have := bY_lt_two hu h0 hi
    omega
  have hj : bY u (i + 2) - 1 < u.length := by omega
  have hji : bY u i ≤ bY u (i + 2) - 1 := by
    have := bY_lt_two hu h0 hi
    omega
  refine ⟨hj, ?_⟩
  have hpr := pr_eq_pPar (r := r) hu (bY u (i + 2) - 1) hj hji (by omega)
  rw [← hpr]
  by_cases hcase : bY u (i + 2) < u.length
  · -- the pair is followed by another block
    have hiN : i < nPair u := by
      by_contra hcon
      have hiN' : i = nPair u := by omega
      rw [hiN', bY_last hu h0] at hcase
      omega
    have hrol : rol u i (bY u (i + 2) - 1) = true := by
      have : bY u (i + 1) < bY u (i + 2) := bY_blk h0 (by omega) (by omega)
      rw [rol, decide_eq_true_eq]; omega
    have hj1 : bY u (i + 2) - 1 + 1 < u.length := by omega
    have hsb : sb (u[bY u (i + 2) - 1 + 1]'hj1) = true :=
      sb_at_bY hu (k := i + 2) (by omega) hj1 (by omega)
    have hadj := adj_at hu hj1
    rw [if_pos hsb] at hadj
    have hS := hadj.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr
    rw [hrol]
    exact hS
  · -- the pair is the last one
    have hyeq : bY u (i + 2) = u.length := by omega
    have hLlt : u.length - 1 < u.length := by omega
    have heq : (u[bY u (i + 2) - 1]'hj) = (u[u.length - 1]'hLlt) :=
      getElem_eq_of_idx_eq (by omega) _ _
    rw [heq]
    have hE := endOK_at hu h0
    by_cases hsa : sa (u[u.length - 1]'hLlt) = true
    · exact (hE.2 hsa).2.2.2.2 _ r hr
    · simp only [Bool.not_eq_true] at hsa
      have hns : nPair u + 1 = nsep sb u := nPair_of_sa_false hu h0 hsa
      have hblk : blk sb u (u.length - 1) = nPair u + 1 := by rw [hns]; exact blk_last h0
      have hb1 : bY u (nPair u + 1) ≤ u.length - 1 := by
        have := bY_le_of_blk (u := u) hLlt; rwa [hblk] at this
      have hiN : i = nPair u := by
        by_contra hcon
        have h2 : bY u (i + 2) ≤ bY u (nPair u + 1) := bY_mono (by omega)
        omega
      have hrol : rol u i (bY u (i + 2) - 1) = true := by
        have hb1' : bY u (i + 1) ≤ u.length - 1 := by rw [hiN]; exact hb1
        rw [rol, decide_eq_true_eq]
        omega
      rw [hrol]
      exact (hE.1 hsa).2.2.2 r hr

/-- **Every window of an accepted annotation satisfies the window condition.** -/
theorem wcond_of_chkLang [Finite A] [Finite B] [Finite Q]
    (hacc : ∀ (p : PieceParam A Q) (v : List A),
      v ∈ WinCond M (K - 1) p ↔ acc p (v.foldl stp ini))
    (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i r : ℕ}
    (hi : i ≤ nPair u) (hr : r < 2 * K + 1) :
    TwoWay.seg (u.map lt) (aCut u i r) (bCut u i r) ∈ WinCond M (K - 1) (pPar u i r) := by
  obtain ⟨hj, hA⟩ := acc_pPar hu h0 hi hr
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  have hpos2 : 0 < bY u (i + 2) := by
    have := bY_lt_two hu h0 hi
    omega
  have hji : bY u i ≤ bY u (i + 2) - 1 := by
    have := bY_lt_two hu h0 hi
    omega
  have hds := ds_eq_foldl hu h0 hi hr (bY u (i + 2) - 1) hji (by omega) hj
  rw [hds] at hA
  have hbhi : bCut u i r ≤ bY u (i + 2) := cutOf_le_hi
  rw [show min (bCut u i r) (bY u (i + 2) - 1 + 1) = bCut u i r from by omega] at hA
  exact (hacc _ _).2 hA

end Chk

end TwoWay

end Lax916827Proofs.Transducers
