/-
**The context letters of the pieces of an accepted annotation.**

The parameters of a window transducer record the letter immediately to the left
and the letter immediately to the right of its window
(`Transducers.TwoWay.Chk.lOf` and `Transducers.TwoWay.Chk.rOf`).  The checking
automaton of stage 1 of the induction step of the book's snake lemma verifies
this letter by letter: at the position where a window flag turns on, and at the
ends of the pair of blocks when it does not turn on at all.  This file collects
those local conditions into the two statements that the chain of pieces needs,
`Transducers.TwoWay.Chk.lOf_pPar` and `Transducers.TwoWay.Chk.rOf_pPar`.
-/
import Lax916827Proofs.Source.PartC.SnakeChkAcc
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open BlockIdx RegPair

variable {A B Q S : Type} {K : ℕ}

lemma take_getLast?_pos {Γ : Type} {v : List Γ} {x : ℕ} (h1 : 0 < x) (h2 : x ≤ v.length) :
    (v.take x).getLast? = some (v[x - 1]'(by omega)) := by
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left h2, List.getElem?_take,
    List.getElem?_eq_getElem (show x - 1 < v.length by omega), if_pos (by omega)]

variable [Inhabited S] {M : TwoWay A B Q} {stp : S → A → S} {ini : S}
  {acc : PieceParam A Q → S → Prop} {u : List (Gam A Q S K)}

/-! ## The role of the last position of a pair -/

/-- If the pair `i` is followed by another block then its last position lies in
its right block. -/
lemma rol_pair_last_of_lt (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i : ℕ}
    (hi : i ≤ nPair u) (hlt : bY u (i + 2) < u.length) {j : ℕ} (hj : j + 1 = bY u (i + 2)) :
    rol u i j = true := by
  have hiN : i < nPair u := by
    by_contra hcon
    have hiN' : i = nPair u := by omega
    rw [hiN', bY_last hu h0] at hlt
    omega
  have hb : bY u (i + 1) < bY u (i + 2) := bY_blk h0 (by omega) (by omega)
  rw [rol, decide_eq_true_eq]
  omega

/-- If the pair `i` reaches the end of the input and the last block is not empty
then the last position of the input lies in the right block of the pair. -/
lemma rol_pair_last_of_end (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i : ℕ}
    (hi : i ≤ nPair u) (hyeq : bY u (i + 2) = u.length)
    (hsa : sa (u[u.length - 1]'(by omega)) = false) {j : ℕ} (hj : j + 1 = bY u (i + 2)) :
    rol u i j = true := by
  have hLlt : u.length - 1 < u.length := by omega
  have hns : nPair u + 1 = nsep sb u := nPair_of_sa_false hu h0 hsa
  have hblk : blk sb u (u.length - 1) = nPair u + 1 := by rw [hns]; exact blk_last h0
  have hb1 : bY u (nPair u + 1) ≤ u.length - 1 := by
    have := bY_le_of_blk (u := u) hLlt; rwa [hblk] at this
  have hiN : i = nPair u := by
    by_contra hcon
    have h2 : bY u (i + 2) ≤ bY u (nPair u + 1) := bY_mono (by omega)
    omega
  have hb1' : bY u (i + 1) ≤ u.length - 1 := by rw [hiN]; exact hb1
  rw [rol, decide_eq_true_eq]
  omega

/-! ## The letter to the left of a window -/

/-- **The letter to the left of a window that does not start at the left end of
the input.** -/
lemma lOf_pPar_succ (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i r n : ℕ}
    (hi : i ≤ nPair u) (hr : r < 2 * K + 1) (hn : aCut u i r = n + 1) (hnl : n < u.length) :
    lOf (pPar u i r) = some (lt (u[n]'hnl)) := by
  have hlt2 : bY u i < bY u (i + 2) := bY_lt_two hu h0 hi
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  have hax : bY u i ≤ n + 1 := by rw [← hn]; exact le_cutOf (le_of_lt hlt2)
  have haY : n + 1 ≤ bY u (i + 2) := by rw [← hn]; exact cutOf_le_hi
  rcases eq_or_lt_of_le hax with hA2 | hB
  · -- the window starts at the boundary between the two blocks of the pair
    have hpos : 0 < bY u i := by omega
    have h1i : 1 ≤ i := by
      by_contra hcon
      have : i = 0 := by omega
      rw [this, bY_zero] at hpos; omega
    have hj1 : n + 1 < u.length := by omega
    have hrf : rol u i (n + 1) = false := by
      rw [← hA2]; exact rol_bY_eq_false h0 hi hpos
    have hfl : flL (u[n + 1]'hj1) false r = true := by
      have := (flL_iff_aCut (i := i) (r := r) hu hj1 hax (by omega)).2 (by omega)
      rwa [hrf] at this
    have hsb : sb (u[n + 1]'hj1) = true := sb_at_bY hu (k := i) h1i hj1 (by omega)
    have hadj := adj_at hu hj1
    rw [if_pos hsb] at hadj
    have hS := hadj.2.2.2.2.2.2.2.2.1 r hfl
    have hp := pr_eq_pPar (i := i) (r := r) hu (n + 1) hj1 hax (by omega)
    rw [hrf] at hp
    rw [← hp]
    exact hS
  · -- the window starts inside the pair
    have hni : bY u i ≤ n := by omega
    rcases eq_or_lt_of_le haY with hC | hB2
    · -- the window is empty at the right end of the pair
      by_cases hcase : bY u (i + 2) < u.length
      · have hrt : rol u i n = true := rol_pair_last_of_lt hu h0 hi hcase hC
        have hj1 : n + 1 < u.length := by omega
        have hfl : flL (u[n]'hnl) true r = false := by
          have : ¬ (flL (u[n]'hnl) (rol u i n) r = true) := by
            rw [flL_iff_aCut (i := i) (r := r) hu hnl hni (by omega)]; omega
          rw [hrt] at this
          simpa using this
        have hsb : sb (u[n + 1]'hj1) = true := sb_at_bY hu (k := i + 2) (by omega) hj1 (by omega)
        have hadj := adj_at hu hj1
        rw [if_pos hsb] at hadj
        have hS := hadj.2.2.2.2.2.2.2.2.2.2.1 r hr hfl
        have hp := pr_eq_pPar (i := i) (r := r) hu n hnl hni (by omega)
        rw [hrt] at hp
        rw [← hp]
        exact hS
      · have hyeq : bY u (i + 2) = u.length := by omega
        have hnL : n = u.length - 1 := by omega
        have hLlt : u.length - 1 < u.length := by omega
        have heq : (u[n]'hnl) = (u[u.length - 1]'hLlt) := getElem_eq_of_idx_eq hnL _ _
        have hE := endOK_at hu h0
        have hp := pr_eq_pPar (i := i) (r := r) hu n hnl hni (by omega)
        by_cases hsa : sa (u[u.length - 1]'hLlt) = true
        · have hfl : flL (u[n]'hnl) (rol u i n) r = false := by
            have : ¬ (flL (u[n]'hnl) (rol u i n) r = true) := by
              rw [flL_iff_aCut (i := i) (r := r) hu hnl hni (by omega)]; omega
            simpa using this
          rw [heq] at hfl hp
          have hS := (hE.2 hsa).2.2.1 _ r hr hfl
          rw [← hp, heq]
          exact hS
        · simp only [Bool.not_eq_true] at hsa
          have hrt : rol u i n = true := rol_pair_last_of_end hu h0 hi hyeq hsa hC
          have hfl : flL (u[n]'hnl) true r = false := by
            have : ¬ (flL (u[n]'hnl) (rol u i n) r = true) := by
              rw [flL_iff_aCut (i := i) (r := r) hu hnl hni (by omega)]; omega
            rw [hrt] at this
            simpa using this
          rw [heq] at hfl
          rw [hrt] at hp
          have hS := (hE.1 hsa).2.1 r hr hfl
          rw [← hp, heq]
          exact hS
    · -- the window starts strictly inside the pair
      have hj1 : n + 1 < u.length := by omega
      have hflT : flL (u[n + 1]'hj1) (rol u i (n + 1)) r = true :=
        (flL_iff_aCut (i := i) (r := r) hu hj1 (by omega) (by omega)).2 (by omega)
      have hflF : flL (u[n]'hnl) (rol u i n) r = false := by
        have : ¬ (flL (u[n]'hnl) (rol u i n) r = true) := by
          rw [flL_iff_aCut (i := i) (r := r) hu hnl hni (by omega)]; omega
        simpa using this
      obtain ⟨hj1', hcase⟩ := pair_step hu hni (by omega)
      have hp := pr_eq_pPar (i := i) (r := r) hu (n + 1) hj1 (by omega) (by omega)
      rw [← hp]
      rcases hcase with ⟨hrol, hsame⟩ | ⟨hr0, hr1, hsep⟩
      · rw [hrol] at hflT ⊢
        rw [hrol] at hp
        exact hsame.2.2.2.2.2.1 (rol u i n) r hflF hflT
      · rw [hr1] at hflT ⊢
        rw [hr0] at hflF
        exact hsep.2.2.2.2.2.1 r hflF hflT

/-- **The letter to the left of the window of a piece.** -/
theorem lOf_pPar (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i r : ℕ}
    (hi : i ≤ nPair u) (hr : r < 2 * K + 1) :
    lOf (pPar u i r) = ((u.map lt).take (aCut u i r)).getLast? := by
  have hlt2 : bY u i < bY u (i + 2) := bY_lt_two hu h0 hi
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  have haY : aCut u i r ≤ bY u (i + 2) := cutOf_le_hi
  have hwl : (u.map lt).length = u.length := length_map_lt u
  rcases Nat.eq_zero_or_pos (aCut u i r) with hz | hpos
  · -- the window starts at the left end of the input
    have hax : bY u i ≤ aCut u i r := le_cutOf (le_of_lt hlt2)
    have hY0 : bY u i = 0 := by omega
    have hfl : flL (u[0]'h0) (rol u i 0) r = true :=
      (flL_iff_aCut (i := i) (r := r) hu h0 (by omega) (by omega)).2 (by omega)
    have hS := (startOK_at hu h0).2.2.1 (rol u i 0) r hfl
    have hp := pr_eq_pPar (i := i) (r := r) hu 0 h0 (by omega) (by omega)
    rw [hp] at hS
    rw [hz, hS]
    simp
  · obtain ⟨n, hn⟩ : ∃ n, aCut u i r = n + 1 := ⟨aCut u i r - 1, by omega⟩
    have hnl : n < u.length := by omega
    rw [hn, take_getLast?_pos (show 0 < n + 1 by omega) (by rw [hwl]; omega)]
    simp only [Nat.add_sub_cancel]
    rw [getElem_map_lt hnl]
    exact lOf_pPar_succ hu h0 hi hr hn hnl

/-! ## The letter to the right of a window -/

/-- **The letter to the right of a window that does not end at the right end of
the input.** -/
lemma rOf_pPar_lt (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i r : ℕ}
    (hi : i ≤ nPair u) (hr : r < 2 * K + 1) (hy : bCut u i r < u.length) :
    rOf (pPar u i r) = some (lt (u[bCut u i r]'hy)) := by
  have hlt2 : bY u i < bY u (i + 2) := bY_lt_two hu h0 hi
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  have hby : bY u i ≤ bCut u i r := le_cutOf (le_of_lt hlt2)
  have hyY : bCut u i r ≤ bY u (i + 2) := cutOf_le_hi
  rcases Nat.eq_zero_or_pos (bCut u i r) with hz | hpos
  · -- the window ends at the left end of the input
    have hfl : flR (u[0]'h0) (rol u i 0) r = true :=
      (flR_iff_bCut (i := i) (r := r) hu h0 (by omega) (by omega)).2 (by omega)
    have hS := (startOK_at hu h0).2.2.2.1 (rol u i 0) r hfl
    have hp := pr_eq_pPar (i := i) (r := r) hu 0 h0 (by omega) (by omega)
    rw [hp] at hS
    have heq : (u[0]'h0) = (u[bCut u i r]'hy) := getElem_eq_of_idx_eq (by omega) _ _
    rw [hS, heq]
  · obtain ⟨m, hm⟩ : ∃ m, bCut u i r = m + 1 := ⟨bCut u i r - 1, by omega⟩
    have hj1 : m + 1 < u.length := by omega
    have hml : m < u.length := by omega
    have heq : (u[m + 1]'hj1) = (u[bCut u i r]'hy) := getElem_eq_of_idx_eq (by omega) _ _
    rw [← heq]
    rcases eq_or_lt_of_le hby with hA2 | hB
    · -- the window ends at the boundary between the two blocks of the pair
      have hpos0 : 0 < bY u i := by omega
      have h1i : 1 ≤ i := by
        by_contra hcon
        have : i = 0 := by omega
        rw [this, bY_zero] at hpos0; omega
      have hrf : rol u i (m + 1) = false := by
        rw [show m + 1 = bY u i from by omega]
        exact rol_bY_eq_false h0 hi hpos0
      have hfl : flR (u[m + 1]'hj1) false r = true := by
        have := (flR_iff_bCut (i := i) (r := r) hu hj1 (by omega) (by omega)).2 (by omega)
        rwa [hrf] at this
      have hsb : sb (u[m + 1]'hj1) = true := sb_at_bY hu (k := i) h1i hj1 (by omega)
      have hadj := adj_at hu hj1
      rw [if_pos hsb] at hadj
      have hS := hadj.2.2.2.2.2.2.2.2.2.1 r hfl
      have hp := pr_eq_pPar (i := i) (r := r) hu (m + 1) hj1 (by omega) (by omega)
      rw [hrf] at hp
      rw [← hp]
      exact hS
    · have hmi : bY u i ≤ m := by omega
      rcases eq_or_lt_of_le hyY with hC | hB2
      · -- the window ends at the right end of the pair
        have hcase : bY u (i + 2) < u.length := by omega
        have hrt : rol u i m = true := rol_pair_last_of_lt hu h0 hi hcase (by omega)
        have hfl : flR (u[m]'hml) true r = false := by
          have : ¬ (flR (u[m]'hml) (rol u i m) r = true) := by
            rw [flR_iff_bCut (i := i) (r := r) hu hml hmi (by omega)]; omega
          rw [hrt] at this
          simpa using this
        have hsb : sb (u[m + 1]'hj1) = true := sb_at_bY hu (k := i + 2) (by omega) hj1 (by omega)
        have hadj := adj_at hu hj1
        rw [if_pos hsb] at hadj
        have hS := hadj.2.2.2.2.2.2.2.2.2.2.2.1 r hr hfl
        have hp := pr_eq_pPar (i := i) (r := r) hu m hml hmi (by omega)
        rw [hrt] at hp
        rw [← hp]
        exact hS
      · -- the window ends strictly inside the pair
        have hflT : flR (u[m + 1]'hj1) (rol u i (m + 1)) r = true :=
          (flR_iff_bCut (i := i) (r := r) hu hj1 (by omega) (by omega)).2 (by omega)
        have hflF : flR (u[m]'hml) (rol u i m) r = false := by
          have : ¬ (flR (u[m]'hml) (rol u i m) r = true) := by
            rw [flR_iff_bCut (i := i) (r := r) hu hml hmi (by omega)]; omega
          simpa using this
        obtain ⟨hj1', hcase⟩ := pair_step hu hmi (by omega)
        have hp := pr_eq_pPar (i := i) (r := r) hu (m + 1) hj1 (by omega) (by omega)
        rw [← hp]
        rcases hcase with ⟨hrol, hsame⟩ | ⟨hr0, hr1, hsep⟩
        · rw [hrol] at hflT ⊢
          rw [hrol] at hp
          exact hsame.2.2.2.2.2.2 (rol u i m) r hflF hflT
        · rw [hr1] at hflT ⊢
          rw [hr0] at hflF
          exact hsep.2.2.2.2.2.2.1 r hflF hflT

/-- **A window that ends at the right end of the input has no letter to its
right.** -/
lemma rOf_pPar_end (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i r : ℕ}
    (hi : i ≤ nPair u) (hy : bCut u i r = u.length) :
    rOf (pPar u i r) = none := by
  have hlt2 : bY u i < bY u (i + 2) := bY_lt_two hu h0 hi
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  have hby : bY u i ≤ bCut u i r := le_cutOf (le_of_lt hlt2)
  have hyY : bCut u i r ≤ bY u (i + 2) := cutOf_le_hi
  have hyeq : bY u (i + 2) = u.length := by omega
  have hLlt : u.length - 1 < u.length := by omega
  have hmi : bY u i ≤ u.length - 1 := by omega
  have hp := pr_eq_pPar (i := i) (r := r) hu (u.length - 1) hLlt hmi (by omega)
  have hE := endOK_at hu h0
  by_cases hsa : sa (u[u.length - 1]'hLlt) = true
  · have hfl : flR (u[u.length - 1]'hLlt) (rol u i (u.length - 1)) r = false := by
      have : ¬ (flR (u[u.length - 1]'hLlt) (rol u i (u.length - 1)) r = true) := by
        rw [flR_iff_bCut (i := i) (r := r) hu hLlt hmi (by omega)]; omega
      simpa using this
    rw [← hp]
    exact (hE.2 hsa).2.2.2.1 _ r hfl
  · simp only [Bool.not_eq_true] at hsa
    have hrt : rol u i (u.length - 1) = true :=
      rol_pair_last_of_end hu h0 hi hyeq hsa (show u.length - 1 + 1 = bY u (i + 2) by omega)
    have hfl : flR (u[u.length - 1]'hLlt) true r = false := by
      have : ¬ (flR (u[u.length - 1]'hLlt) (rol u i (u.length - 1)) r = true) := by
        rw [flR_iff_bCut (i := i) (r := r) hu hLlt hmi (by omega)]; omega
      rw [hrt] at this
      simpa using this
    rw [hrt] at hp
    rw [← hp]
    exact (hE.1 hsa).2.2.1 r hfl

/-- **The letter to the right of the window of a piece.** -/
theorem rOf_pPar (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i r : ℕ}
    (hi : i ≤ nPair u) (hr : r < 2 * K + 1) :
    rOf (pPar u i r) = ((u.map lt).drop (bCut u i r)).head? := by
  have hlt2 : bY u i < bY u (i + 2) := bY_lt_two hu h0 hi
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  have hyY : bCut u i r ≤ bY u (i + 2) := cutOf_le_hi
  have hwl : (u.map lt).length = u.length := length_map_lt u
  rw [List.head?_drop]
  by_cases hy : bCut u i r < u.length
  · rw [List.getElem?_eq_getElem (show bCut u i r < (u.map lt).length by omega),
      getElem_map_lt hy]
    exact rOf_pPar_lt hu h0 hi hr hy
  · have hyeq : bCut u i r = u.length := by omega
    rw [List.getElem?_eq_none (by omega)]
    exact rOf_pPar_end hu h0 hi hyeq

end Chk

end TwoWay

end Lax916827Proofs.Transducers
