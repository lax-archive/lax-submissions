/-
**The structure of an accepted annotation.**

The checking automaton of stage 1 of the induction step of the book's snake
lemma verifies conditions on single letters and on pairs of consecutive letters
of an annotation (`RequestProject/PartC/SnakeChkEnc.lean`).  This file draws
from them the *global* structure of the annotation:

* the blocks tile the input, only the `0`-th one and possibly the last one being
  empty;
* along a pair of neighbouring blocks the two window flags of a piece slot never
  fall back, so that they cut out the window
  (`Transducers.TwoWay.Chk.wb_eq_decide`), and the parameters and the "last
  pair" bit do not change (`Transducers.TwoWay.Chk.pr_eq_pPar`,
  `Transducers.TwoWay.Chk.lp_eq_lpOf`);
* the "last pair" bit is on exactly at the last pair
  (`Transducers.TwoWay.Chk.lpOf_iff`).
-/
import Lax916827Proofs.Source.PartC.SnakeChkRead
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open BlockIdx RegPair

variable {A B Q S : Type} {K : ℕ}

variable [Inhabited S] {M : TwoWay A B Q} {stp : S → A → S} {ini : S}
  {acc : PieceParam A Q → S → Prop} {u : List (Gam A Q S K)}

/-! ## The blocks tile the input -/

lemma one_le_nsep (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) :
    1 ≤ nsep sb u := by
  have h := blk_zero_of_sep (sep := sb) (u := u) h0 (sb_zero hu h0)
  have h2 := blk_le_nsep (sep := sb) (u := u) 0
  omega

omit [Inhabited S] in
lemma nbl_eq_add (u : List (Gam A Q S K)) :
    nbl sb sa u = nsep sb u + (if u.getLast?.elim false sa then 1 else 0) := rfl

omit [Inhabited S] in
lemma nPair_le_nsep : nPair u ≤ nsep sb u := by
  rw [nPair, nbl_eq_add]
  split <;> omega

lemma nsep_le_nPair_succ (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) :
    nsep sb u ≤ nPair u + 1 := by
  have h1 := one_le_nsep hu h0
  rw [nPair, nbl_eq_add]
  split <;> omega

omit [Inhabited S] in
/-- All the blocks but the `0`-th one and the last one are nonempty. -/
lemma bY_blk (h0 : 0 < u.length) {m : ℕ}
    (hm1 : 1 ≤ m) (hmN : m ≤ nPair u) : bY u m < bY u (m + 1) :=
  bstart_lt_succ hm1 (le_trans hmN nPair_le_nsep) h0

/-- The last block ends at the end of the input. -/
lemma bY_last (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) :
    bY u (nPair u + 2) = u.length := by
  refine bstart_of_gt ?_
  have := nsep_le_nPair_succ hu h0
  omega

/-- No pair of neighbouring blocks is empty. -/
lemma bY_lt_two (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i : ℕ}
    (hi : i ≤ nPair u) : bY u i < bY u (i + 2) := by
  rcases Nat.lt_or_ge i (nPair u) with hlt | hge
  · have h1 : bY u (i + 1) < bY u (i + 2) := bY_blk h0 (by omega) (by omega)
    have h2 : bY u i ≤ bY u (i + 1) := bY_mono (by omega)
    omega
  · have hiN : i = nPair u := by omega
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- the only pair is the pair of the two blocks of a one-block annotation
      subst hi0
      have hns : nsep sb u ≤ 1 := by
        have := nsep_le_nPair_succ hu h0
        omega
      have : bY u 2 = u.length := by
        refine bstart_of_gt ?_
        omega
      rw [bY_zero, this]
      exact h0
    · have h1 : bY u i < bY u (i + 1) := bY_blk h0 hipos (by omega)
      have h2 : bY u (i + 1) ≤ bY u (i + 2) := bY_mono (by omega)
      omega

/-- Every position lies in one of the blocks `1, …, nPair u + 1`. -/
lemma blk_bounds (hu : u ∈ ChkLang M K stp ini acc) {j : ℕ} (hj : j < u.length) :
    1 ≤ blk sb u j ∧ blk sb u j ≤ nPair u + 1 := by
  have h0 : 0 < u.length := by omega
  refine ⟨one_le_blk h0 (sb_zero hu h0) j, ?_⟩
  have h1 := blk_le_nsep (sep := sb) (u := u) j
  have h2 := nsep_le_nPair_succ hu h0
  omega

omit [Inhabited S] in
lemma bY_le_of_blk {j : ℕ} (hj : j < u.length) : bY u (blk sb u j) ≤ j :=
  bstart_le_self hj

omit [Inhabited S] in
lemma lt_bY_of_blk {j : ℕ} (hj : j < u.length) : j < bY u (blk sb u j + 1) :=
  lt_bstart_succ hj

omit [Inhabited S] in
/-- The block containing a position of a pair of neighbouring blocks is one of
the two blocks of that pair. -/
lemma blk_of_pair {i j : ℕ} (hj : j < u.length) (h1 : bY u i ≤ j) (h2 : j < bY u (i + 2)) :
    blk sb u j = i ∨ blk sb u j = i + 1 := by
  have hge : i ≤ blk sb u j := by
    by_contra hcon
    push_neg at hcon
    have h3 := bY_mono (u := u) (show blk sb u j + 1 ≤ i by omega)
    have h4 := lt_bY_of_blk hj
    omega
  have hle : blk sb u j ≤ i + 1 := by
    by_contra hcon
    push_neg at hcon
    have h3 := bY_mono (u := u) (show i + 2 ≤ blk sb u j by omega)
    have h4 := bY_le_of_blk hj
    omega
  omega

/-! ## Two consecutive positions of a pair of neighbouring blocks -/

omit [Inhabited S] in
/-- Induction along a pair of neighbouring blocks. -/
lemma pair_prop_induct {i : ℕ} (P : ℕ → Prop) (hb : P (bY u i))
    (hstep : ∀ j, bY u i ≤ j → j + 1 < bY u (i + 2) → P j → P (j + 1)) :
    ∀ j, bY u i ≤ j → j < bY u (i + 2) → P j := by
  intro j
  induction j with
  | zero =>
      intro h1 _
      rw [show (0 : ℕ) = bY u i from by omega]
      exact hb
  | succ j ih =>
      intro h1 h2
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact hb
      · exact hstep j (by omega) h2 (ih (by omega) (by omega))

/-- **The step from a position of a pair of neighbouring blocks to the next
one**: either the two positions lie in the same block and carry the same role,
or the second one starts the right block of the pair. -/
lemma pair_step (hu : u ∈ ChkLang M K stp ini acc) {i j : ℕ}
    (h1 : bY u i ≤ j) (h2 : j + 1 < bY u (i + 2)) :
    ∃ hj1 : j + 1 < u.length,
      (rol u i (j + 1) = rol u i j ∧
        AdjSame K stp (u[j]'(by omega)) (u[j + 1]'hj1))
      ∨ (rol u i j = false ∧ rol u i (j + 1) = true ∧
        AdjSep K stp ini acc (u[j]'(by omega)) (u[j + 1]'hj1)) := by
  have hlen : bY u (i + 2) ≤ u.length := bY_le_length _
  have hj1 : j + 1 < u.length := by omega
  refine ⟨hj1, ?_⟩
  have hadj := adj_at hu hj1
  have hblk : blk sb u (j + 1) = i ∨ blk sb u (j + 1) = i + 1 :=
    blk_of_pair hj1 (by omega) h2
  by_cases hsb : sb (u[j + 1]'hj1) = true
  · -- a new block starts
    have hstart : j + 1 = bY u (blk sb u (j + 1)) :=
      (sep_iff_bstart (sb_zero' hu) hj1).1 hsb
    have hb1 : blk sb u (j + 1) = i + 1 := by
      rcases hblk with h | h
      · exfalso; rw [h] at hstart; omega
      · exact h
    rw [hb1] at hstart
    refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [rol, decide_eq_false_iff_not]; omega
    · rw [rol, decide_eq_true_eq]; omega
    · rw [if_pos hsb] at hadj; exact hadj
  · -- the two positions lie in the same block
    simp only [Bool.not_eq_true] at hsb
    have hne : bY u (i + 1) ≠ j + 1 := by
      intro hcon
      have hb1 : blk sb u (j + 1) = i + 1 :=
        blk_eq_of_between hj1 (by omega) (by omega)
      have := (sep_iff_bstart (sb_zero' hu) hj1).2 (by rw [hb1, ← bY_def]; omega)
      rw [hsb] at this
      exact Bool.noConfusion this
    refine Or.inl ⟨?_, ?_⟩
    · rw [rol, rol]
      by_cases h : bY u (i + 1) ≤ j
      · rw [decide_eq_true (by omega), decide_eq_true h]
      · rw [decide_eq_false (by omega), decide_eq_false (by omega)]
    · rw [if_neg (by simp [hsb])] at hadj; exact hadj

/-! ## The flags cut out the window -/

lemma flLat_mono (hu : u ∈ ChkLang M K stp ini acc) {i r : ℕ} :
    ∀ j, bY u i ≤ j → j + 1 < bY u (i + 2) → flLat u i r j = true →
      flLat u i r (j + 1) = true := by
  intro j h1 h2 hfl
  obtain ⟨hj1, hcase⟩ := pair_step hu h1 h2
  have hj : j < u.length := by omega
  rw [flLat, dif_pos hj] at hfl
  rw [flLat, dif_pos hj1]
  rcases hcase with ⟨hrol, hsame⟩ | ⟨hr0, hr1, hsep⟩
  · rw [hrol]; exact hsame.1 _ _ hfl
  · rw [hr1]; rw [hr0] at hfl; exact hsep.1 _ hfl

lemma flRat_mono (hu : u ∈ ChkLang M K stp ini acc) {i r : ℕ} :
    ∀ j, bY u i ≤ j → j + 1 < bY u (i + 2) → flRat u i r j = true →
      flRat u i r (j + 1) = true := by
  intro j h1 h2 hfl
  obtain ⟨hj1, hcase⟩ := pair_step hu h1 h2
  have hj : j < u.length := by omega
  rw [flRat, dif_pos hj] at hfl
  rw [flRat, dif_pos hj1]
  rcases hcase with ⟨hrol, hsame⟩ | ⟨hr0, hr1, hsep⟩
  · rw [hrol]; exact hsame.2.1 _ _ hfl
  · rw [hr1]; rw [hr0] at hfl; exact hsep.2.1 _ hfl

/-- **The left flag of a piece slot is on exactly from the left end of its
window on.** -/
lemma flL_iff_aCut (hu : u ∈ ChkLang M K stp ini acc) {i r j : ℕ} (hj : j < u.length)
    (h1 : bY u i ≤ j) (h2 : j < bY u (i + 2)) :
    flL (u[j]'hj) (rol u i j) r = true ↔ aCut u i r ≤ j := by
  have h := cutOf_spec (fl := flLat u i r) (lo := bY u i) (hi := bY u (i + 2))
    (flLat_mono hu) h1 h2
  rw [flLat, dif_pos hj] at h
  exact h

/-- **The right flag of a piece slot is on exactly from the right end of its
window on.** -/
lemma flR_iff_bCut (hu : u ∈ ChkLang M K stp ini acc) {i r j : ℕ} (hj : j < u.length)
    (h1 : bY u i ≤ j) (h2 : j < bY u (i + 2)) :
    flR (u[j]'hj) (rol u i j) r = true ↔ bCut u i r ≤ j := by
  have h := cutOf_spec (fl := flRat u i r) (lo := bY u i) (hi := bY u (i + 2))
    (flRat_mono hu) h1 h2
  rw [flRat, dif_pos hj] at h
  exact h

/-- **A letter belongs to the window of a piece slot exactly when its position
lies between the two cuts.** -/
lemma wb_eq_decide (hu : u ∈ ChkLang M K stp ini acc) {i r j : ℕ} (hj : j < u.length)
    (h1 : bY u i ≤ j) (h2 : j < bY u (i + 2)) :
    wb (u[j]'hj) (rol u i j) r = decide (aCut u i r ≤ j ∧ j < bCut u i r) := by
  have hLi := flL_iff_aCut (r := r) hu hj h1 h2
  have hRi := flR_iff_bCut (r := r) hu hj h1 h2
  rw [wb]
  by_cases hA : aCut u i r ≤ j
  · by_cases hB : bCut u i r ≤ j
    · rw [hLi.2 hA, hRi.2 hB]
      have hnot : ¬ (aCut u i r ≤ j ∧ j < bCut u i r) := by omega
      simp [hnot]
    · have hrf : flR (u[j]'hj) (rol u i j) r = false :=
        Bool.eq_false_iff.2 (fun hc => hB (hRi.1 hc))
      rw [hLi.2 hA, hrf]
      have hyes : aCut u i r ≤ j ∧ j < bCut u i r := ⟨hA, by omega⟩
      simp [hyes]
  · have hlf : flL (u[j]'hj) (rol u i j) r = false :=
      Bool.eq_false_iff.2 (fun hc => hA (hLi.1 hc))
    rw [hlf]
    have hnot : ¬ (aCut u i r ≤ j ∧ j < bCut u i r) := by omega
    simp [hnot]

/-! ## The parameters and the last-pair bit are constant along a pair -/

lemma pr_eq_pPar (hu : u ∈ ChkLang M K stp ini acc) {i r : ℕ} :
    ∀ j, ∀ hj : j < u.length, bY u i ≤ j → j < bY u (i + 2) →
      pr (u[j]'hj) (rol u i j) r = pPar u i r := by
  have hkey : ∀ j, bY u i ≤ j → j < bY u (i + 2) →
      ∀ hj : j < u.length, pr (u[j]'hj) (rol u i j) r = pPar u i r := by
    refine pair_prop_induct
      (fun j => ∀ hj : j < u.length, pr (u[j]'hj) (rol u i j) r = pPar u i r) ?_ ?_
    · intro hj
      rw [pPar, dif_pos hj]
    · intro j h1 h2 ih hj1
      obtain ⟨hj1', hcase⟩ := pair_step hu h1 h2
      have hj : j < u.length := by omega
      rcases hcase with ⟨hrol, hsame⟩ | ⟨hr0, hr1, hsep⟩
      · rw [hrol, ← hsame.2.2.1 _ _]; exact ih hj
      · rw [hr1, ← hsep.2.2.1 _]; rw [← hr0]; exact ih hj
  intro j hj h1 h2
  exact hkey j h1 h2 hj

lemma lp_eq_lpOf (hu : u ∈ ChkLang M K stp ini acc) {i : ℕ} :
    ∀ j, ∀ hj : j < u.length, bY u i ≤ j → j < bY u (i + 2) →
      lp (u[j]'hj) (rol u i j) = lpOf u i := by
  have hkey : ∀ j, bY u i ≤ j → j < bY u (i + 2) →
      ∀ hj : j < u.length, lp (u[j]'hj) (rol u i j) = lpOf u i := by
    refine pair_prop_induct
      (fun j => ∀ hj : j < u.length, lp (u[j]'hj) (rol u i j) = lpOf u i) ?_ ?_
    · intro hj
      rw [lpOf, dif_pos hj]
    · intro j h1 h2 ih hj1
      obtain ⟨hj1', hcase⟩ := pair_step hu h1 h2
      have hj : j < u.length := by omega
      rcases hcase with ⟨hrol, hsame⟩ | ⟨hr0, hr1, hsep⟩
      · rw [hrol, ← hsame.2.2.2.1 _]; exact ih hj
      · rw [hr1, ← hsep.2.2.2.1]; rw [← hr0]; exact ih hj
  intro j hj h1 h2
  exact hkey j h1 h2 hj


/-! ## The last pair -/

/-- Transporting an indexed access along an equality of indices. -/
lemma getElem_eq_of_idx_eq {Γ : Type} {v : List Γ} {i j : ℕ} (h : i = j) (hi : i < v.length)
    (hj : j < v.length) : v[i]'hi = v[j]'hj := by subst h; rfl

/-- The first position of a block is marked. -/
lemma sb_at_bY (hu : u ∈ ChkLang M K stp ini acc) {k j : ℕ} (hk1 : 1 ≤ k)
    (hj : j < u.length) (hjk : j = bY u k) : sb (u[j]'hj) = true := by
  classical
  have hlt : bY u k < u.length := by omega
  have hex : ∃ j', j' < u.length ∧ k ≤ blk sb u j' := by
    by_contra hcon
    rw [bY_def, bstart_eq_length hcon] at hlt
    omega
  have hb : blk sb u j = k := by rw [hjk, bY_def]; exact blk_bstart hex hk1
  rw [sep_iff_bstart (sb_zero' hu) hj, hb, ← bY_def]
  exact hjk

omit [Inhabited S] in
lemma bY_lt_length (h0 : 0 < u.length) {k : ℕ} (hk : k ≤ nsep sb u) : bY u k < u.length := by
  have hex : ∃ j, j < u.length ∧ k ≤ blk sb u j :=
    ⟨u.length - 1, by omega, by rw [blk_last h0]; exact hk⟩
  exact (bstart_spec (sep := sb) (u := u) hex).1

omit [Inhabited S] in
lemma getLast_sa (h0 : 0 < u.length) :
    u.getLast?.elim false sa = sa (u[u.length - 1]'(by omega)) := by
  rw [List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (show u.length - 1 < u.length by omega)]
  rfl

lemma nPair_of_sa_true (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length)
    (hsa : sa (u[u.length - 1]'(by omega)) = true) : nPair u = nsep sb u := by
  have h1 := one_le_nsep hu h0
  rw [nPair, nbl_eq_add, getLast_sa h0, hsa]
  simp

lemma nPair_of_sa_false (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length)
    (hsa : sa (u[u.length - 1]'(by omega)) = false) : nPair u + 1 = nsep sb u := by
  have h1 := one_le_nsep hu h0
  rw [nPair, nbl_eq_add, getLast_sa h0, hsa]
  simp
  omega

/-- **The last pair of blocks is marked as such.** -/
lemma lpOf_last (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) :
    lpOf u (nPair u) = true := by
  have hLlt : u.length - 1 < u.length := by omega
  have hE := endOK_at hu h0
  by_cases hsa : sa (u[u.length - 1]'hLlt) = true
  · have hns : nPair u = nsep sb u := nPair_of_sa_true hu h0 hsa
    have hblk : blk sb u (u.length - 1) = nPair u := by rw [hns]; exact blk_last h0
    have h1 : bY u (nPair u) ≤ u.length - 1 := by
      have := bY_le_of_blk (u := u) hLlt; rwa [hblk] at this
    have h2 : u.length - 1 < bY u (nPair u + 1) := by
      have := lt_bY_of_blk (u := u) hLlt; rwa [hblk] at this
    have h3 : u.length - 1 < bY u (nPair u + 2) :=
      lt_of_lt_of_le h2 (bY_mono (by omega))
    have hrol : rol u (nPair u) (u.length - 1) = false := by
      rw [rol, decide_eq_false_iff_not]; omega
    have hlp := lp_eq_lpOf hu (u.length - 1) hLlt h1 h3
    rw [hrol] at hlp
    rw [← hlp]
    exact (hE.2 hsa).1
  · simp only [Bool.not_eq_true] at hsa
    have hns : nPair u + 1 = nsep sb u := nPair_of_sa_false hu h0 hsa
    have hblk : blk sb u (u.length - 1) = nPair u + 1 := by rw [hns]; exact blk_last h0
    have h1 : bY u (nPair u + 1) ≤ u.length - 1 := by
      have := bY_le_of_blk (u := u) hLlt; rwa [hblk] at this
    have h2 : u.length - 1 < bY u (nPair u + 2) := by
      have := lt_bY_of_blk (u := u) hLlt; rwa [hblk] at this
    have h0' : bY u (nPair u) ≤ u.length - 1 := le_trans (bY_mono (by omega)) h1
    have hrol : rol u (nPair u) (u.length - 1) = true := by
      rw [rol, decide_eq_true_eq]; exact h1
    have hlp := lp_eq_lpOf hu (u.length - 1) hLlt h0' h2
    rw [hrol] at hlp
    rw [← hlp]
    exact (hE.1 hsa).1

/-- **A pair of blocks other than the last one is not marked as the last one.** -/
lemma lpOf_of_lt (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i : ℕ}
    (hi : i < nPair u) : lpOf u i = false := by
  have hb1 : bY u (i + 1) < bY u (i + 2) := bY_blk h0 (by omega) (by omega)
  have hylen : bY u (i + 2) ≤ u.length := bY_le_length _
  have hjlt2 : bY u (i + 2) - 1 < bY u (i + 2) := by omega
  have hjlen : bY u (i + 2) - 1 < u.length := by omega
  have hji : bY u i ≤ bY u (i + 2) - 1 :=
    le_trans (bY_mono (show i ≤ i + 1 by omega)) (by omega)
  have hrol : rol u i (bY u (i + 2) - 1) = true := by rw [rol, decide_eq_true_eq]; omega
  have hlp := lp_eq_lpOf hu (bY u (i + 2) - 1) hjlen hji hjlt2
  rw [hrol] at hlp
  rw [← hlp]
  by_cases hcase : bY u (i + 2) < u.length
  · have hj1 : bY u (i + 2) - 1 + 1 < u.length := by omega
    have hsb : sb (u[bY u (i + 2) - 1 + 1]'hj1) = true :=
      sb_at_bY hu (k := i + 2) (by omega) hj1 (by omega)
    have hadj := adj_at hu hj1
    rw [if_pos hsb] at hadj
    exact hadj.2.2.2.2.2.2.2.2.2.2.2.2.2
  · have hyeq : bY u (i + 2) = u.length := by omega
    have hLlt : u.length - 1 < u.length := by omega
    have heq : (u[bY u (i + 2) - 1]'hjlen) = (u[u.length - 1]'hLlt) :=
      getElem_eq_of_idx_eq (by omega) _ _
    rw [heq]
    have hE := endOK_at hu h0
    by_cases hsa : sa (u[u.length - 1]'hLlt) = true
    · exact (hE.2 hsa).2.1
    · exfalso
      simp only [Bool.not_eq_true] at hsa
      have hns : nPair u + 1 = nsep sb u := nPair_of_sa_false hu h0 hsa
      have hblk : blk sb u (u.length - 1) = nPair u + 1 := by rw [hns]; exact blk_last h0
      have h1 : bY u (nPair u + 1) ≤ u.length - 1 := by
        have := bY_le_of_blk (u := u) hLlt; rwa [hblk] at this
      have h2 : bY u (i + 2) ≤ bY u (nPair u + 1) := bY_mono (by omega)
      omega

/-- **The last-pair bit marks exactly the last pair.** -/
lemma lpOf_iff (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i : ℕ}
    (hi : i ≤ nPair u) : lpOf u i = true ↔ i = nPair u := by
  constructor
  · intro h
    by_contra hcon
    rw [lpOf_of_lt hu h0 (by omega)] at h
    exact Bool.noConfusion h
  · rintro rfl
    exact lpOf_last hu h0

end Chk

end TwoWay

end Lax916827Proofs.Transducers
