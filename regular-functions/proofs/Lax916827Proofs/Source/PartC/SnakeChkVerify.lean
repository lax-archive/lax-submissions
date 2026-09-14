/-
**The annotation prescribed by a chain of pieces satisfies the local conditions
of the checking automaton.**

This file verifies, one by one, the five families of local conditions of
`RequestProject/PartC/SnakeChkEnc.lean` -- `LetOK`, `AdjSame`, `AdjSep`,
`StartOK` and `EndOK` -- for the annotation
`Transducers.TwoWay.Chk.ChainData.annot` built from a chain of pieces.  The
assembly into membership in the language of the checking automaton is in
`RequestProject/PartC/SnakeChkBuild.lean`.
-/
import Lax916827Proofs.Source.PartC.SnakeChkAnn
import Lax916827Proofs.Source.PartC.SnakeChkCtx
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open RegPair

variable {A B Q S : Type} {K : ℕ}

/-! ## The data of a slot beyond the last one -/

lemma flL_of_ge {c : Gam A Q S K} {s : Bool} {r : ℕ} (hr : ¬ r < 2 * K + 1) :
    flL c s r = false := dif_neg hr

lemma flR_of_ge {c : Gam A Q S K} {s : Bool} {r : ℕ} (hr : ¬ r < 2 * K + 1) :
    flR c s r = false := dif_neg hr

lemma pr_of_ge {c : Gam A Q S K} {s : Bool} {r : ℕ} (hr : ¬ r < 2 * K + 1) :
    pr c s r = default := dif_neg hr

namespace ChainData

variable {M : TwoWay A B Q} {w : List A} (d : ChainData M K w)
variable [Inhabited S] {stp : S → A → S} {ini : S} {acc : PieceParam A Q → S → Prop}

/-! ## The state of the window-condition automaton -/

omit [Inhabited S] in
lemma dsv_succ (i r j : ℕ) (hj1 : j + 1 < w.length) :
    d.dsv stp ini i r (j + 1)
      = if d.AA i r ≤ j + 1 ∧ j + 1 < d.BB i r then stp (d.dsv stp ini i r j) (w[j + 1]'hj1)
        else d.dsv stp ini i r j := by
  rw [dsv, dsv]
  exact foldl_seg_min_succ stp ini w (d.AA i r) (d.BB i r) (j + 1) hj1

omit [Inhabited S] in
lemma dsv_of_le {i r j : ℕ} (h : j + 1 ≤ d.AA i r) : d.dsv stp ini i r j = ini := by
  rw [dsv, seg_eq_nil (show min (d.BB i r) (j + 1) ≤ d.AA i r by omega)]
  rfl

omit [Inhabited S] in
lemma dsv_zero (i r : ℕ) (h0 : 0 < w.length) :
    d.dsv stp ini i r 0
      = if d.AA i r ≤ 0 ∧ 0 < d.BB i r then stp ini (w[0]'h0) else ini := by
  rw [dsv, foldl_seg_min_succ stp ini w (d.AA i r) (d.BB i r) 0 h0,
    seg_eq_nil (show min (d.BB i r) 0 ≤ d.AA i r by omega)]
  rfl

omit [Inhabited S] in
lemma dsv_full {i r j : ℕ} (hi : i ≤ d.N) (h : d.BB i r ≤ j + 1) :
    d.dsv stp ini i r j = (TwoWay.seg w (d.a i r) (d.b i r)).foldl stp ini := by
  rw [dsv, show min (d.BB i r) (j + 1) = d.BB i r from by omega, AA_of_le d hi, BB_of_le d hi]

/-! ## The context letters -/

lemma lOf_PPar_flip {i r j : ℕ} (hj1 : j + 1 < w.length) (hr : r < 2 * K + 1)
    (hlo : ¬ (d.AA i r ≤ j)) (hhi : d.AA i r ≤ j + 1) :
    lOf (d.PPar i r) = some (w[j]'(by omega)) := by
  have hA : d.AA i r = j + 1 := by omega
  have hiN : i ≤ d.N := by
    by_contra hc
    rw [AA_of_gt d hc] at hA
    omega
  have ha : d.a i r = j + 1 := by rw [← AA_of_le d hiN]; exact hA
  rw [PPar_of_le d hiN, d.ctxL i hiN r hr, ha,
    take_getLast?_pos (show 0 < j + 1 by omega) (by omega)]
  simp

lemma rOf_PPar_flip {i r j : ℕ} (hj1 : j + 1 < w.length) (hr : r < 2 * K + 1)
    (hlo : ¬ (d.BB i r ≤ j)) (hhi : d.BB i r ≤ j + 1) :
    rOf (d.PPar i r) = some (w[j + 1]'hj1) := by
  have hB : d.BB i r = j + 1 := by omega
  have hiN : i ≤ d.N := by
    by_contra hc
    rw [BB_of_gt d hc] at hB
    omega
  have hb : d.b i r = j + 1 := by rw [← BB_of_le d hiN]; exact hB
  rw [PPar_of_le d hiN, d.ctxR i hiN r hr, hb, List.head?_drop,
    List.getElem?_eq_getElem hj1]

lemma lOf_PPar_zero {i r : ℕ} (hr : r < 2 * K + 1) (hA : d.AA i r ≤ 0) :
    lOf (d.PPar i r) = none := by
  have hlen : 0 < w.length := d.length_pos
  have hiN : i ≤ d.N := by
    by_contra hc
    rw [AA_of_gt d hc] at hA
    omega
  have ha : d.a i r = 0 := by rw [← AA_of_le d hiN]; omega
  rw [PPar_of_le d hiN, d.ctxL i hiN r hr, ha]
  simp

lemma rOf_PPar_zero {i r : ℕ} (hr : r < 2 * K + 1) (hB : d.BB i r ≤ 0) :
    rOf (d.PPar i r) = some (w[0]'d.length_pos) := by
  have hlen : 0 < w.length := d.length_pos
  have hiN : i ≤ d.N := by
    by_contra hc
    rw [BB_of_gt d hc] at hB
    omega
  have hb : d.b i r = 0 := by rw [← BB_of_le d hiN]; omega
  rw [PPar_of_le d hiN, d.ctxR i hiN r hr, hb, List.head?_drop,
    List.getElem?_eq_getElem hlen]

lemma lOf_PPar_end {i r : ℕ} (hr : r < 2 * K + 1) (hi : i ≤ d.N)
    (hlo : ¬ (d.AA i r ≤ w.length - 1)) : lOf (d.PPar i r) = some (w[w.length - 1]'(by
      have := d.length_pos; omega)) := by
  have hlen : 0 < w.length := d.length_pos
  have hle : d.AA i r ≤ w.length := AA_le_len d hi hr
  have ha : d.a i r = w.length := by rw [← AA_of_le d hi]; omega
  rw [PPar_of_le d hi, d.ctxL i hi r hr, ha, List.take_length,
    List.getLast?_eq_getElem? , List.getElem?_eq_getElem (show w.length - 1 < w.length by omega)]

lemma rOf_PPar_end {i r : ℕ} (hr : r < 2 * K + 1) (hi : i ≤ d.N)
    (hlo : ¬ (d.BB i r ≤ w.length - 1)) : rOf (d.PPar i r) = none := by
  have hlen : 0 < w.length := d.length_pos
  have hle : d.BB i r ≤ w.length := BB_le_len d hi hr
  have hb : d.b i r = w.length := by rw [← BB_of_le d hi]; omega
  rw [PPar_of_le d hi, d.ctxR i hi r hr, hb, List.drop_length]
  rfl

/-! ## The conditions on a single letter -/

omit [Inhabited S] in
lemma letOK_letAt {j : ℕ} (hj : j < w.length) : LetOK K (d.letAt stp ini j hj) := by
  have hb1 : 1 ≤ d.blkOf j := d.one_le_blkOf j
  have hbN : d.blkOf j ≤ d.N + 1 := d.blkOf_le j
  have h2K : 2 * K < 2 * K + 1 := by omega
  have h0K : 0 < 2 * K + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the window is an interval
    intro s r hfr
    by_cases hr : r < 2 * K + 1
    · rw [flR_letAt d hj hr] at hfr
      rw [flL_letAt d hj hr]
      have hab := AA_le_BB d (i := d.pidx s j) (r := r) hr
      simp only [decide_eq_true_eq] at hfr ⊢
      omega
    · rw [flR_of_ge hr] at hfr
      exact absurd hfr (by simp)
  · -- the kinds of the pieces other than the last one
    intro s r hr1
    have hr : r < 2 * K + 1 := by omega
    rw [kd_letAt d hj hr]
    by_cases hi : d.pidx s j ≤ d.N
    · rw [PPar_of_le d hi]
      exact d.kind _ hi r (by omega)
    · exact Or.inl (kdOf_PPar_of_gt d hi)
  · -- the kind of the last piece of a pair which is not the last pair
    intro s hlp
    rw [lp_letAt] at hlp
    simp only [decide_eq_false_iff_not] at hlp
    rw [kd_letAt d hj h2K]
    by_cases hi : d.pidx s j ≤ d.N
    · rw [PPar_of_le d hi]
      exact d.kind_mid _ (by omega)
    · exact Or.inl (kdOf_PPar_of_gt d hi)
  · -- the kind of the last piece of the last pair
    intro s hlp
    rw [lp_letAt] at hlp
    simp only [decide_eq_true_eq] at hlp
    rw [kd_letAt d hj h2K, PPar_of_le d (le_of_eq hlp), hlp]
    exact d.kind_last
  · -- every piece announces an entry and an exit state
    intro s r hr
    rw [pr_letAt d hj hr]
    by_cases hi : d.pidx s j ≤ d.N
    · rw [PPar_of_le d hi]
      exact d.st _ hi r hr
    · exact ⟨M.init, M.init, stOf_PPar_of_gt d hi⟩
  · -- a halting piece does not change the state
    intro s hlp
    rw [lp_letAt] at hlp
    simp only [decide_eq_true_eq] at hlp
    rw [pr_letAt d hj h2K, PPar_of_le d (le_of_eq hlp), hlp]
    exact d.st_last
  · -- consecutive pieces meet in a common state
    intro s r hr1
    have hr : r < 2 * K + 1 := by omega
    rw [pr_letAt d hj hr, pr_letAt d hj (show r + 1 < 2 * K + 1 by omega)]
    by_cases hi : d.pidx s j ≤ d.N
    · simp only [PPar_of_le d hi]
      exact d.ext_step _ hi r (by omega)
    · rw [extOf_PPar_of_gt d hi, entOf_PPar_of_gt d hi]
  · -- consecutive pieces meet at a common cut
    intro s r hr1
    have hr : r < 2 * K + 1 := by omega
    rw [endfl_letAt d hj hr, startfl_letAt d hj (show r + 1 < 2 * K + 1 by omega)]
    by_cases hi : d.pidx s j ≤ d.N
    · simp only [PPar_of_le d hi, AA_of_le d hi, BB_of_le d hi]
      rw [d.cut_step _ hi r (by omega)]
    · rw [stCut_of_gt d hi, enCut_of_gt d hi]
  · -- the first piece of the left block does not start before the letter
    rw [startfl_letAt d hj h0K]
    simp only [decide_eq_false_iff_not]
    have hif : d.pidx false j = d.blkOf j := rfl
    by_cases hi : d.pidx false j ≤ d.N
    · simp only [PPar_of_le d hi, AA_of_le d hi, BB_of_le d hi]
      rw [d.cut_zero _ hi, hif]
      have := d.lt_Y_blkOf_succ hj
      omega
    · rw [stCut_of_gt d hi]
      omega
  · -- the first piece of the right block starts at or before the letter
    rw [startfl_letAt d hj h0K]
    simp only [decide_eq_true_eq]
    have hit : d.pidx true j = d.blkOf j - 1 := rfl
    have hi : d.pidx true j ≤ d.N := by rw [hit]; omega
    simp only [PPar_of_le d hi, AA_of_le d hi, BB_of_le d hi]
    rw [d.cut_zero _ hi, hit, show d.blkOf j - 1 + 1 = d.blkOf j from by omega]
    exact d.Y_blkOf_le j
  · -- the last piece of a pair which is not the last pair ends after the letter
    intro s hlp
    rw [lp_letAt] at hlp
    simp only [decide_eq_false_iff_not] at hlp
    rw [endfl_letAt d hj h2K]
    simp only [decide_eq_false_iff_not]
    have hlt := d.lt_Y_pidx (s := s) (j := j) hj
    by_cases hi : d.pidx s j ≤ d.N
    · simp only [PPar_of_le d hi, AA_of_le d hi, BB_of_le d hi]
      rw [d.cut_last _ (by omega)]
      omega
    · rw [enCut_of_gt d hi]
      omega
  · -- the last piece of a pair links to the first piece of the next pair
    intro hlp
    rw [lp_letAt] at hlp
    simp only [decide_eq_false_iff_not] at hlp
    obtain ⟨m, hm⟩ : ∃ m, d.blkOf j = m + 1 := ⟨d.blkOf j - 1, by omega⟩
    have h1 : d.pidx true j = m := by rw [pidx_true, hm]; omega
    have h2 : d.pidx false j = m + 1 := by rw [pidx_false, hm]
    rw [h1] at hlp
    have hmN : m + 1 ≤ d.N + 1 := by omega
    rw [pr_letAt d hj h2K, pr_letAt d hj h0K, h1, h2,
      PPar_of_le d (show m ≤ d.N by omega), PPar_of_le d (show m + 1 ≤ d.N by omega)]
    exact d.ext_pair m (by omega)
  · -- the last pair is the pair of the two last blocks
    intro hlp
    rw [lp_letAt] at hlp ⊢
    simp only [decide_eq_true_eq] at hlp
    simp only [decide_eq_false_iff_not]
    have h1 : d.pidx true j = d.blkOf j - 1 := rfl
    have h2 : d.pidx false j = d.blkOf j := rfl
    rw [h1] at hlp
    rw [h2]
    omega

/-! ## The conditions at the two ends of the input -/

lemma startOK_letAt (h0 : 0 < w.length) :
    StartOK M K stp ini (d.letAt stp ini 0 h0) := by
  have hb : d.blkOf 0 = 1 := d.blkOf_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sb_letAt, hb, d.Y_one]
    simp
  · intro s r hr
    rw [ds_letAt d h0 hr, wb_letAt d h0 hr, lt_letAt, dsv_zero d _ _ h0]
    by_cases hc : d.AA (d.pidx s 0) r ≤ 0 ∧ 0 < d.BB (d.pidx s 0) r
    · rw [if_pos hc, decide_eq_true hc, if_pos rfl]
    · rw [if_neg hc, decide_eq_false hc, if_neg (by simp)]
  · intro s r hfl
    by_cases hr : r < 2 * K + 1
    · rw [flL_letAt d h0 hr] at hfl
      simp only [decide_eq_true_eq] at hfl
      rw [pr_letAt d h0 hr]
      exact lOf_PPar_zero d hr hfl
    · rw [flL_of_ge hr] at hfl
      exact absurd hfl (by simp)
  · intro s r hfl
    by_cases hr : r < 2 * K + 1
    · rw [flR_letAt d h0 hr] at hfl
      simp only [decide_eq_true_eq] at hfl
      rw [pr_letAt d h0 hr, lt_letAt]
      exact rOf_PPar_zero d hr hfl
    · rw [flR_of_ge hr] at hfl
      exact absurd hfl (by simp)
  · have hit : d.pidx true 0 = 0 := by rw [pidx_true, hb]
    rw [pr_letAt d h0 (by omega), hit, PPar_of_le d (Nat.zero_le _)]
    exact d.ent_zero

lemma blkOf_last_of_ne (hne : d.Y (d.N + 1) ≠ d.Y (d.N + 2)) :
    d.blkOf (w.length - 1) = d.N + 1 := by
  have h0 : 0 < w.length := d.length_pos
  have hlast : d.Y (d.N + 2) = w.length := d.Y_last
  have hmono : d.Y (d.N + 1) ≤ d.Y (d.N + 2) := d.Y_mono _
  refine d.blkOf_eq (le_refl _) (by omega) ?_
  show w.length - 1 < d.Y (d.N + 2)
  omega

lemma blkOf_last_of_eq (heq : d.Y (d.N + 1) = d.Y (d.N + 2)) :
    1 ≤ d.N ∧ d.blkOf (w.length - 1) = d.N := by
  have h0 : 0 < w.length := d.length_pos
  have hlast : d.Y (d.N + 2) = w.length := d.Y_last
  have hN : 1 ≤ d.N := by
    by_contra hc
    have hN0 : d.N = 0 := by omega
    have heq' : d.Y 1 = d.Y 2 := by rw [hN0] at heq; simpa using heq
    have hlast' : d.Y 2 = w.length := by rw [hN0] at hlast; simpa using hlast
    have h1 : d.Y 1 = 0 := d.Y_one
    omega
  have hblk : d.Y d.N < d.Y (d.N + 1) := d.Y_blk d.N hN (le_refl _)
  refine ⟨hN, d.blkOf_eq (by omega) (by omega) ?_⟩
  omega

lemma endOK_letAt (hacc : ∀ (p : PieceParam A Q) (v : List A),
      v ∈ WinCond M (K - 1) p ↔ acc p (v.foldl stp ini))
    (hL : w.length - 1 < w.length) :
    EndOK K acc (d.letAt stp ini (w.length - 1) hL) := by
  have h0 : 0 < w.length := d.length_pos
  have hlast : d.Y (d.N + 2) = w.length := d.Y_last
  constructor
  · -- the last block is nonempty
    intro hsa
    rw [sa_letAt] at hsa
    simp only [decide_eq_false_iff_not, not_and] at hsa
    have hne : d.Y (d.N + 1) ≠ d.Y (d.N + 2) := hsa trivial
    have hb : d.blkOf (w.length - 1) = d.N + 1 := d.blkOf_last_of_ne hne
    have hit : d.pidx true (w.length - 1) = d.N := by rw [pidx_true, hb]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [lp_letAt, hit]
      simp
    · intro r hr hfl
      rw [flL_letAt d hL hr] at hfl
      simp only [decide_eq_false_iff_not] at hfl
      rw [pr_letAt d hL hr, lt_letAt, hit] at *
      exact lOf_PPar_end d hr (le_refl _) (by rw [hit] at hfl; exact hfl)
    · intro r hfl
      by_cases hr : r < 2 * K + 1
      · rw [flR_letAt d hL hr] at hfl
        simp only [decide_eq_false_iff_not] at hfl
        rw [pr_letAt d hL hr, hit]
        exact rOf_PPar_end d hr (le_refl _) (by rw [hit] at hfl; exact hfl)
      · rw [pr_of_ge hr]
        rfl
    · intro r hr
      rw [pr_letAt d hL hr, ds_letAt d hL hr, hit]
      rw [PPar_of_le d (le_refl _),
        dsv_full d (le_refl _) (show d.BB d.N r ≤ w.length - 1 + 1 by
          have := BB_le_len d (le_refl d.N) hr; omega)]
      exact (hacc _ _).1 (d.wcond d.N (le_refl _) r hr)
  · -- the last block is empty
    intro hsa
    rw [sa_letAt] at hsa
    simp only [decide_eq_true_eq] at hsa
    obtain ⟨-, heq⟩ := hsa
    obtain ⟨hN, hb⟩ := d.blkOf_last_of_eq heq
    have hif : d.pidx false (w.length - 1) = d.N := by rw [pidx_false, hb]
    have hit : d.pidx true (w.length - 1) = d.N - 1 := by rw [pidx_true, hb]
    have hBle : ∀ (s : Bool) (r : ℕ), r < 2 * K + 1 →
        d.pidx s (w.length - 1) ≤ d.N ∧ d.BB (d.pidx s (w.length - 1)) r ≤ w.length := by
      intro s r hr
      have hle : d.pidx s (w.length - 1) ≤ d.N := by
        cases s
        · rw [hif]
        · rw [hit]; omega
      exact ⟨hle, BB_le_len d hle hr⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [lp_letAt, hif]
      simp
    · rw [lp_letAt, hit]
      simp only [decide_eq_false_iff_not]
      omega
    · intro s r hr hfl
      rw [flL_letAt d hL hr] at hfl
      simp only [decide_eq_false_iff_not] at hfl
      rw [pr_letAt d hL hr, lt_letAt]
      exact lOf_PPar_end d hr (hBle s r hr).1 hfl
    · intro s r hfl
      by_cases hr : r < 2 * K + 1
      · rw [flR_letAt d hL hr] at hfl
        simp only [decide_eq_false_iff_not] at hfl
        rw [pr_letAt d hL hr]
        exact rOf_PPar_end d hr (hBle s r hr).1 hfl
      · rw [pr_of_ge hr]
        rfl
    · intro s r hr
      obtain ⟨hle, hBl⟩ := hBle s r hr
      rw [pr_letAt d hL hr, ds_letAt d hL hr, PPar_of_le d hle,
        dsv_full d hle (by omega)]
      exact (hacc _ _).1 (d.wcond _ hle r hr)

/-! ## The conditions on two consecutive letters -/

lemma adjSame_letAt {j : ℕ} (hj : j < w.length) (hj1 : j + 1 < w.length)
    (hblk : d.blkOf (j + 1) = d.blkOf j) :
    AdjSame K stp (d.letAt stp ini j hj) (d.letAt stp ini (j + 1) hj1) := by
  have hpi : ∀ s : Bool, d.pidx s (j + 1) = d.pidx s j := by
    intro s; cases s <;> simp only [pidx_false, pidx_true, hblk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s r hfl
    by_cases hr : r < 2 * K + 1
    · rw [flL_letAt d hj hr] at hfl
      rw [flL_letAt d hj1 hr, hpi s]
      simp only [decide_eq_true_eq] at hfl ⊢
      omega
    · rw [flL_of_ge hr] at hfl
      exact absurd hfl (by simp)
  · intro s r hfl
    by_cases hr : r < 2 * K + 1
    · rw [flR_letAt d hj hr] at hfl
      rw [flR_letAt d hj1 hr, hpi s]
      simp only [decide_eq_true_eq] at hfl ⊢
      omega
    · rw [flR_of_ge hr] at hfl
      exact absurd hfl (by simp)
  · intro s r
    by_cases hr : r < 2 * K + 1
    · rw [pr_letAt d hj hr, pr_letAt d hj1 hr, hpi s]
    · rw [pr_of_ge hr, pr_of_ge hr]
  · intro s
    rw [lp_letAt, lp_letAt, hpi s]
  · intro s r hr
    rw [ds_letAt d hj1 hr, ds_letAt d hj hr, wb_letAt d hj1 hr, lt_letAt, hpi s,
      dsv_succ d _ _ _ hj1]
    by_cases hc : d.AA (d.pidx s j) r ≤ j + 1 ∧ j + 1 < d.BB (d.pidx s j) r
    · rw [if_pos hc, decide_eq_true hc, if_pos rfl]
    · rw [if_neg hc, decide_eq_false hc, if_neg (by simp)]
  · intro s r hf1 hf2
    by_cases hr : r < 2 * K + 1
    · rw [flL_letAt d hj hr] at hf1
      rw [flL_letAt d hj1 hr, hpi s] at hf2
      simp only [decide_eq_false_iff_not] at hf1
      simp only [decide_eq_true_eq] at hf2
      rw [pr_letAt d hj1 hr, lt_letAt, hpi s]
      exact lOf_PPar_flip d hj1 hr hf1 hf2
    · rw [flL_of_ge hr] at hf2
      exact absurd hf2 (by simp)
  · intro s r hf1 hf2
    by_cases hr : r < 2 * K + 1
    · rw [flR_letAt d hj hr] at hf1
      rw [flR_letAt d hj1 hr, hpi s] at hf2
      simp only [decide_eq_false_iff_not] at hf1
      simp only [decide_eq_true_eq] at hf2
      rw [pr_letAt d hj1 hr, lt_letAt, hpi s]
      exact rOf_PPar_flip d hj1 hr hf1 hf2
    · rw [flR_of_ge hr] at hf2
      exact absurd hf2 (by simp)

lemma adjSep_letAt (hacc : ∀ (p : PieceParam A Q) (v : List A),
      v ∈ WinCond M (K - 1) p ↔ acc p (v.foldl stp ini))
    {j : ℕ} (hj : j < w.length) (hj1 : j + 1 < w.length)
    (hblk : d.blkOf (j + 1) = d.blkOf j + 1) (hY : d.Y (d.blkOf j + 1) = j + 1) :
    AdjSep K stp ini acc (d.letAt stp ini j hj) (d.letAt stp ini (j + 1) hj1) := by
  have hb1 : 1 ≤ d.blkOf j := d.one_le_blkOf j
  have hbN : d.blkOf (j + 1) ≤ d.N + 1 := d.blkOf_le (j + 1)
  have hjN : d.blkOf j ≤ d.N := by omega
  -- the pair carried by the role `false` of `b` and the role `true` of `c`
  have hmid : d.pidx true (j + 1) = d.pidx false j := by
    rw [pidx_true, pidx_false, hblk]
    omega
  have hnew : d.pidx false (j + 1) = d.blkOf j + 1 := by rw [pidx_false, hblk]
  have hold : d.pidx true j = d.blkOf j - 1 := rfl
  have hfj : d.pidx false j = d.blkOf j := rfl
  -- the window of the new pair starts at or after the boundary
  have hAnew : ∀ r, r < 2 * K + 1 → j + 1 ≤ d.AA (d.blkOf j + 1) r := by
    intro r hr
    by_cases hi : d.blkOf j + 1 ≤ d.N
    · have := Y_le_AA d hi hr
      omega
    · rw [AA_of_gt d hi]
      omega
  -- the window of the old pair ends at or before the boundary
  have hBold : ∀ r, r < 2 * K + 1 → d.BB (d.blkOf j - 1) r ≤ j + 1 := by
    intro r hr
    have hi : d.blkOf j - 1 ≤ d.N := by omega
    have h1 := BB_le_Y d hi hr
    rw [show d.blkOf j - 1 + 2 = d.blkOf j + 1 from by omega] at h1
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hfl
    by_cases hr : r < 2 * K + 1
    · rw [flL_letAt d hj hr] at hfl
      rw [flL_letAt d hj1 hr, hmid]
      simp only [decide_eq_true_eq] at hfl ⊢
      omega
    · rw [flL_of_ge hr] at hfl
      exact absurd hfl (by simp)
  · intro r hfl
    by_cases hr : r < 2 * K + 1
    · rw [flR_letAt d hj hr] at hfl
      rw [flR_letAt d hj1 hr, hmid]
      simp only [decide_eq_true_eq] at hfl ⊢
      omega
    · rw [flR_of_ge hr] at hfl
      exact absurd hfl (by simp)
  · intro r
    by_cases hr : r < 2 * K + 1
    · rw [pr_letAt d hj hr, pr_letAt d hj1 hr, hmid]
    · rw [pr_of_ge hr, pr_of_ge hr]
  · rw [lp_letAt, lp_letAt, hmid]
  · intro r hr
    rw [ds_letAt d hj1 hr, ds_letAt d hj hr, wb_letAt d hj1 hr, lt_letAt, hmid,
      dsv_succ d _ _ _ hj1]
    by_cases hc : d.AA (d.pidx false j) r ≤ j + 1 ∧ j + 1 < d.BB (d.pidx false j) r
    · rw [if_pos hc, decide_eq_true hc, if_pos rfl]
    · rw [if_neg hc, decide_eq_false hc, if_neg (by simp)]
  · intro r hf1 hf2
    by_cases hr : r < 2 * K + 1
    · rw [flL_letAt d hj hr] at hf1
      rw [flL_letAt d hj1 hr, hmid] at hf2
      simp only [decide_eq_false_iff_not] at hf1
      simp only [decide_eq_true_eq] at hf2
      rw [pr_letAt d hj1 hr, lt_letAt, hmid]
      exact lOf_PPar_flip d hj1 hr hf1 hf2
    · rw [flL_of_ge hr] at hf2
      exact absurd hf2 (by simp)
  · intro r hf1 hf2
    by_cases hr : r < 2 * K + 1
    · rw [flR_letAt d hj hr] at hf1
      rw [flR_letAt d hj1 hr, hmid] at hf2
      simp only [decide_eq_false_iff_not] at hf1
      simp only [decide_eq_true_eq] at hf2
      rw [pr_letAt d hj1 hr, lt_letAt, hmid]
      exact rOf_PPar_flip d hj1 hr hf1 hf2
    · rw [flR_of_ge hr] at hf2
      exact absurd hf2 (by simp)
  · intro r hr
    rw [ds_letAt d hj1 hr, wb_letAt d hj1 hr, lt_letAt, hnew, dsv_succ d _ _ _ hj1,
      dsv_of_le d (hAnew r hr)]
    by_cases hc : d.AA (d.blkOf j + 1) r ≤ j + 1 ∧ j + 1 < d.BB (d.blkOf j + 1) r
    · rw [if_pos hc, decide_eq_true hc, if_pos rfl]
    · rw [if_neg hc, decide_eq_false hc, if_neg (by simp)]
  · intro r hfl
    by_cases hr : r < 2 * K + 1
    · rw [flL_letAt d hj1 hr, hnew] at hfl
      simp only [decide_eq_true_eq] at hfl
      rw [pr_letAt d hj1 hr, lt_letAt, hnew]
      exact lOf_PPar_flip d hj1 hr (by have := hAnew r hr; omega) hfl
    · rw [flL_of_ge hr] at hfl
      exact absurd hfl (by simp)
  · intro r hfl
    by_cases hr : r < 2 * K + 1
    · rw [flR_letAt d hj1 hr, hnew] at hfl
      simp only [decide_eq_true_eq] at hfl
      rw [pr_letAt d hj1 hr, lt_letAt, hnew]
      refine rOf_PPar_flip d hj1 hr ?_ hfl
      have h1 := hAnew r hr
      have h2 := AA_le_BB d (i := d.blkOf j + 1) (r := r) hr
      omega
    · rw [flR_of_ge hr] at hfl
      exact absurd hfl (by simp)
  · intro r hr hfl
    rw [flL_letAt d hj hr, hold] at hfl
    simp only [decide_eq_false_iff_not] at hfl
    rw [pr_letAt d hj hr, lt_letAt, hold]
    refine lOf_PPar_flip d hj1 hr hfl ?_
    have h2 := AA_le_BB d (i := d.blkOf j - 1) (r := r) hr
    have h3 := hBold r hr
    omega
  · intro r hr hfl
    rw [flR_letAt d hj hr, hold] at hfl
    simp only [decide_eq_false_iff_not] at hfl
    rw [pr_letAt d hj hr, lt_letAt, hold]
    exact rOf_PPar_flip d hj1 hr hfl (hBold r hr)
  · intro r hr
    have hi : d.blkOf j - 1 ≤ d.N := by omega
    rw [pr_letAt d hj hr, ds_letAt d hj hr, hold, PPar_of_le d hi,
      dsv_full d hi (hBold r hr)]
    exact (hacc _ _).1 (d.wcond _ hi r hr)
  · rw [lp_letAt, hold]
    simp only [decide_eq_false_iff_not]
    omega

end ChainData

end Chk

end TwoWay

end Lax916827Proofs.Transducers
