/-
**Reading a chain of pieces off an accepted annotation.**

The checking automaton of stage 1 of the induction step of the book's snake
lemma verifies *local* conditions on an annotation of the input
(`RequestProject/PartC/SnakeChkEnc.lean`).  This file collects what those
conditions add up to: an accepted annotation carries a chain of pieces of the
run in the sense of `Transducers.TwoWay.Chk.ChainData`, whose cutting points,
windows and parameters are the ones read off the annotation in
`RequestProject/PartC/SnakeChkRead.lean`.

It also contains the purely combinatorial half of the soundness proof: the
blocks of the string that the annotation produces are the blocks of the
annotated string built from that data
(`Transducers.TwoWay.Chk.splitSep_homOf_snakeOutLet`), so that the
neighbouring-block map combinator gives the same result on the two strings.
-/
import Lax916827Proofs.Source.PartC.SnakeChkStruct
import Lax916827Proofs.Source.PartC.SnakeChkData
import Lax916827Proofs.Source.PartC.SnakeChkCtx
import Lax916827Proofs.Source.PartC.SnakeChkFlag
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open BlockIdx RegPair

variable {A B Q S : Type} {K : ℕ}

/-! ## Annotating a factor with the positions of its letters -/

/-- A list of pairs whose second components depend only on the position is the
positional annotation of the list of first components. -/
lemma map_prod_eq_annFrom {Γ D C : Type} (g : Γ → D) (F : Γ → C) (G : ℕ → C) :
    ∀ (v : List Γ) (x : ℕ), (∀ (i : ℕ) (hi : i < v.length), F v[i] = G (x + i)) →
      v.map (fun c => (g c, F c)) = annFrom (fun j d => ((d, G j) : D × C)) x (v.map g) := by
  intro v
  induction v with
  | nil => intro x _; rfl
  | cons c v ih =>
      intro x h
      have h0 : F c = G x := by
        have h1 := h 0 (by simp)
        simpa using h1
      rw [List.map_cons, List.map_cons, annFrom_cons, h0]
      congr 1
      refine ih (x + 1) (fun i hi => ?_)
      have h1 := h (i + 1) (by simpa using hi)
      simp only [List.getElem_cons_succ] at h1
      rw [h1, show x + (i + 1) = x + 1 + i from by omega]

lemma seg_map {Γ D : Type} (f : Γ → D) (v : List Γ) (x y : ℕ) :
    TwoWay.seg (v.map f) x y = (TwoWay.seg v x y).map f := by
  simp [TwoWay.seg]

variable [Inhabited S] {M : TwoWay A B Q} {stp : S → A → S} {ini : S}
  {acc : PieceParam A Q → S → Prop} {u : List (Gam A Q S K)}

/-! ## The slot data of a letter -/

/-- **The slot data that a letter contributes** is the one prescribed by the
windows and the parameters read off the annotation. -/
lemma slotsOf_eq_slotData (hu : u ∈ ChkLang M K stp ini acc) {m j : ℕ} (hj : j < u.length)
    (hm : 1 ≤ m) (h1 : bY u m ≤ j) (h2 : j < bY u (m + 1)) :
    slotsOf (u[j]'hj) = slotData K (aCut u) (bCut u) (pPar u) m j := by
  funext t
  have h3 : bY u (m + 1) ≤ bY u (m + 2) := bY_mono (by omega)
  by_cases hpar : t.val % 2 = 1
  · -- the letter's block is the right block of the pair
    have hi2 : m - 1 + 2 = m + 1 := by omega
    have hlo : bY u (m - 1) ≤ j := le_trans (bY_mono (by omega)) h1
    have hhi : j < bY u (m - 1 + 2) := by rw [hi2]; exact h2
    have hrol : rol u (m - 1) j = true := by
      rw [rol, decide_eq_true_eq, show m - 1 + 1 = m from by omega]; exact h1
    have hw := wb_eq_decide (r := t.val / 2) hu hj hlo hhi
    have hp := pr_eq_pPar (r := t.val / 2) hu j hj hlo hhi
    rw [hrol] at hw hp
    show (wb (u[j]'hj) (decide (t.val % 2 = 1)) (t.val / 2),
      pr (u[j]'hj) (decide (t.val % 2 = 1)) (t.val / 2)) = _
    rw [decide_eq_true hpar, hw, hp]
    show _ = (decide (aCut u (if t.val % 2 = 1 then m - 1 else m) (t.val / 2) ≤ j ∧
      j < bCut u (if t.val % 2 = 1 then m - 1 else m) (t.val / 2)),
      pPar u (if t.val % 2 = 1 then m - 1 else m) (t.val / 2))
    rw [if_pos hpar]
  · -- the letter's block is the left block of the pair
    have hhi : j < bY u (m + 2) := by omega
    have hrol : rol u m j = false := by
      rw [rol, decide_eq_false_iff_not]; omega
    have hw := wb_eq_decide (r := t.val / 2) hu hj h1 hhi
    have hp := pr_eq_pPar (r := t.val / 2) hu j hj h1 hhi
    rw [hrol] at hw hp
    show (wb (u[j]'hj) (decide (t.val % 2 = 1)) (t.val / 2),
      pr (u[j]'hj) (decide (t.val % 2 = 1)) (t.val / 2)) = _
    rw [decide_eq_false hpar, hw, hp]
    show _ = (decide (aCut u (if t.val % 2 = 1 then m - 1 else m) (t.val / 2) ≤ j ∧
      j < bCut u (if t.val % 2 = 1 then m - 1 else m) (t.val / 2)),
      pPar u (if t.val % 2 = 1 then m - 1 else m) (t.val / 2))
    rw [if_neg hpar]

/-! ## The blocks of the string produced by the annotation -/

/-- **The blocks of the string produced by an accepted annotation** are the
blocks of the annotated string built from the data read off the annotation. -/
theorem splitSep_homOf_snakeOutLet (hu : u ∈ ChkLang M K stp ini acc) (hne : u ≠ []) :
    splitSep (homOf (snakeOutLet K) u)
      = (List.range (nPair u + 2)).map
          (snakeBlock (u.map lt) K (bY u) (aCut u) (bCut u) (pPar u)) := by
  classical
  have h0 : 0 < u.length := List.length_pos_iff.2 hne
  have hsame : homOf (snakeOutLet K) u
      = homOf (outLet sb sa
          (fun c : Gam A Q S K => ((lt c, slotsOf c) : SnakeLet A Q (2 * (2 * K + 1))))) u := rfl
  rw [hsame, splitSep_homOf_outLet hne (sb_zero' hu) (sa_last hu)]
  have hnb : nbl sb sa u + 1 = nPair u + 2 := by
    have h1 := one_le_nsep hu h0
    rw [nPair, nbl_eq_add]
    split <;> omega
  rw [hnb]
  refine List.map_congr_left ?_
  intro m hm
  have hmlt : m < nPair u + 2 := List.mem_range.1 hm
  rw [← bY_def u m, ← bY_def u (m + 1)]
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · -- the `0`-th block is empty
    have hb0 : bY u 0 = 0 := bY_zero
    have hb1 : bY u 1 = 0 := bY_one hu h0
    rw [snakeBlock, hb0, hb1, seg_eq_nil (le_refl 0), seg_eq_nil (le_refl 0)]
    rfl
  · have hylen : bY u (m + 1) ≤ u.length := bY_le_length _
    rw [snakeBlock, seg_map lt u (bY u m) (bY u (m + 1))]
    refine map_prod_eq_annFrom lt slotsOf
      (fun j => slotData K (aCut u) (bCut u) (pPar u) m j) _ (bY u m) ?_
    intro i hi
    have hlen : (TwoWay.seg u (bY u m) (bY u (m + 1))).length = bY u (m + 1) - bY u m :=
      TwoWay.seg_length u hylen
    rw [hlen] at hi
    have hjlt : bY u m + i < u.length := by omega
    rw [seg_getElem u (bY u m) (bY u (m + 1)) i (by rw [hlen]; omega) hjlt]
    exact slotsOf_eq_slotData hu hjlt hm1 (by omega) (by omega)

/-- **An accepted annotation carries a chain of pieces of the run.** -/
theorem exists_chainData_of_chkLang [Finite A] [Finite B] [Finite Q]
    (hacc : ∀ (p : PieceParam A Q) (v : List A),
      v ∈ WinCond M (K - 1) p ↔ acc p (v.foldl stp ini))
    (hu : u ∈ ChkLang M K stp ini acc) (hne : u ≠ []) :
    ∃ d : ChainData M K (u.map lt),
      d.N = nPair u ∧ d.Y = bY u ∧ d.a = aCut u ∧ d.b = bCut u ∧ d.p = pPar u := by
  classical
  have h0 : 0 < u.length := List.length_pos_iff.2 hne
  have hwl : (u.map lt).length = u.length := length_map_lt u
  have hstart : ∀ i, i ≤ nPair u → bY u i < u.length := by
    intro i hi
    exact lt_of_lt_of_le (bY_lt_two hu h0 hi) (bY_le_length _)
  refine ⟨{ N := nPair u, Y := bY u, a := aCut u, b := bCut u, p := pPar u
            Y_one := bY_one hu h0
            Y_mono := fun m => bY_mono (by omega)
            Y_last := by rw [hwl]; exact bY_last hu h0
            Y_lt := fun i hi => bY_lt_two hu h0 hi
            Y_blk := fun m hm1 hmN => bY_blk h0 hm1 hmN
            win := ?_
            ctxL := fun i hi r hr => lOf_pPar hu h0 hi hr
            ctxR := fun i hi r hr => rOf_pPar hu h0 hi hr
            st := ?_
            kind := ?_
            kind_mid := ?_
            kind_last := ?_
            st_last := ?_
            cut_zero := fun i _ => cut_zero_eq hu
            cut_step := fun i _ r hr => cut_step_eq hu hr
            cut_last := fun i hi => cut_last_eq hu h0 hi
            ent_zero := ?_
            ext_step := ?_
            ext_pair := ?_
            wcond := fun i hi r hr => wcond_of_chkLang hacc hu h0 hi hr }, rfl, rfl, rfl, rfl, rfl⟩
  · -- the window lies inside the pair
    intro i hi r hr
    refine ⟨le_cutOf (le_of_lt (bY_lt_two hu h0 hi)), ?_, cutOf_le_hi⟩
    have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
    rw [aCut, bCut]
    refine cutOf_le_cutOf ?_
    intro j h1 h2 hfl
    have hj : j < u.length := by omega
    rw [flRat, dif_pos hj] at hfl
    rw [flLat, dif_pos hj]
    exact (letOK_at hu hj).1 _ _ hfl
  · -- every piece announces an entry and an exit state
    intro i hi r hr
    have hj : bY u i < u.length := hstart i hi
    have hp := pr_eq_pPar (i := i) (r := r) hu (bY u i) hj (le_refl _) (bY_lt_two hu h0 hi)
    rw [← hp]
    exact (letOK_at hu hj).2.2.2.2.1 _ r hr
  · -- the pieces other than the last one of a pair cross their window
    intro i hi r hr
    have hj : bY u i < u.length := hstart i hi
    have hkd := kd_eq_kdOf (i := i) (r := r) hu (bY u i) hj (le_refl _) (bY_lt_two hu h0 hi)
    rw [← hkd]
    exact (letOK_at hu hj).2.1 _ r (by omega)
  · -- the last piece of a pair which is not the last pair crosses its window
    intro i hi
    have hle : i ≤ nPair u := le_of_lt hi
    have hj : bY u i < u.length := hstart i hle
    have hkd := kd_eq_kdOf (i := i) (r := 2 * K) hu (bY u i) hj (le_refl _) (bY_lt_two hu h0 hle)
    have hlp := lp_eq_lpOf (i := i) hu (bY u i) hj (le_refl _) (bY_lt_two hu h0 hle)
    rw [← hkd]
    refine (letOK_at hu hj).2.2.1 _ ?_
    rw [hlp]
    exact lpOf_of_lt hu h0 hi
  · -- the last piece of the last pair halts inside its window
    have hj : bY u (nPair u) < u.length := hstart _ (le_refl _)
    have hkd := kd_eq_kdOf (i := nPair u) (r := 2 * K) hu (bY u (nPair u)) hj (le_refl _)
      (bY_lt_two hu h0 (le_refl _))
    have hlp := lp_eq_lpOf (i := nPair u) hu (bY u (nPair u)) hj (le_refl _)
      (bY_lt_two hu h0 (le_refl _))
    rw [← hkd]
    refine (letOK_at hu hj).2.2.2.1 _ ?_
    rw [hlp]
    exact lpOf_last hu h0
  · -- a halting piece does not change the state
    have hj : bY u (nPair u) < u.length := hstart _ (le_refl _)
    have hp := pr_eq_pPar (i := nPair u) (r := 2 * K) hu (bY u (nPair u)) hj (le_refl _)
      (bY_lt_two hu h0 (le_refl _))
    have hlp := lp_eq_lpOf (i := nPair u) hu (bY u (nPair u)) hj (le_refl _)
      (bY_lt_two hu h0 (le_refl _))
    rw [← hp]
    refine (letOK_at hu hj).2.2.2.2.2.1 _ ?_
    rw [hlp]
    exact lpOf_last hu h0
  · -- the first piece starts in the initial state
    have hlt : bY u 0 < bY u (0 + 2) := bY_lt_two hu h0 (Nat.zero_le _)
    have hrt : rol u 0 0 = true := by
      rw [rol, decide_eq_true_eq, bY_one hu h0]
    have hp := pr_eq_pPar (i := 0) (r := 0) hu 0 h0 (le_of_eq bY_zero) (by
      rw [bY_zero] at hlt; exact hlt)
    rw [hrt] at hp
    rw [← hp]
    exact (startOK_at hu h0).2.2.2.2
  · -- consecutive pieces of a pair meet in a common state
    intro i hi r hr
    have hj : bY u i < u.length := hstart i hi
    have hlt := bY_lt_two hu h0 hi
    have hp1 := pr_eq_pPar (i := i) (r := r) hu (bY u i) hj (le_refl _) hlt
    have hp2 := pr_eq_pPar (i := i) (r := r + 1) hu (bY u i) hj (le_refl _) hlt
    rw [← hp1, ← hp2]
    exact (letOK_at hu hj).2.2.2.2.2.2.1 _ r (by omega)
  · -- the last piece of a pair and the first piece of the next one meet
    intro i hi
    have hb : bY u (i + 1) < bY u (i + 2) := bY_blk h0 (by omega) (by omega)
    have hj : bY u (i + 1) < u.length := lt_of_lt_of_le hb (bY_le_length _)
    have hrt : rol u i (bY u (i + 1)) = true := by rw [rol, decide_eq_true_eq]
    have hrf : rol u (i + 1) (bY u (i + 1)) = false := by
      rw [rol, decide_eq_false_iff_not]
      show ¬ (bY u (i + 2) ≤ bY u (i + 1))
      omega
    have hp1 := pr_eq_pPar (i := i) (r := 2 * K) hu (bY u (i + 1)) hj
      (bY_mono (show i ≤ i + 1 by omega)) hb
    have hp2 := pr_eq_pPar (i := i + 1) (r := 0) hu (bY u (i + 1)) hj (le_refl _)
      (bY_lt_two hu h0 hi)
    have hlp := lp_eq_lpOf (i := i) hu (bY u (i + 1)) hj
      (bY_mono (show i ≤ i + 1 by omega)) hb
    rw [hrt] at hp1 hlp
    rw [hrf] at hp2
    rw [← hp1, ← hp2]
    refine (letOK_at hu hj).2.2.2.2.2.2.2.2.2.2.2.1 ?_
    rw [hlp]
    exact lpOf_of_lt hu h0 hi

end Chk

end TwoWay

end Lax916827Proofs.Transducers
