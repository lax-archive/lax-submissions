/-
**The annotation prescribed by a chain of pieces.**

Given a chain of pieces (`Transducers.TwoWay.Chk.ChainData`) this file builds the
annotation of the input that the checking automaton of stage 1 of the induction
step of the book's snake lemma is supposed to accept: the block boundary bits
mark the cutting points of the chain, the two window flags of a piece slot are
the indicator functions of the two ends of its window, the parameters are the
ones of the chain, and the automaton state is the state of the window-condition
automaton after the letters of the window read so far.

A position in the last block plays the role `false` in a *pair* of blocks that
does not exist -- the pair `N+1`.  The data of that pair is filled in with a
dummy piece whose window is the empty window `[|w|+1, |w|+1)` beyond the right
end of the input, which makes all its flags false and satisfies every local
condition vacuously; this is what `Transducers.TwoWay.Chk.ChainData.AA`,
`Transducers.TwoWay.Chk.ChainData.BB` and
`Transducers.TwoWay.Chk.ChainData.PPar` do.

The verification of the local conditions is in
`RequestProject/PartC/SnakeChkBuild.lean`.
-/
import Lax916827Proofs.Source.PartC.SnakeChkBlkIdx
import Lax916827Proofs.Source.PartC.SnakeChkEnc
import Lax916827Proofs.Source.PartC.SnakeChkAcc
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open RegPair

variable {A B Q : Type}

namespace ChainData

variable {M : TwoWay A B Q} {K : ℕ} {w : List A} (d : ChainData M K w)

/-! ## The data of a piece slot, with a dummy pair beyond the last one -/

/-- The pair of blocks in which the position `j` plays the role `s`. -/
def pidx (s : Bool) (j : ℕ) : ℕ := if s then d.blkOf j - 1 else d.blkOf j

/-- The left end of the window of the `r`-th piece of the pair `i`, with a dummy
value beyond the right end of the input for the pair `N+1`, which does not
exist. -/
def AA (i r : ℕ) : ℕ := if i ≤ d.N then d.a i r else w.length + 1

/-- The right end of the window of the `r`-th piece of the pair `i`, with a
dummy value for the pair `N+1`. -/
def BB (i r : ℕ) : ℕ := if i ≤ d.N then d.b i r else w.length + 1

/-- The parameters of the `r`-th piece of the pair `i`, with a dummy piece for
the pair `N+1`. -/
def PPar (i r : ℕ) : PieceParam A Q :=
  if i ≤ d.N then d.p i r else ((1 : Fin 5), none, none, some (M.init, M.init))

lemma AA_of_le {i r : ℕ} (hi : i ≤ d.N) : d.AA i r = d.a i r := if_pos hi
lemma BB_of_le {i r : ℕ} (hi : i ≤ d.N) : d.BB i r = d.b i r := if_pos hi
lemma PPar_of_le {i r : ℕ} (hi : i ≤ d.N) : d.PPar i r = d.p i r := if_pos hi

lemma AA_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) : d.AA i r = w.length + 1 := if_neg hi
lemma BB_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) : d.BB i r = w.length + 1 := if_neg hi
lemma kdOf_PPar_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) : kdOf (d.PPar i r) = 1 := by
  rw [PPar, if_neg hi]; rfl
lemma lOf_PPar_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) : lOf (d.PPar i r) = none := by
  rw [PPar, if_neg hi]; rfl
lemma rOf_PPar_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) : rOf (d.PPar i r) = none := by
  rw [PPar, if_neg hi]; rfl
lemma stOf_PPar_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) :
    stOf (d.PPar i r) = some (M.init, M.init) := by
  rw [PPar, if_neg hi]; rfl
lemma entOf_PPar_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) : entOf (d.PPar i r) = some M.init := by
  rw [PPar, if_neg hi]; rfl
lemma extOf_PPar_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) : extOf (d.PPar i r) = some M.init := by
  rw [PPar, if_neg hi]; rfl

lemma Y_le_AA {i r : ℕ} (hi : i ≤ d.N) (hr : r < 2 * K + 1) : d.Y i ≤ d.AA i r := by
  rw [AA_of_le d hi]; exact (d.win i hi r hr).1

lemma AA_le_BB {i r : ℕ} (hr : r < 2 * K + 1) : d.AA i r ≤ d.BB i r := by
  by_cases hi : i ≤ d.N
  · rw [AA_of_le d hi, BB_of_le d hi]; exact (d.win i hi r hr).2.1
  · rw [AA_of_gt d hi, BB_of_gt d hi]

lemma BB_le_Y {i r : ℕ} (hi : i ≤ d.N) (hr : r < 2 * K + 1) : d.BB i r ≤ d.Y (i + 2) := by
  rw [BB_of_le d hi]; exact (d.win i hi r hr).2.2

lemma AA_le_len {i r : ℕ} (hi : i ≤ d.N) (hr : r < 2 * K + 1) : d.AA i r ≤ w.length :=
  le_trans (le_trans (AA_le_BB d hr) (BB_le_Y d hi hr)) (d.Y_le_length (i + 2) (by omega))

lemma BB_le_len {i r : ℕ} (hi : i ≤ d.N) (hr : r < 2 * K + 1) : d.BB i r ≤ w.length :=
  le_trans (BB_le_Y d hi hr) (d.Y_le_length (i + 2) (by omega))

lemma lt_AA_of_gt {i r j : ℕ} (hi : ¬ i ≤ d.N) (hj : j < w.length) : j < d.AA i r := by
  rw [AA_of_gt d hi]; omega

lemma lt_BB_of_gt {i r j : ℕ} (hi : ¬ i ≤ d.N) (hj : j < w.length) : j < d.BB i r := by
  rw [BB_of_gt d hi]; omega

/-- The starting cut of a piece slot, in the extended notation. -/
lemma stCut_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) :
    stCut (d.PPar i r) (d.AA i r) (d.BB i r) = w.length + 1 := by
  rw [stCut, if_pos (Or.inl (kdOf_PPar_of_gt d hi)), AA_of_gt d hi]

lemma enCut_of_gt {i r : ℕ} (hi : ¬ i ≤ d.N) :
    enCut (d.PPar i r) (d.AA i r) (d.BB i r) = w.length + 1 := by
  rw [enCut, if_pos (kdOf_PPar_of_gt d hi), BB_of_gt d hi]

/-! ## The pair of blocks of a position -/

lemma pidx_false (j : ℕ) : d.pidx false j = d.blkOf j := rfl
lemma pidx_true (j : ℕ) : d.pidx true j = d.blkOf j - 1 := rfl

lemma pidx_le {s : Bool} {j : ℕ} : d.pidx s j ≤ d.N + 1 := by
  cases s
  · exact d.blkOf_le j
  · have := d.blkOf_le j; rw [pidx_true]; omega

/-- The left end of the pair of blocks in which a position plays a role. -/
lemma Y_pidx_le {s : Bool} {j : ℕ} : d.Y (d.pidx s j) ≤ j := by
  cases s
  · exact d.Y_blkOf_le j
  · exact le_trans (d.Y_le (show d.blkOf j - 1 ≤ d.blkOf j by omega)) (d.Y_blkOf_le j)

/-- The right end of the pair of blocks in which a position plays a role. -/
lemma lt_Y_pidx {s : Bool} {j : ℕ} (hj : j < w.length) : j < d.Y (d.pidx s j + 2) := by
  have h1 := d.lt_Y_blkOf_succ hj
  have h2 := d.one_le_blkOf j
  cases s
  · show j < d.Y (d.blkOf j + 2)
    exact lt_of_lt_of_le h1 (d.Y_le (by omega))
  · show j < d.Y (d.blkOf j - 1 + 2)
    rw [show d.blkOf j - 1 + 2 = d.blkOf j + 1 from by omega]
    exact h1

/-! ## The annotated letter at a position -/

variable {S : Type} [Inhabited S] (stp : S → A → S) (ini : S)

/-- The state of the window-condition automaton of the `r`-th piece of the pair
`i` after the letters of its window up to the position `j`. -/
noncomputable def dsv (i r j : ℕ) : S :=
  (TwoWay.seg w (d.AA i r) (min (d.BB i r) (j + 1))).foldl stp ini

/-- The annotation attached to the position `j`. -/
noncomputable def datOf (j : ℕ) : Dat A Q S K :=
  (decide (j = d.Y (d.blkOf j)),
    decide (j = w.length - 1 ∧ d.Y (d.N + 1) = d.Y (d.N + 2)),
    (fun s => decide (d.pidx s j = d.N)),
    (fun s t => decide (d.AA (d.pidx s j) t.val ≤ j)),
    (fun s t => decide (d.BB (d.pidx s j) t.val ≤ j)),
    (fun s t => d.PPar (d.pidx s j) t.val),
    (fun s t => d.dsv stp ini (d.pidx s j) t.val j))

/-- The annotated letter at the position `j`. -/
noncomputable def letAt (j : ℕ) (hj : j < w.length) : Gam A Q S K :=
  ((w[j]'hj), d.datOf stp ini j)

/-- **The annotation prescribed by a chain of pieces.** -/
noncomputable def annot : List (Gam A Q S K) :=
  List.mapIdx (fun j x => ((x, d.datOf stp ini j) : Gam A Q S K)) w

omit [Inhabited S] in
@[simp] lemma length_annot : (d.annot stp ini).length = w.length := List.length_mapIdx

omit [Inhabited S] in
lemma getElem_annot {j : ℕ} (hj : j < w.length) :
    (d.annot stp ini)[j]'(by rw [length_annot]; exact hj) = d.letAt stp ini j hj := by
  exact List.getElem_mapIdx

omit [Inhabited S] in
lemma map_lt_annot : (d.annot stp ini).map lt = w := by
  refine List.ext_getElem (by simp) ?_
  intro n h1 h2
  rw [List.getElem_map]
  have hn : n < w.length := by simpa using h2
  rw [show (d.annot stp ini)[n]'(by simpa using h1) = d.letAt stp ini n hn from
    getElem_annot d stp ini hn]
  rfl

/-! ## Reading the annotated letter -/

variable {stp} {ini}

omit [Inhabited S] in
@[simp] lemma lt_letAt {j : ℕ} (hj : j < w.length) : lt (d.letAt stp ini j hj) = w[j]'hj := rfl

omit [Inhabited S] in
@[simp] lemma sb_letAt {j : ℕ} (hj : j < w.length) :
    sb (d.letAt stp ini j hj) = decide (j = d.Y (d.blkOf j)) := rfl

omit [Inhabited S] in
@[simp] lemma sa_letAt {j : ℕ} (hj : j < w.length) :
    sa (d.letAt stp ini j hj) = decide (j = w.length - 1 ∧ d.Y (d.N + 1) = d.Y (d.N + 2)) := rfl

omit [Inhabited S] in
@[simp] lemma lp_letAt {j : ℕ} (hj : j < w.length) (s : Bool) :
    lp (d.letAt stp ini j hj) s = decide (d.pidx s j = d.N) := rfl

omit [Inhabited S] in
lemma flL_letAt {j r : ℕ} (hj : j < w.length) (hr : r < 2 * K + 1) (s : Bool) :
    flL (d.letAt stp ini j hj) s r = decide (d.AA (d.pidx s j) r ≤ j) := by
  rw [flL, dif_pos hr]; rfl

omit [Inhabited S] in
lemma flR_letAt {j r : ℕ} (hj : j < w.length) (hr : r < 2 * K + 1) (s : Bool) :
    flR (d.letAt stp ini j hj) s r = decide (d.BB (d.pidx s j) r ≤ j) := by
  rw [flR, dif_pos hr]; rfl

omit [Inhabited S] in
lemma pr_letAt {j r : ℕ} (hj : j < w.length) (hr : r < 2 * K + 1) (s : Bool) :
    pr (d.letAt stp ini j hj) s r = d.PPar (d.pidx s j) r := by
  rw [pr, dif_pos hr]; rfl

lemma ds_letAt {j r : ℕ} (hj : j < w.length) (hr : r < 2 * K + 1) (s : Bool) :
    ds (d.letAt stp ini j hj) s r = d.dsv stp ini (d.pidx s j) r j := by
  rw [ds, dif_pos hr]; rfl

omit [Inhabited S] in
lemma kd_letAt {j r : ℕ} (hj : j < w.length) (hr : r < 2 * K + 1) (s : Bool) :
    kd (d.letAt stp ini j hj) s r = kdOf (d.PPar (d.pidx s j) r) := by
  rw [kd, pr_letAt d hj hr, kdOf]

omit [Inhabited S] in
lemma wb_letAt {j r : ℕ} (hj : j < w.length) (hr : r < 2 * K + 1) (s : Bool) :
    wb (d.letAt stp ini j hj) s r
      = decide (d.AA (d.pidx s j) r ≤ j ∧ j < d.BB (d.pidx s j) r) := by
  rw [wb, flL_letAt d hj hr, flR_letAt d hj hr]
  by_cases h1 : d.AA (d.pidx s j) r ≤ j <;> by_cases h2 : d.BB (d.pidx s j) r ≤ j <;>
    simp [h1, h2]; omega

omit [Inhabited S] in
lemma startfl_letAt {j r : ℕ} (hj : j < w.length) (hr : r < 2 * K + 1) (s : Bool) :
    startfl (d.letAt stp ini j hj) s r
      = decide (stCut (d.PPar (d.pidx s j) r) (d.AA (d.pidx s j) r)
          (d.BB (d.pidx s j) r) ≤ j) := by
  rw [startfl, kd_letAt d hj hr, stCut]
  split_ifs with h
  · rw [flL_letAt d hj hr]
  · rw [flR_letAt d hj hr]

omit [Inhabited S] in
lemma endfl_letAt {j r : ℕ} (hj : j < w.length) (hr : r < 2 * K + 1) (s : Bool) :
    endfl (d.letAt stp ini j hj) s r
      = decide (enCut (d.PPar (d.pidx s j) r) (d.AA (d.pidx s j) r)
          (d.BB (d.pidx s j) r) ≤ j) := by
  rw [endfl, kd_letAt d hj hr, enCut]
  split_ifs with h
  · rw [flR_letAt d hj hr]
  · rw [flL_letAt d hj hr]

end ChainData

end Chk

end TwoWay

end Lax916827Proofs.Transducers
