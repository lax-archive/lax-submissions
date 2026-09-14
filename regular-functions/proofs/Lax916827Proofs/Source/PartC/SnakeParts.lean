/-
The explicit decomposition of a halting run of width at most `k` into pieces of
width at most `k - 1`, each of which is the whole run of a window transducer.

`RequestProject/PartC/SnakeLoop.lean` proves the *existence* of a decomposition
of a halting run of width at most `k` into finitely many consecutive pieces of
width at most `k - 1` (`TwoWay.run_splitsInto_pred`).  For the induction step of
the book's snake lemma that is not enough: the rational function of the book's
first stage has to *mark* the cutting points in the input, so they must be named
and their positions in the input must be known.

This file therefore assembles the named decomposition:

* the run is cut at the first and the last visit to each record-breaking column
  `X i` (`RequestProject/PartC/SnakeRec.lean`);
* the *loop part* of `X i` -- between the first and the last visit to `X i` --
  is cut at the successive visits to `X i` into at most `k` *excursions*
  (`RequestProject/PartC/SnakeExc.lean`);
* each excursion is cut in two at the first visit to the column furthest from
  `X i`;
* the *progress part* of `X i` runs from the last visit to `X i` to the first
  visit to `X (i+1)`, and the last progress part runs to the end of the run.

`TwoWay.runOut_eq_partsOut` states that the output of the run is the
concatenation of the outputs of these pieces, in this order, and the remaining
theorems of the file identify each piece with the whole run of a window
transducer on a factor of the input (`TwoWay.IsPiece`, `TwoWay.IsPieceRev`,
`TwoWay.IsLastPiece` of `RequestProject/PartC/SnakePiece.lean` and
`RequestProject/PartC/SnakePieceRev.lean`), which is what makes the induction
hypothesis of the snake lemma applicable to it.
-/
import Lax916827Proofs.Source.PartC.SnakeExc
import Lax916827Proofs.Source.PartC.SnakeConfine
import Lax916827Proofs.Source.PartC.SnakePieceRev
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-! ### Factors of the input -/

/-- The factor of `w` between the cuts `x` and `y`. -/
def seg (w : List A) (x y : ℕ) : List A := (w.drop x).take (y - x)

lemma take_seg_drop (w : List A) {x y : ℕ} (h : x ≤ y) :
    w.take x ++ seg w x y ++ w.drop y = w := by
  have hd : w.drop y = (w.drop x).drop (y - x) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [seg, List.append_assoc, hd, List.take_append_drop, List.take_append_drop]

lemma seg_length (w : List A) {x y : ℕ} (h : y ≤ w.length) :
    (seg w x y).length = y - x := by
  rw [seg, List.length_take, List.length_drop]
  omega

lemma drop_eq_seg_append (w : List A) {x y : ℕ} (h : x ≤ y) :
    w.drop x = seg w x y ++ w.drop y := by
  have := take_seg_drop w h
  have hx : w.take x ++ (seg w x y ++ w.drop y) = w.take x ++ w.drop x := by
    rw [List.take_append_drop, ← List.append_assoc, this]
  exact (List.append_cancel_left hx).symm

lemma take_append_seg (w : List A) {x y : ℕ} (h : x ≤ y) :
    w.take x ++ seg w x y = w.take y := by
  have h1 : w.take x ++ seg w x y ++ w.drop y = w.take y ++ w.drop y := by
    rw [take_seg_drop w h, List.take_append_drop]
  exact List.append_cancel_right h1

/-! ### The halting time -/

open scoped Classical in
/-- The time at which the run of `M` on `w` halts (`0` if it does not halt). -/
noncomputable def haltT (M : TwoWay A B Q) (w : List A) : ℕ :=
  if h : ∃ T, cfgAt M w T = some Cfg.halt then h.choose else 0

lemma cfgAt_haltT (M : TwoWay A B Q) (w : List A) (h : ∃ T, cfgAt M w T = some Cfg.halt) :
    cfgAt M w (haltT M w) = some Cfg.halt := by
  classical
  rw [haltT, dif_pos h]
  exact h.choose_spec

lemma haltT_eq (M : TwoWay A B Q) (w : List A) {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) :
    haltT M w = T :=
  halt_time_unique M w (cfgAt_haltT M w ⟨T, hT⟩) hT

lemma runOut_eq_outRange (M : TwoWay A B Q) (w : List A)
    (h : ∃ T, cfgAt M w T = some Cfg.halt) : runOut M w = outRange M w 0 (haltT M w) := by
  classical
  rw [runOut, dif_pos h, haltT, dif_pos h]

/-! ### The named cutting points of a run -/

variable (M : TwoWay A B Q) (w : List A)

/-- The last time of the run of `M` on `w` at which the head is on the input. -/
noncomputable def endT : ℕ := haltT M w - 1

/-- The `i`-th record-breaking column of the run. -/
noncomputable def rbCol (i : ℕ) : ℕ := Walk.recSeq (traj M w) 0 (endT M w) i

/-- The number of record-breaking columns of the run, minus one. -/
noncomputable def rbN : ℕ := Walk.recN (traj M w) 0 (endT M w)

/-- The time of the first visit to the `i`-th record-breaking column. -/
noncomputable def rbFirst (i : ℕ) : ℕ := Walk.recFirst (traj M w) 0 (endT M w) i

/-- The time of the last visit to the `i`-th record-breaking column. -/
noncomputable def rbLast (i : ℕ) : ℕ := Walk.recLast (traj M w) 0 (endT M w) i

/-- The time of the `j`-th visit to the `i`-th record-breaking column: the
cutting points of the loop part of `X i` into excursions. -/
noncomputable def excT (i j : ℕ) : ℕ :=
  Walk.visSeq (traj M w) (rbCol M w i) (rbLast M w i) (rbFirst M w i) j

/-- The cutting point of the `j`-th excursion of the `i`-th record-breaking
column into its two halves: the first visit to the column furthest away from
the record-breaking column. -/
noncomputable def excS (i j : ℕ) : ℕ :=
  Walk.excSplit (traj M w) (excT M w i j) (excT M w i (j + 1))

/-- The column furthest away from the `i`-th record-breaking column that is
reached by its `j`-th excursion. -/
noncomputable def excC (i j : ℕ) : ℕ :=
  Walk.excCol (traj M w) (excT M w i j) (excT M w i (j + 1))

/-- The time at which the progress part of the `i`-th record-breaking column
ends: the first visit to the next record-breaking column, or the end of the run
for the last record-breaker. -/
noncomputable def progEnd (i : ℕ) : ℕ :=
  if i < rbN M w then rbFirst M w (i + 1) else haltT M w

/-! ### The output of the run as the concatenation of the outputs of the pieces -/

/-- The output of the loop part of the `i`-th record-breaking column, presented
as the concatenation of the outputs of the two halves of its `k` excursions
(the excursions after the last one are empty). -/
noncomputable def loopOut (k i : ℕ) : List B :=
  (List.range k).flatMap fun j =>
    outRange M w (excT M w i j) (excS M w i j) ++ outRange M w (excS M w i j) (excT M w i (j + 1))

/-- The output of the `i`-th block of the decomposition: the loop part of the
`i`-th record-breaking column followed by its progress part. -/
noncomputable def blockOut (k i : ℕ) : List B :=
  loopOut M w k i ++ outRange M w (rbLast M w i) (progEnd M w i)

/-! ### Elementary facts about the cutting points -/

lemma endT_eq {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) : endT M w = T - 1 := by
  rw [endT, haltT_eq M w hT]

lemma isWalk_trajE {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) :
    Walk.IsWalk (traj M w) (endT M w) := by
  rw [endT_eq M w hT]; exact isWalk_traj M w hT

lemma visitsLe_endT {T k : ℕ} (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w k) :
    Walk.VisitsLe (traj M w) 0 (endT M w) k := by
  rw [endT_eq M w hT]; exact visitsLe_of_widthLe M w hT hwidth

variable {M w}

lemma pos_rbFirst (i : ℕ) : traj M w (rbFirst M w i) = rbCol M w i :=
  Walk.pos_firstV (Walk.visited_recSeq (Nat.zero_le _) i)

lemma pos_rbLast (i : ℕ) : traj M w (rbLast M w i) = rbCol M w i :=
  Walk.pos_lastV (Walk.visited_recSeq (Nat.zero_le _) i)

lemma rbFirst_le_rbLast (i : ℕ) : rbFirst M w i ≤ rbLast M w i :=
  Walk.recFirst_le_recLast (Nat.zero_le _) i

lemma rbLast_le_endT (i : ℕ) : rbLast M w i ≤ endT M w :=
  Walk.recLast_le (Nat.zero_le _) i

lemma visitsLe_loop {T k : ℕ} (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w k)
    (i : ℕ) : Walk.VisitsLe (traj M w) (rbFirst M w i) (rbLast M w i) k :=
  (visitsLe_endT M w hT hwidth).mono (Nat.zero_le _) (rbLast_le_endT i)

lemma excT_zero (i : ℕ) : excT M w i 0 = rbFirst M w i := rfl

lemma excT_mono_step (i j : ℕ) : excT M w i j ≤ excT M w i (j + 1) :=
  Walk.visSeq_mono_step (rbFirst_le_rbLast i) j

lemma excT_le (i j : ℕ) : excT M w i j ≤ rbLast M w i :=
  Walk.visSeq_le (rbFirst_le_rbLast i) j

lemma pos_excT (i j : ℕ) : traj M w (excT M w i j) = rbCol M w i :=
  Walk.pos_visSeq (pos_rbFirst i) (pos_rbLast i) j

lemma excT_stab {T k : ℕ} (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w k) (i : ℕ) :
    excT M w i k = rbLast M w i :=
  Walk.visSeq_stab (rbFirst_le_rbLast i) (pos_rbFirst i) (pos_rbLast i)
    (visitsLe_loop hT hwidth i)

lemma excS_bounds (i j : ℕ) :
    excT M w i j ≤ excS M w i j ∧ excS M w i j ≤ excT M w i (j + 1) :=
  Walk.excSplit_bounds (excT_mono_step i j)

/-! ### The output of the run is the concatenation of the outputs of the pieces -/

/-- The output over a monotone sequence of times telescopes. -/
lemma outRange_flatMap_range (M : TwoWay A B Q) (w : List A) (v : ℕ → ℕ)
    (hv : ∀ j, v j ≤ v (j + 1)) :
    ∀ n, (List.range n).flatMap (fun j => outRange M w (v j) (v (j + 1)))
      = outRange M w (v 0) (v n) := by
  have hmono : Monotone v := monotone_nat_of_le_succ hv
  intro n
  induction n with
  | zero => simp [outRange]
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact (outRange_split M w (hmono (Nat.zero_le n)) (hv n)).symm

/-- The output of the loop part of a record-breaking column is the
concatenation of the outputs of the two halves of its excursions. -/
lemma loopOut_eq {T k : ℕ} (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w k) (i : ℕ) :
    loopOut M w k i = outRange M w (rbFirst M w i) (rbLast M w i) := by
  have hfun : (fun j => outRange M w (excT M w i j) (excS M w i j) ++
      outRange M w (excS M w i j) (excT M w i (j + 1)))
      = fun j => outRange M w (excT M w i j) (excT M w i (j + 1)) := by
    funext j
    exact (outRange_split M w (excS_bounds i j).1 (excS_bounds i j).2).symm
  rw [loopOut, hfun, outRange_flatMap_range M w _ (excT_mono_step i) k, excT_zero,
    excT_stab hT hwidth i]

/-- The concatenation of the outputs of the loop parts and of the progress
parts, written as a flattened list. -/
lemma loopProgOut_eq_flatten (M : TwoWay A B Q) (w : List A) (p : ℕ → ℕ) (a b : ℕ) :
    ∀ (n i : ℕ), loopProgOut M w p a b n i =
      ((List.range n).map (fun j =>
        outRange M w (Walk.recFirst p a b (i + j)) (Walk.recLast p a b (i + j)) ++
          outRange M w (Walk.recLast p a b (i + j))
            (Walk.recFirst p a b (i + j + 1)))).flatten ++
        (outRange M w (Walk.recFirst p a b (i + n)) (Walk.recLast p a b (i + n)) ++
          outRange M w (Walk.recLast p a b (i + n)) b) := by
  intro n
  induction n with
  | zero => intro i; simp [loopProgOut]
  | succ n ih =>
      intro i
      rw [loopProgOut, ih (i + 1), List.range_succ_eq_map, List.map_cons, List.map_map,
        List.flatten_cons]
      simp only [Function.comp_def, Nat.add_zero, Nat.succ_eq_add_one]
      have hshift : ∀ j : ℕ, i + 1 + j = i + (j + 1) := by intro j; omega
      simp only [hshift, List.append_assoc]

/-- **The output of a halting run of width at most `k` is the concatenation of
the outputs of the pieces of its record-breaker decomposition.** -/
theorem runOut_eq_partsOut {T k : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    (hwidth : WidthLe M w k) :
    runOut M w = (List.range (rbN M w + 1)).flatMap (blockOut M w k) := by
  have hex : ∃ T, cfgAt M w T = some Cfg.halt := ⟨T, hT⟩
  have hTh : haltT M w = T := haltT_eq M w hT
  have hTe : endT M w = T - 1 := endT_eq M w hT
  have hN : rbN M w = Walk.recN (traj M w) 0 (T - 1) := by rw [rbN, hTe]
  set N := rbN M w with hNdef
  have h0 : runOut M w = outRange M w 0 T := by
    rw [runOut_eq_outRange M w hex, hTh]
  have h1 := runOutput_eq_loopProgOut M w hT
  have h2 := loopProgOut_eq_flatten M w (traj M w) 0 (T - 1) N 0
  have hrf : ∀ j, Walk.recFirst (traj M w) 0 (T - 1) j = rbFirst M w j := by
    intro j; rw [rbFirst, hTe]
  have hrl : ∀ j, Walk.recLast (traj M w) 0 (T - 1) j = rbLast M w j := by
    intro j; rw [rbLast, hTe]
  simp only [hrf, hrl, Nat.zero_add] at h2
  rw [h0, h1, ← hN, h2]
  rw [List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hpre : (List.range N).flatMap (blockOut M w k)
      = ((List.range N).map (fun j =>
          outRange M w (rbFirst M w j) (rbLast M w j) ++
            outRange M w (rbLast M w j) (rbFirst M w (j + 1)))).flatten := by
    rw [List.flatMap_def]
    congr 1
    refine List.map_congr_left ?_
    intro j hj
    have hjN : j < N := List.mem_range.1 hj
    rw [blockOut, loopOut_eq hT hwidth j, progEnd, if_pos hjN]
  have hlast : blockOut M w k N
      = (outRange M w (rbFirst M w N) (rbLast M w N) ++
          outRange M w (rbLast M w N) (T - 1)) ++ outRange M w (T - 1) T := by
    rw [blockOut, loopOut_eq hT hwidth N, progEnd, if_neg (lt_irrefl N), hTh,
      List.append_assoc]
    congr 1
    have hle1 : rbLast M w N ≤ T - 1 := by
      have := rbLast_le_endT (M := M) (w := w) N
      omega
    have hle2 : T - 1 ≤ T := Nat.sub_le _ _
    exact outRange_split M w hle1 hle2
  rw [hpre, hlast]
  simp [List.append_assoc]

/-! ### The pieces have smaller width -/

/-- A piece of a walk that consists of a single time visits every column at
most once. -/
lemma visitsLe_self (p : ℕ → ℕ) (a : ℕ) : Walk.VisitsLe p a a 1 := by
  classical
  intro y s hs
  have hsub : s ⊆ {a} := by
    intro t ht
    simp only [Finset.mem_singleton]
    have := hs t ht
    omega
  simpa using Finset.card_le_card hsub

lemma visitsLe_weaken {p : ℕ → ℕ} {a b k k' : ℕ} (h : Walk.VisitsLe p a b k) (hk : k ≤ k') :
    Walk.VisitsLe p a b k' := fun y s hs => le_trans (h y s hs) hk

/-- The two halves of an excursion of a record-breaking column visit every
column at most `k - 1` times. -/
theorem excHalves_visitsLe {T k : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    (hwidth : WidthLe M w k) (hk : 2 ≤ k) (i j : ℕ) :
    Walk.VisitsLe (traj M w) (excT M w i j) (excS M w i j) (k - 1) ∧
      Walk.VisitsLe (traj M w) (excS M w i j) (excT M w i (j + 1)) (k - 1) := by
  rcases eq_or_lt_of_le (excT_mono_step (M := M) (w := w) i j) with heq | hlt
  · have hs : excS M w i j = excT M w i j := by
      have h1 := (excS_bounds (M := M) (w := w) i j).1
      have h2 := (excS_bounds (M := M) (w := w) i j).2
      omega
    have h1 : (1 : ℕ) ≤ k - 1 := by omega
    rw [hs, ← heq]
    exact ⟨visitsLe_weaken (visitsLe_self _ _) h1, visitsLe_weaken (visitsLe_self _ _) h1⟩
  · refine Walk.exc_halves_visitsLe (isWalk_trajE M w hT) ?_ hlt ?_ (pos_excT i j)
      (pos_excT i (j + 1)) ?_
    · exact le_trans (excT_le i (j + 1)) (rbLast_le_endT i)
    · exact (visitsLe_endT M w hT hwidth).mono (Nat.zero_le _)
        (le_trans (excT_le i (j + 1)) (rbLast_le_endT i))
    · intro t h1 h2
      exact Walk.visSeq_no_mid h1 h2

/-- The progress part of a record-breaking column that is not the last one
visits every column at most `k - 1` times. -/
theorem prog_visitsLe {T k : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    (hwidth : WidthLe M w k) (hk : 2 ≤ k) {i : ℕ} (hi : i < rbN M w) :
    Walk.VisitsLe (traj M w) (rbLast M w i) (rbFirst M w (i + 1)) (k - 1) := by
  refine Walk.recProgress_visitsLe (isWalk_trajE M w hT) (Nat.zero_le _) (le_refl _)
    (visitsLe_endT M w hT hwidth) hk ?_
  exact Walk.not_recStable_of_lt_recN hi

/-- The last progress part -- from the last visit to the last record-breaking
column to the end of the run -- visits every column at most `k - 1` times. -/
theorem finalProg_visitsLe {T k : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    (hwidth : WidthLe M w k) (hk : 2 ≤ k) :
    Walk.VisitsLe (traj M w) (rbLast M w (rbN M w)) (endT M w) (k - 1) := by
  refine Walk.final_progress_visitsLe (isWalk_trajE M w hT) (le_refl _)
    (visitsLe_endT M w hT hwidth) hk (Walk.visited_recSeq (Nat.zero_le _) (rbN M w)) ?_ ?_
  · intro t _ _
    rw [traj_zero]
    exact Nat.zero_le _
  · exact Walk.recStable_recN (isWalk_trajE M w hT) (Nat.zero_le _) (le_refl _)

end TwoWay

end Lax916827Proofs.Transducers
