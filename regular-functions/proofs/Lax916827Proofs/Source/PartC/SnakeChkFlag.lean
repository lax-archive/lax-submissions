/-
**The cuts at which the pieces of an accepted annotation start and end.**

A piece of the kind `1` or `3` starts at the left end of its window and a piece
of the kind `2` or `4` starts at its right end
(`Transducers.TwoWay.Chk.stCut`); symmetrically for the cut at which a piece
ends (`Transducers.TwoWay.Chk.enCut`).  The checking automaton of stage 1 of the
induction step of the book's snake lemma verifies the chain condition on those
cuts through the two derived flags `Transducers.TwoWay.Chk.startfl` and
`Transducers.TwoWay.Chk.endfl`.  This file identifies the cut cut out by those
flags with `stCut` and `enCut`, and reads off the three chain conditions: the
first piece of a pair starts at the boundary between its two blocks, consecutive
pieces meet, and the last piece of a pair which is not the last pair ends at the
right end of the pair.
-/
import Lax916827Proofs.Source.PartC.SnakeChkStruct
import Lax916827Proofs.Source.PartC.SnakeChkData
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open BlockIdx RegPair

variable {A B Q S : Type} {K : ℕ}

variable [Inhabited S] {M : TwoWay A B Q} {stp : S → A → S} {ini : S}
  {acc : PieceParam A Q → S → Prop} {u : List (Gam A Q S K)}

/-- The flag marking the starting cut of the `r`-th piece of the pair `i`, at
the position `j`. -/
noncomputable def stflAt (u : List (Gam A Q S K)) (i r j : ℕ) : Bool :=
  if h : j < u.length then startfl (u[j]'h) (rol u i j) r else false

/-- The flag marking the ending cut of the `r`-th piece of the pair `i`, at the
position `j`. -/
noncomputable def enflAt (u : List (Gam A Q S K)) (i r j : ℕ) : Bool :=
  if h : j < u.length then endfl (u[j]'h) (rol u i j) r else false

lemma kd_eq_kdOf (hu : u ∈ ChkLang M K stp ini acc) {i r : ℕ} :
    ∀ j, ∀ hj : j < u.length, bY u i ≤ j → j < bY u (i + 2) →
      kd (u[j]'hj) (rol u i j) r = kdOf (pPar u i r) := by
  intro j hj h1 h2
  rw [kd, pr_eq_pPar (i := i) (r := r) hu j hj h1 h2, kdOf]

/-- **The starting cut of a piece slot** is the one cut out by the flag that the
checking automaton uses. -/
lemma stflAt_cut (hu : u ∈ ChkLang M K stp ini acc) {i r : ℕ} :
    cutOf (stflAt u i r) (bY u i) (bY u (i + 2))
      = stCut (pPar u i r) (aCut u i r) (bCut u i r) := by
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  rw [stCut]
  split_ifs with hk
  · rw [aCut]
    refine cutOf_congr ?_
    intro j h1 h2
    have hj : j < u.length := by omega
    rw [stflAt, dif_pos hj, flLat, dif_pos hj, startfl, kd_eq_kdOf hu j hj h1 h2, if_pos hk]
  · rw [bCut]
    refine cutOf_congr ?_
    intro j h1 h2
    have hj : j < u.length := by omega
    rw [stflAt, dif_pos hj, flRat, dif_pos hj, startfl, kd_eq_kdOf hu j hj h1 h2, if_neg hk]

/-- **The ending cut of a piece slot** is the one cut out by the flag that the
checking automaton uses. -/
lemma enflAt_cut (hu : u ∈ ChkLang M K stp ini acc) {i r : ℕ} :
    cutOf (enflAt u i r) (bY u i) (bY u (i + 2))
      = enCut (pPar u i r) (aCut u i r) (bCut u i r) := by
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  rw [enCut]
  split_ifs with hk
  · rw [bCut]
    refine cutOf_congr ?_
    intro j h1 h2
    have hj : j < u.length := by omega
    rw [enflAt, dif_pos hj, flRat, dif_pos hj, endfl, kd_eq_kdOf hu j hj h1 h2, if_pos hk]
  · rw [aCut]
    refine cutOf_congr ?_
    intro j h1 h2
    have hj : j < u.length := by omega
    rw [enflAt, dif_pos hj, flLat, dif_pos hj, endfl, kd_eq_kdOf hu j hj h1 h2, if_neg hk]

/-! ## The chain conditions on the cuts -/

/-- **The first piece of a pair starts at the boundary between its two
blocks.** -/
lemma cut_zero_eq (hu : u ∈ ChkLang M K stp ini acc) {i : ℕ} :
    stCut (pPar u i 0) (aCut u i 0) (bCut u i 0) = bY u (i + 1) := by
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  have hm1 : bY u i ≤ bY u (i + 1) := bY_mono (by omega)
  have hm2 : bY u (i + 1) ≤ bY u (i + 2) := bY_mono (by omega)
  rw [← stflAt_cut hu]
  refine cutOf_eq_of _ hm1 hm2 ?_ ?_
  · intro j h1 h2
    have hj : j < u.length := by omega
    have hrf : rol u i j = false := by rw [rol, decide_eq_false_iff_not]; omega
    rw [stflAt, dif_pos hj, hrf]
    exact (letOK_at hu hj).2.2.2.2.2.2.2.2.1
  · intro j h1 h2
    have hj : j < u.length := by omega
    have hrt : rol u i j = true := by rw [rol, decide_eq_true_eq]; omega
    rw [stflAt, dif_pos hj, hrt]
    exact (letOK_at hu hj).2.2.2.2.2.2.2.2.2.1

/-- **Consecutive pieces of a pair meet at a common cut.** -/
lemma cut_step_eq (hu : u ∈ ChkLang M K stp ini acc) {i r : ℕ} (hr : r < 2 * K) :
    enCut (pPar u i r) (aCut u i r) (bCut u i r)
      = stCut (pPar u i (r + 1)) (aCut u i (r + 1)) (bCut u i (r + 1)) := by
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  rw [← enflAt_cut hu, ← stflAt_cut hu]
  refine cutOf_congr ?_
  intro j h1 h2
  have hj : j < u.length := by omega
  rw [enflAt, dif_pos hj, stflAt, dif_pos hj]
  exact (letOK_at hu hj).2.2.2.2.2.2.2.1 _ r (by omega)

/-- **The last piece of a pair which is not the last pair ends at the right end
of the pair.** -/
lemma cut_last_eq (hu : u ∈ ChkLang M K stp ini acc) (h0 : 0 < u.length) {i : ℕ}
    (hi : i < nPair u) :
    enCut (pPar u i (2 * K)) (aCut u i (2 * K)) (bCut u i (2 * K)) = bY u (i + 2) := by
  have hlen2 : bY u (i + 2) ≤ u.length := bY_le_length _
  rw [← enflAt_cut hu]
  refine cutOf_eq_hi ?_
  intro j h1 h2
  have hj : j < u.length := by omega
  rw [enflAt, dif_pos hj]
  refine (letOK_at hu hj).2.2.2.2.2.2.2.2.2.2.1 _ ?_
  rw [lp_eq_lpOf hu j hj h1 h2]
  exact lpOf_of_lt hu h0 hi

end Chk

end TwoWay

end Lax916827Proofs.Transducers
