/-
The **last piece of the record-breaker decomposition, confined to a window that
does not reach the left end of the input.**

`TwoWay.exists_widthOut_finalProg` (`RequestProject/PartC/SnakePieceIdent.lean`)
identifies the final progress part of a run -- from the last visit to the last
record-breaking column `x_N` to the halting of the run -- with the whole run of
a window transducer.  Once `x_N` has been left for the last time the run stays
on one side of it, but that side may be either one; when it is the left one, the
window that lemma produces is the whole prefix `w[0 .. x_N)` of the input.

That is too coarse for the induction step of the snake lemma: the block function
of `RequestProject/PartC/SnakeBlock.lean` only sees the two blocks around a
record-breaker, so every piece has to be presented on a window that is contained
in those two blocks.  The final progress part *is* so contained -- after the
last visit to `x_{N-1}` the run stays strictly to the right of `x_{N-1}`
(`Walk.recSeq_lt_of_recLast_lt`, `RequestProject/PartC/SnakeConfine.lean`) --
but that information has to be put into the statement.

This file therefore repeats the three lemmas about the last piece with a lower
bound `x` on the columns that the piece visits, which becomes the left end of
its window: the window is the factor `w[x .. x_N)` instead of the prefix
`w[0 .. x_N)`, and the mirrored window transducer is given the letter to the
left of the window as its context.  The case in which the run stays to the right
of `x_N` is unchanged, since there the window is the suffix `w[x_N ..)`, which
is the last block of the decomposition.
-/
import Lax916827Proofs.Source.PartC.SnakePieceIdent
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-- **The last piece of a run that enters its window at the right end and stays
to the right of the column `x` is the whole run of the mirrored window
transducer** on the window `w[x .. y)`. -/
theorem exists_isLastPieceRev_of_run_confined (M : TwoWay A B Q) (w : List A) {a b x y : ℕ}
    (hab : a ≤ b) (hxy : x ≤ y) (hyw : y ≤ w.length) (hpa : posAt M w a = some y)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ x ≤ c ∧ c ≤ y)
    (hhalt : cfgAt M w (b + 1) = some Cfg.halt) :
    ∃ q₀ : Q, IsLastPieceRev M (w.take x) (seg w x y) (w.drop y) q₀ a (b - a) := by
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hlx : (w.take x).length = x := by rw [List.length_take]; omega
  have hlxy : (w.take x).length + (seg w x y).length = y := seg_len_add hxy hyw
  have hum : w.take x ++ seg w x y = w.take y := take_append_seg w hxy
  obtain ⟨q₀, hq₀⟩ := exists_cfg_of_posAt M w hpa
  refine ⟨q₀, ?_, ?_, ?_⟩
  · rw [hw, hum]; exact hq₀
  · intro i hi
    rw [hw]
    obtain ⟨c, hc, h1, h2⟩ := hconf (a + i) (by omega) (by omega)
    exact ⟨c, hc, by omega, by omega⟩
  · rw [hw, show a + (b - a) + 1 = b + 1 from by omega]; exact hhalt

/-- **The output of the last piece of a run that enters its window at the right
end and stays to the right of the column `x`** is a value of the width-`k`
output function of the mirrored window transducer on the reversed window
`w[x .. y)`. -/
theorem exists_widthOut_lastPieceRev_confined (M : TwoWay A B Q) (w : List A) {a b x y k : ℕ}
    (hab : a ≤ b) (hxy : x ≤ y) (hyw : y ≤ w.length) (hpa : posAt M w a = some y)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ x ≤ c ∧ c ≤ y)
    (hhalt : cfgAt M w (b + 1) = some Cfg.halt)
    (hk : Walk.VisitsLe (traj M w) a b k) :
    ∃ q₀ : Q, outRange M w a (b + 1)
      = widthOut ((mirror M).withContext (w.drop y).head? (w.take x).getLast? q₀) k
          (seg w x y).reverse := by
  obtain ⟨q₀, hp⟩ := exists_isLastPieceRev_of_run_confined M w hab hxy hyw hpa hconf hhalt
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hba : a + (b - a) = b := by omega
  refine ⟨q₀, ?_⟩
  have hk' : Walk.VisitsLe (traj M (w.take x ++ seg w x y ++ w.drop y)) a (a + (b - a)) k := by
    rw [hw, hba]; exact hk
  have h := widthOut_lastPieceRev hp hk'
  rw [hw, hba] at h
  exact h.symm

section Parts

variable {M : TwoWay A B Q} {w : List A} {T k : ℕ}

/-- **The last piece of the record-breaker decomposition, on a window confined
to the two blocks around the last record-breaking column.**  This is
`TwoWay.exists_widthOut_finalProg` with a lower bound `x` on the columns visited
after the last visit to the last record-breaking column: in the case in which
the piece runs to the *left* of that column, its window is the factor
`w[x .. x_N)` and not the whole prefix.  Taking `x = 0` gives back
`TwoWay.exists_widthOut_finalProg`; the intended value of `x` is the
record-breaking column `x_{N-1}`, to the right of which the run stays after the
last visit to it. -/
theorem exists_widthOut_finalProg_confined (hT : cfgAt M w T = some Cfg.halt)
    (hwidth : WidthLe M w k) (hk : 2 ≤ k) {x : ℕ} (hx : x ≤ rbCol M w (rbN M w))
    (hlow : ∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w → x ≤ traj M w t) :
    ∃ q₀ : Q,
      outRange M w (rbLast M w (rbN M w)) (haltT M w)
          = widthOut (M.withContext (w.take (rbCol M w (rbN M w))).getLast? none q₀) (k - 1)
              (w.drop (rbCol M w (rbN M w)))
        ∨ outRange M w (rbLast M w (rbN M w)) (haltT M w)
          = widthOut ((mirror M).withContext (w.drop (rbCol M w (rbN M w))).head?
              (w.take x).getLast? q₀) (k - 1) (seg w x (rbCol M w (rbN M w))).reverse := by
  classical
  have hT1 : 1 ≤ T := one_le_of_halt hT
  have hTe : endT M w = T - 1 := endT_eq M w hT
  have hTh : haltT M w = T := haltT_eq M w hT
  have hwalk := isWalk_trajE M w hT
  have haE : rbLast M w (rbN M w) ≤ endT M w := rbLast_le_endT (rbN M w)
  have hpa : traj M w (rbLast M w (rbN M w)) = rbCol M w (rbN M w) := pos_rbLast (rbN M w)
  have hposA : posAt M w (rbLast M w (rbN M w)) = some (rbCol M w (rbN M w)) := by
    rw [posAt_traj hT haE, hpa]
  have hcw : rbCol M w (rbN M w) ≤ w.length := posAt_le_length M w hposA
  have hhalt : cfgAt M w (endT M w + 1) = some Cfg.halt := by
    rw [hTe, show T - 1 + 1 = T from by omega]; exact hT
  have hout : haltT M w = endT M w + 1 := by rw [hTh, hTe]; omega
  have hvis : ∀ t, rbLast M w (rbN M w) < t → t ≤ endT M w →
      traj M w t ≠ rbCol M w (rbN M w) := by
    intro t h1 h2 h3
    have h5 : t ≤ Walk.lastV (traj M w) 0 (endT M w) (rbCol M w (rbN M w)) :=
      Walk.le_lastV ⟨Nat.zero_le _, h2, h3⟩
    rw [← rbLast_eq_lastV] at h5
    omega
  have hkw := finalProg_visitsLe hT hwidth hk
  have hside : (∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w →
        rbCol M w (rbN M w) ≤ traj M w t) ∨
      (∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w →
        traj M w t ≤ rbCol M w (rbN M w)) := by
    rcases eq_or_lt_of_le haE with heq | hlt
    · left
      intro t h1 h2
      have ht : t = rbLast M w (rbN M w) := by omega
      rw [ht, hpa]
    · rcases Nat.lt_or_ge (rbCol M w (rbN M w)) (traj M w (rbLast M w (rbN M w) + 1)) with
        hgt | hle
      · left
        intro t h1 h2
        rcases eq_or_lt_of_le h1 with h | h
        · rw [← h, hpa]
        · by_contra hcon
          push_neg at hcon
          obtain ⟨τ, hτ1, hτ2, hτ3⟩ := Walk.exists_eq_between hwalk
            (show rbLast M w (rbN M w) + 1 ≤ t from by omega) h2
            (Or.inr ⟨le_of_lt hcon, le_of_lt hgt⟩)
          exact hvis τ (by omega) (by omega) hτ3
      · have hne := hvis (rbLast M w (rbN M w) + 1) (by omega) (by omega)
        have hlt' : traj M w (rbLast M w (rbN M w) + 1) < rbCol M w (rbN M w) := by omega
        right
        intro t h1 h2
        rcases eq_or_lt_of_le h1 with h | h
        · rw [← h, hpa]
        · by_contra hcon
          push_neg at hcon
          obtain ⟨τ, hτ1, hτ2, hτ3⟩ := Walk.exists_eq_between hwalk
            (show rbLast M w (rbN M w) + 1 ≤ t from by omega) h2
            (Or.inl ⟨le_of_lt hlt', le_of_lt hcon⟩)
          exact hvis τ (by omega) (by omega) hτ3
  rcases hside with hside | hside
  · obtain ⟨q₀, h⟩ := exists_widthOut_lastPiece M w haE hcw hposA
      (fun t h1 h2 => ⟨traj M w t, posAt_traj hT h2, hside t h1 h2⟩) hhalt hkw
    exact ⟨q₀, Or.inl (by rw [hout]; exact h)⟩
  · obtain ⟨q₀, h⟩ := exists_widthOut_lastPieceRev_confined M w haE hx hcw hposA
      (fun t h1 h2 => ⟨traj M w t, posAt_traj hT h2, hlow t h1 h2, hside t h1 h2⟩) hhalt hkw
    exact ⟨q₀, Or.inr (by rw [hout]; exact h)⟩

end Parts

end TwoWay

end Lax916827Proofs.Transducers
