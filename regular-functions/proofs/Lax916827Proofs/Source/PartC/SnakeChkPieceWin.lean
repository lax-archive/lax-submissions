/-
**From a piece of a run to the window condition of stage 1.**

`RequestProject/PartC/SnakePiece.lean`, `RequestProject/PartC/SnakePieceRev.lean`
and `RequestProject/PartC/SnakePieceIdent.lean` identify a piece of a run with
the whole run of a window transducer and read off its *output*.  For the chain
of pieces of stage 1 (`Transducers.TwoWay.Chk.ChainData`) what is needed instead
is the *window condition* `Transducers.TwoWay.Chk.WinCond`: the local property of
the window and of the parameters of the piece that the checking automaton
verifies.

This file derives the window condition of each of the four kinds of piece from
the same hypotheses on the run, and -- unlike the existential statements of
`RequestProject/PartC/SnakePieceIdent.lean` -- it names the two states of the
piece: they are the states of the run at the two ends of the piece
(`Transducers.TwoWay.qAt`).  That is what makes the pieces chain: the exit state
of a piece is literally the entry state of the next one.
-/
import Lax916827Proofs.Source.PartC.SnakeChkWin
import Lax916827Proofs.Source.PartC.SnakeFinalConf
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-! ## The state of the run at a given time -/

/-- The state of the run of `M` on `w` at time `t`; the initial state if the run
is already over. -/
def qAt (M : TwoWay A B Q) (w : List A) (t : ℕ) : Q := (stateAt M w t).getD M.init

/-- At a time at which the head is at the column `x`, the configuration of the
run is determined. -/
lemma cfgAt_qAt (M : TwoWay A B Q) (w : List A) {t x : ℕ} (hx : posAt M w t = some x) :
    cfgAt M w t = some (Cfg.conf (w.take x) (qAt M w t) (w.drop x)) := by
  obtain ⟨q, hq⟩ := exists_cfg_of_posAt M w hx
  have hst : stateAt M w t = some q := by rw [stateAt, hq]; rfl
  rw [qAt, hst]
  exact hq

lemma qAt_zero (M : TwoWay A B Q) (w : List A) : qAt M w 0 = M.init := by
  have h : stateAt M w 0 = some M.init := by rw [stateAt, cfgAt_zero]; rfl
  rw [qAt, h]
  rfl

/-! ## The four kinds of piece -/

namespace Chk

/-- **The window condition of a piece of the kind `1`**: a piece of the run that
crosses its window from left to right. -/
theorem winCond_kind_one (M : TwoWay A B Q) (w : List A) {s e x y k : ℕ}
    (hse : s ≤ e) (hxy : x ≤ y) (hyw : y ≤ w.length)
    (hpa : posAt M w s = some x) (hpb : posAt M w e = some y)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∃ c, posAt M w t = some c ∧ x ≤ c ∧ c ≤ y)
    (hearly : ∀ t, s ≤ t → t < e → posAt M w t ≠ some y)
    (hk : Walk.VisitsLe (traj M w) s e k) :
    seg w x y ∈ WinCond M k ((1 : Fin 5), (w.take x).getLast?, (w.drop y).head?,
      some (qAt M w s, qAt M w e)) := by
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hxw : x ≤ w.length := le_trans hxy hyw
  have hlx : (w.take x).length = x := by rw [List.length_take]; omega
  have hlxy : (w.take x).length + (seg w x y).length = y := seg_len_add hxy hyw
  have hmz : seg w x y ++ w.drop y = w.drop x := (drop_eq_seg_append w hxy).symm
  have hum : w.take x ++ seg w x y = w.take y := take_append_seg w hxy
  have hp : IsPiece M (w.take x) (seg w x y) (w.drop y) (qAt M w s) (qAt M w e) s (e - s) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hw, hmz]; exact cfgAt_qAt M w hpa
    · intro i hi
      rw [hw]
      obtain ⟨c, hc, h1, h2⟩ := hconf (s + i) (by omega) (by omega)
      exact ⟨c, hc, by omega, by omega⟩
    · intro i hi hcon
      rw [hw, hum] at hcon
      exact hearly (s + i) (by omega) (by omega) (posAt_of_cfgAt M w (by rw [hcon]) hyw)
    · rw [hw, hum, show s + (e - s) = e from by omega]; exact cfgAt_qAt M w hpb
  have hk' : Walk.VisitsLe (traj M (w.take x ++ seg w x y ++ w.drop y)) s (s + (e - s)) k := by
    rw [hw, show s + (e - s) = e from by omega]; exact hk
  refine ⟨⟨e - s, ?_⟩, ⟨e - s + 1, stopRight_halt hp⟩, widthLe_stopRight hp hk'⟩
  rw [cfgAt_stopRight hp (e - s) (le_refl _)]
  exact hp.cfgAt_window_last

/-- **The window condition of a piece of the kind `2`**: a piece of the run that
crosses its window from right to left. -/
theorem winCond_kind_two (M : TwoWay A B Q) (w : List A) {s e x y k : ℕ}
    (hse : s ≤ e) (hxy : x ≤ y) (hyw : y ≤ w.length)
    (hpa : posAt M w s = some y) (hpb : posAt M w e = some x)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∃ c, posAt M w t = some c ∧ x ≤ c ∧ c ≤ y)
    (hearly : ∀ t, s ≤ t → t < e → posAt M w t ≠ some x)
    (hk : Walk.VisitsLe (traj M w) s e k) :
    seg w x y ∈ WinCond M k ((2 : Fin 5), (w.take x).getLast?, (w.drop y).head?,
      some (qAt M w s, qAt M w e)) := by
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hxw : x ≤ w.length := le_trans hxy hyw
  have hlx : (w.take x).length = x := by rw [List.length_take]; omega
  have hlxy : (w.take x).length + (seg w x y).length = y := seg_len_add hxy hyw
  have hmz : seg w x y ++ w.drop y = w.drop x := (drop_eq_seg_append w hxy).symm
  have hum : w.take x ++ seg w x y = w.take y := take_append_seg w hxy
  have hp : IsPieceRev M (w.take x) (seg w x y) (w.drop y) (qAt M w s) (qAt M w e) s (e - s) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hw, hum]; exact cfgAt_qAt M w hpa
    · intro i hi
      rw [hw]
      obtain ⟨c, hc, h1, h2⟩ := hconf (s + i) (by omega) (by omega)
      exact ⟨c, hc, by omega, by omega⟩
    · intro i hi hcon
      rw [hw, hmz] at hcon
      exact hearly (s + i) (by omega) (by omega) (posAt_of_cfgAt M w (by rw [hcon]) hxw)
    · rw [hw, hmz, show s + (e - s) = e from by omega]; exact cfgAt_qAt M w hpb
  have hk' : Walk.VisitsLe (traj M (w.take x ++ seg w x y ++ w.drop y)) s (s + (e - s)) k := by
    rw [hw, show s + (e - s) = e from by omega]; exact hk
  exact ⟨⟨e - s, hp.cfgAt_last⟩, ⟨e - s + 1, pieceRev_halt hp⟩, widthLe_pieceRev hp hk'⟩

/-- **The window condition of the last piece, of the kind `3`**: the run halts
inside the window, which it enters at the left end. -/
theorem winCond_kind_three (M : TwoWay A B Q) (w : List A) {s e x k : ℕ}
    (hse : s ≤ e) (hxw : x ≤ w.length) (hpa : posAt M w s = some x)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∃ c, posAt M w t = some c ∧ x ≤ c)
    (hhalt : cfgAt M w (e + 1) = some Cfg.halt)
    (hk : Walk.VisitsLe (traj M w) s e k) :
    seg w x w.length ∈ WinCond M k ((3 : Fin 5), (w.take x).getLast?, none,
      some (qAt M w s, qAt M w s)) := by
  have hw : w.take x ++ w.drop x ++ ([] : List A) = w := by simp
  have hlx : (w.take x).length = x := by rw [List.length_take]; omega
  have hlen : (w.take x).length + (w.drop x).length = w.length := by
    rw [List.length_take, List.length_drop]; omega
  have hseg : seg w x w.length = w.drop x := seg_to_length w x
  have hp : IsLastPiece M (w.take x) (w.drop x) [] (qAt M w s) s (e - s) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hw]; simpa using cfgAt_qAt M w hpa
    · intro i hi
      rw [hw]
      obtain ⟨c, hc, h1⟩ := hconf (s + i) (by omega) (by omega)
      refine ⟨c, hc, by omega, ?_⟩
      rw [hlen]
      exact posAt_le_length M w hc
    · rw [hw, show s + (e - s) + 1 = e + 1 from by omega]; exact hhalt
  have hk' : Walk.VisitsLe (traj M (w.take x ++ w.drop x ++ ([] : List A))) s (s + (e - s)) k := by
    rw [hw, show s + (e - s) = e from by omega]; exact hk
  have hhaltW : cfgAt (M.withContext (w.take x).getLast? none (qAt M w s)) (w.drop x) (e - s + 1)
      = some Cfg.halt := by
    have h := lastPiece_halt hp
    simpa using h
  have hwidthW : WidthLe (M.withContext (w.take x).getLast? none (qAt M w s)) (w.drop x) k := by
    have h := widthLe_lastPiece hp hk'
    simpa using h
  rw [hseg]
  exact ⟨⟨e - s + 1, hhaltW⟩, hwidthW⟩

/-- **The window condition of the last piece, of the kind `4`**: the run halts
inside the window, which it enters at the right end. -/
theorem winCond_kind_four (M : TwoWay A B Q) (w : List A) {s e x y k : ℕ}
    (hse : s ≤ e) (hxy : x ≤ y) (hyw : y ≤ w.length) (hpa : posAt M w s = some y)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∃ c, posAt M w t = some c ∧ x ≤ c ∧ c ≤ y)
    (hhalt : cfgAt M w (e + 1) = some Cfg.halt)
    (hk : Walk.VisitsLe (traj M w) s e k) :
    seg w x y ∈ WinCond M k ((4 : Fin 5), (w.take x).getLast?, (w.drop y).head?,
      some (qAt M w s, qAt M w s)) := by
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hxw : x ≤ w.length := le_trans hxy hyw
  have hlx : (w.take x).length = x := by rw [List.length_take]; omega
  have hlxy : (w.take x).length + (seg w x y).length = y := seg_len_add hxy hyw
  have hum : w.take x ++ seg w x y = w.take y := take_append_seg w hxy
  have hp : IsLastPieceRev M (w.take x) (seg w x y) (w.drop y) (qAt M w s) s (e - s) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hw, hum]; exact cfgAt_qAt M w hpa
    · intro i hi
      rw [hw]
      obtain ⟨c, hc, h1, h2⟩ := hconf (s + i) (by omega) (by omega)
      exact ⟨c, hc, by omega, by omega⟩
    · rw [hw, show s + (e - s) + 1 = e + 1 from by omega]; exact hhalt
  have hk' : Walk.VisitsLe (traj M (w.take x ++ seg w x y ++ w.drop y)) s (s + (e - s)) k := by
    rw [hw, show s + (e - s) = e from by omega]; exact hk
  exact ⟨⟨e - s + 1, lastPieceRev_halt hp⟩, widthLe_lastPieceRev hp hk'⟩

end Chk

end TwoWay

end Lax916827Proofs.Transducers
