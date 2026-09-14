/-
**One piece of the chain of stage 1, as a package.**

`RequestProject/PartC/SnakeChkPieceWin.lean` proves the window condition of each
of the four kinds of piece.  This file packages, for a piece of the run of `M` on
`w` between two given times, everything that the chain of stage 1
(`Transducers.TwoWay.Chk.ChainData`) has to know about it: the window, the two
context letters, the two states -- the states of the run at the two ends of the
piece -- the kind, the two cuts at which the piece starts and ends, and the
window condition.

`Transducers.TwoWay.Chk.CrossOK` is the package for a piece that crosses its
window, `Transducers.TwoWay.Chk.HaltOK` the one for a piece that halts inside it.
The point of stating the two cuts as the *positions of the head* at the two ends
of the piece is that consecutive pieces then automatically meet at a common cut,
and the point of stating the two states as the *states of the run* is that they
automatically meet in a common state.
-/
import Lax916827Proofs.Source.PartC.SnakeChkPieceWin
import Lax916827Proofs.Source.PartC.SnakeChkData
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

variable {A B Q : Type}

/-! ## A piece that crosses its window -/

/-- **The package of one piece of the chain that crosses its window**, from time
`s` to time `e`, on the window `[a, b)`. -/
structure CrossOK (M : TwoWay A B Q) (w : List A) (k s e a b : ℕ)
    (p : PieceParam A Q) : Prop where
  /-- The window is an interval. -/
  le : a ≤ b
  /-- The window lies inside the input. -/
  b_le : b ≤ w.length
  /-- The letter to the left of the window. -/
  ctxL : lOf p = (w.take a).getLast?
  /-- The letter to the right of the window. -/
  ctxR : rOf p = (w.drop b).head?
  /-- The two states are the states of the run at the two ends of the piece. -/
  st : stOf p = some (qAt M w s, qAt M w e)
  /-- The piece crosses its window. -/
  kind : kdOf p = 1 ∨ kdOf p = 2
  /-- The piece starts where the head is at time `s`. -/
  st_cut : stCut p a b = traj M w s
  /-- The piece ends where the head is at time `e`. -/
  en_cut : enCut p a b = traj M w e
  /-- The window condition. -/
  wcond : seg w a b ∈ WinCond M k p

/-- **A piece of the run that crosses the interval between the columns of its
two ends, reaching the far one for the first time at its end, is a piece of the
chain.** -/
theorem exists_crossOK (M : TwoWay A B Q) (w : List A) {s e c d k : ℕ}
    (hse : s ≤ e) (hpa : posAt M w s = some c) (hpb : posAt M w e = some d)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∃ z, posAt M w t = some z ∧ min c d ≤ z ∧ z ≤ max c d)
    (hearly : ∀ t, s ≤ t → t < e → posAt M w t ≠ some d)
    (hk : Walk.VisitsLe (traj M w) s e k) :
    ∃ p : PieceParam A Q, CrossOK M w k s e (min c d) (max c d) p := by
  have hts : traj M w s = c := traj_eq M w hpa
  have hte : traj M w e = d := traj_eq M w hpb
  have hcw : c ≤ w.length := posAt_le_length M w hpa
  have hdw : d ≤ w.length := posAt_le_length M w hpb
  rcases le_total c d with hcd | hcd
  · have hmin : min c d = c := min_eq_left hcd
    have hmax : max c d = d := max_eq_right hcd
    rw [hmin, hmax] at hconf ⊢
    refine ⟨((1 : Fin 5), (w.take c).getLast?, (w.drop d).head?,
      some (qAt M w s, qAt M w e)), hcd, hdw, rfl, rfl, rfl, Or.inl rfl, ?_, ?_, ?_⟩
    · simp [stCut, kdOf, hts]
    · simp [enCut, kdOf, hte]
    · exact winCond_kind_one M w hse hcd hdw hpa hpb hconf hearly hk
  · have hmin : min c d = d := min_eq_right hcd
    have hmax : max c d = c := max_eq_left hcd
    rw [hmin, hmax] at hconf ⊢
    refine ⟨((2 : Fin 5), (w.take d).getLast?, (w.drop c).head?,
      some (qAt M w s, qAt M w e)), hcd, hcw, rfl, rfl, rfl, Or.inr rfl, ?_, ?_, ?_⟩
    · simp [stCut, kdOf, hts]
    · simp [enCut, kdOf, hte]
    · exact winCond_kind_two M w hse hcd hcw hpa hpb hconf hearly hk

/-! ## A piece that halts inside its window -/

/-- **The package of the last piece of the chain**, which starts at time `s` and
halts inside its window `[a, b)`. -/
structure HaltOK (M : TwoWay A B Q) (w : List A) (k s a b : ℕ)
    (p : PieceParam A Q) : Prop where
  /-- The window is an interval. -/
  le : a ≤ b
  /-- The window lies inside the input. -/
  b_le : b ≤ w.length
  /-- The letter to the left of the window. -/
  ctxL : lOf p = (w.take a).getLast?
  /-- The letter to the right of the window. -/
  ctxR : rOf p = (w.drop b).head?
  /-- A halting piece does not change the state. -/
  st : stOf p = some (qAt M w s, qAt M w s)
  /-- The piece halts inside its window. -/
  kind : kdOf p = 3 ∨ kdOf p = 4
  /-- The piece starts where the head is at time `s`. -/
  st_cut : stCut p a b = traj M w s
  /-- The window condition. -/
  wcond : seg w a b ∈ WinCond M k p

/-- **The last piece of a run that stays to the right of the column where it
starts is a halting piece of the chain**, on the window that reaches to the
right end of the input. -/
theorem exists_haltOK_right (M : TwoWay A B Q) (w : List A) {s e x k : ℕ}
    (hse : s ≤ e) (hpa : posAt M w s = some x)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∃ z, posAt M w t = some z ∧ x ≤ z)
    (hhalt : cfgAt M w (e + 1) = some Cfg.halt)
    (hk : Walk.VisitsLe (traj M w) s e k) :
    ∃ p : PieceParam A Q, HaltOK M w k s x w.length p := by
  have hts : traj M w s = x := traj_eq M w hpa
  have hxw : x ≤ w.length := posAt_le_length M w hpa
  refine ⟨((3 : Fin 5), (w.take x).getLast?, none, some (qAt M w s, qAt M w s)),
    hxw, le_refl _, rfl, ?_, rfl, Or.inl rfl, ?_, ?_⟩
  · show (none : Option A) = (w.drop w.length).head?
    simp
  · simp [stCut, kdOf, hts]
  · exact winCond_kind_three M w hse hxw hpa hconf hhalt hk

/-- **The last piece of a run that stays to the left of the column where it
starts, but to the right of the column `x`, is a halting piece of the chain**,
on the window `[x, y)`. -/
theorem exists_haltOK_left (M : TwoWay A B Q) (w : List A) {s e x y k : ℕ}
    (hse : s ≤ e) (hxy : x ≤ y) (hyw : y ≤ w.length) (hpa : posAt M w s = some y)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∃ z, posAt M w t = some z ∧ x ≤ z ∧ z ≤ y)
    (hhalt : cfgAt M w (e + 1) = some Cfg.halt)
    (hk : Walk.VisitsLe (traj M w) s e k) :
    ∃ p : PieceParam A Q, HaltOK M w k s x y p := by
  have hts : traj M w s = y := traj_eq M w hpa
  refine ⟨((4 : Fin 5), (w.take x).getLast?, (w.drop y).head?,
    some (qAt M w s, qAt M w s)), hxy, hyw, rfl, rfl, rfl, Or.inr rfl, ?_, ?_⟩
  · simp [stCut, kdOf, hts]
  · exact winCond_kind_four M w hse hxy hyw hpa hconf hhalt hk

end Chk

end TwoWay

end Lax916827Proofs.Transducers
