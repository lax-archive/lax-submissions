/-
**Every slot of the record-breaker decomposition carries a piece of the chain of
stage 1.**

`RequestProject/PartC/SnakeChkSlot.lean` produces the pieces of the chain, one
kind at a time.  This file collects them into a single statement,
`Transducers.TwoWay.Chk.exists_slotOK`: for every pair `i` of neighbouring blocks
and every slot `r ≤ 2K` there is a window inside that pair carrying a piece of
the chain, the `2K` first slots being the halves of the `K` excursions of the
`i`-th record-breaking column and the last one its progress part.

The confinement of the window to the pair of blocks is the one of
`RequestProject/PartC/SnakeConfine.lean`, exactly as in
`TwoWay.exists_pieceData` (`RequestProject/PartC/SnakeData.lean`); what is added
here is the chain structure -- the cuts, the states and the window condition.
-/
import Lax916827Proofs.Source.PartC.SnakeChkSlot
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

variable {A B Q : Type} {M : TwoWay A B Q} {w : List A} {T K : ℕ}

/-- **The package of the piece of the chain carried by one slot** of the
record-breaker decomposition: a window inside the pair `i` of neighbouring
blocks, together with the parameters of the window transducer of the piece. -/
structure SlotOK (M : TwoWay A B Q) (w : List A) (K i r a b : ℕ)
    (p : PieceParam A Q) : Prop where
  /-- The window starts inside the pair of blocks. -/
  low : snakeY M w i ≤ a
  /-- The window is an interval. -/
  le : a ≤ b
  /-- The window ends inside the pair of blocks. -/
  high : b ≤ snakeY M w (i + 2)
  /-- The letter to the left of the window. -/
  ctxL : lOf p = (w.take a).getLast?
  /-- The letter to the right of the window. -/
  ctxR : rOf p = (w.drop b).head?
  /-- The two states are the states of the run at the two ends of the piece. -/
  st : stOf p = some (qAt M w (pcStart M w K i r), qAt M w (pcEnd M w K i r))
  /-- The piece starts where the head is at the start of the slot. -/
  st_cut : stCut p a b = traj M w (pcStart M w K i r)
  /-- The window condition. -/
  wcond : seg w a b ∈ WinCond M (K - 1) p
  /-- Every piece but the last one of the last pair crosses its window. -/
  kind_cross : r < 2 * K ∨ i < rbN M w → kdOf p = 1 ∨ kdOf p = 2
  /-- Every piece but the last one of the last pair ends where the head is at
  the end of the slot. -/
  en_cut : r < 2 * K ∨ i < rbN M w → enCut p a b = traj M w (pcEnd M w K i r)
  /-- The last piece of the last pair halts inside its window. -/
  kind_halt : r = 2 * K → i = rbN M w → kdOf p = 3 ∨ kdOf p = 4

/-- **Every slot of the record-breaker decomposition of a halting run of width at
most `K` carries a piece of the chain of stage 1.** -/
theorem exists_slotOK (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w K)
    (hK : 2 ≤ K) (i r : ℕ) :
    ∃ (a b : ℕ) (p : PieceParam A Q), i ≤ rbN M w → r < 2 * K + 1 →
      SlotOK M w K i r a b p := by
  classical
  by_cases hi : i ≤ rbN M w
  swap
  · exact ⟨0, 0, default, fun h => absurd h hi⟩
  have hYc : snakeY M w i ≤ rbCol M w i := snakeY_le_rbCol hi
  have hcY : rbCol M w i ≤ snakeY M w (i + 2) := rbCol_le_snakeY_two hT hi
  by_cases hr : r = 2 * K
  swap
  · -- one of the two halves of an excursion
    obtain ⟨p₁, p₂, h₁, h₂⟩ := exists_crossOK_exc hT hwidth hK i (r / 2)
    have hsplit : traj M w (excS M w i (r / 2)) = excC M w i (r / 2) :=
      Walk.pos_excSplit (excT_mono_step i (r / 2))
    have hs1 : rbFirst M w i ≤ excS M w i (r / 2) :=
      le_trans (rbFirst_le_excT i (r / 2)) (excS_bounds i (r / 2)).1
    have hs2 : excS M w i (r / 2) ≤ rbLast M w i :=
      le_trans (excS_bounds i (r / 2)).2 (excT_le i (r / 2 + 1))
    have hlow : snakeY M w i ≤ excC M w i (r / 2) := by
      rw [← hsplit]
      exact snakeY_le_traj hT hi hs1 (le_trans hs2 (rbLast_le_endT i))
    have hhigh : excC M w i (r / 2) ≤ snakeY M w (i + 2) := by
      rw [← hsplit]
      exact traj_le_snakeY_two hT hi hs2
    by_cases hpar : r % 2 = 0
    · have hst : pcStart M w K i r = excT M w i (r / 2) := by
        rw [pcStart, if_neg hr, if_pos hpar]
      have hen : pcEnd M w K i r = excS M w i (r / 2) := by
        rw [pcEnd, if_neg hr, if_pos hpar]
      refine ⟨min (rbCol M w i) (excC M w i (r / 2)), max (rbCol M w i) (excC M w i (r / 2)),
        p₁, fun _ _ => ⟨by omega, h₁.le, by omega, h₁.ctxL, h₁.ctxR, ?_, ?_, h₁.wcond,
          fun _ => h₁.kind, fun _ => ?_, fun h _ => absurd h hr⟩⟩
      · rw [hst, hen]; exact h₁.st
      · rw [hst]; exact h₁.st_cut
      · rw [hen]; exact h₁.en_cut
    · have hst : pcStart M w K i r = excS M w i (r / 2) := by
        rw [pcStart, if_neg hr, if_neg hpar]
      have hen : pcEnd M w K i r = excT M w i (r / 2 + 1) := by
        rw [pcEnd, if_neg hr, if_neg hpar]
      refine ⟨min (rbCol M w i) (excC M w i (r / 2)), max (rbCol M w i) (excC M w i (r / 2)),
        p₂, fun _ _ => ⟨by omega, h₂.le, by omega, h₂.ctxL, h₂.ctxR, ?_, ?_, h₂.wcond,
          fun _ => h₂.kind, fun _ => ?_, fun h _ => absurd h hr⟩⟩
      · rw [hst, hen]; exact h₂.st
      · rw [hst]; exact h₂.st_cut
      · rw [hen]; exact h₂.en_cut
  · subst hr
    have hst : pcStart M w K i (2 * K) = rbLast M w i := by rw [pcStart, if_pos rfl]
    by_cases hiN : i < rbN M w
    · -- the progress part of a record-breaking column which is not the last one
      obtain ⟨p, hp⟩ := exists_crossOK_prog hT hwidth hK hiN
      have hen : pcEnd M w K i (2 * K) = rbFirst M w (i + 1) := by
        rw [pcEnd, if_pos rfl, if_pos hiN]
      have hhigh : rbCol M w (i + 1) = snakeY M w (i + 2) := by
        rw [show i + 2 = (i + 1) + 1 from rfl, snakeY_succ_of_le (by omega)]
      refine ⟨rbCol M w i, rbCol M w (i + 1), p, fun _ _ =>
        ⟨hYc, hp.le, le_of_eq hhigh, hp.ctxL, hp.ctxR, ?_, ?_, hp.wcond,
          fun _ => hp.kind, fun _ => ?_, fun _ h => absurd h (by omega)⟩⟩
      · rw [hst, hen]; exact hp.st
      · rw [hst]; exact hp.st_cut
      · rw [hen]; exact hp.en_cut
    · -- the final progress part
      have hiN' : i = rbN M w := by omega
      subst hiN'
      have hen : pcEnd M w K (rbN M w) (2 * K) = rbLast M w (rbN M w) := by
        rw [pcEnd, if_pos rfl, if_neg (lt_irrefl _)]
      have hlow : ∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w →
          snakeY M w (rbN M w) ≤ traj M w t := by
        intro t h1 h2
        exact snakeY_le_traj hT hi (le_trans (rbFirst_le_rbLast (rbN M w)) h1) h2
      rcases exists_haltOK_final hT hwidth hK hYc hlow with ⟨p, hp⟩ | ⟨p, hp⟩
      · refine ⟨rbCol M w (rbN M w), w.length, p, fun _ _ =>
          ⟨hYc, hp.le, le_of_eq snakeY_last.symm, hp.ctxL, hp.ctxR, ?_, ?_, hp.wcond,
            fun h => absurd h (by omega), fun h => absurd h (by omega),
            fun _ _ => hp.kind⟩⟩
        · rw [hst, hen]; exact hp.st
        · rw [hst]; exact hp.st_cut
      · refine ⟨snakeY M w (rbN M w), rbCol M w (rbN M w), p, fun _ _ =>
          ⟨le_refl _, hp.le, hcY, hp.ctxL, hp.ctxR, ?_, ?_, hp.wcond,
            fun h => absurd h (by omega), fun h => absurd h (by omega),
            fun _ _ => hp.kind⟩⟩
        · rw [hst, hen]; exact hp.st
        · rw [hst]; exact hp.st_cut

end Chk

end TwoWay

end Lax916827Proofs.Transducers
