/-
**The window condition of a piece**, and the step of the chain of pieces that it
licenses.

Stage 1 of the induction step of the book's snake lemma guesses a decomposition
of the run into pieces and *checks* it.  What has to be checked about one piece
is a property of its window and of its parameters alone, namely that the run of
the window transducer on the window behaves as the parameters claim: for a piece
of the kind `1` or `2` that it reaches the far end of the window in the
announced state, for a piece of the kind `3` or `4` that it halts inside the
window, and in all four cases that it has width at most `k`, so that the
induction hypothesis of the snake lemma computes its output.

That property is `Transducers.TwoWay.Chk.WinCond`; it is a regular language of
windows (`Transducers.TwoWay.Chk.isRegular_winCond`), which is what makes the
checking automaton possible.  The two theorems
`Transducers.TwoWay.Chk.chain_step_adv` and
`Transducers.TwoWay.Chk.chain_step_halt` say that a piece whose window satisfies
the condition really is a piece of the run: they package the four theorems
`TwoWay.exists_outRange_kind_one` … `TwoWay.exists_outRange_kind_four` of
`RequestProject/PartC/SnakeWinRun.lean` in the form in which the chain of stage 1
uses them.
-/
import Lax916827Proofs.Source.PartC.SnakeChkTools
import Lax916827Proofs.Source.PartC.SnakeRunLang
import Lax916827Proofs.Source.PartC.SnakeWinRun
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open SnakeRun

variable {A B Q : Type}

/-! ## The parameters of a piece, read off -/

/-- The kind of the piece. -/
def kdOf (p : PieceParam A Q) : Fin 5 := p.1

/-- The letter to the left of the window. -/
def lOf (p : PieceParam A Q) : Option A := p.2.1

/-- The letter to the right of the window. -/
def rOf (p : PieceParam A Q) : Option A := p.2.2.1

/-- The state in which the piece starts, and the state in which it ends. -/
def stOf (p : PieceParam A Q) : Option (Q × Q) := p.2.2.2

/-- The state in which the piece starts. -/
def entOf (p : PieceParam A Q) : Option Q := p.2.2.2.map Prod.fst

/-- The state in which the piece ends. -/
def extOf (p : PieceParam A Q) : Option Q := p.2.2.2.map Prod.snd

lemma param_eq (p : PieceParam A Q) : p = (kdOf p, lOf p, rOf p, stOf p) := rfl

/-! ## The window condition -/

/-- **The condition that the window of a piece has to satisfy.**  For the kinds
`1` and `2` the window run reaches the far end of the window in the announced
state; for the kinds `3` and `4` it halts; in every case it has width at most
`k`.  The kinds outside `{1, 2, 3, 4}` denote the empty piece, about which
nothing has to be checked. -/
def WinCond (M : TwoWay A B Q) (k : ℕ) (p : PieceParam A Q) : Language A :=
  match p.2.2.2 with
  | none => Set.univ
  | some (q, f) =>
      if p.1 = 1 then
        {v | v ∈ endLang (stopRight M p.2.1 p.2.2.1 q f) f ∧
          v ∈ haltLang (stopRight M p.2.1 p.2.2.1 q f) ∧
          WidthLe (stopRight M p.2.1 p.2.2.1 q f) v k}
      else if p.1 = 2 then
        {v | v.reverse ∈ endLang (stopRight (mirror M) p.2.2.1 p.2.1 q f) f ∧
          v.reverse ∈ haltLang (stopRight (mirror M) p.2.2.1 p.2.1 q f) ∧
          WidthLe (stopRight (mirror M) p.2.2.1 p.2.1 q f) v.reverse k}
      else if p.1 = 3 then
        {v | v ∈ haltLang (M.withContext p.2.1 p.2.2.1 q) ∧
          WidthLe (M.withContext p.2.1 p.2.2.1 q) v k}
      else if p.1 = 4 then
        {v | v.reverse ∈ haltLang ((mirror M).withContext p.2.2.1 p.2.1 q) ∧
          WidthLe ((mirror M).withContext p.2.2.1 p.2.1 q) v.reverse k}
      else Set.univ

/-! ## The window condition is regular -/

section Regular

variable [Finite A] [Finite Q]

omit [Finite A] in
/-- The reverse of a regular language is regular. -/
lemma isRegular_reverseSet {L : Language A} (hL : L.IsRegular) :
    Language.IsRegular {v : List A | v.reverse ∈ L} := by
  have h := hL.reverse
  refine RegAut.isRegular_of_eq h ?_
  intro v
  simp [Language.reverse]

/-- **The window condition is a regular language of windows.** -/
lemma isRegular_winCond (M : TwoWay A B Q) (k : ℕ) (p : PieceParam A Q) :
    (WinCond M k p).IsRegular := by
  classical
  obtain ⟨d1, d2, d3, d4⟩ := p
  rcases d4 with _ | ⟨q, f⟩
  · exact RegAut.isRegular_univ
  · show Language.IsRegular (if d1 = 1 then _ else if d1 = 2 then _ else if d1 = 3 then _
      else if d1 = 4 then _ else Set.univ)
    by_cases h1 : d1 = 1
    · rw [if_pos h1]
      exact RegAut.isRegular_and (isRegular_endLang _ _) (isRegular_haltWidthLang _ _)
    · rw [if_neg h1]
      by_cases h2 : d1 = 2
      · rw [if_pos h2]
        exact isRegular_reverseSet
          (RegAut.isRegular_and (isRegular_endLang _ _) (isRegular_haltWidthLang _ _))
      · rw [if_neg h2]
        by_cases h3 : d1 = 3
        · rw [if_pos h3]
          exact isRegular_haltWidthLang _ _
        · rw [if_neg h3]
          by_cases h4 : d1 = 4
          · rw [if_pos h4]
            exact isRegular_reverseSet (isRegular_haltWidthLang _ _)
          · rw [if_neg h4]
            exact RegAut.isRegular_univ

end Regular

/-! ## A piece whose window condition holds is a piece of the run -/

variable (M : TwoWay A B Q) (w : List A)

/-- **A piece of the kind `1` or `2` moves the run from one end of its window to
the other.** -/
theorem chain_step_adv {k x y a : ℕ} (hxy : x ≤ y)
    {p : PieceParam A Q} {q f : Q} (hst : p.2.2.2 = some (q, f))
    (hl : p.2.1 = (w.take x).getLast?) (hr : p.2.2.1 = (w.drop y).head?)
    (hk : p.1 = 1 ∨ p.1 = 2)
    (hstart : cfgAt M w a
      = some (Cfg.conf (w.take (if p.1 = 1 then x else y)) q
          (w.drop (if p.1 = 1 then x else y))))
    (hwin : seg w x y ∈ WinCond M k p) :
    ∃ n, cfgAt M w (a + n)
        = some (Cfg.conf (w.take (if p.1 = 1 then y else x)) f
            (w.drop (if p.1 = 1 then y else x))) ∧
      outRange M w a (a + n) = pieceOut M k p (seg w x y) := by
  obtain ⟨d1, d2, d3, d4⟩ := p
  simp only at hst hl hr hk hstart hwin ⊢
  subst hst; subst hl; subst hr
  rcases hk with hk | hk
  · subst hk
    rw [if_pos rfl] at hstart ⊢
    exact exists_outRange_kind_one M w hxy hstart hwin.1 hwin.2.2
  · subst hk
    rw [if_neg (by decide : ¬ (2 : Fin 5) = 1)] at hstart ⊢
    exact exists_outRange_kind_two M w hxy hstart hwin.1 hwin.2.2

/-- **A piece of the kind `3` or `4` halts inside its window.** -/
theorem chain_step_halt {k x y a : ℕ} (hxy : x ≤ y)
    {p : PieceParam A Q} {q : Q} (hst : p.2.2.2 = some (q, q))
    (hl : p.2.1 = (w.take x).getLast?) (hr : p.2.2.1 = (w.drop y).head?)
    (hk : p.1 = 3 ∨ p.1 = 4)
    (hstart : cfgAt M w a
      = some (Cfg.conf (w.take (if p.1 = 3 then x else y)) q
          (w.drop (if p.1 = 3 then x else y))))
    (hwin : seg w x y ∈ WinCond M k p) :
    ∃ n, cfgAt M w (a + n) = some Cfg.halt ∧
      outRange M w a (a + n) = pieceOut M k p (seg w x y) := by
  obtain ⟨d1, d2, d3, d4⟩ := p
  simp only at hst hl hr hk hstart hwin ⊢
  subst hst; subst hl; subst hr
  rcases hk with hk | hk
  · subst hk
    rw [if_pos rfl] at hstart
    exact exists_outRange_kind_three M w hxy hstart hwin.1 hwin.2
  · subst hk
    rw [if_neg (by decide : ¬ (4 : Fin 5) = 3)] at hstart
    exact exists_outRange_kind_four M w hxy hstart hwin.1 hwin.2

/-- A piece whose kind is not one of the four real ones produces no output. -/
lemma pieceOut_of_kind_zero {k : ℕ} {p : PieceParam A Q} (h1 : p.1 ≠ 1) (h2 : p.1 ≠ 2)
    (h3 : p.1 ≠ 3) (h4 : p.1 ≠ 4) (v : List A) : pieceOut M k p v = [] := by
  rcases hst : p.2.2.2 with _ | ⟨q, f⟩
  · rw [pieceOut, hst]
  · rw [pieceOut, hst]
    simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]

end Chk

end TwoWay

end Lax916827Proofs.Transducers
