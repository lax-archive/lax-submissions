/-
**Building an annotation out of a chain of pieces.**

The checking automaton of stage 1 of the induction step of the book's snake
lemma verifies *local* conditions on an annotation of the input
(`RequestProject/PartC/SnakeChkEnc.lean`).  This file shows that those local
conditions are satisfied by the annotation that a chain of pieces
(`Transducers.TwoWay.Chk.ChainData`) prescribes: the block boundaries are the
cutting points of the chain, the two window flags of a piece slot are the
indicator functions of the two ends of its window, the parameters are the ones
of the chain, and the automaton state is the state of the window-condition
automaton after the window letters read so far.

The verification of the individual local conditions is in
`RequestProject/PartC/SnakeChkVerify.lean`; here they are assembled into
membership in the language of the checking automaton.

Together with the existence of a chain on every good input
(`RequestProject/PartC/SnakeChkRB.lean`) this is the completeness of the
checking automaton.
-/
import Lax916827Proofs.Source.PartC.SnakeChkVerify
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open RegPair SnakeLoc ChainData

variable {A B Q S : Type}

/-- **Every chain of pieces is described by an annotation that the checking
automaton accepts.** -/
theorem exists_mem_chkLang_of_chainData [Finite A] [Finite B] [Finite Q] [Inhabited S]
    (M : TwoWay A B Q) {K : ℕ} (stp : S → A → S) (ini : S)
    (acc : PieceParam A Q → S → Prop)
    (hacc : ∀ (p : PieceParam A Q) (v : List A),
      v ∈ WinCond M (K - 1) p ↔ acc p (v.foldl stp ini))
    {w : List A} (d : ChainData M K w) :
    ∃ u ∈ ChkLang M K stp ini acc, u.map lt = w := by
  classical
  have h0 : 0 < w.length := d.length_pos
  refine ⟨d.annot stp ini, ?_, d.map_lt_annot stp ini⟩
  intro i hi
  rw [length_annot] at hi
  rw [goodB_iff]
  rcases Nat.lt_or_ge i w.length with hlt | hge
  · -- an interior position: the letter at `i` is the annotated letter `letAt i`
    have hgi : (d.annot stp ini)[i]? = some (d.letAt stp ini i hlt) := by
      rw [List.getElem?_eq_getElem (by simpa using hlt), d.getElem_annot stp ini hlt]
    rw [hgi]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · -- the first letter
      rw [SnakeLoc.prevAt_zero]
      exact ⟨d.letOK_letAt hlt, d.startOK_letAt hlt⟩
    · -- a letter with a predecessor
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j < w.length := by omega
      have hprev : SnakeLoc.prevAt (d.annot stp ini) (j + 1) = some (d.letAt stp ini j hj) := by
        rw [SnakeLoc.prevAt, if_neg (by omega),
          List.getElem?_eq_getElem (show j + 1 - 1 < (d.annot stp ini).length by
            rw [length_annot]; omega)]
        congr 1
        exact d.getElem_annot stp ini hj
      rw [hprev]
      refine ⟨d.letOK_letAt hlt, ?_, ?_⟩
      · rw [sa_letAt]
        simp only [decide_eq_false_iff_not, not_and]
        intro hj'
        omega
      · rcases d.blkOf_succ hlt with hsame | ⟨hnew, hY⟩
        · rw [if_neg ?_]
          · exact d.adjSame_letAt hj hlt hsame
          · rw [sb_letAt, hsame]
            simp only [decide_eq_true_eq]
            have := d.Y_blkOf_le j
            omega
        · rw [if_pos ?_]
          · exact d.adjSep_letAt hacc hj hlt hnew hY
          · rw [sb_letAt, hnew]
            simp only [decide_eq_true_eq]
            omega
  · -- the position just after the last letter
    have hie : i = w.length := by omega
    subst hie
    have hL : w.length - 1 < w.length := by omega
    have hgi : (d.annot stp ini)[w.length]? = none := by
      rw [List.getElem?_eq_none (by rw [length_annot])]
    have hprev : SnakeLoc.prevAt (d.annot stp ini) w.length
        = some (d.letAt stp ini (w.length - 1) hL) := by
      rw [SnakeLoc.prevAt, if_neg (by omega),
        List.getElem?_eq_getElem (show w.length - 1 < (d.annot stp ini).length by
          rw [length_annot]; omega)]
      congr 1
      exact d.getElem_annot stp ini hL
    rw [hgi, hprev]
    exact d.endOK_letAt hacc hL

end Chk

end TwoWay

end Lax916827Proofs.Transducers
