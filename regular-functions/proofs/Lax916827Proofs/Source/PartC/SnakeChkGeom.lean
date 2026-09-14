/-
**Soundness of the checking automaton of stage 1 of the induction step of the
book's snake lemma.**

An annotation accepted by the checking automaton
(`Transducers.TwoWay.Chk.ChkLang`) describes a chain of pieces of the run of `M`
on the annotated input (`Transducers.TwoWay.Chk.exists_chainData_of_chkLang`).
This file combines that reading of the annotation with the telescoping of a
chain (`Transducers.TwoWay.Chk.runOut_of_chainData`) and with the identification
of the blocks of the annotated string
(`Transducers.TwoWay.Chk.splitSep_homOf_snakeOutLet`), and concludes that the
neighbouring-block map combinator applied to the block function reproduces the
output of the run.
-/
import Lax916827Proofs.Source.PartC.SnakeChkReadData
import Lax916827Proofs.Source.PartC.SnakeChkRel
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open RegPair BlockIdx

variable {A B Q S : Type}

/-- Two strings with the same blocks have the same pairs of neighbouring
blocks. -/
lemma pairMap_congr_splitSep {C D : Type} (f : List (Option C) → List D)
    {v v' : List (Option C)} (h : splitSep v = splitSep v') :
    pairMap f v = pairMap f v' := by
  rw [pairMap, pairMap, pairBlocks, pairBlocks, h]

/-- **The checking automaton is sound**: an accepted annotation of a good input
describes a chain of pieces whose outputs concatenate to the output of the
run, so the neighbouring-block map combinator applied to the block function
computes the output of the run on it. -/
theorem chk_sound [Finite A] [Finite B] [Finite Q] [Inhabited S]
    (M : TwoWay A B Q) {K : ℕ} (stp : S → A → S) (ini : S)
    (acc : PieceParam A Q → S → Prop)
    (hacc : ∀ (p : PieceParam A Q) (v : List A),
      v ∈ WinCond M (K - 1) p ↔ acc p (v.foldl stp ini))
    {u : List (Gam A Q S K)} (hu : u ∈ ChkLang M K stp ini acc)
    (hgood : GoodInput M K (u.map lt)) :
    pairMap (blockFun M (K - 1) (2 * K + 1)) (homOf (snakeOutLet K) u)
      = runOut M (u.map lt) := by
  classical
  have hne : u ≠ [] := by
    intro h
    exact hgood.1 (by rw [h]; rfl)
  obtain ⟨d, hN, hY, ha, hb, hp⟩ := exists_chainData_of_chkLang hacc hu hne
  have hsplit : splitSep (homOf (snakeOutLet K) u)
      = splitSep (snakeAnn (u.map lt) K d.N d.Y d.a d.b d.p) := by
    rw [splitSep_homOf_snakeOutLet hu hne, splitSep_snakeAnn, hN, hY, ha, hb, hp]
  rw [pairMap_congr_splitSep _ hsplit,
    pairMap_snakeAnn (k := K - 1) M K (u.map lt) d.Y d.a d.b d.p d.Y_mono d.Y_last d.Y_lt
      (fun i hi r hr => d.win i hi r hr),
    runOut_of_chainData d]

end Chk

end TwoWay

end Lax916827Proofs.Transducers
