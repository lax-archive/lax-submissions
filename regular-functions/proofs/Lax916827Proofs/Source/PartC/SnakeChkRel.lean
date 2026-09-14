/-
**What the marking of stage 1 of the induction step of the book's snake lemma
has to satisfy.**

The induction step uses the marking in exactly one way: the neighbouring-block
map combinator applied to the block function, evaluated on the marking of a
nonempty input, has to be the width-`K` output of the run
(`Transducers.TwoWay.SnakeRel`).  That is weaker than being a *correct* marking
of the record-breaker decomposition (`TwoWay.IsSnakeMarking`), and it is all
that `Transducers.boundedWidth_isRegular_step` needs; keeping the requirement in
this shape is what lets the checking automaton of stage 1 verify a *chain of
pieces* instead of the record-breaker decomposition itself.
-/
import Lax916827Proofs.Source.PartC.SnakeBlock
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open RegPair

variable {A B Q : Type}

/-- The inputs on which the marking of stage 1 has to do real work: the nonempty
inputs whose run halts and has width at most `K`.  On all the other nonempty
inputs the width-`K` output function is empty, so the marking only has to
produce no pair of neighbouring blocks at all. -/
def GoodInput (M : TwoWay A B Q) (K : ℕ) (w : List A) : Prop :=
  w ≠ [] ∧ (∃ T, cfgAt M w T = some Cfg.halt) ∧ WidthLe M w K

/-- **What the marking of stage 1 has to satisfy.**  The empty input is
excluded: on it the annotation has no letters at all, so it cannot carry the
parameters of the pieces, while the run may perfectly well produce a nonempty
output; the induction step therefore treats the empty input separately. -/
def SnakeRel (M : TwoWay A B Q) (K : ℕ) (w : List A)
    (v : List (Option (SnakeLet A Q (2 * (2 * K + 1))))) : Prop :=
  w ≠ [] → pairMap (blockFun M (K - 1) (2 * K + 1)) v = widthOut M K w

/-- A word without separators has no pair of neighbouring blocks. -/
lemma pairBlocks_map_some {C : Type} (v : List C) : pairBlocks (v.map some) = [] := by
  rw [pairBlocks, show (v.map some : List (Option C)) = blockStr [v] from
    (blockStr_singleton v).symm, splitSep_blockStr [v] (by simp), pairsList_singleton]

/-- On an input that is not good, the width-`K` output function is empty. -/
lemma widthOut_eq_nil_of_not_good {M : TwoWay A B Q} {K : ℕ} {w : List A} (hw : w ≠ [])
    (hgood : ¬ GoodInput M K w) : widthOut M K w = [] := by
  classical
  by_cases hwidth : WidthLe M w K
  · have hhalt : ¬ ∃ T, cfgAt M w T = some Cfg.halt := fun h => hgood ⟨hw, h, hwidth⟩
    rw [widthOut, if_pos hwidth, runOut, dif_neg hhalt]
  · rw [widthOut, if_neg hwidth]

/-- On a good input, the width-`K` output function is the output of the run. -/
lemma widthOut_eq_runOut_of_good {M : TwoWay A B Q} {K : ℕ} {w : List A}
    (hgood : GoodInput M K w) : widthOut M K w = runOut M w := by
  rw [widthOut, if_pos hgood.2.2]

end TwoWay

end Lax916827Proofs.Transducers
