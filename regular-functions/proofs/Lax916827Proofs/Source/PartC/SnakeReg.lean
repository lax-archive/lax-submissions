/- The book's snake lemma ("the output of a snake graph is regular") and the reduction of the hard
half of Theorem `thm:2dfa-decomposition-into-primes` (`two-way ⊆ regular`) to it.

The lemma is proved in the book by induction on the width `k` of the snake.
The two base cases, `k = 0` and `k = 1`, are proved in
`RequestProject/PartC/SnakeBase.lean`; the induction step, from `k + 1` to
`k + 2`, is `boundedWidth_isRegular_step`, which is proved here.  Everything
that the book's proof of the induction step rests on is available:

* the closure properties of regular functions, Lemma `lem:regular-closure-properties`
  (`Transducers.regular_closure_properties`) and Claim `claim:conditional`
  (`Transducers.sum_of_regular`), are proved in
  `RequestProject/PartC/RegClosure.lean` and `RequestProject/PartC/RegSum.lean`;
* the combinatorics of the induction step -- the decomposition of a run of
  width at most `k` into the loop parts and the progress parts of the
  record-breaking columns, and the resulting splitting of a halting run into
  finitely many consecutive pieces of width at most `k - 1` whose outputs
  concatenate to the output of the run -- is proved in
  `RequestProject/PartC/SnakeWalk.lean`, `RequestProject/PartC/SnakeRec.lean`
  and `RequestProject/PartC/SnakeLoop.lean`
  (`TwoWay.run_splitsInto_pred`, `TwoWay.runOutput_splits`);
* the *confinement* of those pieces to two consecutive blocks of the input --
  the book's "the loop and the progress parts of the `i`-th record-breaker are
  contained in `wᵢ₋₁ # wᵢ`", which is what makes the rational function that
  produces one copy of the input per piece have linear growth -- is proved in
  `RequestProject/PartC/SnakeConfine.lean` (`Walk.loop_confined`,
  `Walk.progress_confined`);
* the book's "without loss of generality the source column is before the target
  column, otherwise reverse the snake" is available as the *mirroring* of a
  two-way transducer, in `RequestProject/PartC/SnakeMirror.lean`
  (`TwoWay.mirror`, `TwoWay.reaches_mirror_iff`): swapping the two neighbouring
  letters in the transition function and swapping the two directions turns every
  run into the mirrored run on the reversed input, with the same output;
* the gluing of the pieces, once they have been cut out: the *neighbouring-block
  map combinator* of stages 1--3 of the book's proof,

    `w₀ # w₁ # ⋯ # wₙ  ↦  f (w₀ # w₁) · f (w₁ # w₂) ⋯ f (wₙ₋₁ # wₙ)`,

  is a regular operation, `Transducers.RegPair.isRegularFun_pairMap` in
  `RequestProject/PartC/RegPair.lean`;
* the order in time of the visits of the run to a cut -- which is what the
  recursion defining the record-breaking columns refers to -- is available as a
  rational annotation of the input,
  `Transducers.TwoWay.exists_rational_visitOrder_annot` in
  `RequestProject/PartC/TwoWayAnnotOrd.lean`.

* the presentation of each piece of the run as the whole run of a *window
  transducer* on a factor of the input, to which the induction hypothesis
  applies (`TwoWay.exists_widthOut_excHalves`, `TwoWay.exists_widthOut_prog`,
  `TwoWay.exists_widthOut_finalProg_confined`, in
  `RequestProject/PartC/SnakePieceIdent.lean` and
  `RequestProject/PartC/SnakeFinalConf.lean`, on top of
  `RequestProject/PartC/SnakePiece.lean` and
  `RequestProject/PartC/SnakePieceRev.lean`).  No version of `TwoWay.widthOut`
  with a marked source and target has to be introduced: a piece is the whole run
  of `TwoWay.stopRight` applied to `M` (or to its mirror image) on the window;
* the *block function* applied by the map combinator to one pair of
  neighbouring blocks (`TwoWay.isRegularFun_blockFun`) and the fact that the
  combinator applied to it on a correct marking of the input computes the output
  of the run (`TwoWay.pairMap_blockFun_eq_runOut`), both in
  `RequestProject/PartC/SnakeBlock.lean`;
* the **existence of a correct marking** of every nonempty input whose run halts
  with width at most `k` (`TwoWay.exists_isSnakeMarking`, in
  `RequestProject/PartC/SnakeData.lean`, through the assembly of
  `RequestProject/PartC/SnakeAssemble.lean`).

What is missing is only the machine-theoretic half of the book's stage 1: that
the correct markings can be *recognised*.  It is isolated as the single open
statement `TwoWay.exists_regular_snakeLang` in
`RequestProject/PartC/SnakeStage1.lean`, which asks for a regular language of
correctly annotated inputs containing an annotation of every input; guessing an
annotation and checking it (`Transducers.isRationalRel_of_regular_nivat`) and
uniformisation (`Transducers.exists_rationalFun_of_total_rel`, Lemma `lem:uniformisation`) then
produce the regular marking function that the step below uses.
-/
import Lax916827Proofs.Source.PartC.SnakeBase
import Lax916827Proofs.Source.PartC.SnakeLoop
import Lax916827Proofs.Source.PartC.RegPair
import Lax916827Proofs.Source.PartC.SnakeStage1
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

open TwoWay in
/-- **The bounded-width snake functions of width at most `k`, over all finite
alphabets and all state sets.**  This is the shape of the induction hypothesis
of the book's snake lemma: the induction is over *all* snake graphs of a given
width, which here means over all two-way transducers over all finite input
alphabets and all finite state sets. -/
def SnakeReg (k : ℕ) : Prop :=
  ∀ (A B Q : Type), Finite A → Finite B → Finite Q →
    ∀ M : TwoWay A B Q, IsRegularFun (widthOut M k)

open TwoWay in
/-- **The induction step of the snake lemma**: if the output of every snake of
width at most `k + 1` is regular,
then so is the output of every snake of width at most `k + 2`.

The book's proof splits a run of width at most `k + 2` into the loop parts and the progress parts of
its record-breaking columns, all of which have width at most `k + 1` (`TwoWay.run_splitsInto_pred`),
computes the outputs of the parts by the induction hypothesis `ih`, and glues them with the three
closure properties of Lemma `lem:regular-closure-properties` -- the last gluing step, the map
combinator applied to the blocks `wᵢ₋₁ # wᵢ` cut out by the record-breakers, is available as
`Transducers.RegPair.isRegularFun_pairMap`. -/
theorem boundedWidth_isRegular_step (k : ℕ) (ih : SnakeReg (k + 1)) : SnakeReg (k + 2) := by
  classical
  intro A B Q hA hB hQ M
  haveI := hA; haveI := hB; haveI := hQ
  obtain ⟨ann, hreg, hann⟩ := exists_snakeMarking M (by omega : 2 ≤ k + 2)
  have hblock : IsRegularFun (blockFun M (k + 1) (2 * (k + 2) + 1)) :=
    isRegularFun_blockFun M (k + 1) (fun M' => ih A B Q hA hB hQ M') _
  have hpair : IsRegularFun (RegPair.pairMap (blockFun M (k + 1) (2 * (k + 2) + 1))) :=
    RegPair.isRegularFun_pairMap hblock
  have hcomp : IsRegularFun (fun w : List A =>
      RegPair.pairMap (blockFun M (k + 1) (2 * (k + 2) + 1)) (ann w)) :=
    hreg.comp' hpair (fun _ => rfl)
  have hconst : IsRegularFun (fun _ : List A => widthOut M (k + 2) ([] : List A)) :=
    IsRegularFun.of_rational (isRationalFun_const _)
  have hfold : ∀ (u : List A) (b : Bool), u.foldl (fun _ _ => true) b = (b || !u.isEmpty) := by
    intro u
    induction u with
    | nil => intro b; simp
    | cons a u ih' => intro b; simpa using ih' true
  have hL : Language.IsRegular {w : List A | w = []} := by
    refine RegAut.isRegular_of_eq
      (RegAut.isRegular_foldl (Γ := A) (S := Bool) (fun _ _ => true) false {b | b = false}) ?_
    intro u
    constructor
    · intro hu
      have hu' : u = [] := hu
      subst hu'
      show List.foldl (fun _ _ => true) false ([] : List A) = false
      rfl
    · intro hu
      have hu' : List.foldl (fun _ _ => true) false u = false := hu
      rw [hfold] at hu'
      cases u with
      | nil => rfl
      | cons a v => simp at hu'
  refine (isRegularFun_cond hconst hcomp hL).congr ?_
  intro w
  by_cases hw : w = []
  · refine (if_pos hw).trans ?_
    rw [hw]
  · refine (if_neg hw).trans ?_
    exact (widthOut_eq_pairMap M (k + 2) hann hw).symm

open TwoWay in
/-- **The snake lemma** (the book's Lemma "the output of a snake graph is regular", the main
ingredient of the hard half of Theorem `thm:2dfa-decomposition-into-primes`).  For every two-way
transducer `M` and every bound `k`, the function that outputs the run of `M` on the inputs whose run
has width at most `k`, and the empty string on all other inputs, is regular.

The base cases `k = 0` and `k = 1` are proved in
`RequestProject/PartC/SnakeBase.lean`; the induction step is
`boundedWidth_isRegular_step`. -/
theorem snakeReg (k : ℕ) : SnakeReg k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      match k with
      | 0 => exact fun A B Q _ _ _ M => widthOut_zero_isRegular M
      | 1 => exact fun A B Q _ _ _ M => widthOut_one_isRegular M
      | (j + 2) => exact boundedWidth_isRegular_step j (ih (j + 1) (by omega))

open TwoWay in
/-- **Lemma `lem:output-of-snake-graph-is-regular`** (the snake lemma), for a single two-way
transducer: the width-`k` output function of `M` is regular.

*This is the general form, not the form of the book.*  The book states the lemma for an alphabet
`C` of *snake letters*, as a function `C* → B*` that returns the output of the snake graph a string
represents (and `ε` when it represents none), for `k ∈ {1, …, |Q|}`.  That statement is
`Transducers.SnakeGraph.snakeOut_isRegular`, in `RequestProject/PartC/SnakeAlphReg.lean`, and it is
the one the label `lem:output-of-snake-graph-is-regular` names; it is *deduced* from the present
theorem, by walking the snake with a two-way transducer over `C`.  The form here, the regularity of
`TwoWay.widthOut M k` for every `k : ℕ`, is the one in which Theorem
`thm:2dfa-decomposition-into-primes` consumes the lemma, and it is what the induction on the width
actually proves. -/
theorem boundedWidth_isRegular {A B Q : Type} [Finite A] [Finite B] [Finite Q]
    (M : TwoWay A B Q) (k : ℕ) : IsRegularFun (widthOut M k) :=
  snakeReg k A B Q ‹_› ‹_› ‹_› M

open TwoWay in
/-- Every function computed by a two-way transducer is regular, *provided* the
snake lemma `boundedWidth_isRegular` holds: a halting run has width at most the
number of states, so the function computed by `M` is its own width-`|Q|` output
function. -/
theorem isRegularFun_of_isTwoWay {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : IsRegularFun f := by
  obtain ⟨Q, hQ, M, hM⟩ := hf
  haveI := hQ
  have hfe : f = widthOut M (Nat.card Q) := by
    funext w
    obtain ⟨T, hT, -⟩ := exists_halt_time M w (hM w)
    rw [widthOut, if_pos (widthLe_card M w hT), runOut_eq M w (hM w)]
  rw [hfe]
  exact boundedWidth_isRegular M _

end Lax916827Proofs.Transducers
