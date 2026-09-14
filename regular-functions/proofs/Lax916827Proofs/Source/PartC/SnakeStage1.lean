/-
**Stage 1 of the induction step of the book's snake lemma**: the rational
function that marks the record-breaking columns of a run and the pieces of the
record-breaker decomposition inside the blocks that they delimit.

Everything else in the induction step is proved elsewhere:

* the decomposition of a halting run of width at most `K` into the pieces of the
  record-breaker decomposition is `TwoWay.runOut_eq_partsOut`
  (`RequestProject/PartC/SnakeParts.lean`);
* the identification of each piece with the whole run of a *window transducer*
  on a factor of the input, to which the induction hypothesis applies, is
  `TwoWay.exists_widthOut_excHalves`, `TwoWay.exists_widthOut_prog`
  (`RequestProject/PartC/SnakePieceIdent.lean`) and
  `TwoWay.exists_widthOut_finalProg_confined`
  (`RequestProject/PartC/SnakeFinalConf.lean`);
* the *block function*, which recomputes the pieces of one pair of neighbouring
  blocks from the annotated input, is regular (`TwoWay.isRegularFun_blockFun`),
  and the neighbouring-block map combinator applied to it computes the output of
  the run (`TwoWay.pairMap_blockFun_eq_runOut`), both in
  `RequestProject/PartC/SnakeBlock.lean`;
* **a correct marking of the input exists** for every nonempty input whose run
  halts and has width at most `K` (`TwoWay.exists_isSnakeMarking`,
  `RequestProject/PartC/SnakeData.lean`): the blocks are cut at the
  record-breaking columns and every piece is confined to the pair of blocks that
  carries it.  This is the mathematical content of the book's first stage.

What is proved here is the *machine-theoretic* content of that stage: *"we mark
the record-breakers, i.e. we compute the string `w₀ # w₁ # ⋯ # wₙ`, where `wᵢ` is
the part of the input string between the record-breakers `xᵢ₋₁` and `xᵢ`.  This
stage can be implemented by a rational function, since a nondeterministic
automaton with output can guess the record-breakers, and then check that they
satisfy the conditions in the definition."*

It is carried out in exactly that shape.  What has to be produced is the
language of the *checking* automaton, that is, a **regular language of correctly
annotated inputs** which contains an annotation of every input; this is
`TwoWay.exists_regular_snakeLang`, proved in
`RequestProject/PartC/SnakeChkMain.lean` on top of
`RequestProject/PartC/SnakeChkEnc.lean` (the annotated alphabet and the checking
condition), `RequestProject/PartC/SnakeChkGeom.lean` (soundness) and
`RequestProject/PartC/SnakeChkComp.lean` (completeness).  Guessing and checking
is then Nivat's construction (`Transducers.isRationalRel_of_regular_nivat`,
`RequestProject/PartB/GuessCheck.lean`): a regular language of annotations, read
through the homomorphism that erases the annotation and written through the
homomorphism that produces the marked string, is a rational relation
(`TwoWay.exists_rational_snakeRel`).  Since a total rational relation contains
the graph of a rational function (`Transducers.exists_rationalFun_of_total_rel`,
Lemma `lem:uniformisation`), this gives the regular function that the induction step needs
(`TwoWay.exists_snakeMarking`), and no functionality of the guessing has to be
proved.

Two side conditions of the statements below deserve a comment.

* Only a *regular* annotation is asked for, not a rational one: the annotation
  is composed with the regular function `pairMap (blockFun …)`, so regularity is
  all that the assembly of the induction step uses.
* The empty input is excluded.  On the empty input the annotation has no letters
  at all, so it cannot carry the parameters of the pieces, while the run may
  perfectly well produce a nonempty output; the induction step therefore treats
  the empty input separately, by a case distinction over the regular language
  `{[]}` (`Transducers.boundedWidth_isRegular_step`).
-/
import Lax916827Proofs.Source.PartC.SnakeChkMain
import Lax132576Proofs.Source.PartB.UniformFun
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open RegPair

variable {A B Q : Type}

/-- **Stage 1, as a rational relation.**  Guessing an annotation, checking it
against the regular language of `TwoWay.exists_regular_snakeLang` and inserting
the separators is a total rational relation all of whose values are correct
markings (Nivat's construction, `Transducers.isRationalRel_of_regular_nivat`). -/
theorem exists_rational_snakeRel [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) {K : ℕ}
    (hK : 2 ≤ K) :
    ∃ R : List A → List (Option (SnakeLet A Q (2 * (2 * K + 1)))) → Prop,
      IsRationalRel R ∧ (∀ w, ∃ v, R w v) ∧ (∀ w v, R w v → SnakeRel M K w v) := by
  classical
  obtain ⟨Γ, hΓ, inH, outH, L, hreg, hsound, hcover⟩ := exists_regular_snakeLang M hK
  haveI := hΓ
  refine ⟨fun w v => ∃ u ∈ L, homOf inH u = w ∧ homOf outH u = v,
    isRationalRel_of_regular_nivat _ _ hreg, ?_, ?_⟩
  · intro w
    obtain ⟨u, hu, hup⟩ := hcover w
    exact ⟨homOf outH u, u, hu, hup, rfl⟩
  · rintro w v ⟨u, hu, rfl, rfl⟩
    exact hsound u hu

/-- **The marking of stage 1 is computed by a regular function**: the guessing
relation of `TwoWay.exists_rational_snakeRel` is total and rational, hence it
contains the graph of a rational -- so regular -- function (Lemma `lem:uniformisation`). -/
theorem exists_snakeMarking [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) {K : ℕ}
    (hK : 2 ≤ K) :
    ∃ ann : List A → List (Option (SnakeLet A Q (2 * (2 * K + 1)))),
      IsRegularFun ann ∧ ∀ w : List A, SnakeRel M K w (ann w) := by
  classical
  obtain ⟨R, hRat, hTot, hSound⟩ := exists_rational_snakeRel M hK
  obtain ⟨f, hf, hfR⟩ := exists_rationalFun_of_total_rel hRat hTot
  exact ⟨f, IsRegularFun.of_rational hf, fun w => hSound w (f w) (hfR w)⟩

/-- **The output of the run is recomputed from the marking** by the
neighbouring-block map combinator applied to the block function. -/
theorem widthOut_eq_pairMap [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) (K : ℕ)
    {ann : List A → List (Option (SnakeLet A Q (2 * (2 * K + 1))))}
    (hann : ∀ w : List A, SnakeRel M K w (ann w))
    {w : List A} (hw : w ≠ []) :
    widthOut M K w = pairMap (blockFun M (K - 1) (2 * K + 1)) (ann w) :=
  (hann w hw).symm

end TwoWay

end Lax916827Proofs.Transducers
