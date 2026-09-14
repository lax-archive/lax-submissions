/-
Part D: Polyregular functions
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Part D and the statements of its
theorems and lemmas.  All of them are proved: Theorem
`thm:polyregular-functions-are-continuous`, Theorem `thm:for-transducers-are-polyregular`, Lemma
`lemma:prenex-normal-form`, Lemma `lem:for-closed-under-composition`, Theorem
`thm:pebble-are-continuous` and Theorem `thm:pebble-are-for`.

The five results of Section *Pebble transducers* that speak about the string representation of
configurations and of child configuration graphs -- Lemma `lem:reachability-pebble-automaton` and
Claim `claim:reachability-basic-run` (`RequestProject/PartD/PebReach.lean`), Claim
`claim:from-child-configuration-graph-to-children` (`RequestProject/PartD/ChildGraphFor.lean`), and
Claim `claim:from-configuration-to-child-configuration-graph` together with Lemma
`lem:children-of-configuration-in-pebble-run` (`RequestProject/PartD/CGFor.lean`) -- are proved as
well, but in files that come *after* this one, because two of them are obtained from Theorem
`thm:pebble-are-for` and Theorem `thm:for-transducers-are-polyregular`, which are stated here.
The two headline theorems are therefore not proved through those five results: Theorem
`thm:pebble-are-continuous` is proved from the regularity of the languages of pebble automata
(`RequestProject/PartD/PebbleLev1.lean`), of which Lemma `lem:reachability-pebble-automaton` is
another consequence, and the step of Theorem `thm:pebble-are-for` for which the book uses Lemma
`lem:children-of-configuration-in-pebble-run` -- that a pebble transducer computes a polyregular
function -- is proved by the induction on the number of pebbles of
`RequestProject/PartD/PebblePoly.lean`. -/
import Lax314295Proofs.Source.PartC.MSO
import Lax194892Proofs.Source.PartD.PolyDef
import Lax194892Proofs.Source.PartD.ForCompTop
import Lax194892Proofs.Source.PartD.PolyFor
import Lax194892Proofs.Source.PartD.PebbleReg
import Lax194892Proofs.Source.PartD.PebblePoly
import Lax194892Proofs.Source.PartD.PebbleForTop
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers
open Lax314295Proofs Lax314295Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-! ## Polyregular functions (Definition `def:polyregular-functions`) -/

/-! **Example 33 (Marked squaring)** (`markedSquare`) is defined in
`RequestProject/PartD/MarkedSquare.lean`, together with the proof that it is continuous, which is
the main step in the proof of Theorem `thm:polyregular-functions-are-continuous` below. -/

/-! The family of prime polyregular functions (`Transducers.PolyregularFam`) and Definition
`def:polyregular-functions` itself (`Transducers.IsPolyregular`) are defined, unchanged, in
`RequestProject/PartD/PolyDef.lean`, so that the constructions proving Theorem
`thm:for-transducers-are-polyregular` can be developed before the statements below. -/

/-- **Theorem `thm:polyregular-functions-are-continuous`.**  Polyregular functions are continuous. -/
theorem polyregular_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPolyregular f) : Continuous f := by
  induction hf with
  | base h =>
      rcases h with hreg | ⟨A₀, e, e', hfe⟩
      · exact continuous_of_isRegularFun hreg
      · exact Lax916827Proofs.Transducers.Continuous.congr
          (Lax916827Proofs.Transducers.Continuous.comp (continuous_map (e'.symm : A₀ ⊕ A₀ → _))
            (Lax916827Proofs.Transducers.Continuous.comp (continuous_markedSquare A₀) (continuous_map (e : _ → A₀))))
          (fun w => (hfe w).symm)
  | id A => exact continuous_id
  | comp _ _ ihf ihg => exact Lax916827Proofs.Transducers.Continuous.comp ihg ihf

/-! ## For-transducers

The syntax and the semantics of the for-transducers -- `Transducers.ForTest`,
`Transducers.ForProg`, `Transducers.ForTest.Holds`, `Transducers.forLoopRun`,
`Transducers.ForProg.exec`, `Transducers.ForProg.eval`, `Transducers.ForProg.LoopFree`,
`Transducers.ForProg.nestLoops`, `Transducers.ForProg.OutputsAtMostOne`, Definition
`def:prenex-normal-form-for-transducers` (`Transducers.ForProg.PrenexForm`) and
`Transducers.IsForTransducer` -- are defined, unchanged, in
`RequestProject/PartD/ForDef.lean`, so that the constructions proving Lemma
`lemma:prenex-normal-form` and Lemma `lem:for-closed-under-composition` can be developed before
the statements below. -/

/-! ### Equivalence with polyregular functions -/

/-- **Theorem `thm:for-transducers-are-polyregular`.**  A string-to-string function is polyregular
if and only if it is computed by a for-transducer. -/
theorem polyregular_iff_forTransducer {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsPolyregular f ↔ IsForTransducer f :=
  ⟨fun hf => isForTransducer_of_isPolyregular hf ‹Finite A› ‹Finite B›,
    PolyEnum.isPolyregular_of_isForTransducer⟩

/-- **Lemma `lemma:prenex-normal-form`.**  Every for-transducer is equivalent to one in prenex
form. -/
theorem forTransducer_prenex {A B : Type} (P : ForProg A B) :
    ∃ P' : ForProg A B, P'.PrenexForm ∧ ∀ w, P'.eval w = P.eval w :=
  forTransducer_prenex_aux P

/-- **Lemma `lem:for-closed-under-composition`.**  String-to-string functions computed by
for-transducers are closed under composition. -/
theorem forTransducer_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsForTransducer f) (hg : IsForTransducer g) : IsForTransducer (g ∘ f) :=
  forTransducer_comp_aux hf hg

/-! ## Pebble transducers

The syntax and the semantics of the pebble transducers -- `Transducers.PebbleView`,
`Transducers.viewOf`, `Transducers.PebbleAction`, `Transducers.Pebble`,
`Transducers.PebbleCfg`, `Transducers.Pebble.stepCfg`, `Transducers.Pebble.Reaches`,
`Transducers.Pebble.Computes` and `Transducers.IsPebbleTransducer` -- are defined, unchanged, in
`RequestProject/PartD/PebbleDef.lean`, so that the constructions proving Theorem
`thm:pebble-are-continuous` can be developed before the statements below. -/

/-! ### Continuity -/

/-- **Theorem `thm:pebble-are-continuous`.**  Pebble transducers compute continuous functions. -/
theorem pebble_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPebbleTransducer f) : Continuous f :=
  continuous_of_isPebbleTransducer hf

/-! ### Equivalence with for-transducers -/

/-- **Theorem `thm:pebble-are-for`.**  Pebble transducers and for-transducers compute the same
string-to-string functions. -/
theorem pebble_iff_forTransducer {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsPebbleTransducer f ↔ IsForTransducer f :=
  ⟨fun h => (polyregular_iff_forTransducer f).mp (isPolyregular_of_isPebbleTransducer h),
    PebFor.isPebbleTransducer_of_isForTransducer⟩

end Lax194892Proofs.Transducers
