/- The effectivity statements used by the decidability results of Section *Rational relations and
weighted automata* of *Transducers* (M. Bojańczyk).

Theorems `thm:equivalence-weighted-automata`, `thm:equivalence-rational-functions`,
`thm:zeroness-weighted-automata` and `thm:decide-if-mealy` are decidability statements about
weighted automata over the field `ℚ` and about rational functions.  Their mathematical content is
developed in full in this project (Schützenberger's zeroness criterion in
`RequestProject/PartB/WeightedZero.lean`, its effective form in
`RequestProject/PartB/WeightedBound.lean`, the reduction of equivalence of rational functions to
equivalence of weighted automata in `RequestProject/PartB/PairWeighted.lean`,
`RequestProject/PartB/PairWeightedEval.lean` and `RequestProject/PartB/RatEqDec.lean`), but their
*formal* statements ask for a `Computable` decision procedure in the sense of Mathlib's
`Mathlib.Computability.Partrec`.

Both effectivity statements that these results need are now **proved**, and neither is a hypothesis
any more:

* `Transducers.EffectiveWeightedEvalEq` -- a computable equality test for the values of two coded
  weighted automata over `ℚ` -- is proved in `RequestProject/PartB/WCodePrimrec.lean`.  It used to
  be assumed, because Mathlib's `Primrec`/`Computable` API contains no arithmetic on `ℤ` or on `ℚ`;
  that arithmetic is now developed, as a general-purpose library independent of transducers, in
  `RequestProject/Common/PrimrecArith.lean` and `RequestProject/Common/PrimrecList.lean`, and the
  bounded enumeration of the accepting runs of a valid code is carried out in
  `RequestProject/PartB/WCodeRunBound.lean` and `RequestProject/PartB/WCodeEnum.lean`.
* `EffectiveWeightedBound`, an effective form of the Schützenberger bound, is stated below and
  proved in `RequestProject/PartB/WeightedBound.lean` (`Transducers.effectiveWeightedBound`).

This file therefore only carries the statement of the bound; it is kept here, where the decision
procedures of Section *Rational relations and weighted automata* look for it.
-/
import Lax132576Proofs.Source.PartB.WCodePrimrec
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-- **An effective Schützenberger bound.**

There is a computable function `N` which, given two codes of weighted automata
over `ℚ`, returns a length bound with the following property: two valid coded
weighted automata that agree on all strings of length at most `N c₁ c₂` compute
the same function.

This is *not* a hypothesis: it is proved in `RequestProject/PartB/WeightedBound.lean`
(`Transducers.effectiveWeightedBound`), with the explicit bound `Transducers.wcodeBound`.  The
statement is kept here, next to the hypothesis above, because that is where the decision procedures
of Section *Rational relations and weighted automata* look for it.

The proof is the effective form of Schützenberger's criterion.
`Transducers.linRep_eq_of_short` (in `RequestProject/PartB/WeightedZero.lean`)
shows that two functions given by linear representations of dimensions `d₁` and
`d₂` agree everywhere as soon as they agree on the strings of length at most
`d₁ + d₂`, and `Transducers.WBound.exists_linRep_bounded` produces a linear
representation whose dimension is bounded by an explicit function of the code:
the representation has one dimension per useful state of the normalised
automaton, and a useful state is either an initial state or the target of a
transition, hence one of the `1 + |initial states|` initial states of the
normalised automaton or one of the states `cfg t x` where `t` is a lifted or
copied transition and `x` a suffix of its input string.  Nothing here involves
arithmetic on the weights, so the bound is a primitive recursive function of the
two codes. -/
def EffectiveWeightedBound : Prop :=
  ∃ N : WCode → WCode → ℕ, Computable₂ N ∧
    ∀ c₁ c₂, WCodeValid c₁ → WCodeValid c₂ →
      ((∀ v : List ℕ, v.length ≤ N c₁ c₂ → wcodeEval c₁ v = wcodeEval c₂ v) →
        wcodeEval c₁ = wcodeEval c₂)

end Lax132576Proofs.Transducers
