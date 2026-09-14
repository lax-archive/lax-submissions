/-
The effectivity statements used by Theorem `thm:decidable-equivalence-regular` of *Transducers*
(M. Bojańczyk): equivalence is decidable for regular functions.  Both are now **proved**, and the
theorem is unconditional.

The mathematical content of the book's proof is developed in full in this project: the reduction of
the equality of two regular functions to the equivalence of two weighted automata over `ℚ`, through
the prime decomposition and the constructions for map reverse and map duplicate, is in
`RequestProject/PartC/WeightedRegClosure.lean`, and its conclusion
`Transducers.regularFun_eq_of_short` is exactly the decision procedure in semantic form: two
regular functions over a finite input alphabet are equal as soon as they agree on the finitely many
inputs of length at most a bound coming from Schützenberger's criterion.

The *formal* statement of Theorem `thm:decidable-equivalence-regular`, however, asks for a
`Computable` decision procedure on finite descriptions of two-way transducers.  Two effectivity
statements are needed for that, and both are proved.

* Two coded two-way transducers can be compared effectively on a given input.  This is
  `Transducers.EffectiveTwoWayEvalEq` in `RequestProject/PartC/TwoWaySimPrimrec.lean`, from the
  fuel-bounded simulation of `RequestProject/PartC/TwoWaySim.lean`.  It used to be assumed, because
  Mathlib's `Primrec`/`Computable` API has no arithmetic on `ℤ` or on `ℚ`; that arithmetic, and the
  operations on lists that go with it, are now developed as a general-purpose library in
  `RequestProject/Common/PrimrecArith.lean` and `RequestProject/Common/PrimrecList.lean`, and it
  turned out that the comparison of two coded two-way transducers needs no rational arithmetic at
  all -- only a bound on the length of a halting run, which is
  `Transducers.RegDec.halt_time_lt_fuel`.

* An equivalence bound can be *computed* from the two codes.  This is `EffectiveTwoWayBound` below;
  it used to be assumed, and is now proved as `Transducers.effectiveTwoWayBound` in
  `RequestProject/PartC/RegEffBound.lean`, with the explicit bound
  `Transducers.RegDec.codeBound`.  The docstring of `EffectiveTwoWayBound` describes both the
  obstacle that made it a hypothesis and the route that removes it.

Everything else -- that the finitely many strings to be tested may be taken over the letters of the
two codes together with one fresh letter (`RequestProject/PartC/RegCodeSan.lean`), and the assembly
of the decision procedure -- is discharged in full in `RequestProject/PartC/RegEqDec.lean`. -/
import Lax916827Proofs.Source.PartC.TwoWaySimPrimrec
import Lax132576Proofs.Source.PartB.Codes
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- **A computable equivalence bound** (formerly an effectivity hypothesis; now **proved**, see
`Transducers.effectiveTwoWayBound` in `RequestProject/PartC/RegEffBound.lean`).

There is a computable function `N` which, given two codes of two-way
transducers, returns a length bound with the following property: two total coded
two-way transducers that agree on all inputs of length at most `N c₁ c₂`
compute the same relation.

*Why it used to be a hypothesis.*  The *mathematical* content of the statement -- that such a bound
exists for every pair of codes -- was already proved in `RequestProject/PartC/RegCodeBound.lean`
(`Transducers.exists_twoWayCode_bound`), from the conclusion `Transducers.regularFun_eq_of_short` of
the book's proof of Theorem `thm:decidable-equivalence-regular` in
`RequestProject/PartC/WeightedRegClosure.lean`: a coded two-way transducer computes a regular
function (Theorem `thm:2dfa-decomposition-into-primes`, `Transducers.twoWay_isRegular`), the
equality of two regular functions is the zeroness of a weighted automaton over `ℚ` obtained from
them, and Schützenberger's criterion bounds the length of a witness of non-zeroness by the dimension
of a linear representation of that automaton.  But the bound so obtained is *not* a computable
function of the two codes: it comes out of three existential statements over abstract finite types,
none of which carries any size information --
`Transducers.isRegularFun_of_isTwoWay` (`RequestProject/PartC/SnakeReg.lean`), whose conclusion
`IsRegularFun` is an existential over compositions of primes produced by an induction on the width
of the run; `Transducers.isWeighted_comp_regular` and `Transducers.exists_injective_weighted`
(`RequestProject/PartC/WeightedRegClosure.lean`), whose conclusion `IsWeighted` is an existential
over an abstract finite state space; and `Transducers.weighted_eq_of_short`
(`RequestProject/PartB/WeightedZero.lean`), which supplies the bound as the sum of the dimensions of
two linear representations built from those abstract types.

*How it is proved.*  Not by making that chain effective -- the effective, code-to-code form of the
book's reduction to weighted automata is stated for the record as
`Transducers.EffectiveTwoWayWeighted` in `RequestProject/PartC/RegBoundGap.lean`, and remains
unbuilt -- but by a direct argument that produces the bound as a formula.  The value of the output
of a two-way transducer on `u ++ v` is decomposed, in `RequestProject/PartC/RegHankel.lean`, as a
finite sum `∑ ι, g ι u * h ι v` indexed by the crossing data at the cut: the letter at the cut, the
crossing sequence of states, and two indices into it.  That index set has an explicit size
(`Transducers.RegHankel.idxBound`), so the rank criterion
`Transducers.HankelRank.zero_of_short` gives an explicit length bound
(`Transducers.RegHankel.twoWay_eq_of_short`, `RequestProject/PartC/RegShort.lean`), and reading the
number of letters and states off the two code tables turns it into the primitive recursive
`Transducers.RegDec.codeBound`. -/
def EffectiveTwoWayBound : Prop :=
  ∃ N : TwoWayCode → TwoWayCode → ℕ, Computable₂ N ∧
    ∀ c₁ c₂, TwoWayCodeTotal c₁ → TwoWayCodeTotal c₂ →
      ((∀ w : List ℕ, w.length ≤ N c₁ c₂ → twoWayCodeRel c₁ w = twoWayCodeRel c₂ w) →
        twoWayCodeRel c₁ = twoWayCodeRel c₂)

end Lax916827Proofs.Transducers
