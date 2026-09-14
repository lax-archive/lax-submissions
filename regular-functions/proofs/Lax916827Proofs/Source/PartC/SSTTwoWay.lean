/- Every function computed by a streaming string transducer is computed by a two-way transducer: the
"sst to regular" half of Theorem `theorem:sst-two-way-equivalence` of *Transducers* (M. Bojańczyk),
through Theorem `thm:2dfa-decomposition-into-primes`.

The book's argument runs the two-way transducer over the *register flow tree* of
the sst: the composition of all the register updates applied along the input,
followed by the final output function.  The output of the sst is the string
obtained by a depth-first traversal of that tree, and a two-way transducer can
perform that traversal directly on the input string, provided that it can see,
at every position, the state of the sst before reading that position -- which is
an annotation computed by a Mealy machine, hence a rational function, and
two-way transducers are closed under pre-composition with rational functions
(Corollary `cor:2dfa-closure-under-composition`).

The copyless restriction is what makes the traversal possible: when the
traversal of the content of a register `y` at position `i-1` is finished, the
place at which it has to be resumed at position `i` is determined by `y` and by
the letter at position `i`, because `y` occurs at most once in the whole update
applied at position `i`.

The traversal itself is carried out in `RequestProject/PartC/SSTWalk.lean`, for
the *normalised* streaming string transducers of
`RequestProject/PartC/SSTNorm.lean`, to which the annotation reduces an
arbitrary sst.
-/
import Lax916827Proofs.Source.PartC.TwoWayRat
import Lax916827Proofs.Source.PartC.SSTWalk
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- **Theorem `theorem:sst-two-way-equivalence`, left-to-right implication (through Theorem
`thm:2dfa-decomposition-into-primes`).**  Every function computed by a streaming string transducer
is computed by a two-way transducer. -/
theorem isTwoWay_of_isSST {A B : Type} [Finite A] {f : List A → List B}
    (hf : IsSST f) : IsTwoWay f := by
  classical
  obtain ⟨Q, X, hQ, instX, T, rfl⟩ := hf
  haveI : Finite Q := hQ
  haveI : Finite (Q × A) := inferInstance
  obtain ⟨Y, instY, N, hN⟩ := exists_nsst_of_sst T
  have hrat : IsRationalFun (SSTNorm.annot T).eval :=
    PrimeRat.rationalFun_of_isMealy ⟨Q, hQ, SSTNorm.annot T, rfl⟩
  have hcomp : IsTwoWay (N.eval ∘ (SSTNorm.annot T).eval) :=
    isTwoWay_comp_rational hrat (isTwoWay_of_nsst N)
  rwa [show N.eval ∘ (SSTNorm.annot T).eval = T.eval from funext hN] at hcomp

end Lax916827Proofs.Transducers
