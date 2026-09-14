import Lax264807.GraphClasses
import Lax264807.MonadicDependence
import Lax199508.NowhereDenseClasses

/-!
---
title: Weakly sparse monadically dependent classes are nowhere dense
type: theorem
---
Every weakly sparse monadically dependent graph class is nowhere dense.
Together with the statement that nowhere dense classes are monadically
dependent, this carries the classical equivalence: on weakly sparse
classes, monadic dependence and nowhere denseness coincide.

# Formalization notes

The hypotheses are the weak sparseness predicate of the graph classes
concept of this submission and the transduction-based definition of
monadic dependence; the conclusion is `NowhereDense`, the shallow-minor
definition of the *Sparsity Lectures* submission (Lax12), where nowhere
denseness is defined and endorsed. Stating the conclusion over that
definition is what lets this statement compose directly with the
sparsity theory built on it.
-/

namespace Lax264807.WeaklySparseDependent

open Lax199508.GraphClasses Lax199508.NowhereDenseClasses
open Lax264807.GraphClasses Lax264807.MonadicDependence

/-- Every weakly sparse monadically dependent graph class is nowhere
dense. -/
axiom nowhereDense_of_weaklySparse_of_monadicallyDependent
    (C : GraphClass) (hs : WeaklySparse C) (hd : MonadicallyDependent C) :
    NowhereDense C

end Lax264807.WeaklySparseDependent
