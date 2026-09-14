import Lax264807.MonadicDependence
import Lax199508.NowhereDenseClasses

/-!
---
title: Nowhere dense classes are monadically dependent
type: theorem
---
Every nowhere dense graph class is monadically dependent. Together with
the statement that weakly sparse monadically dependent classes are
nowhere dense, this carries the classical equivalence: on weakly sparse
classes, monadic dependence and nowhere denseness coincide.

# Formalization notes

Adler and Adler proved that nowhere dense classes are monadically
*stable*; monadic dependence is the weakening stated here, which is how
the equivalence is used in the literature. The hypothesis is
`NowhereDense`, the shallow-minor definition of the *Sparsity Lectures*
submission (Lax199508), where nowhere denseness is defined and endorsed.
-/

namespace Lax264807.AdlerAdler

open Lax199508.GraphClasses Lax199508.NowhereDenseClasses
open Lax264807.MonadicDependence

/-- Nowhere dense graph classes are monadically dependent. -/
axiom monadicallyDependent_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    MonadicallyDependent C

end Lax264807.AdlerAdler
