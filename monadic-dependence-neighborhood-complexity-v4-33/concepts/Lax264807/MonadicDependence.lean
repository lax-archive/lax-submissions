import Lax264807.GraphClasses
import Lax264807.GraphTransductions

/-!
---
title: Monadic dependence
type: definition
---
A graph class is monadically dependent (also called monadically NIP) if
it does not transduce the class of all graphs.

# Formalization notes

This is the standard transduction-based definition from the model theory
of graph classes, stated over the transduction relation of the
prerequisite concepts.
-/

namespace Lax264807.MonadicDependence

open Lax199508.GraphClasses Lax264807.GraphClasses

/-- A graph class is monadically dependent if it does not transduce the
class of all finite simple graphs. -/
def MonadicallyDependent (C : GraphClass) : Prop :=
  ¬ GraphTransductions.Transduces C allGraphs

end Lax264807.MonadicDependence
