import Lax710763.GraphClasses
import Lax710763.GraphTransductions

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

namespace Lax710763.MonadicDependence

open Lax199508.GraphClasses Lax710763.GraphClasses

/-- A graph class is monadically dependent if it does not transduce the
class of all finite simple graphs. -/
def MonadicallyDependent (C : GraphClass) : Prop :=
  ¬ GraphTransductions.Transduces C allGraphs

end Lax710763.MonadicDependence
