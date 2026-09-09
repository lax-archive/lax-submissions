import Lax48.TwinWidth

/-!
---
title: Cographs
type: definition
---
A finite graph is a cograph if it has twin-width zero.  Equivalently, it can
be reduced to one vertex by repeatedly contracting a pair of twins, without
ever creating a red edge.

# Formalization notes

The definition uses `HasTwinWidthAtMost G 0` rather than the numerical
equality `twinWidth G = 0`.  For finite graphs these are equivalent, while the
bounded predicate exposes the width-zero contraction sequence that witnesses
the property.  The bound really is zero, not one: the width convention counts
the maximum red degree and a cograph contraction creates no red adjacency.
-/

namespace Lax214022.Cographs

open Lax48.TwinWidth

/-- A finite graph is a cograph when it admits a contraction sequence of red
degree zero. -/
def IsCograph {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  HasTwinWidthAtMost G 0

end Lax214022.Cographs
