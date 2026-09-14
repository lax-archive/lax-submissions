import Lax68.Outerplanar

/-!
---
title: Maximal outerplanar graphs
type: definition
---

![Maximal outerplanar illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/4dd917c8b9a1e181ec951b7f6fa384262af31fa9/planar-graph-classes-v4-33/assets/maximal-outerplanar.svg "Maximal outerplanar illustration")

An outerplanar graph is maximal outerplanar when no edge can be added between
its existing vertices while preserving outerplanarity.
-/

set_option autoImplicit false

namespace Lax68.MaximalOuterplanar

def IsMaximalOuterplanar {V : Type*}
    (G : SimpleGraph V) : Prop :=
  Outerplanar.IsOuterplanar G ∧
    ∀ H : SimpleGraph V,
      G < H →
      ¬ Outerplanar.IsOuterplanar H

end Lax68.MaximalOuterplanar
