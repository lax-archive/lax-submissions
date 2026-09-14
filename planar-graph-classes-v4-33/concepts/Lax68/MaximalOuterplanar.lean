import Lax68.Outerplanar
import Lax68.Planar

/-!
---
title: Maximal outerplanar graphs
type: definition
---
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

/-- Every maximal outerplanar graph is outerplanar. -/
axiom maximalOuterplanar_outerplanar {V : Type*} {G : SimpleGraph V} :
  Lax68.MaximalOuterplanar.IsMaximalOuterplanar G →
  Lax68.Outerplanar.IsOuterplanar G

/-- Every maximal outerplanar graph is planar. -/
axiom maximalOuterplanar_planar {V : Type*} {G : SimpleGraph V} :
  Lax68.MaximalOuterplanar.IsMaximalOuterplanar G →
  Lax68.Planar.IsPlanar G

end Lax68.MaximalOuterplanar
