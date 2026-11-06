import Lax185574.DpMinimality
import Lax185574.MonadicDependence

/-!
---
title: Monadically dependent classes are dp-minimal
type: lemma
---
Every monadically dependent graph class is dp-minimal.

# Formalization notes

Monadic dependence is that of `Lax185574.MonadicDependence`, by
transductions. The graphs are those of a `GraphClass`, which are finite.
-/

namespace Lax185574.MonadicDependenceDpMinimal

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.DpMinimality

/-- **Monadic dependence implies dp-minimality.** -/
axiom dpMinimal_of_monadicallyDependent (C : GraphClass) (hC : MonadicallyDependent C) :
    DpMinimal C

end Lax185574.MonadicDependenceDpMinimal
