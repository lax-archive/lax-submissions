import Lax185574.DpMinimality
import Lax185574.MonadicDependence

/-!
---
title: Monadic dependence and dp-minimality coincide on graph classes
type: corollary
---
A graph class is monadically dependent if and only if it is dp-minimal.

# Formalization notes

Monadic dependence is that of `Lax185574.MonadicDependence`, by
transductions. The statement is for the finite graphs of a `GraphClass`.
-/

namespace Lax185574.DpMinimalEquivalence

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.DpMinimality

/-- **Monadic dependence is dp-minimality.** -/
axiom monadicallyDependent_iff_dpMinimal (C : GraphClass) :
    MonadicallyDependent C ↔ DpMinimal C

end Lax185574.DpMinimalEquivalence
