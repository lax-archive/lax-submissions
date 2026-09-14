import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
---
title: Graph minors
type: definition
---

![Graph minor illustration](https://raw.githubusercontent.com/lax-archive/lax-submissions/4dd917c8b9a1e181ec951b7f6fa384262af31fa9/planar-graph-classes-v4-33/assets/graph-minor.svg "Graph minor illustration")

A graph *H* is a minor of a graph *G* when the vertices of *H* can be
represented by pairwise disjoint connected branch sets in *G*, with an edge
joining the corresponding branch sets for every edge of *H*.
-/

set_option autoImplicit false

namespace Lax68.GraphMinors

structure MinorModel {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  branchSet : W → Set V
  connected : ∀ w, (G.induce (branchSet w)).Connected
  disjoint :
    ∀ {u v}, u ≠ v →
      Disjoint (branchSet u) (branchSet v)
  adjacent :
    ∀ {u v}, H.Adj u v →
      ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y

def IsMinor {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (MinorModel H G)

abbrev K5 : SimpleGraph (Fin 5) :=
  SimpleGraph.completeGraph (Fin 5)

abbrev K4 : SimpleGraph (Fin 4) :=
  SimpleGraph.completeGraph (Fin 4)

abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) :=
  completeBipartiteGraph (Fin 3) (Fin 3)

abbrev K23 : SimpleGraph (Fin 2 ⊕ Fin 3) :=
  completeBipartiteGraph (Fin 2) (Fin 3)

end Lax68.GraphMinors
