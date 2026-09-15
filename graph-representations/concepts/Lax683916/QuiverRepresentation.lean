import Lax683916.ThinSymmetricLooplessQuivers

/-!
---
title: Quiver representation of simple graphs
type: theorem
---
Every thin, symmetric, loopless quiver on `V` is hom-wise isomorphic to the
adjacency quiver obtained from a simple graph on `V`.

# Formalization notes

The simple graph records whether each arrow type is inhabited. The three
properties bundled with the quiver make this a simple-graph adjacency
relation, and thinness makes every original arrow type equivalent to its
inhabitation proposition. The theorem preserves the vertex type exactly;
the reverse construction is the definition `ofSimpleGraph`.
-/

namespace Lax683916.QuiverRepresentation

open Lax683916.ThinSymmetricLooplessQuivers

universe u v

/-- Every thin symmetric loopless quiver has a simple-graph representation. -/
axiom exists_simpleGraph_representation {V : Type u}
    (Q : ThinSymmetricLooplessQuiver.{u, v} V) :
  ∃ G : SimpleGraph V, Nonempty (Isomorphic Q (ofSimpleGraph G))

end Lax683916.QuiverRepresentation
