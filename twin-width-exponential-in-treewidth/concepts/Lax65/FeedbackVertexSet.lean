import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
---
title: Feedback vertex set
type: definition
---
A feedback vertex set of a graph *G* is a set of vertices whose deletion
leaves a forest: the subgraph of *G* induced on the remaining vertices has no
cycle.
-/

namespace Lax65.FeedbackVertexSet

/-- `X` is a feedback vertex set of `G`: the subgraph induced on the vertices
outside `X` is acyclic. -/
def IsFeedbackVertexSet {V : Type} (G : SimpleGraph V) (X : Finset V) : Prop :=
  (G.induce {v | v ∉ X}).IsAcyclic

/-- `G` has a feedback vertex set of size `t`. -/
def HasFeedbackVertexSetOfSize {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ X : Finset V, IsFeedbackVertexSet G X ∧ X.card = t

end Lax65.FeedbackVertexSet
