import Lax68.GraphMinors
import Lax994427.SixColorable

/-!
---
title: Hadwiger's conjecture for t = 7
type: theorem
---
Every finite graph with no *K*₇ minor is 6-colourable. This is the first open
case of Hadwiger's conjecture.

# Formalization notes

Finite graphs are stated on the canonical carriers `Fin n`. The complete
seven-vertex graph is written directly as `SimpleGraph.completeGraph (Fin 7)`;
introducing a named abbreviation would add no reusable notion beyond the
existing complete-graph construction.

The minor relation is exactly `Lax68.GraphMinors.IsMinor` from the Planar
Graph Classes submission: a minor model consists of pairwise disjoint,
connected branch sets, with an edge between the appropriate branch sets for
every edge of the modeled graph. Six-colourability is the separate definition
introduced by this submission.

# Research directions

Potential intermediate cases add structure to the excluded-minor hypothesis,
for example by bounding the independence number, excluding specified induced
subgraphs, or requiring a special graph decomposition. These strengthen the
hypotheses but leave the conclusion unchanged.
-/

namespace Lax994427.HadwigerT7

/-- Hadwiger's conjecture at `t = 7`: excluding a `K₇` minor guarantees a
proper colouring with six colours. -/
axiom sixColorable_of_no_K7_minor :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬ Lax68.GraphMinors.IsMinor
        (SimpleGraph.completeGraph (Fin 7)) G →
      Lax994427.SixColorable.IsSixColorable G

end Lax994427.HadwigerT7
