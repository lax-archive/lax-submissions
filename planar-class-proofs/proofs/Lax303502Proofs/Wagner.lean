import Lax303502Proofs.KuratowskiObstructions
import Lax68.KuratowskiPlanarity
import Lax68.PlanarExcludedMinors

set_option autoImplicit false

namespace Lax303502Proofs

/--
---
conclusion: Lax68.PlanarExcludedMinors.planar_iff_excludedMinors
---
Wagner's characterization follows from Kuratowski's straight-line
characterization and the equivalence of the two forbidden pairs.
The only statement assumption is
`Lax68.KuratowskiPlanarity.planar_iff_kuratowskiFree`.

# Proof strategy

First prove the combinatorial equivalence independently of planarity. A
subdivision gives a minor by contracting every path towards one endpoint.
For the converse, choose one connecting edge for every adjacent pair of
minor branch sets. Three attachment vertices in a connected branch set have
paths meeting only at one center, so a `K₃,₃` minor gives a subdivision.

For a `K₅` minor, attach the fourth terminal to the three-arm construction at
its first point of contact. If every branch set gives four paths meeting
only at a center, the local paths combine into a subdivision of `K₅`.
Otherwise one branch set splits into two disjoint connected sets with two
attachments each and an edge between them. Those two sets and the other
four branch sets give a `K₃,₃` minor, to which the previous construction
applies. Finally use the assumed Kuratowski characterization to obtain the
original straight-line version of Wagner's theorem.

# Attribution

Diestel, *Graph Theory*, sixth edition,
[Chapter 4, Lemma 4.4.2, printed page 107](https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch4.pdf),
with the degree-three conversion from
[Chapter 1, Proposition 1.7.3](https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch1.pdf). The implementation
replaces the minimal-tree argument by explicit paths and their first points
of contact. Every minor branch set and subdivision route is constructed and
checked. No drawing theorem is used in the combinatorial bridge.
-/
theorem planar_iff_excludedMinors {V : Type*} {G : SimpleGraph V} :
    Finite V → (Lax68.Planar.IsPlanar G ↔ Lax68.Planar.IsPlanarByExcludedMinors G) := by
  intro hfin
  exact (Lax68.KuratowskiPlanarity.planar_iff_kuratowskiFree hfin).trans
    excludedMinors_iff_kuratowskiFree.symm

end Lax303502Proofs
