This submission puts the finite Ramsey theorems for pairs and for tuples
on the archive as citable, dependency-free statements: a colouring of the
pairs or of the ordered tuples of a large enough finite set admits a
large homogeneous subset. Mathlib states no finite Ramsey theorem at the
pinned revision.

Three theorems are stated over one definition, the order type of a tuple
over a linearly ordered set: the multicolour Ramsey theorem for pairs,
that every colouring of the unordered pairs of a large enough finite set
with *k* colours has a monochromatic subset of any requested size;
Ramsey's theorem in the graph form the literature cites, that every large
enough graph has a clique on *a* vertices or an independent set on *b*
vertices; and the Erdős–Rado theorem for tuples, that every colouring of
the *l*-tuples over a large enough linearly ordered finite set has a
large subset on which the colour of a tuple depends only on its order
type. All three are existential bounds over the canonical carriers
`Fin n`, with sizes counted by `Set.ncard`; no Ramsey number is defined,
since no statement here consumes a numeric bound.

The graph form is discharged by a glue proof from the multicolour
statement alone: a pair is coloured by whether it is an edge, and the two
colour classes are read as a clique and as an independent set. The
multicolour statement is proved by induction on the list of colours from
the two-colour case, the Erdős–Szekeres neighbourhood-splitting
induction; the tuple statement by Erdős–Rado chain building for
strict-monotone tuples, followed by factoring an arbitrary tuple through
its rank pattern and iterating over the finitely many patterns.
