Simple graphs occur in several formally distinct guises. This submission
establishes precise bridges from `SimpleGraph V` to five of them: symmetric
loopless digraphs, simple loopless multigraphs, spanning 2-uniform
hypergraphs, 2-uniform edge set systems, and vertex-indexed neighborhood set
systems.

For digraphs, hypergraphs, edge set systems, and neighborhood set systems the
comparison is an equivalence of the corresponding types. A simple multigraph
is compared with a simple graph up to simultaneous vertex and edge
isomorphism, because `Graph α β` keeps ambient vertex and edge types.
Looplessness of the hypergraph and edge-set-system representations is derived
from 2-uniformity rather than recorded as redundant data.

Neighborhood systems retain their vertex indexing: the neighborhood assigned
to `u` is exactly the set of vertices adjacent to `u`. This indexing is what
makes the construction invertible even when two vertices have the same open
neighborhood.

Together these results make the representation choice modular: a statement
may be proved in the graph language best suited to it and transported across
the appropriate equivalence or isomorphism, subject only to the usual
isomorphism-invariance requirement in the multigraph case.
