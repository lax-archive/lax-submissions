This submission proves the Bonnet–Déprés separation in the form: for every
natural number $k$, there is a finite simple graph $G$ with
$\mathrm{treewidth}(G) \le 2k+4$ and $2^k < \mathrm{twinWidth}(G)$.

The concept surface has three review units: the complete definition of
treewidth, the complete definition of twin-width, and the separation theorem.
Treewidth is phrased through tree decompositions with a bag-size bound;
twin-width through contraction sequences of vertex partitions whose red
degrees are derived from homogeneity in the graph, so no auxiliary state is
carried alongside the partitions. Both parameters are infima of explicit sets
of naturals, and the separation is stated over the canonical finite vertex
types $\mathrm{Fin}\ n$. The proof constructs the explicit Bonnet–Déprés
graph $BD_k$ in a trigraph-based source development and bridges it to the
submitted concepts through the invariant that, along any contraction
sequence, black pairs are exactly the complete pairs and red pairs exactly
the non-homogeneous pairs.

The submission carries the paper it formalizes, Bonnet and Déprés's
*Twin-width can be exponential in treewidth* (arXiv:2204.07670), with its
abstract, both definitions of twin-width, the main theorem, and the proof
section marked. The Lean statement is the paper's Theorem 1 at
$\varepsilon = 1/2$ with $t = 2k+3$ apices: $BD_k$ is $G_{t,\varepsilon}$,
its feedback vertex set of size $t$ gives treewidth at most $t+1 = 2k+4$, and
the paper's bound $2^{(1-\varepsilon)t} \ge 2^{k+1}$ is weakened to $2^k$.

Ported from the original formalization by Édouard Bonnet
(github.com/EdouardBonnet/leaning, `twin-width`, MIT-licensed).
