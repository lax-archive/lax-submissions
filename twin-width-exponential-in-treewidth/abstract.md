This submission states Bonnet and Déprés's *Twin-width can be exponential in
treewidth* (arXiv:2204.07670) with the paper's constants. Its main theorem:
for every real $0 < \varepsilon \le 1/2$ and integer $t > 1/\varepsilon$,
there is a graph $G_{t,\varepsilon}$ with a feedback vertex set of size $t$
and twin-width greater than $2^{(1-\varepsilon)t}$.

The graph $G_{t,\varepsilon}$ is defined explicitly, and the paper's lemmas
about it — treewidth at most $t+1$, twin-width greater than
$2^{(1-\varepsilon)t}$, oriented twin-width at most $t+1$, grid number at
most $t+2$ — and its four corollaries — twin-width exponential in treewidth,
in grid number, and in oriented twin-width, and an apex multiplying
twin-width by $2-\varepsilon$ — are each a concept. Treewidth and twin-width
are the parameters of lax-48, which proves the instance $\varepsilon = 1/2$,
$t = 2k+3$ of the main theorem with the bound weakened to $2^k$.
