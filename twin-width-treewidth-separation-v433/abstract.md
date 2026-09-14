This submission proves the Bonnet–Déprés separation in the form: for every
natural number $k$, there is a finite simple graph $G$ with
$\mathrm{treewidth}(G) \le 2k+4$ and $2^k < \mathrm{twinWidth}(G)$.

The Lean statement is the paper's Theorem 1 at $\varepsilon = 1/2$ with
$t = 2k+3$ apices: $BD_k$ is $G_{t,\varepsilon}$, its feedback vertex set of
size $t$ gives treewidth at most $t+1 = 2k+4$, and the paper's bound
$2^{(1-\varepsilon)t} \ge 2^{k+1}$ is weakened to $2^k$.

Ported from the original formalization by Édouard Bonnet
(github.com/EdouardBonnet/leaning, `twin-width`, MIT-licensed).
