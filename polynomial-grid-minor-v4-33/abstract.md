This submission mainly follows Chuzhoy--Tan's *Towards tight(er) bounds for
the Excluded Grid Theorem*, but improves the resulting grid-minor bound. There
are positive integers $K$ and $b$ such that every finite simple graph of
treewidth at least
$$
K g^8 (\log_2 g)^b
$$
contains the $g \times g$ square grid as a minor.

The improvement comes from a logarithmic-depth amortized controller for the
recursive slicing argument in Section 5 of Chuzhoy--Tan. It produces a square
strong Path-of-Sets system with width and length $g^2$ from a local threshold
of order $g^8 \operatorname{polylog}(g)$.
