The neighborhood set systems of cographs have logarithmic, and sometimes
necessarily logarithmic, Welzl orders.  Every cograph on *n* vertices admits
an order crossed at most `4 * (ceil(log₂ n) + 1)` times by each open
neighborhood.
Conversely, for every *k* there is a cograph on between `3^k` and `4^k`
vertices for which every vertex order is crossed at least *k* times by some
open neighborhood.  Thus the worst possible crossing number is
`Theta(log n)`, already inside the graphs of twin-width zero.

The concept surface has three review units.  The first defines cographs as
the finite graphs admitting a width-zero twin-width contraction sequence.
This is the standard twin-width characterization of cographs: zero is the
correct value under the convention that red degree itself is the width.  The
other two concepts state the matching logarithmic lower and upper bounds,
using the registered definition of Welzl orders and the open radius-one
neighborhood set system.

The lower-bound construction is the underlying graph of the transitive
closure of a complete rooted ternary tree.  Passing from depth *k* to depth
`k+1` adds a universal root above three disjoint copies, or equivalently adds
two alternating levels to its cotree.  In every order one of the three copies
is separated from the new root by nonneighbors, forcing one additional
crossing.  For the upper bound, a heavy root path of a cotree is removed at
each round.  Ordering the off-path subtrees first by join nodes from the root
downward and then by union nodes in reverse makes every vertex's external
neighborhood use at most two intervals.  The number of rounds is the
Strahler rank of the cotree, at most `ceil(log₂ n)`.
