The neighborhood set systems of cographs have logarithmic, and sometimes
necessarily logarithmic, spanning trees in the sense of Welzl.  Every
cograph on *n* positive vertices admits a spanning tree crossed by each open
neighborhood at most `4 * (ceil(log₂ n) + 1)` times.  Conversely, for every
*k* there is a cograph on between `3^k` and `4^k` vertices for which every
spanning tree is crossed at least `ceil(k/2)` times by some open
neighborhood.  Thus the worst possible tree crossing number is
`Theta(log n)`; allowing a branching layout does not make it constant.

The definition follows Welzl: a set crosses an edge when it contains exactly
one endpoint, and the crossing number of a spanning tree is the maximum
number of its edges crossed by one member of the set system.  The two theorem
concepts transfer the matching Welzl-order bounds for cographs through two
general bridges.  An order is itself a path tree with the same crossing
number.  In the other direction, repeatedly deleting a leaf of a tree and
reinserting it beside its neighbor produces an order whose crossing number
is at most twice that of the tree.

The logarithmic order phenomenon is the contiguity theorem of Crespelle and
Gambette: they prove logarithmic upper and lower bounds for the number of
intervals needed to represent all neighborhoods of a cograph in one vertex
order.  Interval count and the number of membership changes along an order
are equivalent up to a factor of two and an additive constant.  The present
submission recasts that result in Welzl's crossing language and shows that
allowing an arbitrary spanning tree, rather than only an order path, still
changes the optimum by at most a factor of two.
