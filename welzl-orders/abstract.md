This submission states the graph form of the main result of Jan Dreier and
Clemens Kuske, *Near-Linear Time Computation of Welzl Orders on Graphs with
Linear Neighborhood Complexity* (arXiv:2602.14625). Given a graph whose
neighborhoods leave at most *c* · |*A*| distinct traces on every nonempty
vertex set *A*, a randomized algorithm computes, with probability at least
2/3, an ordering crossed at most 12*c*² log² *n* times by every vertex
neighborhood. Its running time is `O((n+m) log n)` on the word RAM.

The concept surface has four review units and starts with Welzl orders
themselves: the crossing count of a set in a total order, the maximum over a
set system, and the specialization to the neighborhood set system of a graph.
A separate unit defines the graph's neighborhood complexity function and the
exact linear bound `π_G(k) ≤ c · k`, both for one graph with a specified
constant and uniformly over a graph class; this is distinct from almost-linear
neighborhood complexity. Another gives the finite-randomness reading of a
randomized word-RAM computation: independent uniform random bits are appended
to the ordinary input, every run respects the time bound, and at least two
thirds of the bit strings produce an accepted output. The theorem is stated
for graphs in compressed sparse row form with its constants and success
probability exposed.

The submission reuses rather than restates three registered concepts. The
word RAM and its step-count semantics are those of *The Word RAM* (Lax67),
the graph input is the compressed sparse row representation of *Algorithmic
Experiments on a Random Access Machine* (Lax11), and individual neighborhood
traces are counted by the definition in *Sparsity Lectures* (Lax12). This
submission defines the maximum `π_G` and its linear bound separately; it does
not reuse Lax12's almost-linear class predicate.

This draft contains the definition and theorem statements only. Its proof
obligation is intentionally open while the concept files are reviewed and
endorsed.
