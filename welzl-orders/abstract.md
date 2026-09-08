This submission states the graph form of the main result of Jan Dreier and
Clemens Kuske, *Near-Linear Time Computation of Welzl Orders on Graphs with
Linear Neighborhood Complexity* (arXiv:2602.14625). Given a graph whose
neighborhoods leave at most *c* · |*A*| distinct traces on every nonempty
vertex set *A*, a randomized algorithm computes, with probability at least
2/3, an ordering crossed at most 12*c*² log² *n* times by every open
1-neighborhood. Its running time is `O((n+m) log n)` on the word RAM.

The concept surface has five review units and starts with Welzl orders
themselves: the crossing count of a set in a total order and the maximum over
a set system. A separate graph concept specializes this Welzl-order definition
to the open `k`-neighborhood set system; the theorem uses its radius-one
instance, which is the ordinary open neighborhood system. Another unit defines
the graph's neighborhood complexity function and the
exact linear bound `π_G(k) ≤ c · k`, both for one graph with a specified
constant and uniformly over a graph class; this is distinct from almost-linear
neighborhood complexity. Another gives the finite-randomness reading of a
randomized word-RAM computation with a rational success threshold: independent
uniform random bits are appended to the ordinary input, every run respects the
time bound, and the requested fraction of bit strings produce an accepted
output. The theorem instantiates this parameter with `2/3` and is stated for
graphs in compressed sparse row form with its constants exposed.

The submission reuses rather than restates three registered concepts. The word
RAM and its step-count semantics are those of *The Word RAM* (Lax67), and the
graph input is the compressed sparse row representation of *Algorithmic
Experiments on a Random Access Machine* (Lax11), while graph classes use the
representation from *Sparsity Lectures* (Lax12). This submission still defines
bounded walk distance, neighborhood trace count, the maximum `π_G`, and its
linear bound directly.

This draft contains the definition and theorem statements only. Its proof
obligation is intentionally open while the concept files are reviewed and
endorsed.
