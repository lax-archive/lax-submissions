This submission states Theorem 2 of Dreier, Mählmann, McCarty, Pilipczuk,
Toruńczyk, *Neighborhood Complexity and Radius-1 Merge-Width in
Monadically Dependent Graph Classes* (2026): every monadically dependent
class of finite graphs has almost linear neighborhood complexity — for
every $\varepsilon > 0$ there is a $c$ such that every member $G$ and
every nonempty vertex subset $A$ satisfy
$|\{N(v) \cap A : v \in V(G)\}| \le c\,|A|^{1+\varepsilon}$. Neighborhood
complexity is a notion of sparsity theory, and the theorem extends a
classical bound for nowhere dense classes to a much larger,
model-theoretically defined family. The submission builds on the
*Sparsity Lectures* submission (Lax12), whose graph classes, nowhere
denseness and neighborhood complexity it imports and states its theorems
over, and contributes the model-theoretic side — non-copying first-order
transductions of relational structures, graph transductions, monadic
dependence, weak sparseness — together with three theorems relating the
two: weakly sparse monadically dependent classes are nowhere dense; the
headline theorem; and nowhere dense classes are monadically dependent
(Adler–Adler). Because the nowhere-denseness hypotheses and the
almost-linear bound predicate are the separately endorsed definitions of
Lax12, these statements compose directly with the sparsity theory stated
there, and the surface carries the full classical equivalence that on
weakly sparse classes, monadic dependence and nowhere denseness coincide.

The proof package discharges the headline theorem via the paper's
VC-dimension sparsification argument; the weakly sparse theorem via
Mählmann's Ramsey-theoretic extraction of induced subdivided bicliques
(thesis, Lemma 13.8) together with a star-crossing transduction of all
graphs; and the Adler–Adler direction via uniform quasi-wideness and a
semantic locality argument — the deletion specialization of the
flip-breakability route, with hereditarily finite rank-bounded local types
of decorated balls and a ball-swap back-and-forth system in place of
Gaifman's theorem. A transduction of all graphs would shatter arbitrarily
large sets; quasi-wide scattering, a local-type pigeonhole, and the swap
lemma refute this.

The classical sparsity and Ramsey material the proofs rest on is assumed
from upstream submissions, so the dependency is visible in the archive's
proof network: uniform quasi-wideness and almost linear neighborhood
complexity of nowhere dense classes from *Sparsity Lectures* (Lax12),
which formalizes the lecture notes of Pilipczuk and Siebertz, and
Ramsey's theorem for colourings of pairs with its order-type form for
tuples from *Finite Ramsey* (Lax14). The terminal step of the headline
proof composes the statements of the two halves of the paper's
Corollary 6 — the weakly sparse theorem stated here and the nowhere
dense counting theorem stated in Lax12. What each proof reports beyond
Lean's standard logical axioms is exactly the list in its `assumptions`
block.
