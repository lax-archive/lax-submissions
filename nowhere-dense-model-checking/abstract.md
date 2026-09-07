First-order model checking is fixed-parameter tractable on nowhere
dense graph classes (Grohe–Kreutzer–Siebertz, JACM 2017). This
submission proves that theorem as a running-time claim on the word RAM
of *The Word RAM* (Lax67): for every nowhere dense class *C*, every
first-order sentence φ and every ε > 0 there is one program that
decides φ on every member of *C*, given in compressed sparse row form
as a word *x*, within *c* · (|x| + 1)^(1+ε) steps. Program, constant
and time bound are fixed before the graph and the word length, and the
graph is the whole input: every auxiliary object the algorithm uses is
computed from it.

The route is not the original proof. The logic engine is the
rank-preserving locality theorem of Dreier–Toruńczyk
(arXiv 2606.23180), a purely syntactic rewriting of a sentence into a
boolean combination of local formulas and scatter sentences; around it
the algorithm is rebuilt from an isolation-form splitter game and
sparse neighborhood covers obtained from weak coloring orderings. The
recursion descends the game tree: at each node it computes a
neighborhood cover of the current arena, relativizes the formula to
every cluster, isolates the batch of vertices Splitter picks, records
their distance profiles, and recurses; Splitter's win on nowhere dense
classes bounds the depth.

On the machine the cover is computed as Grohe, Kreutzer and Siebertz
compute it: a transitive–fraternal augmentation chain built sparsely
from the input rows, a minimum-degree elimination order of the
augmented graph, and a peeling sweep that emits the cluster of each
centre in order. The degree of that cover is bounded by the class's
subpolynomial weak coloring number, which is what makes the cluster
family of every node *n*^(1+δ) in size and the whole recursion almost
linear. All programs are written as structured commands in the
refinement framework of Lax62 and compiled to the word RAM together
with their step counts; the time bound is the machine's own count.

The combinatorial hypotheses — nowhere denseness, uniform
quasi-wideness, subpolynomial weak coloring numbers — are consumed from
*Sparsity Lectures* (Lax12); the machine model and timed computation
from *The Word RAM* (Lax67) and its refinement framework (Lax62); graph
encodings from *Algorithmic Experiments on a Random Access Machine*
(Lax11).

The model-checking theorem and the neighborhood-cover construction of
Section 6 are those of Grohe, Kreutzer and Siebertz (JACM 2017, cited
by the numbering of arXiv:1311.3899); the locality theorem is
Dreier–Toruńczyk (arXiv 2606.23180); the sparsity theory behind the
hypotheses follows the Pilipczuk–Siebertz lecture notes as formalized
in Lax12.
