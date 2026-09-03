This submission collects running-time theorems about concrete
algorithms, stated on the word RAM of the archive's model submission
*The Word RAM* — which it requires — and measured by the machine's own
step count. Every statement has the same elementary shape: there are a
program and a constant such that, at every word length $w$, on every
admissible input — admissibility including an explicit fitting
inequality against $2^w$ — the machine halts within an explicit bound,
having written the answer. Nothing is asymptotic: a linear-time claim
is the bound $c(|x|+1)$, and every uniformity claim, over the input,
over a parameter, over the word length, is carried by the order of the
quantifiers.

Two theorems are stated. The connected components of a graph can be
computed in linear time: given any graph in compressed sparse row form
as a word $x$, one program halts within $c(|x|+1)$ steps having
labelled every vertex by the least vertex of its component. Courcelle's
theorem holds in the Courcelle–Makowsky–Rotics form: for every sentence
of monadic second-order logic and every width bound $k$ there are a
program and a constant $c$ such that, given a graph in compressed
sparse row form followed by a $k$-expression evaluating to it, the
machine halts within $c(|x|+1)$ steps having decided the sentence. The
surface also fixes the encodings these are stated on: the compressed
sparse row form of a graph with nothing precomputed, monadic
second-order logic on graphs, $k$-expressions, the instance encoding
pairing a graph with a $k$-expression, and the parameterized instance
format that appends one parameter entry to a graph.

Both theorems are discharged through the verified pipeline of *The Word
RAM*: algorithms are written in its structured while-language, costed
by its loop rule with an invariant and a cost potential, and carried to
the machine by its simulation theorem, so the derivation that yields
the running time also shows that no intermediate value outgrows a
word — which is where the fitting conditions come from. The components
algorithm is the textbook sweep of breadth-first searches, verified
against a pure model of the search state under a single global
potential, so that the searches are amortized together. Courcelle's
theorem is proved as on paper, with the machine kept out of the
mathematics until the mathematics is finished: an Ehrenfeucht–Fraïssé
type algebra with adequacy and a composition lemma for gluing along a
marked, edge-free overlap handles the four operations of a
$k$-expression uniformly; the value table of the fold is extracted by
finiteness and choice; and a generic bottom-up fold, verified once
against a table it knows nothing about, evaluates it in a fixed number
of steps per input entry after a prologue that pays for the table
once. The proof package also contains the bounded search tree of
Downey and Fellows, deciding vertex cover within $c\,2^k(|x|+1)$ steps
over the parameterized instance format.
