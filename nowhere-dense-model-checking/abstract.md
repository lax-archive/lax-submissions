First-order model checking is fixed-parameter tractable on nowhere
dense graph classes (Grohe–Kreutzer–Siebertz, JACM 2017). This
submission states that theorem as a running-time claim on the word RAM
of *The Word RAM* (Lax67): for every nowhere dense class *C*, every
first-order sentence φ and every ε > 0 there is one program that
decides φ on every member of *C*, given in compressed sparse row form
as a word *x*, within *c* · (|x| + 1)^(1+ε) steps.

The route is not the original proof. The logic engine is the
rank-preserving locality theorem of Dreier–Toruńczyk
(arXiv 2606.23180), a purely syntactic rewriting; around it the
algorithm is rebuilt from an isolation-form splitter game and sparse
neighborhood covers obtained from weak coloring orderings. The
combinatorial hypotheses — nowhere denseness, uniform quasi-wideness,
subpolynomial weak coloring numbers — are consumed from *Sparsity
Lectures* (Lax12); the machine model and timed computation from *The
Word RAM* (Lax67) and its refinement framework (Lax62); graph
encodings from *Algorithmic Experiments on a Random Access Machine*
(Lax11).

The concept surface has eleven review units: colored graphs and their
walk distance, first-order logic and the distance logic with its rank
measure, scatter sentences, the isolation splitter game, sparse
neighborhood covers, and five theorems. The proof package discharges
four of them — the locality theorem and its normal form, the
neighborhood-cover bound, and Splitter's win on nowhere dense classes,
the last assuming uniform quasi-wideness from Lax12. The model-checking
theorem itself is the open obligation of this draft.
