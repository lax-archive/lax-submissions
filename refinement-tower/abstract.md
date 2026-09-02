This submission has no concepts and states no theorem. Its concept
package is empty, and everything it contains is in its proof package: a
refinement framework for the word RAM, the machinery through which an
algorithm verified against an abstract specification is carried down,
one proved step at a time, to a program of the structured
while-language of *The Word RAM* together with a bound on the machine's
own step count. Nothing of it shows on the concept level because none
of it is a claim about a mathematical object. It is theorems and tactics
about programs and their costs, and they are consumed only by other
proof packages, which require this one the way a proof package requires
mathlib: the running-time claims those submissions state are their own,
on their own surfaces, in the fixed shape *The Word RAM* prescribes —
one program quantified before the word length, an explicit bound — and
the descent that discharges them is done here once.

The framework is a port to Lean of the Isabelle refinement stack of
Peter Lammich and Maximilian P. L. Haslbeck, kept as close to its
sources as the substrate allows, with every departure recorded in the
module that makes it. Its layers, from the top down: NREST, Haslbeck and
Lammich's nondeterministic result monad with time, whose specifications
carry costs in named currencies, with data refinement, time refinement
by exchange rates, general recursion, loop and foreach combinators, and
the backwards-reasoning verification-condition generator of *Refinement
with Time* and *For a Few Dollars More*; Autoref, Lammich's automatic
data refinement, with its relators, parametricity rules, tagged solvers
and four-phase pipeline; an imperative intermediate language over named
cells and arrays, given a cost-indexed big-step semantics and a
separation logic with credit assertions on the Klein–Kolanski separation
algebra, after the `isabelle_llvm_time` artifact; Sepref, Lammich's
synthesis of imperative programs from monadic ones by relational rules,
here with the credit-paying rules of the timed stack, frame inference,
ownership, a costed allocator with space budgets, and amortized data
structures; the interface and implementation collection of *Refinement
to Imperative/HOL* — arrays, dynamic arrays, stacks, queues, heaps,
maps, matrices, and a union–find with the time analysis of Charguéraud
and Pottier; the one- and two-dimensional asymptotic calculus and the
recurrence lemmas of Zhan and Haslbeck's timed Imperative/HOL, so that a
bound can also be read in Landau form; and a code generator, which is
this submission's own, that embeds the intermediate language into the
while-language and pays every bound down to the machine through *The
Word RAM*'s simulation theorem, where the Isabelle stack ends in a
trusted printer. The examples in the package — breadth-first search in
several forms, array fill, an introsort budget — are acceptance tests
and templates for the submissions that state running times, not
statements.
