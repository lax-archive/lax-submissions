The Post correspondence problem is undecidable: no algorithm decides whether
a finite collection of dominos, each carrying a top and a bottom string,
admits a nonempty sequence of dominos whose top and bottom strings coincide.
This submission puts Sipser's proof on the archive, following Sections 4.2
and 5.2 of *Introduction to the Theory of Computation*, in the form the book
*Transducers* (M. Bojańczyk) takes as given for the undecidability of
equivalence of rational relations.

Three definition-concepts: the acceptance problem $A_{TM}$ for machines,
with mathlib's partial recursive programs as the machines (they supply the
universal machine and the programmability that the diagonalisation needs);
single-tape Turing machines as Sipser presents them, with configurations as
strings and steps as local rewritings; and the Post correspondence problem,
in the domino form and in the index form over lists of pairs of strings.

Six theorem-concepts, all proved: $A_{TM}$ is undecidable (Theorem 4.11, by
diagonalisation); every partial recursive function is computed by a
single-tape Turing machine, in the sense that a fixed machine accepts the
unary encoding of $n$ exactly when the function is defined at $n$ (the
Turing-completeness that links the two machine models, by compiling through
counter machines); the acceptance problem for Turing machines is
undecidable; a decision procedure for the Post correspondence problem would
decide it (Theorem 5.15, the computation-history reduction through the
modified problem and the $\star$ trick, with the construction proved
primitive recursive); and the Post correspondence problem is undecidable, in
the domino form (glued from the two preceding statements) and in the index
form. Decidability is mathlib's `ComputablePred` throughout.
