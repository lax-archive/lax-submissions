Part A of the book *Transducers* (M. Bojańczyk), together with the definition
of its introduction, as concepts and proofs. The Lean development is
Aristotle's formalisation of the book, re-presented in the archive's form:
the definitions and statements of the book are the concept package, and
the original development is the proof package.

The definition-concepts are continuity (Definition 0.1: the inverse image
of every regular language is regular), the closure of a family of functions
under composition through finite alphabets (the "composition of primes"
idiom of every transducer class of the book), Mealy machines and the
functions they compute, their state transformations, the prime Mealy
machines (reversible and flip-flop), map lifting, aperiodicity, and the
derivatives of a string-to-string function.

The theorem-concepts are the numbered results of Part A: decidable
equivalence of Mealy machines in the form of a finite check on inputs of
length at most the product of the numbers of states (A.1.2), closure under
composition (A.1.3), continuity (A.1.4), the Krohn–Rhodes theorem that
every Mealy machine is a composition of reversible and flip-flop machines
(A.2.2), its two lemmas on map lifting (A.2.4) and on the state
transformation transducer of a pre-automaton (A.2.5), closure of reversible
machines under composition (A.2.6), the characterisation of aperiodic Mealy
functions as the compositions of flip-flops (A.2.8, stated as its two
implications and their conjunction), aperiodicity as a pumping property
(A.2.9), the Myhill–Nerode lemma for Mealy machines (A.2.10), and the
stabilisation condition on the minimal machine (A.2.11). All of them are
proved.

Two statements are not the printed ones. Aperiodicity (A.2.7) asks for the
last letter of $f(uv^nw)$ as an element of $B + 1$, since with $u = v = w =
\varepsilon$ there is no last letter and the printed definition is
unsatisfiable; and Lemma A.2.11 speaks of *some* machine computing $f$
rather than of the minimal machine, which it does not construct. The
decidability sentence of Theorem A.2.8 is not formalised. The exercises of
Part A are not part of this submission.
