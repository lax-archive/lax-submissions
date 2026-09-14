Section 5 of Part C of the book *Transducers* (M. Bojańczyk) as concepts and
a proof: the combinator description of the regular functions. The Lean
development is Aristotle's formalisation of the book, re-presented in the
archive's form; it requires the submissions for Parts B and C §1–3.

The definition-concepts are the types built from the unit type by product,
co-product and list, with the string representation of their elements over
an eight-letter alphabet (C.5.1), regularity of a type-to-type function
under string representation (C.5.2), and the regular terms with their
semantics (C.5.3). The theorem-concept is the implication of Theorem C.5.4
that every function defined by a regular term is regular under string
representation, proved by induction on the term with a bracket-counter
parser of the representations. The converse implication, expressive
completeness of the terms, is not formalised and no statement here asserts
it; the auxiliary lemmas and claims of the section are its steps and do not
appear.
