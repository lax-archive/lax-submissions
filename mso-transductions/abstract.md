Section 4 of Part C of the book *Transducers* (M. Bojańczyk) as concepts and
proofs: monadic second-order logic on strings and the logical descriptions
of the rational and the regular functions, together with the first-order
fragment. The Lean development is Aristotle's formalisation of the book,
re-presented in the archive's form; it requires the submissions for Parts A,
B and C §1–3.

The definition-concepts are monadic second-order logic on strings with its
first-order fragment, mso relabellings (C.4.3), string-to-string mso
transductions of a linear type (C.4.7) with the requirement that makes them
functions, and the $k$-types of strings (C.4.12).

The theorem-concepts are Büchi's theorem that the regular languages are the
mso-definable ones (C.4.1, Büchi–Elgot–Trakhtenbrot, as two implications and
their conjunction), the regularity of the annotated strings satisfying a
formula with free variables (C.4.2), the theorem that mso relabellings define
exactly the rational functions (C.4.4, Bloem–Engelfriet, split), the
regularity of correct annotations (C.4.6), the theorem that mso transductions
define exactly the regular functions (C.4.8, Engelfriet–Hoogeboom, split),
the precomputation lemma (C.4.10), the theorem that the first-order definable
languages are the aperiodic ones (C.4.11, Schützenberger, McNaughton–Papert,
split), the correspondence between $k$-types and first-order sentences of
quantifier rank $k$ (C.4.13, for sentences), the three properties of
$k$-types (C.4.15, as three statements), and the theorem that first-order
relabellings are exactly the functions of aperiodic bimachines (C.4.16,
split). All are proved.

Claim C.4.5, Lemma C.4.9 and Claim C.4.14 are internal steps and appear only
inside the proofs; the unnumbered paragraph closing the section, on
first-order transductions, is not formalised. The archive's lax-52 states
Büchi's theorem over mathlib's first-order structures; this submission uses
the concrete syntax the transductions need and does not depend on it.
