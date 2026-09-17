# network-stress-test (lax-771644)

A **synthetic benchmark** for the Lax website's proof-network figure. It
carries no mathematical content worth reading: every statement is a rung of one
trivial divisibility ladder, and the submission exists only so that the
drawing's edge cases live somewhere permanent and stable.

Each concept is named after the shape it exercises:

| concept | shape under test |
| --- | --- |
| `Foundations` | the ladder itself; a definition-concept with no statements |
| `IsolatedIsland` | a concept with no statements, no imports, no uses |
| `SiblingConclusionRight` | sibling proof, conclusion at the rightmost dock |
| `SiblingConclusionLeft` | sibling proof, conclusion at the leftmost dock |
| `SiblingConclusionMiddle` | sibling proof, conclusion at the middle dock |
| `MixedSiblingAndForeign` | one sibling assumption plus one foreign one |
| `SiblingChain` | two sibling proofs stacked into a chain |
| `TwoProofsOneStatement` | two turnstiles into the same dock |
| `ThreeProofsOneStatement` | three turnstiles into one dock: one sibling, two foreign |
| `WideDockRow` | twelve docks, all proven, with an eleven-wide sibling rail |
| `ManyForeignAssumptions` | one proof assuming eight different concepts |
| `CycleAlpha`, `CycleBeta` | a genuine cross-concept cycle; both stay unproven |
| `SelfReferentialProof` | a statement proved from itself |
| `WholeConceptAssumption` | a statement whose id equals its concept's id |
| `OpenRoot`, `OpenMiddle`, `OpenLeaf` | an unproven root and the open chain below it |
| `Chain01` … `Chain09` | a deep linear chain of nine single-statement concepts |
| `AVeryLongConceptNameFor…` | label wrapping: overlong module, title and statement names |
| `UnicodeNames` | non-ASCII title and statement names |
| `ExternalPrimes` | statements discharged from `lax-242665`, so external nodes appear |

Two shapes are deliberately unprovable and must stay that way: the
`CycleAlpha`/`CycleBeta` pair and `SelfReferentialProof`. Both compile — Lean
has no objection to an axiom being used to prove a theorem of its own type —
and the archive's least-fixed-point notion of provenness leaves them open,
which is exactly the input the grey display-cycle envelope needs.

The Lean sources under `concepts/` and `proofs/` are generated from one small
table by `plans/network-stress-test/generate.py` in this repository, so the
cheapest way to add a shape is to extend that table and rerun the generator
rather than to hand-edit eighty files.
