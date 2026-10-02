# Welzl-order construction

Status: proved locally; proof-only program refactor awaiting draft publication.
Submission: `lax-235315`, `welzl-order-construction/`.
Source: Dreier--Kuske, arXiv:2602.14625v1, supplied PDF (14 pages).
Target: `Lax195003.WelzlOrdersComputation.exists_nearLinearTime_randomized_welzlOrder_program`.

## Plan and theorem boundaries

1. Create the new submission before reading the PDF (done).
2. Read Algorithm 1 and Sections 2--3, and state its constituent claims before
   proving them. Keep an explicit mathematical algorithm separate from its
   correctness, probability and machine implementation.
3. Prove the deterministic crossing lemmas: duplicating twins preserves the
   crossing count (Lemma 2.1); changing membership at k positions changes the
   crossing count by at most 2k (Lemma 2.2).
4. Prove the size recurrence and logarithmic stopping bound, with ceiling
   logarithms and separate empty/singleton cases.
5. Define the recursive contraction/reconstruction algorithm, including failure,
   from explicit samples. Prove permutation preservation and the crossing bound
   for every successful run; no probability assumption belongs in this proof.
6. Prove the sampling avoidance bound, pair union bound and history-conditional
   failure bound. Independently implement finite-bit sampling with a bounded
   failure budget. Exact sampling of arbitrary cardinalities from a fixed
   number of fair bits cannot be assumed.
7. Implement and verify the data structures and concrete word-RAM program.
   Prove every run's time bound separately from success probability. Account
   for random-bit reading, address ranges, word overflow, CSR parsing, and
   graph-to-bipartite-system conversion.
8. Combine these theorems and check the exact archive conclusion without
   assuming it, a renamed equivalent, or any remaining component obligation.
   Run `lax build --replay`, inspect axiom dependencies, then publish a draft.

## Source and statement cautions

- The supplied v1 PDF's graph theorem is **1.4** (the general linear theorem
  is 1.2). The existing archive annotation calls it 1.3.
- The PDF uses ceiling sample sizes. Page 6 was rendered and checked visually.
- The PDF has two theorems numbered 3.1; identify them by their content.
- The loop bound `log N - 1` needs small-input treatment; it cannot literally
  be asserted for N=1. The archive's `Nat.clog` formulation handles endpoints
  differently and requires its own arithmetic proof.
- The paper's reservoir sampling and perfect hashing references require
  explicit treatment in the archive's fixed-bit, worst-case-time machine
  model. The completed proof uses finite random keys and concrete scans.
- The website and older local source initially showed Lean 4.30.0, but the
  refreshed archive and exact source at `63ac657db4dd622a1a74f5adfb0f56b2193b3007`
  put Lax195003 in 4.33.0. The new submission now imports that exact record,
  Lax808846 (word RAM), Lax11 (the original theorem's CSR type), and Lax199508
  (graph classes). Lax11 is deliberately retained for definitional identity
  even though the archive also offers its successor Lax271696.

## Completion standard

Concept axioms are open proof obligations, never evidence of proof. A compiled
glue theorem with open assumptions does not solve the original claim. Record
which claims have closed Lean proofs and which remain open in every milestone.

## Current proof map (2026-10-02)

| Claim | Status | Proof module |
| --- | --- | --- |
| Twin insertion and near-twin stability | Proved | Crossings |
| Contraction recurrence | Proved | Contraction |
| Near-twin replacement and finite sampling bounds | Proved | ComponentProofs |
| Reconstruction correctness | Proved | ReconstructionBridge |
| Runtime of the compiled witness | Proved lemma | ProgramContracts |
| Correctness of successful outputs | Proved lemma | ProgramContracts |
| Finite-tape success probability | Proved lemma | ProgramContracts |
| Original Lax195003 existential claim | Proved, without claim assumptions | Assembly |

The seven mathematical support claims remain reviewable concepts. The
compiled word-RAM witness and its three operational contracts are now defined
in the proof package. `ProofProgram.program` is `compileProgram layout
welzlCom`, where `welzlCom` is the readable IMP+ construction. There is no
expanded instruction listing in the concept package. The three proved
contracts refer to this same witness, and the assembly supplies it to the
registered existential theorem.

## Verification

The complete source driver, including setup, adaptive reduction, rejection,
reconstruction, and final output, is proved to fit within
`6000 (|x|+1) (ceil(log₂ n)+1)` source steps. The compiler simulation yields
the word-RAM runtime contract. Accepted histories certify the required graph
Welzl order. Conditional finite-bit failure counting yields success on at least
two thirds of tapes. Empty, singleton, and initial no-round inputs have
separate execution arguments.

`lake build Lax235315Proofs` and `lax build welzl-order-construction --replay`
pass with 9 concepts and 8 annotated proofs. `#print axioms` on each of the
three program-contract lemmas and the final assembly reports only `propext`,
`Classical.choice`, and `Quot.sound`. The remaining archive warnings are
nonfatal unused-helper and dependency notices.

The source PDF SHA-256 is
`f7d8c4965f87ce23ee66b151236024a3e7f7cfe07e9e4def7aa06f60c63bb806`.
The supplied PDF labels the graph theorem 1.4; the registered concept's older
annotation calls it 1.3.
