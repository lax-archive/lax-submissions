# Welzl-order construction

Status: active; original archive theorem is not yet discharged.
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
- The paper's reservoir sampling and perfect hashing references are not yet
  proofs in the archive's fixed-bit, worst-case-time machine model. A proof
  must implement or replace these steps. A deterministic adjacency marking
  scan can replace the hash map in Lemma 3.5.
- New submissions use Lean 4.33.0; the exact target and its dependencies were
  registered under 4.30.0. Cross-environment dependencies are forbidden.
  Resolve a successor route before claiming a formal link to the old target.

## Completion standard

Concept axioms are open proof obligations, never evidence of proof. A compiled
glue theorem with open assumptions does not solve the original claim. Record
which claims have closed Lean proofs and which remain open in every milestone.
