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

## Current proof map (2026-09-27)

| Claim | Status | Proof module |
| --- | --- | --- |
| TwinInsertion | Proved without claim assumptions | Crossings |
| NearTwinStability | Proved without claim assumptions | Crossings |
| ContractionRecurrence | Proved without claim assumptions | Contraction |
| NearTwinReplacement | Proved using the registered crossing number | ComponentProofs |
| UniformSampleAvoidance | Proved; ideal uniform fixed-size sample | ComponentProofs |
| RandomKeyCollisions | Proved; finite key assignment counting | ComponentProofs |
| ReconstructionCorrectness | Proved; checked reconstruction certificate | ReconstructionBridge |
| ConstructionRuntime | OPEN | Full-loop and machine-cost integration required |
| ConstructionCorrectness | OPEN | Full machine run to reconstruction certificate required |
| ConstructionProbability | OPEN | Adaptive finite-tape event analysis required |
| Original Lax195003 claim | Conditional assembly only; OPEN overall | Assembly |

The explicit program has 5,213 instructions and success flag cell 39.
`ProgramLink.program_eq_compilation` proves equality to the compiled source
by kernel reduction. `SuccessfulTermination` counts the final halt instruction
(`t+1 ≤ T`), matching the current registered machine semantics.

The remaining implementation work must preserve the same program across all
three contracts. Each contract asserts a sufficient threshold K₀ and all K≥K₀;
Assembly takes the sum of the three thresholds. Its axiom set is exactly the
three open contracts and the background axioms, and excludes the target claim.

## Reused source and validation

The prior local `codex/welzl-proof` branch at commit `44a44623` supplies 59
proof modules under the new `Lax235315Proofs.Construction` namespace. The
original source worktree (including its uncommitted changes) was not modified.
These modules include mathematical sampling and reconstruction, and verified
source-level subroutines. They are retained intentionally as the working
library for the three open program claims; the archive's unused-helper warnings
reflect that the full integration remains unfinished.

Porting changes adapt finite-set conversion, graph-neighbor coercions,
explicit arguments, and extensional empty-update lemmas. Thirty-nine uses of
`native_decide` in the old component source were replaced with `decide`, since
the archive rejects the native-evaluation axioms. No `sorry`, proof-side axiom,
or native-evaluation axiom is accepted in the final local build.

The source PDF SHA-256 is
`f7d8c4965f87ce23ee66b151236024a3e7f7cfe07e9e4def7aa06f60c63bb806`.
The seven mathematical claims are checked independently of the open program
claims. The paper's graph theorem is 1.4 in this supplied version.

## Checked integration progress (2026-09-27)

- `DriverSetup` executes the literal setup from every valid CSR input and
  finite tape, yielding canonical active arrays, logarithm, counters, and CSR
  arrays. `SourceBounds` proves global memory bounds persist through every
  bounded source execution, including reads from the random tape.
- `MachineBridge` lifts complete source executions to the exact registered
  machine, including its final halt. Its three integration lemmas derive the
  public runtime, output correctness, and probability properties from explicit
  source-level obligations. Those obligations remain to be discharged; they
  are definitions, not new axioms or claimed proofs.
- `ReadKeys.readKeys_run_sharp` charges 120n + 120L|A| + 8 for a round.
  `CostAccounting` bounds the sum over shrinking active sets, including a
  final unsuccessful round, by 736(n+1)(L+1), with at most 32nL random bits.
  The earlier per-round O(nL) bound would have yielded O(nL²) if summed
  directly; the sharper bound removes that obstacle for key reading.
- `RecordRemovedSource` verifies the entire deletion scan, its capacity,
  preserved prefixes, appended vertices and representatives, and round start.
  `CommitSource.commitReduction_run` composes this with adoption of both
  active sets and the round-end update at cost at most 80(n+1).
- `LinkedReconstruction` proves that pointer insertion implements mathematical
  list insertion. `LinkedSource` verifies the literal inner reconstruction
  loop at cost 21 times its log interval length plus 4. `LinkedOutputSource`
  proves the literal final traversal emits the represented list at cost
  13n+9, including the empty-list case.
- `AdaptiveFailure` proves a finite counting union bound for adaptive states.
  `AdaptiveBitBlocks` proves the corresponding rational failure-mass bound
  with history-dependent block widths, so there is no fixed per-round padding.
  `AdaptiveTapeCounting` identifies this mass exactly with the fraction of
  failing fixed-length tapes, counting every unused suffix.
  `AdaptiveMachineBridge` transfers its complement count to the actual machine
  event, conditional on successful source execution outside that failure set.

All these are supporting lemmas. The only theorem concepts remain the same
three main statements, and all three are still open.

## Next concrete leaves

1. Package the active-round invariant, unchanged CSR arrays, workspace sizes,
   exact deletion log, and remaining tape. The canonical initial state and
   persistent value bounds are now checked.
2. Compose the verified sampling, partitioning, and accepted/rejected round
   paths under that invariant. Include collisions and failed near checks.
3. Prove the entire reduction loop and outer linked-list reconstruction match
   the public reconstruction relation. Connect base-list initialization,
   recorded round slices, and the now-verified final traversal, including n=0
   and n=1.
4. Sum all source costs using the checked shrinking and key-reading bounds;
   instantiate `MachineBridge.SourceTotal` and `SourceCorrect` and apply the
   already proved machine-transfer lemmas.
5. Identify the concrete program's adaptive bit blocks and bad events with
   the sampling/key estimates. Apply the now-checked fixed-tape counting bridge
   and instantiate `MachineBridge.SourceProbability`.
6. Discharge the three contracts, then rerun the dependency audit. Only then is
   the original archive claim solved.

## Validated checkpoint

`lax build --replay welzl-order-construction` passed on 2026-09-27:
14 concepts, 10 local statements, 77 imported proof modules, and 8 annotated proofs. Seven proofs have
empty claim-assumption lists. The eighth concludes the original Lax195003
claim relative to exactly the three open program contracts. Kernel replay
passed for the entire submitted concept and proof inventory.

The 508 warnings concern intentionally retained implementation helpers,
dependencies on verified proof packages, and the deliberate use of the exact
Lax11 type occurring in the original claim. There are no validation errors.

## Presentation convention

Only ConstructionRuntime, ConstructionCorrectness, and ConstructionProbability
are theorem concepts. The seven proved component claims are lemma concepts;
supporting proof declarations, including conditional assembly, use `lemma`.
This classification does not alter their propositions or dependency status.
