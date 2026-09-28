# Welzl-order construction

Status: complete; all three program contracts and the exact original archive theorem pass compilation, kernel replay, and the axiom audit.
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

## Historical proof map (2026-09-27)

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
three main statements. The runtime and correctness statements were discharged
on 2026-09-28; the probability statement remains open.

## Further checked integration (2026-09-27)

- `RoundInvariant.setup_frontier` establishes the numeric frontier from the
  literal setup. `BitArrays` checks zero-one stores in the actual syntax;
  this closes the distinction between deletion's zero test and membership's
  one test. `ActiveBookkeeping` proves deletion/active conservation and
  transfers concrete trace partitions to the numeric shrinking recurrence.
- `AcceptedCommit` derives log capacity and valid round indices from the
  frontier itself. `CertificateFrontier` runs both actual trace partitions
  and the verifier, obtaining a shrinking commit candidate at cost
  2200(|x|+1). `CertifiedBranch` includes the acceptance test and reject path.
- `TapeBlocks` decomposes any sufficiently long binary suffix into its actual
  eight L-bit keys per active vertex. `SamplingFrontier` derives workspace
  preconditions, preserves the frontier, and returns the exact unused suffix,
  sampled enumeration, range, and cardinality.
- `ReductionRoundSource` executes the entire literal random round, including
  collision rejection, at cost 4500(|x|+1)+120L|A|. `RoundPotential` shows that
  a reserve of 24L|A| bits pays for the next block and remains sufficient after
  acceptance. `ReductionLoopSource` composes all adaptive iterations of the
  literal while loop. Starting at round zero with n active vertices, its cost
  is at most 5360(|x|+1)(L+1)+4, with no tape-exhaustion assumption hidden in
  the execution. The explicit initial bit reserve is still a precondition
  to be derived from the public driver tape budget.
- `NearCheckSource`, `VerifyNearSource`, `RoundVerifySource`, and
  `RoundSamplePartitionSource` now provide exact acceptance iff lemmas,
  preserving the previous interfaces. The converse is needed to turn the
  mathematical good-sample event into actual program success.
- `LinkedInitializeSource.linkedInitialize_run` verifies the full initial
  active-vertex scan at cost 40(n+1), including empty and nonempty lists,
  arbitrary bounded initial pointer values, and preserved arrays/tape/output.

## Guarded driver and ordered reconstruction (2026-09-27)

- `GuardedArithmetic` derives square and threshold bounds from the literal
  quotient guards; `FrontierFrames` preserves the numeric invariants across
  scratch assignments. `GuardedDriverSource.reduceAll_run` executes every
  guarded branch, including small n, and returns the final frontier or explicit
  rejection together with the base-size bound for n>1.
- `initial_tape_reserve` derives 24Ln unread bits from `sourceCost A n x ≤ T`
  for A≥24. `setup_reduceAll_run` composes the actual setup and guarded phase
  with cost at most 5600(|x|+1)(L+1). `setup_frontier_ready` supplies its initial
  counters while retaining the previous setup API as a projection.
- `LinkedRoundsSource` verifies every reverse log interval with cost at most
  24R + 21 boundary(R) + 4. Only the written prefixes of roundStart/roundEnd
  are constrained; unused array cells do not need artificial values.
- `IndexedRestoreBridge` equates log-indexed writes with vertex-indexed list
  restoration, and turns `recordRemoved_run`'s getD postconditions into exact
  ordered slices and parallel representative values. It also preserves old
  slices across a later append.
- `RemovedRestoreBridge` lifts the actual numeric deletion order to Fin n,
  proves exact enumeration, transports restoration through Fin.val, and builds
  the mathematical `Reduction` using that actual order instead of an unrelated
  enumeration of the deleted set.
- `ReconstructionSource.reconstructAndWrite_run` composes the complete literal
  initialization, reverse replay, and output at cost at most 100(n+1). Its
  `LoggedRestorations` certificate contains only list and log facts, not an
  execution hypothesis. The output equals the certified order; input is
  preserved. This certificate still must be derived from the whole driver.

- `ScanIndexEquiv` identifies positions in the actual increasing active scan
  with the active-vertex subtype. Its forward values equal the source scan's
  getD entries, preparing transport of finite key assignments and samples.
- `RationalFailureBounds` transports the existing one-round finite failure
  fraction and the total 1/6 estimate from real to rational arithmetic, matching
  the adaptive protocol's exact counting field without new combinatorics.

## Next concrete leaves

1. **Completed 2026-09-28.** `RecordedCommit` preserves each certificate's
   concrete partitions and appends its exact deletion slice and representative
   values to `StoredHistory`. `HistoryRoundSource` and `HistoryLoopSource` carry
   that history through accepted rounds and preserve the rejected paths.
2. **Completed 2026-09-28.** `HistoryDriverSource` composes setup, the loop,
   terminal reconstruction, and the rejected natural-order path, proving
   `SourceTotal 6000` and `SourceCorrect 6000`. `ProgramContracts` transfers
   those results to the registered machine runtime and correctness claims.
3. Identify concrete adaptive key blocks and rejected samples with the finite
   counting model. Join row-major tape digits to `roundAssignmentEquiv`, and
   transport the actual sorted prefix through the active scan enumeration to
   graph bad-sample families. Prove a one-round event inclusion: collision-free
   keys outside that bad family make the exact verifier accept. Then use
   history-dependent block widths, the now-proved initial tape sufficiency,
   and unused-suffix counting to prove `SourceProbability`. The numeric
   real-to-rational seam is closed by `RationalFailureBounds`.
4. The runtime and correctness contracts are discharged by
   `ProgramContracts`; the assembly now depends only on the probability
   contract. Discharge that last contract and rerun the dependency audit to
   solve the original archive claim.

## Validated checkpoint

`lax build --replay welzl-order-construction` passed on 2026-09-27:
14 concepts, 10 local statements, 98 imported proof modules, and 8 annotated proofs. Seven proofs have
empty claim-assumption lists. The eighth concludes the original Lax195003
claim relative to exactly the three open program contracts. Kernel replay
passed for the entire submitted concept and proof inventory.

The 667 archive warnings concern intentionally retained implementation helpers,
dependencies on verified proof packages, and the deliberate use of the exact
Lax11 type occurring in the original claim. There are no validation errors. The newly integrated loop, round, setup,
linked initialization, exact verifier, tape-decomposition, guarded-driver,
ordered reconstruction, scan-index, and rational failure-bound lemmas were also
audited with `#print axioms`: each uses only `propext`, `Classical.choice`, and
`Quot.sound`, with none of the three open construction contracts.

## Presentation convention

Only ConstructionRuntime, ConstructionCorrectness, and ConstructionProbability
are theorem concepts. The seven proved component claims are lemma concepts;
supporting proof declarations, including conditional assembly, use `lemma`.
This classification does not alter their propositions or dependency status.

## Final probability integration and source review (2026-09-28)

Commit `2b25312` closes the probability contract using
`LiteralGoodDispatch.source_good_block_accepted` and
`SourceProbabilityBridge.eventually_hasSuccessProbability_of_accepted`.
`ProgramContracts` proves runtime, correctness, and probability, and `Assembly`
uses those proof declarations directly. The earlier open-status entries above
record intermediate checkpoints, not the current implementation.

Source rechecked: Dreier–Kuske, arXiv:2602.14625v1,
https://arxiv.org/html/2602.14625v1, Theorem 1.4 and Sections 3.3–3.4.
Theorem 1.4 is the graph target. Lemmas 3.7–3.8 and Theorem 3.9 supply
the sampling-avoidance, pair-union, and adaptive-round failure argument.
The implementation additionally charges finite-key collisions and proves
that the actual Boolean tape blocks implement the samples; it does not
assume an ideal uniform-sampling oracle. `RationalFailureBounds` bounds the
sum of collision and bad-sample probabilities by 1/6 in the guarded case.
Small inputs and inputs that require no random round have separate proofs.

Before publication, check full kernel replay, the extracted assumption lists,
and `#print axioms` for all three contracts and the assembled original theorem.
The proof network must connect the actual probability and machine-execution
lemmas to the original conclusion, with no open-contract assumption or cycle.
Keep the registered concepts and exact imported target unchanged.

Axiom audit: `#print axioms` for each declaration in `ProgramContracts` and
`Assembly.exists_nearLinearTime_randomized_welzlOrder_program` lists exactly
`propext`, `Classical.choice`, and `Quot.sound`. All 133 proof modules are
imported by the root file. The proof tree contains no `sorry`, `admit`,
proof-side `axiom`, or `native_decide`. The user explicitly requested finishing
and submitting this existing theorem rather than extending the scope.

Final validation: `lax build --replay welzl-order-construction` passed in
12m14s (6m11s proof compilation, 5m12s kernel replay). The output contains
14 concepts and 11 annotated proofs; every proof has an empty assumption
list, including the exact original Lax195003 conclusion. The 174 warnings
are retained helper declarations, the intentional verified compiler/CSR proof
package imports, and Lax11's superseded status. Lax11 remains necessary for
the definitional identity of the registered target. No concepts were changed
in this completion review. The verified checkpoint is ready for draft submission.
