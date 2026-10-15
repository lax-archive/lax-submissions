# Completing Lax457868

Plan requested on 2026-10-15. Checked starting point: commit
`4e67ca28d550cece559d4c7bfe99a6b4009881d3`, accepted as the live draft.
The main theorem is still open. This document distinguishes checked supporting
results from source execution, probabilistic composition, and assembly work
that remains to be proved.

## 1. Fixed target and proof architecture

Keep the existing public concept unchanged:
`Lax457868.RefinedWelzlOrders.exists_refined_randomized_welzlOrder_program`.
Construct one fixed word-RAM program `p` and one universal constant `Ktime`.
Neither the instruction sequence nor `Ktime` may depend on the graph, its
input encoding, its random choices, `c`, or `n`.

For `c,n ≥ 2`, use exactly

```
Lc = Nat.clog 2 c
s  = 64 * Lc
k  = 768 * c^5 * (s + 1) * Lc + 1
T  = Ktime * (x.length + 1) * (Nat.clog 2 n + 1)
```

The required crossing bound is `2 * k * Nat.clog 2 n`. Do not replace it
with a convenient large constant. The program and sampler implementation
remain in the proof package. Supporting statements use `lemma`; the existing
public theorem is the final archive conclusion. Organize the proof under
these three obligations, all referring to the same constructed program:

1. **Correctness.** Every successful execution returns an encoded order with
   the stated crossing bound. A source success flag must be justified by
   actual checks and execution, not by an assumed output certificate.
2. **Runtime.** Every length-`T` fair-bit tape terminates within `T` machine
   steps, including timeout and rejection paths. Expected-cost estimates
   must be converted into this bounded-time implementation.
3. **Probability.** At least two thirds of the equally likely length-`T`
   tapes yield a successful execution. Count failure and timeout explicitly.

Complete only when the annotated proof has the exact public type, has no
unproved mathematical assumptions or self-dependence, passes full kernel
replay, and the accepted draft records that proof.

## 2. What is already checked

| Layer | Checked modules / interfaces | What it does not yet establish |
| --- | --- | --- |
| Sampler mathematics | `SamplerPhases`, `SamplerContract`, the size, charging, one-inclusion, VC, initial-probability, local-probability and retry modules | Efficient execution of all phases by the final program |
| Conditional order correctness | `ReductionPath`, `RefinedOrderCorrectness.output_encodes_graphWelzlOrder` | That the actual machine constructs a successful reduction path |
| Old partition execution | `VerifiedRoundPartitions.runVerifiedRoundPartitions` | Construction of its input sample and surrounding round state |
| Old reconstruction mathematics | `VerifiedReconstructionBridge` and `ReusedOriginal.Construction.Reconstruction` | Complete machine logging, reconstruction execution, and final output assembly |
| One capped random index and lookup | `FairBitRam`, `IndexedDrawRam.countedIndexedDraw_run_tape` | A sequence of calls sharing one finite tape |
| Actual single-draw law | `VerifiedDrawLaw.sourceDrawEvent_card_eq`, exhaustion tail, `sum_sourceDrawCost_le` | Adaptive composition or independence after conditioning on future success |
| Arbitrary domain enumeration | `EnumeratedDraws.prefixDomainEnumeration_lookup` | Construction of every changing domain array |
| Runtime sample marking and packing | `SamplePacking.markDrawArray_run`, `markAndPackSamples_run` | Filling the draw buffer and executing the three sampler phases |

The source marking/packing routine is fixed code, supports repeated draws,
and has bound `20*n + 12*r + 15` source steps from its stated initial state.
The single-draw source cost has finite mean bound `30*clog₂(m) + 79`.
These are source-language bounds; compiler overhead remains to be included.

## 3. Randomness and sequential execution

### R1. Factor a stopped draw into its consumed prefix and untouched suffix

Prove exact lemmas for a positive domain size `m`, retry cap `t`, selected
index `i`, and actual attempt count `u`:

- Success at attempt `u` means `1 ≤ u ≤ t`, the preceding `u-1` blocks
  reject, and block `u` is the unique block encoding `i`.
- The selector's output and consumed count are unchanged by replacing blocks
  after that accepted block.
- The event of that accepted prefix factors as a prefix event times an
  arbitrary remaining tape. Give an explicit equivalence or exact finite
  counting identity, not an informal independence assertion.
- The remaining suffix is uniform conditional on the consumed prefix,
  selected index, and stopping count. Treat `m=1` (zero bit width), `t=0`,
  and complete rejection explicitly.

Reuse `firstDecodedWithCount`, `selectBitIndexWithCount_eq`, unique accepted
block encoding, and the existing exact source residual-input equation.
Do not skip unused retry blocks: the actual source leaves them for the next
call. Do not condition a prefix on all future calls succeeding.

**Completion evidence:** compiled prefix/suffix and count lemmas with only
background axioms; their event is defined using the existing selector.

### R2. Append an actual draw to the runtime sample buffer

Create fixed source code combining the verified draw command with a guarded
append to `sampleDraws[drawCount]`. On success increment `drawCount` once;
on exhaustion preserve the count and buffer. Repetitions remain allowed.
Prove execution, exact stored value and count, untouched cells and arrays,
residual random input, and a derived constant overhead. Buffer capacity is
fixed and may exceed the occupied prefix length.

**Completion evidence:** an actual `Run` theorem from state/array invariants,
with no Run or desired correctness result assumed as a precondition.

### R3. Execute a batch of draws on one tape

After R1 and R2 are landed, define a sequential reference decoder that starts
each call at the exact residual suffix of its predecessor. Implement a fixed
loop filling the runtime buffer, stopping on requested count or failure.
Prove by induction:

- The buffer equals the sequence of accepted decoded domain values.
- Success gives exactly the requested number of draws; failures preserve the
  already completed prefix and terminate.
- Consumed bits and source costs add over calls, with explicit loop overhead.
- The fixed-domain law agrees with sampling with replacement; the adaptive
  formulation keeps each step's failure outcome explicit.

### R4. Adaptive calls, retries, and finite global tapes

Use the original adaptive protocol/counting machinery where its hypotheses
match. Its source is at the pinned original commit, but the original proof
package is a draft and cannot be an archive dependency. Include only the
needed attributed source closure under `ReusedOriginal`, as already done for
partitioning. Likely reusable files: `AdaptiveBitBlocks`,
`AdaptiveTapeCounting`, `AdaptiveStateProtocol`.

Prove that changing domains, representatives, and retry decisions depend only
on observed history. Transfer R1's fresh-suffix result to the next call.
Relate the protocol's transitions to the actual machine suffix equation.
Compose conditional expected costs and failure bounds without conditioning
away later failures. Generic `R * epsilon` bounds are useful only after an
adequate local bound and a justified count of opportunities are supplied.

## 4. Efficient execution of the three sampler phases

### S0. Actual domains and duplicate neighborhoods

Maintain concrete duplicate-free enumerations of active ground vertices and
distinct neighborhoods. Prove the quotient and representative maps preserve
the family to which the existing probability lemmas apply. Full-neighborhood
duplicates must be suppressed where the mathematical proof requires an
injective neighborhood map. Do not sample representatives with a different
weighting from `SamplerInitialProbability`.

### S1. Initial attempt and retry loop

Using R3/R4, draw `|A| / (4*c²)` vertices independently with replacement,
form the sample set, and partition by traces. Choose a uniform member of
each required trace class and prove the conditional representative law.
Compute distances to these representatives and the exceptional set using
actual adjacency data. Check the paper's exception cap
`|A| / (4*c²*(s+1))`, retry on rejection, and transfer the existing
half-rejection and mean-retry estimates to these executions.

Prove cost bounds for domain construction, representative selection,
distance computation, sample packing, and rejected attempts. A direct
pairwise search is not an acceptable implementation of a linear-cost claim.
Reuse the old batched CSR degree/intersection sweep instead of scanning a
representative's adjacency list separately for every class member.
`NearSweepSource.nearSweepLoop_run` and
`NearCounterCorrectness.nearDistance_eq_neighborhood_symmDiff` provide a
linear worst-case distance pass for any valid representative map. Adapt its
output to collect the refined exceptional set. This removes the proposed
replicated-degree expectation obligation for S1; it does not settle the
cost of S3's individual symmetric-difference domains.

### S2. Exception separation

Implement the scan/refinement corresponding to `phase2Scan` with the reused
partition-refinement primitives. Prove that inserting a vertex occurs
exactly when it splits a relevant current class. Maintain a charge to a new
class so the number of additions is bounded by the existing exception
budget. Connect the final state to the established separation lemma.

Charge adjacency visits and class updates explicitly. Avoid scanning all
exception pairs, or scanning the entire graph for every candidate vertex.

### S3. Local repair

For each required far exception, build an actual enumeration of its symmetric
difference with its fixed initial representative. Prove this domain is
nonempty when a repair is required. Draw `s` samples with replacement, check
isolation within the fixed phase-two class, retry failed trials, and add only
accepted trial samples to the accumulator.

Prove equivalence with `phase3Repair`/`phase3Scan`, including which
representatives and phase-two classes remain fixed. Apply the proved local
success and retry bounds to actual draws. Construct domains and test
isolation using the paper's chargeable work; a whole-graph scan per trial
could destroy the required total runtime.

### S4. Full sampler contract and cost

Assemble S0–S3, including the small-set and empty-family branches. Prove that
every successful source sampler run returns the exact `IsRefinedSample`
contract already established for the finite-choice algorithm. Establish its
cost and probability bounds from actual executions. No externally supplied
`InitialChoice`, successful trial, or sample certificate may remain in the
preconditions of the final sampler theorem.

## 5. Word bounds and control state

### W1. Saturated cutoff arithmetic

First compare `c` with `n`. If `n ≤ c`, prove that the base-case bound already
holds and return immediately without computing `clog₂ c`. This is essential
for runtime: an arbitrarily large `c` occupies one input word, whereas `T`
depends on `n`, so an unconditional `O(log c)` preprocessing loop would not
meet the public claim. Only the `c < n` branch computes the logarithm; there
`clog₂ c ≤ clog₂ n`.

The machine cannot first compute an unbounded `c^5` or `k` and then test
whether it fits. Construct guarded saturated addition/multiplication and
prove that they compute `min limit (a+b)` and `min limit (a*b)` without
evaluating overflowing branches. Use these operations to compute
`min n (2*k)` and decide the base-case guard exactly. Every arithmetic
intermediate must be bounded by the cap or by an input already covered by
the public word-size hypothesis. The mathematical crossing bound remains
unchanged.

First prove the arithmetic identities and branch bounds. Then verify the
fixed IMP+ implementation, including constants and computation of `clog₂ c`.

### W2. Layout, loops, and timeout

Specify all arrays, counters, frame conditions, and memory capacities for
one fixed program. Save/restore the graph-wide logarithm when the sampler
uses a domain-specific block width. Choose retry caps with proved tail and
word bounds. The tape is a stream, not an addressable array of size `T`.

Implement a timeout in word-sized control state: the public hypothesis does
not directly guarantee that `T` itself fits in one word. Use a verified
bounded/nested counter or an equivalent source construction. Include the
timeout mechanism's own execution cost and all failure branches.

## 6. Rounds, reconstruction, and final theorem

### A1. One verified reduction round

From a valid round state, execute S4, then the already verified two partition
commands on the exact packed sample and representative arrays. Preserve the
actual representative maps. Prove the new active sets, shrink bound, and
logged restoration data. Derive the resulting `SuccessfulReductionPath`
step from execution rather than assuming it.

### A2. Loop and reconstruction

Iterate A1 until the exact base-case guard holds. Reuse the proved
logarithmic round bound. Verify initialization, round commits, logs, base
order, restoration, and output. The old concrete reconstruction source can
be included with attribution if needed; bridge its log invariant to the
refined reduction path. Finish with
`RefinedOrderCorrectness.output_encodes_graphWelzlOrder`.

### A3. Global costs and success

Sum adjacency work across at most logarithmically many rounds. Sum
vertex-related random-bit work using the shrinking active-set sizes, rather
than paying an unnecessary extra logarithm. Account for every retry and
failure path. Derive a universal expected-work constant from the proved
local bounds.

Use deterministic per-attempt bounds wherever the reused batched source
passes provide them; multiplying such a bound by the proved mean attempt
count does not require independence of cost and acceptance. Where only an
expected per-attempt bound is available, retain the correlation between
cost and rejection and prove a joint cost-until-first-success bound.
Justify any claimed distribution of accepted initial representatives before
using it to charge later repair work. The old program's total runtime does
not establish these new sampler bounds.

Allocate an explicit total failure budget between capped sampling and
runtime truncation; for example, a split into two sixths is a possible
proof design, not an established result. Derive caps and timeout multiplier
from the inequalities. Prove that successful non-timeout executions occupy
at least two thirds of the finite tape space.

### A4. Compiler lift and archive conclusion

Apply the existing IMP+/word-RAM compiler correctness theorem to the actual
fixed source and layout. Combine source costs, compiler overhead, memory
fit, initialization, timeout, and output. Choose one `Ktime` satisfying all
proved requirements. Discharge the exact public existential claim and audit
its axioms. Run full `lax build --replay`, push, update the draft, and verify
the accepted commit and proof status. Do not register the submission.

## 7. Dependency order and first assignments

```
R1 (stopping prefixes) ----+--> R3 (batch) --> R4 (adaptive law) --+
R2 (append actual draw) --+                                    |
S0 (domains/quotient) ----------> S1 --> S2 --> S3 --> S4 -------+--> A1 --> A2
W1 (safe cutoff) -------------------------------> W2 ----------+           |
R4 + local source costs + shrink bounds ----------------------> A3 --------+--> A4
```

First start three independent workers, with exclusive files and seeded
worktrees based on this plan's commit:

| Worker | Owned file | Initial deliverable |
| --- | --- | --- |
| Stopping-prefix worker | `StoppingPrefix.lean` | R1: selector event characterization and exact prefix/suffix factorization |
| Draw-buffer worker | `DrawBuffer.lean` | R2: fixed guarded append composed with the actual draw command |
| Cutoff-arithmetic worker | `SaturatedCutoff.lean` | W1 arithmetic: guarded operations, exact capped cutoff, branch-value bounds |

Use an economical worker for the mechanical source and arithmetic proofs;
use a stronger worker for the stopping-prefix argument if necessary. The
supervisor owns interfaces, semantic review, assembly decisions, and the
full build. Do not start a dependent implementation until its prerequisites
are reviewed and landed. Each worker returns a commit, exact checked
signatures, targeted build output, axiom audit, and remaining limitations.

For each leaf: check the statement against actual source behavior; reject
input-specialized instruction sequences, desired results hidden in
preconditions, and bounds that omit work. Run targeted checks before
landing and full validation at integrated milestones. Preserve unrelated
working-tree changes and the approved concept surface.

## 8. Estimates and progress accounting

The earlier 20–50-hour estimate is a low-confidence planning range, not a
deadline or a token budget. The largest uncertainties are S1–S3's efficient
source implementations, R4's adaptive cost argument, and W2's timeout lift.
The first R1/R2 results should make the next estimate more informative.

Report completed proof interfaces and unresolved dependencies, not a
percentage inferred from file counts. A full build with zero annotated
proofs still means the headline theorem is open.

Current status (2026-10-15): the first three worker leaves are reviewed and
landed. R2 (`be4e0ac5`) verifies the fixed draw-and-append command, exact
buffer/count changes, frames and residual input, with source bound
`(15*clog₂(m)+30)*attemptsUsed + 31`. R1 (`8fdfa3c7`) proves exact stopped
prefix/suffix equivalences and counts, with a source execution bridge.
W1 arithmetic (`27efdf22`, declaration cleanup `e409a29c` and integration)
proves guarded addition/multiplication, the exact capped cutoff, and the
early `c ≥ n` branch. All cutoff results are supporting lemmas.

These are supporting results, not a proof of the headline theorem. Next:
R3 must compose actual draws into a fixed sequential loop on the same tape;
R4 must lift the finite counting argument to changing domains and retries.
The W1 IMP+ implementation and W2 memory/timeout bounds remain open, as do
the efficient sampler phases S0–S4 and final assembly A1–A4.

Validation of this boundary: all three targeted builds and the integrated
`lax build welzl-refined-algorithm-v2 --replay` passed. The archive output
still contains zero annotated proofs: the main conclusion remains open.

## 9. Reuse audit of the earlier complete construction (2026-10-15)

Checked exact accepted source: Lax235315 commit
`33f2eca4379b6ff944489c7c59ac1990c286c21b`, proving the statement in
Lax195003. Its old crossing bound is `12*c²*(clog₂ n)²`; that result alone
does not imply `2*k*clog₂ n` for unbounded `n`. Reuse the common internals,
not the old end-to-end claim. Existing attributed copies of 34 construction
modules already supply the partition/reconstruction foundation. Additional
copies retain attribution and only transport namespaces/imports. The earlier
archive validation run 38564057277 rejected a direct Lax235315Proofs draft
dependency, despite the local CLI issuing only a warning; the attributed
source-copy route has since passed archive validation. No registration of
the older draft is part of this task.

| Plan item | Checked reusable interface | Remaining obligation |
| --- | --- | --- |
| R1/R2 | New `StoppingPrefix` and `DrawBuffer` already checked | No replacement needed |
| R3 | Old `SamplingPrefixSource` is random-key sorting without replacement; new `DrawBuffer` is the correct primitive | Fixed sequential rejection-draw loop using the actual residual tape |
| R4 | Old `AdaptiveBitBlocks.failureMass_le`, `AdaptiveTapeCounting.failingTapes_fraction_eq_failureMass`, `AdaptiveStateProtocol.goodPath_iff_not_mem_failingTapes` | Adapt one-at-a-time rejection blocks and then actual adaptive sampler transitions; do not consume an entire reserved cap on early success |
| S0 | `RoundPartitionSource.firstPartition_run`, `RepData.enum`, `ConcreteTracePartition`, plus current `SamplerTwinSuppression` | Use full active ground set as tests; connect the produced representative prefix to distinct full neighborhoods |
| S1 | `SamplePacking.markAndPackSamples_run`; old `NearSweepSource.nearSweepLoop_run`, `NearCounterCorrectness.nearDistance_eq_neighborhood_symmDiff`, `VerifyNearSource.prepareNearSweep_run` | Uniform within-class representatives, exception collection, actual attempt/retry assembly |
| S2 | `RefineOneSource.refineOne_run`, `PartitionRefinement.Classifies.refine`; current `SamplerRefinementBudget.phase2Scan_card_add_le` | Insert exactly when class count grows; scan candidates once and charge CSR blocks |
| S3 | Current phase-three/local-success mathematics; old neighbor-scan primitives | Build actual symmetric-difference domains and execute/check local trials efficiently |
| S4 | `SamplerContract.refinedSampler_IsRefinedSample` | Derive its legal choices and successful return from source execution |
| W1 | Current `SaturatedCutoff`; old guarded arithmetic and logarithm code as patterns | Implement new guarded formula and the early c≥n branch in IMP+ |
| W2 | Old fixed layout/source frame patterns | New arrays, word-sized timeout and all failure branches |
| A1 | Current `VerifiedRoundPartitions.runVerifiedRoundPartitions` already reuses both old partition runs | Populate its input from sampler; update actual state/log |
| A2 | Current `VerifiedReconstructionBridge`, `RefinedOrderCorrectness`; old history/restoration source as implementation templates | Construct path from executed loop and connect log/restoration invariants |
| A3 | Existing shrink/round counting; old `HistoryDriverSource.sourceTotal` is specific to old sampler | Costs and failure budgets for refined phases and retries |
| A4 | Registered `Lax808846Proofs.Simulation.compile_correct` is generic | Prove new layout/source obligations and public assembly; old `MachineBridge.sourceRun_terminal` and `runtime_of_source` are specialized to old `welzlCom` and are templates, not direct new-program theorems |

Important distribution distinction: old
`RepresentativeSource.representativeSelectLoop_run` picks the first active
member of a class. It is suitable for removing duplicate neighborhoods, but
is not uniform representative selection for the refined probability proof.

The three audited implementation leaves below are now reviewed and landed:
the bounded rejection protocol adapter, full-neighborhood domain adapter,
and batched near-distance adapter. All remain in the proof package. Exception collection from the computed counters is also landed below.
These components do not by themselves assemble an initial sampling attempt.

Reviewed boundary: `BatchedDistances.batchedDistanceSweep_run` reuses the old
clear/sweep source and returns the actual degree/intersection arrays, exact
restricted-neighborhood distance interpretation, preserved graph/masks/map,
and unchanged input/output. Its worst-case source bound is
`300*(n+targetCap+1)`. No representative distribution is needed for this
pass; exception collection and retry execution are still separate tasks.
The nine added source modules match the accepted original exactly after
namespace transport and attribution.

Reviewed boundary: `DistinctNeighborhoodDomain.runDistinctNeighborhoodSource`
reuses the old full-trace partition on independent ground set A and nonempty
family C. It returns the actual representative prefix, pairwise distinct
neighborhoods, the same neighborhood image as C, and cost at most
`900*(x.length+1)`. Its domain enumerations have explicit lookup lemmas tied
to the actual representative array. Empty-family handling and constructing
the full-A test prefix remain for source assembly. The targeted module build
passed; no new public concepts were introduced.

Reviewed boundary: `RejectionProtocol` applies the old adaptive finite-tape
counting framework to one-at-a-time bounded rejection. It proves exact failure
mass, the `2^(-t)` upper bound, a `t*clog₂(m)` bit cap, and pointwise agreement
of its typed-block evaluator with `selectBitIndex`. The three reused adaptive
modules are exact namespace-transported copies of the accepted old source.
This closes the bounded rejection protocol leaf of R4, not R4 as a whole:
flat-tape machine coupling and adaptive composition of all sampler draws
remain. No machine Run or full sampler theorem is claimed here.

Validation of the three reuse adapters: the integrated full `lax build
welzl-refined-algorithm-v2 --replay` passed on 2026-10-15 (101 proof modules).
Separate axiom queries for the distance Run, domain Run and lookup bridges,
finite-tape rejection bound, and selector/evaluator equivalence returned only
`propext`, `Classical.choice`, and `Quot.sound`. The archive conclusion remains
open: the package still contains zero annotated proofs of the main theorem.

Reviewed dependent boundary: `ExceptionCollection.collectAndPackExceptions_run`
proves actual fixed source execution from concrete arrays, word bounds, and
a runtime threshold. It returns exact zero-one exception flags, a duplicate-
free packed enumeration and exact cardinality, preserves the numeric input
arrays and random tape, and costs `94*n+15` source steps (collector `74*n+6`,
packer `20*n+9`). Its exception set is numeric distance > threshold on active
vertices; the preceding batched-distance adapter supplies the graph meaning.
The source never receives the desired exception set as an input. Uniform
within-class representatives, initial attempt/retry execution, and the later
sampler phases remain open. The first economical worker left definitions
only; a focused stronger worker completed the manual source proof using the
old threshold-check proof pattern.

## 10. Focused remaining-work recheck (2026-10-15)

The uniform-representative **probability law is already proved** in
`SamplerInitialProbability` (`RepChoices`, `decodeChoice`,
`conditionalMeanZ_eq_repMean`) and its expectation dependencies. Only the
actual uniform source selection and its distribution bridge are missing.
Do not redo that probability mathematics.

Phase two can reuse `RefineOneSource.refineOne_run` unchanged with
`activeName = "exceptionFlags"`. Its compact-label and exact refinement
postconditions permit comparing classCount before/after, then inserting a
candidate exactly on strict growth. Required new work is the class-count /
trace-count adapter and scan wrapper, initialization and empty-E case, not a
new refinement engine. Reuse `traceClasses_card_lt_insert_of_split` for the
already-proved forward implication.

The current compiler is `Lax808846Proofs.Simulation` at dependency commit
`9394e531cc51cb67a0214bca3f9264dfe97ba5c7`. Both `compile_correct` and
`compileProgram_runsTo` are generic proved interfaces. Do not use the older
Lax13 checkout as version evidence or reproduce the compiler proof. The old
Welzl-specific layout/success-flag wrappers still need adaptation.

Confirmed remaining groups:
1. Sequential draws using exactly the unread suffix; adaptive probability
   composition for actual calls (reuse DrawBuffer, StoppingPrefix,
   RejectionProtocol and the old adaptive counting framework).
2. Uniform class representative source selection and initial-attempt/retry
   assembly (reuse its probability law, partition, packing, distances, and
   exception collection).
3. Phase-two scan/count wrapper and phase-three local-repair source execution
   with chargeable costs (reuse refinement kernel, graph scans, pure phase
   semantics and local success/retry bounds).
4. Guarded cutoff source implementation and word-sized timeout control
   (reuse SaturatedCutoff arithmetic facts and source loop primitives).
5. Actual round/history/restoration assembly and executed reduction path
   (reuse both partition runs, reconstruction bridge and final order lemma).
6. Global expected-cost/failure aggregation, truncation, layout and generic
   compiler lifting to the unchanged public theorem.

Estimate communicated before implementation: 45–90 minutes for the next
shared-tape source loop including review/checks; 10–25 hours of active proof
work as a rough full-completion planning range, with substantial uncertainty
in local-repair costs, timeout and final assembly. This is not a guarantee.
Current independent leaves: shared-tape loop/source execution and the small
class-count bridge enabling direct reuse of the old phase-two command.

Additional exact reuse found below specialized wrappers:

- `RecordedHistory.History.reconstructAndWrite_correct` at the accepted old
  commit is generic in `k`, terminal bound `q`, round count `R`, and desired
  output bound. It already proves the concrete reconstruction/write routine
  at `100*(n+1)`, including unchanged random input. Specialize `q=2*k` and
  use `R+1≤clog₂ n` for the refined output bound. Constructing the recorded
  history from actual refined rounds remains; reproducing reconstruction
  execution or its correctness proof is unnecessary. A small specialization
  and its exact attributed source closure are now assigned.
- `RadixPass.radixPass_run` is generic in `keyName`; it is not restricted to
  the old random keys. With the class-label array as key it groups class
  members in one counting-sort pass at `64*(xs.length+q+1)`, preserving that
  key array. `RadixMath.getD_bucketSort` identifies index
  `startDigit label xs d+j` with index j of the d-th class filter. This is an
  existing route to concrete uniform representative domains: do not build a
  new sorting/grouping engine or reprove the fiber lookup. The offset lookup,
  runtime class-start/size loop, and sampling-law connection still need
  adapters. Choose a justified q/array capacity; do not assume a class count
  changes the allocated count-array length.


Reviewed boundaries following this recheck:

- `ExceptionRefinementBridge` proves that compact numeric labels have exactly
  the trace-class cardinality and that strict count growth is equivalent to
  `splitsExceptionPair`. Consequently the existing refinement command's
  postconditions implement `phase2Step`. This is the semantic count adapter;
  the outer phase-two scan, initialization, and empty-set source branch remain.
- `RefinedHistoryOutput.History.reconstructAndWrite_clog2_bound` specializes
  the existing actual output source proof to `2*k*clog₂ n`, retaining the real
  recorded-history and concrete array premises. Its source cost is
  `100*(n+1)`. The 14 added prerequisite modules were checked byte-for-byte
  against accepted source `33f2eca4` after attribution/namespace transport.
  Constructing that history from executed refined rounds is still required.
- `SequentialDraws.sequentialDraws_run_list` proves the fixed repeated draw
  source on one shared tape. Each next call starts at the exact unread suffix;
  duplicate selections occupy separate cells. It stops at the first exhausted
  rejection cap, preserves completed draws, and proves exact buffer cells,
  failure status, and source cost
  `(15*clog₂ m+30)*actualBlocks + 43*actualCalls + 10` with `actualCalls≤r`.
  The sufficient `r*t` input length is a proof-side bound, never a stored RAM
  product. Zero requests and zero cap are covered. This closes the fixed-domain
  sequential execution leaf, not the adaptive sampler distribution bridge.

All three worker target builds were independently replayed successfully before
landing. These additions leave the public theorem unchanged and open. The next
source leaf is uniform within-class representative selection using the already
proved radix grouping and indexed selector, followed by initial-attempt/retry
assembly. The remaining six groups above are still the completion checklist,
with the completed sequential execution and count-adapter subparts removed.

Integrated validation: full `lax build welzl-refined-algorithm-v2 --replay`
passed after these three additions (119 proof modules). A separate axiom audit
of the new count adapters, history specialization, trace existence, and source
Run returned only `propext`, `Classical.choice`, and `Quot.sound`. The public
concept package is unchanged and the annotated main-proof count remains zero.

Further lookup reuse check: `RadixPass.countPhase_run` and `prefixPhase_run`
already compute class sizes and bucket starts. The full scatter mutates its
count array, so a caller must preserve those starts or maintain a scalar
cumulative class offset. The existing indexed selector reads only index
`drawValue`; the next adapter must read `classOffset + drawValue` with a proved
array bound, or copy each bucket into an existing zero-based domain. No new
sorting or prefix-sum proof is needed. Uniform class choices are conditional
on successful capped draws; exhaustion remains an explicit failure event in
the final probability budget. This applies to classes of the current sampled
family, not only the later exception family.

The Lax11 supersession warning was checked against Lax271696: the used graph
encoding and CC interfaces are namespace ports, and the separately pinned
Lax808846 compiler revision is unchanged. The current validated pins remain
appropriate for this proof batch; a dependency port is a separate mechanical
task, not a missing mathematical proof.


Reviewed next sampler components:
- `ClassBucketDomain` uses `getD_bucketSort` and the existing prefix enumeration
  API to identify each sorted class slice with its existing `RepFiber`. No
  new uniform distribution or sorting argument is introduced.
- `ClassOffsetDraw.countedClassOffsetDraw_run_tape` reuses the rejection source
  and reads `ord[drawOffset+drawValue]` on success. Exact residual input and
  failure preservation are proved, at `(15*clog₂ m+30)*attempts+21` source steps.
- `DrawLogSetup.drawLogSetup_run` reuses the original `computeLog_run`, with
  save/restore of `n` and `qpow`, at `12*clog₂ m+18`. `WelzlLog` is an exact
  attributed namespace-transported source copy from `33f2eca4`; the elementary
  power bound is reused from Lean core rather than proved again.
The three target builds pass after supervisor review. These are prerequisites
for the actual loop across classes, not a complete representative sampler yet.

Additional direct reuse: `RepresentativeSource.representativeMapLoop_run`
accepts any in-range per-class representatives, independent of the old
first-representative selection rule. Fill `repClass` with the new random
choices and reuse that loop to construct the per-vertex map at `104*n+4`.
For the new class loop retain a sum of actual per-class read costs: the existing
`sum_classMultiplicity_of_bounded` and `clog₂ m≤m` allow a linear aggregate
expected representative cost without adding an artificial logarithmic factor.

The integrated kernel replay for these class adapters passed (123 proof modules).
The next active leaves are the actual varying-class loop and a pure transport
of numeric class choices to the existing `RepChoices` expectation theorem.

Probability composition caution: for a fixed initial draw, successful capped
class selectors can have the existing uniform product choice law. Across
initial draws, however, the probability that every class selector succeeds can
depend on the resulting class sizes. Do not claim that conditioning the entire
algorithm on no cap exhaustion preserves the initial uniform draw law. Transfer
bounds using explicit exhaustion events/coupling (or unnormalized probability
bounds), reusing the stopped-prefix and adaptive counting results.

Reviewed `ClassChoiceTransport`: explicit compact-label / trace-class and
per-class product equivalences preserve representative lookup. Reindexing the
existing `totalDistance` finite mean yields `conditionalMeanZ`; no probability
lemma was recreated. Empty class families require no additional nonempty
assumption. The targeted build passed. Actual shared-tape execution and its
distribution coupling remain distinct obligations.
