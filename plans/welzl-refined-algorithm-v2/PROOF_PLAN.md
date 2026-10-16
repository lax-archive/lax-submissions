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

## 2. Current checked interfaces (updated 2026-10-15)

This table supersedes the historical assignment/status snapshots below. Reuse
these exact interfaces; do not recreate a component because an older entry
still describes it as future work. All implementation details remain proof-side.

| Layer | Checked modules / interfaces | Remaining connection |
| --- | --- | --- |
| Sampler mathematics | `SamplerPhases`, `SamplerContract`, size/charging/one-inclusion/VC and initial/local probability/retry results | Derive legal successful choices from the final source |
| Conditional order correctness | `ReductionPath`, `RefinedOrderCorrectness.output_encodes_graphWelzlOrder` | Actual source must construct the successful reduction path |
| Partition execution | `FullSamplePartition.fullSamplePartition_run`, `ClassSizes.countDigit`, unchanged old refinement/partition sources; `VerifiedRoundPartitions` | Compose the initial attempt and refined round state |
| Reconstruction and output | `VerifiedReconstructionBridge`, `RefinedHistoryOutput.History.reconstructAndWrite_clog2_bound` | Actual refined history/log construction; output execution already follows from a valid history |
| Initial draws and packing | `InitialDrawSampleSource.initialDrawSampleSource_run_bits`, `SequentialDraws`, existing draw/lookup primitives | Compute runtime parameters and compose retries/law; guarded acceptance is assembled |
| Stopped-prefix law | `StoppingPrefix`, `EnumeratedDraws`, `VerifiedDrawLaw`, `RejectionProtocol` | Actual adaptive sampler transitions, changing domains, retries and global finite-tape bound |
| Packing and touched cleanup | `SamplePacking.markDrawArrayWith_run`, `clearDrawSupport_run`, `packMarkedSamples`; `PackedActiveSource.packActiveB_run` via `SourceRenaming` | Local-trial insertion/cleanup and final packing |
| Distinct-neighborhood domain | `DistinctNeighborhoodDomain` using unchanged first partition | Full-ground initialization and empty-active-set branch |
| Grouped representative execution | `GroupedClassRepresentatives.groupedClassRepresentatives_run_bits`, reusing old radix sort, `ClassRepresentativeLoop`, old representative map | `InitialSamplerAttempt.initialSamplerAttempt_run_bits` now composes initial draws, partition and representative selection; guarded acceptance is assembled in `FullInitialAttempt`; distribution/cost coupling remain |
| Representative choice mathematics | `ClassBucketDomain`, `ClassChoiceTransport` | Apply the existing finite-choice law to actual flat-tape execution without conditioning away failures |
| Full initial attempt | `FullInitialAttempt.fullInitialAttempt_run_bits`, `InitialSamplerChoice`, `InitialAttemptAcceptance`; reuses `BatchedDistances` and `ExceptionCollection` | Parameter setup, actual retry loop and adaptive distribution/cost coupling |
| Complete phase two | `ExceptionPhaseSource.exceptionPhase_run`, including initial exception partition, empty branch, scan and packing; existing size/separation lemmas | Compose after initial acceptance and before fixed full-B grouping |
| Fixed full-B classes | `FullSamplePartition.groupActiveB_run`, unchanged radix, `RepairClassOffsets.repairClassOffsets_run` and `repairClassLookup_run` | Compose with the local domain/trial source |
| Repair domain | `RepairFilterSource.repairDomainSource_run`: runtime representative lookup, duplicate-safe CSR neighborhoods, exact symmetric-difference domain, touched cleanup | Trial isolation checks and repair retry loop |
| Repair row check | `RepairTrialCheck.collectCheckAndClearTrialRow_run`: actual CSR collection, trace equality, touched cleanup; arbitrary old difference buffer | Build desired trace, scan fixed class, trial insertion/cleanup and retry loop |
| Guarded cutoff | `SaturatedCutoff`, `SaturatedCutoffSource`, `RefinedCutoffSource.refinedCutoffSource_run` | Discharge word-fit preconditions from final layout; timeout remains separate |
| Compiler | Existing pinned `Lax808846Proofs.Simulation` | Apply to the complete source/layout and derived cost bound |

Some useful established source bounds: marking/packing `20*n+12*r+15`;
mean single indexed draw `30*clog₂(m)+79`; grouped representatives
`charge+64*(xs.length+Q+1)+104*n+24`; one exception candidate
`300*(degree+1)+9`; guarded cutoff `12*clog₂(n)+252`. These are
source-language bounds, not yet the public machine-time theorem.

The outstanding substantial layers are parameter setup and initial retry-loop
assembly, efficient phase-three source,
whole-sampler probability/expected costs, timeout/layout, actual rounds/history,
and the final compiler lift. The public theorem remains open.

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

## 7. Dependency order and original assignments (historical)

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

Initial boundary (historical; current status is in Section 2): the first three worker leaves are reviewed and
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

## 9. Initial reuse audit of the earlier complete construction (2026-10-15)

The table records the initial audit. Section 2 and the later reviewed-boundary
notes record which remaining obligations have since been closed.

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

Reviewed `ClassRepresentativeLoop.representativeClassLoop_run_bits`: a fixed
source loop selects from successive contiguous classes on one flat fair-bit
tape, returns the exact unread suffix, fills precisely the completed
`repClass` prefix, and stops at first cap exhaustion. Trace existence follows
from a proof-side sum of capped bit lengths; no large product is stored in a
RAM word. Each completed position is proved to lie in its class slice. Cost
is `12 + Σ_attempted ((15*L_d+30)*u_d + 12*L_d + 61)`, retaining actual attempt
counts and per-class widths. Zero requests, zero cap, and singleton classes
are covered. The target build and independent axiom queries passed.

This closes the varying-class source loop leaf; the sorted arrays/class sizes
still need assembly from the existing radix pass, followed by the unchanged
representative-map loop. The existing choice-law transport is ready, but no
whole flat-tape distribution or initial-attempt/retry theorem is claimed.
The earlier class-choice integration also passed full kernel replay (124
proof modules); a new integrated replay will include the loop.

The guarded arithmetic source primitives are now checked:
`SaturatedCutoffSource.satMulCommand_run` and `satAddCommand_run` implement
the existing `satMul`/`satAdd` at at most 14 source steps each, preserving
other words, arrays, input and output. Products and sums are evaluated only
after their safe guards. These are the primitives, not yet the complete
cutoff command; logarithm/polynomial composition remains the next leaf.

Reviewed `ClassRepresentativeMap.representativeClassMap_run_bits` composes
the new class loop with the unchanged old `representativeMapLoop_run`. It
proves actual flat-tape execution, the selected table prefix, correct mapping
for every active vertex on success, and preservation of the old map on cap
failure. The derived bound is `charge + 104*n + 22`; residual tape and frames
are retained. Its independent target check and axiom query passed. No new
map-loop proof or probability law was introduced. The preceding integrated
class-loop/guarded-primitives kernel replay also passed (127 proof modules).

Reviewed `ExceptionRefinementStep.exceptionRefinementStep_run`: actual
save/refine/count-test/mark source realizes one `phase2Step`, reusing
`refineOne_run` and the existing count-growth equivalence. The new labels
classify the updated sample also in the no-growth branch. It returns compact
class sizes, occupied labels, cleared counters, bounded stamps, exact sample
flags and frame facts, at `300*(degree(candidate)+1)+9`. Target build and
independent axiom check passed. The candidate scan, stamp reset, initial
exception partition and empty-exception branch remain to be assembled.

Reviewed `GroupedClassRepresentatives.groupedClassRepresentatives_run_bits`:
unchanged radix grouping, the class draw loop and unchanged representative map
now compose into one actual source execution. It retains exact selected values,
class membership, completion/failure flags, unread tape and memory frames.
The bound is `charge + 64*(xs.length+Q+1) + 104*n + 24`; radix capacity Q
remains distinct from class count q. Redundant cleared-counter and label-range
preconditions were removed. Independent target and axiom checks passed.
The preceding integrated replay passed, including the single-candidate step.

Reviewed `RefinedCutoffSource.refinedCutoffSource_run`: fixed source returns
`min n (2 * refinedCutoffK c)` within `12*clog₂(n)+252` source steps. The
`c ≥ n` branch avoids computing the logarithm. The other branch reuses the
old logarithm and guarded capped arithmetic; it needs a logarithm power-fit
bound only in that branch, not a word-fit assumption on c^5 or k. Input words
n/c/qpow, arrays, input and output are preserved. Independent target build
and axiom audit passed. Full timeout/layout integration remains open.

Reviewed `ExceptionRefinementScan.exceptionRefinementScan_run`: fixed source
clears stamps once and scans numeric candidates, reusing the single-candidate
step on active vertices. Actual sample flags equal the existing `phase2Scan`;
final labels classify that sample on exceptions, with compact sizes, occupied
labels, cleared counters, bounded stamps and frames. Source cost is at most
`300*(offset n-offset 0)+339*n+12`, hence `339*(n+targetCap+1)`, using
telescoping CSR intervals and mathlib interval monotonicity. Initial stamps
are arbitrary; initial compact exception partition remains a precondition.
Independent build and axiom audit passed. The preceding grouped-representative
and cutoff integration passed full kernel replay (131 proof modules).

Next assembly boundary: initialize the exception partition with the existing
`partitionRefinePrefix_run` (and handle empty exceptions), then apply the
checked scan and existing phase-two budget/separation results. The initial
sampler attempt still needs a single source composition of draws, packing,
partition, grouped representatives, distance/exception collection and acceptance.
Do not reimplement the source components listed in Section 2.

Final integrated validation for this batch passed: all 132 proof modules are
root-imported, the full `lax build --replay` succeeds, and the public concept
and abstract remain unchanged. Newly checked main helper interfaces have only
`propext`, `Classical.choice`, and `Quot.sound` as axioms. The archive output
still has one concept and zero annotated conclusions; the main theorem is open.

Phase-three assembly reminder: the phase-two scan classifies only E. Local
repair needs fixed phase-two classes on all of B and the original sampled
representative map. Reuse `partitionRefinePrefix_run` on the packed phase-two
sample for all of B: this lower-level routine does not rebuild `repB`. Avoid
blindly calling the fuller `firstPartition_run`, which also replaces `repB`.
The threshold bridge must also match `k < 3*distance` exactly (the collector
uses `nearBound < distance`, so set nearBound to the appropriate integer
quotient and prove equivalence); do not silently drop the factor three.

Reviewed `ExceptionPhaseSource.exceptionPhase_run`: the actual exception-count
branch handles the empty case; otherwise the original prefix partition creates
the exception classification, the checked scan enlarges the sample, and the
existing packer writes the final prefix. The original representative map is
preserved. The bound adds the old refinementWork charge, the linear scan and
packing; the original duplicate-free prefix lemma supplies its linear bound.
Independent target build and axiom checks passed. Initial attempt assembly
and the fixed full-B partition/local repair remain next.

Reviewed `SourceRenaming.run_rename`: scalar/array permutations preserve
bounded source semantics and the exact execution cost. `PackedActiveSource`
uses it to pack activeB into ord/alen with the existing packer (20*n+9),
preserving sample flags/count, representatives, and the tape. Independent
target builds and axiom checks passed. Full kernel replay also passed for
the preceding exception-phase integration (133 modules).

Reviewed initial draw, full-B partition/grouping, and touched cleanup:
`initialDrawSampleSource_run_bits` composes clearing, log setup, capped
sequential draws and conditional packing on arbitrary flat Boolean input,
returning the exact unread suffix, explicit failure, sample size bound and
frames. `fullSamplePartition_run` reuses the original partition and derives
full-B classification from a packed sample; `groupActiveB_run` reuses the
packer and radix to expose exact class slices, preserving initial repB.
Class offsets are still mathematical until a runtime prefix table is built.
`markDrawArrayWith_run` generalizes the existing marker without changing its
one-valued API; `clearDrawSupport_run` resets only touched entries even for
arbitrary old stamp values. All three independent target builds and axiom
audits passed. Initial-attempt composition (representatives, distances,
exception acceptance) and actual local-repair source remain open.

Integrated replay passed after the initial draw/full-B/cleanup batch: 137
root-imported proof modules; one public concept and zero annotated conclusions.
The public theorem remains open.

Reviewed repair neighborhood collection and runtime class offsets:
`collectNeighborhoodAt_run` reads actual CSR offsets, reuses the original
collector through static renaming, and returns a duplicate-free active
neighborhood and exact indicator marks at `54*degree+22`.
`repairClassOffsets_run` builds prefix offsets from class sizes in `18*q+8`;
`repairClassLookup_run` reads the selected exception's class interval in 11
steps. Independent target checks and background-only axiom audits passed.
The symmetric-difference filter/cleanup and local trial checker remain next;
this collector checkpoint is landed while its worker continues the filter.

Full LAX build passed after the repair collector/class-offset integration
(139 root-imported proof modules). Public concept and conclusion status unchanged.

Reviewed `RepairFilterSource.appendSymmetricDifference_run`: two stable
filters produce the exact symmetric difference, duplicate-free, with capacity
proved from its vertex-range subset. Cost `24*(hb+hr)+14`; unrelated memory
and tape are preserved. `clearNeighborhoodSupport_run` reuses the existing
marker via static renaming, clearing each list's support in `12*h+6`. Both
independent Lean checks and standard-background axiom audits passed. The
collector/filter/cleanup composition is still being assembled.

Reviewed the complete `repairDomainSource_run`: the fixed command reads
repB[repairB], collects the two restricted neighborhoods, filters the exact
symmetric difference into drawDomain, and clears both private mark arrays.
It preserves the original representative, fixed classes, sample, CSR and tape.
The source bound is at most `90*(CSRdegree(b)+CSRdegree(repB[b]))+73`;
duplicate adjacency entries are allowed and the empty domain is handled.
Independent target build and axiom checks passed. This completes the local
repair domain construction, not yet the trial/retry source.

Reviewed `InitialSamplerAttempt.initialSamplerAttempt_run_bits`: initial
draws, full sample partition, active packing, radix grouping and class draws
now execute as one fixed command. It retains actual DrawTrace/ClassTrace,
exact unread suffix, explicit draw/representative failure, sample bounds,
class-constant representative formula and the downstream state facts.
Explicit n/qpow preservation repairs the conservative syntactic frame gap.
Independent target/axiom checks passed, including focused interface fixes.
The command intentionally leaves attemptAccepted at zero: distance and
exception acceptance are the next suffix, not an assumed successful outcome.

Reviewed `InitialSamplerChoice.initialSamplerAttempt_run_choice`: successful
source choices instantiate the existing InitialChoice, using neighborhoods
restricted to A; failures remain explicit. The source also exports its final
batchFailed guard. `InitialAttemptAcceptance.initialAttemptAcceptance_run`
composes the old distance sweep and exception collector, compares the runtime
cap, and repacks W. Its exact budget is
`300*(n+targetCap+1)+(94*n+15)+8+(20*n+9)`. The numeric distance bridge and
`attemptExceptions_div_three_eq` identify nearBound=k/3 with the paper's
strict exception test. Independent target builds and axiom checks passed.
The guarded wrapper joining selection and this suffix is next.

Retry-loop interface reminder: representative draws overwrite drawModulus
with class sizes. Every new initial attempt must restore the A-domain length
(and any other changed setup scalars) before invoking the checked one-attempt
source; preservation of drawDomain alone is insufficient. Capped-draw failure
must remain distinct from rejection by the exception-count test.

Parameter reuse opportunity: in the outer nontrivial branch,
A.card > min n (2*k) with A.card ≤ n forces the existing cutoff result to
be exactly 2*k < n. After proving this branch fact, nearBound can be computed
as cutoff/6 and farBound as cutoff/3, giving k/3 and (2*k)/3 respectively.
Do not use these identities without the branch fact, or use cutoff/3 for
the initial exception threshold. This may avoid exposing extra cutoff
intermediates in the runtime setup.

Reviewed and independently rebuilt `FullInitialAttempt.fullInitialAttempt_run_bits`:
one fixed guarded source composes selection with distance/exception acceptance,
retaining explicit capped failures and exact paper exceptions. Successful draw
paths export their unread suffix even when representative selection fails. The
failed draw-batch path retains its DrawTrace and selection Run, rather than
an explicit unread-tape formula. No complete retry/law claim is made.

Reviewed `RepairTrialCheck.collectCheckAndClearTrialRow_run`: actual CSR
collection feeds the existing filtered append, checks difference count and
trace lengths, and clears touched row marks. The difference buffer may contain
arbitrary old values; only its count is reset, so no full-vertex clear is needed
between rows. Exact source budget `54*degree+22+36*rowCard+26`, with
`rowCard ≤ degree`. Fixed X, desired marks, sample/class data are preserved.
Both independent axiom audits contain only the three background axioms.
Next: initial retry-loop setup; desired-trace collection and fixed-class scan;
local trial/retry assembly, then adaptive law/cost and outer machine assembly.

Final integrated `lax build --replay` passed: 145 proof modules, one public
concept and zero annotated conclusions; kernel replay took 2m15s (2m39s total).
The headline theorem remains open. Public concepts and abstract are unchanged.


Reviewed and landed the fixed initial retry source and complete repair class scan.
`InitialSamplerRetriesSource.initialSamplerRetriesSource_run` executes one fixed
runtime-cap while loop, restoring the A-domain modulus and batch target after
ordinary exception-count rejection. It returns acceptance with the actual
InitialChoice, capped exception set, representative map and packed sample;
capped random-draw failure and retry exhaustion are separate outcomes. It
preserves n/qpow and exports the exact unread suffix on every exit. The source
bound is `charges.sum + 28*charges.length + 22`, with at most the runtime cap
many attempts. The separate zero-cap lemma needs no random bits or scratch
setup. The existing one-attempt APIs now export failed-batch unread input and
the representative bit-budget bound, rather than recreating their proofs.
Each charge has a standalone checked full-attempt witness; the exported result
is not yet an ordered execution trace coupled to the adaptive probability law.
That coupling and its expected-cost bound remain open.

`RepairClassScan.repairClassLookupAndScan_run` composes the existing runtime
class lookup, one-time desired trace collection, the complete fixed class-slice
loop, and touched desired-mark cleanup. Each row uses the existing checked
collect/compare/clear operation. Its success flag is exactly separation from
every other member of the fixed class; row and desired marks finish zero.
The grouped B mask and trial sample mask are independent. The graph bridge
`scanSuccess_iff_localTrialIsolates` proves that scanning only the trial draws
is sufficient on the fixed old trace fibre. The source bound is
`54*CSRdegree(b) + 12*|trace_S(b)| + 90*sum_slice_CSRdegrees + 70*sliceLength + 47`.
It allows duplicate CSR entries and preserves the initial representative map,
fixed classes, sample flags and X buffers. The row checker's Boolean flag bound
was strengthened for the actual loop guard. Independent targeted builds and
axiom audits passed; all audited lemmas use only the three background axioms.

Next dependent source boundary: assemble local trial draws, marking, this scan,
accept/discard cleanup and bounded local retries, reusing the existing X-domain
construction and touched markers. Then connect accepted initialization through
phase two and fixed full-B regrouping to the repair outer loop. Adaptive joint
law/expected costs, outer history/timeout, and the final machine layout/compiler
lift remain open. The public theorem and abstract are unchanged.
