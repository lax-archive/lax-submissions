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

Initial status: R1, R2 and W1 arithmetic assigned after this plan is saved;
all remaining uncompleted steps above remain open. Update this paragraph
with actual results at the next reviewed boundary.
