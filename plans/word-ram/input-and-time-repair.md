# Input and instruction-time repair

2026-09-09. User approved implementation of the reviewed repair, followed by
retraction and resubmission on lax. `gh`, `git`, and `lax` commands are authorized.

Audited source: `9d9639601dea95e60803cfb7db1f6296478dcb42`; the two RAM concepts
were unchanged at initial main `42c861dc580fa5ac4043a4fd106a56a38ccf5659`.

Core boundary: `7ac514c` plus focused review correction `ca86140`.
The machine now has immutable indexed input, original-length access, and an
EOF branch. Existing input lists and the compiler's zeroed-memory layout are
preserved. `RunsTo` charges fetched terminal instructions; fallthrough costs
zero. Compiler transfer adds the final halt once. The execution driver agrees
with the charged predicate, including its exact fuel boundary.

Reviewed semantic gates: raw-list parity at all word lengths at least one in
exactly `3 * length + 4` instructions; indexed last entry in exactly six;
input immutability and old-subset compatibility; audit examples and overflow,
aliasing, and EOF edges. Concepts and proofs build; key proofs use background
axioms only. Supervisor reviewed source semantics, preconditions, and costs.

All source migrations and dependency pins are reviewed, landed, and published.
The four corrected entries are accepted drafts. Original ownership is restored.

Release mechanism: current lax has a supported maintainer `reset-draft` action;
the current GitHub account is an authorized maintainer. This implements the
user's requested retraction/resubmission while retaining lax-67 and lax-11 and
their namespaces. Reset only after reviewed code is ready. The ordinary delete
command cannot retract a registered record and retires IDs, so it is not the
resubmission mechanism. Verify the resulting archive state and published source.

Reviewed ram-linear-time boundary: `874c8e7` and `fd3d0b3`. Closed-machine
counts and executable fixtures charge the final halt; CC and VC witnesses
become 841 and 9001. Tree-fold and Courcelle retain their constants using
proved slack. Internal IMP costs, input domains, and outputs are preserved.
The sequential-input guards reject the three new input operations. Concepts
and full proofs passed, followed by the supervisor's four-module replay.

Reviewed refinement-tower boundary: `d2d94e7`. The codegen transfer and its
end-to-end examples include the final halt once; exact executable counts and
fuel assertions agree. Internal IR/IMP budgets and specifications are
unchanged. Concepts, full proofs, and the supervisor's narrow replay passed.

Reviewed model-checking boundary: `6540c3d`. Four machine-boundary files add
the terminal instruction exactly once. The headline uses `T + 1` and `cf + 1`,
with the extra unit absorbed using the existing positive exponent hypothesis.
Source programs, internal budgets, domains, outputs, and uniformity are
unchanged. Concepts and all 3575 proof jobs passed; the supervisor reviewed
the full diff and replayed the headline theorem.

Archive boundary: lax-11 and lax-67 were reset from registered to draft using
the supported maintainer action. Lax-67 accepted source `bc4c6e6`, independently
rebuilt by run `34347162845`, archive commit `40dd3740a24fc096342fc2dbf66e0fd8dea23ee9`.
The original lax-13 and lax-67 owner lists are restored. Ram-linear-time and
refinement-tower now pin that accepted RAM revision; their full `lax build`
checks passed against the archive dependencies. Draft-dependency and existing
proof-package advisories are expected for this coordinated draft resubmission.

Lax-11 and lax-62 accepted source `418d847`, in runs `34348739381` and
`34348739457` (archive commits `90d2a3e` and `98b54eb`). Their original owner
lists are restored. Model checking now pins those actual records and `bc4c6e6`
for RAM. Its complete `lax build` passed against the final archive dependencies:
12 concepts and 6 proofs inspected, with only the expected dependency advisories.

Final archive boundary: lax-3 accepted `dcdf38f72851790ebc9e37e6e7b7a8603029e5ab`
in run `34350383245`, archive commit `c24a0c4703a0e1c954465a2d938666368d87aa9d`.
All four independent archive builds passed. Verified all four published source
tuples and draft states, all 11 changed dependency requirements on main, and
exact restoration of the five original owner lists (including lax-13, whose
ownership was temporarily needed for the existing supersedes claim).
All code is landed on main and published on `ram-input-repair`; the pre-existing
unpublished main history and unrelated worktrees were preserved.

Smoke-domain follow-up, 2026-09-09: `542785f` corrects the vacuous Echo and
Sum machine theorems. Their admissible domains now include the per-input
`x.sum + 7 ≤ 2^w` and `x.sum + 8 ≤ 2^w` bounds, respectively; each theorem
holds for every word length on its own domain. Programs, outputs, and the
110/130 time coefficients are unchanged. Each namespace proves eventual
admissibility of every length-prefixed input and an initialized execution on
the nonzero payload `[2, 3]` at four bits. The original impossible universal
hypotheses were independently refuted in Lean. Only `Smoke.lean` changed;
concepts and full proofs built, and the supervisor reviewed the complete diff
and replayed the Smoke target. No downstream caller uses either changed API.

The corrected lax-67 draft accepted `512403f000f23689a1c40d8826062d20f1e28f03`
in archive run `34363212494` (independent rebuild 3m32s). Verified the live
record and exact restoration of the original lax-13/lax-67 owner lists.
Downstream pin boundary `ac2a589` updates five requirements in ram-linear-time
and refinement-tower to that accepted source. Both full `lax build` checks
passed (2m30s and 3m01s); supervisor diff review and narrow CCMain/Cash replays
passed. Only the existing proof-package and draft-dependency advisories remain.

Lax-11 and lax-62 accepted `d82625d050fde928adbe5d23b024a940e6f7d8da` in runs
`34368293295` and `34368295127`, respectively; independent rebuilds passed in
4m12s and 11m04s. Both published source tuples were checked against the live
archive before the final model-checking pin update.

Final pin boundary `f86a1cf` updates exactly six requirements in the two
model-checking lakefiles. Full `lax build` passed in 16m59s (12 concepts and
6 proofs inspected), with only eight existing dependency advisories. The
supervisor reviewed the two-file diff and replayed `Lax3Proofs.SolveMachine`;
all 3567 jobs passed. Sibling overrides report no stale requirements.
