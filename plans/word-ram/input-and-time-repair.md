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

All source migrations are reviewed and landed. Remaining: publish the three
dependents in dependency order, repinning each to the actual archive record.

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
