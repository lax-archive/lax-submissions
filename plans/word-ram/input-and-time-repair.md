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

Remaining: migrate ram-linear-time and refinement-tower independently, then
nowhere-dense-model-checking; validate and publish in dependency order, repinning
each dependent to the actual archive record. Preserve IMP/parser budgets and
encoded outputs, changing only closed-machine costs and justified witnesses.

Release mechanism: current lax has a supported maintainer `reset-draft` action;
the current GitHub account is an authorized maintainer. This implements the
user's requested retraction/resubmission while retaining lax-67 and lax-11 and
their namespaces. Reset only after reviewed code is ready. The ordinary delete
command cannot retract a registered record and retires IDs, so it is not the
resubmission mechanism. Verify the resulting archive state and published source.

Reviewed refinement-tower boundary: `d2d94e7`. The codegen transfer and its
end-to-end examples include the final halt once; exact executable counts and
fuel assertions agree. Internal IR/IMP budgets and specifications are
unchanged. Concepts, full proofs, and the supervisor's narrow replay passed.
