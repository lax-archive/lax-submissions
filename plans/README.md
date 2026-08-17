# plans/ — campaign records

Process history of the submissions in this repository: statement designs,
proof-pipeline surveys, per-campaign plans, and overnight relay briefs.
Each file carries its status in its own header. Folder names mirror the
submission directories at the repo root. New campaigns start their plan
and brief files here, not at the root.

**Open campaigns**

| plan | what |
|------|------|
| `nowhere-dense-model-checking/algorithm-v2.md` | FO model checking is FPT on nowhere dense classes (GKS), rebuilt on the Dreier–Toruńczyk rank-preserving locality theorem (arXiv 2606.23180). **Restarted 2026-08-17 on Jan's instruction**: the entire algorithmic layer (105 files, 103k lines of word-RAM realization plus the abstract evaluator) was pruned and the algorithm redesigned from first principles — pseudocode with per-node charges, one arena builder, greedy scatter, a hard gate at the abstract algorithm before any machine work. The mathematical layer (locality engine, splitter game, sparse covers, the two rewrites; 25 files) survives untouched and green. What was removed and what it taught is in `pruned-algorithmic-layer.md`; the older plans below are evidence, not live plans. |
| `nowhere-dense-model-checking/execution-plan.md` + `execution-ledger.md` | the operational half of the above: §8 of `algorithm-v2.md` expanded into thirteen leaves (E0–E13) with owned files, dependencies, source pins and per-leaf hazards, plus the mutable ledger recording where each stands. Driven by `/ndmc` (`.claude/commands/ndmc.md`), a supervisor loop that dispatches waves of subagents, gates, lands and repeats without stopping at ordinary boundaries. Opened 2026-08-17; wave 1 is E1–E3. |
| `word-ram/tower-expansion-plan.md` | aggressive porting of the remaining Lammich/Haslbeck refinement stack, under Jan's 2026-07-31 mandate (infrastructure is an order of magnitude cheaper than hand-coding a submission; when in doubt, port more). Rev 7 OPEN 2026-08-06 — P0–P4.5 complete (signature machinery, FOREACH, currencies + asymptotics, credits, IICF interfaces + twelve implementation families, ownership substrate with O(1) allocator and compiled space-budget law). Live phase: **P4.6**, the two-half order-phase synthesis probe (S tractability / M member-driven, ledger E42); P5.D/E breadth, P6–P8, and the P9 consumer gate follow its outcome. |

**Proposed campaigns**

| plan | what |
|------|------|
| `pcp-theorem/pcp-plan.md` | the PCP theorem by Dinur gap amplification — the first formal hardness artifact in any assistant. Machine-free Amplification Theorem as the P7 flagship (explicit size-linear gap-doubling transformation on constraint graphs, no machine model anywhere); PCP proper at P8 over the word RAM with tower-verified reduction cost. Five-submission ladder: `constraint-graphs/`, `spectral-expanders/`, `linearity-testing/`, `gap-amplification/`, `pcp-theorem/`. Rev 1 PROPOSAL 2026-07-29, queued behind the RAM campaigns (flag 2 resolved by Jan same day: waits until the dust settles on tower + ND-MC RAM) — flags 1, 3, 4 (charter scope, NP-over-RAM surface, split) open. |

Everything else is closed — most recently
`word-ram/refinement-tower-plan.md` (P0–P8 in three sessions; closing
verdict and adoption analysis in `word-ram/refinement-tower/p8-verdict.md`,
adoption resolved 2026-07-30 by the ND-MC rebase decision).

Cross-cutting process files live at this directory's root:
`submission-polish.md` (closed), `subagent-retro-2026-07.md` (July worker
retrospective), and `worker-brief-template.md` (CONDITIONAL — default sequential workers get
the compact task packet defined at its top; the full template only for an
explicitly requested parallel/isolated wave or a recorded handoff risk).

The live cross-campaign log stays at the root (`NIGHTLOG.md`) and cites
these files by their original root-level names. The map:

| then (repo root)                                            | now                                          |
|-------------------------------------------------------------|----------------------------------------------|
| `design.md`, `pipeline.md`, `cor6a-plan.md`, `adleradler-plan.md` | `monadic-dependence-neighborhood-complexity/` |
| `todo.md`                                                   | `monadic-dependence-neighborhood-complexity/implementation-log.md` |
| `ram-stack-plan.md`                                         | `ram-linear-time/`                           |
| `cc-night-brief.md`                                         | `ram-linear-time/ram-stack-night-brief.md`   |
| `courcelle-plan.md`, `courcelle-night-brief.md`             | `ram-linear-time/`                           |
| `word-ram-plan.md`                                          | `word-ram/`                                  |
| `sparsity-lectures-plan.md`                                 | `sparsity-lectures/`                         |
| `ramsey-fundamentals-plan.md`                               | `finite-ramsey/`                             |
| `vc-ladder-plan.md`, `vc-night-brief.md`, `vc-fib-plan.md`, `vc-fib-night-brief.md`, `vc-rung-b-plan.md`, `vc-contracts/` | `vertex-cover-ladder/` |
| `submission-polish.md`                                      | `./` (cross-cutting)                         |

The two renames fix misleading names: `todo.md` was a completed
implementation log with no open tasks, and `cc-night-brief.md` was the
relay brief for the `ram-stack-plan.md` step-6 campaign (the `CC.lean`
driver), not a Courcelle document.
