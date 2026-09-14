# The v4.33.0 port of Jan's submissions (2026-09-14)

The epoch moved to v4.33.0 (mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`)
on 2026-09-13 and v4.30.0 closed to new records. This folder is the record
of porting Jan's submissions in this repository, prepared in a session
without submit rights; `FINISH.md` is the one-off prompt that lands and
resubmits it, `WORKER-BRIEF.md` the packet each porting worker received.

## Approach

**Drafts move in place.** A draft is updated by resubmitting, and the
publisher's only environment gate on a resubmission is closure
(`environmentAcceptsRecord`): v4.33.0 is open, so a draft keeps its id,
issue and package names and only its pins and Lean move. That is what
Jan asked for, and what the Transducers port (`plans/transducers/`) did
the same day. Four drafts: **word-ram** (lax-67), **ram-linear-time**
(lax-11), **refinement-tower** (lax-62), **nowhere-dense-model-checking**
(lax-3). Every one of the four folders on `main` was already past its
archive record (word-ram by 16 files, ram-linear-time 11, refinement-tower
4, ND-MC 8), so the port is on top of that unsubmitted work.

**Registered records get successors.** A registered record is immutable;
`lax port lax-N` scaffolds a successor (fresh id, `supersedes: lax-N`, the
target pins, every cross-submission require followed to the dependency's
own v4.33.0 successor). Clemens had already done this for the three
registered dependencies on 2026-09-13 — **lax-199508** supersedes lax-12
(sparsity lectures), **lax-345067** lax-14 (finite Ramsey), **lax-865980**
lax-13 (the word RAM, from lax-13's registered source, *not* lax-67's) —
so ND-MC now requires `Lax199508` where it required `Lax12` (renamed
throughout the folder, prose included), and the two folders
`sparsity-lectures-v4-33/`, `finite-ramsey-v4-33/` are copied here verbatim
from `codex/archive-v4.33-migration` for the local loop. One successor was
scaffolded here: **monadic-dependence-neighborhood-complexity-v4-33** =
**lax-264807**, superseding lax-5, requiring `Lax199508` and `Lax345067`.
`lax port` itself had to be fixed first: it refused every pre-six-digit id
(`lax-5`, `lax-13`, …) — `lax-archive/lax` branch
`claude/port-ndmc-latest-epoch-0slpbd`, commit `fb1da25`.

**Local loop.** `lax doctor --env v4.33.0` once (toolchain 34 s, warm store
2 m 27 s, 7.5 GB), `python3 .claude/local-overrides.py` (every package's
`lake-manifest.json` + `.lake/package-overrides.json` from the pins: the
warm store of the environment its `manifest.yaml` names, plus the sibling
folders), `.claude/capture-seed.sh sparsity-lectures-v4-33
finite-ramsey-v4-33` (the registered captures, so those two never
compile), then a direct `lake build` per package, concepts before proofs.
`lax build --replay word-ram` (the archive's own checks, kernel replay
included) runs on the one folder with no cross-submission require.

## What changed, per folder

Pins everywhere: `manifest.yaml` (`leanVersion`, `mathlibVersion`), both
`lean-toolchain` files, both lakefiles' mathlib `rev`. Then:

- **word-ram** (lax-67; 526 + 3029 jobs green). Two proof sites, taken
  from Clemens's lax-865980 port by a per-file three-way merge of
  (lax-13 source → his port) onto main's newer folder, package names
  mapped back to `Lax67`: `proofs/Lax67Proofs/Reasoning.lean:134`
  `set_arrOf` — the `simp only [arrOf, List.length_map, List.length_range]
  at h₁ h₂` no longer makes progress (drift vii), dropped;
  `proofs/Lax67Proofs/Simulation.lean:618` `compile_correct` — `simpa using
  hfits` → `simpa [compile] using hfits` (drift iv). Concepts untouched.
- **ram-linear-time** (lax-11; 1007 + 3083 jobs green). Concepts compile
  unchanged. `proofs/Lax11Proofs/MsoComposition.lean:195` `typ_succ_congr`
  — `simpa [typ_zero] using congrArg T.diagram h` → `exact congrArg
  T.diagram h` (drift iv: `T 0 r s` and `Atomic r s` are defeq, not
  syntactically equal after simp); `proofs/Lax11Proofs/MsoCliqueOps.lean:210`
  `Atomic.of_setRemap` — `decide_eq_decide` no longer fires inside `simp
  only` (drift xiv): `simp only [Atomic.of, setRemap]; refine
  decide_eq_decide.mpr ?_; simp only [Set.mem_iUnion, exists_prop]; exact
  exists_congr …`.
- **refinement-tower** (lax-62): _pending the worker's report_.
- **nowhere-dense-model-checking** (lax-3): _pending_.
- **monadic-dependence-neighborhood-complexity-v4-33** (lax-264807):
  _pending_.

## Not ported, and why (see FINISH.md §4)

- **sparsity-lectures** (lax-12, registered): Clemens's lax-199508 is its
  registered v4.33.0 successor already (same content — `main`'s folder is
  identical to lax-12's record, and his port started from that record);
  a second successor of lax-12 would be a duplicate. The v4.30 folder stays
  as the record's source.
- **lax-introduction** (lax-242665, draft): requires Lax48 (registered,
  v4.30.0, no successor — the draft lax-65 that superseded it was
  deleted). Needs `lax port lax-48` first.
- **lax-48 / lax-49** (twin-width, registered, with Édouard): `lax port`
  each, lax-49 after lax-48.
