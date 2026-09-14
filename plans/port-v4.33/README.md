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
from `codex/archive-v4.33-migration` for the local loop. Two successors were
scaffolded here: **monadic-dependence-neighborhood-complexity-v4-33** =
**lax-264807**, superseding lax-5, requiring `Lax199508` and `Lax345067`;
and **twin-width-treewidth-separation-v4-33** = **lax-768004**, superseding
lax-48 (co-owned with Édouard; the draft lax-65 that once superseded lax-48
was deleted), mathlib only, paper carried unchanged — the dependency
**lax-introduction** (lax-242665, draft, in place) needs, beside
`Lax199508` and `Lax67`.
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
  `lax build --replay word-ram` (the archive's own checks) is green:
  layout, dependencies, compile, kernel replay 49 s, inspect (2 concepts
  · 0 proofs), 1 m 02 s in all; its 608 `statements · unused-lemma`
  warnings are the pre-existing class (the proof package is a library
  with no proof theorem, so every helper is "unused"). Two things that
  gate found first: the manifest's pins had been reverted by a `git
  checkout` during the merge (fixed, commit e937cf9), and
  **`supersedes-taken`** — lax-865980 already supersedes lax-13 and the
  archive allows one successor, so lax-67 could not be resubmitted with
  its `supersedes: lax-13` line; the line is removed (commit 75dad69,
  FINISH.md §4.1).
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
- **twin-width-treewidth-separation-v4-33** (lax-768004): _pending_.
- **lax-introduction** (lax-242665; concepts 585 jobs green): pins, and
  `Lax48` → `Lax768004`, `Lax12` → `Lax199508` in the lakefiles, the Lean
  and the paper's markers; proofs build once lax-768004's concepts do.
- **monadic-dependence-neighborhood-complexity-v4-33** (lax-264807;
  2080 + 2840 jobs green; concepts compile with every declared statement
  byte-identical). The scaffold had left `import Lax12.*`/`Lax14.*` in the
  sources (fixed in `lax port` afterwards, lax commit 044cfa8): renamed to
  `Lax199508`/`Lax345067` everywhere, prose included. Proof sites, by
  drift class — (xi) `Std.Symm` bundling: `proofs/AdlerAdler.lean:48`,
  `SubdividedBicliqueRamsey.lean:256-258`, `CrossingTransduction.lean:60`
  (`G.symm h` → `G.adj_symm h`; `h.symm` there resolves to the recursive
  `BlueWalk.symm` and fails termination); (iv) `simpa` stricter:
  `Sparsification.lean:769` (`simpa [f', tup]`), `NowhereDenseBridge.lean:
  318,340,349` (`exact congrArg copy h`); (i) `TransductionCalculus.lean:
  125-127` (`show … + exact`); (xiv) `SubdividedBicliqueRamsey.lean:341-344`
  (`decide_eq_decide.mp` by hand); (vii) `SubdividedBicliqueRamsey.lean:
  1333` (`try simp only […]` — one `rcases` branch makes no progress).
  New classes: **(xv)** a `Walk.copy` whose proof arguments came from `rfl`
  carries the walk's own endpoints in its type, so `support_copy` /
  `length_copy` / `isPath_copy` never fire ("Application type mismatch …
  _proof_1") — give each proof its declared type with `show lhs = rhs from
  …` (`NowhereDenseBridge.lean:251-256`, which cleared six downstream
  errors); **(xvi)** plain `simp [f]` where `f` unfolds to a `Walk.cons` no
  longer applies `length_cons`/`cons_isPath_iff`/`support_cons` — name them
  under `simp only` (`NowhereDenseBridge.lean:176-178,188,272-273`);
  **(xvii)** `Walk.getVert_zero`/`getVert_length` do not fire under `simp`
  for a walk whose endpoints are `Fin.mk` literals with `by omega` proofs —
  use the term and `rw` (`SubdividedBicliqueRamsey.lean:1087-1091,
  1553-1561`); **(xviii)** an argument supplied at a type only δ-equal to
  the expected one poisons every later `rw`/`simp` in that application
  (`colors : Fin (5*k+2) → …` where `Fin (sparsTransduction k).colors → …`
  is expected: `realize_sup`/`realize_inf` "did not find an occurrence" on
  a pattern that prints identically) — `change` the goal to the fully
  spelled-out formula first (`SparsGraphs.lean:142-147,247-263`;
  `SubdividedBicliqueRamsey.lean:679` `show … before omega`); **(xix)**
  `Function.Embedding.coeFn_mk` does not fire while the embedding
  literal's `inj'` field is still a metavariable inside a `refine ⟨{ … }⟩`
  — bind the embedding with `let`, prove its three `rfl` computation
  lemmas, pass them to `simp_all` (`Corollary6a.lean:272-297`, the one
  moderate restructure; the lemma statement is unchanged).

## Not ported, and why (see FINISH.md §4)

- **sparsity-lectures** (lax-12, registered): Clemens's lax-199508 is its
  registered v4.33.0 successor already (same content — `main`'s folder is
  identical to lax-12's record, and his port started from that record);
  a second successor of lax-12 would be a duplicate. The v4.30 folder stays
  as the record's source.
- **lax-49** (twin-width mixed minor number, registered, with Édouard):
  `lax port lax-49` once lax-768004 is registered (FINISH.md §4).
