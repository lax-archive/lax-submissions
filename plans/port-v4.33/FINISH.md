# Finish the v4.33.0 port of the ND-MC chain — one-off prompt for Jan's machine

Paste everything below the line into a Claude Code session in a checkout
of this repository on a machine with push rights and a logged-in `lax`
(≥ 0.1.43), or follow it by hand. Every step is a shell command plus what
to check.

---

You are finishing the port of four draft submissions from the closed
v4.30.0 archive environment to the v4.33.0 epoch: **word-ram** (lax-67),
**ram-linear-time** (lax-11), **refinement-tower** (lax-62) and
**nowhere-dense-model-checking** (lax-3), plus one new successor of a
registered record: **monadic-dependence-neighborhood-complexity-v4-33**
(lax-264807, `supersedes: lax-5`). The port itself is done and
reviewed on branch `claude/port-ndmc-latest-epoch-0slpbd`: every package
builds at v4.33.0 through the local loop, no concept statement changed,
and `README.md` in this folder records every Lean edit. What remains is
to land the branch and resubmit the chain bottom-up. Do exactly this, in
order, and stop at the first check that fails.

## 0. Preconditions (check, do not skip)

```sh
git status --short            # clean tree on main, or say what is dirty and stop
lax --version                 # ≥ 0.1.43
lax doctor --env v4.33.0      # toolchain + warm store provisioned; account logged in
lax sync
```

## 1. Land the branch

```sh
git fetch origin claude/port-ndmc-latest-epoch-0slpbd
git merge --ff-only origin/claude/port-ndmc-latest-epoch-0slpbd   # or merge, if main moved
git push
```

The branch carries, besides the four ported folders:

- `sparsity-lectures-v4-33/` and `finite-ramsey-v4-33/` — Clemens's
  registered v4.33.0 ports (lax-199508 @ `e9845c2`, lax-345067 @
  `feabf43`), copied verbatim from `codex/archive-v4.33-migration` so the
  local loop can build ND-MC against the sibling folder. If that branch
  has been merged to `main` in the meantime the merge is a no-op on them.
- `.claude/local-overrides.py` — seeds every package's `lake-manifest.json`
  and `.lake/package-overrides.json` (warm store + sibling folders) from
  the pins alone, so a direct `lake build` works before the pins are on the
  archive. `.claude/sibling-overrides.sh` only rewrites the sibling half
  and needs the warm redirects `lax build` writes; this one needs nothing.

Optional local proof that the tree builds before submitting anything
(word-ram ~5 min, ram-linear-time ~10 min, refinement-tower and ND-MC
much longer — one package at a time, concepts before proofs; the two
`-v4-33` dependencies are registered, so `.claude/capture-seed.sh
sparsity-lectures-v4-33 finite-ramsey-v4-33` installs their builds in
seconds):

```sh
python3 .claude/local-overrides.py
export PATH=$HOME/.elan/bin:$PATH LAKE_ARTIFACT_CACHE=false
for s in word-ram ram-linear-time refinement-tower nowhere-dense-model-checking monadic-dependence-neighborhood-complexity-v4-33 twin-width-treewidth-separation-v4-33 lax-introduction; do
  (cd $s/concepts && lake build) && (cd $s/proofs && lake build) || { echo "FAIL $s"; break; }
done
```

## 2. Resubmit the chain bottom-up

The archive only lets same-environment records cite one another, so each
draft is resubmitted after its dependencies, and every resubmission moves
a record its dependents pin. `.claude/resubmit-cascade.sh` does exactly
this per folder: `lax sync`, `.claude/repin.sh <folder>` (every
`LaxN`/`LaxNProofs` require set to the record's current `source`), commit
the repin, push, `lax submit`. Pass the four folders explicitly — the
script's default list still names the v4.30 sparsity/monadic pin-only
refreshes, which do not apply any more:

```sh
LAX_SUBMIT_FLAGS="--force" .claude/resubmit-cascade.sh word-ram ram-linear-time refinement-tower nowhere-dense-model-checking
```

`--force` skips the local `lax build` before each submit (the honest
build clones every pinned dependency and builds it from source — hours
for ND-MC); the archive is the verdict. Drop it if you want the local
build.

The order, with ids and what each step repins:

| step | folder | id | repinned requires |
|---|---|---|---|
| 1 | `word-ram` | lax-67 | none |
| 2 | `ram-linear-time` | lax-11 | Lax67, Lax67Proofs → step 1's record |
| 3 | `refinement-tower` | lax-62 | Lax67, Lax67Proofs → step 1's record |
| 4 | `nowhere-dense-model-checking` | lax-3 | Lax67, Lax67Proofs → 1; Lax11 → 2; Lax62, Lax62Proofs → 3; Lax199508, Lax199508Proofs → lax-199508's record (already registered; the branch pins it already, so this is a no-op) |

Steps 2 and 3 both depend only on step 1 and can be submitted back to
back. After each step:

```sh
lax sync
python3 -c "import json;b=json.load(open('$HOME/.lax/lax-database/lax-<id>/build-output.json'));print(b['inputs']['manifest']['leanVersion'], b['capture']['sourceCommit'][:8])"
# expect: v4.33.0 and the commit you just pushed
```

Known outcomes to expect, and what to do:

- **A validation error in a Lean file**: the port was built with the
  archive's toolchain and mathlib locally, so a failure here is most likely
  the archive's `lax` release differing from the 0.1.43 source tree the
  port used. Read the report `lax submit` downloads, fix the one site in
  the proof package the same way `README.md` fixes that drift class,
  commit, push, resubmit that folder; downstream folders then need a repin
  (rerun the cascade from that folder). Never change a `concepts/` file to
  get through; stop and report instead.
- **"proofs kernel replay exceeded its time limit"**: refinement-tower and
  ND-MC are large; resubmit the same commit once with `--force`. If it
  fails identically twice, stop and report — that is a limits question for
  the archive, not a port defect.
- **Warnings** `layout · proof-dependency` (proof packages require proof
  packages), `dependencies · draft-dependency` and `statements ·
  unused-lemma` were there at v4.30 and are expected.

### 2b. The successor of lax-5

`monadic-dependence-neighborhood-complexity-v4-33` (lax-264807) pins only
registered v4.33.0 records (Lax199508, Lax345067), so it needs no cascade
step: it is a *first* submit of a new id, which takes two runs (the first
binds the control issue into `manifest.yaml` and asks for a commit):

```sh
lax submit --force monadic-dependence-neighborhood-complexity-v4-33   # binds the issue, stops
git add monadic-dependence-neighborhood-complexity-v4-33/manifest.yaml && git commit -m "lax-264807: bind the archive issue" && git push
lax submit --force monadic-dependence-neighborhood-complexity-v4-33
lax sync   # expect ~/.lax/lax-database/lax-264807 as a draft at v4.33.0
```

It stays a draft; registering it (which also marks lax-5 superseded) is
your call, as for the others.

### 2c. The successor of lax-48, then lax-introduction

`twin-width-treewidth-separation-v4-33` (lax-768004, `supersedes: lax-48`,
mathlib only, paper untouched) is a first submit like 2b — two runs. Then
`lax-introduction` (lax-242665, draft, in place) requires it: its lakefile
already names `Lax768004` with a placeholder rev, so it is repinned after
lax-768004 has a record, and after step 1 for `Lax67`:

```sh
lax submit --force twin-width-treewidth-separation-v4-33   # binds the issue, stops
git add twin-width-treewidth-separation-v4-33/manifest.yaml && git commit -m "lax-768004: bind the archive issue" && git push
lax submit --force twin-width-treewidth-separation-v4-33
lax sync
LAX_SUBMIT_FLAGS="--force" .claude/resubmit-cascade.sh lax-introduction   # repins Lax768004, Lax199508, Lax67; submits
```

lax-introduction carries a paper; the archive compiles it (the `paper ·
web-oracle` warning class, if any, is pre-existing).

## 3. Close out

```sh
lax sync
for id in 67 11 62 3 264807 768004 242665; do
  python3 -c "import json;b=json.load(open('$HOME/.lax/lax-database/lax-$id/build-output.json'));print('lax-$id', b['inputs']['manifest']['leanVersion'], b['capture']['sourceCommit'][:8])"
done
```

All seven must read `v4.33.0`. Then note it in `plans/README.md` (one line
under the 2026-09 entries), commit, push. Registration stays your manual
step, bottom-up, as before the port.

## 4. Decisions the port could not make (yours)

1. **lax-67 no longer claims to supersede lax-13 — decided by the
   archive, confirm or reverse.** Clemens registered `word-ram-v4-33` as
   **lax-865980** (`supersedes: lax-13`, ported from lax-13's *registered*
   source `92ae2d6`) on 2026-09-13, and the archive allows one successor:
   `lax build word-ram` with the old manifest failed at the dependency
   gate, `supersedes-taken: lax-865980 already supersedes lax-13`, so
   lax-67 could not be resubmitted at all with that line. The port
   therefore **removed `supersedes: lax-13` from `word-ram/manifest.yaml`**
   (commit "word-ram: drop the supersedes claim"): lax-67 stays your
   draft of the newer word RAM (main's folder is 16 files / 700 lines past
   lax-13, and past lax-67's own record), now a stand-alone one, and
   ND-MC, ram-linear-time and refinement-tower keep requiring `Lax67`.
   The alternative is to retire lax-67 and build on lax-865980: `Lax67`
   → `Lax865980` in the three dependents' lakefiles, imports, namespaces
   and prose (the same rename this port did for `Lax12` → `Lax199508` in
   ND-MC), then repin — but lax-865980 lacks the 700 lines of word-ram
   changes since lax-13, so check first that the dependents do not use
   them (`git diff 92ae2d6:word-ram main:word-ram`). The end state either
   way is probably one v4.33.0 word RAM, with the other deleted.
2. **The registered dependencies were replaced, not ported.** ND-MC now
   requires **Lax199508** (Clemens's registered v4.33.0 sparsity lectures,
   `supersedes: lax-12`) where it required Lax12; `Lax12` was renamed to
   `Lax199508` everywhere in the folder, prose included (89 files). The
   port's concept surface is otherwise unchanged. Lax14 was not a direct
   require of ND-MC.
3. **Not ported (yours, registered or blocked):**
   - **lax-49** (twin-width mixed minor number, registered, with Édouard):
     `lax port lax-49` after lax-768004 has a record (it requires Lax48,
     which the port follows to lax-768004 once that is *registered*; while
     lax-768004 is a draft the port leaves the Lax48 pin and says so —
     repoint by hand as lax-introduction was).
   - **sparsity-lectures** (lax-12, registered): already has its
     registered v4.33.0 successor, Clemens's lax-199508, ported from
     lax-12's own record (`main`'s folder is identical to that record), so
     nothing was ported here — a second successor would duplicate it. If
     you want the successor under your ownership instead, that is an
     owners question on lax-199508 (`/lax admin owners`), not a port.
   - **lax-48 / lax-49** (twin-width, registered, with Édouard): `lax port`
     each, lax-49 after lax-48.
   - The eight Transducers drafts are on branch
     `claude/transducers-latest-epoch-port-jiv5kl`, with their own
     `plans/transducers/FINISH.md`.
