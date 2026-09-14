# Finish the Transducers v4.33.0 port — one-off prompt for Jan's machine

Paste everything below the line into a Claude Code session started in a
checkout of `bojanczyk/transducer-book`, on a machine with push rights to
that repository and a logged-in `lax` (≥ 0.1.43). It can also be followed by
hand; every step is a shell command plus what to check.

---

You are finishing the port of the eight *Transducers* submissions
(`lax/` in this repository) from the closed v4.30.0 archive environment to
the v4.33.0 epoch. The port itself is done and reviewed: every package
builds at v4.33.0, one concept file changed (`Sym8`, agreed), and the
work sits as a patch series in the lax-submissions repository, branch
`claude/transducers-latest-epoch-port-jiv5kl`, folder `plans/transducers/`
(`README.md` there explains the layout; `book-lax/CAMPAIGN.md`, section
"v4.33.0 port", lists every edit). What remains is to land the patches
here and resubmit the chain bottom-up. Do exactly this, in order, and stop
at the first check that fails.

## 0. Preconditions (check, do not skip)

```sh
git status --short            # clean tree on main, or say what is dirty and stop
git log -1 --format=%h main   # the patches were made over 4ec9235; a newer main is fine
lax --version                 # ≥ 0.1.43
lax doctor --env v4.33.0      # toolchain + warm store provisioned; account logged in
lax sync
```

## 1. Land the patches

```sh
git checkout -b port-v4.33 main
git am /path/to/lax-submissions/plans/transducers/patches/*.patch
git log --oneline main..port-v4.33      # expect the series: pins, tools, S0+S1, S2, S3, S4, S5, CONCEPT CHANGE (Sym8), S6, docs, ledger
```

If `git am` stops on a conflict, the only plausible cause is a `lax/`
change on `main` after 4ec9235; resolve it keeping both, `git am --continue`.
Never edit a `concepts/` file beyond what patch 12 (`CONCEPT CHANGE`) does.

Optional local proof that the tree builds before submitting anything
(30–60 min in total, one package at a time):

```sh
cd lax && python3 tools/local-overrides.py && cd ..
export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0/bin:$PATH LAKE_ARTIFACT_CACHE=false
for s in pcp-undecidability mealy-machines rational-functions regular-functions mso-transductions regular-combinators polyregular-functions transducers-book; do
  (cd lax/$s/concepts && lake build) && (cd lax/$s/proofs && lake build) || { echo "FAIL $s"; break; }
done
```

Then merge and push: `git checkout main && git merge --ff-only port-v4.33 && git push`.
Every `lax submit` below submits the pushed HEAD; nothing is submitted
from an unpushed commit.

## 2. Resubmit the chain bottom-up

The archive only lets same-environment records cite one another, so each
part is resubmitted after its dependencies, and every resubmission moves a
record that its dependents pin. The pattern for one step is:

```sh
# repin to the records as they are now (prints one line per changed pin; 0 changes is fine for S0/S1)
python3 lax/tools/repin.py <folder>...
git add lax && git commit -m "lax/<folder>: repin at v4.33.0" && git push
lax submit lax/<folder> --force --allow-dirty     # --force: no local build, the archive is the verdict
lax sync
python3 -c "import json;b=json.load(open('$HOME/.lax/lax-database/lax-<id>/build-output.json'));print(b['inputs']['manifest']['leanVersion'], b['capture']['sourceCommit'][:8])"
# expect: v4.33.0 and the commit you just pushed
```

The order, with ids:

| step | folder(s) | id | requires |
|---|---|---|---|
| 1 | `pcp-undecidability` | lax-251941 | none |
| 2 | `mealy-machines` | lax-765601 | none |
| 3 | `rational-functions` | lax-132576 | 1, 2 |
| 4 | `regular-functions` | lax-916827 | 2, 3 |
| 5 | `mso-transductions` | lax-314295 | 2, 3, 4 |
| 6 | `regular-combinators` | lax-709149 | 2, 3, 4 |
| 7 | `polyregular-functions` | lax-194892 | 2, 3, 4, 5 |
| 8 | `transducers-book` | lax-157538 | all seven — regenerate its lakefiles with `cd lax && python3 tools/umbrella-pins.py` instead of `repin.py` |

Steps 1 and 2 need no repin (no requires) and can be submitted back to back.
Steps 5 and 6 both depend only on 2–4 and can be repinned in one commit and
submitted back to back. Everything else waits for the previous record to
show `v4.33.0` in `lax sync`.

Known outcomes to expect, and what to do:

- **"proofs kernel replay exceeded its time limit"** on step 4 or 7 (the
  large packages; Part D hit the 20-minute cap once at v4.30 and the
  identical retry passed): resubmit the same commit once with `--force`. If
  it fails identically twice, stop and report — that is a limits question
  for the archive, not a port defect.
- **A validation error in a Lean file**: the port was built and, for S0
  and S1, replayed with the archive's own checks locally, so a failure here
  is most likely the archive's `lax` release differing from the source tree
  the port used (0.1.43). Read the report `lax submit` downloads, fix the
  one site in the proof package the same way CAMPAIGN.md's "v4.33.0 port"
  fixes that drift class, commit, push, resubmit that part; downstream
  parts then need a repin. Never change a `concepts/` file to get through;
  stop and report instead.
- **Warnings** `layout · proof-dependency` (proof packages require proof
  packages) and `dependencies · draft-dependency` are expected and were
  there at v4.30; `statements · unused-lemma` likewise.
- The umbrella's known warning `paper · web-oracle` (reflow similarity
  0.9800) is pre-existing and not part of this port.

## 3. Close out

```sh
lax sync
for id in 251941 765601 132576 916827 314295 709149 194892 157538; do
  python3 -c "import json;b=json.load(open('$HOME/.lax/lax-database/lax-$id/build-output.json'));print('lax-$id', b['inputs']['manifest']['leanVersion'], b['capture']['sourceCommit'][:8])"
done
```

All eight must read `v4.33.0`. Then update the status column of the table
at the top of `lax/CAMPAIGN.md` (one line per row: "draft on the archive at
v4.33.0 (<commit>)"), commit, push. Registration stays Jan's manual step,
bottom-up, as before the port.

Report at the end: the eight (id, commit) pairs, any retry that was needed,
and any fix you had to make beyond the patch series.
