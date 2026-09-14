# Transducers: the v4.33.0 port (prepared 2026-09-14)

The eight *Transducers* submissions (Bojańczyk, `bojanczyk/transducer-book`,
folder `lax/`) are drafts on the archive in the closed v4.30.0 environment.
This branch carries their port to the epoch, v4.33.0 (mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`), prepared in a session that could
neither push to the book's repository nor submit. Everything a submission
needs is done except the submissions themselves.

## What is here

- `patches/` — the port as a `git format-patch` series against the book's
  `main` at `4ec9235`, one commit per boundary. This is the copy-back:
  `git am plans/transducers/patches/*.patch` in a checkout of the book.
- The eight submission folders at the repository root, byte-identical to the
  patched `lax/<name>` folders of the book: `pcp-undecidability`,
  `mealy-machines`, `rational-functions`, `regular-functions`,
  `mso-transductions`, `regular-combinators`, `polyregular-functions`,
  `transducers-book`. They are here so that the port builds in this
  repository's local loop; the book is the home.
- `book-lax/` — the book's `lax/` bookkeeping as patched: `CAMPAIGN.md` (the
  ledger, with the port's "v4.33.0 port" section listing every source edit),
  `CLAUDE.md`, `PLAN.md`, and `tools/` (`local-overrides.py`, `repin.py`,
  `umbrella-pins.py`, `port.py`, `mark_paper.py`).

## Why in place, not `lax port`

`lax port` scaffolds a *successor* (fresh id, `supersedes: lax-N`). A
supersedes claim binds only against a **registered** target, and `lax submit`
refuses a claim that can never bind — and all eight records are drafts. Drafts
are updated by resubmitting, and the publisher's only environment gate on a
resubmission is closure (`environmentAcceptsRecord`): v4.33.0 is open, so a
draft created 2026-09-07 may resubmit in it. The ids, issues, package names
and the umbrella's paper markers therefore all stay as they are; only the
pins and the Lean moved.

## What changed

1. Pins: `manifest.yaml` (`leanVersion`, `mathlibVersion`), both
   `lean-toolchain` files and both lakefiles' mathlib `rev` in all eight
   submissions, plus the rev in `tools/umbrella-pins.py`.
2. Lean: proof packages (`proofs/**`), the smallest change that compiles at
   the new mathlib; no statement changed. One concept file changed, as its
   own patch (`CONCEPT CHANGE` in the subject): `Sym8`'s finiteness
   instance in `regular-combinators/concepts/Lax709149/Types.lean`, because
   `deriving Fintype` on an enum fails at this mathlib pin — discussed with
   Jan 2026-09-14. The per-file list, with the fourteen drift classes and
   their fix patterns, is the "v4.33.0 port" section of
   `book-lax/CAMPAIGN.md`.
3. Tools: `tools/local-overrides.py` seeds `lake-manifest.json` and
   `.lake/package-overrides.json` for every package (warm store + sibling
   folders) so a direct `lake build` works before the pins are on the
   archive; `tools/repin.py` repins requires to the archive's records.

## Building here

    lax doctor --env v4.33.0                 # once: toolchain + warm store (~7.5 GB)
    python3 plans/transducers/book-lax/tools/local-overrides.py .   # seeds all 16 packages
    export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0/bin:$PATH LAKE_ARTIFACT_CACHE=false
    (cd mealy-machines/concepts && lake build) && (cd mealy-machines/proofs && lake build)

Bottom-up order: `pcp-undecidability`, `mealy-machines`, `rational-functions`,
`regular-functions`, `mso-transductions`, `regular-combinators`,
`polyregular-functions`, `transducers-book`. `.claude/sibling-overrides.sh`
works too once each package has been seeded once. Only `pcp-undecidability`
and `mealy-machines` can go through `lax build` before the chain is
resubmitted: every other part's requires name v4.30.0 records, which the
resolution phase refuses ("only submissions in v4.33.0 can cite one
another").

## Submitting (Jan): bottom-up, repin at every step

The archive lets only same-environment records cite one another, so the chain
is resubmitted leaf first, and every resubmission moves a record that its
dependents pin. From the book checkout with the patches applied and pushed:

    lax sync
    # S0, S1 — no cross-submission requires
    lax submit lax/pcp-undecidability --force --allow-dirty
    lax submit lax/mealy-machines     --force --allow-dirty
    lax sync
    # S2 ← S0, S1
    python3 lax/tools/repin.py rational-functions && git commit -am "lax/rational-functions: repin at v4.33.0" && git push
    lax submit lax/rational-functions --force --allow-dirty && lax sync
    # S3 ← S1, S2
    python3 lax/tools/repin.py regular-functions && git commit -am "..." && git push
    lax submit lax/regular-functions --force --allow-dirty && lax sync
    # S4, S5 ← S3 (independent of each other)
    python3 lax/tools/repin.py mso-transductions regular-combinators && git commit -am "..." && git push
    lax submit lax/mso-transductions --force --allow-dirty
    lax submit lax/regular-combinators --force --allow-dirty && lax sync
    # S6 ← S4
    python3 lax/tools/repin.py polyregular-functions && git commit -am "..." && git push
    lax submit lax/polyregular-functions --force --allow-dirty && lax sync
    # S7, the umbrella ← all seven
    (cd lax && python3 tools/umbrella-pins.py) && git commit -am "..." && git push
    lax submit lax/transducers-book --force --allow-dirty

`--force` skips the local build; the archive is the verdict (`lax sync`, then
`~/.lax/lax-database/lax-N/build-output.json`). The Part D proof package hit
the 20-minute replay cap once before (its identical retry passed); expect the
same possibility on the first v4.33.0 submission of the large packages.
