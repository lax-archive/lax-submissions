#!/usr/bin/env bash
# Prepare a machine and a checkout for lax submission development: everything
# needed before the first `lake build`, and nothing that belongs to a
# particular submission. Idempotent, non-interactive, no arguments:
#
#   .claude/dev-setup.sh
#
# It is the whole-machine counterpart of worktree-seed.sh. That script seeds a
# *worktree* from a warm main checkout; this one creates the warmth in the
# first place, on a container that has none.
#
# The work splits in two, along the line the cloud environment cache draws:
#
#   the machine half   `.claude/cloud-setup.sh` — the lax CLI, elan and the
#                      pinned toolchain, the warm mathlib store. Lives under
#                      ~/.elan and ~/.lax, shared by every checkout on the
#                      machine, ~4 min cold. Belongs in the environment's
#                      **Setup script** field, whose filesystem snapshot is
#                      reused by later sessions; this script just calls it, and
#                      the call costs ~3 s once the snapshot has it.
#
#   the checkout half  steps 2 and 3 below — the archive database refresh and
#                      each package's lake-manifest.json and
#                      .lake/package-overrides.json. Per-checkout, gitignored,
#                      and cheap, so it runs on every session start: the
#                      repository is cloned fresh each time, lakefiles move as
#                      the campaign moves, and archive records go stale
#                      whenever a dependency is re-submitted.
#
# So a cloud session normally runs the machine half from its cached snapshot
# and only the checkout half at session start. Running this whole script is
# still correct anywhere — a laptop, a worktree, a container whose cache
# expired — because the machine half short-circuits when it is already done.
#
# Neither half touches the submissions' own `.lake/build`, so a fresh checkout
# still compiles each package once. Two optional knobs close that gap, both
# unset by default:
#
#   LAX_SEED_CAPTURES=all            install the archive's published build
#   LAX_SEED_CAPTURES="word-ram ..." artifacts from ghcr instead of compiling
#                                    (`.claude/capture-seed.sh`, seconds). The
#                                    usual choice — but it can only help where
#                                    the tree still matches a submitted commit.
#   LAX_SETUP_BUILD="word-ram ..."   compile those submissions' packages,
#                                    concepts before proofs. What you need when
#                                    the working tree has moved past the last
#                                    submission and no capture matches it.
#
# What it deliberately does not do: `lax login` (a browser device flow) and
# anything that talks to the archive server. Submitting is Jan's step, from
# Jan's machine.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"

step() { printf '\n=== dev-setup: %s\n' "$1" >&2; }
note() { printf '    %s\n' "$1" >&2; }

# --- 1. the machine half ---------------------------------------------------

"$root/.claude/cloud-setup.sh"

# --- 2. the archive database clone -----------------------------------------
# Cross-submission requires are pinned to these records, and re-submitting a
# dependency moves its record — so this is refreshed per session, not cached
# with the machine half. Non-fatal: a checkout with no cross-submission edges
# builds without it, and a stale record is a mismatch sibling-overrides.sh
# reports by name.

step "archive database"
if lax sync >&2; then  # `lax pull-db` before CLI 0.1.31
  note "records at $HOME/.lax/lax-database"
else
  note "WARNING: pull-db failed; cross-submission pins cannot be resolved"
fi

# --- 3. the per-package generated files ------------------------------------
# `.claude/local-overrides.py` writes, for every package of the checkout, the
# complete manifest (the proof package's own concept package, every
# cross-submission require of the closure as the git entry its lakefile
# declares, then the warm workspace's locked mathlib closure verbatim) and the
# overrides redirecting each of those names — mathlib and friends to the
# store of the environment the submission's manifest.yaml names, each
# LaxN/LaxNProofs to the sibling folder — exactly as `lax build` would, so
# lake resolves nothing, clones nothing, and runs no post_update hook. Both
# files are rewritten from the pins alone on every run; the sibling entries
# come from the same pins, so nothing is lost by rewriting. A submission whose
# environment has no store on this machine is reported and skipped (`lax
# doctor --env <id>` provisions it).

step "package manifests and overrides"
python3 "$root/.claude/local-overrides.py" "$root" >&2 || \
  note "WARNING: some packages were not seeded (see above)"

# The cross-submission half: rev-pinned requires redirected to this checkout's
# sibling folders. Reports every pin that no longer matches its archive record.
"$root/.claude/sibling-overrides.sh" >&2 || \
  note "WARNING: sibling-overrides.sh failed; cross-submission builds will use the pins"

# --- 4. optional: warm the submissions themselves --------------------------
# Two ways, and captures are usually the one you want: seconds and a download
# against minutes of compilation, for any submission whose tree still matches
# the commit the archive built. LAX_SETUP_BUILD compiles the working tree
# instead, which is what you need when it has moved past the last submission.

if [ -n "${LAX_SEED_CAPTURES:-}" ]; then
  step "capture seeding (LAX_SEED_CAPTURES)"
  # "1" or "all" means every submission with a capture; otherwise a folder list
  case "$LAX_SEED_CAPTURES" in
    1|all) "$root/.claude/capture-seed.sh" >&2 || note "WARNING: capture seeding failed" ;;
    *) "$root/.claude/capture-seed.sh" $LAX_SEED_CAPTURES >&2 || note "WARNING: capture seeding failed" ;;
  esac
fi

if [ -n "${LAX_SETUP_BUILD:-}" ]; then
  step "submission builds (LAX_SETUP_BUILD)"
  for submission in $LAX_SETUP_BUILD; do
    for kind in concepts proofs; do
      dir="$root/$submission/$kind"
      [ -d "$dir" ] || continue
      note "lake build in $submission/$kind"
      (cd "$dir" && LAKE_ARTIFACT_CACHE=false lake build >&2) || \
        note "WARNING: $submission/$kind did not build"
    done
  done
fi

# `lax doctor` is the authority on whether this worked, so end with its verdict
# rather than a claim of our own. One problem is expected and correct here:
# `github auth`, which only `lax login`'s browser device flow can satisfy and
# which nothing short of `lax submit` needs.
step "ready"
lax doctor 2>&1 | grep -vE '✓' >&2 || true
