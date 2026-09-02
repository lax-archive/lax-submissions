#!/usr/bin/env bash
# Resubmit the drafts whose sources moved, in dependency order, repinning
# each one's cross-submission requires to the record the previous step
# produced, committing and pushing the repin, then submitting. One command:
#
#   .claude/resubmit-cascade.sh              # the whole cascade
#   .claude/resubmit-cascade.sh vertex-cover-ladder nowhere-dense-model-checking
#                                            # resume from a later step
#
# Order (each folder depends only on those before it):
#   word-ram (Lax13)
#   sparsity-lectures (Lax12)                            — pin-only refresh: requires Lax14,
#                                                          whose record moved under it
#   ram-linear-time (Lax11), refinement-tower (Lax62)   — both require Lax13
#   monadic-dependence-neighborhood-complexity (Lax5)    — pin-only refresh: requires Lax12, Lax14
#   vertex-cover-ladder (Lax15)                          — requires Lax11, Lax13
#   nowhere-dense-model-checking (Lax3)                  — requires Lax11, Lax12, Lax13, Lax14, Lax62
# finite-ramsey and the two twin-width submissions match their records and
# depend on nothing that moves; they are not in the list.
#
# Extra flags for `lax submit` (e.g. --allow-dirty) go in LAX_SUBMIT_FLAGS.
# Requires a clean, committed, pushed tree at the start except for what the
# script itself commits: `lax submit` sends the pushed HEAD.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
default=(word-ram sparsity-lectures ram-linear-time refinement-tower monadic-dependence-neighborhood-complexity vertex-cover-ladder nowhere-dense-model-checking)
order=("${@:-${default[@]}}")
[ $# -eq 0 ] && order=("${default[@]}")
for sub in "${order[@]}"; do
  echo "=== $sub ==="
  lax sync
  .claude/repin.sh "$sub"
  .claude/sibling-overrides.sh >/dev/null
  if ! git diff --quiet -- "$sub/concepts/lakefile.toml" "$sub/proofs/lakefile.toml" 2>/dev/null; then
    git add "$sub/concepts/lakefile.toml" "$sub/proofs/lakefile.toml"
    git commit -q -m "$sub: repin cross-submission requires to the resubmitted records

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>"
    echo "committed repin of $sub"
  fi
  git push -q origin HEAD
  # shellcheck disable=SC2086
  lax submit ${LAX_SUBMIT_FLAGS:-} "$sub"
done
lax sync
.claude/sibling-overrides.sh
