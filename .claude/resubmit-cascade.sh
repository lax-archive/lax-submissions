#!/usr/bin/env bash
# Resubmit the drafts whose sources moved, in dependency order, repinning
# each one's cross-submission requires to the record the previous step
# produced, committing and pushing the repin, then submitting. One command:
#
#   .claude/resubmit-cascade.sh              # the whole cascade; steps already
#                                            # archived at this content are skipped
#   .claude/resubmit-cascade.sh monadic-dependence-neighborhood-complexity nowhere-dense-model-checking
#                                            # resume from a later step
#
# Order (each folder depends only on those before it), as of the v4.33.0
# port (plans/port-v4.33/FINISH.md):
#   word-ram (lax-808846)                                    — no cross-submission require
#   ram-linear-time (lax-271696), refinement-tower (lax-62)  — both require Lax808846
#   nowhere-dense-model-checking (lax-3)                 — requires Lax271696, Lax62, Lax808846 and the
#                                                          registered Lax199508
#   lax-introduction (lax-242665)                        — requires Lax808846, the registered Lax199508,
#                                                          and Lax768004 (submit
#                                                          twin-width-treewidth-separation-v4-33 first)
# sparsity-lectures and monadic-dependence are registered v4.30 records with
# registered / drafted v4.33.0 successors (lax-199508, lax-264807) and are
# not resubmitted; finite-ramsey and the two twin-width folders likewise.
#
# Extra flags for `lax submit` (e.g. --allow-dirty) go in LAX_SUBMIT_FLAGS.
# Requires a clean, committed, pushed tree at the start except for what the
# script itself commits: `lax submit` sends the pushed HEAD.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
# the commit the archive's record of a folder was submitted from ("" if none)
archived_commit() {
  python3 - "$1" <<'PY2'
import json, os, re, sys, yaml
folder = sys.argv[1]
ident = str(yaml.safe_load(open(os.path.join(folder, "manifest.yaml")))["id"]).lower()
number = re.sub(r"^lax-?", "", ident)
path = os.path.expanduser(f"~/.lax/lax-database/lax-{number}/record.json")
source = json.load(open(path)).get("source") if os.path.isfile(path) else None
print(source["commit"] if source and source.get("folder") == folder else "")
PY2
}
default=(word-ram ram-linear-time refinement-tower nowhere-dense-model-checking lax-introduction)
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
  # idempotent: a folder whose content (pins included) is already what the
  # archive holds is not resubmitted, so the cascade can be rerun after a
  # failed step without touching the steps that went through
  archived=$(archived_commit "$sub")
  if [ -n "$archived" ] && git diff --quiet "$archived" HEAD -- "$sub" 2>/dev/null; then
    echo "skip: $sub is archived at this content ($archived)"
    continue
  fi
  git push -q origin HEAD
  # shellcheck disable=SC2086
  lax submit ${LAX_SUBMIT_FLAGS:-} "$sub"
done
lax sync
.claude/sibling-overrides.sh
