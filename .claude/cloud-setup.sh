#!/usr/bin/env bash
# The machine half of the lax development environment: the lax CLI, elan and
# the epoch's toolchain, and the epoch's warm mathlib store. Everything here
# lives outside the repository, under ~/.elan and ~/.lax, and is shared by
# every checkout and worktree on the machine. Nothing here reads the checkout —
# the script is deliberately self-contained, so it can run before the
# repository exists.
#
# This is the script to paste into the **Setup script** field of the cloud
# environment dialog at claude.ai/code. That is the only place whose work gets
# cached: Anthropic snapshots the filesystem once the setup script completes
# and reuses that snapshot for every later session, so the ~4 minutes below are
# paid roughly once a week (the cache rebuilds when the script changes, when
# the allowed hosts change, or after about seven days) instead of once per
# session. A SessionStart hook runs after that snapshot is taken, so work done
# there is never cached — which is why the expensive steps live here and not in
# `.claude/hooks/session-start.sh`.
#
# Measured cold 2026-08-08 on a web container, against a five-minute budget:
#
#     lax CLI (npm)                    4 s
#     elan + leanprover/lean4:v4.30.0  39 s   (2.7 GB)
#     warm mathlib store               177 s  (4.6 GB fetched, 7.5 GB on disk)
#     ---------------------------------------
#     total                            ~3 min 40 s
#
# and again 2026-09-14 for v4.33.0 through `lax doctor`: toolchain 34 s, warm
# store 2 min 27 s. That leaves roughly a minute of headroom. The warm store is
# one `lake exe cache get` download and cannot be split, so if mathlib's CDN
# has a slow day this can overrun five minutes. Overrunning is not fatal — the
# cache simply does not build, and `.claude/dev-setup.sh` from the SessionStart
# hook finishes the job per session instead — but it does mean every session
# pays for it. If that becomes common, the documented escape hatch is to let
# the hook launch the warm build in the background.
#
# Why the CLI is the whole recipe (2026-09-14). An earlier version of this
# script installed the CLI only when none was present and then provisioned the
# toolchain and store itself, reading `pins.LEAN_TOOLCHAIN` and `warmDir()` out
# of the installed package. Both assumptions broke when the archive grew a
# second environment: the pins became per-environment functions, and a
# snapshot taken with CLI 0.1.41 (epoch v4.30.0) kept that CLI forever, so
# after the epoch moved to v4.33.0 every session woke up with the closed
# environment provisioned and the epoch missing. `lax doctor` is the CLI's
# own provisioning chain — each row installs what the next needs, for the
# epoch the installed release recommends — so the script now updates the
# CLI and lets it do the rest. `lax doctor --env <id>` provisions another
# admitted environment the same way, on demand.
#
# Exits zero even when a step fails: a non-zero setup script makes the session
# fail to start outright, and every failure here is one the hook can retry.
set -uo pipefail

export PATH="$HOME/.elan/bin:$PATH"

step() { printf '\n=== cloud-setup: %s\n' "$1" >&2; }
note() { printf '    %s\n' "$1" >&2; }

# --- 1. the lax CLI, at its latest release ---------------------------------
# Always an install: it carries the archive pins every later step reads, and
# the epoch moves with the release (v4.33.0 since 0.1.42). Installing pulls in
# neither elan nor mathlib — the package has no install scripts and seven
# pure-JS dependencies — and a re-install of the same version costs seconds.

step "lax CLI"
if npm install -g lax-archive@latest >&2; then
  note "installed: $(lax --version 2>/dev/null)"
elif command -v lax >/dev/null 2>&1; then
  note "WARNING: npm install failed; keeping the installed $(lax --version)"
else
  note "FAILED: the lax CLI is not installed; nothing else can be provisioned"
  exit 0
fi

# --- 2. elan, the epoch's toolchain, and the epoch's warm mathlib store ------
# `lax doctor` provisions what it finds missing, in order: elan, the
# toolchain (elan installs toolchains lazily, so the 2.7 GB download would
# otherwise land on whoever first types `lean` — inside a session, uncached),
# then ~/.lax/warm/<toolchain>-<mathlibrev> — mathlib at the archive pin,
# fetched with `lake exe cache get`, built once, sealed read-only, and
# replayed in place by every submission build through package overrides. It
# never prompts; it reports, and one row is expected to stay unsatisfied
# here: the GitHub login, which only `lax login`'s browser device flow can
# satisfy and which nothing short of `lax submit` needs.

step "epoch environment (lax doctor)"
lax doctor >&2 || note "WARNING: lax doctor left a problem; the session hook will retry"

step "done"
exit 0
