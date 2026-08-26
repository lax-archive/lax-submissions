#!/usr/bin/env bash
set -euo pipefail

repo=${LAX_CONTAINER_REPO:-/workspace/lax-submissions}
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
export LAKE_ARTIFACT_CACHE=false

if [ "${LAX_CONTAINER_SKIP_SETUP:-0}" != 1 ]; then
  "$repo/.claude/dev-setup.sh"
fi

if [ "$#" -eq 0 ]; then
  set -- codex
fi

exec "$@"
