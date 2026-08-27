#!/bin/bash
cd /home/user/lax-submissions/.claude/worktrees/w63/nowhere-dense-model-checking/proofs
timeout 1800 env PATH="$HOME/.elan/bin:$PATH" lake build Lax3Proofs.SolveSweepAug 2>&1 \
  | grep -E '^(error|warning): Lax3Proofs/SolveSweepAug|^error: build|declaration uses' | head -${1:-40}
echo "== build done =="
