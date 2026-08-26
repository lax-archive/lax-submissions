#!/usr/bin/env bash
# Build and enter the isolated proof-development container.
#
#   .claude/docker-dev.sh                 # Codex (the default)
#   .claude/docker-dev.sh claude          # Claude Code
#   .claude/docker-dev.sh bash            # an ordinary shell
#   .claude/docker-dev.sh --rebuild       # refresh the image and all three CLIs
#
# The checkout is bind-mounted read/write. The container has a separate,
# persistent home volume, so its Codex/Claude credentials and Lean/Lax caches
# survive while no host credentials are shared.
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: .claude/docker-dev.sh [OPTIONS] [COMMAND [ARG...]]

Start an interactive proof-development container with this checkout mounted
read/write. COMMAND defaults to `codex`; use `claude` or `bash` when wanted.

Options:
  --rebuild       Pull the base image and reinstall the latest CLI packages.
  --skip-setup    Do not run the repository's Lean/Lax setup on this launch.
  -h, --help      Show this help.

The container uses its own persistent Docker home volume. It does not mount
~/.codex, ~/.claude, ~/.config, or any other host credentials.
EOF
}

rebuild=0
skip_setup=${LAX_DOCKER_SKIP_SETUP:-0}
while [ "$#" -gt 0 ]; do
  case "$1" in
    --rebuild)
      rebuild=1
      shift
      ;;
    --skip-setup)
      skip_setup=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      break
      ;;
    *)
      break
      ;;
  esac
done

if ! command -v docker >/dev/null 2>&1; then
  echo "docker-dev: Docker is not installed" >&2
  exit 1
fi
if ! docker info >/dev/null 2>&1; then
  echo "docker-dev: cannot reach the Docker daemon" >&2
  exit 1
fi

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)
git_common_dir=$(git -C "$repo_root" rev-parse --path-format=absolute --git-common-dir)
docker_dir="$script_dir/docker"
host_uid=$(id -u)
host_gid=$(id -g)

if [ "$host_uid" -eq 0 ] || [ "$host_gid" -eq 0 ]; then
  echo "docker-dev: run this launcher as a non-root host user" >&2
  exit 1
fi

image="lax-submissions-proof-dev:${host_uid}-${host_gid}"
home_volume="lax-submissions-proof-home-${host_uid}-${host_gid}"

build_args=(
  --file "$docker_dir/Dockerfile"
  --build-arg "USER_UID=$host_uid"
  --build-arg "USER_GID=$host_gid"
  --tag "$image"
)
if [ "$rebuild" -eq 1 ]; then
  build_args+=(--pull --no-cache)
fi

docker build "${build_args[@]}" "$docker_dir"

if ! docker volume inspect "$home_volume" >/dev/null 2>&1; then
  printf '%s\n' \
    "docker-dev: first launch will provision Lean and the warm mathlib store" \
    "docker-dev: expect about 10 GB in volume $home_volume"
fi

tty_args=()
if [ -t 0 ] && [ -t 1 ]; then
  tty_args=(--interactive --tty)
fi

mount_args=(
  --mount "type=bind,source=$repo_root,target=$repo_root"
  --mount "type=volume,source=$home_volume,target=/home/dev"
)
# A linked worktree's .git file points into the main checkout. Mount that
# narrow metadata directory too, at the same absolute path, so Git works from
# either the main checkout or a project worktree.
case "$git_common_dir/" in
  "$repo_root/"*) ;;
  *) mount_args+=(--mount "type=bind,source=$git_common_dir,target=$git_common_dir") ;;
esac

env_args=(
  --env "LAX_CONTAINER_REPO=$repo_root"
  --env "LAX_CONTAINER_SKIP_SETUP=$skip_setup"
  --env "TERM=${TERM:-xterm-256color}"
)
for variable in LAX_SEED_CAPTURES LAX_SETUP_BUILD; do
  if [ -n "${!variable:-}" ]; then
    env_args+=(--env "$variable=${!variable}")
  fi
done

if [ "$#" -eq 0 ]; then
  set -- codex
fi

exec docker run --rm --init \
  "${tty_args[@]}" \
  "${mount_args[@]}" \
  "${env_args[@]}" \
  --hostname lax-proofs \
  --workdir "$repo_root" \
  "$image" "$@"
