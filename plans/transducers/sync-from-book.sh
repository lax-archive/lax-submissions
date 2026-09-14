#!/usr/bin/env bash
# Export the book's `port-v4.33` branch into this checkout: the eight
# submission folders at the root, the book's lax/ bookkeeping under
# plans/transducers/book-lax/, and the commits as a patch series against the
# book's main. Exports the committed state (HEAD of the branch), never the
# working tree. Usage: plans/transducers/sync-from-book.sh [book-checkout]
set -euo pipefail
book=${1:-/home/user/transducer-book}
branch=port-v4.33
base=$(git -C "$book" merge-base main "$branch")
top=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
here=$top/plans/transducers
subs="pcp-undecidability mealy-machines rational-functions regular-functions mso-transductions regular-combinators polyregular-functions transducers-book"

tmp=$(mktemp -d)
git -C "$book" archive "$branch" lax | tar -x -C "$tmp"
for s in $subs; do
  rm -rf "$top/$s"
  mv "$tmp/lax/$s" "$top/$s"
done
rm -rf "$here/book-lax" "$here/patches"
mkdir -p "$here/book-lax"
mv "$tmp"/lax/* "$here/book-lax/"
rm -rf "$tmp"
git -C "$book" format-patch --quiet -o "$here/patches" "$base..$branch"
echo "exported $(git -C "$book" rev-parse --short "$branch") ($(ls "$here/patches" | wc -l) patches over $(git -C "$book" rev-parse --short "$base"))"
