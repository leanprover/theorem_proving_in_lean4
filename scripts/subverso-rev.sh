#!/usr/bin/env bash

# Keeps the SubVerso revision in examples/lake-manifest.json equal to the book's.
#
# The book gets SubVerso through Verso, which pins it; the examples project requires it
# directly. `subverso-extract-mod` runs in examples/ and writes the JSON that the book reads
# back, so the two must be built against the same revision for the serialization to line up.
#
#   subverso-rev.sh          copy the book's revision into examples/
#   subverso-rev.sh --check  report a mismatch without writing

set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
book="$repo/book/lake-manifest.json"
examples="$repo/examples/lake-manifest.json"

rev_of() {
  local rev
  rev="$(jq -r 'first(.packages[] | select(.name == "subverso") | .rev) // empty' "$1")"
  if [[ -z "$rev" ]]; then
    echo "error: no SubVerso revision in $1" >&2
    return 1
  fi
  printf '%s' "$rev"
}

book_rev="$(rev_of "$book")"
examples_rev="$(rev_of "$examples")"

if [[ "$book_rev" == "$examples_rev" ]]; then
  echo "SubVerso revisions agree: $book_rev"
  exit 0
fi

if [[ "${1-}" == "--check" ]]; then
  cat >&2 <<EOF
error: SubVerso revision mismatch
  book/lake-manifest.json:     $book_rev
  examples/lake-manifest.json: $examples_rev

Run scripts/subverso-rev.sh to copy the book's revision over, then rebuild.
EOF
  exit 1
fi

tmp="$(mktemp)"
jq --indent 1 --arg rev "$book_rev" \
  '(.packages[] | select(.name == "subverso") | .rev) |= $rev' \
  "$examples" > "$tmp"
mv "$tmp" "$examples"
echo "updated examples/lake-manifest.json: $examples_rev -> $book_rev"
