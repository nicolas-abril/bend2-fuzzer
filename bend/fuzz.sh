#!/bin/sh
# fuzz.sh [count] [options] : builds the Bend fuzzer when fuzz.bend is newer
# than its binary, then runs it from the bend2-core checkout (FZ_ROOT, by
# default a sibling of this repo). Findings land in the repo's findings/
# unless FZ_FINDINGS says otherwise.
here=$(cd "$(dirname "$0")" && pwd)
root=${FZ_ROOT:-$(cd "$here/../../bend2-core" 2>/dev/null && pwd)}
if [ -z "$root" ] || [ ! -f "$root/bend2/main.ts" ]; then
  echo "cannot find the bend2-core checkout: set FZ_ROOT" >&2
  exit 1
fi
bin=$here/.build/fuzz
if [ ! -x "$bin" ] || [ "$here/fuzz.bend" -nt "$bin" ]; then
  mkdir -p "$here/.build"
  echo "building $bin ..." >&2
  (cd "$root" && bun bend2/main.ts "$here/fuzz.bend" -o "$bin" 2>&1 | grep -Ev '^- [A-Za-z_.0-9]*$|^All terms check' >&2)
  [ -x "$bin" ] && [ "$bin" -nt "$here/fuzz.bend" ] || { echo "build failed" >&2; exit 1; }
fi
cd "$root" && FZ_ROOT="$root" FZ_FINDINGS="${FZ_FINDINGS:-$here/../findings-bend}" FZ_SRC="$here/fuzz.bend" FZ_BIN="$bin" exec "$bin" -- "$@"
