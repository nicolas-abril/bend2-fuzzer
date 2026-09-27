#!/bin/sh
# try.sh MAINFILE [args] : fuzz.bend with a test main appended (the
# fuzzer's own main renamed), built and run from the bend2-core checkout
here=$(cd "$(dirname "$0")/.." && pwd)
root=${FZ_ROOT:-$(cd "$here/../../bend2-core" 2>/dev/null && pwd)}
tmp=${TMPDIR:-/tmp}/fzb-try
mkdir -p "$tmp"
sed 's/^def main?() -> IO(Unit):/def main.fuzz?() -> IO(Unit):/' "$here/fuzz.bend" > "$tmp/try.bend"
cat "$1" >> "$tmp/try.bend"
shift
cd "$root" && bun bend2/main.ts "$tmp/try.bend" -o "$tmp/try" 2>&1 | grep -Ev "^- [A-Za-z_.0-9]*$|^All terms check"
"$tmp/try" -- "$@"
