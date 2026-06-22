# bend2-fuzzer

Differential fuzzer for the [Bend2](https://github.com/HigherOrderCO/Bend2) backends.
It generates random well-typed, terminating Bend programs and checks that the JS and C
backends (plus the interpreter, as a third oracle on linear programs) produce the same
result. A value disagreement or a crash in one backend is a finding; timeouts and
programs that fail `--check` are ignored.

## Usage

Run it **from the root of a Bend2 checkout** (the compiler under test). This repo is
expected to sit one directory up from that checkout:

```
Software/
├── Bend2/          # the checkout under test (has bend/src/CLI.ts, base/)
└── bend2-fuzzer/   # this repo
```

```sh
cd /path/to/Software/Bend2
bun run ../bend2-fuzzer/fuzz.ts [count] [--seed N] [--jobs N] [options]
```

The fuzzer resolves the compiler via `process.cwd()/bend/src/CLI.ts`, so the current
directory must be the Bend2 repo root (it errors clearly otherwise). Common flags:

| flag | meaning |
| --- | --- |
| `[count]` | number of programs to generate (default varies) |
| `--seed N` | base seed (reproducible) |
| `--jobs N` | parallel workers |
| `--no-sanitize` | build the C without ASan+UBSan (instrumentation is **on by default**, ~1.35x) |
| `--no-js` | drop the JS backend; the interpreter becomes the primary oracle (interp-vs-C) |
| `--linear-interp` | restrict the interpreter to linear programs (it runs on **all** programs by default) |
| `--dump` / `--dump-min` | print a single generated program (max / min parens) |
| `--show-rejected` | surface `--check` rejects |
| `--with-metal` | also run `@kernel`-shape programs through `--as-metal` (macOS) |
| `--no-server` / `--no-cbatch` | disable the persistent-server / C-batch fast paths |
| `--profile` | per-phase timing breakdown |
| `--loop` | run continuously |

## Oracles

The **interpreter** is the language spec and the primary oracle; the compiled **C**
backend is under test; the legacy **JS** backend is an optional extra. Any value
disagreement among the available oracles is a finding — which side is wrong is
triaged later from a minimal repro. The interpreter prints sugared values (lists as
`[a, b]`, strings, `'c'`, sized ints with a type suffix) while the compiled backends
print the raw form (`cons{a, nil}`, code points, bare ints), so outputs are
structurally canonicalized before comparison. `--no-js` makes the fuzzer run on the
interpreter and C alone, so removing the JS backend from Bend is a one-flag change.
Beyond value diffing, the C-under-test binary is built with ASan+UBSan by default
(needs no oracle — a sanitizer report is a finding on its own; `--no-sanitize` opts
out), and the metamorphic re-parenthesization leg catches front-end bugs the
cross-backend diff cannot.

## Output

Findings, rejects, and skips are written under `findings/` (gitignored) next to
`fuzz.ts`. Each finding is a standalone `.bend` with a header describing the
divergence; reproduce with `bun bend/src/CLI.ts <file>` and `--as-c` from the Bend2
root.

## Notes

`NOTES.md` holds the design rationale, invariants, performance numbers, and validation
recipes — read it before changing the generator.
