# bend2-fuzzer

Differential fuzzer for the [Bend3](https://github.com/HigherOrderCO) runtimes
(the repo name predates Bend3; the fuzzer targets the `bend3` checkout). Each
seed deterministically generates a well-typed, terminating Bend program with a
U32 `main` in two algebraically-equal spellings (raw and identity-sealed) and
runs them across every leg: the TS interpreter (the language spec, evaluated
on the checked book — the CLI's own path), the compiled C backend
(`-DPAR_BACKEND=0`), optionally Metal (`--metal`), and a min-parens
metamorphic re-emission (the parser oracle). Any disagreement, rejection of
generated source, or internal crash is a finding; resource blowups (timeouts,
stack overflows) are persisted but not failures.

## Usage

Run it with **bun** either from the root of a bend3 checkout, or from anywhere
if this repo sits next to a checkout named `bend3`:

```
Software/
├── bend3/          # the checkout under test (bend-ts/src/bend.ts, bend-base/)
└── bend2-fuzzer/   # this repo
```

```sh
cd /path/to/Software/bend3
bun ../bend2-fuzzer/fuzz.ts [count] [--seed N] [--jobs N] [options]
```

Common flags:

| flag | meaning |
| --- | --- |
| `[count]` | number of programs to generate (default 100) |
| `--seed N` | base seed (reproducible; findings print their exact repro line) |
| `--jobs N` | parallel batches (default: cores − 2, max 8) |
| `--batch N` | seeds merged per compiled binary (default 16; `1` disables) |
| `--threads N` | `-DNUM_THREADS` for the C leg (default 1) |
| `--opt N` | `-O` level for clang (default 3) |
| `--metal` | also build and run each binary's Metal leg (macOS, GPU-serialized) |
| `--io` | the IO smoke mode: effectful programs checked by exact process output |
| `--smoke` | fixed seed set that must cover a feature checklist and pass |
| `--check-only` | stop after the checker legs (no clang) |
| `--no-meta` | drop the min-parens metamorphic leg |
| `--dump` / `--dump-min` / `--dump-raw` | print one generated program and exit |
| `--keep` | keep temp build dirs |
| `--loop` | run continuously |
| `--profile` | per-phase timing breakdown |

## Oracles

The interpreter runs the **checked** book (`parse_book` → `book_check`, which
elaborates in place → `term_snf`), exactly what `bun bend-ts/src/bend.ts file.bend
--eval` does. The raw sibling's value is the reference; the sealed sibling
must equal it on the interpreter and on every compiled leg, so a broken seal
cannot bless itself. The metamorphic leg re-emits the same seed with minimal
parentheses (same RNG draws, only string assembly differs) and re-runs it on
the interpreter — the only leg that can see front-end bugs, since all backends
share one front end. In `--io` mode the interpreter performs no effects, so
programs are checked by their exact stdout/exit code instead, plus an orphan
sweep for processes that outlive the binary.

## Output

Findings land in `findings/` (gitignored) next to `fuzz.ts` as standalone
`.bend` files with a verdict header and exact repro line; resource skips go to
`findings/skipped/`. The generator is version-controlled but findings are not:
a generator edit remaps every seed, so the saved program is the durable
artifact.

## Notes

`NOTES.md` holds the maintainer notes: invariants, the batching design,
validation recipes, and what the fuzzer cannot see. Read it before changing
the generator. The long doc comment at the top of `fuzz.ts` is the design
spec proper.
