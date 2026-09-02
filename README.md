# bend2-fuzzer

Differential fuzzer for the [bend2-core](https://github.com/HigherOrderCO)
toolchain (`bend2/bend.ts` + `bend2/comp.ts`). Each seed deterministically
generates a well-typed, terminating Bend program in two algebraically-equal
spellings (raw and identity-sealed) and cross-checks every leg:

- **interp** (the spec): `term_snf` on the pure `result` def, raw and
  sealed — both spellings sit in one book, evaluated in parallel — the
  trusted-kernel path. The raw value is the oracle. The interpreter runs base's structural
  Word code, so this leg is also a bit-level spec differential against the
  native ops the backends substitute.
- **C** (`compile_book`): one standalone `.c` built with clang, run
  sequentially (`--parallel off`); optional lanes on top: CPU parallelism
  (`--threads N`), Metal (`--metal`, macOS) and CUDA (`--cuda`, Linux +
  NVIDIA), both run `--gpu on`.
- **JS** (`js_book`): the emitted `.js` run under bun.

Programs carry a compiled-only `extra` def (F32 — stuck in the interpreter
by design — deep fork trees with `!` marks, long loops) compared across the
compiled legs with the sequential C run as reference, and an optional
deterministic IO tail in `main` (file roundtrip, `get_env`, `print_err`,
`IO.die` exit codes) compared by exact stdout/stderr/exit.

Any disagreement, rejection of generated source, internal crash, or C run
that outlives its cap while the interpreter finished (livelock suspect) is a
finding; resource blowups (timeouts, stack overflows) are persisted skips.

## Usage

Run with **bun** either from the bend2-core repo root, or from anywhere if
this repo sits next to a checkout named `bend2-core` (or `bend2`):

```
Software/
├── bend2-core/     # the checkout under test (bend2/bend.ts, bend2/comp.ts)
└── bend2-fuzzer/   # this repo
```

```sh
cd /path/to/Software/bend2-core
bun ../bend2-fuzzer/fuzz.ts [count] [--seed N] [options]
```

| flag | meaning |
| --- | --- |
| `[count]` | seeds to run (default 100) |
| `--seed N` | base seed (reproducible; findings print their exact repro line) |
| `--jobs N` | batches in flight (default: min(8, cpus−2)) |
| `--batch N` | seeds merged per compiled program (default 8; `1` disables) |
| `--threads N` | also run each C binary with `--threads N --gpu off` and compare (default 0 = off) |
| `--metal` | also build with `-DBEND_METAL` and run `--gpu on` (macOS; GPU-serialized) |
| `--cuda` | also build with `-DBEND_CUDA` and run `--gpu on` (Linux + NVIDIA) |
| `--opt N` | clang `-O` level for the C legs (default 1) |
| `--io-pct N` | percent of seeds carrying an IO tail (default 20) |
| `--check-only` | stop after check + interp + emission (no cc, no runs) |
| `--smoke` | fixed seed set that must cover a feature checklist and pass |
| `--loop` | run continuously |
| `--dump` / `--dump-raw` | print one generated program and exit |
| `--reduce N` | delta-reduce seed N's failing program to `findings/seed-N.min.bend` |
| `--keep` / `--profile` | keep temp dirs / per-phase timing report |

## What it generates

Goal-directed synthesis over the current type system, quantity-aware end to
end: `-x`/`x`/`+x` binder sigils with affine consumption, quantity
polymorphism (`def f(a, -A: Kind(a), ...)` instantiated at `&1`, `&2` and
bound quantity variables), data-kinded datatypes (`is Data` / `is Type` /
`is Kind(a)` / `is Kind(a <&> b)`), the Fill (`D<..>`) and Plus (`+D<..>`)
sugars, erased params and fields. Every primitive with special compilation
is reachable: the full U32/F32/Nat op rosters, Bool/Cmp tables, Nat constant
tables, `String.append`/`cmp`, Char packing, string/list literals, U32/Nat
show+read roundtrips, `Array` new/get/set/swap/size/clone plus the `a[i]`
sugar, Map/Set, fork trees with `!` GPU marks, closures and live-1 partial
application, do-notation (Maybe/Result/IO), equalities, rewrites, minted
theorems, dependent families (large elimination and the Word idiom). Tail
loops descend on any chain-shaped data (at most one self field per
constructor): the program's own such ADTs, base's List at any element
type (the generic ADT path where Nat takes the native), a String, or a
Nat; the fuel value is synthesized like any other, so loops run over data
the program already builds.

## Batching

`--batch N` merges N seeds into ONE compiled program (a concatenation at
disjoint uid ranges) whose main prints each member's lines in order — clang
and process spawn are paid once per batch, attribution stays per line, and
the interp legs (the bottleneck) run per member across the worker pool. A
failing batch re-runs members solo at uid base 0, so saved findings
reproduce under a bare `--seed N`; a batch failing with no failing member is
itself a finding (`batch-only`). A member whose IO tail ends in `IO.die`
would end the whole process, so the batch's `main` dispatches on the
`FZ_MEMBER` environment variable: unset runs the non-dying members, `i`
runs member i's block and dies — one binary, compiled once, run once
plainly and once per dying member, every leg alike.

## Output

Findings land in `findings/` (git-ignored) as standalone `.bend` files with
a verdict header and exact repro line; resource skips in `findings/skipped/`.
The generator is version-controlled but findings are not: a generator edit
remaps the seeds whose draws pass through the edited site (every statement,
minted def and adt draws from its own split of the seed's stream, so the
blast radius is that site's subtree, not the whole program), and the saved
program is the durable artifact. `--reduce N` shrinks a failing seed's
program while its failure holds — drop statements, the extra def, the IO
tail, then unreferenced entries — and saves the result beside the finding.
Curated repros of open compiler bugs live in `repros/`.

## Notes

`NOTES.md` holds the maintainer notes: invariants, probed language rules,
the currently-open compiler bug classes (expected finding noise), and the
validation recipe. The long doc comment at the top of `fuzz.ts` is the
design spec proper.
