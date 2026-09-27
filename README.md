# bend2-fuzzer

Differential fuzzer for the [bend2-core](https://github.com/HigherOrderCO)
toolchain (`bend2/bend.ts` + `bend2/comp.ts`). Each seed deterministically
generates a well-typed, terminating Bend program in two algebraically-equal
spellings (raw and identity-sealed) and cross-checks every leg:

- **interp** (the spec): `term_snf` on the program's result defs, raw and
  sealed, or on a pure `main`, printed by `term_show`. The raw value is the
  oracle. The interpreter runs base's structural Word code, so this leg is
  also a bit-level spec differential against the native ops the backends
  substitute. A book without Base has this leg only.
- **C** (`compile_book`): one standalone `.c` built with clang at the
  group's drawn `-O` level, run sequentially (`--threads 1 --gpu off`) and
  in parallel at the group's drawn thread count; with `--metal` (macOS) or
  `--cuda` (Linux + NVIDIA) the same `.c` is rebuilt for the device and run
  `--gpu on`.
- **JS** (`js_book`): the emitted `.js` run under bun.

Every checked book also meets the template table's invariants: distinct `~`
argument keys name distinct instances, every instance exists, and a key
carries its literals exactly.

What a seed's program is — Base or an empty initial environment, free
declaration names, whether each member sits inline in the entry or in a file
of its own (relative, `../`, absolute, symlinked or hub paths, one file
reached through two), a foreign effect (`.c`/`.js` building the member's own
constructors through `CID(..)`), a clash mutant that must be refused with a
known message, a pure `main` printed as its literal, the IO tail, the
surface-syntax rate — is drawn from the seed alone, so a finding's repro
line reproduces it. Groups of seeds share one compiled program; the group
size, the C-PAR thread count and the `-O` level are drawn from the group's
first seed.

Programs carry a compiled-only `extra` def (F32 — stuck in the interpreter by
design — deep fork trees with `!` marks, long loops) compared across the
compiled legs with the sequential C run as reference, and an optional
deterministic IO tail in `main` (file roundtrip, `get_env`, `print_err`,
`IO.die` exit codes, and a modeled async walk over fibers, channels and
timers).

Any disagreement, rejection of generated source, internal crash, or compiled
run that outlives its cap while the interpreter finished (livelock suspect)
is a finding. Checker/worker stack, memory and timeout exhaustion is
persisted as a skip; so are the reviewed runtime limits: a `!` reaching
`F32.show`/`F32.read` on a GPU (`metal-host-only`, `cuda-host-only`), a
`Char` that is not a Unicode scalar value on the JS runtime
(`js-char-scalar`), and, when C and JS both stop on it, a Nat past the
runtimes' 48-bit immediate (`nat-immediate`) or memory exhausted
(`resource-fault`).

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
bun ../bend2-fuzzer/fuzz.ts [count | duration] [--seed N] [options]
```

| flag | meaning |
| --- | --- |
| `[count]` | seeds to run (default 100), or a duration: `90m`, `12h` |
| `--seed N` | base seed (reproducible; findings print their exact repro line) |
| `--jobs N` | groups in flight (default: min(8, cpus−2)) |
| `--io-pct N` | percent of seeds carrying an IO tail (default 20) |
| `--metal` | also build with `-DBEND_METAL` and run `--gpu on` (macOS; GPU-serialized) |
| `--cuda` | also build with `-DBEND_CUDA` and run `--gpu on` (Linux + NVIDIA) |
| `--dump` | print the program of `--seed` (both spellings) and exit |
| `--threads N` / `--opt N` | override the drawn C-PAR thread count / clang `-O` level (repro lines use them) |

A first ^C stops launching groups and lets the ones in flight finish; the
run then prints its summary.

## What it generates

Type-directed synthesis over one model of the language. The fuzzer carries
its own redefinition of Base (`BASE_TABLE` in `fuzz.ts`): Base's datatypes
and an explicitly picked set of its defs, written in Base's declaration
syntax. Every datatype there is a type the generator draws, builds by its
constructors and matches (a machine word, an `Array` or `IO` is opaque:
literals and calls only), every def is a call any goal of its return type
may take, and the operators follow the parser's table (a two-argument
method call is spelled infix, framed by its family: `(a + b : U32)` is
`U32.add`). A def marked stuck (F32's native ops) stays off the
interpreter-visible side; effects are not in the table (the IO tail owns
them). The generator does not import bend: only the worker, which runs the
toolchain under test, does.

Types are terms: families by match on an index, indexed datatypes holding
the family at their index, propositions (`Empty`, equalities of literals,
their negations) and dependent pairs, with index-generic builders, readers
and casts. Every def with control flow comes from one production:
parameters drawn as types (the goal generalized over type and quantity
variables at times, a leading function a template at times), a match over
some of them, leaves synthesized against the goal after lets of their own,
a self-call only on a sub-field of the decreasing column; loops, folds,
builders, transforms, tree recursion, generic, higher-order and IO defs are
that one production at different goals. The var quantity system runs end to
end (`-x`/`x`/`+x` sigils, affine consumption, quantity parameters and
meets, the Fill and Plus sugars).

Every size — datatypes, constructors, fields, defs, parameters, statements,
the budget of an expression (split among its parts, so a term grows deep,
wide or both), literal lengths, loop counts — draws from one power-law
distribution: small by preference, with a long tail. Once a budget is spent
a term completes by its cheapest form (the fewest steps to a value of its
type, which also decides whether a type has a value at all).

A result or extra def is a run of statements drawn from three productions:
a value of any type read to a U32, a parallel let, and a proof composed from
reflexivity, Base's lemmas and minted inductive theorems. Declarations,
constructors, fields and binders draw from one identifier distribution
mixing random shapes with words and fragments collected from the whole Bend
implementation and the JS host; binders sometimes shadow a live name.

## The Bend port

`bend/fuzz.bend` is the same fuzzer written in Bend: the generator and the
harness, ported from `fuzz.ts` at the tag `bend2-ts`. It draws the same
kinds of programs from the same Base table and runs the same legs, as
processes: the `bend` CLI interprets a pure `main` listing every member's
raw and sealed results and emits C and JS with `-o`; clang, the compiled
binary and bun run the rest. It does not import bend (so the template
table's invariants, which need the checked book, are not checked). Pure
work runs on one thread per Bend process, so a run is several copies of
the fuzzer, each testing chunks of seeds, merged by the first.

```sh
sh ../bend2-fuzzer/bend/fuzz.sh [count | duration] [--seed N] [options]
```

`fuzz.sh` builds `bend/.build/fuzz` with `bend -o` (95 s) when
`fuzz.bend` is newer than it, then runs it from the bend2-core checkout
(`FZ_ROOT`, by default a sibling of this repo). Options as above, less
`--cuda`, plus `--procs N` (fuzzer processes, default seven tenths of the
runtime's threads) and `--jobs N` (groups in flight per process, default
3). Seeds are 32-bit and a group's seeds are consecutive. Findings land in
`findings-bend/` unless `FZ_FINDINGS` says otherwise. `bend/PORT.md` lists
the limitations of Bend the port met;
`bend/tools/` holds the scripts that generate its records (`st.py`,
`regen.py`), copy the Base table (`table.py`) and mark reusable binders
(`plus.py`).

## Output

Findings land in `findings/` (git-ignored) as standalone `.bend` files with
a verdict header and exact repro line, beside the build that failed
(`seed-N.build/`) and a delta-reduced program (`seed-N.min.bend`, the first
two of each failure class). Resource skips land in `findings/skipped/`.
`FZ_FINDINGS=dir` sends them elsewhere. The run ends with the counts, a
phase profile, the skip reasons and the features never reached (Base's
registry adds one feature per def, `base:<name>`; the rest are read off the
generator's own `feat(..)` calls).

The generator is version-controlled but findings are not: a generator edit
remaps the seeds whose draws pass through the edited site (every statement,
minted def and adt draws from its own split of the seed's stream), and the
saved program is the durable artifact.

## Notes

`BUGS.md` lists every bend2-core bug class the fuzzer has found, open and
fixed, with its repro. `NOTES.md` holds the maintainer notes: invariants,
probed language rules, the currently-open compiler bug classes (expected
finding noise), and the validation recipe. The long doc comment at the top of `fuzz.ts` is the
design spec proper.
