# Porting the fuzzer to Bend

`fuzz.bend` is the port of `fuzz.ts` (tag `bend2-ts`): the generator and the
harness, 12k lines of Bend. `fuzz.sh` builds it with `bend -o` and runs it
from a bend2-core checkout. It does not import bend: every leg is a process
(the `bend` CLI for the interpreter and the emitters, clang, the compiled
binary, bun on the emitted JS). This file keeps the two lists the port
produced: the limitations of Bend it met (and how the code works around
each), and the known bugs of the bend2-core toolchain.

## Limitations met while porting

The language:

1. **A match takes a parameter or a field, and heads a def body.** No
   `match f(x):`, no match inside a `do` block or an expression. Every
   branch on a computed value is a def of its own whose parameter is the
   value (`f.go(U32.is_zero(n), ..)` then `match z:`), or `If` below.
2. **A destructuring let takes a parameter or a field** (not a computed
   value, not a local binder), **never inside a `do` block**, and **a let
   may not precede a match on a parameter**. Records are read through
   accessor defs (`Mb.seed(m)`), and a def that needs the fields of a
   computed record passes it to a helper that destructures its parameter.
3. **Order binds defs**: a def calls only defs above it, and there is no
   mutual recursion, unless the def is `@unsafe` (`def f?(..)`). The
   generator is one mutually recursive system, so every def is `?`.
4. **A datatype must be declared above every def that builds or matches
   its constructors**, `?` defs included; each section's types sit at its
   top.
5. **A closure is affine** (callable once), so there is no `map` or
   `filter` over a closure that captures locals; a template's argument must
   be closed. Every list walk is a recursive def of its own, and a kit of
   productions is a list of steps built fresh per draw.
6. **`Bool.pick`, `&&` and `||` evaluate every argument.** There is no
   short-circuit: a recursion guarded by `&&`/`||` never stops, and a
   `Bool.pick` with a recursive call in each branch is exponential. The port
   defines `If(A, c, u => .., u => ..)`, whose branches are closures, and
   keeps a list walk's recursion out of the pick (`keep_str(ok, x,
   walk(t))`). Seven walks slipped through (`decl_lines` among them); the
   first ones hung a run for minutes before a sample of the process named
   them.
7. **No `if`, no `==`** (equality is `T.is_eq`; Bool has none, so
   `Bool.not(Bool.xor(a, b))`), **no record fields or updates**: a getter
   destructures the whole record and a setter rebuilds it, so the records'
   accessors are generated (`tools/st.py`); the state has 30 fields.
8. **A def with a `+` parameter is not a plain function value**
   (`@+x: A -> B` is not `A -> B`), so it cannot serve as a step of a
   monad: a step's state parameter stays affine and is destructured with a
   `+` on the field it reads.
9. **A binder is affine unless marked**: every reused parameter, pattern
   field, `do` bind and let carries `+` (`tools/plus.py` marks the Data
   ones); channels, which are not Data, are marked by hand.
10. **A pair `A & B` is Kind(&1)**, so a pair is affine even of Data parts
    and cannot be read twice (`Pair.fst` then `Pair.snd`); `List<&2, String
    & String>` does not kind-check. Results with tallies are records
    (`LMS{ss, st}`), and the operator table is two parallel lists.
11. **A constructor or list literal in a let needs an annotation**
    (`{K{..} : T}`, `+x : List<&2, String> = [..]`), and every `do` bind a
    type.
12. **`case [] []:` does not parse** (it reads as an index): a
    multi-column list match spells `Nil{}` and `Con{h, t}`.
13. **A keyword cannot name a binder** (`def`, `type`, `law`, `exs`, ...).
14. **Operators need a frame, and `&` in a frame is the pair type**:
    `(a + 1n : Nat)`, and a bitwise and is `(a .&. b : U32)`.
15. **Quantities do not convert**: `IO.args()` answers `List<String>` (a
    `&1` list) and `Process.run` takes one, while the port's lists are
    `&2`; two walks copy between them.
16. **A string literal of the Base table's size (22 KB) overflows the
    compiler's stack** at `-o` ("the machine stack overflowed"): a string
    literal expands to one nested chain. The table is a list of line
    literals.
17. **A program's own name may not repeat Base's** (`Cmp`,
    `Result.is_done`): one file importing Base shares its namespace.

The runtime and its IO:

18. **Strings are lists of characters.** Building program text with `++`
    is linear per append, a map keyed by a string walks its bits, and the
    reference counting of those lists (`term_drop`) leads every profile.
    Generation costs about 50 ms a member against 2 ms in TypeScript; the
    worst seed (a 3.7 KB program) took 30 s while the cost memo keyed types
    by their rendering, 8.6 s with a structural hash as the key.
19. **Pure work runs on the IO thread.** Fibers overlap their IO waits,
    but not their pure work, and a fiber's pure work is not preempted:
    eight fibers in one process kept about two cores busy. The harness runs
    child copies of itself (`FZ_BIN`), each on a chunk of 12 seeds with 3
    fibers, and merges their tallies.
20. **`Process.run` collects a child's output until it exits** and takes
    no working directory or environment: a chunk's findings print when the
    chunk ends; the legs run as `sh -c 'cd DIR && exec ..'` and the CLI as
    `env BEND_LIB=.. bun ..`.
21. **The IO library has files but no directories**: `mkdir`, `rm -rf`,
    `ln -s`, `test -e`, `mktemp` and `date` run as processes.
22. **A compiled program takes `--threads N` from its arguments**: the
    fuzzer's own options follow `--`.
23. **No clock finer than a millisecond `Nat`, no environment listing, no
    process id**: the scratch directory comes from `mktemp`, the default
    seed from the clock.
24. **Building takes 95 s** (`bend -o`, 12k lines): the wrapper rebuilds
    only when `fuzz.bend` is newer than the binary.

What the CLI cannot give a harness that does not import bend:

25. **Check errors and evaluation errors share one channel** (stderr, exit
    1). The harness reads a refusal as an error with no check report
    before it, and strips the report (`All terms check, but ..` and its
    `- name` lines) from what it shows.
26. **The template table's invariants** (distinct keys name distinct
    instances, every instance exists, a key holds its literals exactly)
    need the checked book, so the port does not check them.
27. **Each leg pays a process**: the TS worker checks Base once per
    process and answers a request in about 50 ms; `bun bend2/main.ts`
    re-reads Base per run (about 0.3 s of CPU under load). The interpreter
    leg runs once per group (a pure `main` listing every member's raw and
    sealed values), and the members run alone only when it fails.

Throughput: 1,000 seeds from `--seed 7000` on a 10-core Mac (4 performance and 6 efficiency cores), against the
same bend2-core commit: the TypeScript fuzzer 9.2 seeds/s (108.7 s), the
Bend port 9.3 seeds/s (106.4 s, 7 processes of 3 fibers).
Validation from `--seed 20000`: 2,993 of 3,000 ok at 9.0 seeds/s, 3
`js-char-scalar` skips, and 4 findings: 2 of F4 below, 2 of a generator bug
the port shared with `fuzz.ts` (an indexed datatype drawn as an index type),
since fixed.

## Known bugs of bend2-core

Open, with the fuzzer's finding kind; repros under `../repros/` unless
noted.

1. **An open Array element type** (`compiler-crash`): an Array whose
   element type is an equality, or reaches the emitters open (Base's Array
   helpers called at a type variable), kills both emitters with "an open
   Array element type"; the checker and the interpreter accept it
   (`comp_array_of_equality.bend`). The port's first 1,000 seeds found it
   again (seed 7141).
2. **An Object.prototype name reads as an import alias** (`raw-reject`,
   new): a declared name whose first segment is a property of JavaScript's
   `Object.prototype` (`__defineSetter__`, `constructor`, `toString`, ...)
   is refused with "a fresh name (__defineSetter__ is an import's alias)"
   in a program with no import: the aliases live in a plain object. Found
   by the TypeScript fuzzer on `af569d48`, seed 15733518094780353156:
   `type __defineSetter__._ZrMc is Data: ..`.
3. **F1 `Bool.or`/`||` and `Bool.xor` in C** (`leg-diverge`): the C
   emitter reads a boxed Bool Term as a native 0/1 (the `bool_` intrinsic
   template) (`comp_bool_or_boxed_operand.bend`, `..._scrutinee.bend`,
   `comp_bool_xor_boxed_operand.bend`).
4. **F2 a namespace equal to a Base prefix captures names**
   (`raw-reject`): a file named `Word.bend` resolves bare names into Base's
   (`Nil` becomes `Word.Nil`) (`ns_base_prefix_capture/`).
5. **F4 an alias equal to the file's own namespace is ambiguous**
   (`raw-reject`): `import ./m.bend as m` then `m.f()`
   (`alias_is_own_namespace/`).
6. **F5 a nested match with a later list-literal row** (`raw-reject`):
   refused as "an undestructed scrutinee"
   (`check_nested_match_later_literal.bend`).
7. **F6 `Array.set(..);` swallows the next row** (`raw-reject`): it
   parses as the write statement `a = a[i] <- v; ..`, eating an inline
   match's next row (`parse_array_set_swallows_row.bend`).
8. **family-arm-layout** (`compiler-crash`): a family whose arms have
   different runtime layouts, read per arm after a match on the index,
   dies in the C emitter with "a layout mismatch" or "a constructor outside
   its layout" (`comp_family_arm_layout_sig.bend` and three more).
9. **K1 `F32.show` tie rounding** (`leg-diverge`): C prints `417.70312`,
   JS `417.70313`.
10. **K a list literal of hundreds of calls** is slow to emit (15.7 s of
    user time for the repro).
11. **The compiler's stack overflows on a large string literal** (found by
    the port): `-o` on a 22 KB literal fails with "the machine stack
    overflowed (a deep recursion, or a literal too large to expand)".
12. **`Nat.read` never finishes in the interpreter**: its overflow guard
    divides with Base's unary `Nat.divmod`, an accumulator loop, so no
    digit is observable before 2^48 steps; the registry keeps it off the
    interpreter's side.
13. **F3 Apple clang 17 at `-O0`** (`cc-fail`, not Bend's): "live register
    clobbered by inserted prologue instructions"; the legs pass
    `-fno-stack-check`.

Reviewed limits, counted as skips: `js-char-scalar` (a Char past U+10FFFF
or a surrogate stops the JS runtime), `nat-immediate` (a Nat past 2^48-1
stops both runtimes), `resource-fault` (memory exhausted on every leg),
`metal-host-only` (a `!` reaching `F32.show` or `F32.read` on the GPU).
