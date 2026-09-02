# Fuzzer maintainer notes (`fuzz.ts`)

The long doc comment at the top of `fuzz.ts` is the design spec — what is
generated, which legs run, and why each invariant exists. This file holds
what does NOT belong in the spec: history, probed language rules, the
current known-noise sources, and the validation recipe. Read both before
restructuring anything.

## History

The fuzzer began life as a Bend2 backend fuzzer, was rewritten for the
"bend3" line (goal-directed synthesis, `bend-ts/src/`, paren type
application, `::` modules), and on 2026-09-01 was rewritten from scratch
for **bend2-core** — the affine core with the var quantity system. Nothing
of the bend3 surface survived: that language had `if`/`elif`, computed
match scrutinees, `-->`/`-~>` arrows, `~x` Comp params, paren type
application, module namespaces, an Op-based IO scheduler with
fork/race/timeout/channels, and a min-parens metamorphic leg. All gone.
What carried over is the architecture: seed-deterministic generation, the
raw/sealed sibling differential, a JSON-line worker pool, batching at
disjoint uid ranges with solo attribution, findings as standalone files.

New in this rewrite, in step with the toolchain:

- **The JS leg**: `js_book` is a first-class backend now and runs on every
  seed. It is also the reference-adjacent leg for shapes the C emitter
  refuses by design (structural word views).
- **The `result`/`extra` split**: base's F32 ops are bodiless native
  claims, STUCK in the interpreter, and the interpreter runs base's unary
  Nat / Word-chain code ~1000x slower than natives — so the interp-visible
  `result` fold is small and F32-free, and the heavy shapes (F32, deep
  `!`-marked fork trees, 200k-iteration loops) live in a compiled-only
  `extra` def, compared across compiled legs with C-seq as reference.
- **IO is a tail, not a mode**: the old cancellation kit died with the
  bend3 scheduler. Today's effects (File, get_env, print/print_err/write,
  IO.die) are deterministic, so a probabilistic IO tail rides main's
  do-block on ordinary seeds and compares by exact stdout/stderr/exit.
  TCP/UDP are not generated (ports/routing are not deterministic).
- **The GPU lanes**: `--metal` / `--cuda` build the SAME emitted `.c` with
  the platform flags and run `--gpu on`; `--threads N` adds the CPU-par
  lane on the sequential binary. GPU runs are serialized; a GPU binary
  re-reads its `.c` at the compiled path, so build dirs live until the run
  ends.

Restructured on 2026-09-02:

- **Ctx**: the generator's state is one `State` (entries, adts, registry,
  memo, uid counter) carried by a `Ctx` with its own RNG stream; no module
  globals. `c.sub(label)` is a child Ctx on a split stream.
- **Split RNG**: `Gen.split(label, i)` derives from the stream's ROOT, not
  its position. Every adt, statement, minted def, the fold, the seal and
  the IO tail draw from their own split, so an edit to one site remaps the
  seeds that reach it and leaves the rest alone.
- **One book per member**: the raw and sealed spellings live in one book
  (parsed straight from the string, no temp file), each def evaluated by
  its own parallel worker request. Measured: parse ~1ms, check ~4ms,
  evaluation hundreds of ms and up — evaluation is the whole cost, so the
  two requests stay parallel. A reject is attributed by re-checking the
  raw spelling alone.
- **`--reduce N`**: greedy delta reduction of a failing seed (statements,
  extra, IO tail, entries) under the same failure signature; result in
  `findings/seed-N.min.bend`.
- **Dying members batch**: a member ending in `IO.die` used to be diverted
  to a solo compile. Now `main` reads `FZ_MEMBER` (unset: the non-dying
  members via `fzall`; "i": member i's own block `fzm<i>`, selected by a
  `String.eq` chain) and the harness runs the batch binary once per
  RunSpec — the plain run plus one per dying member — on every leg, each
  against its own expectation. Attribution of a failing die run is
  direct: the member is named by its run.

## Probed language rules (violate = reject noise)

Each of these was probed against HEAD during the rewrite; the generator is
built around them:

- A match scrutinizes a def parameter or a bound field, NOTHING else — no
  `if`, no computed or let-bound scrutinees, no match in a let value, no
  applied lambda-match. Destructuring lets (`(a, b) = p`, `K{x} = v`) are
  matches, so params/fields only. Every computed branch/destructure goes
  through a minted continuation def (base.bend's own `.if`/`.fin`/`.go`
  architecture). Nested matches must follow binder order.
- Patterns name ALL fields, erased ones included; `0n`/`1n+p`/`3n+p` are
  ctor sugar and fine. U32/F32/Word literal or structural patterns —
  including string and char LITERAL patterns, which desugar to
  `Chr{U32{Word..}}` chains — die in the C emitter ("a structural view of
  a machine word") while the JS emitter accepts them; that asymmetry is by
  design and not a finding, so the generator never emits them.
- Defs are emitted in creation = dependency order; no forward refs. An
  assert registers a family name before the ctor types that mention it
  (base's own Word ordering).
- Lone binders are consumed at most once (dropping is fine — affine); `+`
  forms only at concretely-Data types; a `+` scrutinee makes its pattern
  binders Many; a plain-arrow lambda binder is Lone whatever its type's
  kind. Parallel-let binders take NO sigil (always Lone), so fork results
  are fold-only, and their rider values must be bare var atoms (a
  parenthesized rider would glue onto the preceding call as a spaced
  suffix; a literal rider cannot infer).
- A bare literal (U32/F32/Nat/ctor/tuple/list) in a LET VALUE cannot
  infer: `x = {v : T}`. Do-binds are annotated (`x : T <- act`).
  Negative float literals do not exist (`-3.5` heads a binder): spell
  `F32.neg(3.5)`.
- Recursion descends structurally on the FIRST live column (erased
  columns skipped) — any recursive data serves as the fuel: tail loops
  draw a Nat, a List, a String or a minted Peano clone; `@unsafe` opts
  out and is emitted rarely. Partial applications stop at exactly live-1
  arguments.
- Plus sugar (`+D<..>`) is lawful only right after `:` (annotation sites);
  after `(` or `&` it parses as a binder. `ty_str` is the safe rendering,
  `ty_top` the annotation-site one. Fun components of `A & B` need parens
  (`&` binds tighter than `->`).
- Axioms are banned outside base ("a final unfilled assert is an error"),
  so the assert/def split is always filled.
- `<<`/`>>` take a Nat count; there is no U32 `<`, `==` or `!=` infix
  (calls through a Bool reader); `<>` is List-only cons (String uses
  `SCon`/`++`).
- `qt_fits` mirrors term_compare's Typ case: Data fits every kind, every
  kind fits Kind(&0) and Kind(&1), a left meet needs both sides, a right
  meet accepts either side, a stuck target licenses only an identical
  term. Ctor field kinds must fit the declared G.

## Known noise and open compiler bugs (2026-09-01)

Remove entries here when the bends are fixed — every live finding class
drowns real signal. Delta-reduced repros for all of these sit in
`repros/`.

- ~~`compiler-crash` rwt-binder-loss~~: FIXED (2026-09-01) — carbonize
  now drops a rewrite in place (evidence and motive erased, body
  carbonized) and an unused live let drops with it; regression-covered
  by bend2-core's `reg_rwt_carb_binders.bend`. The ford kit's cast coin
  (`ford-cast`) stays as coverage of both spellings.
- ~~`leg-timeout`/`leg-diverge` bang-alien~~: FIXED (2026-09-01) — the
  fuse "pure" walk now refuses fuse_ban calls like fuse_deep does, so a
  callee holding a `!`-marked cut is never inlined into a fused
  continuation; regression-covered by `reg_fuse_bang_cut.bend`. Both
  fixes verified to leave every runtime bench's emitted C byte-identical.
- **erased-arrow application** (OPEN, pre-existing, unmasked by the rwt
  fix — ~1% of seeds): an erased-domain function value
  (`@-zq: A -> B`) drops its lambda when compiled, but a dynamic
  application can keep the erased argument when the function's Ann is
  lost in the inliner readback. Loud flavor: "a Ctr-headed spine in an
  expression" everywhere; silent flavor: C prints a WRONG VALUE and JS
  throws TypeError (a payload applied as a function); it can also hang
  the C binary (fires as `leg-timeout`). Repros:
  `comp_erased_arrow_apply.bend`, `comp_erased_arrow_value.bend`,
  `comp_erased_arrow_hang.bend`.
- ~~C livelock: packed ctor over a Char field~~: FIXED (2026-09-01) —
  a packed Char field ORed its tag/aux bits into the outer word, so
  the ctor masqueraded as cid|CID_CHR: misdispatched matches freed
  header memory and heap_alloc spun forever. ctr_wrap now strips the
  field to its code at build and re-wraps it at the arm;
  regression-covered by `reg_ctr_packed_char.bend`. Of the two finder
  seeds, 8559387686525276681 turned out to be the erased-arrow class
  below (which also fires as a C hang), not this one.
- `trans-ulp` skips: float transcendentals are each backend's libm-family
  routines; a `trans`-flagged member keeps every leg except the JS-vs-C
  (and GPU) comparison of its extra line, which downgrades to a counted
  skip on mismatch. In practice bun's Math agrees bit-exactly with macOS
  libm floats on everything probed, so these are rare.

## What it cannot find (by design)

- Common-mode front-end bugs: all legs share one parser/checker, and the
  old min-parens metamorphic leg died with the grammar that motivated it
  (op2 no longer associates; there is no paren freedom left worth
  varying). The raw/sealed differential still catches evaluator-vs-
  backend disagreements.
- Checker divergence: WONTFIX rule zero — the checker may diverge on any
  input; worker timeouts are persisted skips, never findings.
- F32 in the interpreter (native claims, stuck by design), TCP/UDP
  effects, `--gpu-memory` exhaustion behavior, ASan/UBSan.

## Validation recipe after touching the generator

1. `bunx tsc --noEmit` in this repo — clean.
2. A reject sweep: `for s in $(seq 1 120); do` dump + `--check` each seed;
   zero rejects expected — every reject is a generator bug or a checker
   finding, look before dismissing.
3. `bun ../bend2-fuzzer/fuzz.ts --smoke` from the bend2-core root — all
   pass, no `smoke missing features` line. The smoke seeds are hand-picked
   per generator version (per-feature smallest-passing-seed, solo-verified).
   Splits keep most edits from touching them; when the smoke run reports a
   missing feature or a smoke seed fails after a generator edit, re-pick.
4. A few hundred seeds: `raw-reject` and `generator-reject` must be ZERO;
   `compiler-crash`/`leg-*` findings are expected while the classes above
   stay open.
5. `--threads 4 --metal` on a handful of seeds if touching anything the
   parallel or GPU legs see.
