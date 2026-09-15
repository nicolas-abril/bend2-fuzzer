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
- **Async is a modeled walk, not a race**: a tail's async part is a random
  walk of main's do-block over fibers, channels and timers, and a model
  keeps its answer schedule-independent: a receive takes the FIFO prefix
  when every pending value is one producer's and the whole pending sum
  (commutative) when several producers raced; a producer is joined only
  once its sends are received (a full channel would deadlock the join);
  a timer group registers in deadline order, since the loop stamps each
  timer with a strictly later deadline; the epilogue drains and closes
  every channel and joins every fiber. Only timer pings print, and main
  prints after joining them, so no two fibers' prints can interleave. The
  compiled legs compare it among themselves; the interpreter never runs
  it. Sockets stay out: `UDP.bind` takes a port and parallel jobs would
  collide.
- **The GPU lanes**: `--metal` / `--cuda` build the SAME emitted `.c` with
  the platform flags and run `--gpu on`; `--threads N` adds the CPU-par
  lane on the sequential binary. GPU runs are serialized; a GPU binary
  re-reads its `.c` at the compiled path, so build dirs live until the run
  ends.

Ported to main `627df664` on 2026-09-15 (the port that followed the
2026-09-10 run):

- **Breakages fixed**: `term_show` prints a closed U32 as its decimal
  (the worker decoded a `U32{WCon{..}}` chain); `Chan<A>` is `Chan(A)`
  (a law family applies with parens; the record handle types are gone
  with the handle table); the runtime CLI lost `--parallel`, so the
  sequential lane is `--threads 1 --gpu off`.
- **New surface generated**: `+` on any binder (a case field in
  `adt_row`, a parallel let in `let_fork`, a lambda in `hof_call`, a do
  bind and a do let in `do_call_def`, a tuple let in `let_array`),
  `h <> t` / `[]` rows for List, list literal patterns with a `_` row
  (`match_list_def`), a cons chain ending in a list literal, array
  literals and the `a[i] <- v` statement (`let_array`), bare do steps
  and `;` in the IO tail, `\u{hex}` escapes in `str_char`,
  `File.read_bytes` summed through a cons-pattern walk, twins `f(x, x)`
  in `let_shared`.
- **The show leg**: a pure `main` now really runs on the C and JS
  runtimes and prints its value through a new printer per runtime
  (`show_val` over a descriptor of main's type), so `--show-pct` seeds
  are solo `def main() -> T: v` programs over printable types, the
  interpreter's literal the expectation. A tuple is a Type, so none
  rides inside a List or Maybe (a Data element); the checker refuses
  it. Erased or dependent fields cannot be printed and are kept out.

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
  kind. A `+` marks any binder reusable: a case field (`K{+x}`), a
  variable row (`case +y:`), a tuple or constructor let, one per name of
  a parallel let (`+a +b = f g`), a lambda (`+x => e`), a do bind and a
  do let; the re-bind sinks below a run of leading destructures and into
  every arm of a heading match. A `+x` in a term position is an error.
  Fork rider values must be bare var atoms (a parenthesized rider would
  glue onto the preceding call as a spaced suffix; a literal rider cannot
  infer).
- `h <> t` is the cons in terms and patterns (`+h <> t` marks the head),
  `[]` the empty list, `[a, b]` a literal pattern, `_` a wildcard row;
  `[x : T*n]` (n a literal power of two, the slot count) and `[x : T^d]`
  (a depth) build arrays; `a[i] <- v` followed by a statement at its
  column (or a `;`) is `a = a[i] <- v`; a bare term in a do block is a
  step (`Unit <- term`) and `;` joins two on a line. An opaque handle
  (File, Socket, Listener, Window, Audio, Chan) is a law with no
  constructor and no field: never build or match one; `Chan(A)`.
- A bare literal (U32/F32/Nat/ctor/tuple/list) in a LET VALUE cannot
  infer: `x = {v : T}`. Do-binds are annotated (`x : T <- act`).
  Negative float literals do not exist (`-3.5` heads a binder): spell
  `F32.neg(3.5)`.
- Recursion descends structurally on the FIRST live column (erased
  columns skipped) — any chain adt (at most one self field per
  constructor) serves as a loop's fuel, the program's own included,
  beside a Nat or a String; only the Nat kind counts down a masked
  number, the rest walk synthesized data. `@unsafe` opts out and is
  emitted rarely. Partial applications stop at exactly live-1 arguments.
- Plus sugar (`+D<..>`) is lawful only right after `:` (annotation sites);
  after `(` or `&` it parses as a binder. `ty_str` is the safe rendering,
  `ty_top` the annotation-site one. Fun components of `A & B` need parens
  (`&` binds tighter than `->`).
- Axioms are banned outside base ("a final unfilled assert is an error"),
  so the assert/def split is always filled.
- An operator needs its `( .. : T)` frame (bare, it is Nat's): `+ - * /
  % .&. .|. .^. << >> <= >= >` at U32, `+` at Nat, `+ - * / % <= >= >`
  at F32; `<<`/`>>` take a Nat count; there is no `<`, `==` or `!=`
  infix (calls through a Bool reader); `<>` is List-only cons (String
  uses `SCon`/`++`).
- `qt_fits` mirrors term_compare's Typ case: Data fits every kind, every
  kind fits Kind(&0) and Kind(&1), a left meet needs both sides, a right
  meet accepts either side, a stuck target licenses only an identical
  term. Ctor field kinds must fit the declared G.

## Known noise and open compiler bugs (2026-09-15)

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
- ~~erased-arrow application~~: FIXED (2026-09-05, "Drop the erased
  applications of a function value", bend2-core PR #11): the carbonizer
  drops an erased application whose head is a function value and reads
  a value's quantities off its own annotation; regression-covered by
  `reg_erased_arrow_apps.bend`. The 2026-09-04 triage's other classes
  (A, B, E, H, I) are fixed too, and F (big-literal compile time) on
  nicolas3 (a8917dc (efead59 before the rebase onto e913e65)), see `TRIAGE-2026-09-04.md`; D (the bracket wall)
  stays open. The 2026-09-07 eight-hour run (`TRIAGE-2026-09-07.md`,
  391k seeds) found four more compiler classes (J, L, M, N), all fixed
  in the nicolas3 tree, six more D instances, and one open emit-time
  cliff (K: a list literal of hundreds of calls).
- The operator grammar changed on main (2026-09-05): an operator is a
  method named by the `( .. : T)` frame around it, `+n` and the dotted
  F32 family are gone, `assert`/`forall` read `law`/`for`. `e_bin`
  spells the frame from the op's family tag; every raw template was
  reframed. The repros under `repros/` predate this and need porting
  before they parse.
- ~~C livelock: packed ctor over a Char field~~: FIXED (2026-09-01) —
  a packed Char field ORed its tag/aux bits into the outer word, so
  the ctor masqueraded as cid|CID_CHR: misdispatched matches freed
  header memory and heap_alloc spun forever. ctr_wrap now strips the
  field to its code at build and re-wraps it at the arm;
  regression-covered by `reg_ctr_packed_char.bend`. Of the two finder
  seeds, 8559387686525276681 turned out to be the erased-arrow class
  below (which also fires as a C hang), not this one.
- ~~`compiler-crash` packed-ctr-var-arg~~: FIXED by 2026-09-15 — the
  repro builds on main `627df664` (borrow inference was rebuilt as a
  monotone fixpoint in `03b50532`). It was the only compiler class the
  generator reached in the 2026-09-10 run (4 findings in 126k seeds). A constructor whose own node layout is one machine word,
  belonging to a boxed datatype, with its field spelled as a VARIABLE,
  passed to a def that matches on it: the C emitter dies with `an
  unbound binder: X` (X follows the variable). Introduced by bend2-core
  `8627c94`'s packed-constructor borrow rule in `facts_scan`'s `site`,
  NOT by the current tree's comp.ts work. C-only; the checker, the
  interpreter and the JS backend all accept it. Repro
  `repros/comp_packed_ctr_var_arg.bend`, details in
  `TRIAGE-2026-09-10.md`.
- **The 2026-09-15 run** on `627df664` (45 minutes, 13,250 seeds,
  `--threads 4`, 4.9 seeds/s): no compiler finding. Its 7 failures were
  generator rejects of the port (a lambda as a cons head swallows the
  chain as its body; a nested match on a `+`-marked field binder), both
  fixed in the generator the same day. 227 skips, 204 of them programs
  that call `Nat.read` (below).
- **`Nat.read` is still uninterpretable** on 2026-09-15: 1.7% of seeds
  skip on `raw-worker-timeout`, nine tenths of them `nat-showread`
  programs. Since bend2-core `77eff95`
  (2026-09-08): its overflow guard builds 2^48-1 as a unary Peano Nat
  (`Nat.read.max`) per digit. Native on the compiled lanes, fatal under
  the interpreter's structural evaluation. This is NOT a finding (rule
  zero) but it is the dominant skip source: 89% of the 2026-09-10 run's
  2,209 skips call `Nat.read`, and unlike previous runs' skips they do
  NOT pass when re-run solo. It also cost that run three quarters of its
  throughput (4.3-5.2 seeds/s against 13.6-18.8 on 2026-09-06) and
  blinds the oracle on every `nat-showread` program. Reverting only that
  hunk on HEAD takes a sampled seed from a 45.7s timeout to 0.2s.
- ~~Class D, the clang 256-bracket wall~~: FIXED before 2026-09-10.
  `repros/c_bracket_wall_chain.bend` compiles, and 126k seeds produced no
  D finding. The 2026-09-04 triage's unapplied one-line patch is moot.
- Class K (a list literal of hundreds of calls, emit time) stays open but
  is about twice as fast since `7c2d194`: the repro takes 15.7s of user
  time against 27.3s at its parent, same output.
- The generator drifted from base twice by 2026-09-10 and both showed up
  as `raw-reject` in `--smoke`: `Array.clone` gained `-T: Data`
  (`592b0df`) and `Result.fail` was removed (spell the `Fail{..}` ctor).
  Re-run `--smoke` after any base change before trusting a long run.
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
