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

Types are terms, 2026-09-16: the dependent-type kit (`let_dep`) went,
and its shapes, base's Word idiom, propositions and proofs now emerge
from the one generator:

- **Families** (`fam_new`): `law F: for x: I; Data|Type` then `def
  F(x): match x:` with an arm per constructor of the index (Nat, Bool or
  a minted enum). An arm is a type drawn by `syn_ty` with the arm's
  sub-index in scope as a term (`ivars`): the family at it (`F(p)`), or a
  datatype minted with the index as an erased parameter and holding the
  family in a field (`adt_new(c, ips)`, spelled `D<-p: Nat>`). The law
  comes first because such a datatype names the family before its fill.
  An unfinished family may be applied only at its own sub-index (the
  self-call must decrease).
- **An applied family is a type** (`T.app`): a field, a parameter, a
  list element, a return. `syn` unfolds a closed index to its arm, or
  calls `mk_fam` (`def mf(n: I) -> F(n)` by match on n, the arm's value
  synthesized with the sub-index in scope, so `F(p)` inside is the
  recursive call); `rd` reads through `rd_fam` (`def rf(n: I, v: F(n))
  -> U32`), the arm read INLINE (`rd_arm`: a tuple destructures, a Maybe
  or an indexed datatype matches as the tail, the family at the index
  calls `rf`). Inline because a reader minted under the index would
  recurse back into `rf`, and mutual recursion needs a law forward
  declaration, which only base may leave unfilled. So an index term
  reaches a type's immediate structure only: `ivars` propagate into
  tuple components, a function's result, and at the top of an arm into a
  Maybe or an indexed datatype (`imatch`), never into a List, a Map or a
  self-recursive datatype.
- **The re-bind of the sub-index** (`case 1n+p0:` then `+p = p0`) sits
  AFTER the destructures and INSIDE the match arms that read `v`: a let
  cannot open a later scrutinee (`plus_binder_row`'s rule).
- **Propositions** are types drawn where a type may be uninhabited
  (`syn_ty(.., neg)`: a family's arm, a pair's evidence): `Empty`, `{l ==
  r : I}` of index literals that agree or clash, `{l != r : I}` (a
  function into Empty). `ty_inh` says whether a type has a value (a
  family at a variable index when every arm does; a pair when some
  witness makes its evidence so; a function when its result does or its
  domain refutes), and `syn_ty` in a positive position redraws an
  uninhabited type. `syn` gives `{==}`, `Unit{}`, a witness pair, and for
  a clash a refutation: `refute_ensure` mints `def ne(e: {l == r : I}) ->
  Empty: %e : Disc(_); Unit{}` over a discriminating family (`disc_fam`,
  Empty at r and Unit elsewhere; for Nat one side must be 0n). `rd` reads
  Empty as `match x:`.
- **Dependent pairs** `&x: A -> B` (`T.sig`, spelled also `Exists(A, x
  => B)` and `Sigma<&1, &1, A, x => B>`): the witness is mostly an index
  term the evidence may mention through a family. A reader destructures
  `(+x, e) = p` and reads e inline (`rd_arm`).
- **Dependent parameters**: a minted def's later parameter may be
  evidence `P(p_i)` about an earlier index parameter (which re-binds
  reusable); `syn_def_args` picks that parameter's literal among those
  under which every dependent type has a value (`dep-call`). The law
  spelling reads a pair parameter over an index as `for p: A where
  B[p]` (the def's parameter is the pair, as base's where-laws take it)
  and a pair result as `exs z: C` plus the claim.
- **Spellings**: `Or(A, B)` for Either at &1, &1, `Pair(A, B)` for `A &
  B`, chosen at type creation (ty_str must stay a pure function of the
  type: it keys every memo). A bare `&x: A -> B` parenthesizes at a law
  row, a claim or an annotation (it would head a binder).
- **Templates**: the higher-order kit's def takes `~f: U32 -> U32` a
  third of the time, called with `~(y => ..)` or `~name` of a unary def;
  a template def is not a registry callable.
- **Natives by name now reached**: `F32.show`/`read` (a round trip on the
  compiled side), `F32.bits`, `U32.shl`/`shr`, `Map.del`/`keys`/
  `from_list`, `Set.del`, `List.map` (base's template, `~A, ~B, ~f`),
  `IO.try`. Not generated: `App.*`, `Image.*`, `Event`, the audio and
  window kits (effects), `Nat.read` (above).
- **Two exceptions of the first nine-hour run's first chunk, fixed the
  same night**: a pair drawn under a tuple took a matchable evidence type
  (an indexed datatype) that the flat reader cannot open, so a pair's
  evidence is now as matchable as the pair's own position (`imatch`
  inherits) and a pair at the top of an arm reads its evidence as the
  tail; and a call whose argument type had no value threw out of `syn`
  (`syn_def_args` now answers null, no call).
- **Probed while porting**: `where` makes the parameter a `Sigma<&1, &1,
  A, x => P(x)>` the def receives whole; `exs z: C` returns `(z, proof)`;
  mutual recursion through an unfilled law is base-only ("an unfilled
  law is a dead claim"); a template argument must be closed; `Vec.S<p>`
  takes the index as a type argument; `match e:` with no rows closes an
  Empty branch; a refutation's motive must send the RIGHT side to Empty.

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
- **`Nat.read` is not generated** since 2026-09-15 (it was the
  `nat-showread` entry of `num_gen_nat`'s roster; `U32.read` stays).
  Since bend2-core `77eff95` (2026-09-08) its overflow guard computes
  `Nat.divmod(2^48-1 - d, 10)` per digit, and base's divmod is an
  accumulator loop that counts the dividend down one cell at a time, so
  under the interpreter's unary Nat nothing is observable before 2^48
  iterations: laziness cannot help an accumulator. Native on the
  compiled lanes, never finishes under the interpreter: 1.7% of the
  2026-09-15 run's seeds skipped on it, 89% of the 2026-09-10 run's
  2,209 skips, and none pass solo. A productive divmod (the quotient
  emitted per full divisor window, `(dv.go(..), md.go(..))` as the pair)
  was tried: it reads "4321" in 19 ms but the walk overflows the JS stack
  near an accumulator of 16,000 cells, the interpreter's own depth limit
  (`U32.to_nat(65535)` overflows the same way), so the round trip is out
  of the oracle's reach either way and the roster drops it.
- **`compiler-crash` family-arm-layout**: OPEN (2026-09-16), the first
  class the dependent generator reached (3 findings in 7,875 seeds): a
  family whose arms have different runtime layouts, read per arm by
  `def rf(n: I, v: F(n))` after a match on the index, dies in the C
  emitter with `a layout mismatch` or `a constructor outside its layout`
  (4 findings in 21,075 seeds); the checker, the interpreter and the JS
  backend run it. Repros `repros/comp_family_arm_layout_sig.bend`,
  `comp_family_arm_layout_2.bend`, `comp_family_arm_ctor_layout.bend`,
  `comp_family_arm_char_layout.bend`; details in `TRIAGE-2026-09-16.md`.
  Expect this class as noise until the emitter computes layouts per arm.
- **`arity-wall` skips** (2026-09-16): the emitter refuses a segment
  holding over 255 live words (`an arity over 255`, `FID_ARITY_T` is a
  u8 table), which a list literal of hundreds of calls reaches (every
  built element stays live across the next call's continuation). The
  harness counts the refusal as a skip, not a finding: it is a documented
  limit, loud, and the generator's own `stretch` lists are what hit it
  (1 in 21k seeds). The old class K (an emit-time cliff on the same
  shape) is this wall's slow neighbour.
- **One-off, unreproduced (2026-09-16)**: seed 1363374988789664739 (a
  show program, `def main() -> Maybe<&2, D1>: Some{D1a{0n, Nil{}}}`, 31
  lines) failed C-SEQ with `bend: memory fault (machine stack overflow?)`
  in two of three 300-seed runs from `--seed 3700`, never standalone: 300+
  runs of the same binary (the run's own kept binary and C, byte-identical
  to a standalone emission), under load, with a harness-like name and
  cwd, with an empty and a 100 KB environment, all pass. The runtime maps
  its pool MAP_NORESERVE and reports any SIGBUS/SIGSEGV with that text, so
  a first-touch fault under memory pressure (8 jobs, clang, bun workers)
  fits; a nondeterministic runtime bug does not fit the byte-identical
  binary passing everywhere else. Left open; rule zero does not cover it
  (it is not a timeout), so it will show as `leg-diverge` if it recurs.
- **Worker isolation (2026-09-16)**: the worker clones base's book per
  request by shallow-copying tlds, ctrs, order, and now the template
  descriptors (`tmps`), each with a copy of its instance table and its
  parser state re-pointed at the request's book. Without that, a program
  instantiating base's `List.map` registered `List.map~0` in BASE's book
  and the next request either lacked it ("a defined name"), redeclared it
  ("duplicate declaration") or emitted over a stale instance (`t.$` of
  undefined in carb_book). The CLI never sees this: one book per run.
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
