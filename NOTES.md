# Fuzzer maintainer notes (`devs/_fuzz_.ts`)

Local-only (git-excluded), like the fuzzer itself. Written June 2026 after a
full architecture review, a performance overhaul (3.5x throughput), and the
addition of the metamorphic leg. Read this before restructuring anything —
several things that look accidental are deliberate.

**The fuzzer is entirely local and must stay invisible in the repo's public
record.** Nothing about its workings — seeds, shapes, verdict plumbing,
timeouts/budgets, normalization suppressions, or fuzzer-side follow-up
adjustments — belongs in `devs/issues/` files or commit messages. Issues
describe the compiler problem on its own terms, with at most a brief
"(found by fuzzing)" note as the discovery attribution. Fuzzer-side details
(known noise sources, suppressions to remove when an issue is fixed, etc.)
go in THIS file instead.

## What it is

A differential fuzzer for the Bend backends. Each seed deterministically
generates one well-typed, terminating Bend program, runs it on several
backends, and compares results:

- **JS (reference) vs C (under test)** — always.
- **Interpreter** as a third oracle — only for `linear` programs (no value
  duplicated into expensive recomputation; duplication is the only thing that
  blows up the symbolic normalizer).
- **Metal** — only `@kernel`-shaped programs under `--with-metal`, serialized
  (one GPU).
- **Metamorphic leg** — every passing program is re-emitted in a second
  spelling (minimal parentheses) and re-run on JS; reject or output change =
  front-end bug. This is the only oracle that can see parser bugs, because
  all backends share one front end (common-mode failures are invisible to
  cross-backend diffing).

Verdicts: `ok` / `reject` (failed `--check`) / `skip` (timeout, stack
overflow — resource limits) / `fail` (a finding). Findings stream as they
happen; the summary prints per-shape tallies. `--show-rejected` also prints
skipped (timed-out) seeds so they can be reproduced.

**Findings are persisted to `devs/_fuzz_findings_/seed-N.bend`** (program +
output excerpts as comments; git-excluded). This matters because the
generator itself is not version-controlled: any generator edit changes the
seed→program mapping, so a bare seed does NOT reproduce a finding across
fuzzer versions — the saved program is the durable artifact. The suggested
`--jobs 1` repro command also removes the load/parallelism context (and
pins NUM_THREADS=1), so for flaky parallel-runtime findings, stress the
saved program's C binary directly (compile once, run many times with
NUM_THREADS=4 and BEND_GC_THRESHOLD=1).

**Rejected programs are persisted to `devs/_fuzz_findings_/rejected/seed-N.bend`**
(separate subfolder so they never get confused with real divergence findings;
written by `save_reject`, always, regardless of `--show-rejected`). Most are
background noise (the `char{$m2}` infer bug above), but a reject can mean the
checker is rejecting valid code, which is a compiler bug — that is why they are
kept. Each file leads with a `# REJECTED ... # found=<ISO timestamp>` header
plus the first lines of the checker/parser diagnostic, then the program. Real
findings (in the parent dir) also now carry a `# found=<ISO timestamp>` line so
recent artifacts can be told from stale ones.

**Skipped programs are persisted to `devs/_fuzz_findings_/skipped/seed-N.bend`**
(same scheme, written by `save_skip` at each of the six skip sites in
`prepare_one`/`compare_one`). The header carries `reason=<stage>`:
`emit-timeout`, `compiler-stack-overflow`, `js-run-timeout`, `cc-timeout`,
`c-run-timeout`/`c-missing`, or `runtime-stack-overflow` — so the stage that
gave up is visible without re-running. Skips are mostly load noise, but a
misclassified one can mask a finding (a `cc-timeout` once hid a COMPILE
FAILURE), which is why the program is kept. The scheduler's lone
`record("skip")` in the error handler is a *fuzzer crash*, not a program skip,
and is deliberately NOT persisted (it is logged as FUZZER ERROR instead).

**Known background-noise sources (investigated June 2026, ~1000-program
runs):**
- Rejects (~0.3%): almost all are the fuzzer hitting a real, filed compiler
  bug — `devs/issues/char_literal_match_wildcard_nested_match_cant_infer.md`
  (ctr-literal pattern + wildcard arm containing another match + non-var
  scrutinee ⇒ `Cannot infer type: char{$m0}`). The generator keeps emitting
  the construct on purpose (it is valid code); the rejects disappear when
  the compiler is fixed. If the reject rate climbs above this, investigate:
  an earlier round found a genuine generator bug this way (unannotated char
  literals in scrutinee position — `gen_value` now annotates chars).
- Timeouts (~0.1-0.4%): load noise. Tree-parallel fork programs (2^n tasks)
  used to time out spuriously under GC stress on a saturated machine (they
  pass in isolation); the scheduler now runs **fork programs exclusively**
  (admitted only once the pipeline has drained, and nothing else admitted
  while one runs — see `excl_busy` in the scheduler loop, which also gates the
  next program's generation so the host thread stays free to service the run's
  child-exit promptly), which removes that source. Multi-threaded C runs still get 2x RUN_TIMEOUT as a belt-and-braces
  margin. What remains is mostly `cc` timeouts on fork
  programs whose C output is huge: the CPS transform multiplies code size
  ~17x (filed: `devs/issues/cps_continuations_explode_c_code_size.md`,
  found when such a timeout was misreported as COMPILE FAILURE — seed
  993450568, program preserved in `_fuzz_findings_/`). `cc` timeouts are
  classified as skips (CC_TIMEOUT=40s); a cc *error* with diagnostics is
  still a finding. Rejects of *valid* programs deserve eyeballs; timeouts
  mostly don't.

## Architecture (mirrors the file's layout header)

1. **Numeric tables** — the `Num` records (U8..I32, NAT, F32) carry their op
   lists, literal/divisor printers, and the `CASTS` table. Adding a numeric
   surface usually means touching only these tables. `bit_ops`/`BIT_UNARY` add
   the pure, total bit intrinsics (`count_ones`, `leading_zeros`, `reverse_bits`,
   `rotate_left`, `byte_swap`, `bitwise_get/set/clear`, ...) on the unsigned
   widths only — availability differs per width (see the table). They're folded
   into `gen_num_raw`'s per-type operator pool (a single uniform pick alongside
   the infix ops), so each intrinsic is emitted exactly as often as each infix
   op for that width; they print as call-form atoms and fold through `combine`,
   validated for free by the JS-vs-C differential.
2. **Type universe** — `Ty` plus `gen_type`/`gen_composite`/`gen_adt` (full
   universe) and `gen_print_type` (the show-safe subset; see `ty_print_safe`).
   User ADTs accumulate in the module-global `CUR_ADTS`, reset per program.
3. **Values & expressions** — `produce(g, h, env, fuel)` is the type-directed
   value generator (`gen_value` is an alias): it fills a hole of type `h` by a
   WEIGHTED draw over every way to make an `h` — an in-scope variable (a closure
   when `h` is a function type), a constructor/literal/element-intrinsic, or a
   function whose result is `h` (the universal `Poly/id`/`Hof/ap`/`Hof/twice`
   apply to ANY type, so every hole has function producers, not just
   constructors — higher-order/generic now reaches composites, not only nums).
   When a reduce/transform pipeline is active (`CUR_POLY`, set by `poly_new`),
   generated functions also become producers: a `trf : T -> T` transformer
   (applied to a produced `T`) for composite holes, and — in `gen_num` — a
   `red : structure -> scalar` reducer (folding a produced structure) AND a
   failure-MONAD fold (`M/fold(<bind/do chain>)` via `monad_parts`) for numeric
   holes. The monad producer is NOT capped per program (heavy but rare via its gate); a
   recursion guard (`IN_MONAD`, save/restored around `monad_parts`, whose step
   bodies call `gen_num`) blocks only monad-in-monad nesting — needed because
   `monad_parts` uses a fixed internal fuel, unlike the reducer/transformer
   producers which recurse at fuel-1 — being a `gen_num` producer it composes into any
   numeric position (a let body, an operand, a callback), which a standalone
   `monad` shape couldn't. All register their def into the active poly's `.defs`,
   so they're only
   safe in code emitted AFTER `p.defs` or the def is an unresolved forward
   reference (forward_references_unresolved_same_file.md). Hence `NO_TRF` is ON by
   default (suppressed) and enabled only around the unified shape's main body,
   which `prog_src` emits last; `gen_program` re-suppresses before the dead-def
   injection. Helpers/consts self-suppress via their own save/restore.
   Termination is by construction: at `fuel<=0` it switches to `produce_min`,
   which uses only the minimal base producer per type (none/[]/leaf/a
   non-recursive ctor) and recurses solely on structurally-SMALLER components —
   induction on the type, never a runtime value. Numbers/bools keep their tuned
   operator engines (gen_num/gen_bool), which `produce` delegates to — those are
   precedence/probe machinery, not "ways to make a value", so they stay special.
   `gen_num` is the numeric-expression workhorse (vars, literals, div/mod with
   zero divisors, F32 comparisons via `gen_f32_cmp_arg`, CAD, casts, helper
   calls, HOF closures, bit intrinsics, infix ops); `gen_case_lambda_body` emits
   the `λ{...}` case-lambda sugar (bound to a typed name then applied — direct
   lambda-match application is parser-banned, so it must be eta-bound first);
   `gen_match`'s `str` kind emits string-literal patterns (`case "lit":` + `_`,
   via `str_literal` so NO_NUL is honored); `gen_body`/`gen_match*`/`gen_if` build
   statement-shaped bodies; `gen_helper` builds tail-recursive state machines.
   `gen_body`'s let RHS is general: usually a flat `gen_num`, but ~20% (fuel
   permitting) a nested body — match / if / case-lambda / nested let-block via a
   recursive `gen_body` call — wrapped `(( <block> ) :: ty)`. The wrap *and* the
   annotation are required: a `match` in binding position desugars to a `λ{...}`
   the checker can't infer there otherwise, and indentation is significant
   (Haskell-like — the block sits at ind+2, the close-paren back at ind). Every
   let is the body type and is folded into the result via `combine`, so bindings
   are live (a dead binding wastes fuzz space); a deliberate dead let is left
   only ~rarely (measured ~1%).
4. **Reduce/transform library** — `reduce_expr`/`ensure_reduce` generate
   memoized structural folds (structure -> scalar); `ensure_transform`
   generates structure -> structure functions (maps, reversals, comparator
   filters, optionally threading a callback). `combine` folds scalar names
   with random ops so nothing is dead code; `seal`/`seal_tail` append the
   distributivity poison `e+(((e+e)*e)-((e*e)+(e*e)))` (zero in any correct
   fixed-width backend) so a miscompiled arithmetic form diverges even when
   the raw result looked right. Shared scaffolding: `fold_arm` (the
   "destructure ctor, reduce fields, combine" arm), `finish_tail`,
   `bind_scalar`, `prog_src`.
5. **Shapes** — eleven `gen_*_program` generators registered in `SHAPES`
   with explicit per-mille weights (must sum to 1000). `unified` (67.5%) is the
   compositional workhorse; the rest are focused probes (rank-2 dicts,
   TCO rings, linear arrays, string rewriters, bignat, fork/CPS,
   `@kernel`, IO, `polyshow` = same polymorphic type shown at two
   instantiations). Every shape returns
   `ShapeOut = { ty, src, linear, fork? }`. Shapes exist for two reasons: a
   distinct *construct* not otherwise reachable, OR distinct *infrastructure*
   (fork→scheduler, metal→`--as-metal`, io→spawn path). Constructs that are just
   "emit a def, call it, fold the scalar" belong as `unified` FOLD-mode PROBES
   (see `wf_probe`/`polyfn_probe`/`map_probe`/`array_chain_body`/`monad_parts`/
   `tail_probe`/`eq_transport_probe`/`fork_probe`) so they COMPOSE inside larger
   programs — prefer that over a standalone shape.

   **Well-founded recursion + polymorphic defs + Map (former shapes, now `unified`
   probes).** All three are "emit a def/ops, fold a scalar," so they're fold-mode
   probes, not shapes:
   - `wf_probe`: MOD-measure (Euclid gcd) `f(a, b, acc) = f(b, a % b, …)` — the
     second arg `a % b < b` strictly decreases to the `b==0n` base, halting BY
     CONSTRUCTION (halting checker is off; the generator guarantees the decrease).
     This is the well-founded form `gen_helper`'s single-arg recursion can't
     express. DIVISION-measure `f(n // Kn)` (Kn>=2n, ~log_K(n) steps, any Nat
     cheap) is instead `gen_helper`'s fourth rec kind `"div"` (alongside `nat`/
     `list`/`str`), callable from any numeric leaf — no overlap with `wf_probe`.
     Note: `n // 2` needs the Nat-literal divisor `2n` (a bare `2` infers as U32).
   - `polyfn_probe`: a fully GENERAL parametric synthesizer for polymorphic
     `def f(T0: Type, …, Tk: Type, …) -> …`, built on the ONE type universe — there
     is no separate type language. Type variables are a `Ty` kind, `{ k: "tv", i }`
     (helper `tvar`), generated by `gen_type` only when the module global
     `POLY_NV > 0` (set just inside this probe), so the universe is otherwise
     byte-identical (the `tv` gate short-circuits before drawing RNG). The
     type-variable count is a `decaying_count`; the signature (argument + return
     types) is drawn straight from `gen_type` with `POLY_NV` set, so poly functions
     take/return ANYTHING the universe builds — composites, poly ADTs, and
     functions including `A -> B` (the `fn` domain was widened from `Num` to
     `Num | TVar`; `poly_dom` picks a tv domain in poly context). `poly_safe_ty`
     post-maps the linear `array`/dependent `sig`/indexed `gadt` to plain cousins
     (they don't mix with type vars — `array` linearity, a `Sigma` checker-ordering
     reject, no meaningful index). The body is `produce`d directly: `produce` fills
     a `tv` hole parametrically from the environment (and, gated on `POLY_NV`,
     applies an env function whose codomain matches — that's how an `A -> B`
     argument gets USED); `produce_min` has the matching `tv` case. Every variable
     Ti gets a plain `pi : Ti` argument so any `tv` is always sourceable; the
     dead-closure-param quirk is irrelevant because results come from captured
     args, not closure params. `NO_TRF` is forced on during body synthesis so the
     reducer/monad producers don't fold a tv-bearing structure (and `gen_adt`/
     `gen_gadt` set `POLY_NV=0` for their concrete decls). Instantiated at concrete
     int scalars (`PFN_SC`, T0 = t) via `ty_subst`; the result folded by
     `fold_poly_result` (scalar→cast, function→apply then fold codomain,
     else→`reduce_expr`). `polyfn_body` optionally destructures one `Pair` argument
     first (the `first`/`second`/`swap` pattern); an occasional `List(A) -> Nat`
     form is kept for structural-recursion coverage.
   - `map_probe`: Map-sugar literal/`<~`-set/get→`t?`→fold, flat or nested.

   Mutual recursion / forward references between generated defs resolve if the SIGNATURE
   is forward-declared (`f : T -> U` then `def f`); only body-LESS declarations
   miscompile (bodyless_declaration_calls_compile_to_null.md) — not generated.

   **`mutrec_probe` (rare unified probe): mutually-recursive type definitions.**
   Bend has no forward type declaration and doesn't resolve type forward
   references (forward_references_unresolved_same_file.md covers types —
   `type A {..B..}` before `B` is `unbound: B` either way), so a type CYCLE is
   expressed only by type REDEFINITION: emit a stub `type B { B_d{} }`, then
   `type A {..B..}`, then redefine `type B {..A..}` for real (last wins — verified
   JS==C==interp, and the stub ctor doesn't leak). **This relies on redefinition
   being accepted, which is almost certainly unintended** — hence kept rare
   (~3% gate inside `unified`), and removable in favour of a clean stub-free
   emission if forward type decls (or two-pass type resolution) land. The
   redefinition is name-local (the `Mr<u>` types can't collide with the program's
   universe types), so it composes safely inside a larger `unified` program — it's
   a probe, not a standalone shape. The folds are mutually recursive via
   forward-declared signatures (which DO resolve); values are bounded-depth ending
   in a base ctor, so everything halts.

   **The universe merge (June 2026).** Three former shapes were folded into
   the shared machinery so they compose with everything:
   - `String` is a `Ty` leaf: values via `gen_str_expr`, folds through a
     generated char-code fold, transforms via `String/reverse`. Print-UNSAFE
     inside composites (show-kind degradation) — top-level strings still
     compare textually in the string shape.
   - Poly ADT *instantiations* are a `Ty` kind (`padt`): `gen_poly_adt`
     registers the decl, `padt_fld_ty` substitutes args, ensure_reduce/
     ensure_transform have arms. The `polyshow` shape keeps the focused probe:
     the same type SHOWN at two instantiations. **No hard caps on polymorphism**
     — the soft-curve principle: where the old code had a fixed ceiling, use a
     `decaying_count`/`0.5^count` probability instead, so the count trends small
     but is never bounded. A poly ADT's type-PARAMETER count is `decaying_count`
     (1 common, 2/3/… increasingly rare; unused params are legal phantom types);
     the number of distinct poly ADTs ACTIVE in a program grows with probability
     `0.5^(count so far)` per fresh-vs-reuse decision (so a few, occasionally
     more, never capped). Type-variable names come from `tvar_name` (A, B, C, …,
     then `Tv26`…). Same principle drives `polyfn_probe`'s variable count.
   - GADT instantiations are a `Ty` kind (`gadt`, concrete length); folds are
     per-target-type (`Name/foldT(n, v)`, via `ensure_gadt_fold`); transforms
     skip them (no index-preserving transformer). The `indexed` and `eq`
     shapes retired: their coverage is the universe plus unified's
     `eq_transport_probe`.
   All generated type decls go through `reg_decl` into `CUR_DECLS`
   (creation order = dependency order); `prelude` scans it newest-first
   transitively and emits needed decls in `seq` order — required because
   same-file forward references don't resolve.

   **Unified probes** (fold mode only, each independently gated):
   eq-transport (0.15), tail loop (0.12, accumulator type chosen so the cast
   back to `t` is real — `has_cast` — so the loop is never dead), linear
   array chain (0.12, via `array_chain_body` shared with the array shape, in
   a helper def), monad chain (0.10, via `monad_parts` shared with the monad
   shape), fork pair (0.10 — sets `fork: true` on the ShapeOut so the
   scheduler runs the C binary with pinned threads).

   **Parser-continuation trap when emitting helper defs**: a body line
   starting with `(` after a multi-line construct (do-block result type,
   a bind call) parses as an *application continuation* of the previous
   line. Always follow such constructs with a `name = (...)` bind, never a
   bare parenthesized expression (this is why the monad probe binds the fold
   result through a fresh name).
6. **Oracle & scheduling** — see "Performance machinery" below.

## Invariants you must not break

- **Seed determinism / RNG purity.** `gen_program(seed)` must consume RNG
  draws identically regardless of flags. Seeds are 64-bit (BigInt): a run's
  seeds form a chained splitmix64 walk (`seed_0 = base`,
  `seed_{i+1} = seed_step(seed_i)` — a bijection, so no within-run repeats,
  and different runs' walks practically never overlap). The seed printed in
  a finding IS the program seed: `1 --seed P` reproduces it exactly.
  Note this fixes seed-space collisions only — two seeds can still emit the
  same *text* for degenerate tiny programs (measured ~1 per 1000 on the old
  scheme), which is harmless. The metamorphic leg *regenerates the
  same seed* with `MIN_PARENS` set and relies on the two spellings denoting
  the same expression tree. Any flag-dependent code in generators may only
  change *string assembly*, never which/how many `r()` draws happen.
- **The boundary parenthesization contract.** In `MIN_PARENS` mode the raw
  numeric worker (`gen_num_raw`) returns bare infix spellings, safe only at
  `bin()` operand positions (which track operator precedence via `LAST_OP`).
  The public `gen_num` and `combine` re-parenthesize an infix-topped result
  because dozens of sites embed their output into hand-built syntax (e.g.
  `match (E % 2):`) assuming atom-or-parenthesized shape. If you add a
  generator that emits infix without going through `bin`, wrap it in parens.
  A stale `LAST_OP` tag can only *add* parens (harmless), never drop them.
- **`BIN_PREC` mirrors the parser's table**
  (`Parser$Term$Expr$parse$head$infix$peek` in `bend/src/Lang.ts`). If
  operator precedence in the language changes, update it — the fuzzer will
  loudly tell you via METAMORPHIC findings (verified: mis-transcribing `^`
  yields ~13 findings per 250 seeds). `~` is deliberately absent: infix NOT
  discards its left operand (filed issue), so it stays fully parenthesized in
  both spellings.
- **Programs must terminate by construction.** Recursion is structural
  (ctr 0 of generated ADTs never holds a recursive field; GADT chains carry a
  literal length; tail loops count down a literal Nat). Don't add recursion
  whose termination depends on runtime values.
- **Nothing may be dead code** *within the executed computation*. Every
  generated sub-result is folded into the final scalar via `combine` (which
  excludes `~`, since `a ~ b` drops `a`). A dead value means its whole
  construction stops being tested, silently. **Sanctioned exception:** two rare,
  deliberately-dead *top-level* forms injected by `gen_program` (after the shape
  is generated, so they don't perturb its RNG) — `Fz/dead`, a never-called def
  (~4%), and `Fz/Empty` + `Fz/absurd`, an uninhabited type with its empty-`match`
  eliminator (~1.5%). These exist precisely to exercise the unused-def and
  empty-match *compile* paths; they're inert at runtime (never reached), so they
  can't change any output and don't weaken the differential. Skipped for the
  metal shape so `--as-metal` only sees kernel structure. Don't "fix" them into
  the live fold — that would defeat their purpose.
- **Nat `+` is successor syntax.** `N + x` with a literal N on the left
  expands to N successors at parse time (language design, not a bug — see
  memory/known-limitations). Generators keep Nat-`+` lefts small literals;
  big-nat lefts would explode codegen.
- **`NO_NUL`** is set while generating IO programs: printing a NUL through IO
  is an intentional runtime error with *different* messages per backend.
- **`linear: false`** for show-mode programs (interp sugars shown structures
  differently) and IO. If a new shape duplicates values into expensive
  recomputation, mark it non-linear or the interp leg will time out.

## Comparison normalization (`canon` / `norm_show`)

These suppress *known, filed* show divergences so they don't drown real
findings: NUL `\0` vs ` ` (see
`devs/issues/string_escape_handling_not_unified.md` — remove the
normalization when fixed), signed/unsigned I32 bit-images, Nat losing its `n`
in erased positions, single-char Char renderings, interp's `+` prefix and
width suffixes on scalars (`b`/`s`). F32 compares by float32 value with an
ULP budget scaled by the program's transcendental call-site count (JS f64
libm vs C f32 libm); `sqrt` is exact and excluded from the count. The set of
F32 functions and their exactness lives in ONE table (`F32_FNS`): the emit
pick-lists (`F32_UNARY`/`F32_TRANSCENDENTAL`) and the ULP call-site matcher
(`F32_INEXACT`/`F32_APPROX_RE`, which feeds `approx`) are all derived from it,
so a new F32 op is added in one place and emission can't desync from the
tolerance budget.

Computed chars (`gen_value`'s char branch: `Char/from_u32(...)` and the
char-returning `Fz/mk_char` helper) mask their codepoint to `0..0xD7FF` via
`% 55296` — valid Unicode scalars below the surrogate range. This is a
*generation-side* suppression of a filed backend divergence:
`Char/from_u32` disagrees on invalid codepoints (JS replaces surrogates / values
> 0x10FFFF with U+FFFD; C stores the raw value — see
`devs/issues/char_from_u32_invalid_codepoint_diverges.md`). High scalars stay
covered by the char literals (STR_CHARS). Remove the masks when the bug is fixed.
When a show
issue gets fixed, *delete its normalization* — each suppression is a small
blind spot.

## Performance machinery (the 3.5x overhaul)

Baseline was 4.9 prog/s; now ~17 prog/s (200 programs, 9 jobs, M-series).
Where the time went and what fixed it:

1. **macOS first-exec signature validation was 53% of all busy time**
   (~837ms per fresh binary under parallel load — it serializes through a
   system daemon). Fix: **C batching**. Each program compiles to an object
   with `-Dmain=bend_main_<seed>` (everything else in generated C is
   `static`, so objects can't collide — verified with `nm`), and a small
   dispatcher links ~16 objects into ONE executable, each program run by
   index as its own process with its own env. Plus a **warmup exec** of each
   fresh batch binary (`argc < 2` exits immediately) — without it all 16
   group runs start cold simultaneously and all queue on the same
   validation. The `CBATCH_LINGER` timer flush guarantees progress (queued
   jobs hold scheduler slots; without the timer a drained generator
   deadlocks). Solo-link fallback exists so one bad object can't mask others.
2. **Cold `bun CLI` spawns cost ~170-190ms; warm server requests 2-30ms.**
   Fix: a pool of persistent `bun CLI --test-server` workers (JSON line
   protocol, per-request env — same mechanism as `devs/_test_.ts`). One
   in-flight request per worker; a timeout kills the worker and the pool
   replaces it (this is the old GEN_TIMEOUT semantics). Workers retire after
   `SRV_RETIRE` requests because the server caches checks per *file* and
   fuzz files are unique — unbounded growth otherwise in `--loop`. The
   server merges stdout/stderr into one stream; error detection there relies
   on exit codes (fine: CLI returns proper codes).
   **IO-shape programs must stay on the spawn path**: their runtime spawns
   node with inherited stdio, which would corrupt the server's JSON protocol.
3. **Scheduling**: with warm workers and batching, most of a program's wall
   time is queueing, not CPU — so the program scheduler admits ~2x the core
   budget while token limiters (`cc_lim`, `cbin_lim`; bin runs weighted by
   NUM_THREADS) keep the CPU-heavy stages within budget. Empirically tuned:
   `SRV_MAX = min(budget, 8)`, cap `budget*2+4`; bigger pools/caps thrashed
   (measured worse). **Exception: fork and metal programs are scheduled
   exclusively** — admitted only when `inflight` is empty, and no other job is
   admitted while one is in flight (`excl_busy`; metal counts as exclusive only
   under `--with-metal`, when it actually runs the GPU). A fork's C binary fans
   2^n tasks across every core and metal's run is GPU-serialized, so
   co-scheduling steals resources and fires the run-timeout on a program that
   passes alone. While an exclusive program is in flight we ALSO stop
   generating the next one (the gen guard checks `excl_busy`): `gen_program` is
   synchronous host-thread CPU, and a stall there delays servicing the
   exclusive run's child-exit event — which could fire its run-timeout on a
   binary that finished instantly (the residual "bad luck" false skip). Keeping
   the host idle during the timed run removes that source. This costs a little
   throughput (the pipeline drains around each exclusive program, plus one
   deferred gen) but kills the false-skip noise; fork/metal are a minority so
   the hit is small. The `cbin_lim` NUM_THREADS weighting is now redundant for
   fork (it runs alone) but still governs non-fork bin runs.
4. The remaining dominant *genuine* cost is `cc -c` (~145ms/program): clang
   recompiles the embedded runtime per program at `-O2`. Do NOT lower the
   optimization level — `-O2` codegen is part of what's being tested. The
   next win would need birl's ToC to emit the runtime as a separately
   precompilable object.

Measured strategy contributions (200 progs, seed 9000, jobs=9):
baseline 4.90 prog/s -> server only 6.71 (1.37x) -> cbatch only 6.13 (1.25x)
-> both naive 9.31 (1.90x) -> + warmup + limiters/admission ~17.2 (3.5x).

`--no-server` / `--no-cbatch` restore the spawn paths exactly (also the old
core-budget scheduling) — use them to bisect infrastructure bugs from real
findings, and for per-strategy measurements. `--profile` prints a per-phase
breakdown (phase totals include queue waits; throughput is the number that
matters).

## How to extend

- **New shape**: write `gen_x_program(g: Gen): ShapeOut` ending in
  `finish_tail`/`prog_src`, add a `SHAPES` entry, rebalance weights to 1000.
  Decide `linear` honestly. If it emits new global helpers, route them
  through `prelude()` detection.
- **New type kind**: add the `Ty` variant, then cover ALL of: `ty_str`,
  `ty_eq`, `ty_print_safe` (be conservative), `gen_type`/`gen_composite`
  (and `gen_print_type` if print-safe), `gen_value`, `reduce_expr` or an
  `ensure_reduce` arm, `transform_expr` (pass-through is fine),
  `num_leaves`, and decl registration via `reg_decl` if it declares types.
- **New metamorphic transform**: must be meaning-preserving *by construction*
  from the generator's own knowledge (not from a semantic model — that was
  explicitly rejected as a new trust source). Follow the MIN_PARENS pattern:
  a global mode flag consulted only at string-assembly sites, same RNG
  draws, compare on one backend with exact equality. Candidate next
  transforms: redundant `(e :: T)` annotation insertion (generator knows the
  types), identity-lambda wraps, alpha-renaming via a `fresh` prefix mode.
- **Validation recipe after touching the generator**:
  1. `bun devs/_fuzz_.ts 400 --seed N` — all 15 shapes appear in tallies,
     0 fails, rejects ~0-1.
  2. Paren equivalence: `--dump` vs `--dump-min` identical after
     `tr -d '()'` across ~30 seeds.
  3. Injection sensitivity: flip `"^": 9` to `"^": 2` in `BIN_PREC`, expect
     ~13-16 METAMORPHIC findings per 250 seeds; revert.
  4. Feature frequency: dump a 150-seed corpus and grep markers
     (`:: String`, `Poly[0-9]`, `Idx[0-9]`, `rewrite pf|Equal/cast`,
     `Tl[0-9]*/go`, `Array/drop`, `/bind(`) — each should appear in roughly
     5-25% of programs.
  5. After infra changes: per-shape tallies byte-identical between default
     and `--no-server --no-cbatch` on the same seeds.

## Deliberate non-refactors (don't "fix" these)

- **String building, not an AST + printer.** Each shape reads as the Bend
  text it emits; an AST layer would be larger, hide the emitted syntax, and
  risk silently shifting the generation distribution (invisible coverage
  loss). The paren hazard is already contained by `bin`/boundary wrapping.
- **`gen_knum`/`gen_kf32` duplicate a restricted `gen_num`** (~70 lines) for
  Metal-safe expressions (no Nat, no transcendentals, no helpers/HOFs).
  Folding them into `gen_num` means threading a feature mask through its
  tuned probability branches — worse than the duplication.
- **`g.uid = 0` resets before main generation** in several shapes keep
  main-local fresh names short and stable; helper/def names already emitted
  use distinct prefixes. The prefix choices avoid shadowing ("el" not "h",
  "ac" not "a" — comments at the sites explain each).
- **Module globals** `CUR_ADTS`/`ADT_UID`/`NO_NUL` are reset at
  `gen_program` entry; `MIN_PARENS`/`LAST_OP` are global on purpose (the
  regeneration trick). Threading them through `Gen` is churn without
  behavior change.

## What the fuzzer cannot find (by design)

- **Common-mode front-end bugs** beyond what the metamorphic leg covers: all
  backends share one parser/elaborator/lowering, so a consistent wrong
  meaning produces no cross-backend diff. (This is how the ignored
  constructor-field-labels bug survived; see
  `devs/issues/constructor_field_labels_parsed_but_ignored.md`.)
- **Natives that are wrong the same way everywhere**: interp/JS/C all
  shortcut named Nat helpers; unanimous error matches, only the base asserts
  test them against the spec.
- **Compile-time-only machinery**: rewrite, definitional equality, totality,
  synthesis never execute in a fuzzed program. The SGen HVM checker is a
  fourth implementation the fuzzer never touches
  (`devs/issues/sgen_hvm_checker_numeric_semantics_diverge.md`).
- **Checker bugs in either direction**: rejects are skipped, unsound accepts
  only surface if they cause runtime divergence. A checker-differential
  fuzzer (TS checker vs SGen HVM checker on the same programs) would cover
  this; it does not exist yet.
