# Fuzzer maintainer notes (`fuzz.ts`)

The long doc comment at the top of `fuzz.ts` is the design spec — what is
generated, which legs run, and why each invariant exists. This file holds
what does NOT belong in the spec: history, validation recipes, the current
known-noise sources, and the reasoning behind non-obvious structure. Read
both before restructuring anything.

## History

The fuzzer began life as a Bend2 backend fuzzer, was rewritten from scratch
as `.devs/scripts/fuzz.ts` inside the bend3 repo (goal-directed synthesis
replacing the old shape tables), and moved out to this sibling repo in
August 2026. On 2026-08-04 it was rebased onto the post-rewrite language
(the "bend5 swap", bend3 commits `5bb34766`/`0c5cf10c`, plus everything
through `200bc799`). That rebase changed, in step with the language:

- **Quantities**: `+T`/Rco types, `+x` binder sigils and `-+>` arrows are
  gone from the language; the generator's whole rco type kind, the
  share/claim coercions and shared (`[:+T]`) arrays died with them.
  Contraction of concrete Data values is inferred (copy$/borrow) and is
  generated on purpose; contraction at ABSTRACT types is still refused by
  the checker, so tvar-typed binders stay strictly linear ("once").
- **Builtins**: unary builtins are `$`-spelled (`$sqrt(x)`, `$f32_to_u32`);
  `atan2` became the binary operator `~/` at `*`-precedence.
- **Oracle**: the reference interpreter runs the CHECKED book — `book_check`
  elaborates in place, and elaboration carries meaning (the Bool truth
  bridges evaluate only elaborated), so the old parsed-book oracle and the
  parsed-vs-elaborated differential are gone.
- **Modules**: imports never bind bare content names (only ctor tags
  travel), so the module-split leg rewrites cross-file references to their
  qualified `mod::name` spelling (`mod_qualify`, sound because generated
  names are uid-unique). A seed that minted a do-monad skips the split:
  `do M<..>:` derives `M::bind` from the TYPE's spelled name, which cannot
  straddle a file boundary.
- **Effects**: the ratified Op ruling admits only hand-written `IO::Op`
  rows, so the per-seed C-bodied effect ABI (`io_ffi`), the opaque-Data
  roundtrip (`io_opq`) and the in-process C leak probe are all dead. The
  pgrep orphan sweep survives and remains the only leak detector.
- **Sizes**: the clang 256-bracket wall died (`term_cexp` binds a temp
  every 64 nesting levels; `term_lit` compiles constant 17+-word subtrees
  as static data), so list/string literal caps were raised to the low
  thousands ON PURPOSE and the 64-name combine chunking was deleted.
- **Rewrites**: a motive is a function now (`%e : w => P(w)`; `_` holes are
  parse errors), and an explicit motive in statement position must end in
  `;` — the motive term parse is greedy and swallows a parenthesized next
  line as its application. The ford kit's as-equation identity casts became
  ill-typed (the split specializes the hypothesis in context by itself) and
  were replaced by direct use.

The **2026-08-06 migration** (onto the src-split / dotted-names compiler,
bend3 through the do-bind-elem + f32-fold fixes) changed more, since the
whole surface syntax moved and much of the above is now itself stale:

- **Compiler location + API**: the checkout is `bend-ts/src/{bend,comp}.ts`
  (was `bend-ts/bend.ts`). The worker imports both, uses `parse_file`
  (FS-only — each request's sources are WRITTEN into a per-pid scratch
  `ROOT/.fz-w<pid>/`, a direct child of ROOT so a `../bend-base` import
  resolves), `book_check` (no BendError class — a checker fail is a plain
  `{$:"Err"}`), and `comp.book_compile` with a C-effect reader that serves
  `./bend-base/IO/effs/*.c` from ROOT. Main owns the scratch lifecycle and
  wipes the whole `.fz-w*` glob at startup and on every exit signal (a
  SIGKILLed worker cannot clean its own dir).
- **Application syntax → PARENS**: `T<A,B>` type application and
  `f<A,B>(x)` generic calls became `T(A, B)` and `f(A, B, x)` (call-site
  type args lead the value args). DECLARATION heads keep their `<A>`
  binders (`type D<A>:`, `def f<A>(..)`). `::` qualification is gone —
  dotted names, and NO module namespaces (entry names are global across
  files), so `mod_qualify` is the identity and the module split is a pure
  file cut. `IO<A>`/`Chan<A>` → `IO(A)`/`Chan(A)`. The io templates are
  normalized wholesale by `io_parenify` (a balanced-angle rewrite, safe
  against the object language's spaced `<`/`>` comparisons and `def`/`type`
  decl heads).
- **Builtins are DOTTED, not `$`**: `F32.to_u32`, `U32.to_f32`,
  `F32.sqrt/sin/cos/tanh/exp/log/floor` (the `$`-spelled forms are gone).
- **op2 no longer ASSOCIATES**: an op2 operand is ALWAYS parenthesized —
  `e_in` parens unconditionally, `PREC` survives only as the op-identity
  table, and MIN_PARENS now varies ONLY the statement-head position (def
  body / let value / return). Equation SIDES are operand position, so they
  parenthesize in both modes (a bare op2 side is a min-parens-only reject —
  the one metamorphic finding of the migration).
- **Ctors, equations, arrays, values**: ctor patterns and literals are
  `Type.Ctor{..}` qualified; `{a = b : T}` → `{a == b : T}` and `{=}` →
  `{==}`; `assert` uses `forall` (not `for all`); array literals are
  `![k: v, _: d; n]` (the `!` prefix); `U{}` → `Unit.U{}`; inline
  annotations are `(v : T)` and let annotations `x : T = v` (the `{v : T}`
  brace form is dead); parallel-let is `a & b = x & y`; char literals are
  U32 codepoints (backtick chars gone); dependent arrows `@z:U32 -> F(z)`.
- **do-notation is monad-generic** at HEAD (`do M(..)`), so a user
  Result-over-IO transformer works; the do-bind element resolver
  re-instances alias-spelled types (bend3's elab_bnd), and `return` reaches
  match/if arms inside do-bodies.

## Invariants (violate = silent coverage loss or reject noise)

These are stated precisely in the `fuzz.ts` header; the short list, because
every one of them has been broken at least once:

- `gen(seed)` consumes RNG draws identically regardless of flags. MIN_PARENS
  and the module split are consulted only at string assembly; the flat twin
  and the min-parens sibling must denote the same book.
- Programs terminate by construction; recursion lives only in the minted
  scaffolds, descending argument first.
- Nothing is dead code: every generated sub-value folds into main's U32
  through `num_combine` (the deliberate exceptions: dead defs/lets, emitted
  rarely and marked).
- Defs are emitted in creation = dependency order; the module split takes a
  PREFIX of that order, which is what keeps it closed.
- Names are `<letters><uid>` and globally unique — batching (disjoint uid
  ranges) and `mod_qualify` (word-boundary replacement) both lean on this.

## Known noise and open compiler bugs (2026-08-06)

Remove entries here when the bends are fixed — every live finding class
drowns real signal:

- ~~`c-diverge` f32-generic-field~~: FIXED. The original
  `comp_generic_f32_field_lost` (a tvar field instantiated at F32 in a
  non-final slot lost its payload compiled) was fixed for the DIRECT
  match-opens (comp's `ctr_fty` at pend_open_take + the spun head-arm),
  but this fuzzer's first post-migration run caught the INCOMPLETE half:
  a tvar-F32 field read in the SAME arm that recurses flows through the
  fold's synthesized continuation (`term_leaf_clo` → `term_tree_chain`),
  which bound arm fields at the ctor ROW Ty. `List(F32)` is the everyday
  trigger, so the class fired at ~4%. Fixed by re-instancing at
  `term_tree_chain` too (prep's `ctr_fty`, now the shared law); pinned by
  bend3 `compile_generic_f32_fold.bend`. 300 seeds clean.
- `compiler-crash` stage=comp on big dec patterns
  (`case 3000+x:`): STILL OPEN — verified at HEAD, `--compile`
  stack-overflows ("Maximum call stack size exceeded") on a `K+x` peel
  chain around K=2000-3000. The bracket-wall half was fixed; the
  book_compile per-peel recursion was not. NOTE: the issue FILE
  `comp_dec_switch_bracket_wall.md` was DELETED in a bend3 cleanup with
  only the bracket half recorded as fixed, so this live bug currently has
  no tracking issue — worth refiling. The generator still draws K up to
  4000 on purpose (valid code; findings vanish when the chain compiles
  iteratively).
- `trans-ulp` skips: F32 transcendentals are each backend libm's float
  routines by ruling; a `trans`-flagged program keeps every leg except the
  value comparison (counted skip, kept out of merged folds).

## What it cannot find (by design)

- Common-mode front-end bugs beyond the metamorphic leg (one shared front
  end; a consistent wrong meaning makes no cross-leg diff).
- Nondeterministic interleavings: the losing branch of every generated race
  is silent and never completes, so bugs needing two fibers to finish in
  the same scheduler turn are out of reach of an exact-stdout oracle.
- Timer-heap leaks that never hold a process (the C probe died with the Op
  ruling; the orphan sweep only sees processes).
- ASan/UBSan, CUDA, `--no-halt`, contraction at abstract types, recursion
  on Ford evidence (refused by ruling).

## Coverage gaps flagged during the 2026-08-06 migration (not yet added)

Candidate generator work, in rough value order — each is a shape the
current generator does NOT emit but the language now exercises:

- **`fname`-macro collisions** (`comp_fname_system_macro`, OPEN): a def
  named `lock`/`ok`/`test` compiles to `F_<UPPER>` and collides with a
  `<unistd.h>`/`<fcntl.h>` macro, dying in clang after the checker said
  yes. The fuzzer STRUCTURALLY cannot hit it — every generated name
  carries a uid suffix (`lock38` → `F_LOCK38`, no collision). It DOES
  reach clang, so a rare bare-word name mode drawing from the F_* danger
  lexicon (solo runs, no batch) would catch this class.
- **`io_prebind` shape** (fixed `e0b32fcf`, found by BendQuest not the
  fuzzer): a pure projection let BEFORE an effect bind, whose argument
  uses split across the bind. `--io` never emits it; it should.
- **Bool-condition `if`**: at HEAD `if` takes both U32 and Bool
  conditions. If the generator only emits U32 guards, the Bool-condition
  checker path (`term_check` Swi arm) is untested outside the truth-if
  helper.
- **Metamorphic axis replacement**: min-parens is nearly the identity now
  (op2 always parens), so the parser-differential leg lost most of its
  reach. The do-bind-elem fix makes ALIAS-RESPELLING a lawful metamorphic
  transform (respell a type through definitional alias levels — same
  book, different spelling); that is the natural replacement axis.

## Worker scratch (2026-08-06)

Each worker writes its request's sources into `ROOT/.fz-w<pid>/` — a
DIRECT child of the checkout root, so a generated `import ../bend-base/X`
resolves to `ROOT/bend-base` (one level ONLY; an umbrella subdir breaks
that relative path and every program raw-rejects on the missing import).
Main owns the lifecycle: it wipes the whole `.fz-w*` glob at startup and
on exit/SIGINT/SIGTERM/SIGHUP, because a SIGKILLed or timed-out worker
cannot clean its own dir and a stray `.fz-w*` fails bend3's repo gate
(untracked-entry check).

## Validation recipe after touching the generator

1. `bunx tsc --noEmit` in this repo — clean.
2. `bun ../bend2-fuzzer/fuzz.ts --smoke` and `--smoke --io` from the bend3
   root — all pass, no `smoke missing features` line. The smoke seeds are
   hand-picked per generator version (a greedy set-cover over the first few
   thousand seeds against `smoke_need`); re-pick them after any edit that
   remaps seeds.
3. Paren equivalence: `--dump` vs `--dump-min` identical after `tr -d '()'`
   across ~10 seeds.
4. A few hundred seeds: rejects and crashes should be ZERO — every reject
   is either a generator bug or a checker bug, and both are findings worth
   a look before dismissing. c-diverge findings are expected while the
   bugs above are open.
5. `--metal` on a handful of seeds if touching anything the GPU leg sees.

## Performance notes

- Batching (`--batch`, default 16) merges N seeds into one program per
  compiled binary: one clang run over a translation unit that is ~90%
  identical across seeds, and one ~110ms macOS first-exec instead of N.
  The rotate-xor fold of member answers is a bijection in each argument,
  so one wrong member always changes the batch answer; attribution re-runs
  members solo at uid base 0, so saved findings reproduce under a bare
  `--seed N`. A batch failing with no failing member is itself a finding
  (`batch-only`: the merge is at fault).
- The worker pool (`--pool`) keeps warm bun processes speaking a JSON-line
  protocol; a timeout kills and replaces the worker. Requests are strictly
  one-in-flight per worker.
- `--profile` prints the per-phase breakdown; phases overlap under
  concurrency, so ratios matter, not sums. Wall-clock swings ~2x with
  background load.
