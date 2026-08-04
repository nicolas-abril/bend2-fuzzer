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

## Known noise and open compiler bugs (2026-08-04)

Remove entries here when the bends are fixed — every live finding class
drowns real signal:

- `c-diverge` (~5% of seeds): bend3 issue
  `.devs/issues/comp_generic_f32_field_lost.md` — a multi-ctor generic
  datatype whose ctor has a tvar field instantiated at F32 in a non-final
  position loses that field's payload in the compiled leg. Found by this
  fuzzer during the rebase; fires often because the generator loves exactly
  that shape.
- `metal-leg` LAUNCH failures: `.devs/issues/gpu_drop_join_body_pruned.md`
  — the device dispatcher keeps `F_DROP_JOIN_*` rows whose bodies the
  GPU-reachability pruning dropped, and the gpu source is compiled at
  launch, so the binary dies at startup.
- `compiler-crash` stage=comp RangeError on big dec patterns:
  `.devs/issues/comp_dec_switch_bracket_wall.md` — the clang bracket
  wall half of this issue is FIXED (flat leaf_inline emission +
  function-wide local-name registry, 2026-08-04), but book_compile
  still recurses per `K+x` peel and stack-overflows between K=2000 and
  K=3000. The generator keeps drawing K up to 4000 on purpose (valid
  code; the findings disappear when the chain compiles iteratively).
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
