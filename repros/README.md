# Minimal reproductions — 2026-08-08 triage

One self-contained program per root cause from the overnight run
(`TRIAGE-2026-08-08.md`). Every repro was verified against bend3 HEAD
(`da1a5913`) on 2026-08-08 from THIS directory. `bend` below means:

    bun ../../bend3/bend-ts/src/bend.ts

## bracket_wall.bend — c-leg, 103 findings

    bend bracket_wall.bend -o ./x.out
    # clang: fatal error: bracket nesting level exceeded maximum of 256

A flat left-nested `+` chain of 258 members, LET-BOUND and then used.
The let-binding is the trigger: `r = (((...))); (r + 1)` takes the
unboxed scalar emission path (`u32 v_r = (((...`), which has no
chunking; the identical chain in tail position takes the boxed
`term_u32_add` path where the every-64-levels temp binding chunks it,
and compiles fine. Threshold: 258 members fail, 250 pass. Everything
else in the original findings (forks, mixed operators, defs) is
optional — the chain members can even be literals bound by plain lets.

## dec_switch_overflow.bend — compiler-crash, all 86 findings

    bend dec_switch_overflow.bend --compile
    # RangeError: Maximum call stack size exceeded.

`case 3000+k:` — the known open per-peel recursion (NOTES.md). One root
cause for every RangeError finding in the run: the 14 findings that
looked small-K hide their big-K def in an `fm*` module sibling, and
minimization proved K essential each time it was checked. Two crash
sites, same cause: `book_compile` emission, and prep's need analysis
(`def_leaves_go → def_leaves_chain → def_need → need_seq`). Seeds with
K near the threshold are flaky across runs. Needs its bend3 issue
refiled (the old file was deleted with only the bracket half fixed).

## f32_c_diverge.bend — c-diverge, 35 findings

    bend f32_c_diverge.bend --eval    # interp : 4294966236
    bend f32_c_diverge.bend -o ./d.out && ./d.out   # binary : 4294966235

Interp and compiled binary disagree. Minimized from seed
`10482279896652563345` (oracle 2966087 vs 1126377757); the shape that
survives minimization: a generic type with an ERASED `List(Char)` field
(`D0a{-f0: ...}`), instantiated at F32 and at `(F32 & F32)`, a
`(List(F32) & D0(F32))` tuple built in one def and consumed in another,
and `F32.to_u32` arithmetic over the list elements. Off-by-one in the
final U32 — consistent with an F32 word-classing sibling of the
`3fe899d1`/`8dab9c5a` family. All 35 findings contain F32; 33 use
`F32.to_u32`.

## fork_leaf_no_continuation.bend — compiler-crash, 20 findings

    bend fork_leaf_no_continuation.bend --compile
    # Error: fork leaf without a continuation call   (prep.ts fin_of)

Survivors of minimization, each necessary: a RACING array store chain
(`![...]` array, `ar5@ar6[11] <- ...` then `ar6[0] <- ...`), a match
returning a closure which is immediately applied
(`(ku42(...))(y => 1)`), and a combine that reads the stored value
(`rd8(v7)`) — the fork group's continuation ends up not being a direct
call, violating `fin_of`'s precondition.

## template_value_reject.bend — raw-reject, 24 findings

    bend template_value_reject.bend --eval
    # Error: expected U32 -> F32, observed @~p0:U32 -> F32

Eight lines: a def with a `~` template parameter passed by name as a
first-class function argument. Checker or generator bug depending on
the ruling for `~`-templates as values.

## seq_apply.bend — c-leg, 5 findings

    bend seq_apply.bend -o ./x.out
    # clang: call to undeclared function 'seq_apply_'

The emitted C names `seq_apply_` — the seq body of prep's `apply$`
MARKER def (`$` → `_`) — but no such function is ever rendered: a
liveness/rendering gap for `apply$`. Fifteen lines, no fork needed
(the original seed's fork groups all minimized away). The surviving
trigger: a def returning a CURRIED closure whose innermost body is an
UNDER-APPLIED recursive def (`tl15` given 3 of its 4 args), with the
call result applied over-arity in main
(`(op55(...))(f32)(y => 1.0)(7)`). Both the tuple-typed param of
`op55` and the under-application are load-bearing — simplifying
`op55`'s params to plain U32 makes it compile clean.

## Not program-shaped

- **batch-only (3 findings)**: `bun ../fuzz.ts 1 --seed <N>` passes,
  the batch fails. The merged headers show WHY: "merged crash
  (compile): RangeError" / "merged skip (worker-timeout)" — the merge
  pushes the SAME threshold bugs (class 2's stack depth, the 20s worker
  budget) over the line. Threshold effects, not a distinct merge bug —
  expect them to disappear when class 2 and the timeout budget are
  addressed.
- **worker timeouts (86 skips)**: `bun fuzz.ts 1 --seed
  10039316440360362053` times out at 20s; the same program under a bare
  `bend --eval` finishes CORRECTLY in ~45s. So at least part of the
  population is an interpreter performance tail, not hangs — but a real
  hang would be indistinguishable in the skip bucket; sweep
  `findings/skipped/` with a 120s budget to separate them.

## Grammar note (2026-09-06)

main's operator grammar changed on 2026-09-05: an operator is a method
named by the `( .. : T)` frame around it, `+n` and the dotted F32 family
are gone, and `assert`/`forall` read `law`/`for`. Of the repros here only
`c_bracket_wall_chain.bend` (open class D) and
`c_shared_read_then_drop_hang.bend` (class I, fixed) are ported; the
rest, all fixed classes, still carry the old spellings and need porting
before they parse. Each fixed class has a regression test in bend2-core.


## 2026-09-07 run (bend2-core efead59 plus the nicolas3 fixes)

One repro per class of `TRIAGE-2026-09-07.md`, verified against
bend2-core from THIS directory with `bun ../../bend2-core/bend2/main.ts`:
`comp_intr_boxed_arg.bend` (J, fixed), `comp_use_in_lent_pak.bend` (L,
fixed), `comp_fuse_lent_literal.bend` (M, fixed),
`comp_overlay_borrow_word.bend` (N, fixed), `comp_call_chain_cliff.bend`
(K, open: emit time). Each fixed one crashes or diverges on efead59 and
matches the interpreter with the fixes.
