# bend2-core bugs found by the fuzzer

Every class of bend2-core bug the fuzzer has reached, from the rewrite for
bend2-core (2026-09-01) to the Bend port (2026-09-27), with the finding
kind, the repro under `repros/` (kept beside the checkout, not in the
repository) and the status. **Rechecked** marks a
status verified on 2026-09-27 against bend2-core `af569d48` (2.0.31) by
running the repro (check, `-o` to C and JS, clang, the C binary, bun, the
interpreter); the rest carry the status of the triage that last saw them
(`NOTES.md`, the `TRIAGE-*.md` files).

## Open

1. **An open Array element type** (`compiler-crash`). An Array whose
   element type is an equality, or reaches the emitters open (Base's Array
   helpers called at a type variable), kills both emitters with "an open
   Array element type"; the checker and the interpreter accept it.
   `comp_array_of_equality.bend`. Rechecked: open. The Bend port's first
   1,000 seeds reached it again (seed 7141).
2. **The bracket wall** (`cc-fail`, class D/K2). One expression of more
   than 85 nested binary ops: each `U32_BIN` expands to three parenthesis
   levels and clang stops at 256. `c_bracket_wall_expr.bend`. Rechecked:
   open. (The let-bound chain of the same class, `c_bracket_wall_chain`,
   is fixed.)
3. **A namespace equal to a Base family prefix captures names**
   (`raw-reject`, F2). A file named `Word.bend` resolves bare names into
   Base's (`Nil` becomes `Word.Nil`). `ns_base_prefix_capture/`.
   Rechecked: open.
4. **An alias equal to the file's own namespace is ambiguous**
   (`raw-reject`, F4). `import ./m.bend as m`, then `m.f()`: "an
   unambiguous name (the alias m shadows m.f)". `alias_is_own_namespace/`.
   Rechecked: open. The Bend port's 3,000-seed validation reached it twice
   (seeds 20781, 20795).
5. **A nested match with a later list-literal row** (`raw-reject`, F5).
   Refused as "an undestructed scrutinee".
   `check_nested_match_later_literal.bend`. Rechecked: open.
6. **`Array.set(..);` swallows the next row** (`raw-reject`, F6). The
   statement parses as the write `a = a[i] <- v; ..` and eats an inline
   match's next row. `parse_array_set_swallows_row.bend`. Rechecked: open;
   the diagnostic is now "expected Array<U32>, observed non-inferrable
   term".
7. **A large string literal overflows the compiler's stack** (found by the
   port). `-o` on a program with a 24 KB literal fails with "the machine
   stack overflowed (a deep recursion, or a literal too large to expand)";
   the interpreter runs it. A string literal expands to one nested chain.
   Rechecked: open.
8. **`F32.show` rounds exact ties differently** (`leg-diverge`, K1): C
   prints `417.70312`, JS `417.70313`. Open at the 2026-09-24 run; no repro
   file.
9. **An arity over 255** (`compiler-crash`). A segment with more than 255
   live words (a list literal of ~550 calls) overflows the emitter's `u8`
   arity table (`FID_ARITY_T`) in `compile_tables`. Widening the table to
   `u16` is the patch. A finding since 2026-09-21; not rechecked.
10. **A `+` field binder in a braced pattern, then a nested pattern in the
    same column** (`raw-reject`): "an annotated term (cannot infer)"; the
    checker's `match_flatten` and the `+` rebinding let. Fix proposed, not
    applied (2026-09-18, seed 4616053580496162079); not rechecked.
11. **A `!` reaching `F32.show` or `F32.read` fail-stops on the GPU**
    ("a function the device does not hold"). The device stubs hold no F32
    printing or parsing; a compiler fix was proposed (2026-09-18). The
    fuzzer counts it as the skip `metal-host-only`.
12. **`Nat.read` never finishes in the interpreter.** Its overflow guard
    divides with Base's unary `Nat.divmod`, an accumulator loop, so no
    digit is observable before 2^48 steps; native on the compiled lanes.
    The fuzzer keeps it off the interpreter's side (open since bend2-core
    `77eff95`, 2026-09-08).
13. **A C-SEQ `memory fault` on tiny pure mains** (23 findings on
    2026-09-16, never reproduced: 300+ reruns of the same binary pass).
    Fits a first-touch fault of the `MAP_NORESERVE` pool under memory
    pressure; left open.

Reviewed runtime limits, counted as skips: `js-char-scalar` (a Char past
U+10FFFF or a surrogate stops the JS runtime), `nat-immediate` (a Nat past
2^48-1 stops both runtimes; the spec's Nat is unbounded), `resource-fault`
(memory exhausted on every leg).

## Fixed

Rechecked on `af569d48`, the repro now agrees on every lane:

- **F1 `Bool.or`/`||` and `Bool.xor` read a boxed Bool as 0/1 in C**
  (`leg-diverge`, the most frequent class of the 2026-09-24 run).
  `comp_bool_or_boxed_operand.bend`, `..._scrutinee.bend`,
  `comp_bool_xor_boxed_operand.bend`.
- **family-arm-layout**: a family whose arms have different runtime
  layouts, read per arm, died in the C emitter with "a layout mismatch" or
  "a constructor outside its layout" (`compiler-crash`).
  `comp_family_arm_layout_sig.bend`, `..._2`, `comp_family_arm_ctor_layout`,
  `comp_family_arm_char_layout`.
- **K, a list literal of hundreds of calls, emitted in 80 s**: now 0.8 s.
  `comp_call_chain_cliff.bend`.
- **D, the let-bound flat U32 chain past the bracket wall**.
  `c_bracket_wall_chain.bend`.
- **A def whose only parameters are erased, its body a call, let-bound**
  crashed carbonize (a regression of the comp.ts rewrite).
  `comp_erased_only_call_cut.bend`.
- **Quadratic prologue loads in a wide fork** (14,950 loads at width 100).
  `comp_fork_step_loads.bend`.
- **An intrinsic result laid out as a box when its type is unknown**.
  `comp_intr_bool_layout.bend`.
- **Metal: a `!` loop next to a forking `!` def computed `%` wrong**
  (`batch-only`). `comp_metal_two_bangs.bend` now prints the C value on
  the device. The standalone `metal_urem_const/repro.m` is Apple's Metal
  compiler folding a constant dividend near 2^32.

Fixed by the record of their triage (each with a regression test in
bend2-core; the repros predate the 2026-09-05 operator grammar and no
longer parse):

- **B** the carbonizer lifted calls out of erased constructor fields
  (117 findings); **C** erased-arrow function values kept their erased
  applications; **E** a `+`-shared value of a flat type, boxed by its
  producer, freed on every read (`c_double_free_shared_*`); **H** a null
  let value reached `bind_uses` after a two-step unfold
  (`comp_unused_param_call_null`); **I** a cut's frame sank a word its call
  still borrowed, use after free and C livelock
  (`c_shared_read_then_drop_hang`) — the 2026-09-04 run.
- **F** a big literal emitted as straight-line allocations made clang
  superlinear (cc-timeout).
- **J** an intrinsic took a packed Term as its word
  (`comp_intr_boxed_arg`); **L** a packed constructor argument hid the
  uses under it, "an unbound binder" (`comp_use_in_lent_pak`); **M** a
  fused lent literal's "0" word entered the borrow set
  (`comp_fuse_lent_literal`); **N** a borrow mark followed an overlaid
  word into another arm (`comp_overlay_borrow_word`) — the 2026-09-07 run.
- **P** a packed constructor literal built from a variable, "an unbound
  binder" in the C emitter (`comp_packed_ctr_var_arg`, bisected to
  `8627c94`) — the 2026-09-10 run.
- **rwt-binder-loss**: a rewrite in statement position dropped the
  bindings crossing it (`comp_rwt_*`); **bang-alien**: a `!`-marked call
  aborted with "an alien request" (`c_bang_alien_request`); **erased-arrow
  application** (`comp_erased_arrow_*`); **a packed constructor over a
  Char field** ORed tag bits into the word, C livelock
  (`c_livelock_closure_map`) — fixed 2026-09-01 to 2026-09-05.
- **A peel pattern in a def returning a Char** (BigInt parse),
  **a Fail bound in a do-block over Result** (`arm.k` of undefined),
  **a parallel let passing a family value to a dependent parameter** ("a
  fork's paths hold different values") (`comp_peel_char`,
  `comp_do_result_fail_bind`, `comp_fork_family_arg`), 2026-09-16.
- **`lay_of` recursed forever on the emitter's name-keyed memo left by a
  previous program** in the same process (2026-09-18): the CLI emits one
  book per process, so only an in-process harness meets it; the fuzzer
  took a fresh emitter instance per emission.

Not rechecked, repro in the old grammar: `comp_clo_packed_arg.bend` (a def
used as a closure value read an enum-like packed argument as a boxed term,
so every arm dispatched as the first constructor), `comp_erased_field_call`
(C: "an under-applied def value").

## Not bend2-core's

- **Apple clang 17 crashes at `-O0`** ("live register clobbered by
  inserted prologue instructions", F3); the legs pass `-fno-stack-check`.
- **Apple's Metal compiler folds `4294967295u % d` wrongly** for a constant
  dividend within 128 of 2^32 (`metal_urem_const/repro.m`).
- **"`__defineSetter__` is an import's alias"** (the TypeScript fuzzer,
  seed 15733518094780353156): a duplicate declaration named with the
  wrong reason, because the TS worker passes `parse_book` a plain `{}` as
  its alias table and `a in p.al` finds `Object.prototype`'s keys. The CLI
  names the duplicate correctly.

## The bend3 era

The fuzzer's 2026-08-08 run on bend3 (`repros/README.md`, a different
language) found the bracket wall, a compiler stack overflow on
`case 3000+k:`, an F32 off-by-one between the interpreter and C, "fork
leaf without a continuation call", a template def refused as a function
value, and an unrendered `seq_apply_`. They are kept for the record;
bend2-core does not share that code.
