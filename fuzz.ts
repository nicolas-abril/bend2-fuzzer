#!/usr/bin/env node
// Differential fuzzer for the Bend3 runtimes. Each seed deterministically
// generates raw and identity-sealed siblings with a U32 main, checks both,
// and runs the sealed sibling on the TS interpreter (the language spec), the
// compiled C backend (clang, PAR_BACKEND=0), and optionally Metal
// (--metal, PAR_BACKEND=1, GPU-serialized). Every leg must equal the raw
// interpreter's decimal stdout. A
// disagreement, a crash in any backend, or a compiler rejection of a checked
// program or a rejection of generated source is a finding; resource blowups
// (timeouts, stack overflows) are persisted but not failures.
//
//   bun fuzz.ts [count] [--seed N] [--jobs N] [--threads N]
//     [--metal] [--io] [--opt N] [--dump] [--dump-min] [--dump-raw] [--no-meta]
//     [--keep] [--loop] [--smoke] [--check-only]
//
// Everything folds into one U32 scalar because that is the only value shape
// all three runtimes print identically. Every generated sub-value is folded
// into the result via `num_combine`, so nothing is dead code. Each seed emits
// a raw program returning that fold and a sibling sealed by one of several
// exact U32 identities; the raw interpreter result is the oracle for the
// sealed interpreter and backends, so a broken seal cannot bless itself.
//
// GENERATION IS GOAL-DIRECTED SYNTHESIS, not templates: the core is
// syn(goal, env, fuel) — "produce a term of type `goal`" — which assembles,
// per goal head, every production that is correct by construction (an
// in-scope var whose type matches, an intro form of the head, a call to any
// registered def whose return type UNIFIES with the goal, minting a fresh
// def that returns the goal), and picks one by weight. Types themselves are
// synthesis goals: syn_ty fills type holes (generic instantiations, +T
// wrappers, nested List/ADT applications), so polymorphic defs get
// instantiated at arbitrary generated types, and the same machinery reaches
// dependent territory to a degree: constant-family Sigma telescopes
// (`type Sg(A: Type, B: A -> Type):` with fields `a: A, b: B(a)`), equality
// datatype fields use syn_ty with their in-scope parameters and direct self
// type, rather than a separate field template. Typed Data values remain in
// main's synthesis environment after their independent U32 fold. Equality
// types with convertible sides ({e = e : T} proved by {=}), theorem defs
// whose statements mention their arguments, and live rewrites (`% th(n) e`,
// sometimes with an explicit constant motive `%e : U32`, sometimes in
// expression position inside an annotated let value)
// on main's critical path. Base List/Char are ordinary ADTs to the
// synthesizer (imported rather than declared). Every value ultimately folds
// to U32 through memoized per-instantiation reduce defs (rd_ensure), which
// the synthesizer can also mint mid-expression.
//
// Oracles and legs:
// - interp (spec): pooled `fuzz.ts --worker` children independently load,
//   check (halt ON; book_check elaborates IN PLACE) and normalize the raw
//   and sealed siblings on the CHECKED book — the CLI's own evaluation
//   path; the sealed request also emits C. The reference value is the raw
//   sibling's result, and the sealed result must equal it. A
//   parsed-but-unchecked book stopped being a lawful oracle when
//   elaboration started carrying meaning (the Bool truth bridges evaluate
//   only elaborated), and the old parsed-vs-elaborated differential died
//   with it. A checker reject or an
//   internal crash of the checker/compiler/normalizer on a generated program
//   is a FINDING; a worker
//   process DEATH (segfault/abort — detected via exit tracking, stderr tail
//   attached) is a FINDING, distinct from our timeout kill (skip) and a
//   system SIGKILL (OOM skip).
// - C (under test): the emitted .c built with the file_recipes cpu flags
//   (-O<--opt, default 3>) -DPAR_BACKEND=0 -DNUM_THREADS=<--threads, default 1>.
//   A RUN timeout here is a FINDING, not a skip: the interpreter already
//   finished this program (it's terminating by construction), and compiled
//   code is ordinarily far faster — livelock/perf-cliff suspect. Compile
//   (clang) timeouts stay skips.
// - Metal (--metal): the same .c as ONE objc build (-DPAR_BACKEND=1; the GPU
//   source is embedded and compiled at launch — no .metallib step), strictly
//   one GPU program at a time, run from its own directory. GPU work only
//   actually launches at `f!(..)` marks, which the generator emits with fixed
//   probability. All runtime diagnostics go to stderr; stdout carries only
//   the result.
// - metamorphic (parser oracle, on unless --no-meta): the same seed re-emitted
//   with minimal parentheses (same RNG draws, only string assembly differs)
//   and re-run on the interpreter; a reject or a different value is a parser
//   bug. This is the only leg that can see front-end bugs: the backends share
//   one front end, so a common-mode wrong meaning produces no cross-leg diff.
//
// Generator invariants (violate = silent coverage loss or reject noise):
// - Seed determinism: gen(seed) consumes RNG draws identically regardless of
//   flags; MIN_PARENS is consulted only at string-assembly sites; env
//   mutation (linear-use consumption) replays identically across modes. The
//   per-program Gen seeds through rng_mix64 — fuzz_run steps batch seeds by the
//   SAME golden gamma the Gen uses internally, so unmixed neighboring seeds
//   would emit near-identical shifted programs.
// - Programs terminate by construction: recursion lives only in minted
//   scaffolds (countdown 0-switches, structural folds over ctor-0-non-
//   recursive ADTs, uniform self-instantiation of generic ADTs), descending
//   argument first; synthesis holes never introduce recursion — an on-demand
//   minted def is non-recursive and only calls already-registered defs.
//   Defs are emitted in creation = dependency order.
// - Linearity: closures are strictly linear (env q: "once"), arrays are
//   threaded by the array scaffold and never enter env, and binders of
//   ABSTRACT (tvar) type are also "once": the checker refuses contraction
//   at abstract types (verified against HEAD), so generic bodies never
//   contract tvar-typed values. Everything else contracts freely -- since
//   the refcount removal an extra owner of a Data value is an inferred
//   eager deep copy (copy$) and a dominated read a borrow, and that
//   inference is a prime target.
// - Quantities: `+T`/Rco types and `+x` binder sigils are GONE from the
//   language (ruling B); generated binders are bare Lone or `-x` NONE --
//   an erased param a minted body may not consume, and an erased CTOR
//   FIELD (base's own Op is that shape). An erased field is skipped by
//   every fold (folding consumes it), re-passed untouched by ctor
//   rebuilds, and disqualifies its ctor from the one-word array-default
//   path; self fields stay live, since the structural fold walks them.
// - Non-inferable heads (ctors, list/char/string literals, lambdas, {=})
//   need checked positions: argument and field holes are checked; every
//   non-word let is annotated `{v : T}` (ty_str renders any T, functions
//   parenthesized); `match` never sits in a let value (fold through reduce
//   defs); IIFEs are not emitted.
// - Indentation is syntax: case rows deeper than their `match` token,
//   do-lines deeper than the `do` token, case bodies on a fresh line; an op
//   at line head never continues an expression (single-line exprs only).
// - match rules: literal word arms need a final var arm and must avoid
//   literals an outer switch already took (V.not tracks this along miss-
//   binder chains); computed scrutinees must be VARIABLE-HEADED (a constant
//   one normalizes at the check-time split and makes literal/ctor arms
//   unreachable rows); ADT matches cover every ctor; catch-all rows last;
//   matching a row var consumes it. Multi-scrutinee matches emit a full
//   rigid product.
// - Arrays: fixed capacity = least pow2 above the literal's keys (1 slot if
//   keyless), TOTAL over all u32 indices; defaults are one-word constants
//   (number / K{} / single-u32-field K{lit}) so only monomorphic ADTs with
//   such a ctor become elements; Get is WORD-ONLY (ADT arrays are
//   set-swap only, the set's yield is the displaced owned element);
//   keys > 65535 exercise the slab pool.
// - F32: dyadic literals in [1/8, 32]; unified arithmetic/comparisons plus
//   every float builtin ($-spelled op1s; atan2 is the ~/ Op2); division
//   uses a positive literal denominator and $sqrt squares its input.
//   $f32_to_u32 is total. Negated literals atom-only.
// - Equality sides are IDENTICAL renderings of one synthesized term (types
//   are erased, so occurrences there consume nothing and the sides convert
//   trivially) — EXCEPT the ceql coin: convertible-but-DISTINCT constant
//   sides ((a op b) vs its folded literal, TS mirrors probed exact), which
//   oracle the checker's evaluator through {=}. Rewrites consume their
//   equation, so eql lets feed the final term's rewrite chain.
// - Swarm + size: per-seed multipliers reshape the let-kind weight table
//   (rare kinds get seeds where they dominate); ~8% of seeds are HEAVY
//   (8-16 lets, deeper batch trees) to engage segment spill, slab churn and
//   task-bag pressure that uniform small programs never touch.
//
// Compilation surfaces deliberately stressed: copy$/borrow inference
// (param and statement contraction of Data values, drops), ctor-reuse
// (transform defs),
// borrow-fusion (word-field reduces), closures via partial application, HOF
// lambdas and closure-typed generic instantiation (apply$), computed-match
// splits (fn~i), parallel-let forks in main and recursive batch trees
// (fork law: >= 2 CALL siblings must number a power of two <= 32; value
// riders move free — mixed and rider-only lets are emitted on purpose), GPU
// marks (on SATURATED calls and on UNDER-APPLIED ones, where the mark has
// to survive into the runtime closure -- reg/346), the slab pool, literal
// sugar + base imports, generic ADTs and defs
// at synthesized instantiations, do-notation, dependent telescopes (Sigma),
// live rewrites (default and explicit motive, statement and expression
// position), lambdas at COMP (`~x`) params, if/elif, tuple/Unit sugar, dependent U32
// switches and filled asserts, dead defs/lets.
//
// Custom C-bodied effects are NOT generated: the ratified Op ruling
// admits only the hand-written IO::Op rows (a C-bodied def compiles only
// when its camelized name matches an install ctor), so the old per-seed
// effect ABI shapes and the in-process C leak probe are gone.
//
// The separate --io smoke mode checks generated standard-IO programs by
// their deterministic process output; the interpreter performs no
// effects, so these cannot use the differential oracle. It also generates
// CANCELLATION shapes -- timeout, race, spawn-and-drop, an explicit
// IO::cancel on a live handle, a cancelled channel sender/receiver, and a
// timed-out exec -- plus a WORKING channel (fz_pipe: a spawned producer
// over a cap-1 buffer, so whichever side runs first the other is parked
// and woken -- both rendezvous directions -- then a recv and a send after
// the close, for the end-of-stream Fail and the send-to-closed drop),
// IO::die (the one Op that reclaims NOTHING on its way out: no cancel
// walk, so whatever the seed left running rides entirely on io_run's exit
// teardown, and the exit CODE is the assertion -- leg_c and leg_metal take
// the expected code), and effects bound and DROPPED (now/now_ms/rand_word/
// args/get_env), whose values are nondeterministic so only their dispatch
// is under test.
// The losing branch obeys one rule that keeps that oracle exact: it is
// SILENT (io_quiet: a sleep no seed waits out -- io_never picks a spread
// of deadlines all far past the run cap, so io_timer_del's sift paths see
// a heap and not two clustered values -- and recursively a fiber that
// forks-and-joins, races two children, leaves a spawned sibling parked,
// parks on an fd, or holds a live process -- so the cancelled fiber owns a
// SUBTREE and parks somewhere other than a timer). All SIX of
// io_fib_cancel's named arms are reached -- FD, TIMER, THREAD, JOIN, SEND,
// RECV -- plus RACING/READY-with-children through the subtree walk. FD
// rides fz_fd: the harness hands every binary an open, EMPTY stdin pipe, so
// read_line parks and never answers; run a binary by hand under
// `< /dev/null` and it returns at once, silently costing that arm (output
// is unchanged either way, so nothing fails -- it just stops covering).
//
// A cancel that never fires costs no output. What it costs is a live
// process, read by the ORPHAN SWEEP after the binary exits: each
// cancelled/held exec carries a unique marker, and anything still
// answering to one after the binary is gone outlived the program.
// fz_hold exists to give the sweep something to find: an UNCANCELLED exec,
// so a live child rides every cancellation path and, under a spawn, dies
// only if the exit teardown runs. The sweep diffs against the pids matching
// before the binary ran, so a survivor of an earlier run of the same seed
// is not blamed on this one (markers are seed-derived, hence stable by
// design). The old in-process LEAK PROBE (timer-heap depth + waitpid
// WNOHANG spliced as main's last effect) died with the Op ruling -- it
// was a minted C effect -- so a leaked wait-set ENTRY that never holds a
// process is currently invisible.
//
// The ceiling: the loser NEVER completes, so no generated race is ever
// CLOSE. Bugs needing two fibers to finish in the same scheduler turn are
// out of reach by construction -- an exact-stdout oracle cannot admit a
// nondeterministic interleaving. Not covered yet:
// ASan/UBSan, CUDA, --no-halt, contraction at abstract types (the
// checker refuses it, so it is a language gap, not a generator one),
// timer-heap leak detection (the C probe died with the Op ruling), and
// recursive consumers of Ford evidence (recursion on the EVIDENCE
// column is refused by ruling; the minted eliminators are depth-bounded
// instead).
//
// Dependent types are ONE recipe-driven kit, correct by construction
// off pinned idioms. syn_dep mints a word-indexed family uf : U32 ->
// Type (large elimination) with pick : (n) -> uf(n) and the
// abstract-index transport hop, consumed at RUNTIME indices; by chance
// it instead couples the family to a dependent pair Sg(U32, z => uf(z))
// eliminated whole (sigelim), or passes family+section as VALUES
// through a higher-kinded consumer (-F: U32 -> Type erased, g: @z. F(z)
// a dependent-arrow arg, h: F(0) -> U32 an instantiation-typed
// continuation -- hkdep). syn_ford is the generic indexed-family kit:
// recipe axes are eq-field erasure (forde), a second passthrough index
// (fordm), the payload type, and the Sg coupling; every instance gets a
// word->index converter, a runtime-index builder recursing on the index
// (the split specializes intro goals), and an eliminator -- RECURSIVE
// when eq fields are live (the split specializes the hypothesis in
// context, the opener refutes its impossible arm and crosses the
// tail through injectivity, descent stays structural), SHALLOW when
// erased (evidence can neither refute nor transport, and recursing on
// evidence is refused by ruling); by chance the index is a COMPUTED
// term (vapp -- append answers V(ad(a,b)), so the checker converts
// index EXPRESSIONS), and folds peel d constructors per step (peel).
// theorem_gen mints add-right-identity or add's succ law (thm-shift),
// and its equation composes
// through sym/trans/cong (eqkit); asserts go bodiless by chance (axiom,
// referenced through a dead let: no computational content, a live %
// would wedge the interpreter). Closure-field datatypes (clofield)
// live outside the ADT model as dedicated intro/apply pairs.
//
// Arrows carry quantities: fun types are -> (Lone) or --> (None,
// erased), and None VALUES are minted defs passed by name (sigiled
// lambda binders are not inline syntax; qfun). Dependent arrows
// (@z: U32. F(z)) ride the dep kit as the section of a family.
//
// In io mode, IO is itself first-class (io_first/io_val): actions are
// built UNEXECUTED and flow through minted combinators whose contracts
// fix what runs and in which order -- run params splice their pending
// output, drop params discard it, IO<IO<T>> nests (ionest), ctor
// fields carry actions (iowrap), and (U32 -> IO<T>) continuations
// capture the live env (iokont). Minted do-block defs (doio) run
// multi-bind Bnd elaboration with bare statement lines (dobare). F32
// stays inside the implementation-agnostic fragment by construction:
// $sqrt(e*e), positive division and literal $exp/$log keep NaN/inf/-0.0
// out of every leg (the trans ruling's spirit), and new arms reuse
// those generators.
//
// BATCHING (--batch N, default 4 outside --io). Compiling one program per
// seed was 61% of the run, over a translation unit 89-95% identical across
// seeds -- the runtime, and in --io the emitted scheduler -- plus ~110ms
// per never-seen binary for macOS to validate the inode (against ~7ms of
// actual work). N seeds merge into ONE program: a CONCATENATION, not book
// surgery, because every generated top-level name is <letters><uid> and
// each member gets a disjoint uid range (test.ts's suite_book needs
// term_ren only because hand-written tests collide). `main` becomes bm<k>;
// fzdead was the one other fixed name and is now uid-derived.
//
// The batch's answer is a rotate-xor fold of its members' answers, which is
// a bijection in each argument -- one wrong member ALWAYS changes it -- so
// the whole batch stays a single U32 and the binary is exactly what bend
// emits from an ordinary program, with no driver surgery. A failure names
// the batch, so members are then re-run one at a time to attribute it, at
// uid base 0 so whatever they save still reproduces under a bare --seed N.
// A batch that fails when no member does is reported as batch-only: that
// is the merge at fault, not the compiler (verified by perturbing the fold).
// N=16 is the default. It used to be 4: the seq machine was ONE function
// per program, so merging made it N times bigger and clang's register
// coalescer (per-function, superlinear) went quadratic -- 471ms/program at
// N=8 against 115 at N=4. Since the machine became one function per LABEL
// (bend aa9948af/caa962b9) that cliff is gone: per-program clang cost is
// flat 112-179ms from N=4 to N=100, so bigger batches now win on the ~110ms
// per-binary first-exec they amortise. Re-measured end to end over 480
// programs: 21.0 / 22.4 / 21.8 / 22.1 / 22.1 per second at N = 8/16/24/32/48
// -- flat past 16, so 16 is the peak and a safe middle. --io stays unbatched: side effects, per-seed process markers and
// exit codes do not merge. --profile reports the phase clock behind all of
// this; note wall-clock measurements here swing ~2x with background load.
//
// Findings land in findings/seed-N.bend next to this file (program +
// verdict header), resource skips in findings/skipped/.
// The generator is version-controlled but findings are not: a saved program is
// the durable artifact (a generator edit remaps every seed).

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as readline from "node:readline";
import { pathToFileURL } from "node:url";

// ROOT : the bend3 checkout under test -- the cwd when run from the repo
// root, else the `bend3` sibling of this repo (the layout after the move
// out of .devs/scripts)
const ROOT0 = [process.cwd(), path.join(import.meta.dirname, "..", "bend3")]
  .find((d) => fs.existsSync(path.join(d, "bend-ts", "bend.ts")));
if (ROOT0 === undefined) {
  console.error("cannot find the bend3 checkout: run from its repo root, or keep it as a sibling `bend3/` of this repo");
  process.exit(1);
}
const ROOT: string = ROOT0;
const BEND_TS = path.join(ROOT, "bend-ts", "bend.ts");
const FINDINGS = path.join(import.meta.dirname, "findings");
const WORKER_TIMEOUT = 20_000;
const CC_TIMEOUT = 90_000;
const RUN_TIMEOUT = 15_000;
const METAL_CC_TIMEOUT = 300_000;
const METAL_RUN_TIMEOUT = 60_000;

// CLI
// ---

const argv = process.argv.slice(2);
export const cli_flag = (s: string): boolean => argv.includes(s);
export const cli_opt = (s: string, d: string): string => {
  const i = argv.indexOf(s);
  return i >= 0 && i + 1 < argv.length ? argv[i + 1] : d;
};
const VALUED_FLAGS = ["--seed", "--jobs", "--threads", "--opt", "--batch", "--pool"];
const COUNT = Number(argv.find((a, i) => /^\d+$/.test(a) && !VALUED_FLAGS.includes(argv[i - 1] ?? "")) ?? "100");
const BASE_SEED = BigInt(cli_opt("--seed", String(Math.floor(Math.random() * 2 ** 48))));
const JOBS = Number(cli_opt("--jobs", String(Math.max(1, Math.min(8, os.cpus().length - 2)))));
const THREADS = Number(cli_opt("--threads", "1"));
const WITH_METAL = cli_flag("--metal");
const WITH_IO = cli_flag("--io");
const NO_META = cli_flag("--no-meta");
const KEEP = cli_flag("--keep");
const PROFILE = cli_flag("--profile");
const BATCH = Math.max(1, Math.min(64, Number(cli_opt("--batch", WITH_IO ? "1" : "16"))));
const LOOP = cli_flag("--loop");
const SMOKE = cli_flag("--smoke");
const CHECK_ONLY = cli_flag("--check-only");

// Phase
// -----
// Concurrency means phases overlap and total more than the run: the point
// is the RATIO between phases and the per-call cost, not the sum.

const PHASE: Record<string, { ms: number; n: number; all: number[] }> = {};

export function phase_note(name: string, t: number): void {
  const p = PHASE[name] ?? { ms: 0, n: 0, all: [] };
  const d = performance.now() - t;
  p.ms += d;
  p.n += 1;
  p.all.push(d);
  PHASE[name] = p;
}

export async function phase<A>(name: string, f: () => Promise<A>): Promise<A> {
  if (!PROFILE) {
    return f();
  }
  const t = performance.now();
  try {
    return await f();
  } finally {
    phase_note(name, t);
  }
}

export function phase_sync<A>(name: string, f: () => A): A {
  if (!PROFILE) {
    return f();
  }
  const t = performance.now();
  try {
    return f();
  } finally {
    phase_note(name, t);
  }
}

export function phase_report(): void {
  const rows = Object.entries(PHASE).sort((a, b) => b[1].ms - a[1].ms);
  const tot = rows.reduce((a, r) => a + r[1].ms, 0);
  console.log("\nphase                 total(s)  calls  mean   p50   p90   max   share");
  for (const [k, v] of rows) {
    const a = [...v.all].sort((x, y) => x - y);
    const at = (q: number): string => (a[Math.min(a.length - 1, Math.floor(q * a.length))] ?? 0).toFixed(0).padStart(6);
    console.log(k.padEnd(20)
      + (v.ms / 1000).toFixed(2).padStart(9)
      + String(v.n).padStart(7)
      + (v.ms / Math.max(1, v.n)).toFixed(0).padStart(6)
      + at(0.5) + at(0.9) + at(0.999)
      + (100 * v.ms / Math.max(1, tot)).toFixed(1).padStart(7) + "%");
  }
}

// Rng
// ---

const M64 = (1n << 64n) - 1n;

export function rng_step(x: bigint): bigint {
  return (x + 0x9e3779b97f4a7c15n) & M64;
}

export function rng_mix64(x: bigint): bigint {
  let z = x & M64;
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & M64;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & M64;
  return z ^ (z >> 31n);
}

class Gen {
  state: bigint;
  constructor(seed: bigint) {
    this.state = seed & M64;
  }
  r(): bigint {
    this.state = rng_step(this.state);
    return rng_mix64(this.state);
  }
  int(n: number): number {
    return Number(this.r() % BigInt(n));
  }
  chance(p: number): boolean {
    return this.int(1000) < p * 1000;
  }
  pick<T>(xs: T[]): T {
    return xs[this.int(xs.length)];
  }
  wpick<T>(xs: Array<[number, T]>): T {
    let total = 0;
    for (const [w] of xs) {
      total += w;
    }
    let roll = this.int(total);
    for (const [w, v] of xs) {
      if (roll < w) {
        return v;
      }
      roll -= w;
    }
    return xs[xs.length - 1][1];
  }
  decay(p: number): number {
    let n = 1;
    while (this.chance(p)) {
      n++;
    }
    return n;
  }
}

// E
// -
// An E is a rendered expression plus the precedence of its top operator (99 =
// atom). MIN_PARENS is consulted ONLY here: full mode parenthesizes every
// binary node, minimal mode only where the parser's precedence table (PREC
// mirrors OPRS/PREC in bend-ts/bend.ts; every binary op is left-assoc)
// requires it. Both spellings denote the same tree — the metamorphic leg
// relies on exactly this.

let MIN_PARENS = false;

const PREC: Record<string, number> = {
  "||": 2, "&&": 3,
  "==": 4, "!=": 4,
  "<=": 5, ">=": 5, "<": 5, ">": 5,
  ".|.": 6, ".^.": 7, ".&.": 8,
  "<<": 9, ">>": 9,
  "+": 10, "-": 10,
  "*": 11, "/": 11, "%": 11, "~/": 11,
};

type E = { s: string; p: number; head?: string; op?: string };

export const e_atom = (s: string): E => ({ s, p: 99 });
export const e_defcall = (head: string, s: string): E => ({ s, p: 99, head });

export function e_at(e: E): string {
  return MIN_PARENS || e.p === 99 ? e.s : "(" + e.s + ")";
}

export function e_in(e: E, need: number, right: boolean): string {
  if (e.p === 99) {
    return e.s;
  }
  const bare = MIN_PARENS && (e.p > need || (e.p === need && !right));
  return bare ? e.s : "(" + e.s + ")";
}

export function e_bin(l: E, op: string, r: E): E {
  const p = PREC[op];
  return { s: e_in(l, p, false) + " " + op + " " + e_in(r, p, true), p, op };
}

export function e_fn1(op: string, x: E): E {
  return e_atom(op + "(" + e_at(x) + ")");
}

export function e_fn2(op: string, x: E, y: E): E {
  return e_atom(op + "(" + e_at(x) + ", " + e_at(y) + ")");
}

export function e_ann_bind(name: string, val: E, type: string): string {
  if (val.op !== "!=") {
    return name + " = {" + val.s + " : " + type + "}";
  }
  const raw = "an" + String(uid_next());
  return raw + " = " + e_at(val) + "\n  " + name + " = {" + raw + " : " + type + "}";
}

// Types (the generator's mirror of the object language)
// -----------------------------------------------------
// T is a synthesis goal. tvars appear only inside generic decl/def bodies
// and in registry signatures (unification binds them at call sites). eql
// carries ONE rendered side — both sides of the emitted type are that same
// string, so they convert trivially and {=} always proves it. A dep (Sigma)
// ADT's two "tvars" are the telescope A and the constant family's result:
// `Sg(A: Type, B: A -> Type)` instantiated as `Sg(T1, z => T2)`.

type T =
  | { k: "u32" }
  | { k: "f32" }
  | { k: "tvar"; n: string }
  | { k: "adt"; a: Adt; args: T[] }
  | { k: "fun"; dom: T; cod: T; q?: "none" }
  | { k: "io"; t: T }
  | { k: "eql"; t: T; side: string };

type TyHole = { vars: string[]; self?: T };
// er : er: the index of this ctor's ERASED field (-1: none). An erased
// field is bound at None wherever the ctor is matched, so nothing
// may consume it -- folds skip it and rebuilds re-pass it untouched.
type Ctor = { name: string; fields: T[]; er: number };
type Adt = {
  name: string;
  tvars: string[];
  ctors: Ctor[];
  rec: boolean;
  data: number[] | null;
  dep?: boolean;
  sugar?: "pair" | "unit";
};

const U32C: T = { k: "u32" };
const F32C: T = { k: "f32" };

let G: Gen;
let UID = 0;
let DECLS: string[] = [];
let DEFS: string[] = [];
let ADTS: Adt[] = [];
let LISTA: Adt | null = null;
let CHARA: Adt | null = null;
let PAIRA: Adt | null = null;
let UNITA: Adt | null = null;
let IMPORTS: Set<string> = new Set();
let REDUCES: Map<string, string> = new Map();
let RD_WIP: Set<string> = new Set();
let HEAVY = false;
let BUILDERS: Map<string, string> = new Map();
let BUILDER_WIDE: Set<string> = new Set();
let TRANSFORMS: Map<string, string> = new Map();
let SHUSER = "";
let SIDES: Map<string, string> = new Map();
let MINTS = 0;
let FEAT: Record<string, number> = {};

// er : er: index of this def's ERASED param, if any. It changes the ARROW
// (`-->`, not `->`), so a partial application that stops before it does
// not have a plain function type.
type DefR = { name: string; tps: string[]; ps: T[]; ret: T; mask?: Array<number | null>; er?: number };
let DEFR: DefR[] = [];

// Feature
// -------

export function feature_add(k: string): void {
  FEAT[k] = (FEAT[k] ?? 0) + 1;
}

export function feature_goal(k: string, goal: T): void {
  feature_add(k);
  if (goal.k !== "u32") {
    feature_add(k + "-goal");
  }
}

// Size
// ----
// EVERY structural size draws from this one distribution: the site's
// small BODY (today's ranges) carries ~.99 of the mass, and a
// log-uniform tail from the body to the site's cap carries the rest --
// long functions, deep values, big matches and long chains EMERGE when
// draws land in the tail, several at once when several land. Tail hits
// are mostly moderate (log-uniform), so throughput holds. Caps come
// from measured walls: runtime chains are cheap to 300k on both legs;
// LITERAL chains used to stop at ~180 (clang's 256-bracket wall), but
// term_cexp (bend caf5de19) binds a temp every 64 nesting levels and
// term_lit (200bc799) compiles constant 17+-word subtrees as static
// data, so deep literals are now stretched to the low thousands ON
// PURPOSE -- they exercise exactly those two paths
// (compile_literal_bracket_wall.bend pins the wall's old face); dec
// patterns (case k+x) stop at 4000 -- the checker is linear in k since
// the codomain-composition fix, but term_higher still dies raw near
// k~10000. The dec peel's emitted-C nesting is flattened now (the
// scope_name loc registry + flat leaf_inline), but book_compile still
// RECURSES per peel and stack-overflows between k=2000 and k=3000
// (comp_dec_switch_bracket_wall.md) -- big-k draws land a real
// compiler-crash finding, kept on purpose until the chain compiles
// iteratively.

export function size_pick(body: number, cap: number): number {
  const lo = Math.max(1, body);
  if (cap > lo && G.chance(0.003)) {
    feature_add("stretch");
    return Math.floor(lo * Math.pow(cap / lo, G.int(1024) / 1024));
  }
  return body;
}

// Uid
// ---

export function uid_next(): number {
  return UID++;
}

// Ty
// --

export function ty_str(t: T): string {
  switch (t.k) {
    case "u32": return "U32";
    case "f32": return "F32";
    case "tvar": return t.n;
    case "adt": {
      if (t.a.sugar === "pair") {
        return "(" + ty_str(t.args[0]) + " & " + ty_str(t.args[1]) + ")";
      }
      if (t.a.dep === true) {
        return t.a.name + "(" + ty_str(t.args[0]) + ", z => " + ty_str(t.args[1]) + ")";
      }
      return t.args.length === 0 ? t.a.name : t.a.name + "<" + t.args.map(ty_str).join(",") + ">";
    }
    case "fun": return "(" + ty_str(t.dom) + (t.q === "none" ? " --> " : " -> ") + ty_str(t.cod) + ")";
    case "io": return "IO<" + ty_str(t.t) + ">";
    case "eql": return "{" + t.side + " = " + t.side + " : " + ty_str(t.t) + "}";
  }
}

export function ty_key(t: T): string {
  return ty_str(t);
}

export function ty_bind(name: string, t: T): string {
  return name + ": " + ty_str(t);
}

export function ty_eq(a: T, b: T): boolean {
  return ty_key(a) === ty_key(b);
}

export function ty_sub(t: T, m: Map<string, T>): T {
  switch (t.k) {
    case "tvar": return m.get(t.n) ?? t;
    case "adt": return { ...t, args: t.args.map((x) => ty_sub(x, m)) };
    case "fun": return { k: "fun", dom: ty_sub(t.dom, m), cod: ty_sub(t.cod, m), q: t.q };
    case "io": return { k: "io", t: ty_sub(t.t, m) };
    default: return t;
  }
}

export function ty_data(t: T): boolean {
  switch (t.k) {
    case "u32": case "f32": case "eql": return true;
    case "tvar": return false;
    case "adt": return t.a.data !== null && t.a.data.every((i) => ty_data(t.args[i]));
    case "fun": case "io": return false;
  }
}

export function ty_open(t: T): boolean {
  switch (t.k) {
    case "tvar": return true;
    case "adt": return t.args.some(ty_open);
    case "fun": return ty_open(t.dom) || ty_open(t.cod);
    case "io": return ty_open(t.t);
    default: return false;
  }
}

export function ty_unify(pat: T, goal: T, m: Map<string, T>): boolean {
  if (pat.k === "tvar") {
    const got = m.get(pat.n);
    if (got !== undefined) {
      return ty_eq(got, goal);
    }
    m.set(pat.n, goal);
    return true;
  }
  if (pat.k !== goal.k) {
    return false;
  }
  if (pat.k === "adt" && goal.k === "adt") {
    return pat.a === goal.a && pat.args.every((x, i) => ty_unify(x, goal.args[i], m));
  }
  if (pat.k === "fun" && goal.k === "fun") {
    return ty_unify(pat.dom, goal.dom, m) && ty_unify(pat.cod, goal.cod, m);
  }
  if (pat.k === "eql" && goal.k === "eql") {
    return false;
  }
  return true;
}

// Need
// ----

export function need_list(): Adt {
  if (LISTA === null) {
    IMPORTS.add("List");
    const a: Adt = { name: "List", tvars: ["A"], ctors: [], rec: true, data: [0] };
    a.ctors.push({ name: "Cons", fields: [{ k: "tvar", n: "A" }, { k: "adt", a, args: [{ k: "tvar", n: "A" }] }], er: -1 });
    a.ctors.push({ name: "Nil", fields: [], er: -1 });
    LISTA = a;
  }
  return LISTA;
}

export function need_char(): Adt {
  if (CHARA === null) {
    IMPORTS.add("Char");
    CHARA = { name: "Char", tvars: [], ctors: [{ name: "Char", fields: [U32C], er: -1 }], rec: false, data: [] };
  }
  return CHARA;
}

export function need_str(): T {
  IMPORTS.add("String");
  return { k: "adt", a: need_list(), args: [{ k: "adt", a: need_char(), args: [] }] };
}

export function need_pair(a: T, b: T): T {
  if (PAIRA === null) {
    IMPORTS.add("Pair");
    PAIRA = {
      name: "Pair",
      tvars: ["A", "B"],
      ctors: [{ name: "Tuple", fields: [{ k: "tvar", n: "A" }, { k: "tvar", n: "B" }], er: -1 }],
      rec: false,
      data: [0, 1],
      dep: true,
      sugar: "pair",
    };
  }
  return { k: "adt", a: PAIRA, args: [a, b] };
}

export function need_unit(): T {
  if (UNITA === null) {
    IMPORTS.add("Unit");
    UNITA = {
      name: "Unit",
      tvars: [],
      ctors: [{ name: "U", fields: [], er: -1 }],
      rec: false,
      data: [],
      sugar: "unit",
    };
  }
  return { k: "adt", a: UNITA, args: [] };
}

// Adt minting
// -----------
// user ADT field holes use the same constrained type synthesis as value/type
// holes. Ctor 0 never recurs; direct self fields keep uniform recursion, so
// generated folds stay structurally decreasing.

export function adt_field_data(a: Adt, f: T): number[] | null {
  switch (f.k) {
    case "u32": case "f32": case "eql": return [];
    case "tvar": return [a.tvars.indexOf(f.n)];
    case "fun": case "io": return null;
    case "adt": {
      if (f.a === a) {
        return [];
      }
      if (f.a.data === null) {
        return null;
      }
      let out: number[] = [];
      for (const i of f.a.data) {
        const sub = adt_field_data(a, f.args[i]);
        if (sub === null) {
          return null;
        }
        out = out.concat(sub);
      }
      return out;
    }
  }
}

export function adt_value(a: Adt, c: Ctor, fields: string[]): string {
  if (a.sugar === "pair") {
    return "(" + fields.join(", ") + ")";
  }
  if (a.sugar === "unit") {
    return "()";
  }
  return c.name + "{" + fields.join(", ") + "}";
}

export function adt_pattern(a: Adt, c: Ctor, fields: string[]): string {
  return adt_value(a, c, fields);
}

export function adt_new(): Adt {
  const id = uid_next();
  const name = "D" + String(id);
  const ntv = G.int(3);
  const tvars = ["A", "B"].slice(0, ntv);
  const a: Adt = { name, tvars, ctors: [], rec: false, data: [] };
  const self: T = { k: "adt", a, args: tvars.map((n) => ({ k: "tvar", n }) as T) };
  const nctors = size_pick(1 + G.int(3), 40);
  for (let c = 0; c < nctors; c++) {
    const fields: T[] = [];
    const nf = size_pick(G.int(4), 12);
    for (let f = 0; f < nf; f++) {
      const field = syn_ty(2, true, { vars: tvars, self: c > 0 ? self : undefined });
      fields.push(field);
      if (field.k === "adt" && field.a === a) {
        a.rec = true;
      }
    }
    const cand = fields.map((f, i) => ({ f, i }))
      .filter((x) => !(x.f.k === "adt" && x.f.a === a));
    const er = cand.length > 0 && G.chance(0.2) ? G.pick(cand).i : -1;
    if (er >= 0) {
      feature_add("erased-field");
    }
    a.ctors.push({ name: name + ("abcd"[c] ?? "k" + String(c)), fields, er });
  }
  let deps: number[] | null = [];
  for (const c of a.ctors) {
    for (const f of c.fields) {
      const d = adt_field_data(a, f);
      if (d === null) {
        deps = null;
        break;
      }
      if (deps !== null) {
        deps = [...new Set(deps.concat(d))];
      }
    }
  }
  a.data = deps;
  const head = tvars.length > 0 ? name + "<" + tvars.join(",") + ">" : name;
  const rows = a.ctors.map((c) => "  " + c.name + "{"
    + c.fields.map((f, i) => i === c.er ? "-f" + String(i) + ": " + ty_str(f) : ty_bind("f" + String(i), f)).join(", ") + "}");
  DECLS.push("type " + head + ":\n" + rows.join("\n"));
  ADTS.push(a);
  return a;
}

export function adt_sig_new(): Adt {
  feature_add("sig");
  const id = uid_next();
  const name = "Sg" + String(id);
  const a: Adt = { name, tvars: ["A", "B"], ctors: [], rec: false, data: null, dep: true };
  a.ctors.push({ name: name + "a", fields: [{ k: "tvar", n: "A" }, { k: "tvar", n: "B" }], er: -1 });
  DECLS.push("type " + name + "(A: Type, B: A -> Type):\n  " + name + "a{a: A, b: B(a)}");
  ADTS.push(a);
  return a;
}

// Syn
// ---
// a type-valued hole: picks/instantiates from the universe. data=true
// restricts to the Data class (needed under +, for adt args, for foldable
// lets). Instantiation args are always Data so every synthesized value
// stays foldable and shareable.

export function syn_ty(fuel: number, data: boolean, hole?: TyHole): T {
  const nested = hole === undefined ? undefined : { vars: hole.vars };
  return G.wpick<() => T>([
    [12, () => U32C],
    [12, () => F32C],
    [(hole?.vars.length ?? 0) > 0 ? 16 : 0, () => ({ k: "tvar", n: G.pick(hole?.vars ?? []) })],
    [hole?.self !== undefined ? 14 : 0, () => hole?.self ?? U32C],
    [fuel > 0 && (ADTS.length > 0 || hole === undefined) ? 16 : 0, () => {
      const cands = ADTS.filter((a) => a.data !== null && a.dep !== true);
      const mk = hole === undefined && (cands.length === 0 || G.chance(0.2));
      const a = mk ? adt_new() : cands.length > 0 ? G.pick(cands) : adt_new();
      if (a.data === null || a.dep === true) {
        return U32C;
      }
      return { k: "adt", a, args: a.tvars.map(() => syn_ty(fuel - 1, true, nested)) };
    }],
    [fuel > 0 ? 10 : 0, () => ({ k: "adt", a: need_list(), args: [syn_ty(fuel - 1, true, nested)] }) as T],
    [fuel > 0 ? 4 : 0, () => need_str()],
    [fuel > 0 ? 10 : 0, () => need_pair(syn_ty(fuel - 1, true, nested), syn_ty(fuel - 1, true, nested))],
    [fuel > 0 ? 5 : 0, () => need_unit()],
    [!data && fuel > 0 ? 8 : 0, () => {
      const q = G.wpick<"none" | undefined>([[80, undefined], [20, "none"]]);
      const dom = G.pick([U32C, F32C]);
      return { k: "fun", q, dom, cod: syn_ty(fuel - 1, true) } as T;
    }],
    [!data && fuel > 1 && G.chance(0.5) ? 4 : 0, () => {
      const a = adt_sig_new();
      return { k: "adt", a, args: [syn_ty(0, true), syn_ty(0, true)] };
    }],
  ])();
}

// V
// -
// q "once": closures and tvar-typed binders (strictly linear — the checker
// refuses contraction at abstract types); q "many": everything else (words,
// Data values — an extra owner is an inferred copy$, a dominated read a
// borrow). not: word literals this binder can no longer match (miss-binder
// chains). Arrays never enter env.

type V = { name: string; ty: T; q: "many" | "once" | "dead"; not?: number[] };

export function v_many(name: string, ty: T): V {
  return { name, ty, q: ty_data(ty) || ty.k === "u32" || ty.k === "f32" ? "many" : "once" };
}

// Env
// ---

export function env_nums(env: V[]): V[] {
  return env.filter((v) => v.q !== "dead" && v.ty.k === "u32");
}

export function env_take(v: V): string {
  if (v.q === "once") {
    v.q = "dead";
  }
  return v.name;
}

// Num
// ---

const OPS: Array<[number, string]> = [
  [20, "+"], [14, "-"], [14, "*"], [7, "/"], [7, "%"],
  [6, ".^."], [4, ".&."], [4, ".|."],
  [5, "=="], [4, "!="], [5, "<"], [4, "<="], [4, ">"], [4, ">="],
  [5, "<<"], [5, ">>"], [4, "&&"], [4, "||"],
];

export function num_lit_u32(): E {
  return e_atom(String(G.wpick<() => string>([
    [30, () => String(G.int(16))],
    [25, () => String(G.int(1000))],
    [15, () => String(G.int(4294967296))],
    [10, () => "4294967295"],
    [10, () => "2147483648"],
    [5, () => "65536"],
    [5, () => "0"],
  ])()));
}

export function num_gen_u32(env: V[], fuel: number): E {
  const vars = env_nums(env);
  if (fuel <= 0) {
    return vars.length > 0 && G.chance(0.55) ? e_atom(G.pick(vars).name) : num_lit_u32();
  }
  return G.wpick<() => E>([
    [15, () => num_lit_u32()],
    [vars.length > 0 ? 22 : 0, () => e_atom(G.pick(vars).name)],
    [1, () => e_atom("`" + str_char() + "`")],
    [34, () => {
      const op = G.wpick(OPS);
      const l = num_gen_u32(env, fuel - 1);
      const r = num_gen_u32(env, fuel - 1);
      return e_bin(l, op, r);
    }],
    [6, () => e_bin(num_gen_u32(env, fuel - 1), G.pick(["/", "%"]), G.chance(0.25) ? e_atom("0") : num_gen_u32(env, fuel - 1))],
    [6, () => {
      feature_add("f32");
      return e_fn1("$f32_to_u32", num_gen_f32(env, fuel - 1));
    }],
    [4, () => {
      feature_add("f32cmp");
      const op = G.pick(["<", "<=", ">", ">=", "==", "!="]);
      return e_bin(num_gen_f32(env, fuel - 1), op, num_gen_f32(env, fuel - 1));
    }],
    [fuel >= 2 ? 5 : 0, () => call_helper(env, fuel)],
    [fuel >= 2 ? 4 : 0, () => call_hof(env, fuel)],
    [fuel >= 2 ? 4 : 0, () => syn_call_unify(U32C, env, fuel) ?? num_lit_u32()],
    [fuel >= 2 ? 3 : 0, () => {
      const t = syn_ty(1, true);
      if (t.k === "u32") {
        return num_gen_u32(env, 1);
      }
      if (t.k === "f32") {
        return e_fn1("$f32_to_u32", num_gen_f32(env, 1));
      }
      feature_add("fold");
      return e_atom(rd_ensure(t) + "(" + e_at(syn(t, env, 1)) + ")");
    }],
  ])();
}

export function num_lit_f32(neg: boolean): E {
  const num = 1 + G.int(256);
  const den = G.pick([8, 16, 32, 8, 4]);
  const v = num / den;
  const sgn = neg && G.chance(0.15) ? "-" : "";
  const s = String(v);
  return e_atom(sgn + (s.includes(".") ? s : s + ".0"));
}

export function num_gen_f32(env: V[], fuel: number): E {
  const vars = env.filter((v) => v.q !== "dead" && v.ty.k === "f32");
  if (fuel <= 0) {
    return vars.length > 0 && G.chance(0.4) ? e_atom(G.pick(vars).name) : num_lit_f32(false);
  }
  return G.wpick<() => E>([
    [26, () => num_lit_f32(false)],
    [vars.length > 0 ? 12 : 0, () => e_atom(G.pick(vars).name)],
    [4, () => num_lit_f32(true)],
    [15, () => e_fn1("$u32_to_f32", num_gen_u32(env, 0))],
    [40, () => e_bin(num_gen_f32(env, fuel - 1), G.pick(["+", "-", "*"]), num_gen_f32(env, fuel - 1))],
    [8, () => {
      feature_add("fdiv");
      return e_bin(num_gen_f32(env, fuel - 1), "/", num_lit_f32(false));
    }],
    [8, () => {
      const e = num_gen_f32(env, fuel - 1);
      return e_fn1("$sqrt", e_bin(e, "*", e));
    }],
    [4, () => e_fn1("$floor", num_gen_f32(env, fuel - 1))],
    [5, () => {
      feature_add("trans");
      return e_fn1(G.pick(["$sin", "$cos", "$tanh"]), num_gen_f32(env, fuel - 1));
    }],
    [2, () => {
      feature_add("trans");
      return e_fn1("$exp", num_lit_f32(false));
    }],
    [2, () => {
      feature_add("trans");
      return e_fn1("$log", num_lit_f32(false));
    }],
    [3, () => {
      feature_add("trans");
      return e_bin(num_gen_f32(env, fuel - 1), "~/", num_gen_f32(env, fuel - 1));
    }],
  ])();
}

// num_combine : a single element gets a neutral + 0 so a bare char
// literal cannot BE the raw result -- its spelling flag would reach the
// display and re-find bug B (b1/b2 pin it; any arithmetic forces the
// word, which is also why multi-element combines never showed it)
export function num_combine(es: E[]): E {
  if (es.length === 1) {
    return e_bin(es[0], "+", e_atom("0"));
  }
  let acc = es[0];
  for (const e of es.slice(1)) {
    acc = e_bin(acc, G.pick(["+", "-", "*", ".^.", "+", "+"]), e);
  }
  return acc;
}

export function num_seal(name: string): E {
  const e = e_atom(name);
  const k = num_lit_u32();
  switch (G.int(6)) {
    case 0: {
      feature_add("seal-add");
      return e_bin(e_bin(e, "+", k), "-", k);
    }
    case 1: {
      feature_add("seal-xor");
      return e_bin(e_bin(e, ".^.", k), ".^.", k);
    }
    case 2: {
      feature_add("seal-dist");
      const twice = e_bin(e_bin(e, "+", e), "*", e);
      const sq = e_bin(e, "*", e);
      return e_bin(e, "+", e_bin(twice, "-", e_bin(sq, "+", sq)));
    }
    case 3: {
      feature_add("seal-mask");
      const inv = e_bin(k, ".^.", e_atom("4294967295"));
      return e_bin(e_bin(e, ".&.", k), ".|.", e_bin(e, ".&.", inv));
    }
    case 4: {
      feature_add("seal-cmp");
      const cmp = e_bin(e, "<", k);
      return e_bin(e, ".^.", e_bin(cmp, ".^.", cmp));
    }
    default: {
      feature_add("seal-rot");
      const n = 1 + G.int(31);
      const l = e_atom(String(n));
      const r = e_atom(String(32 - n));
      const rot = e_bin(e_bin(e, "<<", l), ".|.", e_bin(e, ">>", r));
      return e_bin(e_bin(rot, ">>", l), ".|.", e_bin(rot, "<<", r));
    }
  }
}

const STR_CHARS = "abcdefgxyzABCXYZ0189 _.,:!?/+*-#";

// Str
// ---

export function str_char(): string {
  return STR_CHARS[G.int(STR_CHARS.length)];
}

export function str_lit(n: number): string {
  let s = "";
  for (let i = 0; i < n; i++) {
    s += G.chance(0.06) ? G.pick(["\\n", "\\t", "\\\"", "\\\\"]) : str_char();
  }
  return "\"" + s + "\"";
}

// Syn
// ---
// syn(goal, env, fuel): produce a term of type goal. Productions per goal
// head: matching env vars, intro forms, unifying registry calls, on-demand
// minted defs.
// Results may be intro-headed (non-inferable) — callers placing them in an
// INFER position (a bare let) must annotate; every field/argument hole here
// is a checked position.

export function syn(goal: T, env: V[], fuel: number): E {
  if (fuel >= 2 && syn_form_ok(goal) && G.chance(0.12)) {
    return syn_form(goal, env, fuel);
  }
  const direct = env.filter((v) => v.q !== "dead" && ty_eq(v.ty, goal));
  const var_w = direct.length > 0 ? 30 : 0;
  const uni_w = fuel >= 1 ? 8 : 0;
  const mint_w = fuel >= 2 && MINTS < 8 ? 4 : 0;
  const pick_var = (): E => e_atom(env_take(G.pick(direct)));
  const uni = (): E | null => syn_call_unify(goal, env, fuel);
  switch (goal.k) {
    case "u32": {
      return num_gen_u32(env, fuel);
    }
    case "f32": {
      return num_gen_f32(env, fuel);
    }
    case "tvar": {
      if (direct.length > 0) {
        return pick_var();
      }
      if (fuel > 0) {
        const got = uni();
        if (got !== null) {
          return got;
        }
      }
      throw new Error("no inhabitant for tvar " + goal.n);
    }
    case "adt": {
      const a = goal.a;
      const m = new Map<string, T>(a.tvars.map((n, i) => [n, goal.args[i]]));
      const intro = (): E => {
        const ctors = fuel <= 0 ? a.ctors.filter((c) => !c.fields.some((f) => f.k === "adt" && f.a === a)) : a.ctors;
        const c = G.pick(ctors.length > 0 ? ctors : [a.ctors[0]]);
        const args = c.fields.map((f) => {
          const ft = ty_sub(f, m);
          const sub = f.k === "adt" && f.a === a ? fuel - 1 : Math.min(fuel - 1, 1);
          return e_at(syn(ft, env, Math.max(0, sub)));
        });
        if (a.sugar === "pair") {
          feature_add("tuple");
        } else if (a.sugar === "unit") {
          feature_add("unit");
        }
        return e_atom(adt_value(a, c, args));
      };
      const is_str = a === LISTA && goal.args[0].k === "adt" && goal.args[0].a === CHARA;
      const is_list = a === LISTA && !is_str;
      return G.wpick<() => E>([
        [var_w, pick_var],
        [30, intro],
        [is_list && fuel > 0 ? 20 : 0, () => {
          const n = size_pick(G.int(5), 2500);
          const els: string[] = [];
          for (let i = 0; i < n; i++) {
            els.push(e_at(syn(goal.args[0], env, 0)));
          }
          return e_atom("[" + els.join(", ") + "]");
        }],
        [is_str ? 40 : 0, () => {
          IMPORTS.add("String");
          if (G.chance(0.25)) {
            return e_atom("'" + str_char() + "' <> " + str_lit(size_pick(1 + G.int(6), 2000)));
          }
          return e_atom(str_lit(size_pick(G.int(9), 2000)));
        }],
        [a === CHARA ? 30 : 0, () => e_atom("'" + str_char() + "'")],
        [a.rec && fuel > 0 && !ty_open(goal) ? 22 : 0, () => {
          const bname = builder_ensure(goal);
          const bcap = size_pick(4 + G.int(6), BUILDER_WIDE.has(bname) ? 15 : 30000);
          const fuelArg = e_bin(num_gen_u32(env, 1), "%", e_atom(String(bcap)));
          return e_atom(bname + "(" + e_at(fuelArg) + ")");
        }],
        [a.dep !== true && fuel >= 1 && !ty_open(goal) ? 6 : 0, () => {
          feature_add("reuse");
          return e_atom(tf_ensure(goal) + "(" + e_at(syn(goal, env, Math.max(0, fuel - 1))) + ")");
        }],
        [uni_w, () => uni() ?? intro()],
        [mint_w, () => syn_mint_def(goal, env) ?? intro()],
      ])();
    }
    case "fun": {
      const lam = (): E => {
        const b = "y" + String(uid_next());
        if (goal.q === "none") {
          feature_add("qfun");
          const name = "qf" + String(uid_next());
          DEFS.push("def " + name + "(-" + b + ": " + ty_str(goal.dom) + ") -> " + ty_str(goal.cod) + ":\n  "
            + e_at(syn(goal.cod, [], Math.min(Math.max(0, fuel - 1), 2))));
          return e_atom(name);
        }
        const benv = env.concat([v_many(b, goal.dom)]);
        if (!ty_data(goal.dom)) {
          benv[benv.length - 1].q = "once";
        }
        return e_atom(b + " => " + e_at(syn(goal.cod, benv, Math.min(fuel, 1))));
      };
      return G.wpick<() => E>([
        [var_w, pick_var],
        [35, lam],
        [fuel >= 1 && goal.q === undefined ? 15 : 0, () => {
          const cands = DEFR.filter((d) =>
            d.tps.length === 0 && d.ps.length >= 1
            && ty_eq(d.ps[d.ps.length - 1], goal.dom) && ty_eq(d.ret, goal.cod)
            && (d.mask?.[d.ps.length - 1] ?? null) === null
            && d.er !== d.ps.length - 1);
          if (cands.length === 0) {
            return lam();
          }
          feature_add("clo");
          const d = G.pick(cands);
          const front = d.ps.slice(0, -1).map((p, i) => syn_def_arg(d, i, p, env, Math.max(0, fuel - 1)));
          return e_atom(front.length > 0 ? d.name + "(" + front.join(", ") + ")" : d.name);
        }],
      ])();
    }
    case "eql": {
      feature_add("eql");
      return e_atom("{=}");
    }
    case "io": {
      throw new Error("io goals never reach syn (io_val owns them)");
    }
  }
}

export function syn_def_arg(d: DefR, i: number, t: T, env: V[], fuel: number): string {
  const e = syn(t, env, fuel);
  const mod = d.mask?.[i];
  return mod === undefined || mod === null ? e_at(e) : e_at(e_bin(e, "%", e_atom(String(mod))));
}

export function syn_call_unify(goal: T, env: V[], fuel: number): E | null {
  const cands: Array<{ d: DefR; m: Map<string, T> }> = [];
  for (const d of DEFR) {
    const m = new Map<string, T>();
    if (ty_unify(d.ret, goal, m)) {
      cands.push({ d, m });
    }
  }
  if (cands.length === 0) {
    return null;
  }
  const { d, m } = G.pick(cands);
  for (const tp of d.tps) {
    if (!m.has(tp)) {
      m.set(tp, syn_ty(0, true));
    }
  }
  feature_add(d.tps.length > 0 ? "generic" : "unicall");
  const args = d.ps.map((p, i) => syn_def_arg(d, i, ty_sub(p, m), env, Math.max(0, fuel - 1)));
  const targs = d.tps.map((tp) => ty_str(m.get(tp) as T));
  const head = d.tps.length > 0 ? d.name + "<" + targs.join(",") + ">" : d.name;
  return e_defcall(d.name, head + "(" + args.join(", ") + ")");
}

export function syn_mint_def(goal: T, env: V[]): E | null {
  if (goal.k === "eql" || ty_open(goal)) {
    return null;
  }
  MINTS++;
  feature_add("mint");
  const name = "fn" + String(uid_next());
  const nps = 1 + G.int(3);
  const ps: T[] = [];
  for (let i = 0; i < nps; i++) {
    ps.push(syn_ty(1, false));
  }
  // er : an ERASED param: bound at None, so the body may not consume it at
  // all. Uses are tracked three-valued (None < Lone < Many) and checked
  // at every binder -- without this, generated defs only ever bound the
  // upper two, and no value of an erased type was ever built.
  const er = G.chance(0.25) ? G.int(ps.length + 1) : -1;
  if (er >= 0) {
    feature_add("erased");
    ps.splice(er, 0, syn_plain_ty(1));
  }
  const penv = ps.map((p, i) => v_many("p" + String(i), p)).filter((_, i) => i !== er);
  const body = syn(goal, penv, 2);
  const params = ps.map((p, i) => i === er ? "-p" + String(i) + ": " + ty_str(p) : ty_bind("p" + String(i), p));
  DEFS.push("def " + name + "(" + params.join(", ") + ") -> " + ty_str(goal) + ":\n  " + e_at(body));
  DEFR.push({ name, tps: [], ps, ret: goal, er: er >= 0 ? er : undefined });
  const args = ps.map((p) => e_at(syn(p, env, 1)));
  return e_atom(name + "(" + args.join(", ") + ")");
}

export function syn_plain_ty(fuel: number): T {
  return syn_ty(fuel, true);
}

export function syn_form_ok(goal: T): boolean {
  return goal.k !== "tvar" && goal.k !== "eql" && !ty_open(goal);
}

export function syn_form(goal: T, env: V[], fuel: number): E {
  return G.wpick<() => E>([
    [20, () => syn_if(goal, env, fuel)],
    [18, () => syn_comp(goal, env, fuel)],
    [18, () => syn_open(goal, env, fuel)],
    [16, () => syn_assert(goal, env, fuel)],
    [ty_data(goal) ? 16 : 0, () => syn_dep(goal, env, fuel)],
    [10, () => syn_ford(goal, env, fuel)],
    [8, () => syn_clofield(goal, env, fuel)],
    [14, () => syn_lib(goal, env, fuel)],
  ])();
}

export function syn_if(goal: T, env: V[], fuel: number): E {
  feature_goal("if", goal);
  const name = "if" + String(uid_next());
  const a = 1 + G.int(8);
  const b = a + 1 + G.int(8);
  const branch = (): string => e_at(syn(goal, [v_many("n", U32C)], Math.max(0, fuel - 1)));
  DEFS.push("def " + name + "(n: U32) -> " + ty_str(goal) + ":\n  if n < " + String(a) + ":\n    " + branch()
    + "\n  elif n < " + String(b) + ":\n    " + branch()
    + "\n  else:\n    " + branch());
  DEFR.push({ name, tps: [], ps: [U32C], ret: goal });
  return e_defcall(name, name + "(" + e_at(num_gen_u32(env, 1)) + ")");
}

export function syn_comp(goal: T, env: V[], fuel: number): E {
  feature_goal("comp", goal);
  const name = "cp" + String(uid_next());
  const dom = ty_data(goal) && G.chance(0.5) ? goal : syn_plain_ty(1);
  const z = "z" + String(uid_next());
  const captures = env.filter((v) => v.q === "many");
  const words = captures.filter((v) => v.ty.k === "u32");
  const arg = syn(dom, env, Math.max(0, fuel - 1));
  const kind = G.wpick<string>([[60, "one"], [25, "two"], [words.length > 0 ? 15 : 0, "era"]]);
  if (kind === "two") {
    feature_add("comp2");
    const mid = syn_plain_ty(1);
    DEFS.push("def " + name + "(~f: " + ty_str(dom) + " -> " + ty_str(mid) + ", ~g: " + ty_str(mid) + " -> " + ty_str(goal) + ", x: " + ty_str(dom) + ") -> " + ty_str(goal) + ":\n  g(f(x))");
    const z2 = "z" + String(uid_next());
    const bodyF = ty_eq(dom, mid) ? e_atom(z) : syn(mid, captures.concat([v_many(z, dom)]), Math.max(0, fuel - 1));
    const bodyG = ty_eq(mid, goal) ? e_atom(z2) : syn(goal, captures.concat([v_many(z2, mid)]), Math.max(0, fuel - 1));
    return e_atom(name + "(" + z + " => " + e_at(bodyF) + ", " + z2 + " => " + e_at(bodyG) + ", " + e_at(arg) + ")");
  }
  DEFS.push("def " + name + "(~f: " + ty_str(dom) + " -> " + ty_str(goal) + ", x: " + ty_str(dom) + ") -> " + ty_str(goal) + ":\n  f(x)");
  if (kind === "era") {
    // compera : the capture reaches the template body ONLY through an
    // erased param (the reg/357 class: argument and parameter must
    // erase together or the saturated call loses an argument)
    feature_add("compera");
    const sink = "ce" + String(uid_next());
    DEFS.push("def " + sink + "(-e: U32, " + ty_bind("y", goal) + ") -> " + ty_str(goal) + ":\n  y");
    const w = G.pick(words).name;
    const cenv = captures.filter((v) => v.name !== w);
    const inner = ty_eq(dom, goal) ? e_atom(z) : syn(goal, cenv.concat([v_many(z, dom)]), Math.max(0, fuel - 1));
    return e_atom(name + "(" + z + " => " + sink + "(" + w + ", " + e_at(inner) + "), " + e_at(arg) + ")");
  }
  const body = ty_eq(dom, goal)
    ? e_atom(z)
    : syn(goal, captures.concat([v_many(z, dom)]), Math.max(0, fuel - 1));
  return e_atom(name + "(" + z + " => " + e_at(body) + ", " + e_at(arg) + ")");
}

export function syn_open(goal: T, env: V[], fuel: number): E {
  feature_goal("open", goal);
  const fst = ty_data(goal) ? goal : syn_plain_ty(1);
  const snd = syn_plain_ty(1);
  const pair = need_pair(fst, snd);
  const unit = need_unit();
  const name = "op" + String(uid_next());
  const a = "a" + String(uid_next());
  const b = "b" + String(uid_next());
  const penv = [v_many(a, fst), v_many(b, snd)];
  const body = ty_eq(fst, goal)
    ? e_atom(a)
    : syn(goal, penv, Math.max(0, fuel - 1));
  DEFS.push("def " + name + "(p: " + ty_str(pair) + ", u: Unit) -> " + ty_str(goal) + ":\n  ("
    + a + ", " + b + ") = p\n  match u:\n    case ():\n      " + e_at(body));
  DEFR.push({ name, tps: [], ps: [pair, unit], ret: goal });
  return e_defcall(name, name + "(" + e_at(syn(pair, env, 1)) + ", " + e_at(syn(unit, env, 1)) + ")");
}

export function syn_assert(goal: T, env: V[], fuel: number): E {
  feature_goal("assert", goal);
  const id = String(uid_next());
  const proof = "as" + id;
  const use = "au" + id;
  const witness = ty_data(goal) && G.chance(0.5) ? goal : syn_plain_ty(1);
  // bodiless : the assert and its FILL are one unit -- a fill must sit
  // in the same file as its assertion, and the module split cuts
  // between entries
  const bodiless = G.chance(0.3);
  DEFS.push("assert " + proof + ":\n  for all -A : Type\n  for all x : A\n  {x = x : A}"
    + (bodiless ? "" : "\n\ndef " + proof + "(A, x):\n  {=}"));
  const body = ty_eq(witness, goal)
    ? e_atom("x")
    : syn(goal, [v_many("x", witness)], Math.max(0, fuel - 1));
  if (bodiless) {
    // axiom : no computational content -- a live % rewrite would wedge the
    // interpreter on the unshed proof, so the reference rides a dead let
    feature_add("axiom");
    DEFS.push("def " + use + "(x: " + ty_str(witness) + ") -> " + ty_str(goal) + ":\n  zp" + id + " = "
      + proof + "(" + ty_str(witness) + ", x)\n  " + e_at(body));
  } else {
    DEFS.push("def " + use + "(x: " + ty_str(witness) + ") -> " + ty_str(goal) + ":\n  %"
      + proof + "(" + ty_str(witness) + ", x)\n  " + e_at(body));
  }
  DEFR.push({ name: use, tps: [], ps: [witness], ret: goal });
  return e_defcall(use, use + "(" + e_at(syn(witness, env, Math.max(0, fuel - 1))) + ")");
}

// syn_clofield : a closure stored in a ctor FIELD -- the datatype leaves
// the Data class (no share/fold), so it lives outside the ADT model: a
// dedicated intro whose lambda captures the live env, and a match that
// applies the field
export function syn_clofield(goal: T, env: V[], fuel: number): E {
  feature_goal("clofield", goal);
  const id = String(uid_next());
  const Cf = "Kf" + id;
  DECLS.push("type " + Cf + ":\n  " + Cf + "a{f: U32 -> U32, k: U32}");
  const use = "ku" + id;
  const body = goal.k === "u32"
    ? "f(k)"
    : "fk = f(k)\n      " + e_at(syn(goal, [v_many("fk", U32C)], Math.max(0, fuel - 1)));
  DEFS.push("def " + use + "(c: " + Cf + ") -> " + ty_str(goal) + ":\n  match c:\n    case " + Cf + "a{f, k}:\n      " + body);
  const y = "y" + String(uid_next());
  const lam = y + " => " + e_at(num_gen_u32(env.concat([v_many(y, U32C)]), 1));
  return e_defcall(use, use + "(" + Cf + "a{" + lam + ", " + e_at(num_gen_u32(env, 1)) + "})");
}

// syn_lib : the SHIPPED library as a caller sees it -- List/String
// functions over generated data, including the ~comp-param ones
// (map/fold/filter take templates). Answers a U32 so any goal reaches
// it through one reader
export function syn_lib(goal: T, env: V[], fuel: number): E {
  feature_goal("lib", goal);
  const id = String(uid_next());
  IMPORTS.add("List");
  const n = 1 + G.int(4);
  const els = Array.from({ length: n }, () => e_at(num_gen_u32(env, 0))).join(", ");
  const xs = "[" + els + "]";
  const shape = G.wpick<string>([[16, "sum"], [12, "len"], [12, "rev"], [10, "cat"], [12, "map"], [10, "fold"], [8, "take"], [10, "str"], [10, "cnt"]]);
  feature_add("lib-" + shape);
  let call: string;
  if (shape === "sum") {
    call = "List::sum(" + xs + ")";
  } else if (shape === "len") {
    call = "List::length<U32>(" + xs + ")";
  } else if (shape === "rev") {
    call = "List::sum(List::reverse<U32>(" + xs + "))";
  } else if (shape === "cat") {
    call = "List::sum(List::concat<U32>(" + xs + ", " + xs + "))";
  } else if (shape === "map") {
    call = "List::sum(List::map<U32, U32>(y" + id + " => " + e_at(num_gen_u32([v_many("y" + id, U32C)], 1)) + ", " + xs + "))";
  } else if (shape === "fold") {
    call = "List::fold<U32, U32>(a" + id + " => b" + id + " => (a" + id + " + b" + id + "), " + String(G.int(64)) + ", " + xs + ")";
  } else if (shape === "take") {
    call = "List::sum(List::take<U32>(" + String(1 + G.int(3)) + ", " + xs + "))";
  } else if (shape === "cnt") {
    call = "List::count(" + e_at(num_gen_u32(env, 0)) + ", " + xs + ")";
  } else {
    IMPORTS.add("String");
    IMPORTS.add("Char");
    call = "String::length(String::concat(" + str_lit(1 + G.int(5)) + ", String::reverse(" + str_lit(1 + G.int(5)) + ")))";
  }
  if (goal.k === "u32") {
    return e_atom(call);
  }
  const rd = "lb" + id;
  DEFS.push("def " + rd + "(x: U32) -> " + ty_str(goal) + ":\n  " + e_at(syn(goal, [v_many("x", U32C)], Math.max(0, fuel - 1))));
  DEFR.push({ name: rd, tps: [], ps: [U32C], ret: goal });
  return e_defcall(rd, rd + "(" + call + ")");
}

// syn_ford : the generic indexed-family kit (chk/006 idioms, minted
// parametrically off ONE recipe): an index Nat clone, a payload family
// pinned per ctor by eq fields (LIVE or ERASED), a word->index
// converter, a runtime-index builder recursing on the index (the split
// specializes each arm's goal, so intro needs no transport), and an
// eliminator. Live eq: single-def RECURSIVE elimination -- the split
// specializes the hypothesis's type in the arm's own context (the old
// as-equation identity-cast hop is ill-typed now, not just redundant),
// the opener refutes its impossible arm through the discriminator
// motive and crosses the tail to the smaller index through injectivity,
// and the recursive call descends structurally. Erased eq: evidence cannot refute or
// transport, so the reader is the SHALLOW match (recursing on evidence
// is refused by ruling). Recipe axes: eq erasure, a second passthrough
// index, payload type, and a dependent-pair coupling that eliminates
// Sg(N, i => F(i)) at a runtime index.
export function syn_ford(goal: T, env: V[], fuel: number): E {
  feature_goal("ford", goal);
  IMPORTS.add("Unit");
  IMPORTS.add("Empty");
  IMPORTS.add("Pair");
  const id = String(uid_next());
  const N = "Fn" + id;
  const Z = N + "z";
  const S = N + "s";
  DECLS.push("type " + N + ":\n  " + Z + "{}\n  " + S + "{p: " + N + "}");
  const erased = G.chance(0.35);
  const midx = G.chance(0.3);
  const P = syn_plain_ty(1);
  const V = "Fv" + id;
  const VZ = V + "z";
  const VS = V + "s";
  const em = erased ? "-" : "";
  const ixd = midx ? "(n: " + N + ", m: U32)" : "(n: " + N + ")";
  const fat = (i: string): string => midx ? V + "(" + i + ", m)" : V + "(" + i + ")";
  DECLS.push("type " + V + ixd + ":\n  " + VZ + "{" + em + "eq: {n = " + Z + "{} : " + N + "}, w: " + ty_str(P) + "}\n  "
    + VS + "{p: " + N + ", x: " + ty_str(P) + ", t: " + fat("p") + ", " + em + "eq: {n = " + S + "{p} : " + N + "}}");
  const toN = "fw" + id;
  DEFS.push("def " + toN + "(k: U32) -> " + N + ":\n  match k:\n    case 0:\n      " + Z + "{}\n    case 1+p:\n      " + S + "{" + toN + "(p)}");
  const benv = midx ? [v_many("m", U32C)] : [];
  const bps = midx ? "(n: " + N + ", m: U32)" : "(n: " + N + ")";
  const bargs = midx ? "p, m" : "p";
  DEFS.push("def " + V + "b" + bps + " -> " + fat("n") + ":\n  match n:\n    case " + Z + "{}:\n      "
    + VZ + "{{=}, " + e_at(syn(P, benv, 1)) + "}\n    case " + S + "{p}:\n      "
    + VS + "{p, " + e_at(syn(P, benv, 1)) + ", " + V + "b(" + bargs + "), {=}}");
  const pc = (b: string): string => P.k === "u32" ? b : e_at(syn(U32C, [v_many(b, P)], 1));
  const eps = midx ? "(n: " + N + ", m: U32, v: " + fat("n") + ")" : "(n: " + N + ", v: " + fat("n") + ")";
  const eargs = (i: string, vv: string): string => midx ? i + ", m, " + vv : i + ", " + vv;
  if (erased) {
    feature_add("forde");
    DEFS.push("def " + V + "e" + eps + " -> U32:\n  match v:\n    case " + VZ + "{eq, w}:\n      "
      + pc("w") + "\n    case " + VS + "{p, x, t, eq}:\n      " + pc("x"));
  } else {
    const D = "fd" + id;
    DEFS.push("def " + D + "(x: " + N + ", zc: Type, sc: Type) -> Type:\n  match x:\n    case " + Z + "{}:\n      zc\n    case " + S + "{p}:\n      sc");
    const sz = "fr" + id;
    DEFS.push("def " + sz + "(p: " + N + ", e: {" + S + "{p} = " + Z + "{} : " + N + "}) -> Empty:\n  %e : w => " + D + "(w, Unit, Empty)\n  U{}");
    const pr = "fp" + id;
    DEFS.push("def " + pr + "(n: " + N + ") -> " + N + ":\n  match n:\n    case " + Z + "{}:\n      " + Z + "{}\n    case " + S + "{p}:\n      p");
    const inj = "fj" + id;
    DEFS.push("def " + inj + "(a: " + N + ", b: " + N + ", e: {" + S + "{a} = " + S + "{b} : " + N + "}) -> {a = b : " + N + "}:\n  %e : w => {" + pr + "(w) = b : " + N + "}\n  {=}");
    const ops = midx ? "(p: " + N + ", m: U32, vv: " + fat(S + "{p}") + ")" : "(p: " + N + ", vv: " + fat(S + "{p}") + ")";
    DEFS.push("def " + V + "o" + ops + " -> (U32 & " + fat("p") + "):\n  match vv:\n    case " + VZ + "{eq, w}:\n      Empty::absurd((U32 & " + fat("p") + "), " + sz + "(p, eq))\n    case " + VS + "{q, x, t, eq}:\n      ("
      + pc("x") + ", ({(%" + inj + "(p, q, eq) (w => w)) : (" + fat("q") + " -> " + fat("p") + ")})(t))");
    // split : the checker's split specializes v's type to fat(S{p}) in
    // the arm's context by itself now, so the old as-equation identity
    // cast ({(%en (w => w)) : fat(n) -> fat(S{p})})(v) is not just
    // unnecessary but ill-typed -- v is used direct; the as-equation
    // stays bound as syntax coverage
    DEFS.push("def " + V + "e" + eps + " -> U32:\n  match n as en:\n    case " + Z + "{}:\n      "
      + String(G.int(64)) + "\n    case " + S + "{p}:\n      pr = " + V + "o(" + eargs("p", "v") + ")\n      match pr:\n        case (x, t2):\n          (x + " + V + "e(" + eargs("p", "t2") + "))");
  }
  if (!erased && !midx && P.k === "u32" && G.chance(0.25)) {
    // vapp : the index is a COMPUTED term -- append answers Vc(ad(a,b)),
    // so the checker converts index EXPRESSIONS (ad(Ns{p},b) reduces to
    // Ns{ad(p,b)}, which is what makes the cons arm's {=} land)
    feature_add("vapp");
    const ad = "fa" + id;
    DEFS.push("def " + ad + "(a: " + N + ", b: " + N + ") -> " + N + ":\n  match a:\n    case " + Z + "{}:\n      b\n    case " + S + "{p}:\n      " + S + "{" + ad + "(p, b)}");
    const ap = V + "p";
    DEFS.push("def " + ap + "(a: " + N + ", b: " + N + ", x: " + V + "(a), y: " + V + "(b)) -> " + V + "(" + ad + "(a, b)):\n  match a as ea:\n    case " + Z + "{}:\n      y\n    case " + S + "{p}:\n      pp = " + V + "o(p, x)\n      match pp:\n        case (hv, tv):\n          " + VS + "{" + ad + "(p, b), hv, " + ap + "(p, b, tv, y), {=}}");
    const uu = "fv" + id;
    DEFS.push("def " + uu + "(k: U32, j: U32) -> U32:\n  na = " + toN + "(k % 4)\n  nb = " + toN + "(j % 4)\n  " + V + "e(" + ad + "(na, nb), " + ap + "(na, nb, " + V + "b(na), " + V + "b(nb)))");
    DEFR.push({ name: uu, tps: [], ps: [U32C, U32C], ret: U32C });
    const vc = uu + "(" + e_at(num_gen_u32(env, 1)) + ", " + e_at(num_gen_u32(env, 1)) + ")";
    if (goal.k === "u32") {
      return e_defcall(uu, vc);
    }
    const vf = "vg" + id;
    DEFS.push("def " + vf + "(x: U32) -> " + ty_str(goal) + ":\n  " + e_at(syn(goal, [v_many("x", U32C)], Math.max(0, fuel - 1))));
    DEFR.push({ name: vf, tps: [], ps: [U32C], ret: goal });
    return e_defcall(vf, vf + "(" + vc + ")");
  }
  const bound = String(size_pick(2 + G.int(5), 2000));
  const ups = midx ? "(k: U32, m: U32)" : "(k: U32)";
  const uargs = (nn: string): string => midx ? nn + ", m, " : nn + ", ";
  const ucall = (nn: string): string => V + "e(" + uargs(nn) + V + "b(" + (midx ? nn + ", m" : nn) + "))";
  let core: string;
  if (!erased && !midx && G.chance(0.3)) {
    feature_add("sigelim");
    const sg = "Sf" + id;
    DECLS.push("type " + sg + "(A: Type, B: A -> Type):\n  " + sg + "a{a: A, b: B(a)}");
    core = "s = {" + sg + "a{nn, " + V + "b(nn)} : " + sg + "(" + N + ", i => " + V + "(i))}\n  match s:\n    case " + sg + "a{a, b}:\n      " + V + "e(a, b)";
  } else {
    core = ucall("nn");
  }
  const use = "fu" + id;
  DEFS.push("def " + use + ups + " -> U32:\n  nn = " + toN + "(k % " + bound + ")\n  " + core);
  if (midx) {
    feature_add("fordm");
  }
  const call = use + "(" + e_at(num_gen_u32(env, 1)) + (midx ? ", " + e_at(num_gen_u32(env, 1)) : "") + ")";
  if (goal.k === "u32") {
    DEFR.push({ name: use, tps: [], ps: midx ? [U32C, U32C] : [U32C], ret: U32C });
    return e_defcall(use, call);
  }
  const fm = "ff" + id;
  DEFS.push("def " + fm + "(x: U32) -> " + ty_str(goal) + ":\n  " + e_at(syn(goal, [v_many("x", U32C)], Math.max(0, fuel - 1))));
  DEFR.push({ name: fm, tps: [], ps: [U32C], ret: goal });
  return e_defcall(fm, fm + "(" + call + ")");
}

export function syn_dep(goal: T, env: V[], fuel: number): E {
  feature_goal("u32dep", goal);
  const id = String(uid_next());
  const fam = "uf" + id;
  const pick = "up" + id;
  const left = ty_data(goal) ? goal : syn_plain_ty(1);
  let right = syn_plain_ty(1);
  for (let i = 0; i < 4 && ty_eq(left, right); i++) {
    right = syn_plain_ty(1);
  }
  if (ty_eq(left, right)) {
    right = left.k === "u32" ? F32C : U32C;
  }
  const hop = "uh" + id;
  DEFS.push("def " + fam + "(n: U32) -> Type:\n  match n:\n    case 0:\n      " + ty_str(left) + "\n    case 1+p:\n      " + ty_str(right));
  DEFS.push("def " + pick + "(n: U32) -> " + fam + "(n):\n  match n:\n    case 0:\n      "
    + e_at(syn(left, [], Math.max(0, fuel - 1))) + "\n    case 1+p:\n      " + e_at(syn(right, [], Math.max(0, fuel - 1))));
  const arm = (source: T): string => ty_eq(source, goal)
    ? "v"
    : e_at(syn(goal, [v_many("v", source)], Math.max(0, fuel - 1)));
  DEFS.push("def " + hop + "(k: U32, v: " + fam + "(k)) -> " + ty_str(goal) + ":\n  match k:\n    case 0:\n      "
    + arm(left) + "\n    case 1+q:\n      " + arm(right));
  if (G.chance(0.25)) {
    // hkdep : the family and its section as VALUES -- a higher-kinded
    // F: U32 -> Type param, a dependent-arrow @z. F(z) arg (pick by
    // name), and an instantiation-typed continuation F(0) -> U32
    feature_goal("hkdep", goal);
    const hm = "hm" + id;
    DEFS.push("def " + hm + "(x: " + ty_str(left) + ") -> U32:\n  "
      + (left.k === "u32" ? "x" : e_at(syn(U32C, [v_many("x", left)], 1))));
    const hk = "hk" + id;
    DEFS.push("def " + hk + "(-F: U32 -> Type, g: @z: U32. F(z), h: (F(0) -> U32)) -> U32:\n  h(g(0))");
    const call = hk + "(" + fam + ", " + pick + ", " + hm + ")";
    if (goal.k === "u32") {
      return e_atom(call);
    }
    const hf = "hf" + id;
    DEFS.push("def " + hf + "(x: U32) -> " + ty_str(goal) + ":\n  " + e_at(syn(goal, [v_many("x", U32C)], Math.max(0, fuel - 1))));
    DEFR.push({ name: hf, tps: [], ps: [U32C], ret: goal });
    return e_defcall(hf, hf + "(" + call + ")");
  }
  if (G.chance(0.4)) {
    feature_goal("sigelim", goal);
    const sg = "Sk" + id;
    const su = "us" + id;
    DECLS.push("type " + sg + "(A: Type, B: A -> Type):\n  " + sg + "a{a: A, b: B(a)}");
    DEFS.push("def " + su + "(n: U32) -> " + ty_str(goal) + ":\n  s = {" + sg + "a{n, " + pick + "(n)} : "
      + sg + "(U32, z => " + fam + "(z))}\n  match s:\n    case " + sg + "a{a, b}:\n      " + hop + "(a, b)");
    DEFR.push({ name: su, tps: [], ps: [U32C], ret: goal });
    return e_defcall(su, su + "(" + e_at(num_gen_u32(env, 1)) + ")");
  }
  const use = "uu" + id;
  DEFS.push("def " + use + "(n: U32) -> " + ty_str(goal) + ":\n  " + hop + "(n, " + pick + "(n))");
  DEFR.push({ name: use, tps: [], ps: [U32C], ret: goal });
  return e_defcall(use, use + "(" + e_at(num_gen_u32(env, 1)) + ")");
}

// Builder
// -------
// def mk(n: U32) -> T — countdown structural builders per instantiation key;
// halt sees the n-1 decrease under the 0-switch.

export function builder_ensure(t: T & { k: "adt" }): string {
  const key = "mk:" + ty_key(t);
  const got = BUILDERS.get(key);
  if (got !== undefined) {
    return got;
  }
  const name = "mk" + String(uid_next());
  BUILDERS.set(key, name);
  const a = t.a;
  const m = new Map<string, T>(a.tvars.map((n, i) => [n, t.args[i]]));
  const base = a.ctors.find((c) => !c.fields.some((f) => f.k === "adt" && f.a === a)) ?? a.ctors[0];
  const recs = a.ctors.filter((c) => c.fields.some((f) => f.k === "adt" && f.a === a));
  const rec = recs.length > 0 ? G.pick(recs) : base;
  if (rec.fields.filter((f) => f.k === "adt" && f.a === a).length >= 2) {
    BUILDER_WIDE.add(name);
  }
  const env: V[] = [v_many("n", U32C)];
  const fld = (c: Ctor, self: string): string[] =>
    c.fields.map((f) => {
      if (f.k === "adt" && f.a === a) {
        return self;
      }
      return e_at(syn(ty_sub(f, m), c === base ? [] : env, 0));
    });
  DEFS.push("def " + name + "(n: U32) -> " + ty_str(t) + ":\n  match n:\n    case 0:\n      "
    + base.name + "{" + fld(base, "").join(", ") + "}\n    case 1+n:\n      "
    + rec.name + "{" + fld(rec, name + "(n)").join(", ") + "}");
  DEFR.push({ name, tps: [], ps: [U32C], ret: t, mask: [4 + G.int(6)] });
  return name;
}

// Rd
// --
// def rd(x: T) -> U32 — memoized structural folds per instantiation key;
// every ctor covered, every field folded in (nothing dead), literal salts
// keep arms distinguishable. Word-only-field arms are borrow-fusion
// candidates; +T variants exercise the shared-match path (arms bind owned
// copies).

export function rd_ensure(t: T): string {
  if (t.k === "eql") {
    throw new Error("rd_ensure at an eql type (mode-dependent memo key)");
  }
  const key = "rd:" + ty_key(t);
  const got = REDUCES.get(key);
  if (got !== undefined) {
    if (RD_WIP.has(key)) {
      throw new Error("rd_ensure knot (mutually recursive reduces): " + key);
    }
    return got;
  }
  const name = "rd" + String(uid_next());
  REDUCES.set(key, name);
  RD_WIP.add(key);
  switch (t.k) {
    case "u32": {
      DEFS.push("def " + name + "(x: U32) -> U32:\n  x + " + String(1 + G.int(99)));
      break;
    }
    case "f32": {
      DEFS.push("def " + name + "(x: F32) -> U32:\n  $f32_to_u32(x * " + num_lit_f32(false).s + ")");
      break;
    }
    case "adt": {
      DEFS.push(rd_match(name, t, t, key));
      break;
    }
    case "fun": {
      const arg = t.dom.k === "f32" ? num_lit_f32(false) : num_lit_u32();
      const app = e_atom("f(" + arg.s + ")");
      const res = t.cod.k === "f32" ? e_fn1("$f32_to_u32", app) : t.cod.k === "u32" ? app : e_atom(rd_ensure(t.cod) + "(" + app.s + ")");
      DEFS.push("def " + name + "(f: " + ty_str(t) + ") -> U32:\n  " + e_at(res));
      break;
    }
    default: {
      DEFS.push("def " + name + "(x: " + ty_str(t) + ") -> U32:\n  " + String(1 + G.int(99)));
    }
  }
  DEFR.push({ name, tps: [], ps: [t], ret: U32C });
  RD_WIP.delete(key);
  return name;
}

// rd_deep : the fold's peel depth rides the size distribution -- a
// List-shaped ADT (one single-self rec ctor, one base, no erased
// fields) folds d constructors per step: the rec arm nests the rec
// pattern d deep, and each shallower nesting gets a base-tailed arm,
// so the case tree is total and every self-call strips d peels
export function rd_deep(name: string, t: T & { k: "adt" }, param: T, selfkey: string, d: number): string {
  const a = t.a;
  const m = new Map<string, T>(a.tvars.map((n, i) => [n, t.args[i]]));
  const rec = a.ctors.find((c) => c.fields.some((f) => f.k === "adt" && f.a === a)) as Ctor;
  const base = a.ctors.find((c) => c !== rec) as Ctor;
  const si = rec.fields.findIndex((f) => f.k === "adt" && f.a === a);
  const fpart = (f: T, v: string): E => {
    const ft = ty_sub(f, m);
    if (ft.k === "u32") {
      return e_atom(v);
    }
    if (ft.k === "f32") {
      return e_fn1("$f32_to_u32", e_bin(e_atom(v), "*", num_lit_f32(false)));
    }
    const fkey = "rd:" + ty_key(ft);
    return e_atom((fkey === selfkey || (f.k === "adt" && f.a === a) ? name : rd_ensure(ft)) + "(" + v + ")");
  };
  const mkpat = (k: number, core: string): string => {
    let p = core;
    for (let i = k; i >= 1; i--) {
      p = adt_pattern(a, rec, rec.fields.map((_, j) => (j === si ? p : "l" + String(i) + "_" + String(j))));
    }
    return p;
  };
  const mkparts = (k: number): E[] => {
    const out: E[] = [];
    for (let i = 1; i <= k; i++) {
      rec.fields.forEach((f, j) => {
        if (j !== si) {
          out.push(fpart(f, "l" + String(i) + "_" + String(j)));
        }
      });
    }
    return out;
  };
  const bp = adt_pattern(a, base, base.fields.map((_, j) => "b" + String(j)));
  const rows = ["    case " + mkpat(d, "t") + ":\n      "
    + e_at(num_combine(mkparts(d).concat([e_atom(name + "(t)")], [num_lit_u32()])))];
  for (let k = d - 1; k >= 0; k--) {
    rows.push("    case " + mkpat(k, bp) + ":\n      "
      + e_at(num_combine(mkparts(k).concat(base.fields.map((f, j) => fpart(f, "b" + String(j))), [num_lit_u32()]))));
  }
  return "def " + name + "(" + ty_bind("x", param) + ") -> U32:\n  match x:\n" + rows.join("\n");
}

export function rd_match(name: string, t: T & { k: "adt" }, param: T, selfkey: string): string {
  const a = t.a;
  const recs = a.ctors.filter((c) => c.fields.filter((f) => f.k === "adt" && f.a === a).length === 1 && c.er < 0);
  const bases = a.ctors.filter((c) => !c.fields.some((f) => f.k === "adt" && f.a === a) && c.er < 0);
  const peel = a.ctors.length === 2 && recs.length === 1 && bases.length === 1 ? size_pick(1, 4) : 1;
  if (peel > 1) {
    feature_add("peel");
    return rd_deep(name, t, param, selfkey, peel);
  }
  const m = new Map<string, T>(a.tvars.map((n, i) => [n, t.args[i]]));
  const rows = a.ctors.map((c) => {
    const vs = c.fields.map((_, i) => "x" + String(i));
    const parts = c.fields.flatMap((f, i) => {
      if (i === c.er) {
        return [];
      }
      const ft = ty_sub(f, m);
      if (ft.k === "u32") {
        return [e_atom(vs[i])];
      }
      if (ft.k === "f32") {
        return [e_fn1("$f32_to_u32", e_bin(e_atom(vs[i]), "*", num_lit_f32(false)))];
      }
      const fkey = "rd:" + ty_key(ft);
      const fname = fkey === selfkey || (f.k === "adt" && f.a === a) ? name : rd_ensure(ft);
      return [e_atom(fname + "(" + vs[i] + ")")];
    });
    parts.push(num_lit_u32());
    return "    case " + adt_pattern(a, c, vs) + ":\n      " + e_at(num_combine(parts));
  });
  // as_eq : `match E as e:` (bend df0f9b0a) gives the match a SECOND pattern
  // column -- one equation Var per arm, {E = that arm's pattern} -- which
  // term_elab_split reads as its marker. The equation is erased, so an arm
  // that never mentions it still drives the whole flatten/elab path, and
  // the compiled answer is unchanged.
  const as_eq = G.chance(0.25) ? " as e" + String(uid_next()) : "";
  if (as_eq !== "") {
    feature_add("matchas");
  }
  return "def " + name + "(" + ty_bind("x", param) + ") -> U32:\n  match x" + as_eq + ":\n" + rows.join("\n");
}

// Tf
// --
// def tf(x: T) -> T — same-ctor rebuilds: every arm re-emits the ctor it
// matched with mutated word fields and recursed self fields; the compiler's
// ctor-reuse (take_N handing back the owned node) triggers exactly here.

export function tf_ensure(t: T & { k: "adt" }): string {
  const key = "tf:" + ty_key(t);
  const got = TRANSFORMS.get(key);
  if (got !== undefined) {
    return got;
  }
  const name = "tf" + String(uid_next());
  TRANSFORMS.set(key, name);
  const a = t.a;
  const m = new Map<string, T>(a.tvars.map((n, i) => [n, t.args[i]]));
  const rows = a.ctors.map((c) => {
    const vs = c.fields.map((_, i) => "x" + String(i));
    const args = c.fields.map((f, i) => {
      const ft = ty_sub(f, m);
      if (i === c.er) {
        return vs[i];
      }
      if (ft.k === "u32") {
        return e_at(e_bin(e_atom(vs[i]), G.pick(["+", "*", ".^."]), e_atom(String(1 + G.int(9)))));
      }
      if (ft.k === "f32") {
        return e_at(e_bin(e_atom(vs[i]), G.pick(["+", "*"]), num_lit_f32(false)));
      }
      if (f.k === "adt" && f.a === a) {
        return name + "(" + vs[i] + ")";
      }
      return vs[i];
    });
    return "    case " + adt_pattern(a, c, vs) + ":\n      " + adt_value(a, c, args);
  });
  DEFS.push("def " + name + "(x: " + ty_str(t) + ") -> " + ty_str(t) + ":\n  match x:\n" + rows.join("\n"));
  DEFR.push({ name, tps: [], ps: [t], ret: t });
  return name;
}

// Call
// ----
// tail-recursive countdown state machines: 0-switch on the first column,
// extra scalar accumulators, n-1 decrease. The compiled seq machine's bread
// and butter.

export function call_helper(env: V[], fuel: number): E {
  feature_add("tail");
  const name = "tl" + String(uid_next());
  const naccs = G.decay(0.35);
  const accs = Array.from({ length: naccs }, (_, i) => "a" + String(i));
  const henv: V[] = accs.map((a) => v_many(a, U32C));
  const base = e_at(num_combine(accs.map((a) => e_atom(a)).concat([num_lit_u32()])));
  const K = size_pick(G.chance(0.25) ? 2 + G.int(8) : 1, 4000);
  // deck : k>=2 dec descent must bind FRESH (shadowing the scrutinee
  // loses the Inc-slot descent) and the descending param must sit LAST
  // (position-sensitivity, repro_dec_swi_position.bend); k=1 keeps the
  // canonical first-position rebind spelling
  const db = K === 1 ? "n" : "nk" + String(uid_next());
  const step = accs.map(() => e_at(num_gen_u32(henv.concat([v_many(db, U32C)]), 1)));
  if (K > 1) {
    feature_add("deck");
  }
  const params = K === 1
    ? ["n: U32"].concat(accs.map((a) => a + ": U32"))
    : accs.map((a) => a + ": U32").concat(["n: U32"]);
  const arms = K === 1
    ? "  match n:\n    case 0:\n      " + base + "\n    case 1+n:\n      " + name + "(n, " + step.join(", ") + ")"
    : "  match n:\n" + (G.chance(0.3) ? "    case 0:\n      " + e_at(num_combine(accs.map((a) => e_atom(a)).concat([num_lit_u32()]))) + "\n" : "")
      + "    case " + String(K) + "+" + db + ":\n      " + name + "(" + step.concat([db]).join(", ") + ")\n    case n:\n      " + base;
  DEFS.push("def " + name + "(" + params.join(", ") + ") -> U32:\n" + arms);
  DEFR.push({ name, tps: [], ps: params.map(() => U32C), ret: U32C, mask: params.map((_, i) => (i === (K === 1 ? 0 : params.length - 1) ? 16 : null)) });
  const iters = String(size_pick(2 + G.int(14), 200000));
  const args = accs.map(() => e_at(num_gen_u32(env, Math.min(fuel - 1, 1))));
  return e_defcall(name, name + "(" + (K === 1 ? [iters].concat(args) : args.concat([iters])).join(", ") + ")");
}

export function call_hof(env: V[], fuel: number): E {
  feature_add("hof");
  const name = "hf" + String(uid_next());
  const henv: V[] = [v_many("x", U32C)];
  const rParts = [e_atom("f(" + e_at(num_gen_u32(henv, 1)) + ")"), num_gen_u32(henv, 1)];
  DEFS.push("def " + name + "(f: (U32 -> U32), x: U32) -> U32:\n  " + e_at(num_combine(rParts)));
  const lam = syn({ k: "fun", dom: U32C, cod: U32C }, env, Math.min(fuel - 1, 1));
  return e_defcall(name, name + "(" + e_at(lam) + ", " + e_at(num_gen_u32(env, Math.min(fuel - 1, 1))) + ")");
}

// Generic
// -------
// erased Type params through the <> sugar; params and return mention the
// tvars, so unification instantiates them at ANY synthesized type. Bodies
// treat tvar-typed params as strictly linear (the abstract-contraction
// compiler gap) and are synthesized like any hole.

export function generic_mint(): void {
  feature_add("generic");
  const name = "g" + String(uid_next());
  const ntv = G.chance(0.35) ? 2 : 1;
  const tps = ["A", "B"].slice(0, ntv);
  const tA: T = { k: "tvar", n: "A" };
  const ps: T[] = [tA];
  if (G.chance(0.4)) {
    ps.push(G.wpick<T>([[40, U32C], [30, { k: "adt", a: need_list(), args: [tA] }], [ntv > 1 ? 30 : 0, { k: "tvar", n: "B" }]]));
  }
  const ret = G.wpick<T>([[50, tA], [30, { k: "adt", a: need_list(), args: [tA] }], [20, U32C]]);
  const penv = ps.map((p, i) => {
    const v = v_many("p" + String(i), p);
    if (p.k === "tvar" || !ty_data(p)) {
      v.q = "once";
    }
    return v;
  });
  let body: E;
  try {
    body = syn(ret, penv, 1);
  } catch {
    body = ret.k === "u32" ? num_lit_u32() : ret.k === "tvar" ? e_atom("p0") : e_atom("Nil{}");
  }
  const params = ps.map((p, i) => "p" + String(i) + ": " + ty_str(p));
  DEFS.push("def " + name + "<" + tps.join(",") + ">(" + params.join(", ") + ") -> " + ty_str(ret) + ":\n  " + e_at(body));
  DEFR.push({ name, tps, ps, ret });
}

// Batch
// -----
// def bt(d: U32, i: U32) -> U32 with an internal parallel let: the ONE real
// fork shape (prep_forks marks it; par_ emission + the task bag run it).

export function batch_ensure(): string {
  const got = BUILDERS.get("batch");
  if (got !== undefined) {
    return got;
  }
  const name = "bt" + String(uid_next());
  BUILDERS.set("batch", name);
  const lenv: V[] = [v_many("i", U32C)];
  const leaf = e_at(num_combine([e_bin(e_bin(e_atom("i"), "*", e_atom("2654435761")), ".&.", e_atom("8191")), num_gen_u32(lenv, 1)]));
  const c0 = String(G.int(4));
  const c1 = String(G.int(4));
  DEFS.push("def " + name + "(d: U32, i: U32) -> U32:\n  match d:\n    case 0:\n      " + leaf
    + "\n    case 1+d:\n      a, b = " + name + "(d, i * 2 + " + c0 + "), " + name + "(d, i * 2 + " + c1 + ")\n      "
    + e_at(num_combine([e_atom("a"), e_atom("b")])));
  return name;
}

// Match
// -----
// match trees exercising the flattener and the check-time computed-match
// split (fn~i minting). Computed scrutinees are var-headed (a constant one
// normalizes at the split and strands literal/ctor arms as unreachable
// rows); nested matches only scrutinize the arm's own binders or computed
// expressions; V.not keeps miss-binder chains off already-taken literals.

export function match_scrut_num(env: V[], mod: number): E {
  const v = G.pick(env_nums(env));
  return e_bin(e_bin(e_atom(v.name), G.pick(["+", "*", ".^."]), num_gen_u32(env, 1)), "%", e_atom(String(mod)));
}

export function match_body(env: V[], depth: number, ind: number): string {
  const pad = " ".repeat(ind);
  if (depth <= 0 || G.chance(0.3)) {
    const lines: string[] = [];
    const names = env_nums(env).map((v) => e_atom(v.name));
    if (G.chance(0.4)) {
      const x = "v" + String(uid_next());
      lines.push(pad + x + " = " + e_at(num_gen_u32(env, 2)));
      names.push(e_atom(x));
    }
    names.push(num_gen_u32(env, 1));
    lines.push(pad + e_at(num_combine(names)));
    return lines.join("\n");
  }
  const scal = env_nums(env).length > 0;
  const kind = G.wpick<string>([
    [scal ? 35 : 0, "num"], [scal ? 20 : 0, "cmp"],
    [scal && ADTS.some((a) => a.rec && a.dep !== true) ? 25 : 0, "adt"],
    [scal ? 15 : 0, "multi"],
    [scal ? 0 : 1, "leaf"],
  ]);
  if (kind === "leaf") {
    return match_body(env, 0, ind);
  }
  if (kind === "adt") {
    const a = G.pick(ADTS.filter((x) => x.rec && x.dep !== true));
    const t: T = { k: "adt", a, args: a.tvars.map(() => syn_ty(0, true)) };
    const m = new Map<string, T>(a.tvars.map((n, i) => [n, t.args[i]]));
    const mk = builder_ensure(t as T & { k: "adt" });
    const scrut = mk + "(" + e_at(match_scrut_num(env, size_pick(3 + G.int(5), 2000))) + ")";
    const arms = a.ctors.map((c) => {
      const vs = c.fields.map((_, i) => "m" + String(uid_next()));
      const folded = c.fields
        .flatMap((f, i) => {
          if (i === c.er) {
            return [];
          }
          const ft = ty_sub(f, m);
          if (ft.k === "u32") {
            return [e_atom(vs[i])];
          }
          if (ft.k === "f32") {
            return [e_fn1("$f32_to_u32", e_atom(vs[i]))];
          }
          return [e_atom(rd_ensure(ft) + "(" + vs[i] + ")")];
        })
        .concat([num_gen_u32(env.concat(c.fields.flatMap((f, i) => (i !== c.er && ty_sub(f, m).k === "u32" ? [v_many(vs[i], U32C)] : []))), 1)]);
      const pat = c.name + "{" + vs.join(", ") + "}";
      return pad + "  case " + pat + ":\n" + " ".repeat(ind + 4) + e_at(num_combine(folded));
    });
    feature_add("with");
    return pad + "match " + scrut + ":\n" + arms.join("\n");
  }
  if (kind === "multi") {
    feature_add("multi");
    const s1 = e_at(match_scrut_num(env, 2 + G.int(4)));
    const s2 = e_at(match_scrut_num(env, 2 + G.int(4)));
    const k1 = "k" + String(uid_next());
    const k2 = "k" + String(uid_next());
    const arm = (extra: V[]): string => match_body(env.concat(extra), 0, ind + 4);
    return pad + "match " + s1 + ", " + s2 + ":\n"
      + pad + "  case 0, 0:\n" + arm([]) + "\n"
      + pad + "  case 0, " + k2 + ":\n" + arm([v_many(k2, U32C)]) + "\n"
      + pad + "  case " + k1 + ", 0:\n" + arm([v_many(k1, U32C)]) + "\n"
      + pad + "  case " + k1 + ", " + k2 + ":\n" + arm([v_many(k1, U32C), v_many(k2, U32C)]);
  }
  let scrut: string;
  let arm_env = env;
  let taken: number[] = [];
  if (kind === "cmp") {
    scrut = e_at(e_bin(e_atom(G.pick(env_nums(env)).name), G.pick(["<", "<=", "==", ">"]), num_gen_u32(env, 1)));
    feature_add("with");
  } else if (G.chance(0.4)) {
    const picked = G.pick(env_nums(env));
    scrut = picked.name;
    arm_env = env.filter((v) => v !== picked);
    taken = picked.not ?? [];
  } else {
    scrut = e_at(match_scrut_num(env, size_pick(2 + G.int(6), 2000)));
    feature_add("with");
  }
  const avail = [0, 1, 2, 3, 4, 5, 6, 7].filter((l) => !taken.includes(l));
  const lits = [avail[0]];
  if (kind !== "cmp" && avail.length > 1 && G.chance(0.35)) {
    lits.push(avail[1 + G.int(avail.length - 1)]);
  }
  const wide = kind !== "cmp" ? size_pick(0, 400) : 0;
  for (let l = 8; l < 8 + wide; l++) {
    lits.push(l);
  }
  const v = "k" + String(uid_next());
  const chosen = [...new Set(lits)].sort((x, y) => x - y);
  const rows: string[] = [];
  for (const l of chosen) {
    rows.push(pad + "  case " + String(l) + ":\n" + match_body(arm_env, depth - 1, ind + 4));
  }
  const dv = v_many(v, U32C);
  dv.not = taken.concat(chosen);
  rows.push(pad + "  case " + v + ":\n" + match_body(arm_env.concat([dv]), depth - 1, ind + 4));
  return pad + "match " + scrut + ":\n" + rows.join("\n");
}

export function match_call_def(env: V[], fuel: number): E {
  feature_add("match");
  const name = "mt" + String(uid_next());
  const henv: V[] = [v_many("s", U32C)];
  const body = match_body(henv, 1 + G.int(2), 2);
  DEFS.push("def " + name + "(s: U32) -> U32:\n" + body);
  DEFR.push({ name, tps: [], ps: [U32C], ret: U32C });
  return e_defcall(name, name + "(" + e_at(num_gen_u32(env, Math.min(fuel, 1))) + ")");
}

// String
// ------
// string-literal patterns above a var fallback row; the argument sometimes
// matches the literal so both arms run across seeds. Char-literal patterns
// ride the same flattener path.

export function string_call_def(env: V[]): E {
  feature_add("str");
  const st = need_str();
  const name = "sp" + String(uid_next());
  const lit = str_lit(1 + G.int(4));
  const fall = rd_ensure(st);
  DEFS.push("def " + name + "(s: String) -> U32:\n  match s:\n    case " + lit + ":\n      " + e_at(num_gen_u32([], 1)) + "\n    case s:\n      " + fall + "(s)");
  const arg = G.wpick<() => string>([
    [40, () => lit],
    [40, () => e_at(syn(st, env, 1))],
    [20, () => "'" + str_char() + "' <> " + lit],
  ])();
  return e_defcall(name, name + "(" + arg + ")");
}

export function string_call_char_def(env: V[]): E {
  feature_add("chr");
  need_char();
  IMPORTS.add("List");
  const name = "cv" + String(uid_next());
  const c1 = str_char();
  DEFS.push("def " + name + "(c: Char) -> U32:\n  match c:\n    case '" + c1 + "':\n      " + e_at(num_gen_u32([], 1)) + "\n    case Char{n}:\n      n + " + String(G.int(99)));
  const arg = G.chance(0.4) ? "'" + c1 + "'" : "'" + str_char() + "'";
  void env;
  return e_defcall(name, name + "(" + arg + ")");
}

// Do
// --
// a minted one-ctor monad + M::pure/M::bind and a def whose body is a do
// block; parse-time sugar over the bind/pure convention.

export function do_call_def(env: V[]): E {
  feature_add("do");
  const id = uid_next();
  const M = "Bx" + String(id);
  const C = M + "v";
  DECLS.push("type " + M + "<A>:\n  " + C + "{v: A}");
  DEFS.push("def " + M + "::pure<A>(x: A) -> " + M + "<A>:\n  " + C + "{x}");
  DEFS.push("def " + M + "::bind<A,B>(m: " + M + "<A>, f: A -> " + M + "<B>) -> " + M + "<B>:\n  match m:\n    case " + C + "{v}:\n      f(v)");
  const un = "ub" + String(uid_next());
  DEFS.push("def " + un + "(b: " + M + "<U32>) -> U32:\n  match b:\n    case " + C + "{v}:\n      v");
  const name = "dm" + String(uid_next());
  const henv: V[] = [v_many("n", U32C)];
  const x = "x" + String(uid_next());
  const y = "y" + String(uid_next());
  DEFS.push("def " + name + "(n: U32) -> " + M + "<U32>:\n  do " + M + "<U32>:\n    "
    + x + " <- {" + C + "{" + e_at(num_gen_u32(henv, 1)) + "} : " + M + "<U32>}\n    "
    + y + " <- {" + C + "{" + e_at(num_gen_u32(henv.concat([v_many(x, U32C)]), 1)) + "} : " + M + "<U32>}\n    "
    + "return " + e_at(num_combine([e_atom(x), e_atom(y), num_gen_u32(henv, 0)])));
  return e_defcall(un, un + "(" + name + "(" + e_at(num_gen_u32(env, 1)) + "))");
}

// Theorem
// -------
// an equational development over a minted Nat: dependent elimination,
// Eql/Rfl/Rwt through the checker. Returns the pieces so main can also USE
// the theorem live (`% th(n) e` — the rewrite runs, consumes its proof, and
// sheds once it reaches {=}).

export function theorem_gen(): { N: string; th: string; z: string; s: string; add: string; arity: number } {
  feature_add("thm");
  const id = uid_next();
  const N = "Nt" + String(id);
  const Z = N + "z";
  const S = N + "s";
  DECLS.push("type " + N + ":\n  " + Z + "{}\n  " + S + "{p: " + N + "}");
  // k : the OP under proof is generated -- op(z, b) = S^k(b) and
  // op(s{p}, b) = S^m(op(p, b)) denote S^(m*a+k)(b), so the shift law
  // op(a, s{b}) = s{op(a, b)} holds for EVERY k and m by the same
  // two-line induction: statement, definition and conversion work all
  // vary while the skeleton stays schema-driven (the right-identity
  // law needs op to BE addition, so it rides k=0, m=1)
  const k = G.int(3);
  const m = 1 + G.int(3);
  const wrap = (n: number, x: string): string => {
    for (let i = 0; i < n; i++) {
      x = S + "{" + x + "}";
    }
    return x;
  };
  const add = "ad" + String(uid_next());
  DEFS.push("def " + add + "(a: " + N + ", b: " + N + ") -> " + N + ":\n  match a:\n    case " + Z + "{}:\n      "
    + wrap(k, "b") + "\n    case " + S + "{p}:\n      " + wrap(m, add + "(p, b)"));
  const th = "th" + String(uid_next());
  if (k > 0 || m > 1 || G.chance(0.5)) {
    feature_add("thm-shift");
    const b = "b" + String(uid_next());
    DEFS.push("def " + th + "(a: " + N + ", " + b + ": " + N + ") -> {" + add + "(a, " + S + "{" + b + "}) = " + S + "{" + add + "(a, " + b + ")} : " + N + "}:\n  match a:\n    case " + Z + "{}:\n      {=}\n    case " + S + "{p}:\n      %" + th + "(p, " + b + ")\n      {=}");
    return { N, th, z: Z, s: S, add, arity: 2 };
  }
  DEFS.push("def " + th + "(a: " + N + ") -> {" + add + "(a, " + Z + "{}) = a : " + N + "}:\n  match a:\n    case " + Z + "{}:\n      {=}\n    case " + S + "{p}:\n      %" + th + "(p)\n      {=}");
  return { N, th, z: Z, s: S, add, arity: 1 };
}

// Destructure
// -----------
// `K{a,b} = v` — one-case match at statement head; single-ctor ADTs only.
// The value depends on runtime vars where possible (destructuring an
// all-concrete call makes the checker run it at check time).

export function destructure_gen(): { defname: string } {
  feature_add("destr");
  const id = uid_next();
  const a: Adt = { name: "R" + String(id), tvars: [], ctors: [], rec: false, data: [] };
  const nf = 2 + G.int(2);
  a.ctors.push({ name: "R" + String(id) + "a", fields: Array.from({ length: nf }, () => U32C as T), er: -1 });
  DECLS.push("type " + a.name + ":\n  " + a.ctors[0].name + "{" + a.ctors[0].fields.map((_, i) => "f" + String(i) + ": U32").join(", ") + "}");
  ADTS.push(a);
  const mk = "mr" + String(uid_next());
  const menv: V[] = [v_many("n", U32C)];
  DEFS.push("def " + mk + "(n: U32) -> " + a.name + ":\n  " + a.ctors[0].name + "{" + a.ctors[0].fields.map(() => e_at(num_gen_u32(menv, 1))).join(", ") + "}");
  const name = "ds" + String(uid_next());
  const vs = a.ctors[0].fields.map((_, i) => "d" + String(i));
  const denv: V[] = vs.map((v) => v_many(v, U32C)).concat([v_many("n", U32C)]);
  DEFS.push("def " + name + "(n: U32) -> U32:\n  " + a.ctors[0].name + "{" + vs.join(", ") + "} = " + mk + "(" + e_at(num_gen_u32([v_many("n", U32C)], 1)) + ")\n  " + e_at(num_combine(vs.map((v) => e_atom(v)).concat([num_gen_u32(denv, 1)]))));
  return { defname: name };
}

// Shared
// ------

export function shared_ensure_user(): string {
  if (SHUSER !== "") {
    return SHUSER;
  }
  const name = "us" + String(uid_next());
  SHUSER = name;
  const henv: V[] = [v_many("s", U32C), v_many("k", U32C)];
  DEFS.push("def " + name + "(s: U32, k: U32) -> U32:\n  " + e_at(num_combine([e_atom("s"), e_atom("s"), num_gen_u32(henv, 1)])));
  return name;
}

// GPU marks
// ---------
// f!(args): a zero-semantics placement request on a top-level def call —
// honored on a Metal/CUDA build at a sequential point, inert otherwise. The
// coin is an RNG draw, so both parenthesization modes agree.

export function gpu_mark(): string {
  if (G.chance(0.2)) {
    feature_add("gpu");
    return "!";
  }
  return "";
}

// Let
// ---
// binds: U32 expressions folded into the result. vars: typed values kept in
// scope for later synthesis; folding and the environment are independent.
// eqs: equality-let names consumed by the final term's rewrite chain.

type Line = { text: string; binds: string[]; vars: V[]; eqs?: string[] };

export function let_scalar(env: V[]): Line {
  const x = "v" + String(uid_next());
  return { text: x + " = " + e_at(num_gen_u32(env, 2 + G.int(3))), binds: [x], vars: [v_many(x, U32C)] };
}

export function let_value(env: V[]): Line {
  const prior = env.filter((v) => v.q !== "dead" && v.ty.k !== "u32" && ty_data(v.ty));
  const reuse = prior.length > 0 && G.chance(0.4);
  const t = reuse ? G.pick(prior).ty : syn_ty(size_pick(2, 8), false);
  if (reuse) {
    feature_add("typed-reuse");
  }
  if (t.k === "u32") {
    return let_scalar(env);
  }
  feature_add(t.k === "fun" ? "clo" : "value");
  const x = "v" + String(uid_next());
  const y = "v" + String(uid_next());
  const val = MINTS < 8 && G.chance(0.4) ? syn_mint_def(t, env) ?? syn(t, env, 2 + G.int(2)) : syn(t, env, size_pick(2 + G.int(2), 7));
  const mono = t.k === "adt" && t.a.dep !== true;
  const kind = G.wpick<string>([
    [50, "plain"],
    [mono ? 20 : 0, "tf"],
    [ty_data(t) ? 15 : 0, "twice"],
  ]);
  let fold: string;
  const rd = rd_ensure(t);
  if (kind === "tf") {
    feature_add("reuse");
    fold = rd + "(" + tf_ensure(t as T & { k: "adt" }) + "(" + x + "))";
  } else if (kind === "twice") {
    feature_add("dup");
    fold = rd + "(" + x + ") + " + rd + "(" + x + ")";
  } else {
    fold = rd + "(" + x + ")";
  }
  const text = e_ann_bind(x, val, ty_str(t)) + "\n  " + y + " = " + fold;
  const vars = [v_many(y, U32C)];
  if (ty_data(t)) {
    vars.push(v_many(x, t));
  }
  return { text, binds: [y], vars };
}

const CONST_OPS: Array<[string, (a: number, b: number) => number]> = [
  ["+", (a, b) => (a + b) >>> 0],
  ["-", (a, b) => (a - b) >>> 0],
  ["*", (a, b) => Math.imul(a, b) >>> 0],
  [".^.", (a, b) => (a ^ b) >>> 0],
  [".&.", (a, b) => (a & b) >>> 0],
  [".|.", (a, b) => (a | b) >>> 0],
  ["<<", (a, b) => (a << (b & 31)) >>> 0],
  [">>", (a, b) => a >>> (b & 31)],
  ["==", (a, b) => (a === b ? 1 : 0)],
  ["<", (a, b) => (a < b ? 1 : 0)],
];

// let_eql : safe marks which equations may feed a % REWRITE: a generic
// instantiation's nullary ctor is identical to its siblings' after
// type-arg erasure, so rewriting such an equation corrupts any ctx
// hypothesis holding the other instantiation (A-class; the ctx face is
// repro_rwt_ctx_cross.bend) -- those equations stay BOUND (the Eql
// intro still checks) but are not %-applied while A is open
export function let_eql(env: V[]): Line {
  feature_add("eql");
  const x = "e" + String(uid_next());
  let ety: string;
  let safe = true;
  if (G.chance(0.3)) {
    feature_add("ceql");
    const num = (): number => G.wpick<() => number>([[40, () => G.int(16)], [30, () => G.int(1000)], [30, () => G.int(4294967296)]])();
    const [op, f] = G.pick(CONST_OPS);
    const a = num();
    const b = num();
    const lhs = "(" + String(a) + " " + op + " " + String(b) + ")";
    const r = String(f(a, b));
    ety = G.chance(0.5) ? "{" + lhs + " = " + r + " : U32}" : "{" + r + " = " + lhs + " : U32}";
  } else {
    const base = syn_ty(1, true);
    let t = base.k === "eql" ? U32C : base;
    const menv = env.filter((v) => v.q === "many");
    let side = e_at(syn(t, menv, 1));
    const prev = SIDES.get(side);
    if (prev !== undefined && prev !== ty_key(t)) {
      t = U32C;
      side = String(3000000000 + G.int(1000000000));
    }
    SIDES.set(side, ty_key(t));
    ety = ty_str({ k: "eql", t, side });
    safe = t.k === "u32" || t.k === "f32" || (t.k === "adt" && t.args.length === 0);
  }
  const etext = x + " = {{=} : " + ety + "}";
  if (safe && G.chance(0.35)) {
    feature_add("rwte");
    const w = "v" + String(uid_next());
    // mot : a motive is a FUNCTION now (lhs-type -> Type), so the
    // constant motive is a constant lambda; its body parse is greedy (a
    // following parenthesized term reads as its application), so the
    // explicit form needs the `;` separator
    const mot = G.chance(0.4) ? x + " : mw" + String(uid_next()) + " => U32; " : " " + x + " ";
    return { text: etext + "\n  " + w + " = {(%" + mot + e_at(num_gen_u32(env, 1)) + ") : U32}", binds: [w], vars: [v_many(w, U32C)] };
  }
  return { text: etext, binds: [], vars: [], eqs: safe ? [x] : [] };
}

export function let_fork(env: V[]): Line {
  feature_add("fork");
  // ncalls : fork arities are 2, 4, 8, 16 or 32 -- a stretched draw
  // snaps DOWN to the ladder (0 and 1 mean no fork at all)
  const raw = size_pick(G.wpick<number>([[60, 2], [18, 4], [12, 0], [10, 1]]), 40);
  const ncalls = [32, 16, 8, 4, 2, 1, 0].find((n) => n <= raw) ?? 0;
  const nvals = ncalls >= 2 ? (G.chance(0.35) ? 1 + G.int(2) : 0) : 2 + G.int(2);
  const mkcall = (): string => {
    if (G.chance(0.4)) {
      return batch_ensure() + gpu_mark() + "(" + String(2 + G.int(3) + (HEAVY ? 2 : 0)) + ", " + e_at(num_gen_u32(env, 1)) + ")";
    }
    return call_helper(env, 2).s;
  };
  const vals: string[] = [];
  for (let i = 0; i < ncalls; i++) {
    vals.push(mkcall());
  }
  for (let i = 0; i < nvals; i++) {
    vals.push(e_at(num_gen_u32(env, 1)));
  }
  for (let i = vals.length - 1; i > 0; i--) {
    const j = G.int(i + 1);
    const t = vals[i];
    vals[i] = vals[j];
    vals[j] = t;
  }
  const ks = vals.map(() => "p" + String(uid_next()));
  return { text: ks.join(", ") + " = " + vals.join(", "), binds: ks, vars: ks.map((k) => v_many(k, U32C)) };
}

export function let_adt_dflt(a: Adt): string | null {
  const ok = a.ctors.filter((c) => c.er < 0 && (c.fields.length === 0 || (c.fields.length === 1 && c.fields[0].k === "u32")));
  if (ok.length === 0) {
    return null;
  }
  const c = G.pick(ok);
  return c.fields.length === 0 ? c.name + "{}" : c.name + "{" + String(G.int(64)) + "}";
}

export function let_array(env: V[]): Line {
  feature_add("array");
  const able = ADTS.filter((x) =>
    x.tvars.length === 0 && x.dep !== true && x.data !== null
    && x.ctors.some((c) => c.er < 0 && (c.fields.length === 0 || (c.fields.length === 1 && c.fields[0].k === "u32"))));
  const mode = G.wpick<string>([[60, "u32"], [able.length > 0 ? 40 : 0, "adt"]]);
  const a = mode === "u32" ? null : G.pick(able);
  const elT: T = a !== null ? { k: "adt", a, args: [] } : U32C;
  const tyArr = "[:" + ty_str(elT) + "]";
  const wrap = (e: E): string => (e.p === 99 ? e.s : "(" + e.s + ")");
  const elV = (): string => {
    const v = syn(elT, env, a !== null ? 1 : 0);
    return a !== null ? "{" + v.s + " : " + a.name + "}" : wrap(v);
  };
  const dflt = a !== null ? (let_adt_dflt(a) as string) : String(G.int(100));
  const big = a === null && G.chance(0.05);
  const nkeys = size_pick(G.int(4), 48);
  const keys = [...new Set(Array.from({ length: nkeys }, () => (big ? 40000 + G.int(200000) : G.int(8))))].sort((x, y) => x - y);
  if (big) {
    feature_add("bigarr");
  }
  const maxk = keys.length > 0 ? keys[keys.length - 1] : 0;
  const len = maxk < 8 ? 8 : 2 ** (32 - Math.clz32(maxk));
  const lit = "[" + keys.map((k) => String(k) + ": " + elV() + ", ").join("") + "_: " + dflt + "; " + String(len) + "]";
  let cur = "ar" + String(uid_next());
  const lines: string[] = [cur + " = {" + lit + " : " + tyArr + "}"];
  const binds: string[] = [];
  const vars: V[] = [];
  const idx = (): string => {
    const r = G.int(10);
    if (r < 6) {
      return String(G.int(maxk + 1));
    }
    if (r < 8) {
      return String(maxk + 1 + G.int(16));
    }
    if (r < 9) {
      return e_at(e_bin(num_gen_u32(env, 1), "%", e_atom(String(maxk + 2))));
    }
    return "4294967295";
  };
  const nops = 1 + G.int(3);
  for (let i = 0; i < nops; i++) {
    const ren = G.chance(0.5);
    const nxt = ren ? "ar" + String(uid_next()) : cur;
    const at = ren ? cur + "@" + nxt : cur;
    // get : Get is word-only (the refcount removal's gate), so element
    // reads happen on u32 arrays alone; an ADT array is set/swap only,
    // and the SET's yield -- the displaced old element, owned -- is what
    // gets folded
    if (a === null && G.chance(0.5)) {
      const x = "v" + String(uid_next());
      lines.push(x + " = " + at + "[" + idx() + "]");
      binds.push(x);
      vars.push(v_many(x, U32C));
    } else {
      const x = G.chance(0.2) ? "_" : "v" + String(uid_next());
      lines.push(x + " = " + at + "[" + idx() + "] <- " + elV());
      if (x !== "_") {
        binds.push(a !== null ? rd_ensure(elT) + "(" + x + ")" : x);
        vars.push(v_many(x, elT));
      }
    }
    cur = nxt;
  }
  return { text: lines.join("\n  "), binds, vars };
}

export function let_float(env: V[]): Line {
  feature_add("f32");
  const f = "f" + String(uid_next());
  const x = "v" + String(uid_next());
  const val = num_gen_f32(env, 2 + G.int(2));
  const rhs = G.chance(0.7) ? e_fn1("$f32_to_u32", e_atom(f)) : e_bin(e_atom(f), G.pick(["<", "<=", ">=", "!=", "=="]), num_gen_f32(env, 2));
  return { text: e_ann_bind(f, val, "F32") + "\n  " + x + " = " + e_at(rhs), binds: [x], vars: [v_many(f, F32C), v_many(x, U32C)] };
}

export function let_call(env: V[]): Line {
  const x = "v" + String(uid_next());
  const e = G.wpick<() => E>([
    [24, () => match_call_def(env, 1)],
    [18, () => call_helper(env, 2)],
    [14, () => call_hof(env, 1)],
    [30, () => syn_form(U32C, env, 3)],
    [12, () => string_call_def(env)],
    [8, () => string_call_char_def(env)],
    [8, () => {
      const d = destructure_gen().defname;
      return e_defcall(d, d + "(" + e_at(num_gen_u32(env, 1)) + ")");
    }],
    [10, () => {
      generic_mint();
      return syn_call_unify(U32C, env, 2) ?? num_gen_u32(env, 2);
    }],
    [6, () => do_call_def(env)],
  ])();
  const s = e.head !== undefined && gpu_mark() !== "" ? e.head + "!" + e.s.slice(e.head.length) : e.s;
  return { text: x + " = " + (e.p === 99 ? s : MIN_PARENS ? s : "(" + s + ")"), binds: [x], vars: [v_many(x, U32C)] };
}

export function let_partial(env: V[]): Line {
  feature_add("clo");
  const name = "pa" + String(uid_next());
  const henv: V[] = [v_many("a", U32C), v_many("b", U32C), v_many("c", U32C)];
  DEFS.push("def " + name + "(a: U32, b: U32, c: U32) -> U32:\n  " + e_at(num_combine([e_atom("a"), e_atom("b"), e_atom("c"), num_gen_u32(henv, 1)])));
  DEFR.push({ name, tps: [], ps: [U32C, U32C, U32C], ret: U32C });
  const g = "g" + String(uid_next());
  const x = "v" + String(uid_next());
  const lines: string[] = [];
  if (G.chance(0.5)) {
    lines.push(g + " = " + name + gpu_mark() + "(" + e_at(num_gen_u32(env, 1)) + ")");
    lines.push(x + " = " + g + "(" + e_at(num_gen_u32(env, 1)) + ", " + e_at(num_gen_u32(env, 1)) + ")");
  } else {
    const fun: T = { k: "fun", dom: U32C, cod: U32C };
    const lam = syn(fun, env, 1);
    lines.push(g + " = {" + lam.s + " : " + ty_str(fun) + "}");
    const hf = "hg" + String(uid_next());
    DEFS.push("def " + hf + "(f: (U32 -> U32), x: U32) -> U32:\n  f(x) + x");
    lines.push(x + " = " + hf + "(" + g + ", " + e_at(num_gen_u32(env, 1)) + ")");
  }
  return { text: lines.join("\n  "), binds: [x], vars: [v_many(x, U32C)] };
}

// let_truth : The truth bridges (bend 9b291a30): the machine word (0 false, else
// true) and Bool (F{}/T{}) are one thing, and the checker joins them at
// every branch. Three directions, all type-directed at elaboration, so
// each is a distinct path: T/F patterns over a WORD scrutinee, an `if`
// over a BOOL, and a word coerced where Bool is expected. Minted as defs
// because a match may not sit in a let value.
export function let_truth(env: V[]): Line {
  feature_add("truth");
  IMPORTS.add("Bool");
  const name = "tb" + String(uid_next());
  const x = "v" + String(uid_next());
  const lo = String(G.int(1000));
  const hi = String(G.int(1000));
  const body = G.wpick<() => string>([
    // truth_pat : T{}/F{} patterns over a U32 scrutinee: term_elab_split wraps it in
    // Bool::from_u32
    [10, () => {
      feature_add("truth-pat");
      return "  match n:\n    case T{}:\n      " + lo + "\n    case F{}:\n      " + hi;
    }],
    // truth_if : an if over a Bool: term_check's Swi arm rebuilds it as the F/T match
    [9, () => {
      feature_add("truth-if");
      return "  if Bool::from_u32(n):\n    " + lo + "\n  else:\n    " + hi;
    }],
    // truth_meet : a U32 met where Bool is expected coerces at term_elab_meet
    [8, () => {
      feature_add("truth-meet");
      return "  Bool::to_u32(Bool::not(n)) + " + lo;
    }],
  ])();
  DEFS.push("def " + name + "(n: U32) -> U32:\n" + body);
  DEFR.push({ name, tps: [], ps: [U32C], ret: U32C });
  return {
    text: x + " = " + name + "(" + e_at(num_gen_u32(env, 1)) + ")",
    binds: [x],
    vars: [v_many(x, U32C)],
  };
}

// let_shared : contraction on purpose -- an extra owner of a Data value
// is an inferred deep copy (copy$), a read under a dominating owner a
// borrow. The def's param is used twice (param contraction) and the
// binder feeds both that call and a direct fold (statement contraction).
export function let_shared(env: V[]): Line {
  feature_add("share");
  const s = "sh" + String(uid_next());
  const x = "v" + String(uid_next());
  const y = "v" + String(uid_next());
  const able = ADTS.filter((a) => a.tvars.length === 0 && a.data !== null && a.dep !== true);
  if (able.length > 0 && G.chance(0.35)) {
    feature_add("shp");
    const a = G.pick(able);
    const dt: T = { k: "adt", a, args: [] };
    const rdp = rd_ensure(dt);
    const us = "us" + String(uid_next());
    DEFS.push("def " + us + "(s: " + a.name + ", k: U32) -> U32:\n  " + e_at(num_combine([e_atom(rdp + "(s)"), e_atom(rdp + "(s)"), e_atom("k")])));
    const val = syn(dt, env, 2);
    const lines = [
      e_ann_bind(s, val, a.name),
      x + " = " + us + "(" + s + ", " + e_at(num_gen_u32(env, 1)) + ")",
      y + " = " + rdp + "(" + s + ") + " + x,
    ];
    return { text: lines.join("\n  "), binds: [x, y], vars: [v_many(s, dt), v_many(x, U32C), v_many(y, U32C)] };
  }
  const us = shared_ensure_user();
  const val = num_gen_u32(env, 2);
  const lines = [
    s + " = " + e_at(val),
    x + " = " + us + "(" + s + ", " + e_at(num_gen_u32(env, 1)) + ")",
    y + " = " + s + " + " + x,
  ];
  return { text: lines.join("\n  "), binds: [x, y], vars: [v_many(s, U32C), v_many(x, U32C), v_many(y, U32C)] };
}

// Gen
// ---

export function gen_reset(seed: bigint, minParens: boolean, uid0 = 0): void {
  G = new Gen(rng_mix64(seed));
  MIN_PARENS = minParens;
  UID = uid0;
  DECLS = [];
  DEFS = [];
  ADTS = [];
  LISTA = null;
  CHARA = null;
  PAIRA = null;
  UNITA = null;
  IMPORTS = new Set();
  REDUCES = new Map();
  RD_WIP = new Set();
  BUILDERS = new Map();
  BUILDER_WIDE = new Set();
  TRANSFORMS = new Map();
  SHUSER = "";
  SIDES = new Map();
  MINTS = 0;
  DEFR = [];
  FEAT = {};
}

// mod_names : the top-level names a DECLS/DEFS entry defines (the assert
// name and its fill share one name; ctor tags are NOT collected -- they
// resolve bare across imports)
export function mod_names(entry: string): string[] {
  const m = entry.match(/^(?:def|type|assert) ([A-Za-z0-9_:]+)/);
  return m === null ? [] : [m[1].replace(/:+$/, "")];
}

// mod_qualify : rewrite whole-identifier occurrences of moved names to
// their <mod>::<name> spelling, skipping string/char/backtick literals
export function mod_qualify(text: string, map: Map<string, string>): string {
  if (map.size === 0) {
    return text;
  }
  const lit = /"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])'|`[^`]`/g;
  const sub = (s: string): string => s.replace(/[A-Za-z_][A-Za-z0-9_]*(?:::[A-Za-z_][A-Za-z0-9_]*)*/g, (w) => map.get(w) ?? w);
  let out = "";
  let last = 0;
  for (const m of text.matchAll(lit)) {
    out += sub(text.slice(last, m.index)) + m[0];
    last = m.index + m[0].length;
  }
  return out + sub(text.slice(last));
}

export type GenParts = { imps: string[]; decls: string[]; defs: string[]; seal: string; raw: string };

export type GenOut = { src: string; raw: string; feats: string[]; parts: GenParts; files: Record<string, string> };

export function gen_program(seed: bigint, minParens: boolean, uid0 = 0, flat = false): GenOut {
  gen_reset(seed, minParens, uid0);

  const nadts = G.int(3);
  for (let i = 0; i < nadts; i++) {
    adt_new();
  }

  const env: V[] = [];
  const lines: string[] = [];
  const names: string[] = [];
  const eqs: string[] = [];
  const LETK: Array<[number, (e: V[]) => Line]> = [
    [10, let_scalar],
    [40, let_value],
    [12, let_call],
    [8, let_fork],
    [8, let_array],
    [6, let_float],
    [5, let_partial],
    [5, let_shared],
    [4, let_eql],
    [7, let_truth],
  ];
  const swarm = LETK.map(([w, f]) => [w * G.wpick<number>([[20, 0], [45, 1], [20, 2], [15, 4]]), f] as [number, (e: V[]) => Line]);
  const table = swarm.some(([w]) => w > 0) ? swarm : LETK;
  HEAVY = G.chance(0.08);
  if (HEAVY) {
    feature_add("big");
  }
  const nlets = size_pick(HEAVY ? 8 + G.int(9) : 2 + G.int(4), 320);
  for (let i = 0; i < nlets; i++) {
    const line = G.wpick<(e: V[]) => Line>(table)(env);
    lines.push(line.text);
    for (const b of line.binds) {
      names.push(b);
    }
    env.push(...line.vars);
    eqs.push(...(line.eqs ?? []));
  }

  if (G.chance(0.04)) {
    feature_add("deaddef");
    DEFS.push("def fzdead" + String(uid_next()) + "(x: U32) -> U32:\n  x + " + String(1 + G.int(99)));
  }
  if (G.chance(0.09)) {
    const t = theorem_gen();
    if (G.chance(0.5)) {
      feature_add("rwt");
      const n = "n" + String(uid_next());
      lines.push(n + " = {" + t.s + "{" + t.s + "{" + t.z + "{}}} : " + t.N + "}");
      const az = t.arity === 2
        ? t.add + "(" + n + ", " + t.s + "{" + t.z + "{}})"
        : t.add + "(" + n + ", " + t.z + "{})";
      const rhs = t.arity === 2 ? t.s + "{" + t.add + "(" + n + ", " + t.z + "{})}" : n;
      const e0 = t.arity === 2 ? t.th + "(" + n + ", " + t.z + "{})" : t.th + "(" + n + ")";
      if (G.chance(0.4)) {
        feature_add("eqkit");
        IMPORTS.add("Equal");
        eqs.push(G.wpick<string>([
          [3, "Equal::sym(" + t.N + ", " + az + ", " + rhs + ", " + e0 + ")"],
          [2, "Equal::trans(" + t.N + ", " + az + ", " + rhs + ", " + az + ", " + e0 + ", Equal::sym(" + t.N + ", " + az + ", " + rhs + ", " + e0 + "))"],
          [2, "Equal::cong(" + t.N + ", " + t.N + ", y => " + t.s + "{y}, " + az + ", " + rhs + ", " + e0 + ")"],
        ]));
      } else {
        eqs.push(e0);
      }
    }
  }
  if (G.chance(0.05)) {
    feature_add("deadlet");
    const t = syn_ty(1, true);
    const v = syn(t, env, 1);
    // zz : through e_ann_bind, not hand-assembled: `{a != b : T}` in a brace
    // statement parses as an inequality PROPOSITION (Empty::Not), which
    // needs `import Empty`, and e_ann_bind is what knows to bind the `!=`
    // to a temp first
    const zz = "zz" + String(uid_next());
    lines.push(t.k === "u32" || t.k === "f32" ? zz + " = " + e_at(v) : e_ann_bind(zz, v, ty_str(t)));
  }

  const res = "r" + String(uid_next());
  // fin : one flat left fold -- the old 64-name chunking through rc
  // intermediates dodged clang's bracket wall, which term_cexp now
  // handles in the emitter (a temp every 64 levels)
  const combined = names.map((n) => e_atom(n));
  const fin = res + " = " + e_at(num_combine(combined.concat([num_gen_u32(env, 1)])));
  // rlines : an explicit motive ends in `;` -- the motive term parse is
  // greedy and would swallow a parenthesized next line as application
  const rlines = eqs.slice(0, 2).map((e) =>
    G.chance(0.3) ? "%" + e + " : mw" + String(uid_next()) + " => U32;" : "% " + e);
  const seal = e_at(num_seal(res));
  const fun = G.chance(0.7);
  const imps = ["List", "Char", "String", "Pair", "Unit", "Bool", "Empty", "Equal"].filter((m) => IMPORTS.has(m)).map((m) => "import " + m);
  const body = (last: string): string => lines.concat([fin], rlines, [last]).join("\n  ");
  // mods : the book splits across SIBLING FILES -- all decls and a prefix
  // of the defs move out (defs are pushed in dependency order, so a
  // prefix is closed), m2 imports m1 and main imports both: relative
  // ids, transitive loads, cross-file ctors and calls. Imports never
  // bind bare content names -- only ctor tags travel -- so every
  // cross-file reference to a moved type or def is rewritten to its
  // qualified <mod>::<name> spelling (names are uid-unique, making
  // word-boundary replacement outside string/char literals sound).
  const files: Record<string, string> = {};
  // monads : a do-block derives M::bind from the monad TYPE's spelled
  // name, so the type and its ::-named defs cannot straddle a file
  // boundary; a seed that minted a monad skips the split whole (the
  // prefix cut knows nothing about group boundaries)
  const monadic = DEFS.some((d) => (mod_names(d)[0] ?? "").includes("::"));
  const nmod = DEFS.length >= 2 && !flat && !monadic ? size_pick(G.chance(0.25) ? 1 + G.int(2) : 0, 6) : 0;
  const mods: string[] = [];
  const qmap = new Map<string, string>();
  let mdecls = DECLS;
  let mdefs = DEFS;
  if (nmod > 0) {
    feature_add("module");
    const cut = Math.max(1, Math.floor(DEFS.length / (nmod + 1)));
    const head = imps.length > 0 ? imps.join("\n") + "\n\n" : "";
    for (let i = 0; i < nmod; i++) {
      const id = "./fm" + String(seed % 1000n) + "_" + String(uid_next());
      const take = (i === 0 ? DEFS.slice(0, cut) : DEFS.slice(cut * i, cut * (i + 1))).map((d) => mod_qualify(d, qmap));
      const decls = i === 0 ? DECLS : [];
      const sib = mods.length > 0 ? mods.map((m) => "import " + m).join("\n") + "\n\n" : "";
      files[id] = "# fuzz module\n\n" + head + sib + decls.join("\n\n") + (decls.length > 0 ? "\n\n" : "") + take.join("\n\n") + "\n";
      for (const nm of decls.concat(take).flatMap(mod_names)) {
        qmap.set(nm, id.slice(2) + "::" + nm);
      }
      mods.push(id);
    }
    mdecls = [];
    mdefs = DEFS.slice(cut * nmod).map((d) => mod_qualify(d, qmap));
  }
  // lex : layout is meaning-free, so it varies -- comment lines between
  // entries and extra blank runs. The min-parens metamorphic sibling
  // draws the same way, so a divergence is a real parser bug
  const lex = G.chance(0.2);
  if (lex) {
    feature_add("lex");
  }
  const glue = (): string => {
    if (!lex) {
      return "\n\n";
    }
    return G.wpick<string>([[40, "\n\n"], [20, "\n\n\n"], [25, "\n\n# fz " + String(G.int(1024)) + "\n"], [15, "\n\n#\n\n"]]);
  };
  const source = (last: string, kind: string): string => {
    const main = mod_qualify((fun ? "def main() -> U32:\n  " : "main : U32 =\n  ") + body(last), qmap);
    const parts = (imps.length > 0 || mods.length > 0
      ? [imps.concat(mods.map((m) => "import " + m)).join("\n")]
      : []).concat(mdecls).concat(mdefs).concat([main]);
    return "# fuzz " + kind + " seed=" + String(seed) + "\n\n" + parts.reduce((acc, p2, i) => acc + (i === 0 ? "" : glue()) + p2, "") + "\n";
  };
  return {
    src: source(seal, "sealed"),
    raw: source(res, "raw"),
    feats: Object.keys(FEAT),
    parts: { imps, decls: DECLS.slice(), defs: DEFS.slice(), seal: body(seal), raw: body(res) },
    files,
  };
}

// Io
// --

type IoProgram = { src: string; files: Record<string, string>; out: string; feats: string[]; marks: string[]; code: number };
type IoCtx = { key: string; files: Record<string, string>; helps: Set<string>; marks: string[]; alive: boolean };
type IoTerm = { s: string; out: string[] };

// IO_HELPS : The cancellation shapes below all keep the exact-stdout oracle by
// construction: the branch that loses is SILENT (a long sleep over a
// pure value), so a cancel that never happens costs no output either --
// what it costs is a leaked wait-set entry or a live process, which the
// leak probe and the orphan sweep read instead.
const IO_HELPS: Record<string, { src: string; imps: string[] }> = {
  // fz_slow : yields A only after a sleep no seed ever waits out: the loser of
  // every race, and the body of every timeout
  fz_slow: {
    src: "def fz_slow<A>(ms: U32, v: A) -> IO<A>:\n"
      + "  IO::bind<Unit, A>(IO::sleep(ms), u => IO::pure<A>(v))",
    imps: ["Unit"],
  },
  // fz_tmo : run x under an already-expired deadline: x is always cancelled, and
  // the Result never escapes (the generator never has to spell it)
  fz_tmo: {
    src: "def fz_tmo<A>(x: IO<A>) -> IO<Unit>:\n"
      + "  IO::bind<Result<(U32 & String), A>, Unit>(IO::timeout<A>(0, x), r => IO::pure<Unit>(U{}))",
    imps: ["Unit", "Result", "String", "Pair"],
  },
  // fz_exec : exec's own yield is already a Result, so its cancelled form nests
  // one -- the shape repro_exec_cancel_orphan was written in
  fz_exec: {
    src: "def fz_exec(cmd: String) -> IO<Unit>:\n"
      + "  IO::bind<Result<(U32 & String), Result<(U32 & String), Bytes>>, Unit>(\n"
      + "    IO::timeout<Result<(U32 & String), Bytes>>(0, IO::exec(cmd)), r => IO::pure<Unit>(U{}))",
    imps: ["Unit", "Result", "String", "Pair", "Bytes"],
  },
  // fz_wait : block on a child that never finishes: the waiter parks in JOIN and
  // owns a live subtree, so cancelling it must take both
  fz_wait: {
    src: "def fz_wait<A>(x: IO<A>) -> IO<A>:\n"
      + "  IO::bind<IO::Task<A>, A>(IO::fork<A>(x), t => IO::join<A>(t))",
    imps: [],
  },
  // fz_kill : the explicit Cancel op: consume the handle by cancelling instead of
  // joining (Task is linear -- exactly one of the two)
  fz_kill: {
    src: "def fz_kill<A>(x: IO<A>) -> IO<Unit>:\n"
      + "  IO::bind<IO::Task<A>, Unit>(IO::fork<A>(x), t =>\n"
      + "    IO::bind<Bool, Unit>(IO::cancel<A>(t), b => IO::pure<Unit>(U{})))",
    imps: ["Unit", "Bool"],
  },
  // fz_fd : parks on fd 0 -- the harness gives every binary an open, empty stdin
  // pipe, so this never answers. The one way to a cancelled FIB_FD.
  fz_fd: {
    src: "def fz_fd<A>(v: A) -> IO<A>:\n"
      + "  IO::bind<Result<(U32 & String), String>, A>(IO::read_line(), r => IO::pure<A>(v))",
    imps: ["Result", "String", "Pair"],
  },
  // fz_hold : holds a LIVE child across whatever cancels it -- uncancelled exec,
  // so the process dies only if the runtime reclaims it. Under a spawn
  // this is the exit teardown, the one property no in-process probe can
  // see (it runs before main emits).
  fz_hold: {
    src: "def fz_hold(cmd: String) -> IO<Unit>:\n"
      + "  IO::bind<Result<(U32 & String), Bytes>, Unit>(IO::exec(cmd), r => IO::pure<Unit>(U{}))",
    imps: ["Unit", "Result", "String", "Pair", "Bytes"],
  },
  // fz_prod : producer half of fz_pipe: the second send parks on the full buffer
  // until a recv drains it, so the receiver wakes a parked SENDER.
  // The channel helpers are MONOMORPHIC (U32 elements): a channel value
  // fans out freely only at a concrete type -- Chan<A> at abstract A
  // cannot contract, and every helper here uses c more than once.
  fz_prod: {
    src: "def fz_prod(c: Chan<U32>, v: U32, w: U32) -> IO<Unit>:\n"
      + "  IO::bind<Result<(U32 & String), Unit>, Unit>(Chan::send<U32>(c, v), r1 =>\n"
      + "    IO::bind<Result<(U32 & String), Unit>, Unit>(Chan::send<U32>(c, w), r2 =>\n"
      + "      IO::pure<Unit>(U{})))",
    imps: ["Unit", "Result", "String", "Pair", "IO/Chan"],
  },
  // fz_pipe : a channel used for what channels are for. Whichever side runs first,
  // the value arrives and nothing is printed -- so this is deterministic
  // while covering the rendezvous both ways (a send waking a parked
  // receiver, a recv waking a parked sender) and, after the close, the
  // end-of-stream Fail and the send-to-closed drop.
  fz_pipe: {
    src: "def fz_pipe(v: U32, w: U32) -> IO<Unit>:\n"
      + "  IO::bind<Chan<U32>, Unit>(Chan::new<U32>(1), c =>\n"
      + "    IO::bind<Unit, Unit>(IO::spawn(fz_prod(c, v, w)), u =>\n"
      + "      IO::bind<Result<(U32 & String), U32>, Unit>(Chan::recv<U32>(c), r1 =>\n"
      + "        IO::bind<Result<(U32 & String), U32>, Unit>(Chan::recv<U32>(c), r2 =>\n"
      + "          IO::bind<Bool, Unit>(Chan::close<U32>(c), b =>\n"
      + "            IO::bind<Result<(U32 & String), U32>, Unit>(Chan::recv<U32>(c), r3 =>\n"
      + "              IO::pure<Unit>(U{})))))))",
    imps: ["Unit", "Bool", "Result", "String", "Pair", "IO/Chan"],
  },
  // fz_recv : a receiver cancelled while parked on an empty channel (reg/349)
  fz_recv: {
    src: "def fz_recv() -> IO<Unit>:\n"
      + "  IO::bind<Chan<U32>, Unit>(Chan::new<U32>(1), c =>\n"
      + "    IO::bind<Unit, Unit>(fz_tmo<Result<(U32 & String), U32>>(Chan::recv<U32>(c)), u =>\n"
      + "      IO::bind<Bool, Unit>(Chan::close<U32>(c), b => IO::pure<Unit>(U{}))))",
    imps: ["Unit", "Bool", "Result", "String", "Pair", "IO/Chan"],
  },
  // fz_send : a sender cancelled while parked on a full one
  fz_send: {
    src: "def fz_send(v: U32, w: U32) -> IO<Unit>:\n"
      + "  IO::bind<Chan<U32>, Unit>(Chan::new<U32>(1), c =>\n"
      + "    IO::bind<Result<(U32 & String), Unit>, Unit>(Chan::send<U32>(c, v), r =>\n"
      + "      IO::bind<Unit, Unit>(fz_tmo<Result<(U32 & String), Unit>>(Chan::send<U32>(c, w)), u =>\n"
      + "        IO::bind<Bool, Unit>(Chan::close<U32>(c), b => IO::pure<Unit>(U{})))))",
    imps: ["Unit", "Bool", "Result", "String", "Pair", "IO/Chan"],
  },
};

export function io_help(ctx: IoCtx, name: string): string {
  if (ctx.helps.has(name)) {
    return name;
  }
  ctx.helps.add(name);
  for (const m of IO_HELPS[name].imps) {
    IMPORTS.add(m);
  }
  for (const other of Object.keys(IO_HELPS)) {
    if (other !== name && (IO_HELPS[name].src.includes(other + "<") || IO_HELPS[name].src.includes(other + "("))) {
      io_help(ctx, other);
    }
  }
  return name;
}

// io_never : An action of `goal` that is SILENT and never finishes: whatever wraps
// it always wins, so it is the loser of every cancellation shape. The
// recursive arms give the loser a SUBTREE and park it somewhere other
// than a timer -- io_fib_cancel walks children first and then switches
// on the fiber's own state, and a leaf sleeper exercises neither.
// a deadline no run reaches (the C leg caps at RUN_TIMEOUT), spread so
// the timer heap is a heap and not two clustered values
export function io_never(): string {
  return String(60_000 + G.int(600_000));
}

export function io_quiet(goal: T, env: V[], fuel: number, ctx: IoCtx): string {
  const cap = env.filter((v) => v.q === "many").map((v) => ({ ...v }));
  const g = ty_str(goal);
  const leaf = (): string =>
    io_help(ctx, "fz_slow") + "<" + g + ">(" + io_never() + ", "
      + e_at(syn(goal, cap, Math.max(0, fuel - 1))) + ")";
  if (fuel <= 0) {
    return leaf();
  }
  return G.wpick<() => string>([
    [30, leaf],
    // fz_wait : parked in JOIN on a child that never answers
    [16, () => io_help(ctx, "fz_wait") + "<" + g + ">(" + io_quiet(goal, env, fuel - 1, ctx) + ")"],
    // race : parked in RACING with two live children (cancel's default arm,
    // reached only through the subtree walk)
    [14, () => "IO::race<" + g + ">(" + io_quiet(goal, env, fuel - 1, ctx) + ", "
      + io_quiet(goal, env, fuel - 1, ctx) + ")"],
    // spawn : a spawned sibling still parked when the parent is cancelled
    [12, () => {
      const u = "qu" + String(uid_next());
      return "IO::bind<Unit," + g + ">(IO::spawn(" + io_help(ctx, "fz_slow") + "<Unit>("
        + io_never() + ", U{})), " + u + " => " + io_quiet(goal, env, fuel - 1, ctx) + ")";
    }],
    // fz_fd : parked on an fd instead of a timer
    [10, () => io_help(ctx, "fz_fd") + "<" + g + ">(" + e_at(syn(goal, cap, Math.max(0, fuel - 1))) + ")"],
    // exec : parked on a worker while a real process runs: the continuation is
    // unreachable by construction, it only has to typecheck
    [9, () => {
      const mark = "fzhold_" + ctx.key + "_" + String(uid_next());
      ctx.marks.push(mark);
      const u = "qh" + String(uid_next());
      return "IO::bind<Unit," + g + ">(" + io_help(ctx, "fz_hold") + "(\"sleep 600; echo "
        + mark + "\"), " + u + " => " + leaf() + ")";
    }],
  ])();
}

export function io_timeout(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("timeout", goal);
  const inner = syn_ty(1, true);
  const x = "io" + String(uid_next());
  const rest = io_syn(goal, env.concat([v_many(x, need_unit())]), fuel - 1, ctx);
  return {
    s: "IO::bind<Unit," + ty_str(goal) + ">(" + io_help(ctx, "fz_tmo") + "<" + ty_str(inner) + ">("
      + io_quiet(inner, env, fuel, ctx) + "), " + x + " => " + rest.s + ")",
    out: rest.out,
  };
}

export function io_race(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("raceio", goal);
  const won = syn_ty(1, true);
  const fast = syn(won, env.filter((v) => v.q === "many"), Math.max(0, fuel - 1));
  const x = "io" + String(uid_next());
  const rest = io_syn(goal, env.concat([v_many(x, won)]), fuel - 1, ctx);
  return {
    s: "IO::bind<" + ty_str(won) + "," + ty_str(goal) + ">(IO::race<" + ty_str(won) + ">(IO::pure<"
      + ty_str(won) + ">(" + e_at(fast) + "), " + io_quiet(won, env, fuel, ctx) + "), " + x + " => " + rest.s + ")",
    out: rest.out,
  };
}

// io_spawn : a fiber still parked when main emits: the root's cancel walk must
// reclaim it (nothing may be left running or waiting after exit)
export function io_spawn(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("spawnio", goal);
  ctx.alive = true;
  const x = "io" + String(uid_next());
  const rest = io_syn(goal, env.concat([v_many(x, need_unit())]), fuel - 1, ctx);
  return {
    s: "IO::bind<Unit," + ty_str(goal) + ">(IO::spawn(" + io_quiet(need_unit(), env, fuel, ctx)
      + "), " + x + " => " + rest.s + ")",
    out: rest.out,
  };
}

// io_exec : a cancelled exec: the command outlives its deadline by far and prints
// a marker no expected output carries, so an unkilled child shows up
// either in this run's stdout or in the orphan sweep after it
export function io_exec(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("execio", goal);
  const mark = "fzorph_" + ctx.key + "_" + String(uid_next());
  ctx.marks.push(mark);
  const x = "io" + String(uid_next());
  const rest = io_syn(goal, env.concat([v_many(x, need_unit())]), fuel - 1, ctx);
  return {
    s: "IO::bind<Unit," + ty_str(goal) + ">(" + io_help(ctx, "fz_exec") + "(\"sleep 600; echo "
      + mark + "\"), " + x + " => " + rest.s + ")",
    out: rest.out,
  };
}

export function io_pure(goal: T, env: V[], fuel: number): IoTerm {
  const value = syn(goal, env, Math.max(0, fuel));
  return { s: "IO::pure<" + ty_str(goal) + ">(" + e_at(value) + ")", out: [] };
}

export function io_print(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("print", goal);
  IMPORTS.add("String");
  const text = "fuzz_" + ctx.key + "_" + String(uid_next());
  const x = "io" + String(uid_next());
  const unit = need_unit();
  const rest = io_syn(goal, env.concat([v_many(x, unit)]), fuel - 1, ctx);
  return {
    s: "IO::bind<Unit," + ty_str(goal) + ">(IO::print(\"" + text + "\"), " + x + " => " + rest.s + ")",
    out: [text].concat(rest.out),
  };
}

// io_ffi is DEAD: the ratified Op ruling admits only the hand-written
// IO::Op rows -- a C-bodied def compiles only when its camelized name
// matches an install Op ctor, so per-seed minted effects (and the C
// leak probe that rode the same ABI) cannot compile anymore. The
// marshalling boundary is covered by the base ops the other arms drive.

export function io_fork(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("forkio", goal);
  const yielded = syn_ty(1, true);
  const child_env = env.filter((v) => v.q === "many").map((v) => ({ ...v }));
  const child_io = io_syn(yielded, child_env, Math.max(0, fuel - 2), ctx);
  const task = "it" + String(uid_next());
  const value = "iv" + String(uid_next());
  const rest = io_syn(goal, env.concat([v_many(value, yielded)]), fuel - 1, ctx);
  const inner = "IO::bind<" + ty_str(yielded) + "," + ty_str(goal) + ">(IO::join<"
    + ty_str(yielded) + ">(" + task + "), " + value + " => " + rest.s + ")";
  return {
    s: "IO::bind<IO::Task<" + ty_str(yielded) + ">," + ty_str(goal) + ">(IO::fork<"
      + ty_str(yielded) + ">(" + child_io.s + "), " + task + " => " + inner + ")",
    out: child_io.out.concat(rest.out),
  };
}

// io_kill : the explicit Cancel op on a live subtree: Task is linear, so choosing
// cancel over join is the other lawful way to consume the handle
export function io_kill(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("killio", goal);
  const held = syn_ty(1, true);
  const x = "io" + String(uid_next());
  const rest = io_syn(goal, env.concat([v_many(x, need_unit())]), fuel - 1, ctx);
  return {
    s: "IO::bind<Unit," + ty_str(goal) + ">(" + io_help(ctx, "fz_kill") + "<" + ty_str(held) + ">("
      + io_quiet(held, env, fuel, ctx) + "), " + x + " => " + rest.s + ")",
    out: rest.out,
  };
}

// IO_QUIET_EFFS : a fiber cancelled while parked on a channel -- the SEND and RECV arms
// of io_fib_cancel, which no other shape reaches
const IO_QUIET_EFFS: { call: string; yield: string; imps: string[] }[] = [
  { call: "IO::now()", yield: "U32", imps: [] },
  { call: "IO::now_ms()", yield: "U32", imps: [] },
  { call: "IO::rand_word()", yield: "U32", imps: [] },
  { call: "IO::args()", yield: "List<String>", imps: ["List", "String"] },
  { call: "IO::get_env(\"FZ_UNSET\")", yield: "Result<(U32 & String), String>", imps: ["Result", "String", "Pair"] },
];

// io_eff : effects bound and DROPPED: their values are nondeterministic (a clock,
// a random word, the environment), so only the dispatch is under test --
// which is the part that had no coverage at all
export function io_eff(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("quieteff", goal);
  const e = IO_QUIET_EFFS[G.int(IO_QUIET_EFFS.length)];
  for (const m of e.imps) {
    IMPORTS.add(m);
  }
  const x = "io" + String(uid_next());
  const rest = io_syn(goal, env, fuel - 1, ctx);
  return {
    s: "IO::bind<" + e.yield + "," + ty_str(goal) + ">(" + e.call + ", " + x + " => " + rest.s + ")",
    out: rest.out,
  };
}

export function io_pipe(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("pipeio", goal);
  const cap2 = env.filter((v) => v.q === "many").map((v) => ({ ...v }));
  const x = "io" + String(uid_next());
  const rest = io_syn(goal, env.concat([v_many(x, need_unit())]), fuel - 1, ctx);
  return {
    s: "IO::bind<Unit," + ty_str(goal) + ">(" + io_help(ctx, "fz_pipe") + "("
      + e_at(num_gen_u32(cap2, 1)) + ", " + e_at(num_gen_u32(cap2, 1)) + "), " + x + " => " + rest.s + ")",
    out: rest.out,
  };
}

export function io_chan(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("chanio", goal);
  const cap = env.filter((v) => v.q === "many").map((v) => ({ ...v }));
  const send = G.chance(0.5);
  const call = send
    ? io_help(ctx, "fz_send") + "(" + e_at(num_gen_u32(cap, 1)) + ", " + e_at(num_gen_u32(cap, 1)) + ")"
    : io_help(ctx, "fz_recv") + "()";
  const x = "io" + String(uid_next());
  const rest = io_syn(goal, env.concat([v_many(x, need_unit())]), fuel - 1, ctx);
  return {
    s: "IO::bind<Unit," + ty_str(goal) + ">(" + call + ", " + x + " => " + rest.s + ")",
    out: rest.out,
  };
}

// io_do : a minted def whose body is a DO-BLOCK -- multi-bind Bnd
// elaboration, bare statement lines (wildcard binds), and nesting when a
// sub-action picks io_do again; word env vars cross as params
export function io_do(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("doio", goal);
  const name = "dd" + String(uid_next());
  const g = ty_str(goal);
  const caps = env.filter((v) => v.q === "many" && v.ty.k === "u32").slice(0, 2);
  let benv = caps.map((v) => v_many(v.name, U32C));
  const lines: string[] = [];
  const outs: string[][] = [];
  const n = size_pick(1 + G.int(2), 48);
  for (let i = 0; i < n; i++) {
    const yt = syn_ty(1, true);
    const act = io_syn(yt, benv, Math.max(0, fuel - 2), ctx);
    outs.push(act.out);
    if (G.chance(0.3)) {
      feature_add("dobare");
      lines.push("    {" + act.s + " : IO<" + ty_str(yt) + ">}");
    } else {
      const x = "dv" + String(uid_next());
      lines.push("    " + x + " <- {" + act.s + " : IO<" + ty_str(yt) + ">}");
      if (yt.k === "u32") {
        benv = benv.concat([v_many(x, U32C)]);
      }
    }
  }
  const fin = io_syn(goal, benv, Math.max(0, fuel - 2), ctx);
  outs.push(fin.out);
  DEFS.push("def " + name + "(" + caps.map((v) => v.name + ": U32").join(", ") + ") -> IO<" + g + ">:\n  do IO<" + g + ">:\n"
    + lines.join("\n") + "\n    {" + fin.s + " : IO<" + g + ">}");
  return { s: name + "(" + caps.map((v) => v.name).join(", ") + ")", out: outs.flat() };
}

// io_val : an IO VALUE, built and not yet executed -- its out is what
// it will print IF someone runs it; a dropped value contributes nothing
export function io_val(t: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  if (fuel > 0 && G.chance(0.4)) {
    const name = "av" + String(uid_next());
    const act = io_syn(t, [], Math.max(0, fuel - 2), ctx);
    DEFS.push("def " + name + "() -> IO<" + ty_str(t) + ">:\n  " + act.s);
    return { s: name + "()", out: act.out };
  }
  return { s: "IO::pure<" + ty_str(t) + ">(" + e_at(syn(t, env.filter((v) => v.q === "many"), Math.min(fuel, 1))) + ")", out: [] };
}

// io_first : IO as a FIRST-CLASS type. Values (io_val) flow through
// minted defs whose CONTRACT fixes what runs, in which order -- that is
// what keeps the exact-stdout oracle: a run param splices its pending
// out at its position, a drop param discards it (an unexecuted action
// prints nothing), nesting rides IO<IO<T>>, wrappers carry actions in
// ctor fields, continuations pass (U32 -> IO<T>) lambdas that may
// capture the live env
export function io_first(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("ioval", goal);
  const g = ty_str(goal);
  const id = String(uid_next());
  const t = syn_plain_ty(1);
  const ts = ty_str(t);
  const shape = G.int(4);
  if (shape === 0) {
    feature_add("iodrop");
    const t2 = syn_plain_ty(1);
    const name = "cb" + id;
    const inner = io_syn(goal, [v_many("k", U32C)], Math.max(0, fuel - 2), ctx);
    DEFS.push("def " + name + "(a: IO<" + ts + ">, b: IO<" + ty_str(t2) + ">, k: U32) -> IO<" + g + ">:\n  "
      + "IO::bind<" + ts + "," + g + ">(a, x" + id + " => " + inner.s + ")");
    const va = io_val(t, env, fuel - 1, ctx);
    const vb = io_val(t2, env, fuel - 1, ctx);
    return { s: name + "(" + va.s + ", " + vb.s + ", " + e_at(num_gen_u32(env, 1)) + ")", out: va.out.concat(inner.out) };
  }
  if (shape === 1) {
    feature_add("ionest");
    const v = io_val(t, env, fuel - 1, ctx);
    const x = "nx" + id;
    const y = "ny" + id;
    const benv = t.k === "u32" ? env.concat([v_many(y, U32C)]) : env;
    const rest = io_syn(goal, benv, Math.max(0, fuel - 2), ctx);
    return {
      s: "IO::bind<IO<" + ts + ">," + g + ">(IO::pure<IO<" + ts + ">>(" + v.s + "), " + x + " => IO::bind<" + ts + "," + g + ">(" + x + ", " + y + " => " + rest.s + "))",
      out: v.out.concat(rest.out),
    };
  }
  if (shape === 2) {
    feature_add("iowrap");
    const W = "Wf" + id;
    const name = "rw" + id;
    const inner = io_syn(goal, [v_many("k", U32C)], Math.max(0, fuel - 2), ctx);
    const v = io_val(t, env, fuel - 1, ctx);
    if (G.chance(0.35)) {
      // pair : the action rides a TUPLE inside the ctor field -- IO
      // wherever a type is accepted
      IMPORTS.add("Pair");
      DECLS.push("type " + W + ":\n  " + W + "a{a: (IO<" + ts + "> & U32)}");
      DEFS.push("def " + name + "(w: " + W + ") -> IO<" + g + ">:\n  match w:\n    case " + W + "a{p}:\n      match p:\n        case (io" + id + ", k):\n          IO::bind<" + ts + "," + g + ">(io" + id + ", x" + id + " => " + inner.s + ")");
      return { s: name + "(" + W + "a{(" + v.s + ", " + e_at(num_gen_u32(env, 1)) + ")})", out: v.out.concat(inner.out) };
    }
    DECLS.push("type " + W + ":\n  " + W + "a{a: IO<" + ts + ">, k: U32}");
    DEFS.push("def " + name + "(w: " + W + ") -> IO<" + g + ">:\n  match w:\n    case " + W + "a{a, k}:\n      IO::bind<" + ts + "," + g + ">(a, x" + id + " => " + inner.s + ")");
    return { s: name + "(" + W + "a{" + v.s + ", " + e_at(num_gen_u32(env, 1)) + "})", out: v.out.concat(inner.out) };
  }
  feature_add("iokont");
  const name = "kn" + id;
  const inner = io_syn(goal, [v_many("k", U32C)], Math.max(0, fuel - 2), ctx);
  DEFS.push("def " + name + "(f: (U32 -> IO<" + ts + ">), s" + id + ": U32, k: U32) -> IO<" + g + ">:\n  "
    + "IO::bind<" + ts + "," + g + ">(f(s" + id + "), x" + id + " => " + inner.s + ")");
  const b = "kb" + id;
  const larm = io_syn(t, env.concat([v_many(b, U32C)]), Math.max(0, fuel - 2), ctx);
  return {
    s: name + "(" + b + " => " + larm.s + ", " + e_at(num_gen_u32(env, 1)) + ", " + e_at(num_gen_u32(env, 1)) + ")",
    out: larm.out.concat(inner.out),
  };
}

// io_base : the shipped IO surface, one arm per base effect family --
// all/par put IO INSIDE containers (List<IO<A>>, paired actions), the
// Result rows ride timeout/unwrap, get_env and the file roundtrip,
// read_line drains the harness's empty stdin, argv/clock/rand yield
// NONDETERMINISTIC words -- safe because yields flow only into env
// words through minted readers and never into stdout: prints stay
// literal, so the exact-stdout oracle holds
export function io_base(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  feature_goal("baseio", goal);
  const g = ty_str(goal);
  const id = String(uid_next());
  const x = "bx" + id;
  const rest = io_syn(goal, env.concat([v_many(x, U32C)]), Math.max(0, fuel - 1), ctx);
  const word = (call: string, yt: string): IoTerm => (
    { s: "IO::bind<" + yt + "," + g + ">(" + call + ", " + x + " => " + rest.s + ")", out: rest.out });
  const read = (call: string, yt: string, rd: string): IoTerm => (
    { s: "IO::bind<" + yt + "," + g + ">(" + call + ", r" + id + " => IO::bind<U32," + g + ">(IO::pure<U32>(" + rd + "(r" + id + ")), " + x + " => " + rest.s + "))", out: rest.out });
  const RS = "Result<(U32 & String), ";
  const shape = G.wpick<string>([[14, "all"], [12, "par"], [12, "tmo"], [10, "env"], [12, "file"], [6, "argv"], [10, "clock"], [8, "rand"], [8, "slp"], [8, "perr"]]);
  feature_add("base-" + shape);
  IMPORTS.add("String");
  IMPORTS.add("Pair");
  IMPORTS.add("Unit");
  if (shape === "all") {
    IMPORTS.add("List");
    const rd = "bl" + id;
    DEFS.push("def " + rd + "(xs: List<U32>) -> U32:\n  match xs:\n    case Cons{h, t}:\n      h\n    case Nil{}:\n      0");
    const els = Array.from({ length: 2 + G.int(2) }, () => "IO::pure<U32>(" + e_at(num_gen_u32(env, 1)) + ")");
    return read("IO::all<U32>([" + els.join(", ") + "])", "List<U32>", rd);
  }
  if (shape === "par") {
    const rd = "bp" + id;
    DEFS.push("def " + rd + "(p: (U32 & U32)) -> U32:\n  match p:\n    case (a, b):\n      (a + b)");
    return read("IO::par<U32, U32>(IO::pure<U32>(" + e_at(num_gen_u32(env, 1)) + "), IO::pure<U32>(" + e_at(num_gen_u32(env, 1)) + "))", "(U32 & U32)", rd);
  }
  if (shape === "tmo") {
    IMPORTS.add("Result");
    const inner = io_val(U32C, env, Math.max(0, fuel - 1), ctx);
    const t = {
      s: "IO::bind<" + RS + "U32>," + g + ">(IO::timeout<U32>(60000, " + inner.s + "), r" + id + " => IO::bind<U32," + g + ">(IO::unwrap<U32>(r" + id + "), " + x + " => " + rest.s + "))",
      out: inner.out.concat(rest.out),
    };
    return t;
  }
  if (shape === "env") {
    // env : read_line stays OUT of this roster -- the harness keeps
    // stdin open and empty by design (fz_fd parks on it), so it parks
    IMPORTS.add("Result");
    const rd = "br" + id;
    DEFS.push("def " + rd + "(e: " + RS + "String>) -> U32:\n  match e:\n    case Done{s}:\n      String::length(s)\n    case Fail{er}:\n      " + String(1 + G.int(64)));
    return read("IO::get_env(\"FZQ" + id + "\")", RS + "String>", rd);
  }
  if (shape === "file") {
    IMPORTS.add("Result");
    const rd = "bf" + id;
    DEFS.push("def " + rd + "(e: " + RS + "String>) -> U32:\n  match e:\n    case Done{s}:\n      String::length(s)\n    case Fail{er}:\n      " + String(1 + G.int(64)));
    const txt = "fz".repeat(1 + G.int(5));
    const fn = "fzf" + id + ".txt";
    return {
      s: "IO::bind<" + RS + "Unit>," + g + ">(IO::write_text(\"" + fn + "\", \"" + txt + "\"), w" + id + " => IO::bind<" + RS + "String>," + g + ">(IO::read_text(\"" + fn + "\"), r" + id + " => IO::bind<U32," + g + ">(IO::pure<U32>(" + rd + "(r" + id + ")), " + x + " => " + rest.s + ")))",
      out: rest.out,
    };
  }
  if (shape === "argv") {
    IMPORTS.add("List");
    const rd = "ba" + id;
    DEFS.push("def " + rd + "(xs: List<String>) -> U32:\n  match xs:\n    case Cons{h, t}:\n      (1 + " + rd + "(t))\n    case Nil{}:\n      0");
    return read("IO::args()", "List<String>", rd);
  }
  if (shape === "clock") {
    return word(G.chance(0.5) ? "IO::now()" : "IO::now_ms()", "U32");
  }
  if (shape === "rand") {
    return word("IO::rand_word()", "U32");
  }
  const u = "bu" + id;
  const call = shape === "slp" ? "IO::sleep(0)" : "IO::print_err(\"fz" + id + "\")";
  return {
    s: "IO::bind<Unit," + g + ">(" + call + ", " + u + " => IO::bind<U32," + g + ">(IO::pure<U32>(" + String(G.int(1024)) + "), " + x + " => " + rest.s + "))",
    out: rest.out,
  };
}

export function io_syn(goal: T, env: V[], fuel: number, ctx: IoCtx): IoTerm {
  if (fuel <= 0) {
    return io_pure(goal, env, 1);
  }
  return G.wpick<() => IoTerm>([
    [18, () => io_pure(goal, env, Math.min(fuel, 2))],
    [26, () => io_print(goal, env, fuel, ctx)],
    [22, () => io_fork(goal, env, fuel, ctx)],
    [13, () => io_timeout(goal, env, fuel, ctx)],
    [13, () => io_race(goal, env, fuel, ctx)],
    [9, () => io_spawn(goal, env, fuel, ctx)],
    [7, () => io_exec(goal, env, fuel, ctx)],
    [11, () => io_kill(goal, env, fuel, ctx)],
    [11, () => io_chan(goal, env, fuel, ctx)],
    [11, () => io_pipe(goal, env, fuel, ctx)],
    [10, () => io_eff(goal, env, fuel, ctx)],
    [14, () => io_do(goal, env, fuel, ctx)],
    [15, () => io_first(goal, env, fuel, ctx)],
    [15, () => io_base(goal, env, fuel, ctx)],
  ])();
}

// Gen
// ---

export function gen_io_program(seed: bigint): IoProgram {
  gen_reset(seed, false);
  feature_add("io");
  IMPORTS.add("IO");
  const nadts = G.int(3);
  for (let i = 0; i < nadts; i++) {
    adt_new();
  }
  const yielded = syn_ty(2, true);
  const key = (seed & M64).toString(16);
  const ctx: IoCtx = { key, files: {}, helps: new Set(), marks: [], alive: false };
  const action = io_syn(yielded, [], 3, ctx);
  const value = "io" + String(uid_next());
  // The in-process LEAK PROBE (timer-heap depth + waitpid(WNOHANG) as a
  // last effect) died with the Op ruling: it was a minted C effect, and
  // only hand-written Op rows compile. A leaked timer entry is invisible
  // now; a leaked PROCESS is still caught by the orphan sweep outside
  // the binary.
  const tail = "";
  // dies : Die is the one Op that reclaims NOTHING on its way out -- no cancel
  // walk at all -- so whatever the seed left running rides entirely on
  // io_run's exit teardown. Paired with a live spawn it is the only
  // generated witness for that path; the exit code is the assertion.
  const dies = G.chance(0.15);
  const code = 1 + G.int(200);
  if (dies) {
    feature_add("dieio");
    IMPORTS.add("String");
  }
  const bye = dies
    ? "    dz" + String(uid_next()) + " <- IO::die<U32>(" + String(code) + ", \"fzdie\")\n"
    : "";
  const main = "def main() -> IO<U32>:\n  do IO<U32>:\n    " + value
    + " <- {" + action.s + " : IO<" + ty_str(yielded) + ">}\n" + tail + bye + "    return 0";
  const helps = Object.keys(IO_HELPS).filter((h) => ctx.helps.has(h)).map((h) => IO_HELPS[h].src);
  const order = ["List", "Char", "String", "Pair", "Unit", "Bool", "Empty", "Equal", "Result", "Bytes", "IO", "IO/Chan"];
  const imps = order.filter((m) => IMPORTS.has(m)).map((m) => "import " + m);
  const parts = [imps.join("\n")].concat(DECLS).concat(helps).concat(DEFS).concat([main]);
  const src = "# fuzz io seed=" + String(seed) + "\n\n" + parts.filter((p) => p !== "").join("\n\n") + "\n";
  return { src, files: ctx.files, out: action.out.join("\n"), feats: Object.keys(FEAT), marks: ctx.marks, code: dies ? code : 0 };
}

// Worker
// ------
// `fuzz.ts --worker`: JSON-line protocol on stdin/stdout. One request loads
// (parse_book with a base/-serving reader), checks (halt ON), normalizes main
// on the interpreter, and emits the C. Verdicts: reject (BendError: the
// checker refused), skip (resource limit: stack overflow), crash (internal
// error in load/check/normalize/compile on a generated program — a finding),
// ok.

type WorkerMode = "full" | "interp" | "compile";
type WorkerReq = { id: number; src: string; base: string; mode: WorkerMode; files?: Record<string, string> };
type WorkerRes = { id: number; verdict: "ok" | "reject" | "skip" | "crash"; out?: string; csrc?: string; err?: string; stage?: string; ms?: number };

export async function worker_main(): Promise<void> {
  const bend = await import(pathToFileURL(BEND_TS).href);
  // BendErr : the dynamic import types as any, so name the class once to
  // get instanceof narrowing back
  const BendErr = bend.BendError as new () => Error & { err: never };
  const err_str = (e: unknown): string => {
    if (typeof e === "string") {
      return e;
    }
    if (e instanceof BendErr) {
      try {
        return bend.err_show(e.err);
      } catch {
        return "unshowable checker error: " + e.message;
      }
    }
    if (e instanceof Error) {
      return e.constructor.name + ": " + e.message;
    }
    return String(e);
  };
  const base_read = (id: string, kind: string): string | null => {
    const p = path.join(ROOT, "bend-base", id + (kind === "Bend" ? ".bend" : ""));
    if (!fs.existsSync(p)) {
      return null;
    }
    return fs.readFileSync(p, "utf8");
  };
  const rl = readline.createInterface({ input: process.stdin, terminal: false });
  // handle : requests are strictly one-in-flight per worker (the pool
  // dispatches the next only after the reply), so an async handler
  // cannot interleave
  const handle = async (l: string): Promise<void> => {
    const req = JSON.parse(l) as WorkerReq;
    const reply = (r: WorkerRes): void => {
      process.stdout.write(JSON.stringify(r) + "\n");
    };
    const reader = (id: string, kind: string): string | null => {
      if (id === req.base && kind === "Bend") {
        return req.src;
      }
      return req.files?.[id] ?? base_read(id, kind);
    };
    const read = async (id: string): Promise<string | null> => reader(id, "Bend");
    // book_check elaborates IN PLACE, and elaboration carries meaning
    // (truth bridges), so the CHECKED book is both what normalizes and
    // what book_compile consumes -- exactly the CLI's path
    let book;
    try {
      book = await bend.parse_book(req.base, read);
      bend.book_check(book, true);
    } catch (e) {
      if (e instanceof RangeError) {
        reply({ id: req.id, verdict: "skip", stage: "check-stack-overflow", err: err_str(e) });
      } else if (e instanceof bend.BendError) {
        reply({ id: req.id, verdict: "reject", err: err_str(e) });
      } else {
        reply({ id: req.id, verdict: "crash", stage: "check", err: err_str(e) });
      }
      return;
    }
    if (req.mode === "compile") {
      try {
        const csrc = bend.book_compile(book, req.base.slice(2), req.src, reader);
        reply({ id: req.id, verdict: "ok", csrc });
      } catch (e) {
        reply({ id: req.id, verdict: "crash", stage: "compile", err: err_str(e) });
      }
      return;
    }
    let out: string;
    const t0 = performance.now();
    try {
      const m = book.entries["main"];
      if (m === undefined || m.$ !== "Func" || m.v === undefined) {
        throw new Error("no main Func after check");
      }
      out = bend.term_show(bend.term_snf(book, m.v)).trim();
    } catch (e) {
      if (e instanceof RangeError) {
        reply({ id: req.id, verdict: "skip", stage: "interp-stack-overflow", err: err_str(e) });
      } else {
        reply({ id: req.id, verdict: "crash", stage: "interp", err: err_str(e) });
      }
      return;
    }
    const ms = Math.round(performance.now() - t0);
    if (req.mode === "interp") {
      reply({ id: req.id, verdict: "ok", out, ms });
      return;
    }
    let csrc: string;
    try {
      csrc = bend.book_compile(book, req.base.slice(2), req.src, reader);
    } catch (e) {
      reply({ id: req.id, verdict: "crash", stage: "comp", err: err_str(e) });
      return;
    }
    reply({ id: req.id, verdict: "ok", out, csrc, ms });
  };
  rl.on("line", (l: string) => {
    void handle(l);
  });
}

// Worker pool
// -----------

type Pending = { resolve: (r: WorkerRes) => void; timer: NodeJS.Timeout };
type Slot = { proc: child.ChildProcess; busy: boolean; reqId: number | null; expired: boolean; errbuf: string };

class Pool {
  workers: Slot[] = [];
  pending: Map<number, Pending> = new Map();
  queue: Array<{ req: WorkerReq; resolve: (r: WorkerRes) => void }> = [];
  nextId = 1;

  constructor(n: number) {
    for (let i = 0; i < n; i++) {
      this.workers.push(this.spawn());
    }
  }

  spawn(): Slot {
    const proc = child.spawn(process.execPath, [import.meta.filename, "--worker"], {
      stdio: ["pipe", "pipe", "pipe"],
      cwd: ROOT,
    });
    const slot: Slot = { proc, busy: false, reqId: null, expired: false, errbuf: "" };
    proc.stdin?.on("error", () => {});
    proc.stderr?.on("data", (d: Buffer) => {
      slot.errbuf = (slot.errbuf + String(d)).slice(-8192);
    });
    proc.on("exit", (code, sig) => {
      const i = this.workers.indexOf(slot);
      if (i < 0) {
        return;
      }
      this.workers[i] = this.spawn();
      const rid = slot.reqId;
      const p = rid !== null ? this.pending.get(rid) : undefined;
      if (rid !== null && p !== undefined) {
        clearTimeout(p.timer);
        this.pending.delete(rid);
        const tail = slot.errbuf.trim().slice(-1500);
        p.resolve(slot.expired
          ? { id: rid, verdict: "skip", stage: "worker-timeout", err: "worker timeout after " + String(WORKER_TIMEOUT) + "ms" }
          : sig === "SIGKILL"
            ? { id: rid, verdict: "skip", stage: "worker-oom-killed", err: "worker SIGKILLed by the system\n" + tail }
            : { id: rid, verdict: "crash", stage: "worker-death", err: "worker died code=" + String(code) + " sig=" + String(sig) + "\nstderr tail:\n" + tail });
      }
      this.drain();
    });
    const rl = readline.createInterface({ input: proc.stdout as NodeJS.ReadableStream, terminal: false });
    rl.on("line", (l: string) => {
      let res: WorkerRes;
      try {
        res = JSON.parse(l) as WorkerRes;
      } catch {
        return;
      }
      const p = this.pending.get(res.id);
      if (p !== undefined) {
        clearTimeout(p.timer);
        this.pending.delete(res.id);
        slot.busy = false;
        slot.reqId = null;
        p.resolve(res);
        this.drain();
      }
    });
    return slot;
  }

  drain(): void {
    while (this.queue.length > 0) {
      const w = this.workers.find((x) => !x.busy);
      if (w === undefined) {
        return;
      }
      const job = this.queue.shift();
      if (job === undefined) {
        return;
      }
      this.dispatch(w, job.req, job.resolve);
    }
  }

  dispatch(w: Slot, req: WorkerReq, resolve: (r: WorkerRes) => void): void {
    w.busy = true;
    w.reqId = req.id;
    w.errbuf = "";
    const timer = setTimeout(() => {
      w.expired = true;
      w.proc.kill("SIGKILL");
    }, WORKER_TIMEOUT);
    this.pending.set(req.id, { resolve, timer });
    w.proc.stdin?.write(JSON.stringify(req) + "\n");
  }

  run(src: string, base: string, mode: WorkerMode, files?: Record<string, string>): Promise<WorkerRes> {
    const req: WorkerReq = { id: this.nextId++, src, base, mode, files };
    return new Promise((resolve) => {
      const w = this.workers.find((x) => !x.busy);
      if (w !== undefined) {
        this.dispatch(w, req, resolve);
      } else {
        this.queue.push({ req, resolve });
      }
    });
  }

  close(): void {
    const ws = this.workers;
    this.workers = [];
    for (const w of ws) {
      w.proc.kill();
    }
  }
}

// Leg
// ---
// Flags mirror comp.file_recipes: -fno-slp-vectorize is load-bearing (SLP
// merges stores across the heap span) and -lm covers the f32 builtins.

type Run = { ok: boolean; out: string; err: string; timeout: boolean; code: number };

export function leg_exec(cmd: string, args: string[], cwd: string, timeout: number): Promise<Run> {
  return new Promise((resolve) => {
    child.execFile(cmd, args, { cwd, timeout, encoding: "utf8", maxBuffer: 64 * 1024 * 1024 }, (e, out, err) => {
      const killed = e !== null && (e as { killed?: boolean }).killed === true;
      const ec = e === null ? 0 : typeof (e as { code?: unknown }).code === "number" ? (e as { code: number }).code : -1;
      resolve({ ok: e === null, out, err, timeout: killed, code: ec });
    });
  });
}

const OPT = "-O" + cli_opt("--opt", "3");
const CC_FLAGS = [OPT, "-w", "-fno-slp-vectorize", "-DPAR_BACKEND=0", "-DNUM_THREADS=" + String(THREADS)];

// file_link : the compiler's own `//! link` line (file_flags in bend.ts):
// extra link flags an effect body asked for ride into every leg
export function file_link(csrc: string): string[] {
  const m = csrc.match(/^\/\/! link (.+)$/m);
  return m === null ? [] : m[1].split(" ").filter((s) => s !== "");
}

export async function leg_c(dir: string, base: string, csrc: string, want = 0): Promise<{ kind: "ok" | "skip" | "fail"; out: string; why?: string }> {
  const cfile = path.join(dir, base + ".c");
  const bin = path.join(dir, base + "_cpu");
  fs.writeFileSync(cfile, csrc);
  const cc = await phase("clang", () => leg_exec("clang", [...CC_FLAGS, cfile, "-lpthread", "-lm", ...file_link(csrc), "-o", bin], dir, CC_TIMEOUT));
  if (!cc.ok) {
    return cc.timeout
      ? { kind: "skip", out: "", why: "cc-timeout" }
      : { kind: "fail", out: "", why: "C COMPILE FAILURE:\n" + cc.err.slice(0, 2000) };
  }
  const cap = RUN_TIMEOUT * (THREADS > 1 ? 2 : 1) * (BATCH > 1 ? BATCH : 1);
  const run = await phase("binrun", () => leg_exec(bin, [], dir, cap));
  if (run.timeout) {
    return { kind: "fail", out: "", why: "C RUN TIMEOUT after " + String(cap) + "ms (interp finished — livelock/perf-cliff suspect)" };
  }
  if (run.code !== want) {
    return { kind: "fail", out: run.out.trim(), why: "C EXIT " + String(run.code) + " (want " + String(want) + "):\n" + (run.err + run.out).slice(0, 2000) };
  }
  return { kind: "ok", out: run.out.trim() };
}

let metal_lock: Promise<void> = Promise.resolve();

export function leg_metal(dir: string, base: string, want = 0): Promise<{ kind: "ok" | "skip" | "fail"; out: string; why?: string }> {
  const go = async (): Promise<{ kind: "ok" | "skip" | "fail"; out: string; why?: string }> => {
    const cfile = base + ".c";
    const csrc = fs.readFileSync(path.join(dir, cfile), "utf8");
    const cc = await phase("metal-clang", () => leg_exec("clang", [OPT, "-w", "-fno-slp-vectorize", "-x", "objective-c", "-fobjc-arc", "-DPAR_BACKEND=1", cfile, "-framework", "Metal", "-framework", "Foundation", "-lpthread", ...file_link(csrc), "-o", base + "_gpu"], dir, METAL_CC_TIMEOUT));
    if (!cc.ok) {
      return cc.timeout ? { kind: "skip", out: "", why: "metal-cc-timeout" } : { kind: "fail", out: "", why: "METAL COMPILE FAILURE:\n" + cc.err.slice(0, 2000) };
    }
    const run = await phase("metal-binrun", () => leg_exec(path.join(dir, base + "_gpu"), [], dir, METAL_RUN_TIMEOUT * (BATCH > 1 ? BATCH : 1)));
    if (run.timeout) {
      return { kind: "fail", out: "", why: "METAL RUN TIMEOUT after " + String(METAL_RUN_TIMEOUT) + "ms (interp finished — livelock suspect; a first-ever kernel compile can also trip this, re-run to confirm)" };
    }
    if (run.code !== want) {
      return { kind: "fail", out: run.out.trim(), why: "METAL EXIT " + String(run.code) + " (want " + String(want) + "):\n" + (run.err + run.out).slice(0, 2000) };
    }
    return { kind: "ok", out: run.out.trim() };
  };
  const res = metal_lock.then(go);
  metal_lock = res.then(() => undefined, () => undefined);
  return res;
}

// Save
// ----

export function save_file(sub: string, seed: bigint, header: string[], src: string): string {
  const dir = sub === "" ? FINDINGS : path.join(FINDINGS, sub);
  fs.mkdirSync(dir, { recursive: true });
  const f = path.join(dir, "seed-" + String(seed) + ".bend");
  const head = header.map((l) => "# " + l.replaceAll("\n", "\n# ")).join("\n");
  fs.writeFileSync(f, head + "\n# found=" + new Date().toISOString() + "\n\n" + src);
  return f;
}

export function save_finding(seed: bigint, kind: string, detail: string[], src: string): string {
  return save_file("", seed, ["FUZZ FINDING kind=" + kind, "repro: bun " + import.meta.filename + " 1 --seed " + String(seed) + (WITH_METAL ? " --metal" : "") + (WITH_IO ? " --io" : ""), ...detail], src);
}

export function save_aux(files: Record<string, string>): void {
  for (const [id, src] of Object.entries(files)) {
    fs.writeFileSync(path.join(FINDINGS, path.basename(id)), src);
  }
}

// Io probes
// ---------
// The orphan sweep: the in-process leak probe can only see what is
// still there when main's last effect runs, so a process the runtime
// let escape ENTIRELY -- forked after its fiber died, or never killed
// at exit -- is invisible to it. Each cancelled exec carries a unique
// marker; anything still answering to one after the binary is gone is
// a resource that outlived the program. Survivors are killed so a
// finding cannot poison the rest of the run.
export function io_marked(marks: string[]): Map<string, string[]> {
  const seen = new Map<string, string[]>();
  for (const m of marks) {
    const r = child.spawnSync("pgrep", ["-f", m], { encoding: "utf8" });
    seen.set(m, (r.stdout ?? "").split("\n").map((s) => s.trim()).filter((s) => /^\d+$/.test(s)));
  }
  return seen;
}

// io_orphans : Markers are seed-derived, so they are stable across runs by design --
// which means a survivor from an EARLIER run of the same seed would be
// blamed on this one. Diffing against the set that existed before the
// binary ran drops those, and drops a concurrent instance's children
// too unless they appear inside our window.
export function io_orphans(marks: string[], before: Map<string, string[]>): string[] {
  const live: string[] = [];
  for (const [m, pids] of io_marked(marks)) {
    const fresh = pids.filter((p) => !(before.get(m) ?? []).includes(p));
    if (fresh.length > 0) {
      live.push(m + " (" + fresh.join(",") + ")");
      for (const p of fresh) {
        try {
          process.kill(Number(p), "SIGKILL");
        } catch {
        }
      }
    }
  }
  return live;
}

// Tally
// -----

type Verdict = { kind: "ok" | "skip" | "fail"; note?: string };

const tally = { ok: 0, skip: 0, fail: 0 };
const feat_tally: Record<string, number> = {};
const skip_why: Record<string, number> = {};
let TMP = "";
let pool: Pool;

export function tally_feats(feats: string[]): void {
  for (const f of feats) {
    feat_tally[f] = (feat_tally[f] ?? 0) + 1;
  }
}

// Batch
// -----
// Compiling N programs costs N clang runs over a translation unit that is
// 89-95% IDENTICAL across seeds -- the runtime and, in --io, the emitted
// scheduler. Merging the members into ONE program pays that once, and pays
// ONE first-exec instead of N (a never-seen binary costs ~110ms on macOS
// against ~7ms of actual work).
//
// The merge is a CONCATENATION, not book surgery: every generated
// top-level name is <letters><uid>, so handing each member a disjoint uid
// range makes collisions impossible. (test.ts's suite_book needs term_ren
// only because hand-written tests collide.) `main` is the one name that
// would clash and becomes bm<k>; fzdead was the one other fixed name and
// is now uid-derived.
//
// The batch's answer is a ROTATE-XOR fold of its members' answers. That is
// a bijection in each argument, so a single wrong member ALWAYS changes it
// -- no masking -- and it keeps the batch a single U32, the one shape every
// runtime prints identically. So no C driver surgery: the binary is exactly
// what bend emits from an ordinary Bend program.
//
// A mismatch names the batch, not the seed, so attribution re-runs the
// members one at a time -- which costs only when something is wrong. That
// second pass regenerates at uid base 0, so a saved finding still
// reproduces under a bare `--seed N`. If the batch fails and no member
// does, that is reported too (batch-only): it means the merge itself, not
// the compiler, is at fault.
//
// A batched member's own worker request is interp-only: its compiled leg
// is the merged binary's, so a solo emission would be discarded. The
// straggler path re-emits with the member's known raw answer, skipping
// the interp legs it already passed.

const UID_STRIDE = 1_000_000;

export function batch_fold(vals: number[]): number {
  let a = vals[0] >>> 0;
  for (const v of vals.slice(1)) {
    a = (((((a << 7) >>> 0) | (a >>> 25)) >>> 0) ^ (v >>> 0)) >>> 0;
  }
  return a >>> 0;
}

export function batch_src(parts: GenParts[]): string {
  const imps = [...new Set(parts.flatMap((p) => p.imps))];
  const mains = parts.map((p, k) => "def bm" + String(k) + "() -> U32:\n  " + p.seal);
  const rot = "def bmrot(a: U32) -> U32:\n  ((a << 7) .|. (a >> 25))";
  const fold = parts.map((_, k) => k === 0
    ? "  ba0 = bm0()"
    : "  ba" + String(k) + " = (bmrot(ba" + String(k - 1) + ") .^. bm" + String(k) + "())");
  const main = "def main() -> U32:\n" + fold.join("\n") + "\n  ba" + String(parts.length - 1);
  const blocks = (imps.length > 0 ? [imps.join("\n")] : [])
    .concat(parts.flatMap((p) => p.decls))
    .concat(parts.flatMap((p) => p.defs))
    .concat([rot], mains, [main]);
  return "# fuzz batch of " + String(parts.length) + "\n\n" + blocks.filter((b) => b !== "").join("\n\n") + "\n";
}

// Test
// ----

export async function test_io(seed: bigint): Promise<Verdict> {
  const prog = phase_sync("gen", () => gen_io_program(seed));
  tally_feats(prog.feats);
  const base = "fzio" + String(seed);
  const w = await phase("worker:compile", () => pool.run(prog.src, "./" + base, "compile", prog.files));
  if (w.verdict === "reject" || w.verdict === "crash") {
    const f = save_finding(seed, w.verdict === "reject" ? "generator-reject" : "compiler-crash", ["stage=" + (w.stage ?? "check"), w.err ?? ""], prog.src);
    save_aux(prog.files);
    console.log("\nFINDING " + w.verdict + " seed=" + String(seed) + "\n  " + (w.err ?? "").split("\n")[0] + "\n  -> " + f);
    return { kind: "fail" };
  }
  if (w.verdict === "skip") {
    save_file("skipped", seed, ["SKIPPED reason=" + (w.stage ?? "?"), w.err ?? ""], prog.src);
    return { kind: "skip", note: w.stage };
  }
  if (CHECK_ONLY) {
    return { kind: "ok" };
  }
  const dir = phase_sync("tmpdir", () => fs.mkdtempSync(path.join(TMP, "io-")));
  const before = phase_sync("pgrep:before", () => io_marked(prog.marks));
  try {
    const c = await leg_c(dir, base, w.csrc ?? "", prog.code);
    if (c.kind === "skip") {
      save_file("skipped", seed, ["SKIPPED reason=" + (c.why ?? "?")], prog.src);
      return { kind: "skip", note: c.why };
    }
    if (c.kind === "fail" || c.out !== prog.out) {
      const why = c.kind === "fail" ? c.why ?? "" : "expected: " + prog.out + "\nobserved: " + c.out;
      const f = save_finding(seed, c.kind === "fail" ? "io-c-leg" : "io-diverge", [why], prog.src);
      save_aux(prog.files);
      console.log("\nFINDING io seed=" + String(seed) + "\n  " + why.split("\n")[0] + "\n  -> " + f);
      return { kind: "fail" };
    }
    const orph = phase_sync("pgrep:after", () => io_orphans(prog.marks, before));
    if (orph.length > 0) {
      const why = "processes outlived the program: " + orph.join(", ");
      const f = save_finding(seed, "io-orphan", [why], prog.src);
      save_aux(prog.files);
      console.log("\nFINDING io-orphan seed=" + String(seed) + "\n  " + why + "\n  -> " + f);
      return { kind: "fail" };
    }
    if (WITH_METAL) {
      const m = await leg_metal(dir, base, prog.code);
      if (m.kind === "skip") {
        save_file("skipped", seed, ["SKIPPED reason=" + (m.why ?? "?")], prog.src);
        return { kind: "skip", note: m.why };
      }
      if (m.kind === "fail" || m.out !== prog.out) {
        const why = m.kind === "fail" ? m.why ?? "" : "expected: " + prog.out + "\nobserved: " + m.out;
        const f = save_finding(seed, m.kind === "fail" ? "io-metal-leg" : "io-metal-diverge", [why], prog.src);
        save_aux(prog.files);
        console.log("\nFINDING io-metal seed=" + String(seed) + "\n  " + why.split("\n")[0] + "\n  -> " + f);
        return { kind: "fail" };
      }
    }
  } finally {
    // reap : reap unconditionally: an early return (the leak probe firing, a
    // skip) would otherwise leave the run's children alive for as long
    // as their command lasts. Reporting stays on the path above; this
    // is cleanup, and by then it has nothing left to find.
    phase_sync("pgrep:reap", () => io_orphans(prog.marks, before));
    phase_sync("rmdir", () => {
      if (!KEEP) {
        fs.rmSync(dir, { recursive: true, force: true });
      }
    });
  }
  return { kind: "ok" };
}

export async function test_batch(seeds: bigint[]): Promise<Verdict[]> {
  const collect: { seed: bigint; want: string }[] = [];
  const vs = await Promise.all(seeds.map((sd) => test_one(sd, collect)));
  if (collect.length < 2) {
    // stragglers : nothing survived to batch (or only one did): give the stragglers
    // their own compiled leg so coverage does not silently drop -- the
    // interp legs already passed, so the known answer skips them
    for (const m of collect) {
      const v = await test_one(m.seed, undefined, m.want);
      vs[seeds.indexOf(m.seed)] = v;
    }
    return vs;
  }
  const parts = collect.map((m, k) => phase_sync("gen", () => gen_program(m.seed, false, k * UID_STRIDE).parts));
  const src = batch_src(parts);
  const want = String(batch_fold(collect.map((m) => Number(m.want))));
  const base = "fzb" + String(collect[0].seed);
  const w = await phase("worker:batch", () => pool.run(src, "./" + base, "compile"));
  let why: string | null = null;
  if (w.verdict !== "ok") {
    why = "merged " + w.verdict + " (" + (w.stage ?? "?") + "): " + (w.err ?? "").split("\n")[0];
  } else {
    const dir = fs.mkdtempSync(path.join(TMP, "b-"));
    try {
      const c = await leg_c(dir, base, w.csrc ?? "");
      if (c.kind === "fail") {
        why = c.why ?? "merged C leg failed";
      } else if (c.kind === "ok" && c.out !== want) {
        why = "merged fold: want " + want + ", got " + c.out;
      }
      // leg_metal : the merged binary carries the Metal leg too -- without this the
      // batch silently drops it and --metal becomes a no-op
      if (why === null && WITH_METAL) {
        const mm = await leg_metal(dir, base);
        if (mm.kind === "fail") {
          why = mm.why ?? "merged Metal leg failed";
        } else if (mm.kind === "ok" && mm.out !== want) {
          why = "merged Metal fold: want " + want + ", got " + mm.out;
        }
      }
    } finally {
      if (!KEEP) {
        fs.rmSync(dir, { recursive: true, force: true });
      }
    }
  }
  if (why === null) {
    return vs;
  }
  // attribute : attribute: re-run each member alone, at uid base 0, so whatever it
  // saves reproduces under a bare --seed
  console.log("\nbatch of " + String(collect.length) + " failed, isolating: " + why.split("\n")[0]);
  let blamed = false;
  for (const m of collect) {
    const v = await test_one(m.seed);
    vs[seeds.indexOf(m.seed)] = v;
    if (v.kind === "fail") {
      blamed = true;
    }
  }
  if (!blamed) {
    const f = save_finding(collect[0].seed, "batch-only",
      ["no member fails alone -- the MERGE is at fault, not the compiler", why,
        "members: " + collect.map((m) => String(m.seed)).join(" ")], src);
    console.log("FINDING batch-only seeds=" + collect.length + "\n  " + why.split("\n")[0] + "\n  -> " + f);
    vs[0] = { kind: "fail" };
  }
  return vs;
}

export async function test_one(seed: bigint, collect?: { seed: bigint; want: string }[], known?: string): Promise<Verdict> {
  if (WITH_IO) {
    return test_io(seed);
  }
  const { src, raw, feats, files } = phase_sync("gen", () => gen_program(seed, false));
  // fuzzy : f32 transcendentals are each backend libm's FLOAT routines by ruling
  // (wontfix "F32 transcendental precision"); the interpreter can only
  // compute double + fround, so their values may legitimately differ by
  // ULPs. A trans program keeps every leg EXCEPT the value comparison:
  // it stays out of the merged fold (one flip would poison the batch
  // into a spurious batch-only finding) and a lone mismatch is a counted
  // skip, not a finding.
  const fuzzy = feats.includes("trans");
  const base = "fz" + String(seed);
  let iout: string;
  let want: string;
  let csrc: string;
  let ms: number | undefined;
  if (known !== undefined) {
    // known : a batch straggler -- its interp legs already passed with this
    // raw answer, so only the compiled legs are owed: re-emit and go
    const c = await phase("worker:emit", () => pool.run(src, "./" + base, "compile", files));
    if (c.verdict === "skip") {
      save_file("skipped", seed, ["SKIPPED reason=" + (c.stage ?? "?"), c.err ?? ""], src);
      return { kind: "skip", note: c.stage };
    }
    if (c.verdict !== "ok") {
      const f = save_finding(seed, "compiler-crash", ["stage=" + (c.stage ?? "?"), c.err ?? ""], src);
      save_aux(files);
      console.log("\nFINDING compiler-crash seed=" + String(seed) + " stage=" + (c.stage ?? "?") + "\n  " + (c.err ?? "").split("\n")[0] + "\n  -> " + f);
      return { kind: "fail" };
    }
    iout = known;
    want = known;
    csrc = c.csrc ?? "";
  } else {
    tally_feats(feats);
    // mode : a batched non-fuzzy member's compiled leg is the merged binary's,
    // so a solo emission would be discarded -- interp skips it
    const mode: WorkerMode = collect !== undefined && !fuzzy ? "interp" : "full";
    const [w, oracle] = await Promise.all([
      phase("worker:full", () => pool.run(src, "./" + base, mode, files)),
      phase("worker:oracle", () => pool.run(raw, "./" + base + "r", "interp", files)),
    ]);
    if (oracle.verdict === "reject" || oracle.verdict === "crash") {
      const f = save_finding(seed, "raw-" + oracle.verdict, ["stage=" + (oracle.stage ?? "check"), oracle.err ?? ""], raw);
      save_aux(files);
      console.log("\nFINDING raw-" + oracle.verdict + " seed=" + String(seed) + "\n  " + (oracle.err ?? "").split("\n")[0] + "\n  -> " + f);
      return { kind: "fail" };
    }
    if (oracle.verdict === "skip") {
      save_file("skipped", seed, ["SKIPPED reason=raw-" + (oracle.stage ?? "?"), oracle.err ?? ""], raw);
      return { kind: "skip", note: "raw-" + (oracle.stage ?? "?") };
    }
    if (w.verdict === "reject") {
      const f = save_finding(seed, "generator-reject", [w.err ?? ""], src);
      save_aux(files);
      console.log("\nFINDING generator-reject seed=" + String(seed) + "\n  " + (w.err ?? "").split("\n")[0] + "\n  -> " + f);
      return { kind: "fail" };
    }
    if (w.verdict === "skip") {
      save_file("skipped", seed, ["SKIPPED reason=" + (w.stage ?? "?"), w.err ?? ""], src);
      return { kind: "skip", note: w.stage };
    }
    if (w.verdict === "crash") {
      const f = save_finding(seed, "compiler-crash", ["stage=" + (w.stage ?? "?"), w.err ?? ""], src);
      save_aux(files);
      console.log("\nFINDING compiler-crash seed=" + String(seed) + " stage=" + (w.stage ?? "?") + "\n  " + (w.err ?? "").split("\n")[0] + "\n  -> " + f);
      return { kind: "fail" };
    }
    iout = (w.out ?? "").trim();
    want = (oracle.out ?? "").trim();
    if (iout !== want) {
      const f = save_finding(seed, "seal-diverge", ["raw interp:    " + want, "sealed interp: " + iout], src);
      save_aux(files);
      console.log("\nFINDING seal-diverge seed=" + String(seed) + " raw=" + want + " sealed=" + iout + "\n  -> " + f);
      return { kind: "fail" };
    }
    if (CHECK_ONLY) {
      return { kind: "ok" };
    }
    // flat : the module system's real differential -- the same book as ONE
  // file. Layout is meaning-free by contract, so a split book and its
  // flat twin must answer alike (name resolution across imports, load
  // order, cross-file shadowing); checking alone proves nothing. It
  // runs BEFORE the batch hand-off: the leg is interp-only and cheap,
  // and a batched member would otherwise never be checked
  if (!NO_META && Object.keys(files).length > 0) {
    const { src: fsrc } = gen_program(seed, false, 0, true);
    const fw = await phase("worker:flat", () => pool.run(fsrc, "./" + base, "interp"));
    if (fw.verdict === "reject" || fw.verdict === "crash") {
      const f = save_finding(seed, "module-" + fw.verdict, ["the single-file twin of a split book was refused:", fw.err ?? "", "--- raw oracle: " + want], fsrc);
      save_aux(files);
      console.log("\nFINDING module-" + fw.verdict + " seed=" + String(seed) + "\n  -> " + f);
      return { kind: "fail" };
    }
    if (fw.verdict === "ok" && (fw.out ?? "").trim() !== want) {
      const f = save_finding(seed, "module-diverge", ["raw oracle: " + want, "split-book interp: " + iout, "flat-book interp: " + (fw.out ?? "").trim()], fsrc);
      save_aux(files);
      console.log("\nFINDING module-diverge seed=" + String(seed) + " raw=" + want + " flat=" + (fw.out ?? "").trim() + "\n  -> " + f);
      return { kind: "fail" };
    }
  }
  if (collect !== undefined && !fuzzy) {
      // collect : the interpreter legs passed; this seed's compiled leg is owed by
      // the batch it belongs to
      collect.push({ seed, want });
      return { kind: "ok" };
    }
    csrc = w.csrc ?? "";
    ms = w.ms;
  }
  const dir = fs.mkdtempSync(path.join(TMP, "p-"));
  try {
    const c = await leg_c(dir, base, csrc);
    if (c.kind === "skip") {
      save_file("skipped", seed, ["SKIPPED reason=" + (c.why ?? "?")], src);
      return { kind: "skip", note: c.why };
    }
    if (c.kind === "fail") {
      const f = save_finding(seed, "c-leg", [c.why ?? "", "raw oracle: " + want, "sealed interp: " + iout + (ms !== undefined ? " (" + String(ms) + "ms)" : "")], src);
      save_aux(files);
      console.log("\nFINDING c-leg seed=" + String(seed) + "\n  " + (c.why ?? "").split("\n")[0] + "\n  -> " + f);
      return { kind: "fail" };
    }
    if (c.out !== want) {
      if (fuzzy) {
        save_file("skipped", seed, ["SKIPPED reason=trans-ulp", "raw oracle: " + want, "c: " + c.out], src);
        return { kind: "skip", note: "trans-ulp" };
      }
      const f = save_finding(seed, "c-diverge", ["raw oracle: " + want, "sealed interp: " + iout, "c: " + c.out], src);
      save_aux(files);
      console.log("\nFINDING c-diverge seed=" + String(seed) + " raw=" + want + " c=" + c.out + "\n  -> " + f);
      return { kind: "fail" };
    }
    if (WITH_METAL) {
      const m = await leg_metal(dir, base);
      if (m.kind === "fail") {
        const f = save_finding(seed, "metal-leg", [m.why ?? "", "interp: " + iout + (ms !== undefined ? " (" + String(ms) + "ms)" : "")], src);
        save_aux(files);
        console.log("\nFINDING metal-leg seed=" + String(seed) + "\n  " + (m.why ?? "").split("\n")[0] + "\n  -> " + f);
        return { kind: "fail" };
      }
      if (m.kind === "ok" && m.out !== want) {
        if (fuzzy) {
          save_file("skipped", seed, ["SKIPPED reason=trans-ulp", "raw oracle: " + want, "metal: " + m.out], src);
          return { kind: "skip", note: "trans-ulp" };
        }
        const f = save_finding(seed, "metal-diverge", ["raw oracle: " + want, "sealed interp: " + iout, "metal: " + m.out], src);
        save_aux(files);
        console.log("\nFINDING metal-diverge seed=" + String(seed) + " raw=" + want + " metal=" + m.out + "\n  -> " + f);
        return { kind: "fail" };
      }
      if (m.kind === "skip") {
        save_file("skipped", seed, ["SKIPPED reason=" + (m.why ?? "?")], src);
        return { kind: "skip", note: m.why };
      }
    }
  } finally {
    if (!KEEP) {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  }
  if (!NO_META) {
    const { src: msrc, files: mfiles } = gen_program(seed, true);
    if (msrc !== src) {
      const mw = await pool.run(msrc, "./" + base, "interp", mfiles);
      if (mw.verdict === "reject" || mw.verdict === "crash") {
        const f = save_finding(seed, "metamorphic-reject", ["min-parens spelling rejected:", mw.err ?? "", "--- raw oracle: " + want, "sealed max-parens interp: " + iout], msrc);
        save_aux(files);
        console.log("\nFINDING metamorphic-reject seed=" + String(seed) + "\n  -> " + f);
        return { kind: "fail" };
      }
      if (mw.verdict === "ok" && (mw.out ?? "").trim() !== want) {
        const f = save_finding(seed, "metamorphic-diverge", ["raw oracle: " + want, "max-parens interp: " + iout, "min-parens interp: " + (mw.out ?? "").trim()], msrc);
        save_aux(files);
        console.log("\nFINDING metamorphic-diverge seed=" + String(seed) + " raw=" + want + " min=" + (mw.out ?? "").trim() + "\n  -> " + f);
        return { kind: "fail" };
      }
    }
  }
  return { kind: "ok" };
}

// Fuzz
// ----

export async function fuzz_run(): Promise<void> {
  if (cli_flag("--dump") || cli_flag("--dump-min") || cli_flag("--dump-raw")) {
    if (WITH_IO) {
      process.stdout.write(gen_io_program(BASE_SEED).src);
    } else {
      const prog = gen_program(BASE_SEED, cli_flag("--dump-min"));
      process.stdout.write(cli_flag("--dump-raw") ? prog.raw : prog.src);
    }
    return;
  }
  fs.mkdirSync(FINDINGS, { recursive: true });
  fs.writeFileSync(path.join(FINDINGS, ".gitignore"), "*\n!.gitignore\n");
  TMP = fs.mkdtempSync(path.join(os.tmpdir(), "bend-fuzz-"));
  pool = new Pool(Number(cli_opt("--pool", String(Math.min(JOBS * (BATCH > 1 ? 2 : 1), BATCH > 1 ? 10 : 6)))));
  const smoke = WITH_IO
    ? [9n, 3n]
    : [1963n, 1782n, 44n, 115n, 4n, 8n];
  const fixed = SMOKE ? smoke : null;
  const count = fixed?.length ?? COUNT;
  console.log("bend3 fuzz: count=" + String(count) + (LOOP ? " (loop)" : "") + " seed=" + String(BASE_SEED) + " jobs=" + String(JOBS) + " threads=" + String(THREADS) + (SMOKE ? " +smoke" : "") + (CHECK_ONLY ? " +check-only" : "") + (WITH_IO ? " +io" : "") + (WITH_METAL ? " +metal" : "") + (NO_META || WITH_IO || CHECK_ONLY ? " -metamorphic" : ""));
  const t0 = performance.now();
  let seed = BASE_SEED;
  let done = 0;
  let launched = 0;
  const inflight = new Set<Promise<void>>();
  const total = (): number => (LOOP && fixed === null ? Infinity : count);
  while (done < total()) {
    while (inflight.size < JOBS && launched < total()) {
      const batch: bigint[] = [];
      while (batch.length < (WITH_IO ? 1 : BATCH) && launched < total()) {
        batch.push(fixed?.[launched] ?? seed);
        if (fixed === null) {
          seed = rng_step(seed);
        }
        launched++;
      }
      const p = (batch.length > 1 ? test_batch(batch) : test_one(batch[0]).then((v) => [v]))
        .then((vs) => {
          for (const v of vs) {
            tally[v.kind]++;
            if (v.kind === "skip" && v.note !== undefined) {
              skip_why[v.note] = (skip_why[v.note] ?? 0) + 1;
            }
          }
        })
        .catch((e: unknown) => {
          tally.fail++;
          console.log("\nFUZZER ERROR seeds=" + batch.map(String).join(",") + ": " + String(e));
        })
        .finally(() => {
          const was = done;
          done += batch.length;
          inflight.delete(p);
          if (Math.floor(done / 25) > Math.floor(was / 25)) {
            const dt = (performance.now() - t0) / 1000;
            process.stdout.write("\r" + String(done) + " done, " + (done / dt).toFixed(1) + "/s, ok=" + String(tally.ok) + " skip=" + String(tally.skip) + " FAIL=" + String(tally.fail) + "   ");
          }
        });
      inflight.add(p);
    }
    if (inflight.size > 0) {
      await Promise.race(inflight);
    }
  }
  pool.close();
  if (!KEEP) {
    fs.rmSync(TMP, { recursive: true, force: true });
  }
  const dt = (performance.now() - t0) / 1000;
  console.log("\n\n" + String(done) + " programs in " + dt.toFixed(1) + "s (" + (done / dt).toFixed(1) + "/s)");
  console.log("ok=" + String(tally.ok) + " skip=" + String(tally.skip) + " FAIL=" + String(tally.fail));
  const feats = Object.entries(feat_tally).sort((a, b) => b[1] - a[1]).map(([k, v]) => k + "=" + String(v)).join(" ");
  console.log("features: " + feats);
  if (PROFILE) {
    phase_report();
  }
  if (Object.keys(skip_why).length > 0) {
    console.log("skips: " + Object.entries(skip_why).map(([k, v]) => k + "=" + String(v)).join(" "));
  }
  const smoke_need = WITH_IO
    ? ["forkio-goal", "print-goal", "doio-goal", "baseio-goal"]
    : ["comp-goal", "if-goal", "open-goal", "tuple", "unit", "u32dep-goal", "assert-goal", "fdiv", "trans",
      "typed-reuse", "mint", "seal-add", "seal-xor", "seal-dist", "seal-mask", "seal-cmp", "seal-rot", "ford-goal",
      "module", "lib-goal"];
  const smoke_miss = SMOKE ? smoke_need.filter((f) => feat_tally[f] === undefined) : [];
  if (smoke_miss.length > 0) {
    console.log("smoke missing features: " + smoke_miss.join(" "));
  }
  if (tally.fail > 0 || (SMOKE && tally.skip > 0) || smoke_miss.length > 0) {
    console.log("findings in " + FINDINGS);
    process.exit(1);
  }
}

if (path.resolve(process.argv[1] ?? "") === import.meta.filename) {
  if (cli_flag("--worker")) {
    await worker_main();
  } else {
    await fuzz_run();
  }
}
