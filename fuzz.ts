#!/usr/bin/env bun
// Differential fuzzer for the bend2-core toolchain (bend2/bend.ts + comp.ts).
// Each seed deterministically generates a well-typed, terminating Bend program
// in two algebraically-equal spellings (raw and identity-sealed) and runs it
// across every leg:
//
//   - interp (the spec): term_snf on the result defs, raw and sealed, or on
//     a pure main, printed by term_show — the trusted-kernel evaluation
//     path, and the only leg a book without Base has. The raw value is the
//     oracle; the sealed one must equal it, so a broken seal cannot bless
//     itself. The interpreter runs base's structural code (Word adder
//     chains), so this leg is also a bit-level spec differential against the
//     native ops the backends substitute.
//   - C (compile_book): one standalone .c, built with clang at the group's
//     drawn -O level and run sequentially (--threads 1 --gpu off), then in
//     parallel at the group's drawn thread count; with --metal / --cuda the
//     same .c is rebuilt for the device and run --gpu on.
//   - JS (js_book): the emitted .js run under bun.
//
// Every checked book also meets the template table's invariants (distinct
// ~ argument keys name distinct instances; a key carries its literals
// exactly), which every generated template call exercises.
//
// What a seed's program is — Base or an empty initial environment, free
// declaration names, whether the member sits in a file of its own, a
// foreign effect, a clash mutant, a pure printed main, the IO tail, the
// surface-syntax rate — is its profile, drawn from the seed alone (see
// profile()), so a solo re-run reproduces it. Only --io-pct shapes it from
// the command line.
//
// The program shape ties the legs together:
//
//   def result() -> U32: ...   pure, small, F32-free — interp-comparable
//   def extra()  -> U32: ...   heavy: F32 (stuck in the interpreter by
//                              design — base's F32 ops are native claims),
//                              fork trees with ! marks, long loops, big
//                              literals — compared across compiled legs only,
//                              with the sequential C run as the reference
//   def main() -> IO(Unit):    prints result, an optional deterministic IO
//                              tail (file roundtrip, get_env, print_err,
//                              IO.die exit codes), then extra
//
// Compiled legs compare full stdout/stderr/exit; the `result` line must
// equal the interpreter's decoded value. A `trans`-flagged program (float
// transcendentals) downgrades a JS-vs-C mismatch on the extra line to a
// counted skip (libm float vs fround(double) may differ by ULPs; C lanes
// and the GPU stay exact per the repo's own ruling).
//
// GENERATION IS GOAL-DIRECTED SYNTHESIS over the current type system:
// syn(c, goal, env, fuel) assembles correct-by-construction productions per
// goal head; types are synthesis goals too (syn_ty), and the machinery is
// quantity-aware end to end:
//   - the var quantity system: -x / x / +x binder sigils, affine
//     consumption (Lone once, Many free, + only at concretely-Data types,
//     `+x2 = x` copies), erased params and fields;
//   - quantity polymorphism: minted defs and datatypes take Quant
//     parameters (`def f(a, -A: Kind(a), ...)`), instantiated at &1, &2 and
//     at quantity VARIABLES bound by enclosing generics;
//   - data-kinded types: generated ADTs declare `is Data`, `is Type`,
//     `is Kind(a)` and `is Kind(a <&> b)`; instantiation respects the
//     declared kinds; the Fill (`D<..>` = &1) and Plus (`+D<..>` = &2)
//     sugars are all emitted.
//
// Surface forms compose with the same terms and types in every run: inline
// matches, applied lambdas, rewrites, erased lets, annotations and constructor
// destructuring all reach every applicable backend.
//   - statement matches scrutinize def parameters or bound fields.
//     Applied inline matches accept computed scrutinees in the checker;
//     the current C and JS emitters cannot compile all these forms.
//   - destructuring lets ((a,b) = p, K{x} = v) are matches: params/fields
//     only.
//   - patterns name ALL fields, erased ones included; Nat literal patterns
//     (0n, 1n+p, 3n+p deep peels) are ctor sugar and fine; U32/F32/Word
//     literal or structural patterns DIE in the C emitter by design
//     ("a structural view of a machine word") — never emitted here, though
//     the JS emitter accepts them (asymmetry is by design, not a finding).
//   - defs are emitted in creation = dependency order; no forward refs.
//   - a self-call shrinks at the first live argument that changes: every
//     live argument before it passes through unchanged (the parameter, or
//     the variable row that re-bound it), the shrinking one is a sub-field
//     bound by a constructor pattern (a variable row binds the whole value,
//     which does not shrink), later ones are free; @unsafe opts out of
//     descent and is emitted rarely.
//   - a nested match scrutinizes the last binder of the enclosing row's
//     last column, a field binder (a variable row's binder after literal
//     rows is a known constructor and cannot be matched again), never a +
//     binder; one row's binders are distinct; a binder of a descending
//     column never shadows a name in scope.
//   - non-inferable values in let position ride `x = {v : T}` annotations;
//     do-binds are annotated (`x : T <- act`); partial applications stop at
//     exactly live-1 arguments (deeper partials die in js_book).
//   - a + marks any binder reusable: a case field (K{+x}), a variable row,
//     a tuple or constructor let, one per name of a parallel let
//     (+a +b = f g), a lambda (+x => e), a do bind and a do let. h <> t is
//     the cons in terms and patterns, [] the empty list, [a, b] a literal
//     pattern with _ the wildcard row; [x : T*n] (n a literal power of
//     two) and [x : T^d] build arrays; a[i] <- v as a statement re-binds
//     a; a bare term in a do block is a step and ";" joins two; \u{hex}
//     escapes a code point. An opaque handle (File, Chan, ..) is a law
//     with no constructor, applied with parens: Chan(A).
//   - an operator is a method named by the frame around it, "(a + b : T)"
//     being T.add: + - * / % .&. .|. .^. << >> (Nat rhs!) <= >= > at U32,
//     Nat (+ only) and F32; && || ++ are fixed. e_bin spells the frame
//     from the op's family tag ("+n" Nat, "+." F32). There is no <, ==
//     or != infix; those are calls folded through a minted Bool reader.
//
// TYPES ARE TERMS. Beside the datatypes it mints, the generator mints
// families: a type-level def by match on one index (Nat, Bool or a minted
// enum), `law F: for x: I; Data` then `def F(x): match x: ..`, each arm a
// type drawn like any other in a scope where the arm's sub-index is a term
// the type may mention, through the family itself at it or through a
// datatype minted with the index as an erased parameter (Word's idiom,
// `type D<-p: Nat> is Data: K{.., t: F(p)}`). An applied family F(3n) is
// then a type wherever a type goes; a closed index unfolds to its arm and
// a variable one goes through the family's index-generic defs (mk: the
// value by match on the index; rd: the reader, its arm read inline). A
// family's arm may be a proposition: Empty, an equality of literals that
// agree or clash, or its negation; a dependent pair &x: A -> B (Exists)
// holds a witness under which the evidence has a value; a clash is refuted
// by a rewrite through a discriminating family; a minted def may take
// evidence about an earlier index parameter and is called at the indices
// whose arm has a value; the law spelling of such a def reads `for x: A
// where P(x)` and a pair result reads `exs`. None of this is a kit: the
// same syn/syn_ty/rd productions serve every type, so a Vec, a Word, an
// IsZero, an Exists and their compositions emerge from one generator.
//
// DEFS ARE ONE PRODUCTION. def_new(c, goal, env, fuel) mints every def with
// control flow: parameters drawn as types (a state parameter of the goal's
// own type a third of the time), a match at the head of the body over
// some of them (a decision tree over their constructors, a variable row
// where an arm does not care, a nested match on a row's last binder), each
// leaf synthesized by syn against the goal under the row's binders. The
// def sits in the registry while its leaves are drawn and may call itself
// only with a sub-field of its decreasing column, each once per leaf, so a
// countdown loop, a fold, a tree recursion (two self-calls in a parallel
// let, `!`-marked at times), a record rebuilt each step, a tuple-returning
// walk and an IO loop are the same production at different goals; a
// monadic goal (IO, Maybe, Result) may take a do-block leaf; a
// loop-flavoured def ends every recursive leaf in a tail self-call and
// counts down a long Nat. Arrays are a type like any other (a parameter, a
// field, a goal), linear, read and measured through pairs.
//
// STATEMENTS ARE THREE PRODUCTIONS: a value of any type read to a U32, a
// parallel let (the one fork shape, `!`-marked at times) and a proof
// (reflexivity, Base's lemmas, a minted inductive theorem, composed by
// Equal.sym/cong/trans, then rewritten on). CALLS ARE ONE REGISTRY: the
// defs the program mints and Base's own public defs, read off the checked
// Base book (quantity, type and template parameters included), so every
// Array, Map, Set, List, String, Char, Maybe, Result and Pair operation Base
// offers is a call any goal of its type may take; the numeric families keep
// hand-weighted rosters (num_gen_*) because an arbitrary U32 or Nat argument
// can unfold a unary Nat the interpreter never finishes. Primitives with
// special compilation (comp.ts OPERATIONS/OPTIMIZED and base.bend's native
// claims) are all reachable: the full U32/F32/Nat op rosters, Bool/Cmp
// tables, Char packing, string and list literals, the U32 and F32 show+read
// roundtrips, F32.bits, the a[i] / a[i] <- v array sugar, Nat constant
// tables (CONSTV), fork trees with `!` GPU marks, closures, partial
// application (of Base's natives too), templates, erased params/fields.
//
// GROUPS: a group of seeds (its size drawn from its first seed) merges into
// ONE compiled program — a concatenation at disjoint uid ranges, or files
// apart by namespace — whose main prints each member's result/tail/extra in
// order, so clang and process spawn are paid once per group while
// attribution stays per-line. The interp legs run per member (they are the
// bottleneck and parallelize across the worker pool). A member whose tail
// dies is reached through the FZ_MEMBER environment variable, so one binary
// serves the plain run and one run per dying member. A failing group re-runs
// its members solo at uid base 0 under the group's lanes, so saved findings
// reproduce under their repro line; a group that fails when no member does
// is itself a finding (batch-only: the merge or whole-book emission is at
// fault).
//
// Findings land in findings/seed-N.bend (program + verdict header + exact
// repro line), beside the build that failed and a delta-reduced program.
// Checker/worker resource exhaustion is persisted as a skip; a compiled CPU
// or GPU run that outlives its cap is a finding for triage. The generator is
// version-controlled but findings are not: a generator edit remaps the seeds
// whose draws reach the edited site (each adt, statement and minted def
// draws from its own split stream), so the saved program is the durable
// artifact.

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as readline from "node:readline";
import { pathToFileURL } from "node:url";

// ROOT : the bend2-core checkout under test — the cwd when run from the
// repo root, else a sibling of this repo named bend2-core (or bend2)
const ROOT0 = [
  process.cwd(),
  path.join(import.meta.dirname, "..", "bend2-core"),
  path.join(import.meta.dirname, "..", "bend2"),
].find((d) => fs.existsSync(path.join(d, "bend2", "bend.ts")));
if (ROOT0 === undefined) {
  console.error("cannot find the bend2-core checkout: run from its repo root, or keep it as a sibling `bend2-core/` of this repo");
  process.exit(1);
}
const ROOT: string = ROOT0;
const BEND_TS = path.join(ROOT, "bend2", "bend.ts");
const COMP_TS = path.join(ROOT, "bend2", "comp.ts");
// FZ_FINDINGS : where a run saves, the repo's findings/ by default
const FINDINGS = process.env.FZ_FINDINGS ?? path.join(import.meta.dirname, "findings");
const WORKER_LIFE = 300;
const WORKER_TIMEOUT = 45_000;
const CC_TIMEOUT = 120_000;
const RUN_TIMEOUT = 20_000;
const GPU_CC_TIMEOUT = 300_000;
const GPU_RUN_TIMEOUT = 60_000;

// CLI
// ---

const argv = process.argv.slice(2);
const cli_flag = (s: string): boolean => argv.includes(s);
const cli_opt = (s: string, d: string): string => {
  const i = argv.indexOf(s);
  return i >= 0 && i + 1 < argv.length ? argv[i + 1] : d;
};
const VALUED_FLAGS = ["--seed", "--jobs", "--io-pct", "--threads", "--opt"];
// the count: a number of seeds, or a duration (90m, 12h) to run until
const COUNT_ARG = argv.find((a, i) => /^\d+(?:\.\d+)?[smh]?$/.test(a) && !VALUED_FLAGS.includes(argv[i - 1] ?? "")) ?? "100";
const COUNT_UNIT = /[smh]$/.exec(COUNT_ARG)?.[0];
const COUNT = COUNT_UNIT === undefined ? Number(COUNT_ARG) : Infinity;
const DEADLINE = COUNT_UNIT === undefined ? Infinity
  : Date.now() + parseFloat(COUNT_ARG) * { s: 1_000, m: 60_000, h: 3_600_000 }[COUNT_UNIT as "s" | "m" | "h"];
const BASE_SEED = BigInt(cli_opt("--seed", String(Math.floor(Math.random() * 2 ** 48))));
const JOBS = Number(cli_opt("--jobs", String(Math.max(1, Math.min(8, os.cpus().length - 2)))));
const WITH_METAL = cli_flag("--metal");
const WITH_CUDA = cli_flag("--cuda");
const IO_PCT = Math.max(0, Math.min(100, Number(cli_opt("--io-pct", "20"))));
// repro overrides of the lane parameters a group draws (see group_lanes):
// a finding isolated out of a batch runs under the batch's own
const THREADS_ARG = cli_opt("--threads", "");
const OPT_ARG = cli_opt("--opt", "");

function print_help(): void {
  process.stdout.write([
    "bend2 differential fuzzer — generates typed Bend programs and cross-checks",
    "the interpreter (spec), the compiled C backend (sequential, parallel,",
    "Metal, CUDA) and the compiled JS backend.",
    "",
    "Usage: bun fuzz.ts [count] [options]   (from the bend2-core repo root,",
    "       or with bend2-core as a sibling checkout)",
    "",
    "  count          seeds to run (default 100), or a duration: 90m, 12h",
    "",
    "Options:",
    "  --seed N       base seed (default: random; findings print their repro)",
    "  --jobs N       parallel groups in flight (default: min(8, cpus-2))",
    "  --io-pct N     percent of seeds with a deterministic IO tail in main",
    "                 (files, env, stderr, exit codes, fibers, channels,",
    "                 timers; default 20)",
    "  --metal        ALSO build each program with -DBEND_METAL and run",
    "                 --gpu on (macOS; GPU runs are serialized)",
    "  --cuda         ALSO build each program with -DBEND_CUDA and run",
    "                 --gpu on (Linux + NVIDIA)",
    "  --dump         print the program of --seed (both spellings) and exit",
    "  -h, --help     show this help and exit",
    "",
    "Everything else is drawn per seed: Base or an empty environment, free",
    "declaration names, the file layout, foreign effects, name clashes, a",
    "pure printed main, the surface-syntax rate; per group: the batch size,",
    "the C-PAR thread count and the clang -O level (--threads N / --opt N",
    "override the last two; repro lines use them).",
    "",
    "Findings land in findings/ (git-ignored) with a `repro:` header line, a",
    "reduced program beside them (seed-N.min.bend) and the compiled sources",
    "(seed-N.build/); resource skips in findings/skipped/. FZ_FINDINGS=dir",
    "saves elsewhere. The run ends with a phase profile and the features",
    "never reached. See the top-of-file comment for the full model.",
    "",
  ].join("\n"));
}

// Phase
// -----
// Concurrency means phases overlap and total more than the run: the point
// is the RATIO between phases and the per-call cost, not the sum.

const PHASE: Record<string, { ms: number; n: number; all: number[] }> = {};

function phase_note(name: string, t: number): void {
  const p = PHASE[name] ?? { ms: 0, n: 0, all: [] };
  const d = performance.now() - t;
  p.ms += d;
  p.n += 1;
  p.all.push(d);
  PHASE[name] = p;
}

async function phase<A>(name: string, f: () => Promise<A>): Promise<A> {
  const t = performance.now();
  try {
    return await f();
  } finally {
    phase_note(name, t);
  }
}

function phase_sync<A>(name: string, f: () => A): A {
  const t = performance.now();
  try {
    return f();
  } finally {
    phase_note(name, t);
  }
}

function phase_report(): void {
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

function rng_step(x: bigint): bigint {
  return (x + 0x9e3779b97f4a7c15n) & M64;
}

function rng_mix64(x: bigint): bigint {
  let z = x & M64;
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & M64;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & M64;
  return z ^ (z >> 31n);
}

// str_hash : FNV-1a over the label's code units
function str_hash(s: string): bigint {
  let h = 0xcbf29ce484222325n;
  for (let i = 0; i < s.length; i++) {
    h = ((h ^ BigInt(s.charCodeAt(i))) * 0x100000001b3n) & M64;
  }
  return h;
}

// Gen : one sequential stream. split(label, i) derives a child stream
// from the stream's ROOT (its seed), never its position, so a child's
// draws depend only on the path of labels that led to it: an edit that
// changes how many draws one site makes remaps that site's subtree and
// nothing beside it.
class Gen {
  root: bigint;
  state: bigint;
  constructor(seed: bigint) {
    this.root = seed & M64;
    this.state = this.root;
  }
  split(label: string, i: number): Gen {
    return new Gen(rng_mix64(rng_mix64(this.root ^ str_hash(label)) + BigInt(i)));
  }
  r(): bigint {
    this.state = rng_step(this.state);
    return rng_mix64(this.state);
  }
  int(n: number): number {
    return Number(this.r() % BigInt(Math.max(1, n)));
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
    if (total <= 0) {
      throw new Error("weighted choice has no available production");
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
// A rendered expression plus the precedence of its top operator (99 = atom).
// Operands always parenthesize unless atomic (op2 does not associate in the
// object grammar and mixed levels would mis-parse otherwise); statement-head
// positions may stay bare.

const PREC: Record<string, number> = { "||": 2, "&&": 3, "++": 5 };

// An operator is a method named by the ": T" frame around it: "+n" is
// Nat's add, a dotted op ("+.", "<=.") is F32's, the rest are U32's.
// F32's ==. !=. <. have no infix (only <= >= > ride one) and become
// calls. The frame's parens make every op expression an atom.
const F32_CALLS: Record<string, string> = { "==.": "is_eq", "!=.": "is_ne", "<.": "is_lt" };

type E = { s: string; p: number; head?: string };

const e_atom = (s: string): E => ({ s, p: 99 });
const e_call = (head: string, s: string): E => ({ s, p: 99, head });

function e_at(e: E): string {
  return e.p === 99 ? e.s : "(" + e.s + ")";
}

function e_bin(l: E, op: string, r: E): E {
  if (op in PREC) {
    return { s: e_at(l) + " " + op + " " + e_at(r), p: PREC[op] };
  }
  if (op in F32_CALLS) {
    return e_fn("F32." + F32_CALLS[op], l, r);
  }
  const f32 = op.endsWith(".") && !op.startsWith(".");
  const ty = op === "+n" ? "Nat" : f32 ? "F32" : "U32";
  const o = op === "+n" ? "+" : f32 ? op.slice(0, -1) : op;
  return e_atom("(" + e_at(l) + " " + o + " " + e_at(r) + " : " + ty + ")");
}

function e_fn(op: string, ...xs: E[]): E {
  return e_atom(op + "(" + xs.map(e_at).join(", ") + ")");
}

// Types (the generator's mirror of the object language)
// -----------------------------------------------------
// QT is a quantity term: a literal (&0/&1/&2), a bound quantity variable,
// or a meet. T is a synthesis goal. tvars appear only inside generic
// bodies and registry signatures; their kind is a QT. An ADT instance
// carries its quantity arguments (qs) beside its type arguments; the
// instance's own kind is the declared G with qs substituted in.

type QT = { k: "q"; q: 0 | 1 | 2 } | { k: "qv"; n: string } | { k: "qm"; a: QT; b: QT };

const Q0: QT = { k: "q", q: 0 };
const Q1: QT = { k: "q", q: 1 };
const Q2: QT = { k: "q", q: 2 };

function qt_str(q: QT): string {
  switch (q.k) {
    case "q": return "&" + String(q.q);
    case "qv": return q.n;
    case "qm": return "(" + qt_str(q.a) + " <&> " + qt_str(q.b) + ")";
  }
}

function qt_known(q: QT): 0 | 1 | 2 | null {
  switch (q.k) {
    case "q": return q.q;
    case "qv": return null;
    case "qm": {
      const a = qt_known(q.a);
      const b = qt_known(q.b);
      return a === null || b === null ? null : (Math.min(a, b) as 0 | 1 | 2);
    }
  }
}

function qt_eq(a: QT, b: QT): boolean {
  return qt_str(a) === qt_str(b);
}

function qt_sub(q: QT, m: Map<string, QT>): QT {
  switch (q.k) {
    case "q": return q;
    case "qv": return m.get(q.n) ?? q;
    case "qm": return { k: "qm", a: qt_sub(q.a, m), b: qt_sub(q.b, m) };
  }
}

// Sigil quantities on binders: 0 erased (-), 1 lone (bare), 2 many (+)
type BQ = 0 | 1 | 2;

function bq_prefix(q: BQ): string {
  return q === 0 ? "-" : q === 2 ? "+" : "";
}

type T =
  | { k: "u32" }
  | { k: "f32" }
  | { k: "nat" }
  | { k: "bool" }
  | { k: "cmp" }
  | { k: "char" }
  | { k: "str" }
  | { k: "unit" }
  | { k: "tvar"; n: string; q: QT }
  | { k: "adt"; a: Adt; qs: QT[]; args: T[]; iargs?: string[]; spell?: "or" | "bar" }
  | { k: "app"; f: Fam; arg: string }
  | { k: "empty" }
  | { k: "sig"; x: string; a: T; b: T; spell: "amp" | "exists" | "sigma" }
  | { k: "tup"; a: T; b: T; q: 1 | 2; spell?: "pair" }
  | { k: "fun"; q: BQ; dom: T; cod: T }
  | { k: "arr"; el: T }
  | { k: "io"; t: T }
  | { k: "map"; q: QT; v: T }
  | { k: "eql"; t: T; side: string; rhs?: string; spell?: "ne" }
  | { k: "set" };
// Propositions are types: Empty has no value, {a == b : T} has one when the
// sides agree, a dependent pair &x: A -> B holds a witness with evidence
// about it (Exists), a family may send an index to Empty or to an
// equality, and {a != b : T} is {a == b : T} -> Empty. Every one of them
// is drawn by syn_ty like any type (Empty and a clashing equality only
// where a type may be uninhabited: a family's arm, a pair's evidence),
// inhabited by syn ({==}, Unit{}, a witness, a refutation through a
// discriminating family), and read by rd (an empty match).

// Field / ctor / adt : q on a field is its sigil; a "self" field is the
// family at its own parameters. kind is the declared G (a QT over the
// adt's own quantity-parameter names); qps the quantity parameter names;
// tps the type parameters (name + declared kind over qps).
type Field = { q: BQ; t: T };
type Ctor = { name: string; fields: Field[] };
type Adt = {
  name: string;
  qps: string[];
  tps: Array<{ n: string; q: QT }>;
  kind: QT;
  ctors: Ctor[];
  rec: boolean;
  base?: boolean;
  // ips : erased index parameters (terms), the Word.Con<-p: Nat> shape; an
  // instance supplies iargs, and a field may mention a family at one
  ips?: IVar[];
};

// Families
// --------
// Types are terms: a family is a type-level def by match on one index,
// `def F(x: I) -> K:` with an arm per constructor of I (Nat, Bool or a
// minted enum). An arm is a type drawn like any other, in a scope where
// the arm's sub-index is a term the type may mention: through the family
// itself at the sub-index (F(p)), or through a datatype minted with that
// index as an erased parameter and holding F(p) in a field (Word's
// idiom). An applied family F(3n) is then a type like any other, at a
// field, a parameter, a list element, a return, and the productions that
// serve every type serve it: a closed index unfolds to its arm, a
// variable index goes through an index-generic def that matches on it
// (mk_fam: def mk(n: I) -> F(n), rd_fam: def rd(n: I, v: F(n)) -> U32),
// so Vec's fill and sum, and the dependent-type kit, emerge from the one
// generator.

type IVar = { n: string; t: T; sub?: boolean };
//   sub: the term is a family arm's sub-index (the one place an unfinished
//   family may be applied: the self-call must decrease)
type FamArm = { pat: string; sub: string | null; lit: string | null; ty: T; src?: string };
//   src: the name the sub-index binds under before its reusable re-bind
type Fam = { name: string; idx: T; kind: QT; arms: FamArm[]; done: boolean };
//   done: false while the arms are being drawn, when the family may be
//   applied only at its own sub-index (the self-call must decrease)

const U32C: T = { k: "u32" };
const F32C: T = { k: "f32" };
const NATC: T = { k: "nat" };
const BOOLC: T = { k: "bool" };
const CMPC: T = { k: "cmp" };
const CHARC: T = { k: "char" };
const STRC: T = { k: "str" };
const UNITC: T = { k: "unit" };
// Base's Set: a Data type with no constructor the generator sees, built and
// read only through Base's own Set.* calls
const SETC: T = { k: "set" };

// Base generic ADTs (base.bend shapes, quantity params included)
// --------------------------------------------------------------

function base_adts(): Record<string, Adt> {
  const tv = (n: string, q: QT): T => ({ k: "tvar", n, q });
  const qv = (n: string): QT => ({ k: "qv", n });
  const list: Adt = {
    name: "List", qps: ["a"], tps: [{ n: "A", q: qv("a") }], kind: qv("a"),
    ctors: [], rec: true, base: true,
  };
  list.ctors.push({ name: "Nil", fields: [] });
  list.ctors.push({
    name: "Con",
    fields: [{ q: 1, t: tv("A", qv("a")) }, { q: 1, t: { k: "adt", a: list, qs: [qv("a")], args: [tv("A", qv("a"))] } }],
  });
  const maybe: Adt = {
    name: "Maybe", qps: ["a"], tps: [{ n: "A", q: qv("a") }], kind: qv("a"),
    ctors: [
      { name: "None", fields: [] },
      { name: "Some", fields: [{ q: 1, t: tv("A", qv("a")) }] },
    ],
    rec: false, base: true,
  };
  const either: Adt = {
    name: "Either", qps: ["a", "b"], tps: [{ n: "A", q: qv("a") }, { n: "B", q: qv("b") }],
    kind: { k: "qm", a: qv("a"), b: qv("b") },
    ctors: [
      { name: "Inl", fields: [{ q: 1, t: tv("A", qv("a")) }] },
      { name: "Inr", fields: [{ q: 1, t: tv("B", qv("b")) }] },
    ],
    rec: false, base: true,
  };
  const result: Adt = {
    name: "Result", qps: ["a", "b"], tps: [{ n: "E", q: qv("a") }, { n: "A", q: qv("b") }],
    kind: { k: "qm", a: qv("a"), b: qv("b") },
    ctors: [
      { name: "Fail", fields: [{ q: 1, t: tv("E", qv("a")) }] },
      { name: "Done", fields: [{ q: 1, t: tv("A", qv("b")) }] },
    ],
    rec: false, base: true,
  };
  return { List: list, Maybe: maybe, Either: either, Result: result };
}

const BASE = base_adts();

function t_list(q: QT, el: T): T {
  return { k: "adt", a: BASE.List, qs: [q], args: [el] };
}

function t_maybe(q: QT, el: T): T {
  return { k: "adt", a: BASE.Maybe, qs: [q], args: [el] };
}

// Ty
// --

// ty_str is the SAFE rendering: it never leads with '+' (a '+'-headed
// type after '(' or '&' would parse as a binder), so the Plus sugar lives
// only in ty_top, used at annotation sites (right after ':'), the one
// position the sugar is lawful everywhere.
function ty_str(t: T): string {
  switch (t.k) {
    case "u32": return "U32";
    case "f32": return "F32";
    case "nat": return "Nat";
    case "bool": return "Bool";
    case "cmp": return "Cmp";
    case "char": return "Char";
    case "str": return "String";
    case "unit": return "Unit";
    case "set": return "Set()";
    case "tvar": return t.n;
    case "adt": {
      const iargs = t.iargs ?? [];
      if (t.spell === "or") {
        return "Or(" + t.args.map(ty_grp).join(", ") + ")";
      }
      if (t.spell === "bar") {
        return t.args.map(ty_grp).join(" | ");
      }
      if (t.qs.length + t.args.length + iargs.length === 0) {
        return t.a.name;
      }
      // the Fill sugar (all &1) drops the quantity block and stays safe
      const all1 = t.qs.length > 0 && t.qs.every((q) => q.k === "q" && q.q === 1);
      if (all1 && t.args.length > 0) {
        return t.a.name + "<" + t.args.map(ty_grp).concat(iargs).join(", ") + ">";
      }
      return t.a.name + "<" + t.qs.map(qt_str).concat(t.args.map(ty_grp), iargs).join(", ") + ">";
    }
    case "app": return t.f.name + "(" + t.arg + ")";
    case "empty": return "Empty";
    case "sig": return t.spell === "amp" ? "&" + t.x + ": " + ty_grp(t.a) + " -> " + ty_str(t.b)
      : t.spell === "exists" ? "Exists(" + ty_grp(t.a) + ", " + t.x + " => " + ty_str(t.b) + ")"
      : "Sigma<&1, &1, " + ty_grp(t.a) + ", " + t.x + " => " + ty_str(t.b) + ">";
    case "tup": {
      if (t.q === 2) {
        return "Sigma<&2, &2, " + ty_grp(t.a) + ", _ => " + ty_str(t.b) + ">";
      }
      if (t.spell === "pair") {
        return "Pair(" + ty_grp(t.a) + ", " + ty_grp(t.b) + ")";
      }
      return ty_grp(t.a) + " & " + ty_grp(t.b);
    }
    case "fun": {
      const dom = t.q === 1 ? ty_grp(t.dom) : "@" + bq_prefix(t.q) + "zq: " + ty_grp(t.dom) + " ->";
      if (t.q === 1) {
        return dom + " -> " + ty_str(t.cod);
      }
      return dom + " " + ty_str(t.cod);
    }
    case "arr": return "Array<" + ty_grp(t.el) + ">";
    case "io": return "IO(" + ty_str(t.t) + ")";
    case "map": return "Map<" + qt_str(t.q) + ", " + ty_grp(t.v) + ">";
    case "eql": return "{" + t.side + (t.spell === "ne" ? " != " : " == ") + (t.rhs ?? t.side) + " : " + ty_str(t.t) + "}";
  }
}

// ty_top : the annotation-site rendering — Plus sugar (all-&2 quantity
// blocks dropped behind a leading '+') fires here and only here
function ty_top(t: T): string {
  if (t.k === "adt" && t.qs.length > 0 && t.qs.every((q) => q.k === "q" && q.q === 2)) {
    const rest = t.args.map(ty_grp).concat(t.iargs ?? []);
    return "+" + t.a.name + (rest.length > 0 ? "<" + rest.join(", ") + ">" : "");
  }
  if (t.k === "tup" && t.q === 2) {
    return "+Sigma<" + ty_grp(t.a) + ", _ => " + ty_str(t.b) + ">";
  }
  // a bare &x: A -> B heads a binder at a law row or a claim
  return t.k === "sig" && t.spell === "amp" ? "(" + ty_str(t) + ")" : ty_str(t);
}

// ty_grp : parenthesize where juxtaposition would mis-parse: arrow domains,
// tuple components inside other types, and type arguments (a FIRST argument
// after `<` commits on one token; parens are harmless on the rest)
function ty_grp(t: T): string {
  return t.k === "fun" || (t.k === "tup" && t.q === 1 && t.spell === undefined) || (t.k === "sig" && t.spell === "amp") || (t.k === "adt" && t.spell === "bar")
    ? "(" + ty_str(t) + ")" : ty_str(t);
}

function ty_eq(a: T, b: T): boolean {
  return ty_str(a) === ty_str(b);
}

// ty_quant : the type's kind quantity (a QT — may be open)
function ty_quant(t: T): QT {
  switch (t.k) {
    case "u32": case "f32": case "nat": case "bool": case "cmp":
    case "char": case "str": case "unit": case "eql": case "set":
      return Q2;
    case "tvar": return t.q;
    case "adt": {
      const m = new Map<string, QT>(t.a.qps.map((n, i) => [n, t.qs[i]]));
      return qt_sub(t.a.kind, m);
    }
    case "tup": return t.q === 2 ? Q2 : Q1;
    case "fun": return Q1;
    case "arr": return Q1;
    case "io": return Q1;
    case "map": return t.q;
    case "app": return t.f.kind;
    case "empty": return Q2;
    case "sig": return Q1;
  }
}

// ty_data : may this type sit under a + binder (concretely Data)?
function ty_data(t: T): boolean {
  return qt_known(ty_quant(t)) === 2;
}

// qt_fits : is a type of kind quantity `have` accepted where Kind(`need`)
// is demanded? Mirrors term_compare's Typ case: Data (&2) fits every
// kind, every kind fits Kind(&0) and Kind(&1) (a non-Many literal target
// accepts everything), a meet on the left needs both sides, a meet on
// the right accepts either side, and a stuck target licenses only an
// identical term. Conservative where the checker would have to reduce.
function qt_fits(have: QT, need: QT): boolean {
  if (qt_known(have) === 2) {
    return true;
  }
  const n = qt_known(need);
  if (need.k === "q" && (n === 0 || n === 1)) {
    return true;
  }
  if (qt_eq(have, need)) {
    return true;
  }
  if (have.k === "qm") {
    return qt_fits(have.a, need) && qt_fits(have.b, need);
  }
  if (need.k === "qm") {
    return qt_fits(have, need.a) || qt_fits(have, need.b);
  }
  return false;
}

function ty_sub(t: T, m: Map<string, T>, qm: Map<string, QT>): T {
  switch (t.k) {
    case "tvar": {
      const got = m.get(t.n);
      if (got !== undefined) {
        return got;
      }
      return { k: "tvar", n: t.n, q: qt_sub(t.q, qm) };
    }
    case "adt": return { k: "adt", a: t.a, qs: t.qs.map((q) => qt_sub(q, qm)), args: t.args.map((x) => ty_sub(x, m, qm)), iargs: t.iargs, spell: t.spell };
    case "sig": return { k: "sig", x: t.x, a: ty_sub(t.a, m, qm), b: ty_sub(t.b, m, qm), spell: t.spell };
    case "tup": return { k: "tup", a: ty_sub(t.a, m, qm), b: ty_sub(t.b, m, qm), q: t.q, spell: t.spell };
    case "fun": return { k: "fun", q: t.q, dom: ty_sub(t.dom, m, qm), cod: ty_sub(t.cod, m, qm) };
    case "arr": return { k: "arr", el: ty_sub(t.el, m, qm) };
    case "io": return { k: "io", t: ty_sub(t.t, m, qm) };
    case "map": return { k: "map", q: qt_sub(t.q, qm), v: ty_sub(t.v, m, qm) };
    default: return t;
  }
}

// ty_tsub : the type with the index term `n` replaced by `e` (an arm's
// sub-index at a closed literal, a datatype's index parameter at its arg)
function ty_tsub(t: T, n: string, e: string): T {
  switch (t.k) {
    case "app": return t.arg === n ? { k: "app", f: t.f, arg: e } : t;
    case "adt": return { k: "adt", a: t.a, qs: t.qs, args: t.args.map((x) => ty_tsub(x, n, e)), iargs: (t.iargs ?? []).map((x) => x === n ? e : x), spell: t.spell };
    case "tup": return { k: "tup", a: ty_tsub(t.a, n, e), b: ty_tsub(t.b, n, e), q: t.q, spell: t.spell };
    case "sig": return t.x === n ? t : { k: "sig", x: t.x, a: ty_tsub(t.a, n, e), b: ty_tsub(t.b, n, e), spell: t.spell };
    case "fun": return { k: "fun", q: t.q, dom: ty_tsub(t.dom, n, e), cod: ty_tsub(t.cod, n, e) };
    case "arr": return { k: "arr", el: ty_tsub(t.el, n, e) };
    case "io": return { k: "io", t: ty_tsub(t.t, n, e) };
    case "map": return { k: "map", q: t.q, v: ty_tsub(t.v, n, e) };
    default: return t;
  }
}

// ty_open : does the type mention an abstract type or quantity variable?
function ty_open(t: T): boolean {
  switch (t.k) {
    case "tvar": return true;
    case "app": return !idx_is_lit(t.f.idx, t.arg);
    // the pair binds its witness: the evidence is closed once it is a term
    case "sig": return ty_open(t.a) || ty_open(idx_type(t.a) ? ty_tsub(t.b, t.x, idx_first(t.a)) : t.b);
    case "adt": return t.args.some(ty_open) || t.qs.some((q) => qt_known(q) === null)
      || (t.iargs ?? []).some((x, i) => !idx_is_lit((t.a.ips as IVar[])[i].t, x));
    case "tup": return ty_open(t.a) || ty_open(t.b);
    case "fun": return ty_open(t.dom) || ty_open(t.cod);
    case "arr": return ty_open(t.el);
    case "io": return ty_open(t.t);
    case "map": return qt_known(t.q) === null || ty_open(t.v);
    default: return false;
  }
}

// A term binder may occur in the index of another live value's type. Such a
// binder cannot be shadowed while that value remains in scope: the printed
// type would resolve the index to the new binder instead.
function ty_term_mentions(t: T, name: string): boolean {
  switch (t.k) {
    case "app": return t.arg === name;
    case "adt": return t.args.some((arg) => ty_term_mentions(arg, name)) || (t.iargs ?? []).includes(name);
    case "sig": return ty_term_mentions(t.a, name) || (t.x !== name && ty_term_mentions(t.b, name));
    case "tup": return ty_term_mentions(t.a, name) || ty_term_mentions(t.b, name);
    case "fun": return ty_term_mentions(t.dom, name) || ty_term_mentions(t.cod, name);
    case "arr": return ty_term_mentions(t.el, name);
    case "io": return ty_term_mentions(t.t, name);
    case "map": return ty_term_mentions(t.v, name);
    case "eql": return ty_term_mentions(t.t, name) || t.side === name || t.rhs === name;
    default: return false;
  }
}

// ty_unify : bind pat's tvars/qvars so pat matches goal (registry calls)
function ty_unify(pat: T, goal: T, m: Map<string, T>, qm: Map<string, QT>): boolean {
  if (pat.k === "tvar") {
    const got = m.get(pat.n);
    if (got !== undefined) {
      return ty_eq(got, goal);
    }
    // the bound type must fit the tvar's declared kind
    if (!qt_fits(ty_quant(goal), qt_sub(pat.q, qm))) {
      return false;
    }
    m.set(pat.n, goal);
    return true;
  }
  if (pat.k !== goal.k) {
    return false;
  }
  if (pat.k === "app" && goal.k === "app") {
    return pat.f === goal.f && pat.arg === goal.arg;
  }
  if (pat.k === "sig" && goal.k === "sig") {
    return ty_unify(pat.a, goal.a, m, qm) && ty_unify(ty_tsub(pat.b, pat.x, goal.x), goal.b, m, qm);
  }
  if (pat.k === "adt" && goal.k === "adt") {
    if (pat.a !== goal.a || (pat.iargs ?? []).join(",") !== (goal.iargs ?? []).join(",")) {
      return false;
    }
    for (let i = 0; i < pat.qs.length; i++) {
      if (!qt_unify(pat.qs[i], goal.qs[i], qm)) {
        return false;
      }
    }
    return pat.args.every((x, i) => ty_unify(x, goal.args[i], m, qm));
  }
  if (pat.k === "tup" && goal.k === "tup") {
    return pat.q === goal.q && ty_unify(pat.a, goal.a, m, qm) && ty_unify(pat.b, goal.b, m, qm);
  }
  if (pat.k === "fun" && goal.k === "fun") {
    return pat.q === goal.q && ty_unify(pat.dom, goal.dom, m, qm) && ty_unify(pat.cod, goal.cod, m, qm);
  }
  if (pat.k === "map" && goal.k === "map") {
    return qt_unify(pat.q, goal.q, qm) && ty_unify(pat.v, goal.v, m, qm);
  }
  if (pat.k === "arr" && goal.k === "arr") {
    return ty_unify(pat.el, goal.el, m, qm);
  }
  if (pat.k === "io" && goal.k === "io") {
    return ty_unify(pat.t, goal.t, m, qm);
  }
  if (pat.k === "eql") {
    return false;
  }
  return true;
}

function qt_unify(pat: QT, goal: QT, qm: Map<string, QT>): boolean {
  if (pat.k === "qv") {
    const got = qm.get(pat.n);
    if (got !== undefined) {
      return qt_eq(got, goal);
    }
    qm.set(pat.n, goal);
    return true;
  }
  return qt_eq(qt_sub(pat, qm), goal);
}

// Ctx
// ---
// One program's generator state. State is what the program accumulates:
// entries (ordered top-level types + defs — order IS dependency order,
// the book refuses forward references, so everything minted on demand
// lands before its first caller), the adt list, the callable registry,
// the memo of minted helpers/readers/builders/transforms, the uid
// counter. A Ctx is that shared state plus one RNG stream; sub(label)
// hands out a child Ctx on a split stream, indexed per label within
// the parent, so sibling lines and minted defs draw independently.

// DefR : the callable registry. Call spelling:
//   name(<quantity args>, <type args>, <value args>)
// mask caps a value argument with `% mask` at call sites (loop fuels).
type DefR = {
  name: string;
  qps: string[];
  tps: Array<{ n: string; q: QT }>;
  // a parameter's type may name an earlier parameter (n) of an index type
  // (dep: the parameter may be depended on)
  ps: Array<{ q: BQ; t: T; n?: string; dep?: boolean }>;
  ret: T;
  mask?: Array<number | null>;
  // tm : the leading template parameters (written ~x, their arguments
  // closed); base : read off Base's own signatures
  tm?: number;
  base?: boolean;
  // hdr : the quantity and type parameters in the telescope's own order,
  // when they interleave (List.zip's a, A, b, B)
  hdr?: string[];
  // wip: the def's own leaves are being drawn; a self-call passes one of
  // the current sub-fields at the decreasing column (col), each once
  wip?: { col: number; ps: V[]; subs: V[]; calls: number };
};

type State = {
  uid: number;
  base: boolean;
  freeNames: boolean;
  names: Set<string>;
  decls: Set<string>;
  entries: string[];
  adts: Adt[];
  fams: Fam[];
  defr: DefR[];
  memo: Map<string, string>;
  wip: Set<string>;
  // wips: the defs under construction, innermost last
  wips: DefR[];
  mints: number;
  feat: Record<string, number>;
  // pure : true while generating the interp-visible side — no F32
  // computation may flow into the fold (base's F32 ops are stuck in the
  // interpreter: native claims with no body)
  pure: boolean;
  // trans : set when a member computes a float transcendental — JS-vs-C
  // on the extra line downgrades to a counted skip for that member
  trans: boolean;
  // surface : the chance per synthesis node of a surface wrapper
  surface: number;
  // tmpl : drawing a template's argument, which its instance substitutes
  // where it may head an application (a head must infer: no rewrite form)
  tmpl: boolean;
};

class Ctx {
  private counts = new Map<string, number>();
  constructor(readonly s: State, readonly g: Gen) {}
  sub(label: string): Ctx {
    const i = this.counts.get(label) ?? 0;
    this.counts.set(label, i + 1);
    return new Ctx(this.s, this.g.split(label, i));
  }
  uid(): number {
    return this.s.uid++;
  }
  push(text: string): void {
    this.s.entries.push(text);
    for (const name of text_names(text)) {
      this.s.names.add(name);
      this.s.decls.add(name);
    }
  }
  feat(k: string): void {
    this.s.feat[k] = (this.s.feat[k] ?? 0) + 1;
  }
  get entries(): string[] {
    return this.s.entries;
  }
  get base(): boolean {
    return this.s.base;
  }
  get freeNames(): boolean {
    return this.s.freeNames;
  }
  get names(): Set<string> {
    return this.s.names;
  }
  get decls(): Set<string> {
    return this.s.decls;
  }
  get adts(): Adt[] {
    return this.s.adts;
  }
  get fams(): Fam[] {
    return this.s.fams;
  }
  get defr(): DefR[] {
    return this.s.defr;
  }
  get memo(): Map<string, string> {
    return this.s.memo;
  }
  get wip(): Set<string> {
    return this.s.wip;
  }
  get mints(): number {
    return this.s.mints;
  }
  set mints(n: number) {
    this.s.mints = n;
  }
  get pure(): boolean {
    return this.s.pure;
  }
  set pure(b: boolean) {
    this.s.pure = b;
  }
  get trans(): boolean {
    return this.s.trans;
  }
  set trans(b: boolean) {
    this.s.trans = b;
  }
}

function ctx_new(seed: bigint, uid0: number, base: boolean, freeNames: boolean, surface: number): Ctx {
  const names = new Set(base ? BASE_NAMES : CORE_NAMES);
  const decls = new Set(base ? BASE_DECL_NAMES : []);
  return new Ctx({ uid: uid0, base, freeNames, names, decls, entries: [], adts: [], fams: [], defr: base ? BASE_DEFR.slice() : [],
    memo: new Map(), wip: new Set(), wips: [], mints: 0, feat: {}, pure: true, trans: false, surface, tmpl: false }, new Gen(rng_mix64(seed)));
}

// Base's signatures
// -----------------
// Base's public defs (Family.fn) join the call registry, read off the checked
// Base book: a quantity binder is a quantity parameter, an erased type binder
// a type parameter, the rest value parameters, the first x of them templates
// (written ~). A def enters when every type in its telescope has a spelling in
// T; effects (IO) and dependent types have none and stay out. The numeric
// families keep their hand-weighted rosters (num_gen_*): a U32 or Nat call at
// an arbitrary argument can unfold a unary Nat the interpreter never
// finishes. A Nat argument is masked small (base loops over it).

const BASE_DEFR: DefR[] = [];

async function base_registry_load(): Promise<void> {
  const bend = await import(pathToFileURL(BEND_TS).href);
  const book = bend.book_nil();
  await bend.book_load(book, fs.realpathSync(path.join(ROOT, "bend2", "base.bend")), "", new Map());
  bend.book_valid(book);
  type L = { $: string; [k: string]: any };
  type B = { n: string; kind: "q" | "t" | "v"; q?: QT };
  const q_of = (t: L, env: B[]): QT | null => {
    switch (t.$) {
      case "Qua": return t.q.$ === "None" ? Q0 : t.q.$ === "Lone" ? Q1 : Q2;
      case "Var": return env[t.i]?.kind === "q" ? { k: "qv", n: env[t.i].n } : null;
      case "Min": {
        const a = q_of(t.a, env);
        const b = q_of(t.b, env);
        return a === null || b === null ? null : { k: "qm", a, b };
      }
      default: return null;
    }
  };
  const ty_of = (t: L, env: B[]): T | null => {
    switch (t.$) {
      case "Ref": return ({ U32: U32C, F32: F32C, Nat: NATC, Bool: BOOLC, Cmp: CMPC, Char: CHARC, String: STRC, Unit: UNITC, Empty: { k: "empty" }, Set: SETC } as Record<string, T>)[t.k] ?? null;
      case "Var": return env[t.i]?.kind === "t" ? { k: "tvar", n: env[t.i].n, q: env[t.i].q as QT } : null;
      case "App": {
        if (t.f.$ === "App" && t.f.f.$ === "Ref" && t.f.f.k === "Pair") {
          const a = ty_of(t.f.x, env);
          const b = ty_of(t.x, env);
          return a === null || b === null ? null : { k: "tup", a, b, q: 1 };
        }
        return null;
      }
      case "ADT": {
        if (t.k === "Array") {
          const el = ty_of(t.x[0], env);
          return el === null ? null : { k: "arr", el };
        }
        if (t.k === "Map") {
          const q = q_of(t.x[0], env);
          const v = ty_of(t.x[1], env);
          return q === null || v === null ? null : { k: "map", q, v };
        }
        const a = BASE[t.k];
        if (a === undefined) {
          return null;
        }
        const qs = t.x.slice(0, a.qps.length).map((x: L) => q_of(x, env));
        const args = t.x.slice(a.qps.length).map((x: L) => ty_of(x, env));
        return qs.includes(null) || args.includes(null) ? null : { k: "adt", a, qs, args };
      }
      case "All": {
        const dom = ty_of(t.A, env);
        const cod = ty_of(t.B, [...env, { n: t.k, kind: "v" }]);
        const q: BQ = t.q.$ === "None" ? 0 : t.q.$ === "Lone" ? 1 : 2;
        return dom === null || cod === null ? null : { k: "fun", q, dom, cod };
      }
      default: return null;
    }
  };
  for (const name of Object.keys(book.tlds)) {
    const d = book.tlds[name];
    const fam = name.split(".");
    if (d.$ !== "Def" || fam.length !== 2 || ["U32", "F32", "Nat"].includes(fam[0])) {
      continue;
    }
    const env: B[] = [];
    const r: DefR = { name, qps: [], tps: [], ps: [], ret: UNITC, tm: d.x ?? 0, base: true, mask: [], hdr: [] };
    let t: L = bend.term_lower(d.T);
    let ok = true;
    for (; ok && t.$ === "All"; t = t.B) {
      if (t.A.$ === "Qnt" || t.A.$ === "Typ") {
        // a quantity or type parameter after a value one has no spelling in
        // the registry's call order
        const q = t.A.$ === "Typ" ? q_of(t.A.g, env) : Q0;
        ok = r.ps.length === 0 && q !== null;
        env.push({ n: t.k, kind: t.A.$ === "Qnt" ? "q" : "t", q: q ?? Q0 });
        (r.hdr as string[]).push(t.k);
        (t.A.$ === "Qnt" ? r.qps : r.tps as unknown[]).push(t.A.$ === "Qnt" ? t.k : { n: t.k, q });
        continue;
      }
      const pt = ty_of(t.A, env);
      ok = pt !== null;
      r.ps.push({ q: t.q.$ === "None" ? 0 : t.q.$ === "Lone" ? 1 : 2, t: pt ?? UNITC });
      (r.mask as Array<number | null>).push(pt?.k === "nat" ? 8 : null);
      env.push({ n: t.k, kind: "v" });
    }
    const ret = ok ? ty_of(t, env) : null;
    if (ret !== null) {
      r.ret = ret;
      BASE_DEFR.push(r);
    }
  }
}

// Size
// ----
// EVERY structural size draws from one distribution: the site's small BODY
// carries ~.997 of the mass and a log-uniform tail to the site's cap
// carries the rest, so big shapes EMERGE without sinking throughput. Caps
// respect the interpreter: it runs base's Word chains, ~1000x slower per
// U32 op than the backends, so interp-side caps are small and the heavy
// tails live on the compiled-only side.

function size_pick(c: Ctx, body: number, cap: number): number {
  const lo = Math.max(1, body);
  if (cap > lo && c.g.chance(0.003)) {
    c.feat("stretch");
    return Math.floor(lo * Math.pow(cap / lo, c.g.int(1024) / 1024));
  }
  return body;
}

// Env
// ---
// q "lone": consumed at most once (env_take flips to dead); "many": free
// (a + binder — only concretely-Data types); "dead": gone. Dropping a
// lone binder is fine (the system is affine).

// dec: a sub-field the self-call may descend on; of: the parameter a
// variable row re-binds (passed through unchanged, it still counts as it)
type V = { name: string; ty: T; q: "lone" | "many" | "dead"; dec?: boolean; of?: V };

function v_new(name: string, ty: T, many = false): V {
  return { name, ty, q: many && ty_data(ty) ? "many" : "lone" };
}

function env_take(v: V): string {
  if (v.q === "lone") {
    v.q = "dead";
  }
  return v.name;
}

function env_of(env: V[], pred: (t: T) => boolean): V[] {
  return env.filter((v) => v.q !== "dead" && pred(v.ty));
}

function env_nums(env: V[]): V[] {
  return env_of(env, (t) => t.k === "u32");
}

// text_names : the top-level names a source text declares (defs, laws,
// types and their constructors), with every dotted prefix, since a binder
// of that name would shadow them
function text_names(text: string): string[] {
  const out: string[] = [];
  for (const m of text.matchAll(/^(?:def|law|type)\s+([A-Za-z_][\w.]*)|^\s+([A-Za-z_][\w.]*)\{/gm)) {
    const parts = (m[1] ?? m[2]).split(".");
    for (let i = 1; i <= parts.length; i++) {
      out.push(parts.slice(0, i).join("."));
    }
  }
  return out;
}

const KEYWORDS = ["def", "type", "law", "match", "case", "do", "return", "for", "exs", "where", "is", "import", "Type", "Data", "Kind", "Quant"];
const BASE_SOURCE = fs.readFileSync(path.join(ROOT, "bend2", "base.bend"), "utf8");
const BASE_DECL_NAMES = text_names(BASE_SOURCE);
const CORE_NAMES = new Set([...KEYWORDS, "_", "main"]);
const BASE_NAMES = new Set([...CORE_NAMES, ...BASE_DECL_NAMES]);
// the shape of every name the generator mints at top level (a stem, a uid,
// a constructor's letter), in any member of a batch
const MINTED = /^[A-Za-z]+\d+[a-z]?$/;
const NAME_HEAD = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_";
const NAME_BODY = NAME_HEAD + "0123456789";

// General identifier vocabulary: every source identifier in the language,
// compiler and Base, plus every reflected property of the JS host prototypes.
// Camel/snake/digit boundaries are split before sampling, so no complete Base
// or known-problem spelling is privileged; names emerge by recombination.
const NAME_TEXT = [
  BASE_SOURCE,
  fs.readFileSync(path.join(ROOT, "bend2", "bend.ts"), "utf8"),
  fs.readFileSync(path.join(ROOT, "bend2", "comp.ts"), "utf8"),
].join("\n");
const HOST_NAMES = [Object.prototype, Function.prototype, Array.prototype, Number.prototype, String.prototype]
  .flatMap((obj) => Object.getOwnPropertyNames(obj));
const NAME_WORDS = [...new Set([
  ...NAME_TEXT.matchAll(/[A-Za-z_][A-Za-z_0-9]*/g),
].map((m) => m[0]).concat(HOST_NAMES))]
  .filter((name) => /^[A-Za-z_][A-Za-z_0-9]*$/.test(name) && !KEYWORDS.includes(name));
const DECL_WORDS = [...new Set([...NAME_WORDS, ...BASE_DECL_NAMES])];
const DECL_SET = new Set(DECL_WORDS);
const NAME_FRAGMENTS = [...new Set([
  ...NAME_TEXT.matchAll(/[A-Za-z_][A-Za-z_0-9]*/g),
].map((m) => m[0]).concat(HOST_NAMES).flatMap((name) => name
  .replace(/([a-z0-9])([A-Z])/g, "$1 $2")
  .replace(/([A-Z]+)([A-Z][a-z])/g, "$1 $2")
  .split(/[^A-Za-z]+/)
  .filter((part) => part.length > 0)
  .map((part) => part.toLowerCase())))]
  .filter((part) => part.length <= 24 && !KEYWORDS.includes(part));

function identifier(c: Ctx, allowOne = true): string {
  const shape = c.g.int(100);
  if (shape < 42) {
    const minimum = allowOne ? 1 : 2;
    const length = shape < 2 ? 33 + c.g.int(224) : Math.min(32, minimum - 1 + c.g.decay(0.72));
    return c.g.pick(NAME_HEAD.split(""))
      + Array.from({ length: length - 1 }, () => c.g.pick(NAME_BODY.split(""))).join("");
  }
  if (shape < 67) {
    let name = c.g.pick(NAME_WORDS);
    if (c.g.chance(0.18)) name = c.g.pick([name.toLowerCase(), name.toUpperCase(), "_" + name, name + "_", name + String(c.g.int(100))]);
    if (!allowOne && name.length === 1) name += c.g.pick(NAME_BODY.split(""));
    return name;
  }
  if (shape < 90) {
    const parts = Array.from({ length: 1 + c.g.int(3) }, () => c.g.pick(NAME_FRAGMENTS));
    const style = c.g.int(5);
    let name = style === 0 ? parts.join("")
      : style === 1 ? parts[0] + parts.slice(1).map((p) => p[0].toUpperCase() + p.slice(1)).join("")
      : style === 2 ? parts.map((p) => p[0].toUpperCase() + p.slice(1)).join("")
      : style === 3 ? parts.join("_")
      : parts.join("_").toUpperCase();
    if (c.g.chance(0.18)) name = "_".repeat(1 + c.g.int(2)) + name;
    if (c.g.chance(0.12)) name += "_".repeat(1 + c.g.int(2));
    if (c.g.chance(0.22)) name += String(c.g.int(100));
    if (!allowOne && name.length === 1) name += c.g.pick(NAME_BODY.split(""));
    return name;
  }
  const length = c.g.pick([2, 8, 16, 31, 32, 63, 64, 80, 127, 128, 255]);
  const char = c.g.pick(NAME_HEAD.split(""));
  return char + c.g.pick([char, "_", c.g.pick(NAME_BODY.split(""))]).repeat(length - 1);
}

// Every generated top-level role uses this allocator. Most batched books keep
// a uid suffix so independently generated members cannot collide. A random
// subset runs alone and draws unrestricted names from the same identifier
// distribution used by binders; Base only changes which names are occupied.
function decl_name(c: Ctx, hint: string): string {
  for (;;) {
    let name = c.freeNames ? identifier(c, false) : hint + String(c.uid());
    if (c.freeNames && c.g.chance(0.18)) {
      const words = DECL_WORDS.filter((word) => word.length > 1 && (!word.includes(".") || c.names.has(word.slice(0, word.indexOf(".")))));
      name = c.g.pick(words);
    }
    if (c.freeNames && c.g.chance(0.08)) {
      const prefixes = [...c.names].filter((part) => /^[A-Za-z_][A-Za-z_0-9]*$/.test(part) && !CORE_NAMES.has(part));
      if (prefixes.length > 0) name = c.g.pick(prefixes) + "." + identifier(c, false);
    }
    if (c.freeNames && c.decls.size > 0 && c.g.chance(0.18)) {
      const parts = c.g.pick([...c.decls]).split(".");
      const leaf = parts.pop() as string;
      const affix = identifier(c, false);
      parts.push(c.g.chance(0.5) ? affix + leaf : leaf + affix);
      name = parts.join(".");
      c.feat("name-affix");
    }
    // the shape of the generator's own uid names (a stem, a uid, a letter)
    // is theirs, unless the word is one the implementation spells
    const minted = c.freeNames && MINTED.test(name.slice(name.lastIndexOf(".") + 1)) && !DECL_SET.has(name);
    if (!minted && !c.names.has(name) && !KEYWORDS.includes(name) && name !== "_") {
      c.names.add(name);
      c.decls.add(name);
      if (c.freeNames) c.feat("free-name");
      return name;
    }
  }
}

// A value binder's name: any name the parser takes as a binder that names
// nothing else (not `_`, a keyword, an occupied initial name, nor of the shape of a
// minted top-level name, which another member of a batch may hold), or a
// fifth of the time the name of a binder in scope, which the new one then
// shadows. `taken` holds the names bound beside it (one line's binders
// are distinct).
function bind_name(c: Ctx, env: V[], taken: string[] = []): string {
  const scoped = env.filter((v) => v.q !== "dead");
  const protectedNames = new Set(scoped.filter((candidate) =>
    scoped.some((value) => value !== candidate && ty_term_mentions(value.ty, candidate.name))).map((v) => v.name));
  const live = scoped.filter((v) => !taken.includes(v.name) && !protectedNames.has(v.name));
  if (live.length > 0 && c.g.chance(0.2)) {
    c.feat("shadow");
    const name = c.g.pick(live).name;
    c.names.add(name);
    return name;
  }
  for (;;) {
    const name = identifier(c);
    if (!c.names.has(name) && !MINTED.test(name) && !taken.includes(name) && !protectedNames.has(name)) {
      c.feat("generated-name");
      c.names.add(name);
      return name;
    }
  }
}

// env_bind : the scope under new binders; a binder in scope with the same
// name is shadowed, so it is dead there (an erased binder shadows too)
function env_bind(env: V[], names: string[], vs: V[] = []): V[] {
  return env.map((v) => names.includes(v.name) ? { ...v, q: "dead" as const } : v).concat(vs);
}

// bind_keep : a fold bind is consumed once BY the fold; only a + binder
// may also stay in the environment for later lines. One coin owns that
// choice everywhere (parallel-let binders take no sigil, so fork results
// are always fold-only).
function bind_keep(c: Ctx): boolean {
  return c.g.chance(0.55);
}

// Helpers (memoized single-mint readers)
// --------------------------------------
// helper(c, key, stem, body): mint the def once per program; body sees the
// fresh name and may mint what it depends on first.

function helper(c: Ctx, key: string, stem: string, body: (c: Ctx, name: string) => string): string {
  const got = c.memo.get(key);
  if (got !== undefined) {
    return got;
  }
  const name = decl_name(c, stem);
  c.memo.set(key, name);
  c.push(body(c.sub("helper"), name));
  return name;
}

// helper_bool : Bool -> U32 (0/1) — the bridge every comparison fold rides
function helper_bool(c: Ctx): string {
  return helper(c, "bool", "bu", (c, n) => {
    const b = bind_name(c, []);
    return "def " + n + "(" + b + ": Bool) -> U32:\n  match " + b + ":\n    case False{}:\n      0\n    case True{}:\n      1";
  });
}

function helper_cmp(c: Ctx): string {
  return helper(c, "cmp", "cu", (c, n) => {
    const x = bind_name(c, []);
    return "def " + n + "(" + x + ": Cmp) -> U32:\n  match " + x + ":\n    case LT{}:\n      " + String(c.g.int(64))
      + "\n    case EQ{}:\n      " + String(64 + c.g.int(64)) + "\n    case GT{}:\n      " + String(128 + c.g.int(64));
  });
}

function helper_chr(c: Ctx): string {
  return helper(c, "chr", "ch", (c, n) => {
    const x = bind_name(c, []);
    const code = bind_name(c, [], [x]);
    return "def " + n + "(" + x + ": Char) -> U32:\n  Chr{" + code + "} = " + x + "\n  " + code;
  });
}

// helper_strlen : String -> U32 with a rolling code hash (exercises SCon
// elimination and Char packing)
function helper_strlen(c: Ctx): string {
  return helper(c, "strlen", "sl", (c, n) => {
    const s = bind_name(c, []);
    const acc = bind_name(c, [], [s]);
    const h = bind_name(c, [], [s, acc]);
    const t = bind_name(c, [], [s, acc, h]);
    return "def " + n + "(" + s + ": String, +" + acc + ": U32) -> U32:\n  match " + s
      + ":\n    case SNil{}:\n      " + acc + "\n    case SCon{" + h + ", " + t + "}:\n      "
      + n + "(" + t + ", (" + acc + " * 31 + " + helper_chr(c) + "(" + h + ") : U32))";
  });
}

// Num
// ---

function num_lit_u32(c: Ctx): E {
  return e_atom(String(c.g.wpick<() => string>([
    [30, () => String(c.g.int(16))],
    [25, () => String(c.g.int(1000))],
    [15, () => String(c.g.int(4294967296))],
    [10, () => "4294967295"],
    [10, () => "2147483648"],
    [5, () => "65536"],
    [5, () => "0"],
  ])()));
}

const U32_OPS: Array<[number, string]> = [
  [22, "+"], [16, "-"], [14, "*"], [7, "/"], [7, "%"],
  [6, ".^."], [5, ".&."], [5, ".|."],
];

function num_gen_u32(c: Ctx, env: V[], fuel: number): E {
  const vars = env_nums(env);
  if (fuel <= 0) {
    return vars.length > 0 && c.g.chance(0.55) ? e_atom(env_take(c.g.pick(vars))) : num_lit_u32(c);
  }
  return c.g.wpick<() => E>([
    [15, () => num_lit_u32(c)],
    [vars.length > 0 ? 22 : 0, () => e_atom(env_take(c.g.pick(vars)))],
    [30, () => {
      const op = c.g.wpick(U32_OPS);
      return e_bin(num_gen_u32(c, env, fuel - 1), op, num_gen_u32(c, env, fuel - 1));
    }],
    // division/modulo with a sometimes-zero denominator: div(a,0) = 0 and
    // mod(a,0) = a at every backend, so the identity is fair game
    [5, () => e_bin(num_gen_u32(c, env, fuel - 1), c.g.pick(["/", "%"]), c.g.chance(0.25) ? e_atom("0") : num_gen_u32(c, env, fuel - 1))],
    // shifts: the infix << and >> take a Nat count
    [6, () => {
      c.feat("u32-shift");
      return e_bin(num_gen_u32(c, env, fuel - 1), c.g.pick(["<<", ">>"]), e_atom(String(c.g.int(40)) + "n"));
    }],
    [3, () => e_fn("U32.not", num_gen_u32(c, env, fuel - 1))],
    [3, () => e_fn("U32.inc", num_gen_u32(c, env, fuel - 1))],
    // comparisons: <= >= > ride infix, the rest are calls; all fold
    // through the Bool reader
    [6, () => {
      c.feat("u32-cmp");
      const b = c.g.wpick<() => E>([
        [3, () => e_bin(num_gen_u32(c, env, fuel - 1), c.g.pick(["<=", ">=", ">"]), num_gen_u32(c, env, fuel - 1))],
        [3, () => e_fn("U32." + c.g.pick(["is_eq", "is_ne", "is_lt", "is_le", "is_gt", "is_ge"]), num_gen_u32(c, env, fuel - 1), num_gen_u32(c, env, fuel - 1))],
        [1, () => e_fn("U32.is_zero", num_gen_u32(c, env, fuel - 1))],
      ])();
      return e_fn(helper_bool(c), b);
    }],
    [3, () => {
      c.feat("cmp-ops");
      return e_fn(helper_cmp(c), e_fn("U32.cmp", num_gen_u32(c, env, fuel - 1), num_gen_u32(c, env, fuel - 1)));
    }],
    [3, () => {
      c.feat("nat-ops");
      return e_fn("U32.from_nat", num_gen_nat(c, env, fuel - 1));
    }],
    [2, () => {
      c.feat("char");
      return e_fn(helper_chr(c), e_atom("'" + str_char(c) + "'"));
    }],
    [2, () => {
      c.feat("u32-showread");
      return e_fn("Maybe.default", e_atom("&2"), e_atom("U32"), e_fn("U32.read", e_fn("U32.show", num_gen_u32(c, env, fuel - 1))), num_lit_u32(c));
    }],
    [!c.pure ? 6 : 0, () => {
      c.feat("f32-conv");
      return e_fn("F32.to_u32", num_gen_f32(c, env, fuel - 1));
    }],
    [!c.pure ? 3 : 0, () => {
      c.feat("f32-bits");
      return e_fn("F32.bits", num_gen_f32(c, env, fuel - 1));
    }],
    // the one-step shifts (U32.shl/shr take no count)
    [2, () => e_fn("U32." + c.g.pick(["shl", "shr"]), num_gen_u32(c, env, fuel - 1))],
    [!c.pure ? 3 : 0, () => {
      c.feat("f32-cmp");
      const op = c.g.pick(["==.", "!=.", "<.", "<=.", ">.", ">=."]);
      return e_fn(helper_bool(c), e_bin(num_gen_f32(c, env, fuel - 1), op, num_gen_f32(c, env, fuel - 1)));
    }],
    [fuel >= 2 ? 5 : 0, () => def_new(c, U32C, env, fuel) ?? num_lit_u32(c)],
    [fuel >= 2 ? 4 : 0, () => syn_call_unify(c, U32C, env, fuel) ?? num_lit_u32(c)],
    [fuel >= 2 ? 2 : 0, () => {
      generic_mint(c);
      return syn_call_unify(c, U32C, env, fuel) ?? num_lit_u32(c);
    }],
    [fuel >= 2 ? 2 : 0, () => hof_call(c, env)],
  ])();
}

function num_gen_nat(c: Ctx, env: V[], fuel: number): E {
  const vars = env_of(env, (t) => t.k === "nat");
  const lit = (): E => e_atom(String(c.g.wpick<() => number>([
    [40, () => c.g.int(8)],
    [35, () => c.g.int(64)],
    [20, () => c.g.int(600)],
    [5, () => c.g.int(2400)],
  ])()) + "n");
  if (fuel <= 0) {
    return vars.length > 0 && c.g.chance(0.5) ? e_atom(env_take(c.g.pick(vars))) : lit();
  }
  return c.g.wpick<() => E>([
    [30, () => lit()],
    [vars.length > 0 ? 20 : 0, () => e_atom(env_take(c.g.pick(vars)))],
    [12, () => e_bin(num_gen_nat(c, env, fuel - 1), "+n", num_gen_nat(c, env, fuel - 1))],
    [8, () => e_fn("Nat.add", num_gen_nat(c, env, fuel - 1), num_gen_nat(c, env, fuel - 1))],
    [8, () => e_fn("Nat.sub", num_gen_nat(c, env, fuel - 1), num_gen_nat(c, env, fuel - 1))],
    // keep multiplication operands small: the interpreter's Nat is unary
    [6, () => e_fn("Nat.mul", e_atom(String(c.g.int(40)) + "n"), e_atom(String(c.g.int(40)) + "n"))],
    [4, () => e_fn("Nat.double", num_gen_nat(c, env, fuel - 1))],
    [6, () => e_fn("U32.to_nat", e_bin(num_gen_u32(c, env, 0), "%", e_atom(String(2 + c.g.int(500)))))],
    // no Nat.read: its overflow guard divides 2^48-1 as a unary Nat per
    // digit, which the interpreter cannot finish (see NOTES.md)
  ])();
}

function num_lit_f32(c: Ctx, neg: boolean): E {
  const num = 1 + c.g.int(256);
  const den = c.g.pick([8, 16, 32, 8, 4]);
  const v = num / den;
  const s0 = String(v);
  const s = s0.includes(".") ? s0 : s0 + ".0";
  // there is no negative-literal syntax ('-' glued to a digit heads a
  // binder): negation is the F32.neg native
  if (neg && c.g.chance(0.15)) {
    return e_atom("F32.neg(" + s + ")");
  }
  return e_atom(s);
}

function num_gen_f32(c: Ctx, env: V[], fuel: number): E {
  const vars = env_of(env, (t) => t.k === "f32");
  if (c.pure || fuel <= 0) {
    return vars.length > 0 && c.g.chance(0.4) ? e_atom(env_take(c.g.pick(vars))) : num_lit_f32(c, !c.pure);
  }
  return c.g.wpick<() => E>([
    [22, () => num_lit_f32(c, false)],
    [vars.length > 0 ? 12 : 0, () => e_atom(env_take(c.g.pick(vars)))],
    [4, () => num_lit_f32(c, true)],
    [12, () => e_fn("U32.to_f32", num_gen_u32(c, env, 0))],
    // the show/read round trip of a float (a native on every compiled lane)
    [3, () => {
      c.feat("f32-showread");
      return e_fn("Maybe.default", e_atom("&2"), e_atom("F32"), e_fn("F32.read", e_fn("F32.show", num_gen_f32(c, env, fuel - 1))), num_lit_f32(c, false));
    }],
    [34, () => {
      c.feat("f32-arith");
      return e_bin(num_gen_f32(c, env, fuel - 1), c.g.pick(["+.", "-.", "*."]), num_gen_f32(c, env, fuel - 1));
    }],
    [7, () => e_bin(num_gen_f32(c, env, fuel - 1), "/.", c.g.chance(0.2) ? num_gen_f32(c, env, fuel - 1) : num_lit_f32(c, false))],
    [5, () => e_bin(num_gen_f32(c, env, fuel - 1), "%.", num_lit_f32(c, false))],
    [8, () => e_fn("F32." + c.g.pick(["sqrt", "abs", "neg", "floor", "ceil", "trunc"]), num_gen_f32(c, env, fuel - 1))],
    [5, () => {
      c.feat("f32-trans");
      c.trans = true;
      return e_fn("F32." + c.g.pick(["sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "exp", "log", "log2", "log10"]), num_gen_f32(c, env, fuel - 1));
    }],
    [3, () => {
      c.feat("f32-trans");
      c.trans = true;
      return e_fn("F32." + c.g.pick(["pow", "atan2"]), num_gen_f32(c, env, fuel - 1), num_gen_f32(c, env, fuel - 1));
    }],
  ])();
}

// u32_rhs : a bare literal is a constructor and cannot infer in a let
// value; annotate exactly those
function u32_rhs(e: E): string {
  return /^\d+$/.test(e.s) ? "{" + e.s + " : U32}" : e_at(e);
}

// num_combine : fold a list of U32 expressions into one; a single element
// gets a neutral +0 so a bare literal cannot be the whole answer
function num_combine(c: Ctx, es: E[]): E {
  if (es.length === 0) {
    return num_lit_u32(c);
  }
  if (es.length === 1) {
    return e_bin(es[0], "+", e_atom("0"));
  }
  let acc = es[0];
  for (const e of es.slice(1)) {
    acc = e_bin(acc, c.g.pick(["+", "-", "*", ".^.", "+", "+"]), e);
  }
  return acc;
}

// num_seal : one of six exact U32 identities over the raw result name.
// Comparisons yield Bool now, so the cmp seal rides the Bool reader.
function num_seal(c: Ctx, name: string): E {
  const e = e_atom(name);
  const k = num_lit_u32(c);
  switch (c.g.int(6)) {
    case 0: {
      c.feat("seal-add");
      return e_bin(e_bin(e, "+", k), "-", k);
    }
    case 1: {
      c.feat("seal-xor");
      return e_bin(e_bin(e, ".^.", k), ".^.", k);
    }
    case 2: {
      c.feat("seal-dist");
      const twice = e_bin(e_bin(e, "+", e), "*", e);
      const sq = e_bin(e, "*", e);
      return e_bin(e, "+", e_bin(twice, "-", e_bin(sq, "+", sq)));
    }
    case 3: {
      c.feat("seal-mask");
      const inv = e_fn("U32.not", k);
      return e_bin(e_bin(e, ".&.", k), ".|.", e_bin(e, ".&.", inv));
    }
    case 4: {
      c.feat("seal-cmp");
      const cmp = e_fn(helper_bool(c), e_bin(e, "<=", k));
      return e_bin(e, ".^.", e_bin(cmp, ".^.", cmp));
    }
    default: {
      c.feat("seal-rot");
      const n = 1 + c.g.int(31);
      const l = e_atom(String(n) + "n");
      const r = e_atom(String(32 - n) + "n");
      const rot = e_bin(e_bin(e, "<<", l), ".|.", e_bin(e, ">>", r));
      return e_bin(e_bin(rot, ">>", l), ".|.", e_bin(rot, "<<", r));
    }
  }
}

const STR_CHARS = "abcdefgxyzABCXYZ0189 _.,:!?/+*-#";

function str_char(c: Ctx): string {
  if (c.g.chance(0.03)) {
    c.feat("str-escape");
    return "\\u{" + c.g.pick(["1", "7f", "1b", "e9", "4e2d", "1f600"]) + "}";
  }
  return STR_CHARS[c.g.int(STR_CHARS.length)];
}

function str_lit(c: Ctx, n: number): string {
  let s = "";
  for (let i = 0; i < n; i++) {
    s += c.g.chance(0.06) ? c.g.pick(["\\n", "\\t", "\\\"", "\\\\"]) : str_char(c);
  }
  return "\"" + s + "\"";
}

// Syn: types
// ----------
// syn_ty(c, fuel, need, tvars): a type-valued hole whose kind must fit
// Kind(need). tvars are the enclosing generic's abstract types (their own
// declared kinds ride along). Data slots (need = &2) stay concrete.

type TvarInfo = { n: string; q: QT };

function syn_ty(c: Ctx, fuel: number, need: QT, tvars: TvarInfo[] = [], qvars: string[] = [], ivars: IVar[] = [], imatch = true, neg = false): T {
  const t = syn_ty0(c, fuel, need, tvars, qvars, ivars, imatch, neg);
  // A type that must have a value: draw again, then settle on an available
  // closed datatype. U32 is only in the initial environment with Base.
  if (!neg && !ty_inh(t)) {
    const t2 = syn_ty0(c, fuel, need, tvars, qvars, ivars, imatch, neg);
    if (ty_inh(t2)) return t2;
    if (c.base) return U32C;
    const own = c.adts.find((a) => a.qps.length === 0 && a.tps.length === 0 && a.ips === undefined && a.ctors.length > 0 && qt_fits(a.kind, need));
    if (own === undefined) throw new Error("no inhabited type in a no-Base context");
    return { k: "adt", a: own, qs: [], args: [] };
  }
  return t;
}

// eql_lit : {l == r : I} over an index type, agreeing sides or a clash
function eql_lit(c: Ctx, clash: boolean): T {
  const t = c.g.pick([NATC, BOOLC]);
  const ls = idx_lits(t);
  const l = c.g.pick(ls);
  const r = clash ? c.g.pick(ls.filter((x) => x !== l && (t.k !== "nat" || l === "0n" || x === "0n"))) : l;
  return { k: "eql", t, side: l, rhs: r };
}

function syn_ty0(c: Ctx, fuel: number, need: QT, tvars: TvarInfo[], qvars: string[], ivars: IVar[], imatch: boolean, neg: boolean): T {
  const fits = (t: T): boolean => qt_fits(ty_quant(t), need);
  const tfit = tvars.filter((tv) => qt_fits(tv.q, need));
  const ffit = c.fams.filter((f) => qt_fits(f.kind, need) && (f.done || ivars.some((iv) => iv.sub === true && ty_eq(iv.t, f.idx))));
  const pick_qt = (): QT => {
    if (qvars.length > 0 && c.g.chance(0.4)) {
      return { k: "qv", n: c.g.pick(qvars) };
    }
    return c.g.chance(0.5) ? Q1 : Q2;
  };
  const needData = qt_known(need) === 2;
  const adtCands = c.adts.concat(c.base ? [BASE.List, BASE.Maybe, BASE.Either, BASE.Result] : [])
    .filter((a) => fuel > 0 || (a.tps.length === 0 && a.ips === undefined));
  return c.g.wpick<() => T>([
    [c.base ? 16 : 0, () => U32C],
    [c.base && !needData && fuel > 0 ? 4 : 0, () => ({ k: "arr", el: U32C })],
    [c.base ? (!c.pure ? 8 : 3) : 0, () => F32C],
    [c.base ? 8 : 0, () => NATC],
    [c.base ? 6 : 0, () => BOOLC],
    [c.base ? 3 : 0, () => CMPC],
    [c.base ? 4 : 0, () => CHARC],
    [c.base ? 6 : 0, () => STRC],
    [c.base ? 3 : 0, () => UNITC],
    [tfit.length > 0 ? 18 : 0, () => {
      const tv = c.g.pick(tfit);
      return { k: "tvar", n: tv.n, q: tv.q } as T;
    }],
    // an instantiated datatype (generated or base generic): draw the
    // quantity args, then the type args at their substituted kinds; the
    // whole instance's kind must fit the slot
    [adtCands.length > 0 ? 22 : 0, () => {
      const cands = adtCands;
      for (let tries = 0; tries < 3; tries++) {
        const a = c.g.pick(cands);
        const qs = a.qps.map(() => needData ? Q2 : pick_qt());
        const qm = new Map<string, QT>(a.qps.map((n, i) => [n, qs[i]]));
        const inst_kind = qt_sub(a.kind, qm);
        if (!qt_fits(inst_kind, need)) {
          continue;
        }
        // an index term reaches a Maybe's element at the top of an arm; the
        // other datatypes take closed types
        const args = a.tps.map((tp) => syn_ty(c, fuel - 1, qt_sub(tp.q, qm), tvars, qvars, a === BASE.Maybe && imatch ? ivars : [], false));
        // an indexed datatype takes a closed index, or a matching index term
        const iargs = (a.ips ?? []).map((ip) => a.ips !== undefined && imatch ? idx_arg(c, ip.t, ivars) : idx_lit(c, ip.t));
        // Either at &1, &1 may spell as Or(A, B)
        const spell = a === BASE.Either && qs.every((q) => q.k === "q" && q.q === 1) && c.g.chance(0.4) ? c.g.pick(["or", "bar"] as const) : undefined;
        if (spell !== undefined) {
          c.feat("or");
        }
        return { k: "adt", a, qs, args, iargs, spell } as T;
      }
      const own = c.adts.find((a) => a.qps.length === 0 && a.tps.length === 0 && a.ips === undefined && qt_fits(a.kind, need));
      return own === undefined ? U32C : { k: "adt", a: own, qs: [], args: [] } as T;
    }],
    // an applied family: a closed index, or one of the index terms in scope
    [fuel > 0 && ffit.length > 0 ? 8 : 0, () => {
      const f = c.g.pick(ffit);
      c.feat("fam-use");
      const arg = f.done ? idx_arg(c, f.idx, ivars) : c.g.pick(ivars.filter((iv) => iv.sub === true && ty_eq(iv.t, f.idx))).n;
      return { k: "app", f, arg } as T;
    }],
    // inside a family's arm: a datatype indexed by the arm's sub-index,
    // whose fields may hold the family at it (Word's idiom)
    [fuel > 0 && ivars.length > 0 && imatch && c.g.chance(0.5) ? 14 : 0, () => {
      const a = adt_new(c.sub("iadt"), ivars, need);
      return { k: "adt", a, qs: [], args: [], iargs: ivars.map((iv) => iv.n) } as T;
    }],
    [c.base && fuel > 0 ? 8 : 0, () => {
      const q: 1 | 2 = needData ? 2 : c.g.chance(0.3) ? 2 : 1;
      const el = (): T => syn_ty(c, fuel - 1, q === 2 ? Q2 : need, tvars, qvars, ivars, false);
      const spell = q === 1 && c.g.chance(0.2) ? "pair" : undefined;
      if (spell !== undefined) {
        c.feat("pair");
      }
      return { k: "tup", a: el(), b: el(), q, spell } as T;
    }],
    [fuel > 0 && !needData ? 7 : 0, () => {
      const q: BQ = c.g.wpick<BQ>([[7, 1], [2, 0], [1, 2]]);
      const dom = q === 2 ? syn_ty(c, 0, Q2, tvars, qvars) : syn_ty(c, fuel - 1, Q0, tvars, qvars);
      return { k: "fun", q, dom, cod: syn_ty(c, fuel - 1, Q0, tvars, qvars, ivars, false) } as T;
    }],
    [c.base && fuel > 0 && c.g.chance(0.4) ? 4 : 0, () => {
      const q = needData ? Q2 : pick_qt();
      return { k: "map", q, v: syn_ty(c, 0, q, tvars, qvars) } as T;
    }],
    [c.base ? 2 : 0, () => SETC],
    // the pairs Base's containers answer in (Array.get, swap, size, clone;
    // Map.has, pop, get; Set.has): the container comes back beside the read
    [c.base && fuel > 0 && !needData ? 5 : 0, () => {
      c.feat("container-pair");
      const el = c.g.pick([U32C, U32C, BOOLC, STRC, NATC]);
      const q = c.g.chance(0.5) ? Q2 : Q1;
      return c.g.pick<() => T>([
        () => ({ k: "tup", a: { k: "arr", el }, b: el, q: 1 }),
        () => ({ k: "tup", a: { k: "arr", el }, b: U32C, q: 1 }),
        () => ({ k: "tup", a: { k: "arr", el }, b: { k: "arr", el }, q: 1 }),
        () => ({ k: "tup", a: { k: "map", q, v: el }, b: BOOLC, q: 1 }),
        () => ({ k: "tup", a: { k: "map", q, v: el }, b: t_maybe(q, el), q: 1 }),
        () => ({ k: "tup", a: { k: "map", q: Q2, v: el }, b: el, q: 1 }),
        () => ({ k: "tup", a: SETC, b: BOOLC, q: 1 }),
      ])();
    }],
    // a dependent pair: a witness, mostly an index term, and evidence about
    // it, which may be a proposition
    [c.base && fuel > 0 && !needData ? 3 : 0, () => {
      c.feat("sig");
      const x = bind_name(c, []);
      const a = c.g.chance(0.7) ? c.g.pick([NATC, BOOLC].concat(c.adts.filter((d) => idx_type({ k: "adt", a: d, qs: [], args: [] })).map((d): T => ({ k: "adt", a: d, qs: [], args: [] })))) : syn_ty(c, 0, Q2, tvars, qvars);
      const b = syn_ty(c, fuel - 1, Q0, tvars, qvars, idx_type(a) ? ivars.concat([{ n: x, t: a }]) : ivars, imatch, true);
      const spell = c.g.wpick<"amp" | "exists" | "sigma">([[5, "amp"], [3, "exists"], [2, "sigma"]]);
      return { k: "sig", x, a, b, spell } as T;
    }],
    // propositions, where the type may be uninhabited: Empty, an equality
    // of literals (agreeing or a clash), its negation
    [c.base && neg ? 6 : 0, () => {
      c.feat("empty");
      return { k: "empty" } as T;
    }],
    [c.base && neg ? 5 : 0, () => {
      const clash = c.g.chance(0.5);
      c.feat(clash ? "eql-clash" : "eql-lit");
      return eql_lit(c, clash);
    }],
    [c.base && neg && !needData ? 3 : 0, () => {
      c.feat("eql-ne");
      const e = eql_lit(c, c.g.chance(0.7)) as Extract<T, { k: "eql" }>;
      return { k: "fun", q: 1, dom: e, cod: { k: "empty" } } as T;
    }],
  ])();
}

// idx_type : may a term of this type index a family (Nat, Bool, an enum)?
function idx_type(t: T): boolean {
  return t.k === "nat" || t.k === "bool"
    || (t.k === "adt" && t.a.qps.length === 0 && t.a.tps.length === 0 && t.a.ips === undefined && ty_data(t)
      && t.a.ctors.length > 0 && t.a.ctors.every((ct) => ct.fields.length === 0));
}

// idx_lits : the closed literals syn draws for an index type (Nat: 0..3)
function idx_lits(t: T): string[] {
  if (t.k === "nat") {
    return ["0n", "1n", "2n", "3n"];
  }
  if (t.k === "bool") {
    return ["False{}", "True{}"];
  }
  if (t.k === "adt") {
    return t.a.ctors.map((ct) => ct.name + "{}");
  }
  return [];
}

function idx_first(t: T): string {
  return idx_lits(t)[0];
}

// ty_inh : has the type a value the generator can build? A family at an
// index term is inhabited when every arm is; a pair when some witness
// makes its evidence so; a function when its result is, or its domain
// refutes; an equality when its sides agree.
function ty_inh(t: T, seen: Set<Adt | Fam> = new Set()): boolean {
  switch (t.k) {
    case "empty": return false;
    case "eql": return t.rhs === undefined || t.rhs === t.side;
    case "app": {
      const arm = fam_unfold(t.f, t.arg);
      return arm !== null ? ty_inh(arm, seen) : fam_total(t.f, seen);
    }
    case "sig": return idx_type(t.a) ? idx_lits(t.a).some((w) => ty_inh(ty_tsub(t.b, t.x, w), seen)) : ty_inh(t.a, seen) && ty_inh(t.b, seen);
    case "fun": return ty_inh(t.cod, seen) || ty_refutable(t.dom);
    case "tup": return ty_inh(t.a, seen) && ty_inh(t.b, seen);
    case "adt": {
      // a datatype met again on the way is taken inhabited: recursion
      // through a family's sub-index ends at the base arm
      if (seen.has(t.a)) {
        return true;
      }
      const s2 = new Set(seen).add(t.a);
      return t.a.ctors.length === 0 ? false
        : t.a.ctors.some((ct) => ct.fields.every((f) => f.q === 0 || ty_inh(f.t, s2)));
    }
    default: return true;
  }
}

function fam_total(f: Fam, seen: Set<Adt | Fam> = new Set()): boolean {
  if (seen.has(f)) {
    return true;
  }
  const s2 = new Set(seen).add(f);
  return f.done && f.arms.every((arm) => ty_inh(arm.ty, s2));
}

// ty_refutable : an equality of two different constructor literals of an
// index type (for Nat, one side is 0n), refuted by a rewrite through a
// discriminating family
function ty_refutable(t: T): boolean {
  if (t.k !== "eql" || t.rhs === undefined || t.rhs === t.side || !idx_type(t.t)) {
    return false;
  }
  return t.t.k !== "nat" || t.side === "0n" || t.rhs === "0n";
}

// idx_lit : a closed literal of an index type; idx_arg : that, or an index
// term in scope (an arm's sub-index) when one has the type
function idx_lit(c: Ctx, t: T): string {
  if (t.k === "nat") {
    return String(c.g.int(4)) + "n";
  }
  if (t.k === "bool") {
    return c.g.pick(["False{}", "True{}"]);
  }
  if (t.k === "adt") {
    return c.g.pick(t.a.ctors).name + "{}";
  }
  throw new Error("not an index type: " + ty_str(t));
}

function idx_arg(c: Ctx, t: T, ivars: IVar[]): string {
  const vs = ivars.filter((iv) => ty_eq(iv.t, t));
  return vs.length > 0 && c.g.chance(0.7) ? c.g.pick(vs).n : idx_lit(c, t);
}

function idx_is_lit(t: T, arg: string): boolean {
  if (t.k === "nat") {
    return /^\d+n$/.test(arg);
  }
  return /\{\}$/.test(arg);
}

// fam_unfold : the arm a closed index selects, with the arm's sub-index
// (if any) substituted; null on a variable index
function fam_unfold(f: Fam, arg: string): T | null {
  if (!idx_is_lit(f.idx, arg)) {
    return null;
  }
  if (f.idx.k === "nat") {
    const n = Number(arg.slice(0, -1));
    const arm = f.arms[n === 0 ? 0 : 1];
    return arm.sub === null ? arm.ty : ty_tsub(arm.ty, arm.sub, String(n - 1) + "n");
  }
  const arm = f.arms.find((x) => x.lit === arg);
  return arm === undefined ? null : arm.ty;
}

// fam_new : def F(x: I) -> K by match, one arm per constructor of I
function fam_new(c: Ctx): Fam {
  const name = decl_name(c, "Fm");
  const ik = c.base ? c.g.wpick<string>([[5, "nat"], [3, "bool"], [3, "enum"]]) : "enum";
  c.feat("fam-" + ik);
  let idx: T = ik === "nat" ? NATC : BOOLC;
  if (ik === "enum") {
    const en = decl_name(c, "E");
    const ctors = ["a", "b", "c"].slice(0, 2 + c.g.int(2)).map((x) => ({ name: decl_name(c, en + x), fields: [] }));
    const a: Adt = { name: en, qps: [], tps: [], kind: Q2, ctors, rec: false };
    c.push("type " + en + " is Data:\n" + ctors.map((ct) => "  " + ct.name + "{}").join("\n"));
    c.adts.push(a);
    idx = { k: "adt", a, qs: [], args: [] };
  }
  const kind = c.g.chance(0.5) ? Q2 : Q1;
  const f: Fam = { name, idx, kind, arms: [], done: false };
  c.fams.push(f);
  const index = bind_name(c, []);
  // the law first (a datatype minted in an arm mentions the family), the
  // def fills it after the arms: base's own Word ordering
  const kind_s = qt_known(kind) === 2 ? "Data" : "Type";
  c.push("law " + name + ":\n  for " + index + ": " + ty_str(idx) + "\n  " + kind_s);
  const pred = ik === "nat" ? bind_name(c, [], [index]) : "";
  const pats: Array<{ pat: string; sub: string | null; lit: string | null; src?: string }> = ik === "nat"
    ? [{ pat: "0n", sub: null, lit: "0n" }, { pat: "1n+" + pred, sub: pred, lit: null, src: bind_name(c, [], [index, pred]) }]
    : ik === "bool" ? [{ pat: "False{}", sub: null, lit: "False{}" }, { pat: "True{}", sub: null, lit: "True{}" }]
    : (idx as Extract<T, { k: "adt" }>).a.ctors.map((ct) => ({ pat: ct.name + "{}", sub: null, lit: ct.name + "{}" }));
  for (const pt of pats) {
    // the recursive arm may mention the family at its sub-index; the rest
    // are ordinary types, so every unfolding ends
    const ivars: IVar[] = pt.sub === null ? [] : [{ n: pt.sub, t: idx, sub: true }];
    const ty = syn_ty(c.sub("arm"), 2, kind, [], [], ivars, true, true);
    f.arms.push({ ...pt, ty });
  }
  const rows = f.arms.map((arm) => "    case " + arm.pat + ":\n      " + ty_str(arm.ty));
  c.push("def " + name + "(" + index + "):\n  match " + index + ":\n" + rows.join("\n"));
  f.done = true;
  return f;
}

// fam_pat : an arm's case row in an index-generic def; the sub-index binds
// under a fresh name and re-binds reusable, since the arm may hold the
// family at it more than once
function fam_pat(arm: FamArm, rebind: boolean): string {
  if (arm.sub === null) {
    return arm.pat + ":";
  }
  const pos = arm.pat.lastIndexOf(arm.sub);
  const pat = arm.pat.slice(0, pos) + (arm.src ?? arm.sub + "0") + arm.pat.slice(pos + arm.sub.length);
  return pat + ":" + (rebind ? "\n      " + fam_rebind(arm) : "");
}

function fam_rebind(arm: FamArm): string {
  return "+" + arm.sub + " = " + (arm.src ?? arm.sub + "0");
}

// refute_ensure : def rf(e: {l == r : I}) -> Empty, for two different
// constructor literals: a discriminating family sends r to Empty and the
// rest to Unit, so rewriting the goal Empty (= Disc(r)) through e leaves
// Disc(l) = Unit, answered by Unit{}
function refute_ensure(c: Ctx, e: Extract<T, { k: "eql" }>): string {
  const key = "refute:" + ty_str(e);
  const got = c.memo.get(key);
  if (got !== undefined) {
    return got;
  }
  c.feat("refute");
  const r = e.rhs as string;
  const disc = disc_fam(c, e.t, r);
  const name = decl_name(c, "ne");
  c.memo.set(key, name);
  c.push("def " + name + "(e: {" + e.side + " == " + r + " : " + ty_str(e.t) + "}) -> Empty:\n  %e : " + disc.name + "(_);\n  Unit{}");
  return name;
}

// disc_fam : the family over an index type that is Empty at one literal and
// Unit elsewhere (for Nat, at zero or at every successor)
function disc_fam(c: Ctx, idx: T, at: string): Fam {
  const key = "disc:" + ty_str(idx) + ":" + at;
  const got = c.memo.get(key);
  if (got !== undefined) {
    return c.fams.find((f) => f.name === got) as Fam;
  }
  const name = decl_name(c, "Fm");
  c.memo.set(key, name);
  const arms: FamArm[] = idx.k === "nat"
    ? [{ pat: "0n", sub: null, lit: "0n", ty: at === "0n" ? { k: "empty" } : UNITC },
      { pat: "1n+p", sub: "p", lit: null, ty: at === "0n" ? UNITC : { k: "empty" } }]
    : idx_lits(idx).map((l) => ({ pat: l, sub: null, lit: l, ty: (l === at ? { k: "empty" } : UNITC) as T }));
  const f: Fam = { name, idx, kind: Q2, arms, done: true };
  c.fams.push(f);
  c.push("def " + name + "(x: " + ty_str(idx) + ") -> Data:\n  match x:\n" + arms.map((arm) => "    case " + arm.pat + ":\n      " + ty_str(arm.ty)).join("\n"));
  return f;
}

// cast_ensure : def fc(-m: I, -n: I, e: {m == n : I}, w: F(m)) -> F(n), a
// rewrite through the family with a hole motive
function cast_ensure(c: Ctx, f: Fam): string {
  return helper(c, "cast:" + f.name, "fc", (c, name) => {
    const vs: string[] = [];
    for (let i = 0; i < 4; i++) {
      vs.push(bind_name(c, [], vs));
    }
    const [m, n, e, w] = vs;
    const I = ty_str(f.idx);
    return "def " + name + "(-" + m + ": " + I + ", -" + n + ": " + I + ", " + e + ": {" + m + " == " + n + " : " + I + "}, "
      + w + ": " + f.name + "(" + m + ")) -> " + f.name + "(" + n + "):\n  %" + e + " : " + f.name + "(_); " + w;
  });
}

// mk_fam : def mk(n: I) -> F(n), the index-generic value of a family:
// each arm synthesizes its type with the sub-index in scope, so F(p)
// inside is the recursive call
function mk_fam(c: Ctx, f: Fam): string {
  const key = "mk:fam:" + f.name;
  const got = c.memo.get(key);
  if (got !== undefined) {
    return got;
  }
  const name = decl_name(c, "mf");
  c.memo.set(key, name);
  c.wip.add(key);
  c.feat("fam-mk");
  c = c.sub("mkf");
  const index = bind_name(c, []);
  const rows = f.arms.map((arm) => {
    const env: V[] = arm.sub === null ? [] : [v_new(arm.sub, f.idx, true)];
    if (env.length > 0) env[0].dec = true;
    return "    case " + fam_pat(arm, true) + "\n      " + e_at(syn(c, arm.ty, env, 1));
  });
  c.push("def " + name + "(" + index + ": " + ty_str(f.idx) + ") -> " + f.name + "(" + index + "):\n  match " + index + ":\n" + rows.join("\n"));
  c.wip.delete(key);
  return name;
}

// rd_fam : def rd(n: I, v: F(n)) -> U32, reading v at the arm the index
// selects (the checker refines v's type under the match on n)
function rd_fam(c: Ctx, f: Fam): string {
  const key = "rd:fam:" + (c.pure ? "p:" : "x:") + f.name;
  const got = c.memo.get(key);
  if (got !== undefined) {
    return got;
  }
  const name = decl_name(c, "rf");
  c.memo.set(key, name);
  c.feat("fam-rd");
  c = c.sub("rdf");
  const index = bind_name(c, []);
  const valueName = bind_name(c, [], [index]);
  // the re-bind of the sub-index sits after the destructures and inside
  // the match arms that read v: a let cannot open a later scrutinee
  const rows = f.arms.map((arm) => "    case " + fam_pat(arm, false) + "\n      " + rd_arm(c, arm.ty, valueName, "      ", arm.sub === null ? null : fam_rebind(arm)));
  c.push("def " + name + "(" + index + ": " + ty_str(f.idx) + ", " + valueName + ": " + f.name + "(" + index + ")) -> U32:\n  match " + index + ":\n" + rows.join("\n"));
  return name;
}

// Adt minting
// -----------
// Flavors: "data" (is Data, concrete Data fields), "qpoly" (quantity
// parameters + Kind(a) / Kind(a <&> b), parameter-typed fields), "type"
// (is Type: closure and Array-free function fields welcome). Ctor 0 never
// recurs; self fields keep uniform recursion so minted folds descend.

function adt_new(c: Ctx, ips: IVar[] = [], ikind: QT | null = null): Adt {
  const name = decl_name(c, "D");
  // an indexed datatype (ips) is monomorphic over its index: its kind is
  // the family arm's, its fields may hold the family at the index
  const flavor = ips.length > 0 ? (qt_known(ikind ?? Q2) === 2 ? "data" : "type")
    : !c.base && c.adts.length === 0 ? "data" : c.g.wpick<string>([[5, "data"], [4, "qpoly"], [2, "type"]]);
  const nqp = flavor === "qpoly" ? 1 + c.g.int(2) : 0;
  const qps: string[] = [];
  for (let i = 0; i < nqp; i++) qps.push(bind_name(c, [], qps));
  const ntp = ips.length > 0 ? 0 : flavor === "qpoly" ? Math.max(1, c.g.int(3)) : flavor === "type" ? c.g.int(2) : 0;
  const tps: Array<{ n: string; q: QT }> = [];
  for (let i = 0; i < ntp; i++) {
    const q: QT = nqp > 0 ? { k: "qv", n: qps[i % nqp] } : Q1;
    tps.push({ n: bind_name(c, [], [...qps, ...tps.map((tp) => tp.n)]), q });
  }
  let kind: QT;
  if (flavor === "data") {
    kind = Q2;
  } else if (flavor === "type") {
    kind = Q1;
  } else if (nqp === 2 && c.g.chance(0.6)) {
    c.feat("kind-meet");
    kind = { k: "qm", a: { k: "qv", n: qps[0] }, b: { k: "qv", n: qps[1] } };
  } else {
    c.feat("kind-qvar");
    kind = { k: "qv", n: qps[0] };
  }
  const a: Adt = { name, qps, tps, kind, ctors: [], rec: false, ips: ips.length > 0 ? ips : undefined };
  if (ips.length > 0) {
    c.feat("adt-indexed");
  }
  const selfT: T = {
    k: "adt", a, qs: qps.map((n) => ({ k: "qv", n }) as QT),
    args: tps.map((tp) => ({ k: "tvar", n: tp.n, q: tp.q }) as T),
  };
  const tvinfo: TvarInfo[] = tps.map((tp) => ({ n: tp.n, q: tp.q }));
  const nctors = size_pick(c, 1 + c.g.int(3), 24);
  for (let ci = 0; ci < nctors; ci++) {
    const fields: Field[] = [];
    // The first declaration in an empty environment is the foundation for
    // later types. Until it is installed there is no field type to draw.
    const nf = !c.base && c.adts.length === 0 ? 0 : size_pick(c, c.g.int(4), 8);
    for (let f = 0; f < nf; f++) {
      const eq = c.g.chance(0.12) ? 0 : 1;
      if (eq === 0) {
        // erased field: any type fits Kind(&0)
        c.feat("erased-field");
        fields.push({ q: 0, t: syn_ty(c, 1, Q0, tvinfo, qps) });
        continue;
      }
      const self = ips.length === 0 && ci > 0 && c.g.chance(0.3);
      if (self) {
        a.rec = true;
        fields.push({ q: 1, t: selfT });
        continue;
      }
      // an indexed datatype's field: a family at the index, or any type
      // drawn with the index in scope
      if (ips.length > 0) {
        const t0 = syn_ty(c, 1, flavor === "data" ? Q2 : Q1, [], [], ips, false);
        fields.push({ q: 1, t: t0 });
        continue;
      }
      // a live field's kind must fit Kind(G): parameter types fit by
      // construction (their kind is a side of the meet), Data fits all,
      // and a "type"-kinded family also takes functions
      let t: T;
      if (c.base && flavor === "type" && c.g.chance(0.35)) {
        t = { k: "fun", q: 1, dom: c.g.pick([U32C, NATC, BOOLC]), cod: c.g.pick([U32C, BOOLC]) };
      } else if (tvinfo.some((tv) => qt_fits(tv.q, kind)) && c.g.chance(0.5)) {
        const tv = c.g.pick(tvinfo.filter((x) => qt_fits(x.q, kind)));
        t = { k: "tvar", n: tv.n, q: tv.q };
      } else {
        t = syn_ty(c, 1, Q2, [], []);
      }
      const many = ty_data(t) && c.g.chance(0.15) ? 2 : 1;
      fields.push({ q: many as BQ, t });
    }
    a.ctors.push({ name: decl_name(c, name + ("abcd"[ci] ?? "k" + String(ci))), fields });
  }
  const head = qps.concat(tps.map((tp) => "-" + tp.n + ": Kind(" + qt_bare(tp.q) + ")"), ips.map((ip) => "-" + ip.n + ": " + ty_str(ip.t)));
  const kind_s = flavor === "data" ? "Data" : flavor === "type" ? "Type" : "Kind(" + qt_bare(kind) + ")";
  const rows = a.ctors.map((ct) => {
    const fieldNames: string[] = [];
    const fields = ct.fields.map((f) => {
      const field = bind_name(c, [], fieldNames.concat(qps, tps.map((tp) => tp.n), ips.map((ip) => ip.n)));
      fieldNames.push(field);
      return bq_prefix(f.q) + field + ": " + ty_top(f.t);
    });
    return "  " + ct.name + "{" + fields.join(", ") + "}";
  });
  c.push("type " + name + (head.length > 0 ? "<" + head.join(", ") + ">" : "") + " is " + kind_s + ":"
    + (rows.length > 0 ? "\n" + rows.join("\n") : ""));
  c.feat("adt-" + flavor);
  c.adts.push(a);
  return a;
}

// qt_bare : a quantity term without the outer parens (inside Kind(..))
function qt_bare(q: QT): string {
  return q.k === "qm" ? qt_str(q.a) + " <&> " + qt_str(q.b) : qt_str(q);
}

// adt_inst : instantiate a generated/base adt at concrete quantities
function adt_inst(c: Ctx, a: Adt, needData: boolean): T | null {
  for (let tries = 0; tries < 3; tries++) {
    const qs = a.qps.map(() => needData ? Q2 : (c.g.chance(0.5) ? Q1 : Q2));
    const qm = new Map<string, QT>(a.qps.map((n, i) => [n, qs[i]]));
    if (needData && qt_known(qt_sub(a.kind, qm)) !== 2) {
      continue;
    }
    const args = a.tps.map((tp) => syn_ty(c, 1, qt_sub(tp.q, qm), [], []));
    return { k: "adt", a, qs, args, iargs: (a.ips ?? []).map((ip) => idx_lit(c, ip.t)) };
  }
  return null;
}

// adt_field_ty : a field's type at an instance: type args substituted, and
// an indexed datatype's index params replaced by the instance's args
function adt_field_ty(ft: T, t: Extract<T, { k: "adt" }>, m: Map<string, T>, qm: Map<string, QT>): T {
  let r = ty_sub(ft, m, qm);
  (t.a.ips ?? []).forEach((ip, i) => {
    r = ty_tsub(r, ip.n, (t.iargs ?? [])[i]);
  });
  return r;
}

// Pattern helpers
// ---------------

// adt_row : one match row for a ctor of an instantiated adt — pattern text
// plus the bound field vars (erased fields bind but stay dead)
function adt_row(c: Ctx, t: Extract<T, { k: "adt" }>, ct: Ctor, scrMany: boolean, env: V[] = []): { pat: string; vs: V[]; plus: V[]; names: string[] } {
  const m = new Map<string, T>(t.a.tps.map((tp, i) => [tp.n, t.args[i]]));
  const qm = new Map<string, QT>(t.a.qps.map((n, i) => [n, t.qs[i]]));
  const vs: V[] = [];
  const plus: V[] = [];
  const names: string[] = [];
  for (let i = 0; i < ct.fields.length; i++) {
    const f = ct.fields[i];
    const nm = bind_name(c, env, vs.map((v) => v.name).concat(names));
    const ft = adt_field_ty(f.t, t, m, qm);
    if (f.q === 0) {
      names.push(nm);
      continue;
    }
    // a + on a lone Data field binder re-binds it reusable (case K{+x})
    const mark = f.q === 1 && !scrMany && ty_data(ft) && c.g.chance(0.2);
    if (mark) {
      c.feat("plus-pat");
    }
    names.push((mark ? "+" : "") + nm);
    const v = v_new(nm, ft, (f.q === 2 || scrMany || mark) && ty_data(ft));
    vs.push(v);
    if (mark) {
      plus.push(v);
    }
  }
  // a List row spells its constructor as the cons or the empty literal
  if (t.a === BASE.List && c.g.chance(0.5)) {
    c.feat("cons-pat");
    return { pat: ct.name === "Nil" ? "[]" : names[0] + " <> " + names[1], vs, plus, names };
  }
  return { pat: ct.name + "{" + names.join(", ") + "}", vs, plus, names };
}

// Readers
// -------
// rd_ensure(c, t): a memoized `def rd(x: T) -> U32` structural fold. Every
// live field folds in (nothing dead) except F32 on the c.pure side, which is
// dropped — base's F32 ops are stuck in the interpreter. Literal salts
// keep arms distinguishable.

// rd_call : the reader applied to x; a family at an index term reads
// through the family's own reader
function rd_call(c: Ctx, t: T, x: string): string {
  if (t.k === "u32") {
    return x;
  }
  if (t.k === "app" && !idx_is_lit(t.f.idx, t.arg)) {
    return rd_fam(c, t.f) + "(" + t.arg + ", " + x + ")";
  }
  return rd_ensure(c, t) + "(" + x + ")";
}

// rd_arm : the body reading x at a type that may mention an index term,
// inline: a tuple destructures, a function applies, a Maybe or an indexed
// datatype matches (the tail of the body), the family at the index calls
// its reader, and a closed type calls its own. No def is minted under the
// index, so nothing recurses back into the family's reader but itself.
function rd_arm(c: Ctx, t: T, x: string, ind: string, rebind: string | null = null, plus: string | null = null): string {
  const pre: string[] = [];
  const rb = rebind === null ? "" : rebind + "\n";
  // plus : expressions added to every final expression (a pair's witness
  // read, beside its evidence's)
  const extra: string[] = plus === null ? [] : [plus];
  const add = (e: string): string => extra.length === 0 ? e : "(" + [e, ...extra].join(" + ") + " : U32)";
  const flat = (t2: T, x2: string): string => {
    if (!ty_open(t2) || t2.k === "app") {
      return rd_call(c, t2, x2);
    }
    if (t2.k === "sig") {
      pre.push("(" + (idx_type(t2.a) ? "+" : "") + t2.x + ", " + x2 + "e) = " + x2);
      return "(" + flat(t2.a, t2.x) + " + " + flat(t2.b, x2 + "e") + " : U32)";
    }
    if (t2.k === "tup") {
      const a = x2 + "a";
      const b = x2 + "b";
      pre.push("(" + a + ", " + b + ") = " + x2);
      return "(" + flat(t2.a, a) + " + " + flat(t2.b, b) + " : U32)";
    }
    if (t2.k === "fun") {
      return flat(t2.cod, x2 + "(" + e_at(syn(c, t2.dom, [], 1)) + ")");
    }
    throw new Error("rd_arm: not flat: " + ty_str(t2));
  };
  const tail = (t2: T, x2: string, ind2: string): string => {
    if (t2.k === "sig" && ty_open(t2)) {
      pre.push("(" + (idx_type(t2.a) ? "+" : "") + t2.x + ", " + x2 + "e) = " + x2);
      extra.push(flat(t2.a, t2.x));
      return tail(t2.b, x2 + "e", ind2);
    }
    if (t2.k === "adt" && t2.a === BASE.Maybe && ty_open(t2)) {
      const y = x2 + "s";
      return "match " + x2 + ":\n" + ind2 + "  case None{}:\n" + ind2 + "    " + add(String(1 + c.g.int(99)))
        + "\n" + ind2 + "  case Some{" + y + "}:\n" + ind2 + "    " + rd_arm(c, t2.args[0], y, ind2 + "    ", rebind, plus);
    }
    if (t2.k === "adt" && t2.a.ips !== undefined && ty_open(t2)) {
      const m = new Map<string, T>();
      const qm = new Map<string, QT>();
      const rows = t2.a.ctors.map((ct) => {
        const vs: string[] = [];
        for (const _ of ct.fields) vs.push(bind_name(c, [], vs));
        const pre2: string[] = [];
        const parts: string[] = [];
        ct.fields.forEach((f, i) => {
          if (f.q === 0) {
            return;
          }
          const ft = adt_field_ty(f.t, t2, m, qm);
          if (ft.k === "f32" && c.pure) {
            return;
          }
          const saved = pre.length;
          parts.push(flat(ft, vs[i]));
          pre2.push(...pre.splice(saved));
        });
        parts.push(String(1 + c.g.int(99)));
        return ind2 + "  case " + ct.name + "{" + vs.join(", ") + "}:\n" + pre2.concat(rebind === null ? [] : [rebind]).map((l) => ind2 + "    " + l + "\n").join("")
          + ind2 + "    " + add(parts.length > 1 ? "(" + parts.join(" + ") + " : U32)" : parts[0]);
      });
      return "match " + x2 + ":\n" + rows.join("\n");
    }
    return flat(t2, x2);
  };
  const e = tail(t, x, ind);
  // a match tail carries the re-bind and the addend in its arms; a flat
  // one takes them last
  const flatTail = !e.startsWith("match ");
  return pre.map((l) => l + "\n" + ind).join("") + (flatTail ? rb.replace("\n", "\n" + ind) + add(e) : e);
}

function rd_ensure(c: Ctx, t: T): string {
  const key = "rd:" + (c.pure ? "p:" : "x:") + ty_str(t);
  const got = c.memo.get(key);
  if (got !== undefined) {
    if (c.wip.has(key)) {
      throw new Error("rd_ensure knot: " + key);
    }
    return got;
  }
  const name = decl_name(c, "rd");
  c.memo.set(key, name);
  c.wip.add(key);
  c = c.sub("rd");
  const arg = bind_name(c, []);
  const salt = (): string => String(1 + c.g.int(99));
  const def1 = (param: string, body: string): string => "def " + name + "(" + param + ") -> U32:\n  " + body;
  const src = ((): string => {
    switch (t.k) {
      case "u32": return def1(arg + ": U32", "(" + arg + " + " + salt() + " : U32)");
      case "f32": return def1(arg + ": F32", c.pure ? salt() : "F32.to_u32((" + arg + " * " + num_lit_f32(c, false).s + " : F32))");
      case "nat": return def1(arg + ": Nat", "(U32.from_nat(" + arg + ") + " + salt() + " : U32)");
      case "bool": return def1(arg + ": Bool", "(" + helper_bool(c) + "(" + arg + ") + " + salt() + " : U32)");
      case "cmp": return def1(arg + ": Cmp", "(" + helper_cmp(c) + "(" + arg + ") * " + String(1 + c.g.int(9)) + " : U32)");
      case "char": return def1(arg + ": Char", "(" + helper_chr(c) + "(" + arg + ") + " + salt() + " : U32)");
      case "str": return def1(arg + ": String", helper_strlen(c) + "(" + arg + ", " + salt() + ")");
      case "arr": {
        const pair = bind_name(c, []);
        const array = bind_name(c, [], [pair]);
        const size = bind_name(c, [], [pair, array]);
        const sized = decl_name(c, "rb");
        c.push("def " + sized + "(" + pair + ": " + ty_str(t) + " & U32) -> U32:\n  (" + array + ", " + size + ") = " + pair + "\n  (" + size + " + " + salt() + " : U32)");
        return def1(arg + ": " + ty_str(t), sized + "(Array.size(" + ty_grp(t.el) + ", " + arg + "))");
      }
      case "unit": return def1(arg + ": Unit", "match " + arg + ":\n    case Unit{}:\n      " + salt());
      case "set": return def1(arg + ": Set()", "(U32.from_nat(Set.size(" + arg + ")) + " + salt() + " : U32)");
      case "tup": {
        // a + on a destructured Data component re-binds it reusable
        const plus = ty_data(t.a) && c.g.chance(0.3);
        if (plus) {
          c.feat("plus-tup");
        }
        const ta = bind_name(c, [], [arg]);
        const tb = bind_name(c, [], [arg, ta]);
        return def1(arg + ": " + ty_str(t), "(" + (plus ? "+" : "") + ta + ", " + tb + ") = " + arg + "\n  (" + rd_call(c, t.a, ta) + " + " + rd_call(c, t.b, tb) + " : U32)");
      }
      case "fun": {
        if (!ty_inh(t.dom)) {
          return def1(arg + ": " + ty_grp(t), salt());
        }
        const app = arg + "(" + e_at(syn(c, t.dom, [], 1)) + ")";
        return def1(arg + ": " + ty_grp(t), t.cod.k === "u32" ? "(" + app + " + " + salt() + " : U32)" : rd_call(c, t.cod, app));
      }
      case "map": {
        const sl = helper_strlen(c);
        const keyName = bind_name(c, [], [arg]);
        const valueName = bind_name(c, [], [arg, keyName]);
        const pos = bind_name(c, [], [arg, keyName, valueName]);
        const lo = bind_name(c, [], [arg, keyName, valueName, pos]);
        const hi = bind_name(c, [], [arg, keyName, valueName, pos, lo]);
        return def1(arg + ": Map<" + qt_str(t.q) + ", " + ty_grp(t.v) + ">", "match " + arg + ":\n"
          + "    case MTip{}:\n      " + salt() + "\n"
          + "    case MLeaf{" + keyName + ", " + valueName + "}:\n      (" + sl + "(" + keyName + ", 3) + " + rd_call(c, t.v, valueName) + " : U32)\n"
          + "    case MNode{" + pos + ", " + lo + ", " + hi + "}:\n      (U32.from_nat(" + pos + ") + " + name + "(" + lo + ") + " + name + "(" + hi + ") : U32)");
      }
      case "app": return def1(arg + ": " + ty_str(t), rd_fam(c, t.f) + "(" + t.arg + ", " + arg + ")");
      case "empty": return def1(arg + ": Empty", "match " + arg + ":");
      case "sig": {
        // the witness re-binds reusable: read on its own, added into the
        // evidence's read, and named in the evidence's type
        const ra = rd_call(c, t.a, t.x);
        const ev = bind_name(c, [], [arg, t.x]);
        return def1(arg + ": " + ty_str(t), "(" + (idx_type(t.a) ? "+" : "") + t.x + ", " + ev + ") = " + arg + "\n  " + rd_arm(c, t.b, ev, "  ", null, ra));
      }
      case "adt": return rd_adt(c, name, t);
      default: return def1(arg + ": " + ty_str(t), salt());
    }
  })();
  c.push(src);
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 1, t }], ret: U32C });
  c.wip.delete(key);
  return name;
}

function rd_adt(c: Ctx, name: string, t: Extract<T, { k: "adt" }>): string {
  const arg = bind_name(c, []);
  const m = new Map<string, T>(t.a.tps.map((tp, i) => [tp.n, t.args[i]]));
  const qm = new Map<string, QT>(t.a.qps.map((n, i) => [n, t.qs[i]]));
  const rows = t.a.ctors.map((ct) => {
    const vs: string[] = [];
    for (const _ of ct.fields) vs.push(bind_name(c, [], vs));
    const parts: E[] = [];
    ct.fields.forEach((f, i) => {
      if (f.q === 0) {
        return;
      }
      const ft = adt_field_ty(f.t, t, m, qm);
      if (ft.k === "adt" && ft.a === t.a && ty_eq(ft, t)) {
        parts.push(e_atom(name + "(" + vs[i] + ")"));
      } else if (ft.k === "u32") {
        parts.push(e_atom(vs[i]));
      } else if (ft.k === "f32" && c.pure) {
        // dropped: F32 is stuck in the interpreter
      } else if (ft.k === "tvar") {
        // abstract: cannot fold — dropped (instantiated readers see the
        // concrete type instead)
      } else {
        parts.push(e_atom(rd_call(c, ft, vs[i])));
      }
    });
    parts.push(num_lit_u32(c));
    return "    case " + ct.name + "{" + vs.join(", ") + "}:\n      " + e_at(num_combine(c, parts));
  });
  if (t.a.ctors.length === 0) {
    return "def " + name + "(" + arg + ": " + ty_str(t) + ") -> U32:\n  match " + arg + ":";
  }
  return "def " + name + "(" + arg + ": " + ty_str(t) + ") -> U32:\n  match " + arg + ":\n" + rows.join("\n");
}

// Builders
// --------
// def mk(+n: Nat, +s: U32) -> T — countdown structural builders per
// instantiation key; the Nat fuel is the first column so descent holds.

function builder_ensure(c: Ctx, t: Extract<T, { k: "adt" }>): string {
  const key = "mk:" + ty_str(t);
  const got = c.memo.get(key);
  if (got !== undefined) {
    return got;
  }
  const name = decl_name(c, "mk");
  c.memo.set(key, name);
  c = c.sub("mk");
  const a = t.a;
  const m = new Map<string, T>(a.tps.map((tp, i) => [tp.n, t.args[i]]));
  const qm = new Map<string, QT>(a.qps.map((n, i) => [n, t.qs[i]]));
  const is_self = (f: Field): boolean => {
    const ft = ty_sub(f.t, m, qm);
    return ft.k === "adt" && ft.a === a && ty_eq(ft, t);
  };
  const base = a.ctors.find((ct) => !ct.fields.some(is_self)) ?? a.ctors[0];
  const recs = a.ctors.filter((ct) => ct.fields.some(is_self));
  const rec = recs.length > 0 ? c.g.pick(recs) : base;
  const count = bind_name(c, []);
  const saltName = bind_name(c, [], [count]);
  const pred = bind_name(c, [], [count, saltName]);
  const senv: V[] = [{ name: saltName, ty: U32C, q: "many" }];
  const fld = (ct: Ctor, self: string): string[] =>
    ct.fields.map((f) => {
      if (is_self(f) && self !== "") {
        return self;
      }
      const ft = adt_field_ty(f.t, t, m, qm);
      return e_at(syn(c, ft, ct === base ? [] : senv, 0));
    });
  const brow = base.name + "{" + fld(base, "").join(", ") + "}";
  if (recs.length === 0) {
    c.push("def " + name + "(+" + count + ": Nat, +" + saltName + ": U32) -> " + ty_str(t) + ":\n  " + brow);
  } else {
    c.push("def " + name + "(+" + count + ": Nat, +" + saltName + ": U32) -> " + ty_str(t) + ":\n  match " + count + ":\n    case 0n:\n      "
      + brow + "\n    case 1n+" + pred + ":\n      " + rec.name + "{" + fld(rec, name + "(" + pred + ", (" + saltName + " * 3 + 7 : U32))").join(", ") + "}");
  }
  // a builder whose constructor holds k self fields makes k^n nodes: its
  // depth keeps a value under 128 nodes, the interpreter's budget (a
  // ternary one at depth 7 took the raw leg 45 s, the C leg 0.2 s)
  const k = rec.fields.filter(is_self).length;
  const depth = k <= 1 ? 8 + c.g.int(8) : 2 + c.g.int(Math.floor(Math.log2(128) / Math.log2(k)) - 1);
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 2, t: NATC }, { q: 2, t: U32C }], ret: t, mask: [depth, null] });
  return name;
}

// builder_call : a built value of an instantiated recursive adt
function builder_call(c: Ctx, t: Extract<T, { k: "adt" }>, env: V[], cap: number): E {
  const name = builder_ensure(c, t);
  const reg = c.defr.find((d) => d.name === name);
  const depth = Math.min(reg?.mask?.[0] ?? 8, cap);
  const fuel = "U32.to_nat((" + e_at(num_gen_u32(c, env, 1)) + " % " + String(Math.max(2, depth)) + " : U32))";
  return e_call(name, name + "(" + fuel + ", " + e_at(num_gen_u32(c, env, 0)) + ")");
}

// Transforms
// ----------
// def tf(x: T) -> T — same-ctor rebuilds: every arm re-emits the ctor it
// matched with mutated scalar fields and recursed self fields; the
// compiler's ctor-reuse (spares) triggers exactly here.

function tf_ensure(c: Ctx, t: Extract<T, { k: "adt" }>): string {
  const key = "tf:" + (c.pure ? "p:" : "x:") + ty_str(t);
  const got = c.memo.get(key);
  if (got !== undefined) {
    return got;
  }
  const name = decl_name(c, "tf");
  c.memo.set(key, name);
  c = c.sub("tf");
  const arg = bind_name(c, []);
  const a = t.a;
  const m = new Map<string, T>(a.tps.map((tp, i) => [tp.n, t.args[i]]));
  const qm = new Map<string, QT>(a.qps.map((n, i) => [n, t.qs[i]]));
  const rows = a.ctors.map((ct) => {
    const vs: string[] = [];
    for (const _ of ct.fields) vs.push(bind_name(c, [], vs));
    const args = ct.fields.map((f, i) => {
      if (f.q === 0) {
        return vs[i];
      }
      const ft = adt_field_ty(f.t, t, m, qm);
      if (ft.k === "adt" && ft.a === a && ty_eq(ft, t)) {
        return name + "(" + vs[i] + ")";
      }
      if (ft.k === "u32") {
        return e_at(e_bin(e_atom(vs[i]), c.g.pick(["+", "*", ".^."]), e_atom(String(1 + c.g.int(9)))));
      }
      if (ft.k === "f32" && !c.pure) {
        return e_at(e_bin(e_atom(vs[i]), c.g.pick(["+.", "*."]), num_lit_f32(c, false)));
      }
      if (ft.k === "nat") {
        return e_at(e_bin(e_atom(vs[i]), "+n", e_atom(String(1 + c.g.int(4)) + "n")));
      }
      if (ft.k === "bool") {
        return "Bool.not(" + vs[i] + ")";
      }
      if (ft.k === "str") {
        return e_at(e_bin(e_atom(vs[i]), "++", e_atom(str_lit(c, 1 + c.g.int(3)))));
      }
      return vs[i];
    });
    return "    case " + ct.name + "{" + vs.join(", ") + "}:\n      " + ct.name + "{" + args.join(", ") + "}";
  });
  const body = a.ctors.length === 0 ? "  match " + arg + ":" : "  match " + arg + ":\n" + rows.join("\n");
  c.push("def " + name + "(" + arg + ": " + ty_str(t) + ") -> " + ty_str(t) + ":\n" + body);
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 1, t }], ret: t });
  return name;
}

// Syn: values
// -----------
// syn(c, goal, env, fuel): produce a term of type goal. Productions per goal
// head: matching env vars, intro forms, unifying registry calls, builders.
// Results may be intro-headed (non-inferable) — callers placing them in an
// INFER position (a bare let) must annotate; every field/argument hole
// here is a checked position.

function syn(c: Ctx, goal: T, env: V[], fuel: number): E {
  if (fuel > 0 && !ty_open(goal) && c.g.chance(c.s.surface)) {
    const form = c.g.pick(c.base && !c.s.tmpl ? [0, 1, 2, 3, 4, 5] : c.base ? [0, 1, 3, 4, 5] : [0, 1, 4, 5]);
    const ty = ty_str(goal);
    const name = "sx" + String(c.uid());
    if (form === 0) {
      c.feat("syntax-ann");
      return e_atom("{" + e_at(syn(c, goal, env, fuel - 1)) + " : " + ty + "}");
    }
    if (form === 1) {
      c.feat("syntax-beta");
      const arg = e_at(syn(c, goal, env, fuel - 1));
      return e_atom("{(" + name + " => " + name + ") : (" + ty + ") -> (" + ty + ")}(" + arg + ")");
    }
    if (form === 2) {
      c.feat("syntax-rewrite");
      return e_atom("(%" + name + "@{{==} : {0n == 0n : Nat}} : " + ty + "; (" + e_at(syn(c, goal, env, fuel - 1)) + "))");
    }
    if (form === 3) {
      c.feat("syntax-erased-let");
      const rhs = e_at(syn(c, NATC, env.filter((v) => v.q === "many"), fuel - 1));
      const body = e_at(syn(c, goal, env, fuel - 1));
      return e_atom("{(" + name + " => -" + name + "e = {" + rhs + " : Nat}; " + body + ") : Unit -> (" + ty + ")}(Unit{})");
    }
    if (form === 4) {
      c.feat("syntax-ctor-let");
      const unbox = helper(c, "syntax-unbox", "sxunbox", (hc, fn) => {
        const valueName = bind_name(hc, [], ["T"]);
        const boxName = bind_name(hc, [], ["T", valueName]);
        return "type " + fn + "Box<-T: Type> is Type:\n  " + fn + "K{" + valueName + ": T}\n\n"
          + "def " + fn + "(-T: Type, " + boxName + ": " + fn + "Box<T>) -> T:\n  "
          + fn + "K{" + valueName + "} = " + boxName + "\n  " + valueName;
      });
      const value = e_at(syn(c, goal, env, fuel - 1));
      return e_atom(unbox + "(" + ty_grp(goal) + ", " + unbox + "K{" + value + "})");
    }
    c.feat("syntax-inline");
    const choices: Array<{ t: T; ctors: Ctor[] }> = [
      ...(c.base ? [
        { t: BOOLC, ctors: [{ name: "False", fields: [] }, { name: "True", fields: [] }] },
        { t: NATC, ctors: [{ name: "Zero", fields: [] }, { name: "Succ", fields: [{ q: 1 as BQ, t: NATC }] }] },
        { t: CMPC, ctors: ["LT", "EQ", "GT"].map((name) => ({ name, fields: [] })) },
      ] : []),
      ...c.adts.filter((a) => a.ctors.length > 0 && a.qps.length === 0 && a.tps.length === 0 && !a.ips?.length)
        .map((a) => ({ t: { k: "adt", a, qs: [], args: [] } as T, ctors: a.ctors })),
    ];
    const shape = c.g.pick(choices);
    c.feat("syntax-inline-" + shape.t.k);
    const scrut = e_at(syn(c, shape.t, env, fuel - 1));
    const branches: V[][] = [];
    const arm = (fields: Field[] = []): string => {
      const local = env.map((v) => ({ ...v }));
      branches.push(local);
      const vars = fields.map((f, i) => {
        const v = v_new(name + "f" + i, f.t, f.q === 2);
        if (f.q === 0) v.q = "dead";
        return v;
      });
      return vars.map((v) => v.name + " => ").join("")
        + e_at(syn(c, goal, local.concat(vars), fuel - 1));
    };
    const tail = c.g.chance(0.5);
    const ctors = tail ? shape.ctors.slice(0, -1) : shape.ctors;
    const arms = ctors.map((ct) => ct.name + ": " + arm(ct.fields))
      .concat(tail ? [name + " => " + arm()] : []).join("; ");
    if (tail) c.feat("syntax-inline-default");
    env.forEach((v, i) => {
      if (v.q === "lone" && branches.some((branch) => branch[i].q === "dead")) v.q = "dead";
    });
    return e_atom("{(\\{" + arms + "}) : (" + ty_str(shape.t) + ") -> (" + ty + ")}(" + scrut + ")");
  }
  const direct = env.filter((v) => v.q !== "dead" && ty_eq(v.ty, goal));
  const var_w = direct.length > 0 ? 30 : 0;
  const pick_var = (): E => e_atom(env_take(c.g.pick(direct)));
  const uni = (): E | null => fuel >= 1 ? syn_call_unify(c, goal, env, fuel) : null;
  // any goal may be a call of a registered def (a minted one or Base's)
  if (fuel >= 1 && c.g.chance(0.06)) {
    const got = uni();
    if (got !== null) {
      return got;
    }
  }
  switch (goal.k) {
    case "u32": return num_gen_u32(c, env, fuel);
    case "f32": return num_gen_f32(c, env, fuel);
    case "nat": return num_gen_nat(c, env, fuel);
    case "unit": return c.g.wpick<() => E>([
      [var_w, pick_var],
      [30, () => e_atom("Unit{}")],
    ])();
    case "bool": {
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [20, () => e_atom(c.g.pick(["True{}", "False{}"]))],
        [fuel > 0 ? 12 : 0, () => e_fn("U32." + c.g.pick(["is_eq", "is_ne", "is_lt", "is_le", "is_gt", "is_ge"]), num_gen_u32(c, env, fuel - 1), num_gen_u32(c, env, fuel - 1))],
        [fuel > 0 ? 3 : 0, () => e_fn("U32.is_zero", num_gen_u32(c, env, fuel - 1))],
        [fuel > 0 ? 5 : 0, () => e_bin(syn(c, BOOLC, env, fuel - 1), c.g.pick(["&&", "||"]), syn(c, BOOLC, env, fuel - 1))],
        [fuel > 0 ? 4 : 0, () => e_fn("Nat.is_lt", num_gen_nat(c, env, fuel - 1), num_gen_nat(c, env, fuel - 1))],
        [fuel > 0 ? 12 : 0, () => uni() ?? e_atom("True{}")],
        [fuel > 0 && !c.pure ? 5 : 0, () => e_bin(num_gen_f32(c, env, fuel - 1), c.g.pick(["==.", "!=.", "<.", "<=.", ">.", ">=."]), num_gen_f32(c, env, fuel - 1))],
      ])();
    }
    case "cmp": {
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [15, () => e_atom(c.g.pick(["LT{}", "EQ{}", "GT{}"]))],
        [fuel > 0 ? 15 : 0, () => e_fn("U32.cmp", num_gen_u32(c, env, fuel - 1), num_gen_u32(c, env, fuel - 1))],
        [fuel > 0 ? 6 : 0, () => e_fn("Nat.cmp", num_gen_nat(c, env, fuel - 1), num_gen_nat(c, env, fuel - 1))],
        [fuel > 0 ? 5 : 0, () => uni() ?? e_atom("EQ{}")],
      ])();
    }
    case "char": {
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [25, () => e_atom("'" + str_char(c) + "'")],
        [fuel > 0 ? 8 : 0, () => e_atom("Chr{" + e_at(e_bin(num_gen_u32(c, env, fuel - 1), "%", e_atom("55000"))) + "}")],
        [fuel > 0 ? 6 : 0, () => uni() ?? e_atom("'a'")],
      ])();
    }
    case "str": {
      c.feat("string-lit");
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [30, () => e_atom(str_lit(c, size_pick(c, c.g.int(9), c.pure ? 160 : 2000)))],
        [fuel > 0 ? 12 : 0, () => {
          c.feat("string-append");
          return e_bin(syn(c, STRC, env, fuel - 1), "++", syn(c, STRC, env, fuel - 1));
        }],
        [fuel > 0 ? 8 : 0, () => e_atom("SCon{" + e_at(syn(c, CHARC, env, fuel - 1)) + ", " + e_at(syn(c, STRC, env, fuel - 1)) + "}")],
        [fuel > 0 ? 6 : 0, () => e_fn("U32.show", num_gen_u32(c, env, fuel - 1))],
        [fuel > 0 ? 4 : 0, () => e_fn("Nat.show", num_gen_nat(c, env, fuel - 1))],
        [fuel > 0 && !c.pure ? 3 : 0, () => {
          c.feat("f32-show");
          return e_fn("F32.show", num_gen_f32(c, env, fuel - 1));
        }],
        [fuel >= 2 ? 4 : 0, () => def_new(c, goal, env, fuel - 1) ?? e_atom(str_lit(c, 3))],
        [fuel > 0 ? 10 : 0, () => uni() ?? e_atom(str_lit(c, 2))],
      ])();
    }
    case "set": {
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [10, () => e_atom("Set.new()")],
        [fuel > 0 ? 30 : 0, () => uni() ?? e_atom("Set.new()")],
      ])();
    }
    case "tvar": {
      if (direct.length > 0) {
        return pick_var();
      }
      const got = uni();
      if (got !== null) {
        return got;
      }
      throw new Error("no inhabitant for tvar " + goal.n);
    }
    case "eql": {
      if (!ty_inh(goal)) {
        throw new Error("no inhabitant: " + ty_str(goal));
      }
      c.feat("eql");
      return e_atom("{==}");
    }
    case "empty": throw new Error("no inhabitant: Empty");
    case "sig": {
      // a witness whose evidence has a value, then the evidence
      const ws = idx_type(goal.a) ? idx_lits(goal.a).filter((w) => ty_inh(ty_tsub(goal.b, goal.x, w))) : [];
      const w = idx_type(goal.a) ? (ws.length > 0 ? c.g.pick(ws) : null) : e_at(syn(c, goal.a, env, Math.max(0, fuel - 1)));
      if (w === null) {
        throw new Error("no inhabitant: " + ty_str(goal));
      }
      c.feat("sig-value");
      return e_atom("(" + w + ", " + e_at(syn(c, ty_tsub(goal.b, goal.x, w), env, Math.max(0, fuel - 1))) + ")");
    }
    case "tup": {
      const intro = (): E => e_atom("(" + e_at(syn(c, goal.a, env, Math.max(0, fuel - 1))) + ", " + e_at(syn(c, goal.b, env, Math.max(0, fuel - 1))) + ")");
      // an array read or measured: the array comes back beside the word
      const arrs = goal.a.k === "arr" && goal.b.k === "u32" && goal.q === 1 ? env.filter((v) => v.q !== "dead" && ty_eq(v.ty, goal.a)) : [];
      // a container beside its read comes back from the container's op
      const container = goal.a.k === "arr" || goal.a.k === "map" || goal.a.k === "set";
      const u32arr = goal.a.k === "arr" && goal.a.el.k === "u32" && goal.b.k === "u32";
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [30, intro],
        [container ? 60 : 8, () => uni() ?? intro()],
        // the index sugar a[i] reads a U32 array, any array term
        [u32arr && fuel > 0 ? 15 : 0, () => {
          c.feat("array-sugar");
          return e_atom(e_at(syn(c, goal.a, env, fuel - 1)) + "[" + num_gen_u32(c, env, 0).s + "]");
        }],
        [arrs.length > 0 ? 40 : 0, () => {
          c.feat("array-ops");
          const a = env_take(c.g.pick(arrs));
          const el = (goal.a as Extract<T, { k: "arr" }>).el;
          if (el.k !== "u32" || c.g.chance(0.3)) {
            return e_fn("Array.size", e_atom(ty_grp(el)), e_atom(a));
          }
          // the index sugar a[i] reads a U32 array
          c.feat("array-sugar");
          return c.g.chance(0.5) ? e_fn("Array.get", e_atom("U32"), e_atom(a), num_gen_u32(c, env, 0)) : e_atom(a + "[" + num_gen_u32(c, env, 0).s + "]");
        }],
        [fuel >= 2 ? 5 : 0, () => def_new(c, goal, env, fuel - 1) ?? intro()],
      ])();
    }
    case "map": {
      const mk = (): E => {
        c.feat("map-ops");
        const qs = qt_str(goal.q);
        const vt = ty_grp(goal.v);
        let acc = "Map.new(" + qs + ", " + vt + ")";
        const n = c.g.int(3);
        for (let i = 0; i < n; i++) {
          acc = "Map.set(" + qs + ", " + vt + ", " + acc + ", " + e_at(syn(c, STRC, env, 0)) + ", " + e_at(syn(c, goal.v, env, Math.max(0, fuel - 1))) + ")";
        }
        return e_atom(acc);
      };
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [30, mk],
      ])();
    }
    case "fun": {
      if (ty_refutable(goal.dom) && !ty_inh(goal.cod)) {
        // a clash refuted: the rewrite through a discriminating family
        return e_atom(refute_ensure(c, goal.dom as Extract<T, { k: "eql" }>));
      }
      if (ty_refutable(goal.dom)) {
        c.feat("absurd");
        const b = "y" + String(c.uid());
        return e_atom(b + " => Empty.absurd(" + ty_str(goal.cod) + ", " + refute_ensure(c, goal.dom as Extract<T, { k: "eql" }>) + "(" + b + "))");
      }
      const lam = (): E => {
        const b = bind_name(c, env);
        if (goal.q === 0) {
          // erased domain: the binder is dead inside
          const body = e_at(syn(c, goal.cod, env_bind(env, [b]), Math.min(Math.max(0, fuel - 1), 2)));
          return e_atom(b + " => " + body);
        }
        const bv = v_new(b, goal.dom, goal.q === 2);
        return e_atom(b + " => " + e_at(syn(c, goal.cod, env_bind(env, [b], [bv]), Math.min(fuel, 1))));
      };
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [35, lam],
        // partial application: a registry def missing EXACTLY its last
        // argument (deeper partials die in js_book)
        [fuel >= 1 && goal.q === 1 ? 15 : 0, () => {
          const cands = c.defr.filter((d) =>
            d.wip === undefined && d.qps.length === 0 && d.tps.length === 0 && (d.tm ?? 0) === 0 && d.ps.length >= 1
            && ty_eq(d.ps[d.ps.length - 1].t, goal.dom) && ty_eq(d.ret, goal.cod)
            && d.ps[d.ps.length - 1].q === 1
            && (d.mask?.[d.ps.length - 1] ?? null) === null);
          if (cands.length === 0) {
            return lam();
          }
          const d = c.g.pick(cands);
          // the front is drawn as a call's arguments are (an index chosen and
          // substituted into the parameters it types), short of the last
          const front = syn_def_args(c, { ...d, ps: d.ps.slice(0, -1) }, env, Math.max(0, fuel - 1));
          if (front === null) {
            return lam();
          }
          c.feat("partial");
          return e_atom(front.length > 0 ? d.name + "(" + front.join(", ") + ")" : d.name);
        }],
      ])();
    }
    case "adt": {
      const a = goal.a;
      const m = new Map<string, T>(a.tps.map((tp, i) => [tp.n, goal.args[i]]));
      const qm = new Map<string, QT>(a.qps.map((n, i) => [n, goal.qs[i]]));
      const is_self = (f: Field): boolean => {
        const ft = ty_sub(f.t, m, qm);
        return ft.k === "adt" && ft.a === a && ty_eq(ft, goal);
      };
      const intro = (): E => {
        const ctors = fuel <= 0 ? a.ctors.filter((ct) => !ct.fields.some(is_self)) : a.ctors;
        const ct = c.g.pick(ctors.length > 0 ? ctors : [a.ctors[0]]);
        const args = ct.fields.map((f) => {
          const ft = adt_field_ty(f.t, goal as Extract<T, { k: "adt" }>, m, qm);
          const sub = is_self(f) ? fuel - 1 : Math.min(fuel - 1, 1);
          // erased and + fields synthesize against a copy-only env: a dead
          // position never consumes, and a + argument is certified once —
          // the conservative shared env keeps the accounting sound
          const fenv = f.q === 1 ? env : env.filter((v) => v.q === "many");
          return e_at(syn(c, ft, fenv, Math.max(0, sub)));
        });
        return e_atom(ct.name + "{" + args.join(", ") + "}");
      };
      const is_list = a === BASE.List;
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [30, intro],
        [is_list && fuel > 0 ? 20 : 0, () => {
          c.feat("list-lit");
          const n = size_pick(c, c.g.int(5), c.pure ? 60 : 1500);
          const els: string[] = [];
          for (let i = 0; i < n; i++) {
            els.push(e_at(syn(c, goal.args[0], env, 0)));
          }
          // a chain a <> b <> [..] ends in a list literal; a lambda head
          // would swallow the chain as its body
          const el = goal.args[0].k === "app" ? fam_unfold(goal.args[0].f, goal.args[0].arg) ?? goal.args[0] : goal.args[0];
          const heads = n > 0 && el.k !== "fun" && goal.args[0].k !== "fun" && c.g.chance(0.3) ? 1 + c.g.int(Math.min(n, 3)) : 0;
          if (heads > 0) {
            c.feat("cons-lit");
          }
          return e_atom(els.slice(0, heads).map((e) => e + " <> ").join("") + "[" + els.slice(heads).join(", ") + "]");
        }],
        [c.base && a.rec && fuel > 0 && !ty_open(goal) ? 20 : 0, () => builder_call(c, goal as Extract<T, { k: "adt" }>, env, c.pure ? 10 : 16)],
        [!ty_open(goal) && fuel >= 1 ? 6 : 0, () => {
          c.feat("reuse");
          return e_atom(tf_ensure(c, goal as Extract<T, { k: "adt" }>) + "(" + e_at(syn(c, goal, env, Math.max(0, fuel - 1))) + ")");
        }],
        [8, () => uni() ?? intro()],
        [!ty_open(goal) && fuel >= 2 ? 5 : 0, () => def_new(c, goal, env, fuel - 1) ?? intro()],
      ])();
    }
    case "arr": {
      // arrays are linear: a fresh one, or one in scope written at an index
      const arrs = env.filter((v) => v.q !== "dead" && ty_eq(v.ty, goal));
      // a fresh one: Array.new, or a literal by depth ([v : T^d]) or by a
      // power-of-two slot count ([v : T*n]); its fill value is Data
      const fresh = (): E => {
        c.feat("array-ops");
        const d = size_pick(c, 1 + c.g.int(3), c.pure ? 6 : 12);
        const v = e_at(syn(c, goal.el, env.filter((w) => w.q === "many"), 0));
        const how = c.g.int(3);
        if (how > 0) {
          c.feat("array-lit");
        }
        return how === 0 ? e_fn("Array.new", e_atom(ty_grp(goal.el)), e_atom(String(d) + "n"), e_atom(v))
          : e_atom("[" + v + " : " + ty_grp(goal.el) + (how === 1 ? "^" + String(d) : "*" + String(2 ** d)) + "n]");
      };
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [ty_data(goal.el) ? 30 : 0, fresh],
        [arrs.length > 0 && fuel > 0 ? 30 : 0, () => {
          c.feat("array-write");
          const a = env_take(c.g.pick(arrs));
          const i = num_gen_u32(c, env, 0);
          const v = syn(c, goal.el, env, Math.max(0, fuel - 1));
          // the write sugar a[i] <- v sets a U32 array
          return goal.el.k === "u32" && c.g.chance(0.5) ? e_atom("(" + a + "[" + i.s + "] <- " + e_at(v) + ")")
            : e_fn("Array.set", e_atom(ty_grp(goal.el)), e_atom(a), i, v);
        }],
        [fuel > 0 ? 20 : 0, () => {
          const got = uni();
          if (got === null && !ty_data(goal.el)) {
            throw new Error("no array of " + ty_str(goal.el));
          }
          return got ?? fresh();
        }],
      ])();
    }
    case "io": {
      const pure = (): E => e_atom("IO.pure(" + ty_grp(goal.t) + ", " + e_at(syn(c, goal.t, env, Math.max(0, fuel - 1))) + ")");
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [25, pure],
        [fuel >= 1 ? 30 : 0, () => uni() ?? pure()],
        [fuel >= 2 ? 8 : 0, () => def_new(c, goal, env, fuel - 1) ?? pure()],
      ])();
    }
    case "app": {
      // a closed index unfolds to its arm; any index goes through the
      // family's index-generic def
      const arm = fam_unfold(goal.f, goal.arg);
      const total = fam_total(goal.f);
      const mkKey = "mk:fam:" + goal.f.name;
      const inMk = c.wip.has(mkKey);
      const decreasingMk = inMk && env.some((v) => v.name === goal.arg && v.dec === true && v.q !== "dead");
      const canMk = total && (!inMk || decreasingMk);
      if ((arm === null && !total && direct.length === 0) || (arm !== null && !ty_inh(arm))) {
        throw new Error("no inhabitant: " + ty_str(goal));
      }
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [arm !== null ? 20 : 0, () => {
          c.feat("fam-unfold");
          return syn(c, arm as T, env, Math.max(0, fuel - 1));
        }],
        [canMk ? 20 : 0, () => {
          const mk = inMk ? c.memo.get(mkKey) as string : mk_fam(c, goal.f);
          return e_call(mk, mk + "(" + goal.arg + ")");
        }],
        [arm !== null && !total ? 20 : 0, () => syn(c, arm as T, env, Math.max(0, fuel - 1))],
        [canMk ? 8 : 0, () => {
          const mk = inMk ? c.memo.get(mkKey) as string : mk_fam(c, goal.f);
          return uni() ?? e_call("", mk + "(" + goal.arg + ")");
        }],
        // a value moved across the reflexive index equation: the
        // hole-motive transport, Word.cast's shape
        [total && fuel > 0 ? 5 : 0, () => {
          c.feat("fam-cast");
          const cast = cast_ensure(c, goal.f);
          return e_call(cast, cast + "(" + goal.arg + ", " + goal.arg + ", {==}, " + e_at(syn(c, goal, env, fuel - 1)) + ")");
        }],
      ])();
    }
  }
}

function syn_def_arg(c: Ctx, d: DefR, i: number, t: T, env: V[], fuel: number): string {
  const mask = d.mask?.[i] ?? null;
  if (mask !== null && t.k === "nat") {
    return "U32.to_nat((" + e_at(num_gen_u32(c, env, fuel)) + " % " + String(mask) + " : U32))";
  }
  // a template's argument is closed: nothing in scope reaches it
  if (d.qps.length + d.tps.length + i < (d.tm ?? 0)) {
    c.feat("template-arg");
    const was = c.s.tmpl;
    c.s.tmpl = true;
    try {
      return e_at(syn(c, t, [], Math.max(1, fuel)));
    } finally {
      c.s.tmpl = was;
    }
  }
  const fenv = d.ps[i].q === 1 ? env : env.filter((v) => v.q === "many");
  const e = syn(c, t, fenv, fuel);
  if (mask !== null && t.k === "u32") {
    return e_at(e_bin(e, "%", e_atom(String(mask))));
  }
  return e_at(e);
}

// syn_def_args : the value arguments in order; an index parameter that
// later parameters depend on takes a literal under which every dependent
// type has a value (null when none does)
function syn_def_args(c: Ctx, d: DefR, env: V[], fuel: number): string[] | null {
  const args: string[] = [];
  let ps = d.ps.slice();
  if (d.wip !== undefined && c.s.wips[c.s.wips.length - 1]?.name !== d.name) {
    return null;
  }
  const subs = d.wip === undefined ? null : d.wip.subs.filter((v) => v.q !== "dead" && env.includes(v));
  if (subs !== null && subs.length === 0) {
    return null;
  }
  for (let i = 0; i < ps.length; i++) {
    const p = ps[i];
    if (subs !== null && i < (d.wip as { col: number }).col) {
      // the checker takes the first changed live argument as the one
      // that must shrink: an earlier one is the parameter itself (or the
      // variable that re-bound it), or there is no self-call here
      const pn = d.ps[i].n as string;
      if (p.q === 0) {
        if (env.some((v) => v.name === pn)) {
          return null;
        }
        args.push(pn);
        continue;
      }
      const own = (d.wip as { ps: V[] }).ps[i];
      const same = env.find((v) => v.q !== "dead" && (v === own || v.of === own));
      if (same === undefined) {
        return null;
      }
      args.push(env_take(same));
      continue;
    }
    if (subs !== null && i === d.wip?.col) {
      const sub = c.g.pick(subs);
      d.wip.subs = d.wip.subs.filter((v) => v !== sub);
      d.wip.calls++;
      args.push(env_take(sub));
      continue;
    }
    const deps = p.n === undefined || p.dep === false ? [] : ps.slice(i + 1).filter((q) => new RegExp("\\b" + (p.n as string) + "\\b").test(ty_str(q.t)));
    if (deps.length > 0 && idx_type(p.t)) {
      const ok = idx_lits(p.t).filter((w) => deps.every((q) => ty_inh(ty_tsub(q.t, p.n as string, w))));
      if (ok.length === 0) {
        return null;
      }
      const w = c.g.pick(ok);
      c.feat("dep-call");
      args.push(w);
      ps = ps.map((q, j) => j > i ? { ...q, t: ty_tsub(q.t, p.n as string, w) } : q);
      continue;
    }
    if (!ty_inh(p.t)) {
      return null;
    }
    try {
      args.push(syn_def_arg(c, { ...d, ps }, i, p.t, env, fuel));
    } catch {
      return null;
    }
  }
  // twins: one reusable value passed as two arguments
  if (new Set(args).size < args.length && args.some((a, j) => /^[A-Za-z_]\w*$/.test(a) && args.indexOf(a) !== j)) {
    c.feat("twins");
  }
  return args;
}

// syn_call_unify : call any registered def whose return type unifies with
// the goal — quantity variables and type variables both bind; leftovers
// draw fresh (&1/&2, fitting types).
function syn_call_unify(c: Ctx, goal: T, env: V[], fuel: number): E | null {
  const cands: Array<{ d: DefR; m: Map<string, T>; qm: Map<string, QT> }> = [];
  const shadowed = new Set(env.filter((v) => v.q !== "dead").map((v) => v.name));
  for (const d of c.defr) {
    if (shadowed.has(d.name)) continue;
    const m = new Map<string, T>();
    const qm = new Map<string, QT>();
    if (ty_unify(d.ret, goal, m, qm)) {
      cands.push({ d, m, qm });
    }
  }
  if (cands.length === 0) {
    return null;
  }
  // Base's defs and the program's own share the draw evenly
  const own = cands.filter((x) => x.d.base !== true);
  const base = cands.filter((x) => x.d.base === true);
  const { d, m, qm } = c.g.pick(own.length === 0 ? base : base.length === 0 || c.g.chance(0.5) ? own : base);
  for (const qp of d.qps) {
    if (!qm.has(qp)) {
      qm.set(qp, c.g.chance(0.5) ? Q1 : Q2);
    }
  }
  for (const tp of d.tps) {
    if (!m.has(tp.n)) {
      m.set(tp.n, syn_ty(c, 1, qt_sub(tp.q, qm), [], []));
    }
  }
  // a + parameter must instantiate at a concretely-Data type
  const ps = d.ps.map((p) => ({ ...p, t: ty_sub(p.t, m, qm) }));
  if (ps.some((p) => (p.q === 2 && !ty_data(p.t)) || ty_open(p.t))) {
    return null;
  }
  if (d.base === true) {
    c.feat("base:" + d.name);
  } else if (d.qps.length > 0) {
    c.feat("qpoly-call");
  } else if (d.tps.length > 0) {
    c.feat("generic-call");
  }
  const args = syn_def_args(c, { ...d, ps }, env, Math.max(0, fuel - 1));
  if (args === null) {
    return null;
  }
  const head = (d.hdr ?? [...d.qps, ...d.tps.map((tp) => tp.n)])
    .map((n) => d.qps.includes(n) ? qt_str(qm.get(n) as QT) : ty_grp(m.get(n) as T));
  if ((d.tm ?? 0) > 0) {
    c.feat("template");
  }
  const all = head.concat(args).map((a, i) => i < (d.tm ?? 0) ? "~" + a : a);
  return e_call(d.name, d.name + "(" + all.join(", ") + ")");
}

// Defs
// ----
// One production mints every def with control flow. def_new(c, goal, env,
// fuel) draws the parameters, matches on some of them at the head of the
// body (a decision tree over their constructors, a variable row where an
// arm does not care, a nested match on a row's last binder) and
// synthesizes each leaf against the goal with the row's binders in scope.
// The def sits in the registry while its leaves are drawn, callable only
// with a sub-field bound by a constructor pattern at its decreasing column
// (a variable row binds the whole value, which does not shrink), each such
// sub-field once per leaf. So a countdown loop, a fold, a tree recursion,
// a state record rebuilt each step, a tuple-returning walk and an IO loop
// are one production at different goals and parameter types; a monadic
// goal (IO, Maybe, Result) may take a do-block leaf. Loop-flavoured defs
// end every recursive leaf in a tail self-call and run long.

type Split = { pat: string; vs: V[]; subs: V[]; wild: boolean };
type DefSt = { loop: boolean; dec: V | null; fuel: number; leaves: number; cap: number };

function col_matchable(t: T): boolean {
  switch (t.k) {
    case "nat": case "bool": case "cmp": case "unit": case "char": case "str": case "tup": return true;
    case "adt": return t.a.ctors.length > 0 && !ty_open(t);
    default: return false;
  }
}

// col_wild : a variable row over one column, the whole value re-bound
function col_wild(c: Ctx, v: V, env: V[], taken: string[] = []): Split {
  const n = bind_name(c, env, taken);
  return { pat: n, vs: [{ ...v_new(n, v.ty, v.q === "many"), of: v.of ?? v }], subs: [], wild: true };
}

// col_splits : the constructor rows one column splits into; a Nat may
// peel or table with a variable row last, a List<U32> may take literal
// patterns, a datatype's rows come from adt_row
function col_splits(c: Ctx, v: V, env: V[], desc: boolean, bound: string[]): Split[] {
  const t = v.ty;
  const many = v.q === "many";
  const fresh = (desc ? env.map((w) => w.name) : []).concat(bound);
  const senv = env.filter((w) => !bound.includes(w.name));
  const bind = (taken: string[], ty: T): V => v_new(bind_name(c, senv, taken.concat(fresh)), ty, many);
  const row = (pat: (vs: V[]) => string, vs: V[], subs: V[] = []): Split => ({ pat: pat(vs), vs, subs, wild: false });
  switch (t.k) {
    case "nat": {
      const style = c.g.wpick<string>([[6, "succ"], [2, "peel"], [2, "table"]]);
      c.feat("match-nat");
      if (style === "succ") {
        const p = bind([], NATC);
        return [row(() => "0n", []), row((vs) => "1n+" + vs[0].name, [p], [p])];
      }
      if (style === "peel") {
        c.feat("peel");
        const p = bind([], NATC);
        return [row((vs) => String(2 + c.g.int(4)) + "n+" + vs[0].name, [p], [p]), col_wild(c, v, senv, fresh)];
      }
      c.feat("nat-table");
      const n = 2 + c.g.int(size_pick(c, 4, 40));
      return Array.from({ length: n }, (_, i) => row(() => String(i) + "n", [])).concat([col_wild(c, v, senv, fresh)]);
    }
    case "bool":
      c.feat("match-bool");
      return [row(() => "False{}", []), row(() => "True{}", [])];
    case "cmp":
      c.feat("match-cmp");
      return ["LT{}", "EQ{}", "GT{}"].map((p) => row(() => p, []));
    case "unit":
      return [row(() => "Unit{}", [])];
    case "char": {
      c.feat("match-char");
      const k = bind([], U32C);
      return [row((vs) => "Chr{" + vs[0].name + "}", [k])];
    }
    case "str": {
      c.feat("match-str");
      const h = bind([], CHARC);
      const tl = bind([h.name], STRC);
      return [row(() => "SNil{}", []), row((vs) => "SCon{" + vs[0].name + ", " + vs[1].name + "}", [h, tl], [tl])];
    }
    case "tup": {
      c.feat("match-tup");
      const a = bind([], t.a);
      const b = bind([a.name], t.b);
      return [row((vs) => "(" + vs[0].name + ", " + vs[1].name + ")", [a, b])];
    }
    case "adt": {
      c.feat("match-adt");
      if (t.a === BASE.List && t.args[0].k === "u32" && t.qs[0].k === "q" && t.qs[0].q === 2 && c.g.chance(0.3)) {
        c.feat("list-pat");
        const u = bind([], U32C);
        const w = bind([u.name], U32C);
        u.q = "many";
        return [row((vs) => "[+" + vs[0].name + ", " + vs[1].name + "]", [u, w]), row(() => "[]", []), { pat: "_", vs: [], subs: [], wild: true }];
      }
      return t.a.ctors.map((ct) => {
        const r = adt_row(c, t, ct, many, desc ? [] : senv);
        const erased = r.names.map((nm) => nm.replace(/^\+/, "")).filter((nm) => !r.vs.some((w) => w.name === nm))
          .map((nm): V => ({ name: nm, ty: U32C, q: "dead" }));
        return { pat: r.pat, vs: r.vs.concat(erased), subs: r.vs.filter((f) => ty_eq(f.ty, t)), wild: false };
      });
    }
    default:
      return [col_wild(c, v, senv, fresh)];
  }
}

// match_text : a match over columns (parameters, or one bound field), its
// rows the decision tree over their splits, each leaf drawn under the
// row's binders with the sub-fields the self-call may descend on
function match_text(c: Ctx, d: DefR, goal: T, cols: V[], env: V[], subs: V[], ind: string, depth: number, st: DefSt): string {
  const rows: string[] = [];
  const bound: V[] = [];
  const go = (i: number, pats: string[], env2: V[], subs2: V[], last: V | null): void => {
    if (i === cols.length) {
      rows.push(ind + "  case " + pats.join(", ") + ":\n" + leaf_text(c, d, goal, env2, subs2, last, ind + "    ", depth, st));
      return;
    }
    void last;
    const col = cols[i];
    const wild = !col_matchable(col.ty) || st.leaves + rows.length > st.cap || (cols.length > 1 && c.g.chance(0.25));
    if (wild && col_matchable(col.ty)) {
      c.feat("wild");
    }
    // a sub-field descends when its column is the decreasing one, or a
    // binder that descends (a nested match on it)
    const desc = col.dec === true || col === st.dec;
    const row = pats.length === 0 ? [] : env2.filter((w) => w.of !== undefined || bound.includes(w)).map((w) => w.name);
    const splits = wild ? [col_wild(c, col, env2, row)] : col_splits(c, col, env2, desc, row);
    for (const s of splits) {
      if (desc) {
        s.subs.forEach((w) => { w.dec = true; });
      }
      const env3 = env_bind(env2, s.vs.map((w) => w.name), s.vs);
      bound.push(...s.vs);
      // a nested match may scrutinize the last column's last binder only
      const lastHere = i === cols.length - 1 && !s.wild ? (s.vs.length > 0 ? s.vs[s.vs.length - 1] : null) : null;
      go(i + 1, pats.concat([s.pat]), env3, desc ? subs2.concat(s.subs) : subs2, lastHere);
    }
  };
  if (cols.length > 1) {
    c.feat("match-multi");
  }
  for (const v of cols) {
    if (v.q === "lone") {
      v.q = "dead";
    }
  }
  go(0, [], env.filter((v) => v.q !== "dead"), subs.filter((v) => v.q !== "dead"), null);
  return ind + "match " + cols.map((v) => v.name).join(", ") + ":\n" + rows.join("\n");
}

// leaf_text : a row's body: maybe a nested match on the row's last binder,
// else lines — a lone Data binder copied reusable (+x2 = x), two
// self-calls in a parallel let — and the final value: a tail self-call in
// a loop, a do-block at a monadic goal, or any term of the goal
function leaf_text(c: Ctx, d: DefR, goal: T, env: V[], subs: V[], last: V | null, ind: string, depth: number, st: DefSt): string {
  st.leaves++;
  if (last !== null && last.q === "lone" && depth < 2 && col_matchable(last.ty) && c.g.chance(0.3)) {
    c.feat("match-nest");
    return match_text(c, d, goal, [last], env, subs, ind, depth + 1, st);
  }
  const wip = d.wip as { col: number; ps: V[]; subs: V[]; calls: number };
  const lines: string[] = [];
  for (const v of env.filter((w) => w.q === "lone" && w.of === undefined && ty_data(w.ty))) {
    if (env.includes(v) && c.g.chance(0.12)) {
      c.feat("plus-rebind");
      const n = bind_name(c, env);
      lines.push("+" + n + " = {" + env_take(v) + " : " + ty_str(v.ty) + "}");
      env = env_bind(env, [n], [v_new(n, v.ty, true)]);
    }
  }
  wip.subs = subs.filter((v) => v.q !== "dead");
  // self-call : the decreasing argument drawn here, the others under an
  // empty sub list (no self-call nests inside an argument)
  const self_call = (fuel: number): string | null => {
    const cands = wip.subs.filter((v) => v.q !== "dead");
    if (cands.length === 0) {
      return null;
    }
    const s = c.g.pick(cands);
    const saved = wip.subs.filter((v) => v !== s);
    wip.subs = [s];
    const args = syn_def_args(c, d, env, fuel);
    wip.subs = saved;
    return args === null ? null : d.name + "(" + args.join(", ") + ")";
  };
  if (goal.k !== "io" && wip.subs.length >= 2 && c.g.chance(0.3)) {
    const a = self_call(1);
    const b = self_call(1);
    if (a !== null && b !== null) {
      c.feat("fork");
      const plus = ty_data(goal) && c.g.chance(0.3);
      const x = bind_name(c, env);
      const y = bind_name(c, env, [x]);
      lines.push((plus ? "+" : "") + x + " " + (plus ? "+" : "") + y + " = " + a.replace("(", gpu_mark(c) + "(") + " " + b.replace("(", gpu_mark(c) + "("));
      env = env_bind(env, [x, y], [v_new(x, goal, plus), v_new(y, goal, plus)]);
    }
  }
  let fin: string | null = null;
  if (st.loop && wip.subs.some((v) => v.q !== "dead")) {
    fin = self_call(1);
  }
  if (fin === null && (goal.k === "io" || (goal.k === "adt" && (goal.a === BASE.Maybe || goal.a === BASE.Result))) && (goal.k === "io" || c.g.chance(0.5))) {
    fin = do_text(c, goal, env, ind, st.fuel);
  }
  if (fin === null) {
    fin = e_at(syn(c, goal, env, st.fuel));
  }
  return lines.concat([fin]).map((l, i) => (i === 0 ? ind : "\n" + ind) + l).join("");
}

// do_text : a do-block at a monadic goal — binds drawn as values of the
// monad at a small element type (the def itself among them at IO, so an
// IO walk recurses from inside its block), a do let, and the final action
function do_text(c: Ctx, goal: T, env: V[], ind: string, fuel: number): string {
  const io = goal.k === "io";
  const inner = io ? (goal as Extract<T, { k: "io" }>).t : (goal as Extract<T, { k: "adt" }>).args[(goal as Extract<T, { k: "adt" }>).args.length - 1];
  const g = goal as Extract<T, { k: "adt" }>;
  const head = io ? "do IO<" + ty_str(inner) + ">:" : "do " + g.a.name + "<" + g.qs.map(qt_str).concat(g.args.map(ty_grp)).join(", ") + ">:";
  c.feat(io ? "do-io" : (goal as Extract<T, { k: "adt" }>).a === BASE.Maybe ? "do-maybe" : "do-result");
  const lines: string[] = [];
  const n = c.g.int(3);
  for (let i = 0; i < n; i++) {
    const el = c.g.pick([U32C, U32C, BOOLC, UNITC]);
    const act: T = io ? { k: "io", t: el } : { ...(goal as Extract<T, { k: "adt" }>), args: (goal as Extract<T, { k: "adt" }>).args.slice(0, -1).concat([el]) };
    const plus = ty_data(el) && c.g.chance(0.3);
    if (plus) {
      c.feat("plus-do");
    }
    const x = bind_name(c, env);
    lines.push((plus ? "+" : "") + x + " : " + ty_str(el) + " <- " + e_at(syn(c, act, env, Math.max(0, fuel - 1))));
    env = env_bind(env, [x], [v_new(x, el, plus)]);
  }
  if (c.g.chance(0.3)) {
    c.feat("do-let");
    const z = bind_name(c, env);
    lines.push("+" + z + " : U32 = " + e_at(num_gen_u32(c, env, 1)));
    env = env_bind(env, [z], [v_new(z, U32C, true)]);
  }
  const fin = io ? e_at(syn(c, goal, env, fuel)) : "return " + e_at(syn(c, inner, env, fuel));
  return head + lines.concat([fin]).map((l) => "\n" + ind + "  " + l).join("");
}

function def_new(c: Ctx, goal: T, env: V[], fuel: number): E | null {
  if (goal.k === "eql" || ty_open(goal) || c.mints >= 12) {
    return null;
  }
  c.mints++;
  c.feat("def");
  c = c.sub("def");
  const name = decl_name(c, "fn");
  const nps = Math.min(10, c.g.decay(0.55));
  const ps: Array<{ q: BQ; t: T; n: string; dep?: boolean }> = [];
  const names: string[] = [];
  for (let i = 0; i < nps; i++) {
    const pn = bind_name(c, [], names);
    names.push(pn);
    // evidence about an earlier index parameter: a family at it (the def
    // is then callable at the indices whose arm has a value)
    const idxps = ps.filter((p) => p.dep === true);
    const fams = idxps.length > 0 ? c.fams.filter((f) => f.done && idxps.some((p) => ty_eq(p.t, f.idx))) : [];
    if (fams.length > 0 && c.g.chance(0.35)) {
      c.feat("dep-param");
      const f = c.g.pick(fams);
      const on = c.g.pick(idxps.filter((p) => ty_eq(p.t, f.idx)));
      ps.push({ q: 1, t: { k: "app", f, arg: on.n }, n: pn, dep: false });
      continue;
    }
    // a parameter of the goal's own type: the state a loop rebuilds
    const state = i === 0 && (goal.k === "adt" || goal.k === "tup" || goal.k === "str" || goal.k === "arr") && c.g.chance(0.35);
    if (state) {
      c.feat("state");
    }
    const t = state ? goal : syn_ty(c, 1, Q0, [], []);
    const q: BQ = c.g.wpick<BQ>([[7, 1], [2, 0], [ty_data(t) ? 3 : 0, 2]]);
    ps.push({ q: idx_type(t) && q !== 0 ? 2 : q, t, n: pn, dep: idx_type(t) && q !== 0 });
  }
  if (ps.some((p) => p.q === 0)) {
    c.feat("erased-param");
  }
  const penv = ps.map((p) => {
    const v = v_new(p.n, p.t, p.q === 2);
    if (p.q === 0) {
      v.q = "dead";
    }
    return v;
  });
  // the scrutinees: live matchable parameters, in order, at most three
  const depended = new Set(ps.filter((p) => p.t.k === "app").map((p) => (p.t as Extract<T, { k: "app" }>).arg));
  const cols = penv.filter((v) => v.q !== "dead" && !depended.has(v.name) && col_matchable(v.ty) && c.g.chance(0.6)).slice(0, 3);
  const descends = (t: T): boolean => t.k === "nat" || t.k === "str" || (t.k === "adt" && t.a.rec);
  const decs = cols.filter((v) => descends(v.ty));
  const dec = decs.length > 0 && c.g.chance(0.85) ? c.g.pick(decs) : null;
  const col = dec === null ? -1 : penv.indexOf(dec);
  const loop = dec !== null && c.g.chance(0.4);
  const mask: Array<number | null> = ps.map((p, i) => i === col && p.t.k === "nat"
    ? (loop ? (c.pure ? 2 + c.g.int(size_pick(c, 90, 900)) : size_pick(c, 200 + c.g.int(4000), 200000)) : 4 + c.g.int(8))
    : null);
  const d: DefR = { name, qps: [], tps: [], ps, ret: goal, mask, wip: { col, ps: penv, subs: [], calls: 0 } };
  c.defr.push(d);
  c.s.wips.push(d);
  const st: DefSt = { loop, dec, fuel: 2, leaves: 0, cap: 24 };
  let body: string;
  try {
    body = cols.length > 0
      ? match_text(c, d, goal, cols, penv.filter((v) => v.q !== "dead"), [], "  ", 0, st)
      : leaf_text(c, d, goal, penv.filter((v) => v.q !== "dead"), [], null, "  ", 0, st);
  } catch {
    c.defr.splice(c.defr.indexOf(d), 1);
    c.s.wips.pop();
    c.mints--;
    return null;
  }
  c.s.wips.pop();
  const calls = (d.wip as { calls: number }).calls;
  delete d.wip;
  if (calls > 0) {
    c.feat("rec");
    c.feat("rec-" + (dec as V).ty.k);
    if (loop) {
      c.feat("loop");
    }
  }
  if (goal.k === "io") {
    c.feat("io-def");
    if (calls > 0) {
      c.feat("rec-io");
    }
  }
  if (goal.k === "tup") {
    c.feat("ret-tup");
  }
  if (ps.some((p) => p.t.k === "arr")) {
    c.feat("arr-param");
  }
  const params = ps.map((p) => bq_prefix(p.q) + p.n + ": " + ty_top(p.t));
  if (c.g.chance(0.15)) {
    c.feat("assert-def");
    // a law telescope: a pair parameter over an index may read as `for x: A
    // where B`, the def then opening the pair; a pair result as `exs`
    const rows: string[] = [];
    for (const p of ps) {
      if (p.t.k === "sig" && p.q === 1 && idx_type(p.t.a) && c.g.chance(0.6)) {
        c.feat("law-where");
        rows.push("  for " + p.n + ": " + ty_top(p.t.a) + " where " + ty_str(ty_tsub(p.t.b, p.t.x, p.n)));
        continue;
      }
      rows.push("  for " + bq_prefix(p.q) + p.n + ": " + ty_top(p.t));
    }
    let claim = ty_top(goal);
    if (goal.k === "sig" && c.g.chance(0.6)) {
      c.feat("law-exs");
      rows.push("  exs " + goal.x + ": " + ty_top(goal.a));
      claim = ty_top(goal.b);
    }
    c.push("law " + name + ":\n" + rows.join("\n") + "\n  " + claim + "\n\ndef " + name + "(" + ps.map((p) => p.n).join(", ") + "):\n" + body);
  } else {
    const unsafe = c.g.chance(0.04);
    if (unsafe) {
      c.feat("unsafe");
    }
    c.push((unsafe ? "@unsafe\n" : "") + "def " + name + "(" + params.join(", ") + ") -> " + ty_str(goal) + ":\n" + body);
  }
  const args = syn_def_args(c, d, env, Math.min(fuel, 1));
  if (args === null) {
    return null;
  }
  return e_call(name, name + "(" + args.join(", ") + ")");
}

// def_call : a minted def's call as a statement value, or a registry call
function def_call(c: Ctx, goal: T, env: V[], fuel: number): E | null {
  return def_new(c, goal, env, fuel) ?? syn_call_unify(c, goal, env, fuel);
}

// generic_mint : a quantity- and type-polymorphic def. The tvar-typed
// parameter is strictly linear inside (its kind is abstract, so + cannot
// form); recursion over List<a, A> descends past the erased columns.
function generic_mint(c: Ctx): void {
  c.feat("qpoly-def");
  c = c.sub("generic");
  const name = decl_name(c, "g");
  const nq = c.g.chance(0.3) ? 2 : 1;
  const qps = ["qa", "qb"].slice(0, nq);
  const qv = (n: string): QT => ({ k: "qv", n });
  const tps = [{ n: "A", q: qv(qps[0]) }];
  if (nq === 2 && c.g.chance(0.5)) {
    tps.push({ n: "B", q: qv(qps[1]) });
  }
  const tA: T = { k: "tvar", n: "A", q: qv(qps[0]) };
  const shape = c.g.wpick<string>([[4, "swap"], [4, "len"], [3, "wrap"], [3, "pick"]]);
  if (shape === "len") {
    // structural length over List<a, A>, dropping elements (affine)
    const lt: T = t_list(qv(qps[0]), tA);
    c.push("def " + name + "(" + qps[0] + ", -A: Kind(" + qps[0] + "), l: " + ty_str(lt) + ", +acc: U32) -> U32:\n"
      + "  match l:\n    case Nil{}:\n      acc\n    case Con{h, t}:\n      " + name + "(" + qps[0] + ", A, t, (acc + " + String(1 + c.g.int(9)) + " : U32))");
    c.defr.push({ name, qps: [qps[0]], tps: [{ n: "A", q: qv(qps[0]) }], ps: [{ q: 1, t: lt }, { q: 2, t: U32C }], ret: U32C });
    return;
  }
  if (shape === "wrap") {
    // wrap into Maybe at the same quantity
    const mt: T = t_maybe(qv(qps[0]), tA);
    c.push("def " + name + "(" + qps[0] + ", -A: Kind(" + qps[0] + "), x: A) -> " + ty_str(mt) + ":\n  Some{x}");
    c.defr.push({ name, qps: [qps[0]], tps: [{ n: "A", q: qv(qps[0]) }], ps: [{ q: 1, t: tA }], ret: mt });
    return;
  }
  if (shape === "pick") {
    // eliminate a Maybe with a default: quantity-polymorphic match
    const mt: T = t_maybe(qv(qps[0]), tA);
    c.push("def " + name + "(" + qps[0] + ", -A: Kind(" + qps[0] + "), m: " + ty_str(mt) + ", d: A) -> A:\n"
      + "  match m:\n    case None{}:\n      d\n    case Some{v}:\n      v");
    c.defr.push({ name, qps: [qps[0]], tps: [{ n: "A", q: qv(qps[0]) }], ps: [{ q: 1, t: mt }, { q: 1, t: tA }], ret: tA });
    return;
  }
  // swap : Either at a meet of two quantity variables
  const tB: T = tps.length > 1 ? { k: "tvar", n: "B", q: qv(qps[1]) } : U32C;
  const qb: QT = nq === 2 ? qv(qps[1]) : Q2;
  const et: T = { k: "adt", a: BASE.Either, qs: [qv(qps[0]), qb], args: [tA, tB] };
  const rt: T = { k: "adt", a: BASE.Either, qs: [qb, qv(qps[0])], args: [tB, tA] };
  const head = qps.slice(0, nq).concat(tps.map((tp) => "-" + tp.n + ": Kind(" + qt_bare(tp.q) + ")"));
  c.push("def " + name + "(" + head.join(", ") + ", e: " + ty_str(et) + ") -> " + ty_str(rt) + ":\n"
    + "  match e:\n    case Inl{v}:\n      Inr{v}\n    case Inr{v}:\n      Inl{v}");
  c.defr.push({ name, qps: qps.slice(0, nq), tps, ps: [{ q: 1, t: et }], ret: rt });
}

// Statements
// ----------
// A result or extra def is a run of statements, each binding names the fold
// reads. Three productions make them: a value of any type, read to a U32
// through its reader (a U32 is its own reading, a call may carry a `!`
// mark); a parallel let, the one fork shape; and a proof, an equation
// rewritten on or left bound. Arrays, maps, sets, floats, shared values and
// calls are values of some type: Base's own Array.*, Map.*, Set.* and List.*
// defs reach them through the registry, so no container has a kit of its
// own.

type Line = { text: string; binds: string[]; vars: V[] };

// let_value : a value of a drawn type bound (annotated: an intro-headed
// value does not infer in a bare let) and read; a Data value may stay in
// scope under a + binder, read twice, or be rebuilt through a same-ctor
// transform first
function let_value(c: Ctx, env: V[]): Line {
  const t = c.g.wpick<() => T>([
    [c.base ? 30 : 0, () => U32C],
    [c.base && !c.pure ? 30 : 0, () => F32C],
    [40, () => syn_ty(c, size_pick(c, 2, 5), Q0, [], [])],
  ])();
  const x = bind_name(c, env);
  if (t.k === "u32") {
    const e = c.g.chance(0.4) ? def_call(c, U32C, env, 2) ?? num_gen_u32(c, env, 2) : num_gen_u32(c, env, 2 + c.g.int(3));
    const bang = e.head !== undefined && e.s.startsWith(e.head + "(") ? gpu_mark(c) : "";
    const s = bang === "" ? e : e_atom((e.head as string) + bang + e.s.slice((e.head as string).length));
    const keep = bind_keep(c);
    return { text: (keep ? "+" : "") + x + " = " + u32_rhs(s), binds: [x], vars: keep ? [v_new(x, U32C, true)] : [] };
  }
  c.feat(t.k === "fun" ? "clo" : t.k === "f32" ? "f32" : "value");
  const y = bind_name(c, env, [x]);
  const val = c.g.chance(0.3) ? def_new(c, t, env, 2) ?? syn(c, t, env, 2) : syn(c, t, env, 2 + c.g.int(2));
  const keep = ty_data(t) && c.g.chance(0.4);
  const kind = c.g.wpick<string>([
    [50, "plain"],
    [t.k === "adt" && !ty_open(t) ? 20 : 0, "tf"],
    [keep ? 15 : 0, "twice"],
  ]);
  const rd = rd_ensure(c, t);
  const ykeep = bind_keep(c);
  const lines: string[] = [(keep ? "+" : "") + x + " = {" + val.s + " : " + ty_top(t) + "}"];
  if (kind === "tf") {
    c.feat("reuse");
    lines.push((ykeep ? "+" : "") + y + " = " + rd + "(" + tf_ensure(c, t as Extract<T, { k: "adt" }>) + "(" + x + "))");
  } else if (kind === "twice") {
    c.feat("dup");
    lines.push((ykeep ? "+" : "") + y + " = (" + rd + "(" + x + ") + " + rd + "(" + x + ") : U32)");
  } else {
    lines.push((ykeep ? "+" : "") + y + " = " + rd + "(" + x + ")");
  }
  const vars = ykeep ? [v_new(y, U32C, true)] : [];
  if (keep && kind !== "twice") {
    vars.push(v_new(x, t, true));
  }
  return { text: lines.join("\n  "), binds: [y], vars };
}

// Proofs
// ------
// let_proof : an equation bound by a proof term, then rewritten on with a
// constant motive (%x : U32;) or left bound. The proof grammar composes:
// reflexivity over a side drawn from reusable binders only (it is written
// twice), Base's U32.add_comm, a minted theorem (a Nat clone's shift law
// proved by induction), and Equal's sym, cong and trans over any of them.

type Prf = { s: string; t: string; a: string; b: string; ap?: (x: string) => string };

// theorem : a minted Nat clone, an op on it (op(z, b) = S^k(b), op(s{p}, b)
// = S^m(op(p, b))) and its shift law op(a, S{b}) == S{op(a, b)}, proved by
// induction, its inductive arm rewriting with the hypothesis
function theorem(c: Ctx): Prf {
  c.feat("thm");
  const id = String(c.uid());
  const N = "Nt" + id;
  const Z = N + "z";
  const S = N + "s";
  c.push("type " + N + " is Data:\n  " + Z + "{}\n  " + S + "{p: " + N + "}");
  const k = c.g.int(3);
  const m = 1 + c.g.int(2);
  const wrap = (n: number, x: string): string => {
    for (let i = 0; i < n; i++) {
      x = S + "{" + x + "}";
    }
    return x;
  };
  const add = "ad" + id;
  c.push("def " + add + "(a: " + N + ", b: " + N + ") -> " + N + ":\n  match a:\n    case " + Z + "{}:\n      "
    + wrap(k, "b") + "\n    case " + S + "{p}:\n      " + wrap(m, add + "(p, b)"));
  const th = "th" + id;
  c.push("def " + th + "(a: " + N + ", -b: " + N + ") -> {" + add + "(a, " + S + "{b}) == " + S + "{" + add + "(a, b)} : " + N + "}:\n"
    + "  match a:\n    case " + Z + "{}:\n      {==}\n    case " + S + "{p}:\n      %" + th + "(p, b) : {"
    + wrap(m, add + "(p, " + S + "{b})") + " == " + wrap(m - 1, S + "{_}") + " : " + N + "};\n      {==}");
  const a = wrap(1 + c.g.int(3), Z + "{}");
  const b = wrap(c.g.int(2), Z + "{}");
  return { s: th + "(" + a + ", " + b + ")", t: N, a: add + "(" + a + ", " + S + "{" + b + "})", b: S + "{" + add + "(" + a + ", " + b + ")}",
    ap: (x) => S + "{" + x + "}" };
}

function proof(c: Ctx, env: V[], depth: number): Prf {
  if (depth > 0 && c.g.chance(0.5)) {
    const p = proof(c, env, depth - 1);
    return c.g.wpick<() => Prf>([
      [3, () => {
        c.feat("eq-sym");
        return { ...p, s: "Equal.sym(" + p.t + ", " + p.a + ", " + p.b + ", " + p.s + ")", a: p.b, b: p.a };
      }],
      [p.ap !== undefined ? 3 : 0, () => {
        c.feat("eq-cong");
        const w = "w" + String(c.uid());
        const f = p.ap as (x: string) => string;
        return { ...p, s: "Equal.cong(" + p.t + ", " + p.t + ", " + w + " => " + f(w) + ", " + p.a + ", " + p.b + ", " + p.s + ")", a: f(p.a), b: f(p.b) };
      }],
      [2, () => {
        c.feat("eq-trans");
        return { ...p, s: "Equal.trans(" + p.t + ", " + p.a + ", " + p.b + ", " + p.b + ", " + p.s + ", {==})" };
      }],
    ])();
  }
  return c.g.wpick<() => Prf>([
    [4, () => {
      c.feat("eql");
      const t = c.g.pick([U32C, NATC, BOOLC]);
      const side = e_at(syn(c, t, env.filter((v) => v.q === "many"), 1));
      const ap = t.k === "u32" ? (x: string) => "U32.inc(" + x + ")" : t.k === "nat" ? (x: string) => "Nat.double(" + x + ")" : (x: string) => "Bool.not(" + x + ")";
      return { s: "{==}", t: ty_str(t), a: side, b: side, ap };
    }],
    [3, () => {
      c.feat("eqkit");
      const a = num_lit_u32(c).s;
      const b = num_lit_u32(c).s;
      return { s: "U32.add_comm(" + a + ", " + b + ")", t: "U32", a: "U32.add(" + a + ", " + b + ")", b: "U32.add(" + b + ", " + a + ")",
        ap: (x) => "(" + x + " + " + b + " : U32)" };
    }],
    [2, () => theorem(c)],
  ])();
}

function let_proof(c: Ctx, env: V[]): Line {
  // the proof binder is internal to the statement: it must not shadow a
  // value that later statements still fold
  const x = bind_name(c, []);
  const p = proof(c, env, 2);
  const lines = [x + " = {" + p.s + " : {" + p.a + " == " + p.b + " : " + p.t + "}}"];
  const binds: string[] = [];
  if (c.g.chance(0.6)) {
    c.feat("rwt");
    const w = bind_name(c, env, [x]);
    lines.push("%" + x + " : U32;", w + " = " + u32_rhs(num_gen_u32(c, env, 1)));
    binds.push(w);
  }
  return { text: lines.join("\n  "), binds, vars: [] };
}

// Fork kit
// --------
// Parallel lets over saturated calls — the ONE fork shape — plus balanced
// batch trees with ! GPU marks. Interp-side trees stay shallow; the
// compiled-only side goes deep.

function gpu_mark(c: Ctx): string {
  if (c.g.chance(0.25)) {
    c.feat("bang");
    return "!";
  }
  return "";
}

function let_fork(c: Ctx, env: V[]): Line {
  c.feat("fork");
  const ncalls = c.g.wpick<number>([[55, 2], [20, 3], [15, 4], [10, 8]]);
  const nvals = c.g.chance(0.3) ? 1 + c.g.int(2) : 0;
  const vals: string[] = [];
  for (let i = 0; i < ncalls; i++) {
    const e = def_call(c, U32C, env, 2);
    if (e !== null && e.head !== undefined) {
      vals.push(e.head + gpu_mark(c) + e.s.slice(e.head.length));
    }
  }
  for (let i = 0; i < nvals; i++) {
    // riders must be VAR atoms: a parenthesized value would glue onto a
    // preceding call as a spaced suffix, and a bare literal cannot infer
    const nums = env_nums(env);
    if (nums.length === 0) {
      break;
    }
    vals.push(env_take(c.g.pick(nums)));
  }
  // no call minted and no rider in scope: nothing to fork
  if (vals.length === 0) {
    return let_value(c, env);
  }
  for (let i = vals.length - 1; i > 0; i--) {
    const j = c.g.int(i + 1);
    const t = vals[i];
    vals[i] = vals[j];
    vals[j] = t;
  }
  const ks: string[] = [];
  for (const _ of vals) {
    ks.push(bind_name(c, env, ks));
  }
  // a + per name re-binds the fork's results reusable (+a +b = f g)
  const plus = c.g.chance(0.3);
  if (plus) {
    c.feat("plus-par");
  }
  return {
    text: ks.map((k) => (plus ? "+" : "") + k).join(" ") + " = " + vals.join(" "),
    binds: ks, vars: plus ? ks.map((k) => v_new(k, U32C, true)) : [],
  };
}

// hof_call : closures through HOFs and partial application
function hof_call(c: Ctx, env: V[]): E {
  c.feat("hof");
  c = c.sub("hof");
  const id = String(c.uid());
  const name = "pa" + id;
  c.push("def " + name + "(+a: U32, +b: U32, c: U32) -> U32:\n  " + e_at(num_combine(c, [e_atom("a"), e_atom("b"), e_atom("c"), num_lit_u32(c)])));
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 2, t: U32C }, { q: 2, t: U32C }, { q: 1, t: U32C }], ret: U32C });
  const hf = "hg" + id;
  // a template parameter is substituted at compile time: its argument is
  // closed (a lambda over its own binder, or a unary def), and the def is
  // not a plain callable of the registry
  const tmpl = c.g.chance(0.35);
  if (tmpl) {
    c.feat("template");
    c.push("def " + hf + "(~f: U32 -> U32, +x: U32) -> U32:\n  (f(x) + x : U32)");
  } else {
    c.push("def " + hf + "(f: U32 -> U32, +x: U32) -> U32:\n  (f(x) + x : U32)");
    c.defr.push({ name: hf, qps: [], tps: [], ps: [{ q: 1, t: { k: "fun", q: 1, dom: U32C, cod: U32C } }, { q: 2, t: U32C }], ret: U32C });
  }
  if (!tmpl && c.g.chance(0.5)) {
    c.feat("partial");
    // a def value at exactly live-1 arguments
    return e_atom(hf + "(" + name + "(" + e_at(num_gen_u32(c, env, 1)) + ", " + e_at(num_gen_u32(c, env, 1)) + "), " + e_at(num_gen_u32(c, env, 1)) + ")");
  }
  const unary = c.defr.filter((d) => d.wip === undefined && d.qps.length === 0 && d.tps.length === 0 && d.ps.length === 1 && d.ps[0].q === 1 && d.ps[0].t.k === "u32" && d.ret.k === "u32" && (d.mask?.[0] ?? null) === null);
  if (tmpl && unary.length > 0 && c.g.chance(0.4)) {
    c.feat("template-def");
    return e_atom(hf + "(~" + c.g.pick(unary).name + ", " + e_at(num_gen_u32(c, env, 1)) + ")");
  }
  const b = "y" + id;
  // a template's lambda takes no + binder (the parser reads ~( as a term)
  const plus = !tmpl && c.g.chance(0.5);
  if (plus) {
    c.feat("plus-lam");
  }
  const lam = (plus ? "+" : "") + b + " => " + e_at(num_gen_u32(c, [v_new(b, U32C, plus)], plus ? 2 : 1));
  return e_atom(hf + "(" + (tmpl ? "~(" + lam + ")" : lam) + ", " + e_at(num_gen_u32(c, env, 1)) + ")");
}

// Member generation
// -----------------
// A member is one seed's program pieces, position-independent so a batched
// member and its solo re-run draw identically at their own uid base.

// out lines: a string is generator-known; null is deterministic but only
// cross-leg comparable (platform errno text lengths, file offsets)
type IoTail = { lines: string[]; out: Array<string | null>; err: string[]; code: number };

// Stmt : one statement of result/extra with the names it binds
type Stmt = { text: string; binds: string[] };

// A member keeps its program as parts — entries, the result statements
// with their fold and seal, the extra statements, the IO tail — so the
// reducer can drop pieces and assemble() re-renders the rest.
type Member = {
  seed: bigint;
  prof: Profile;
  withBase: boolean;
  resultName: string;
  rawName: string;
  res: string;
  lines: Stmt[];
  fold: string;
  seal: string;
  extraName: string | null;
  xlines: Stmt[];
  xfold: string;
  tail: IoTail | null;
  show: { ty: string; t: T; val: string } | null;
  entries: string[];
  feats: string[];
  trans: boolean;
  eff: Eff | null;
};

// Eff : a foreign effect of the member's own. A datatype with a nullary and
// a U32-field constructor, a foreign def whose .c and .js build them through
// CID(..) and register with io_eff, and a reader that prints the value. The
// names come from the member's own distribution (free names included), so
// CID resolution, the C id table, the JS tags and the registration keys all
// meet them. calls: each call's argument and the line it prints.
type Eff = { file: string; decls: string[]; c: string; js: string; name: string; ty: string; show: string; ctors: string[]; calls: Array<[number, string]> };

// Show programs
// -------------
// A pure main prints its value as a literal at run time, on the C and JS
// runtimes through their own value printers (show_val, driven by a
// descriptor of main's type) and on the interpreter through term_show.
// A show member is one solo program `def main() -> T: v` over a printable
// type: the interpreter's literal is the expectation and the compiled
// legs must print it. Printable: the scalars, tuples, List, Maybe, a
// non-generic program datatype with no erased field, an Array of U32.

// Profile : what a seed's program is, drawn from the seed alone so a solo
// re-run reproduces it. base: Base in the initial environment; free:
// unrestricted declaration names; show: a pure main printed as its literal
// (always so without Base: IO is Base's); file: the member sits in a file of
// its own, else inline in the entry; effect: a foreign effect of its own;
// clash: also checked as a program that must be refused; io: an IO tail;
// surface: the chance per synthesis node of a surface wrapper.
type Profile = { base: boolean; free: boolean; show: boolean; file: boolean; effect: boolean; clash: boolean; io: boolean; surface: number };

const PROFILES = new Map<bigint, Profile>();

function profile(seed: bigint): Profile {
  const got = PROFILES.get(seed);
  if (got !== undefined) {
    return got;
  }
  const g = new Gen(rng_mix64(seed ^ 0x70f1en));
  const base = g.chance(0.88);
  const show = !base || g.chance(0.08);
  const p: Profile = {
    base,
    free: g.chance(0.2),
    show,
    file: g.chance(0.25),
    effect: base && !show && g.chance(0.25),
    clash: !show && g.chance(0.15),
    io: base && !show && g.int(100) < IO_PCT,
    surface: g.wpick<number>([[2, 0], [3, 0.02], [3, 0.08], [2, 0.2]]),
  };
  if (PROFILES.size > 100_000) {
    PROFILES.clear();
  }
  PROFILES.set(seed, p);
  return p;
}

// standalone : a seed that owns its whole program — a pure main, an empty
// initial environment, or free names inline in the entry (in a file of its
// own they are namespaced apart)
function standalone(seed: bigint): boolean {
  const p = profile(seed);
  return p.show || !p.base || (p.free && !p.file);
}

function ty_showable(t: T, depth = 0): boolean {
  switch (t.k) {
    case "empty": case "sig": case "eql": return false;
    case "u32": case "nat": case "bool": case "char": case "str": case "unit": return true;
    case "tup": return t.q === 1 && ty_showable(t.a, depth + 1) && ty_showable(t.b, depth + 1);
    case "arr": return t.el.k === "u32";
    case "adt": {
      if (t.a === BASE.List || t.a === BASE.Maybe) {
        // a Data element: a lone tuple is a Type, so none rides inside
        return t.qs.length === 1 && t.qs[0].k === "q" && t.qs[0].q === 2 && ty_data(t.args[0]) && ty_showable(t.args[0], depth + 1);
      }
      if (t.a.base === true || t.a.qps.length > 0 || t.a.tps.length > 0 || t.a.ips !== undefined || t.a.ctors.length === 0 || !ty_data(t)) {
        return false;
      }
      return depth < 3 && t.a.ctors.every((ct) => ct.fields.every((f) =>
        f.q !== 0 && ((f.t.k === "adt" && f.t.a === t.a) || ty_showable(f.t, depth + 1))));
    }
    default: return false;
  }
}

function show_ty(c: Ctx, fuel: number, data = false): T {
  const own = c.adts.filter((a) => ty_showable({ k: "adt", a, qs: [], args: [] }));
  const leaf = (): T => c.base
    ? c.g.pick([U32C, U32C, NATC, BOOLC, CHARC, STRC, UNITC])
    : { k: "adt", a: c.g.pick(own), qs: [], args: [] };
  if (fuel <= 0) {
    return leaf();
  }
  return c.g.wpick<() => T>([
    [30, leaf],
    [c.base && !data ? 12 : 0, () => ({ k: "tup", a: show_ty(c, fuel - 1), b: show_ty(c, fuel - 1), q: 1 })],
    [c.base ? 12 : 0, () => t_list(Q2, show_ty(c, fuel - 1, true))],
    [c.base ? 6 : 0, () => t_maybe(Q2, show_ty(c, fuel - 1, true))],
    [own.length > 0 ? 14 : 0, () => ({ k: "adt", a: c.g.pick(own), qs: [], args: [] })],
    [c.base && !data ? 5 : 0, () => ({ k: "arr", el: U32C })],
  ])();
}

// io_tail : a deterministic IO sequence for main — file roundtrip in the
// run's cwd, get_env of an unset name, print_err, and rarely an IO.die
// whose exit code is the assertion. Every yield is deterministic.
// Async tail
// ----------
// Fibers, timers and channels, compared C-SEQ against JS, C-PAR and the
// GPU lanes with no interpreter leg. Each scenario is one def main awaits,
// schedule-independent by construction: every fiber it forks is joined and
// every channel drained before it answers, timers register in deadline
// order (the loop stamps each with a strictly later deadline, so equal
// spans keep registration order), and two producers into one channel fold
// commutatively. Its prints and its answer are the generator's own
// expectations, or a cross-leg line when a batch computation rides in.

type Scen = { name: string; prints: string[]; value: bigint | null };

const M32 = 0xffffffffn;

function shuffle<T>(c: Ctx, xs: T[]): T[] {
  const out = xs.slice();
  for (let i = out.length - 1; i > 0; i--) {
    const j = c.g.int(i + 1);
    const t = out[i];
    out[i] = out[j];
    out[j] = t;
  }
  return out;
}

// async_ping : sleep ms, print tag when given, answer v
function async_ping(c: Ctx, ms: number, tag: string | null, v: string): string {
  const n = "fzp" + String(c.uid());
  c.push("def " + n + "() -> IO(U32):\n  do IO<U32>:\n    u : Unit <- IO.sleep(" + String(ms) + ")\n"
    + (tag === null ? "" : "    w : Unit <- IO.print(\"" + tag + "\")\n") + "    IO.pure(U32, " + v + ")");
  return n;
}

function async_block(name: string, rows: string[], end: string): string {
  return "def " + name + "() -> IO(U32):\n  do IO<U32>:\n" + rows.concat([end]).map((r) => "    " + r).join("\n");
}

// The async walk
// --------------
// One scenario is a random walk of main's do-block over an async state:
// fibers forked (a value, a sleep then a value, a batch computation that
// may carry a `!`, or a producer that sends known values into a channel)
// and joined, producers spawned and detached, channels received from, the
// clock read, a group of timers registered in deadline order. A model
// keeps the answer schedule-independent: a value received from a channel
// with one outstanding sender is its FIFO prefix, with several it is the
// whole pending multiset summed; a producer is joined only once its sends
// are received (else a full channel deadlocks the join); the epilogue
// receives everything pending, closes every channel and joins every fiber.
// The answer is the sum of every number main holds: known unless a batch
// value rode in.

type AFiber = { name: string; v: bigint | null; prod: AProd | null };
type AProd = { chan: AChan; left: number };
type AChan = { name: string; open: boolean; queue: Array<{ v: bigint; p: AProd }>; prods: AProd[] };

type AWalk = {
  c: Ctx;
  key: string;
  id: string;
  rows: string[];
  fibers: AFiber[];
  chans: AChan[];
  nums: Array<{ name: string; v: bigint | null }>;
  prints: string[];
  n: number;
};

function a_name(w: AWalk, stem: string): string {
  return stem + w.id + "_" + String(w.n++);
}

function a_fork(w: AWalk, act: string, v: bigint | null, prod: AProd | null): void {
  const name = a_name(w, "t");
  w.rows.push(name + " : Chan(U32) <- IO.fork(U32, " + act + ")");
  w.fibers.push({ name, v, prod });
}

// a_producer : a def that sends k literal values into its channel and
// answers k; the model queues the values behind the channel's others
function a_producer(w: AWalk, ch: AChan): { act: string; prod: AProd; k: number } {
  const k = 1 + w.c.g.int(4);
  const vals = Array.from({ length: k }, () => BigInt(w.c.g.int(100000)));
  const def = a_name(w, "fzs");
  const channel = bind_name(w.c, []);
  const shared = bind_name(w.c, [], [channel]);
  const sent = vals.map((_, j) => bind_name(w.c, [], [channel, shared]));
  w.c.push("def " + def + "(" + channel + ": Chan(U32)) -> IO(U32):\n  +" + shared + " = " + channel + "\n  do IO<U32>:\n"
    + vals.map((v, j) => "    " + sent[j] + " : Bool <- Chan.send(U32, " + shared + ", " + String(v) + ")").join("\n")
    + "\n    IO.pure(U32, " + String(k) + ")");
  const prod: AProd = { chan: ch, left: k };
  ch.queue.push(...vals.map((v) => ({ v, p: prod })));
  ch.prods.push(prod);
  return { act: def + "(" + ch.name + ")", prod, k };
}

// a_recv : n receives folded into one number; the values are the FIFO
// prefix when every pending value is one producer's, else everything
// pending (two producers' sends interleave as they will)
function a_recv(w: AWalk, ch: AChan, all: boolean): void {
  const senders = new Set(ch.queue.map((q) => q.p)).size;
  const pending = ch.queue.length;
  const n = all || senders > 1 ? pending : 1 + w.c.g.int(pending);
  if (n === 0) {
    return;
  }
  const some = helper(w.c, "some1", "sv", (c, nm) => {
    const maybe = bind_name(c, []);
    const valueName = bind_name(c, [], [maybe]);
    return "def " + nm + "(" + maybe + ": Maybe<&1, U32>) -> U32:\n  match " + maybe
      + ":\n    case None{}:\n      0\n    case Some{" + valueName + "}:\n      " + valueName;
  });
  const ms: string[] = [];
  for (let j = 0; j < n; j++) {
    const m = a_name(w, "m");
    w.rows.push(m + " : Maybe<&1, U32> <- Chan.recv(U32, " + ch.name + ")");
    ms.push(some + "(" + m + ")");
  }
  const got = ch.queue.splice(0, n);
  for (const q of got) {
    q.p.left -= 1;
  }
  const name = a_name(w, "v");
  w.rows.push(name + " : U32 <- IO.pure(U32, (" + ms.join(" + ") + " : U32))");
  w.nums.push({ name, v: got.reduce((a, q) => (a + q.v) & M32, 0n) });
}

function a_join(w: AWalk, f: AFiber): void {
  w.fibers.splice(w.fibers.indexOf(f), 1);
  const name = a_name(w, "v");
  w.rows.push(name + " : U32 <- IO.join(U32, " + f.name + ")");
  w.nums.push({ name, v: f.v });
}

function a_close(w: AWalk, ch: AChan): void {
  ch.open = false;
  w.rows.push(a_name(w, "u") + " : Unit <- Chan.close(U32, " + ch.name + ")");
}

// a_step : one statement of the walk, drawn from what the state allows
function a_step(w: AWalk): void {
  const c = w.c;
  const joinable = w.fibers.filter((f) => f.prod === null || f.prod.left === 0);
  const open = w.chans.filter((ch) => ch.open);
  const loaded = open.filter((ch) => ch.queue.length > 0);
  const closable = open.filter((ch) => ch.queue.length === 0 && ch.prods.every((p) => p.left === 0));
  const closed = w.chans.filter((ch) => !ch.open);
  const kit: Array<[number, () => void]> = [
    [15, () => { c.feat("fiber"); const lit = c.g.int(100000); a_fork(w, "IO.pure(U32, " + String(lit) + ")", BigInt(lit), null); }],
    [10, () => { c.feat("fiber"); const lit = c.g.int(100000); a_fork(w, async_ping(c, 1 + c.g.int(6), null, String(lit)) + "()", BigInt(lit), null); }],
    [8, () => {
      const e = def_call(c, U32C, [], 2);
      if (e !== null && e.head !== undefined) {
        c.feat("async-batch");
        a_fork(w, "IO.pure(U32, " + e.head + gpu_mark(c) + e.s.slice(e.head.length) + ")", null, null);
      }
    }],
    [6, () => { w.rows.push(a_name(w, "u") + " : Unit <- IO.sleep(" + String(1 + c.g.int(4)) + ")"); }],
    [4, () => {
      c.feat("timer");
      const a = a_name(w, "n");
      const b = a_name(w, "n");
      const name = a_name(w, "v");
      w.rows.push(a + " : Nat <- IO.now()", a_name(w, "u") + " : Unit <- IO.sleep(" + String(1 + c.g.int(3)) + ")", b + " : Nat <- IO.now()",
        name + " : U32 <- IO.pure(U32, " + helper_bool(c) + "(Bool.not(Nat.is_lt(" + b + ", " + a + "))))");
      w.nums.push({ name, v: 1n });
    }],
    [8, () => {
      c.feat("timer");
      const k = 2 + c.g.int(4);
      const base = 1 + c.g.int(4);
      const step = c.g.pick([0, 1, 2, 4]);
      const ts: string[] = [];
      for (let j = 0; j < k; j++) {
        const tag = "fzt_" + w.key + "_" + w.id + "_" + String(w.n);
        const t = a_name(w, "t");
        w.rows.push(t + " : Chan(U32) <- IO.fork(U32, " + async_ping(c, base + j * step, tag, "1") + "())");
        w.prints.push(tag);
        ts.push(t);
      }
      for (const t of shuffle(c, ts)) {
        const name = a_name(w, "v");
        w.rows.push(name + " : U32 <- IO.join(U32, " + t + ")");
        w.nums.push({ name, v: 1n });
      }
    }],
  ];
  if (open.length > 0) {
    kit.push([14, () => { c.feat("chan"); const ch = c.g.pick(open); const p = a_producer(w, ch); a_fork(w, p.act, BigInt(p.k), p.prod); }]);
    kit.push([8, () => { c.feat("chan"); const ch = c.g.pick(open); const p = a_producer(w, ch); w.rows.push(a_name(w, "u") + " : Unit <- IO.spawn(U32, " + p.act + ")"); }]);
  }
  if (loaded.length > 0) {
    kit.push([16, () => a_recv(w, c.g.pick(loaded), false)]);
    kit.push([6, () => a_recv(w, c.g.pick(loaded), true)]);
  }
  if (joinable.length > 0) {
    kit.push([18, () => a_join(w, c.g.pick(joinable))]);
  }
  if (closable.length > 0) {
    kit.push([3, () => a_close(w, c.g.pick(closable))]);
  }
  if (closed.length > 0) {
    // a receive on a closed channel answers None at once
    kit.push([3, () => {
      const ch = c.g.pick(closed);
      const m = a_name(w, "m");
      const name = a_name(w, "v");
      const some = helper(c, "some1", "sv", (_c, nm) => "def " + nm + "(m: Maybe<&1, U32>) -> U32:\n  match m:\n    case None{}:\n      0\n    case Some{v}:\n      v");
      w.rows.push(m + " : Maybe<&1, U32> <- Chan.recv(U32, " + ch.name + ")", name + " : U32 <- IO.pure(U32, " + some + "(" + m + "))");
      w.nums.push({ name, v: 0n });
    }]);
  }
  c.g.wpick(kit)();
}

function async_walk(c: Ctx, key: string): Scen {
  const id = String(c.uid());
  const w: AWalk = { c, key, id, rows: [], fibers: [], chans: [], nums: [], prints: [], n: 0 };
  const nch = c.g.wpick<number>([[35, 0], [45, 1], [20, 2]]);
  for (let i = 0; i < nch; i++) {
    w.chans.push({ name: "ch" + id + "_" + String(i), open: true, queue: [], prods: [] });
  }
  const steps = size_pick(c, 2 + c.g.int(4), 24);
  for (let i = 0; i < steps; i++) {
    a_step(w);
  }
  // epilogue: every channel drained and closed, every fiber joined
  for (const ch of w.chans) {
    if (ch.open) {
      a_recv(w, ch, true);
      a_close(w, ch);
    }
  }
  while (w.fibers.length > 0) {
    a_join(w, w.fibers[0]);
  }
  const fold = w.nums.length === 0 ? "0" : "(" + w.nums.map((x) => x.name).join(" + ") + " : U32)";
  const body = "fzb" + id;
  const params = w.chans.map((ch, i) => "c" + String(i) + ": Chan(U32)").join(", ");
  c.push("def " + body + "(" + params + ") -> IO(U32):\n" + w.chans.map((ch, i) => "  +" + ch.name + " = c" + String(i) + "\n").join("")
    + "  do IO<U32>:\n" + w.rows.concat(["IO.pure(U32, " + fold + ")"]).map((r) => "    " + r).join("\n"));
  const name = "fza" + id;
  const rooms = w.chans.map((ch, i) => "c" + String(i) + " : Chan(U32) <- Chan.new(U32, " + String(c.g.pick([0, 1, 4])) + ")");
  c.push(async_block(name, rooms, body + "(" + w.chans.map((_, i) => "c" + String(i)).join(", ") + ")"));
  const known = w.nums.every((x) => x.v !== null);
  return { name, prints: w.prints, value: known ? w.nums.reduce((a, x) => (a + (x.v as bigint)) & M32, 0n) : null };
}

function async_tail(c: Ctx, key: string, id: string, lines: string[], out: Array<string | null>): void {
  const n = c.g.wpick<number>([[70, 1], [30, 2]]);
  for (let i = 0; i < n; i++) {
    const sc = async_walk(c.sub("async"), key);
    lines.push("t" + id + "x" + String(i) + " : U32 <- " + sc.name + "()");
    lines.push("t" + id + "y" + String(i) + " : Unit <- IO.print(U32.show(t" + id + "x" + String(i) + "))");
    out.push(...sc.prints, sc.value === null ? null : String(sc.value));
  }
}

function io_tail(c: Ctx, seed: bigint): IoTail {
  c.feat("io-tail");
  const id = String(c.uid());
  const key = (seed & 0xffffffn).toString(16);
  const lines: string[] = [];
  const out: Array<string | null> = [];
  const err: string[] = [];
  let code = 0;
  if (c.g.chance(0.5)) {
    const msg = "fz_" + key + "_" + String(c.g.int(1000));
    // a print as a bind, as a bare step line, or two steps joined by ";"
    const how = c.g.wpick<string>([[5, "bind"], [3, "step"], [2, "pair"]]);
    if (how !== "bind") {
      c.feat("do-step");
    }
    if (how === "pair") {
      const msg2 = "fz_" + key + "_" + String(c.g.int(1000));
      lines.push("IO.print(\"" + msg + "\"); IO.print(\"" + msg2 + "\")");
      out.push(msg, msg2);
    } else {
      lines.push((how === "bind" ? "t" + id + "a : Unit <- " : "") + "IO.print(\"" + msg + "\")");
      out.push(msg);
    }
  }
  if (c.g.chance(0.45)) {
    c.feat("file-io");
    const sl = helper_strlen(c);
    const fn = "fzf_" + key + ".txt";
    const txt = "data".repeat(1 + c.g.int(4)) + String(c.g.int(100));
    // the read back as text (File.read) or as bytes (File.read_bytes,
    // summed through a cons-pattern walk)
    const bytes = c.g.chance(0.4);
    let rdT = "String";
    let rdF = "File.read";
    let rdV = sl + "(s, 0)";
    if (bytes) {
      c.feat("read-bytes");
      const bs = "bs" + id;
      c.push("def " + bs + "(xs: List<&2, U32>) -> U32:\n  match xs:\n    case []:\n      0\n    case +h <> t:\n      (h + h + " + bs + "(t) : U32)");
      rdT = "List<&2, U32>";
      rdF = "File.read_bytes";
      rdV = bs + "(s)";
    }
    const rk = "fr" + id;
    c.push("def " + rk + "(fr: File & Result<&1, &1, U32 & String, " + rdT + ">) -> IO(U32):\n"
      + "  (f, r) = fr\n  match r:\n    case Done{s}:\n      do IO<U32>:\n        u : Unit <- File.close(f)\n        IO.pure(U32, " + rdV + ")\n"
      + "    case Fail{e}:\n      (c, m) = e\n      do IO<U32>:\n        u2 : Unit <- File.close(f)\n        IO.pure(U32, (c + " + sl + "(m, 0) : U32))");
    const wk = "fw" + id;
    const readBind = bind_name(c, []);
    c.push("def " + wk + "(fr: File & Result<&1, &1, U32 & String, Unit>) -> IO(U32):\n"
      + "  (f, r) = fr\n  match r:\n    case Done{u3}:\n      do IO<U32>:\n        " + readBind + " : File & Result<&1, &1, U32 & String, " + rdT + "> <- " + rdF + "(f, 4096)\n        " + rk + "(" + readBind + ")\n"
      + "    case Fail{e}:\n      (c, m) = e\n      do IO<U32>:\n        u4 : Unit <- File.close(f)\n        IO.pure(U32, c)");
    const io = "fio" + id;
    c.push("def " + io + "() -> IO(U32):\n  do IO<U32>:\n"
      + (c.g.chance(0.5)
        ? "    r : Result<&1, &1, U32 & String, File> <- File.open(\"" + fn + "\", \"w\")\n    f : File <- IO.pass(File, r)\n"
        : (c.feat("io-try"), "    f : File <- IO.try(File, File.open(\"" + fn + "\", \"w\"))\n"))
      + "    wr : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, \"" + txt + "\")\n"
      + "    " + wk + "(wr)");
    lines.push("t" + id + "b : U32 <- " + io + "()");
    lines.push("t" + id + "c : Unit <- IO.print(U32.show(t" + id + "b))");
    // the read-after-write offset behavior is deterministic per backend
    // pair but not generator-predictable: cross-leg comparison only
    out.push(null);
  }
  if (c.g.chance(0.4)) {
    c.feat("get-env");
    const sl = helper_strlen(c);
    const ek = "ge" + id;
    c.push("def " + ek + "(r: Result<&1, &1, U32 & String, String>) -> U32:\n  match r:\n"
      + "    case Done{s}:\n      " + sl + "(s, 1000)\n    case Fail{e}:\n      (c, m) = e\n      (c + " + String(c.g.int(64)) + " : U32)");
    lines.push("t" + id + "d : Result<&1, &1, U32 & String, String> <- IO.get_env(\"FZ_UNSET_" + String(c.g.int(1000)) + "\")");
    lines.push("t" + id + "e : Unit <- IO.print(U32.show(" + ek + "(t" + id + "d)))");
    // the errno/strerror pair for an unset name is platform text:
    // cross-leg comparison only
    out.push(null);
  }
  if (c.g.chance(0.4)) {
    c.feat("print-err");
    const msg = "fzerr_" + key + "_" + String(c.g.int(1000));
    lines.push("t" + id + "f : Unit <- IO.print_err(\"" + msg + "\")");
    err.push(msg);
  }
  if (c.g.chance(0.5)) {
    const e = def_new(c.sub("iodef"), { k: "io", t: U32C }, [], 2);
    if (e !== null) {
      lines.push("t" + id + "g : U32 <- " + e.s);
      lines.push("t" + id + "h : Unit <- IO.print(U32.show(t" + id + "g))");
      out.push(null);
    }
  }
  if (c.g.chance(0.6)) {
    c.feat("async");
    async_tail(c.sub("async"), key, id, lines, out);
  }
  if (c.g.chance(0.18)) {
    c.feat("io-die");
    code = 1 + c.g.int(200);
    err.push("fzdie_" + key);
  }
  return { lines, out, err, code };
}

type Kit = Array<[number, (c: Ctx, e: V[]) => Line]>;

// stmt_bound : the names a statement's text binds (`x = ..`, `+a +b = ..`,
// `(a, b) = ..`, `x : T <- ..`), a kit's own inner binders included
function stmt_bound(text: string): string[] {
  return text.split("\n").flatMap((ln) => {
    const m = /^\s*([+%\w\s,()]+?)\s*=(?!=)/.exec(ln) ?? /^\s*(\+?\w+)\s*:.*<-/.exec(ln);
    return m === null ? [] : m[1].match(/[A-Za-z_]\w*/g) ?? [];
  });
}

// lines_gen : n statement lines drawn from a kit table, binding into env;
// a name a line binds shadows the binder of that name in scope, and a
// result the seal would fold is dropped when a later line rebinds its name
function lines_gen(c: Ctx, kit: Kit, label: string, n: number, env: V[]): Stmt[] {
  const lines: Stmt[] = [];
  const bound: string[][] = [];
  for (let i = 0; i < n; i++) {
    const line = c.g.wpick(kit)(c.sub(label), env);
    lines.push({ text: line.text, binds: line.binds });
    bound.push(stmt_bound(line.text));
    for (const v of env) {
      if (bound[i].includes(v.name)) {
        v.q = "dead";
      }
    }
    env.push(...line.vars);
  }
  for (let i = 0; i < n; i++) {
    lines[i].binds = lines[i].binds.filter((b) => !bound.slice(i + 1).some((names) => names.includes(b)));
  }
  return lines;
}

function stmt_names(lines: Stmt[]): string[] {
  return [...new Set(lines.flatMap((l) => l.binds))];
}

// gen_member : one seed's whole program. RNG draws are identical for the
// raw and sealed spellings (the seal is string assembly over one extra
// unconditional draw), so the two books differ only in result's reply.
// eff_new : the member's effect (see Eff); its files are named after the
// seed, so the members of a batch keep theirs apart
function eff_new(c: Ctx, seed: bigint): Eff {
  const file = "fze" + (seed & 0xffffffffffffn).toString(16);
  const ty = decl_name(c, "ft");
  const ctors = [decl_name(c, "fk"), decl_name(c, "fk")];
  const name = decl_name(c, "fe");
  const show = decl_name(c, "fs");
  let field = identifier(c, false);
  while (KEYWORDS.includes(field)) {
    field = identifier(c, false);
  }
  const b = bind_name(c, []);
  c.feat("effect");
  if (c.freeNames) {
    c.feat("effect-free-name");
  }
  const decls = [
    "type " + ty + " is Data:\n  " + ctors[0] + "{}\n  " + ctors[1] + "{" + field + ": U32}",
    "def " + name + "(n: U32) -> IO(" + ty + "):\n  import \"./" + file + ".c\"\n  import \"./" + file + ".js\"",
    "def " + show + "(t: " + ty + ") -> String:\n  match t:\n    case " + ctors[0] + "{}:\n      \"none\"\n    case "
      + ctors[1] + "{" + b + "}:\n      U32.show(" + b + ")",
  ];
  const csrc = "Term " + file + "_run(Env e, Term* f, IoWork* w) {\n  u32 n = (u32)f[0];\n"
    + "  return n % 2 == 0 ? term_pak(CID(" + ctors[0] + "), 0)\n    : term_pak(CID(" + ctors[1] + "), (u32)(n * 3u + 1u));\n}\n\n"
    + "static void __attribute__((constructor)) " + file + "_use(void) {\n  io_eff(CID(" + name + "), " + file + "_run, 0);\n}\n";
  const jssrc = "function " + file + "(n) {\n  return n % 2 === 0 ? { $: CID(" + ctors[0] + ") }\n    : { $: CID(" + ctors[1] + "), ["
    + JSON.stringify(field) + "]: (n * 3 + 1) >>> 0 };\n}\n\nio_eff(CID(" + name + "), " + file + ");\n";
  const calls: Array<[number, string]> = Array.from({ length: 1 + c.g.int(3) }, () => {
    const k = c.g.chance(0.5) ? c.g.int(64) : Number(c.g.r() % 4294967296n);
    return [k, k % 2 === 0 ? "none" : String((k * 3 + 1) >>> 0)];
  });
  return { file, decls, c: csrc, js: jssrc, name, ty, show, ctors, calls };
}

// eff_rows : member i's effect calls, each bound and printed
function eff_rows(e: Eff, i: number): string[] {
  return e.calls.flatMap(([k], j) => ["w" + String(i) + "e" + String(j) + " : " + e.ty + " <- " + e.name + "(" + String(k) + ")",
    "w" + String(i) + "f" + String(j) + " : Unit <- IO.print(" + e.show + "(w" + String(i) + "e" + String(j) + "))"]);
}

function gen_member(seed: bigint, uid0 = 0): Member {
  const prof = profile(seed);
  const withBase = prof.base;
  const c = ctx_new(seed, uid0, withBase, prof.free, prof.surface);
  c.feat(withBase ? "with-base" : "no-base");
  const nadts = withBase ? c.g.int(3) : 1 + c.g.int(4);
  for (let i = 0; i < nadts; i++) {
    adt_new(c.sub("adt"));
  }
  // families after the datatypes (an arm may use them), then a datatype
  // after the families (a field may apply one)
  const nfams = c.g.chance(0.35) ? 1 + c.g.int(2) : 0;
  for (let i = 0; i < nfams; i++) {
    fam_new(c.sub("fam"));
  }
  if (nfams > 0 && c.g.chance(0.5)) {
    adt_new(c.sub("adt"));
  }
  c.pure = true;
  const member = (m: Partial<Member>): Member => ({
    seed, prof, withBase, resultName: "", rawName: "", res: "", lines: [], fold: "", seal: "", extraName: null, xlines: [], xfold: "",
    tail: null, show: null, eff: null, ...m, entries: c.entries.slice(), feats: Object.keys(c.s.feat), trans: c.trans,
  });
  if (prof.show) {
    c.feat("show");
    const t = show_ty(c.sub("show"), 2);
    c.feat("show-" + t.k);
    const val = e_at(syn(c.sub("show"), t, [], 2 + c.g.int(2)));
    return member({ show: { ty: t.k === "tup" ? "(" + ty_str(t) + ")" : ty_str(t), t, val } });
  }
  // the statement table, reshaped per seed (swarm) so a rare production
  // gets seeds where it dominates; result is the interpreter-visible side,
  // extra the compiled-only one (F32, deep forks, long loops)
  const kit = (pure: boolean): Kit => {
    const k: Kit = [[60, let_value], [pure ? 16 : 25, let_fork], [pure ? 12 : 5, let_proof]];
    const swarm: Kit = k.map(([w, f]) => [w * c.g.wpick<number>([[20, 0], [45, 1], [20, 2], [15, 4]]), f]);
    return swarm.some(([w]) => w > 0) ? swarm : k;
  };
  const env: V[] = [];
  const heavy = c.g.chance(0.08);
  if (heavy) {
    c.feat("big");
  }
  const lines = lines_gen(c, kit(true), "res", size_pick(c, heavy ? 5 + c.g.int(5) : 2 + c.g.int(3), 48), env);
  if (c.g.chance(0.04)) {
    c.feat("deaddef");
    c.push("def " + decl_name(c, "zd") + "(x: U32) -> U32:\n  (x + " + String(1 + c.g.int(99)) + " : U32)");
  }
  const res = bind_name(c, env);
  const fold = e_at(num_combine(c.sub("fold"), stmt_names(lines).map((n) => e_atom(n)).concat([num_gen_u32(c.sub("fold"), env, 1)])));
  const seal = e_at(num_seal(c.sub("seal"), res));
  const resultName = decl_name(c, "rs");
  const rawName = decl_name(c, "rw");
  c.pure = false;
  let extraName: string | null = null;
  let xlines: Stmt[] = [];
  let xfold = "";
  if (c.g.chance(0.9)) {
    extraName = decl_name(c, "xt");
    const xenv: V[] = [];
    xlines = lines_gen(c, kit(false), "extra", 1 + c.g.int(3), xenv);
    xfold = e_at(num_combine(c.sub("xfold"), stmt_names(xlines).map((n) => e_atom(n)).concat([num_gen_u32(c.sub("xfold"), xenv, 1)])));
  }
  c.pure = true;
  const tail = prof.io ? io_tail(c.sub("io"), seed) : null;
  const eff = prof.effect ? eff_new(c.sub("eff"), seed) : null;
  return member({ resultName, rawName, res, lines, fold, seal, extraName, xlines, xfold, tail, eff });
}

// member_defs : the member's own defs — result (sealed), the raw sibling
// when asked, and extra — rendered after its entries
function member_defs(m: Member, raw: boolean, main = "main"): string[] {
  if (m.show !== null) {
    return ["def " + main + "() -> " + m.show.ty + ":\n  " + m.show.val];
  }
  const head = m.lines.map((l) => l.text).concat(["+" + m.res + " = " + m.fold]).join("\n  ");
  const def = (name: string, ret: string): string => "def " + name + "() -> U32:\n  " + head + "\n  " + ret;
  const out = [def(m.resultName, m.seal)];
  if (raw) {
    out.push(def(m.rawName, "(" + m.res + " + 0 : U32)"));
  }
  if (m.extraName !== null) {
    out.push("def " + m.extraName + "() -> U32:\n  " + m.xlines.map((l) => l.text).concat([m.xfold]).join("\n  "));
  }
  return out;
}

// member_drop : the member without statement i of lines/xlines; the
// dropped binds read as 0 wherever the rest mentioned them
function member_drop(m: Member, which: "lines" | "xlines", i: number): Member {
  const gone = m[which][i].binds;
  const zero = (t: string): string => gone.reduce((acc, b) => acc.replace(new RegExp("\\b" + b + "\\b", "g"), "0"), t);
  const rest = m[which].filter((_, j) => j !== i).map((l) => ({ text: zero(l.text), binds: l.binds }));
  return which === "lines" ? { ...m, lines: rest, fold: zero(m.fold) } : { ...m, xlines: rest, xfold: zero(m.xfold) };
}

// Assembly
// --------
// Expected stdout per member: the result line (interp-known), its effect's
// lines, the tail's lines (known or cross-leg-only), the extra line
// (cross-leg-only). `null` marks a line whose value only the legs can agree
// on.

type Expect = { out: Array<string | null>; err: string[]; code: number };

function member_expect(m: Member, want: string | null): Expect {
  const out: Array<string | null> = [want, ...(m.eff?.calls.map(([, line]) => line) ?? [])];
  const err: string[] = [];
  let code = 0;
  if (m.tail !== null) {
    out.push(...m.tail.out);
    err.push(...m.tail.err);
    code = m.tail.code;
  }
  if (m.extraName !== null && code === 0) {
    out.push(null);
  }
  return { out, err, code };
}

type Spelling = "sealed" | "raw" | "both";

function member_dies(m: Member): boolean {
  return m.tail !== null && m.tail.code !== 0;
}

// member_rows : one member's lines of a main — its result, its effect, its
// tail, and its extra unless it dies (the IO.die ends its rows)
function member_rows(m: Member, i: number, spelling: Spelling): string[] {
  const rows = ["w" + String(i) + "a : Unit <- IO.print(U32.show(" + (spelling === "raw" ? m.rawName : m.resultName) + "()))"];
  if (m.eff !== null) {
    rows.push(...eff_rows(m.eff, i));
  }
  if (m.tail !== null) {
    rows.push(...m.tail.lines);
  }
  if (m.extraName !== null && !member_dies(m)) {
    rows.push("w" + String(i) + "b : Unit <- IO.print(U32.show(" + m.extraName + "()))");
  }
  return rows;
}

// Programs on disk
// ----------------
// A Prog is what a worker loads: the entry's source, plus files beside it
// (paths relative to the request's root), symlinks (a path to its target,
// relative to the link's directory) and files of the hub store (paths
// relative to BEND_LIB). A one-file program is its source alone.

type Prog = { src: string; entry?: string; files?: Record<string, string>; links?: Record<string, string>; hub?: Record<string, string> };

// prog_text : the program as one text, for findings and traces
function prog_text(p: Prog): string {
  if (p.entry === undefined && p.files === undefined) {
    return p.src;
  }
  const out = [p.entry === undefined ? p.src : "# (a file layout: the entry is " + p.entry + ")\n"];
  for (const [f, t] of Object.entries(p.files ?? {})) {
    out.push("#@@ file " + f + "\n" + t);
  }
  for (const [f, t] of Object.entries(p.links ?? {})) {
    out.push("#@@ link " + f + " -> " + t);
  }
  for (const [f, t] of Object.entries(p.hub ?? {})) {
    out.push("#@@ hub " + f + "\n" + t);
  }
  return out.join("\n");
}

// Layout
// ------
// A program is an entry file and what it imports. Each member sits inline
// in the entry or in a file of its own (its profile draws which), under a
// path the group draws: nested directories, hyphens, host and Base words, an
// entry below the root so imports climb with ../, spellings with and without
// ./, a symlinked directory, the hub store (0x<hash>/.., the hash of the
// file's text). A member reached through a link is sometimes imported
// twice, through its real path too, under a second alias: one file, one
// namespace, both aliases reach it. Inline members keep apart by uid, filed
// ones by namespace. Every member gets a rows def printing its lines (ending
// in its IO.die when its tail dies); main runs the rows of every member
// that lives and hands FZ_MEMBER=i to member i's rows when it dies. A show
// member's main is its value, reached through its alias when it is filed.

const SEG_HEAD = NAME_HEAD;
const SEG_BODY = NAME_BODY + "-";
const BASE_PREFIXES = new Set(BASE_DECL_NAMES.filter((n) => n.includes(".")).map((n) => n.slice(0, n.indexOf("."))));

// seg : a path segment a module may take (letters, digits, _ and -, led by
// a letter or _), a host or Base word a fifth of the time
function seg(g: Gen): string {
  if (g.chance(0.2)) {
    const w = g.pick(NAME_WORDS);
    if (/^[A-Za-z_][\w-]{0,60}$/.test(w)) {
      return w;
    }
  }
  const n = g.chance(0.05) ? 30 + g.int(30) : 1 + g.decay(0.6);
  return g.pick(SEG_HEAD.split("")) + Array.from({ length: n - 1 }, () => g.pick(SEG_BODY.split(""))).join("");
}

// alias_new : an import's alias, fresh in the entry, and no Base prefix
// (the entry calls Base's IO and U32 through their own names)
function alias_new(g: Gen, taken: Set<string>): string {
  for (;;) {
    const a = g.chance(0.3) ? g.pick(NAME_WORDS) : seg(g).replace(/-/g, "_");
    if (/^[A-Za-z_]\w*$/.test(a) && a.length <= 40 && !KEYWORDS.includes(a) && !BASE_PREFIXES.has(a) && !taken.has(a)) {
      taken.add(a);
      return a;
    }
  }
}

// fresh_name : stem, or stem and a counter, not in taken (which it joins)
function fresh_name(stem: string, taken: Set<string>): string {
  let n = stem;
  for (let k = 0; taken.has(n); k++) {
    n = stem + String(k);
  }
  taken.add(n);
  return n;
}

function hex32(x: bigint): string {
  return rng_mix64(x).toString(16).padStart(16, "0") + rng_mix64(x ^ 0x5eedn).toString(16).padStart(16, "0");
}

// Mod : one member's place. file: false for an inline member (its text
// goes into the entry), else its path from the request root, or from the
// store for a hub file; spell: how the entry imports it; twice: the second
// spelling and alias when it is imported twice; rows: its rows def (its
// value's def for a show member)
type Mod = { i: number; m: Member; file: boolean; dir: string[]; base: string; hub: string | null; alias: string; spell: string;
  twice: { alias: string; spell: string } | null; rows: string; text: string; effC: string; effJs: string };

// Layout : a program's parts; a clash edits them before serial(). entryHead,
// entryDefs and mainRows are lines a clash adds to the entry; names: what
// the entry declares
type Layout = { entryDir: string[]; entryName: string; mods: Mod[]; links: Record<string, string>;
  extraFiles: Record<string, string>; extraHub: Record<string, string>; entryHead: string[]; entryDefs: string[];
  mainRows: string[]; withBase: boolean; names: Set<string>; spelling: Spelling };

function mod_file(md: Mod): string {
  return [...md.dir, md.base + ".bend"].join("/");
}

function member_blocks(m: Member, spelling: Spelling, main = "main"): string[] {
  return [...m.entries, ...(m.eff?.decls ?? []), ...member_defs(m, spelling !== "sealed", main)];
}

// layout : a group's program parts, a function of its members' seeds;
// filed puts every member in a file (a clash mutates one)
function layout(ms: Member[], spelling: Spelling, filed = false): Layout {
  const g = new Gen(rng_mix64(ms[0].seed ^ 0x6d6fn));
  const used = new Set<string>();
  const fresh = (p: string): boolean => {
    const k = p.toLowerCase();
    if (used.has(k)) {
      return false;
    }
    used.add(k);
    return true;
  };
  const entryDir = g.chance(0.3) ? Array.from({ length: 1 + g.int(2) }, () => seg(g)) : [];
  entryDir.forEach((_, j) => fresh("d:" + entryDir.slice(0, j + 1).join("/")));
  const entryName = seg(g);
  fresh([...entryDir, entryName + ".bend"].join("/"));
  const inline = (m: Member): boolean => !filed && !m.prof.file;
  // what the entry declares: an alias must not be its first segment
  const names = new Set<string>(ms.filter(inline).flatMap((m) => member_blocks(m, spelling).flatMap(text_names)));
  // nor a name main's own rows bind or declare
  const aliases = new Set<string>([...names].map((n) => n.split(".")[0])
    .concat(["main", "fzall", "fzdis", "fzsel", "sel", "s", "s0", "z", "r", "e"], ms.flatMap((_, i) => ["w" + String(i), "w" + String(i) + "t"])));
  const links: Record<string, string> = {};
  const mods: Mod[] = ms.map((m, i) => {
    const md: Mod = { i, m, file: false, dir: entryDir, base: entryName, hub: null, alias: "", spell: "", twice: null, rows: "", text: "",
      effC: m.eff?.c ?? "", effJs: m.eff?.js ?? "" };
    if (inline(m)) {
      return md;
    }
    const mg = new Gen(rng_mix64(m.seed ^ 0x7061n));
    const hub = mg.chance(0.15) ? "0x" : null;
    let dir: string[];
    let base: string;
    for (;;) {
      dir = Array.from({ length: mg.chance(0.5) ? 1 + mg.int(3) : 0 }, () => seg(mg));
      base = seg(mg);
      if (hub !== null || (dir.every((_, j) => fresh("d:" + dir.slice(0, j + 1).join("/"))) && fresh([...dir, base + ".bend"].join("/")))) {
        break;
      }
    }
    const alias = alias_new(mg, aliases);
    const real = [...dir, base + ".bend"].join("/");
    let spell = "";
    let twice: Mod["twice"] = null;
    if (hub === null) {
      const rel = path.posix.relative(entryDir.join("/") || ".", real);
      spell = !rel.startsWith("../") && mg.chance(0.7) ? "./" + rel : rel;
      if (dir.length > 0 && mg.chance(0.25)) {
        let link = seg(mg);
        while (!fresh("d:" + link)) {
          link = seg(mg);
        }
        links[link] = dir.join("/");
        const via = path.posix.relative(entryDir.join("/") || ".", link + "/" + base + ".bend");
        if (m.withBase && m.show === null && !member_dies(m) && mg.chance(0.5)) {
          twice = { alias: alias_new(mg, aliases), spell };
        }
        spell = !via.startsWith("../") ? "./" + via : via;
      }
    }
    return { ...md, file: true, dir, base, hub, alias, spell, twice };
  });
  for (const md of mods) {
    const m = md.m;
    const taken = md.file ? new Set(member_blocks(m, spelling).flatMap(text_names)) : names;
    md.rows = fresh_name(m.show !== null ? "fzshow" : "fzrows", taken);
    const blocks = member_blocks(m, spelling, md.file ? md.rows : "main");
    if (m.show === null) {
      const end = member_dies(m) ? "IO.die(Unit, " + String((m.tail as IoTail).code) + ", \"fzdie_" + (m.seed & 0xffffffn).toString(16) + "\")"
        : "IO.pure(Unit, Unit{})";
      blocks.push("def " + md.rows + "() -> IO(Unit):\n  do IO<Unit>:\n" + member_rows(m, md.i, spelling).concat([end]).map((r) => "    " + r).join("\n"));
    }
    md.text = (md.file && m.withBase ? "import Base\n\n" : "") + blocks.filter((b) => b !== "").join("\n\n") + (md.file ? "\n" : "");
  }
  return { entryDir, entryName, mods, links, extraFiles: {}, extraHub: {}, entryHead: [], entryDefs: [], mainRows: [], withBase: ms[0].withBase, names, spelling };
}

// ty_qual : a show member's type as the entry spells it, the member's own
// datatypes under its alias
function ty_qual(md: Mod): string {
  const show = md.m.show as { ty: string; t: T };
  const own: string[] = [];
  const walk = (t: T): void => {
    if (t.k === "adt") {
      if (t.a.base !== true && !own.includes(t.a.name)) {
        own.push(t.a.name);
      }
      t.args.forEach(walk);
    } else if (t.k === "tup") {
      walk(t.a);
      walk(t.b);
    } else if (t.k === "arr") {
      walk(t.el);
    }
  };
  walk(show.t);
  own.sort((a, b) => b.length - a.length);
  return own.length === 0 ? show.ty
    : show.ty.replace(new RegExp("(?<![\\w.])(" + own.map(re_lit).join("|") + ")(?![\\w.])", "g"), md.alias + ".$1");
}

// main_defs : the entry's main over its members
function main_defs(l: Layout): string[] {
  const md0 = l.mods[0];
  if (md0.m.show !== null) {
    return md0.file ? ["def main() -> " + ty_qual(md0) + ":\n  " + md0.alias + "." + md0.rows + "()"] : [];
  }
  const taken = new Set(l.names);
  const [all, dis] = [fresh_name("fzall", taken), fresh_name("fzdis", taken)];
  const block = (name: string, rows: string[]): string =>
    "def " + name + "() -> IO(Unit):\n  do IO<Unit>:\n" + rows.concat(["IO.pure(Unit, Unit{})"]).map((r) => "    " + r).join("\n");
  const call = (md: Mod): string => (md.file ? md.alias + "." : "") + md.rows + "()";
  const rowsOf = (md: Mod): string[] => ["w" + String(md.i) + " : Unit <- " + call(md),
    ...md.twice === null ? [] : ["w" + String(md.i) + "t : Unit <- IO.print(U32.show(" + md.twice.alias + "." + md.m.resultName + "()))"]];
  const dying = l.mods.filter((md) => member_dies(md.m));
  const rest = l.mods.filter((md) => !member_dies(md.m)).flatMap(rowsOf).concat(l.mainRows);
  if (dying.length === 0) {
    return [block("main", rest)];
  }
  const RES = "Result<&1, &1, U32 & String, String>";
  const sels = dying.map(() => fresh_name("fzsel", taken));
  const sel = (j: number): string => sels[j] + "(String.eq(s, \"" + String(dying[j].i) + "\"), s)";
  const defs = [block(all, rest)];
  // the selector chain, last link first: no forward references
  for (let j = dying.length - 1; j >= 0; j--) {
    defs.push("def " + sels[j] + "(z: Bool, +s: String) -> IO(Unit):\n  match z:\n    case True{}:\n      " + call(dying[j])
      + "\n    case False{}:\n      " + (j + 1 < dying.length ? sel(j + 1) : all + "()"));
  }
  defs.push("def " + dis + "(r: " + RES + ") -> IO(Unit):\n  match r:\n    case Done{s0}:\n      +s = s0\n      " + sel(0)
    + "\n    case Fail{e}:\n      " + all + "()");
  defs.push("def main() -> IO(Unit):\n  do IO<Unit>:\n    sel : " + RES + " <- IO.get_env(\"FZ_MEMBER\")\n    " + dis + "(sel)");
  return defs;
}

// serial : the layout as a Prog. A hub file's package is named after its
// final text (a clash's included): the store keeps what it once took
function serial(l: Layout): Prog {
  for (const md of l.mods) {
    if (md.hub !== null) {
      md.hub = "0x" + hex32(str_hash(md.text + "\0" + md.effC + "\0" + md.effJs));
      md.spell = md.hub + "/" + mod_file(md);
    }
  }
  const entry = [...l.entryDir, l.entryName + ".bend"].join("/");
  const files: Record<string, string> = { ...l.extraFiles };
  const hub: Record<string, string> = { ...l.extraHub };
  for (const md of l.mods) {
    const at = md.hub === null ? files : hub;
    const root = md.hub === null ? "" : md.hub + "/";
    if (md.file) {
      at[root + mod_file(md)] = md.text;
    }
    if (md.m.eff !== null) {
      const d = [...md.dir, md.m.eff.file].join("/");
      at[root + d + ".c"] = md.effC;
      at[root + d + ".js"] = md.effJs;
    }
  }
  const imports = l.mods.filter((md) => md.file).flatMap((md) => ["import " + md.spell + " as " + md.alias,
    ...md.twice === null ? [] : ["import " + md.twice.spell + " as " + md.twice.alias]]);
  // a clash names a module's spelling, known here, as @SPELL<i>@
  const head = l.entryHead.map((h) => h.replace(/@SPELL(\d+)@/g, (_, i) => l.mods[Number(i)].spell));
  const ms = l.mods.map((md) => md.m);
  const tag = "# fuzz " + l.spelling + (ms.length > 1 ? " batch of " + String(ms.length) : "") + " seed=" + ms.map((m) => String(m.seed)).join(",");
  const top = [tag, ...(l.withBase ? ["import Base"] : []), ...imports, ...head].join("\n");
  const body = [...l.mods.filter((md) => !md.file).map((md) => md.text), ...l.entryDefs, ...main_defs(l)].filter((b) => b !== "");
  files[entry] = top + "\n\n" + body.join("\n\n") + "\n";
  const one = Object.keys(files).length === 1 && Object.keys(hub).length === 0 && Object.keys(l.links).length === 0 && l.entryDir.length === 0;
  return one ? { src: files[entry] } : { src: "", entry, files, links: l.links, hub };
}

// mod_key : how a worker names a member's def: bare in the entry, else its
// file and the def
function mod_key(md: Mod, name: string): string {
  return !md.file ? name : (md.hub === null ? "" : "@lib/" + md.hub + "/") + mod_file(md) + "::" + name;
}

// prog_of : a group's program, its layout too; key names a member's def to
// the worker
function prog_of(ms: Member[], spelling: Spelling, filed = false): { p: Prog; l: Layout; key: (i: number, n: string) => string } {
  const l = layout(ms, spelling, filed);
  return { p: serial(l), l, key: (i, n) => mod_key(l.mods[i], n) };
}

// Clashes
// -------
// A clash seed also takes its member's module layout (whatever layout its
// positive run used) and mutates it with ONE clash from a catalog, each a
// way two names, paths or registrations could come to mean one thing. The
// mutated program must fail loudly, at the stage and with the error the
// clash names: accepted is `clash-accepted`, refused otherwise
// `clash-other`, an internal error `clash-crash`. The catalog, each drawn
// over the member's own names, paths and effect:
//   base-redecl      a module declares a def, type or constructor of Base's
//   root-redecl      the entry declares a key a module declares
//   alias-dup        two imports under one alias (one file or two)
//   alias-shadow     an alias named like a Base prefix P, the module
//                    declaring x, and the entry naming P.x
//   alias-decl       the entry declares a name under an import's alias
//   bad-path         a path segment of a forbidden form: a dot, a ~, a
//                    digit or 0x lead, any other character
//   inner-dotdot     a .. inside an import's path
//   link-bad-target  an import through a link to a badly named directory
//   hub-escape       a hub file importing outside its package
//   bad-name         a declared name with an empty or digit-led segment
//   cid-unknown      an effect's CID(..) of no constructor or def
//   effect-ctr-name  a foreign def named like a constructor
//   effect-two-ns    one effect source imported from two namespaces
//   effect-dup-reg   an effect registered twice: the C and JS runs fail

type Clash = { kind: string; mode: "check" | "emit" | "run"; want: RegExp };

const BASE_DECLS = (() => {
  const out = { defs: new Set<string>(), types: new Set<string>(), ctors: new Set<string>() };
  for (const mm of BASE_SOURCE.matchAll(/^(def|law|type)\s+([A-Za-z_][\w.]*)|^  ([A-Za-z_][\w.]*)\{/gm)) {
    (mm[3] !== undefined ? out.ctors : mm[1] === "type" ? out.types : out.defs).add(mm[3] ?? mm[2]);
  }
  return { defs: [...out.defs], types: [...out.types], ctors: [...out.ctors] };
})();

const PATH_ERR = /an import path of plain names|an import \('import Base'|a package as <name>@<version>/;

function re_lit(t: string): string {
  return t.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

// bad_seg : a path segment of a form the loader must refuse
function bad_seg(g: Gen): string {
  const good = seg(g).replace(/-/g, "_");
  return g.wpick<() => string>([
    [4, () => good + "." + seg(g)],
    [1, () => good + "."],
    [3, () => good + "~" + seg(g)],
    [3, () => String(g.int(10)) + good],
    [2, () => "0x" + hex32(g.r()).slice(0, 8 + g.int(24))],
    [4, () => good + g.pick([..."!$%&'()*+,:;<=>?[]^`{|}é中ß"]) + seg(g)],
    [1, () => good + " " + seg(g)],
    [1, () => good + "@" + seg(g)],
  ])();
}

// clash_new : one clash on the member's layout, or null when none applies
function clash_new(g: Gen, l: Layout): Clash | null {
  const md = l.mods[0];
  const m = md.m;
  const fresh = "fzq" + (m.seed & 0xffffffn).toString(16);
  const names = new Set(text_names(md.text));
  const kinds: Array<[number, () => Clash | null]> = [
    [3, () => {
      if (!m.withBase) {
        return null;
      }
      const which = g.int(3);
      const pool = [BASE_DECLS.defs, BASE_DECLS.types, BASE_DECLS.ctors][which];
      const n = g.pick(pool);
      md.text += which === 0 ? "\ndef " + n + "() -> U32:\n  0\n"
        : which === 1 ? "\ntype " + n + " is Data:\n  " + fresh + "K{}\n"
        : "\ntype " + fresh + "T is Data:\n  " + n + "{}\n";
      return { kind: "base-redecl", mode: "check", want: new RegExp("a fresh " + (which === 2 ? "constructor " : "") + "name \\(duplicate declaration: " + re_lit(n) + "\\)") };
    }],
    [2, () => {
      if (md.hub !== null || md.dir.length > 0 || l.entryDir.length > 0 || !/^[A-Za-z_]\w*$/.test(md.base) || m.show !== null || m.resultName === "") {
        return null;
      }
      l.entryDefs.push("def " + md.base + "." + m.resultName + "() -> U32:\n  0");
      return { kind: "root-redecl", mode: "check", want: /duplicate declaration|is an import's alias/ };
    }],
    [2, () => {
      if (g.chance(0.5)) {
        l.entryHead.push("import @SPELL" + String(md.i) + "@ as " + md.alias);
      } else {
        const other = seg(g) + "_" + fresh;
        l.extraFiles[other + ".bend"] = "def " + fresh + "() -> " + (m.withBase ? "U32:\n  0\n" : "Type:\n  Type\n");
        l.entryHead.push("import " + path.posix.relative(l.entryDir.join("/") || ".", other + ".bend") + " as " + md.alias);
      }
      return { kind: "alias-dup", mode: "check", want: /a fresh alias/ };
    }],
    [3, () => {
      if (!m.withBase) {
        return null;
      }
      const opts = BASE_DECLS.defs.filter((n) => {
        const d = n.indexOf(".");
        return d > 0 && /^[A-Za-z_]\w*$/.test(n.slice(0, d)) && !BASE_NAMES.has(n.slice(d + 1)) && !names.has(n.slice(d + 1))
          && l.mods.every((o) => o === md || o.alias !== n.slice(0, d));
      });
      if (opts.length === 0) {
        return null;
      }
      const n = g.pick(opts);
      const p = n.slice(0, n.indexOf("."));
      md.text += "\ndef " + n.slice(p.length + 1) + "() -> U32:\n  0\n";
      md.alias = p;
      l.entryDefs.push("def " + fresh + "() -> U32:\n  " + n);
      return { kind: "alias-shadow", mode: "check", want: new RegExp("an unambiguous name \\(the alias " + re_lit(p) + " shadows ") };
    }],
    [2, () => {
      l.entryDefs.push("def " + md.alias + "." + fresh + "() -> " + (m.withBase ? "U32:\n  0" : "Type:\n  Type"));
      return { kind: "alias-decl", mode: "check", want: new RegExp(re_lit(md.alias) + " is an import's alias") };
    }],
    [4, () => {
      const bad = bad_seg(g);
      const at = g.int(md.dir.length + 1);
      if (at < md.dir.length) {
        md.dir[at] = bad;
      } else {
        md.base = bad;
      }
      md.spell = "./" + path.posix.relative(l.entryDir.join("/") || ".", mod_file(md));
      md.twice = null;
      return { kind: "bad-path", mode: "check", want: PATH_ERR };
    }],
    [2, () => {
      if (md.hub !== null || md.dir.length === 0) {
        return null;
      }
      const up = path.posix.relative(l.entryDir.join("/") || ".", md.dir[0]);
      md.spell = up + "/../" + mod_file(md);
      md.twice = null;
      return { kind: "inner-dotdot", mode: "check", want: PATH_ERR };
    }],
    [2, () => {
      if (md.hub !== null) {
        return null;
      }
      md.dir = [bad_seg(g).replace(/[ @]/g, ".")];
      const tops = new Set([md.dir[0], l.entryDir[0] ?? "", l.entryName + ".bend", ...Object.keys(l.links), ...Object.keys(l.extraFiles)]
        .map((t) => t.split("/")[0].toLowerCase()));
      let link = seg(g);
      while (tops.has(link.toLowerCase())) {
        link = seg(g);
      }
      l.links[link] = md.dir[0];
      md.spell = "./" + path.posix.relative(l.entryDir.join("/") || ".", link + "/" + md.base + ".bend");
      md.twice = null;
      return { kind: "link-bad-target", mode: "check", want: PATH_ERR };
    }],
    [2, () => {
      const out = seg(g).replace(/-/g, "_") + "_" + fresh;
      const esc = "import ../" + out + ".bend as Q\n\ndef " + fresh + "() -> " + (m.withBase ? "U32:\n  0\n" : "Type:\n  Type\n");
      const pkg = "0x" + hex32(str_hash(esc + out));
      l.extraHub[pkg + "/esc.bend"] = esc;
      l.extraHub[out + ".bend"] = "def " + fresh + "() -> " + (m.withBase ? "U32:\n  0\n" : "Type:\n  Type\n");
      l.entryHead.push("import " + pkg + "/esc.bend as " + fresh + "E");
      return { kind: "hub-escape", mode: "check", want: PATH_ERR };
    }],
    [3, () => {
      const decls = [...md.text.matchAll(/^(?:def|law|type)\s+([A-Za-z_][\w.]*)|^  ([A-Za-z_][\w.]*)\{/gm)];
      if (decls.length === 0) {
        return null;
      }
      const d = g.pick(decls);
      const n = d[1] ?? d[2];
      const bad = g.pick([n + "." + String(g.int(10)) + seg(g).replace(/-/g, "_"), n + "..x", n + "." + String(g.int(100))]);
      const at = (d.index as number) + d[0].lastIndexOf(n);
      md.text = md.text.slice(0, at) + bad + md.text.slice(at + n.length);
      return { kind: "bad-name", mode: "check", want: /a name \(words joined by dots, got / };
    }],
    [2, () => {
      if (m.eff === null) {
        return null;
      }
      const k = g.pick(m.eff.ctors);
      const unknown = fresh + "U";
      if (g.chance(0.5)) {
        md.effC = md.effC.replace("CID(" + k + ")", "CID(" + unknown + ")");
      } else {
        md.effJs = md.effJs.replace("CID(" + k + ")", "CID(" + unknown + ")");
      }
      return { kind: "cid-unknown", mode: "emit", want: new RegExp("CID\\(" + unknown + "\\) names no constructor or def") };
    }],
    [2, () => {
      if (m.eff === null) {
        return null;
      }
      const k = g.pick(m.eff.ctors);
      md.text += "\ndef " + k + "() -> IO(U32):\n  import \"./" + m.eff.file + ".c\"\n  import \"./" + m.eff.file + ".js\"\n";
      return { kind: "effect-ctr-name", mode: "emit", want: new RegExp(re_lit(k) + " names both a constructor and a foreign def") };
    }],
    [2, () => {
      if (m.eff === null || md.hub !== null || l.mods.some((o) => member_dies(o.m))) {
        return null;
      }
      const dir2 = seg(g).replace(/-/g, "_") + "_" + fresh;
      const eff = [...md.dir, m.eff.file].join("/");
      const rel = path.posix.relative(dir2, eff);
      l.extraFiles[dir2 + "/m.bend"] = "import Base\n\ndef " + fresh + "(n: U32) -> IO(U32):\n  import \"" + rel + ".c\"\n  import \""
        + rel + ".js\"\n\ndef " + md.rows + "() -> IO(Unit):\n  do IO<Unit>:\n    z : U32 <- " + fresh + "(1)\n    IO.pure(Unit, Unit{})\n";
      l.entryHead.push("import " + path.posix.relative(l.entryDir.join("/") || ".", dir2 + "/m.bend") + " as " + fresh + "M");
      l.mainRows.push("wz : Unit <- " + fresh + "M." + md.rows + "()");
      return { kind: "effect-two-ns", mode: "emit", want: /is imported from two namespaces/ };
    }],
    [2, () => {
      if (m.eff === null) {
        return null;
      }
      md.effC += "\nstatic void __attribute__((constructor)) " + m.eff.file + "_use2(void) {\n  io_eff(CID(" + m.eff.name + "), " + m.eff.file + "_run, 0);\n}\n";
      md.effJs += "\nio_eff(CID(" + m.eff.name + "), " + m.eff.file + ");\n";
      return { kind: "effect-dup-reg", mode: "run", want: /two effects register/ };
    }],
  ];
  const order = kinds.slice();
  while (order.length > 0) {
    const pick = g.wpick(order.map((k, i) => [k[0], i] as [number, number]));
    const got = order[pick][1]();
    if (got !== null) {
      return got;
    }
    order.splice(pick, 1);
  }
  return null;
}

// clash_test : the member's clash, run to its refusal: the check or
// emission must refuse it, or every compiled lane must
async function clash_test(m: Member, lanes: Lanes, mode: Mode): Promise<Verdict | null> {
  const l = layout([m], "sealed", true);
  const c = clash_new(new Gen(rng_mix64(m.seed ^ 0xc1a5n)), l);
  if (c === null) {
    return null;
  }
  feat_tally["clash-" + c.kind] = (feat_tally["clash-" + c.kind] ?? 0) + 1;
  const p = serial(l);
  const text = prog_text(p);
  const found = (kind: string, why: string, dir?: string): Verdict => {
    save_finding(m.seed, kind, ["clash=" + c.kind, "want=" + String(c.want), why], text, c.kind + ": " + why.split("\n")[0], lanes, dir, mode);
    return { kind: "fail", fkind: kind, why };
  };
  const w = await phase("worker:clash", () => pool.run(p, c.mode === "check" ? "check" : "emit"));
  if (w.verdict === "skip") {
    return { kind: "skip", note: "clash-" + (w.stage ?? "?") };
  }
  const err = w.err ?? "";
  if (c.mode !== "run") {
    if (w.verdict === "ok") {
      return found("clash-accepted", "the " + c.mode + " stage accepted it");
    }
    return c.want.test(err) ? null : found(w.verdict === "crash" && c.mode === "check" ? "clash-crash" : "clash-other", err);
  }
  if (w.verdict !== "ok") {
    return found("clash-other", err);
  }
  const r = await compiled(w, [{ label: "", env: undefined, exp: { refuse: c.want }, transLines: [] }], lanes, "fzc" + String(m.seed), 1, mode);
  try {
    if (r.skip !== null) {
      return { kind: "skip", note: "clash-" + r.skip };
    }
    return r.fail === null ? null : found(/got exit 0\b/.test(r.fail) ? "clash-accepted" : "clash-other", r.fail, r.dir);
  } finally {
    fs.rmSync(r.dir, { recursive: true, force: true });
  }
}

// Worker
// ------
// `fuzz.ts --worker`: JSON-line protocol on stdin/stdout. The worker
// imports bend.ts/comp.ts once, seeds a checked base book once, and per
// request clones it, loads the program, validates it, checks its template
// instance table, and either evaluates the requested defs on the
// interpreter (term_snf, answering each normal form as term_show prints
// it) or emits the C and JS sources. Verdicts: reject (the checker
// refused), skip (resource limit), crash (an internal error on a checked
// program — a finding), ok.
//
// The template table: a live closed call T(~a, ..) is the instance keyed by
// term_key of its arguments. Distinct keys must name distinct instances,
// every instance must exist, and a key must hold its literals exactly (a
// Lit that JSON cannot carry — NaN, an infinity, an unsafe integer —
// would alias two instances). Every generated template call meets it.

type WorkerMode = "eval" | "emit" | "check";
type WorkerReq = { id: number; src: string; mode: WorkerMode; defs?: string[]; prog?: Prog };
type WorkerRes = {
  id: number;
  verdict: "ok" | "reject" | "skip" | "crash";
  outs?: string[];
  csrc?: string;
  jssrc?: string;
  err?: string;
  stage?: string;
  def?: string;
  ms?: number;
};

// tmps_check : the template table's invariants (see above), or null
function tmps_check(book: { tlds: Record<string, unknown>; tmps: Record<string, Record<string, string>> }): string | null {
  const owner = new Map<string, string>();
  const lossy = (x: unknown): boolean => {
    if (Array.isArray(x)) {
      return x.some(lossy);
    }
    if (typeof x !== "object" || x === null) {
      return false;
    }
    const o = x as Record<string, unknown>;
    if (o.$ === "Lit" && o.k !== "String" && (typeof o.v !== "number" || !Number.isSafeInteger(o.v) || Object.is(o.v, -0))) {
      return true;
    }
    return Object.values(o).some(lossy);
  };
  for (const [t, is] of Object.entries(book.tmps)) {
    for (const [k, inst] of Object.entries(is)) {
      const prev = owner.get(inst);
      if (prev !== undefined) {
        return "instance " + inst + " named by two keys: " + prev.slice(0, 200) + " and " + (t + " " + k).slice(0, 200);
      }
      owner.set(inst, t + " " + k);
      if (book.tlds[inst] === undefined) {
        return "instance " + inst + " of " + t + " is not in the book";
      }
      // one term_key per ~ argument, a line each
      let parsed: unknown;
      try {
        parsed = k.split("\n").map((x) => JSON.parse(x));
      } catch {
        return "template key of " + t + " is not term_key lines: " + k.slice(0, 300);
      }
      if (lossy(parsed)) {
        return "template key of " + t + " holds a literal JSON cannot carry: " + k.slice(0, 300);
      }
    }
  }
  return null;
}

async function worker_main(): Promise<void> {
  const bend = await import(pathToFileURL(BEND_TS).href);
  // the emitter keeps tables for the life of its module (layouts by type
  // and constructor name among them), so every emission takes a fresh
  // instance of it: a query on the import defeats the module cache (on a
  // plain path; bun folds a file: URL's query away)
  const comp_fresh = async (id: number): Promise<{ compile_book: (b: unknown) => string; js_book: (b: unknown) => string }> =>
    await import(COMP_TS + "?r=" + String(id));
  const is_err = (e: unknown): boolean => typeof e === "object" && e !== null && (e as { $?: string }).$ === "Err";
  const err_str = (e: unknown): string => {
    if (typeof e === "string") {
      return e;
    }
    if (is_err(e)) {
      try {
        return bend.err_show(e);
      } catch {
        return "unshowable checker error";
      }
    }
    if (e instanceof Error) {
      return e.constructor.name + ": " + e.message;
    }
    return String(e);
  };
  // base book seeded once per process (test.ts's own pattern): clone the
  // tlds shallowly per request and skip base's entries in book_valid
  const BASE_PATH = fs.realpathSync(path.join(ROOT, "bend2", "base.bend"));
  let base_book: { tlds: Record<string, unknown>; ctrs: Record<string, unknown>; order: string[]; hols: number; tmps: Record<string, unknown> } | null = null;
  const base_book_seed = async (): Promise<typeof base_book> => {
    if (base_book === null) {
      const b = bend.book_nil();
      await bend.book_load(b, BASE_PATH, "", new Map());
      bend.book_valid(b);
      base_book = b;
    }
    return base_book;
  };
  // prog_dir : a program's files on disk, in a fresh directory under the
  // run's temporary root; the hub store's files under BEND_LIB, once
  const prog_dir = (p: Prog): string => {
    const dir = fs.mkdtempSync(path.join(process.env.FZ_TMP ?? os.tmpdir(), "w-"));
    for (const [f, t] of Object.entries(p.files ?? {})) {
      fs.mkdirSync(path.dirname(path.join(dir, f)), { recursive: true });
      fs.writeFileSync(path.join(dir, f), t);
    }
    for (const [f, t] of Object.entries(p.links ?? {})) {
      fs.mkdirSync(path.dirname(path.join(dir, f)), { recursive: true });
      fs.symlinkSync(t, path.join(dir, f));
    }
    for (const [f, t] of Object.entries(p.hub ?? {})) {
      const at = path.join(process.env.BEND_LIB as string, f);
      if (!fs.existsSync(at)) {
        fs.mkdirSync(path.dirname(at), { recursive: true });
        fs.writeFileSync(at + ".part" + String(process.pid), t);
        fs.renameSync(at + ".part" + String(process.pid), at);
      }
    }
    return dir;
  };
  // book_of: Base is an input environment. A book without `import Base`
  // starts empty, so those names remain available to ordinary generation.
  // A program with files loads from its directory: a module layout through
  // book_load, as `bend` does, seen mapping each file to its namespace
  const book_of = async (src: string, p?: Prog, dir?: string, seen?: Map<string, string | null>): Promise<{ book?: unknown; err?: string; range?: unknown }> => {
    const book = bend.book_nil();
    try {
      const entry = p?.entry === undefined ? null : path.join(dir as string, p.entry);
      if (entry !== null) {
        src = fs.readFileSync(entry, "utf8");
      }
      const usesBase = /^import Base$/m.test(src);
      let baseCount = 0;
      if (usesBase) {
        const base = await base_book_seed() as { tlds: Record<string, unknown>; ctrs: Record<string, unknown>; order: string[]; tmps: Record<string, unknown> };
        for (const k of Object.keys(base.tlds)) {
          book.tlds[k] = { ...(base.tlds[k] as Record<string, unknown>) };
        }
        Object.assign(book.ctrs, base.ctrs);
        // The parser reads a ~ argument from the callee's template
        // descriptor, so every request needs fresh instance tables.
        for (const k of Object.keys(base.tmps)) {
          const tm = base.tmps[k] as { p: Record<string, unknown>; is: Record<string, string> };
          book.tmps[k] = { ...tm, p: { ...tm.p, book }, is: { ...tm.is } };
        }
        book.order.push(...base.order);
        baseCount = base.order.length;
      }
      if (entry !== null) {
        (seen as Map<string, string | null>).set(BASE_PATH, "");
        await bend.book_load(book, entry, "", seen);
      } else {
        bend.parse_book(book, (dir ?? ROOT) + "/", src.replace(/^import Base$/m, ""), "");
      }
      bend.book_valid(book, baseCount);
      return { book };
    } catch (e) {
      if (e instanceof RangeError) {
        return { range: e };
      }
      if (is_err(e)) {
        return { err: err_str(e) };
      }
      throw e;
    }
  };
  const rl = readline.createInterface({ input: process.stdin, terminal: false });
  const handle = async (l: string): Promise<void> => {
    const req = JSON.parse(l) as WorkerReq;
    const reply = (r: WorkerRes): void => {
      process.stdout.write(JSON.stringify(r) + "\n");
    };
    // a RangeError is a stack overflow when it says so, else JavaScriptCore
    // out of memory: the worker answers and exits, the pool respawns it and
    // retries the request once
    const range = (stage: string, e: unknown, def?: string): void => {
      const oom = !/call stack/i.test(String((e as Error).message));
      process.stdout.write(JSON.stringify({ id: req.id, verdict: "skip", stage: stage + (oom ? "-oom" : "-stack-overflow"), err: err_str(e), def }) + "\n", () => {
        if (oom) {
          process.exit(0);
        }
      });
    };
    let checked: { book?: unknown; err?: string; range?: unknown };
    const dir = req.prog?.files === undefined ? undefined : prog_dir(req.prog);
    const seen = new Map<string, string | null>();
    const done = (): void => {
      if (dir !== undefined) {
        fs.rmSync(dir, { recursive: true, force: true });
      }
    };
    // a def a module declares is named by its file: "file::def" is the def's
    // key in the namespace the loader gave that file
    const key = (d: string): string => {
      const at = d.indexOf("::");
      if (at < 0) {
        return d;
      }
      const f = d.slice(0, at);
      const real = fs.realpathSync(f.startsWith("@lib/") ? path.join(process.env.BEND_LIB as string, f.slice(5)) : path.join(dir as string, f));
      const ns = seen.get(real) ?? "";
      return ns === "" ? d.slice(at + 2) : ns + "." + d.slice(at + 2);
    };
    try {
      checked = await book_of(req.src, req.prog, dir, seen);
    } catch (e) {
      done();
      reply({ id: req.id, verdict: "crash", stage: "check", err: err_str(e) });
      return;
    }
    try {
      await handle_book(req, checked, key, reply, range);
    } finally {
      done();
    }
  };
  const handle_book = async (req: WorkerReq, checked: { book?: unknown; err?: string; range?: unknown }, key: (d: string) => string,
    reply: (r: WorkerRes) => void, range: (stage: string, e: unknown, def?: string) => void): Promise<void> => {
    if (checked.range !== undefined) {
      range("check", checked.range);
      return;
    }
    if (checked.err !== undefined) {
      reply({ id: req.id, verdict: "reject", err: checked.err });
      return;
    }
    const book = checked.book as { tlds: Record<string, unknown>; tmps: Record<string, Record<string, string>> };
    const tmpl = tmps_check(book);
    if (tmpl !== null) {
      reply({ id: req.id, verdict: "crash", stage: "template-key", err: tmpl });
      return;
    }
    if (req.mode === "check") {
      reply({ id: req.id, verdict: "ok" });
      return;
    }
    if (req.mode === "eval") {
      const t0 = performance.now();
      const outs: string[] = [];
      for (const def of req.defs ?? []) {
        let shown: string;
        try {
          shown = bend.term_show(bend.term_lower(bend.term_snf(book, bend.Ref(key(def)))));
        } catch (e) {
          if (e instanceof RangeError) {
            range("interp", e, def);
          } else {
            reply({ id: req.id, verdict: "crash", stage: "interp", err: err_str(e), def });
          }
          return;
        }
        outs.push(shown);
      }
      reply({ id: req.id, verdict: "ok", outs, ms: Math.round(performance.now() - t0) });
      return;
    }
    const emit = (stage: string, f: () => string): string | null => {
      try {
        return f();
      } catch (e) {
        if (e instanceof RangeError) {
          range(stage, e);
        } else {
          reply({ id: req.id, verdict: "crash", stage, err: err_str(e) });
        }
        return null;
      }
    };
    const comp = await comp_fresh(req.id);
    const csrc = emit("emit-c", () => comp.compile_book(book));
    const jssrc = csrc === null ? null : emit("emit-js", () => comp.js_book(book));
    if (csrc !== null && jssrc !== null) {
      reply({ id: req.id, verdict: "ok", csrc, jssrc });
    }
  };
  let queue: Promise<void> = Promise.resolve();
  rl.on("line", (l: string) => {
    queue = queue.then(() => handle(l));
  });
}

// Worker pool
// -----------

type Pending = { resolve: (r: WorkerRes) => void; timer: NodeJS.Timeout };
type Slot = { proc: child.ChildProcess; busy: boolean; reqId: number | null; expired: boolean; errbuf: string; served: number };

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
    // BEND_LIB: the run's own hub store (a module layout's hub files land
    // there), BEND_HUB unreachable: a program never fetches
    const proc = child.spawn(process.execPath, [import.meta.filename, "--worker"], {
      stdio: ["pipe", "pipe", "pipe"],
      cwd: ROOT,
      env: { ...process.env, FZ_TMP: TMP, BEND_LIB: path.join(TMP, "lib"), BEND_HUB: "http://127.0.0.1:9" },
    });
    const slot: Slot = { proc, busy: false, reqId: null, expired: false, errbuf: "", served: 0 };
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
        // a worker that answered out of memory is exiting, and one that
        // has served its life retires: neither takes more work until its
        // exit respawns it (the compiler's memory grows for the life of a
        // process, and six workers over hours had the run killed twice)
        slot.served += 1;
        slot.busy = (res.verdict === "skip" && (res.stage ?? "").endsWith("-oom")) || slot.served >= WORKER_LIFE;
        if (slot.served >= WORKER_LIFE) {
          slot.proc.kill();
        }
        slot.reqId = null;
        p.resolve(res);
        this.drain();
      }
    });
    return slot;
  }

  drain(): void {
    for (let w = this.workers.find((x) => !x.busy); w !== undefined && this.queue.length > 0; w = this.workers.find((x) => !x.busy)) {
      const job = this.queue.shift() as { req: WorkerReq; resolve: (r: WorkerRes) => void };
      this.dispatch(w, job.req, job.resolve);
    }
  }

  dispatch(w: Slot, req: WorkerReq, resolve: (r: WorkerRes) => void): void {
    w.busy = true;
    w.reqId = req.id;
    w.errbuf = "";
    w.expired = false;
    const timer = setTimeout(() => {
      w.expired = true;
      w.proc.kill("SIGKILL");
    }, WORKER_TIMEOUT);
    this.pending.set(req.id, { resolve, timer });
    if (process.env.FUZZ_TRACE_DIR !== undefined) {
      fs.writeFileSync(path.join(process.env.FUZZ_TRACE_DIR, String(req.id).padStart(6, "0") + "-" + req.mode + ".bend"), req.prog === undefined ? req.src : prog_text(req.prog));
    }
    w.proc.stdin?.write(JSON.stringify(req) + "\n");
  }

  async run(src: string | Prog, mode: WorkerMode, defs?: string[], retry = true): Promise<WorkerRes> {
    const req: WorkerReq = typeof src === "string" ? { id: this.nextId++, src, mode, defs }
      : src.files === undefined ? { id: this.nextId++, src: src.src, mode, defs }
      : { id: this.nextId++, src: src.src, mode, defs, prog: src };
    const res = await new Promise<WorkerRes>((resolve) => {
      this.queue.push({ req, resolve });
      this.drain();
    });
    return retry && res.verdict === "skip" && (res.stage ?? "").endsWith("-oom") ? this.run(src, mode, defs, false) : res;
  }

  close(): void {
    const ws = this.workers;
    this.workers = [];
    for (const w of ws) {
      w.proc.kill();
    }
  }
}

// Legs
// ----

type Run = { ok: boolean; out: string; err: string; timeout: boolean; code: number };

type Env = Record<string, string> | undefined;

function leg_exec(cmd: string, args: string[], cwd: string, timeout: number, env: Env = undefined): Promise<Run> {
  return new Promise((resolve) => {
    const opts = { cwd, timeout, encoding: "utf8" as const, maxBuffer: 64 * 1024 * 1024, env: env === undefined ? undefined : { ...process.env, ...env } };
    child.execFile(cmd, args, opts, (e, out, err) => {
      const killed = e !== null && (e as { killed?: boolean }).killed === true;
      const ec = e === null ? 0 : typeof (e as { code?: unknown }).code === "number" ? (e as { code: number }).code : -1;
      resolve({ ok: e === null, out, err, timeout: killed, code: ec });
    });
  });
}

const CC_FLAGS = ["-std=c11", "-w", "-fno-slp-vectorize"];

type LegOut = { kind: "ok" | "skip" | "fail"; out: string; err: string; code: number; why?: string };

async function leg_run(bin: string, args: string[], dir: string, cap: number, env: Env = undefined): Promise<LegOut> {
  const run = await leg_exec(bin, args, dir, cap, env);
  const why = run.timeout ? "RUN TIMEOUT after " + String(cap) + "ms (the interpreter finished this program — livelock/perf-cliff suspect)" : undefined;
  return { kind: run.timeout ? "fail" : "ok", out: run.out, err: run.err, code: run.code, why };
}

async function leg_cc(dir: string, base: string, csrc: string, extra: string[], bin: string, cap: number): Promise<{ ok: boolean; why?: string; skip?: boolean }> {
  const cfile = path.join(dir, base + ".c");
  if (!fs.existsSync(cfile)) {
    fs.writeFileSync(cfile, csrc);
  }
  const cc = await phase("clang", () => leg_exec("clang", [...CC_FLAGS, ...extra, cfile, "-lpthread", "-lm", "-o", path.join(dir, bin)], dir, cap));
  if (!cc.ok) {
    if (cc.timeout) {
      return { ok: false, skip: true, why: "cc-timeout" };
    }
    return { ok: false, why: "C COMPILE FAILURE:\n" + (cc.err + cc.out).slice(0, 2000) };
  }
  return { ok: true };
}

// gpu_lock : strictly one GPU program at a time
let gpu_lock: Promise<void> = Promise.resolve();

function gpu_serial<A>(f: () => Promise<A>): Promise<A> {
  const res = gpu_lock.then(f);
  gpu_lock = res.then(() => undefined, () => undefined);
  return res;
}

// Lanes : what a group's compiled legs run under, drawn from its first seed:
// the C-PAR thread count and the clang -O level (--threads / --opt
// override them, as a finding isolated out of a batch's repro line does)
type Lanes = { threads: number; opt: number };

function group_lanes(seed: bigint): Lanes {
  const g = new Gen(rng_mix64(seed ^ 0x1a4e5n));
  const threads = g.pick([2, 3, 4, 8, 16]);
  const opt = g.wpick<number>([[2, 0], [4, 1], [3, 2], [1, 3]]);
  return { threads: THREADS_ARG !== "" ? Number(THREADS_ARG) : threads, opt: OPT_ARG !== "" ? Number(OPT_ARG) : opt };
}

// group_size : how many seeds the group a seed heads merges
function group_size(seed: bigint): number {
  return new Gen(rng_mix64(seed ^ 0xba7cn)).wpick<number>([[1, 1], [2, 4], [5, 8], [2, 16]]);
}

// Compare
// -------
// cmp_expect : the sequential C leg against the generator's own
// expectations (null lines are cross-leg-only). cmp_legs : any other leg
// against the sequential reference, with the trans policy on the extra
// lines. A refusal (a clash) is every lane's own expectation.

type Want = Expect | { refuse: RegExp };

// lines_of : non-empty lines of a leg's stream
function lines_of(s: string): string[] {
  return s.split("\n").filter((l) => l !== "");
}

function exit_diff(want: number, got: LegOut, what: string): string | null {
  if (got.code === want) {
    return null;
  }
  return "exit: " + what + " " + String(want) + ", got " + String(got.code) + (got.err.trim() !== "" ? " (stderr: " + got.err.trim().slice(0, 400) + ")" : "");
}

function cmp_expect(exp: Want, got: LegOut): string | null {
  if ("refuse" in exp) {
    return got.code !== 0 && exp.refuse.test(got.err) ? null
      : "expected a refusal matching " + String(exp.refuse) + ", got exit " + String(got.code) + ": " + (got.err || got.out).slice(0, 500);
  }
  const ed = exit_diff(exp.code, got, "expected");
  if (ed !== null) {
    return ed;
  }
  const lines = lines_of(got.out);
  if (lines.length !== exp.out.length) {
    return "stdout shape: expected " + String(exp.out.length) + " lines, got " + String(lines.length) + ": " + JSON.stringify(lines.slice(0, 6));
  }
  for (let i = 0; i < exp.out.length; i++) {
    const want = exp.out[i];
    if (want !== null && lines[i] !== want) {
      return "stdout line " + String(i + 1) + ": expected " + JSON.stringify(want) + ", got " + JSON.stringify(lines[i]);
    }
  }
  const errs = lines_of(got.err);
  if (errs.join("\n") !== exp.err.join("\n")) {
    return "stderr: expected " + JSON.stringify(exp.err) + ", got " + JSON.stringify(errs.slice(0, 6));
  }
  return null;
}

function cmp_legs(refr: LegOut, got: LegOut, transLines: number[], soft: boolean): { diff: string | null; ulp: boolean } {
  const ed = exit_diff(refr.code, got, "reference");
  if (ed !== null) {
    return { diff: ed, ulp: false };
  }
  const a = lines_of(refr.out);
  const b = lines_of(got.out);
  if (a.length !== b.length) {
    return { diff: "stdout shape: reference " + String(a.length) + " lines, got " + String(b.length), ulp: false };
  }
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) {
      if (soft && transLines.includes(i)) {
        return { diff: null, ulp: true };
      }
      return { diff: "stdout line " + String(i + 1) + ": reference " + JSON.stringify(a[i]) + ", got " + JSON.stringify(b[i]), ulp: false };
    }
  }
  const ea = lines_of(refr.err).join("\n");
  const eb = lines_of(got.err).join("\n");
  if (ea !== eb) {
    return { diff: "stderr: reference " + JSON.stringify(ea.slice(0, 300)) + ", got " + JSON.stringify(eb.slice(0, 300)), ulp: false };
  }
  return { diff: null, ulp: false };
}

// RunSpec : one execution of a binary — its environment, what it must do,
// and the stdout line indexes owned by trans-flagged members' extra lines
type RunSpec = { label: string; env: Env; exp: Want; transLines: number[] };

// known : a lane's failure is a reviewed limit of that lane (a skip once it
// is attributed to one member): the device holds no F32.show or F32.read
// (a bang reaching one fail-stops), and a JS string holds Unicode scalar
// values only (a Char past U+10FFFF or a surrogate, which Base's Chr{x}
// and the C runtime take, fail-stops the JS runtime)
type Compiled = { fail: string | null; skip: string | null; ulp: boolean; dir: string; known?: string };

const SEQ_LIMITS: Array<[RegExp, string]> = [
  [/memory fault/, "resource-fault"],
  [/a Nat past the largest immediate/, "nat-immediate"],
];

const KNOWN_LIMITS: Array<[RegExp, RegExp, string]> = [
  [/^(METAL|CUDA)/, /a function the device does not hold/, "host-only"],
  [/^JS/, /is not a Unicode scalar value/, "js-char-scalar"],
];

// compiled : the emitted C and JS through every compiled lane. C-SEQ runs
// each RunSpec against its expectation; JS, C-PAR and the GPU lanes run it
// against C-SEQ's output (a refusal against its own). The build directory
// is the caller's to keep or remove.
async function compiled(w: WorkerRes, runs: RunSpec[], lanes: Lanes, base: string, members: number, mode: Mode = LOUD): Promise<Compiled> {
  const dir = fs.mkdtempSync(path.join(TMP, "g-"));
  const out = (r: Partial<Compiled>): Compiled => ({ fail: null, skip: null, ulp: false, dir, ...r });
  const cap = RUN_TIMEOUT * Math.max(1, members);
  const opt = "-O" + String(lanes.opt);
  const cpu = path.join(dir, base + "_cpu");
  const cc = await leg_cc(dir, base, w.csrc ?? "", [opt], base + "_cpu", CC_TIMEOUT);
  if (cc.skip === true) {
    return out({ skip: cc.why ?? "cc-timeout" });
  }
  if (!cc.ok) {
    return out({ fail: cc.why ?? "cc failed" });
  }
  const jsf = path.join(dir, base + ".js");
  fs.writeFileSync(jsf, w.jssrc ?? "");
  const seqs: LegOut[] = [];
  for (const r of runs) {
    const seq = await phase("run:seq", () => leg_run(cpu, ["--threads", "1", "--gpu", "off"], dir, cap, r.env));
    if (seq.why !== undefined) {
      return out({ fail: "C-SEQ" + r.label + " " + seq.why });
    }
    const d = cmp_expect(r.exp, seq);
    if (d !== null) {
      // a runtime limit every compiled leg hits alike is a skip, JS
      // confirming it: memory exhausted (a loop doubling its state), or a
      // Nat past the runtimes' 48-bit immediate (the spec's Nat is unbounded)
      const lim = SEQ_LIMITS.find(([re]) => re.test(seq.err));
      if (lim !== undefined) {
        const js = await leg_run(process.execPath, [path.join(dir, base + ".js")], dir, cap, r.env);
        if (js.code !== 0 && lim[0].test(js.err)) {
          return out({ skip: lim[1] });
        }
      }
      return out({ fail: "C-SEQ" + r.label + " vs expectation: " + d });
    }
    seqs.push(seq);
  }
  let ulp = false;
  let known: { fail: string; known: string } | null = null;
  // limit : a lane failure that is a known limit is noted and the other
  // lanes still run; any other failure ends the group
  const limit = (f: string | null): string | null => {
    const k = f === null ? undefined : KNOWN_LIMITS.find(([l, m]) => l.test(f) && m.test(f));
    if (f === null || k === undefined) {
      return f;
    }
    known = known ?? { fail: f, known: (/^(METAL|CUDA)/.exec(f)?.[1]?.toLowerCase() ?? "") + (k[2] === "host-only" ? "-host-only" : k[2]) };
    return null;
  };
  // lane : one more leg, every run against its reference
  const lane = async (label: string, soft: boolean, run: (env: Env) => Promise<LegOut>): Promise<string | null> => {
    for (let i = 0; i < runs.length; i++) {
      const got = await run(runs[i].env);
      if (got.why !== undefined) {
        return label + runs[i].label + " " + got.why;
      }
      const exp = runs[i].exp;
      if ("refuse" in exp) {
        const d = cmp_expect(exp, got);
        if (d !== null) {
          return label + runs[i].label + " vs expectation: " + d;
        }
        continue;
      }
      const d = cmp_legs(seqs[i], got, runs[i].transLines, soft);
      if (d.diff !== null) {
        return label + runs[i].label + " vs C-SEQ: " + d.diff;
      }
      ulp = ulp || d.ulp;
    }
    return null;
  };
  const js = limit(await lane("JS", true, (env) => phase("run:js", () => leg_run(process.execPath, [jsf], dir, cap, env))));
  if (js !== null) {
    return out({ fail: js });
  }
  const par = await lane("C-PAR(" + String(lanes.threads) + ")", false,
    (env) => phase("run:par", () => leg_run(cpu, ["--threads", String(lanes.threads), "--gpu", "off"], dir, cap * 2, env)));
  if (par !== null) {
    return out({ fail: par });
  }
  // GPU lanes: the same .c rebuilt with the platform flags, run --gpu on,
  // strictly one program at a time
  const gpus: Array<[boolean, string, string[], string]> = [
    [WITH_METAL, "METAL", ["-DBEND_METAL=1", "-x", "objective-c", "-fobjc-arc", "-framework", "Metal", "-framework", "Foundation"], base + "_mtl"],
    [WITH_CUDA, "CUDA", ["-DBEND_CUDA=1", "-I/usr/local/cuda/include", "-L/usr/local/cuda/lib64", "-Wl,-rpath,/usr/local/cuda/lib64", "-lcuda", "-lnvrtc"], base + "_cud"],
  ];
  for (const [on, label, flags, bin] of gpus) {
    if (!on || !mode.gpu) {
      continue;
    }
    const lname = label.toLowerCase();
    const got = await gpu_serial(async (): Promise<Partial<Compiled>> => {
      const gc = await leg_cc(dir, base, w.csrc ?? "", [opt, ...flags], bin, GPU_CC_TIMEOUT);
      if (gc.skip === true) {
        return { skip: lname + "-cc-timeout" };
      }
      if (!gc.ok) {
        return { fail: label + " " + (gc.why ?? "cc failed") };
      }
      // the device program is built once beside the binary, as `bend -o`
      // does; a launch without it compiles and says so on stderr
      const gb = await phase("gpu-build", () => leg_exec(path.join(dir, bin), ["--gpu-build"], dir, GPU_CC_TIMEOUT));
      if (gb.timeout) {
        return { skip: lname + "-build-timeout" };
      }
      if (!gb.ok) {
        // a refusal may come at the device build, before any run
        const refuse = runs.every((r) => "refuse" in r.exp && r.exp.refuse.test(gb.err + gb.out));
        return refuse ? {} : { fail: label + " GPU BUILD FAILURE:\n" + (gb.err + gb.out).slice(0, 2000) };
      }
      const f = limit(await lane(label, true, (env) => phase("run:" + lname, () => leg_run(path.join(dir, bin), ["--gpu", "on"], dir, GPU_RUN_TIMEOUT * Math.max(1, members), env))));
      return f !== null ? { fail: f } : {};
    });
    if (got.skip !== undefined || got.fail !== undefined) {
      return out({ ...got, ulp });
    }
  }
  return out({ ulp, ...(known ?? {}) });
}

// Save
// ----

// Mode : how a test runs. The reducer's trials are quiet (neither save nor
// announce) and skip the GPU lanes when the failure they keep is not on
// one; everything else is loud. Per call: a reduction runs beside the groups
// still in flight.
type Mode = { quiet: boolean; gpu: boolean };

const LOUD: Mode = { quiet: false, gpu: true };

function save_file(sub: string, seed: bigint, header: string[], src: string, suffix = "", mode: Mode = LOUD): string {
  if (mode.quiet) {
    return "";
  }
  const dir = sub === "" ? FINDINGS : path.join(FINDINGS, sub);
  fs.mkdirSync(dir, { recursive: true });
  const f = path.join(dir, "seed-" + String(seed) + suffix + ".bend");
  const head = header.map((l) => "# " + l.replaceAll("\n", "\n# ")).join("\n");
  fs.writeFileSync(f, head + "\n# found=" + new Date().toISOString() + "\n\n" + src);
  return f;
}

// repro_line : the command that re-runs one seed; the lanes it ran under
// are named when they are not the seed's own
function repro_line(seed: bigint, lanes?: Lanes): string {
  const own = group_lanes(seed);
  const flags = (WITH_METAL ? " --metal" : "") + (WITH_CUDA ? " --cuda" : "") + (IO_PCT !== 20 ? " --io-pct " + String(IO_PCT) : "")
    + (lanes !== undefined && lanes.threads !== own.threads ? " --threads " + String(lanes.threads) : "")
    + (lanes !== undefined && lanes.opt !== own.opt ? " --opt " + String(lanes.opt) : "");
  return "repro: bun " + import.meta.filename + " 1 --seed " + String(seed) + flags;
}

// save_finding : persist the program with its verdict header and exact
// repro line (and its build, when one ran), and announce it
function save_finding(seed: bigint, kind: string, detail: string[], src: string, head: string, lanes?: Lanes, dir?: string, mode: Mode = LOUD): string {
  const f = save_file("", seed, ["FUZZ FINDING kind=" + kind, repro_line(seed, lanes), ...detail], src, "", mode);
  if (!mode.quiet) {
    if (dir !== undefined && fs.existsSync(dir)) {
      fs.cpSync(dir, path.join(FINDINGS, "seed-" + String(seed) + ".build"), { recursive: true });
    }
    console.log("\nFINDING " + kind + " seed=" + String(seed) + "\n  " + head + "\n  -> " + f);
  }
  return f;
}

function failure_head(error: string): string {
  return error.split("\n").find((line) => line.trim() !== "" && line.trim() !== "Error:") ?? "Error";
}

// Tally
// -----

// Verdict : note names a skip's reason; fkind/why carry a failure's
// finding kind and message (the reducer's signature)
type Verdict = { kind: "ok" | "skip" | "fail"; note?: string; fkind?: string; why?: string };

const tally = { ok: 0, skip: 0, fail: 0 };
const feat_tally: Record<string, number> = {};
const skip_why: Record<string, number> = {};
let TMP = "";
let pool: Pool;

function tally_feats(feats: string[]): void {
  for (const f of feats) {
    feat_tally[f] = (feat_tally[f] ?? 0) + 1;
  }
}

// Test
// ----
// One group = one compiled program (a batch, or a solo member). The interp
// legs run per member on solo layouts; the compiled legs run on the merged
// program; any compiled failure re-runs members solo, under the group's
// lanes, for attribution. A member whose profile draws a clash is then
// checked as the program that must be refused.

const UID_STRIDE = 1_000_000;

type MemberState = {
  m: Member;
  verdict: Verdict | null;
  want: string | null;
};

// member_interp : the interpreter leg for one member: the raw and sealed
// results evaluated in parallel requests on one book (evaluation is the
// cost; parsing and checking is ~5ms), or a show member's main. Answers
// the value the compiled legs must print, or a verdict. A reject is
// attributed by re-checking the raw spelling alone: raw-reject is a
// generator bug, generator-reject a broken seal.
async function member_interp(ms: MemberState, mode: Mode): Promise<void> {
  const m = ms.m;
  const show = m.show !== null;
  const both = prog_of([m], show ? "sealed" : "both");
  const src = prog_text(both.p);
  const defs = show ? ["main"] : [both.key(0, m.rawName), both.key(0, m.resultName)];
  const ws = await Promise.all(defs.map((d, i) => phase(i === 0 ? "worker:raw" : "worker:sealed", () => pool.run(both.p, "eval", [d]))));
  const fail = (kind: string, detail: string[], prog: string, head: string, why = head): void => {
    save_finding(m.seed, kind, detail, prog, head, undefined, undefined, mode);
    ms.verdict = { kind: "fail", fkind: kind, why };
  };
  const oracle = ws[0];
  if (oracle.verdict === "reject") {
    const error = oracle.err ?? "";
    if (show) {
      fail("raw-reject", ["stage=check", error], src, failure_head(error), error);
      return;
    }
    const rawp = prog_of([m], "raw").p;
    const r = await phase("worker:check", () => pool.run(rawp, "check"));
    const kind = r.verdict === "ok" ? "generator-reject" : "raw-reject";
    fail(kind, ["stage=check", error], kind === "raw-reject" ? prog_text(rawp) : src, failure_head(error), error);
    return;
  }
  for (const [x, kind] of ws.map((w, i) => [w, i === 0 ? "raw-crash" : "interp-crash"] as const)) {
    if (x.verdict === "crash") {
      fail(kind, ["stage=" + (x.stage ?? "?"), x.err ?? ""], src, (x.err ?? "").split("\n")[0], x.err ?? "");
      return;
    }
  }
  const skipped = ws.find((w) => w.verdict === "skip");
  if (skipped !== undefined) {
    const why = (skipped === oracle ? "raw-" : "") + (skipped.stage ?? "?");
    save_file("skipped", m.seed, ["SKIPPED reason=" + why, skipped.err ?? ""], src, "", mode);
    ms.verdict = { kind: "skip", note: why };
    return;
  }
  const outs = ws.map((w) => (w.outs?.[0] ?? "").trim());
  if (!show && !/^\d+$/.test(outs[0])) {
    fail("interp-stuck", ["not a closed U32: " + outs[0].slice(0, 300)], src, "not a closed U32");
    return;
  }
  if (!show && outs[1] !== outs[0]) {
    fail("seal-diverge", ["raw interp:    " + outs[0], "sealed interp: " + outs[1]], src, "raw=" + outs[0] + " sealed=" + outs[1]);
    return;
  }
  ms.want = outs[0];
}

// group_runs : the plain run over the members that live, then one run
// per dying member, selected by FZ_MEMBER; twice: members a second alias
// prints again
function group_runs(states: MemberState[], twice: Set<Member>): RunSpec[] {
  const plain = group_expect(states.filter((s) => !member_dies(s.m)), twice);
  const runs: RunSpec[] = [{ label: "", env: undefined, ...plain }];
  states.forEach((s, i) => {
    if (member_dies(s.m)) {
      runs.push({ label: " [FZ_MEMBER=" + String(i) + "]", env: { FZ_MEMBER: String(i) }, exp: member_expect(s.m, s.want), transLines: [] });
    }
  });
  return runs;
}

function group_expect(states: MemberState[], twice: Set<Member>): { exp: Expect; transLines: number[] } {
  const out: Array<string | null> = [];
  const err: string[] = [];
  const transLines: number[] = [];
  let code = 0;
  for (const ms of states) {
    const e = member_expect(ms.m, ms.want);
    for (let i = 0; i < e.out.length; i++) {
      if (e.out[i] === null && ms.m.trans) {
        transLines.push(out.length + i);
      }
    }
    out.push(...e.out);
    if (twice.has(ms.m)) {
      out.push(ms.want);
    }
    err.push(...e.err);
    code = e.code;
  }
  return { exp: { out, err, code }, transLines };
}

// group_compiled : the group's program emitted and through every compiled
// lane. A show program's value is its one line. Without Base there is no
// compiled leg: the emitters take their runtime types from Base.
async function group_compiled(live: MemberState[], solo: boolean, lanes: Lanes, mode: Mode): Promise<{ fail: string | null; skip: string | null; err?: string; batch: string; ulp: boolean; dir?: string; known?: string }> {
  const members = live.map((s) => s.m);
  if (live.length === 0) {
    return { fail: null, skip: null, batch: "", ulp: false };
  }
  const prog = prog_of(members, "sealed");
  const src = prog_text(prog.p);
  for (const md of prog.l.mods) {
    tally_feats(["layout-" + (md.file ? "file" : "inline"), ...md.hub !== null ? ["layout-hub"] : [],
      ...md.twice !== null ? ["layout-twice"] : [], ...md.file && Object.keys(prog.l.links).length > 0 ? ["layout-link"] : []]);
  }
  if (!members[0].withBase) {
    return { fail: null, skip: null, batch: src, ulp: false };
  }
  const w = await phase("worker:emit", () => pool.run(prog.p, "emit"));
  if (w.verdict === "skip") {
    return { fail: null, skip: w.stage ?? "emit-skip", err: w.err, batch: src, ulp: false };
  }
  if (w.verdict !== "ok") {
    return { fail: "EMIT " + w.verdict + " (" + (w.stage ?? "?") + "): " + (w.err ?? "").split("\n").slice(0, 3).join(" "), skip: null, batch: src, ulp: false };
  }
  const runs: RunSpec[] = members[0].show !== null
    ? [{ label: "", env: undefined, exp: { out: [live[0].want], err: [], code: 0 }, transLines: [] }]
    : group_runs(live, new Set(prog.l.mods.filter((md) => md.twice !== null).map((md) => md.m)));
  const r = await compiled(w, runs, lanes, "fz" + String(members[0].seed) + (solo ? "s" : "b"), members.length, mode);
  return { ...r, batch: src };
}

async function test_group(seeds: bigint[], solo: boolean, lanes: Lanes, mode: Mode = LOUD): Promise<Verdict[]> {
  const states: MemberState[] = seeds.map((sd, k) => {
    const m = phase_sync("gen", () => gen_member(sd, solo ? 0 : k * UID_STRIDE));
    return { m, verdict: null, want: null };
  });
  for (const s of states) {
    tally_feats(s.m.feats);
  }
  return test_members(states, solo, lanes, mode);
}

// test_members : run the legs over already-generated members
async function test_members(states: MemberState[], solo: boolean, lanes: Lanes, mode: Mode = LOUD): Promise<Verdict[]> {
  await Promise.all(states.map((s) => member_interp(s, mode)));
  const live = states.filter((s) => s.verdict === null);
  const res = await group_compiled(live, solo, lanes, mode);
  try {
    if (res.known !== undefined && solo) {
      live[0].verdict = { kind: "skip", note: res.known };
    } else if (res.skip !== null) {
      for (const s of live) {
        const own = prog_text(prog_of([s.m], "sealed").p);
        save_file("skipped", s.m.seed, ["SKIPPED reason=" + res.skip, res.err ?? ""], own, "", mode);
        if (res.batch !== own) {
          save_file("skipped", s.m.seed, ["SKIPPED reason=" + res.skip + " (the batch that skipped)", res.err ?? ""], res.batch, "-batch", mode);
        }
        s.verdict = { kind: "skip", note: res.skip };
      }
    } else if (res.fail !== null && solo) {
      const s = live[0];
      const kind = res.fail.startsWith("EMIT") ? "compiler-crash"
        : /COMPILE FAILURE/.test(res.fail) ? "cc-fail"
        : /TIMEOUT/.test(res.fail) ? "leg-timeout" : "leg-diverge";
      save_finding(s.m.seed, kind, [res.fail], res.batch, res.fail.split("\n")[0], lanes, res.dir, mode);
      s.verdict = { kind: "fail", fkind: kind, why: res.fail };
    } else if (res.fail !== null) {
      // attribute: re-run each member alone at uid base 0 under the same
      // lanes, so whatever it saves reproduces under its repro line
      if (!mode.quiet) {
        console.log("\nbatch of " + String(live.length) + " failed, isolating: " + res.fail.split("\n")[0]);
      }
      let blamed = false;
      for (const s of live) {
        const v = await test_group([s.m.seed], true, lanes, mode);
        s.verdict = v[0];
        blamed = blamed || v[0].kind === "fail" || (res.known !== undefined && v[0].note === res.known);
      }
      if (!blamed) {
        save_finding(live[0].m.seed, "batch-only",
          ["no member fails alone — the MERGE or whole-book emission is at fault", res.fail,
            "members: " + live.map((s) => String(s.m.seed)).join(" ")], res.batch,
          String(live.length) + " members: " + res.fail.split("\n")[0], lanes, res.dir, mode);
        live[0].verdict = { kind: "fail", fkind: "batch-only", why: res.fail };
      }
    }
  } finally {
    if (res.dir !== undefined) {
      fs.rmSync(res.dir, { recursive: true, force: true });
    }
  }
  if (res.ulp) {
    for (const s of live) {
      if (s.verdict === null && s.m.trans) {
        s.verdict = { kind: "skip", note: "trans-ulp" };
      }
    }
  }
  for (const s of states) {
    if (s.verdict === null && s.m.prof.clash) {
      s.verdict = await clash_test(s.m, lanes, mode);
    }
  }
  for (const s of states) {
    if (s.verdict === null) {
      s.verdict = { kind: "ok" };
    }
  }
  if (solo && !mode.quiet && states[0].verdict?.kind === "fail") {
    await reduce_auto(states[0].m, states[0].verdict, lanes);
  }
  return states.map((s) => s.verdict as Verdict);
}

// Reduce
// ------
// Every solo finding is reduced as it is saved: a greedy delta reduction
// of its member (drop result and extra statements, their binds read as 0
// downstream, the extra def, the IO tail, the effect, then every entry
// nothing needs) keeping a change while the same failure signature holds,
// under the same lanes. The result lands beside the finding as
// seed-N.min.bend. The first two findings of a signature are reduced; the
// rest are the same class.

// fail_sig : the failure's identity — its finding kind, plus the first
// message line with digits masked for crashes and rejects (values in a
// divergence message shift as the program shrinks)
function fail_sig(v: Verdict): string | null {
  if (v.kind !== "fail") {
    return null;
  }
  const kind = v.fkind ?? "fail";
  if (/reject/.test(kind)) {
    const diagnostic = (v.why ?? "").split("\n")
      .filter((line) => /^- (?:expected|observed)\s*:|^Location:/.test(line))
      .slice(0, 3).join(" | ").replace(/[0-9]+/g, "#");
    return kind + ":" + diagnostic;
  }
  const exact = /crash|reject|cc-fail|clash/.test(kind);
  return kind + (exact ? ":" + (v.why ?? "").split("\n")[0].replace(/[0-9]+/g, "#") : "");
}

const REDUCED = new Map<string, number>();

async function reduce_auto(m0: Member, v: Verdict, lanes: Lanes): Promise<void> {
  const want = fail_sig(v);
  // the budget is per class: the kind and the head of its message, values
  // masked (the signature a reduction keeps is coarser: values shift)
  const cls = (v.fkind ?? "") + ":" + (v.why ?? "").split("\n")[0].replace(/"[^"]*"/g, "\"\"").replace(/[0-9]+/g, "#").slice(0, 60);
  if (want === null || (REDUCED.get(cls) ?? 0) >= 2 || /^clash/.test(want)) {
    return;
  }
  REDUCED.set(cls, (REDUCED.get(cls) ?? 0) + 1);
  const mode: Mode = { quiet: true, gpu: /^(METAL|CUDA)/.test(v.why ?? "") };
  const sig = async (m: Member): Promise<string | null> =>
    fail_sig((await test_members([{ m, verdict: null, want: null }], true, lanes, mode))[0]);
  let m = m0;
  let tries = 0;
  {
    const keep = async (m2: Member): Promise<boolean> => {
      tries++;
      const ok = (await sig(m2)) === want;
      if (ok) {
        m = m2;
      }
      return ok;
    };
    for (let changed = true; changed && tries < 400;) {
      changed = false;
      for (const which of ["lines", "xlines"] as const) {
        for (let i = m[which].length - 1; i >= 0; i--) {
          changed = (await keep(member_drop(m, which, i))) || changed;
        }
      }
      if (m.extraName !== null) {
        changed = (await keep({ ...m, extraName: null, xlines: [], xfold: "" })) || changed;
      }
      if (m.tail !== null) {
        changed = (await keep({ ...m, tail: null })) || changed;
      }
      if (m.eff !== null) {
        changed = (await keep({ ...m, eff: null })) || changed;
      }
      for (let i = m.entries.length - 1; i >= 0; i--) {
        changed = (await keep({ ...m, entries: m.entries.filter((_, j) => j !== i) })) || changed;
      }
    }
  }
  const f = save_file("", m.seed, ["FUZZ REDUCED kind=" + want, repro_line(m.seed, lanes),
    "reduced from the finding beside it: the same failure on this program (" + String(tries) + " trials)"], prog_text(prog_of([m], "sealed").p), ".min");
  console.log("  reduced -> " + f);
}

// Fuzz
// ----

// FEATURES : what a run is expected to reach; the ones it never did are
// listed at its end (Base's registry adds one per def: base:<name>)
const FEATURES = ["qpoly-def", "qpoly-call", "kind-qvar", "kind-meet", "adt-data", "adt-qpoly", "adt-type",
  "erased-field", "erased-param", "f32", "f32-arith", "f32-trans", "f32-conv", "nat-table", "peel",
  "array-ops", "array-sugar", "array-lit", "array-write", "map-ops", "container-pair", "string-append",
  "match-adt", "do-maybe", "do-result", "fork", "bang", "def", "rec", "loop", "match-multi", "wild", "match-nest", "state",
  "ret-tup", "io-def", "rec-io", "do-io", "match-nat", "match-bool", "match-cmp", "match-str", "match-char", "match-tup",
  "arr-param", "plus-rebind", "eql", "rwt", "thm", "eqkit", "eq-sym", "eq-cong", "eq-trans", "partial", "io-tail",
  "fam-nat", "fam-bool", "fam-enum", "fam-use", "fam-unfold", "fam-mk", "fam-rd", "fam-cast", "adt-indexed",
  "sig", "sig-value", "empty", "eql-clash", "eql-ne", "refute", "dep-param", "dep-call", "law-where", "law-exs", "or", "pair",
  "template", "template-arg", "template-def", "f32-bits", "f32-showread", "f32-show", "u32-showread", "io-try",
  "async", "fiber", "timer", "chan", "async-batch", "effect", "effect-free-name",
  "seal-add", "seal-xor", "seal-dist", "seal-mask", "seal-cmp", "seal-rot",
  "plus-pat", "cons-pat", "list-pat", "list-lit", "plus-par", "plus-lam", "plus-do", "do-let", "plus-tup",
  "do-step", "cons-lit", "str-escape", "read-bytes", "file-io", "get-env", "print-err", "io-die", "twins", "dup", "reuse", "clo",
  "show", "show-adt", "show-tup", "show-str", "show-arr", "no-base", "with-base", "free-name", "name-affix", "shadow",
  "syntax-ann", "syntax-beta", "syntax-rewrite", "syntax-erased-let", "syntax-ctor-let", "syntax-inline", "syntax-inline-default",
  "unsafe", "assert-def", "hof", "absurd", "deaddef", "big", "stretch",
  "layout-inline", "layout-file", "layout-hub", "layout-link", "layout-twice"];

async function fuzz_run(): Promise<void> {
  await base_registry_load();
  if (cli_flag("--dump")) {
    process.stdout.write(prog_text(prog_of([gen_member(BASE_SEED, 0)], "both").p));
    return;
  }
  fs.mkdirSync(FINDINGS, { recursive: true });
  fs.writeFileSync(path.join(FINDINGS, ".gitignore"), "*\n!.gitignore\n");
  TMP = fs.mkdtempSync(path.join(os.tmpdir(), "bend-fuzz-"));
  if (WITH_CUDA) {
    // a missing toolkit would otherwise fail every batch as cc-fail noise
    const probe = path.join(TMP, "cuda-probe.c");
    fs.writeFileSync(probe, "#include <cuda.h>\n#include <nvrtc.h>\nint main(void){return 0;}\n");
    const got = child.spawnSync("clang", [probe, "-I/usr/local/cuda/include",
      "-L/usr/local/cuda/lib64", "-lcuda", "-lnvrtc", "-o", path.join(TMP, "cuda-probe")], { encoding: "utf8" });
    if (got.status !== 0) {
      console.error("--cuda: the CUDA toolkit is not usable here (clang cannot build against"
        + " /usr/local/cuda):\n" + (got.stderr ?? "").split("\n").slice(0, 3).join("\n"));
      process.exit(1);
    }
  }
  if (WITH_METAL && process.platform !== "darwin") {
    console.error("--metal needs macOS");
    process.exit(1);
  }
  pool = new Pool(Math.max(2, Math.min(10, JOBS * 2)));
  // a first ^C stops launching and lets the groups in flight finish
  let deadline = DEADLINE;
  process.on("SIGINT", () => {
    if (deadline === 0) {
      process.exit(130);
    }
    deadline = 0;
    console.log("\nstopping: the groups in flight finish (^C again to quit now)");
  });
  const legs = "interp+cseq+js+par" + (WITH_METAL ? "+metal" : "") + (WITH_CUDA ? "+cuda" : "");
  console.log("bend2 fuzz: " + (COUNT_UNIT !== undefined ? "for " + COUNT_ARG : "count=" + String(COUNT)) + " seed=" + String(BASE_SEED)
    + " jobs=" + String(JOBS) + " legs=" + legs + " io-pct=" + String(IO_PCT) + " registry=" + String(BASE_DEFR.length) + " base defs");
  const t0 = performance.now();
  let seed = BASE_SEED;
  let done = 0;
  let launched = 0;
  let last = 0;
  const inflight = new Set<Promise<void>>();
  const more = (): boolean => launched < COUNT && Date.now() < deadline;
  const status = (): string => String(done) + " done, " + (done / ((performance.now() - t0) / 1000)).toFixed(1) + "/s, ok=" + String(tally.ok)
    + " skip=" + String(tally.skip) + " FAIL=" + String(tally.fail);
  while (more() || inflight.size > 0) {
    while (inflight.size < JOBS && more()) {
      const head = seed;
      const size = standalone(head) ? 1 : group_size(head);
      const batch: bigint[] = [];
      while (batch.length < size && more()) {
        // a seed that owns its program closes the group before it
        if (standalone(seed) && batch.length > 0) {
          break;
        }
        batch.push(seed);
        seed = rng_step(seed);
        launched++;
      }
      const p = test_group(batch, batch.length === 1, group_lanes(head))
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
          console.log("\nFUZZER ERROR seeds=" + batch.map(String).join(",") + ": " + String(e instanceof Error ? e.stack ?? e.message : e));
        })
        .finally(() => {
          done += batch.length;
          inflight.delete(p);
          if (process.stdout.isTTY) {
            process.stdout.write("\r" + status() + "   ");
          } else if (performance.now() - last > 60_000) {
            last = performance.now();
            console.log("[" + new Date().toISOString() + "] " + status());
          }
        });
      inflight.add(p);
    }
    if (inflight.size > 0) {
      await Promise.race(inflight);
    }
  }
  pool.close();
  fs.rmSync(TMP, { recursive: true, force: true });
  const dt = (performance.now() - t0) / 1000;
  console.log("\n\n" + String(done) + " programs in " + dt.toFixed(1) + "s (" + (done / dt).toFixed(1) + "/s)");
  console.log("ok=" + String(tally.ok) + " skip=" + String(tally.skip) + " FAIL=" + String(tally.fail));
  console.log("features: " + Object.entries(feat_tally).sort((a, b) => b[1] - a[1]).map(([k, v]) => k + "=" + String(v)).join(" "));
  phase_report();
  if (Object.keys(skip_why).length > 0) {
    console.log("skips: " + Object.entries(skip_why).map(([k, v]) => k + "=" + String(v)).join(" "));
  }
  const never = FEATURES.concat(BASE_DEFR.map((d) => "base:" + d.name)).filter((f) => feat_tally[f] === undefined);
  if (never.length > 0) {
    console.log("never reached: " + never.join(" "));
  }
  if (tally.fail > 0) {
    console.log("findings in " + FINDINGS);
    process.exit(1);
  }
}

if (path.resolve(process.argv[1] ?? "") === import.meta.filename) {
  if (cli_flag("--help") || cli_flag("-h")) {
    print_help();
  } else if (cli_flag("--worker")) {
    await worker_main();
  } else {
    await fuzz_run();
  }
}
