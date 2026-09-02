#!/usr/bin/env bun
// Differential fuzzer for the bend2-core toolchain (bend2/bend.ts + comp.ts).
// Each seed deterministically generates a well-typed, terminating Bend program
// in two algebraically-equal spellings (raw and identity-sealed) and runs it
// across every leg:
//
//   - interp (the spec): term_snf on a pure `result` def, raw and sealed —
//     both spellings in one book, evaluated in parallel — the trusted-kernel
//     evaluation path. The raw value is the oracle; the sealed one must
//     equal it, so a broken seal cannot bless itself. The interpreter runs
//     base's structural code (Word adder chains), so this leg is also a
//     bit-level spec differential against the native ops the backends
//     substitute.
//   - C (compile_book): one standalone .c, built with clang and run
//     sequentially (--parallel off). Lanes on the SAME binary:
//     --threads N --gpu off (CPU parallelism, --threads flag) — plus
//     separate builds for Metal (--metal) and CUDA (--cuda), run --gpu on.
//   - JS (js_book): the emitted .js run under bun.
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
// Hard-won language rules the generator is built around (each was probed
// against HEAD before this rewrite; violating one is reject noise):
//   - a match scrutinizes a def parameter or a bound field, NOTHING else:
//     no if, no computed scrutinees, no match in a let value, no applied
//     lambda-match. Every computed branch/destructure goes through a minted
//     continuation def (base.bend's own .if/.fin/.go architecture).
//   - destructuring lets ((a,b) = p, K{x} = v) are matches: params/fields
//     only.
//   - patterns name ALL fields, erased ones included; Nat literal patterns
//     (0n, 1n+p, 3n+p deep peels) are ctor sugar and fine; U32/F32/Word
//     literal or structural patterns DIE in the C emitter by design
//     ("a structural view of a machine word") — never emitted here, though
//     the JS emitter accepts them (asymmetry is by design, not a finding).
//   - defs are emitted in creation = dependency order; no forward refs.
//   - recursion descends structurally on the FIRST live column (Nat fuel
//     first); @unsafe opts out of descent and is emitted rarely.
//   - non-inferable values in let position ride `x = {v : T}` annotations;
//     do-binds are annotated (`x : T <- act`); partial applications stop at
//     exactly live-1 arguments (deeper partials die in js_book).
//   - infix ops: + - * / % .&. .|. .^. << >> (Nat rhs!) <= >= > && ||
//     +. -. *. /. %. ==. !=. <. <=. >. >=. ++ +n — there is no U32 <, ==
//     or != infix; those are calls folded through a minted Bool reader.
//
// Primitives with special compilation (comp.ts OPERATIONS/OPTIMIZED and
// base.bend's native claims) are all reachable: the full U32/F32/Nat op
// rosters, Bool/Cmp tables, String.append/cmp, Char packing, string and
// list literals, U32/Nat show+read roundtrips, Array new/get/set/swap/
// size/clone plus the a[i] / a[i] <- v sugar, Map/Set (the one family that
// runs as written), Nat constant tables (CONSTV), fork trees with `!` GPU
// marks, closures, partial application, erased params/fields.
//
// BATCHING (--batch N): N seeds merge into ONE compiled program — a
// concatenation at disjoint uid ranges, no book surgery — whose main
// prints each member's result/tail/extra in order, so clang and process
// spawn are paid once per batch while attribution stays per-line. The
// interp legs run per member (they are the bottleneck and parallelize
// across the worker pool). A member whose tail dies gets its own main
// block behind the FZ_MEMBER environment variable, so one binary serves
// the plain run and one run per dying member. A failing batch re-runs its
// members solo at uid base 0, so saved findings reproduce under a bare
// --seed N; a batch that fails when no member does is itself a finding
// (batch-only: the merge or whole-book emission is at fault).
//
// Findings land in findings/seed-N.bend (program + verdict header + exact
// repro line); resource blowups (timeouts, stack overflows — WONTFIX rule
// zero: the checker may diverge on any input) go to findings/skipped/ and
// are not failures. The generator is version-controlled but findings are
// not: a generator edit remaps the seeds whose draws reach the edited site
// (each adt, statement and minted def draws from its own split stream),
// so the saved program is the durable artifact; --reduce N shrinks one.

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
const FINDINGS = path.join(import.meta.dirname, "findings");
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
const VALUED_FLAGS = ["--seed", "--jobs", "--threads", "--opt", "--batch", "--pool", "--io-pct", "--reduce"];
const COUNT = Number(argv.find((a, i) => /^\d+$/.test(a) && !VALUED_FLAGS.includes(argv[i - 1] ?? "")) ?? "100");
const BASE_SEED = BigInt(cli_opt("--seed", String(Math.floor(Math.random() * 2 ** 48))));
const JOBS = Number(cli_opt("--jobs", String(Math.max(1, Math.min(8, os.cpus().length - 2)))));
// THREADS : 0 disables the CPU-parallel lane; N > 0 runs the C binary a
// second time with --threads N --gpu off and compares against the seq run
const THREADS = Number(cli_opt("--threads", "0"));
const WITH_METAL = cli_flag("--metal");
const WITH_CUDA = cli_flag("--cuda");
const IO_PCT = Math.max(0, Math.min(100, Number(cli_opt("--io-pct", "20"))));
const KEEP = cli_flag("--keep");
const PROFILE = cli_flag("--profile");
const BATCH = Math.max(1, Math.min(64, Number(cli_opt("--batch", "8"))));
const LOOP = cli_flag("--loop");
const SMOKE = cli_flag("--smoke");
const CHECK_ONLY = cli_flag("--check-only");
const OPT = "-O" + cli_opt("--opt", "1");
const REDUCE = cli_opt("--reduce", "");

function print_help(): void {
  process.stdout.write([
    "bend2 differential fuzzer — generates typed Bend programs and cross-checks",
    "the interpreter (spec), the compiled C backend (seq / threads / Metal /",
    "CUDA) and the compiled JS backend.",
    "",
    "Usage: bun fuzz.ts [count] [options]   (from the bend2-core repo root,",
    "       or with bend2-core as a sibling checkout)",
    "",
    "  count          seeds to run (default 100)",
    "",
    "Options:",
    "  --seed N       base seed (default: random; findings print their repro)",
    "  --jobs N       parallel batches in flight (default: min(8, cpus-2))",
    "  --threads N    ALSO run each C binary with --threads N --gpu off and",
    "                 compare against the sequential run (default 0 = off)",
    "  --metal        ALSO build each program with -DBEND_METAL and run",
    "                 --gpu on (macOS; GPU runs are serialized)",
    "  --cuda         ALSO build each program with -DBEND_CUDA and run",
    "                 --gpu on (Linux + NVIDIA)",
    "  --opt N        clang -O level for the C legs (default 1)",
    "  --batch N      seeds merged per compiled program, 1..64 (default 8)",
    "  --pool N       interp/emit worker pool size (default: from jobs)",
    "  --io-pct N     percent of seeds with a deterministic IO tail in main",
    "                 (file roundtrip, get_env, print_err, IO.die; default 20)",
    "  --check-only   stop after check + interp + emission (no cc, no runs)",
    "  --smoke        run the fixed smoke-seed set and assert feature coverage",
    "  --loop         run continuously until a finding",
    "  --keep         keep temporary build dirs",
    "  --profile      print a phase-timing report at the end",
    "  --dump         print the generated sealed program for --seed and exit",
    "  --dump-raw     print the raw (unsealed) sibling and exit",
    "  --reduce N     delta-reduce seed N's failing program (drop statements,",
    "                 the extra def, the IO tail, then unreferenced entries",
    "                 while the same failure holds) to findings/seed-N.min.bend",
    "  -h, --help     show this help and exit",
    "",
    "Findings land in findings/ (git-ignored) with a `repro:` header line;",
    "resource skips in findings/skipped/. See the top-of-file comment for the",
    "full model.",
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

function phase_sync<A>(name: string, f: () => A): A {
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

function seed_roll(seed: bigint, salt: bigint): number {
  return Number(rng_mix64(seed ^ salt) % 100n);
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

const PREC: Record<string, number> = {
  "||": 2, "&&": 3,
  "<=": 4, ">=": 4, ">": 4,
  "==.": 4, "!=.": 4, "<.": 4, "<=.": 4, ">.": 4, ">=.": 4,
  "++": 5, "+n": 10,
  ".|.": 6, ".^.": 7, ".&.": 8,
  "<<": 9, ">>": 9,
  "+": 10, "-": 10,
  "*": 11, "/": 11, "%": 11,
  "+.": 10, "-.": 10, "*.": 11, "/.": 11, "%.": 11,
};

type E = { s: string; p: number; head?: string };

const e_atom = (s: string): E => ({ s, p: 99 });
const e_call = (head: string, s: string): E => ({ s, p: 99, head });

function e_at(e: E): string {
  return e.p === 99 ? e.s : "(" + e.s + ")";
}

function e_bin(l: E, op: string, r: E): E {
  return { s: e_at(l) + " " + op + " " + e_at(r), p: PREC[op] };
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
  | { k: "adt"; a: Adt; qs: QT[]; args: T[] }
  | { k: "tup"; a: T; b: T; q: 1 | 2 }
  | { k: "fun"; q: BQ; dom: T; cod: T }
  | { k: "arr"; el: T }
  | { k: "map"; q: QT; v: T }
  | { k: "eql"; t: T; side: string };

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
};

const U32C: T = { k: "u32" };
const F32C: T = { k: "f32" };
const NATC: T = { k: "nat" };
const BOOLC: T = { k: "bool" };
const CMPC: T = { k: "cmp" };
const CHARC: T = { k: "char" };
const STRC: T = { k: "str" };
const UNITC: T = { k: "unit" };

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
    case "tvar": return t.n;
    case "adt": {
      if (t.qs.length + t.args.length === 0) {
        return t.a.name;
      }
      // the Fill sugar (all &1) drops the quantity block and stays safe
      const all1 = t.qs.length > 0 && t.qs.every((q) => q.k === "q" && q.q === 1);
      if (all1 && t.args.length > 0) {
        return t.a.name + "<" + t.args.map(ty_grp).join(", ") + ">";
      }
      return t.a.name + "<" + t.qs.map(qt_str).concat(t.args.map(ty_grp)).join(", ") + ">";
    }
    case "tup": {
      if (t.q === 2) {
        return "Sigma<&2, &2, " + ty_grp(t.a) + ", _ => " + ty_str(t.b) + ">";
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
    case "map": return "Map<" + qt_str(t.q) + ", " + ty_grp(t.v) + ">";
    case "eql": return "{" + t.side + " == " + t.side + " : " + ty_str(t.t) + "}";
  }
}

// ty_top : the annotation-site rendering — Plus sugar (all-&2 quantity
// blocks dropped behind a leading '+') fires here and only here
function ty_top(t: T): string {
  if (t.k === "adt" && t.qs.length > 0 && t.qs.every((q) => q.k === "q" && q.q === 2)) {
    return "+" + t.a.name + (t.args.length > 0 ? "<" + t.args.map(ty_grp).join(", ") + ">" : "");
  }
  if (t.k === "tup" && t.q === 2) {
    return "+Sigma<" + ty_grp(t.a) + ", _ => " + ty_str(t.b) + ">";
  }
  return ty_str(t);
}

// ty_grp : parenthesize where juxtaposition would mis-parse: arrow domains,
// tuple components inside other types, and type arguments (a FIRST argument
// after `<` commits on one token; parens are harmless on the rest)
function ty_grp(t: T): string {
  return t.k === "fun" || (t.k === "tup" && t.q === 1) ? "(" + ty_str(t) + ")" : ty_str(t);
}

function ty_eq(a: T, b: T): boolean {
  return ty_str(a) === ty_str(b);
}

// ty_quant : the type's kind quantity (a QT — may be open)
function ty_quant(t: T): QT {
  switch (t.k) {
    case "u32": case "f32": case "nat": case "bool": case "cmp":
    case "char": case "str": case "unit": case "eql":
      return Q2;
    case "tvar": return t.q;
    case "adt": {
      const m = new Map<string, QT>(t.a.qps.map((n, i) => [n, t.qs[i]]));
      return qt_sub(t.a.kind, m);
    }
    case "tup": return t.q === 2 ? Q2 : Q1;
    case "fun": return Q1;
    case "arr": return Q1;
    case "map": return t.q;
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
    case "adt": return { k: "adt", a: t.a, qs: t.qs.map((q) => qt_sub(q, qm)), args: t.args.map((x) => ty_sub(x, m, qm)) };
    case "tup": return { k: "tup", a: ty_sub(t.a, m, qm), b: ty_sub(t.b, m, qm), q: t.q };
    case "fun": return { k: "fun", q: t.q, dom: ty_sub(t.dom, m, qm), cod: ty_sub(t.cod, m, qm) };
    case "arr": return { k: "arr", el: ty_sub(t.el, m, qm) };
    case "map": return { k: "map", q: qt_sub(t.q, qm), v: ty_sub(t.v, m, qm) };
    default: return t;
  }
}

// ty_open : does the type mention an abstract type or quantity variable?
function ty_open(t: T): boolean {
  switch (t.k) {
    case "tvar": return true;
    case "adt": return t.args.some(ty_open) || t.qs.some((q) => qt_known(q) === null);
    case "tup": return ty_open(t.a) || ty_open(t.b);
    case "fun": return ty_open(t.dom) || ty_open(t.cod);
    case "arr": return ty_open(t.el);
    case "map": return qt_known(t.q) === null || ty_open(t.v);
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
  if (pat.k === "adt" && goal.k === "adt") {
    if (pat.a !== goal.a) {
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
  ps: Array<{ q: BQ; t: T }>;
  ret: T;
  mask?: Array<number | null>;
};

type State = {
  uid: number;
  entries: string[];
  adts: Adt[];
  defr: DefR[];
  memo: Map<string, string>;
  wip: Set<string>;
  mints: number;
  feat: Record<string, number>;
  // pure : true while generating the interp-visible side — no F32
  // computation may flow into the fold (base's F32 ops are stuck in the
  // interpreter: native claims with no body)
  pure: boolean;
  // trans : set when a member computes a float transcendental — JS-vs-C
  // on the extra line downgrades to a counted skip for that member
  trans: boolean;
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
  }
  feat(k: string): void {
    this.s.feat[k] = (this.s.feat[k] ?? 0) + 1;
  }
  get entries(): string[] {
    return this.s.entries;
  }
  get adts(): Adt[] {
    return this.s.adts;
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

function ctx_new(seed: bigint, uid0: number): Ctx {
  return new Ctx({ uid: uid0, entries: [], adts: [], defr: [], memo: new Map(), wip: new Set(),
    mints: 0, feat: {}, pure: true, trans: false }, new Gen(rng_mix64(seed)));
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

type V = { name: string; ty: T; q: "lone" | "many" | "dead" };

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
  const name = stem + String(c.uid());
  c.memo.set(key, name);
  c.push(body(c.sub("helper"), name));
  return name;
}

// helper_bool : Bool -> U32 (0/1) — the bridge every comparison fold rides
function helper_bool(c: Ctx): string {
  return helper(c, "bool", "bu", (c, n) => "def " + n + "(b: Bool) -> U32:\n  match b:\n    case False{}:\n      0\n    case True{}:\n      1");
}

function helper_cmp(c: Ctx): string {
  return helper(c, "cmp", "cu", (c, n) => "def " + n + "(c: Cmp) -> U32:\n  match c:\n    case LT{}:\n      " + String(c.g.int(64))
    + "\n    case EQ{}:\n      " + String(64 + c.g.int(64)) + "\n    case GT{}:\n      " + String(128 + c.g.int(64)));
}

function helper_chr(c: Ctx): string {
  return helper(c, "chr", "ch", (c, n) => "def " + n + "(c: Char) -> U32:\n  Chr{n} = c\n  n");
}

// helper_strlen : String -> U32 with a rolling code hash (exercises SCon
// elimination and Char packing)
function helper_strlen(c: Ctx): string {
  return helper(c, "strlen", "sl", (c, n) => "def " + n + "(s: String, +acc: U32) -> U32:\n  match s:\n    case SNil{}:\n      acc\n    case SCon{h, t}:\n      "
    + n + "(t, (acc * 31 + " + helper_chr(c) + "(h)))");
}

// helper_may / helper_maynat : Maybe<&2, U32|Nat> -> U32 (show/read roundtrips)
function helper_may(c: Ctx): string {
  return helper(c, "may", "mu", (c, n) => "def " + n + "(m: Maybe<&2, U32>, alt: U32) -> U32:\n  match m:\n    case None{}:\n      alt\n    case Some{v}:\n      v");
}

function helper_maynat(c: Ctx): string {
  return helper(c, "maynat", "mn", (c, n) => "def " + n + "(m: Maybe<&2, Nat>, alt: U32) -> U32:\n  match m:\n    case None{}:\n      alt\n    case Some{v}:\n      U32.from_nat(v)");
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
      return e_fn(helper_may(c), e_fn("U32.read", e_fn("U32.show", num_gen_u32(c, env, fuel - 1))), num_lit_u32(c));
    }],
    [!c.pure ? 6 : 0, () => {
      c.feat("f32-conv");
      return e_fn("F32.to_u32", num_gen_f32(c, env, fuel - 1));
    }],
    [!c.pure ? 3 : 0, () => {
      c.feat("f32-cmp");
      const op = c.g.pick(["==.", "!=.", "<.", "<=.", ">.", ">=."]);
      return e_fn(helper_bool(c), e_bin(num_gen_f32(c, env, fuel - 1), op, num_gen_f32(c, env, fuel - 1)));
    }],
    [fuel >= 2 ? 5 : 0, () => tail_call(c, env, fuel)],
    [fuel >= 2 ? 4 : 0, () => syn_call_unify(c, U32C, env, fuel) ?? num_lit_u32(c)],
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
    [3, () => {
      c.feat("nat-showread");
      return e_fn("U32.to_nat", e_bin(e_fn(helper_maynat(c), e_fn("Nat.read", e_fn("Nat.show", num_gen_nat(c, env, fuel - 1))), num_lit_u32(c)), "%", e_atom("1024")));
    }],
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

function syn_ty(c: Ctx, fuel: number, need: QT, tvars: TvarInfo[] = [], qvars: string[] = []): T {
  const fits = (t: T): boolean => qt_fits(ty_quant(t), need);
  const tfit = tvars.filter((tv) => qt_fits(tv.q, need));
  const pick_qt = (): QT => {
    if (qvars.length > 0 && c.g.chance(0.4)) {
      return { k: "qv", n: c.g.pick(qvars) };
    }
    return c.g.chance(0.5) ? Q1 : Q2;
  };
  const needData = qt_known(need) === 2;
  return c.g.wpick<() => T>([
    [16, () => U32C],
    [!c.pure ? 8 : 3, () => F32C],
    [8, () => NATC],
    [6, () => BOOLC],
    [3, () => CMPC],
    [4, () => CHARC],
    [6, () => STRC],
    [3, () => UNITC],
    [tfit.length > 0 ? 18 : 0, () => {
      const tv = c.g.pick(tfit);
      return { k: "tvar", n: tv.n, q: tv.q } as T;
    }],
    // an instantiated datatype (generated or base generic): draw the
    // quantity args, then the type args at their substituted kinds; the
    // whole instance's kind must fit the slot
    [fuel > 0 ? 22 : 0, () => {
      const cands = c.adts.concat([BASE.List, BASE.Maybe, BASE.Either, BASE.Result]);
      for (let tries = 0; tries < 3; tries++) {
        const a = c.g.pick(cands);
        const qs = a.qps.map(() => needData ? Q2 : pick_qt());
        const qm = new Map<string, QT>(a.qps.map((n, i) => [n, qs[i]]));
        const inst_kind = qt_sub(a.kind, qm);
        if (!qt_fits(inst_kind, need)) {
          continue;
        }
        const args = a.tps.map((tp) => syn_ty(c, fuel - 1, qt_sub(tp.q, qm), tvars, qvars));
        return { k: "adt", a, qs, args } as T;
      }
      return U32C;
    }],
    [fuel > 0 ? 8 : 0, () => {
      const q: 1 | 2 = needData ? 2 : c.g.chance(0.3) ? 2 : 1;
      const el = (): T => syn_ty(c, fuel - 1, q === 2 ? Q2 : need, tvars, qvars);
      return { k: "tup", a: el(), b: el(), q } as T;
    }],
    [fuel > 0 && !needData ? 7 : 0, () => {
      const q: BQ = c.g.wpick<BQ>([[7, 1], [2, 0], [1, 2]]);
      const dom = q === 2 ? syn_ty(c, 0, Q2, tvars, qvars) : syn_ty(c, fuel - 1, Q0, tvars, qvars);
      return { k: "fun", q, dom, cod: syn_ty(c, fuel - 1, Q0, tvars, qvars) } as T;
    }],
    [fuel > 0 && c.g.chance(0.4) ? 4 : 0, () => {
      const q = needData ? Q2 : pick_qt();
      return { k: "map", q, v: syn_ty(c, 0, q, tvars, qvars) } as T;
    }],
  ])();
}

// Adt minting
// -----------
// Flavors: "data" (is Data, concrete Data fields), "qpoly" (quantity
// parameters + Kind(a) / Kind(a <&> b), parameter-typed fields), "type"
// (is Type: closure and Array-free function fields welcome). Ctor 0 never
// recurs; self fields keep uniform recursion so minted folds descend.

function adt_new(c: Ctx): Adt {
  const id = c.uid();
  const name = "D" + String(id);
  const flavor = c.g.wpick<string>([[5, "data"], [4, "qpoly"], [2, "type"]]);
  const nqp = flavor === "qpoly" ? 1 + c.g.int(2) : 0;
  const qps = ["qa", "qb"].slice(0, nqp);
  const ntp = flavor === "qpoly" ? Math.max(1, c.g.int(3)) : flavor === "type" ? c.g.int(2) : 0;
  const tps: Array<{ n: string; q: QT }> = [];
  for (let i = 0; i < ntp; i++) {
    const q: QT = nqp > 0 ? { k: "qv", n: qps[i % nqp] } : Q1;
    tps.push({ n: "T" + String(i), q });
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
  const a: Adt = { name, qps, tps, kind, ctors: [], rec: false };
  const selfT: T = {
    k: "adt", a, qs: qps.map((n) => ({ k: "qv", n }) as QT),
    args: tps.map((tp) => ({ k: "tvar", n: tp.n, q: tp.q }) as T),
  };
  const tvinfo: TvarInfo[] = tps.map((tp) => ({ n: tp.n, q: tp.q }));
  const nctors = size_pick(c, 1 + c.g.int(3), 24);
  for (let ci = 0; ci < nctors; ci++) {
    const fields: Field[] = [];
    const nf = size_pick(c, c.g.int(4), 8);
    for (let f = 0; f < nf; f++) {
      const eq = c.g.chance(0.12) ? 0 : 1;
      if (eq === 0) {
        // erased field: any type fits Kind(&0)
        c.feat("erased-field");
        fields.push({ q: 0, t: syn_ty(c, 1, Q0, tvinfo, qps) });
        continue;
      }
      const self = ci > 0 && c.g.chance(0.3);
      if (self) {
        a.rec = true;
        fields.push({ q: 1, t: selfT });
        continue;
      }
      // a live field's kind must fit Kind(G): parameter types fit by
      // construction (their kind is a side of the meet), Data fits all,
      // and a "type"-kinded family also takes functions
      let t: T;
      if (flavor === "type" && c.g.chance(0.35)) {
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
    a.ctors.push({ name: name + ("abcd"[ci] ?? "k" + String(ci)), fields });
  }
  const head = qps.concat(tps.map((tp) => "-" + tp.n + ": Kind(" + qt_bare(tp.q) + ")"));
  const kind_s = flavor === "data" ? "Data" : flavor === "type" ? "Type" : "Kind(" + qt_bare(kind) + ")";
  const rows = a.ctors.map((ct) => "  " + ct.name + "{"
    + ct.fields.map((f, i) => bq_prefix(f.q) + "g" + String(i) + ": " + ty_top(f.t)).join(", ") + "}");
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
    return { k: "adt", a, qs, args };
  }
  return null;
}

// Pattern helpers
// ---------------

// adt_row : one match row for a ctor of an instantiated adt — pattern text
// plus the bound field vars (erased fields bind but stay dead)
function adt_row(c: Ctx, t: Extract<T, { k: "adt" }>, ct: Ctor, scrMany: boolean): { pat: string; vs: V[] } {
  const m = new Map<string, T>(t.a.tps.map((tp, i) => [tp.n, t.args[i]]));
  const qm = new Map<string, QT>(t.a.qps.map((n, i) => [n, t.qs[i]]));
  const vs: V[] = [];
  const names: string[] = [];
  for (let i = 0; i < ct.fields.length; i++) {
    const f = ct.fields[i];
    const nm = "m" + String(c.uid());
    names.push(nm);
    const ft = ty_sub(f.t, m, qm);
    if (f.q === 0) {
      continue;
    }
    const many = (f.q === 2 || scrMany) && ty_data(ft);
    vs.push(v_new(nm, ft, many));
  }
  return { pat: ct.name + "{" + names.join(", ") + "}", vs };
}

// Readers
// -------
// rd_ensure(c, t): a memoized `def rd(x: T) -> U32` structural fold. Every
// live field folds in (nothing dead) except F32 on the c.pure side, which is
// dropped — base's F32 ops are stuck in the interpreter. Literal salts
// keep arms distinguishable.

function rd_ensure(c: Ctx, t: T): string {
  const key = "rd:" + (c.pure ? "p:" : "x:") + ty_str(t);
  const got = c.memo.get(key);
  if (got !== undefined) {
    if (c.wip.has(key)) {
      throw new Error("rd_ensure knot: " + key);
    }
    return got;
  }
  const name = "rd" + String(c.uid());
  c.memo.set(key, name);
  c.wip.add(key);
  c = c.sub("rd");
  const salt = (): string => String(1 + c.g.int(99));
  const def1 = (param: string, body: string): string => "def " + name + "(" + param + ") -> U32:\n  " + body;
  const src = ((): string => {
    switch (t.k) {
      case "u32": return def1("x: U32", "x + " + salt());
      case "f32": return def1("x: F32", c.pure ? salt() : "F32.to_u32(x *. " + num_lit_f32(c, false).s + ")");
      case "nat": return def1("x: Nat", "U32.from_nat(x) + " + salt());
      case "bool": return def1("x: Bool", helper_bool(c) + "(x) + " + salt());
      case "cmp": return def1("x: Cmp", helper_cmp(c) + "(x) * " + String(1 + c.g.int(9)));
      case "char": return def1("x: Char", helper_chr(c) + "(x) + " + salt());
      case "str": return def1("x: String", helper_strlen(c) + "(x, " + salt() + ")");
      case "unit": return def1("x: Unit", "match x:\n    case Unit{}:\n      " + salt());
      case "tup": {
        const ra = rd_ensure(c, t.a);
        const rb = rd_ensure(c, t.b);
        return def1("x: " + ty_str(t), "(ta, tb) = x\n  " + ra + "(ta) + " + rb + "(tb)");
      }
      case "fun": {
        const app = "f(" + e_at(syn(c, t.dom, [], 1)) + ")";
        const rc = t.cod.k === "u32" ? null : rd_ensure(c, t.cod);
        return def1("f: " + ty_grp(t), rc === null ? app + " + " + salt() : rc + "(" + app + ")");
      }
      case "map": {
        const rv = rd_ensure(c, t.v);
        const sl = helper_strlen(c);
        return def1("m: Map<" + qt_str(t.q) + ", " + ty_grp(t.v) + ">", "match m:\n"
          + "    case MTip{}:\n      " + salt() + "\n"
          + "    case MLeaf{key, val}:\n      " + sl + "(key, 3) + " + rv + "(val)\n"
          + "    case MNode{pos, lo, hi}:\n      U32.from_nat(pos) + " + name + "(lo) + " + name + "(hi)");
      }
      case "adt": return rd_adt(c, name, t);
      default: return def1("x: " + ty_str(t), salt());
    }
  })();
  c.push(src);
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 1, t }], ret: U32C });
  c.wip.delete(key);
  return name;
}

function rd_adt(c: Ctx, name: string, t: Extract<T, { k: "adt" }>): string {
  const m = new Map<string, T>(t.a.tps.map((tp, i) => [tp.n, t.args[i]]));
  const qm = new Map<string, QT>(t.a.qps.map((n, i) => [n, t.qs[i]]));
  const rows = t.a.ctors.map((ct) => {
    const vs = ct.fields.map((_, i) => "x" + String(i));
    const parts: E[] = [];
    ct.fields.forEach((f, i) => {
      if (f.q === 0) {
        return;
      }
      const ft = ty_sub(f.t, m, qm);
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
        parts.push(e_atom(rd_ensure(c, ft) + "(" + vs[i] + ")"));
      }
    });
    parts.push(num_lit_u32(c));
    return "    case " + ct.name + "{" + vs.join(", ") + "}:\n      " + e_at(num_combine(c, parts));
  });
  if (t.a.ctors.length === 0) {
    return "def " + name + "(x: " + ty_str(t) + ") -> U32:\n  match x:";
  }
  return "def " + name + "(x: " + ty_str(t) + ") -> U32:\n  match x:\n" + rows.join("\n");
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
  const name = "mk" + String(c.uid());
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
  const senv: V[] = [{ name: "s", ty: U32C, q: "many" }];
  const fld = (ct: Ctor, self: string): string[] =>
    ct.fields.map((f) => {
      if (is_self(f) && self !== "") {
        return self;
      }
      const ft = ty_sub(f.t, m, qm);
      return e_at(syn(c, ft, ct === base ? [] : senv, 0));
    });
  const brow = base.name + "{" + fld(base, "").join(", ") + "}";
  if (recs.length === 0) {
    c.push("def " + name + "(+n: Nat, +s: U32) -> " + ty_str(t) + ":\n  " + brow);
  } else {
    c.push("def " + name + "(+n: Nat, +s: U32) -> " + ty_str(t) + ":\n  match n:\n    case 0n:\n      "
      + brow + "\n    case 1n+p:\n      " + rec.name + "{" + fld(rec, name + "(p, (s * 3 + 7))").join(", ") + "}");
  }
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 2, t: NATC }, { q: 2, t: U32C }], ret: t, mask: [8 + c.g.int(8), null] });
  return name;
}

// builder_call : a built value of an instantiated recursive adt
function builder_call(c: Ctx, t: Extract<T, { k: "adt" }>, env: V[], cap: number): E {
  const name = builder_ensure(c, t);
  const reg = c.defr.find((d) => d.name === name);
  const depth = Math.min(reg?.mask?.[0] ?? 8, cap);
  const fuel = "U32.to_nat(" + e_at(num_gen_u32(c, env, 1)) + " % " + String(Math.max(2, depth)) + ")";
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
  const name = "tf" + String(c.uid());
  c.memo.set(key, name);
  c = c.sub("tf");
  const a = t.a;
  const m = new Map<string, T>(a.tps.map((tp, i) => [tp.n, t.args[i]]));
  const qm = new Map<string, QT>(a.qps.map((n, i) => [n, t.qs[i]]));
  const rows = a.ctors.map((ct) => {
    const vs = ct.fields.map((_, i) => "x" + String(i));
    const args = ct.fields.map((f, i) => {
      if (f.q === 0) {
        return vs[i];
      }
      const ft = ty_sub(f.t, m, qm);
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
  const body = a.ctors.length === 0 ? "  match x:" : "  match x:\n" + rows.join("\n");
  c.push("def " + name + "(x: " + ty_str(t) + ") -> " + ty_str(t) + ":\n" + body);
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 1, t }], ret: t });
  return name;
}

// Tail loops
// ----------
// def tl(+n: Nat, a0: U32, ..) -> U32 — countdown state machines: the
// compiled seq machine's bread and butter (WL_SPIN when fused at a cut).
// Deep peels (case 3n+p) exercise the flattener's Succ chains.

function tail_call(c: Ctx, env: V[], fuel: number): E {
  c.feat("tail");
  c = c.sub("tail");
  const name = "tl" + String(c.uid());
  const naccs = c.g.decay(0.35);
  const accs = Array.from({ length: naccs }, (_, i) => "a" + String(i));
  const henv: V[] = accs.map((a2) => v_new(a2, U32C, true));
  const base = e_at(num_combine(c, accs.map((a2) => e_atom(a2)).concat([num_lit_u32(c)])));
  const peel = c.g.chance(0.25) ? 2 + c.g.int(3) : 1;
  if (peel > 1) {
    c.feat("peel");
  }
  const step = (): string[] => accs.map(() => e_at(num_gen_u32(c, henv.map((v) => ({ ...v })), 1)));
  let arms: string;
  if (peel === 1) {
    arms = "  match n:\n    case 0n:\n      " + base + "\n    case 1n+p:\n      " + name + "(p, " + step().join(", ") + ")";
  } else {
    arms = "  match n:\n    case " + String(peel) + "n+p:\n      " + name + "(p, " + step().join(", ") + ")\n    case q:\n      " + base;
  }
  const params = ["+n: Nat"].concat(accs.map((a2) => "+" + a2 + ": U32"));
  c.push("def " + name + "(" + params.join(", ") + ") -> U32:\n" + arms);
  const iters = c.pure ? 2 + c.g.int(size_pick(c, 90, 900)) : size_pick(c, 200 + c.g.int(4000), 200000);
  c.defr.push({ name, qps: [], tps: [], ps: params.map((_, i) => ({ q: 2 as BQ, t: i === 0 ? NATC : U32C })), ret: U32C, mask: [iters, ...accs.map(() => null)] });
  const fuelArg = "U32.to_nat(" + e_at(num_gen_u32(c, env, 1)) + " % " + String(iters) + ")";
  const args = accs.map(() => e_at(num_gen_u32(c, env, Math.min(fuel - 1, 1))));
  return e_call(name, name + "(" + [fuelArg].concat(args).join(", ") + ")");
}

// Syn: values
// -----------
// syn(c, goal, env, fuel): produce a term of type goal. Productions per goal
// head: matching env vars, intro forms, unifying registry calls, builders.
// Results may be intro-headed (non-inferable) — callers placing them in an
// INFER position (a bare let) must annotate; every field/argument hole
// here is a checked position.

function syn(c: Ctx, goal: T, env: V[], fuel: number): E {
  const direct = env.filter((v) => v.q !== "dead" && ty_eq(v.ty, goal));
  const var_w = direct.length > 0 ? 30 : 0;
  const pick_var = (): E => e_atom(env_take(c.g.pick(direct)));
  const uni = (): E | null => fuel >= 1 ? syn_call_unify(c, goal, env, fuel) : null;
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
        [fuel > 0 ? 8 : 0, () => {
          c.feat("bool-ops");
          const op = c.g.pick(["Bool.and", "Bool.or", "Bool.xor"]);
          return e_fn(op, syn(c, BOOLC, env, fuel - 1), syn(c, BOOLC, env, fuel - 1));
        }],
        [fuel > 0 ? 5 : 0, () => e_bin(syn(c, BOOLC, env, fuel - 1), c.g.pick(["&&", "||"]), syn(c, BOOLC, env, fuel - 1))],
        [fuel > 0 ? 4 : 0, () => e_fn("Bool.not", syn(c, BOOLC, env, fuel - 1))],
        [fuel > 0 ? 4 : 0, () => e_fn("Nat.is_lt", num_gen_nat(c, env, fuel - 1), num_gen_nat(c, env, fuel - 1))],
        [fuel > 0 && !c.pure ? 5 : 0, () => e_bin(num_gen_f32(c, env, fuel - 1), c.g.pick(["==.", "!=.", "<.", "<=.", ">.", ">=."]), num_gen_f32(c, env, fuel - 1))],
      ])();
    }
    case "cmp": {
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [15, () => e_atom(c.g.pick(["LT{}", "EQ{}", "GT{}"]))],
        [fuel > 0 ? 15 : 0, () => e_fn("U32.cmp", num_gen_u32(c, env, fuel - 1), num_gen_u32(c, env, fuel - 1))],
        [fuel > 0 ? 6 : 0, () => e_fn("Nat.cmp", num_gen_nat(c, env, fuel - 1), num_gen_nat(c, env, fuel - 1))],
        [fuel > 0 ? 5 : 0, () => e_fn("Bool.cmp", syn(c, BOOLC, env, fuel - 1), syn(c, BOOLC, env, fuel - 1))],
      ])();
    }
    case "char": {
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [25, () => e_atom("'" + str_char(c) + "'")],
        [fuel > 0 ? 8 : 0, () => e_atom("Chr{" + e_at(e_bin(num_gen_u32(c, env, fuel - 1), "%", e_atom("55000"))) + "}")],
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
      c.feat("eql");
      return e_atom("{==}");
    }
    case "tup": {
      const intro = (): E => e_atom("(" + e_at(syn(c, goal.a, env, Math.max(0, fuel - 1))) + ", " + e_at(syn(c, goal.b, env, Math.max(0, fuel - 1))) + ")");
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [30, intro],
        [8, () => uni() ?? intro()],
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
      const lam = (): E => {
        const b = "y" + String(c.uid());
        if (goal.q === 0) {
          // erased domain: the binder is dead inside
          const body = e_at(syn(c, goal.cod, env, Math.min(Math.max(0, fuel - 1), 2)));
          return e_atom(b + " => " + body);
        }
        const bv = v_new(b, goal.dom, goal.q === 2);
        return e_atom(b + " => " + e_at(syn(c, goal.cod, env.concat([bv]), Math.min(fuel, 1))));
      };
      return c.g.wpick<() => E>([
        [var_w, pick_var],
        [35, lam],
        // partial application: a registry def missing EXACTLY its last
        // argument (deeper partials die in js_book)
        [fuel >= 1 && goal.q === 1 ? 15 : 0, () => {
          const cands = c.defr.filter((d) =>
            d.qps.length === 0 && d.tps.length === 0 && d.ps.length >= 1
            && ty_eq(d.ps[d.ps.length - 1].t, goal.dom) && ty_eq(d.ret, goal.cod)
            && d.ps[d.ps.length - 1].q === 1
            && (d.mask?.[d.ps.length - 1] ?? null) === null);
          if (cands.length === 0) {
            return lam();
          }
          c.feat("partial");
          const d = c.g.pick(cands);
          const front = d.ps.slice(0, -1).map((p, i) => syn_def_arg(c, d, i, p.t, env, Math.max(0, fuel - 1)));
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
          const ft = ty_sub(f.t, m, qm);
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
          return e_atom("[" + els.join(", ") + "]");
        }],
        [a.rec && fuel > 0 && !ty_open(goal) ? 20 : 0, () => builder_call(c, goal as Extract<T, { k: "adt" }>, env, c.pure ? 10 : 16)],
        [!ty_open(goal) && fuel >= 1 ? 6 : 0, () => {
          c.feat("reuse");
          return e_atom(tf_ensure(c, goal as Extract<T, { k: "adt" }>) + "(" + e_at(syn(c, goal, env, Math.max(0, fuel - 1))) + ")");
        }],
        [8, () => uni() ?? intro()],
      ])();
    }
    case "arr": {
      // arrays are linear and live in the array kit; a bare goal builds one
      const d = 1 + c.g.int(3);
      return e_fn("Array.new", e_atom(ty_grp(goal.el)), e_atom(String(d) + "n"), syn(c, goal.el, env, 0));
    }
  }
}

function syn_def_arg(c: Ctx, d: DefR, i: number, t: T, env: V[], fuel: number): string {
  const mask = d.mask?.[i] ?? null;
  if (mask !== null && t.k === "nat") {
    return "U32.to_nat(" + e_at(num_gen_u32(c, env, fuel)) + " % " + String(mask) + ")";
  }
  const fenv = d.ps[i].q === 1 ? env : env.filter((v) => v.q === "many");
  const e = syn(c, t, fenv, fuel);
  if (mask !== null && t.k === "u32") {
    return e_at(e_bin(e, "%", e_atom(String(mask))));
  }
  return e_at(e);
}

// syn_call_unify : call any registered def whose return type unifies with
// the goal — quantity variables and type variables both bind; leftovers
// draw fresh (&1/&2, fitting types).
function syn_call_unify(c: Ctx, goal: T, env: V[], fuel: number): E | null {
  const cands: Array<{ d: DefR; m: Map<string, T>; qm: Map<string, QT> }> = [];
  for (const d of c.defr) {
    const m = new Map<string, T>();
    const qm = new Map<string, QT>();
    if (ty_unify(d.ret, goal, m, qm)) {
      cands.push({ d, m, qm });
    }
  }
  if (cands.length === 0) {
    return null;
  }
  const { d, m, qm } = c.g.pick(cands);
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
  const ps = d.ps.map((p) => ({ q: p.q, t: ty_sub(p.t, m, qm) }));
  if (ps.some((p) => (p.q === 2 && !ty_data(p.t)) || ty_open(p.t))) {
    return null;
  }
  if (d.qps.length > 0) {
    c.feat("qpoly-call");
  } else if (d.tps.length > 0) {
    c.feat("generic-call");
  }
  const args = ps.map((p, i) => syn_def_arg(c, { ...d, ps }, i, p.t, env, Math.max(0, fuel - 1)));
  const qargs = d.qps.map((qp) => qt_str(qm.get(qp) as QT));
  const targs = d.tps.map((tp) => ty_grp(m.get(tp.n) as T));
  return e_call(d.name, d.name + "(" + qargs.concat(targs, args).join(", ") + ")");
}

// Minted defs
// -----------
// syn_mint_def : a fresh def returning the goal, with -/plain/+ parameter
// sigils drawn per position; occasionally split as assert + fill, and
// rarely @unsafe (skips descent — still terminating by construction).

function syn_mint_def(c: Ctx, goal: T, env: V[]): E | null {
  if (goal.k === "eql" || goal.k === "arr" || ty_open(goal) || c.mints >= 10) {
    return null;
  }
  c.mints++;
  c.feat("mint");
  c = c.sub("mint");
  const name = "fn" + String(c.uid());
  const nps = 1 + c.g.int(3);
  const ps: Array<{ q: BQ; t: T }> = [];
  for (let i = 0; i < nps; i++) {
    const t = syn_ty(c, 1, Q0, [], []);
    const q: BQ = c.g.wpick<BQ>([[7, 1], [2, 0], [ty_data(t) ? 3 : 0, 2]]);
    ps.push({ q, t });
  }
  if (ps.some((p) => p.q === 0)) {
    c.feat("erased-param");
  }
  const penv = ps.map((p, i) => {
    const v = v_new("p" + String(i), p.t, p.q === 2);
    if (p.q === 0) {
      v.q = "dead";
    }
    return v;
  }).filter((v) => v.q !== "dead");
  let body: E;
  try {
    body = syn(c, goal, penv, 2);
  } catch {
    c.mints--;
    return null;
  }
  const params = ps.map((p, i) => bq_prefix(p.q) + "p" + String(i) + ": " + ty_top(p.t));
  const split = c.g.chance(0.2);
  if (split) {
    c.feat("assert-def");
    c.push("assert " + name + ":\n" + ps.map((p, i) => "  forall " + bq_prefix(p.q) + "p" + String(i) + ": " + ty_top(p.t)).join("\n")
      + "\n  " + ty_top(goal) + "\n\ndef " + name + "(" + ps.map((_, i) => "p" + String(i)).join(", ") + "):\n  " + e_at(body));
  } else {
    const unsafe = c.g.chance(0.06);
    if (unsafe) {
      c.feat("unsafe");
    }
    c.push((unsafe ? "@unsafe\n" : "") + "def " + name + "(" + params.join(", ") + ") -> " + ty_str(goal) + ":\n  " + e_at(body));
  }
  const d: DefR = { name, qps: [], tps: [], ps, ret: goal };
  c.defr.push(d);
  const args = ps.map((p, i) => syn_def_arg(c, d, i, p.t, env, 1));
  return e_call(name, name + "(" + args.join(", ") + ")");
}

// generic_mint : a quantity- and type-polymorphic def. The tvar-typed
// parameter is strictly linear inside (its kind is abstract, so + cannot
// form); recursion over List<a, A> descends past the erased columns.
function generic_mint(c: Ctx): void {
  c.feat("qpoly-def");
  c = c.sub("generic");
  const name = "g" + String(c.uid());
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
      + "  match l:\n    case Nil{}:\n      acc\n    case Con{h, t}:\n      " + name + "(" + qps[0] + ", A, t, acc + " + String(1 + c.g.int(9)) + ")");
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

// Match trees
// -----------
// Minted defs whose bodies are matches over their own parameters — the
// only lawful scrutinees. Nat switches (constant tables, deep peels),
// Bool/Cmp products, adt folds with nested field matches.

function match_nat_def(c: Ctx, env: V[], fuel: number): E {
  c.feat("match-nat");
  c = c.sub("match");
  const name = "mt" + String(c.uid());
  const style = c.g.wpick<string>([[4, "table"], [3, "peel"], [3, "nest"]]);
  let body: string;
  if (style === "table") {
    // 3+ constant word entries: the CONSTV/TAB_AT special
    c.feat("nat-table");
    const n = 3 + c.g.int(size_pick(c, 4, 40));
    const rows: string[] = [];
    for (let i = 0; i < n; i++) {
      rows.push("    case " + String(i) + "n:\n      " + String(c.g.int(100000)));
    }
    rows.push("    case k:\n      " + String(c.g.int(1000)));
    body = "  match n:\n" + rows.join("\n");
  } else if (style === "peel") {
    const k = 2 + c.g.int(4);
    c.feat("peel");
    body = "  match n:\n    case " + String(k) + "n+p:\n      U32.from_nat(p) + " + String(c.g.int(64))
      + "\n    case q:\n      U32.from_nat(q) * " + String(2 + c.g.int(9));
  } else {
    c.feat("match-nest");
    body = "  match n:\n    case 0n:\n      " + String(c.g.int(64))
      + "\n    case 1n+p:\n      match p:\n        case 0n:\n          " + String(c.g.int(64))
      + "\n        case 1n+q:\n          U32.from_nat(q) + " + String(c.g.int(64));
  }
  c.push("def " + name + "(n: Nat) -> U32:\n" + body);
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 1, t: NATC }], ret: U32C, mask: [64] });
  return e_call(name, name + "(U32.to_nat(" + e_at(num_gen_u32(c, env, Math.min(fuel, 1))) + " % 64))");
}

function match_bool_def(c: Ctx, env: V[], fuel: number): E {
  c.feat("match-bool");
  c = c.sub("match");
  const name = "mb" + String(c.uid());
  const two = c.g.chance(0.4);
  let body: string;
  if (two) {
    c.feat("match-multi");
    const arm = (): string => e_at(num_gen_u32(c, [], 1));
    body = "  match a b:\n    case False{} False{}:\n      " + arm()
      + "\n    case False{} True{}:\n      " + arm()
      + "\n    case True{} False{}:\n      " + arm()
      + "\n    case True{} True{}:\n      " + arm();
    c.push("def " + name + "(a: Bool, b: Bool) -> U32:\n" + body);
    c.defr.push({ name, qps: [], tps: [], ps: [{ q: 1, t: BOOLC }, { q: 1, t: BOOLC }], ret: U32C });
    return e_call(name, name + "(" + e_at(syn(c, BOOLC, env, fuel)) + ", " + e_at(syn(c, BOOLC, env, fuel)) + ")");
  }
  // the branchless OR-mask special: two constant equality tests on one var
  c.feat("bool-ormask");
  const k1 = String(c.g.int(64));
  const k2 = String(c.g.int(64));
  body = "  match b:\n    case False{}:\n      " + helper_bool(c) + "(U32.is_eq(x, " + k1 + "))"
    + "\n    case True{}:\n      " + helper_bool(c) + "(U32.is_eq(x, " + k2 + "))";
  c.push("def " + name + "(b: Bool, +x: U32) -> U32:\n" + body);
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 1, t: BOOLC }, { q: 2, t: U32C }], ret: U32C });
  return e_call(name, name + "(" + e_at(syn(c, BOOLC, env, fuel)) + ", " + e_at(num_gen_u32(c, env, 1)) + ")");
}

function match_adt_def(c: Ctx, env: V[], fuel: number): E | null {
  const closed = c.adts.filter((a) => a.ctors.length > 0);
  if (closed.length === 0) {
    return null;
  }
  c.feat("match-adt");
  c = c.sub("match");
  const a = c.g.pick(closed);
  const t = adt_inst(c, a, false);
  if (t === null || t.k !== "adt") {
    return null;
  }
  const name = "ma" + String(c.uid());
  const scrMany = ty_data(t) && c.g.chance(0.3);
  const rows = a.ctors.map((ct) => {
    const { pat, vs } = adt_row(c, t, ct, scrMany);
    // nested match on the LAST bound field when it is a Bool (a nested
    // scrutinee must be the pattern's last binder), else a fold
    const last = ct.fields[ct.fields.length - 1];
    const nest = last !== undefined && last.q !== 0 && vs[vs.length - 1]?.ty.k === "bool" && c.g.chance(0.3)
      ? vs[vs.length - 1] : undefined;
    if (nest !== undefined) {
      c.feat("match-nest");
      const rest = vs.filter((v) => v !== nest);
      const arm = (): string => e_at(num_combine(c, rest.filter((v) => v.ty.k === "u32").map((v) => e_atom(v.name)).concat([num_lit_u32(c)])));
      return "    case " + pat + ":\n      match " + nest.name + ":\n        case False{}:\n          " + arm() + "\n        case True{}:\n          " + arm();
    }
    const parts = vs.map((v) => {
      if (v.ty.k === "u32") {
        return e_atom(v.name);
      }
      if (v.ty.k === "f32" && c.pure) {
        return null;
      }
      if (ty_open(v.ty)) {
        return null;
      }
      return e_atom(rd_ensure(c, v.ty) + "(" + v.name + ")");
    }).filter((x): x is E => x !== null);
    parts.push(num_lit_u32(c));
    return "    case " + pat + ":\n      " + e_at(num_combine(c, parts));
  });
  c.push("def " + name + "(" + (scrMany ? "+" : "") + "x: " + ty_str(t) + ") -> U32:\n  match x:\n" + rows.join("\n"));
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: (scrMany ? 2 : 1) as BQ, t }], ret: U32C });
  return e_call(name, name + "(" + e_at(syn(c, t, env, Math.min(fuel, 2))) + ")");
}

// String / Char dispatch on literals. Literal patterns would desugar to
// Chr{U32{Word..}} chains — a structural view of a machine word, refused
// by the C emitter by design — so the tests ride String.eq / U32.is_eq
// through a Bool continuation instead; SNil/SCon arms stay structural.
function match_str_def(c: Ctx, env: V[]): E {
  c.feat("match-str");
  c = c.sub("match");
  const name = "sp" + String(c.uid());
  const lit = str_lit(c, 1 + c.g.int(4));
  const sl = helper_strlen(c);
  const bif = "sq" + String(c.uid());
  c.push("def " + bif + "(z: Bool, rest: U32) -> U32:\n  match z:\n    case False{}:\n      rest\n    case True{}:\n      " + e_at(num_gen_u32(c, [], 1)));
  c.push("def " + name + "(+s: String) -> U32:\n  match s:\n    case SNil{}:\n      " + String(c.g.int(64))
    + "\n    case SCon{h, t}:\n      " + bif + "(String.eq(SCon{h, t}, " + lit + "), " + sl + "(s, 7))");
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 2, t: STRC }], ret: U32C });
  const arg = c.g.wpick<() => string>([
    [40, () => lit],
    [40, () => e_at(syn(c, STRC, env, 1))],
    [20, () => "SCon{'" + str_char(c) + "', " + lit + "}"],
  ])();
  return e_call(name, name + "(" + arg + ")");
}

function match_char_def(c: Ctx, env: V[]): E {
  c.feat("match-char");
  c = c.sub("match");
  const name = "cv" + String(c.uid());
  const c1 = str_char(c);
  const bif = "cq" + String(c.uid());
  c.push("def " + bif + "(z: Bool, +n: U32) -> U32:\n  match z:\n    case False{}:\n      n + " + String(c.g.int(99))
    + "\n    case True{}:\n      " + e_at(num_gen_u32(c, [], 1)));
  c.push("def " + name + "(c: Char) -> U32:\n  Chr{n} = c\n  +n2 = n\n  " + bif + "(U32.is_eq(n2, " + String(c1.charCodeAt(0)) + "), n2)");
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 1, t: CHARC }], ret: U32C });
  const arg = c.g.chance(0.4) ? "'" + c1 + "'" : "'" + str_char(c) + "'";
  return e_call(name, name + "(" + arg + ")");
}

// Do-notation
// -----------
// do Maybe<..>: / do Result<..>: blocks (base's monads); binds are
// annotated, binders are lone and consumed once.

function do_call_def(c: Ctx, env: V[], fuel: number): E {
  c = c.sub("do");
  const which = c.g.pick(["maybe", "result"]);
  const id = String(c.uid());
  const name = "dm" + id;
  const x = "dx" + id;
  const y = "dy" + id;
  const henv: V[] = [v_new("k", U32C, true)];
  if (which === "maybe") {
    c.feat("do-maybe");
    const mt = "Maybe<&2, U32>";
    c.push("def " + name + "(+k: U32) -> " + mt + ":\n  do Maybe<&2, U32>:\n    "
      + x + " : U32 <- Maybe.pure(&2, U32, " + e_at(num_gen_u32(c, henv, 1)) + ")\n    "
      + y + " : U32 <- Some{" + e_at(num_gen_u32(c, henv.concat([v_new(x, U32C)]), 1)) + "}\n    "
      + "return " + e_at(num_combine(c, [e_atom(y), num_gen_u32(c, henv, 0)])));
    const rd = helper_may(c);
    return e_call(name, rd + "(" + name + "(" + e_at(num_gen_u32(c, env, Math.min(fuel, 1))) + "), " + num_lit_u32(c).s + ")");
  }
  c.feat("do-result");
  const rt = "Result<&1, &1, String, U32>";
  const fail = c.g.chance(0.3);
  const mid = fail
    ? y + " : U32 <- Result.fail(&1, &1, String, U32, " + str_lit(c, 3) + ")"
    : y + " : U32 <- Result.pure(&1, &1, String, U32, " + e_at(num_gen_u32(c, henv.concat([v_new(x, U32C)]), 1)) + ")";
  c.push("def " + name + "(+k: U32) -> " + rt + ":\n  do Result<&1, &1, String, U32>:\n    "
    + x + " : U32 <- Done{k + 1}\n    " + mid + "\n    "
    + "return " + e_at(num_combine(c, [e_atom(y), num_gen_u32(c, henv, 0)])));
  const un = "ur" + id;
  const sl = helper_strlen(c);
  c.push("def " + un + "(r: " + rt + ") -> U32:\n  match r:\n    case Fail{e}:\n      " + sl + "(e, 11)\n    case Done{v}:\n      v");
  return e_call(un, un + "(" + name + "(" + e_at(num_gen_u32(c, env, Math.min(fuel, 1))) + "))");
}

// Equality and rewrites
// ---------------------
// let_eql : an equality binding proved by {==} over identical renderings
// of one synthesized side; consumed by a constant-motive rewrite or left
// bound. Axiom asserts (bodiless) are referenced only from erased lets —
// a live reference to an unfilled assert is refused, and a live rewrite
// on one would wedge the interpreter.

type Line = { text: string; binds: string[]; vars: V[] };

function let_eql(c: Ctx, env: V[]): Line {
  c.feat("eql");
  const id = String(c.uid());
  const x = "e" + id;
  const menv = env.filter((v) => v.q === "many");
  const t = c.g.pick([U32C, NATC, BOOLC]);
  const sideE = syn(c, t, menv, 1);
  const side = sideE.p === 99 ? sideE.s : "(" + sideE.s + ")";
  const ety = "{" + side + " == " + side + " : " + ty_str(t) + "}";
  const lines: string[] = [x + " = {{==} : " + ety + "}"];
  const binds: string[] = [];
  const vars: V[] = [];
  if (c.g.chance(0.5)) {
    c.feat("rwt");
    const w = "v" + id;
    lines.push("%" + x + " : U32;");
    lines.push(w + " = " + u32_rhs(num_gen_u32(c, env, 1)));
    binds.push(w);
  }
  return { text: lines.join("\n  "), binds, vars };
}

// theorem_gen : a minted Nat clone with a generated op (op(z,b) = S^k(b),
// op(s{p},b) = S^m(op(p,b))) and its shift law, proved by two-line
// induction; the equation then rides the Equal kit (cong/sym/trans) or a
// direct constant-motive rewrite on the critical path.
function theorem_gen(c: Ctx, env: V[]): Line {
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
  // shift law: op(a, S{b}) == S{op(a, b)}. The inductive arm rewrites
  // with the IH: motive marks the S{op(p,b)} occurrence as S{_}.
  c.push("def " + th + "(a: " + N + ", -b: " + N + ") -> {" + add + "(a, " + S + "{b}) == " + S + "{" + add + "(a, b)} : " + N + "}:\n"
    + "  match a:\n    case " + Z + "{}:\n      {==}\n    case " + S + "{p}:\n      %" + th + "(p, b) : {"
    + wrap(m, add + "(p, " + S + "{b})") + " == " + wrap(m - 1, S + "{_}") + " : " + N + "};\n      {==}");
  // use the theorem live: bind nats, rewrite with a constant motive
  const id2 = String(c.uid());
  const na = "na" + id2;
  const nb = "nb" + id2;
  const w = "v" + id2;
  const depth = 1 + c.g.int(3);
  const lines = [
    na + " = {" + wrap(depth, Z + "{}") + " : " + N + "}",
    nb + " = {" + wrap(c.g.int(2), Z + "{}") + " : " + N + "}",
    "%" + th + "(" + na + ", " + nb + ") : U32;",
    w + " = " + u32_rhs(num_gen_u32(c, env, 1)),
  ];
  return { text: lines.join("\n  "), binds: [w], vars: [] };
}

// eqkit : Equal.cong / sym / trans over base's own proofs
function let_eqkit(c: Ctx, env: V[]): Line {
  c.feat("eqkit");
  const id = String(c.uid());
  const x = "qa" + id;
  const w = "v" + id;
  const a = num_lit_u32(c);
  const b = num_lit_u32(c);
  const e0 = "U32.add_comm(" + a.s + ", " + b.s + ")";
  const az = "U32.add(" + a.s + ", " + b.s + ")";
  const za = "U32.add(" + b.s + ", " + a.s + ")";
  const eq = c.g.wpick<string>([
    [3, e0],
    [2, "Equal.sym(U32, " + az + ", " + za + ", " + e0 + ")"],
    [2, "Equal.cong(U32, U32, w" + id + " => U32.inc(w" + id + "), " + az + ", " + za + ", " + e0 + ")"],
    [1, "Equal.trans(U32, " + az + ", " + za + ", " + za + ", " + e0 + ", {==})"],
  ]);
  const lines = [
    x + " = " + eq,
    "%" + x + " : U32;",
    w + " = " + u32_rhs(num_gen_u32(c, env, 1)),
  ];
  return { text: lines.join("\n  "), binds: [w], vars: [] };
}

// Array kit
// ---------
// Arrays are linear (Type kind): the kit threads one array through
// new/set/swap/get/size/clone inside a single minted def, using the
// a[i] / a[i] <- v sugar where it applies. Element reads return pairs, so
// each step chains through a continuation def — minted flat here as a
// state-machine of helper defs, base.bend style.

function let_array(c: Ctx, env: V[]): Line {
  c.feat("array-ops");
  const id = String(c.uid());
  const name = "aru" + id;
  const depth = c.pure ? 2 + c.g.int(3) : 3 + c.g.int(9);
  const elu32 = c.pure || c.g.chance(0.7);
  const x = "v" + String(c.uid());
  if (elu32) {
    c.feat("array-sugar");
    // U32 elements: get/swap/size/clone all legal. Every pair-returning
    // op chains through its own continuation def (params destructure,
    // computed values do not).
    const clone = c.g.chance(0.4);
    const k1 = "ak" + id;
    const k2 = "ah" + id;
    if (clone) {
      c.feat("array-clone");
      const k3 = "ac" + id;
      c.push("def " + k3 + "(r: Array<U32> & U32, +n: U32) -> U32:\n  (a4, w) = r\n  w + n");
      c.push("def " + k2 + "b(r: Array<U32> & U32, c: Array<U32>) -> U32:\n  (a3, n) = r\n  +n2 = n\n  " + k3 + "(Array.get(U32, c, n2), n2)");
      c.push("def " + k2 + "(r: Array<U32> & Array<U32>) -> U32:\n  (b2, c2) = r\n  " + k2 + "b(Array.size(U32, b2), c2)");
    } else {
      c.push("def " + k2 + "(r: Array<U32> & U32) -> U32:\n  (a2, n) = r\n  n + " + String(c.g.int(64)));
    }
    const k2call = clone
      ? (a: string): string => k2 + "(Array.clone(" + a + "))"
      : (a: string): string => k2 + "(Array.size(U32, " + a + "))";
    c.push("def " + k1 + "(r: Array<U32> & U32, +i: U32) -> U32:\n  (a1, old) = r\n  old + " + k2call("a1"));
    c.push("def " + name + "(+i: U32, +s: U32) -> U32:\n"
      + "  a0 = Array.new(U32, " + String(depth) + "n, s)\n"
      + "  a1 = a0[i] <- (s * 3 + 1)\n"
      + "  " + k1 + "(Array.swap(U32, a1, (i + 1), (s .^. 255)), i)");
    c.defr.push({ name, qps: [], tps: [], ps: [{ q: 2, t: U32C }, { q: 2, t: U32C }], ret: U32C });
    const keep = bind_keep(c);
    return {
      text: (keep ? "+" : "") + x + " = " + name + "(" + e_at(num_gen_u32(c, env, 1)) + ", " + e_at(num_gen_u32(c, env, 1)) + ")",
      binds: [x], vars: keep ? [v_new(x, U32C, true)] : [],
    };
  }
  // boxed Data elements: new/set/swap (get needs Data too — allowed), the
  // swap yield is the displaced owned element
  const cands = c.adts.filter((a) => a.ctors.length > 0);
  const el = cands.length > 0 ? adt_inst(c, c.g.pick(cands), true) : null;
  const elT = el !== null && ty_data(el) ? el : ({ k: "tup", a: U32C, b: U32C, q: 2 }) as T;
  c.feat("array-boxed");
  const rdE = rd_ensure(c, elT);
  const k1 = "ab" + id;
  c.push("def " + k1 + "(r: Array<" + ty_grp(elT) + "> & " + ty_str(elT) + ") -> U32:\n  (a1, old) = r\n  " + rdE + "(old)");
  const dv = e_at(syn(c, elT, [], 1));
  c.push("def " + name + "(+i: U32) -> U32:\n"
    + "  a0 = Array.new(" + ty_grp(elT) + ", " + String(depth) + "n, " + dv + ")\n"
    + "  a1 = Array.set(" + ty_grp(elT) + ", a0, i, " + e_at(syn(c, elT, [], 1)) + ")\n"
    + "  " + k1 + "(Array.swap(" + ty_grp(elT) + ", a1, (i + 3), " + e_at(syn(c, elT, [], 1)) + "))");
  c.defr.push({ name, qps: [], tps: [], ps: [{ q: 2, t: U32C }], ret: U32C });
  const keep = bind_keep(c);
  return {
    text: (keep ? "+" : "") + x + " = " + name + "(" + e_at(num_gen_u32(c, env, 1)) + ")",
    binds: [x], vars: keep ? [v_new(x, U32C, true)] : [],
  };
}

// Map kit
// -------
// Map/Set run as written (no native interception): set/get/has/pop/del/
// keys/union threading through continuation defs.

function let_map(c: Ctx, _env: V[]): Line {
  c.feat("map-ops");
  const id = String(c.uid());
  const x = "v" + String(c.uid());
  const vT = c.g.pick([U32C, BOOLC, STRC]);
  const q = ty_data(vT) && c.g.chance(0.7) ? Q2 : Q1;
  const mT: T = { k: "map", q, v: vT };
  const qs = qt_str(q);
  const vs = ty_grp(vT);
  const rdM = rd_ensure(c, mT);
  const name = "mpu" + id;
  const keys = Array.from({ length: 2 + c.g.int(4) }, () => str_lit(c, 1 + c.g.int(6)));
  let acc = "Map.new(" + qs + ", " + vs + ")";
  for (const k of keys) {
    acc = "Map.set(" + qs + ", " + vs + ", " + acc + ", " + k + ", " + e_at(syn(c, vT, [], 1)) + ")";
  }
  const style = c.g.wpick<string>([[3, "rd"], [2, "has"], [2, "pop"], [qt_known(q) === 2 && vT.k === "u32" ? 3 : 0, "get"], [1, "set-kit"]]);
  const lines: string[] = [];
  if (style === "has") {
    const k1 = "mh" + id;
    c.push("def " + k1 + "(r: Map<" + qs + ", " + vs + "> & Bool) -> U32:\n  (m2, b) = r\n  " + helper_bool(c) + "(b) + " + rdM + "(m2)");
    lines.push(x + " = " + k1 + "(Map.has(" + qs + ", " + vs + ", " + acc + ", " + c.g.pick(keys) + "))");
  } else if (style === "pop") {
    const k1 = "mp" + id;
    const mayT: T = { k: "adt", a: BASE.Maybe, qs: [q], args: [vT] };
    const rdMay = rd_ensure(c, mayT);
    c.push("def " + k1 + "(r: Map<" + qs + ", " + vs + "> & " + ty_str(mayT) + ") -> U32:\n  (m2, got) = r\n  " + rdMay + "(got) + " + rdM + "(m2)");
    lines.push(x + " = " + k1 + "(Map.pop(" + qs + ", " + vs + ", " + acc + ", " + (c.g.chance(0.5) ? c.g.pick(keys) : str_lit(c, 3)) + "))");
  } else if (style === "get") {
    c.feat("set-ops");
    const k1 = "mg" + id;
    c.push("def " + k1 + "(r: Map<&2, U32> & U32) -> U32:\n  (m2, v) = r\n  v + " + rdM + "(m2)");
    lines.push(x + " = " + k1 + "(Map.get(U32, " + num_lit_u32(c).s + ", " + acc + ", " + c.g.pick(keys) + "))");
  } else if (style === "set-kit") {
    c.feat("set-ops");
    const k1 = "ms" + id;
    c.push("def " + k1 + "(r: Set() & Bool) -> U32:\n  (s2, b) = r\n  " + helper_bool(c) + "(b) + " + String(c.g.int(64)));
    let sacc = "Set.new()";
    for (const k of keys.slice(0, 3)) {
      sacc = "Set.add(" + sacc + ", " + k + ")";
    }
    lines.push(x + " = " + k1 + "(Set.has(" + sacc + ", " + c.g.pick(keys) + "))");
  } else {
    lines.push(x + " = " + rdM + "(" + (c.g.chance(0.3) ? "Map.union(" + qs + ", " + vs + ", " + acc + ", Map.new(" + qs + ", " + vs + "))" : acc) + ")");
  }
  const keep = bind_keep(c);
  lines[lines.length - 1] = (keep ? "+" : "") + lines[lines.length - 1];
  return { text: lines.join("\n  "), binds: [x], vars: keep ? [v_new(x, U32C, true)] : [] };
}

// Fork kit
// --------
// Parallel lets over saturated calls — the ONE fork shape — plus balanced
// batch trees with ! GPU marks. Interp-side trees stay shallow; the
// compiled-only side goes deep.

function batch_ensure(c: Ctx): string {
  const got = c.memo.get("batch");
  if (got !== undefined) {
    return got;
  }
  const name = "bt" + String(c.uid());
  c.memo.set("batch", name);
  c = c.sub("batch");
  const leaf = e_at(num_combine(c, [e_bin(e_bin(e_atom("i"), "*", e_atom("2654435761")), ".&.", e_atom("8191")), num_gen_u32(c, [v_new("i", U32C, true)], 1)]));
  c.push("def " + name + "(+d: Nat, +i: U32) -> U32:\n  match d:\n    case 0n:\n      " + leaf
    + "\n    case 1n+q:\n      a b = " + name + "(q, (i * 2)) " + name + "(q, (i * 2 + 1))\n      "
    + e_at(num_combine(c, [e_atom("a"), e_atom("b")])));
  return name;
}

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
  const depth = c.pure ? 2 + c.g.int(4) : 5 + c.g.int(8);
  const mkcall = (): string => {
    if (c.g.chance(0.5)) {
      return batch_ensure(c) + gpu_mark(c) + "(" + String(depth) + "n, " + e_at(num_gen_u32(c, env, 1)) + ")";
    }
    return tail_call(c, env, 2).s;
  };
  const vals: string[] = [];
  for (let i = 0; i < ncalls; i++) {
    vals.push(mkcall());
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
  for (let i = vals.length - 1; i > 0; i--) {
    const j = c.g.int(i + 1);
    const t = vals[i];
    vals[i] = vals[j];
    vals[j] = t;
  }
  const ks = vals.map(() => "p" + String(c.uid()));
  return { text: ks.join(" ") + " = " + vals.join(" "), binds: ks, vars: [] };
}

// Share kit
// ---------
// Contraction on purpose: a + binder read many times, a + parameter read
// twice inside a callee — the refcount/borrow machinery's prime shapes.

function let_shared(c: Ctx, env: V[]): Line {
  c.feat("share");
  const id = String(c.uid());
  const s = "sh" + id;
  const x = "v" + String(c.uid());
  const y = "v" + String(c.uid());
  const closed = c.adts.filter((a) => a.ctors.length > 0);
  const inst = closed.length > 0 ? adt_inst(c, c.g.pick(closed), true) : null;
  if (inst !== null && ty_data(inst) && c.g.chance(0.6)) {
    const rdp = rd_ensure(c, inst);
    const us = "us" + id;
    c.push("def " + us + "(+s: " + ty_str(inst) + ", +k: U32) -> U32:\n  " + e_at(num_combine(c, [e_atom(rdp + "(s)"), e_atom(rdp + "(s)"), e_atom("k")])));
    c.defr.push({ name: us, qps: [], tps: [], ps: [{ q: 2, t: inst }, { q: 2, t: U32C }], ret: U32C });
    const lines = [
      "+" + s + " = {" + syn(c, inst, env, 2).s + " : " + ty_str(inst) + "}",
      x + " = " + us + "(" + s + ", " + e_at(num_gen_u32(c, env, 1)) + ")",
      y + " = " + rdp + "(" + s + ") + " + x,
    ];
    return { text: lines.join("\n  "), binds: [y], vars: [] };
  }
  const lines = [
    "+" + s + " = " + u32_rhs(num_gen_u32(c, env, 2)),
    x + " = " + e_at(num_combine(c, [e_atom(s), e_atom(s), num_gen_u32(c, env, 1)])),
    y + " = " + s + " + " + x,
  ];
  return { text: lines.join("\n  "), binds: [y], vars: [] };
}

// Dep kit
// -------
// Large elimination: a Nat-indexed family uf : Nat -> Type with a section
// pick : @n -> uf(n) and a transport hop consuming uf(k) at both indices —
// the checker specializes the context type per arm (probed against HEAD).

function let_dep(c: Ctx, env: V[]): Line {
  c.feat("dep");
  const id = String(c.uid());
  const fam = "uf" + id;
  const pick = "up" + id;
  const hop = "uh" + id;
  const left = c.g.pick([U32C, BOOLC, STRC]);
  let right = c.g.pick([U32C, NATC, CMPC]);
  if (ty_eq(left, right)) {
    right = NATC;
  }
  c.push("def " + fam + "(n: Nat) -> Type:\n  match n:\n    case 0n:\n      " + ty_str(left) + "\n    case 1n+p:\n      " + ty_str(right));
  c.push("def " + pick + "(n: Nat) -> " + fam + "(n):\n  match n:\n    case 0n:\n      "
    + e_at(syn(c, left, [], 1)) + "\n    case 1n+p:\n      " + e_at(syn(c, right, [], 1)));
  const rdl = left.k === "u32" ? null : rd_ensure(c, left);
  const rdr = right.k === "u32" ? null : rd_ensure(c, right);
  c.push("def " + hop + "(k: Nat, v: " + fam + "(k)) -> U32:\n  match k:\n    case 0n:\n      "
    + (rdl === null ? "v + 1" : rdl + "(v)") + "\n    case 1n+q:\n      " + (rdr === null ? "v * 2" : rdr + "(v)"));
  const use = "ud" + id;
  c.push("def " + use + "(+n: Nat) -> U32:\n  " + hop + "(n, " + pick + "(n))");
  c.defr.push({ name: use, qps: [], tps: [], ps: [{ q: 2, t: NATC }], ret: U32C, mask: [4] });
  const x = "v" + String(c.uid());
  return {
    text: x + " = " + use + "(U32.to_nat(" + e_at(num_gen_u32(c, env, 1)) + " % 4))",
    binds: [x], vars: [],
  };
}

// Ford kit
// --------
// The Word idiom: an indexed family as a filled type-level def over a
// minted Nat clone, per-index constructor types, index-first matching
// (the field's computed type reduces per arm), and a hole-motive
// transport (Word.cast style).
function let_ford(c: Ctx, env: V[]): Line {
  c.feat("ford");
  const id = String(c.uid());
  const N = "Fn" + id;
  const Z = N + "z";
  const S = N + "s";
  c.push("type " + N + " is Data:\n  " + Z + "{}\n  " + S + "{p: " + N + "}");
  const V0 = "Fv" + id;
  const P = c.g.pick([U32C, BOOLC]);
  c.push("assert " + V0 + ":\n  forall n: " + N + "\n  Data");
  c.push("type " + V0 + ".Nil is Data:\n  " + V0 + "n{}");
  c.push("type " + V0 + ".Con<-p: " + N + "> is Data:\n  " + V0 + "c{head: " + ty_str(P) + ", tail: " + V0 + "(p)}");
  c.push("def " + V0 + "(n):\n  match n:\n    case " + Z + "{}:\n      " + V0 + ".Nil\n    case " + S + "{p}:\n      " + V0 + ".Con<p>");
  const toN = "fw" + id;
  c.push("def " + toN + "(k: Nat) -> " + N + ":\n  match k:\n    case 0n:\n      " + Z + "{}\n    case 1n+p:\n      " + S + "{" + toN + "(p)}");
  const bld = "fb" + id;
  c.push("def " + bld + "(n: " + N + ", +s: U32) -> " + V0 + "(n):\n  match n:\n    case " + Z + "{}:\n      " + V0 + "n{}\n    case " + S + "{p}:\n      "
    + V0 + "c{" + (P.k === "u32" ? "s" : "U32.is_gt(s, 4)") + ", " + bld + "(p, (s + 3))}");
  const rdP = P.k === "u32" ? null : helper_bool(c);
  const eat = "fe" + id;
  c.push("def " + eat + "(n: " + N + ", v: " + V0 + "(n), +acc: U32) -> U32:\n  match n:\n    case " + Z + "{}:\n      acc\n    case " + S + "{p}:\n      match v:\n        case " + V0 + "c{h, t}:\n          "
    + eat + "(p, t, (acc + " + (rdP === null ? "h" : rdP + "(h)") + "))");
  // hole-motive transport: cast across a proved index equation
  const cast = "fc" + id;
  c.push("def " + cast + "(-m: " + N + ", -n: " + N + ", e: {m == n : " + N + "}, w: " + V0 + "(m)) -> " + V0 + "(n):\n  %e : " + V0 + "(_); w");
  const use = "fu" + id;
  // n is consumed twice (eat and bld): copy through a + binder; the cast
  // — the identity transport across the reflexive index equation — rides
  // a coin: its Word.cast shape (%e : F(_); w) is a live compiler-bug
  // class today (repros/comp_rwt_cast_body.bend), and the coin keeps the
  // cast-free spelling reaching the compiled legs while it stands
  const casted = c.g.chance(0.5);
  if (casted) {
    c.feat("ford-cast");
  }
  const built = casted ? cast + "(n, n, {==}, " + bld + "(n, s))" : bld + "(n, s)";
  c.push("def " + use + "(k: Nat, +s: U32) -> U32:\n  +n = " + toN + "(k)\n  " + eat + "(n, " + built + ", 7)");
  c.defr.push({ name: use, qps: [], tps: [], ps: [{ q: 1, t: NATC }, { q: 2, t: U32C }], ret: U32C, mask: [c.pure ? 12 : 40, null] });
  const x = "v" + String(c.uid());
  return {
    text: x + " = " + use + "(U32.to_nat(" + e_at(num_gen_u32(c, env, 1)) + " % " + String(c.pure ? 12 : 40) + "), " + e_at(num_gen_u32(c, env, 1)) + ")",
    binds: [x], vars: [],
  };
}

// Line kits
// ---------

function let_scalar(c: Ctx, env: V[]): Line {
  const x = "v" + String(c.uid());
  const keep = bind_keep(c);
  return {
    text: (keep ? "+" : "") + x + " = " + u32_rhs(num_gen_u32(c, env, 2 + c.g.int(3))),
    binds: [x],
    vars: keep ? [v_new(x, U32C, true)] : [],
  };
}

// let_value : a typed value of a synthesized type, bound (annotated when
// non-inferable) and folded through its reader; Data values sometimes
// stay in scope under a + binder for later reuse.
function let_value(c: Ctx, env: V[]): Line {
  const t = syn_ty(c, size_pick(c, 2, 5), Q0, [], []);
  if (t.k === "u32" || t.k === "arr") {
    return let_scalar(c, env);
  }
  c.feat(t.k === "fun" ? "clo" : "value");
  const x = "v" + String(c.uid());
  const y = "v" + String(c.uid());
  const val = c.mints < 10 && c.g.chance(0.3) ? syn_mint_def(c, t, env) ?? syn(c, t, env, 2) : syn(c, t, env, 2 + c.g.int(2));
  const keep = ty_data(t) && c.g.chance(0.4);
  const kind = c.g.wpick<string>([
    [50, "plain"],
    [t.k === "adt" && !ty_open(t) ? 20 : 0, "tf"],
    [keep ? 15 : 0, "twice"],
  ]);
  const rd = rd_ensure(c, t);
  const sig = keep ? "+" : "";
  const ykeep = bind_keep(c);
  // annotate: intro-headed values are not inferable in a bare let
  const lines: string[] = [sig + x + " = {" + val.s + " : " + ty_top(t) + "}"];
  if (kind === "tf") {
    c.feat("reuse");
    lines.push((ykeep ? "+" : "") + y + " = " + rd + "(" + tf_ensure(c, t as Extract<T, { k: "adt" }>) + "(" + x + "))");
  } else if (kind === "twice") {
    c.feat("dup");
    lines.push((ykeep ? "+" : "") + y + " = " + rd + "(" + x + ") + " + rd + "(" + x + ")");
  } else {
    lines.push((ykeep ? "+" : "") + y + " = " + rd + "(" + x + ")");
  }
  const vars = ykeep ? [v_new(y, U32C, true)] : [];
  if (keep && kind !== "twice") {
    vars.push(v_new(x, t, true));
  }
  return { text: lines.join("\n  "), binds: [y], vars };
}

function let_call(c: Ctx, env: V[]): Line {
  const x = "v" + String(c.uid());
  const e = c.g.wpick<() => E>([
    [16, () => match_nat_def(c, env, 1)],
    [10, () => match_bool_def(c, env, 1)],
    [14, () => match_adt_def(c, env, 1) ?? match_nat_def(c, env, 1)],
    [14, () => tail_call(c, env, 2)],
    [8, () => match_str_def(c, env)],
    [6, () => match_char_def(c, env)],
    [10, () => do_call_def(c, env, 1)],
    [10, () => {
      generic_mint(c);
      return syn_call_unify(c, U32C, env, 2) ?? num_gen_u32(c, env, 2);
    }],
    [8, () => hof_call(c, env)],
  ])();
  const bang = e.head !== undefined && e.s.startsWith(e.head + "(") && gpu_mark(c) !== "";
  const s = bang ? (e.head as string) + "!" + e.s.slice((e.head as string).length) : e.s;
  const keep = bind_keep(c);
  const rhs = e.p === 99 ? (/^\d+$/.test(s) ? "{" + s + " : U32}" : s) : "(" + s + ")";
  return { text: (keep ? "+" : "") + x + " = " + rhs, binds: [x], vars: keep ? [v_new(x, U32C, true)] : [] };
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
  c.push("def " + hf + "(f: U32 -> U32, +x: U32) -> U32:\n  f(x) + x");
  c.defr.push({ name: hf, qps: [], tps: [], ps: [{ q: 1, t: { k: "fun", q: 1, dom: U32C, cod: U32C } }, { q: 2, t: U32C }], ret: U32C });
  if (c.g.chance(0.5)) {
    c.feat("partial");
    // a def value at exactly live-1 arguments
    return e_atom(hf + "(" + name + "(" + e_at(num_gen_u32(c, env, 1)) + ", " + e_at(num_gen_u32(c, env, 1)) + "), " + e_at(num_gen_u32(c, env, 1)) + ")");
  }
  const b = "y" + id;
  const lam = b + " => " + e_at(num_gen_u32(c, [v_new(b, U32C)], 1));
  return e_atom(hf + "(" + lam + ", " + e_at(num_gen_u32(c, env, 1)) + ")");
}

// let_float : an F32 chain folded through exact conversions — compiled
// legs only (c.pure guards its reachability)
function let_float(c: Ctx, env: V[]): Line {
  c.feat("f32");
  const f = "f" + String(c.uid());
  const x = "v" + String(c.uid());
  const val = num_gen_f32(c, env, 2 + c.g.int(2));
  const many = c.g.chance(0.4);
  const rhs = c.g.chance(0.7)
    ? e_fn("F32.to_u32", e_bin(e_atom(f), "*.", num_lit_f32(c, false)))
    : e_fn(helper_bool(c), e_bin(e_atom(f), c.g.pick(["<.", "<=.", ">=.", "!=.", "==."]), num_gen_f32(c, env, 2)));
  const keep = bind_keep(c);
  // an F32 literal is a bare constructor: a let value must annotate
  return {
    text: (many ? "+" : "") + f + " = {" + val.s + " : F32}\n  " + (keep ? "+" : "") + x + " = " + e_at(rhs),
    binds: [x],
    vars: (many ? [v_new(f, F32C, true)] : []).concat(keep ? [v_new(x, U32C, true)] : []),
  };
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
  entries: string[];
  feats: string[];
  trans: boolean;
};

// io_tail : a deterministic IO sequence for main — file roundtrip in the
// run's cwd, get_env of an unset name, print_err, and rarely an IO.die
// whose exit code is the assertion. Every yield is deterministic.
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
    lines.push("t" + id + "a : Unit <- IO.print(\"" + msg + "\")");
    out.push(msg);
  }
  if (c.g.chance(0.45)) {
    c.feat("file-io");
    const sl = helper_strlen(c);
    const fn = "fzf_" + key + ".txt";
    const txt = "data".repeat(1 + c.g.int(4)) + String(c.g.int(100));
    const rk = "fr" + id;
    c.push("def " + rk + "(fr: File & Result<&1, &1, U32 & String, String>) -> IO(U32):\n"
      + "  (f, r) = fr\n  match r:\n    case Done{s}:\n      do IO<U32>:\n        u : Unit <- File.close(f)\n        IO.pure(U32, " + sl + "(s, 0))\n"
      + "    case Fail{e}:\n      (c, m) = e\n      do IO<U32>:\n        u2 : Unit <- File.close(f)\n        IO.pure(U32, c + " + sl + "(m, 0))");
    const wk = "fw" + id;
    c.push("def " + wk + "(fr: File & Result<&1, &1, U32 & String, Unit>) -> IO(U32):\n"
      + "  (f, r) = fr\n  match r:\n    case Done{u3}:\n      do IO<U32>:\n        fr2 : File & Result<&1, &1, U32 & String, String> <- File.read(f, 4096)\n        " + rk + "(fr2)\n"
      + "    case Fail{e}:\n      (c, m) = e\n      do IO<U32>:\n        u4 : Unit <- File.close(f)\n        IO.pure(U32, c)");
    const io = "fio" + id;
    c.push("def " + io + "() -> IO(U32):\n  do IO<U32>:\n"
      + "    r : Result<&1, &1, U32 & String, File> <- File.open(\"" + fn + "\", \"w\")\n"
      + "    f : File <- IO.pass(File, r)\n"
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
      + "    case Done{s}:\n      " + sl + "(s, 1000)\n    case Fail{e}:\n      (c, m) = e\n      c + " + String(c.g.int(64)));
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
  if (c.g.chance(0.18)) {
    c.feat("io-die");
    code = 1 + c.g.int(200);
    err.push("fzdie_" + key);
  }
  return { lines, out, err, code };
}

type Kit = Array<[number, (c: Ctx, e: V[]) => Line]>;

// lines_gen : n statement lines drawn from a kit table, binding into env
function lines_gen(c: Ctx, kit: Kit, label: string, n: number, env: V[]): Stmt[] {
  const lines: Stmt[] = [];
  for (let i = 0; i < n; i++) {
    const line = c.g.wpick(kit)(c.sub(label), env);
    lines.push({ text: line.text, binds: line.binds });
    env.push(...line.vars);
  }
  return lines;
}

function stmt_names(lines: Stmt[]): string[] {
  return lines.flatMap((l) => l.binds);
}

// gen_member : one seed's whole program. RNG draws are identical for the
// raw and sealed spellings (the seal is string assembly over one extra
// unconditional draw), so the two books differ only in result's reply.
function gen_member(seed: bigint, uid0 = 0, io_ok = true): Member {
  const c = ctx_new(seed, uid0);
  const nadts = c.g.int(3);
  for (let i = 0; i < nadts; i++) {
    adt_new(c.sub("adt"));
  }
  // result: the interp-visible side
  c.pure = true;
  const env: V[] = [];
  const LETK: Kit = [
    [12, let_scalar],
    [30, let_value],
    [16, let_call],
    [7, let_fork],
    [7, let_array],
    [6, let_map],
    [6, let_shared],
    [4, let_eql],
    [3, theorem_gen],
    [3, let_eqkit],
    [4, let_dep],
    [3, let_ford],
  ];
  // swarm : per-seed multipliers reshape the weight table so rare kinds
  // get seeds where they dominate
  const swarm: Kit = LETK.map(([w, f]) => [w * c.g.wpick<number>([[20, 0], [45, 1], [20, 2], [15, 4]]), f]);
  const table = swarm.some(([w]) => w > 0) ? swarm : LETK;
  const heavy = c.g.chance(0.08);
  if (heavy) {
    c.feat("big");
  }
  const lines = lines_gen(c, table, "res", size_pick(c, heavy ? 5 + c.g.int(5) : 2 + c.g.int(3), 48), env);
  if (c.g.chance(0.04)) {
    c.feat("deaddef");
    c.push("def zd" + String(c.uid()) + "(x: U32) -> U32:\n  x + " + String(1 + c.g.int(99)));
  }
  const res = "r" + String(c.uid());
  const fold = e_at(num_combine(c.sub("fold"), stmt_names(lines).map((n) => e_atom(n)).concat([num_gen_u32(c.sub("fold"), env, 1)])));
  const seal = e_at(num_seal(c.sub("seal"), res));
  const resultName = "rs" + String(c.uid());
  const rawName = "rw" + String(c.uid());
  // extra: the compiled-only side (F32, deep forks, long loops)
  c.pure = false;
  let extraName: string | null = null;
  let xlines: Stmt[] = [];
  let xfold = "";
  if (c.g.chance(0.9)) {
    extraName = "xt" + String(c.uid());
    const xenv: V[] = [];
    const XK: Kit = [
      [30, let_float],
      [16, let_fork],
      [14, let_call],
      [10, let_value],
      [8, let_array],
      [8, let_scalar],
    ];
    xlines = lines_gen(c, XK, "extra", 1 + c.g.int(3), xenv);
    xfold = e_at(num_combine(c.sub("xfold"), stmt_names(xlines).map((n) => e_atom(n)).concat([num_gen_u32(c.sub("xfold"), xenv, 1)])));
  }
  c.pure = true;
  // io tail
  const tail = io_ok && seed_roll(seed, 0x17n) < IO_PCT ? io_tail(c.sub("io"), seed) : null;
  return {
    seed, resultName, rawName, res, lines, fold, seal, extraName, xlines, xfold, tail,
    entries: c.entries.slice(),
    feats: Object.keys(c.s.feat),
    trans: c.trans,
  };
}

// member_defs : the member's own defs — result (sealed), the raw sibling
// when asked, and extra — rendered after its entries
function member_defs(m: Member, raw: boolean): string[] {
  const head = m.lines.map((l) => l.text).concat(["+" + m.res + " = " + m.fold]).join("\n  ");
  const def = (name: string, ret: string): string => "def " + name + "() -> U32:\n  " + head + "\n  " + ret;
  const out = [def(m.resultName, m.seal)];
  if (raw) {
    out.push(def(m.rawName, m.res + " + 0"));
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
// Expected stdout per member: the result line (interp-known), the tail's
// lines (known or cross-leg-only), the extra line (cross-leg-only).
// `null` marks a line whose value only the legs can agree on.

type Expect = { out: Array<string | null>; err: string[]; code: number };

function member_expect(m: Member, want: string | null): Expect {
  const out: Array<string | null> = [want];
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

// member_rows : one member's lines of a main — its result, its tail, and
// its extra unless it dies (the IO.die is the block's end)
function member_rows(m: Member, i: number, spelling: Spelling): string[] {
  const rows = ["w" + String(i) + "a : Unit <- IO.print(U32.show(" + (spelling === "raw" ? m.rawName : m.resultName) + "()))"];
  if (m.tail !== null) {
    rows.push(...m.tail.lines);
  }
  if (m.extraName !== null && !member_dies(m)) {
    rows.push("w" + String(i) + "b : Unit <- IO.print(U32.show(" + m.extraName + "()))");
  }
  return rows;
}

// member_main : the program's main. With no dying member it prints every
// member in order. A dying member ends the process, so it gets its own
// block, and main dispatches on the FZ_MEMBER environment variable: unset
// runs the non-dying members (fzall), "i" runs member i's block — one
// binary, one run per dying member plus one for the rest.
function member_main(ms: Member[], spelling: Spelling): string {
  const block = (name: string, rows: string[], end: string): string =>
    "def " + name + "() -> IO(Unit):\n  do IO<Unit>:\n" + rows.concat([end]).map((r) => "    " + r).join("\n");
  const dying = ms.map((_, i) => i).filter((i) => member_dies(ms[i]));
  const rest = ms.flatMap((m, i) => member_dies(m) ? [] : member_rows(m, i, spelling));
  if (dying.length === 0) {
    return block("main", rest, "IO.pure(Unit, Unit{})");
  }
  const RES = "Result<&1, &1, U32 & String, String>";
  const sel = (j: number): string => "fzsel" + String(j) + "(String.eq(s, \"" + String(dying[j]) + "\"), s)";
  const defs = [block("fzall", rest, "IO.pure(Unit, Unit{})")];
  for (const i of dying) {
    const m = ms[i];
    defs.push(block("fzm" + String(i), member_rows(m, i, spelling),
      "IO.die(Unit, " + String((m.tail as IoTail).code) + ", \"fzdie_" + (m.seed & 0xffffffn).toString(16) + "\")"));
  }
  // the selector chain, last link first: no forward references
  for (let j = dying.length - 1; j >= 0; j--) {
    defs.push("def fzsel" + String(j) + "(z: Bool, +s: String) -> IO(Unit):\n  match z:\n    case True{}:\n      fzm" + String(dying[j])
      + "()\n    case False{}:\n      " + (j + 1 < dying.length ? sel(j + 1) : "fzall()"));
  }
  defs.push("def fzdis(r: " + RES + ") -> IO(Unit):\n  match r:\n    case Done{s0}:\n      +s = s0\n      " + sel(0)
    + "\n    case Fail{e}:\n      fzall()");
  defs.push("def main() -> IO(Unit):\n  do IO<Unit>:\n    sel : " + RES + " <- IO.get_env(\"FZ_MEMBER\")\n    fzdis(sel)");
  return defs.join("\n\n");
}

// assemble : one program. "sealed" is what the compiled legs run and
// findings save; "both" adds the raw sibling for the interpreter
// differential; "raw" is the raw spelling alone, for attributing a reject.
function assemble(ms: Member[], spelling: Spelling): string {
  const head = "# fuzz " + spelling + (ms.length > 1 ? " batch of " + String(ms.length) : "")
    + " seed=" + ms.map((m) => String(m.seed)).join(",") + "\n\nimport Base\n\n";
  const blocks: string[] = [];
  for (const m of ms) {
    blocks.push(...m.entries);
    blocks.push(...member_defs(m, spelling !== "sealed"));
  }
  blocks.push(member_main(ms, spelling));
  return head + blocks.join("\n\n") + "\n";
}

// Worker
// ------
// `fuzz.ts --worker`: JSON-line protocol on stdin/stdout. The worker
// imports bend.ts/comp.ts once, seeds a checked base book once, and per
// request clones it, parses the program source, validates, and either
// evaluates the requested defs on the interpreter (term_snf, decoding
// each U32 Word chain) or emits the C and JS sources. Verdicts: reject
// (the checker refused), skip (resource limit), crash (an internal error
// on a checked program — a finding), ok.

type WorkerMode = "interp" | "emit" | "check";
type WorkerReq = { id: number; src: string; mode: WorkerMode; defs?: string[] };
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

// worker_decode : read a decimal out of the shown normal form — a U32 is
// its 32-bit Word chain, LSB first
function worker_decode(shown: string): string | null {
  if (!shown.startsWith("U32{")) {
    return null;
  }
  let v = 0n;
  let i = 0;
  const re = /WCon\{(False|True)\{\}/g;
  let m2: RegExpExecArray | null;
  while ((m2 = re.exec(shown)) !== null) {
    if (m2[1] === "True") {
      v |= 1n << BigInt(i);
    }
    i++;
  }
  if (i !== 32 || !shown.includes("WNil{}")) {
    return null;
  }
  return String(v);
}

async function worker_main(): Promise<void> {
  const bend = await import(pathToFileURL(BEND_TS).href);
  const comp = await import(pathToFileURL(COMP_TS).href);
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
  let base_book: { tlds: Record<string, unknown>; ctrs: Record<string, unknown>; order: string[]; hols: number } | null = null;
  const base_seed = async (): Promise<typeof base_book> => {
    if (base_book === null) {
      const b = bend.book_nil();
      await bend.book_load(b, BASE_PATH, "", new Map());
      bend.book_valid(b);
      base_book = b;
    }
    return base_book;
  };
  // book_of : the program's `import Base` is the pre-seeded base, so the
  // rest parses straight from the string
  const book_of = async (src: string): Promise<{ book?: unknown; err?: string; skip?: string }> => {
    const book = bend.book_nil();
    try {
      const base = await base_seed() as { tlds: Record<string, unknown>; ctrs: Record<string, unknown>; order: string[] };
      for (const k of Object.keys(base.tlds)) {
        book.tlds[k] = { ...(base.tlds[k] as Record<string, unknown>) };
      }
      Object.assign(book.ctrs, base.ctrs);
      book.order.push(...base.order);
      bend.parse_book(book, ROOT + "/", src.replace(/^import Base$/m, ""), "");
      bend.book_valid(book, base.order.length);
      return { book };
    } catch (e) {
      if (e instanceof RangeError) {
        return { skip: "check-stack-overflow" };
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
    let checked: { book?: unknown; err?: string; skip?: string };
    try {
      checked = await book_of(req.src);
    } catch (e) {
      reply({ id: req.id, verdict: "crash", stage: "check", err: err_str(e) });
      return;
    }
    if (checked.skip !== undefined) {
      reply({ id: req.id, verdict: "skip", stage: checked.skip });
      return;
    }
    if (checked.err !== undefined) {
      reply({ id: req.id, verdict: "reject", err: checked.err });
      return;
    }
    const book = checked.book;
    if (req.mode === "check") {
      reply({ id: req.id, verdict: "ok" });
      return;
    }
    if (req.mode === "interp") {
      const t0 = performance.now();
      const outs: string[] = [];
      for (const def of req.defs ?? []) {
        let shown: string;
        try {
          shown = bend.term_show(bend.term_lower(bend.term_snf(book, bend.Ref(def))));
        } catch (e) {
          if (e instanceof RangeError) {
            reply({ id: req.id, verdict: "skip", stage: "interp-stack-overflow", def });
          } else {
            reply({ id: req.id, verdict: "crash", stage: "interp", err: err_str(e), def });
          }
          return;
        }
        const dec = worker_decode(shown);
        if (dec === null) {
          reply({ id: req.id, verdict: "crash", stage: "interp-stuck", err: "not a closed U32: " + shown.slice(0, 300), def });
          return;
        }
        outs.push(dec);
      }
      reply({ id: req.id, verdict: "ok", outs, ms: Math.round(performance.now() - t0) });
      return;
    }
    const emit = (stage: string, f: () => string): string | null => {
      try {
        return f();
      } catch (e) {
        if (e instanceof RangeError) {
          reply({ id: req.id, verdict: "skip", stage: stage + "-stack-overflow" });
        } else {
          reply({ id: req.id, verdict: "crash", stage, err: err_str(e) });
        }
        return null;
      }
    };
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
    w.proc.stdin?.write(JSON.stringify(req) + "\n");
  }

  run(src: string, mode: WorkerMode, defs?: string[]): Promise<WorkerRes> {
    const req: WorkerReq = { id: this.nextId++, src, mode, defs };
    return new Promise((resolve) => {
      this.queue.push({ req, resolve });
      this.drain();
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

const CC_FLAGS = [OPT, "-std=c11", "-w", "-fno-slp-vectorize"];

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

// Compare
// -------
// cmp_expect : the sequential C leg against the generator's own
// expectations (null lines are cross-leg-only). cmp_legs : any other leg
// against the sequential reference, with the trans policy on the extra
// lines.

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

function cmp_expect(exp: Expect, got: LegOut): string | null {
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

// Save
// ----

// QUIET : the reducer's trials neither save nor announce
let QUIET = false;

function save_file(sub: string, seed: bigint, header: string[], src: string, suffix = ""): string {
  if (QUIET) {
    return "";
  }
  const dir = sub === "" ? FINDINGS : path.join(FINDINGS, sub);
  fs.mkdirSync(dir, { recursive: true });
  const f = path.join(dir, "seed-" + String(seed) + suffix + ".bend");
  const head = header.map((l) => "# " + l.replaceAll("\n", "\n# ")).join("\n");
  fs.writeFileSync(f, head + "\n# found=" + new Date().toISOString() + "\n\n" + src);
  return f;
}

// save_finding : persist the program with its verdict header and exact
// repro line, and announce it; head is the one-line summary printed
function repro_line(seed: bigint): string {
  const flags = (THREADS > 0 ? " --threads " + String(THREADS) : "")
    + (WITH_METAL ? " --metal" : "") + (WITH_CUDA ? " --cuda" : "");
  return "repro: bun " + import.meta.filename + " 1 --seed " + String(seed) + flags;
}

function save_finding(seed: bigint, kind: string, detail: string[], src: string, head: string): string {
  const f = save_file("", seed, ["FUZZ FINDING kind=" + kind, repro_line(seed), ...detail], src);
  if (!QUIET) {
    console.log("\nFINDING " + kind + " seed=" + String(seed) + "\n  " + head + "\n  -> " + f);
  }
  return f;
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
// One group = one compiled program (a batch, or a solo member). The
// interp legs run per member on solo-assembled siblings; the compiled
// legs run on the merged program; any compiled failure re-runs members
// solo for attribution.

const UID_STRIDE = 1_000_000;

type MemberState = {
  m: Member;
  verdict: Verdict | null;
  want: string | null;
};

// member_interp : the raw/sealed interpreter differential for one member
// — one book holding both spellings, each def evaluated by its own worker
// request in parallel (evaluation is the cost; parsing and checking the
// book is ~5ms); answers the raw value (the compiled reference) or a
// verdict. A reject is attributed by re-checking the raw spelling alone:
// raw-reject is a generator bug, generator-reject a broken seal.
async function member_interp(ms: MemberState): Promise<void> {
  const m = ms.m;
  const src = assemble([m], "both");
  const [oracle, w] = await Promise.all([
    phase("worker:raw", () => pool.run(src, "interp", [m.rawName])),
    phase("worker:sealed", () => pool.run(src, "interp", [m.resultName])),
  ]);
  const fail = (kind: string, detail: string[], prog: string, head: string): void => {
    save_finding(m.seed, kind, detail, prog, head);
    ms.verdict = { kind: "fail", fkind: kind, why: head };
  };
  if (oracle.verdict === "reject") {
    const raw = assemble([m], "raw");
    const r = await phase("worker:check", () => pool.run(raw, "check"));
    const kind = r.verdict === "ok" ? "generator-reject" : "raw-reject";
    fail(kind, ["stage=check", oracle.err ?? ""], kind === "raw-reject" ? raw : src, (oracle.err ?? "").split("\n")[0]);
    return;
  }
  for (const [x, kind] of [[oracle, "raw-crash"], [w, "interp-crash"]] as const) {
    if (x.verdict === "crash") {
      fail(kind, ["stage=" + (x.stage ?? "?"), x.err ?? ""], src, (x.err ?? "").split("\n")[0]);
      return;
    }
  }
  if (oracle.verdict === "skip" || w.verdict === "skip") {
    const why = oracle.verdict === "skip" ? "raw-" + (oracle.stage ?? "?") : (w.stage ?? "?");
    save_file("skipped", m.seed, ["SKIPPED reason=" + why], src);
    ms.verdict = { kind: "skip", note: why };
    return;
  }
  const want = (oracle.outs?.[0] ?? "").trim();
  const got = (w.outs?.[0] ?? "").trim();
  if (got !== want) {
    fail("seal-diverge", ["raw interp:    " + want, "sealed interp: " + got], src, "raw=" + want + " sealed=" + got);
    return;
  }
  ms.want = want;
}

// RunSpec : one execution of the batch binary — its environment, what it
// must print, and the stdout line indexes owned by trans-flagged members'
// extra lines. group_runs: the plain run over the non-dying members, then
// one run per dying member selected by FZ_MEMBER.
type RunSpec = { label: string; env: Env; exp: Expect; transLines: number[] };

function group_runs(states: MemberState[]): RunSpec[] {
  const plain = group_expect(states.filter((s) => !member_dies(s.m)));
  const runs: RunSpec[] = [{ label: "", env: undefined, ...plain }];
  states.forEach((s, i) => {
    if (member_dies(s.m)) {
      runs.push({ label: " [FZ_MEMBER=" + String(i) + "]", env: { FZ_MEMBER: String(i) }, exp: member_expect(s.m, s.want), transLines: [] });
    }
  });
  return runs;
}

function group_expect(states: MemberState[]): { exp: Expect; transLines: number[] } {
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
    err.push(...e.err);
    code = e.code;
  }
  return { exp: { out, err, code }, transLines };
}

async function group_compiled(states: MemberState[], solo: boolean): Promise<{ fail: string | null; skip: string | null; ulp: boolean }> {
  const live = states.filter((s) => s.verdict === null);
  if (live.length === 0) {
    return { fail: null, skip: null, ulp: false };
  }
  const members = live.map((s) => s.m);
  const src = assemble(members, "sealed");
  const w = await phase("worker:emit", () => pool.run(src, "emit"));
  if (w.verdict === "skip") {
    return { fail: null, skip: w.stage ?? "emit-skip", ulp: false };
  }
  if (w.verdict !== "ok") {
    return { fail: "EMIT " + w.verdict + " (" + (w.stage ?? "?") + "): " + (w.err ?? "").split("\n").slice(0, 3).join(" "), skip: null, ulp: false };
  }
  if (CHECK_ONLY) {
    return { fail: null, skip: null, ulp: false };
  }
  const runs = group_runs(live);
  const base = "fz" + String(members[0].seed) + (solo ? "s" : "b");
  const dir = fs.mkdtempSync(path.join(TMP, "g-"));
  const fail = (why: string): { fail: string; skip: null; ulp: boolean } => ({ fail: why, skip: null, ulp: false });
  let ulp = false;
  try {
    const cap = RUN_TIMEOUT * Math.max(1, members.length);
    const cpu = path.join(dir, base + "_cpu");
    // C sequential: the compiled reference, every run against its expectation
    const cc = await leg_cc(dir, base, w.csrc ?? "", [], base + "_cpu", CC_TIMEOUT);
    if (cc.skip === true) {
      return { fail: null, skip: cc.why ?? "cc-timeout", ulp: false };
    }
    if (!cc.ok) {
      return fail(cc.why ?? "cc failed");
    }
    const seqs: LegOut[] = [];
    for (const r of runs) {
      const seq = await phase("run:seq", () => leg_run(cpu, ["--parallel", "off"], dir, cap, r.env));
      if (seq.why !== undefined) {
        return fail("C-SEQ" + r.label + " " + seq.why);
      }
      const d = cmp_expect(r.exp, seq);
      if (d !== null) {
        return fail("C-SEQ" + r.label + " vs expectation: " + d);
      }
      seqs.push(seq);
    }
    // lane : one more leg, every run against its sequential reference
    const lane = async (label: string, soft: boolean, run: (env: Env) => Promise<LegOut>): Promise<string | null> => {
      for (let i = 0; i < runs.length; i++) {
        const got = await run(runs[i].env);
        if (got.why !== undefined) {
          return label + runs[i].label + " " + got.why;
        }
        const d = cmp_legs(seqs[i], got, runs[i].transLines, soft);
        if (d.diff !== null) {
          return label + runs[i].label + " vs C-SEQ: " + d.diff;
        }
        ulp = ulp || d.ulp;
      }
      return null;
    };
    const jsf = path.join(dir, base + ".js");
    fs.writeFileSync(jsf, w.jssrc ?? "");
    const js = await lane("JS", true, (env) => phase("run:js", () => leg_run(process.execPath, [jsf], dir, cap, env)));
    if (js !== null) {
      return fail(js);
    }
    if (THREADS > 0) {
      const par = await lane("C-PAR", false, (env) => phase("run:par", () => leg_run(cpu, ["--threads", String(THREADS), "--gpu", "off"], dir, cap * 2, env)));
      if (par !== null) {
        return fail(par);
      }
    }
    // GPU lanes: the same .c rebuilt with the platform flags, run --gpu on,
    // strictly one program at a time
    const gpu = (label: string, flags: string[], bin: string): Promise<{ skip?: string; fail?: string }> => gpu_serial(async () => {
      const lname = label.toLowerCase();
      const gc = await leg_cc(dir, base, w.csrc ?? "", flags, bin, GPU_CC_TIMEOUT);
      if (gc.skip === true) {
        return { skip: gc.why ?? lname + "-cc-timeout" };
      }
      if (!gc.ok) {
        return { fail: label + " " + (gc.why ?? "cc failed") };
      }
      const f = await lane(label, true, (env) => phase("run:" + lname, () => leg_run(path.join(dir, bin), ["--gpu", "on"], dir, GPU_RUN_TIMEOUT * Math.max(1, members.length), env)));
      return f !== null ? { fail: f } : {};
    });
    const lanes: Array<[boolean, string, string[], string]> = [
      [WITH_METAL, "METAL", ["-DBEND_METAL=1", "-x", "objective-c", "-fobjc-arc",
        "-framework", "Metal", "-framework", "Foundation"], base + "_mtl"],
      [WITH_CUDA, "CUDA", ["-DBEND_CUDA=1", "-I/usr/local/cuda/include", "-L/usr/local/cuda/lib64",
        "-Wl,-rpath,/usr/local/cuda/lib64", "-lcuda", "-lnvrtc"], base + "_cud"],
    ];
    for (const [on, label, flags, bin] of lanes) {
      if (!on) {
        continue;
      }
      const got = await gpu(label, flags, bin);
      if (got.skip !== undefined) {
        return { fail: null, skip: got.skip, ulp };
      }
      if (got.fail !== undefined) {
        return { fail: got.fail, skip: null, ulp };
      }
    }
  } finally {
    if (!KEEP) {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  }
  return { fail: null, skip: null, ulp };
}

async function test_group(seeds: bigint[], solo: boolean): Promise<Verdict[]> {
  const states: MemberState[] = seeds.map((sd, k) => {
    const m = phase_sync("gen", () => gen_member(sd, solo ? 0 : k * UID_STRIDE));
    return { m, verdict: null, want: null };
  });
  for (const s of states) {
    tally_feats(s.m.feats);
  }
  return test_members(states, solo);
}

// test_members : run the legs over already-generated members
async function test_members(states: MemberState[], solo: boolean): Promise<Verdict[]> {
  const grouped = states;
  await Promise.all(grouped.map((s) => member_interp(s)));
  const res = await group_compiled(grouped, solo);
  if (res.skip !== null) {
    for (const s of grouped) {
      if (s.verdict === null) {
        save_file("skipped", s.m.seed, ["SKIPPED reason=" + res.skip], assemble([s.m], "sealed"));
        s.verdict = { kind: "skip", note: res.skip };
      }
    }
  } else if (res.fail !== null && solo) {
    const s = grouped[0];
    const kind = res.fail.startsWith("EMIT") ? "compiler-crash"
      : /COMPILE FAILURE/.test(res.fail) ? "cc-fail"
      : /TIMEOUT/.test(res.fail) ? "leg-timeout" : "leg-diverge";
    save_finding(s.m.seed, kind, [res.fail], assemble([s.m], "sealed"), res.fail.split("\n")[0]);
    s.verdict = { kind: "fail", fkind: kind, why: res.fail };
  } else if (res.fail !== null) {
    // attribute: re-run each member alone at uid base 0, so whatever it
    // saves reproduces under a bare --seed
    console.log("\nbatch of " + String(grouped.length) + " failed, isolating: " + res.fail.split("\n")[0]);
    let blamed = false;
    for (const s of grouped) {
      if (s.verdict !== null) {
        continue;
      }
      const v = await test_group([s.m.seed], true);
      s.verdict = v[0];
      if (v[0].kind === "fail") {
        blamed = true;
      }
    }
    if (!blamed) {
      save_finding(grouped[0].m.seed, "batch-only",
        ["no member fails alone — the MERGE or whole-book emission is at fault", res.fail,
          "members: " + grouped.map((s) => String(s.m.seed)).join(" ")], assemble(grouped.map((s) => s.m), "sealed"),
        String(grouped.length) + " members: " + res.fail.split("\n")[0]);
      grouped[0].verdict = { kind: "fail", fkind: "batch-only", why: res.fail };
    }
  }
  if (res.ulp) {
    for (const s of grouped) {
      if (s.verdict === null && s.m.trans) {
        s.verdict = { kind: "skip", note: "trans-ulp" };
      }
    }
  }
  for (const s of states) {
    if (s.verdict === null) {
      s.verdict = { kind: "ok" };
    }
  }
  return states.map((s) => s.verdict as Verdict);
}

// Reduce
// ------
// Greedy delta reduction of one seed's failing program: drop result and
// extra statements (their binds read as 0 downstream), the extra def, the
// IO tail, then every entry nothing needs, keeping a change while the
// same failure signature holds. Legs run exactly as in a solo test.

// fail_sig : the failure's identity — its finding kind, plus the first
// message line with digits masked for crashes and rejects (values in a
// divergence message shift as the program shrinks)
function fail_sig(v: Verdict): string | null {
  if (v.kind !== "fail") {
    return null;
  }
  const kind = v.fkind ?? "fail";
  const exact = /crash|reject|cc-fail/.test(kind);
  return kind + (exact ? ":" + (v.why ?? "").split("\n")[0].replace(/[0-9]+/g, "#") : "");
}

async function reduce_run(seed: bigint): Promise<void> {
  const sig = async (m: Member): Promise<string | null> =>
    fail_sig((await test_members([{ m, verdict: null, want: null }], true))[0]);
  const size = (m: Member): string => String(m.lines.length) + "+" + String(m.xlines.length) + " statements, "
    + String(m.entries.length) + " entries" + (m.tail !== null ? ", io tail" : "");
  let m = gen_member(seed, 0);
  const want = await sig(m);
  if (want === null) {
    console.log("seed " + String(seed) + " passes: nothing to reduce");
    return;
  }
  console.log("reducing seed=" + String(seed) + " [" + want + "]: " + size(m));
  QUIET = true;
  const keep = async (m2: Member): Promise<boolean> => {
    const ok = (await sig(m2)) === want;
    if (ok) {
      m = m2;
    }
    return ok;
  };
  for (let pass = 1, changed = true; changed; pass++) {
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
    for (let i = m.entries.length - 1; i >= 0; i--) {
      changed = (await keep({ ...m, entries: m.entries.filter((_, j) => j !== i) })) || changed;
    }
    console.log("pass " + String(pass) + ": " + size(m));
  }
  QUIET = false;
  const f = save_file("", seed, ["FUZZ REDUCED kind=" + want, repro_line(seed),
    "reduced by --reduce: the same failure on this program"], assemble([m], "sealed"), ".min");
  console.log("-> " + f);
}

// Fuzz
// ----

async function fuzz_run(): Promise<void> {
  if (cli_flag("--dump") || cli_flag("--dump-raw")) {
    const m = gen_member(BASE_SEED, 0);
    process.stdout.write(assemble([m], cli_flag("--dump-raw") ? "raw" : "sealed"));
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
  pool = new Pool(Number(cli_opt("--pool", String(Math.max(2, Math.min(10, JOBS * 2))))));
  if (REDUCE !== "") {
    try {
      await reduce_run(BigInt(REDUCE));
    } finally {
      pool.close();
      if (!KEEP) {
        fs.rmSync(TMP, { recursive: true, force: true });
      }
    }
    return;
  }
  // smoke : hand-verified per-feature cover (re-pick after any edit that
  // remaps seeds: each seed passes solo and the union covers smoke_need)
  const smoke = [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n, 9n, 13n, 15n, 17n, 24n, 79n];
  const fixed = SMOKE ? smoke : null;
  const count = fixed?.length ?? COUNT;
  const lanes = "interp+cseq+js" + (THREADS > 0 ? "+par" + String(THREADS) : "") + (WITH_METAL ? "+metal" : "") + (WITH_CUDA ? "+cuda" : "");
  console.log("bend2 fuzz: count=" + String(count) + (LOOP ? " (loop)" : "") + " seed=" + String(BASE_SEED)
    + " jobs=" + String(JOBS) + " batch=" + String(BATCH) + " legs=" + lanes
    + (SMOKE ? " +smoke" : "") + (CHECK_ONLY ? " +check-only" : ""));
  const t0 = performance.now();
  let seed = BASE_SEED;
  let done = 0;
  let launched = 0;
  const inflight = new Set<Promise<void>>();
  const total = (): number => (LOOP && fixed === null ? Infinity : count);
  while (done < total()) {
    while (inflight.size < JOBS && launched < total()) {
      const batch: bigint[] = [];
      while (batch.length < BATCH && launched < total()) {
        batch.push(fixed?.[launched] ?? seed);
        if (fixed === null) {
          seed = rng_step(seed);
        }
        launched++;
      }
      const p = test_group(batch, batch.length === 1)
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
  const smoke_need = ["qpoly-def", "qpoly-call", "kind-qvar", "kind-meet", "adt-data", "adt-qpoly",
    "erased-field", "erased-param", "f32-arith", "f32-trans", "f32-conv", "nat-table", "peel",
    "array-ops", "map-ops", "string-append", "match-adt", "do-maybe", "do-result", "fork", "bang",
    "tail", "eql", "rwt", "thm", "dep", "ford", "share", "partial", "io-tail",
    "seal-add", "seal-xor", "seal-dist", "seal-mask", "seal-cmp", "seal-rot"];
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
  if (cli_flag("--help") || cli_flag("-h")) {
    print_help();
  } else if (cli_flag("--worker")) {
    await worker_main();
  } else {
    await fuzz_run();
  }
}
