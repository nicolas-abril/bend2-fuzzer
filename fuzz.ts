#!/usr/bin/env bun
// Differential fuzzer for the bend2-core toolchain (bend2/bend.ts + comp.ts).
// Each seed deterministically generates a well-typed, terminating Bend program
// in two algebraically-equal spellings (raw and identity-sealed) and runs it
// across every leg:
//
//   - interp (the spec): term_snf on the result defs, raw and sealed, or on
//     a pure main, printed by term_show — the only leg a book without Base
//     has. The raw value is the oracle; the sealed one must equal it, so a
//     broken seal cannot bless itself. The interpreter runs Base's
//     structural code (Word adder chains), so this leg is also a bit-level
//     spec differential against the native ops the backends substitute.
//   - C (compile_book): one standalone .c, built with clang at the group's
//     drawn -O level and run sequentially (+RTS --threads 1 --gpu off), then in
//     parallel at the group's drawn thread count; with --metal / --cuda the
//     same .c is rebuilt for the device and run +RTS --gpu on.
//   - JS (js_book): the emitted .js run under bun.
//
// Every checked book also meets the template table's invariants (distinct
// ~ argument keys name distinct instances; a key carries its literals
// exactly), which every generated template call exercises.
//
// The program shape ties the legs together:
//
//   def result() -> U32: ...   pure: no native claim of Base (F32's ops,
//                              effects) reaches it — interp-comparable
//   def extra()  -> U32: ...   the rest: F32, forks with ! marks, long loops,
//                              compared across compiled legs only, with the
//                              sequential C run as the reference
//   def main() -> IO(Unit):    prints result, an optional deterministic IO
//                              tail, then extra
//
// A `trans`-flagged program (a float transcendental) downgrades a JS-vs-C
// mismatch on its extra line to a counted skip (libm vs fround(double)).
//
// GENERATION IS TYPE-DIRECTED SYNTHESIS over one model of the language:
//
//   - THE ENVIRONMENT IS READ, NOT MIRRORED. With Base in scope (a seed's
//     draw), every datatype of Base is a type the generator draws, builds
//     by its constructors and matches, read off the checked Base book; a
//     datatype the backends hold natively (a machine word, an Array) or whose
//     fields have no spelling here is opaque: its values come from literals
//     and calls only. Every def of Base's interface (Family.fn; a deeper
//     name is a helper) whose signature has a spelling is a call any goal
//     of its return type may take; its flags come from its
//     body: one that reaches a native claim (a bodiless law: F32's ops, the
//     effects) is stuck in the interpreter and stays off the pure side, one
//     that reaches an effect is never drawn (the IO tail owns effects). The
//     operators are the parser's own table: a two-argument call of a method
//     the table names is spelled infix, framed by its family ((a + b : U32)
//     is U32.add), a fixed one bare (a || b), Array.get/set as a[i] and
//     a[i] <- v. Literals are per type (U32, F32, Nat, Char, String, List,
//     Array), since the surface is.
//   - TYPES ARE TERMS: families by match on an index (Nat or an enum), a
//     datatype indexed by an arm's sub-index (Word's idiom), propositions
//     (Empty, equalities of literals, their negation), dependent pairs, and
//     a def's evidence about an earlier index parameter; see fam_new.
//   - DEFS ARE ONE PRODUCTION (def_new): parameters drawn as types (the
//     goal generalized over type and quantity variables at times, a leading
//     function parameter a template at times), a match at the head of the
//     body over some of them (a decision tree over constructors, variable
//     rows, a nested match on a row's last binder), each leaf synthesized
//     against the goal, the def callable from its own leaves with a
//     sub-field of its decreasing column. Loops, folds, tree recursion,
//     builders, transforms, generic and higher-order defs are this one
//     production at different goals and parameter types.
//   - STATEMENTS ARE THREE PRODUCTIONS: a value of any type read to a U32,
//     a parallel let (the one fork shape, `!`-marked at times), a proof
//     rewritten on.
//   - SIZES ARE ONE DISTRIBUTION (Gen.size): every count and depth — types,
//     constructors, fields, defs, parameters, statements, expression and
//     type depth, literal lengths, loop counts — is small by preference with
//     a power-law tail to its cap.
//   - the var quantity system end to end: -x / x / +x sigils, affine
//     consumption, quantity parameters and meets, data-kinded datatypes,
//     the Fill and Plus sugars.
//
// What a seed's program is — Base or an empty initial environment, free
// declaration names, a file of its own, a foreign effect, a clash mutant,
// a pure printed main, the IO tail, the surface-syntax rate — is its
// profile, drawn from the seed alone (profile()), so a solo re-run
// reproduces it.
//
// GROUPS: a group of seeds (its size drawn from its first seed) merges into
// ONE compiled program — a concatenation at disjoint uid ranges, or files
// apart by namespace — whose main prints each member's lines in order, so
// clang and process spawn are paid once per group while attribution stays
// per line. A member whose tail dies closes its group (its IO.die ends
// main after every other member's lines). A failing
// group re-runs its members solo at uid base 0 under the group's lanes; a
// group that fails when no member does is itself a finding (batch-only).
//
// Findings land in findings/seed-N.bend (program + verdict + repro line),
// beside the build that failed and a delta-reduced program. Resource
// exhaustion is a skip. A generator edit remaps the seeds whose draws reach
// the edited site (each site draws from its own split stream), so the saved
// program is the durable artifact.

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
const BASE_PATH = fs.realpathSync(path.join(ROOT, "bend2", "base.bend"));
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
    "                 +RTS --gpu on (macOS; GPU runs are serialized)",
    "  --cuda         ALSO build each program with -DBEND_CUDA and run",
    "                 +RTS --gpu on (Linux + NVIDIA)",
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

// phase : f timed under name, sync or async
function phase<A>(name: string, f: () => A): A {
  const t = performance.now();
  const note = (): void => {
    const p = PHASE[name] ??= { ms: 0, n: 0, all: [] };
    const d = performance.now() - t;
    p.ms += d;
    p.n += 1;
    p.all.push(d);
  };
  let r: A;
  try {
    r = f();
  } catch (e) {
    note();
    throw e;
  }
  if (r instanceof Promise) {
    return r.finally(note) as A;
  }
  note();
  return r;
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

// TAIL : the power-law exponent of every size draw (smaller: heavier tail)
const TAIL = 1.7;

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
    return Number(this.r() % BigInt(Math.max(1, Math.floor(n))));
  }
  chance(p: number): boolean {
    return this.int(1000) < p * 1000;
  }
  pick<T>(xs: readonly T[]): T {
    return xs[this.int(xs.length)];
  }
  wpick<T>(xs: Array<[number, T]>): T {
    const total = xs.reduce((a, [w]) => a + w, 0);
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
  // size : lo plus a Pareto draw of scale `scale`, capped at cap: small by
  // preference (the median is lo + ~0.5 scale), with a power-law tail
  size(lo: number, scale: number, cap: number): number {
    const u = (this.int(1 << 20) + 1) / (1 << 20);
    return Math.min(cap, lo + Math.floor(scale * (Math.pow(u, -1 / TAIL) - 1)));
  }
  shuffle<T>(xs: readonly T[]): T[] {
    const out = xs.slice();
    for (let i = out.length - 1; i > 0; i--) {
      const j = this.int(i + 1);
      [out[i], out[j]] = [out[j], out[i]];
    }
    return out;
  }
}

// Types
// -----
// The generator's mirror of the object language. QT is a quantity term: a
// literal (&0/&1/&2), a bound quantity variable, or a meet. Every nominal
// type is an adt instance — Base's datatypes and type-level defs, and the
// program's own — carrying its quantity, type and index arguments; an adt
// with null ctors is opaque (built and read only through literals and
// calls). sig is Base's Sigma: a tuple when x is null, else a dependent
// pair whose second type may mention x. Propositions are types: Empty (a
// datatype with no constructor), {l == r : T} over literals, and {l != r :
// T}, spelled for {l == r : T} -> Empty.

type QT = { k: "q"; q: 0 | 1 | 2 } | { k: "qv"; n: string } | { k: "qm"; a: QT; b: QT };

const Q0: QT = { k: "q", q: 0 };
const Q1: QT = { k: "q", q: 1 };
const Q2: QT = { k: "q", q: 2 };

function qt_str(q: QT): string {
  switch (q.k) {
    case "q": return "&" + String(q.q);
    case "qv": return q.n;
    case "qm": return "(" + qt_bare(q) + ")";
  }
}

// qt_bare : a quantity term without the outer parens (inside Kind(..))
function qt_bare(q: QT): string {
  return q.k === "qm" ? qt_str(q.a) + " <&> " + qt_str(q.b) : qt_str(q);
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

function qt_sub(q: QT, m: Map<string, QT>): QT {
  switch (q.k) {
    case "q": return q;
    case "qv": return m.get(q.n) ?? q;
    case "qm": return { k: "qm", a: qt_sub(q.a, m), b: qt_sub(q.b, m) };
  }
}

// qt_fits : is a type of kind quantity `have` accepted where Kind(`need`)
// is demanded? Mirrors term_compare's Typ case: Data (&2) fits every
// kind, every kind fits Kind(&0) and Kind(&1), a meet on the left needs
// both sides, a meet on the right accepts either side, and a stuck target
// licenses only an identical term.
function qt_fits(have: QT, need: QT): boolean {
  const n = qt_known(need);
  if (qt_known(have) === 2 || (need.k === "q" && n !== 2) || qt_str(have) === qt_str(need)) {
    return true;
  }
  if (have.k === "qm") {
    return qt_fits(have.a, need) && qt_fits(have.b, need);
  }
  return need.k === "qm" && (qt_fits(have, need.a) || qt_fits(have, need.b));
}

function qt_unify(pat: QT, goal: QT, qm: Map<string, QT>): boolean {
  if (pat.k === "qv" && !qm.has(pat.n)) {
    qm.set(pat.n, goal);
    return true;
  }
  return qt_str(qt_sub(pat, qm)) === qt_str(goal);
}

// Sigil quantities on binders: 0 erased (-), 1 lone (bare), 2 many (+)
type BQ = 0 | 1 | 2;

function bq_prefix(q: BQ): string {
  return q === 0 ? "-" : q === 2 ? "+" : "";
}

type Field = { q: BQ; t: T };
type Ctor = { name: string; fields: Field[] };
type TvarInfo = { n: string; q: QT };
// IVar : a term in scope a type may mention (an index parameter, an arm's
// sub-index — sub: the one place an unfinished family may be applied)
type IVar = { n: string; t: T; sub?: boolean };
type Adt = {
  // id : the datatype's identity (names may repeat across members)
  id: number;
  name: string;
  qps: string[];
  tps: TvarInfo[];
  // ips : erased index parameters (terms), the Word.Con<-p: Nat> shape
  ips: IVar[];
  kind: QT;
  // null : opaque — no constructor the generator builds or matches
  ctors: Ctor[] | null;
  // paren : a type-level def, applied as Name(args)
  paren: boolean;
  base: boolean;
  // rec : a constructor holds the type at its own parameters
  rec: boolean;
};

// Families : a type-level def by match on one index (see fam_new)
type FamArm = { pat: string; sub: string | null; lit: string | null; ty: T; src?: string };
type Fam = { id: number; name: string; idx: T; kind: QT; arms: FamArm[]; done: boolean };
let IDS = 0;

type AdtT = { k: "adt"; a: Adt; qs: QT[]; args: T[]; iargs: string[]; spell?: "or" | "bar" };
type SigT = { k: "sig"; x: string | null; a: T; b: T; q: 1 | 2; spell: "amp" | "pair" | "sigma" | "exists" };
type FunT = { k: "fun"; q: BQ; dom: T; cod: T; ne?: boolean };
type EqlT = { k: "eql"; t: T; l: string; r: string };
type T = { k: "tvar"; n: string; q: QT } | AdtT | { k: "app"; f: Fam; arg: string } | SigT | FunT | EqlT;

function inst(a: Adt, qs: QT[] = [], args: T[] = [], iargs: string[] = []): AdtT {
  return { k: "adt", a, qs, args, iargs };
}

// adt_self : the datatype at its own parameters
function adt_self(a: Adt): AdtT {
  return inst(a, a.qps.map((n): QT => ({ k: "qv", n })), a.tps.map((tp): T => ({ k: "tvar", n: tp.n, q: tp.q })), a.ips.map((ip) => ip.n));
}

// is_t : t is Base's datatype of that name
function is_t(t: T, name: string): boolean {
  return t.k === "adt" && t.a.base && t.a.name === name;
}

// ty_str is the SAFE rendering: it never leads with '+' (a '+'-headed type
// after '(' or '&' would parse as a binder); the Plus sugar lives only in
// ty_top, used at annotation sites. canon renders the structure alone (the
// spellings dropped): the key of equality, unification and every memo.
// ty_infix : does the type render as an infix or arrow form (an arrow, an
// & or | chain, a bare dependent pair), which a juxtaposed position
// parenthesizes?
function ty_infix(t: T): boolean {
  return (t.k === "fun" && !(t.ne === true && t.dom.k === "eql")) || (t.k === "adt" && t.spell === "bar")
    || (t.k === "sig" && t.q === 1 && (t.x === null ? t.spell !== "pair" && t.spell !== "sigma" : t.spell === "amp"));
}

function ty_render(t: T, canon: boolean): string {
  const grp = (u: T): string => {
    const s = ty_render(u, canon);
    return !canon && ty_infix(u) ? "(" + s + ")" : s;
  };
  switch (t.k) {
    case "tvar": return t.n;
    case "app": return t.f.name + (canon ? "#" + String(t.f.id) : "") + "(" + t.arg + ")";
    case "adt": {
      if (!canon && t.spell === "or") {
        return "Or(" + t.args.map(grp).join(", ") + ")";
      }
      if (!canon && t.spell === "bar") {
        return t.args.map(grp).join(" | ");
      }
      // the Fill sugar: an all-&1 quantity block drops
      const fill = !canon && t.args.length > 0 && t.qs.every((q) => q.k === "q" && q.q === 1);
      const xs = (fill ? [] : t.qs.map(qt_str)).concat(t.args.map(grp), t.iargs);
      const name = t.a.name + (canon && !t.a.base ? "#" + String(t.a.id) : "");
      return t.a.paren ? name + "(" + xs.join(", ") + ")" : xs.length === 0 ? name : name + "<" + xs.join(", ") + ">";
    }
    case "sig": {
      const b = ty_render(t.b, canon);
      if (canon || t.spell === "sigma" || t.q === 2) {
        return "Sigma<&" + String(t.q) + ", &" + String(t.q) + ", " + grp(t.a) + ", " + (t.x ?? "_") + " => " + b + ">";
      }
      if (t.x === null) {
        return t.spell === "pair" ? "Pair(" + grp(t.a) + ", " + grp(t.b) + ")" : grp(t.a) + " & " + grp(t.b);
      }
      return t.spell === "exists" ? "Exists(" + grp(t.a) + ", " + t.x + " => " + b + ")" : "&" + t.x + ": " + grp(t.a) + " -> " + b;
    }
    case "fun": {
      if (!canon && t.ne === true && t.dom.k === "eql") {
        return "{" + t.dom.l + " != " + t.dom.r + " : " + ty_render(t.dom.t, canon) + "}";
      }
      return t.q === 1 ? grp(t.dom) + " -> " + ty_render(t.cod, canon)
        : "@" + bq_prefix(t.q) + "zq: " + grp(t.dom) + " -> " + ty_render(t.cod, canon);
    }
    case "eql": return "{" + t.l + " == " + t.r + " : " + ty_render(t.t, canon) + "}";
  }
}

function ty_str(t: T): string {
  return ty_render(t, false);
}

function ty_key(t: T): string {
  return ty_render(t, true);
}

function ty_eq(a: T, b: T): boolean {
  return ty_key(a) === ty_key(b);
}

// ty_grp : parenthesize where juxtaposition would mis-parse: arrow domains,
// & chains, | chains, and type arguments
function ty_grp(t: T): string {
  return ty_infix(t) ? "(" + ty_str(t) + ")" : ty_str(t);
}

// ty_top : the annotation-site rendering — the Plus sugar (an all-&2
// quantity block dropped behind a leading '+') fires here and only here,
// and a bare &x: A -> B parenthesizes (it would head a binder)
function ty_top(t: T): string {
  if (t.k === "adt" && !t.a.paren && t.qs.length > 0 && t.qs.every((q) => q.k === "q" && q.q === 2)) {
    const rest = t.args.map(ty_grp).concat(t.iargs);
    return "+" + t.a.name + (rest.length > 0 ? "<" + rest.join(", ") + ">" : "");
  }
  if (t.k === "sig" && t.q === 2) {
    return "+Sigma<" + ty_grp(t.a) + ", " + (t.x ?? "_") + " => " + ty_str(t.b) + ">";
  }
  return t.k === "sig" && t.x !== null && ty_infix(t) ? "(" + ty_str(t) + ")" : ty_str(t);
}

// ty_quant : the type's kind quantity (a QT — may be open)
function ty_quant(t: T): QT {
  switch (t.k) {
    case "tvar": return t.q;
    case "adt": return qt_sub(t.a.kind, new Map(t.a.qps.map((n, i) => [n, t.qs[i]])));
    case "app": return t.f.kind;
    case "sig": return t.q === 2 ? Q2 : Q1;
    case "fun": return Q1;
    case "eql": return Q2;
  }
}

// ty_data : may this type sit under a + binder (concretely Data)?
function ty_data(t: T): boolean {
  return qt_known(ty_quant(t)) === 2;
}

function ty_sub(t: T, m: Map<string, T>, qm: Map<string, QT>): T {
  switch (t.k) {
    case "tvar": return m.get(t.n) ?? { ...t, q: qt_sub(t.q, qm) };
    case "adt": return { ...t, qs: t.qs.map((q) => qt_sub(q, qm)), args: t.args.map((x) => ty_sub(x, m, qm)) };
    case "sig": return { ...t, a: ty_sub(t.a, m, qm), b: ty_sub(t.b, m, qm) };
    case "fun": return { ...t, dom: ty_sub(t.dom, m, qm), cod: ty_sub(t.cod, m, qm) };
    case "eql": return { ...t, t: ty_sub(t.t, m, qm) };
    case "app": return t;
  }
}

// ty_tsub : the type with the term `n` replaced by `e` (an arm's sub-index
// at a literal, an index parameter at its argument, a witness)
function ty_tsub(t: T, n: string, e: string): T {
  switch (t.k) {
    case "app": return t.arg === n ? { ...t, arg: e } : t;
    case "adt": return { ...t, args: t.args.map((x) => ty_tsub(x, n, e)), iargs: t.iargs.map((x) => x === n ? e : x) };
    case "sig": return { ...t, a: ty_tsub(t.a, n, e), b: t.x === n ? t.b : ty_tsub(t.b, n, e) };
    case "fun": return { ...t, dom: ty_tsub(t.dom, n, e), cod: ty_tsub(t.cod, n, e) };
    case "eql": return { ...t, l: t.l === n ? e : t.l, r: t.r === n ? e : t.r };
    case "tvar": return t;
  }
}

// ty_mentions : does the type mention the term `n`? (a binder such a type
// holds cannot be shadowed while the value lives)
function ty_mentions(t: T, n: string): boolean {
  switch (t.k) {
    case "app": return t.arg === n;
    case "adt": return t.iargs.includes(n) || t.args.some((x) => ty_mentions(x, n));
    case "sig": return ty_mentions(t.a, n) || (t.x !== n && ty_mentions(t.b, n));
    case "fun": return ty_mentions(t.dom, n) || ty_mentions(t.cod, n);
    case "eql": return t.l === n || t.r === n;
    case "tvar": return false;
  }
}

// ty_open : does the type mention an abstract type, a quantity variable or
// an index term?
function ty_open(t: T): boolean {
  switch (t.k) {
    case "tvar": return true;
    case "app": return !idx_is_lit(t.f.idx, t.arg);
    // the pair binds its witness: the evidence is closed once it is a term
    case "sig": return ty_open(t.a) || ty_open(t.x !== null && idx_type(t.a) ? ty_tsub(t.b, t.x, idx_lits(t.a)[0]) : t.b);
    case "adt": return t.args.some(ty_open) || t.qs.some((q) => qt_known(q) === null) || t.iargs.some((x, i) => !idx_is_lit(t.a.ips[i].t, x));
    case "fun": return ty_open(t.dom) || ty_open(t.cod);
    case "eql": return ty_open(t.t);
  }
}

// ty_unify : bind pat's type and quantity variables so pat matches goal
function ty_unify(pat: T, goal: T, m: Map<string, T>, qm: Map<string, QT>): boolean {
  if (pat.k === "tvar") {
    const got = m.get(pat.n);
    if (got !== undefined) {
      return ty_eq(got, goal);
    }
    // the bound type must fit the variable's declared kind
    if (!qt_fits(ty_quant(goal), qt_sub(pat.q, qm))) {
      return false;
    }
    m.set(pat.n, goal);
    return true;
  }
  if (pat.k === "adt" && goal.k === "adt") {
    return pat.a === goal.a && pat.iargs.join(",") === goal.iargs.join(",")
      && pat.qs.every((q, i) => qt_unify(q, goal.qs[i], qm)) && pat.args.every((x, i) => ty_unify(x, goal.args[i], m, qm));
  }
  if (pat.k === "sig" && goal.k === "sig") {
    return pat.q === goal.q && (pat.x === null) === (goal.x === null) && ty_unify(pat.a, goal.a, m, qm)
      && ty_unify(pat.x === null || goal.x === null ? pat.b : ty_tsub(pat.b, pat.x, goal.x), goal.b, m, qm);
  }
  if (pat.k === "fun" && goal.k === "fun") {
    return pat.q === goal.q && ty_unify(pat.dom, goal.dom, m, qm) && ty_unify(pat.cod, goal.cod, m, qm);
  }
  return pat.k === goal.k && ty_eq(pat, goal);
}

// ctor_fields : a constructor's fields at an instance: type and quantity
// arguments substituted, index parameters replaced by the instance's
function ctor_fields(t: AdtT, ct: Ctor): Field[] {
  const m = new Map(t.a.tps.map((tp, i) => [tp.n, t.args[i]]));
  const qm = new Map(t.a.qps.map((n, i) => [n, t.qs[i]]));
  return ct.fields.map((f) => ({ q: f.q, t: t.a.ips.reduce((u, ip, i) => ty_tsub(u, ip.n, t.iargs[i]), ty_sub(f.t, m, qm)) }));
}

// Index types : a term of Nat or of an enum (every constructor nullary)
// may index a family
function idx_type(t: T): t is AdtT {
  return t.k === "adt" && t.args.length + t.qs.length + t.iargs.length === 0 && t.a.ctors !== null && t.a.ctors.length > 0
    && (is_t(t, "Nat") || t.a.ctors.every((ct) => ct.fields.length === 0)) && ty_data(t);
}

// idx_lits : the closed literals drawn for an index type (Nat: 0..3)
function idx_lits(t: T): string[] {
  if (is_t(t, "Nat")) {
    return ["0n", "1n", "2n", "3n"];
  }
  return t.k === "adt" ? (t.a.ctors ?? []).map((ct) => ct.name + "{}") : [];
}

function idx_is_lit(t: T, arg: string): boolean {
  return is_t(t, "Nat") ? /^\d+n$/.test(arg) : /\{\}$/.test(arg);
}

// ty_cost : the fewest steps that complete a term of the type once its
// budget is spent (Infinity: none the generator builds): a literal, a
// nullary constructor or {==} completes at once; a constructor, a pair, a
// lambda, a family's unfolding or a call one step above its dearest part;
// a type met again on the way does not complete (a recursive constructor
// is never the cheapest), except a family met again inside its own arms
// (the recursion through its sub-index ends at the base arm). A type
// variable is taken as a binder in scope. A finite cost found on the way
// is kept (a bound, if a type met before was barred), an infinite one only
// at the top.
const COST = new Map<string, number>();
function ty_cost(t: T, seen: Set<string> = new Set()): number {
  const key = ty_key(t);
  const memo = COST.get(key);
  if (memo !== undefined && (memo < Infinity || seen.size === 0)) {
    return memo;
  }
  if (seen.has(key)) {
    return Infinity;
  }
  const s2 = new Set(seen).add(key);
  const max = (ts: T[]): number => ts.reduce((m, u) => Math.max(m, ty_cost(u, s2)), 0);
  const cost = ((): number => {
    switch (t.k) {
      case "tvar": return 0;
      case "eql": return t.l === t.r ? 0 : Infinity;
      case "fun": return ty_refutable(t.dom) ? 1 : 1 + ty_cost(t.cod, s2);
      case "sig": return 1 + (t.x !== null && idx_type(t.a)
        ? Math.min(...idx_lits(t.a).map((w) => ty_cost(ty_tsub(t.b, t.x as string, w), s2)))
        : max([t.a, t.b]));
      case "app": {
        const arm = fam_unfold(t.f, t.arg);
        return arm !== null ? 1 + ty_cost(arm, s2) : fam_total(t.f, s2) ? 1 : Infinity;
      }
      case "adt": {
        const lit = t.a.base ? LITS[t.a.name] : undefined;
        if (lit !== undefined && (lit.ok?.(t) ?? true)) {
          return 0;
        }
        if (t.a.ctors !== null) {
          return Math.min(Infinity, ...t.a.ctors.map((ct) => ct.fields.length === 0 ? 0 : 1 + max(ctor_fields(t, ct).map((f) => f.t))));
        }
        // an opaque type: a call answering it that binds every type
        // variable it has
        return Math.min(Infinity, ...(BASE_BY_HEAD.get(head(t)) ?? []).map((d) => {
          const m = new Map<string, T>();
          const qm = new Map<string, QT>();
          if (d.effect === true || !ty_unify(d.ret, t, m, qm) || d.tps.some((tp) => !m.has(tp.n))) {
            return Infinity;
          }
          const ps = d.ps.map((p) => ({ ...p, t: ty_sub(p.t, m, qm) }));
          return ps.some((p) => p.q === 2 && !ty_data(p.t)) ? Infinity : 1 + max(ps.filter((p) => p.mask === undefined).map((p) => p.t));
        }));
      }
    }
  })();
  if (cost < Infinity || seen.size === 0) {
    COST.set(key, cost);
  }
  return cost;
}

function ty_inh(t: T): boolean {
  return ty_cost(t) < Infinity;
}

// fam_total : every arm of the family has a value (the family met again
// inside its arms is taken so)
function fam_total(f: Fam, seen: Set<string> = new Set()): boolean {
  const key = "fam:" + f.name + "#" + String(f.id);
  return seen.has(key) || (f.done && f.arms.every((arm) => ty_cost(arm.ty, new Set(seen).add(key)) < Infinity));
}

// ty_refutable : an equality of two different constructor literals of an
// index type (for Nat, one side is 0n), refuted by a rewrite through a
// discriminating family
function ty_refutable(t: T): t is EqlT {
  return t.k === "eql" && t.l !== t.r && idx_type(t.t) && (!is_t(t.t, "Nat") || t.l === "0n" || t.r === "0n");
}

// fam_unfold : the arm a closed index selects, its sub-index substituted;
// null on a variable index
function fam_unfold(f: Fam, arg: string): T | null {
  if (!idx_is_lit(f.idx, arg)) {
    return null;
  }
  if (is_t(f.idx, "Nat")) {
    const n = Number(arg.slice(0, -1));
    const arm = f.arms[n === 0 ? 0 : 1];
    return arm.sub === null ? arm.ty : ty_tsub(arm.ty, arm.sub, String(n - 1) + "n");
  }
  return f.arms.find((x) => x.lit === arg)?.ty ?? null;
}

// ty_showable : may a pure main of this type print as its literal? The
// runtimes print through a descriptor of main's type and refuse a function,
// an opaque handle, an erased or a dependent field.
function ty_showable(t: T, seen: Set<Adt> = new Set()): boolean {
  switch (t.k) {
    case "eql": return true;
    case "sig": return t.x === null && ty_showable(t.a, seen) && ty_showable(t.b, seen);
    case "app": {
      const arm = fam_unfold(t.f, t.arg);
      return arm !== null && ty_showable(arm, seen);
    }
    case "adt": {
      if (t.a.ctors === null) {
        return ["U32", "F32"].includes(t.a.name) || (t.a.name === "Array" && ty_showable(t.args[0], seen));
      }
      if (t.a.ips.length > 0 || (t.a.base && IO_OPS.has(t.a.name))) {
        return false;
      }
      if (seen.has(t.a)) {
        return true;
      }
      const s2 = new Set(seen).add(t.a);
      return t.a.ctors.every((ct) => ctor_fields(t, ct).every((f) => f.q !== 0 && ty_showable(f.t, s2)));
    }
    default: return false;
  }
}

// The call registry
// -----------------
// Every def a goal may call: Base's (read off its book) and the program's
// own (registered as they are minted). Spelled
//   name(<quantity and type args, in hdr order>, <value args>)
// with the first tm of them templates (~, closed arguments). A value
// parameter's type may name an earlier parameter n of an index type (dep:
// later types depend on it); mask caps an argument: a Nat one is drawn as a
// small U32 converted, a U32 one taken modulo it.

type Param = { q: BQ; t: T; n?: string; dep?: boolean; mask?: number };
type DefR = {
  name: string;
  qps: string[];
  tps: TvarInfo[];
  hdr: string[];
  ps: Param[];
  ret: T;
  tm: number;
  // stuck : reaches a native claim (the interpreter cannot run it);
  // effect : reaches an effect (only the IO tail performs effects)
  stuck?: boolean;
  effect?: boolean;
  base?: boolean;
  // wip : the def's own leaves are being drawn; a self-call passes one of
  // the current sub-fields at the decreasing column (col)
  wip?: { col: number; ps: V[]; subs: V[]; calls: number };
};

// head : the registry's index of a type (a type variable matches any head)
function head(t: T): string {
  return t.k === "adt" ? "a:" + t.a.name + (t.a.base ? "" : "'") : t.k === "app" ? "f:" + t.f.name : t.k === "tvar" ? "*" : t.k;
}

// Base
// ----
// The fuzzer's own redefinition of Base: its datatypes and an explicitly
// picked set of its defs, written in Base's own declaration syntax and
// read by base_load. A datatype with constructors is transparent (drawn,
// built, matched and read like the program's own); an `opaque` one is built
// and read only through literals and calls: U32 and F32 hold a machine word
// the backends refuse to view structurally, Array's constructors are the
// runtime's own, IO is a type-level def. A def marked `# stuck` reaches a
// native claim (F32's ops): the interpreter cannot run it, so it stays off
// the pure side. The effects are not here: only the IO tail performs them.
// A def of a type-level alias is spelled at its unfolding (Set() is
// Map<&2, Unit>). Sigma is the generator's own sig (`A & B`).

const BASE_TABLE = `
type Empty is Data:
type Unit is Data:
  Unit{}
type Bool is Data:
  False{}
  True{}
type Cmp is Data:
  LT{}
  EQ{}
  GT{}
type Either<a, b, -A: Kind(a), -B: Kind(b)> is Kind(a <&> b):
  Inl{A}
  Inr{B}
type Nat is Data:
  Zero{}
  Succ{Nat}
type Maybe<a, -A: Kind(a)> is Kind(a):
  None{}
  Some{A}
type Result<a, b, -E: Kind(a), -A: Kind(b)> is Kind(a <&> b):
  Fail{E}
  Done{A}
type List<a, -A: Kind(a)> is Kind(a):
  Nil{}
  Con{A, List<a, A>}
type Word.Nil is Data:
  WNil{}
opaque U32 is Data
opaque F32 is Data
type Char is Data:
  Chr{U32}
type String is Data:
  SNil{}
  SCon{Char, String}
opaque Array<-T: Kind(&1)> is Type
type Image is Data:
  Pix{U32}
  Qua{Image, Image, Image, Image}
type Event is Data:
  Key{U32, Bool}
  Mouse{U32, U32, U32, Bool}
  Move{U32, U32}
  Look{F32, F32}
  Scroll{U32, U32, F32, F32}
  Close{}
type Map<a, -V: Kind(a)> is Kind(a):
  MTip{}
  MLeaf{String, V}
  MNode{Nat, Map<a, V>, Map<a, V>}
type IO.OP<-R: Kind(&1)> is Type:
  Emit{R}
  Halt{U32, String}
type App<-S: Kind(&1)> is Type:
  App{S -> S & Image, List<Event> -> S -> IO(Maybe<S>)}
opaque IO(-A: Kind(&1)) is Type
def Pair.fst(-A: Kind(&1), -B: Kind(&1), x0: A & B) -> A
def Pair.snd(-A: Kind(&1), -B: Kind(&1), x0: A & B) -> B
def IO.pure(-A: Kind(&1), x0: A) -> IO(A)
def IO.bind(-A: Kind(&1), -B: Kind(&1), x0: IO(A), x1: A -> IO(B)) -> IO(B)
def Empty.absurd(-A: Kind(&1), x0: Empty) -> A
def Bool.not(x0: Bool) -> Bool
def Bool.and(x0: Bool, x1: Bool) -> Bool
def Bool.or(x0: Bool, x1: Bool) -> Bool
def Bool.xor(x0: Bool, x1: Bool) -> Bool
def Bool.cmp(x0: Bool, x1: Bool) -> Cmp
def Bool.pick(-A: Kind(&1), x0: Bool, x1: A, x2: A) -> A
def Bool.to_u32(x0: Bool) -> U32
def Cmp.is_lt(x0: Cmp) -> Bool
def Cmp.is_eq(x0: Cmp) -> Bool
def Cmp.is_gt(x0: Cmp) -> Bool
def Cmp.is_le(x0: Cmp) -> Bool
def Cmp.is_ge(x0: Cmp) -> Bool
def Nat.double(x0: Nat) -> Nat
def Nat.add(x0: Nat, x1: Nat) -> Nat
def Nat.sub(x0: Nat, x1: Nat) -> Nat
def Nat.mul(x0: Nat, +x1: Nat) -> Nat
def Nat.divmod(x0: Nat, x1: Nat) -> Nat & Nat
def Nat.cmp(x0: Nat, x1: Nat) -> Cmp
def Nat.is_lt(x0: Nat, x1: Nat) -> Bool
def Nat.is_eq(x0: Nat, x1: Nat) -> Bool
def Nat.is_ne(x0: Nat, x1: Nat) -> Bool
def Nat.is_le(x0: Nat, x1: Nat) -> Bool
def Nat.is_gt(x0: Nat, x1: Nat) -> Bool
def Nat.is_ge(x0: Nat, x1: Nat) -> Bool
def Nat.min(+x0: Nat, +x1: Nat) -> Nat
def Nat.max(+x0: Nat, +x1: Nat) -> Nat
def Nat.div(x0: Nat, x1: Nat) -> Nat
def Nat.mod(x0: Nat, x1: Nat) -> Nat
def Nat.pow(+x0: Nat, x1: Nat) -> Nat
def Maybe.pure(a, -A: Kind(a), x0: A) -> Maybe<a, A>
def Maybe.bind(a, -A: Kind(a), -B: Kind(a), x0: Maybe<a, A>, x1: A -> Maybe<a, B>) -> Maybe<a, B>
def Maybe.default(a, -A: Kind(a), x0: Maybe<a, A>, x1: A) -> A
def Maybe.is_some(a, -A: Kind(a), x0: Maybe<a, A>) -> Bool
def Maybe.is_none(a, -A: Kind(a), x0: Maybe<a, A>) -> Bool
def Maybe.map(a, -A: Kind(a), -B: Kind(a), x0: A -> B, x1: Maybe<a, A>) -> Maybe<a, B>
def Maybe.or(a, -A: Kind(a), x0: Maybe<a, A>, x1: Maybe<a, A>) -> Maybe<a, A>
def Result.pure(a, b, -E: Kind(a), -A: Kind(b), x0: A) -> Result<a, b, E, A>
def Result.bind(a, b, -E: Kind(a), -A: Kind(b), -B: Kind(b), x0: Result<a, b, E, A>, x1: A -> Result<a, b, E, B>) -> Result<a, b, E, B>
def Result.default(a, b, -E: Kind(a), -A: Kind(b), x0: Result<a, b, E, A>, x1: A) -> A
def Result.is_done(a, b, -E: Kind(a), -A: Kind(b), x0: Result<a, b, E, A>) -> Bool
def Result.is_fail(a, b, -E: Kind(a), -A: Kind(b), x0: Result<a, b, E, A>) -> Bool
def Result.map(a, b, -E: Kind(a), -A: Kind(b), -B: Kind(b), x0: A -> B, x1: Result<a, b, E, A>) -> Result<a, b, E, B>
def List.map(~A: Kind(&1), ~B: Kind(&1), ~x0: A -> B, x1: List<A>) -> List<B>
def List.length(a, -A: Kind(a), x0: List<a, A>) -> Nat
def List.append(a, -A: Kind(a), x0: List<a, A>, x1: List<a, A>) -> List<a, A>
def List.concat(a, -A: Kind(a), x0: List<a, List<a, A>>) -> List<a, A>
def List.reverse(a, -A: Kind(a), x0: List<a, A>) -> List<a, A>
def List.is_empty(a, -A: Kind(a), x0: List<a, A>) -> Bool
def List.head(a, -A: Kind(a), x0: List<a, A>) -> Maybe<a, A>
def List.tail(a, -A: Kind(a), x0: List<a, A>) -> List<a, A>
def List.last(a, -A: Kind(a), x0: List<a, A>) -> Maybe<a, A>
def List.get(a, -A: Kind(a), x0: List<a, A>, x1: Nat) -> Maybe<a, A>
def List.set(a, -A: Kind(a), x0: List<a, A>, x1: Nat, x2: A) -> List<a, A>
def List.take(a, -A: Kind(a), x0: List<a, A>, x1: Nat) -> List<a, A>
def List.drop(a, -A: Kind(a), x0: List<a, A>, x1: Nat) -> List<a, A>
def List.zip(a, -A: Kind(a), b, -B: Kind(b), x0: List<a, A>, x1: List<b, B>) -> List<(A & B)>
def List.range(x0: Nat) -> List<&2, Nat>
def List.replicate(-A: Kind(&2), x0: Nat, +x1: A) -> List<&2, A>
def List.filter(~A: Kind(&2), ~x0: A -> Bool, x1: List<&2, A>) -> List<&2, A>
def List.foldl(~a: Quant, ~A: Kind(a), ~B: Kind(&1), ~x0: B -> A -> B, x1: List<a, A>, x2: B) -> B
def List.foldr(~a: Quant, ~A: Kind(a), ~B: Kind(&1), ~x0: A -> B -> B, x1: List<a, A>, x2: B) -> B
def List.any(~a: Quant, ~A: Kind(a), ~x0: A -> Bool, x1: List<a, A>) -> Bool
def List.all(~a: Quant, ~A: Kind(a), ~x0: A -> Bool, x1: List<a, A>) -> Bool
def List.find(~A: Kind(&2), ~x0: A -> Bool, x1: List<&2, A>) -> Maybe<&2, A>
def List.contains(~A: Kind(&2), ~x0: A -> A -> Bool, x1: List<&2, A>, +x2: A) -> Bool
def List.sort(~A: Kind(&2), ~x0: A -> A -> Bool, +x1: List<&2, A>) -> List<&2, A>
def List.for_each(~a: Quant, ~A: Kind(a), ~x0: A -> IO(Unit), x1: List<a, A>) -> IO(Unit)
def U32.inc(x0: U32) -> U32
def U32.add(x0: U32, x1: U32) -> U32
def U32.sub(x0: U32, x1: U32) -> U32
def U32.mul(x0: U32, x1: U32) -> U32
def U32.not(x0: U32) -> U32
def U32.and(x0: U32, x1: U32) -> U32
def U32.or(x0: U32, x1: U32) -> U32
def U32.xor(x0: U32, x1: U32) -> U32
def U32.shl(x0: U32) -> U32
def U32.shr(x0: U32) -> U32
def U32.shln(x0: U32, x1: Nat) -> U32
def U32.shrn(x0: U32, x1: Nat) -> U32
def U32.cmp(x0: U32, x1: U32) -> Cmp
def U32.is_eq(x0: U32, x1: U32) -> Bool
def U32.is_ne(x0: U32, x1: U32) -> Bool
def U32.is_lt(x0: U32, x1: U32) -> Bool
def U32.is_le(x0: U32, x1: U32) -> Bool
def U32.is_gt(x0: U32, x1: U32) -> Bool
def U32.is_ge(x0: U32, x1: U32) -> Bool
def U32.is_zero(x0: U32) -> Bool
def U32.to_nat(x0: U32) -> Nat
def U32.from_nat(x0: Nat) -> U32
def U32.log2(+x0: U32) -> Nat
def U32.div(x0: U32, +x1: U32) -> U32
def U32.mod(x0: U32, +x1: U32) -> U32
def U32.min(+x0: U32, +x1: U32) -> U32
def U32.max(+x0: U32, +x1: U32) -> U32
def U32.clamp(x0: U32, x1: U32, x2: U32) -> U32
def U32.pow(+x0: U32, x1: Nat) -> U32
def U32.is_even(x0: U32) -> Bool
def U32.to_f32(x0: U32) -> F32 # stuck
def F32.to_u32(x0: F32) -> U32 # stuck
def F32.add(x0: F32, x1: F32) -> F32 # stuck
def F32.sub(x0: F32, x1: F32) -> F32 # stuck
def F32.mul(x0: F32, x1: F32) -> F32 # stuck
def F32.div(x0: F32, x1: F32) -> F32 # stuck
def F32.mod(x0: F32, x1: F32) -> F32 # stuck
def F32.pow(x0: F32, x1: F32) -> F32 # stuck
def F32.atan2(x0: F32, x1: F32) -> F32 # stuck
def F32.neg(x0: F32) -> F32 # stuck
def F32.abs(x0: F32) -> F32 # stuck
def F32.sqrt(x0: F32) -> F32 # stuck
def F32.exp(x0: F32) -> F32 # stuck
def F32.log(x0: F32) -> F32 # stuck
def F32.log2(x0: F32) -> F32 # stuck
def F32.log10(x0: F32) -> F32 # stuck
def F32.sin(x0: F32) -> F32 # stuck
def F32.cos(x0: F32) -> F32 # stuck
def F32.tan(x0: F32) -> F32 # stuck
def F32.asin(x0: F32) -> F32 # stuck
def F32.acos(x0: F32) -> F32 # stuck
def F32.atan(x0: F32) -> F32 # stuck
def F32.sinh(x0: F32) -> F32 # stuck
def F32.cosh(x0: F32) -> F32 # stuck
def F32.tanh(x0: F32) -> F32 # stuck
def F32.floor(x0: F32) -> F32 # stuck
def F32.ceil(x0: F32) -> F32 # stuck
def F32.trunc(x0: F32) -> F32 # stuck
def F32.is_eq(x0: F32, x1: F32) -> Bool # stuck
def F32.is_ne(x0: F32, x1: F32) -> Bool # stuck
def F32.is_lt(x0: F32, x1: F32) -> Bool # stuck
def F32.is_le(x0: F32, x1: F32) -> Bool # stuck
def F32.is_gt(x0: F32, x1: F32) -> Bool # stuck
def F32.is_ge(x0: F32, x1: F32) -> Bool # stuck
def F32.show(+x0: F32) -> String # stuck
def F32.bits(x0: F32) -> U32 # stuck
def F32.read(x0: String) -> Maybe<&2, F32> # stuck
def F32.min(+x0: F32, +x1: F32) -> F32 # stuck
def F32.max(+x0: F32, +x1: F32) -> F32 # stuck
def F32.clamp(x0: F32, x1: F32, x2: F32) -> F32 # stuck
def F32.lerp(+x0: F32, x1: F32, x2: F32) -> F32 # stuck
def F32.square(+x0: F32) -> F32 # stuck
def F32.hypot(+x0: F32, +x1: F32) -> F32 # stuck
def F32.round(x0: F32) -> F32 # stuck
def F32.from_nat(x0: Nat) -> F32 # stuck
def F32.to_nat(x0: F32) -> Nat # stuck
def Char.cmp(x0: Char, x1: Char) -> (Char & Char) & Cmp
def Char.to_u32(x0: Char) -> U32
def Char.from_u32(x0: U32) -> Char
def Char.is_eq(x0: Char, x1: Char) -> Bool
def Char.is_digit(x0: Char) -> Bool
def Char.is_upper(x0: Char) -> Bool
def Char.is_lower(x0: Char) -> Bool
def Char.is_alpha(+x0: Char) -> Bool
def Char.is_space(x0: Char) -> Bool
def Char.to_upper(+x0: Char) -> Char
def Char.to_lower(+x0: Char) -> Char
def String.append(x0: String, x1: String) -> String
def String.cmp(x0: String, x1: String) -> (String & String) & Cmp
def String.eq(x0: String, x1: String) -> Bool
def String.length(x0: String) -> Nat
def String.is_empty(x0: String) -> Bool
def String.reverse(x0: String) -> String
def String.order(x0: String, x1: String) -> Cmp
def String.is_lt(x0: String, x1: String) -> Bool
def String.is_le(x0: String, x1: String) -> Bool
def String.is_gt(x0: String, x1: String) -> Bool
def String.is_ge(x0: String, x1: String) -> Bool
def String.starts_with(x0: String, x1: String) -> Bool
def String.ends_with(x0: String, x1: String) -> Bool
def String.contains(+x0: String, +x1: String) -> Bool
def String.take(x0: String, x1: Nat) -> String
def String.drop(x0: String, x1: Nat) -> String
def String.get(x0: String, x1: Nat) -> Maybe<&2, Char>
def String.to_list(x0: String) -> List<&2, Char>
def String.from_list(x0: List<&2, Char>) -> String
def String.concat(x0: List<&2, String>) -> String
def String.join(x0: List<&2, String>, +x1: String) -> String
def String.split(x0: String, +x1: Char) -> List<&2, String>
def String.lines(x0: String) -> List<&2, String>
def String.repeat(+x0: String, x1: Nat) -> String
def String.to_upper(x0: String) -> String
def String.to_lower(x0: String) -> String
def String.trim_start(x0: String) -> String
def String.trim_end(x0: String) -> String
def String.trim(x0: String) -> String
def Nat.show(x0: Nat) -> String
def Nat.read(x0: String) -> Maybe<&2, Nat>
def U32.show(x0: U32) -> String
def U32.read(x0: String) -> Maybe<&2, U32>
def Bool.show(x0: Bool) -> String
def Char.show(x0: Char) -> String
def Maybe.show(~a: Quant, ~A: Kind(a), ~x0: A -> String, x1: Maybe<a, A>) -> String
def List.show(~a: Quant, ~A: Kind(a), ~x0: A -> String, x1: List<a, A>) -> String
def Array.size(-T: Kind(&1), x0: Array<T>) -> Array<T> & U32
def Array.swap(-T: Kind(&1), x0: Array<T>, +x1: U32, x2: T) -> Array<T> & T
def Array.clone(-T: Kind(&2), x0: Array<T>) -> Array<T> & Array<T>
def Array.fork(-T: Kind(&1), +x0: Array<T>) -> Array<T> & Array<T>
def Array.join(-T: Kind(&1), x0: Array<T>, x1: Array<T>) -> Array<T>
def Array.new(-T: Kind(&2), +x0: Nat, +x1: T) -> Array<T>
def Array.set(-T: Kind(&1), x0: Array<T>, x1: U32, x2: T) -> Array<T>
def Array.get(-T: Kind(&2), x0: Array<T>, +x1: U32) -> Array<T> & T
def Array.to_list(~T: Kind(&1), x0: Array<T>) -> List<T>
def Array.map(~T: Kind(&2), ~U: Kind(&2), ~x0: T -> U, x1: Array<T>) -> Array<U>
def Map.new(a, -V: Kind(a)) -> Map<a, V>
def Map.set(a, -V: Kind(a), x0: Map<a, V>, x1: String, x2: V) -> Map<a, V>
def Map.has(a, -V: Kind(a), x0: Map<a, V>, x1: String) -> Map<a, V> & Bool
def Map.get(-V: Kind(&2), x0: V, x1: Map<&2, V>, x2: String) -> Map<&2, V> & V
def Map.pop(a, -V: Kind(a), x0: Map<a, V>, x1: String) -> Map<a, V> & Maybe<a, V>
def Map.del(a, -V: Kind(a), x0: Map<a, V>, x1: String) -> Map<a, V>
def Map.keys(a, -V: Kind(a), x0: Map<a, V>) -> List<&2, String>
def Map.union(a, -V: Kind(a), x0: Map<a, V>, x1: Map<a, V>) -> Map<a, V>
def Map.size(a, -V: Kind(a), x0: Map<a, V>) -> Nat
def Map.values(a, -V: Kind(a), x0: Map<a, V>) -> List<a, V>
def Set.new() -> Map<&2, Unit>
def Set.add(x0: Map<&2, Unit>, x1: String) -> Map<&2, Unit>
def Set.has(x0: Map<&2, Unit>, x1: String) -> Map<&2, Unit> & Bool
def Set.del(x0: Map<&2, Unit>, x1: String) -> Map<&2, Unit>
def Set.size(x0: Map<&2, Unit>) -> Nat
def Set.to_list(x0: Map<&2, Unit>) -> List<&2, String>
def Set.from_list(x0: List<&2, String>) -> Map<&2, Unit>
`;

const BASE_ADTS = new Map<string, Adt>();
const BASE_DEFS: DefR[] = [];
const BASE_BY_HEAD = new Map<string, DefR[]>();
// IO_OPS : the datatypes IO's own definition runs on: no runtime prints one
const IO_OPS = new Set(["IO.OP"]);

// OPS : the parser's operator table: a method (".add", framed by its
// family: (a + b : U32) is U32.add) or a fixed name to its symbol
const OPS = new Map<string, string>([
  [".is_lt", "<"], [".is_le", "<="], [".is_gt", ">"], [".is_ge", ">="], [".or", ".|."], [".xor", ".^."], [".and", ".&."],
  [".shln", "<<"], [".shrn", ">>"], [".add", "+"], [".sub", "-"], [".mul", "*"], [".div", "/"], [".mod", "%"],
  ["Bool.or", "||"], ["Bool.and", "&&"], ["Con", "<>"], ["String.append", "++"],
]);

function bt(name: string): AdtT {
  const a = BASE_ADTS.get(name);
  if (a === undefined) {
    throw new Error("Base has no type " + name);
  }
  return inst(a);
}

function t_list(q: QT, el: T): AdtT {
  return inst(BASE_ADTS.get("List") as Adt, [q], [el]);
}

// Scope : the names a type in the table may mention: quantity and type
// parameters
type Scope = { qs: Set<string>; ts: Map<string, QT> };

// ty_parse : a type of the table's syntax — Name, Name<..> (the Fill sugar:
// a missing quantity block is &1), Name(..), A & B, A -> B, @-x: A -> B,
// (A) — at the scope's parameters and the declared datatypes
function ty_parse(src: string, sc: Scope): T {
  const toks = src.match(/&\d|->|=>|[A-Za-z_][\w.]*|\S/g) ?? [];
  let i = 0;
  const eat = (t: string): void => {
    if (toks[i++] !== t) {
      throw new Error("base table: expected " + t + " in " + src);
    }
  };
  const q_parse = (): QT => {
    const t = toks[i++];
    const lit: QT | null = /^&\d$/.test(t) ? [Q0, Q1, Q2][Number(t[1])] : sc.qs.has(t) ? { k: "qv", n: t } : null;
    if (lit === null) {
      throw new Error("base table: a quantity, got " + t + " in " + src);
    }
    return lit;
  };
  const atom = (): T => {
    const t = toks[i++];
    if (t === "(") {
      const x = arrow();
      eat(")");
      return x;
    }
    if (t === "@") {
      const q: BQ = toks[i] === "-" ? 0 : toks[i] === "+" ? 2 : 1;
      i += q === 1 ? 0 : 1;
      i++;
      eat(":");
      const dom = amp();
      eat("->");
      return { k: "fun", q, dom, cod: arrow() };
    }
    const tv = sc.ts.get(t);
    if (tv !== undefined) {
      return { k: "tvar", n: t, q: tv };
    }
    const a = BASE_ADTS.get(t);
    if (a === undefined) {
      throw new Error("base table: unknown type " + t + " in " + src);
    }
    const close = toks[i] === "<" ? ">" : toks[i] === "(" && a.paren ? ")" : null;
    if (close === null) {
      return inst(a);
    }
    i++;
    const qs: QT[] = [];
    const ts: T[] = [];
    const fill = (): boolean => {
      // a quantity block is there when its first item is a quantity
      const t0 = toks[i];
      return a.qps.length > 0 && (/^&\d$/.test(t0) || sc.qs.has(t0));
    };
    const explicit = fill();
    for (let k = 0; toks[i] !== close; k++) {
      if (k > 0) {
        eat(",");
      }
      if (explicit && qs.length < a.qps.length) {
        qs.push(q_parse());
      } else {
        ts.push(arrow());
      }
    }
    i++;
    return inst(a, explicit ? qs : a.qps.map(() => Q1), ts);
  };
  const amp = (): T => {
    const a = atom();
    if (toks[i] === "&") {
      i++;
      return { k: "sig", x: null, a, b: amp(), q: 1, spell: "amp" };
    }
    return a;
  };
  const arrow = (): T => {
    const d = amp();
    if (toks[i] === "->") {
      i++;
      return { k: "fun", q: 1, dom: d, cod: arrow() };
    }
    return d;
  };
  const t = arrow();
  if (i !== toks.length) {
    throw new Error("base table: trailing " + toks.slice(i).join(" ") + " in " + src);
  }
  return t;
}

// split_top : the items of a comma list at bracket depth zero
function split_top(src: string): string[] {
  const out: string[] = [];
  let depth = 0;
  let cur = "";
  for (let i = 0; i < src.length; i++) {
    const ch = src[i];
    if (ch === "<" || ch === "(" || ch === "{") {
      depth++;
    } else if ((ch === ">" && src[i - 1] !== "-" && src[i - 1] !== "=") || ch === ")" || ch === "}") {
      depth--;
    }
    if (ch === "," && depth === 0) {
      out.push(cur.trim());
      cur = "";
    } else {
      cur += ch;
    }
  }
  return cur.trim() === "" ? out : [...out, cur.trim()];
}

// kind_parse : Data, Type or Kind(q)
function kind_parse(src: string, sc: Scope): QT {
  if (src === "Data") {
    return Q2;
  }
  if (src === "Type") {
    return Q1;
  }
  const m = /^Kind\((.*)\)$/.exec(src);
  const parts = (m?.[1] ?? "").split("<&>").map((x) => x.trim());
  const one = (x: string): QT => /^&\d$/.test(x) ? [Q0, Q1, Q2][Number(x[1])] : sc.qs.has(x) ? { k: "qv", n: x } : Q1;
  return parts.length === 2 ? { k: "qm", a: one(parts[0]), b: one(parts[1]) } : one(parts[0]);
}

// base_load : BASE_TABLE read: the datatypes' headers first (a field may
// name a later one), then their rows and the defs
function base_load(): void {
  const blocks = BASE_TABLE.trim().split(/\n(?=\S)/);
  const heads: Array<[Adt, Scope, string[]]> = [];
  for (const b of blocks.filter((x) => /^(type|opaque) /.test(x))) {
    const [head, ...rows] = b.split("\n");
    const m = /^(type|opaque) ([\w.]+)(?:([<(])(.*)[>)])? is (\S+)/.exec(head) as RegExpExecArray;
    const a: Adt = { id: IDS++, name: m[2], qps: [], tps: [], ips: [], kind: Q1, ctors: m[1] === "type" ? [] : null, paren: m[3] === "(", base: true, rec: false };
    const sc: Scope = { qs: new Set(), ts: new Map() };
    for (const p of split_top(m[4] ?? "")) {
      const pm = /^-(\w+): (.*)$/.exec(p);
      if (pm === null) {
        a.qps.push(p);
        sc.qs.add(p);
      } else {
        const q = kind_parse(pm[2], sc);
        a.tps.push({ n: pm[1], q });
        sc.ts.set(pm[1], q);
      }
    }
    a.kind = kind_parse(m[5].replace(/:$/, ""), sc);
    BASE_ADTS.set(a.name, a);
    heads.push([a, sc, rows]);
  }
  for (const [a, sc, rows] of heads) {
    for (const row of rows) {
      const rm = /^\s+([\w.]+)\{(.*)\}$/.exec(row) as RegExpExecArray;
      const fields = split_top(rm[2]).map((f): Field => {
        const q: BQ = f[0] === "-" ? 0 : f[0] === "+" ? 2 : 1;
        return { q, t: ty_parse(q === 1 ? f : f.slice(1), sc) };
      });
      (a.ctors as Ctor[]).push({ name: rm[1], fields });
    }
    const self = adt_self(a);
    a.rec = (a.ctors ?? []).some((ct) => ct.fields.some((f) => ty_eq(f.t, self)));
  }
  for (const b of blocks.filter((x) => x.startsWith("def "))) {
    const m = /^def ([\w.]+)\((.*)\) -> (.*?)( # stuck)?$/.exec(b) as RegExpExecArray;
    const r: DefR = { name: m[1], qps: [], tps: [], hdr: [], ps: [], ret: bt("Unit"), tm: 0, base: true, stuck: m[4] !== undefined };
    const sc: Scope = { qs: new Set(), ts: new Map() };
    for (const p of split_top(m[2])) {
      r.tm += p.startsWith("~") ? 1 : 0;
      const pm = /^[~+-]?(\w+)(?:: (.*))?$/.exec(p) as RegExpExecArray;
      if (pm[2] === undefined || pm[2] === "Quant") {
        r.qps.push(pm[1]);
        r.hdr.push(pm[1]);
        sc.qs.add(pm[1]);
      } else if (/^(Kind\(.*\)|Type|Data)$/.test(pm[2])) {
        const q = kind_parse(pm[2], sc);
        r.tps.push({ n: pm[1], q });
        r.hdr.push(pm[1]);
        sc.ts.set(pm[1], q);
      } else {
        r.ps.push({ q: p[0] === "-" ? 0 : p[0] === "+" ? 2 : 1, t: ty_parse(pm[2], sc) });
      }
    }
    r.ret = ty_parse(m[3], sc);
    // a Nat argument is small, and so is a word that becomes a Nat: the
    // interpreter's Nat is unary
    const toNat = /\bNat\b/.test(ty_key(r.ret));
    for (const p of r.ps) {
      p.mask = is_t(p.t, "Nat") ? 6 : toNat && is_t(p.t, "U32") ? 64 : undefined;
    }
    BASE_DEFS.push(r);
    const h = head(r.ret);
    BASE_BY_HEAD.set(h, [...BASE_BY_HEAD.get(h) ?? [], r]);
  }
}

// Names
// -----
// Every name the generator writes draws from one identifier distribution:
// fresh strings of every length, words of Base's source and of the JS host
// (split at camel/snake/digit boundaries and recombined, so no complete
// spelling is privileged), and runs of one character. A top-level name
// keeps a uid suffix in a batch, so independently generated members cannot
// collide; a free-names seed draws it like any identifier, near the names
// already declared at times (a dotted extension, an affix, a word of Base).

// text_decls : what a source text declares: defs, laws, types and the
// constructors of a type's rows
function text_decls(text: string): Array<{ kind: "def" | "law" | "type" | "ctor"; name: string }> {
  const out: Array<{ kind: "def" | "law" | "type" | "ctor"; name: string }> = [];
  let rows = false;
  for (const line of text.split("\n")) {
    const top = /^(def|law|type)\s+([A-Za-z_][\w.]*)/.exec(line);
    const row = rows && top === null ? /^ +([A-Za-z_][\w.]*)\{/.exec(line) : null;
    rows = top !== null ? top[1] === "type" : rows && /^ /.test(line);
    if (top !== null) {
      out.push({ kind: top[1] as "def" | "law" | "type", name: top[2] });
    } else if (row !== null) {
      out.push({ kind: "ctor", name: row[1] });
    }
  }
  return out;
}

// text_names : the names a source text declares with every dotted prefix,
// since a binder of that name would shadow them
function text_names(text: string): string[] {
  return text_decls(text).flatMap(({ name }) => name.split(".").map((_, i, ps) => ps.slice(0, i + 1).join(".")));
}

const KEYWORDS = new Set(["def", "type", "law", "match", "case", "do", "return", "for", "exs", "where", "is", "import", "Type", "Data", "Kind", "Quant"]);
const BASE_SOURCE = fs.readFileSync(BASE_PATH, "utf8");
const BASE_DECL_NAMES = text_names(BASE_SOURCE);
const CORE_NAMES = new Set([...KEYWORDS, "_", "main"]);
const BASE_NAMES = new Set([...CORE_NAMES, ...BASE_DECL_NAMES]);
// the shape of every name the generator mints at top level (a stem, a uid,
// a constructor's letter), in any member of a batch
const MINTED = /^[A-Za-z]+\d+[a-z]?$/;
const NAME_HEAD = [..."ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_"];
const NAME_BODY = [...NAME_HEAD, ..."0123456789"];
const NAME_WORDS = [...new Set([
  ...BASE_SOURCE.matchAll(/[A-Za-z_][A-Za-z_0-9]*/g),
].map((m) => m[0]).concat([Object.prototype, Function.prototype, Array.prototype, Number.prototype, String.prototype]
  .flatMap((obj) => Object.getOwnPropertyNames(obj))))]
  .filter((name) => /^[A-Za-z_]\w*$/.test(name) && !KEYWORDS.has(name));
const DECL_SET = new Set([...NAME_WORDS, ...BASE_DECL_NAMES]);
const DECL_WORDS = [...DECL_SET].filter((w) => w.length > 1);
const NAME_FRAGMENTS = [...new Set(NAME_WORDS.flatMap((name) => name
  .replace(/([a-z0-9])([A-Z])/g, "$1 $2")
  .replace(/([A-Z]+)([A-Z][a-z])/g, "$1 $2")
  .split(/[^A-Za-z]+/)
  .filter((part) => part.length > 0 && part.length <= 24)
  .map((part) => part.toLowerCase())))]
  .filter((part) => !KEYWORDS.has(part));

// identifier : one draw of the identifier distribution (min: its length)
function identifier(g: Gen, min = 1): string {
  const name = g.wpick<() => string>([
    [42, () => g.pick(NAME_HEAD) + Array.from({ length: g.size(min - 1, 2, 256) }, () => g.pick(NAME_BODY)).join("")],
    [25, () => {
      const w = g.pick(NAME_WORDS);
      return g.chance(0.18) ? g.pick([w.toLowerCase(), w.toUpperCase(), "_" + w, w + "_", w + String(g.int(100))]) : w;
    }],
    [23, () => {
      const parts = Array.from({ length: g.size(1, 1, 6) }, () => g.pick(NAME_FRAGMENTS));
      const cap = (p: string): string => p[0].toUpperCase() + p.slice(1);
      const name = g.pick([parts.join(""), parts[0] + parts.slice(1).map(cap).join(""), parts.map(cap).join(""),
        parts.join("_"), parts.join("_").toUpperCase()]);
      return "_".repeat(g.chance(0.18) ? 1 + g.int(2) : 0) + name + "_".repeat(g.chance(0.12) ? 1 + g.int(2) : 0)
        + (g.chance(0.22) ? String(g.int(100)) : "");
    }],
    [10, () => {
      const ch = g.pick(NAME_HEAD);
      return ch + g.pick([ch, "_", g.pick(NAME_BODY)]).repeat(g.pick([1, 7, 15, 30, 31, 62, 63, 79, 126, 127, 254]));
    }],
  ])();
  return name.length < min ? name + g.pick(NAME_BODY).repeat(min - name.length) : name;
}

// Ctx
// ---
// One program's generator state (State: what the program accumulates —
// entries in dependency order, since the book refuses forward references,
// its datatypes, families and callable defs, the memo of minted helpers)
// carried with one RNG stream. sub(label) hands out a child Ctx on a split
// stream, indexed per label within the parent.

type State = {
  uid: number;
  base: boolean;
  free: boolean;
  names: Set<string>;
  decls: Set<string>;
  entries: string[];
  adts: Adt[];
  fams: Fam[];
  defs: DefR[];
  memo: Map<string, string>;
  // wip : the memo keys whose def is being drawn
  wip: Set<string>;
  // wips : the defs whose leaves are being drawn, innermost last
  wips: DefR[];
  mints: number;
  maxMints: number;
  feat: Record<string, number>;
  // pure : drawing the interp-visible side: no stuck call may flow in
  pure: boolean;
  // trans : the member computes a float transcendental
  trans: boolean;
  // surface : the chance per synthesis node of a surface wrapper
  surface: number;
  // tmpl : drawing a template's argument, which its instance substitutes
  // where it may head an application (no rewrite form: it does not infer)
  tmpl: boolean;
  // framed : an infix expression's text to its operator text and family,
  // so an operand of the same family may inherit the frame
  framed: Map<string, [string, string]>;
  steps: number;
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
}

function ctx_new(seed: bigint, uid0: number, p: Profile): Ctx {
  const g = new Gen(rng_mix64(seed));
  return new Ctx({
    uid: uid0, base: p.base, free: p.free, names: new Set(p.base ? BASE_NAMES : CORE_NAMES), decls: new Set(p.base ? BASE_DECL_NAMES : []),
    entries: [], adts: [], fams: [], defs: [], memo: new Map(), wip: new Set(), wips: [], mints: 0, maxMints: g.size(4, 8, 96),
    feat: {}, pure: true, trans: false, surface: p.surface, tmpl: false, framed: new Map(), steps: 0,
  }, g);
}

// decl_name : a fresh top-level name for a role (the stem names it in a
// batch: its uid keeps members apart)
function decl_name(c: Ctx, stem: string): string {
  for (;;) {
    const name = !c.s.free ? stem + String(c.uid()) : c.g.wpick<() => string>([
      [64, () => identifier(c.g, 2)],
      [18, () => c.g.pick(DECL_WORDS)],
      [8, () => {
        const ps = [...c.s.names].filter((n) => /^[A-Za-z_]\w*$/.test(n) && !CORE_NAMES.has(n));
        return ps.length === 0 ? identifier(c.g, 2) : c.g.pick(ps) + "." + identifier(c.g, 2);
      }],
      [c.s.decls.size > 0 ? 18 : 0, () => {
        c.feat("name-affix");
        const parts = c.g.pick([...c.s.decls]).split(".");
        const leaf = parts.pop() as string;
        const affix = identifier(c.g, 2);
        return [...parts, c.g.chance(0.5) ? affix + leaf : leaf + affix].join(".");
      }],
    ])();
    // a name of a dotted prefix nothing declares is refused, and the shape
    // of the generator's uid names is theirs unless the word is one the
    // implementation spells
    const dot = name.lastIndexOf(".");
    const ok = dot < 0 || c.s.names.has(name.slice(0, name.indexOf(".")));
    if (ok && !c.s.names.has(name) && !CORE_NAMES.has(name) && (!c.s.free || !MINTED.test(name.slice(dot + 1)) || DECL_SET.has(name))) {
      c.s.names.add(name);
      c.s.decls.add(name);
      if (c.s.free) {
        c.feat("free-name");
      }
      return name;
    }
  }
}

// Env
// ---
// A binder in scope. q "lone": consumed at most once (env_take flips it to
// dead); "many": free (a + binder, only at concretely-Data types); "dead":
// gone. Dropping a lone binder is fine (the system is affine). dec: a
// sub-field the self-call may descend on; of: the parameter a variable row
// re-binds (passed through unchanged, it still counts as it).

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

function env_live(env: V[], pred: (t: T) => boolean = () => true): V[] {
  return env.filter((v) => v.q !== "dead" && pred(v.ty));
}

// env_bind : the scope under new binders; a binder in scope with the same
// name is shadowed, so it is dead there (an erased binder shadows too)
function env_bind(env: V[], names: string[], vs: V[] = []): V[] {
  return env.map((v) => names.includes(v.name) ? { ...v, q: "dead" as const } : v).concat(vs);
}

// bind_name : a value binder's name: any identifier that names nothing
// else (not `_`, a keyword, an occupied top-level name, nor of the shape of
// a minted top-level name, which another member of a batch may hold), or a
// fifth of the time a binder in scope, which the new one then shadows —
// unless a live value's type mentions it. taken: the names bound beside it
// (one line's binders are distinct).
function bind_name(c: Ctx, env: V[], taken: string[] = []): string {
  const live = env_live(env);
  const kept = new Set(live.filter((v) => live.some((w) => w !== v && ty_mentions(w.ty, v.name))).map((v) => v.name));
  const shadow = live.filter((v) => !taken.includes(v.name) && !kept.has(v.name));
  if (shadow.length > 0 && c.g.chance(0.2)) {
    c.feat("shadow");
    return c.g.pick(shadow).name;
  }
  for (;;) {
    const name = identifier(c.g);
    if (!c.s.names.has(name) && !MINTED.test(name) && !taken.includes(name) && !kept.has(name)) {
      c.s.names.add(name);
      return name;
    }
  }
}

// bind_names : n distinct binders
function bind_names(c: Ctx, n: number, env: V[] = [], taken: string[] = []): string[] {
  const out: string[] = [];
  for (let i = 0; i < n; i++) {
    out.push(bind_name(c, env, [...taken, ...out]));
  }
  return out;
}

// helper : a def minted once per program under a key; body sees the fresh
// name and may mint what it depends on first. A key met again while its
// def is being drawn is a knot (the inner def would land first and call
// forward): it throws, and the production that asked falls back.
function helper(c: Ctx, key: string, stem: string, body: (c: Ctx, name: string) => string, after?: (name: string) => void): string {
  const got = c.s.memo.get(key);
  if (got !== undefined) {
    if (c.s.wip.has(key)) {
      throw new Error("helper knot: " + key);
    }
    return got;
  }
  const name = decl_name(c, stem);
  c.s.memo.set(key, name);
  c.s.wip.add(key);
  try {
    c.push(body(c.sub(stem), name));
  } catch (e) {
    c.s.memo.delete(key);
    throw e;
  } finally {
    c.s.wip.delete(key);
  }
  after?.(name);
  return name;
}

// the ! GPU mark a call may carry at a statement's head
function gpu_mark(c: Ctx, e: string): string {
  const m = /^[A-Za-z_][\w.]*(?=\()/.exec(e);
  if (m === null || !c.g.chance(0.25)) {
    return e;
  }
  c.feat("bang");
  return m[0] + "!" + e.slice(m[0].length);
}

// Literals
// --------
// The surface's literal forms, per type of Base: a production like any
// other at a goal of that type (the terms they abbreviate — Succ chains,
// SCon chains, Con chains, ALeaf trees — are the constructors and calls
// the synthesis also reaches).

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

function u32_lit(c: Ctx): string {
  return c.g.wpick<() => string>([
    [30, () => String(c.g.int(16))],
    [25, () => String(c.g.int(1000))],
    [15, () => String(c.g.int(4294967296))],
    [20, () => c.g.pick(["0", "4294967295", "2147483648", "65536"])],
  ])();
}

function f32_lit(c: Ctx): string {
  const s = String((1 + c.g.int(256)) / c.g.pick([4, 8, 16, 32]));
  return s.includes(".") ? s : s + ".0";
}

// Lit : a literal form of a type; ok: whether the instance has one
type Lit = { ok?: (t: AdtT) => boolean; f: (c: Ctx, t: AdtT, env: V[], fuel: number) => string };

const LITS: Record<string, Lit> = {
  U32: { f: (c) => u32_lit(c) },
  F32: { f: (c) => f32_lit(c) },
  Nat: { f: (c) => String(c.g.size(0, 6, c.s.pure ? 64 : 2400)) + "n" },
  Char: { f: (c) => "'" + str_char(c) + "'" },
  String: {
    f: (c) => {
      c.feat("string-lit");
      return str_lit(c, c.g.size(0, 5, c.s.pure ? 160 : 2000));
    },
  },
  // a list literal, a cons chain ending in one at times (a lambda head
  // would swallow the chain as its body)
  List: {
    f: (c, t, env, fuel) => {
      c.feat("list-lit");
      const n = fuel <= FLOOR ? 0 : c.g.size(0, 3, c.s.pure ? 60 : 1500);
      const els = split(c.g, fuel - 1, n).map((f) => syn(c, t.args[0], env, f));
      const heads = els.length > 0 && !els.some((e) => e.includes("=>")) && c.g.chance(0.3) ? 1 + c.g.int(Math.min(els.length, 3)) : 0;
      if (heads > 0) {
        c.feat("cons-lit");
      }
      const lit = "[" + els.slice(heads).join(", ") + "]";
      return heads === 0 ? lit : "(" + els.slice(0, heads).map((e) => e + " <> ").join("") + lit + ")";
    },
  },
  // an array by depth ([v : T^d]) or by a power-of-two slot count
  // ([v : T*n]); its fill value is Data
  Array: {
    ok: (t) => ty_data(t.args[0]),
    f: (c, t, env, fuel) => {
      c.feat("array-lit");
      const d = c.g.size(1, 1.5, c.s.pure ? 6 : 12);
      const v = syn(c, t.args[0], env_live(env).filter((w) => w.q === "many"), fuel - 1);
      return "[" + v + " : " + ty_grp(t.args[0]) + (c.g.chance(0.5) ? "^" + String(d) : "*" + String(2 ** d)) + "n]";
    },
  },
};

// Syn: types
// ----------
// syn_ty(c, fuel, need, sc, neg): a type-valued hole whose kind must fit
// Kind(need). sc is what the type may mention: the enclosing generic's type
// and quantity variables, and index terms (ivars) — imatch: the position is
// one a reader may match on (the top of a family's arm). neg: the type may
// be uninhabited (a family's arm, a pair's evidence), so propositions may
// appear.

type TyScope = { tvars: TvarInfo[]; qvars: string[]; ivars: IVar[]; imatch: boolean };
const NO_SCOPE: TyScope = { tvars: [], qvars: [], ivars: [], imatch: false };

function syn_ty(c: Ctx, fuel: number, need: QT, sc: TyScope = NO_SCOPE, neg = false): T {
  for (let i = 0; i < 3; i++) {
    const t = syn_ty0(c, fuel, need, sc, neg);
    if (neg || ty_inh(t)) {
      return t;
    }
  }
  if (c.s.base) {
    return bt("U32");
  }
  const own = c.s.adts.find((a) => a.qps.length + a.tps.length + a.ips.length === 0 && qt_fits(a.kind, need) && ty_inh(inst(a)));
  if (own === undefined) {
    throw new Error("no inhabited type in a no-Base context");
  }
  return inst(own);
}

// adt_pool : the datatypes a type may instantiate: the program's own and,
// with Base, Base's that can have a value
function adt_pool(c: Ctx): Adt[] {
  return c.s.base ? c.s.adts.concat(base_pool()) : c.s.adts;
}

let BASE_POOL: Adt[] | null = null;
function base_pool(): Adt[] {
  return BASE_POOL ??= [...BASE_ADTS.values()].filter((a) => a.ctors !== null || a.name in LITS || (BASE_BY_HEAD.get("a:" + a.name) ?? []).some((d) => d.effect !== true));
}

// eql_lit : {l == r : I} over an index type, agreeing sides or a clash
function eql_lit(c: Ctx, clash: boolean): EqlT {
  const t = c.g.pick(idx_pool(c));
  const ls = idx_lits(t);
  const l = c.g.pick(ls);
  const rs = ls.filter((x) => x !== l && (!is_t(t, "Nat") || l === "0n" || x === "0n"));
  return { k: "eql", t, l, r: clash && rs.length > 0 ? c.g.pick(rs) : l };
}

// idx_pool : the index types in scope (Nat, Base's and the program's enums)
function idx_pool(c: Ctx): AdtT[] {
  return adt_pool(c).map((a) => inst(a)).filter(idx_type);
}

function syn_ty0(c: Ctx, fuel: number, need: QT, sc: TyScope, neg: boolean): T {
  const needData = qt_known(need) === 2;
  // a Type (a tuple at &1, a function, a dependent pair) fits a slot of
  // kind &0 or &1 only
  const typ = qt_fits(Q1, need);
  const pick_qt = (): QT => sc.qvars.length > 0 && c.g.chance(0.4) ? { k: "qv", n: c.g.pick(sc.qvars) } : needData || c.g.chance(0.5) ? Q2 : Q1;
  const tfit = sc.tvars.filter((tv) => qt_fits(tv.q, need));
  const ffit = c.s.fams.filter((f) => qt_fits(f.kind, need) && (f.done || sc.ivars.some((iv) => iv.sub === true && ty_eq(iv.t, f.idx))));
  const adts = adt_pool(c).filter((a) => fuel > 0 || a.qps.length + a.tps.length + a.ips.length === 0);
  return c.g.wpick<() => T>([
    [tfit.length > 0 ? 18 : 0, () => {
      const tv = c.g.pick(tfit);
      return { k: "tvar", n: tv.n, q: tv.q };
    }],
    // an instantiated datatype: the quantity arguments, then the type
    // arguments at their substituted kinds; an index term reaches the
    // arguments of a non-recursive datatype at a matchable position (its
    // reader matches it inline)
    [adts.length > 0 ? 40 : 0, () => {
      for (let tries = 0; tries < 3; tries++) {
        const a = c.g.pick(adts);
        const qs = a.qps.map(pick_qt);
        const qm = new Map(a.qps.map((n, i) => [n, qs[i]]));
        if (!qt_fits(qt_sub(a.kind, qm), need)) {
          continue;
        }
        const open = sc.imatch && a.ctors !== null && !a.rec;
        const budget = split(c.g, fuel - 1, a.tps.length);
        const args = a.tps.map((tp, i) => syn_ty(c, budget[i], qt_sub(tp.q, qm), open ? { ...sc, imatch: false } : { ...sc, ivars: [], imatch: false }));
        const iargs = a.ips.map((ip) => idx_arg(c, ip.t, sc.imatch ? sc.ivars : []));
        // Either at &1, &1 may spell Or(A, B) or A | B
        const spell = a.base && a.name === "Either" && qs.every((q) => qt_known(q) === 1) && c.g.chance(0.4) ? c.g.pick(["or", "bar"] as const) : undefined;
        if (spell !== undefined) {
          c.feat("or");
        }
        return { k: "adt", a, qs, args, iargs, spell };
      }
      return c.s.base ? bt("U32") : syn_ty(c, 0, need, sc, neg);
    }],
    // a type some def of the registry answers in, instantiated (the pairs
    // Base's containers answer in, a Maybe of a read, ...)
    [c.s.base && fuel > 0 ? 10 : 0, () => {
      const d = c.g.pick(BASE_DEFS.filter((x) => x.effect !== true && !(c.s.pure && x.stuck === true)));
      const qm = new Map(d.qps.map((n): [string, QT] => [n, pick_qt()]));
      const m = new Map(d.tps.map((tp): [string, T] => [tp.n, syn_ty(c, fuel - 1, qt_sub(tp.q, qm), { ...sc, ivars: [], imatch: false })]));
      const t = ty_sub(d.ret, m, qm);
      c.feat("ret-type");
      return qt_fits(ty_quant(t), need) && !ty_open(t) ? t : bt("U32");
    }],
    // an applied family: a closed index, or an index term in scope
    [fuel > 0 && ffit.length > 0 ? 8 : 0, () => {
      const f = c.g.pick(ffit);
      c.feat("fam-use");
      const arg = f.done ? idx_arg(c, f.idx, sc.ivars) : c.g.pick(sc.ivars.filter((iv) => iv.sub === true && ty_eq(iv.t, f.idx))).n;
      return { k: "app", f, arg };
    }],
    // inside a family's arm: a datatype indexed by the arm's sub-index,
    // whose fields may hold the family at it (Word's idiom)
    [fuel > 0 && sc.ivars.length > 0 && sc.imatch ? 7 : 0, () => {
      const a = adt_new(c.sub("iadt"), sc.ivars, need);
      return inst(a, [], [], sc.ivars.map((iv) => iv.n));
    }],
    // a tuple (Base's Sigma)
    [c.s.base && fuel > 0 ? 8 : 0, () => {
      const q: 1 | 2 = !typ || c.g.chance(0.3) ? 2 : 1;
      const budget = split(c.g, fuel - 1, 2);
      const el = (i: number): T => syn_ty(c, budget[i], q === 2 ? Q2 : need, { ...sc, imatch: false });
      const spell = c.g.wpick<SigT["spell"]>([[7, "amp"], [2, "pair"], [1, "sigma"]]);
      if (spell === "pair") {
        c.feat("pair");
      }
      return { k: "sig", x: null, a: el(0), b: el(1), q, spell };
    }],
    // a dependent pair: a witness, mostly an index term, and evidence about
    // it, which may be a proposition
    [c.s.base && fuel > 0 && typ ? 3 : 0, () => {
      c.feat("sig");
      const x = bind_name(c, []);
      const idx = idx_pool(c);
      const a = c.g.chance(0.7) && idx.length > 0 ? c.g.pick(idx) : syn_ty(c, 0, Q2, { ...sc, ivars: [], imatch: false });
      const b = syn_ty(c, fuel - 1, Q0, idx_type(a) ? { ...sc, ivars: sc.ivars.concat([{ n: x, t: a }]) } : sc, true);
      return { k: "sig", x: idx_type(a) ? x : null, a, b, q: 1, spell: c.g.wpick<SigT["spell"]>([[5, "amp"], [3, "exists"], [2, "sigma"]]) };
    }],
    [fuel > 0 && typ ? 7 : 0, () => {
      const q = c.g.wpick<BQ>([[7, 1], [2, 0], [1, 2]]);
      const [fd, fc] = split(c.g, fuel - 1, 2);
      const dom = syn_ty(c, q === 2 ? 0 : fd, q === 2 ? Q2 : Q0, { ...sc, ivars: [], imatch: false });
      return { k: "fun", q, dom, cod: syn_ty(c, fc, Q0, { ...sc, imatch: false }) };
    }],
    // propositions, where the type may be uninhabited: Empty, an equality
    // of literals (agreeing or a clash), its negation
    [c.s.base && neg ? 6 : 0, () => {
      c.feat("empty");
      return bt("Empty");
    }],
    [c.s.base && neg ? 5 : 0, () => {
      const clash = c.g.chance(0.5);
      c.feat(clash ? "eql-clash" : "eql-lit");
      return eql_lit(c, clash);
    }],
    [c.s.base && neg && typ ? 3 : 0, () => {
      c.feat("eql-ne");
      return { k: "fun", q: 1, dom: eql_lit(c, c.g.chance(0.7)), cod: bt("Empty"), ne: c.g.chance(0.5) };
    }],
  ])();
}

// idx_lit : a closed literal of an index type; idx_arg : that, or an index
// term in scope of the type
function idx_lit(c: Ctx, t: T): string {
  return is_t(t, "Nat") ? String(c.g.int(4)) + "n" : c.g.pick(idx_lits(t));
}

function idx_arg(c: Ctx, t: T, ivars: IVar[]): string {
  const vs = ivars.filter((iv) => ty_eq(iv.t, t));
  return vs.length > 0 && c.g.chance(0.7) ? c.g.pick(vs).n : idx_lit(c, t);
}

// Datatypes
// ---------
// Flavors: "data" (is Data), "qpoly" (quantity parameters, is Kind(a) or
// Kind(a <&> b)), "type" (is Type: closures welcome). A field's type is
// drawn at the declared kind with the parameters in scope; constructor 0
// never recurs, self fields keep uniform recursion so folds descend. An
// indexed datatype (ips, inside a family's arm) is monomorphic over its
// index: its kind is the arm's, its fields may hold the family at it.

function adt_new(c: Ctx, ips: IVar[] = [], ikind: QT = Q2): Adt {
  const name = decl_name(c, "D");
  const flavor = ips.length > 0 ? (qt_known(ikind) === 2 ? "data" : "type")
    : !c.s.base && c.s.adts.length === 0 ? "data" : c.g.wpick<string>([[5, "data"], [4, "qpoly"], [2, "type"]]);
  const qps = flavor === "qpoly" ? bind_names(c, c.g.size(1, 0.5, 4)) : [];
  const tps: TvarInfo[] = bind_names(c, flavor === "qpoly" ? c.g.size(1, 1, 6) : flavor === "type" && ips.length === 0 ? c.g.size(0, 0.7, 4) : 0, [], qps)
    .map((n, i) => ({ n, q: qps.length > 0 ? { k: "qv", n: qps[i % qps.length] } : Q1 }));
  const meet = qps.length >= 2 && c.g.chance(0.6);
  if (meet) {
    c.feat("kind-meet");
  }
  const kind: QT = flavor === "data" ? Q2 : flavor === "type" ? Q1
    : meet ? { k: "qm", a: { k: "qv", n: qps[0] }, b: { k: "qv", n: qps[1] } } : { k: "qv", n: qps[0] };
  c.feat("adt-" + flavor);
  const a: Adt = { id: IDS++, name, qps, tps, ips, kind, ctors: [], paren: false, base: false, rec: false };
  const self = adt_self(a);
  const sc: TyScope = { tvars: tps, qvars: qps, ivars: ips, imatch: false };
  const nctors = c.g.size(1, 2, 32);
  for (let ci = 0; ci < nctors; ci++) {
    // the first datatype of an empty environment is the foundation of the
    // later ones: there is no field type to draw before it
    const nf = !c.s.base && c.s.adts.length === 0 ? 0 : c.g.size(0, 1.5, 16);
    const fields: Field[] = [];
    for (let f = 0; f < nf; f++) {
      if (c.g.chance(0.12)) {
        c.feat("erased-field");
        fields.push({ q: 0, t: syn_ty(c, c.g.size(0, 1, 12), Q0, sc) });
      } else if (ips.length === 0 && ci > 0 && c.g.chance(0.3)) {
        a.rec = true;
        fields.push({ q: 1, t: self });
      } else {
        // a live field's kind must fit Kind(G)
        const t = syn_ty(c, c.g.size(0, 1, 12), kind, sc);
        fields.push({ q: ty_data(t) && c.g.chance(0.15) ? 2 : 1, t });
      }
    }
    (a.ctors as Ctor[]).push({ name: decl_name(c, name + ("abcd"[ci] ?? "k" + String(ci))), fields });
  }
  if (ips.length > 0) {
    c.feat("adt-indexed");
  }
  const head = [...qps, ...tps.map((tp) => "-" + tp.n + ": Kind(" + qt_bare(tp.q) + ")"), ...ips.map((ip) => "-" + ip.n + ": " + ty_str(ip.t))];
  const kind_s = flavor === "data" ? "Data" : flavor === "type" ? "Type" : "Kind(" + qt_bare(kind) + ")";
  const rows = (a.ctors as Ctor[]).map((ct) => {
    const fs = bind_names(c, ct.fields.length, [], [...qps, ...tps.map((tp) => tp.n), ...ips.map((ip) => ip.n)]);
    return "  " + ct.name + "{" + ct.fields.map((f, i) => bq_prefix(f.q) + fs[i] + ": " + ty_top(f.t)).join(", ") + "}";
  });
  c.push("type " + name + (head.length > 0 ? "<" + head.join(", ") + ">" : "") + " is " + kind_s + ":" + rows.map((r) => "\n" + r).join(""));
  c.s.adts.push(a);
  return a;
}

// Families
// --------
// Types are terms: a family is `law F: for x: I; K` then `def F(x): match
// x:` with an arm per constructor of the index I (Nat or an enum). An arm
// is a type drawn like any other in a scope where the arm's sub-index is a
// term: the family at it (F(p)), a datatype indexed by it, a proposition.
// The law comes first because such a datatype names the family before its
// fill. An applied family is then a type like any other; syn unfolds a
// closed index, or calls mk_fam (def mk(n: I) -> F(n)); a reader reads
// through rd_fam (def rd(n: I, v: F(n)) -> U32) with each arm read inline.

function fam_new(c: Ctx): Fam {
  const name = decl_name(c, "Fm");
  const enums = idx_pool(c).filter((t) => !is_t(t, "Nat"));
  const idx: AdtT = c.g.wpick<() => AdtT>([
    [c.s.base ? 5 : 0, () => bt("Nat")],
    [enums.length > 0 ? 3 : 0, () => c.g.pick(enums)],
    [3, () => {
      const en = decl_name(c, "E");
      const a: Adt = { id: IDS++, name: en, qps: [], tps: [], ips: [], kind: Q2, ctors: [], paren: false, base: false, rec: false };
      a.ctors = Array.from({ length: c.g.size(2, 1, 12) }, (_, i) => ({ name: decl_name(c, en + ("abcd"[i] ?? "k" + String(i))), fields: [] }));
      c.push("type " + en + " is Data:" + a.ctors.map((ct) => "\n  " + ct.name + "{}").join(""));
      c.s.adts.push(a);
      return inst(a);
    }],
  ])();
  const nat = is_t(idx, "Nat");
  c.feat(nat ? "fam-nat" : "fam-enum");
  const kind = c.g.chance(0.5) ? Q2 : Q1;
  const f: Fam = { id: IDS++, name, idx, kind, arms: [], done: false };
  c.s.fams.push(f);
  const [index, pred, src] = bind_names(c, 3);
  c.push("law " + name + ":\n  for " + index + ": " + ty_str(idx) + "\n  " + (qt_known(kind) === 2 ? "Data" : "Type"));
  const pats = nat ? [{ pat: "0n", sub: null, lit: "0n" }, { pat: "1n+" + pred, sub: pred, lit: null, src }]
    : (idx.a.ctors as Ctor[]).map((ct) => ({ pat: ct.name + "{}", sub: null, lit: ct.name + "{}" }));
  for (const pt of pats) {
    // the recursive arm may mention the family at its sub-index; the rest
    // are ordinary types, so every unfolding ends
    const ivars: IVar[] = pt.sub === null ? [] : [{ n: pt.sub, t: idx, sub: true }];
    f.arms.push({ ...pt, ty: syn_ty(c.sub("arm"), c.g.size(1, 1, 12), kind, { tvars: [], qvars: [], ivars, imatch: true }, true) });
  }
  c.push("def " + name + "(" + index + "):\n  match " + index + ":\n" + f.arms.map((arm) => "    case " + arm.pat + ":\n      " + ty_str(arm.ty)).join("\n"));
  f.done = true;
  return f;
}

// fam_pat : an arm's case row in an index-generic def; the sub-index binds
// under a fresh name and re-binds reusable (the arm may hold the family
// at it more than once)
function fam_pat(arm: FamArm, rebind: boolean): string {
  if (arm.sub === null) {
    return arm.pat + ":";
  }
  const pos = arm.pat.lastIndexOf(arm.sub);
  return arm.pat.slice(0, pos) + arm.src + arm.pat.slice(pos + arm.sub.length) + ":" + (rebind ? "\n      " + fam_rebind(arm) : "");
}

function fam_rebind(arm: FamArm): string {
  return "+" + arm.sub + " = " + arm.src;
}

// disc_fam : the family over an index type that is Empty at one literal and
// Unit elsewhere (for Nat, at zero or at every successor)
function disc_fam(c: Ctx, idx: AdtT, at: string): Fam {
  const name = helper(c, "disc:" + ty_key(idx) + ":" + at, "Fm", (c, name) => {
    const [x, p, p0] = bind_names(c, 3);
    const [empty, unit] = [bt("Empty"), bt("Unit")];
    const arms: FamArm[] = is_t(idx, "Nat")
      ? [{ pat: "0n", sub: null, lit: "0n", ty: at === "0n" ? empty : unit }, { pat: "1n+" + p, sub: p, lit: null, ty: at === "0n" ? unit : empty, src: p0 }]
      : idx_lits(idx).map((l) => ({ pat: l, sub: null, lit: l, ty: l === at ? empty : unit }));
    c.s.fams.push({ id: IDS++, name, idx, kind: Q2, arms, done: true });
    return "def " + name + "(" + x + ": " + ty_str(idx) + ") -> Data:\n  match " + x + ":\n" + arms.map((arm) => "    case " + arm.pat + ":\n      " + ty_str(arm.ty)).join("\n");
  });
  return c.s.fams.find((f) => f.name === name) as Fam;
}

// refute : def ne(e: {l == r : I}) -> Empty, for two different literals: a
// discriminating family sends r to Empty and the rest to Unit, so
// rewriting the goal Empty (= Disc(r)) through e leaves Disc(l) = Unit
function refute(c: Ctx, e: EqlT): string {
  c.feat("refute");
  return helper(c, "refute:" + ty_key(e), "ne", (c, name) => {
    const disc = disc_fam(c, e.t as AdtT, e.r);
    return "def " + name + "(e: {" + e.l + " == " + e.r + " : " + ty_str(e.t) + "}) -> Empty:\n  %e : " + disc.name + "(_);\n  Unit{}";
  });
}

// cast_fam : def fc(-m: I, -n: I, e: {m == n : I}, w: F(m)) -> F(n), a
// rewrite through the family with a hole motive (Word.cast's shape)
function cast_fam(c: Ctx, f: Fam): string {
  return helper(c, "cast:" + f.name, "fc", (c, name) => {
    const [m, n, e, w] = bind_names(c, 4);
    const I = ty_str(f.idx);
    return "def " + name + "(-" + m + ": " + I + ", -" + n + ": " + I + ", " + e + ": {" + m + " == " + n + " : " + I + "}, "
      + w + ": " + f.name + "(" + m + ")) -> " + f.name + "(" + n + "):\n  %" + e + " : " + f.name + "(_); " + w;
  });
}

// mk_fam : def mk(n: I) -> F(n), the index-generic value of a family: each
// arm synthesizes its type with the sub-index in scope, so F(p) inside is
// the recursive call
function mk_fam(c: Ctx, f: Fam): string {
  c.feat("fam-mk");
  return helper(c, "mk:fam:" + f.name, "mf", (c, name) => {
    const index = bind_name(c, []);
    const rows = f.arms.map((arm) => {
      const env: V[] = arm.sub === null ? [] : [{ ...v_new(arm.sub, f.idx, true), dec: true }];
      return "    case " + fam_pat(arm, true) + "\n      " + syn(c, arm.ty, env, 1);
    });
    return "def " + name + "(" + index + ": " + ty_str(f.idx) + ") -> " + f.name + "(" + index + "):\n  match " + index + ":\n" + rows.join("\n");
  });
}

// rd_fam : def rd(n: I, v: F(n)) -> U32, reading v at the arm the index
// selects (the checker refines v's type under the match on n); the re-bind
// of the sub-index sits after the destructures and inside the match arms
// that read v: a let cannot open a later scrutinee
function rd_fam(c: Ctx, f: Fam): string {
  c.feat("fam-rd");
  return helper(c, "rd:fam:" + (c.s.pure ? "p:" : "x:") + f.name, "rf", (c, name) => {
    const [index, value] = bind_names(c, 2);
    const rows = f.arms.map((arm) => "    case " + fam_pat(arm, false) + "\n      " + rd_arm(c, arm.ty, value, "      ", arm.sub === null ? null : fam_rebind(arm)));
    return "def " + name + "(" + index + ": " + ty_str(f.idx) + ", " + value + ": " + f.name + "(" + index + ")) -> U32:\n  match " + index + ":\n" + rows.join("\n");
  });
}

// Syn: values
// -----------
// syn(c, goal, env, fuel): a term of type goal. fuel is a size budget: a
// production spends one and splits the rest among its parts (split), so
// a big budget makes a deep, a wide or a bushy term. The productions:
// a binder in scope, a call of the registry, a minted def's call, an
// application of a function in scope, and the goal's own introductions
// (constructors, literals, tuples, lambdas, partial applications, a
// family's unfolding); any of them may fail, and the next is drawn.
// Results may be intro-headed (non-inferable): a caller placing one in an
// inferring position (a bare let) annotates it.

// FLOOR : at and below it a goal takes a leaf form when it has one (a
// binder, a literal, a nullary constructor, {==}), else its cheapest
// completion (ty_cost: a constructor, a pair, a lambda, a family's
// unfolding, a call answering exactly its head), whose parts are cheaper
// still: the term ends
const FLOOR = -2;
// STEPS : the synthesis steps a member takes before it settles on floor
// terms (a failing search branches)
const STEPS = 200_000;

// split : n spread over k parts, one of them heavy (a spine) at times; a
// budget at or below zero passes itself to every part
function split(g: Gen, n: number, k: number): number[] {
  const out = new Array<number>(k).fill(Math.min(0, n));
  if (k === 0 || n <= 0) {
    return out;
  }
  const heavy = g.int(k);
  out[heavy] = Math.floor(n * g.int(1001) / 1000);
  for (let i = out[heavy]; i < n; i++) {
    out[g.int(k)]++;
  }
  return out;
}

type Kit = Array<[number, () => string | null]>;

// FIELD_MASKS : a constructor field of Base taken modulo a bound: a Char's
// code stays below the surrogates (the JS runtime holds Unicode scalar
// values only, a reviewed limit)
const FIELD_MASKS: Record<string, number[]> = { Chr: [0xd800] };

// attempt : a weighted draw over productions that may fail (null or a
// throw); a failed one is struck and the next drawn, and when none is
// left, last
function attempt(c: Ctx, kit: Kit, what: string, last?: () => string): string {
  const live = kit.filter(([w]) => w > 0);
  while (live.length > 0) {
    const i = c.g.wpick(live.map(([w], j): [number, number] => [w, j]));
    let got: string | null = null;
    try {
      got = live[i][1]();
    } catch (e) {
      if (!(e instanceof Error) || !/^(no inhabitant|helper knot)/.test(e.message)) {
        throw e;
      }
    }
    if (got !== null && got !== "") {
      return got;
    }
    live.splice(i, 1);
  }
  if (last !== undefined) {
    return last();
  }
  throw new Error("no inhabitant: " + what);
}

function syn(c: Ctx, goal: T, env: V[], fuel: number): string {
  if (fuel <= FLOOR && ty_cost(goal) === Infinity) {
    throw new Error("no inhabitant: " + ty_str(goal));
  }
  // a member that has searched long draws its cheapest terms from here on
  if (++c.s.steps > STEPS) {
    fuel = Math.min(fuel, FLOOR);
  }
  if (fuel > 0 && !ty_open(goal) && c.g.chance(c.s.surface)) {
    return surface(c, goal, env, fuel - 1);
  }
  const vars = env_live(env, (t) => ty_eq(t, goal));
  const leaf: Kit = [[vars.length > 0 ? 30 : 0, () => env_take(c.g.pick(vars))], ...leaves(c, goal, env, fuel)];
  if (fuel <= FLOOR) {
    return attempt(c, leaf.some(([w]) => w > 0) ? leaf : [...intros(c, goal, env, fuel), [10, () => call_unify(c, goal, env, fuel - 1, { exact: true })]], ty_str(goal));
  }
  // when every production fails, the cheapest completion
  return attempt(c, [
    ...leaf,
    ...intros(c, goal, env, fuel),
    [fuel > 0 ? 14 : 4, () => call_unify(c, goal, env, fuel - 1, { exact: fuel <= 0 })],
    [fuel >= 2 && !ty_open(goal) ? 4 : 0, () => def_new(c, goal, env, fuel - 1)],
    [6, () => apply(c, goal, env, fuel - 1)],
  ], ty_str(goal), () => syn(c, goal, env, FLOOR));
}

// leaves : the goal's forms with no part: a literal, a nullary
// constructor, reflexivity
function leaves(c: Ctx, goal: T, env: V[], fuel: number): Kit {
  if (goal.k === "eql") {
    return [[goal.l === goal.r ? 30 : 0, () => (c.feat("eql"), "{==}")]];
  }
  if (goal.k !== "adt") {
    return [];
  }
  const lit = goal.a.base ? LITS[goal.a.name] : undefined;
  const nullary = (goal.a.ctors ?? []).filter((ct) => ct.fields.length === 0);
  return [
    [lit !== undefined && (lit.ok?.(goal) ?? true) ? 25 : 0, () => (lit as Lit).f(c, goal, env, fuel)],
    [nullary.length > 0 ? 15 : 0, () => c.g.pick(nullary).name + "{}"],
  ];
}

// intros : the goal's introduction forms with parts
function intros(c: Ctx, goal: T, env: V[], fuel: number): Kit {
  switch (goal.k) {
    case "tvar": case "eql": return [];
    case "sig": return [[30, () => {
      const [fa, fb] = split(c.g, fuel - 1, 2);
      if (goal.x === null) {
        return "(" + syn(c, goal.a, env, fa) + ", " + syn(c, goal.b, env, fb) + ")";
      }
      // a witness whose evidence has a value, then the evidence
      const x = goal.x;
      const ws = idx_type(goal.a) ? idx_lits(goal.a).filter((w) => ty_inh(ty_tsub(goal.b, x, w))) : [];
      if (fuel <= FLOOR) {
        ws.sort((u, v) => ty_cost(ty_tsub(goal.b, x, u)) - ty_cost(ty_tsub(goal.b, x, v)));
        ws.length = Math.min(ws.length, 1);
      }
      if (ws.length === 0) {
        return null;
      }
      c.feat("sig-value");
      const w = c.g.pick(ws);
      return "(" + w + ", " + syn(c, ty_tsub(goal.b, x, w), env, fb) + ")";
    }]];
    case "fun": {
      if (ty_refutable(goal.dom)) {
        // a clash refuted through a discriminating family
        const dom = goal.dom;
        return [[30, () => {
          if (!ty_inh(goal.cod)) {
            return refute(c, dom);
          }
          c.feat("absurd");
          const b = bind_name(c, env);
          return b + " => Empty.absurd(" + ty_str(goal.cod) + ", " + refute(c, dom) + "(" + b + "))";
        }]];
      }
      return [
        [35, () => {
          const b = bind_name(c, env);
          // an erased binder is dead inside
          const inner = goal.q === 0 ? env_bind(env, [b]) : env_bind(env, [b], [v_new(b, goal.dom, goal.q === 2)]);
          const plus = goal.q === 1 && ty_data(goal.dom) && c.s.tmpl === false && c.g.chance(0.2);
          if (plus) {
            c.feat("plus-lam");
            inner[inner.length - 1].q = "many";
          }
          return (plus ? "+" : "") + b + " => " + syn(c, goal.cod, inner, fuel - 1);
        }],
        // partial application: a def missing exactly its last argument
        // (deeper partials die in js_book)
        [fuel >= 1 && goal.q === 1 ? 15 : 0, () => {
          const cands = visible(c, env).filter((d) => d.wip === undefined && d.hdr.length === 0 && d.tm === 0 && d.ps.length >= 1
            && d.ps[d.ps.length - 1].q === 1 && d.ps[d.ps.length - 1].mask === undefined
            && ty_eq(d.ps[d.ps.length - 1].t, goal.dom) && ty_eq(d.ret, goal.cod));
          if (cands.length === 0) {
            return null;
          }
          const d = c.g.pick(cands);
          const front = call_args(c, { ...d, ps: d.ps.slice(0, -1) }, env, fuel - 1);
          if (front === null) {
            return null;
          }
          c.feat("partial");
          return front.length > 0 ? d.name + "(" + front.join(", ") + ")" : d.name;
        }],
      ];
    }
    case "app": {
      // a closed index unfolds to its arm; any index goes through the
      // family's index-generic def (inside it, only at a decreasing index)
      const arm = fam_unfold(goal.f, goal.arg);
      const key = "mk:fam:" + goal.f.name;
      const inMk = c.s.wip.has(key);
      const canMk = fam_total(goal.f) && (!inMk || env.some((v) => v.name === goal.arg && v.dec === true && v.q !== "dead"));
      return [
        [arm !== null && ty_inh(arm) ? 20 : 0, () => {
          c.feat("fam-unfold");
          return syn(c, arm as T, env, fuel - 1);
        }],
        [canMk ? 20 : 0, () => (inMk ? c.s.memo.get(key) as string : mk_fam(c, goal.f)) + "(" + goal.arg + ")"],
        // a value moved across the reflexive index equation
        [fam_total(goal.f) && fuel > 0 ? 5 : 0, () => {
          c.feat("fam-cast");
          const cast = cast_fam(c, goal.f);
          return cast + "(" + goal.arg + ", " + goal.arg + ", {==}, " + syn(c, goal, env, fuel - 1) + ")";
        }],
      ];
    }
    case "adt": {
      // at a small budget, a constructor that does not recur; at the floor,
      // one of the cheapest
      const cost = (ct: Ctor): number => ctor_fields(goal, ct).reduce((m, f) => Math.max(m, ty_cost(f.t)), 0);
      const self = (ct: Ctor): boolean => ctor_fields(goal, ct).some((f) => ty_eq(f.t, goal));
      const all = (goal.a.ctors ?? []).filter((ct) => ct.fields.length > 0 && (fuel > 0 || !self(ct)));
      const least = Math.min(...all.map(cost));
      const ctors = fuel <= FLOOR ? all.filter((ct) => cost(ct) === least && least < Infinity) : all;
      return [[ctors.length > 0 ? 30 : 0, () => {
        const ct = c.g.pick(ctors);
        const fs = ctor_fields(goal, ct);
        const budget = split(c.g, fuel - 1, fs.length);
        const mask = goal.a.base ? FIELD_MASKS[ct.name] : undefined;
        // an erased or + field synthesizes against the reusable binders:
        // a dead position never consumes, a + argument is certified once
        const args = fs.map((f, i) => {
          const e = syn(c, f.t, f.q === 1 ? env : env_live(env).filter((v) => v.q === "many"), budget[i]);
          return mask?.[i] === undefined ? e : "(" + e + " % " + String(mask[i]) + " : U32)";
        });
        const op = OPS.get(ct.name);
        if (goal.a.base && op !== undefined && args.length === 2 && !args[0].includes("=>") && c.g.chance(0.5)) {
          c.feat("cons");
          return "(" + args[0] + " " + op + " " + args[1] + ")";
        }
        return ct.name + "{" + args.join(", ") + "}";
      }]];
    }
  }
}

// surface : one of the surface forms around a term of the goal:
// an annotation, an applied identity, a rewrite by reflexivity, an erased
// let, a box destructured, an applied inline match
function surface(c: Ctx, goal: T, env: V[], fuel: number): string {
  const ty = ty_str(goal);
  const name = "sx" + String(c.uid());
  const inner = (): string => syn(c, goal, env, fuel);
  const shapes = adt_pool(c).filter((a) => a.ctors !== null && a.ctors.length > 0 && a.qps.length + a.tps.length + a.ips.length === 0);
  return attempt(c, [
    [3, () => {
      c.feat("syntax-ann");
      return "{" + inner() + " : " + ty + "}";
    }],
    [3, () => {
      c.feat("syntax-beta");
      return "{(" + name + " => " + name + ") : (" + ty + ") -> (" + ty + ")}(" + inner() + ")";
    }],
    [c.s.base && !c.s.tmpl ? 2 : 0, () => {
      c.feat("syntax-rewrite");
      return "(%" + name + "@{{==} : {0n == 0n : Nat}} : " + ty + "; (" + inner() + "))";
    }],
    [c.s.base ? 2 : 0, () => {
      c.feat("syntax-erased-let");
      const rhs = syn(c, bt("Nat"), env_live(env).filter((v) => v.q === "many"), fuel);
      return "{(" + name + " => -" + name + "e = {" + rhs + " : Nat}; " + inner() + ") : Unit -> (" + ty + ")}(Unit{})";
    }],
    [2, () => {
      c.feat("syntax-ctor-let");
      const unbox = helper(c, "syntax-unbox", "sxunbox", (hc, fn) => {
        const [value, box] = bind_names(hc, 2, [], ["T"]);
        return "type " + fn + "Box<-T: Type> is Type:\n  " + fn + "K{" + value + ": T}\n\n"
          + "def " + fn + "(-T: Type, " + box + ": " + fn + "Box<T>) -> T:\n  " + fn + "K{" + value + "} = " + box + "\n  " + value;
      });
      return unbox + "(" + ty_grp(goal) + ", " + unbox + "K{" + inner() + "})";
    }],
    [shapes.length > 0 ? 4 : 0, () => {
      const shape = inst(c.g.pick(shapes));
      c.feat("syntax-inline");
      const scrut = syn(c, shape, env, fuel);
      const branches: V[][] = [];
      const arm = (fields: Field[]): string => {
        const local = env.map((v) => ({ ...v }));
        branches.push(local);
        const vars = fields.map((f, i) => {
          const v = v_new(name + "f" + String(i), f.t, f.q === 2);
          if (f.q === 0) {
            v.q = "dead";
          }
          return v;
        });
        return vars.map((v) => v.name + " => ").join("") + syn(c, goal, local.concat(vars), fuel);
      };
      const ctors = shape.a.ctors as Ctor[];
      const tail = ctors.length > 1 && c.g.chance(0.5);
      if (tail) {
        c.feat("syntax-inline-default");
      }
      const arms = (tail ? ctors.slice(0, -1) : ctors).map((ct) => ct.name + ": " + arm(ctor_fields(shape, ct)))
        .concat(tail ? [name + " => " + arm([])] : []).join("; ");
      env.forEach((v, i) => {
        if (v.q === "lone" && branches.some((b) => b[i].q === "dead")) {
          v.q = "dead";
        }
      });
      return "{(\\{" + arms + "}) : (" + ty_str(shape) + ") -> (" + ty + ")}(" + scrut + ")";
    }],
  ], ty);
}

// apply : a function in scope applied to as many arguments as reach the
// goal
function apply(c: Ctx, goal: T, env: V[], fuel: number): string | null {
  const arity = (t: T): FunT[] | null => {
    const out: FunT[] = [];
    for (; t.k === "fun" && out.length < 4; t = t.cod) {
      out.push(t);
      if (ty_eq(t.cod, goal)) {
        return out;
      }
    }
    return null;
  };
  const fs = env_live(env, (t) => arity(t) !== null);
  if (fs.length === 0) {
    return null;
  }
  const f = c.g.pick(fs);
  const doms = arity(f.ty) as FunT[];
  c.feat("apply");
  const budget = split(c.g, fuel, doms.length);
  const head = env_take(f);
  return head + "(" + doms.map((d, i) => syn(c, d.dom, d.q === 1 ? env : env_live(env).filter((v) => v.q === "many"), budget[i])).join(", ") + ")";
}

// Calls
// -----

// visible : the registry at this point: Base's defs (none stuck on the
// pure side, no effect), the program's own, none a binder shadows, and no
// template inside a template's argument (its instances would not stop
// growing)
function visible(c: Ctx, env: V[], goal?: T): DefR[] {
  const shadowed = new Set(env_live(env).map((v) => v.name));
  const h = goal === undefined ? null : head(goal);
  const base = !c.s.base ? [] : h === null ? BASE_DEFS : h === "*" ? BASE_DEFS : [...BASE_BY_HEAD.get(h) ?? [], ...BASE_BY_HEAD.get("*") ?? []];
  const own = c.s.defs.filter((d) => h === null || h === "*" || head(d.ret) === h || head(d.ret) === "*");
  return [...base, ...own].filter((d) => d.effect !== true && !(c.s.pure && d.stuck === true) && !(c.s.tmpl && d.tm > 0) && !shadowed.has(d.name.split(".")[0])
    && !shadowed.has(d.name));
}

// call_unify : a call of a visible def whose return type unifies with the
// goal — quantity and type variables bind, the leftovers draw fresh; a few
// candidates are tried, Base's defs and the program's own evenly, and at a
// budget spent the ones of fewest parameters first
function call_unify(c: Ctx, goal: T, env: V[], fuel: number, opt: { plain?: boolean; exact?: boolean } = {}): string | null {
  const cands = visible(c, env, goal).filter((d) => (opt.exact !== true || head(d.ret) === head(goal)) && ty_unify(d.ret, goal, new Map(), new Map()));
  if (fuel < 0) {
    // a call whose unification binds every type variable, and whose
    // parameters are cheaper than the goal (the term ends)
    const top = ty_cost(goal);
    const cost = (d: DefR): number => {
      const m = new Map<string, T>();
      const qm = new Map<string, QT>();
      ty_unify(d.ret, goal, m, qm);
      return d.tps.some((tp) => !m.has(tp.n)) ? Infinity
        : d.ps.reduce((x, p) => Math.max(x, p.mask !== undefined ? 0 : ty_cost(ty_sub(p.t, m, qm))), 0);
    };
    for (const d of c.g.shuffle(cands).map((d): [number, DefR] => [cost(d), d]).filter(([k]) => k < top).sort((a, b) => a[0] - b[0]).slice(0, 2).map(([, d]) => d)) {
      const got = call(c, d, goal, env, fuel, { plain: opt.plain });
      if (got !== null) {
        return got;
      }
    }
    return null;
  }
  const pools = [c.g.shuffle(cands.filter((d) => d.base !== true)), c.g.shuffle(cands.filter((d) => d.base === true))];
  for (let tries = 3; tries > 0 && pools.some((p) => p.length > 0); tries--) {
    const pool = pools[0].length === 0 ? pools[1] : pools[1].length === 0 || c.g.chance(0.5) ? pools[0] : pools[1];
    const got = call(c, pool.pop() as DefR, goal, env, fuel, { plain: opt.plain });
    if (got !== null) {
      return got;
    }
  }
  return null;
}

// CallOpt : fixed arguments by position, variables already bound, and a
// plain spelling (no operator or sugar)
type CallOpt = { fixed?: Map<number, string>; m?: Map<string, T>; qm?: Map<string, QT>; plain?: boolean };

// call : d called at the goal (its return type unifies with it). A
// self-call keeps its own type and quantity variables; elsewhere a
// variable the goal leaves free draws fresh.
function call(c: Ctx, d: DefR, goal: T, env: V[], fuel: number, opt: CallOpt = {}): string | null {
  // a self-call keeps the def's own variables (its pass-through arguments
  // have their types)
  const own = d.wip !== undefined;
  const m = opt.m ?? new Map<string, T>(own ? d.tps.map((tp): [string, T] => [tp.n, { k: "tvar", n: tp.n, q: tp.q }]) : []);
  const qm = opt.qm ?? new Map<string, QT>(own ? d.qps.map((n): [string, QT] => [n, { k: "qv", n }]) : []);
  if (!ty_unify(d.ret, goal, m, qm)) {
    return null;
  }
  for (const qp of d.qps) {
    if (!qm.has(qp)) {
      qm.set(qp, c.g.chance(0.5) ? Q1 : Q2);
    }
  }
  for (const tp of d.tps) {
    if (!m.has(tp.n)) {
      m.set(tp.n, syn_ty(c, c.g.size(0, 1, 8), qt_sub(tp.q, qm)));
    }
  }
  // a + parameter must instantiate at a concretely-Data type
  const ps = d.ps.map((p) => ({ ...p, t: ty_sub(p.t, m, qm) }));
  if (ps.some((p) => p.q === 2 && !ty_data(p.t))) {
    return null;
  }
  const args = call_args(c, { ...d, ps }, env, fuel, opt.fixed);
  if (args === null) {
    return null;
  }
  c.feat(d.base === true ? "base:" + d.name : d.hdr.length > 0 ? "generic-call" : "call");
  if (d.tm > 0) {
    c.feat("template");
  }
  // a template's type arguments are closed (a type variable of the def
  // being drawn is not comptime), unless the def passes its own through
  if (d.wip === undefined && d.hdr.slice(0, d.tm).some((n) => d.qps.includes(n) ? qt_known(qm.get(n) as QT) === null : ty_open(m.get(n) as T))) {
    return null;
  }
  const hdr = d.hdr.map((n) => d.qps.includes(n) ? qt_str(qm.get(n) as QT) : ty_grp(m.get(n) as T));
  return spell_call(c, d, hdr, args, ps, opt.plain === true);
}

// spell_call : a call as the surface spells it: the operator the parser's
// table names for its method, framed by its family ((a + b : U32) is
// U32.add; an operand of the same family inherits the frame), a fixed
// operator bare (a || b), Array.get and set as a[i] and a[i] <- v, or the
// plain call, templates marked ~
function spell_call(c: Ctx, d: DefR, hdr: string[], args: string[], ps: Param[], plain: boolean): string {
  const dot = d.name.lastIndexOf(".");
  const fam = d.name.slice(0, dot);
  const op = OPS.get(d.name) ?? (dot > 0 ? OPS.get(d.name.slice(dot)) : undefined);
  const frame = ps.length > 0 && ps[0].t.k === "adt" && ps[0].t.a.name === fam && !ps[0].t.a.paren ? ty_str(ps[0].t) : null;
  if (!plain && op !== undefined && d.tm === 0 && hdr.length === 0 && args.length === 2 && !args.some((a) => a.includes("=>")) && c.g.chance(0.7)) {
    if (OPS.has(d.name)) {
      c.feat("op-fixed");
      return "(" + args[0] + " " + op + " " + args[1] + ")";
    }
    if (frame !== null) {
      c.feat("op-method");
      const [a, b] = args.map((x) => {
        const f = c.s.framed.get(x);
        return f !== undefined && f[1] === frame && c.g.chance(0.3) ? (c.feat("op-inherit"), "(" + f[0] + ")") : x;
      });
      const body = a + " " + op + " " + b;
      const s = "(" + body + " : " + frame + ")";
      c.s.framed.set(s, [body, frame]);
      return s;
    }
  }
  if (!plain && d.base === true && (d.name === "Array.get" || d.name === "Array.set") && hdr[0] === "U32" && !args[0].includes("=>") && c.g.chance(0.5)) {
    c.feat("array-sugar");
    return d.name === "Array.get" ? args[0] + "[" + args[1] + "]" : "(" + args[0] + "[" + args[1] + "] <- " + args[2] + ")";
  }
  const all = hdr.concat(args).map((a, i) => i < d.tm ? "~" + a : a);
  return d.name + "(" + all.join(", ") + ")";
}

// call_args : the value arguments in order. A self-call passes through
// every live argument before its decreasing column (the parameter, or the
// variable row that re-bound it) and every template, and a sub-field at the
// column; an index parameter later types depend on takes a literal under
// which each has a value; a masked one is small; a template's is closed.
function call_args(c: Ctx, d: DefR, env: V[], fuel: number, fixed: Map<number, string> = new Map()): string[] | null {
  const wip = d.wip;
  if (wip !== undefined && c.s.wips[c.s.wips.length - 1]?.name !== d.name) {
    return null;
  }
  const subs = wip === undefined ? null : wip.subs.filter((v) => v.q !== "dead" && env.includes(v));
  if (subs !== null && subs.length === 0) {
    return null;
  }
  const args: string[] = [];
  let ps = d.ps.slice();
  const budget = split(c.g, fuel, ps.length);
  for (let i = 0; i < ps.length; i++) {
    const p = ps[i];
    const tmpl = d.hdr.length + i < d.tm;
    const got = fixed.get(i);
    if (got !== undefined) {
      args.push(got);
      continue;
    }
    if (wip !== undefined && (i < wip.col || tmpl)) {
      // an erased or template parameter passes by its own name, unless a
      // binder shadows it here
      if (p.q === 0 || tmpl) {
        if (env.some((v) => v.name === p.n && v !== wip.ps[i])) {
          return null;
        }
        args.push(p.n as string);
        continue;
      }
      const same = env.find((v) => v.q !== "dead" && (v === wip.ps[i] || v.of === wip.ps[i]));
      if (same === undefined) {
        return null;
      }
      args.push(env_take(same));
      continue;
    }
    if (wip !== undefined && i === wip.col) {
      const sub = c.g.pick(subs as V[]);
      wip.subs = wip.subs.filter((v) => v !== sub);
      wip.calls++;
      args.push(env_take(sub));
      continue;
    }
    const deps = p.n === undefined || p.dep !== true ? [] : ps.slice(i + 1).filter((q) => ty_mentions(q.t, p.n as string));
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
    if (p.mask !== undefined) {
      const w = syn(c, bt("U32"), env, budget[i]);
      args.push(is_t(p.t, "Nat") ? "U32.to_nat((" + w + " % " + String(p.mask) + " : U32))" : "(" + w + " % " + String(p.mask) + " : U32)");
      continue;
    }
    if (tmpl) {
      // a template's argument is closed: nothing in scope reaches it
      c.feat("template-arg");
      const was = c.s.tmpl;
      c.s.tmpl = true;
      try {
        args.push(syn(c, p.t, [], budget[i]));
      } finally {
        c.s.tmpl = was;
      }
      continue;
    }
    try {
      args.push(syn(c, p.t, p.q === 1 ? env : env_live(env).filter((v) => v.q === "many"), budget[i]));
    } catch (e) {
      if (e instanceof Error && /^(no inhabitant|helper knot)/.test(e.message)) {
        return null;
      }
      throw e;
    }
  }
  // twins: one reusable value passed as two arguments
  if (args.some((a, j) => /^[A-Za-z_]\w*$/.test(a) && args.indexOf(a) !== j)) {
    c.feat("twins");
  }
  return args;
}

// Defs
// ----
// One production mints every def with control flow. def_new(c, goal, env,
// fuel) may first generalize the goal (a closed part of it becomes a type
// variable, the quantities around it a quantity variable), draws the
// parameters (evidence about an earlier index parameter, the goal's own
// type as a state, a leading function as a template), matches on some of
// them at the head of the body (a decision tree over their constructors, a
// variable row where an arm does not care, a nested match on a row's last
// binder) and synthesizes each leaf against the goal with the row's
// binders in scope, after lets of its own. The def sits in the registry
// while its leaves are drawn, callable only with a sub-field bound by a
// constructor pattern at its decreasing column, each once per leaf; so a
// countdown loop, a fold, a builder, a transform, a tree recursion (two
// self-calls in a parallel let), a tuple-returning walk, an IO loop and a
// generic or higher-order def are one production at different goals and
// parameter types. A monadic goal (a family of Base with bind and pure)
// may take a do-block leaf.

type Split = { pat: string; vs: V[]; subs: V[]; wild: boolean };
type DefSt = { loop: boolean; dec: V | null; fuel: number; leaves: number; cap: number; depth: number };

function col_matchable(t: T): boolean {
  return (t.k === "adt" && t.a.ctors !== null && t.a.ctors.length > 0) || (t.k === "sig" && t.x === null);
}

// ty_wf : every type argument fits its parameter's declared kind
function ty_wf(t: T): boolean {
  switch (t.k) {
    case "adt": {
      const qm = new Map(t.a.qps.map((n, i) => [n, t.qs[i]]));
      return t.args.every((x, i) => qt_fits(ty_quant(x), qt_sub(t.a.tps[i].q, qm)) && ty_wf(x));
    }
    case "sig": return (t.q === 1 || (ty_data(t.a) && ty_data(t.b))) && ty_wf(t.a) && ty_wf(t.b);
    case "fun": return (t.q !== 2 || ty_data(t.dom)) && ty_wf(t.dom) && ty_wf(t.cod);
    default: return true;
  }
}

type Gnr = { ret: T; qps: string[]; tps: TvarInfo[] };

// generalize : the goal with one closed part of it a type variable A (and,
// at times, the quantities that govern A's positions a variable a, A:
// Kind(a)); the def's return type, which the goal instantiates
function generalize(c: Ctx, goal: T): Gnr | null {
  const parts: T[] = [];
  const walk = (t: T): void => {
    if (!ty_open(t) && t.k !== "eql" && t.k !== "app") {
      parts.push(t);
    }
    if (t.k === "adt") {
      t.args.forEach(walk);
    } else if (t.k === "sig" && t.x === null) {
      walk(t.a);
      walk(t.b);
    } else if (t.k === "fun") {
      walk(t.dom);
      walk(t.cod);
    }
  };
  walk(goal);
  if (parts.length === 0) {
    return null;
  }
  const s = c.g.pick(parts);
  const [A, a] = bind_names(c, 2);
  const tv = (q: QT): T => ({ k: "tvar", n: A, q });
  const rep = (t: T, v: T): T => ty_eq(t, s) ? v
    : t.k === "adt" ? { ...t, args: t.args.map((x) => rep(x, v)) }
    : t.k === "sig" && t.x === null ? { ...t, a: rep(t.a, v), b: rep(t.b, v) }
    : t.k === "fun" ? { ...t, dom: rep(t.dom, v), cod: rep(t.cod, v) } : t;
  // the quantity a of the instances holding A where their parameter's kind
  // is one of their own quantity parameters
  const qrep = (t: T): T => {
    if (t.k === "adt") {
      const qs = t.qs.slice();
      t.args.forEach((x, i) => {
        const k = t.a.tps[i].q;
        if (x.k === "tvar" && x.n === A && k.k === "qv") {
          qs[t.a.qps.indexOf(k.n)] = { k: "qv", n: a };
        }
      });
      return { ...t, qs, args: t.args.map(qrep) };
    }
    return t.k === "sig" && t.x === null ? { ...t, a: qrep(t.a), b: qrep(t.b) } : t.k === "fun" ? { ...t, dom: qrep(t.dom), cod: qrep(t.cod) } : t;
  };
  if (c.g.chance(0.5)) {
    const ret = qrep(rep(goal, tv({ k: "qv", n: a })));
    if (ty_wf(ret)) {
      c.feat("qpoly-def");
      return { ret, qps: [a], tps: [{ n: A, q: { k: "qv", n: a } }] };
    }
  }
  const q = ty_data(s) && c.g.chance(0.5) ? Q2 : Q1;
  const ret = rep(goal, tv(q));
  return ty_wf(ret) ? { ret, qps: [], tps: [{ n: A, q }] } : null;
}

// col_wild : a variable row over one column, the whole value re-bound
function col_wild(c: Ctx, v: V, env: V[], taken: string[] = []): Split {
  const n = bind_name(c, env, taken);
  return { pat: n, vs: [{ ...v_new(n, v.ty, v.q === "many"), of: v.of ?? v }], subs: [], wild: true };
}

// adt_row : one match row for a constructor of an instance: the pattern
// and the bound field binders (erased ones bind dead); a + on a lone Data
// field binder re-binds it reusable; a List row may spell its constructor
// as the cons or the empty literal
function adt_row(c: Ctx, t: AdtT, ct: Ctor, many: boolean, env: V[], taken: string[]): Split {
  const vs: V[] = [];
  const names: string[] = [];
  for (const f of ctor_fields(t, ct)) {
    const nm = bind_name(c, env, taken.concat(vs.map((v) => v.name)));
    const mark = f.q === 1 && !many && ty_data(f.t) && c.g.chance(0.2);
    if (mark) {
      c.feat("plus-pat");
    }
    names.push((mark ? "+" : "") + nm);
    const v = v_new(nm, f.t, (f.q === 2 || many || mark) && ty_data(f.t));
    if (f.q === 0) {
      v.q = "dead";
    }
    vs.push(v);
  }
  const op = OPS.get(ct.name);
  if (t.a.base && op !== undefined && names.length === 2 && c.g.chance(0.5)) {
    c.feat("cons-pat");
    return { pat: names[0] + " " + op + " " + names[1], vs, subs: [], wild: false };
  }
  if (t.a.base && t.a.name === "List" && names.length === 0 && c.g.chance(0.5)) {
    return { pat: "[]", vs, subs: [], wild: false };
  }
  return { pat: ct.name + "{" + names.join(", ") + "}", vs, subs: [], wild: false };
}

// col_splits : the rows one column splits into: a Nat may peel or table
// with a variable row last, a List may take literal patterns with a
// wildcard row, the rest split by constructor. The sub-fields a self-call
// may descend on are the binders of the column's own type.
function col_splits(c: Ctx, v: V, env: V[], desc: boolean, bound: string[]): Split[] {
  const t = v.ty;
  const many = v.q === "many";
  const taken = (desc ? env.map((w) => w.name) : []).concat(bound);
  const senv = env.filter((w) => !bound.includes(w.name));
  const bind = (ty: T, more: string[] = []): V => v_new(bind_name(c, senv, taken.concat(more)), ty, many);
  const row = (pat: string, vs: V[], subs: V[] = []): Split => ({ pat, vs, subs, wild: false });
  if (t.k === "sig") {
    c.feat("match-tup");
    const a = bind(t.a);
    const b = bind(t.b, [a.name]);
    return [row("(" + a.name + ", " + b.name + ")", [a, b])];
  }
  const at = t as AdtT;
  c.feat(at.a.base ? "match-" + at.a.name : "match-adt");
  if (is_t(at, "Nat")) {
    const style = c.g.wpick<string>([[4, "succ"], [2, "peel"], [2, "table"], [2, "ctor"]]);
    c.feat("nat-" + style);
    if (style === "succ" || style === "peel") {
      const p = bind(at);
      const k = style === "succ" ? 1 : 2 + c.g.int(4);
      return [...(style === "succ" ? [row("0n", [])] : []), row(String(k) + "n+" + p.name, [p], [p]), ...(style === "peel" ? [col_wild(c, v, senv, taken)] : [])];
    }
    if (style === "table") {
      return Array.from({ length: c.g.size(2, 3, 40) }, (_, i) => row(String(i) + "n", [])).concat([col_wild(c, v, senv, taken)]);
    }
  }
  if (is_t(at, "List") && ty_data(at.args[0]) && c.g.chance(0.3)) {
    c.feat("list-pat");
    const els = Array.from({ length: c.g.size(1, 1, 6) }, () => at.args[0]);
    const vs: V[] = [];
    for (const el of els) {
      vs.push(bind(el, vs.map((w) => w.name)));
    }
    const plus = vs.map((w) => qt_known(at.qs[0]) === 2 && w.q === "lone" && c.g.chance(0.3) ? (w.q = "many", "+") : "");
    // (no nested match opens on a literal pattern's binder)
    return [{ ...row("[" + vs.map((w, i) => plus[i] + w.name).join(", ") + "]", vs), wild: true }, row("[]", []), { pat: "_", vs: [], subs: [], wild: true }];
  }
  return (at.a.ctors as Ctor[]).map((ct) => {
    const r = adt_row(c, at, ct, many, desc ? [] : senv, taken);
    return { ...r, subs: r.vs.filter((f) => f.q !== "dead" && ty_eq(f.ty, t)) };
  });
}

// match_text : a match over columns (parameters, or one bound field), its
// rows the decision tree over their splits, each leaf drawn under the
// row's binders with the sub-fields the self-call may descend on
function match_text(c: Ctx, d: DefR, goal: T, cols: V[], env: V[], subs: V[], ind: string, st: DefSt): string {
  const rows: string[] = [];
  const bound: V[] = [];
  const go = (i: number, pats: string[], env2: V[], subs2: V[], last: V | null): void => {
    if (i === cols.length) {
      rows.push(ind + "  case " + pats.join(", ") + ":\n" + leaf_text(c, d, goal, env2, subs2, last, ind + "    ", st));
      return;
    }
    const col = cols[i];
    const wild = !col_matchable(col.ty) || st.leaves + rows.length > st.cap || (cols.length > 1 && c.g.chance(0.25));
    if (wild && col_matchable(col.ty)) {
      c.feat("wild");
    }
    // a sub-field descends when its column is the decreasing one, or a
    // binder that descends (a nested match on it)
    const desc = col.dec === true || col === st.dec;
    const row = pats.length === 0 ? [] : env2.filter((w) => w.of !== undefined || bound.includes(w)).map((w) => w.name);
    for (const s of wild ? [col_wild(c, col, env2, row)] : col_splits(c, col, env2, desc, row)) {
      if (desc) {
        s.subs.forEach((w) => {
          w.dec = true;
        });
      }
      bound.push(...s.vs);
      // a nested match may scrutinize the last column's last binder only
      const lastHere = i === cols.length - 1 && !s.wild && s.vs.length > 0 ? s.vs[s.vs.length - 1] : null;
      go(i + 1, pats.concat([s.pat]), env_bind(env2, s.vs.map((w) => w.name), s.vs), desc ? subs2.concat(s.subs) : subs2, lastHere);
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
  go(0, [], env_live(env), subs.filter((v) => v.q !== "dead"), null);
  return ind + "match " + cols.map((v) => v.name).join(", ") + ":\n" + rows.join("\n");
}

// monad : the family of Base whose bind and pure a do-block of this goal
// desugars to, if any
function monad(c: Ctx, goal: T): AdtT | null {
  return c.s.base && goal.k === "adt" && goal.a.base && goal.args.length > 0
    && BASE_DEFS.some((d) => d.name === goal.a.name + ".bind") && BASE_DEFS.some((d) => d.name === goal.a.name + ".pure") ? goal : null;
}

// leaf_text : a row's body: a nested match on the row's last binder, or
// lines — lets of its own, a lone Data binder copied reusable (+x2 = x),
// two self-calls in a parallel let — and the final value: a tail self-call
// in a loop, a do-block at a monadic goal, or any term of the goal
function leaf_text(c: Ctx, d: DefR, goal: T, env: V[], subs: V[], last: V | null, ind: string, st: DefSt): string {
  st.leaves++;
  if (last !== null && last.q === "lone" && st.depth > 0 && col_matchable(last.ty) && c.g.chance(0.3)) {
    c.feat("match-nest");
    st.depth--;
    const out = match_text(c, d, goal, [last], env, subs, ind, st);
    st.depth++;
    return out;
  }
  const wip = d.wip as NonNullable<DefR["wip"]>;
  const lines: string[] = [];
  for (let i = c.g.size(0, 0.4, 12); i > 0; i--) {
    c.feat("leaf-let");
    const t = syn_ty(c, c.g.size(0, 1, 12), Q0, { tvars: d.tps, qvars: d.qps, ivars: [], imatch: false });
    const x = bind_name(c, env);
    const plus = ty_data(t) && c.g.chance(0.3);
    lines.push((plus ? "+" : "") + x + " = {" + syn(c, t, env, st.fuel) + " : " + ty_top(t) + "}");
    env = env_bind(env, [x], [v_new(x, t, plus)]);
  }
  for (const v of env_live(env).filter((w) => w.q === "lone" && w.of === undefined && ty_data(w.ty))) {
    // (a binder an earlier re-bind shadowed is gone from env)
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
  const self_call = (): string | null => {
    const cands = wip.subs.filter((v) => v.q !== "dead");
    if (cands.length === 0) {
      return null;
    }
    const s = c.g.pick(cands);
    const saved = wip.subs.filter((v) => v !== s);
    wip.subs = [s];
    const got = call(c, d, goal, env, 1);
    wip.subs = saved;
    return got;
  };
  if (monad(c, goal) === null && wip.subs.length >= 2 && c.g.chance(0.3)) {
    const a = self_call();
    const b = self_call();
    if (a !== null && b !== null) {
      c.feat("fork");
      const plus = ty_data(goal) && c.g.chance(0.3);
      const [x, y] = bind_names(c, 2, env);
      lines.push([x, y].map((n) => (plus ? "+" : "") + n).join(" ") + " = " + gpu_mark(c, a) + " " + gpu_mark(c, b));
      env = env_bind(env, [x, y], [v_new(x, goal, plus), v_new(y, goal, plus)]);
    }
  }
  let fin = st.loop ? self_call() : null;
  const m = monad(c, goal);
  if (fin === null && m !== null && (is_t(goal, "IO") || c.g.chance(0.5))) {
    fin = do_text(c, m, env, ind, st.fuel);
  }
  fin ??= syn(c, goal, env, st.fuel);
  return lines.concat([fin]).map((l, i) => (i === 0 ? ind : "\n" + ind) + l).join("");
}

// do_text : a do-block at a monadic goal — binds drawn as values of the
// monad at element types its bind accepts (the def itself among them, so
// an IO walk recurses from inside its block), a do let, and the final
// action or return
function do_text(c: Ctx, goal: AdtT, env: V[], ind: string, fuel: number): string {
  c.feat("do-" + goal.a.name);
  const last = goal.args.length - 1;
  const need = qt_sub(goal.a.tps[last].q, new Map(goal.a.qps.map((n, i) => [n, goal.qs[i]])));
  const lines: string[] = [];
  for (let i = c.g.size(0, 1, 16); i > 0; i--) {
    const el = syn_ty(c, c.g.size(0, 1, 8), need);
    const plus = ty_data(el) && c.g.chance(0.3);
    if (plus) {
      c.feat("plus-do");
    }
    const x = bind_name(c, env);
    lines.push((plus ? "+" : "") + x + " : " + ty_grp(el) + " <- " + syn(c, { ...goal, args: goal.args.map((a, j) => j === last ? el : a), spell: undefined }, env, fuel));
    env = env_bind(env, [x], [v_new(x, el, plus)]);
  }
  if (c.s.base && c.g.chance(0.3)) {
    c.feat("do-let");
    const z = bind_name(c, env);
    lines.push("+" + z + " : U32 = " + syn(c, bt("U32"), env, fuel));
    env = env_bind(env, [z], [v_new(z, bt("U32"), true)]);
  }
  const fin = is_t(goal, "IO") && c.g.chance(0.5) ? syn(c, goal, env, fuel) : "return " + syn(c, goal.args[last], env, fuel);
  return "do " + goal.a.name + "<" + goal.qs.map(qt_str).concat(goal.args.map(ty_grp)).join(", ") + ">:" + lines.concat([fin]).map((l) => "\n" + ind + "  " + l).join("");
}

function def_new(c: Ctx, goal: T, env: V[], fuel: number): string | null {
  if (goal.k === "eql" || ty_open(goal) || c.s.mints >= c.s.maxMints) {
    return null;
  }
  c.s.mints++;
  c.feat("def");
  c = c.sub("def");
  const name = decl_name(c, "fn");
  const gen = c.g.chance(0.25) ? generalize(c, goal) : null;
  const ret = gen?.ret ?? goal;
  const qps = gen?.qps ?? [];
  const tps = gen?.tps ?? [];
  const sc: TyScope = { tvars: tps, qvars: qps, ivars: [], imatch: false };
  const ps: Param[] = [];
  const names: string[] = [...qps, ...tps.map((tp) => tp.n)];
  for (let i = c.g.size(gen === null ? 0 : 1, 1.2, 12); i > 0; i--) {
    const pn = bind_name(c, [], names);
    names.push(pn);
    // evidence about an earlier index parameter: a family at it (the def
    // is then callable at the indices whose arm has a value)
    const idxps = ps.filter((p) => p.dep === true);
    const fams = c.s.fams.filter((f) => f.done && idxps.some((p) => ty_eq(p.t, f.idx)));
    if (fams.length > 0 && c.g.chance(0.35)) {
      c.feat("dep-param");
      const f = c.g.pick(fams);
      ps.push({ q: 1, t: { k: "app", f, arg: c.g.pick(idxps.filter((p) => ty_eq(p.t, f.idx))).n as string }, n: pn });
      continue;
    }
    // the first parameter: a value of the generalized type, or the goal's
    // own type (the state a loop rebuilds)
    const t = ps.length === 0 && gen !== null ? { k: "tvar" as const, n: tps[0].n, q: tps[0].q }
      : ps.length === 0 && ret.k !== "fun" && c.g.chance(0.3) ? (c.feat("state"), ret)
      : syn_ty(c, c.g.size(0, 1, 12), Q0, sc);
    const q = c.g.wpick<BQ>([[7, 1], [2, 0], [ty_data(t) ? 3 : 0, 2]]);
    ps.push({ q: idx_type(t) && q !== 0 ? 2 : q, t, n: pn, dep: idx_type(t) && q !== 0 });
  }
  // a leading function parameter may be a template, and then so is every
  // type and quantity parameter before it
  const tm = ps.length > 0 && ps[0].t.k === "fun" && ps[0].q !== 0 && c.g.chance(0.3) ? qps.length + tps.length + 1 : 0;
  if (tm > 0) {
    c.feat("template-def");
    ps[0].q = 1;
  }
  if (ps.some((p) => p.q === 0)) {
    c.feat("erased-param");
  }
  const penv = ps.map((p, i) => {
    const v = v_new(p.n as string, p.t, p.q === 2);
    v.q = p.q === 0 ? "dead" : i === 0 && tm > 0 ? "many" : v.q;
    return v;
  });
  // the scrutinees: live matchable parameters, in order
  const depended = new Set(ps.flatMap((p) => p.t.k === "app" ? [p.t.arg] : []));
  const cols = penv.filter((v, i) => v.q !== "dead" && !(i === 0 && tm > 0) && !depended.has(v.name) && col_matchable(v.ty) && c.g.chance(0.6))
    .slice(0, c.g.size(1, 0.7, 5));
  const decs = cols.filter((v) => v.ty.k === "adt" && v.ty.a.rec);
  const dec = decs.length > 0 && c.g.chance(0.85) ? c.g.pick(decs) : null;
  const col = dec === null ? -1 : penv.indexOf(dec);
  const loop = dec !== null && c.g.chance(0.4);
  if (col >= 0 && is_t(ps[col].t, "Nat")) {
    ps[col].mask = loop ? (c.s.pure ? c.g.size(2, 20, 900) : c.g.size(200, 2000, 200000)) : 4 + c.g.int(8);
  }
  const d: DefR = { name, qps, tps, hdr: names.slice(0, qps.length + tps.length), ps, ret, tm, wip: { col, ps: penv, subs: [], calls: 0 } };
  c.s.defs.push(d);
  c.s.wips.push(d);
  const st: DefSt = { loop, dec, fuel: c.g.size(1, 2, 16), leaves: 0, cap: c.g.size(4, 12, 128), depth: c.g.size(0, 1, 6) };
  let body: string;
  try {
    body = cols.length > 0 ? match_text(c, d, ret, cols, penv, [], "  ", st) : leaf_text(c, d, ret, env_live(penv), [], null, "  ", st);
  } catch (e) {
    if (!(e instanceof Error) || !/^(no inhabitant|helper knot)/.test(e.message)) {
      throw e;
    }
    c.s.defs.splice(c.s.defs.indexOf(d), 1);
    c.s.wips.pop();
    c.s.mints--;
    return null;
  }
  c.s.wips.pop();
  const calls = (d.wip as { calls: number }).calls;
  delete d.wip;
  if (calls > 0) {
    c.feat("rec");
    c.feat(loop ? "loop" : "rec-" + head(ps[col].t));
  }
  const hdr = [...qps.map((q) => tm > 0 ? "~" + q + ": Quant" : q), ...tps.map((tp) => (tm > 0 ? "~" : "-") + tp.n + ": Kind(" + qt_bare(tp.q) + ")")];
  const params = ps.map((p, i) => (i === 0 && tm > 0 ? "~" : bq_prefix(p.q)) + p.n + ": " + ty_top(p.t));
  if (tm === 0 && hdr.length === 0 && c.g.chance(0.15)) {
    c.feat("law-def");
    // a law telescope: a pair parameter over an index may read as `for x: A
    // where B`, the def then opening the pair; a pair result as `exs`
    const rows = ps.map((p) => {
      if (p.t.k === "sig" && p.t.x !== null && p.q === 1 && c.g.chance(0.6)) {
        c.feat("law-where");
        return "  for " + p.n + ": " + ty_top(p.t.a) + " where " + ty_str(ty_tsub(p.t.b, p.t.x, p.n as string));
      }
      return "  for " + bq_prefix(p.q) + p.n + ": " + ty_top(p.t);
    });
    let claim = ty_top(ret);
    if (ret.k === "sig" && ret.x !== null && c.g.chance(0.6)) {
      c.feat("law-exs");
      rows.push("  exs " + ret.x + ": " + ty_top(ret.a));
      claim = ty_top(ret.b);
    }
    c.push("law " + name + ":\n" + rows.join("\n") + "\n  " + claim + "\n\ndef " + name + "(" + ps.map((p) => p.n).join(", ") + "):\n" + body);
  } else {
    const unsafe = c.g.chance(0.04);
    if (unsafe) {
      c.feat("unsafe");
    }
    c.push((unsafe ? "@unsafe\n" : "") + "def " + name + "(" + hdr.concat(params).join(", ") + ") -> " + ty_str(ret) + ":\n" + body);
  }
  return call(c, d, goal, env, fuel);
}

// Readers
// -------
// rd(c, t, x): an expression folding x into a U32 — every live part of it
// observed, so a divergence anywhere in a value reaches the printed line.
// A U32 is its own reading; a transparent type is read by a def matching
// its constructors (rd_def); an opaque one through a call of the registry
// that takes it and answers something else (F32.to_u32, Array.size, ...);
// a family at an index term through the family's reader. A reading that
// would call back into a reader still being drawn is a constant: the value
// is dropped (the system is affine).

function rd(c: Ctx, t: T, x: string): string {
  if (is_t(t, "U32")) {
    return x;
  }
  if (t.k === "app" && !idx_is_lit(t.f.idx, t.arg)) {
    return rd_fam(c, t.f) + "(" + t.arg + ", " + x + ")";
  }
  try {
    return rd_def(c, t) + "(" + x + ")";
  } catch (e) {
    if (e instanceof Error && /^(helper knot|no inhabitant)/.test(e.message)) {
      return "{" + String(1 + c.g.int(99)) + " : U32}";
    }
    throw e;
  }
}

function rd_def(c: Ctx, t: T): string {
  return helper(c, "rd:" + (c.s.pure ? "p:" : "x:") + ty_key(t), "rd", (c, name) => {
    const [arg, a, b] = bind_names(c, 3);
    const salt = String(1 + c.g.int(99));
    const def1 = (body: string): string => "def " + name + "(" + arg + ": " + ty_top(t) + ") -> U32:\n  " + body;
    switch (t.k) {
      case "sig": {
        // a witness re-binds reusable: read on its own, added into the
        // evidence's read, and named in the evidence's type
        if (t.x !== null) {
          const ev = bind_name(c, [], [arg, t.x]);
          return def1("(+" + t.x + ", " + ev + ") = " + arg + "\n  " + rd_arm(c, t.b, ev, "  ", null, rd(c, t.a, t.x)));
        }
        const plus = ty_data(t.a) && c.g.chance(0.3);
        if (plus) {
          c.feat("plus-tup");
        }
        return def1("(" + (plus ? "+" : "") + a + ", " + b + ") = " + arg + "\n  (" + rd(c, t.a, a) + " + " + rd(c, t.b, b) + " : U32)");
      }
      case "fun": return def1(ty_inh(t.dom) ? rd(c, t.cod, arg + "(" + syn(c, t.dom, [], 1) + ")") : salt);
      case "app": return def1(rd_fam(c, t.f) + "(" + t.arg + ", " + arg + ")");
      case "adt": {
        if (t.a.ctors === null) {
          return def1(observe(c, t, arg) ?? salt);
        }
        const rows = t.a.ctors.map((ct) => {
          const fs = ctor_fields(t, ct);
          const vs = bind_names(c, fs.length, [], [arg]);
          const parts = fs.flatMap((f, i) => f.q === 0 || f.t.k === "tvar" ? [] : [ty_eq(f.t, t) ? name + "(" + vs[i] + ")" : rd(c, f.t, vs[i])]);
          return "    case " + ct.name + "{" + vs.join(", ") + "}:\n      " + num_combine(c, parts.concat([u32_lit(c)]));
        });
        return def1("match " + arg + ":" + rows.map((r) => "\n" + r).join(""));
      }
      default: return def1(salt);
    }
  }, (name) => c.s.defs.push({ name, qps: [], tps: [], hdr: [], ps: [{ q: 1, t, n: "x" }], ret: bt("U32"), tm: 0 }));
}

// observe : an opaque value read through a call that takes it and answers
// another closed type (null when the registry holds none); the leftover
// variables of the call draw fresh
function observe(c: Ctx, t: AdtT, x: string): string | null {
  const cands = c.g.shuffle(visible(c, []).flatMap((d) => d.base !== true ? [] : d.ps.flatMap((p, i) => p.q === 1 && ty_unify(p.t, t, new Map(), new Map()) ? [{ d, i }] : [])));
  for (const { d, i } of cands.slice(0, 4)) {
    const m = new Map<string, T>();
    const qm = new Map<string, QT>();
    ty_unify(d.ps[i].t, t, m, qm);
    d.qps.forEach((q) => qm.has(q) || qm.set(q, c.g.chance(0.5) ? Q1 : Q2));
    d.tps.forEach((tp) => m.has(tp.n) || m.set(tp.n, syn_ty(c, 1, qt_sub(tp.q, qm))));
    const ret = ty_sub(d.ret, m, qm);
    const got = ty_open(ret) || ty_eq(ret, t) ? null : call(c, d, ret, [], 2, { fixed: new Map([[i, x]]), m, qm, plain: true });
    if (got !== null) {
      c.feat("observe");
      return rd(c, ret, got);
    }
  }
  return null;
}

// rd_arm : the body reading x at a type that may mention an index term,
// inline (no def is minted under the index, so nothing recurses back into
// the family's reader): a pair destructures, a function applies, a
// non-recursive datatype matches (the tail of the body; a constructor of
// one field reads it as a tail again), the family at the index calls its
// reader, a closed type its own; what has no inline reading is dropped.
// rebind: the arm's sub-index re-bind, after the destructures; plus: an
// addend of every final expression (a witness's read).
function rd_arm(c: Ctx, t: T, x: string, ind: string, rebind: string | null = null, plus: string | null = null): string {
  const pre: string[] = [];
  const extra: string[] = plus === null ? [] : [plus];
  const add = (e: string): string => extra.length === 0 ? e : "(" + [e, ...extra].join(" + ") + " : U32)";
  const destructure = (t2: SigT, x2: string): [string, string] => {
    const [a, b] = bind_names(c, 2, [], [x2]);
    const w = t2.x ?? a;
    pre.push("(" + (t2.x !== null ? "+" : "") + w + ", " + b + ") = " + x2);
    return [w, b];
  };
  const flat = (t2: T, x2: string): string => {
    if (!ty_open(t2) || t2.k === "app") {
      return rd(c, t2, x2);
    }
    if (t2.k === "sig") {
      const [a, b] = destructure(t2, x2);
      return "(" + flat(t2.a, a) + " + " + flat(t2.b, b) + " : U32)";
    }
    // an application is read whole, or dropped: a destructure takes a
    // parameter or a field, not a computed value
    if (t2.k === "fun" && ty_inh(t2.dom) && (!ty_open(t2.cod) || t2.cod.k === "app")) {
      return rd(c, t2.cod, x2 + "(" + syn(c, t2.dom, [], 1) + ")");
    }
    return String(1 + c.g.int(99));
  };
  const tail = (t2: T, x2: string, ind2: string): string => {
    if (t2.k === "sig" && t2.x !== null && ty_open(t2)) {
      const [w, b] = destructure(t2, x2);
      extra.push(flat(t2.a, w));
      return tail(t2.b, b, ind2);
    }
    if (t2.k === "adt" && t2.a.ctors !== null && t2.a.ctors.length > 0 && !t2.a.rec && ty_open(t2)) {
      const rows = t2.a.ctors.map((ct) => {
        const fs = ctor_fields(t2, ct);
        const vs = bind_names(c, fs.length, [], [x2]);
        const live = fs.flatMap((f, i) => f.q === 0 ? [] : [i]);
        const body = ind2 + "    ";
        if (live.length === 1) {
          return ind2 + "  case " + ct.name + "{" + vs.join(", ") + "}:\n" + body + rd_arm(c, fs[live[0]].t, vs[live[0]], body, rebind, extra.length === 0 ? null : extra.join(" + "));
        }
        const saved = pre.splice(0);
        const parts = live.map((i) => flat(fs[i].t, vs[i])).concat([String(1 + c.g.int(99))]);
        const lines = pre.splice(0).concat(rebind === null ? [] : [rebind]);
        pre.push(...saved);
        return ind2 + "  case " + ct.name + "{" + vs.join(", ") + "}:\n" + lines.map((l) => body + l + "\n").join("") + body + add("(" + parts.join(" + ") + " : U32)");
      });
      return "match " + x2 + ":\n" + rows.join("\n");
    }
    return flat(t2, x2);
  };
  const e = tail(t, x, ind);
  // a match tail carries the re-bind and the addend in its arms; a flat
  // one takes them last
  return pre.map((l) => l + "\n" + ind).join("") + (e.startsWith("match ") ? e : (rebind === null ? "" : rebind + "\n" + ind) + add(e));
}

// num_combine : U32 expressions folded into one, as a balanced tree (a
// long run of statements stays shallow); a single element gets a neutral
// +0 so a bare literal cannot be the whole answer
function num_combine(c: Ctx, es: string[]): string {
  if (es.length <= 1) {
    return "(" + (es[0] ?? u32_lit(c)) + " + 0 : U32)";
  }
  const tree = (xs: string[]): string => xs.length === 1 ? xs[0]
    : "(" + tree(xs.slice(0, xs.length >> 1)) + " " + c.g.pick(["+", "-", "*", ".^.", "+", "+"]) + " " + tree(xs.slice(xs.length >> 1)) + " : U32)";
  return tree(es);
}

// num_seal : one of six exact U32 identities over the raw result's name
function num_seal(c: Ctx, e: string): string {
  const k = u32_lit(c);
  const op = (a: string, o: string, b: string): string => "(" + a + " " + o + " " + b + " : U32)";
  return c.g.pick<() => string>([
    () => (c.feat("seal-add"), op(op(e, "+", k), "-", k)),
    () => (c.feat("seal-xor"), op(op(e, ".^.", k), ".^.", k)),
    () => (c.feat("seal-dist"), op(e, "+", op(op(op(e, "+", e), "*", e), "-", op(op(e, "*", e), "+", op(e, "*", e))))),
    () => (c.feat("seal-mask"), op(op(e, ".&.", k), ".|.", op(e, ".&.", "U32.not(" + k + ")"))),
    () => {
      c.feat("seal-cmp");
      const cmp = "Bool.to_u32(" + op(e, "<=", k) + ")";
      return op(e, ".^.", op(cmp, ".^.", cmp));
    },
    () => {
      c.feat("seal-rot");
      const n = 1 + c.g.int(31);
      const [l, r] = [String(n) + "n", String(32 - n) + "n"];
      const rot = op(op(e, "<<", l), ".|.", op(e, ">>", r));
      return op(op(rot, ">>", l), ".|.", op(rot, "<<", r));
    },
  ])();
}

// Statements
// ----------
// A result or extra def is a run of statements, each binding names the
// fold reads. Three productions make them: a value of any type, read to a
// U32 (a U32 is its own reading, a call may carry a ! mark); a parallel
// let, the one fork shape; and a proof, an equation rewritten on or left
// bound.

// Line : a statement's text, the names the fold reads (binds), every name
// it binds (bound), and the binders later lines may use (vars)
type Line = { text: string; binds: string[]; bound: string[]; vars: V[] };

// let_value : a value of a drawn type bound (annotated: an intro-headed
// value does not infer in a bare let) and read; a Data value may stay in
// scope under a + binder, or be read twice
function let_value(c: Ctx, env: V[]): Line {
  const t = c.s.base && c.g.chance(0.3) ? bt("U32") : syn_ty(c, c.g.size(0, 1.5, 24), Q0);
  const fuel = c.g.size(1, 3, 48);
  const x = bind_name(c, env);
  const keep = c.g.chance(0.55);
  if (is_t(t, "U32")) {
    const e = gpu_mark(c, syn(c, t, env, fuel));
    return { text: (keep ? "+" : "") + x + " = " + (/^[A-Za-z_][\w.]*!?\(/.test(e) ? e : "{" + e + " : U32}"), binds: [x], bound: [x], vars: keep ? [v_new(x, t, true)] : [] };
  }
  c.feat("value");
  const y = bind_name(c, env, [x]);
  const plus = ty_data(t) && c.g.chance(0.4);
  const twice = plus && c.g.chance(0.3);
  const lines = [(plus ? "+" : "") + x + " = {" + syn(c, t, env, fuel) + " : " + ty_top(t) + "}"];
  if (twice) {
    c.feat("dup");
  }
  lines.push((keep ? "+" : "") + y + " = " + (twice ? "(" + rd(c, t, x) + " + " + rd(c, t, x) + " : U32)" : rd(c, t, x)));
  return { text: lines.join("\n  "), binds: [y], bound: [x, y], vars: [...keep ? [v_new(y, bt("U32"), true)] : [], ...plus && !twice ? [v_new(x, t, true)] : []] };
}

// let_fork : a parallel let over saturated calls (a ! at times) and
// U32 binders in scope as riders; a rider must be a bare binder (a
// parenthesized one would glue onto the call before it)
function let_fork(c: Ctx, env: V[]): Line {
  c.feat("fork");
  const vals: string[] = [];
  for (let i = c.g.size(2, 1, 16); i > 0; i--) {
    try {
      const e = def_new(c, bt("U32"), env, c.g.size(1, 2, 16)) ?? call_unify(c, bt("U32"), env, c.g.size(1, 2, 16), { plain: true });
      if (e !== null && /^[A-Za-z_][\w.]*\(/.test(e)) {
        vals.push(gpu_mark(c, e));
      }
    } catch (e) {
      if (!(e instanceof Error) || !/^(no inhabitant|helper knot)/.test(e.message)) {
        throw e;
      }
    }
  }
  const nums = env_live(env, (t) => is_t(t, "U32"));
  for (let i = c.g.chance(0.3) ? 1 + c.g.int(2) : 0; i > 0 && nums.length > 0; i--) {
    vals.push(env_take(c.g.pick(nums)));
  }
  if (vals.length === 0) {
    return let_value(c, env);
  }
  const ks = bind_names(c, vals.length, env);
  // a + per name re-binds the fork's results reusable (+a +b = f g)
  const plus = c.g.chance(0.3);
  if (plus) {
    c.feat("plus-par");
  }
  return { text: ks.map((k) => (plus ? "+" : "") + k).join(" ") + " = " + c.g.shuffle(vals).join(" "), binds: ks, bound: ks, vars: plus ? ks.map((k) => v_new(k, bt("U32"), true)) : [] };
}

// Proofs : an equation bound by a proof term, then rewritten on with a
// constant motive (%x : U32;) or left bound. The grammar composes:
// reflexivity over a side drawn from reusable binders (it is written
// twice), Base's U32.add_comm, a minted theorem (a Nat clone's shift law
// proved by induction), and Equal's sym, cong and trans over any of them.

type Prf = { s: string; t: string; a: string; b: string; ap?: (x: string) => string };

// theorem : a Nat clone, an op on it (op(z, b) = S^k(b), op(s{p}, b) =
// S^m(op(p, b))) and its shift law op(a, S{b}) == S{op(a, b)}, proved by
// induction, its inductive arm rewriting with the hypothesis
function theorem(c: Ctx): Prf {
  c.feat("thm");
  const N = decl_name(c, "Nt");
  const [Z, S, add, th] = [decl_name(c, N + "z"), decl_name(c, N + "s"), decl_name(c, "ad"), decl_name(c, "th")];
  const [a, b, p, f] = bind_names(c, 4);
  c.push("type " + N + " is Data:\n  " + Z + "{}\n  " + S + "{" + f + ": " + N + "}");
  const k = c.g.int(3);
  const m = 1 + c.g.int(2);
  const wrap = (n: number, x: string): string => n === 0 ? x : wrap(n - 1, S + "{" + x + "}");
  c.push("def " + add + "(" + a + ": " + N + ", " + b + ": " + N + ") -> " + N + ":\n  match " + a + ":\n    case " + Z + "{}:\n      "
    + wrap(k, b) + "\n    case " + S + "{" + p + "}:\n      " + wrap(m, add + "(" + p + ", " + b + ")"));
  c.push("def " + th + "(" + a + ": " + N + ", -" + b + ": " + N + ") -> {" + add + "(" + a + ", " + S + "{" + b + "}) == " + S + "{" + add + "(" + a + ", " + b + ")} : " + N + "}:\n"
    + "  match " + a + ":\n    case " + Z + "{}:\n      {==}\n    case " + S + "{" + p + "}:\n      %" + th + "(" + p + ", " + b + ") : {"
    + wrap(m, add + "(" + p + ", " + S + "{" + b + "})") + " == " + wrap(m - 1, S + "{_}") + " : " + N + "};\n      {==}");
  const x = wrap(1 + c.g.int(3), Z + "{}");
  const y = wrap(c.g.int(2), Z + "{}");
  return { s: th + "(" + x + ", " + y + ")", t: N, a: add + "(" + x + ", " + S + "{" + y + "})", b: S + "{" + add + "(" + x + ", " + y + ")}", ap: (v) => S + "{" + v + "}" };
}

function proof(c: Ctx, env: V[], depth: number): Prf {
  if (depth > 0 && c.g.chance(0.5)) {
    const p = proof(c, env, depth - 1);
    return c.g.wpick<() => Prf>([
      [3, () => (c.feat("eq-sym"), { ...p, s: "Equal.sym(" + [p.t, p.a, p.b, p.s].join(", ") + ")", a: p.b, b: p.a })],
      [p.ap !== undefined ? 3 : 0, () => {
        c.feat("eq-cong");
        const w = bind_name(c, env);
        const f = p.ap as (x: string) => string;
        return { ...p, s: "Equal.cong(" + [p.t, p.t, w + " => " + f(w), p.a, p.b, p.s].join(", ") + ")", a: f(p.a), b: f(p.b) };
      }],
      [2, () => (c.feat("eq-trans"), { ...p, s: "Equal.trans(" + [p.t, p.a, p.b, p.b, p.s, "{==}"].join(", ") + ")" })],
    ])();
  }
  return c.g.wpick<() => Prf>([
    [4, () => {
      c.feat("eql");
      const t = c.g.pick(["U32", "Nat", "Bool"]);
      const side = syn(c, bt(t), env_live(env).filter((v) => v.q === "many"), c.g.size(0, 2, 8));
      const ap: Record<string, (x: string) => string> = { U32: (x) => "U32.inc(" + x + ")", Nat: (x) => "Nat.double(" + x + ")", Bool: (x) => "Bool.not(" + x + ")" };
      return { s: "{==}", t, a: side, b: side, ap: ap[t] };
    }],
    [3, () => {
      c.feat("eqkit");
      const [a, b] = [u32_lit(c), u32_lit(c)];
      return { s: "U32.add_comm(" + a + ", " + b + ")", t: "U32", a: "U32.add(" + a + ", " + b + ")", b: "U32.add(" + b + ", " + a + ")", ap: (x) => "(" + x + " + " + b + " : U32)" };
    }],
    [2, () => theorem(c)],
  ])();
}

function let_proof(c: Ctx, env: V[]): Line {
  // the proof binder is internal to the statement: it must not shadow a
  // value that later statements still fold
  const x = bind_name(c, []);
  const p = proof(c, env, c.g.size(0, 1, 6));
  const lines = [x + " = {" + p.s + " : {" + p.a + " == " + p.b + " : " + p.t + "}}"];
  if (!c.g.chance(0.6)) {
    return { text: lines[0], binds: [], bound: [x], vars: [] };
  }
  c.feat("rwt");
  const w = bind_name(c, env, [x]);
  lines.push("%" + x + " : U32;", w + " = {" + syn(c, bt("U32"), env, c.g.size(1, 2, 16)) + " : U32}");
  return { text: lines.join("\n  "), binds: [w], bound: [x, w], vars: [] };
}

// lines_gen : n statements drawn from a production table, binding into
// env; a name a line binds shadows the binder of that name in scope, and a
// result the fold would read is dropped when a later line rebinds its name
function lines_gen(c: Ctx, kit: Array<[number, (c: Ctx, env: V[]) => Line]>, label: string, n: number, env: V[]): Line[] {
  const lines: Line[] = [];
  for (let i = 0; i < n; i++) {
    const line = c.g.wpick(kit)(c.sub(label), env);
    for (const v of env) {
      if (line.bound.includes(v.name)) {
        v.q = "dead";
      }
    }
    env.push(...line.vars);
    lines.push(line);
  }
  return lines.map((l, i) => ({ ...l, binds: l.binds.filter((b) => !lines.slice(i + 1).some((m) => m.bound.includes(b))) }));
}

// Members
// -------
// A member is one seed's program pieces, position-independent so a batched
// member and its solo re-run draw identically at their own uid base, kept
// as parts (entries, the result statements with their fold and seal, the
// extra statements, the IO tail, the effect) so the reducer can drop
// pieces and member_defs re-renders the rest.

// out lines: a string is generator-known; null is deterministic but only
// cross-leg comparable (platform errno text lengths, file offsets)
type IoTail = { lines: string[]; out: Array<string | null>; err: string[]; code: number };

type Member = {
  seed: bigint;
  prof: Profile;
  resultName: string;
  rawName: string;
  res: string;
  lines: Line[];
  fold: string;
  seal: string;
  extraName: string | null;
  xlines: Line[];
  xfold: string;
  tail: IoTail | null;
  show: { ty: string; t: T; val: string } | null;
  entries: string[];
  feats: string[];
  trans: boolean;
  eff: Eff | null;
};

// Profile : what a seed's program is, drawn from the seed alone so a solo
// re-run reproduces it. base: Base in the initial environment; free:
// unrestricted declaration names; show: a pure main printed as its literal
// (always so without Base: IO is Base's); file: the member sits in a file of
// its own, else inline in the entry; effect: a foreign effect of its own;
// clash: also checked as a program that must be refused; io: an IO tail;
// die: the tail ends in IO.die (the member runs last in its group);
// surface: the chance per synthesis node of a surface wrapper.
type Profile = { base: boolean; free: boolean; show: boolean; file: boolean; effect: boolean; clash: boolean; io: boolean; die: boolean; surface: number };

function profile(seed: bigint): Profile {
  const g = new Gen(rng_mix64(seed ^ 0x70f1en));
  const base = g.chance(0.88);
  const show = !base || g.chance(0.08);
  const io = base && !show && g.int(100) < IO_PCT;
  return {
    base,
    free: g.chance(0.2),
    show,
    file: g.chance(0.25),
    effect: base && !show && g.chance(0.25),
    clash: !show && g.chance(0.15),
    io,
    die: io && g.chance(0.18),
    surface: g.wpick<number>([[2, 0], [3, 0.02], [3, 0.08], [2, 0.2]]),
  };
}

// standalone : a seed that owns its whole program — a pure main, an empty
// initial environment, or free names inline in the entry (in a file of its
// own they are namespaced apart)
function standalone(seed: bigint): boolean {
  const p = profile(seed);
  return p.show || !p.base || (p.free && !p.file);
}

function gen_member(seed: bigint, uid0 = 0): Member {
  const prof = profile(seed);
  const c = ctx_new(seed, uid0, prof);
  c.feat(prof.base ? "with-base" : "no-base");
  for (let i = c.g.size(prof.base ? 0 : 1, 1, 24); i > 0; i--) {
    adt_new(c.sub("adt"));
  }
  // families after the datatypes (an arm may use them), then datatypes
  // after the families (a field may apply one)
  const nfams = c.g.size(0, 0.4, 8);
  for (let i = 0; i < nfams; i++) {
    fam_new(c.sub("fam"));
  }
  for (let i = nfams > 0 ? c.g.size(0, 0.5, 8) : 0; i > 0; i--) {
    adt_new(c.sub("adt"));
  }
  const member = (m: Partial<Member>): Member => ({
    seed, prof, resultName: "", rawName: "", res: "", lines: [], fold: "", seal: "", extraName: null, xlines: [], xfold: "",
    tail: null, show: null, eff: null, ...m, entries: c.s.entries.slice(), feats: Object.keys(c.s.feat), trans: c.s.trans,
  });
  if (prof.show) {
    c.feat("show");
    const sc = c.sub("show");
    let t: T = prof.base ? bt("U32") : inst(c.s.adts[0]);
    for (let i = 0; i < 8; i++) {
      const u = syn_ty(sc, sc.g.size(0, 1.5, 16), Q0);
      if (ty_showable(u) && ty_inh(u) && !ty_open(u)) {
        t = u;
        break;
      }
    }
    c.feat("show-" + head(t));
    const val = syn(c.sub("show"), t, [], c.g.size(1, 3, 48));
    return member({ show: { ty: t.k === "sig" ? "(" + ty_str(t) + ")" : ty_str(t), t, val } });
  }
  // the statement table, reshaped per seed (swarm) so a rare production
  // gets seeds where it dominates; result is the interpreter-visible side,
  // extra the compiled-only one (F32, forks, long loops)
  const kit = (pure: boolean): Array<[number, (c: Ctx, env: V[]) => Line]> => {
    const k: Array<[number, (c: Ctx, env: V[]) => Line]> = [[60, let_value], [pure ? 16 : 25, let_fork], [pure ? 12 : 5, let_proof]];
    const swarm = k.map(([w, f]): [number, (c: Ctx, env: V[]) => Line] => [w * c.g.wpick<number>([[20, 0], [45, 1], [20, 2], [15, 4]]), f]);
    return swarm.some(([w]) => w > 0) ? swarm : k;
  };
  const fold = (label: string, lines: Line[], env: V[]): string =>
    num_combine(c.sub(label), [...new Set(lines.flatMap((l) => l.binds))].concat([syn(c.sub(label), bt("U32"), env, 2)]));
  const env: V[] = [];
  const lines = lines_gen(c, kit(true), "res", c.g.size(1, 3, 64), env);
  const res = bind_name(c, env);
  const rfold = fold("fold", lines, env);
  const seal = num_seal(c.sub("seal"), res);
  const resultName = decl_name(c, "rs");
  const rawName = decl_name(c, "rw");
  c.s.pure = false;
  let extraName: string | null = null;
  let xlines: Line[] = [];
  let xfold = "";
  if (c.g.chance(0.9)) {
    extraName = decl_name(c, "xt");
    const xenv: V[] = [];
    xlines = lines_gen(c, kit(false), "extra", c.g.size(1, 2, 64), xenv);
    xfold = fold("xfold", xlines, xenv);
  }
  c.s.pure = true;
  const tail = prof.io ? io_tail(c.sub("io"), seed, prof.die) : null;
  const eff = prof.effect ? eff_new(c.sub("eff"), seed) : null;
  return member({ resultName, rawName, res, lines, fold: rfold, seal, extraName, xlines, xfold, tail, eff });
}

// member_defs : the member's own defs — result (sealed), the raw sibling
// when asked, and extra — rendered after its entries
function member_defs(m: Member, raw: boolean, main = "main"): string[] {
  if (m.show !== null) {
    return ["def " + main + "() -> " + m.show.ty + ":\n  " + m.show.val];
  }
  const head = m.lines.map((l) => l.text).concat(["+" + m.res + " = " + m.fold]).join("\n  ");
  const def = (name: string, ret: string): string => "def " + name + "() -> U32:\n  " + head + "\n  " + ret;
  return [def(m.resultName, m.seal), ...raw ? [def(m.rawName, "(" + m.res + " + 0 : U32)")] : [],
    ...m.extraName !== null ? ["def " + m.extraName + "() -> U32:\n  " + m.xlines.map((l) => l.text).concat([m.xfold]).join("\n  ")] : []];
}

// member_drop : the member without statement i of lines/xlines; the
// dropped binds read as 0 wherever the rest mentioned them
function member_drop(m: Member, which: "lines" | "xlines", i: number): Member {
  const gone = m[which][i].binds;
  const zero = (t: string): string => gone.reduce((acc, b) => acc.replace(new RegExp("\\b" + b + "\\b", "g"), "0"), t);
  const rest = m[which].filter((_, j) => j !== i).map((l) => ({ ...l, text: zero(l.text) }));
  return which === "lines" ? { ...m, lines: rest, fold: zero(m.fold) } : { ...m, xlines: rest, xfold: zero(m.xfold) };
}

// IO tail
// -------
// A deterministic IO sequence in main: a print (a bind, a bare step, or two
// steps joined by ;), a file roundtrip in the run's cwd read back as text or
// as bytes, get_env of an unset name, print_err, an IO def of the program's
// own, the async walk, and rarely an IO.die whose exit code is the
// assertion. Its expectations are known to the generator, or cross-leg
// only where platform text or file offsets ride in.

function io_tail(c: Ctx, seed: bigint, die: boolean): IoTail {
  c.feat("io-tail");
  const id = String(c.uid());
  const key = (seed & 0xffffffn).toString(16);
  const lines: string[] = [];
  const out: Array<string | null> = [];
  const err: string[] = [];
  const RES = (t: string): string => "Result<&1, &1, U32 & String, " + t + ">";
  if (c.g.chance(0.5)) {
    const msg = "fz_" + key + "_" + String(c.g.int(1000));
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
    const fn = "fzf_" + key + ".txt";
    const txt = "data".repeat(1 + c.g.int(4)) + String(c.g.int(100));
    // the read back as text (File.read) or as bytes (File.read_bytes)
    const bytes = c.g.chance(0.4);
    if (bytes) {
      c.feat("read-bytes");
    }
    const rdT = bytes ? "List<&2, U32>" : "String";
    const [f, r, s, e, cd, m, u, rb] = bind_names(c, 8);
    const rk = decl_name(c, "fr");
    c.push("def " + rk + "(fr: File & " + RES(rdT) + ") -> IO(U32):\n"
      + "  (" + f + ", " + r + ") = fr\n  match " + r + ":\n    case Done{" + s + "}:\n      do IO<U32>:\n        " + u + " : Unit <- File.close(" + f + ")\n"
      + "        IO.pure(U32, " + rd(c, bytes ? t_list(Q2, bt("U32")) : bt("String"), s) + ")\n"
      + "    case Fail{" + e + "}:\n      (" + cd + ", " + m + ") = " + e + "\n      do IO<U32>:\n        " + u + " : Unit <- File.close(" + f + ")\n"
      + "        IO.pure(U32, (" + cd + " + " + rd(c, bt("String"), m) + " : U32))");
    const wk = decl_name(c, "fw");
    c.push("def " + wk + "(fr: File & " + RES("Unit") + ") -> IO(U32):\n"
      + "  (" + f + ", " + r + ") = fr\n  match " + r + ":\n    case Done{" + u + "}:\n      do IO<U32>:\n        " + rb + " : File & " + RES(rdT) + " <- "
      + (bytes ? "File.read_bytes" : "File.read") + "(" + f + ", 4096)\n        " + rk + "(" + rb + ")\n"
      + "    case Fail{" + e + "}:\n      (" + cd + ", " + m + ") = " + e + "\n      do IO<U32>:\n        " + u + " : Unit <- File.close(" + f + ")\n        IO.pure(U32, " + cd + ")");
    const io = decl_name(c, "fio");
    const try_ = c.g.chance(0.5);
    if (try_) {
      c.feat("io-try");
    }
    c.push("def " + io + "() -> IO(U32):\n  do IO<U32>:\n"
      + (try_ ? "    " + f + " : File <- IO.try(File, File.open(\"" + fn + "\", \"w\"))\n"
        : "    " + r + " : " + RES("File") + " <- File.open(\"" + fn + "\", \"w\")\n    " + f + " : File <- IO.pass(File, " + r + ")\n")
      + "    " + rb + " : File & " + RES("Unit") + " <- File.write(" + f + ", \"" + txt + "\")\n    " + wk + "(" + rb + ")");
    lines.push("t" + id + "b : U32 <- " + io + "()", "t" + id + "c : Unit <- IO.print(U32.show(t" + id + "b))");
    // the read-after-write offset behavior is deterministic per backend
    // pair but not generator-predictable: cross-leg comparison only
    out.push(null);
  }
  if (c.g.chance(0.4)) {
    c.feat("get-env");
    const [r, s, e, cd, m] = bind_names(c, 5);
    const ek = decl_name(c, "ge");
    c.push("def " + ek + "(" + r + ": " + RES("String") + ") -> U32:\n  match " + r + ":\n"
      + "    case Done{" + s + "}:\n      " + rd(c, bt("String"), s) + "\n    case Fail{" + e + "}:\n      (" + cd + ", " + m + ") = " + e + "\n      (" + cd + " + " + String(c.g.int(64)) + " : U32)");
    lines.push("t" + id + "d : " + RES("String") + " <- IO.get_env(\"FZ_UNSET_" + String(c.g.int(1000)) + "\")",
      "t" + id + "e : Unit <- IO.print(U32.show(" + ek + "(t" + id + "d)))");
    // the errno/strerror pair of an unset name is platform text
    out.push(null);
  }
  if (c.g.chance(0.4)) {
    c.feat("print-err");
    const msg = "fzerr_" + key + "_" + String(c.g.int(1000));
    lines.push("t" + id + "f : Unit <- IO.print_err(\"" + msg + "\")");
    err.push(msg);
  }
  if (c.g.chance(0.5)) {
    const e = def_new(c.sub("iodef"), inst(BASE_ADTS.get("IO") as Adt, [], [bt("U32")]), [], 2);
    if (e !== null) {
      c.feat("io-def");
      lines.push("t" + id + "g : U32 <- " + e, "t" + id + "h : Unit <- IO.print(U32.show(t" + id + "g))");
      out.push(null);
    }
  }
  if (c.g.chance(0.6)) {
    c.feat("async");
    for (let i = c.g.size(1, 0.5, 4); i > 0; i--) {
      const sc = async_walk(c.sub("async"), key);
      const v = "t" + id + "x" + String(i);
      lines.push(v + " : U32 <- " + sc.name + "()", "t" + id + "y" + String(i) + " : Unit <- IO.print(U32.show(" + v + "))");
      out.push(...sc.prints, sc.value === null ? null : String(sc.value));
    }
  }
  if (die) {
    c.feat("io-die");
    err.push("fzdie_" + key);
  }
  return { lines, out, err, code: die ? 1 + c.g.int(200) : 0 };
}

// The async walk
// --------------
// One scenario is a random walk of a do-block over an async state: fibers
// forked (a value, a sleep then a value, a computation of the program's
// that may carry a `!`, or a producer that sends known values into a
// channel) and joined, producers spawned and detached, channels received
// from, the clock read, a group of timers registered in deadline order (the
// loop stamps each timer with a strictly later deadline). A model keeps the
// answer schedule-independent: a value received from a channel with one
// outstanding sender is its FIFO prefix, with several the whole pending
// multiset summed; a producer is joined only once its sends are received
// (else a full channel deadlocks the join); the epilogue receives
// everything pending, closes every channel and joins every fiber. Only
// timer pings print, and main prints after joining them. The answer is the
// sum of every number the walk holds: known unless a computation rode in.

type Scen = { name: string; prints: string[]; value: bigint | null };
type AProd = { chan: AChan; left: number };
type AChan = { name: string; open: boolean; queue: Array<{ v: bigint; p: AProd }>; prods: AProd[] };
type AWalk = { c: Ctx; key: string; id: string; rows: string[]; fibers: Array<{ name: string; v: bigint | null; prod: AProd | null }>; chans: AChan[]; nums: Array<{ name: string; v: bigint | null }>; prints: string[]; n: number };

const M32 = 0xffffffffn;

function a_name(w: AWalk, stem: string): string {
  return stem + w.id + "_" + String(w.n++);
}

// a_ping : a def that sleeps ms, prints tag when given, answers v
function a_ping(w: AWalk, ms: number, tag: string | null, v: string): string {
  const n = a_name(w, "fzp");
  const [u, x] = bind_names(w.c, 2);
  w.c.push("def " + n + "() -> IO(U32):\n  do IO<U32>:\n    " + u + " : Unit <- IO.sleep(" + String(ms) + ")\n"
    + (tag === null ? "" : "    " + x + " : Unit <- IO.print(\"" + tag + "\")\n") + "    IO.pure(U32, " + v + ")");
  return n + "()";
}

function a_fork(w: AWalk, act: string, v: bigint | null, prod: AProd | null = null): void {
  const name = a_name(w, "t");
  w.rows.push(name + " : Chan(U32) <- IO.fork(U32, " + act + ")");
  w.fibers.push({ name, v, prod });
}

function a_num(w: AWalk, v: bigint | null, row: (name: string) => string): void {
  const name = a_name(w, "v");
  w.rows.push(row(name));
  w.nums.push({ name, v });
}

// a_producer : a def that sends k literal values into its channel and
// answers k; the model queues the values behind the channel's others
function a_producer(w: AWalk, ch: AChan): { act: string; prod: AProd; k: number } {
  const k = w.c.g.size(1, 2, 16);
  const vals = Array.from({ length: k }, () => BigInt(w.c.g.int(100000)));
  const def = a_name(w, "fzs");
  const [channel, shared, ...sent] = bind_names(w.c, 2 + k);
  w.c.push("def " + def + "(" + channel + ": Chan(U32)) -> IO(U32):\n  +" + shared + " = " + channel + "\n  do IO<U32>:\n"
    + vals.map((v, j) => "    " + sent[j] + " : Bool <- Chan.send(U32, " + shared + ", " + String(v) + ")").join("\n")
    + "\n    IO.pure(U32, " + String(k) + ")");
  const prod: AProd = { chan: ch, left: k };
  ch.queue.push(...vals.map((v) => ({ v, p: prod })));
  ch.prods.push(prod);
  return { act: def + "(" + ch.name + ")", prod, k };
}

// a_recv : receives folded into one number: the FIFO prefix when every
// pending value is one producer's, else everything pending
function a_recv(w: AWalk, ch: AChan, all: boolean): void {
  const n = all || new Set(ch.queue.map((q) => q.p)).size > 1 ? ch.queue.length : 1 + w.c.g.int(ch.queue.length);
  if (n === 0) {
    return;
  }
  const ms = Array.from({ length: n }, () => {
    const m = a_name(w, "m");
    w.rows.push(m + " : Maybe<&1, U32> <- Chan.recv(U32, " + ch.name + ")");
    return "Maybe.default(&1, U32, " + m + ", 0)";
  });
  const got = ch.queue.splice(0, n);
  got.forEach((q) => {
    q.p.left -= 1;
  });
  a_num(w, got.reduce((a, q) => (a + q.v) & M32, 0n), (name) => name + " : U32 <- IO.pure(U32, (" + ms.join(" + ") + " : U32))");
}

function a_join(w: AWalk, f: AWalk["fibers"][number]): void {
  w.fibers.splice(w.fibers.indexOf(f), 1);
  a_num(w, f.v, (name) => name + " : U32 <- IO.join(U32, " + f.name + ")");
}

function a_close(w: AWalk, ch: AChan): void {
  ch.open = false;
  w.rows.push(a_name(w, "u") + " : Unit <- Chan.close(U32, " + ch.name + ")");
}

// a_step : one statement of the walk, drawn from what the state allows
function a_step(w: AWalk): void {
  const c = w.c;
  const open = w.chans.filter((ch) => ch.open);
  const loaded = open.filter((ch) => ch.queue.length > 0);
  const joinable = w.fibers.filter((f) => f.prod === null || f.prod.left === 0);
  const closable = open.filter((ch) => ch.queue.length === 0 && ch.prods.every((p) => p.left === 0));
  const closed = w.chans.filter((ch) => !ch.open);
  c.g.wpick<() => void>([
    [15, () => {
      c.feat("fiber");
      const lit = c.g.int(100000);
      a_fork(w, "IO.pure(U32, " + String(lit) + ")", BigInt(lit));
    }],
    [10, () => {
      c.feat("fiber");
      const lit = c.g.int(100000);
      a_fork(w, a_ping(w, 1 + c.g.int(6), null, String(lit)), BigInt(lit));
    }],
    [8, () => {
      const e = def_new(c, bt("U32"), [], 2);
      if (e !== null) {
        c.feat("async-batch");
        a_fork(w, "IO.pure(U32, " + gpu_mark(c, e) + ")", null);
      }
    }],
    [6, () => {
      w.rows.push(a_name(w, "u") + " : Unit <- IO.sleep(" + String(1 + c.g.int(4)) + ")");
    }],
    [4, () => {
      c.feat("timer");
      const [a, b] = [a_name(w, "n"), a_name(w, "n")];
      w.rows.push(a + " : Nat <- IO.now()", a_name(w, "u") + " : Unit <- IO.sleep(" + String(1 + c.g.int(3)) + ")", b + " : Nat <- IO.now()");
      a_num(w, 1n, (name) => name + " : U32 <- IO.pure(U32, Bool.to_u32(Bool.not(Nat.is_lt(" + b + ", " + a + "))))");
    }],
    [8, () => {
      c.feat("timer");
      const base = 1 + c.g.int(4);
      const step = c.g.pick([0, 1, 2, 4]);
      const ts = Array.from({ length: c.g.size(2, 2, 16) }, (_, j) => {
        const tag = "fzt_" + w.key + "_" + w.id + "_" + String(w.n);
        const t = a_name(w, "t");
        w.rows.push(t + " : Chan(U32) <- IO.fork(U32, " + a_ping(w, base + j * step, tag, "1") + ")");
        w.prints.push(tag);
        return t;
      });
      for (const t of c.g.shuffle(ts)) {
        a_num(w, 1n, (name) => name + " : U32 <- IO.join(U32, " + t + ")");
      }
    }],
    [open.length > 0 ? 14 : 0, () => {
      c.feat("chan");
      const p = a_producer(w, c.g.pick(open));
      a_fork(w, p.act, BigInt(p.k), p.prod);
    }],
    [open.length > 0 ? 8 : 0, () => {
      c.feat("chan");
      w.rows.push(a_name(w, "u") + " : Unit <- IO.spawn(U32, " + a_producer(w, c.g.pick(open)).act + ")");
    }],
    [loaded.length > 0 ? 16 : 0, () => a_recv(w, c.g.pick(loaded), false)],
    [loaded.length > 0 ? 6 : 0, () => a_recv(w, c.g.pick(loaded), true)],
    [joinable.length > 0 ? 18 : 0, () => a_join(w, c.g.pick(joinable))],
    [closable.length > 0 ? 3 : 0, () => a_close(w, c.g.pick(closable))],
    // a receive on a closed channel answers None at once
    [closed.length > 0 ? 3 : 0, () => {
      const m = a_name(w, "m");
      w.rows.push(m + " : Maybe<&1, U32> <- Chan.recv(U32, " + c.g.pick(closed).name + ")");
      a_num(w, 0n, (name) => name + " : U32 <- IO.pure(U32, Maybe.default(&1, U32, " + m + ", 0))");
    }],
  ])();
}

function async_walk(c: Ctx, key: string): Scen {
  const id = String(c.uid());
  const w: AWalk = { c, key, id, rows: [], fibers: [], chans: [], nums: [], prints: [], n: 0 };
  for (let i = c.g.size(0, 1, 6); i > 0; i--) {
    w.chans.push({ name: "ch" + id + "_" + String(w.chans.length), open: true, queue: [], prods: [] });
  }
  for (let i = c.g.size(2, 3, 48); i > 0; i--) {
    a_step(w);
  }
  // epilogue: every channel drained and closed, every fiber joined
  for (const ch of w.chans.filter((x) => x.open)) {
    a_recv(w, ch, true);
    a_close(w, ch);
  }
  while (w.fibers.length > 0) {
    a_join(w, w.fibers[0]);
  }
  const fold = w.nums.length === 0 ? "0" : "(" + w.nums.map((x) => x.name).join(" + ") + " : U32)";
  const body = "fzb" + id;
  const cs = w.chans.map((_, i) => "c" + String(i));
  c.push("def " + body + "(" + cs.map((x) => x + ": Chan(U32)").join(", ") + ") -> IO(U32):\n" + w.chans.map((ch, i) => "  +" + ch.name + " = " + cs[i] + "\n").join("")
    + "  do IO<U32>:\n" + w.rows.concat(["IO.pure(U32, " + fold + ")"]).map((r) => "    " + r).join("\n"));
  const name = "fza" + id;
  c.push("def " + name + "() -> IO(U32):\n  do IO<U32>:\n" + cs.map((x) => "    " + x + " : Chan(U32) <- Chan.new(U32, " + String(c.g.pick([0, 1, 4])) + ")\n").join("")
    + "    " + body + "(" + cs.join(", ") + ")");
  const known = w.nums.every((x) => x.v !== null);
  return { name, prints: w.prints, value: known ? w.nums.reduce((a, x) => (a + (x.v as bigint)) & M32, 0n) : null };
}

// Effects
// -------
// A foreign effect of the member's own: a datatype with a nullary and a
// U32-field constructor, a foreign def whose .c and .js build them through
// CID(..) and register with io_eff, and a reader that prints the value.
// The names come from the member's own distribution (free names included),
// so CID resolution, the C id table, the JS tags and the registration keys
// all meet them; its files are named after the seed, so a batch's members
// keep theirs apart. calls: each call's argument and the line it prints.
type Eff = { file: string; decls: string[]; c: string; js: string; name: string; ty: string; show: string; ctors: string[]; calls: Array<[number, string]> };

function eff_new(c: Ctx, seed: bigint): Eff {
  const file = "fze" + (seed & 0xffffffffffffn).toString(16);
  const ty = decl_name(c, "ft");
  const ctors = [decl_name(c, "fk"), decl_name(c, "fk")];
  const name = decl_name(c, "fe");
  const show = decl_name(c, "fs");
  let field = identifier(c.g, 2);
  while (KEYWORDS.has(field)) {
    field = identifier(c.g, 2);
  }
  const [b, t] = bind_names(c, 2);
  c.feat("effect");
  if (c.s.free) {
    c.feat("effect-free-name");
  }
  const decls = [
    "type " + ty + " is Data:\n  " + ctors[0] + "{}\n  " + ctors[1] + "{" + field + ": U32}",
    "def " + name + "(n: U32) -> IO(" + ty + "):\n  import \"./" + file + ".c\"\n  import \"./" + file + ".js\"",
    "def " + show + "(" + t + ": " + ty + ") -> String:\n  match " + t + ":\n    case " + ctors[0] + "{}:\n      \"none\"\n    case "
      + ctors[1] + "{" + b + "}:\n      U32.show(" + b + ")",
  ];
  const csrc = "Term " + file + "_run(Env e, Term* f, IoWork* w) {\n  u32 n = (u32)f[0];\n"
    + "  return n % 2 == 0 ? term_pak(CID(" + ctors[0] + "), 0)\n    : term_pak(CID(" + ctors[1] + "), (u32)(n * 3u + 1u));\n}\n\n"
    + "static void __attribute__((constructor)) " + file + "_use(void) {\n  io_eff(CID(" + name + "), " + file + "_run, 0);\n}\n";
  const jssrc = "function " + file + "(n) {\n  return n % 2 === 0 ? { $: CID(" + ctors[0] + ") }\n    : { $: CID(" + ctors[1] + "), ["
    + JSON.stringify(field) + "]: (n * 3 + 1) >>> 0 };\n}\n\nio_eff(CID(" + name + "), " + file + ");\n";
  const calls = Array.from({ length: c.g.size(1, 1, 8) }, (): [number, string] => {
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
// in its IO.die when its tail dies); main runs every member's rows in
// order, a dying member last. A show
// member's main is its value, reached through its alias when it is filed.


const SEG_BODY = [...NAME_BODY, "-"];
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
  return g.pick(NAME_HEAD) + Array.from({ length: g.size(0, 1.5, 60) }, () => g.pick(SEG_BODY)).join("");
}

// alias_new : an import's alias, fresh in the entry, and no Base prefix
// (the entry calls Base's IO and U32 through their own names)
function alias_new(g: Gen, taken: Set<string>): string {
  for (;;) {
    const a = g.chance(0.3) ? g.pick(NAME_WORDS) : seg(g).replace(/-/g, "_");
    if (/^[A-Za-z_]\w*$/.test(a) && a.length <= 40 && !KEYWORDS.has(a) && !BASE_PREFIXES.has(a) && !taken.has(a)) {
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
  mainRows: string[]; base: boolean; names: Set<string>; spelling: Spelling };

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
        if (m.prof.base && m.show === null && !member_dies(m) && mg.chance(0.5)) {
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
    md.text = (md.file && m.prof.base ? "import Base\n\n" : "") + blocks.filter((b) => b !== "").join("\n\n") + (md.file ? "\n" : "");
  }
  return { entryDir, entryName, mods, links, extraFiles: {}, extraHub: {}, entryHead: [], entryDefs: [], mainRows: [], base: ms[0].prof.base, names, spelling };
}

// ty_qual : a show member's type as the entry spells it, the names the
// member declares under its alias
function ty_qual(md: Mod): string {
  const own = new Set(md.m.entries.flatMap(text_names));
  return (md.m.show as { ty: string }).ty.replace(/(?<![\w.])[A-Za-z_][\w.]*/g, (w) => own.has(w) ? md.alias + "." + w : w);
}

// main_defs : the entry's main over its members
function main_defs(l: Layout): string[] {
  const md0 = l.mods[0];
  if (md0.m.show !== null) {
    return md0.file ? ["def main() -> " + ty_qual(md0) + ":\n  " + md0.alias + "." + md0.rows + "()"] : [];
  }
  // every member's rows in order: a dying member is its group's last
  const call = (md: Mod): string => (md.file ? md.alias + "." : "") + md.rows + "()";
  const rows = l.mods.flatMap((md) => ["w" + String(md.i) + " : Unit <- " + call(md),
    ...md.twice === null ? [] : ["w" + String(md.i) + "t : Unit <- IO.print(U32.show(" + md.twice.alias + "." + md.m.resultName + "()))"]]);
  return ["def main() -> IO(Unit):\n  do IO<Unit>:\n" + rows.concat(l.mainRows, ["IO.pure(Unit, Unit{})"]).map((r) => "    " + r).join("\n")];
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
  const top = [tag, ...(l.base ? ["import Base"] : []), ...imports, ...head].join("\n");
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
  const of = (...ks: string[]): string[] => [...new Set(text_decls(BASE_SOURCE).filter((d) => ks.includes(d.kind)).map((d) => d.name))];
  return { defs: of("def", "law"), types: of("type"), ctors: of("ctor") };
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
      if (!m.prof.base) {
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
        l.extraFiles[other + ".bend"] = "def " + fresh + "() -> " + (m.prof.base ? "U32:\n  0\n" : "Type:\n  Type\n");
        l.entryHead.push("import " + path.posix.relative(l.entryDir.join("/") || ".", other + ".bend") + " as " + md.alias);
      }
      return { kind: "alias-dup", mode: "check", want: /a fresh alias/ };
    }],
    [3, () => {
      if (!m.prof.base) {
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
      l.entryDefs.push("def " + md.alias + "." + fresh + "() -> " + (m.prof.base ? "U32:\n  0" : "Type:\n  Type"));
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
      const esc = "import ../" + out + ".bend as Q\n\ndef " + fresh + "() -> " + (m.prof.base ? "U32:\n  0\n" : "Type:\n  Type\n");
      const pkg = "0x" + hex32(str_hash(esc + out));
      l.extraHub[pkg + "/esc.bend"] = esc;
      l.extraHub[out + ".bend"] = "def " + fresh + "() -> " + (m.prof.base ? "U32:\n  0\n" : "Type:\n  Type\n");
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
  const r = await compiled(w, { refuse: c.want }, [], lanes, "fzc" + String(m.seed), 1, mode);
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
        bend.parse_book(book, (dir ?? ROOT) + "/", src.replace(/^import Base$/m, ""), "", {});
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

// Run : one process run; why: a lane run that outlived its cap
type Run = { ok: boolean; out: string; err: string; timeout: boolean; code: number; why?: string };

function leg_exec(cmd: string, args: string[], cwd: string, timeout: number): Promise<Run> {
  return new Promise((resolve) => {
    const opts = { cwd, timeout, encoding: "utf8" as const, maxBuffer: 64 * 1024 * 1024 };
    child.execFile(cmd, args, opts, (e, out, err) => {
      const killed = e !== null && (e as { killed?: boolean }).killed === true;
      const ec = e === null ? 0 : typeof (e as { code?: unknown }).code === "number" ? (e as { code: number }).code : -1;
      resolve({ ok: e === null, out, err, timeout: killed, code: ec });
    });
  });
}

// -fno-stack-check : Apple clang 17 crashes at -O0 without it ("live
// register clobbered by inserted prologue instructions"; not Bend's)
const CC_FLAGS = ["-std=c11", "-w", "-fno-slp-vectorize", "-fno-stack-check"];

async function leg_run(bin: string, args: string[], dir: string, cap: number): Promise<Run> {
  const run = await leg_exec(bin, args, dir, cap);
  return run.timeout ? { ...run, why: "RUN TIMEOUT after " + String(cap) + "ms (the interpreter finished this program — livelock/perf-cliff suspect)" } : run;
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

function exit_diff(want: number, got: Run, what: string): string | null {
  if (got.code === want) {
    return null;
  }
  return "exit: " + what + " " + String(want) + ", got " + String(got.code) + (got.err.trim() !== "" ? " (stderr: " + got.err.trim().slice(0, 400) + ")" : "");
}

function cmp_expect(exp: Want, got: Run): string | null {
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

function cmp_legs(refr: Run, got: Run, transLines: number[], soft: boolean): { diff: string | null; ulp: boolean } {
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

// Compiled : a compiled lane's verdict. known: a lane's failure that is a
// reviewed limit of that lane (a skip once it is attributed to one
// member): the device holds no F32.show or F32.read (a bang reaching one
// fail-stops), and a JS string holds Unicode scalar values only.
type Compiled = { fail: string | null; skip: string | null; ulp: boolean; dir: string; known?: string };

// a runtime limit every compiled leg hits alike is a skip, JS confirming
// it: memory exhausted (a loop doubling its state), or a Nat past the
// runtimes' 48-bit immediate (the spec's Nat is unbounded)
const SEQ_LIMITS: Array<[RegExp, string]> = [
  [/memory fault/, "resource-fault"],
  [/a Nat past the largest immediate/, "nat-immediate"],
];

const KNOWN_LIMITS: Array<[RegExp, RegExp, string]> = [
  [/^(METAL|CUDA)/, /a function the device does not hold/, "host-only"],
  [/^JS/, /is not a Unicode scalar value/, "js-char-scalar"],
];

// compiled : the emitted C and JS through every compiled lane: C-SEQ
// against the expectation (the reference), then JS, C-PAR and the GPU
// lanes against C-SEQ's output (a refusal against its own). The build
// directory is the caller's to keep or remove.
async function compiled(w: WorkerRes, want: Want, trans: number[], lanes: Lanes, base: string, members: number, mode: Mode = LOUD): Promise<Compiled> {
  const dir = fs.mkdtempSync(path.join(TMP, "g-"));
  const out = (r: Partial<Compiled>): Compiled => ({ fail: null, skip: null, ulp: false, dir, ...r });
  const cap = RUN_TIMEOUT * Math.max(1, members);
  const opt = "-O" + String(lanes.opt);
  const cpu = path.join(dir, base + "_cpu");
  const jsf = path.join(dir, base + ".js");
  const cc = await leg_cc(dir, base, w.csrc ?? "", [opt], base + "_cpu", CC_TIMEOUT);
  if (!cc.ok) {
    return out(cc.skip === true ? { skip: cc.why } : { fail: cc.why ?? "cc failed" });
  }
  fs.writeFileSync(jsf, w.jssrc ?? "");
  const seq = await phase("run:seq", () => leg_run(cpu, ["+RTS", "--threads", "1", "--gpu", "off"], dir, cap));
  if (seq.why !== undefined) {
    return out({ fail: "C-SEQ " + seq.why });
  }
  const d = cmp_expect(want, seq);
  if (d !== null) {
    const lim = SEQ_LIMITS.find(([re]) => re.test(seq.err));
    if (lim !== undefined) {
      const js = await leg_run(process.execPath, [jsf], dir, cap);
      if (js.code !== 0 && lim[0].test(js.err)) {
        return out({ skip: lim[1] });
      }
    }
    return out({ fail: "C-SEQ vs expectation: " + d });
  }
  let ulp = false;
  let known: string | undefined;
  // check : one more lane's run; a known limit of the lane is noted and the
  // other lanes still run, any other failure ends the group
  const check = (label: string, soft: boolean, got: Run): string | null => {
    let f: string | null;
    if (got.why !== undefined) {
      f = label + " " + got.why;
    } else if ("refuse" in want) {
      const e = cmp_expect(want, got);
      f = e === null ? null : label + " vs expectation: " + e;
    } else {
      const r = cmp_legs(seq, got, trans, soft);
      ulp ||= r.ulp;
      f = r.diff === null ? null : label + " vs C-SEQ: " + r.diff;
    }
    const k = f === null ? undefined : KNOWN_LIMITS.find(([l, m]) => l.test(f as string) && m.test(f as string));
    if (k !== undefined) {
      known ??= (/^(METAL|CUDA)/.test(label) ? label.toLowerCase() + "-" : "") + k[2];
      return null;
    }
    return f;
  };
  const js = check("JS", true, await phase("run:js", () => leg_run(process.execPath, [jsf], dir, cap)));
  if (js !== null) {
    return out({ fail: js });
  }
  const par = check("C-PAR(" + String(lanes.threads) + ")", false,
    await phase("run:par", () => leg_run(cpu, ["+RTS", "--threads", String(lanes.threads), "--gpu", "off"], dir, cap * 2)));
  if (par !== null) {
    return out({ fail: par });
  }
  // GPU lanes: the same .c rebuilt with the platform flags, run +RTS --gpu on,
  // strictly one program at a time
  const gpus: Array<[boolean, string, string[]]> = [
    [WITH_METAL, "METAL", ["-DBEND_METAL=1", "-x", "objective-c", "-fobjc-arc", "-framework", "Metal", "-framework", "Foundation"]],
    [WITH_CUDA, "CUDA", ["-DBEND_CUDA=1", "-I/usr/local/cuda/include", "-L/usr/local/cuda/lib64", "-Wl,-rpath,/usr/local/cuda/lib64", "-lcuda", "-lnvrtc"]],
  ];
  for (const [on, label, flags] of gpus) {
    if (!on || !mode.gpu) {
      continue;
    }
    const lname = label.toLowerCase();
    const bin = base + "_" + lname;
    const got = await gpu_serial(async (): Promise<Partial<Compiled>> => {
      const gc = await leg_cc(dir, base, w.csrc ?? "", [opt, ...flags], bin, GPU_CC_TIMEOUT);
      if (!gc.ok) {
        return gc.skip === true ? { skip: lname + "-cc-timeout" } : { fail: label + " " + (gc.why ?? "cc failed") };
      }
      // the device program is built once beside the binary, as `bend -o`
      // does; a launch without it compiles and says so on stderr
      const gb = await phase("gpu-build", () => leg_exec(path.join(dir, bin), ["+RTS", "--gpu-build"], dir, GPU_CC_TIMEOUT));
      if (gb.timeout) {
        return { skip: lname + "-build-timeout" };
      }
      if (!gb.ok) {
        // a refusal may come at the device build, before any run
        return "refuse" in want && want.refuse.test(gb.err + gb.out) ? {} : { fail: label + " GPU BUILD FAILURE:\n" + (gb.err + gb.out).slice(0, 2000) };
      }
      const f = check(label, true, await phase("run:" + lname, () => leg_run(path.join(dir, bin), ["+RTS", "--gpu", "on"], dir, GPU_RUN_TIMEOUT * Math.max(1, members))));
      return f !== null ? { fail: f } : {};
    });
    if (got.skip !== undefined || got.fail !== undefined) {
      return out({ ...got, ulp });
    }
  }
  return out({ ulp, known });
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

// group_expect : the group's expected streams (a dying member runs last)
// and the stdout lines owned by trans-flagged members' extra lines;
// twice: members a second alias prints again
function group_expect(states: MemberState[], twice: Set<Member>): { exp: Expect; trans: number[] } {
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
  return { exp: { out, err, code }, trans: transLines };
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
  if (!members[0].prof.base) {
    return { fail: null, skip: null, batch: src, ulp: false };
  }
  const w = await phase("worker:emit", () => pool.run(prog.p, "emit"));
  if (w.verdict === "skip") {
    return { fail: null, skip: w.stage ?? "emit-skip", err: w.err, batch: src, ulp: false };
  }
  if (w.verdict !== "ok") {
    return { fail: "EMIT " + w.verdict + " (" + (w.stage ?? "?") + "): " + (w.err ?? "").split("\n").slice(0, 3).join(" "), skip: null, batch: src, ulp: false };
  }
  const { exp, trans } = members[0].show !== null ? { exp: { out: [live[0].want], err: [], code: 0 }, trans: [] }
    : group_expect(live, new Set(prog.l.mods.filter((md) => md.twice !== null).map((md) => md.m)));
  const r = await compiled(w, exp, trans, lanes, "fz" + String(members[0].seed) + (solo ? "s" : "b"), members.length, mode);
  return { ...r, batch: src };
}

async function test_group(seeds: bigint[], solo: boolean, lanes: Lanes, mode: Mode = LOUD): Promise<Verdict[]> {
  const states: MemberState[] = seeds.map((sd, k) => {
    const m = phase("gen", () => gen_member(sd, solo ? 0 : k * UID_STRIDE));
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

// FEATURES : what a run is expected to reach, read off this file's own
// feat(..) calls (the ones it never did are listed at its end), with one
// per def of Base's registry the synthesis may draw (base:<name>)
const FEATURES = [...new Set([...fs.readFileSync(import.meta.filename, "utf8").matchAll(/feat\(([^()]*(?:\([^()]*\)[^()]*)*)\)/g)]
  .flatMap((m) => [...m[1].matchAll(/"([\w-]*\w)"/g)].map((x) => x[1])))];

async function fuzz_run(): Promise<void> {
  base_load();
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
    + " jobs=" + String(JOBS) + " legs=" + legs + " io-pct=" + String(IO_PCT) + " registry=" + String(BASE_DEFS.length) + " base defs");
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
      // a seed that owns its program closes the group before it, and a
      // dying one closes it after it (its IO.die ends main)
      while (batch.length < size && more() && !(standalone(seed) && batch.length > 0)) {
        batch.push(seed);
        seed = rng_step(seed);
        launched++;
        if (profile(batch[batch.length - 1]).die) {
          break;
        }
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
  const never = FEATURES.concat(BASE_DEFS.filter((d) => d.effect !== true).map((d) => "base:" + d.name)).filter((f) => feat_tally[f] === undefined);
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
