#!/usr/bin/env bun
// Parser and template-specialization key coverage. Parser-only candidates may
// be ill typed by design. End-to-end template books are checker-valid.
import fs from "node:fs";
import path from "node:path";

const argv = process.argv.slice(2);
function option(name: string, fallback: string): string {
  const at = argv.indexOf(name);
  if (at < 0) return fallback;
  const value = argv[at + 1];
  if (!value || value.startsWith("--")) throw Error(`missing ${name} value`);
  return value;
}
function integer(name: string, fallback: number, min = 0): number {
  const value = Number(option(name, String(fallback)));
  if (!Number.isSafeInteger(value) || value < min) throw Error(`invalid ${name}`);
  return value;
}

const root = path.resolve(option("--root", fs.existsSync("bend2/bend.ts") ? "." : "../bend2-core"));
const fuzzCount = integer("--fuzz", 3_000);
const seed = integer("--seed", 1) >>> 0;
const output = path.resolve(option("--out", "findings/keys"));
const B = await import(path.join(root, "bend2/bend.ts"));

const PRELUDE = `type Flag is Data:
  Up{}
  Down{}

type Word is Data:
  WBit{bit: Flag, tail: Word}
  WEnd{}

type Scalar is Data:
  F32{word: Word}
  U32{word: Word}

type Natty is Data:
  Z{}
  S{pred: Natty}

def nan() -> Scalar:
  F32{${word(0x7fc00000)}}

def inf() -> Scalar:
  F32{${word(0x7f800000)}}

`;

function word(bits: number, annotateEvery = 0, wrap = false): string {
  let result = "WEnd{}";
  for (let bit = 31; bit >= 0; --bit) {
    let flag = (bits >>> bit) & 1 ? "Up{}" : "Down{}";
    if (annotateEvery > 0 && bit % annotateEvery === 0) flag = `{${flag} : Flag}`;
    result = `WBit{${flag}, ${result}}`;
  }
  return wrap ? `{${result} : Word}` : result;
}

function structural(term: any): string {
  const go = (node: any): unknown => {
    switch (node.$) {
      case "Var": return ["Var", node.k, node.i];
      case "Ref": return ["Ref", node.k, node.b === true];
      case "PVar": return ["PVar", node.k, node.i, node.q?.$];
      case "PCtr": return ["PCtr", node.k, node.x.map(go)];
      case "Sub": return ["Sub", node.i, go(node.v), go(node.f)];
      case "Let": return ["Let", node.k, node.i, node.q.map((q: any) => q.$), node.v.map(go), go(node.f)];
      case "Typ": return ["Typ", go(node.g)];
      case "Qnt": return ["Qnt"];
      case "Qua": return ["Qua", node.q.$];
      case "Min": return ["Min", go(node.a), go(node.b)];
      case "All": return ["All", node.q.$, node.k, node.i, go(node.A), go(node.B)];
      case "Lam": return ["Lam", node.k, node.i, node.q?.$ ?? null, go(node.f)];
      case "App": return ["App", go(node.f), go(node.x)];
      case "ADT": return ["ADT", node.k, node.x.map(go), node.r];
      case "Ctr": return ["Ctr", node.k, node.x.map(go)];
      case "Mat": return ["Mat", node.k, go(node.h), go(node.m)];
      case "Efq": return ["Efq"];
      case "Eql": return ["Eql", go(node.a), go(node.b), go(node.T)];
      case "Rfl": return ["Rfl"];
      case "Rwt": return ["Rwt", go(node.e), go(node.p), go(node.f)];
      case "Hol": return ["Hol", node.k];
      case "Ann": return ["Ann", go(node.x), go(node.T)];
      default: throw Error(`unhandled syntax node ${String(node?.$)}`);
    }
  };
  return JSON.stringify(go(term));
}

function parseTerm(source: string): any | null {
  const book = B.book_nil();
  try {
    B.parse_book(book, ".", `${PRELUDE}def parser_probe() -> Type:\n  ${source}\n`);
    const probe = book.tlds.parser_probe;
    return probe?.$ === "Def" && probe.v !== null ? B.term_lower(probe.v) : null;
  } catch {
    return null;
  }
}

const pairs: [string, string, string][] = [
  ["nan-payload", `F32{${word(0x7fc00000)}}`, `F32{${word(0x7fc00001)}}`],
  ["nan-sign", `F32{${word(0x7fc00000)}}`, `F32{${word(0xffc00000)}}`],
  ["nan-ref", "nan", `F32{${word(0x7fc00000)}}`],
  ["inf-ref", "inf", `F32{${word(0x7f800000)}}`],
  ["u32-inner-ann", `U32{${word(42)}}`, `U32{${word(42, 1)}}`],
  ["f32-inner-ann", `F32{${word(0x3f800000)}}`, `F32{${word(0x3f800000, 5)}}`],
  ["u32-word-ann", `U32{${word(9)}}`, `U32{${word(9, 0, true)}}`],
];

let state = seed;
const random = (n: number): number => {
  state = (Math.imul(state, 1_664_525) + 1_013_904_223) >>> 0;
  return Math.floor(state / 0x1_0000_0000 * n);
};
const pick = <T>(values: T[]): T => values[random(values.length)];
function randomWord(depth: number): string {
  if (depth === 0 || random(5) === 0) return "WEnd{}";
  const flag = random(3) === 0 ? `{${pick(["Up{}", "Down{}"]) } : Flag}` : pick(["Up{}", "Down{}"]);
  return `WBit{${flag}, ${randomWord(depth - 1)}}`;
}
function randomTerm(depth: number): string {
  const leaves = ["Z{}", "Up{}", "Down{}", "WEnd{}", "nan", "inf", `U32{${word(random(16))}}`, `F32{${word(pick([0x3f800000, 0x7fc00000, 0x7f800000, 0x80000000]))}}`];
  if (depth === 0) return pick(leaves);
  const sub = (): string => randomTerm(depth - 1);
  return pick<() => string>([
    () => `S{${sub()}}`,
    () => `WBit{${pick(["Up{}", "Down{}"])}, ${randomWord(5)}}`,
    () => `U32{${randomWord(7)}}`,
    () => `F32{${randomWord(7)}}`,
    () => `{${sub()} : ${pick(["Natty", "Flag", "Word", "Scalar", "Type"])}}`,
    () => `{(x => x) : Natty -> Natty}(${sub()})`,
    () => `{${sub()} == ${sub()} : Natty}`,
    () => `(%proof@{{==} : {Z{} == Z{} : Natty}} : Natty; (${sub()}))`,
    () => `{(\\{Z: Z{}; S: p => p; rest => rest}) : Natty -> Natty}(${sub()})`,
  ])();
}

type Seen = { source: string; structural: string };
const seen = new Map<string, Seen>();
const collisions: { key: string; first: Seen; second: Seen }[] = [];
let parsed = 0;
let rejected = 0;
function feed(source: string): void {
  const term = parseTerm(source);
  if (term === null) { rejected++; return; }
  parsed++;
  const key = B.term_key(term);
  const shape = structural(term);
  const previous = seen.get(key);
  if (previous !== undefined && previous.structural !== shape) collisions.push({ key, first: previous, second: { source, structural: shape } });
  else if (previous === undefined) seen.set(key, { source, structural: shape });
}

for (const [, left, right] of pairs) { feed(left); feed(right); }
for (let index = 0; index < fuzzCount; ++index) feed(randomTerm(4));

type Specialization = { name: string; instances: number; distinctNormalForms: boolean };
const specializations: Specialization[] = [];
const specializationErrors: Record<string, unknown>[] = [];
for (const [name, left, right] of pairs) {
  try {
    const source = `${PRELUDE}def choose(~value: Scalar) -> Scalar:\n  value\n\ndef left() -> Scalar:\n  choose(~${left})\n\ndef right() -> Scalar:\n  choose(~${right})\n`;
    const book = B.book_nil();
    B.parse_book(book, ".", source);
    B.book_valid(book);
    const instances = Object.keys(book.tmps.choose ?? {}).length;
    const normal = (definition: string): string => structural(B.term_lower(B.term_snf(book, B.Ref(definition))));
    const distinctNormalForms = normal("left") !== normal("right");
    specializations.push({ name, instances, distinctNormalForms });
    if (instances !== 2) specializationErrors.push({ name, status: "instance-alias", instances, source });
    if ((name === "nan-payload" || name === "nan-sign") && !distinctNormalForms) {
      specializationErrors.push({ name, status: "wrong-instance-normal-form", source });
    }
  } catch (error) {
    specializationErrors.push({ name, status: "checker-or-normalizer-error", error: String((error as Error)?.stack ?? error) });
  }
}

fs.mkdirSync(output, { recursive: true });
const revision = Bun.spawnSync(["git", "-C", root, "rev-parse", "HEAD"]).stdout.toString().trim();
const report = {
  revision, root, seed, fuzzCount, parsed, rejected, distinctKeys: seen.size,
  collisions: collisions.length, specializationErrors: specializationErrors.length,
  pairs: pairs.map(([name]) => name), specializations,
};
fs.writeFileSync(path.join(output, `run-${seed}.json`), JSON.stringify({ ...report, collisionDetails: collisions, specializationErrorDetails: specializationErrors }, null, 2) + "\n");
fs.writeFileSync(path.join(output, "summary.json"), JSON.stringify(report, null, 2) + "\n");
console.log(JSON.stringify(report));
for (const collision of collisions) {
  console.log(`COLLISION ${collision.first.source.slice(0, 100)} <> ${collision.second.source.slice(0, 100)}`);
}
for (const error of specializationErrors) console.log(`SPECIALIZATION ERROR ${JSON.stringify(error)}`);
if (collisions.length > 0 || specializationErrors.length > 0) process.exitCode = 1;
