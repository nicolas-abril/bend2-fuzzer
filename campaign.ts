#!/usr/bin/env bun
// Runs mutually exclusive fuzzing lanes until the deadline. A nonzero lane
// stops the campaign so its durable artifacts can be triaged before resuming.
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

const directory = import.meta.dirname;
const root = path.resolve(option("--root", fs.existsSync("bend2/bend.ts") ? "." : path.join(directory, "..", "bend2-core")));
const minutes = integer("--minutes", 360, 1);
const jobs = integer("--jobs", 4, 1);
const batch = integer("--batch", 8, 1);
const threads = integer("--threads", 0);
const metal = argv.includes("--metal");
const initialSeed = BigInt(option("--seed", String(Date.now())));
const stamp = new Date().toISOString().replaceAll(":", "-");
const output = path.resolve(option("--out", path.join(directory, "findings", `campaign-${stamp}`)));
const deadline = Date.now() + minutes * 60_000;
fs.mkdirSync(output, { recursive: true });

type Run = {
  lane: string;
  args: string[];
  started: string;
  ended: string;
  code: number;
  skips: number;
  skipReasons: Record<string, number>;
};
const runs: Run[] = [];
const logPath = path.join(output, "campaign.log");
const statePath = path.join(output, "state.json");
const bun = Bun.which("bun") ?? "bun";

function persist(status: string, cycle: number): void {
  const state = {
    status, cycle, root, minutes, jobs, batch, threads, metal,
    initialSeed: String(initialSeed), deadline: new Date(deadline).toISOString(), runs,
  };
  fs.writeFileSync(statePath, JSON.stringify(state, null, 2) + "\n");
}

async function pump(stream: ReadableStream<Uint8Array>, prefix: string): Promise<string> {
  const reader = stream.getReader();
  const decoder = new TextDecoder();
  let output = "";
  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    const text = decoder.decode(value, { stream: true });
    output += text;
    fs.appendFileSync(logPath, text);
    process.stdout.write(prefix + text.replaceAll("\n", `\n${prefix}`));
  }
  return output;
}

async function run(lane: string, script: string, args: string[]): Promise<{ code: number; skips: number; reviewSkips: string[] }> {
  const command = [bun, path.join(directory, script), ...args];
  const header = `\n[${new Date().toISOString()}] ${lane}: ${command.join(" ")}\n`;
  fs.appendFileSync(logPath, header);
  process.stdout.write(header);
  const started = new Date().toISOString();
  const child = Bun.spawn(command, { cwd: root, stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr] = await Promise.all([pump(child.stdout, `[${lane}] `), pump(child.stderr, `[${lane}:err] `)]);
  const code = await child.exited;
  const combined = stdout + stderr;
  const totals = [...combined.matchAll(/\bok=\d+\s+skip=(\d+)\s+FAIL=/g)];
  const skips = Number(totals.at(-1)?.[1] ?? 0);
  const skipReasons: Record<string, number> = Object.create(null);
  const summary = /^skips:\s+(.+)$/m.exec(combined)?.[1] ?? "";
  for (const entry of summary.split(/\s+/).filter(Boolean)) {
    const split = entry.lastIndexOf("=");
    if (split > 0) skipReasons[entry.slice(0, split)] = Number(entry.slice(split + 1));
  }
  const reasons = Object.keys(skipReasons);
  const reviewSkips = skips === 0 ? []
    : reasons.length === 0 ? ["unclassified"]
    : reasons.filter((reason) => !/^(?:metal|cuda)-host-only$/.test(reason));
  runs.push({ lane, args, started, ended: new Date().toISOString(), code, skips, skipReasons });
  return { code, skips, reviewSkips };
}

if (argv.includes("--help")) {
  console.log("bun campaign.ts --root BEND --minutes 360 --jobs 4 --batch 8 [--threads N] [--metal] [--seed N] [--out DIR]\nRuns the compositional differential generator and parser/key oracle sequentially; stops on the first finding or skip.");
} else {
  let cycle = 0;
  persist("running", cycle);
  outer: while (Date.now() < deadline) {
    const cycleSeed = initialSeed + BigInt(cycle) * 10_000n;
    const compiled = ["32", "--seed", String(cycleSeed), "--jobs", String(jobs), "--batch", String(batch), "--threads", String(threads)];
    if (metal) compiled.push("--metal");
    const lanes: [string, string, string[]][] = [
      ["compiled", "fuzz.ts", compiled],
      ["keys", "keys.ts", ["--root", root, "--fuzz", "3000", "--seed", String(Number((cycleSeed + 3_000n) & 0xffff_ffffn)), "--out", path.join(output, `keys-${cycle}`)]],
    ];
    for (const [lane, script, args] of lanes) {
      if (Date.now() >= deadline) break outer;
      const result = await run(lane, script, args);
      persist(result.code !== 0 ? "finding" : result.reviewSkips.length > 0 ? "review-skip" : "running", cycle);
      if (result.code !== 0 || result.reviewSkips.length > 0) {
        console.error(`campaign stopped: ${lane} exited ${result.code}, review-skips=${result.reviewSkips.join(",")}; triage ${output}`);
        process.exitCode = result.code !== 0 ? result.code : 2;
        break outer;
      }
    }
    cycle++;
    persist("running", cycle);
  }
  if (process.exitCode === undefined || process.exitCode === 0) persist("complete", cycle);
  console.log(`campaign artifacts: ${output}`);
}
