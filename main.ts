// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does sections 1 to 4, 9 and 10 of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write. The other three formats are
// detected and then read as holding no edit, so they answer `error: parse 1`: reading unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7) and V4A patches (section 8), and matching lines at three tiers (section 5), are
// yours to write. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file's lines, its line break and whether it ends with one (SPEC section 3). */
interface FileLines { lines: string[]; br: string; final: boolean }
function splitFile(text: string): FileLines {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  let final = false;
  if (text.endsWith(br)) { final = true; lines.pop(); }
  return { lines, br, final };
}
function joinFile(lines: string[], br: string, final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (final ? br : '');
}
function leadWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
}
function normLine(s: string, tier: number): string {
  if (tier === 0) return s;
  const t = s.replace(/[ \t]+$/, '');
  return tier === 1 ? t : t.replace(/^[ \t]+/, '');
}
/** Every 0-based position where `pat` occurs in `lines` at one tier, at or after `from` (SPEC section 5). */
function occurrences(lines: string[], pat: string[], tier: number, from = 0): number[] {
  const out: number[] = [];
  if (pat.length === 0) return out;
  for (let i = from; i + pat.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < pat.length; j++) {
      if (normLine(lines[i + j]!, tier) !== normLine(pat[j]!, tier)) { ok = false; break; }
    }
    if (ok) out.push(i);
  }
  return out;
}
/** The first tier at which `pat` occurs at or after `from`, with its occurrences. */
function findTier(lines: string[], pat: string[], strict: boolean, from = 0): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrences(lines, pat, t, from);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}
/** One line of an old/new block: its text, and whether it is a context line. */
interface BlockLine { text: string; ctx: boolean }
/**
 * The lines that replace a matched block (SPEC section 5): a context line is written as the file's own matched
 * line; at tier 2 every other line is re-indented from the old block's first line to the file's.
 */
function buildReplacement(fileLines: string[], at: number, o: BlockLine[], n: BlockLine[], tier: number): string[] {
  const oCtx: number[] = [];
  o.forEach((x, k) => { if (x.ctx) oCtx.push(k); });
  const f = fileLines[at] ?? '';
  const p = o.length > 0 ? o[0]!.text : '';
  const F = leadWs(f);
  const P = leadWs(p);
  const out: string[] = [];
  let ci = 0;
  for (const item of n) {
    if (item.ctx) {
      out.push(fileLines[at + oCtx[ci]!] ?? item.text);
      ci++;
    } else if (tier === 2) {
      const t = item.text;
      out.push(t !== '' && t.trim() !== '' && t.startsWith(P) ? F + t.slice(P.length) : t);
    } else out.push(item.text);
  }
  return out;
}
/** Moves a move edit made, for the `R` output line (SPEC section 2). */
const MOVES: [string, string][] = [];

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ---- Unified diffs (SPEC section 6) ---- */

function stripAB(p: string): string {
  return p.startsWith('a/') || p.startsWith('b/') ? p.slice(2) : p;
}
function gitPaths(line: string): [string, string] | null {
  const rest = line.slice('diff --git '.length).trimEnd();
  if (!rest.startsWith('a/')) return null;
  const sep = rest.indexOf(' b/', 2);
  if (sep < 0) return null;
  const x = rest.slice(2, sep);
  const y = rest.slice(sep + 3);
  if (x === '' || y === '') return null;
  return [x, y];
}
interface BodyLine { k: ' ' | '-' | '+' | '\\'; text: string }
function collectBody(lines: string[], i: number): { body: BodyLine[]; next: number } {
  const body: BodyLine[] = [];
  let j = i;
  while (j < lines.length) {
    const l = lines[j]!;
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
    if (l.startsWith(' ')) body.push({ k: ' ', text: l.slice(1) });
    else if (l.startsWith('-')) body.push({ k: '-', text: l.slice(1) });
    else if (l.startsWith('+')) body.push({ k: '+', text: l.slice(1) });
    else if (l.startsWith('\\')) body.push({ k: '\\', text: l });
    else if (l === '') body.push({ k: ' ', text: '' });
    else break;
    j++;
  }
  while (body.length > 0) {
    const last = body[body.length - 1]!;
    if (last.k === ' ' && last.text === '') body.pop();
    else break;
  }
  return { body, next: j };
}
interface Hunk {
  a: number;
  o: BlockLine[];
  n: BlockLine[];
  /** A `\` line follows the hunk's last context or `+` line. */
  noNl: boolean;
  /** A `\` line follows the hunk's last `+` line. */
  plusNoNl: boolean;
}
function hunkFrom(a: number, body: BodyLine[]): Hunk {
  const o: BlockLine[] = [];
  const n: BlockLine[] = [];
  for (const b of body) {
    if (b.k === ' ') { o.push({ text: b.text, ctx: true }); n.push({ text: b.text, ctx: true }); }
    else if (b.k === '-') o.push({ text: b.text, ctx: false });
    else if (b.k === '+') n.push({ text: b.text, ctx: false });
  }
  let lastCtxPlus = -1;
  let lastPlus = -1;
  body.forEach((b, k) => {
    if (b.k === ' ' || b.k === '+') lastCtxPlus = k;
    if (b.k === '+') lastPlus = k;
  });
  return {
    a,
    o,
    n,
    noNl: lastCtxPlus >= 0 && body[lastCtxPlus + 1]?.k === '\\',
    plusNoNl: lastPlus >= 0 && body[lastPlus + 1]?.k === '\\',
  };
}
interface Section {
  oldPath: string | null;
  newPath: string | null;
  create: boolean;
  remove: boolean;
  hunks: Hunk[];
}
/** Apply a section's hunks in order to a file's text (SPEC section 6). */
function applyHunks(text: string, hunks: Hunk[], strict: boolean, path: string): string {
  let cur = splitFile(text);
  let d = 0;
  for (const h of hunks) {
    const lines = cur.lines;
    if (h.o.length === 0) {
      const at = Math.min(h.a + d, lines.length);
      const ins = h.n.map((x) => x.text);
      const next = [...lines.slice(0, at), ...ins, ...lines.slice(at)];
      const final = at === lines.length ? !h.noNl : cur.final;
      cur = { lines: next, br: cur.br, final };
    } else {
      const pat = h.o.map((x) => x.text);
      const found = findTier(lines, pat, strict);
      if (found === null) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let best = found.occ[0]!;
      for (const p of found.occ) {
        if (Math.abs(p - target) < Math.abs(best - target)) best = p;
      }
      const rep = buildReplacement(lines, best, h.o, h.n, found.tier);
      const next = [...lines.slice(0, best), ...rep, ...lines.slice(best + h.o.length)];
      const final = best + h.o.length === lines.length ? !h.noNl : cur.final;
      cur = { lines: next, br: cur.br, final };
    }
    d += h.n.length - h.o.length;
  }
  return joinFile(cur.lines, cur.br, cur.final);
}
/** The file a creation section makes from its hunks' `+` lines (SPEC section 6). */
function creationText(hunks: Hunk[]): string {
  const plus: string[] = [];
  let lastPlusHunk: Hunk | null = null;
  for (const h of hunks) {
    for (const x of h.n) if (!x.ctx) { plus.push(x.text); lastPlusHunk = h; }
  }
  if (plus.length === 0) return '';
  return plus.join('\n') + (lastPlusHunk !== null && lastPlusHunk.plusNoNl ? '' : '\n');
}
function sectionEdit(s: Section, strict: boolean): Edit {
  return (tree) => {
    const oldP = s.oldPath;
    const newP = s.newPath;
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    if (oldP === null || s.create) {
      if (newP === null) return;
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      tree.now.set(newP, creationText(s.hunks));
      return;
    }
    if (newP === null || s.remove) {
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    if (oldP !== newP) {
      const before = tree.get(oldP);
      if (before === null) throw new Fail('missing', oldP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const out = applyHunks(before, s.hunks, strict, oldP);
      tree.now.set(oldP, null);
      tree.now.set(newP, out);
      MOVES.push([oldP, newP]);
      return;
    }
    const before = tree.get(oldP);
    if (before === null) throw new Fail('missing', oldP);
    tree.now.set(oldP, applyHunks(before, s.hunks, strict, oldP));
  };
}
function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let pair = false;
  const newSection = (oldPath: string | null, newPath: string | null): void => {
    const s: Section = { oldPath, newPath, create: false, remove: false, hunks: [] };
    sections.push(s);
    cur = s;
    pair = false;
  };
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const g = gitPaths(l);
      if (g === null) throw new Exit2(`error: parse ${i + 1}`);
      newSection(g[0], g[1]);
      i++;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const oldRaw = l.slice(4).split('\t')[0]!.trim();
      const newRaw = lines[i + 1]!.slice(4).split('\t')[0]!.trim();
      const oldP = oldRaw === '/dev/null' ? null : stripAB(oldRaw);
      const newP = newRaw === '/dev/null' ? null : stripAB(newRaw);
      if (cur !== null && cur.hunks.length === 0 && !pair) {
        cur.oldPath = oldP;
        cur.newPath = newP;
        pair = true;
      } else {
        newSection(oldP, newP);
        pair = true;
      }
      i += 2;
      continue;
    }
    if (l.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(l);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const { body, next } = collectBody(lines, i + 1);
      cur.hunks.push(hunkFrom(Number(m[1]), body));
      i = next;
      continue;
    }
    if (cur !== null && cur.hunks.length === 0) {
      if (l.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (l.startsWith('rename from ')) {
        if (!pair) cur.oldPath = l.slice('rename from '.length).trim();
      } else if (l.startsWith('rename to ')) {
        if (!pair) cur.newPath = l.slice('rename to '.length).trim();
      } else if (l === 'new file mode' || l.startsWith('new file mode ')) cur.create = true;
      else if (l === 'deleted file mode' || l.startsWith('deleted file mode ')) cur.remove = true;
      i++;
      continue;
    }
    i++;
  }
  return sections.map((s) => sectionEdit(s, strict));
}

/* ---- SEARCH/REPLACE blocks (SPEC section 7) ---- */

function srEdit(path: string, old: string[], nw: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (old.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, nw.length === 0 ? '' : nw.join('\n') + '\n');
      return;
    }
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    const f = splitFile(text);
    const found = findTier(f.lines, old, strict);
    if (found === null) throw new Fail('no-match', path);
    if (found.occ.length > 1) throw new Fail('ambiguous', path);
    const at = found.occ[0]!;
    const rep = buildReplacement(
      f.lines,
      at,
      old.map((t) => ({ text: t, ctx: false })),
      nw.map((t) => ({ text: t, ctx: false })),
      found.tier,
    );
    const out = [...f.lines.slice(0, at), ...rep, ...f.lines.slice(at + old.length)];
    tree.now.set(path, joinFile(out, f.br, f.final));
  };
}
function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let prevEnd = 0;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') { i++; continue; }
    const searchLine = i;
    let path: string | null = null;
    for (let j = searchLine - 1; j >= prevEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    let j = searchLine + 1;
    const old: string[] = [];
    while (j < lines.length && lines[j]!.trimEnd() !== '=======') { old.push(lines[j]!); j++; }
    if (j >= lines.length) throw new Exit2(`error: parse ${searchLine + 1}`);
    j++;
    const nw: string[] = [];
    while (j < lines.length && lines[j]!.trimEnd() !== '>>>>>>> REPLACE') { nw.push(lines[j]!); j++; }
    if (j >= lines.length) throw new Exit2(`error: parse ${searchLine + 1}`);
    edits.push(srEdit(path, old, nw, strict));
    prevPath = path;
    prevEnd = j + 1;
    i = j + 1;
  }
  return edits;
}

/* ---- V4A patches (SPEC section 8) ---- */

interface VChunk {
  anchor: string | null;
  body: BodyLine[];
  eof: boolean;
}
function v4aChunkEdit(path: string, moveTo: string | null, chunks: VChunk[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const f = splitFile(text);
    let cur = [...f.lines];
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null && ch.anchor !== '') {
        const found = findTier(cur, [ch.anchor], strict, cursor);
        if (found === null) throw new Fail('no-match', path);
        cursor = found.occ[0]! + 1;
      }
      const o: BlockLine[] = [];
      const n: BlockLine[] = [];
      for (const b of ch.body) {
        if (b.k === ' ') { o.push({ text: b.text, ctx: true }); n.push({ text: b.text, ctx: true }); }
        else if (b.k === '-') o.push({ text: b.text, ctx: false });
        else if (b.k === '+') n.push({ text: b.text, ctx: false });
      }
      if (o.length === 0) {
        const at = ch.eof ? cur.length : cursor;
        const ins = n.map((x) => x.text);
        cur = [...cur.slice(0, at), ...ins, ...cur.slice(at)];
        cursor = at + ins.length;
      } else {
        const pat = o.map((x) => x.text);
        let found: { tier: number; occ: number[] } | null = null;
        if (ch.eof) {
          // only an occurrence ending at the file's last line counts, at the first tier with one
          const tiers = strict ? [0] : [0, 1, 2];
          for (const t of tiers) {
            const occ = occurrences(cur, pat, t, cursor).filter((p) => p + pat.length === cur.length);
            if (occ.length > 0) { found = { tier: t, occ }; break; }
          }
        } else {
          found = findTier(cur, pat, strict, cursor);
        }
        if (found === null) throw new Fail('no-match', path);
        const at = found.occ[0]!;
        const rep = buildReplacement(cur, at, o, n, found.tier);
        cur = [...cur.slice(0, at), ...rep, ...cur.slice(at + o.length)];
        cursor = at + rep.length;
      }
    }
    const out = joinFile(cur, f.br, f.final);
    if (moveTo !== null) {
      tree.now.set(path, null);
      tree.now.set(moveTo, out);
      MOVES.push([path, moveTo]);
    } else {
      tree.now.set(path, out);
    }
  };
}
function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) { last = k; break; }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const isStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) { i++; continue; }
    if (!isStart(line)) throw new Exit2(`error: parse ${i + 1}`);
    const kind = line.startsWith('*** Add File: ') ? 'add' : line.startsWith('*** Delete File: ') ? 'delete' : 'update';
    const prefix = kind === 'add' ? '*** Add File: ' : kind === 'delete' ? '*** Delete File: ' : '*** Update File: ';
    const path = line.slice(prefix.length).trim();
    const startLine = i + 1;
    i++;
    const raw: { text: string; num: number }[] = [];
    while (i < last && !isStart(lines[i]!)) { raw.push({ text: lines[i]!, num: i + 1 }); i++; }
    while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
    if (kind === 'add') {
      const content: string[] = [];
      for (const r of raw) {
        if (r.text === '') content.push('');
        else if (r.text.startsWith('+')) content.push(r.text.slice(1));
        else throw new Exit2(`error: parse ${r.num}`);
      }
      edits.push(((p, c) => (tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, c.length === 0 ? '' : c.join('\n') + '\n');
      })(path, content));
    } else if (kind === 'delete') {
      for (const r of raw) {
        if (!blank(r.text)) throw new Exit2(`error: parse ${r.num}`);
      }
      edits.push(((p) => (tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      })(path));
    } else {
      let moveTo: string | null = null;
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      for (const r of raw) {
        const t = r.text;
        if (t.startsWith('*** Move to: ')) {
          if (moveTo !== null || chunks.length > 0 || cur !== null) throw new Exit2(`error: parse ${r.num}`);
          moveTo = t.slice('*** Move to: '.length).trim();
        } else if (t.startsWith('@@')) {
          cur = { anchor: t.slice(2).trim(), body: [], eof: false };
          chunks.push(cur);
        } else if (t === '*** End of File') {
          if (cur === null) throw new Exit2(`error: parse ${r.num}`);
          cur.eof = true;
          cur = null;
        } else if (t === '' || t.startsWith(' ') || t.startsWith('-') || t.startsWith('+')) {
          if (cur === null) { cur = { anchor: null, body: [], eof: false }; chunks.push(cur); }
          cur.body.push({ k: t === '' ? ' ' : (t[0] as ' ' | '-' | '+'), text: t === '' ? '' : t.slice(1) });
        } else throw new Exit2(`error: parse ${r.num}`);
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${startLine}`);
      edits.push(v4aChunkEdit(path, moveTo, chunks, strict));
    }
  }
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    MOVES.length = 0;
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: { key: string; text: string }[] = [];
  const pairs: [string, string][] = [];
  for (const [o, n] of MOVES) {
    if (tree.original(o) !== null && tree.get(o) === null && tree.original(n) === null && tree.get(n) !== null) pairs.push([o, n]);
  }
  const movedOld = new Set(pairs.map((p) => p[0]));
  const movedNew = new Set(pairs.map((p) => p[1]));
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (!check) {
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
    if (movedOld.has(p) || movedNew.has(p)) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const [o, n] of pairs) rows.push({ key: n, text: `R ${o} -> ${n}` });
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const out = rows.map((r) => r.text);
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
