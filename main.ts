// Sokoban solver: push-optimal BFS over pushes, solved room by room. A level
// is a hallway with 1-4 small rooms (3-4 boxes each) off it; a box never
// leaves its room, so rooms are independent and the level optimum is the sum
// of the rooms' optima. Each room is solved by breadth-first search over
// pushes (first solved state is push-optimal), pruning dead squares and
// frozen 2x2 blocks. A state is the boxes plus the player's reachable region
// (named by its lowest square). Fallbacks: the whole level by the same push
// search, then a plain move A*. Budgets are counted in states, never the
// clock, so two runs write the same bytes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const RS = 250_000, LS = 400_000, MS = 1_500_000;
const D: [number, number, string, string][] = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']];
type L = { w: number; h: number; wall: Uint8Array; goals: number[]; boxes: number[]; player: number };
function parse(t: string): L {
  const rows = t.split('\n').filter(r => r.length > 0), h = rows.length;
  const w = Math.max(...rows.map(r => r.length));
  const wall = new Uint8Array(w * h).fill(1), goals: number[] = [], boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => { for (let x = 0; x < row.length; x++) { const c = row[x], i = y * w + x; if (c === '#') continue; wall[i] = 0; if (c === '.' || c === '*' || c === '+') goals.push(i); if (c === '$' || c === '*') boxes.push(i); if (c === '@' || c === '+') player = i; } });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  return { w, h, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}
function live(l: L): Uint8Array {
  const { w, wall, goals } = l, lv = new Uint8Array(wall.length), q = [...goals];
  for (const g of goals) lv[g] = 1;
  for (let i = 0; i < q.length; i++) { const x = q[i]!; for (const [dx, dy] of D) { const d = dy * w + dx, y = x - d; if (!wall[y] && !wall[y - d] && !lv[y]) { lv[y] = 1; q.push(y); } } }
  return lv;
}
function reach(l: L, oc: Uint8Array, from: number, seen: Int32Array, st: number, sk: Int32Array): number {
  const { w, wall } = l; let low = from, n = 0;
  sk[n++] = from; seen[from] = st;
  while (n > 0) { const p = sk[--n]!; if (p < low) low = p;
    for (const q of [p - w, p + w, p - 1, p + 1]) if (wall[q] === 0 && oc[q] === 0 && seen[q] !== st) { seen[q] = st; sk[n++] = q; } }
  return low;
}
function frozen(l: L, oc: Uint8Array, g: Uint8Array, t: number): boolean {
  const { w, wall } = l;
  for (const a of [t, t - 1, t - w, t - w - 1]) { const b = a + 1, c = a + w, d = c + 1;
    if (!(wall[a] || oc[a]) || !(wall[b] || oc[b]) || !(wall[c] || oc[c]) || !(wall[d] || oc[d])) continue;
    if ((oc[a] && !g[a]) || (oc[b] && !g[b]) || (oc[c] && !g[c]) || (oc[d] && !g[d])) return true; }
  return false;
}
function walk(l: L, oc: Uint8Array, from: number, to: number): string {
  const { w, wall } = l; if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1), how = new Array<string>(wall.length), q = [from];
  prev[from] = from;
  for (let i = 0; i < q.length; i++) { const p = q[i]!; if (p === to) break;
    for (const [dx, dy, letter] of D) { const r = p + dy * w + dx; if (wall[r] || oc[r] || prev[r] !== -1) continue; prev[r] = p; how[r] = letter; q.push(r); } }
  if (prev[to] === -1) throw new Error('walk: out of reach');
  let s = ''; for (let p = to; p !== from; p = prev[p]!) s = how[p]! + s; return s;
}
function endOf(w: number, from: number, m: string): number {
  let p = from; for (const c of m.toLowerCase()) p += c === 'u' ? -w : c === 'd' ? w : c === 'l' ? -1 : 1; return p;
}
function pushOpt(l: L, max: number): { pushes: number; moves: string } | null {
  const { w, wall, goals } = l, size = wall.length, goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const lv = live(l), oc = new Uint8Array(size), seen = new Int32Array(size), mark = new Int32Array(size), sk = new Int32Array(size);
  let st = 0;
  const done = (b: number[]) => b.every(x => goal[x]);
  if (l.boxes.some(b => !lv[b])) return null;
  const sb: number[][] = [l.boxes], sp: number[] = [l.player], par: number[] = [-1];
  const idx = new Map<string, number>();
  for (const b of l.boxes) oc[b] = 1;
  idx.set(`${reach(l, oc, l.player, seen, ++st, sk)}:${l.boxes.join(',')}`, 0);
  for (const b of l.boxes) oc[b] = 0;
  let found = done(l.boxes) ? 0 : -1;
  for (let head = 0; found < 0 && head < sb.length; head++) {
    const boxes = sb[head]!;
    for (const b of boxes) oc[b] = 1;
    reach(l, oc, sp[head]!, seen, ++st, sk);
    const here = st;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) { const b = boxes[bi]!;
      for (const [dx, dy] of D) { const d = dy * w + dx, t = b + d;
        if (seen[b - d] !== here || wall[t] || oc[t] || !lv[t]) continue;
        oc[b] = 0; oc[t] = 1;
        const fr = frozen(l, oc, goal, t);
        let key = '', next: number[] | null = null;
        if (!fr) { next = boxes.slice(); next[bi] = t; next.sort((x, y) => x - y); key = `${reach(l, oc, b, mark, ++st, sk)}:${next.join(',')}`; }
        oc[t] = 0; oc[b] = 1;
        if (fr || idx.has(key)) continue;
        if (sb.length >= max) { for (const x of boxes) oc[x] = 0; return null; }
        idx.set(key, sb.length); sb.push(next!); sp.push(b); par.push(head);
        if (done(next!)) { found = sb.length - 1; break; } } }
    for (const x of boxes) oc[x] = 0;
  }
  if (found < 0) return null;
  const path: number[] = [];
  for (let s = found; s > 0; s = par[s]!) path.push(s);
  path.reverse();
  let moves = '', player = l.player, boxes = l.boxes;
  for (const s of path) { const nb = sb[s]!, from = boxes.find(b => !nb.includes(b))!, to = nb.find(b => !boxes.includes(b))!, d = to - from;
    const dir = D.find(([dx, dy]) => dy * w + dx === d)!;
    for (const b of boxes) oc[b] = 1;
    moves += walk(l, oc, player, from - d);
    for (const b of boxes) oc[b] = 0;
    moves += dir[3]; player = from; boxes = nb; }
  return { pushes: path.length, moves };
}
type R = { boxes: number[]; goals: number[]; done?: boolean };
function rooms(l: L): R[] | null {
  const { w, wall, goals, boxes, player } = l, lv = live(l), row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !lv[i]) cut[i] = 1;
  if (boxes.some(b => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1), rs: R[] = [];
  for (let s = 0; s < wall.length; s++) { if (wall[s] || cut[s] || part[s] >= 0) continue;
    const sq = [s]; part[s] = rs.length;
    for (let i = 0; i < sq.length; i++) for (const [dx, dy] of D) { const q = sq[i]! + dy * w + dx; if (!wall[q] && !cut[q] && part[q] < 0) { part[q] = rs.length; sq.push(q); } }
    rs.push({ boxes: [], goals: [] }); }
  for (const b of boxes) rs[part[b]!]!.boxes.push(b);
  for (const g of goals) if (part[g]! >= 0) rs[part[g]!]!.goals.push(g);
  if (goals.some(g => part[g]! < 0) || rs.some(r => r.boxes.length !== r.goals.length)) return null;
  return rs.filter(r => r.boxes.length > 0);
}
function byRooms(l: L): { pushes: number; moves: string } | null {
  const rs = rooms(l); if (rs === null) return null;
  let player = l.player, pushes = 0, moves = '';
  for (const r of rs) { const wall = l.wall.slice();
    for (const o of rs) if (o !== r) for (const b of o.done ? o.goals : o.boxes) wall[b] = 1;
    const sub: L = { w: l.w, h: l.h, wall, goals: r.goals.slice().sort((a, b) => a - b), boxes: r.boxes.slice().sort((a, b) => a - b), player };
    const s = pushOpt(sub, RS); if (s === null) return null;
    pushes += s.pushes; moves += s.moves; player = endOf(l.w, player, s.moves); r.done = true; }
  return { pushes, moves };
}
function moveA(l: L): { pushes: number; moves: string } | null {
  const { w, wall, goals } = l, goal = new Uint8Array(wall.length);
  for (const g of goals) goal[g] = 1;
  const lv = live(l);
  const dist = (b: number) => Math.min(...goals.map(g => Math.abs((g % w) - (b % w)) + Math.abs(Math.floor(g / w) - Math.floor(b / w))));
  const est = (b: number[]) => b.reduce((a, x) => a + dist(x), 0);
  const key = (p: number, b: number[]) => `${p}:${b.join(',')}`;
  const sp: number[] = [l.player], sb: number[][] = [l.boxes], sg: number[] = [0], par: number[] = [-1], stp: string[] = [''];
  const best = new Map<string, number>([[key(l.player, l.boxes), 0]]);
  const heap: [number, number, number][] = [[est(l.boxes), 0, 0]];
  const less = (a: [number, number, number], b: [number, number, number]) => a[0] < b[0] || (a[0] === b[0] && (a[1] > b[1] || (a[1] === b[1] && a[2] < b[2])));
  const push = (e: [number, number, number]) => { let i = heap.length; heap.push(e); while (i > 0) { const p = (i - 1) >> 1; if (!less(heap[i]!, heap[p]!)) break; [heap[i], heap[p]] = [heap[p]!, heap[i]!]; i = p; } };
  const pop = (): [number, number, number] => { const t = heap[0]!, last = heap.pop()!; if (heap.length > 0) { heap[0] = last; for (let i = 0; ;) { let c = 2 * i + 1; if (c >= heap.length) break; if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++; if (!less(heap[c]!, heap[i]!)) break; [heap[i], heap[c]] = [heap[c]!, heap[i]!]; i = c; } } return t; };
  let ex = 0;
  while (heap.length > 0 && ex < MS) { const [, g, s] = pop(); if (best.get(key(sp[s]!, sb[s]!)) !== s) continue;
    const bs = sb[s]!;
    if (bs.every(b => goal[b])) { let m = '', pu = 0; for (let t = s; t > 0; t = par[t]!) { m = stp[t]! + m; if (stp[t]! >= 'A' && stp[t]! <= 'Z') pu++; } return { pushes: pu, moves: m }; }
    ex++; const p = sp[s]!;
    for (const [dx, dy, letter] of D) { const d = dy * w + dx, q = p + d; if (wall[q]) continue;
      let nb = bs, mv = letter; const at = bs.indexOf(q);
      if (at >= 0) { if (wall[q + d] || bs.includes(q + d) || !lv[q + d]) continue; nb = bs.slice(); nb[at] = q + d; nb.sort((a, b) => a - b); mv = letter.toUpperCase(); }
      const k = key(q, nb), si = best.get(k); if (si !== undefined && sg[si]! <= g + 1) continue;
      const t = sp.length; sp.push(q); sb.push(nb); sg.push(g + 1); par.push(s); stp.push(mv); best.set(k, t); push([g + 1 + est(nb), g + 1, t]); } }
  return null;
}
function solve(t: string): string {
  let l: L; try { l = parse(t); } catch { return ''; }
  try { const r = byRooms(l); if (r !== null) return r.moves; } catch { /* fall through */ }
  try { const r = pushOpt(l, LS); if (r !== null) return r.moves; } catch { /* fall through */ }
  try { const r = moveA(l); if (r !== null) return r.moves; } catch { /* fall through */ }
  return '';
}
for (const id of readdirSync(I).sort()) {
  let moves = '';
  try { moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8')); } catch { moves = ''; }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
