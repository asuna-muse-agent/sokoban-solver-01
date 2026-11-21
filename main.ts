// Room-decomposed push-optimal Sokoban solver: parse, cut the hallway's dead
// squares into rooms, solve each room push-optimally by BFS over pushes
// (dead-square + frozen 2x2 pruning), walk between pushes, concatenate.
// Deterministic: state caps by count only, never the clock.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const D = [[0, -1, 'u'], [0, 1, 'd'], [-1, 0, 'l'], [1, 0, 'r']], M = 250000;
function P(t) {
  let r = t.split('\n').filter((x) => x), h = r.length, w = 0;
  for (let x of r) w = Math.max(w, x.length);
  let a = new Uint8Array(w * h).fill(1), g = [], b = [], p = -1;
  r.forEach((y, j) => {
    for (let x = 0; x < y.length; x++) {
      let c = y[x], k = j * w + x;
      if (c === '#') continue;
      a[k] = 0;
      if (c === '.' || c === '*' || c === '+') g.push(k);
      if (c === '$' || c === '*') b.push(k);
      if (c === '@' || c === '+') p = k;
    }
  });
  for (let i = 0; i < w * h; i++) if (i < w || i >= w * (h - 1) || i % w < 1 || i % w === w - 1) a[i] = 1;
  return { w, a, g, b: b.sort((x, y) => x - y), p };
}
function L(v) {
  let { w, a, g } = v, n = new Uint8Array(a.length), q = [...g];
  for (let x of g) n[x] = 1;
  for (let i = 0; i < q.length; i++) {
    let x = q[i];
    for (let j = 0; j < 4; j++) {
      let d = D[j][1] * w + D[j][0], y = x - d;
      if (!a[y] && !a[y - d] && !n[y]) { n[y] = 1; q.push(y); }
    }
  }
  return n;
}
function R(v, o, f, s, t, k) {
  let { w, a } = v, m = f, n = 0;
  k[n++] = f; s[f] = t;
  while (n) {
    let p = k[--n];
    if (p < m) m = p;
    for (let j = 0; j < 4; j++) {
      let q = j < 1 ? p - w : j < 2 ? p + w : j < 3 ? p - 1 : p + 1;
      if (!a[q] && !o[q] && s[q] !== t) { s[q] = t; k[n++] = q; }
    }
  }
  return m;
}
function F(v, o, g, t) {
  let { w, a } = v;
  for (let x of [t, t - 1, t - w, t - w - 1]) {
    let b = x + 1, c = x + w, d = c + 1;
    if ((a[x] || o[x]) && (a[b] || o[b]) && (a[c] || o[c]) && (a[d] || o[d]) && ((o[x] && !g[x]) || (o[b] && !g[b]) || (o[c] && !g[c]) || (o[d] && !g[d]))) return 1;
  }
  return 0;
}
const E = (b, l, n) => { let k = l; for (let x of b) k = k * n + x; return k; };
function S(v, C = M) {
  let { w, a, g } = v, n = a.length, G = new Uint8Array(n);
  for (let x of g) G[x] = 1;
  let V = L(v), o = new Uint8Array(n), s = new Int32Array(n), m = new Int32Array(n), k = new Int32Array(n), T = 0;
  if (v.b.some((x) => !V[x])) return null;
  let B = [v.b], Y = [v.p], Q = [-1], K = new Map();
  for (let x of v.b) o[x] = 1;
  K.set(E(v.b, R(v, o, v.p, s, ++T, k), n), 0);
  for (let x of v.b) o[x] = 0;
  let f = v.b.every((x) => G[x]) ? 0 : -1;
  for (let h = 0; f < 0 && h < B.length; h++) {
    let b = B[h];
    for (let x of b) o[x] = 1;
    R(v, o, Y[h], s, ++T, k);
    let H = T;
    for (let i = 0; i < b.length && f < 0; i++) {
      let c = b[i];
      for (let j = 0; j < 4; j++) {
        let d = D[j][1] * w + D[j][0], t = c + d;
        if (s[c - d] !== H || a[t] || o[t] || !V[t]) continue;
        o[c] = 0; o[t] = 1;
        let z = F(v, o, G, t), e = -1, N = null;
        if (!z) { N = b.slice(); N[i] = t; N.sort((x, y) => x - y); e = E(N, R(v, o, c, m, ++T, k), n); }
        o[t] = 0; o[c] = 1;
        if (z || K.has(e)) continue;
        if (B.length >= C) { for (let x of b) o[x] = 0; return null; }
        K.set(e, B.length); B.push(N); Y.push(c); Q.push(h);
        if (N.every((x) => G[x])) { f = B.length - 1; break; }
      }
    }
    for (let x of b) o[x] = 0;
  }
  if (f < 0) return null;
  let p = [], mv = '', pl = v.p, bb = v.b;
  for (let s2 = f; s2 > 0; s2 = Q[s2]) p.push(s2);
  p.reverse();
  for (let s2 of p) {
    let nb = B[s2], fr = bb.find((x) => !nb.includes(x)), to = nb.find((x) => !bb.includes(x)), d = to - fr;
    let dr = D.find(([x, y]) => y * w + x === d);
    for (let x of bb) o[x] = 1;
    mv += W(v, o, pl, fr - d);
    for (let x of bb) o[x] = 0;
    mv += dr[2].toUpperCase(); pl = fr; bb = nb;
  }
  return { pushes: p.length, moves: mv };
}
function W(v, o, f, t) {
  let { w, a } = v;
  if (f === t) return '';
  let p = new Int32Array(a.length).fill(-1), h = new Array(a.length), q = [f];
  p[f] = f;
  for (let i = 0; i < q.length; i++) {
    let x = q[i];
    if (x === t) break;
    for (let j = 0; j < 4; j++) {
      let n = x + D[j][1] * w + D[j][0];
      if (a[n] || o[n] || p[n] > -1) continue;
      p[n] = x; h[n] = D[j][2]; q.push(n);
    }
  }
  if (p[t] < 0) throw 0;
  let s = '';
  for (let x = t; x !== f; x = p[x]) s = h[x] + s;
  return s;
}
function U(v) {
  let { w, a, g, b, p } = v, V = L(v), r = Math.floor(p / w), c = new Uint8Array(a.length);
  for (let i = r * w; i < (r + 1) * w; i++) if (!a[i] && !V[i]) c[i] = 1;
  if (b.some((x) => c[x])) return null;
  let t = new Int32Array(a.length).fill(-1), z = [];
  for (let s = 0; s < a.length; s++) {
    if (a[s] || c[s] || t[s] > -1) continue;
    let q = [s];
    t[s] = z.length;
    for (let i = 0; i < q.length; i++) for (let j = 0; j < 4; j++) {
      let n = q[i] + D[j][1] * w + D[j][0];
      if (!a[n] && !c[n] && t[n] < 0) { t[n] = z.length; q.push(n); }
    }
    z.push({ b: [], g: [] });
  }
  for (let x of b) z[t[x]].b.push(x);
  for (let x of g) if (t[x] > -1) z[t[x]].g.push(x);
  if (g.some((x) => t[x] < 0) || z.some((x) => x.b.length !== x.g.length)) return null;
  return z.filter((x) => x.b.length);
}
function A(v) {
  let r = U(v);
  if (!r) return S(v);
  let p = v.p, ps = 0, mv = '';
  for (let o of r) {
    let w = v.a.slice();
    for (let q of r) if (q !== o) for (let x of q.d ? q.g : q.b) w[x] = 1;
    let s = S({ w: v.w, a: w, g: o.g.slice().sort((x, y) => x - y), b: o.b.slice().sort((x, y) => x - y), p });
    if (!s) return null;
    ps += s.pushes; mv += s.moves;
    for (let c of s.moves.toLowerCase()) p += c === 'u' ? -v.w : c === 'd' ? v.w : c === 'l' ? -1 : 1;
    o.d = 1;
  }
  return { pushes: ps, moves: mv };
}
for (let id of readdirSync(I).sort()) {
  let v = P(readFileSync(`${I}/${id}/level.txt`, 'utf8')), s = null;
  try { s = A(v) || S(v); } catch (e) {}
  mkdirSync(`${O}/${id}`, { recursive: true });
  writeFileSync(`${O}/${id}/solution.txt`, `${s ? s.moves : ''}\n`);
}
