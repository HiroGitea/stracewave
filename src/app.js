import { parseStraceLog } from './parse.js';

const $ = (s, r = document) => r.querySelector(s);
const EXAMPLES = [
  { key: 'uv', name: 'uv build', url: 'examples/uv_build.json' },
  { key: 'ruby', name: 'Ruby build', url: 'examples/ruby_build.json' },
  { key: 'linux', name: 'Linux kernel', url: 'examples/linux_build.json' },
];

// Dark steps of the categorical palette, in their fixed order. Programs past the eighth share one neutral.
const SERIES = ['#3987e5', '#d95926', '#199e70', '#c98500', '#d55181', '#008300', '#9085e9', '#e66767'];
const OTHER = '#6f7785';
const INK = { done: '#0ca30c', running: '#fab219', dot: '#56627a', axis: '#6f7b90', cursor: '#e6ebf4' };
const BINS_3D = 256, ROW_H = 22, AXIS_H = 24, MINI_H = 34, TOP = MINI_H + AXIS_H, PITCH = 8, CELL = 6, PLAY_SECONDS = 24;

const S = {
  key: null, procs: [], span: 1, root: null, rows: [], expanded: new Set(),
  t: 0, playing: false, speed: 1, hover: -1, colorOf: new Map(), vmax: 1,
  starts: null, ends: null, failEnds: null,
  v0: 0, v1: 1, stamp: 0,          // visible time range; stamp invalidates cached series when it changes
  busy: null, cores: 1, coresFrom: '', chain: [], rowOf: new Map(),
};
const dirty = { tl: true, ui: true };
let view3d = null;

const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const fmtT = (t) => t.toFixed(1) + ' s';
const fmtD = (d) => (d >= 100 ? Math.round(d) + 's' : d.toFixed(1) + 's');
const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
function ub(a, x) { let lo = 0, hi = a.length; while (lo < hi) { const m = (lo + hi) >> 1; if (a[m] <= x) lo = m + 1; else hi = m; } return lo; }
const colorFor = (name) => S.colorOf.get(name) || OTHER;
const cmdLine = (c) => { const t = c.split(' '); t[0] = t[0].split('/').pop(); return t.join(' '); };

// ---------------------------------------------------------------- process tree
function stats(n) {
  n.procs.sort((a, b) => a.start - b.start);
  n.starts = Float64Array.from(n.procs, (p) => p.start);
  n.ends = Float64Array.from(n.procs, (p) => p.end).sort();
  n.failEnds = Float64Array.from(n.procs.filter((p) => p.exit !== 0), (p) => p.end).sort();
  n.self = 0;
  for (const p of n.procs) n.self += p.end - p.start;
  n.first = n.procs.length ? n.starts[0] : Infinity;
  n.last = n.procs.length ? n.ends[n.ends.length - 1] : -Infinity;
}

function buildTree(procs) {
  const mk = (id, name, parent) => ({ id, name, parent, depth: parent ? parent.depth + 1 : -1, children: [], kids: new Map(), procs: [], cache: new Map() });
  const root = mk('', '(trace)', null);
  const nodeOf = new Array(procs.length).fill(null);
  const visiting = new Uint8Array(procs.length);
  function nodeFor(i) {
    if (nodeOf[i]) return nodeOf[i];
    const p = procs[i];
    let par = root;
    if (p.parent >= 0 && p.parent !== i && !visiting[i]) { visiting[i] = 1; par = nodeFor(p.parent); visiting[i] = 0; }
    if (nodeOf[i]) return nodeOf[i];
    let n = par.kids.get(p.prog);
    if (!n) { n = mk(par.id + '/' + p.prog, p.prog, par); par.kids.set(p.prog, n); par.children.push(n); }
    n.procs.push(p);
    return (nodeOf[i] = n);
  }
  for (let i = 0; i < procs.length; i++) nodeFor(i);
  procs.forEach((p, i) => { p.node = nodeOf[i]; });
  (function finalize(n) {
    stats(n);
    n.sub = n.self; n.subFirst = n.first;
    for (const c of n.children) { finalize(c); n.sub += c.sub; n.subFirst = Math.min(n.subFirst, c.subFirst); }
    n.children.sort((a, b) => a.subFirst - b.subFirst);
  })(root);
  return root;
}

// Siblings that account for under 0.4% of all process time share one "N more" row, which opens like any parent.
function foldOf(n, small) {
  if (n.fold) return n.fold;
  const f = { id: n.id + '/+', name: small.length + ' more (small)', parent: n, depth: n.depth + 1, children: small, kids: new Map(), procs: [], cache: new Map(), isFold: true };
  (function collect(x) { for (const p of x.procs) f.procs.push(p); x.children.forEach(collect); })({ procs: [], children: small });
  stats(f);
  f.sub = f.self; f.subFirst = f.first;
  return (n.fold = f);
}
function visibleRows() {
  const out = [], floor = S.root.sub * 0.004;
  (function walk(n, depth) {
    let kids = n.children;
    if (!n.isFold && kids.length > 4) {
      const small = kids.filter((c) => c.sub < floor);
      if (small.length >= 2) kids = kids.filter((c) => c.sub >= floor).concat([foldOf(n, small)]);
    }
    for (const c of kids) { c.vdepth = depth; out.push(c); if (S.expanded.has(c.id)) walk(c, depth + 1); }
  })(S.root, 0);
  return out;
}

// Open the nodes hiding the most process time until about 14 rows show.
function defaultExpand() {
  S.expanded.clear();
  for (;;) {
    const rows = visibleRows();
    if (rows.length >= 14) break;
    let best = null;
    for (const n of rows) {
      if (n.isFold || !n.children.length || S.expanded.has(n.id)) continue;
      if (!best || n.sub - n.self > best.sub - best.self) best = n;
    }
    if (!best) break;
    S.expanded.add(best.id);
  }
}

// Average number of this node's processes alive in each of `bins` equal time bins.
// Average number of this node's processes alive in each of `bins` equal time bins, over the visible range
// (or over the whole trace when `full` is set, for the minimap).
function seriesOf(n, bins, full) {
  if (n.stamp !== S.stamp) { n.cache.clear(); n.stamp = S.stamp; }
  const key = full ? -bins : bins;
  let s = n.cache.get(key);
  if (s) return s;
  const v0 = full ? 0 : S.v0, v1 = full ? S.span : S.v1;
  s = new Float32Array(bins);
  const diff = new Float32Array(bins + 1), bw = (v1 - v0) / bins, top = bins - 1e-6;
  for (const p of n.procs) {
    if (p.start >= v1) break;
    if (p.end <= v0) continue;
    const a = Math.min(Math.max(0, (p.start - v0) / bw), top), b = Math.min((p.end - v0) / bw, top);
    const b0 = Math.floor(a), b1 = Math.floor(b);
    if (b0 === b1) { s[b0] += b - a; continue; }
    s[b0] += b0 + 1 - a; s[b1] += b - b1;
    if (b1 > b0 + 1) { diff[b0 + 1] += 1; diff[b1] -= 1; }
  }
  let acc = 0;
  for (let i = 0; i < bins; i++) { acc += diff[i]; s[i] += acc; }
  n.cache.set(key, s);
  return s;
}

// One height scale for everything on screen: every row, the busy total and the core line.
function rescale() {
  let m = Math.max(1, S.cores);
  const scan = (n) => { if (!n.procs.length) return; const s = seriesOf(n, BINS_3D); for (let i = 0; i < s.length; i++) if (s[i] > m) m = s[i]; };
  (function walk(n) { scan(n); if (n.fold) scan(n.fold); n.children.forEach(walk); })(S.root);
  scan(S.busy);
  S.vmax = m;
}

// What the build was actually doing, as opposed to which processes merely existed:
//  - busy: a process counts only while none of its children is alive (a parent waiting on a child is idle);
//  - cores: taken from a -jN flag when there is one, otherwise estimated from the busy total;
//  - chain: walking back from the end, the busy stretch that finished last before each one began. Its long
//    links are the processes the whole build sat waiting for.
// Programs that spend their life waiting on what they launch. Old logs recover only part of the process tree, so a
// waiting parent whose children could not be linked would otherwise look busy for its whole life. Logs recorded
// with fork tracing have an exact tree and do not need this list.
const WAITERS = /^(g?make|ninja|samu|cargo|rustup|sh|bash|dash|zsh|env|sudo|time|timeout|nice|xargs|ccache|sccache|distcc|collect2|(.*-)?(gcc|g\+\+|cc|c\+\+)(-\d+)?)$/;

function analyse() {
  const kids = new Array(S.procs.length);
  for (const p of S.procs) if (p.parent >= 0) (kids[p.parent] || (kids[p.parent] = [])).push(p);
  const act = [];
  for (const p of S.procs) {
    if (!S.exact && WAITERS.test(p.prog)) continue;
    const ch = kids[p.i];
    if (!ch) { act.push({ start: p.start, end: p.end, p }); continue; }
    let cur = p.start;
    for (const c of ch) {
      const a = Math.max(c.start, p.start), b = Math.min(c.end, p.end);
      if (b <= cur) continue;
      if (a > cur) act.push({ start: cur, end: a, p });
      cur = b;
    }
    if (cur < p.end) act.push({ start: cur, end: p.end, p });
  }
  act.sort((x, y) => x.start - y.start);
  S.busy = { name: 'busy', procs: act, cache: new Map(), children: [] };

  S.cores = 0; S.coresFrom = '';
  for (const p of S.procs) {
    const m = p.cmd && /^(g?make|ninja|cargo|bazel|meson|cmake)$/.test(p.prog) && /(?:^|\s)-j ?(\d+)(?:\s|$)/.exec(p.cmd);
    if (m && +m[1] > 0) { S.cores = +m[1]; S.coresFrom = 'from -j' + m[1] + ' in the trace'; break; }
  }
  if (!S.cores) {
    const b = Array.from(seriesOf(S.busy, BINS_3D, true)).sort((x, y) => x - y);
    S.cores = Math.max(1, Math.round(b[Math.floor(b.length * 0.97)]));
    S.coresFrom = 'estimated from the trace';
  }

  const iv = act.filter((x) => x.end - x.start >= 0.02).sort((x, y) => x.end - y.end);
  const ends = Float64Array.from(iv, (x) => x.end), chain = [];
  for (let k = iv.length - 1; k >= 0;) {
    const cur = iv[k];
    chain.push(cur);
    if (cur.start <= 0.02) break;
    k = Math.min(ub(ends, cur.start + 0.02) - 1, k - 1);
  }
  const floor = Math.max(1, S.span * 0.015);
  S.chain = chain.filter((x) => x.end - x.start >= floor).sort((x, y) => x.start - y.start);
}

function setCores(n, from) {
  S.cores = clamp(Math.round(n) || 1, 1, 4096); S.coresFrom = from;
  const el = $('#cores'); el.value = String(S.cores); el.title = 'Core line: ' + S.coresFrom;
  S.stamp++; rescale();
  dirty.tl = true; refresh3D();
}

// Visible time range. The timeline follows at once; the 3D ridges are rebuilt a moment later.
let refreshTimer = 0;
function refresh3D() { clearTimeout(refreshTimer); refreshTimer = setTimeout(() => { if (view3d) view3d.setRows(); }, 90); }
const zoomed = () => S.v1 - S.v0 < S.span - 1e-6;
function setView(a, b) {
  const minW = Math.max(S.span / 400, 0.05);
  a = clamp(a, 0, S.span); b = clamp(b, 0, S.span);
  if (b - a < minW) { a = clamp((a + b) / 2 - minW / 2, 0, S.span - minW); b = a + minW; }
  if (a === S.v0 && b === S.v1) return;
  S.v0 = a; S.v1 = b; S.stamp++;
  rescale();
  setT(S.t);
  syncZoom();
  refresh3D();
}
function syncZoom() {
  const el = $('#zoomReset');
  if (!el) return;
  el.hidden = !zoomed();
  el.textContent = fmtD(S.v0) + ' – ' + fmtD(S.v1) + '  ✕';
}

const hOf = (v) => (v <= 0 ? 0 : Math.sqrt(Math.min(1, v / S.vmax)));
const liveCount = (n, t) => ub(n.starts, t) - ub(n.ends, t);
function stateOf(n, t) {
  if (t < n.first) return 'waiting';
  if (liveCount(n, t) > 0) return 'running';
  return t >= n.last ? 'done' : 'idle';
}
function pathOf(n) { const parts = []; for (let x = n; x && (x.parent || x.isFold); x = x.parent) parts.unshift(x.name); return parts.join(' › '); }
function longestLive(n, t) { for (const p of n.procs) { if (p.start > t) break; if (t < p.end) return p; } return null; }

function shortLabel(p) {
  const c = p.cmd;
  if (!c) return p.prog;
  let m = c.match(/--crate-name (\S+)/);
  if (m) return p.prog + ' ' + m[1];
  const toks = c.split(' ');
  for (let i = toks.length - 1; i > 0; i--) {
    if (/\.(c|cc|cpp|cxx|rs|S|s|rb|y|o|a|so|py|sh|mk|def|inc|h)$/.test(toks[i])) return p.prog + ' ' + toks[i].split('/').pop();
  }
  m = c.match(/ -o (\S+)/);
  if (m) return p.prog + ' → ' + m[1].split('/').pop();
  return p.prog + (toks.length > 1 ? ' ' + toks.slice(1, 3).join(' ') : '');
}

// ---------------------------------------------------------------- dataset
function showTrace(key, d) {
  S.key = key;
  S.span = d.span;
  S.procs = d.procs.map((p, i) => ({ i, start: p[0] / 1000, end: Math.max(p[1], p[0] + 1) / 1000, prog: d.programs[p[2]], parent: p[3], exit: p[4], cmd: p[5] }));
  const total = new Map();
  for (const p of S.procs) total.set(p.prog, (total.get(p.prog) || 0) + p.end - p.start);
  S.colorOf = new Map([...total.entries()].sort((a, b) => b[1] - a[1]).slice(0, SERIES.length).map(([name], i) => [name, SERIES[i]]));
  S.v0 = 0; S.v1 = S.span; S.stamp++;
  S.exact = !!d.exact;
  S.root = buildTree(S.procs);
  analyse();
  S.starts = Float64Array.from(S.procs, (p) => p.start).sort();
  S.ends = Float64Array.from(S.procs, (p) => p.end).sort();
  S.failEnds = Float64Array.from(S.procs.filter((p) => p.exit !== 0), (p) => p.end).sort();
  rescale();
  $('#cores').value = String(S.cores); $('#cores').title = 'Core line: ' + S.coresFrom;
  defaultExpand();
  S.hover = -1;
  S.playing = false;
  $('#meta').innerHTML = (d.file ? esc(d.file) + ' · ' : '') + '$ ' + esc(cmdLine(d.command)) + ' · <b>' + S.procs.length.toLocaleString() + '</b> processes · <b>' + fmtT(S.span) + '</b>' +
    (S.exact ? '' : ' · <span title="This log has no fork records, so some processes could not be linked to their parent and hang off the first process. Record with the strace command in the README for an exact tree.">approximate tree</span>');
  $('#clockEnd').textContent = fmtT(S.span);
  for (const b of $('#datasets').children) b.setAttribute('aria-pressed', String(b.dataset.key === key));
  rowsChanged();
  const all = seriesOf({ procs: S.procs, cache: new Map() }, BINS_3D, true);
  let peak = 0;
  for (let i = 1; i < all.length; i++) if (all[i] > all[peak]) peak = i;
  setT(((peak + 0.5) / BINS_3D) * S.span);
  syncPlay();
  start();
}

const exampleCache = new Map();
async function openExample(key) {
  const ex = EXAMPLES.find((e) => e.key === key);
  try {
    let d = exampleCache.get(key);
    if (!d) {
      const res = await fetch(ex.url);
      if (!res.ok) throw new Error(ex.url + ': HTTP ' + res.status);
      d = await res.json();
      exampleCache.set(key, d);
    }
    showTrace(key, d);
    $('#toast').hidden = true;
  } catch (err) {
    console.error(err);
    toast('Could not load the ' + ex.name + ' example. Serve this folder over HTTP, or open your own log.', 6000);
  }
}
async function openFile(file) {
  toast('Reading ' + file.name + ' …', 60000);
  try {
    const d = parseStraceLog(await file.text());
    if (!d.procs.length) { toast('No execve lines found in ' + file.name + '. Record it with the strace command in the README.', 6000); return; }
    d.file = file.name;
    showTrace('file', d);
    toast(d.procs.length.toLocaleString() + ' processes loaded');
  } catch (err) {
    console.error(err);
    toast('Could not read ' + file.name + '.', 6000);
  }
}

// ---------------------------------------------------------------- timeline (terminal-style tree)
const tlLabels = $('#tlLabels'), tlCanvas = $('#tlCanvas'), tlCtx = tlCanvas.getContext('2d');
let rowEls = [], tlCols = 0, tlW = 0;

function rowsChanged() {
  S.rows = visibleRows();
  S.rowOf = new Map();
  S.rows.forEach((n, i) => {
    if (S.expanded.has(n.id)) { if (!n.isFold) S.rowOf.set(n, i); }
    else (function mark(x) { if (!x.isFold) S.rowOf.set(x, i); x.children.forEach(mark); })(n);
  });
  tlLabels.innerHTML = '<div class="axis-pad"><span>Timeline</span><button type="button" class="zoom-reset" id="zoomReset" title="Show the whole trace" hidden></button></div>' + S.rows.map((n, i) => {
    const has = n.children.length > 0, open = S.expanded.has(n.id), k = n.procs.length;
    return '<button type="button" class="row" data-i="' + i + '" style="--d:' + n.vdepth + '"' + (has ? ' aria-expanded="' + open + '"' : '') + '>' +
      '<span class="st" data-st=""></span><span class="caret">' + (has ? (open ? '▾' : '▸') : '') + '</span>' +
      '<i class="chip" style="background:' + colorFor(n.name) + '"></i><span class="nm">' + esc(n.name) + '</span>' +
      '<span class="ct">(' + k.toLocaleString() + (k === 1 ? ' unit' : ' units') + ')</span><span class="fl"></span></button>';
  }).join('');
  rowEls = [...tlLabels.querySelectorAll('.row')];
  syncZoom();
  sizeTimeline();
  if (view3d) view3d.setRows();
  dirty.tl = dirty.ui = true;
}

function sizeTimeline() {
  const dpr = window.devicePixelRatio || 1;
  const h = TOP + S.rows.length * ROW_H;
  tlCanvas.style.height = h + 'px';
  const w = Math.max(40, tlCanvas.clientWidth);
  tlCols = Math.max(8, Math.floor(w / PITCH));
  tlW = tlCols * PITCH;
  tlCanvas.width = Math.round(w * dpr);
  tlCanvas.height = Math.round(h * dpr);
  dirty.tl = true;
}

function niceStep(raw) { const p = Math.pow(10, Math.floor(Math.log10(raw))); const f = raw / p; return (f <= 1 ? 1 : f <= 2 ? 2 : f <= 5 ? 5 : 10) * p; }

const tickLabel = (v, step) => (step < 1 ? v.toFixed(1) : String(Math.round(v))) + 's';
const xOfT = (t) => ((t - S.v0) / (S.v1 - S.v0)) * tlW;

function drawTimeline() {
  const dpr = window.devicePixelRatio || 1, ctx = tlCtx;
  const w = tlCanvas.width / dpr, h = tlCanvas.height / dpr;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, w, h);
  ctx.font = '11px "JetBrains Mono", ui-monospace, monospace';
  ctx.textBaseline = 'middle';

  // minimap: busy processes over the whole trace, the core line, and the window being viewed
  const mini = seriesOf(S.busy, tlCols, true), mh = MINI_H - 10;
  let mmax = S.cores;
  for (let c = 0; c < tlCols; c++) if (mini[c] > mmax) mmax = mini[c];
  const c0 = Math.floor((S.v0 / S.span) * tlCols), c1 = Math.ceil((S.v1 / S.span) * tlCols);
  for (let c = 0; c < tlCols; c++) {
    if (mini[c] < 0.02) continue;
    const bh = Math.max(1, Math.round((mini[c] / mmax) * mh));
    ctx.fillStyle = c >= c0 && c < c1 ? '#8494ad' : '#39445a';
    ctx.fillRect(c * PITCH, MINI_H - 4 - bh, CELL, bh);
  }
  const cy = Math.round(MINI_H - 4 - (S.cores / mmax) * mh) + 0.5;
  ctx.strokeStyle = '#8fd3ff'; ctx.globalAlpha = 0.8; ctx.setLineDash([4, 3]);
  ctx.beginPath(); ctx.moveTo(0, cy); ctx.lineTo(tlW, cy); ctx.stroke();
  ctx.setLineDash([]); ctx.globalAlpha = 1;
  const coreText = S.cores + (S.cores === 1 ? ' core' : ' cores');
  ctx.fillStyle = '#8fd3ff'; ctx.textAlign = 'right';
  ctx.fillText(coreText, tlW - 2, cy > 12 ? cy - 7 : cy + 8);
  ctx.textAlign = 'left';
  if (zoomed()) {
    const xa = (S.v0 / S.span) * tlW, xb = (S.v1 / S.span) * tlW;
    ctx.strokeStyle = '#8fd3ff'; ctx.lineWidth = 1;
    ctx.strokeRect(Math.round(xa) + 0.5, 1.5, Math.max(2, Math.round(xb - xa) - 1), MINI_H - 3);
  }
  const mx = Math.round((S.t / S.span) * tlW) + 0.5;
  ctx.strokeStyle = INK.cursor; ctx.globalAlpha = 0.7;
  ctx.beginPath(); ctx.moveTo(mx, 2); ctx.lineTo(mx, MINI_H - 2); ctx.stroke();
  ctx.globalAlpha = 1;

  // axis for the visible range
  ctx.fillStyle = INK.axis;
  const step = niceStep((S.v1 - S.v0) / Math.max(2, tlW / 84));
  for (let v = Math.ceil(S.v0 / step - 1e-9) * step; v <= S.v1 + 1e-6; v += step) {
    const x = xOfT(v);
    ctx.globalAlpha = 0.5; ctx.fillRect(Math.round(x), TOP - 5, 1, 4); ctx.globalAlpha = 1;
    if (x + 34 < w) ctx.fillText(tickLabel(v, step), x + 4, MINI_H + AXIS_H / 2 - 1);
  }
  if (S.hover >= 0 && S.hover < S.rows.length) { ctx.fillStyle = 'rgba(255,255,255,0.06)'; ctx.fillRect(0, TOP + S.hover * ROW_H, w, ROW_H); }
  const cur = Math.min(tlCols - 1, Math.floor(((S.t - S.v0) / (S.v1 - S.v0)) * tlCols));
  const maxH = ROW_H - 8;
  for (let r = 0; r < S.rows.length; r++) {
    const s = seriesOf(S.rows[r], tlCols), base = TOP + r * ROW_H + ROW_H - 4;
    for (let c = 0; c < tlCols; c++) {
      const v = s[c];
      if (v < 0.002) continue;
      const x = c * PITCH;
      if (c > cur) { ctx.fillStyle = INK.dot; ctx.fillRect(x + 2, base - 3, 2, 2); continue; }
      const bh = Math.max(2, Math.round((Math.max(1, Math.round(hOf(v) * 8)) / 8) * maxH));
      ctx.fillStyle = c === cur ? INK.running : INK.done;
      ctx.fillRect(x, base - bh, CELL, bh);
    }
  }
  // the long links of the critical chain, underlined on the row that holds each process
  ctx.fillStyle = INK.cursor;
  for (const seg of S.chain) {
    const r = S.rowOf.get(seg.p.node);
    if (r === undefined || seg.end <= S.v0 || seg.start >= S.v1) continue;
    const xa = Math.max(0, xOfT(seg.start)), xb = Math.min(tlW, xOfT(seg.end));
    ctx.fillRect(xa, TOP + r * ROW_H + ROW_H - 3, Math.max(2, xb - xa), 2);
  }
  const cx = Math.round(xOfT(S.t)) + 0.5;
  ctx.strokeStyle = INK.cursor; ctx.globalAlpha = 0.85; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(cx, TOP - 6); ctx.lineTo(cx, h); ctx.stroke();
  ctx.fillStyle = INK.cursor; ctx.beginPath(); ctx.moveTo(cx - 4, TOP - 10); ctx.lineTo(cx + 4, TOP - 10); ctx.lineTo(cx, TOP - 4); ctx.closePath(); ctx.fill();
  ctx.globalAlpha = 1;
}

function updateUI() {
  const t = S.t, N = S.procs.length;
  const started = ub(S.starts, t), ended = ub(S.ends, t), failed = ub(S.failEnds, t);
  $('#tlFoot').innerHTML =
    '<span><span class="k-done">✓</span> <b>' + (ended - failed).toLocaleString() + '</b> done</span>' +
    '<span><span class="k-run">►</span> <b>' + (started - ended).toLocaleString() + '</b> running</span>' +
    '<span><span class="k-wait">·</span> <b>' + (N - started).toLocaleString() + '</b> waiting</span>' +
    '<span><span class="k-fail">×</span> <b>' + failed.toLocaleString() + '</b> failed</span>';
  const GLYPH = { waiting: '·', running: '►', idle: '►', done: '✓' };
  for (let i = 0; i < rowEls.length; i++) {
    const n = S.rows[i], el = rowEls[i], st = stateOf(n, t), sEl = el.firstChild;
    if (sEl.dataset.st !== st) { sEl.dataset.st = st; sEl.textContent = GLYPH[st]; }
    const f = ub(n.failEnds, t), fEl = el.lastChild, txt = f ? '×' + f : '';
    if (fEl.textContent !== txt) fEl.textContent = txt;
  }
  $('#clockT').textContent = fmtT(t);
  $('#sliceT').textContent = fmtT(t);
  const scrub = $('#scrub');
  if (document.activeElement !== scrub || S.playing) scrub.value = String(Math.round(((t - S.v0) / (S.v1 - S.v0)) * 1000));
  // slice panel: who is alive right now, longest-running first
  const live = [];
  for (const p of S.procs) { if (p.start > t) break; if (t < p.end) live.push(p); }
  $('#sliceN').textContent = live.length + ' running';
  const show = live.slice(0, window.innerWidth <= 900 ? 5 : 10);
  $('#sliceList').innerHTML = show.map((p) => {
    const el = t - p.start, d = p.end - p.start;
    return '<li><button type="button" data-p="' + p.i + '" title="' + esc(p.cmd || p.prog) + '">' +
      '<i style="background:' + colorFor(p.prog) + '"></i><span class="lb">' + esc(shortLabel(p)) + '</span>' +
      '<span class="el">' + fmtD(el) + ' / ' + fmtD(d) + '</span><span class="bar"><b style="width:' + ((el / d) * 100).toFixed(1) + '%"></b></span></button></li>';
  }).join('');
  $('#sliceMore').textContent = live.length > show.length ? '+ ' + (live.length - show.length) + ' more' : (live.length ? '' : 'Nothing is running at this instant.');
}

// ---------------------------------------------------------------- shared interactions
const tip = $('#tip');
function showTip(html, x, y) {
  tip.innerHTML = html; tip.hidden = false;
  const r = tip.getBoundingClientRect();
  let left = x + 14, top = y + 14;
  if (left + r.width > window.innerWidth - 8) left = x - r.width - 14;
  if (top + r.height > window.innerHeight - 8) top = y - r.height - 14;
  tip.style.transform = 'translate(' + Math.max(8, left) + 'px,' + Math.max(8, top) + 'px)';
}
const hideTip = () => { tip.hidden = true; };
function nodeTip(n, t) {
  const live = liveCount(n, t), p = longestLive(n, t);
  return '<div class="p">' + esc(pathOf(n)) + '</div>' +
    '<div>' + fmtT(t) + ' · ' + live + ' running · ' + n.procs.length.toLocaleString() + ' total</div>' +
    (p ? '<div class="c">' + esc(shortLabel(p)) + ' — ' + fmtD(t - p.start) + ' of ' + fmtD(p.end - p.start) + '</div>' : '');
}
function setHover(i) {
  if (i === S.hover) return;
  if (rowEls[S.hover]) rowEls[S.hover].classList.remove('hot');
  S.hover = i;
  if (rowEls[i]) rowEls[i].classList.add('hot');
  dirty.tl = true;
  if (view3d) view3d.setHover(i);
}
function setT(t) {
  S.t = clamp(t, S.v0, S.v1);
  dirty.tl = dirty.ui = true;
  if (view3d) view3d.setCursor();
}
function syncPlay() { const b = $('#play'); b.textContent = S.playing ? '❚❚' : '▶'; b.setAttribute('aria-label', S.playing ? 'Pause' : 'Play'); if (view3d) view3d.touch(); }
function togglePlay() { if (!S.playing && S.t >= S.v1 - 1e-6) setT(S.v0); S.playing = !S.playing; syncPlay(); }
let toastTimer = 0;
function toast(text, ms = 1600) { const el = $('#toast'); el.textContent = text; el.hidden = false; clearTimeout(toastTimer); toastTimer = setTimeout(() => { el.hidden = true; }, ms); }

tlLabels.addEventListener('click', (e) => {
  if (e.target.closest('#zoomReset')) { setView(0, S.span); return; }
  const b = e.target.closest('.row'); if (!b) return;
  const n = S.rows[+b.dataset.i]; if (!n || !n.children.length) return;
  if (S.expanded.has(n.id)) S.expanded.delete(n.id); else S.expanded.add(n.id);
  S.hover = -1;
  rowsChanged();
  const again = rowEls[S.rows.indexOf(n)]; if (again) again.focus({ preventScroll: true });
});
tlLabels.addEventListener('pointerover', (e) => { const b = e.target.closest('.row'); setHover(b ? +b.dataset.i : -1); });
tlLabels.addEventListener('pointerleave', () => setHover(-1));

let drag = null;
const tlPos = (e) => { const r = tlCanvas.getBoundingClientRect(); return { x: e.clientX - r.left, y: e.clientY - r.top }; };
const tlTime = (x) => S.v0 + clamp(x / tlW, 0, 1) * (S.v1 - S.v0);
const miniTime = (x) => clamp(x / tlW, 0, 1) * S.span;
tlCanvas.addEventListener('pointerdown', (e) => {
  const { x, y } = tlPos(e);
  tlCanvas.setPointerCapture(e.pointerId);
  if (y >= MINI_H) { drag = { mode: 'scrub' }; setT(tlTime(x)); return; }
  const t = miniTime(x);
  drag = zoomed() && t >= S.v0 && t <= S.v1 ? { mode: 'pan', t, v0: S.v0, v1: S.v1 } : { mode: 'brush', t, x, moved: false };
});
tlCanvas.addEventListener('pointermove', (e) => {
  const { x, y } = tlPos(e);
  if (drag && drag.mode === 'scrub') setT(tlTime(x));
  else if (drag && drag.mode === 'pan') { const w = drag.v1 - drag.v0, a = clamp(drag.v0 + miniTime(x) - drag.t, 0, S.span - w); setView(a, a + w); }
  else if (drag && drag.mode === 'brush') {
    if (Math.abs(x - drag.x) > 3) drag.moved = true;
    if (drag.moved) { const t = miniTime(x); setView(Math.min(drag.t, t), Math.max(drag.t, t)); }
  }
  const i = Math.floor((y - TOP) / ROW_H);
  if (y >= TOP && i < S.rows.length) { setHover(i); showTip(nodeTip(S.rows[i], tlTime(x)), e.clientX, e.clientY); }
  else if (y < MINI_H) {
    setHover(-1);
    const t = miniTime(x), s = seriesOf(S.busy, tlCols, true), c = Math.min(tlCols - 1, Math.floor((t / S.span) * tlCols));
    showTip('<div class="p">' + fmtT(t) + ' · ' + s[c].toFixed(1) + ' busy</div><div class="c">Drag to zoom into a range. Double-click to show everything.</div>', e.clientX, e.clientY);
  } else { setHover(-1); hideTip(); }
});
const endDrag = () => {
  // a plain click on the minimap while zoomed moves the window there
  if (drag && drag.mode === 'brush' && !drag.moved && zoomed()) { const w = S.v1 - S.v0, a = clamp(drag.t - w / 2, 0, S.span - w); setView(a, a + w); }
  drag = null;
};
tlCanvas.addEventListener('pointerup', endDrag);
tlCanvas.addEventListener('pointercancel', endDrag);
tlCanvas.addEventListener('pointerleave', () => { if (!drag) { setHover(-1); hideTip(); } });
tlCanvas.addEventListener('dblclick', (e) => { if (tlPos(e).y < MINI_H) setView(0, S.span); });
$('#cores').addEventListener('change', (e) => setCores(+e.target.value, 'set by you'));

$('#play').addEventListener('click', togglePlay);
$('#speeds').addEventListener('click', (e) => { const b = e.target.closest('button'); if (!b) return; S.speed = +b.dataset.speed; for (const x of $('#speeds').children) x.setAttribute('aria-pressed', String(x === b)); });
$('#scrub').addEventListener('input', (e) => setT(S.v0 + (+e.target.value / 1000) * (S.v1 - S.v0)));
$('#datasets').innerHTML = EXAMPLES.map((e) => '<button type="button" data-key="' + e.key + '" aria-pressed="false">' + esc(e.name) + '</button>').join('');
$('#datasets').addEventListener('click', (e) => { const b = e.target.closest('button'); if (b && b.dataset.key !== S.key) openExample(b.dataset.key); });
$('#openLog').addEventListener('click', () => $('#logFile').click());
$('#logFile').addEventListener('change', (e) => { const f = e.target.files[0]; if (f) openFile(f); e.target.value = ''; });
document.addEventListener('dragover', (e) => e.preventDefault());
document.addEventListener('drop', (e) => { e.preventDefault(); const f = e.dataTransfer && e.dataTransfer.files[0]; if (f) openFile(f); });
$('#resetView').addEventListener('click', () => { if (view3d) view3d.resetView(); });
$('#rt').addEventListener('change', (e) => { if (view3d) view3d.setRT(e.target.checked); else e.target.checked = false; });
$('#sliceList').addEventListener('click', (e) => {
  const b = e.target.closest('button'); if (!b) return;
  const p = S.procs[+b.dataset.p], text = (p.cmd || p.prog) + '\n' + fmtD(p.end - p.start);
  const done = () => toast('Command copied');
  try { navigator.clipboard.writeText(text).then(done, () => toast(p.cmd || p.prog)); } catch (err) { toast(p.cmd || p.prog); }
});
document.addEventListener('keydown', (e) => {
  if (e.code !== 'Space' || e.target.closest('button, input, a')) return;
  e.preventDefault(); togglePlay();
});
new ResizeObserver(() => sizeTimeline()).observe(tlCanvas.parentElement);

// ---------------------------------------------------------------- 3D wavetable
async function init3D() {
  const stage = $('#stage'), canvas = $('#gl'), labelsEl = $('#glLabels'), msg = $('#glMsg'), badge = $('#rtState');
  const fail = (text) => { msg.textContent = text; msg.hidden = false; canvas.hidden = true; $('#rt').disabled = true; return null; };
  let THREE, OrbitControls, EffectComposer, RenderPass, UnrealBloomPass, OutputPass, Reflector;
  try {
    const m = await Promise.all([
      import('three'), import('three/addons/controls/OrbitControls.js'), import('three/addons/postprocessing/EffectComposer.js'),
      import('three/addons/postprocessing/RenderPass.js'), import('three/addons/postprocessing/UnrealBloomPass.js'), import('three/addons/postprocessing/OutputPass.js'),
      import('three/addons/objects/Reflector.js'),
    ]);
    THREE = m[0]; OrbitControls = m[1].OrbitControls; EffectComposer = m[2].EffectComposer; RenderPass = m[3].RenderPass; UnrealBloomPass = m[4].UnrealBloomPass; OutputPass = m[5].OutputPass; Reflector = m[6].Reflector;
  } catch (err) { console.error(err); return fail('The 3D view could not load three.js. The timeline below still works.'); }
  let renderer;
  try { renderer = new THREE.WebGLRenderer({ canvas, antialias: false, powerPreference: 'high-performance' }); }
  catch (err) { console.error(err); return fail('WebGL is not available here. The timeline below still works.'); }
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  const glc = renderer.getContext(), dbg = glc.getExtension('WEBGL_debug_renderer_info');
  const gpuRaw = String(glc.getParameter(dbg ? dbg.UNMASKED_RENDERER_WEBGL : glc.RENDERER) || '');
  const software = /swiftshader|llvmpipe|softpipe|software|basic render/i.test(gpuRaw);
  const angle = gpuRaw.match(/^ANGLE \((?:[^,]*, )?([^,]+)/);
  const gpuName = (angle ? angle[1].split(/\/| Direct3D| \(0x/)[0] : gpuRaw).trim().slice(0, 60);
  const gpuEl = $('#gpuInfo');
  gpuEl.textContent = software ? 'Software rendering (' + gpuName + '). Turn on hardware acceleration in the browser for ray tracing.' : 'GPU · ' + (gpuName || 'unknown');
  gpuEl.classList.toggle('warn', software);
  gpuEl.hidden = false;
  renderer.toneMapping = THREE.ACESFilmicToneMapping;
  renderer.toneMappingExposure = 1.05;

  const W = 24, X0 = -12, H = 4.6, Y0 = 0.012;
  const xOf = (t) => X0 + ((t - S.v0) / (S.v1 - S.v0)) * W;
  let dz = 0.7, D = 8;
  const zOf = (i) => D / 2 - i * dz;

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x0b0e14);
  scene.environment = makeEnv();
  const sun = new THREE.DirectionalLight(0xdfe9ff, 1.1);
  sun.position.set(-8, 12, 10);
  scene.add(sun);

  const camera = new THREE.PerspectiveCamera(30, 2, 0.1, 300);
  const controls = new OrbitControls(camera, canvas);
  controls.enableDamping = true; controls.dampingFactor = 0.15;
  controls.minDistance = 8; controls.maxDistance = 90;
  controls.maxPolarAngle = 1.5; controls.zoomSpeed = 0.7;
  const HOME_DIR = new THREE.Vector3(-0.3, 0.47, 0.83).normalize();
  let userMoved = false;
  controls.addEventListener('start', () => { userMoved = true; });
  // Back the camera off along the home direction until the whole table, with its labels, is in frame.
  function resetView() {
    const xa = X0 - 3.2, xb = X0 + W + 0.6, za = -D / 2 - 0.8, zb = D / 2 + 1.9, q = new THREE.Vector3();
    controls.target.set((xa + xb) / 2, 0.7, 0);
    for (let dist = 14; dist < 120; dist += 1) {
      camera.position.copy(controls.target).addScaledVector(HOME_DIR, dist);
      camera.lookAt(controls.target); camera.updateMatrixWorld();
      let ok = true;
      for (const x of [xa, xb]) for (const y of [0, H * 0.8]) for (const z of [za, zb]) {
        q.set(x, y, z).project(camera);
        if (Math.abs(q.x) > 0.96 || q.y > 0.84 || q.y < -0.92) ok = false;
      }
      if (ok) break;
    }
    controls.update(); userMoved = false; camChanged();
  }

  const mkTarget = () => new THREE.WebGLRenderTarget(4, 4, { type: THREE.HalfFloatType, samples: 4 });
  const composer = new EffectComposer(renderer, mkTarget());
  composer.addPass(new RenderPass(scene, camera));
  composer.addPass(new UnrealBloomPass(new THREE.Vector2(4, 4), 0.5, 0.55, 0.8));
  composer.addPass(new OutputPass());

  // floor, slice sheet and blade
  // Two floors with the same frosted look. The path tracer gets a rough metal and blurs reflections physically;
  // the raster renderer gets a planar reflection smeared by a grainy disc blur.
  const floor = new THREE.Mesh(new THREE.PlaneGeometry(1, 1), new THREE.MeshStandardMaterial({ color: 0x8a93a6, roughness: 0.34, metalness: 1 }));
  floor.rotation.x = -Math.PI / 2;
  const frost = new Reflector(new THREE.PlaneGeometry(1, 1), {
    textureWidth: 640, textureHeight: 320, clipBias: 0.003, color: 0x06080c,
    shader: {
      name: 'FrostedFloor',
      uniforms: { color: { value: null }, tDiffuse: { value: null }, textureMatrix: { value: null } },
      vertexShader: 'uniform mat4 textureMatrix; varying vec4 vUv; void main() { vUv = textureMatrix * vec4(position, 1.0); gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0); }',
      fragmentShader: [
        'uniform vec3 color; uniform sampler2D tDiffuse; varying vec4 vUv;',
        'void main() {',
        '  vec2 uv = vUv.xy / vUv.w;',
        '  float spin = 6.2831853 * fract(52.9829189 * fract(dot(gl_FragCoord.xy, vec2(0.06711056, 0.00583715))));',
        '  vec3 acc = vec3(0.0);',
        '  for (int i = 0; i < 16; i++) {',
        '    float a = spin + float(i) * 2.3999632, r = sqrt((float(i) + 0.5) / 16.0);',
        '    acc += texture2D(tDiffuse, uv + vec2(cos(a) * 0.016, sin(a) * 0.045) * r).rgb;',
        '  }',
        '  gl_FragColor = vec4(color + acc * (0.5 / 16.0), 1.0);',
        '}',
      ].join('\n'),
    },
  });
  frost.rotation.x = -Math.PI / 2;
  scene.add(frost);
  const tickMat = new THREE.MeshStandardMaterial({ color: 0x000000, emissive: 0x30415c, emissiveIntensity: 0.9, roughness: 1 });
  const ticks = new THREE.Group(); scene.add(ticks);
  const sheetMat = new THREE.MeshStandardMaterial({ color: 0x000000, emissive: 0x8fd3ff, emissiveIntensity: 0.55, transparent: true, opacity: 0.075, side: THREE.DoubleSide, depthWrite: false, roughness: 1 });
  const sheet = new THREE.Mesh(new THREE.PlaneGeometry(1, 1), sheetMat);
  sheet.rotation.y = Math.PI / 2;
  const bladeMat = new THREE.MeshStandardMaterial({ color: 0x000000, emissive: 0xcfeaff, emissiveIntensity: 2.4, roughness: 1 });
  const blade = new THREE.Mesh(new THREE.BoxGeometry(1, 1, 1), bladeMat);
  const ribbonGeo = new THREE.BufferGeometry();
  const ribbon = new THREE.Mesh(ribbonGeo, new THREE.MeshStandardMaterial({ color: 0x000000, emissive: 0xe8f5ff, emissiveIntensity: 2.6, side: THREE.DoubleSide, roughness: 1 }));
  ribbon.frustumCulled = false;
  const frameMat = new THREE.MeshStandardMaterial({ color: 0x000000, emissive: 0x8fd3ff, emissiveIntensity: 1.1, roughness: 1 });
  const frameTop = new THREE.Mesh(new THREE.BoxGeometry(1, 1, 1), frameMat), frameA = new THREE.Mesh(new THREE.BoxGeometry(1, 1, 1), frameMat), frameB = new THREE.Mesh(new THREE.BoxGeometry(1, 1, 1), frameMat);
  const slice = new THREE.Group(); slice.add(sheet, blade, ribbon, frameTop, frameA, frameB); scene.add(slice);
  const beadGeo = new THREE.SphereGeometry(0.085, 14, 10);
  const ridges = new THREE.Group(); scene.add(ridges);
  // The slice is drawn as an overlay on top of the path-traced picture. This scene holds it during ray tracing, with
  // depth-only copies of the ridges so it still disappears behind them.
  const overlayScene = new THREE.Scene(), occluders = new THREE.Group();
  const occluderMat = new THREE.MeshBasicMaterial({ colorWrite: false });
  overlayScene.add(occluders);
  let bodies = [], crests = [], rests = [], beads = [], series = [], rowLabels = [], tickLabels = [];

  // Fill gradient for ridge faces: near black at the baseline, brightest just under the crest.
  const FILL = 0.85;
  const fillTex = (() => {
    const n = 64, data = new Uint8Array(n * 4);
    for (let i = 0; i < n; i++) {
      const v = i / (n - 1), lin = 0.012 + 0.62 * Math.pow(v, 2.1), srgb = lin <= 0.0031308 ? lin * 12.92 : 1.055 * Math.pow(lin, 1 / 2.4) - 0.055;
      data.set([srgb * 255, srgb * 255, srgb * 255, 255], i * 4);
    }
    const tex = new THREE.DataTexture(data, 1, n, THREE.RGBAFormat, THREE.UnsignedByteType);
    tex.colorSpace = THREE.SRGBColorSpace; tex.minFilter = tex.magFilter = THREE.LinearFilter; tex.wrapS = tex.wrapT = THREE.ClampToEdgeWrapping; tex.needsUpdate = true;
    return tex;
  })();

  function makeEnv() {
    const w = 64, h = 32, data = new Uint16Array(w * h * 4), toHalf = THREE.DataUtils.toHalfFloat;
    for (let y = 0; y < h; y++) {
      const v = y / (h - 1), up = Math.max(0, v - 0.5) * 2;
      for (let x = 0; x < w; x++) {
        const hz = 0.02 * Math.exp(-(((v - 0.5) / 0.08) ** 2));
        const i = (y * w + x) * 4;
        data[i] = toHalf(0.012 + 0.06 * up + hz);
        data[i + 1] = toHalf(0.016 + 0.09 * up + hz * 1.3);
        data[i + 2] = toHalf(0.026 + 0.16 * up + hz * 1.9);
        data[i + 3] = toHalf(1);
      }
    }
    const tex = new THREE.DataTexture(data, w, h, THREE.RGBAFormat, THREE.HalfFloatType);
    tex.mapping = THREE.EquirectangularReflectionMapping;
    tex.colorSpace = THREE.LinearSRGBColorSpace;
    tex.minFilter = tex.magFilter = THREE.LinearFilter;
    tex.needsUpdate = true;
    return tex;
  }

  function sampleRow(i, t) {
    const s = series[i], f = clamp(((t - S.v0) / (S.v1 - S.v0)) * BINS_3D - 0.5, 0, BINS_3D - 1), a = Math.floor(f), b = Math.min(BINS_3D - 1, a + 1);
    return Y0 + H * hOf(s[a] + (s[b] - s[a]) * (f - a));
  }

  function buildRidge(n, i) {
    const s = seriesOf(n, BINS_3D), P = BINS_3D + 2, col = new THREE.Color(colorFor(n.name));
    const th = Math.min(0.07, dz * 0.22), zf = th / 2, zb = -th / 2, lw = 0.05;
    const xs = new Float32Array(P), hs = new Float32Array(P);
    for (let k = 0; k < P; k++) {
      const b = clamp(k - 1, 0, BINS_3D - 1);
      xs[k] = X0 + W * (k === 0 ? 0 : k === P - 1 ? 1 : (b + 0.5) / BINS_3D);
      hs[k] = Y0 + H * hOf(s[b]);
    }
    // body: front and back faces with a dark-to-colour gradient
    const pos = new Float32Array(P * 12), uv = new Float32Array(P * 8), nor = new Float32Array(P * 12), idx = [];
    for (let k = 0; k < P; k++) {
      const o = k * 12, x = xs[k], y = hs[k], top = clamp(0.3 + 1.4 * (y - Y0) / H, 0.3, 1);
      pos.set([x, 0, zf, x, y, zf, x, 0, zb, x, y, zb], o);
      uv.set([0.5, 0, 0.5, top, 0.5, 0, 0.5, top], k * 8);
      nor.set([0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, -1], o);
      if (k < P - 1) { const a = k * 4, b = a + 4; idx.push(a, b, a + 1, a + 1, b, b + 1, a + 2, a + 3, b + 2, a + 3, b + 3, b + 2); }
    }
    const bodyGeo = new THREE.BufferGeometry();
    bodyGeo.setAttribute('position', new THREE.BufferAttribute(pos, 3));
    bodyGeo.setAttribute('uv', new THREE.BufferAttribute(uv, 2));
    bodyGeo.setAttribute('normal', new THREE.BufferAttribute(nor, 3));
    bodyGeo.setIndex(idx);
    const body = new THREE.Mesh(bodyGeo, new THREE.MeshStandardMaterial({ color: col.clone().multiplyScalar(0.05), roughness: 0.4, metalness: 0, emissive: col, emissiveMap: fillTex, emissiveIntensity: FILL }));
    // crest: the glowing top strip plus an outline ribbon on both faces
    const cp = new Float32Array(P * 18), ci = [], cb = [];
    for (let k = 0; k < P; k++) {
      const x = xs[k], y = hs[k], kp = Math.max(0, k - 1), kn = Math.min(P - 1, k + 1);
      let tx = xs[kn] - xs[kp], ty = hs[kn] - hs[kp]; const tl = Math.hypot(tx, ty) || 1; tx /= tl; ty /= tl;
      const ix = x + ty * lw, iy = Math.max(0, y - tx * lw);
      cp.set([x, y, zf, x, y, zb, x, y, zf + 0.002, ix, iy, zf + 0.002, x, y, zb - 0.002, ix, iy, zb - 0.002], k * 18);
      if (k < P - 1) {
        const a = k * 6, b = a + 6, lit = Math.max(hs[k], hs[k + 1]) > Y0 + 0.02;
        (lit ? ci : cb).push(a, b, a + 1, a + 1, b, b + 1, a + 2, a + 3, b + 2, a + 3, b + 3, b + 2, a + 4, b + 4, a + 5, a + 5, b + 4, b + 5);
      }
    }
    const cpAttr = new THREE.BufferAttribute(cp, 3);
    const mkCrest = (index, intensity) => {
      const g = new THREE.BufferGeometry(); g.setAttribute('position', cpAttr); g.setIndex(index.length ? index : [0, 0, 0]); g.computeVertexNormals();
      const m = new THREE.Mesh(g, new THREE.MeshStandardMaterial({ color: 0x000000, emissive: col, emissiveIntensity: intensity, roughness: 1, side: THREE.DoubleSide }));
      m.userData.base = intensity; return m;
    };
    const crest = mkCrest(ci, 1.35), rest = mkCrest(cb, 0.16);
    const bead = new THREE.Mesh(beadGeo, new THREE.MeshStandardMaterial({ color: 0x000000, emissive: col.clone().lerp(new THREE.Color(0xffffff), 0.35), emissiveIntensity: 3, roughness: 1 }));
    body.userData.i = i;
    for (const m of [body, crest, rest]) { m.position.z = zOf(i); ridges.add(m); }
    const occ = new THREE.Mesh(bodyGeo, occluderMat); occ.position.z = zOf(i); occluders.add(occ);
    slice.add(bead);
    bodies.push(body); crests.push(crest); rests.push(rest); beads.push(bead); series.push(s);
  }

  function setRows() {
    for (const m of [...bodies, ...crests, ...rests]) { m.geometry.dispose(); m.material.dispose(); }
    ridges.clear(); occluders.clear();
    for (const b of beads) { slice.remove(b); b.material.dispose(); }
    for (const t of ticks.children) t.geometry.dispose();
    ticks.clear(); bodies = []; crests = []; rests = []; beads = []; series = [];
    const R = S.rows.length;
    dz = clamp(11 / Math.max(1, R), 0.26, 0.8); D = dz * Math.max(0, R - 1);
    S.rows.forEach(buildRidge);
    floor.scale.set(W + 400, D + 400, 1); frost.scale.copy(floor.scale);
    // one persistent buffer for the slice outline, so moving the slice only rewrites vertex positions
    const ribbonIdx = [];
    for (let i = 0; i < R - 1; i++) { const a = i * 2; ribbonIdx.push(a, a + 1, a + 2, a + 1, a + 3, a + 2); }
    ribbonGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(Math.max(2, R) * 6), 3));
    ribbonGeo.deleteAttribute('normal');
    ribbonGeo.setIndex(ribbonIdx);
    sheet.scale.set(D + 1.6, H + 0.9, 1); sheet.position.y = (H + 0.9) / 2;
    blade.scale.set(0.035, 0.02, D + 1.6); blade.position.y = 0.012;
    const SH = H + 0.9, SZ = D / 2 + 0.8;
    frameTop.scale.set(0.02, 0.02, D + 1.6); frameTop.position.set(0, SH, 0);
    frameA.scale.set(0.02, SH, 0.02); frameA.position.set(0, SH / 2, SZ);
    frameB.scale.set(0.02, SH, 0.02); frameB.position.set(0, SH / 2, -SZ);
    const step = niceStep((S.v1 - S.v0) / 8);
    labelsEl.textContent = ''; tickLabels = []; rowLabels = [];
    for (let v = Math.ceil(S.v0 / step - 1e-9) * step; v <= S.v1 + 1e-6; v += step) {
      const m = new THREE.Mesh(new THREE.BoxGeometry(0.014, 0.004, D + 1.6), tickMat);
      m.position.set(xOf(v), 0.003, 0); ticks.add(m);
      const el = document.createElement('span'); el.className = 'tick'; el.textContent = tickLabel(v, step);
      labelsEl.appendChild(el); tickLabels.push({ el, p: new THREE.Vector3(xOf(v), 0, D / 2 + 1.25) });
    }
    S.rows.forEach((n, i) => {
      const el = document.createElement('span'); el.className = 'rowl';
      const chip = document.createElement('i'); chip.style.background = colorFor(n.name);
      el.append(chip, n.name);
      labelsEl.appendChild(el); rowLabels.push({ el, p: new THREE.Vector3(X0 - 0.35, 0.05, zOf(i)) });
    });
    setHover(S.hover);
    setCursor();
    if (!userMoved) resetView();
    sceneChanged();
  }

  function setCursor() {
    const R = S.rows.length, x = xOf(S.t);
    slice.position.x = x;
    const attr = ribbonGeo.getAttribute('position'), pos = attr.array;
    for (let i = 0; i < R; i++) {
      const y = sampleRow(i, S.t), z = zOf(i);
      beads[i].position.set(0, y, z);
      pos.set([0, y + 0.03, z, 0, y - 0.03, z], i * 6);
    }
    attr.needsUpdate = true;
    ribbonGeo.computeVertexNormals();
    touch();
  }

  function setHover(i) {
    for (let k = 0; k < bodies.length; k++) {
      const hot = k === i, dim = i >= 0 && !hot;
      bodies[k].material.emissiveIntensity = hot ? FILL * 1.9 : dim ? FILL * 0.55 : FILL;
      crests[k].material.emissiveIntensity = hot ? 2.6 : dim ? 0.7 : 1.35;
      rests[k].material.emissiveIntensity = hot ? 0.9 : 0.16;
      if (rowLabels[k]) rowLabels[k].el.classList.toggle('hot', hot);
    }
    rt.matDirty = true; touch();
  }

  // ---- render scheduling. With ray tracing on, the ridges and floor are path traced on the GPU and keep accumulating
  // samples, and the slice is rasterised on top each frame, so playing or scrubbing never restarts the picture. Moving
  // the camera, hovering a row or changing the rows does restart it. The raster renderer covers loading, shader
  // compilation and GPUs that cannot hold a sample per frame while the camera moves.
  let needsRender = true, lastCam = 0, look = 'raster';
  const rt = { on: false, pt: null, loading: false, max: 400, composer: null, mix: null, overlay: null, geoDirty: true, matDirty: false, camDirty: false,
    drawn: -1, spf: 2, prev: 0, slow: 0, fast: 0, liteCam: false, scale: 1, motion: false };
  function setLook(next) {
    if (look === next) return;
    look = next;
    if (next === 'traced') { scene.remove(frost); scene.add(floor); overlayScene.add(slice); }
    else { scene.remove(floor); scene.add(frost); scene.add(slice); }
  }
  function touch() { needsRender = true; }
  function camChanged() { rt.camDirty = true; lastCam = performance.now(); needsRender = true; }
  function sceneChanged() { rt.geoDirty = true; needsRender = true; }
  controls.addEventListener('change', camChanged);
  const setBadge = (text) => { badge.hidden = !text; badge.textContent = text || ''; };

  async function setRT(on) {
    rt.on = on; needsRender = true;
    try { localStorage.setItem('stracewave.rt', on ? '1' : '0'); } catch (err) { /* storage is optional */ }
    if (!on) { setBadge(''); return; }
    if (rt.pt || rt.loading) return;
    rt.loading = true; setBadge('ray tracing · loading');
    try {
      const [m, sp] = await Promise.all([import('three-gpu-pathtracer'), import('three/addons/postprocessing/ShaderPass.js')]);
      const pt = new m.WebGLPathTracer(renderer);
      pt.renderToCanvas = false; pt.rasterizeScene = false; pt.dynamicLowRes = false;
      pt.renderDelay = 0; pt.minSamples = 0; pt.bounces = 5; pt.filterGlossyFactor = 0.6;
      pt.tiles.set(1, 1);
      rt.scale = Math.min(1, 1.25 / renderer.getPixelRatio());
      pt.renderScale = rt.scale;
      pt.target.texture.minFilter = pt.target.texture.magFilter = THREE.LinearFilter;
      rt.overlay = new THREE.WebGLRenderTarget(4, 4, { type: THREE.HalfFloatType, samples: 4 });
      rt.mix = new sp.ShaderPass({
        name: 'TracedPlusSlice',
        uniforms: { tTraced: { value: null }, tSlice: { value: null } },
        vertexShader: 'varying vec2 vUv; void main() { vUv = uv; gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0); }',
        fragmentShader: 'uniform sampler2D tTraced; uniform sampler2D tSlice; varying vec2 vUv; void main() { vec4 s = texture2D(tSlice, vUv); gl_FragColor = vec4(texture2D(tTraced, vUv).rgb * (1.0 - s.a) + s.rgb, 1.0); }',
      });
      rt.composer = new EffectComposer(renderer, new THREE.WebGLRenderTarget(4, 4, { type: THREE.HalfFloatType }));
      rt.composer.addPass(rt.mix);
      rt.composer.addPass(new UnrealBloomPass(new THREE.Vector2(4, 4), 0.38, 0.5, 0.85));
      rt.composer.addPass(new OutputPass());
      rt.pt = pt; rt.geoDirty = true;
      resize();
    } catch (err) {
      console.error(err); rt.on = false; $('#rt').checked = false; setBadge('ray tracing unavailable in this browser');
    }
    rt.loading = false;
  }

  function rasterRender() { setLook('raster'); composer.render(); needsRender = false; placeLabels(); }

  function tracedRender() {
    const alpha = renderer.getClearAlpha();
    renderer.setRenderTarget(rt.overlay); renderer.setClearAlpha(0); renderer.clear();
    renderer.render(overlayScene, camera);
    renderer.setRenderTarget(null); renderer.setClearAlpha(alpha);
    rt.mix.uniforms.tTraced.value = rt.pt.target.texture;
    rt.mix.uniforms.tSlice.value = rt.overlay.texture;
    rt.composer.render();
    rt.drawn = rt.pt.samples; needsRender = false; placeLabels();
  }

  function frame(now) {
    controls.update();
    const gap = now - rt.prev; rt.prev = now;
    if (rt.on && rt.pt) {
      const camBusy = now - lastCam < 250;
      if (rt.liteCam && camBusy) setBadge('ray tracing · resumes when the camera stops');
      else {
        try {
          setLook('traced');
          if (camBusy !== rt.motion) {
            rt.motion = camBusy;
            rt.pt.renderScale = rt.scale * (camBusy ? 0.6 : 1);
            rt.pt.bounces = camBusy ? 3 : 5;
            rt.camDirty = true;
          }
          if (rt.geoDirty || rt.matDirty || rt.camDirty) {
            if (rt.geoDirty) rt.pt.setScene(scene, camera);
            else { if (rt.matDirty) rt.pt.updateMaterials(); if (rt.camDirty) rt.pt.updateCamera(); }
            rt.geoDirty = rt.matDirty = rt.camDirty = false; rt.drawn = -1;
          }
          const compiling = rt.pt.isCompiling;
          if (rt.pt.samples < rt.max) {
            if (!compiling && gap < 200) {
              // steer samples per frame by frame time
              if (gap < 19) { rt.slow = 0; if (++rt.fast > 10) { rt.fast = 0; rt.spf = Math.min(12, rt.spf + 1); } }
              else if (gap > 30) {
                rt.fast = 0;
                if (++rt.slow > 3) {
                  rt.slow = 0;
                  if (rt.spf > 1) rt.spf--;
                  else if (camBusy) rt.liteCam = true;
                  else if (rt.pt.tiles.x < 3) rt.pt.tiles.set(rt.pt.tiles.x + 1, rt.pt.tiles.x + 1);
                }
              }
            }
            const n = compiling ? 1 : rt.spf;
            for (let k = 0; k < n && rt.pt.samples < rt.max; k++) rt.pt.renderSample();
          }
          if (rt.pt.samples >= 1) { if (rt.pt.samples !== rt.drawn || needsRender) tracedRender(); }
          else if (needsRender) rasterRender();
          setBadge(compiling ? 'ray tracing · compiling shaders' : 'ray tracing · ' + Math.floor(rt.pt.samples) + ' / ' + rt.max + ' samples');
          return;
        } catch (err) {
          console.error(err); rt.on = false; $('#rt').checked = false; needsRender = true; setBadge('ray tracing failed, using the standard renderer');
        }
      }
    }
    if (needsRender) rasterRender();
  }

  const v3 = new THREE.Vector3();
  function project(p) { v3.copy(p).project(camera); return v3.z > 1 || v3.z < -1 ? null : [(v3.x * 0.5 + 0.5) * stage.clientWidth, (-v3.y * 0.5 + 0.5) * stage.clientHeight]; }
  function placeLabels() {
    const w = stage.clientWidth, h = stage.clientHeight;
    for (const t of tickLabels) {
      const q = project(t.p), ok = q && q[0] > 12 && q[0] < w - 12 && q[1] > 28 && q[1] < h - 6;
      t.el.hidden = !ok; if (ok) t.el.style.transform = 'translate(' + q[0].toFixed(1) + 'px,' + q[1].toFixed(1) + 'px) translate(-50%,-50%)';
    }
    // Row names: the hovered row always shows; the rest show front to back wherever they do not collide.
    const pts = rowLabels.map((r) => project(r.p)), taken = [];
    const fits = (q) => q && q[0] > 30 && q[0] < w && q[1] > 28 && q[1] < h - 4;
    if (S.hover >= 0 && fits(pts[S.hover])) taken.push(pts[S.hover][1]);
    rowLabels.forEach((r, i) => {
      const q = pts[i];
      let ok = fits(q);
      if (ok && i !== S.hover) { ok = taken.every((y) => Math.abs(y - q[1]) >= 13); if (ok) taken.push(q[1]); }
      r.el.hidden = !ok; if (ok) r.el.style.transform = 'translate(' + q[0].toFixed(1) + 'px,' + q[1].toFixed(1) + 'px) translate(-100%,-50%)';
    });
  }

  function resize() {
    const w = Math.max(2, stage.clientWidth), h = Math.max(2, stage.clientHeight);
    renderer.setSize(w, h, false);
    composer.setSize(w, h);
    if (rt.composer) { rt.composer.setSize(w, h); const pr = renderer.getPixelRatio(); rt.overlay.setSize(Math.round(w * pr), Math.round(h * pr)); }
    camera.aspect = w / h; camera.updateProjectionMatrix();
    if (!userMoved) resetView();
    camChanged();
  }
  new ResizeObserver(resize).observe(stage);

  // picking: hover a ridge for details, click to move the slice
  const ray = new THREE.Raycaster(), ndc = new THREE.Vector2(), ground = new THREE.Plane(new THREE.Vector3(0, 1, 0), 0), hitV = new THREE.Vector3();
  function pick(e) {
    const r = canvas.getBoundingClientRect();
    ndc.set(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1);
    ray.setFromCamera(ndc, camera);
    const hit = ray.intersectObjects(bodies, false)[0];
    if (hit) return { i: hit.object.userData.i, t: S.v0 + clamp((hit.point.x - X0) / W, 0, 1) * (S.v1 - S.v0) };
    return ray.ray.intersectPlane(ground, hitV) && Math.abs(hitV.z) < D / 2 + 1.5 && hitV.x > X0 - 0.5 && hitV.x < X0 + W + 0.5 ? { i: -1, t: S.v0 + clamp((hitV.x - X0) / W, 0, 1) * (S.v1 - S.v0) } : null;
  }
  let down = null;
  canvas.addEventListener('pointerdown', (e) => { down = [e.clientX, e.clientY]; hideTip(); });
  canvas.addEventListener('pointermove', (e) => {
    if (e.buttons) return;
    const h = pick(e);
    if (h && h.i >= 0) { api.onHover(h.i); showTip(nodeTip(S.rows[h.i], h.t), e.clientX, e.clientY); } else { api.onHover(-1); hideTip(); }
  });
  canvas.addEventListener('pointerup', (e) => { if (down && Math.hypot(e.clientX - down[0], e.clientY - down[1]) < 5) { const h = pick(e); if (h) api.onPick(h.t); } down = null; });
  canvas.addEventListener('pointerleave', () => { api.onHover(-1); hideTip(); });

  const api = { software, setRows, setCursor, setHover, setRT, resetView, touch, frame, onHover: () => {}, onPick: () => {}, debug: { rt, scene, camera, renderer } };
  resize();
  setRows();
  return api;
}

// ---------------------------------------------------------------- boot
let last = performance.now(), lastUI = 0;
function frame(now) {
  const dt = Math.min(0.1, (now - last) / 1000); last = now;
  if (S.playing) {
    setT(S.t + dt * ((S.v1 - S.v0) / PLAY_SECONDS) * S.speed);
    if (S.t >= S.v1) { S.playing = false; syncPlay(); }
  }
  if (dirty.tl) { drawTimeline(); dirty.tl = false; }
  if (dirty.ui && now - lastUI > 90) { updateUI(); dirty.ui = false; lastUI = now; }
  if (view3d) view3d.frame(now);
  requestAnimationFrame(frame);
}

// The render loop and the 3D scene start once the first trace is on screen.
let started = false;
function start() {
  if (started) return;
  started = true;
  requestAnimationFrame(frame);
  init3D().then((v) => {
    if (!v) return;
    v.onHover = setHover;
    v.onPick = setT;
    view3d = v;
    window.__wt = { S, view3d: v };
    let wantRT = !v.software && !window.matchMedia('(pointer: coarse)').matches;
    try { const saved = localStorage.getItem('stracewave.rt'); if (saved !== null) wantRT = saved === '1'; } catch (err) { /* storage is optional */ }
    $('#rt').checked = wantRT;
    if (wantRT) v.setRT(true);
  });
}
openExample('uv');
if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => { dirty.tl = true; });
