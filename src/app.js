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
  solo: new Set(), mute: new Set(), unfolded: new Set(),   // per-row view switches, by node id
  rows3: [], r3: [], row3Of: new Map(),                   // rows the 3D view shows, and how timeline rows and tree nodes map onto them
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
  S.solo.clear(); S.mute.clear(); S.unfolded.clear();
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
let rowEls = [], rowParts = [], tlCols = 0, tlW = 0;

function rowsChanged() {
  S.rows = visibleRows();
  S.rowOf = new Map();
  S.rows.forEach((n, i) => {
    if (S.expanded.has(n.id)) { if (!n.isFold) S.rowOf.set(n, i); }
    else (function mark(x) { if (!x.isFold) S.rowOf.set(x, i); x.children.forEach(mark); })(n);
  });
  // solo and mute decide which rows reach the 3D view; the timeline always lists every row
  const ids = new Set(S.rows.map((n) => n.id));
  for (const set of [S.solo, S.mute, S.unfolded]) for (const id of set) if (!ids.has(id)) set.delete(id);
  S.rows3 = S.rows.filter((n) => (S.solo.size ? S.solo.has(n.id) : !S.mute.has(n.id)));
  S.r3 = S.rows.map((n) => S.rows3.indexOf(n));
  S.row3Of = new Map();
  for (const [node, i] of S.rowOf) if (S.r3[i] >= 0) S.row3Of.set(node, S.r3[i]);
  const tool = (act, glyph, title, on) => '<button type="button" class="tool" data-act="' + act + '" aria-pressed="' + on + '" title="' + title + '">' + glyph + '</button>';
  tlLabels.innerHTML = '<div class="axis-pad"><span>Timeline</span><button type="button" class="zoom-reset" id="zoomReset" title="Show the whole trace" hidden></button></div>' + S.rows.map((n, i) => {
    const has = n.children.length > 0, open = S.expanded.has(n.id), k = n.procs.length;
    return '<div class="row' + (S.r3[i] < 0 ? ' off' : '') + '" data-i="' + i + '" style="--d:' + n.vdepth + '">' +
      '<button type="button" class="rowmain"' + (has ? ' aria-expanded="' + open + '"' : '') + '>' +
      '<span class="st" data-st=""></span><span class="caret">' + (has ? (open ? '▾' : '▸') : '') + '</span>' +
      '<i class="chip" style="background:' + colorFor(n.name) + '"></i><span class="nm">' + esc(n.name) + '</span>' +
      '<span class="ct">(' + k.toLocaleString() + (k === 1 ? ' unit' : ' units') + ')</span><span class="fl"></span></button>' +
      '<span class="tools">' + tool('blocks', '▤', 'Show each process as a block in 3D', S.unfolded.has(n.id)) +
      tool('solo', 'S', 'Solo: show only the soloed rows in 3D', S.solo.has(n.id)) + tool('mute', 'M', 'Mute: hide this row in 3D', S.mute.has(n.id)) + '</span></div>';
  }).join('');
  rowEls = [...tlLabels.querySelectorAll('.row')];
  rowParts = rowEls.map((el) => ({ st: el.querySelector('.st'), fl: el.querySelector('.fl') }));
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
    const n = S.rows[i], st = stateOf(n, t), sEl = rowParts[i].st;
    if (sEl.dataset.st !== st) { sEl.dataset.st = st; sEl.textContent = GLYPH[st]; }
    const f = ub(n.failEnds, t), fEl = rowParts[i].fl, txt = f ? '×' + f : '';
    if (fEl.textContent !== txt) fEl.textContent = txt;
  }
  // name tags in 3D: the busy processes that have been running longest at the slice, one per row
  if (view3d) {
    const busy = [];
    for (const a of S.busy.procs) { if (a.start > t) break; if (t < a.end && t - a.p.start >= 0.3) busy.push(a.p); }
    busy.sort((x, y) => x.start - y.start);
    const tags = [], used = new Set();
    for (const p of busy) {
      const k = S.row3Of.get(p.node);
      if (k === undefined || used.has(k)) continue;
      used.add(k); tags.push({ k, text: shortLabel(p) + ' · ' + fmtD(t - p.start) });
      if (tags.length === 3) break;
    }
    view3d.setTags(tags);
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

// ---------------------------------------------------------------- sound
// A mixing desk driven by the trace. Every row shown in 3D is its own track:
//  - a track holds one note of the A minor pentatonic scale (front rows low, back rows high), so any combination of
//    tracks is consonant. Its timbre is picked by program name, and it sits at its own place between left and right;
//  - a track's volume is the height of its ridge where the slice cuts it, so the mix is the slice. Soloing or muting
//    a row does the same to its track, and pointing at a row brings its track forward;
//  - a bass note under everything follows how busy the machine is and walks through A, F, C, G along the timeline;
//  - a process that starts on a different row from its parent rings a bell on that row's note, an octave up. At most
//    about six a second, the longest-lived process winning;
//  - everything goes through a reverb, and the bells through an echo. It sounds while the slice moves and rings out
//    when it stops.
const SCALE = [45, 48, 50, 52, 55, 57, 60, 62, 64, 67, 69, 72, 74, 76, 79];   // MIDI notes, A2 to G5
const BASS = [33, 29, 36, 31];                                                // A1, F1, C2, G1
const MAX_TRACKS = 32;
const hz = (midi) => 440 * Math.pow(2, (midi - 69) / 12);
const audio = { dest: null, ctx: null, on: false, moved: 0, lastT: 0, lastPluck: 0, tracks: [], rowsRef: null, timbres: [], bass: [], bassGain: null, bus: null, filter: null, out: null, master: null, wet: null, echo: null, analyser: null };
function levelAt(n, t) {
  const s = seriesOf(n, BINS_3D), f = clamp(((t - S.v0) / (S.v1 - S.v0)) * BINS_3D - 0.5, 0, BINS_3D - 1), a = Math.floor(f), b = Math.min(BINS_3D - 1, a + 1);
  return s[a] + (s[b] - s[a]) * (f - a);
}
function setSound(on) {
  audio.on = on;
  if (on && !audio.ctx) {
    const Ctx = window.AudioContext || window.webkitAudioContext;
    if (!Ctx) { $('#sound').checked = false; audio.on = false; toast('This browser has no Web Audio.'); return; }
    const ctx = audio.ctx = new Ctx();
    const comp = ctx.createDynamicsCompressor(); comp.threshold.value = -16; comp.ratio.value = 4;
    audio.analyser = ctx.createAnalyser(); audio.analyser.fftSize = 2048;
    audio.master = ctx.createGain(); audio.master.gain.value = 0.9;
    audio.master.connect(comp).connect(audio.analyser).connect(ctx.destination);
    // reverb from a generated impulse: stereo noise that dies away over 2.6 seconds
    const conv = ctx.createConvolver(), len = Math.floor(ctx.sampleRate * 2.6), ir = ctx.createBuffer(2, len, ctx.sampleRate);
    for (let c = 0; c < 2; c++) { const d = ir.getChannelData(c); for (let i = 0; i < len; i++) d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / len, 2.6); }
    conv.buffer = ir;
    audio.wet = ctx.createGain();
    const wetOut = ctx.createGain(); wetOut.gain.value = 0.3;
    audio.wet.connect(conv).connect(wetOut).connect(audio.master);
    // echo for the bells: a filtered delay that feeds back into itself
    audio.echo = ctx.createDelay(1); audio.echo.delayTime.value = 0.33;
    const fb = ctx.createGain(); fb.gain.value = 0.38;
    const damp = ctx.createBiquadFilter(); damp.type = 'lowpass'; damp.frequency.value = 1800;
    const echoOut = ctx.createGain(); echoOut.gain.value = 0.45;
    audio.echo.connect(damp).connect(fb).connect(audio.echo);
    damp.connect(echoOut).connect(audio.master); echoOut.connect(audio.wet);
    // tracks and bass share one low-pass filter and one output fader
    audio.bus = ctx.createGain();
    audio.filter = ctx.createBiquadFilter(); audio.filter.type = 'lowpass'; audio.filter.frequency.value = 700; audio.filter.Q.value = 0.5;
    audio.out = ctx.createGain(); audio.out.gain.value = 0;
    audio.bus.connect(audio.filter).connect(audio.out); audio.out.connect(audio.master); audio.out.connect(audio.wet);
    // three timbres, from round to slightly hollow to slightly bright; all soft
    const wave = (partials) => ctx.createPeriodicWave(new Float32Array(partials.length + 1), Float32Array.from([0, ...partials]));
    audio.timbres = [wave([1, 0.25, 0.08]), wave([1, 0, 0.33, 0, 0.12, 0, 0.05]), wave([1, 0.5, 0.18, 0.3, 0.05, 0.1])];
    audio.bassGain = ctx.createGain(); audio.bassGain.gain.value = 0; audio.bassGain.connect(audio.bus);
    for (const [type, oct, amp] of [['sine', 1, 0.5], ['triangle', 2, 0.22]]) {
      const osc = ctx.createOscillator(), g = ctx.createGain();
      osc.type = type; osc.frequency.value = hz(BASS[0]) * oct; g.gain.value = amp;
      osc.connect(g).connect(audio.bassGain); osc.start();
      audio.bass.push({ osc, oct });
    }
  }
  if (audio.ctx) { if (on) audio.ctx.resume(); else audio.out.gain.setTargetAtTime(0, audio.ctx.currentTime, 0.1); }
}
// One oscillator per row shown in 3D. Rebuilt whenever that set of rows changes.
function buildTracks() {
  const ctx = audio.ctx, rows = S.rows3.slice(0, MAX_TRACKS), R = rows.length;
  for (const t of audio.tracks) { t.osc.stop(); t.last.disconnect(); }
  audio.tracks = rows.map((n, k) => {
    const osc = ctx.createOscillator(), gain = ctx.createGain();
    const note = SCALE[Math.round((k / Math.max(1, R - 1)) * (SCALE.length - 1))];
    let h = 0; for (const ch of n.name) h = (h * 31 + ch.charCodeAt(0)) >>> 0;
    osc.setPeriodicWave(audio.timbres[h % audio.timbres.length]);
    osc.frequency.value = hz(note); osc.detune.value = ((k * 7) % 11) - 5;      // a few cents apart, so shared notes shimmer instead of phasing
    gain.gain.value = 0;
    osc.connect(gain);
    let last = gain;
    if (ctx.createStereoPanner) { last = ctx.createStereoPanner(); last.pan.value = R > 1 ? (k / (R - 1)) * 1.3 - 0.65 : 0; gain.connect(last); }
    last.connect(audio.bus); osc.start();
    return { osc, gain, last, node: n, note };
  });
  audio.rowsRef = S.rows3;
}
// A soft bell: a sine with quieter partials above it that fade faster, panned, with reverb and echo.
function pluck(midi, level, pan) {
  const ctx = audio.ctx, at = ctx.currentTime, g = ctx.createGain();
  for (const [mult, amp, decay] of [[1, 1, 0.9], [2, 0.28, 0.35], [3, 0.08, 0.2]]) {
    const osc = ctx.createOscillator(), e = ctx.createGain();
    osc.frequency.value = hz(midi) * mult;
    e.gain.setValueAtTime(0, at); e.gain.linearRampToValueAtTime(level * amp, at + 0.008); e.gain.exponentialRampToValueAtTime(0.0001, at + decay);
    osc.connect(e).connect(g); osc.start(at); osc.stop(at + decay + 0.05);
  }
  let out = g;
  if (ctx.createStereoPanner) { out = ctx.createStereoPanner(); out.pan.value = pan; g.connect(out); }
  out.connect(audio.master); out.connect(audio.wet); out.connect(audio.echo);
}
function updateSound(now) {
  if (!audio.on || !audio.ctx) return;
  const ctx = audio.ctx, at = ctx.currentTime, where = (S.t - S.v0) / (S.v1 - S.v0);
  if (audio.rowsRef !== S.rows3) buildTracks();
  const tracks = audio.tracks, R = tracks.length, hot = S.hover >= 0 ? S.r3[S.hover] : -1;
  const sounding = S.playing || now - audio.moved < 250;
  const busy = clamp(levelAt(S.busy, S.t) / Math.max(1, S.cores), 0, 1);
  // the mix: each track as loud as its ridge is tall at the slice; the pointed-at track comes forward
  const unit = 0.3 / Math.sqrt(Math.max(1, R));
  tracks.forEach((t, k) => {
    const lift = hot < 0 ? 1 : k === hot ? 2 : 0.45;
    t.gain.gain.setTargetAtTime(unit * Math.pow(hOf(levelAt(t.node, S.t)), 1.3) * lift, at, 0.07);
  });
  const root = BASS[Math.min(7, Math.floor(where * 8)) % 4];
  for (const b of audio.bass) b.osc.frequency.setTargetAtTime(hz(root) * b.oct, at, 0.1);
  audio.bassGain.gain.setTargetAtTime(0.1 + 0.2 * busy, at, 0.15);
  audio.filter.frequency.setTargetAtTime(500 + 3000 * Math.pow(busy, 0.8), at, 0.12);
  if (sounding) {
    // bells: of the processes started since the last update, the longest-lived one that landed on another row
    const from = audio.lastT, to = S.t;
    if (to > from && to - from < (S.v1 - S.v0) * 0.05 && R && now - audio.lastPluck >= 150) {
      let best = null;
      for (let i = ub(S.starts, from), end = ub(S.starts, to); i < end; i++) {
        const p = S.procs[i];
        if (p.parent < 0) continue;
        const kc = S.row3Of.get(p.node), kp = S.row3Of.get(S.procs[p.parent].node);
        if (kc !== undefined && kc !== kp && kc < R && (!best || p.end - p.start > best[0])) best = [p.end - p.start, kc];
      }
      if (best) {
        audio.lastPluck = now;
        pluck(tracks[best[1]].note + 12, 0.05 + 0.05 * clamp(Math.log10(1 + best[0]) / 2, 0, 1), clamp(where * 1.4 - 0.7, -0.7, 0.7));
      }
    }
  }
  audio.lastT = S.t;
  audio.out.gain.setTargetAtTime(sounding ? 1 : 0, at, sounding ? 0.12 : 0.35);
}

// ---------------------------------------------------------------- video export
// Recording plays the visible range from its start and captures it, sound included, in real time. The picture is
// composed on a canvas of its own each frame: the 3D view with its labels, then the timeline with its row names.
const rec = { active: false, canvas: document.createElement('canvas'), g: null, recorder: null, chunks: [], mime: '', ending: 0, last: null, lay: null };
const REC_W = 1920, REC_PAD = 36, REC_HEAD = 92, REC_FOOT = 64;
const FONT_UI = '"Space Grotesk", system-ui, sans-serif', FONT_MONO = '"JetBrains Mono", ui-monospace, monospace';

function startRecording() {
  if (!window.MediaRecorder || !rec.canvas.captureStream) { toast('This browser cannot record video.', 4000); return; }
  if (!view3d) { toast('The 3D view is not ready yet.'); return; }
  if (!audio.on) { $('#sound').checked = true; setSound(true); }
  if (!audio.ctx) { toast('Sound is not available, so there is nothing to record with the picture.', 4000); return; }
  if (!audio.dest) { audio.dest = audio.ctx.createMediaStreamDestination(); audio.analyser.connect(audio.dest); }
  // fix the layout for the whole take
  const stage = $('#stage'), labelsW = tlLabels.clientWidth, barsW = tlCanvas.clientWidth, gap = 10;
  const h3 = Math.round((REC_W * stage.clientHeight) / stage.clientWidth), ft = (REC_W - 2 * REC_PAD) / (labelsW + gap + barsW);
  const tlH = Math.round((TOP + S.rows.length * ROW_H) * ft);
  rec.lay = { h3, ft, tlH, tlY: REC_HEAD + h3 + 20, barsX: REC_PAD + (labelsW + gap) * ft, barsW: barsW * ft };
  rec.canvas.width = REC_W; rec.canvas.height = Math.ceil((rec.lay.tlY + tlH + REC_FOOT) / 2) * 2;
  rec.g = rec.canvas.getContext('2d');
  const stream = rec.canvas.captureStream(30);
  for (const track of audio.dest.stream.getAudioTracks()) stream.addTrack(track);
  rec.mime = ['video/mp4;codecs=avc1.640033,mp4a.40.2', 'video/mp4;codecs=avc1.640033,opus', 'video/webm;codecs=vp9,opus', 'video/webm'].find((m) => MediaRecorder.isTypeSupported(m)) || '';
  rec.chunks = [];
  rec.recorder = new MediaRecorder(stream, { mimeType: rec.mime || undefined, videoBitsPerSecond: 16e6, audioBitsPerSecond: 192e3 });
  rec.recorder.ondataavailable = (e) => { if (e.data.size) rec.chunks.push(e.data); };
  rec.recorder.onstop = saveRecording;
  S.playing = false; setT(S.v0); syncPlay();
  rec.active = true; rec.ending = 0;
  composeFrame();
  rec.recorder.start(1000);
  setTimeout(() => { if (rec.active) { S.playing = true; syncPlay(); } }, 500);      // half a second of still picture first
  syncRecord();
}
function stopRecording() {
  if (!rec.active) return;
  rec.active = false; S.playing = false; syncPlay();
  if (rec.recorder.state !== 'inactive') rec.recorder.stop();
  syncRecord();
}
function saveRecording() {
  const ext = rec.mime.includes('mp4') ? 'mp4' : 'webm';
  rec.last = new Blob(rec.chunks, { type: rec.mime.split(';')[0] || 'video/webm' });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(rec.last); a.download = 'stracewave-' + (S.key === 'file' ? 'trace' : S.key) + '.' + ext;
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 60000);
  toast('Saved ' + a.download + ' (' + (rec.last.size / 1e6).toFixed(1) + ' MB)', 5000);
}
function syncRecord() { const b = $('#record'); b.textContent = rec.active ? '■ Stop recording' : 'Record video'; b.classList.toggle('live', rec.active); }

function composeFrame() {
  const g = rec.g, L = rec.lay, W = rec.canvas.width, Ht = rec.canvas.height, glc = $('#gl'), stage = $('#stage');
  g.fillStyle = '#0d1117'; g.fillRect(0, 0, W, Ht);
  g.textBaseline = 'middle'; g.textAlign = 'left';
  // header: name, what was traced, where the slice is
  g.fillStyle = '#e6ebf4'; g.font = '600 34px ' + FONT_UI; g.fillText('stracewave', REC_PAD, 36);
  g.fillStyle = '#6f7b90'; g.font = '18px ' + FONT_MONO; g.fillText($('#meta').innerText.replace(' · approximate tree', ''), REC_PAD, 70);
  g.textAlign = 'right'; g.fillStyle = '#e6ebf4'; g.font = '34px ' + FONT_MONO; g.fillText(fmtT(S.t), W - REC_PAD, 40);
  g.fillStyle = '#6f7b90'; g.font = '18px ' + FONT_MONO; g.fillText('of ' + fmtT(S.span), W - REC_PAD, 72);
  g.textAlign = 'left';
  // 3D view and the labels that float over it
  g.drawImage(glc, 0, REC_HEAD, W, L.h3);
  const sr = stage.getBoundingClientRect(), k = W / sr.width, COLORS = { tick: '#6f7b90', rowl: '#aab4c5', corel: '#8fd3ff', crit: '#ffffff', tag: '#e6ebf4' };
  g.font = Math.round(11 * k) + 'px ' + FONT_MONO;
  for (const el of $('#glLabels').children) {
    if (el.hidden) continue;
    const r = el.getBoundingClientRect(), cls = el.className.split(' ')[0];
    let x = (r.left - sr.left) * k; const y = REC_HEAD + (r.top - sr.top + r.height / 2) * k;
    if (y < REC_HEAD + 8 || y > REC_HEAD + L.h3 - 8) continue;
    if (cls === 'tag') { g.fillStyle = 'rgba(8,11,16,0.8)'; g.fillRect(x, y - r.height * k / 2, r.width * k, r.height * k); x += 5 * k; }
    const chip = el.firstElementChild;
    if (chip) { g.fillStyle = chip.style.background; g.fillRect(x, y - 3.5 * k, 7 * k, 7 * k); x += 12 * k; }
    g.fillStyle = el.classList.contains('hot') ? '#e6ebf4' : COLORS[cls] || '#aab4c5';
    g.fillText(el.textContent, x, y);
  }
  // timeline: bars from its own canvas, row names redrawn beside them
  const ft = L.ft, y0 = L.tlY;
  g.drawImage(tlCanvas, L.barsX, y0, L.barsW, L.tlH);
  g.fillStyle = '#6f7b90'; g.font = '500 ' + Math.round(11 * ft) + 'px ' + FONT_UI; g.fillText('TIMELINE', REC_PAD, y0 + (TOP - 14) * ft);
  g.font = Math.round(12.5 * ft) + 'px ' + FONT_MONO;
  const ST = { done: '#0ca30c', running: '#fab219', idle: 'rgba(250,178,25,0.45)', waiting: '#6f7b90' };
  S.rows.forEach((n, i) => {
    const y = y0 + (TOP + i * ROW_H + ROW_H / 2) * ft, st = rowParts[i].st;
    let x = REC_PAD + 2 * ft;
    g.globalAlpha = S.r3[i] < 0 ? 0.42 : 1;
    g.fillStyle = ST[st.dataset.st] || '#6f7b90'; g.fillText(st.textContent, x, y);
    x += (18 + n.vdepth * 14 + 16) * ft;
    g.fillStyle = colorFor(n.name); g.fillRect(x, y - 4 * ft, 8 * ft, 8 * ft); x += 14 * ft;
    g.fillStyle = '#aab4c5'; g.fillText(n.name, x, y); x += g.measureText(n.name).width + 6 * ft;
    g.fillStyle = '#6f7b90'; g.fillText('(' + n.procs.length.toLocaleString() + (n.procs.length === 1 ? ' unit)' : ' units)'), x, y);
    g.globalAlpha = 1;
  });
  g.fillStyle = '#aab4c5'; g.font = Math.round(12.5 * ft) + 'px ' + FONT_MONO;
  g.fillText($('#tlFoot').innerText.replace(/\s*\n\s*/g, ' ').replace(/\s{2,}/g, ' ').replace(/ (✓|►|·|×) /g, '     $1 '), REC_PAD, y0 + L.tlH + REC_FOOT / 2);
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
function procTip(p) {
  return '<div class="p">' + esc(shortLabel(p)) + '</div>' +
    '<div>' + fmtT(p.start) + ' → ' + fmtT(p.end) + ' · ' + fmtD(p.end - p.start) + (p.exit ? ' · exit ' + (p.exit < 0 ? 'by signal' : p.exit) : '') + '</div>' +
    (p.cmd ? '<div class="c">' + esc(p.cmd) + '</div>' : '');
}
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
  if (view3d) view3d.setHover(i >= 0 ? S.r3[i] : -1);
}
function setT(t) {
  S.t = clamp(t, S.v0, S.v1);
  audio.moved = performance.now();
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
  const n = S.rows[+b.dataset.i]; if (!n) return;
  const tl = e.target.closest('.tool');
  if (tl) {
    const act = tl.dataset.act, set = { blocks: S.unfolded, solo: S.solo, mute: S.mute }[act];
    if (set.has(n.id)) set.delete(n.id); else set.add(n.id);
    if (act === 'solo') S.mute.delete(n.id);
    if (act === 'mute') S.solo.delete(n.id);
    S.hover = -1;
    rowsChanged();
    return;
  }
  if (!n.children.length) return;
  if (S.expanded.has(n.id)) S.expanded.delete(n.id); else S.expanded.add(n.id);
  S.hover = -1;
  rowsChanged();
  const again = rowEls[S.rows.indexOf(n)]; if (again) again.querySelector('.rowmain').focus({ preventScroll: true });
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
$('#rt').addEventListener('change', (e) => {
  if (!view3d) { e.target.checked = false; return; }
  try { localStorage.setItem('stracewave.raytracing', e.target.checked ? '1' : '0'); } catch (err) { /* storage is optional */ }
  view3d.setRT(e.target.checked);
});
$('#glass').addEventListener('change', (e) => {
  try { localStorage.setItem('stracewave.glass', e.target.checked ? '1' : '0'); } catch (err) { /* storage is optional */ }
  if (view3d) view3d.setGlass(e.target.checked);
});
$('#sound').addEventListener('change', (e) => setSound(e.target.checked));
$('#record').addEventListener('click', () => (rec.active ? stopRecording() : startRecording()));
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
    const xa = X0 - 3.2, xb = X0 + W + 2.2, za = zWall - 0.6, zb = D / 2 + 1.9, q = new THREE.Vector3();
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
  // In front of a glass ridge the slice should show through, dimmed: this multiplies what is already drawn instead of hiding it.
  const veilMat = new THREE.MeshBasicMaterial({ color: 0x000000, transparent: true, opacity: 0.4, depthWrite: false, blending: THREE.CustomBlending,
    blendSrc: THREE.ZeroFactor, blendDst: THREE.OneMinusSrcAlphaFactor, blendSrcAlpha: THREE.ZeroFactor, blendDstAlpha: THREE.OneMinusSrcAlphaFactor });
  const WHITE = new THREE.Color(0xffffff);
  let glass = true, hoverK = -1;
  // Hover highlight for the ray-traced picture. It is drawn in the overlay, on top of the traced image, so pointing
  // at a row never restarts the path tracer. The raster renderer brightens and dims the materials themselves.
  const hlMat = (opacity) => new THREE.MeshBasicMaterial({ transparent: true, opacity, blending: THREE.AdditiveBlending, depthWrite: false, side: THREE.DoubleSide });
  const hlFill = new THREE.Mesh(new THREE.BufferGeometry(), hlMat(0.2)), hlEdge = new THREE.Mesh(new THREE.BufferGeometry(), hlMat(0.9));
  for (const m of [hlFill, hlEdge]) { m.renderOrder = 5; m.visible = false; m.frustumCulled = false; overlayScene.add(m); }
  overlayScene.add(occluders);
  const wall = new THREE.Group(); scene.add(wall);
  // per-row state, indexed like S.rows3
  let gl = [], pickables = [], beads = [], rowLabels = [], tickLabels = [], fixedLabels = [], tagEls = [], tags = [], zWall = 0, wallSeries = null;
  // spawn arcs: a short-lived line from the parent's ridge to the child's, drawn for processes started just behind the slice
  const ARC_MAX = 64, ARC_SEG = 10;
  const arcGeo = new THREE.BufferGeometry();
  arcGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(ARC_MAX * ARC_SEG * 6), 3));
  arcGeo.setAttribute('color', new THREE.BufferAttribute(new Float32Array(ARC_MAX * ARC_SEG * 6), 3));
  const arcs = new THREE.LineSegments(arcGeo, new THREE.LineBasicMaterial({ vertexColors: true, transparent: true, blending: THREE.AdditiveBlending, depthWrite: false }));
  arcs.frustumCulled = false; scene.add(arcs);
  const threeColor = new Map();
  const colOf = (name) => { let c = threeColor.get(name); if (!c) { c = new THREE.Color(colorFor(name)); threeColor.set(name, c); } return c; };

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

  function heightAt(s, t) {
    const f = clamp(((t - S.v0) / (S.v1 - S.v0)) * BINS_3D - 0.5, 0, BINS_3D - 1), a = Math.floor(f), b = Math.min(BINS_3D - 1, a + 1);
    return Y0 + H * hOf(s[a] + (s[b] - s[a]) * (f - a));
  }
  const sampleRow = (k, t) => (gl[k].laneH ? Y0 + Math.min(H, gl[k].laneH * liveCount(gl[k].node, t)) : heightAt(gl[k].series, t));

  // A ridge: a face that glows from the baseline up, and a crest that is bright where the ridge rises and dim along the baseline.
  function makeRidge(s, col, th, fill) {
    const P = BINS_3D + 2, zf = th / 2, zb = -th / 2, lw = 0.05;
    const xs = new Float32Array(P), hs = new Float32Array(P);
    for (let k = 0; k < P; k++) {
      const b = clamp(k - 1, 0, BINS_3D - 1);
      xs[k] = X0 + W * (k === 0 ? 0 : k === P - 1 ? 1 : (b + 0.5) / BINS_3D);
      hs[k] = Y0 + H * hOf(s[b]);
    }
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
    const body = new THREE.Mesh(bodyGeo, new THREE.MeshPhysicalMaterial({ color: col.clone().multiplyScalar(0.05), roughness: 0.4, metalness: 0, emissive: col, emissiveMap: fillTex, emissiveIntensity: fill }));
    let base = fill, hot = false, dim = false, applied = 0;
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
      return new THREE.Mesh(g, new THREE.MeshStandardMaterial({ color: 0x000000, emissive: col, emissiveIntensity: intensity, roughness: 1, side: THREE.DoubleSide }));
    };
    const crest = mkCrest(ci, 1.35), rest = mkCrest(cb, 0.16);
    return {
      meshes: [body, crest, rest], solids: [body], hs, th,
      tone(h, d) {
        hot = h; dim = d;
        body.material.emissiveIntensity = base * (hot ? 1.9 : dim ? 0.55 : 1);
        crest.material.emissiveIntensity = hot ? 2.6 : dim ? 0.7 : 1.35;
        rest.material.emissiveIntensity = hot ? 0.9 : 0.16;
      },
      // Glass: the path tracer refracts through a tinted pane; the raster renderer stands in with plain transparency.
      look(asGlass, traced) {
        const state = asGlass ? (traced ? 2 : 1) : 0;
        if (state === applied) return;
        applied = state;
        const m = body.material;
        if (!asGlass) { m.transmission = 0; m.transparent = false; m.opacity = 1; m.depthWrite = true; m.roughness = 0.4; m.color.copy(col).multiplyScalar(0.05); base = fill; }
        else if (traced) { m.transmission = 1; m.ior = 1.45; m.transparent = false; m.opacity = 1; m.depthWrite = true; m.roughness = 0.05; m.color.copy(col).lerp(WHITE, 0.55); m.attenuationColor.copy(col).lerp(WHITE, 0.3); m.attenuationDistance = 0.12; base = fill * 0.4; }
        else { m.transmission = 0; m.transparent = true; m.opacity = 0.42; m.depthWrite = false; m.roughness = 0.15; m.color.copy(col).multiplyScalar(0.12); base = fill * 0.75; }
        m.needsUpdate = true;
        this.tone(hot, dim);
      },
    };
  }

  // A row unfolded into its processes: one block each, stacked into lanes like a Gantt chart. Failed ones are red.
  function makeBlocks(n, col, th) {
    const minDur = (S.v1 - S.v0) / 700;
    let ps = n.procs.filter((p) => p.end > S.v0 && p.start < S.v1 && p.end - p.start >= minDur);
    if (ps.length > 4000) ps = ps.sort((a, b) => (b.end - b.start) - (a.end - a.start)).slice(0, 4000).sort((a, b) => a.start - b.start);
    const lanes = [], lane = new Array(ps.length);
    ps.forEach((p, i) => { let j = 0; while (j < lanes.length && lanes[j] > p.start) j++; lanes[j] = p.end; lane[i] = j; });
    const laneH = Math.min(0.17, (H * 0.96) / Math.max(1, lanes.length)), zh = Math.max(th, 0.06) / 2;
    const build = (list, emissive) => {
      const pos = new Float32Array(list.length * 24), idx = new Uint32Array(list.length * 36);
      list.forEach(([p, j], b) => {
        let x0 = xOf(Math.max(p.start, S.v0)), x1 = xOf(Math.min(p.end, S.v1));
        const gap = Math.min(0.012, (x1 - x0) * 0.2); x0 += gap; x1 -= gap;
        const y0 = Y0 + j * laneH + laneH * 0.1, y1 = Y0 + (j + 1) * laneH - laneH * 0.1;
        pos.set([x0, y0, zh, x1, y0, zh, x1, y1, zh, x0, y1, zh, x0, y0, -zh, x1, y0, -zh, x1, y1, -zh, x0, y1, -zh], b * 24);
        const o = b * 8;
        idx.set([0, 1, 2, 0, 2, 3, 5, 4, 7, 5, 7, 6, 3, 2, 6, 3, 6, 7, 4, 5, 1, 4, 1, 0, 1, 5, 6, 1, 6, 2, 4, 0, 3, 4, 3, 7].map((v) => v + o), b * 36);
      });
      const g = new THREE.BufferGeometry();
      g.setAttribute('position', new THREE.BufferAttribute(pos, 3));
      g.setIndex(new THREE.BufferAttribute(idx, 1));
      g.computeVertexNormals();
      const m = new THREE.Mesh(g, new THREE.MeshStandardMaterial({ color: emissive.clone().multiplyScalar(0.06), roughness: 0.45, emissive, emissiveIntensity: 0.8 }));
      m.userData.procs = list.map(([p]) => p);
      return m;
    };
    const all = ps.map((p, i) => [p, lane[i]]), ok = all.filter(([p]) => p.exit === 0), bad = all.filter(([p]) => p.exit !== 0);
    const meshes = [];
    if (ok.length) meshes.push(build(ok, col));
    if (bad.length) meshes.push(build(bad, new THREE.Color(0xd03b3b)));
    return {
      meshes, solids: meshes, laneH, th,
      tone(hot, dim) { for (const m of meshes) m.material.emissiveIntensity = hot ? 1.5 : dim ? 0.45 : 0.8; },
    };
  }

  function setRows() {
    for (const g of [ridges, wall]) { for (const m of g.children) { m.geometry.dispose(); m.material.dispose(); } g.clear(); }
    occluders.clear();
    for (const b of beads) { slice.remove(b); b.material.dispose(); }
    for (const t of ticks.children) t.geometry.dispose();
    ticks.clear(); gl = []; pickables = []; beads = [];
    threeColor.clear();
    const R = S.rows3.length;
    dz = clamp(11 / Math.max(1, R), 0.26, 0.8); D = dz * Math.max(0, R - 1);
    zWall = -D / 2 - Math.max(1.1, dz * 1.7);
    const th = Math.min(0.07, dz * 0.22);
    const place = (rec, z, group) => {
      for (const m of rec.meshes) { m.position.z = z; group.add(m); }
      for (const m of rec.solids) { const occ = new THREE.Mesh(m.geometry, occluderMat); occ.position.z = z; occ.userData.pane = !!rec.look && group === ridges; occluders.add(occ); }
    };
    const mkBead = (color, z) => {
      const b = new THREE.Mesh(beadGeo, new THREE.MeshStandardMaterial({ color: 0x000000, emissive: color.clone().lerp(new THREE.Color(0xffffff), 0.35), emissiveIntensity: 3, roughness: 1 }));
      b.position.z = z; slice.add(b); beads.push(b);
    };
    S.rows3.forEach((n, k) => {
      const col = colOf(n.name), unfolded = S.unfolded.has(n.id);
      const rec = unfolded ? makeBlocks(n, col, th) : makeRidge(seriesOf(n, BINS_3D), col, th, FILL);
      rec.node = n; rec.series = seriesOf(n, BINS_3D);
      place(rec, zOf(k), ridges);
      for (const m of rec.solids) { m.userData.k = k; pickables.push(m); }
      mkBead(col, zOf(k));
      gl.push(rec);
    });

    // back wall: busy processes in total, with the core count as a line across it
    wallSeries = seriesOf(S.busy, BINS_3D);
    const wallCol = new THREE.Color(0x9aa9c2);
    place(makeRidge(wallSeries, wallCol, 0.05, FILL * 0.5), zWall, wall);
    const coreY = Y0 + H * hOf(S.cores);
    const coreLine = new THREE.Mesh(new THREE.BoxGeometry(W + 0.5, 0.016, 0.016), new THREE.MeshStandardMaterial({ color: 0x000000, emissive: 0x8fd3ff, emissiveIntensity: 1.7, roughness: 1 }));
    coreLine.position.set(X0 + W / 2, coreY, zWall + 0.06); wall.add(coreLine);
    mkBead(wallCol, zWall);

    // critical chain: a white ribbon riding just above the ridge of each long link
    const cpos = [], cidx = [], crit = [];
    for (const seg of S.chain) {
      const k = S.row3Of.get(seg.p.node), a = Math.max(seg.start, S.v0), b = Math.min(seg.end, S.v1);
      if (k === undefined || b <= a) continue;
      const rec = gl[k], z = zOf(k) + rec.th / 2 + 0.006, n = Math.max(2, Math.ceil(((b - a) / (S.v1 - S.v0)) * BINS_3D));
      const base = cpos.length / 3;
      let top = 0;
      for (let i = 0; i <= n; i++) {
        const t = a + ((b - a) * i) / n, y = sampleRow(k, t) + 0.1;
        cpos.push(xOf(t), y + 0.022, z, xOf(t), y - 0.022, z);
        if (y > top) top = y;
        if (i < n) { const o = base + i * 2; cidx.push(o, o + 1, o + 2, o + 1, o + 3, o + 2); }
      }
      crit.push({ seg, d: b - a, p: new THREE.Vector3(xOf((a + b) / 2), top + 0.3, z) });
    }
    if (cidx.length) {
      const g = new THREE.BufferGeometry();
      g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(cpos), 3)); g.setIndex(cidx); g.computeVertexNormals();
      ridges.add(new THREE.Mesh(g, new THREE.MeshStandardMaterial({ color: 0x000000, emissive: 0xffffff, emissiveIntensity: 2.2, roughness: 1, side: THREE.DoubleSide })));
    }

    // the slice spans every row and the wall
    const zFar = zWall - 0.4, zNear = D / 2 + 0.8, zLen = zNear - zFar, zMid = (zNear + zFar) / 2, SH = H + 0.9;
    floor.scale.set(W + 400, D + 400, 1); frost.scale.copy(floor.scale);
    const ribbonIdx = [];
    for (let i = 0; i < R; i++) { const a = i * 2; ribbonIdx.push(a, a + 1, a + 2, a + 1, a + 3, a + 2); }
    ribbonGeo.setAttribute('position', new THREE.BufferAttribute(new Float32Array((R + 1) * 6), 3));
    ribbonGeo.deleteAttribute('normal');
    ribbonGeo.setIndex(ribbonIdx);
    sheet.scale.set(zLen, SH, 1); sheet.position.set(0, SH / 2, zMid);
    blade.scale.set(0.035, 0.02, zLen); blade.position.set(0, 0.012, zMid);
    frameTop.scale.set(0.02, 0.02, zLen); frameTop.position.set(0, SH, zMid);
    frameA.scale.set(0.02, SH, 0.02); frameA.position.set(0, SH / 2, zNear);
    frameB.scale.set(0.02, SH, 0.02); frameB.position.set(0, SH / 2, zFar);

    // labels: time ticks, row names, the wall, the core line, the longest critical links
    const step = niceStep((S.v1 - S.v0) / 8);
    labelsEl.textContent = ''; tickLabels = []; rowLabels = []; fixedLabels = []; tagEls = [];
    const label = (cls, text, chip) => {
      const el = document.createElement('span'); el.className = cls;
      if (chip) { const c = document.createElement('i'); c.style.background = chip; el.append(c); }
      el.append(text); labelsEl.appendChild(el); return el;
    };
    for (let v = Math.ceil(S.v0 / step - 1e-9) * step; v <= S.v1 + 1e-6; v += step) {
      const m = new THREE.Mesh(new THREE.BoxGeometry(0.014, 0.004, zLen), tickMat);
      m.position.set(xOf(v), 0.003, zMid); ticks.add(m);
      tickLabels.push({ el: label('tick', tickLabel(v, step)), p: new THREE.Vector3(xOf(v), 0, D / 2 + 1.25) });
    }
    S.rows3.forEach((n, k) => rowLabels.push({ el: label('rowl', n.name, colorFor(n.name)), p: new THREE.Vector3(X0 - 0.35, 0.05, zOf(k)) }));
    fixedLabels.push({ el: label('rowl', 'busy, all rows', '#9aa9c2'), p: new THREE.Vector3(X0 - 0.35, 0.05, zWall), align: 'right' });
    fixedLabels.push({ el: label('corel', S.cores + (S.cores === 1 ? ' core' : ' cores')), p: new THREE.Vector3(X0 + W + 0.45, coreY, zWall + 0.06), align: 'left' });
    crit.sort((a, b) => b.d - a.d).slice(0, 3).forEach((c) => fixedLabels.push({ el: label('crit', shortLabel(c.seg.p) + ' · ' + fmtD(c.seg.end - c.seg.start)), p: c.p, align: 'center' }));
    for (let i = 0; i < 3; i++) { const el = label('tag', ''); el.hidden = true; tagEls.push(el); }
    setHover(S.hover >= 0 ? S.r3[S.hover] : -1);
    applyLook();
    setCursor();
    if (!userMoved) resetView();
    sceneChanged();
  }

  // Materials that differ between the two renderers, and between glass and solid ridges.
  function applyLook() {
    const traced = look === 'traced';
    for (const rec of gl) if (rec.look) rec.look(glass, traced);
    for (const occ of occluders.children) { const pane = glass && occ.userData.pane; occ.material = pane ? veilMat : occluderMat; occ.renderOrder = pane ? 10 : 0; }
    sheetMat.depthWrite = traced;
  }
  function setGlass(on) { glass = on; applyLook(); sceneChanged(); }

  function updateArcs() {
    const pa = arcGeo.getAttribute('position'), ca = arcGeo.getAttribute('color'), pos = pa.array, col = ca.array;
    const t = S.t, w = (S.v1 - S.v0) * 0.04, lo = ub(S.starts, Math.max(S.v0, t - w)), hi = ub(S.starts, t);
    let n = 0;
    const perPair = new Map();
    for (let i = hi - 1; i >= lo && n < ARC_MAX; i--) {
      const p = S.procs[i];
      if (p.parent < 0) continue;
      const kc = S.row3Of.get(p.node), kp = S.row3Of.get(S.procs[p.parent].node);
      if (kc === undefined || kp === undefined || kc === kp) continue;
      const pair = kp * 4096 + kc, seen = perPair.get(pair) || 0;
      if (seen >= 3) continue;
      perPair.set(pair, seen + 1);
      const x = xOf(p.start), ya = sampleRow(kp, p.start), yb = sampleRow(kc, p.start), za = zOf(kp), zb = zOf(kc);
      const ym = Math.max(ya, yb) + 0.3 + 0.1 * Math.abs(kc - kp), zm = (za + zb) / 2;
      const fade = 1 - (t - p.start) / w, c = colOf(p.prog), f = 0.9 * fade * fade;
      let py = ya, pz = za;
      for (let j = 1; j <= ARC_SEG; j++) {
        const u = j / ARC_SEG, v = 1 - u, qy = v * v * ya + 2 * v * u * ym + u * u * yb, qz = v * v * za + 2 * v * u * zm + u * u * zb;
        const o = (n * ARC_SEG + j - 1) * 6;
        pos[o] = x; pos[o + 1] = py; pos[o + 2] = pz; pos[o + 3] = x; pos[o + 4] = qy; pos[o + 5] = qz;
        col[o] = col[o + 3] = c.r * f; col[o + 1] = col[o + 4] = c.g * f; col[o + 2] = col[o + 5] = c.b * f;
        py = qy; pz = qz;
      }
      n++;
    }
    arcGeo.setDrawRange(0, n * ARC_SEG * 2);
    pa.needsUpdate = true; ca.needsUpdate = true;
  }

  function setCursor() {
    const R = gl.length;
    slice.position.x = xOf(S.t);
    const attr = ribbonGeo.getAttribute('position'), pos = attr.array;
    for (let k = 0; k <= R; k++) {
      const y = k < R ? sampleRow(k, S.t) : heightAt(wallSeries, S.t), z = k < R ? zOf(k) : zWall;
      beads[k].position.set(0, y, z);
      pos.set([0, y + 0.03, z, 0, y - 0.03, z], k * 6);
    }
    attr.needsUpdate = true;
    ribbonGeo.computeVertexNormals();
    updateArcs();
    touch();
  }

  function setHover(k) {
    hoverK = k;
    const traced = look === 'traced', rec = k >= 0 ? gl[k] : null;
    gl.forEach((r, i) => { r.tone(!traced && i === k, !traced && k >= 0 && i !== k); if (rowLabels[i]) rowLabels[i].el.classList.toggle('hot', i === k); });
    hlFill.visible = hlEdge.visible = false;
    if (traced && rec && rec.solids.length) {
      const col = colOf(rec.node.name);
      hlFill.geometry = rec.solids[0].geometry; hlFill.material.color.copy(col); hlFill.position.z = zOf(k); hlFill.visible = true;
      if (!rec.laneH) { hlEdge.geometry = rec.meshes[1].geometry; hlEdge.material.color.copy(col).lerp(WHITE, 0.45); hlEdge.position.z = zOf(k); hlEdge.visible = true; }
    }
    touch();
  }

  function setTags(list) {
    tags = list;
    tagEls.forEach((el, i) => { const t = list[i]; el.hidden = !t; if (t && el.textContent !== t.text) el.textContent = t.text; });
    touch();
  }

  // ---- render scheduling. With ray tracing on, the ridges and floor are path traced on the GPU and keep accumulating
  // samples, and the slice is rasterised on top each frame, so playing or scrubbing never restarts the picture. Moving
  // the camera, hovering a row or changing the rows does restart it. The raster renderer covers loading, shader
  // compilation and GPUs that cannot hold a sample per frame while the camera moves.
  let needsRender = true, lastCam = 0, look = 'raster';
  const rt = { on: false, pt: null, loading: false, max: 400, composer: null, mix: null, overlay: null, geoDirty: true, matDirty: false, camDirty: false,
    drawn: -1, spf: 2, prev: 0, slow: 0, fast: 0, liteCam: false, scale: 1, motion: false };
  // Temporal accumulation, the way games keep ray tracing affordable. While something is changing, only one sample
  // per pixel is traced each frame and blended into the previous frame's picture, which is first re-projected
  // through the new camera using the world position each pixel sees. `hist` holds the running picture (alpha counts
  // how many frames went into a pixel); `pos` holds the world positions for this frame and the last.
  const tmp = { on: false, hist: [], pos: [], hi: 0, pi: 0, prevVP: new THREE.Matrix4(), quad: null, mat: null, posMat: null, reset: true, camMoved: true, fast: 0 };
  function setLook(next) {
    if (look === next) return;
    look = next;
    if (next === 'traced') { scene.remove(frost); scene.add(floor); overlayScene.add(slice, arcs); }
    else { scene.remove(floor); scene.add(frost); scene.add(slice, arcs); }
    applyLook();
    setHover(hoverK);
  }
  function touch() { needsRender = true; }
  function camChanged() { rt.camDirty = true; lastCam = performance.now(); needsRender = true; }
  function sceneChanged() { rt.geoDirty = true; needsRender = true; }
  controls.addEventListener('change', camChanged);
  const setBadge = (text) => { badge.hidden = !text; badge.textContent = text || ''; };

  async function setRT(on) {
    rt.on = on; needsRender = true;
    if (!on) { setBadge(''); return; }
    if (rt.pt || rt.loading) return;
    rt.loading = true; setBadge('ray tracing · loading');
    try {
      const [m, sp, ps] = await Promise.all([import('three-gpu-pathtracer'), import('three/addons/postprocessing/ShaderPass.js'), import('three/addons/postprocessing/Pass.js')]);
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
      const histOpts = { type: THREE.HalfFloatType, depthBuffer: false };
      const posOpts = { type: THREE.FloatType, minFilter: THREE.NearestFilter, magFilter: THREE.NearestFilter };
      tmp.hist = [new THREE.WebGLRenderTarget(4, 4, histOpts), new THREE.WebGLRenderTarget(4, 4, histOpts)];
      tmp.pos = [new THREE.WebGLRenderTarget(4, 4, posOpts), new THREE.WebGLRenderTarget(4, 4, posOpts)];
      tmp.posMat = new THREE.ShaderMaterial({
        side: THREE.DoubleSide,
        vertexShader: 'varying vec3 vW; void main() { vec4 w = modelMatrix * vec4(position, 1.0); vW = w.xyz; gl_Position = projectionMatrix * viewMatrix * w; }',
        fragmentShader: 'varying vec3 vW; void main() { gl_FragColor = vec4(vW, 1.0); }',
      });
      tmp.mat = new THREE.ShaderMaterial({
        depthTest: false, depthWrite: false,
        uniforms: { tNew: { value: null }, tHist: { value: null }, tPos: { value: null }, tPosPrev: { value: null }, prevVP: { value: tmp.prevVP }, mode: { value: 1 }, cap: { value: 30 }, soft: { value: 0 }, px: { value: new THREE.Vector2() } },
        vertexShader: 'varying vec2 vUv; void main() { vUv = uv; gl_Position = vec4(position.xy, 0.0, 1.0); }',
        fragmentShader: [
          'uniform sampler2D tNew, tHist, tPos, tPosPrev; uniform mat4 prevVP; uniform float mode, cap, soft; uniform vec2 px; varying vec2 vUv;',
          '// a single sample can be wildly bright (a firefly); clamp it so one of them cannot outweigh the history',
          'vec3 fresh(vec2 uv) { vec3 c = texture2D(tNew, uv).rgb; float l = max(c.r, max(c.g, c.b)); return l > 3.0 ? c * (3.0 / l) : c; }',
          'void main() {',
          '  if (mode > 1.5) { gl_FragColor = vec4(texture2D(tNew, vUv).rgb, cap); return; }      // seed the history with a finished picture',
          '  vec3 cur = fresh(vUv);',
          '  vec4 P = texture2D(tPos, vUv);',
          '  vec4 c = prevVP * vec4(P.xyz, 1.0);',
          '  if (soft > 0.5 && P.a > 0.5) {',
          '    // while moving, average the new sample with its neighbours that lie on the same surface',
          '    float sigma = 0.05 + 0.01 * abs(c.w), wsum = 1.0;',
          '    for (int j = -1; j <= 1; j++) for (int i = -1; i <= 1; i++) {',
          '      if (i == 0 && j == 0) continue;',
          '      vec2 o = vUv + vec2(float(i), float(j)) * px * 1.5;',
          '      vec4 Pn = texture2D(tPos, o); vec3 d = Pn.xyz - P.xyz;',
          '      float w = Pn.a > 0.5 ? exp(-dot(d, d) / (sigma * sigma)) : 0.0;',
          '      cur += fresh(o) * w; wsum += w;',
          '    }',
          '    cur /= wsum;',
          '  }',
          '  vec2 uv = vUv; bool ok = mode < 0.5;',
          '  if (ok && P.a > 0.5) {',
          '    uv = c.xy / c.w * 0.5 + 0.5;',
          '    ok = c.w > 0.0 && uv.x >= 0.0 && uv.x <= 1.0 && uv.y >= 0.0 && uv.y <= 1.0;',
          '    if (ok) {',
          '      vec4 Q = texture2D(tPosPrev, uv);',
          '      float dq = (prevVP * vec4(Q.xyz, 1.0)).w;',
          '      ok = Q.a > 0.5 && abs(dq - c.w) < 0.02 + 0.012 * c.w;      // same surface as last frame, or newly revealed?',
          '    }',
          '  } else if (ok) { ok = texture2D(tPosPrev, uv).a < 0.5; }',
          '  float n = 0.0; vec3 col = cur;',
          '  if (ok) { vec4 h = texture2D(tHist, uv); n = min(h.a, cap); col = mix(h.rgb, cur, 1.0 / (n + 1.0)); }',
          '  gl_FragColor = vec4(col, n + 1.0);',
          '}',
        ].join('\n'),
      });
      tmp.quad = new ps.FullScreenQuad(tmp.mat);
      rt.pt = pt; rt.geoDirty = true;
      resize();
    } catch (err) {
      console.error(err); rt.on = false; $('#rt').checked = false; setBadge('ray tracing unavailable in this browser');
    }
    rt.loading = false;
  }

  function rasterRender() { setLook('raster'); composer.render(); needsRender = false; placeLabels(); }

  function tracedRender(texture) {
    const alpha = renderer.getClearAlpha();
    renderer.setRenderTarget(rt.overlay); renderer.setClearAlpha(0); renderer.clear();
    renderer.render(overlayScene, camera);
    renderer.setRenderTarget(null); renderer.setClearAlpha(alpha);
    rt.mix.uniforms.tTraced.value = texture;
    rt.mix.uniforms.tSlice.value = rt.overlay.texture;
    rt.composer.render();
    rt.drawn = rt.pt.samples; needsRender = false; placeLabels();
  }

  // Copy the finished picture into the history, so the first frame of a change starts from it instead of from noise.
  function seedHistory() {
    const u = tmp.mat.uniforms;
    u.mode.value = 2; u.cap.value = 30; u.tNew.value = rt.pt.target.texture;
    renderer.setRenderTarget(tmp.hist[tmp.hi]); tmp.quad.render(renderer); renderer.setRenderTarget(null);
  }

  // One frame of temporal accumulation; returns the texture to show.
  function temporalStep(now) {
    const u = tmp.mat.uniforms, alpha = renderer.getClearAlpha();
    let cur = tmp.pos[tmp.pi];
    if (tmp.camMoved || tmp.reset) {
      // world position seen by each pixel, drawn with the same geometry the path tracer sees
      cur = tmp.pos[1 - tmp.pi];
      const bg = scene.background;
      scene.background = null; scene.overrideMaterial = tmp.posMat;
      renderer.setRenderTarget(cur); renderer.setClearAlpha(0); renderer.clear();
      renderer.render(scene, camera);
      scene.overrideMaterial = null; scene.background = bg; renderer.setClearAlpha(alpha);
    }
    u.mode.value = tmp.reset ? 1 : 0;
    u.cap.value = now - tmp.fast < 300 ? 5 : 30;       // adapt quickly right after a highlight changes
    u.soft.value = rt.motion ? 1 : 0;
    u.px.value.set(1 / rt.pt.target.width, 1 / rt.pt.target.height);
    u.tNew.value = rt.pt.target.texture;
    u.tHist.value = tmp.hist[tmp.hi].texture;
    u.tPos.value = cur.texture; u.tPosPrev.value = tmp.pos[tmp.pi].texture;
    renderer.setRenderTarget(tmp.hist[1 - tmp.hi]); tmp.quad.render(renderer); renderer.setRenderTarget(null);
    tmp.hi = 1 - tmp.hi;
    if (cur !== tmp.pos[tmp.pi]) tmp.pi = 1 - tmp.pi;
    tmp.prevVP.multiplyMatrices(camera.projectionMatrix, camera.matrixWorldInverse);
    tmp.reset = false; tmp.camMoved = false;
    return tmp.hist[tmp.hi].texture;
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
            rt.pt.renderScale = rt.scale * (camBusy ? 0.5 : 1);
            rt.pt.bounces = camBusy ? 2 : 5;
            rt.pt.transmissiveBounces = camBusy ? 4 : 10;
            rt.camDirty = true;
          }
          if (rt.geoDirty || rt.matDirty || rt.camDirty) {
            // going from a finished picture into a change: keep that picture as the starting history
            if (!tmp.on && !rt.geoDirty && !tmp.reset && rt.pt.samples >= 8) seedHistory();
            if (rt.geoDirty) { rt.pt.setScene(scene, camera); tmp.reset = true; }
            else {
              if (rt.matDirty) { rt.pt.updateMaterials(); tmp.fast = now; }
              if (rt.camDirty) { rt.pt.updateCamera(); tmp.camMoved = true; }
            }
            rt.geoDirty = rt.matDirty = rt.camDirty = false; rt.drawn = -1; tmp.on = true;
          }
          const compiling = rt.pt.isCompiling;
          if (rt.pt.samples < rt.max) {
            if (!compiling && gap < 200) {
              // steer samples per frame by frame time
              if (gap < 19) { rt.slow = 0; if (++rt.fast > 10) { rt.fast = 0; rt.spf = Math.min(4, rt.spf + 1); } }
              else if (gap > 30) {
                rt.fast = 0;
                if (++rt.slow > 3) {
                  rt.slow = 0;
                  if (rt.spf > 1) rt.spf--;
                  else if (camBusy && gap > 60) rt.liteCam = true;
                }
              }
            }
            // one sample per frame while the camera moves; a few more once it rests, to finish quickly
            const n = compiling || camBusy ? 1 : rt.spf;
            for (let k = 0; k < n && rt.pt.samples < rt.max; k++) rt.pt.renderSample();
          }
          if (rt.pt.samples >= 1) {
            if (rt.pt.samples !== rt.drawn || needsRender) {
              let texture = rt.pt.target.texture;
              if (tmp.on) { texture = temporalStep(now); if (!camBusy && rt.pt.samples >= 48) tmp.on = false; }
              tracedRender(texture);
            }
          } else if (needsRender) rasterRender();
          setBadge(compiling ? 'ray tracing · compiling shaders' : 'ray tracing · ' + Math.floor(rt.pt.samples) + ' / ' + rt.max + ' samples');
          return;
        } catch (err) {
          console.error(err); rt.on = false; $('#rt').checked = false; needsRender = true; setBadge('ray tracing failed, using the standard renderer');
        }
      }
    }
    if (needsRender) rasterRender();
  }

  const v3 = new THREE.Vector3(), v4 = new THREE.Vector3();
  function project(p) { v3.copy(p).project(camera); return v3.z > 1 || v3.z < -1 ? null : [(v3.x * 0.5 + 0.5) * stage.clientWidth, (-v3.y * 0.5 + 0.5) * stage.clientHeight]; }
  function placeLabels() {
    const w = stage.clientWidth, h = stage.clientHeight;
    for (const t of tickLabels) {
      const q = project(t.p), ok = q && q[0] > 12 && q[0] < w - 12 && q[1] > 28 && q[1] < h - 6;
      t.el.hidden = !ok; if (ok) t.el.style.transform = 'translate(' + q[0].toFixed(1) + 'px,' + q[1].toFixed(1) + 'px) translate(-50%,-50%)';
    }
    // Row names: the hovered row always shows; the rest show front to back wherever they do not collide.
    const pts = rowLabels.map((r) => project(r.p)), taken = [], hot = S.hover >= 0 ? S.r3[S.hover] : -1;
    const fits = (q) => q && q[0] > 30 && q[0] < w && q[1] > 28 && q[1] < h - 4;
    if (hot >= 0 && fits(pts[hot])) taken.push(pts[hot][1]);
    rowLabels.forEach((r, i) => {
      const q = pts[i];
      let ok = fits(q);
      if (ok && i !== hot) { ok = taken.every((y) => Math.abs(y - q[1]) >= 13); if (ok) taken.push(q[1]); }
      r.el.hidden = !ok; if (ok) r.el.style.transform = 'translate(' + q[0].toFixed(1) + 'px,' + q[1].toFixed(1) + 'px) translate(-100%,-50%)';
    });
    const ANCHOR = { right: '-100%,-50%', left: '0,-50%', center: '-50%,-100%' }, placed = [];
    const clear = (q) => placed.every((o) => Math.abs(o[1] - q[1]) >= 17 || Math.abs(o[0] - q[0]) >= 150);
    for (const f of fixedLabels) {
      const q = project(f.p);
      let ok = q && q[0] > 4 && q[0] < w - 4 && q[1] > 24 && q[1] < h - 4;
      if (ok && f.align === 'right') ok = taken.every((y) => Math.abs(y - q[1]) >= 13);
      if (ok && f.align === 'center') { ok = clear(q); if (ok) placed.push(q); }
      f.el.hidden = !ok; if (ok) f.el.style.transform = 'translate(' + q[0].toFixed(1) + 'px,' + q[1].toFixed(1) + 'px) translate(' + ANCHOR[f.align] + ')';
    }
    // name tags ride above the beads where the slice meets each row
    tags.forEach((t, i) => {
      const el = tagEls[i];
      if (!el || t.k >= gl.length) return;
      v4.set(xOf(S.t), sampleRow(t.k, S.t) + 0.28, zOf(t.k));
      const q = project(v4), ok = q && q[0] > 40 && q[0] < w - 40 && q[1] > 30 && q[1] < h - 8 && clear(q);
      if (ok) placed.push(q);
      el.hidden = !ok; if (ok) el.style.transform = 'translate(' + q[0].toFixed(1) + 'px,' + q[1].toFixed(1) + 'px) translate(-50%,-100%)';
    });
  }

  function resize() {
    const w = Math.max(2, stage.clientWidth), h = Math.max(2, stage.clientHeight);
    renderer.setSize(w, h, false);
    composer.setSize(w, h);
    if (rt.composer) {
      const pr = renderer.getPixelRatio(), bw = Math.round(w * pr), bh = Math.round(h * pr);
      rt.composer.setSize(w, h); rt.overlay.setSize(bw, bh);
      for (const t of [...tmp.hist, ...tmp.pos]) t.setSize(bw, bh);
      tmp.reset = true;
    }
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
    const hit = ray.intersectObjects(pickables, false)[0];
    if (hit) {
      const procs = hit.object.userData.procs;
      return { i: hit.object.userData.k, proc: procs ? procs[Math.floor(hit.faceIndex / 12)] : null, t: S.v0 + clamp((hit.point.x - X0) / W, 0, 1) * (S.v1 - S.v0) };
    }
    return ray.ray.intersectPlane(ground, hitV) && Math.abs(hitV.z) < D / 2 + 1.5 && hitV.x > X0 - 0.5 && hitV.x < X0 + W + 0.5 ? { i: -1, t: S.v0 + clamp((hitV.x - X0) / W, 0, 1) * (S.v1 - S.v0) } : null;
  }
  let down = null;
  canvas.addEventListener('pointerdown', (e) => { down = [e.clientX, e.clientY]; hideTip(); });
  canvas.addEventListener('pointermove', (e) => {
    if (e.buttons) return;
    const h = pick(e);
    if (h && h.i >= 0) { api.onHover(S.rows.indexOf(S.rows3[h.i])); showTip(h.proc ? procTip(h.proc) : nodeTip(S.rows3[h.i], h.t), e.clientX, e.clientY); } else { api.onHover(-1); hideTip(); }
  });
  canvas.addEventListener('pointerup', (e) => { if (down && Math.hypot(e.clientX - down[0], e.clientY - down[1]) < 5) { const h = pick(e); if (h) api.onPick(h.t); } down = null; });
  canvas.addEventListener('pointerleave', () => { api.onHover(-1); hideTip(); });
  canvas.addEventListener('dblclick', (e) => { const h = pick(e); if (h && h.i >= 0) api.onUnfold(S.rows3[h.i]); });

  const api = { software, setRows, setCursor, setHover, setTags, setRT, setGlass, resetView, touch, frame, onHover: () => {}, onPick: () => {}, onUnfold: () => {}, debug: { rt, tmp, scene, camera, renderer, THREE } };
  resize();
  setRows();
  return api;
}

// ---------------------------------------------------------------- boot
let last = performance.now(), lastUI = 0, lastSound = 0;
function frame(now) {
  const dt = Math.min(0.1, (now - last) / 1000); last = now;
  if (S.playing) {
    setT(S.t + dt * ((S.v1 - S.v0) / PLAY_SECONDS) * S.speed);
    if (S.t >= S.v1) { S.playing = false; syncPlay(); }
  }
  if (rec.active) {
    // stop a little after the slice reaches the end, so the reverb can ring out; keep the 3D view redrawing meanwhile
    if (!S.playing && S.t >= S.v1 - 1e-6) { if (!rec.ending) rec.ending = now; else if (now - rec.ending > 2000) stopRecording(); }
    if (view3d) view3d.touch();
  }
  if (dirty.tl) { drawTimeline(); dirty.tl = false; }
  if (dirty.ui && now - lastUI > 90) { updateUI(); dirty.ui = false; lastUI = now; }
  if (audio.on && now - lastSound > 80) { updateSound(now); lastSound = now; }
  if (view3d) view3d.frame(now);
  if (rec.active) composeFrame();
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
    v.onUnfold = (n) => { if (S.unfolded.has(n.id)) S.unfolded.delete(n.id); else S.unfolded.add(n.id); S.hover = -1; rowsChanged(); };
    view3d = v;
    window.__wt = { S, view3d: v, audio, rec };
    // ray tracing is opt-in; the choice is remembered once the viewer has made one
    let wantRT = false;
    try { wantRT = !v.software && localStorage.getItem('stracewave.raytracing') === '1'; } catch (err) { /* storage is optional */ }
    $('#rt').checked = wantRT;
    if (wantRT) v.setRT(true);
    let wantGlass = true;
    try { wantGlass = localStorage.getItem('stracewave.glass') !== '0'; } catch (err) { /* storage is optional */ }
    $('#glass').checked = wantGlass;
    v.setGlass(wantGlass);
  });
}
openExample('uv');
if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => { dirty.tl = true; });
