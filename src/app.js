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
const BINS_3D = 256, ROW_H = 22, AXIS_H = 24, PITCH = 8, CELL = 6, PLAY_SECONDS = 24;

const S = {
  key: null, procs: [], span: 1, root: null, rows: [], expanded: new Set(),
  t: 0, playing: false, speed: 1, hover: -1, colorOf: new Map(), vmax: 1,
  starts: null, ends: null, failEnds: null,
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
function seriesOf(n, bins) {
  let s = n.cache.get(bins);
  if (s) return s;
  s = new Float32Array(bins);
  const diff = new Float32Array(bins + 1), bw = S.span / bins, top = bins - 1e-6;
  for (const p of n.procs) {
    const a = Math.min(p.start / bw, top), b = Math.min(p.end / bw, top);
    const b0 = Math.floor(a), b1 = Math.floor(b);
    if (b0 === b1) { s[b0] += b - a; continue; }
    s[b0] += b0 + 1 - a; s[b1] += b - b1;
    if (b1 > b0 + 1) { diff[b0 + 1] += 1; diff[b1] -= 1; }
  }
  let acc = 0;
  for (let i = 0; i < bins; i++) { acc += diff[i]; s[i] += acc; }
  n.cache.set(bins, s);
  return s;
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
  S.root = buildTree(S.procs);
  S.starts = Float64Array.from(S.procs, (p) => p.start).sort();
  S.ends = Float64Array.from(S.procs, (p) => p.end).sort();
  S.failEnds = Float64Array.from(S.procs.filter((p) => p.exit !== 0), (p) => p.end).sort();
  S.vmax = 1;
  (function scan(n) { if (n.procs.length) { const s = seriesOf(n, BINS_3D); for (let i = 0; i < s.length; i++) if (s[i] > S.vmax) S.vmax = s[i]; } n.children.forEach(scan); })(S.root);
  defaultExpand();
  S.hover = -1;
  S.playing = false;
  $('#meta').innerHTML = (d.file ? esc(d.file) + ' · ' : '') + '$ ' + esc(cmdLine(d.command)) + ' · <b>' + S.procs.length.toLocaleString() + '</b> processes · <b>' + fmtT(S.span) + '</b>';
  $('#clockEnd').textContent = fmtT(S.span);
  for (const b of $('#datasets').children) b.setAttribute('aria-pressed', String(b.dataset.key === key));
  rowsChanged();
  const all = seriesOf({ procs: S.procs, cache: new Map() }, BINS_3D);
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
  tlLabels.innerHTML = '<div class="axis-pad">Timeline</div>' + S.rows.map((n, i) => {
    const has = n.children.length > 0, open = S.expanded.has(n.id), k = n.procs.length;
    return '<button type="button" class="row" data-i="' + i + '" style="--d:' + n.vdepth + '"' + (has ? ' aria-expanded="' + open + '"' : '') + '>' +
      '<span class="st" data-st=""></span><span class="caret">' + (has ? (open ? '▾' : '▸') : '') + '</span>' +
      '<i class="chip" style="background:' + colorFor(n.name) + '"></i><span class="nm">' + esc(n.name) + '</span>' +
      '<span class="ct">(' + k.toLocaleString() + (k === 1 ? ' unit' : ' units') + ')</span><span class="fl"></span></button>';
  }).join('');
  rowEls = [...tlLabels.querySelectorAll('.row')];
  sizeTimeline();
  if (view3d) view3d.setRows();
  dirty.tl = dirty.ui = true;
}

function sizeTimeline() {
  const dpr = window.devicePixelRatio || 1;
  const h = AXIS_H + S.rows.length * ROW_H;
  tlCanvas.style.height = h + 'px';
  const w = Math.max(40, tlCanvas.clientWidth);
  tlCols = Math.max(8, Math.floor(w / PITCH));
  tlW = tlCols * PITCH;
  tlCanvas.width = Math.round(w * dpr);
  tlCanvas.height = Math.round(h * dpr);
  dirty.tl = true;
}

function niceStep(raw) { const p = Math.pow(10, Math.floor(Math.log10(raw))); const f = raw / p; return (f <= 1 ? 1 : f <= 2 ? 2 : f <= 5 ? 5 : 10) * p; }

function drawTimeline() {
  const dpr = window.devicePixelRatio || 1, ctx = tlCtx;
  const w = tlCanvas.width / dpr, h = tlCanvas.height / dpr;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, w, h);
  // axis
  ctx.font = '11px "JetBrains Mono", ui-monospace, monospace';
  ctx.textBaseline = 'middle';
  ctx.fillStyle = INK.axis;
  const step = niceStep(S.span / Math.max(2, tlW / 84));
  for (let v = 0; v <= S.span + 1e-6; v += step) {
    const x = (v / S.span) * tlW;
    ctx.globalAlpha = 0.5; ctx.fillRect(Math.round(x), AXIS_H - 5, 1, 4); ctx.globalAlpha = 1;
    if (x + 30 < w) ctx.fillText(Math.round(v) + 's', x + 4, AXIS_H / 2 - 1);
  }
  if (S.hover >= 0 && S.hover < S.rows.length) { ctx.fillStyle = 'rgba(255,255,255,0.06)'; ctx.fillRect(0, AXIS_H + S.hover * ROW_H, w, ROW_H); }
  const cur = Math.min(tlCols - 1, Math.floor((S.t / S.span) * tlCols));
  const maxH = ROW_H - 8;
  for (let r = 0; r < S.rows.length; r++) {
    const s = seriesOf(S.rows[r], tlCols), base = AXIS_H + r * ROW_H + ROW_H - 4;
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
  const cx = Math.round((S.t / S.span) * tlW) + 0.5;
  ctx.strokeStyle = INK.cursor; ctx.globalAlpha = 0.85; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(cx, AXIS_H - 6); ctx.lineTo(cx, h); ctx.stroke();
  ctx.fillStyle = INK.cursor; ctx.beginPath(); ctx.moveTo(cx - 4, AXIS_H - 10); ctx.lineTo(cx + 4, AXIS_H - 10); ctx.lineTo(cx, AXIS_H - 4); ctx.closePath(); ctx.fill();
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
  if (document.activeElement !== scrub || S.playing) scrub.value = String(Math.round((t / S.span) * 1000));
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
  S.t = clamp(t, 0, S.span);
  dirty.tl = dirty.ui = true;
  if (view3d) view3d.setCursor();
}
function syncPlay() { const b = $('#play'); b.textContent = S.playing ? '❚❚' : '▶'; b.setAttribute('aria-label', S.playing ? 'Pause' : 'Play'); if (view3d) view3d.touch(); }
function togglePlay() { if (!S.playing && S.t >= S.span - 1e-6) setT(0); S.playing = !S.playing; syncPlay(); }
let toastTimer = 0;
function toast(text, ms = 1600) { const el = $('#toast'); el.textContent = text; el.hidden = false; clearTimeout(toastTimer); toastTimer = setTimeout(() => { el.hidden = true; }, ms); }

tlLabels.addEventListener('click', (e) => {
  const b = e.target.closest('.row'); if (!b) return;
  const n = S.rows[+b.dataset.i]; if (!n || !n.children.length) return;
  if (S.expanded.has(n.id)) S.expanded.delete(n.id); else S.expanded.add(n.id);
  S.hover = -1;
  rowsChanged();
  const again = rowEls[S.rows.indexOf(n)]; if (again) again.focus({ preventScroll: true });
});
tlLabels.addEventListener('pointerover', (e) => { const b = e.target.closest('.row'); setHover(b ? +b.dataset.i : -1); });
tlLabels.addEventListener('pointerleave', () => setHover(-1));

let scrubbing = false;
const tlTime = (e) => { const r = tlCanvas.getBoundingClientRect(); return clamp((e.clientX - r.left) / tlW, 0, 1) * S.span; };
tlCanvas.addEventListener('pointerdown', (e) => { scrubbing = true; tlCanvas.setPointerCapture(e.pointerId); setT(tlTime(e)); });
tlCanvas.addEventListener('pointermove', (e) => {
  const r = tlCanvas.getBoundingClientRect(), i = Math.floor((e.clientY - r.top - AXIS_H) / ROW_H), t = tlTime(e);
  if (scrubbing) setT(t);
  if (i >= 0 && i < S.rows.length) { setHover(i); showTip(nodeTip(S.rows[i], t), e.clientX, e.clientY); } else { setHover(-1); hideTip(); }
});
const endScrub = () => { scrubbing = false; };
tlCanvas.addEventListener('pointerup', endScrub);
tlCanvas.addEventListener('pointercancel', endScrub);
tlCanvas.addEventListener('pointerleave', () => { if (!scrubbing) { setHover(-1); hideTip(); } });

$('#play').addEventListener('click', togglePlay);
$('#speeds').addEventListener('click', (e) => { const b = e.target.closest('button'); if (!b) return; S.speed = +b.dataset.speed; for (const x of $('#speeds').children) x.setAttribute('aria-pressed', String(x === b)); });
$('#scrub').addEventListener('input', (e) => setT((+e.target.value / 1000) * S.span));
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
  let THREE, OrbitControls, EffectComposer, RenderPass, UnrealBloomPass, OutputPass;
  try {
    const m = await Promise.all([
      import('three'), import('three/addons/controls/OrbitControls.js'), import('three/addons/postprocessing/EffectComposer.js'),
      import('three/addons/postprocessing/RenderPass.js'), import('three/addons/postprocessing/UnrealBloomPass.js'), import('three/addons/postprocessing/OutputPass.js'),
    ]);
    THREE = m[0]; OrbitControls = m[1].OrbitControls; EffectComposer = m[2].EffectComposer; RenderPass = m[3].RenderPass; UnrealBloomPass = m[4].UnrealBloomPass; OutputPass = m[5].OutputPass;
  } catch (err) { console.error(err); return fail('The 3D view could not load three.js. The timeline below still works.'); }
  let renderer;
  try { renderer = new THREE.WebGLRenderer({ canvas, antialias: false, powerPreference: 'high-performance' }); }
  catch (err) { console.error(err); return fail('WebGL is not available here. The timeline below still works.'); }
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  renderer.toneMapping = THREE.ACESFilmicToneMapping;
  renderer.toneMappingExposure = 1.05;

  const W = 24, X0 = -12, H = 4.6, Y0 = 0.012;
  const xOf = (t) => X0 + (t / S.span) * W;
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
  controls.enableDamping = true; controls.dampingFactor = 0.09;
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
    controls.update(); userMoved = false; touch();
  }

  const mkTarget = () => new THREE.WebGLRenderTarget(4, 4, { type: THREE.HalfFloatType, samples: 4 });
  const composer = new EffectComposer(renderer, mkTarget());
  composer.addPass(new RenderPass(scene, camera));
  composer.addPass(new UnrealBloomPass(new THREE.Vector2(4, 4), 0.5, 0.55, 0.8));
  composer.addPass(new OutputPass());

  // floor, slice sheet and blade
  const floor = new THREE.Mesh(new THREE.PlaneGeometry(1, 1), new THREE.MeshStandardMaterial({ color: 0x080b11, roughness: 0.2, metalness: 0.5, transparent: true, opacity: 0.925 }));
  floor.rotation.x = -Math.PI / 2;
  scene.add(floor);
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
  // Raster stand-in for floor reflections: the ridges again, flipped under a slightly see-through floor. Path tracing swaps it for the real thing.
  const mirror = new THREE.Group(); mirror.scale.y = -1; scene.add(mirror);
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
        const u = x / (w - 1);
        const box = 1.8 * Math.exp(-(((u - 0.36) / 0.08) ** 2) - (((v - 0.86) / 0.07) ** 2)) + 0.5 * Math.exp(-(((u - 0.82) / 0.1) ** 2) - (((v - 0.78) / 0.08) ** 2));
        const hz = 0.02 * Math.exp(-(((v - 0.5) / 0.08) ** 2));
        const i = (y * w + x) * 4;
        data[i] = toHalf(0.012 + 0.05 * up + hz + box * 0.9);
        data[i + 1] = toHalf(0.016 + 0.075 * up + hz * 1.3 + box * 0.96);
        data[i + 2] = toHalf(0.026 + 0.13 * up + hz * 1.9 + box);
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
    const s = series[i], f = clamp((t / S.span) * BINS_3D - 0.5, 0, BINS_3D - 1), a = Math.floor(f), b = Math.min(BINS_3D - 1, a + 1);
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
    for (const m of [body, crest, rest]) {
      m.position.z = zOf(i); ridges.add(m);
      const twin = new THREE.Mesh(m.geometry, m.material); twin.position.z = zOf(i); mirror.add(twin);
    }
    slice.add(bead);
    bodies.push(body); crests.push(crest); rests.push(rest); beads.push(bead); series.push(s);
  }

  function setRows() {
    for (const m of [...bodies, ...crests, ...rests]) { m.geometry.dispose(); m.material.dispose(); }
    ridges.clear(); mirror.clear();
    for (const b of beads) { slice.remove(b); b.material.dispose(); }
    for (const t of ticks.children) t.geometry.dispose();
    ticks.clear(); bodies = []; crests = []; rests = []; beads = []; series = [];
    const R = S.rows.length;
    dz = clamp(11 / Math.max(1, R), 0.26, 0.8); D = dz * Math.max(0, R - 1);
    S.rows.forEach(buildRidge);
    floor.scale.set(W + 400, D + 400, 1);
    sheet.scale.set(D + 1.6, H + 0.9, 1); sheet.position.y = (H + 0.9) / 2;
    blade.scale.set(0.035, 0.02, D + 1.6); blade.position.y = 0.012;
    const SH = H + 0.9, SZ = D / 2 + 0.8;
    frameTop.scale.set(0.02, 0.02, D + 1.6); frameTop.position.set(0, SH, 0);
    frameA.scale.set(0.02, SH, 0.02); frameA.position.set(0, SH / 2, SZ);
    frameB.scale.set(0.02, SH, 0.02); frameB.position.set(0, SH / 2, -SZ);
    const step = niceStep(S.span / 8);
    labelsEl.textContent = ''; tickLabels = []; rowLabels = [];
    for (let v = 0; v <= S.span + 1e-6; v += step) {
      const m = new THREE.Mesh(new THREE.BoxGeometry(0.014, 0.004, D + 1.6), tickMat);
      m.position.set(xOf(v), 0.003, 0); ticks.add(m);
      const el = document.createElement('span'); el.className = 'tick'; el.textContent = Math.round(v) + 's';
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
    const pos = new Float32Array(Math.max(2, R) * 6), idx = [];
    for (let i = 0; i < R; i++) {
      const y = sampleRow(i, S.t), z = zOf(i);
      beads[i].position.set(0, y, z);
      pos.set([0, y + 0.03, z, 0, y - 0.03, z], i * 6);
      if (i < R - 1) { const a = i * 2; idx.push(a, a + 1, a + 2, a + 1, a + 3, a + 2); }
    }
    ribbonGeo.setAttribute('position', new THREE.BufferAttribute(pos, 3));
    ribbonGeo.setIndex(idx);
    ribbonGeo.computeVertexNormals();
    sceneChanged();
  }

  function setHover(i) {
    for (let k = 0; k < bodies.length; k++) {
      const hot = k === i, dim = i >= 0 && !hot;
      bodies[k].material.emissiveIntensity = hot ? FILL * 1.9 : dim ? FILL * 0.55 : FILL;
      crests[k].material.emissiveIntensity = hot ? 2.6 : dim ? 0.7 : 1.35;
      rests[k].material.emissiveIntensity = hot ? 0.9 : 0.16;
      if (rowLabels[k]) rowLabels[k].el.classList.toggle('hot', hot);
    }
    sceneChanged();
  }

  // ---- render scheduling: raster while anything moves, path tracing once it has been still for a moment
  let needsRender = true, lastChange = performance.now();
  const rt = { on: false, pt: null, loading: false, active: false, sceneDirty: true, shown: false, max: 400, composer: null, pass: null, prev: 0, slow: 0, fast: 0 };
  function rasterLook(on) {
    if (on) { scene.add(mirror); slice.add(sheet); } else { scene.remove(mirror); slice.remove(sheet); }
    const f = floor.material;
    f.transparent = on; f.opacity = on ? 0.925 : 1; f.metalness = on ? 0.5 : 1; f.roughness = on ? 0.2 : 0.13; f.color.set(on ? 0x080b11 : 0x535b6b); f.needsUpdate = true;
  }
  function touch() { needsRender = true; lastChange = performance.now(); if (rt.active) { rt.active = false; rt.shown = false; rasterLook(true); } }
  function sceneChanged() { rt.sceneDirty = true; touch(); }
  controls.addEventListener('change', touch);
  const setBadge = (text) => { badge.hidden = !text; badge.textContent = text || ''; };

  async function setRT(on) {
    rt.on = on;
    if (!on) { touch(); setBadge(''); return; }
    if (!rt.pt && !rt.loading) {
      rt.loading = true; setBadge('ray tracing · loading');
      try {
        const [m, tp] = await Promise.all([import('three-gpu-pathtracer'), import('three/addons/postprocessing/TexturePass.js')]);
        const pt = new m.WebGLPathTracer(renderer);
        pt.renderToCanvas = false; pt.rasterizeScene = false; pt.dynamicLowRes = false;
        pt.renderDelay = 0; pt.minSamples = 0; pt.bounces = 5; pt.filterGlossyFactor = 0.6;
        pt.tiles.set(2, 2);
        pt.renderScale = Math.min(1, 1.25 / renderer.getPixelRatio());
        rt.pass = new tp.TexturePass(pt.target.texture);
        rt.composer = new EffectComposer(renderer, mkTarget());
        rt.composer.addPass(rt.pass);
        rt.composer.addPass(new UnrealBloomPass(new THREE.Vector2(4, 4), 0.38, 0.5, 0.85));
        rt.composer.addPass(new OutputPass());
        rt.pt = pt; rt.sceneDirty = true;
        resize();
      } catch (err) {
        console.error(err); rt.on = false; $('#rt').checked = false; setBadge('ray tracing unavailable in this browser');
      }
      rt.loading = false;
    }
    touch();
  }

  function rasterRender() { composer.render(); needsRender = false; placeLabels(); }

  function frame(now) {
    controls.update();
    if (rt.on && rt.pt && !S.playing && now - lastChange > 450) {
      try {
        if (!rt.active) {
          rasterLook(false);
          if (rt.sceneDirty) { rt.pt.setScene(scene, camera); rt.sceneDirty = false; } else rt.pt.updateCamera();
          rt.active = true; rt.shown = false;
        }
        if (rt.pt.samples < rt.max) {
          const gap = now - rt.prev; rt.prev = now;
          if (!rt.pt.isCompiling && gap < 200) {
            if (gap < 20) { rt.fast++; rt.slow = 0; } else if (gap > 45) { rt.slow++; rt.fast = 0; }
            if (rt.fast > 20 && rt.pt.tiles.x > 1) { rt.pt.tiles.set(1, 1); rt.fast = 0; }
            if (rt.slow > 6 && rt.pt.tiles.x < 3) { rt.pt.tiles.set(rt.pt.tiles.x + 1, rt.pt.tiles.x + 1); rt.slow = 0; }
          }
          rt.pt.renderSample();
          if (rt.pt.samples >= 3) { rt.pass.map = rt.pt.target.texture; rt.composer.render(); rt.shown = true; }
          setBadge(rt.pt.isCompiling ? 'ray tracing · compiling shaders' : 'ray tracing · ' + Math.floor(rt.pt.samples) + ' / ' + rt.max + ' samples');
        } else setBadge('ray tracing · ' + rt.max + ' samples');
      } catch (err) {
        console.error(err); rt.on = false; $('#rt').checked = false; touch(); setBadge('ray tracing failed, back to raster');
      }
      if (!rt.shown && needsRender) rasterRender();
      return;
    }
    if (rt.on && rt.pt && !rt.active) setBadge(S.playing ? 'ray tracing · paused while playing' : 'ray tracing · waiting for stillness');
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
    if (rt.composer) rt.composer.setSize(w, h);
    camera.aspect = w / h; camera.updateProjectionMatrix();
    if (!userMoved) resetView();
    touch();
  }
  new ResizeObserver(resize).observe(stage);

  // picking: hover a ridge for details, click to move the slice
  const ray = new THREE.Raycaster(), ndc = new THREE.Vector2(), ground = new THREE.Plane(new THREE.Vector3(0, 1, 0), 0), hitV = new THREE.Vector3();
  function pick(e) {
    const r = canvas.getBoundingClientRect();
    ndc.set(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1);
    ray.setFromCamera(ndc, camera);
    const hit = ray.intersectObjects(bodies, false)[0];
    if (hit) return { i: hit.object.userData.i, t: clamp((hit.point.x - X0) / W, 0, 1) * S.span };
    return ray.ray.intersectPlane(ground, hitV) && Math.abs(hitV.z) < D / 2 + 1.5 && hitV.x > X0 - 0.5 && hitV.x < X0 + W + 0.5 ? { i: -1, t: clamp((hitV.x - X0) / W, 0, 1) * S.span } : null;
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

  const api = { setRows, setCursor, setHover, setRT, resetView, touch, frame, onHover: () => {}, onPick: () => {}, debug: { rt, scene, camera, renderer } };
  resize();
  setRows();
  return api;
}

// ---------------------------------------------------------------- boot
let last = performance.now(), lastUI = 0;
function frame(now) {
  const dt = Math.min(0.1, (now - last) / 1000); last = now;
  if (S.playing) {
    setT(S.t + dt * (S.span / PLAY_SECONDS) * S.speed);
    if (S.t >= S.span) { S.playing = false; syncPlay(); }
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
  });
}
openExample('uv');
if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => { dirty.tl = true; });
