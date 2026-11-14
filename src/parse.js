// Parse a strace log recorded with
//   strace --trace=execve,execveat,exit,exit_group --follow-forks --string-limit=1000 -ttt --output=... <command>
// into a compact trace:
//   { command, span, programs: [name], procs: [[startMs, endMs, programIndex, parentIndex, exitCode, command]] }
// procs are sorted by start time; parentIndex is -1 for the first process; exitCode is -1 when killed by a signal.

const LINE = /^(\d+)\s+(\d+\.\d+)\s+(.*)$/;
const EXECVE = /^execve\("([^"]*)", \[(.*)\], (?:0x[0-9a-f]+|\[)/;
const ARG = /"((?:[^"\\]|\\.)*)"/g;
const EXEC_FAILED = /=\s*-1\s+E\w+/;
const SIGCHLD = /^--- SIGCHLD \{.*?si_code=(?:CLD_EXITED|CLD_KILLED|CLD_DUMPED), si_pid=(\d+)/;
const EXITED = /^\+\+\+ exited with (\d+) \+\+\+/;
const KILLED = /^\+\+\+ killed by \w+/;
const EXITCALL = /^exit(?:_group)?\((\d+)\)/;

export function parseStraceLog(text) {
  const cur = new Map(), recs = [], parentOf = new Map();
  let tLast = 0;
  for (const raw of text.split('\n')) {
    const m = LINE.exec(raw);
    if (!m) continue;
    const pid = +m[1], t = parseFloat(m[2]), rest = m[3];
    if (t > tLast) tLast = t;
    let x;
    if (rest.startsWith('execve(')) {
      if (EXEC_FAILED.test(rest)) continue;
      const e = EXECVE.exec(rest);
      if (!e) continue;
      const cmd = [...e[2].matchAll(ARG)].map((a) => a[1].replaceAll('\\"', '"')).join(' ');
      let r = cur.get(pid);
      if (r && r.end === null) {
        // exec chain: the same process replaced its image
        r.program = e[1]; r.cmd = cmd;
      } else {
        r = { pid, start: t, end: null, program: e[1], cmd, exit: 0 };
        cur.set(pid, r); recs.push(r);
      }
    } else if ((x = EXITCALL.exec(rest))) {
      const r = cur.get(pid);
      if (r && r.end === null) { r.end = t; if (rest.startsWith('exit_group')) r.exit = +x[1]; }
    } else if ((x = EXITED.exec(rest))) {
      const r = cur.get(pid);
      if (r && r.end === null) { r.end = t; r.exit = +x[1]; }
    } else if (KILLED.test(rest)) {
      const r = cur.get(pid);
      if (r && (r.end === null || t - r.end < 1e-3)) { if (r.end === null) r.end = t; r.exit = -1; }
    } else if ((x = SIGCHLD.exec(rest))) {
      // the process that receives SIGCHLD for a child is that child's parent
      parentOf.set(+x[1], pid);
    }
  }
  if (!recs.length) return { command: '', span: 0, programs: [], procs: [] };
  for (const r of recs) if (r.end === null) r.end = tLast;
  recs.sort((a, b) => a.start - b.start);
  const byPid = new Map();
  recs.forEach((r, i) => { r.i = i; if (!byPid.has(r.pid)) byPid.set(r.pid, r); });
  const t0 = recs[0].start;
  let tEnd = t0;
  for (const r of recs) if (r.end > tEnd) tEnd = r.end;
  // Walk up to the nearest ancestor that itself exec'd; anything left over hangs off the first process.
  for (const r of recs) {
    let q = parentOf.get(r.pid), hops = 0, par = null;
    while (q !== undefined && hops < 64) {
      const cand = byPid.get(q);
      if (cand && cand !== r) { par = cand; break; }
      q = parentOf.get(q); hops++;
    }
    r.parent = par ? par.i : (r.i !== 0 ? 0 : -1);
  }
  const programs = [], index = new Map();
  const procs = recs.map((r) => {
    const base = r.program.slice(r.program.lastIndexOf('/') + 1) || r.program;
    if (!index.has(base)) { index.set(base, programs.length); programs.push(base); }
    const cmd = r.end - r.start >= 0.25 ? (r.cmd.length <= 170 ? r.cmd : r.cmd.slice(0, 96) + ' … ' + r.cmd.slice(-64)) : '';
    return [Math.round((r.start - t0) * 1000), Math.round((r.end - t0) * 1000), index.get(base), r.parent, r.exit, cmd];
  });
  return { command: recs[0].cmd.slice(0, 120), span: Math.round((tEnd - t0) * 1000) / 1000, programs, procs };
}
