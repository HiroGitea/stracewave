# stracewave

A 3D "wavetable" view of a build recorded with `strace`. Every row of the process tree becomes a ridge whose height is how many of its processes are running at that moment, and a time slice sweeps through the build.

![stracewave showing a Linux kernel build](docs/screenshot.png)

This is a prototype.

## Try it

It is a static page with no build step. Serve this folder and open it:

```bash
python3 -m http.server 8000
# then open http://localhost:8000
```

three.js is loaded from jsDelivr, so the 3D view needs network access. The timeline works without it.

## Record your own build

```bash
strace \
    --trace=execve,execveat,exit,exit_group,clone,clone3,fork,vfork \
    --follow-forks \
    --string-limit=1000 \
    -ttt \
    --output=strace.log \
    --seccomp-bpf \
    <command to profile>
```

Then press **Open strace log…** or drop the file on the page. The log is parsed in your browser and is not uploaded anywhere.

Logs recorded with straceprof's shorter command (without `clone,clone3,fork,vfork`) also load, with an approximate process tree.

## Reading the view

- **Ridges**: one per row of the process tree. Height is how many of that row's processes are running, on a square-root scale so a single long-running process stays visible next to a burst of a hundred.
- **Light sheet**: the time slice. Press play, drag the bars in the timeline, or click the 3D view to move it. The line on the sheet joins every row's height at that instant.
- **Slice panel**: the processes alive at the slice, longest-running first. Click one to copy its command.
- **Back wall**: busy processes across all rows, with the core count as a line. Where the wall sits far under the line, the machine is idle.
- **White ribbons and labels**: the long links of the critical chain, riding on the ridge that holds each process.
- **Name tags**: the busy processes that have been running longest at the slice.
- **Arcs**: when a process starts, a short-lived arc runs from its parent's ridge to its own.
- **Row tools** (hover a timeline row): ▤ unfolds the row into one block per process, stacked like a Gantt chart, with failed ones in red; hover a block for its command. S shows only the soloed rows in 3D, M hides a row. Double-clicking a ridge also unfolds it. Pointing at a row highlights it; with ray tracing on, the highlight is drawn over the traced picture, so it does not restart the render.
- **Timeline**: green has finished, yellow is running now, dots have not started. The footer counts individual processes. A white underline marks the critical chain.
- **Minimap**: the strip above the timeline shows busy processes over the whole trace against a dashed core line. Drag across it to zoom the timeline and the 3D view into that range, drag the window to pan, double-click to show everything.
- **Busy and cores**: a process counts as busy only while none of its children is alive, since a parent waiting on a child is idle. The core count comes from a `-jN` flag in the trace when there is one, otherwise it is estimated; the Cores box overrides it. Stretches where busy sits far below the core line are where the build is not using the machine.
- **Critical chain**: walking back from the end of the build, the busy stretch that finished last before each one began. Its long links are the processes the whole build waited for.
- **Glass**: on by default. Ridges are tinted panes you can see through; the standard renderer uses plain transparency, and the path tracer refracts through them. Turn it off for solid ridges, which also converge faster.
- **Sound**: off by default. Every row shown in 3D is its own track: one note of a pentatonic scale (front rows low, back rows high), a timbre picked by program name, and its own place between left and right. A track is as loud as its ridge is tall where the slice cuts it, so the mix you hear is the slice. Soloing or muting a row does the same to its track, and pointing at a row brings its track forward. A bass note follows how busy the machine is, and a process starting on a different row from its parent rings a bell on that row's note. It sounds while the slice moves.
- **Record video**: plays the visible range from its start and records it with sound, then saves an MP4 (or WebM where the browser cannot write MP4). The frame holds the 3D view with its labels and the timeline with its row names. Recording runs in real time and turns Sound on; press the button again to stop early.
- **Ray tracing**: off by default; once you switch it on, the choice is remembered per browser. The ridges and floor are path traced on the GPU and keep refining, while the slice is drawn on top each frame, so playing and scrubbing do not restart the picture. While the camera moves, the page works the way games do: it traces one sample per pixel per frame at half resolution and blends it into the previous frame's picture, re-projected through the new camera, with over-bright samples clamped and neighbours on the same surface averaged. That keeps a drag smooth at a fraction of the GPU load; the picture sharpens to full quality once the camera rests. The first use compiles shaders, which took about 10 seconds on the machine this was developed on. The corner of the 3D view names the GPU the browser is using; if that is a software renderer, ray tracing stays off.

## How the process tree is built

- With fork records in the log (`clone`, `clone3`, `fork`, `vfork`), every process is linked to the process that forked it, and threads are folded into their process. The tree is exact.
- Without them, a process's parent is the process that received `SIGCHLD` for it. That signal is not reported for every child (several exits can share one signal), so in the bundled example traces 73 to 88 percent of processes link to a parent and the rest attach to the first process. The page marks such a trace "approximate tree", and leaves programs that only wait on others (`make`, shells, compiler drivers) out of the busy estimate so they are not mistaken for bottlenecks.
- Intermediate forks that never exec (subshells, for example) are skipped: each process attaches to its nearest ancestor that did exec.
- Siblings that run the same program merge into one row. Siblings that account for under 0.4 percent of all process time share one "N more (small)" row, which opens like any other.

## Layout

| Path | What it is |
| --- | --- |
| `index.html` | The page and the import map for three.js |
| `src/parse.js` | strace log to compact trace |
| `src/app.js` | Process tree, timeline, slice panel and the 3D scene |
| `src/style.css` | Styles |
| `examples/*.json` | Three converted example traces |
| `tools/convert.mjs` | `node tools/convert.mjs strace.log > examples/name.json` |

## Known limits

- The uv and Linux kernel examples were recorded without fork records, so their trees are approximate. The Ruby example has them.
- Busy counts processes, not threads, so a multi-threaded compiler counts once.
- `execveat` is not parsed.
- The whole log is read into memory, so multi-gigabyte logs will not load.
- Ray tracing needs WebGL2.

## Credits

The log format and the example traces come from [straceprof](https://github.com/akawashiro/straceprof) by Akira Kawata (MIT). See `NOTICE`.

At runtime the page loads [three.js](https://threejs.org/), [three-mesh-bvh](https://github.com/gkjohnson/three-mesh-bvh) and [three-gpu-pathtracer](https://github.com/gkjohnson/three-gpu-pathtracer) from a CDN; none of them is vendored here.

## License

MIT. See `LICENSE`. The example traces carry straceprof's MIT notice in `NOTICE`.
