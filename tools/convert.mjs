#!/usr/bin/env node
// Convert a strace log into the compact JSON the page loads for its examples.
//   node tools/convert.mjs path/to/strace.log > examples/name.json
import { readFileSync } from 'node:fs';
import { parseStraceLog } from '../src/parse.js';

const path = process.argv[2];
if (!path) { console.error('usage: node tools/convert.mjs <strace.log> > out.json'); process.exit(1); }
const trace = parseStraceLog(readFileSync(path, 'utf8'));
console.error(`${path}: ${trace.procs.length} processes, ${trace.span} s, ${trace.programs.length} programs`);
process.stdout.write(JSON.stringify(trace));
