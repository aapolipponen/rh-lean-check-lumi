# Independent verification of Alpöge's Lean formalization of RH / GRH, run on LUMI

On 20 November 2026 Levent Alpöge announced a Lean proof of the Riemann Hypothesis and of GRH for
Dirichlet L-functions, found with Claude ([remark.pdf](https://alpo.ge/remark.pdf)). The proof is theirs.
This repository records one independent check of the published archive: we compile it in a sandbox and audit, from the
compiled environment, what the main theorems state and depend on.

## Status: compile in its last stretch (updated 2026-11-20 20:50 UTC)

This is one independent confirmation among several. Andrew Sutherland (MIT) reported a full compile,
axiom audit, per-module kernel replay and a nanoda pass hours before this run got this far; see the
"Discussion: Alpöge Proves the Riemann Hypothesis" thread on the Lean Zulip and
https://math.mit.edu/~drew/grh/ . Nothing below should be read as a verdict of ours until the compile
and the audit have both finished.

| Check | Result |
|---|---|
| Archive | 14 parts from alpo.ge, concatenated sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` |
| Static scan of all 175,187 files | done: no `axiom`, `sorry`, `admit` or `native_decide` in the source ([results/static-scan.txt](results/static-scan.txt)) |
| Compile all 175,187 modules (Lean v4.33.1, Mathlib tag `v4.33.1`), each `lean` process sandboxed | **running**: 171,000+ compiled (97.6%), no Lean errors. The first 94% took 48 min on 8 LUMI-C nodes; the deepest 6% is slow for the reasons below. |
| Statement and axioms of the five theorems in `Main.lean`, from the compiled environment | queued (runs after the compile) |
| Which modules and declarations the five theorems actually depend on | queued (same run) |
| Kernel replay (`leanchecker`) of every module | **not run by us.** Already done by Sutherland; we chose not to spend allocation repeating it. |
| Second, independent kernel (nanoda / Comparator) | not run by us; nanoda pass reported by Sutherland |

### Notes for anyone else building this

**`vm.max_map_count`.** Lean maps every imported file separately, and for module-system libraries that is
five files per module (`.olean`, `.olean.server`, `.olean.private`, `.ir`, `.ir.sig`). `import Mathlib`
alone costs about 52,000 memory mappings. With the traditional Linux default of 65,530 per process, any
module with more than roughly 12,000 transitive project imports fails with
`failed to read file '….olean'` although the file is fine: 8,974 of the 175,187 modules, including `Main`.
With root, `sysctl vm.max_map_count=1048576` fixes it. Without (LUMI), [`rhshim.c`](rhshim.c) is
preloaded: it makes Lean read small files instead of mapping them (42,000 of Mathlib's files are under
4 KB) and lets Lean's own read fallback allocate. It changes where bytes are held, not what is loaded.

**Memory.** A module near the top of the tree needs about 5 to 6 GB of private memory just to import its
dependencies, against under 1 GB for a shallow one. Scheduling by core count alone runs a 256 GB node out
of memory once the build reaches the deep modules; `dbuild.py` weights modules by import-closure size and
kills and retries the largest jobs before the node does.

**Olean hashes and paths.** Some oleans embed the absolute path of their source file. The same module
compiled under two spellings of one directory gave different bytes; with Lake's spelling our output was
byte-identical to Lake's. Hashes are comparable only between builds at the same absolute path.

**Wall time is the import chain, not cores.** The build is a few hundred CPU-hours in total; the import
graph is 203 levels deep, and the last 68 levels hold the 10,000 expensive modules.

## What this does and does not establish

A full pass would establish that the published Lean files compile with the pinned toolchain, that the five theorems in
`Main.lean` have the stated types, that they rest on no axioms beyond Lean's standard three, and that the
Lean kernel accepts every declaration when replayed.

It would not establish that anyone understands the argument, and it trusts: the Lean 4.33.1 kernel and
toolchain binaries, Mathlib's definitions (in particular `RiemannHypothesis`, `riemannZeta` and
`DirichletCharacter.LFunction`), and the four definitions in `src/Statements.lean`, which a human should
read. Mathlib's compiled files came from the official build cache and were replayed in the kernel here.

## Method

The archive is untrusted code: Lean files can run arbitrary programs while they compile. Every Lean process
ran in a Singularity container (bubblewrap where available) with no network, a read-only view of its inputs and one private scratch
directory.

1. **Scan** (`scan.py`): import graph of all 175,187 files and a text audit. No `axiom`, `sorry`, `admit`
   or `native_decide` in the source. Import depth 203; every file is reachable from `Main`.
2. **Build** (`dbuild.py`): a coordinator hands modules to one worker per node, longest dependency chain
   first. Each module is compiled with the same `lean` invocation Lake uses (taken from `lake build -v`),
   including the lakefile's options. Outputs are written to a temporary name and renamed.
3. **Audit** (`verify/Audit.lean`): a program that imports only `Lean`, loads the compiled environment
   without running any project code, and walks every constant the five theorems depend on.
4. **Replay** (`dbuild.py --mode replay`): `leanchecker` on each module. Implemented and tested on a
   sample, but not run over the whole tree (see the table above).

Everything needed to repeat this is in this repository; see [RUNBOOK.md](RUNBOOK.md). Raw outputs
(per-module results, olean hashes, audit output, replay results, Slurm logs) are added to `results/` as
each stage finishes.

## Acknowledgements

Computations were run on the LUMI supercomputer, owned by the EuroHPC Joint Undertaking and hosted by
CSC – IT Center for Science (Finland) and the LUMI consortium. We thank CSC for the computing resources and
for their quick support.

Run by Aapo Lipponen.
