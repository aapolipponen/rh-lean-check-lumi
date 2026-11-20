# 9. Building and checking

Checking this archive by machine means compiling 175,187 modules with the pinned toolchain, auditing the axioms behind the five final theorems, and replaying the declarations through one or more independent kernels. This page explains how the independent LUMI build was done, the two practical obstacles (the Linux memory-mapping limit and per-module memory), what that run did and did not do, and the public verification status as recorded on the evening of 2026-11-20.

## Terms used on this page

| Term | Meaning |
|---|---|
| `.olean` | the compiled form of a Lean module; importing a module loads (memory-maps) its `.olean` and related files |
| kernel | the small trusted core of Lean that checks every declaration; "replay" means re-checking compiled declarations against it |
| `leanchecker` | the official tool that replays `.olean` files through the Lean kernel |
| nanoda, con-leche, con-ron, lean4lean | independent re-implementations of a Lean kernel that check an exported proof |
| `lake comparator` | a tool that checks a submission's statements against a reference and audits axioms |
| `vm.max_map_count` | the Linux per-process limit on memory mappings |

## Getting the archive

From rhcheck/RUNBOOK.md and rhcheck/README.md.

- 14 parts `https://alpo.ge/lean.tar.gz.part01..14`; concatenated sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
- 175,187 Lean files, 1.03 GB, 17.4M lines. Lean `v4.33.1`, Mathlib tag `v4.33.1` (`0df444a3`). Mathlib's compiled files come from the official build cache (`lake exe cache get`).
- Every file is in the import closure of `Main.lean`; import depth 203.

**The archive is untrusted code.** Lean files can run arbitrary programs while they compile. In the independent run every Lean process ran in a sandbox (Singularity container, or `bwrap` where available) with no network, a read-only view of its inputs, home and shared filesystems hidden, and one private scratch directory. (rhcheck/README.md, Method; rhcheck/RUNBOOK.md)

## How the build command was derived

`lake build -v` on one module shows Lake's own call:

```
lean --tstack=400000 FILE -o … --setup setup.json --json
```

with the lakefile's `leanOptions` in the setup file. The independent driver `dbuild.py` issues the same call (without `-i`/`-c`), including the extra `synthInstance.maxHeartbeats` of the `GroundTheoryFields` library. Outputs are written to a temporary name and renamed. (rhcheck/RUNBOOK.md) Sutherland's page notes the same approach for his build: files compiled by calling `lean` directly, with a 77-module sample byte-identical to `lake build` (web-briefing.md §A).

## Obstacle 1: the memory-mapping limit

Lean maps every imported file separately, and for module-system libraries that is five files per module (`.olean`, `.olean.server`, `.olean.private`, `.ir`, `.ir.sig`). `import Mathlib` alone costs about 52,000 mappings. With the traditional Linux default `vm.max_map_count = 65530`, any module with more than roughly 12,000 transitive project imports fails with

```
failed to read file '….olean'
```

although the file is fine. That affects **8,974 of the 175,187 modules, including `Main`**. (rhcheck/README.md; structure.md)

Fixes:
- With root: `sysctl vm.max_map_count=1048576`.
- Without root (as on LUMI): preload `rhshim.c`, which makes Lean read small files instead of mapping them (42,000 of Mathlib's files are under 4 KB) and lets Lean's own read fallback allocate. It changes where bytes are held, not what is loaded. (rhcheck/README.md)

## Obstacle 2: memory per module

A module near the top of the tree needs about **5 to 6 GB of private memory** just to import its dependencies, against under 1 GB for a shallow one. Scheduling by core count alone runs a 256 GB node out of memory once the build reaches the deep modules. `dbuild.py` weights modules by import-closure size and kills and retries the largest jobs before the node does; out-of-memory jobs are retried alone with more slots. (rhcheck/README.md; rhcheck/RUNBOOK.md) Sutherland's page gives about 100 GB RAM and 70 GB disk to check from oleans (web-briefing.md §A).

## Wall time is the import chain, not cores

The build is a few hundred CPU-hours in total. The import graph is about 203 levels deep, and the last 68 levels hold the 10,000 most expensive modules, so the end of the build is sequential whatever the core count. In the independent run, the first 94% took 48 minutes on 8 LUMI-C nodes; the deepest 6% was slow. (rhcheck/README.md)

## Olean hashes depend on the path

Some oleans embed the absolute path of their source file. The same module compiled under two spellings of one directory gave different bytes; with Lake's spelling the independent output was byte-identical to Lake's. **Hashes are comparable only between builds at the same absolute path.** (rhcheck/README.md)

## The independent run (LUMI)

Run by Aapo Lipponen on the LUMI supercomputer (EuroHPC Joint Undertaking, hosted by CSC – IT Center for Science, Finland). Stages and status as of the last README update, **2026-11-20 20:50 UTC** (rhcheck/README.md):

| Stage | What | Status at 20:50 UTC |
|---|---|---|
| 0 scan | import graph and static audit of all files | done: no `axiom`, `sorry`, `admit` or `native_decide` in the source |
| 1 build | compile every module, critical path first, across nodes | done: 175,187 of 175,187 compiled, no Lean errors (finished 22:21 UTC, 2026-11-20); `Main.olean` and `Statements.olean` hashes identical to those Andrew Sutherland published |
| 2 audit | statements and axioms of the five `Main` theorems, and the modules and declarations they depend on, from the compiled environment, by a program importing only `Lean` (`verify/Audit.lean`) | queued, to run after the compile |
| 3 replay | `leanchecker` on each module | implemented and tested on a sample; **not run over the whole tree**, because Sutherland had already done it |
| independent kernel | nanoda / Comparator | not run by this project |

Later results of stages 1 and 2 go to `rhcheck/results/` and are not among the inputs to these documents. A full pass would establish that the published files compile with the pinned toolchain, that the five theorems have the stated types, and that they rest on no axioms beyond Lean's three. It would not establish that anyone understands the argument. It trusts the Lean 4.33.1 kernel and binaries, Mathlib's definitions (`RiemannHypothesis`, `riemannZeta`, `DirichletCharacter.LFunction`) and the four definitions in `Statements.lean`. (rhcheck/README.md)

The independent run did not: replay the kernel over the whole tree, run a second kernel, or compare statements with `lake comparator`. It was one confirmation among several.

## Public verification status

As recorded in web-briefing.md, compiled from web search at about **21:15 UTC on 2026-11-20**. It may be out of date when you read this; check the linked pages.

| Check | By | Result as recorded |
|---|---|---|
| compile of all 175,187 modules | Andrew Sutherland (MIT), https://math.mit.edu/~drew/grh/ | passed (16:43 UTC) |
| axioms of the five `Main` theorems | Sutherland | only `propext`, `Classical.choice`, `Quot.sound` |
| `leanchecker` replay of all modules | Sutherland | passed (about 18:17 UTC) |
| nanoda (independent kernel) | Sutherland | accepts the export (19:05:45 UTC, 27 min 42 s, 80 threads); export sha256 `bd484ac9...` matches Deicyde CI |
| Lean default and paranoid kernels | Sutherland | running |
| `lake comparator` | Sutherland | statement comparison and axiom check passed in one run; kernels still running |
| con-leche, con-ron | Sutherland's page (19:45 UTC version) | "declined" (exit 2, not a rejection): they do not support the reflexive inductive `FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate` |
| con-leche | Szymon Teżewski (report 20:40 to 20:58 UTC) | accepts |
| lean4lean | | 4.36 cannot read a v4.33 export; a build with 4.33.1 was planned by Deicyde |
| CI checks | Deicyde, https://github.com/Deicyde/riemann-hypothesis | green at 15:07 UTC: source identical to the tarball, challenge compiles against Mathlib; static scan finds no `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `opaque`; Comparator on the submission not yet run ("build takes hours") |
| replay campaign | https://github.com/rohanarun/alpoge-rh-replay | full build, axiom audit and kernel check pending at 21:03 UTC |

**Conflict, unresolved in the inputs.** For con-leche, Sutherland's 19:45 UTC page and Teżewski's later report disagree. The later report says it accepts; the earlier page says it declined because of an unsupported reflexive inductive type, which is not a rejection. These documents record both and do not resolve it. (web-briefing.md §A)

No verification statement from the Lean FRO, Leonardo de Moura, Terence Tao or Anthropic was found as of the briefing (web-briefing.md §A).

## What machine checking establishes, and what it does not

| Established by machine (per the reports above) | Not established by machine |
|---|---|
| the archive compiles with Lean v4.33.1 and Mathlib v4.33.1 | that the definitions in `Statements.lean` and Mathlib mean what a mathematician means (a human must read them; the first statements review judged them faithful) |
| the five theorems use only Lean's three standard axioms | that anyone understands the proof |
| the kernel, and at least one independent kernel (nanoda), accept the declarations | that the named intermediate statements match the literature (pages [07](07-named-theorems.md) and [10](10-open-frontier.md)) |

## Sources

- rhcheck/README.md (status, notes for builders, method, what a pass establishes)
- rhcheck/RUNBOOK.md (archive, stages, build command)
- analysis/web-briefing.md (§A, public verification status, dated about 21:15 UTC 2026-11-20)
- rhcheck/results/structure.md (modules above the mapping threshold)
