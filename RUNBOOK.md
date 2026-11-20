# rhcheck: checking the `lean.tar.gz` GRH formalization fast

Source: https://alpo.ge/remark.pdf, archive parts `https://alpo.ge/lean.tar.gz.part01..14`
(concatenated sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`).
175,187 Lean files, 1.03 GB, 17.4 M lines, Lean `v4.33.1`, Mathlib tag `v4.33.1`
(`0df444a3`). Every file is in the import closure of `Main.lean`; import depth 203.

The archive is untrusted: Lean files run arbitrary code while they elaborate. Every Lean
process here runs in a `bwrap` sandbox: no network, filesystem read-only, home and shared
filesystems hidden, one private scratch dir.

## Stages

| stage | what | tool |
|---|---|---|
| 0 scan | import graph + static audit (`axiom`, `sorry`, `native_decide`, metaprogramming…) | `scan.py SRC OUT` |
| 1 build | compile every module, critical-path first, across nodes | `dbuild.py … --mode build` |
| 2 audit | statements and axioms of the five `Main` theorems, from the compiled environment, by a script that imports only `Lean` | `verify/audit.sh BASE` |
| 3 replay | re-check every declaration of every module (project + Mathlib & deps) in the Lean kernel | `dbuild.py … --mode replay` |

Stage 3 does not trust stage 1: a scheduler or sandbox mistake cannot produce a false pass,
because every olean is replayed through the kernel against its imports.
Not done yet: an independent kernel (lean4export + nanoda / `comparator`).

## Layout of a BASE directory

    BASE/lean/            extracted archive (+ .lake/packages after `lake exe cache get`)
    BASE/out/graph.json   from scan.py
    BASE/conf.json        from mkconf.sh BASE
    BASE/build/lib/       oleans we produce
    BASE/state/           results-build.jsonl, results-replay.jsonl, summary-*.json
    BASE/verify/          audit-result.txt, used-modules.txt

chili: `BASE=/bulk/shared/rieman`. LUMI: `BASE=/flash/project_462001825/rieman`
(scratch is near its file quota; flash has room), `ELAN_HOME=$BASE/elan`.

## Running

    python3 rhcheck/scan.py lean/src out                # 30 s
    rhcheck/mkconf.sh . > conf.json
    # one node (chili):  SLOTS=26 rhcheck/run-local.sh . [--mode replay] [--roots A,B]
    # LUMI:              sbatch -N 8 -t 02:00:00 rhcheck/lumi-run.sbatch            (build)
    #                    sbatch -N 8 -t 01:00:00 rhcheck/lumi-run.sbatch --mode replay
    rhcheck/verify/audit.sh .                           # after the build

Resubmitting resumes: modules with a successful result line and an existing olean are skipped.
A failed module is retried once, then reported; its dependents stay unbuilt and the run exits 1
with the list in `state/summary-build.json`. Out-of-memory jobs are retried alone with more slots.

## How the build command was derived

`lake build -v` on one module shows lake's own call: `lean --tstack=400000 FILE -o … --setup
setup.json --json` with the lakefile's `leanOptions` in the setup file. `dbuild.py` issues the
same call (without `-i`/`-c`), including the `GroundTheoryFields` library's extra
`synthInstance.maxHeartbeats`.
