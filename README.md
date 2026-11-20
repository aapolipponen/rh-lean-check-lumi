# Independent verification of Alpöge's Lean formalization of RH / GRH, run on LUMI

On 20 November 2026 Levent Alpöge announced a Lean proof of the Riemann Hypothesis and of GRH for
Dirichlet L-functions, found with Claude ([remark.pdf](https://alpo.ge/remark.pdf)). The proof is theirs.
This repository records one independent check of the published archive: we compiled it, audited what the
main theorems depend on, and re-checked every module in the Lean kernel.

## Status: run in progress (updated 2026-11-20 19:25 UTC)

No verdict yet. This table is filled in as each stage finishes; nothing here should be read as a result
until the compile, the audit and the kernel replay have all passed.

| Check | Result |
|---|---|
| Archive | 14 parts from alpo.ge, concatenated sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` |
| Static scan of all 175,187 files | done: no `axiom`, `sorry`, `admit` or `native_decide` in the source ([results/static-scan.txt](results/static-scan.txt)) |
| Compile all 175,187 modules (Lean v4.33.1, Mathlib tag `v4.33.1`) | **running**: 121,830 compiled, 0 failures, after 25 min on 8 LUMI-C nodes |
| `riemannHypothesis : RiemannHypothesis` is a theorem whose statement is Mathlib's own definition | queued (runs after the compile) |
| Axioms of the five theorems in `Main.lean` | queued |
| Kernel replay (`leanchecker`) of every project module and every Mathlib/dependency module | queued |
| Second, independent kernel (nanoda / Comparator) | not run |

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
ran in a Singularity container with no network, a read-only view of its inputs and one private scratch
directory.

1. **Scan** (`scan.py`): import graph of all 175,187 files and a text audit. No `axiom`, `sorry`, `admit`
   or `native_decide` in the source. Import depth 203; every file is reachable from `Main`.
2. **Build** (`dbuild.py`): a coordinator hands modules to one worker per node, longest dependency chain
   first. Each module is compiled with the same `lean` invocation Lake uses (taken from `lake build -v`),
   including the lakefile's options. Outputs are written to a temporary name and renamed.
3. **Audit** (`verify/Audit.lean`): a program that imports only `Lean`, loads the compiled environment
   without running any project code, and walks every constant the five theorems depend on.
4. **Replay** (`dbuild.py --mode replay`): `leanchecker` on each module. A scheduler or sandbox mistake in
   step 2 cannot produce a false pass, because every compiled file is re-checked against its imports.

Everything needed to repeat this is in this repository; see [RUNBOOK.md](RUNBOOK.md). Raw outputs
(per-module results, olean hashes, audit output, replay results, Slurm logs) are added to `results/` as
each stage finishes.

## Acknowledgements

Computations were run on the LUMI supercomputer, owned by the EuroHPC Joint Undertaking and hosted by
CSC – IT Center for Science (Finland) and the LUMI consortium. We thank CSC for the computing resources and
for their quick support.

Run by Aapo Lipponen with Claude (Anthropic) writing and operating the checker.
