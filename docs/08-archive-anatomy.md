# 8. Archive anatomy

The archive is 175,187 Lean files and about 17.4 million lines in ten libraries, with no comments at all, about one million declarations, and an import graph 202 to 203 levels deep in which `Main` sits on top of everything. This page gives its size and shape, its proof style, its duplicates, and a static name-level reachability analysis, with an explanation of what that analysis does and does not show.

All figures are from text scans of the source (scan.py, idx.py, reach.py), not from the compiled proof terms. Nothing here concerns mathematical content.

## Terms used on this page

| Term | Meaning |
|---|---|
| module | one `.lean` file; Lean compiles each to an `.olean` |
| import closure | all modules a module imports, directly or transitively |
| import depth | length of the longest import chain below a module |
| tactic proof | a proof written `:= by …` as a script of tactics; a term proof is written directly |
| `maxHeartbeats` | a per-declaration limit on elaboration work; the default is 200,000 |
| static reachability | which declarations are *mentioned*, transitively, starting from the final theorems, judged from source text |

## Size and libraries

From structure.md (import graph) and archive-stats.md §0, §8.

| Library | Modules | Lines | Median import closure | Declarations reachable (rule A) |
|---|---:|---:|---:|---:|
| `Development` | 141,928 | 12,232,663 | 1,129 | 403,705 of 678,484 |
| `Formalism` | 18,254 | 3,200,748 | 229 | 136,815 of 237,054 |
| `GroundTheory` | 8,507 | 1,119,138 | 19 | 33,366 of 73,681 |
| `ReciprocityTheory` | 3,845 | 563,016 | 24 | 25,012 of 36,123 |
| `CompanionTheory` | 2,027 | 194,218 | 399 | 9,934 of 11,650 |
| `PositivityTheory` | 449 | 55,130 | 21,541 | 1,124 of 4,551 |
| `Lemmata` | 167 | 9,232 | 1 | 193 of 243 |
| `BuildAid` | 5 | 20 | 1 | |
| `Supplements` | 3 | 22 | 175,183 | 4 of 4 |
| `Statements` | 1 | 16 | 1 | 4 of 4 |
| `Main` | 1 | 12 | 175,187 | 5 of 5 |
| **All** | **175,187** | **17,374,215** | **721** | **610,162 of 1,041,799** |

Line counts differ slightly between the two scans: structure.md reports 17,374,215 lines from the import graph, archive-stats.md 17,549,402 including 2,017,643 blank lines; the difference comes from how the two scripts count. The archive is about 1.03 GB (rhcheck/RUNBOOK.md).

95,418 files (54%) are under `Development/AbelianVarietyTheory/Proofs`. Directories are flat: 138,172 files sit exactly four directories deep. (archive-stats.md §4)

## Imports

- 753,569 project import edges. 136,003 modules (77.6%) `import Mathlib` wholesale; only 269 import a specific Mathlib module; 22.2% import nothing external. (structure.md; archive-stats.md §7)
- Import closure sizes: median 721, 90th percentile 9,284, 99th 24,339, 99.9th 34,817. 8,974 modules have closures above 12,000, which matters for building (page [09](09-building-and-checking.md)); 17 are above 60,000. (structure.md)
- Import depth: `Main` 202, `Supplements.Kernels.MainTheoremsAll` 201 (archive-stats.md §8). The rhcheck README counts 203 levels, counting differently.
- 987 modules are import-only aggregators (structure.md). Every file is in `Main`'s import closure (rhcheck/RUNBOOK.md), and structure.md counts a single module that no other module imports.
- Most-imported modules: `CTSmallCone` (3,088), `SiegelWeilAnisotropicHermitian` (2,972), `DiscreteSeriesHermitianUnique` (2,518), `ExistsNormLeHeightPow` (2,460). (structure.md)

The top of the tree (structure.md):

| Module | Modules beneath | Direct imports | Lines |
|---|---:|---:|---:|
| `Main` | 175,187 | 2 | 12 |
| `Supplements.Kernels.MainTheorems` | 175,179 | 3 | 16 |
| `…CharacterBoxes.MainConclusion` | 175,174 | 5 | 14 |
| `…DenseThresholdCases.VwinOfRow` | 157,604 | 2 | 5 |
| `…DenseThresholdCases.TopMainZj` | 157,603 | 11 | 75 |
| `…ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin` | 151,286 | 201 | 814 |
| `…DenseThresholdCases.TemperedProductOfSquareIntegrable` | 146,663 | 192 | 344 |
| `…CharacterBoxes.RiemannHypothesisOfEveryCharacter` | 102,080 | 208 | 231 |

## Declarations and file shapes

From archive-stats.md §1, §4, "What stands out".

- About 1.07 million declarations by keyword count: 784,092 `theorem`, 34,663 `lemma`, 212,819 `def`, 13,202 `abbrev`, 8,286 `structure`, 7,598 `instance`, 4,662 `example`. 65,565 are `private`. (The reachability parser counts 1,041,799 declarations of the main kinds.)
- 78,670 files (44.9%) hold exactly one declaration.
- 46,610 file names (26.6%) end in `Statement`. Many deep facts are routed through `…Statement.lean` wrappers of the form `first | exact @X.foo | …`, so the real proof often sits one file lower (frontier-c-galois.md Q1).
- File lengths: 68,153 files of 10 to 49 lines; 252 of 1,000 to 1,999; 62 of 2,000 to 4,999; 11 of 5,000 or more.
- Naming uses short opaque suffixes: `Zero`, `One`, `Bound`, `Pf`, `Holds`, `A`, `B`, `C`, `L`, `St`; 468 names end in `Alt`. Names do not always describe content (page [07](07-named-theorems.md), "misnamed").

## Proof style

From archive-stats.md §2, §3 and special constructs.

- 689,060 tactic proofs (65%) and 364,943 term proofs (35%). Tactic proofs have median 9 lines in every large library, 90th percentile 35 to 43, 99th 103 to 120.
- The 15 longest proofs (534 to 8,001 lines) are all in `Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities`; the longest is `UpperTheory.Reformulated.B.Gr34.mem_UC` (8,001 lines, `FixPiIff.lean`). Outside `Development` the longest is 478 lines.
- Tactic mix: `have` 2.18M lines, `rw` 1.47M, `exact` 0.77M, `obtain` 0.58M, `refine` 0.51M, `intro` 0.49M. `omega` 137,597 occurrences, `grind` 126, `aesop` 28, `simp_all` 1,620.
- `set_option maxHeartbeats` appears 57,556 times, about once per 19 declarations; 88% set 1,000,000 (5 times the default), the largest 64,000,000.
- Local scaffolding: 50,672 `attribute [local instance]`, 28,187 `open … in`, 1,695 `local notation`.
- **No `sorry`, `admit`, `native_decide`, `exact?` or `apply?`** in comment-stripped code. The rhcheck static scan also found no `axiom` (rhcheck/README.md).
- `Lemmata` (167 files) differs from the rest: median tactic proof 23 lines, 97% tactic style.

## No comments

There are zero comment lines, zero docstrings (`/--`), zero module docs (`/-!`) and zero TODO / FIXME / HACK in all 175,187 files, confirmed by grep on a 20,000-file sample. (archive-stats.md §6) There is also no human-readable paper; the only prose is the four-page announcement. Everything these documents say about content therefore comes from reading Lean statements and proofs.

## Duplicates

282 groups of exact duplicates (imports, namespace and `end` lines stripped) cover 781 files, of which 499 are redundant. One group has 151 files identical apart from imports (`…Imports.lean` stubs in `CompanionTheory/…/PieriDegreeBounds`). Many groups are three or four same-named copies in sibling directories, for example `StabilizerVolume`, `StabilizerOrbitVolume`, `WeilStabilizerVolume` under `Formalism/PeriodIntegrals/UnitaryGroupMassFormula`. Loosening the comparison (digits, `Alt`/`Bis` suffixes, primes removed) gives 289 groups and 508 redundant files. (archive-stats.md §5)

There are also many near-parallel declarations with `_alt`, `_alt_alt` and `_bis` suffixes on the proof path (for example `vwin_of_hypotheses_H_E_alt`, `NLinkClose.main_alt_alt`), and homonyms in different namespaces, such as two `SiegelWeilUnitaryConvergent` and several `StrongApproxSU` (statements-review-2-reptheory.md #17, #24).

## Sizes of subtrees on the proof map

Directory sizes quoted by the content reports, to give a sense of scale for the strands on pages 03 to 06.

| Directory (under `src/`) | Files | Lines | Content | Source |
|---|---:|---:|---|---|
| `Development/WeilBound/CoreStatements/PadicHodgeComparison/` | 538 | 50,512 | Hodge–Tate comparison for good reduction | frontier-g-deep-inputs.md §I.3 |
| `…/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/` | 532 | 49,736 | assembly of the window bound and modularity input | frontier-g-deep-inputs.md §II.2 |
| `…/AutomorphicVarieties/PatchingModules/` | 441 | 50,353 | Taylor–Wiles patching | frontier-g-deep-inputs.md §II.2 |
| `…/AutomorphicVarieties/LiteratureResults/KTheoryStability/` | 286 | 34,368 | homological stability, Soulé-type bounds | frontier-d-window.md Q3 |
| `…/AutomorphicVarieties/KatoQuadraticCharacters/` | 200 | 23,400 | Kato's Euler system | frontier-d-window.md Q2 |
| `…/GaloisRepresentations/SphericalCoordinates/` | 147 | 16,605 | complex uniformisation and fixed points | frontier-g-deep-inputs.md §I.2 |
| `…/AutomorphicVarieties/CommutativeAlgebra/` | 127 | 19,400 | graded rings, `LemmaM` | frontier-d-window.md Q2 |
| `…/GaloisRepresentations/LocalMaximality/` | 100 | 16,500 | local computations for the Lefschetz formula | frontier-g-deep-inputs.md §I.2 |
| `…/Foundations/EtaleClopenDescent/` | 83 | 14,457 | algebraic holomorphic Lefschetz formula | frontier-g-deep-inputs.md §I.2 |
| `…/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/` | 62 | 4,672 | Ferrero–Washington via Sinnott | frontier-d-window.md Q5 |
| `…/AutomorphicVarieties/PrimitiveFrobeniusFixed/` | | 7,350 | Kolyvagin–Rubin Euler system | frontier-d-window.md Q2 |

Line counts given as "23.4k", "19.4k" and "16.5k" in the reports are shown rounded.

## Static reachability

### What was done

static-reachability.md parsed every file into declarations, resolved each identifier token to candidate project declarations (using namespaces, `open`s and the import closure), and traversed from the five theorems of `Main`. Three rules:
- **A**: no instances;
- **B**: also an instance is reachable if its module is in the closure of a module with a reachable declaration and its text mentions a reachable structure or class;
- **C**: like A, but follow only tokens with a unique candidate.

### Headline

| Rule | Reachable declarations | % of declarations | Modules with ≥ 1 reachable | % of modules | % of declaration lines |
|---|---:|---:|---:|---:|---:|
| A | 610,162 | 58.6% | 118,200 | 68.0% | 62.4% |
| B | 612,472 | 58.8% | 118,347 | 68.1% | 62.5% |
| C | 595,783 | 57.2% | 116,311 | 66.9% | 60.8% |

Maximum reference depth from the roots is 52, the bulk at depths 10 to 30. Only 3 of 158 directories with at least 20 modules have no reachable declaration (72 modules in all). So the unused material is spread within directories, not concentrated in whole subtrees. (static-reachability.md)

Other findings:
- All 242 `UpperTheory.LiteratureTheorems` theorems in literature.json are reachable, because `every_character_of_literature_of_vWin` mentions them or their bundles. 177 of 182 distinct statement constants are reachable. Of 1,549 `GlobalTheory.Published` declarations, 656 (A) / 698 (B) are reachable.
- 151 of 8,265 structures and classes are never mentioned anywhere else (a lower bound on dead structures), for example `GeneralHyps` and `GeneralHypV`.
- Specific modules on the proof map with few or no reachable declarations: the module defining the chain length `mAt` (0 of 38 under rule A, 1 under rule B); `IteratedLiftChains` (1 of 20); `NoExcludedParameterOfLiftParameters` (2 of 5) (theta-chain.md Q3); all 14 `Formalism.BehrendSets.*` modules (none reachable) (frontier-d-window.md Q4).

### What it means and what it does not

It is an **over-approximation by source text**:
- a mention is not a use. A theorem named inside a hypothesis bundle counts as reachable even if its proof is never consumed;
- name ambiguity can add unused declarations: 1.1% of resolved tokens were still ambiguous after the import-closure filter;
- local variables that coincide with project names can add false edges.

It can also **miss** uses through typeclass instances (only partly modelled by rule B), notation, macros, `open … in`, `attribute [instance]`, generalized field notation (`h.foo`), and declarations whose header the line-based parser misread.

So "about 59% of declarations are reachable" is an estimate of the dependency cone, not the exact set. The exact set requires walking the compiled proof terms, which the rhcheck audit stage does from the compiled environment (rhcheck/README.md, Method step 3); its results arrived after this page was written: the exact figure is 146,440 of 175,187 project modules (83.6%), well above the static estimate, so the static tracer misses many real uses. Treat every "unreachable" flag on this page as a hint only; several were wrong (the determinant inequality and the twist chain are used), though the `mAt` one was right. "Unreachable" is the stronger signal: a module with no reachable declaration (such as the `mAt` module) is very likely not used, subject to the missed-use caveats above.

## Sources

- rhcheck/results/structure.md
- analysis/archive-stats.md
- analysis/static-reachability.md
- analysis/theta-chain.md (Q3, reachability of chain modules)
- analysis/frontier-d-window.md (Q4, Behrend)
- analysis/frontier-c-galois.md (Q1, `…Statement` wrappers)
- analysis/frontier-g-deep-inputs.md (directory sizes)
- analysis/statements-review-2-reptheory.md (homonyms)
- rhcheck/README.md, rhcheck/RUNBOOK.md (import depth, size, static scan)
