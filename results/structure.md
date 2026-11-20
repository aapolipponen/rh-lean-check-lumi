# Structure of the archive (static, from the import graph)

175,187 modules, 17,374,215 lines, 753,569 project import edges. 136,003 modules import all of Mathlib directly.

| Library | modules | lines | mean lines/module | median imports closure |
|---|---:|---:|---:|---:|
| `Development` | 141,928 | 12,232,663 | 86 | 1,129 |
| `Formalism` | 18,254 | 3,200,748 | 175 | 229 |
| `GroundTheory` | 8,507 | 1,119,138 | 131 | 19 |
| `ReciprocityTheory` | 3,845 | 563,016 | 146 | 24 |
| `CompanionTheory` | 2,027 | 194,218 | 95 | 399 |
| `PositivityTheory` | 449 | 55,130 | 122 | 21,541 |
| `Lemmata` | 167 | 9,232 | 55 | 1 |
| `BuildAid` | 5 | 20 | 4 | 1 |
| `Supplements` | 3 | 22 | 7 | 175,183 |
| `Statements` | 1 | 16 | 16 | 1 |
| `Main` | 1 | 12 | 12 | 175,187 |

**Import-only modules** (nothing but import lines): 987. They act as aggregators. The largest fan-ins:
- `ReciprocityTheory.GroupCohomology.ImportsAlt`: 13 imports
- `ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Imports`: 13 imports
- `CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SocleOfMultiplicityOne`: 11 imports
- `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AttachedRepsAgreeOnIntersection`: 10 imports
- `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AttachedRepConjugationTrace`: 9 imports
- `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsomorphismOfFrobeniusTraces`: 9 imports
- `ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsAlt`: 9 imports
- `ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports`: 9 imports

**Import closure sizes** (how many project modules a module transitively imports):
- 50th percentile: 721
- 90th percentile: 9,284
- 99th percentile: 24,339
- 99.9th percentile: 34,817
- modules above 12,000 (cannot load on a stock `vm.max_map_count`): 8,974
- modules above 60,000: 17

**The top of the tree** (largest closures):
- `Main`: 175,187 modules beneath it, 2 direct imports, 12 lines
- `Supplements.Kernels.MainTheoremsAll`: 175,185 modules beneath it, 2 direct imports, 2 lines
- `Supplements.Kernels.MainTheoremsCritical`: 175,183 modules beneath it, 4 direct imports, 4 lines
- `Supplements.Kernels.MainTheorems`: 175,179 modules beneath it, 3 direct imports, 16 lines
- `Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion`: 175,174 modules beneath it, 5 direct imports, 14 lines
- `Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf`: 170,702 modules beneath it, 4 direct imports, 29 lines
- `Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow`: 157,604 modules beneath it, 2 direct imports, 5 lines
- `Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TopMainZj`: 157,603 modules beneath it, 11 direct imports, 75 lines
- `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin`: 151,286 modules beneath it, 201 direct imports, 814 lines
- `Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TemperedProductOfSquareIntegrable`: 146,663 modules beneath it, 192 direct imports, 344 lines
- `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SiegelEisensteinSecondTermHypotheses`: 112,385 modules beneath it, 34 direct imports, 76 lines
- `Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter`: 102,080 modules beneath it, 208 direct imports, 231 lines
- `Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.EveryCharacterE`: 100,723 modules beneath it, 33 direct imports, 88 lines
- `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypothesesNonemptyOfUnramifiedExponents`: 79,669 modules beneath it, 32 direct imports, 64 lines

**Modules nothing else imports** (besides `Main`): 1.
**Most-imported modules:** `CTSmallCone` (3,088), `SiegelWeilAnisotropicHermitian` (2,972), `DiscreteSeriesHermitianUnique` (2,518), `ExistsNormLeHeightPow` (2,460), `UniformisationConclusion` (2,390), `UnifUniqSt` (2,284)
