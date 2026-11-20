# Static name-level reachability from the five Main.lean theorems

**Caveat (read first).** This is an over-approximation by source text, not the exact dependency set. A mention is not a use, and name ambiguity can add unused declarations. It can also miss uses through typeclass instances (partly modelled, see below), notation, macros, `open ... in`, `attribute [instance]`, generalized field notation (`h.foo` with `h : Foo`), and declarations whose header the line-based parser misread. Local variables that coincide with project names can add false edges. The exact set will come from the compiled proof terms (separate job).

## Method actually run

- Script: `analysis/scripts/idx.py` (parse, 13 s) and `reach.py` (resolve/traverse, ~2.5 min), run as Slurm jobs on chili. Outputs on chili: `/bulk/shared/rieman/analysis/reach/`.
- Parser: comments stripped (non-nested regex), commands split at column-0 command keywords, `namespace`/`section`/`mutual`/`end` stack (incl. `noncomputable section`), `open` lists per frame, attributes and `open .. in` prefixes merged into the next declaration. Names may be dotted or `_root_.`. Anonymous instances get a synthetic name. Structure fields and inductive constructors are recorded as `S.f` and edge back to `S`; they are not counted as declarations below.
- Resolution: token T in declaration X (namespace N, opens O) resolves to full name p.T for p in {root, prefixes of N, prefixes of X's own namespace part, each open o, q.o for q a prefix of N}. For dotted tokens the longest dotted prefix that resolves is used (the rest is treated as field access). All candidates are kept, then restricted to modules in the transitive import closure of the referencing module (bitset closure from graph.json). Unresolved tokens are ignored.
- Roots: the five theorems of `Main`; their statement constants live in `Statements`.
- Rule A: no instances. Rule B (conservative instance rule): additionally, an instance (named or anonymous) whose module is in the import closure of some module that already has a reachable declaration, and whose text resolves to a reachable structure/class/inductive, is reachable (iterated to fixpoint). Rule C (extra, strict): like A but follow only tokens with exactly one candidate after the closure filter.
- Not done: nothing from the brief was dropped. Not modelled: `@[instance]` defs/abbrevs, `deriving instance`, `attribute [instance]`, notation/macro expansion.

## Headline

Totals: 175187 modules (173839 with declarations), 1041799 declarations (theorem/lemma/def/abbrev/instance/structure/class/inductive; 74087 field and 353 constructor entries not counted), 12,648,113 lines in those declarations (non-blank, comments stripped), 17,374,215 source lines overall in graph.json.

| Rule | reachable decls | % of decls | modules with >=1 reachable decl | % of modules | decl lines | % of decl lines |
|---|---|---|---|---|---|---|
| A (no instances) | 610162 | 58.6% | 118200 | 68.0% | 7,892,325 | 62.4% |
| B (with instances) | 612472 | 58.8% | 118347 | 68.1% | 7,904,770 | 62.5% |
| C (strict, unique candidate only) | 595783 | 57.2% | 116311 | 66.9% | 7,686,344 | 60.8% |

B adds only 2310 declarations over A (instances reached by the structure rule plus what they in turn mention; only 382 structures/classes are mentioned by any instance). Max reference depth from the roots: 52. Depth histogram (rule A) is bulk at depths 10-30.

### Per top-level library

| prefix | modules | decls | decl lines | A: mods / decls / lines | B: mods / decls / lines |
|---|---|---|---|---|---|
| CompanionTheory | 1945 | 11650 | 148,555 | 1833 / 9934 / 133,210 | 1833 / 9936 / 133,212 |
| Development | 140801 | 678484 | 8,733,702 | 95019 / 403705 / 5,535,946 | 95115 / 405159 / 5,542,739 |
| Formalism | 18194 | 237054 | 2,478,010 | 13097 / 136815 / 1,501,242 | 13120 / 137067 / 1,502,257 |
| GroundTheory | 8468 | 73681 | 794,728 | 4991 / 33366 / 390,696 | 5017 / 33900 / 394,968 |
| Lemmata | 167 | 243 | 7,217 | 131 / 193 / 5,859 | 131 / 193 / 5,859 |
| Main | 1 | 5 | 5 | 1 / 5 / 5 | 1 / 5 / 5 |
| PositivityTheory | 445 | 4551 | 37,085 | 173 / 1124 / 10,360 | 173 / 1127 / 10,364 |
| ReciprocityTheory | 3816 | 36123 | 448,793 | 2953 / 25012 / 314,989 | 2955 / 25077 / 315,348 |
| Statements | 1 | 4 | 11 | 1 / 4 / 11 | 1 / 4 / 11 |
| Supplements | 1 | 4 | 7 | 1 / 4 / 7 | 1 / 4 / 7 |

### Per two-component prefix (top 45 by declarations; all 337 in `reach/pre2.tsv`)

| prefix | modules | decls | decl lines | A: mods / decls / lines | B: mods / decls / lines |
|---|---|---|---|---|---|
| Development.AbelianVarietyTheory | 98471 | 447120 | 5,670,961 | 63241 / 249905 / 3,394,108 | 63323 / 251096 / 3,399,736 |
| Development.AutomorphicArithmetic | 18136 | 89158 | 1,351,483 | 13603 / 57431 / 932,712 | 13609 / 57507 / 933,216 |
| Formalism.LocalToGlobal | 5486 | 72101 | 712,753 | 4394 / 45176 / 474,361 | 4397 / 45236 / 474,581 |
| Development.AutomorphicSpectrum | 15100 | 68290 | 875,497 | 11464 / 46402 / 616,392 | 11466 / 46468 / 616,657 |
| Development.WeilBound | 6990 | 54359 | 621,609 | 5497 / 38938 / 450,057 | 5502 / 38989 / 450,235 |
| Formalism.SharpRestriction | 3074 | 53928 | 554,437 | 1986 / 25461 / 284,939 | 1999 / 25612 / 285,468 |
| GroundTheory.HeightsAndTheta | 6372 | 36770 | 434,555 | 3482 / 13871 / 193,468 | 3483 / 13901 / 193,624 |
| Formalism.HermitianCurvature | 1919 | 35669 | 363,502 | 1641 / 25344 / 262,328 | 1641 / 25345 / 262,331 |
| Formalism.PeriodIntegrals | 4339 | 32405 | 348,931 | 3063 / 21536 / 243,091 | 3065 / 21558 / 243,233 |
| ReciprocityTheory.ReductiveGroups | 2780 | 26103 | 324,143 | 2176 / 18671 / 230,572 | 2176 / 18716 / 230,835 |
| GroundTheory.AutomorphicForms | 541 | 10884 | 118,587 | 399 / 6143 / 69,770 | 399 / 6149 / 69,780 |
| Development.EtaleCohomology | 1392 | 10153 | 77,700 | 643 / 4083 / 32,118 | 643 / 4084 / 32,119 |
| Development.ResolutionOfSingularities | 499 | 8033 | 118,148 | 470 / 6361 / 103,079 | 471 / 6427 / 103,282 |
| GroundTheory.ProfiniteCohomology | 450 | 6202 | 60,000 | 392 / 4344 / 43,757 | 400 / 4571 / 44,624 |
| CompanionTheory.SpectralGeometry | 1219 | 5803 | 81,801 | 1191 / 5454 / 78,334 | 1191 / 5454 / 78,334 |
| GroundTheory.GlobalFields | 384 | 5718 | 53,081 | 299 / 3559 / 33,522 | 299 / 3569 / 33,556 |
| GroundTheory.PAdicHodge | 226 | 5339 | 49,852 | 83 / 1344 / 12,129 | 97 / 1496 / 14,768 |
| PositivityTheory.AutomorphicForms | 443 | 4546 | 36,951 | 171 / 1119 / 10,226 | 171 / 1122 / 10,230 |
| Formalism.ThetaLogCoordinates | 292 | 4162 | 43,534 | 189 / 2512 / 28,709 | 189 / 2512 / 28,709 |
| Formalism.GL3MeanSquares | 438 | 4090 | 65,694 | 302 / 1966 / 33,307 | 302 / 1966 / 33,307 |
| GroundTheory.ArithmeticGeometry | 218 | 3748 | 34,011 | 147 / 1795 / 15,792 | 147 / 1824 / 15,914 |
| Formalism.LocalRingCardinality | 173 | 3275 | 26,009 | 85 / 1108 / 8,119 | 88 / 1123 / 8,229 |
| GroundTheory.LocalFields | 159 | 3214 | 29,670 | 122 / 1763 / 16,747 | 123 / 1830 / 17,093 |
| CompanionTheory.AutomorphicTheory | 420 | 2778 | 35,946 | 388 / 2260 / 30,927 | 388 / 2262 / 30,929 |
| Formalism.PieriBlockIdeals | 98 | 2549 | 24,722 | 24 / 295 / 2,705 | 24 / 295 / 2,705 |
| Formalism.FlagUnipotentLattices | 77 | 2412 | 26,338 | 33 / 663 / 10,110 | 33 / 663 / 10,110 |
| ReciprocityTheory.AnalyticForms | 192 | 2291 | 30,589 | 142 / 1404 / 18,924 | 142 / 1405 / 18,930 |
| Formalism.SizeWindowBrackets | 64 | 2251 | 23,443 | 17 / 246 / 2,698 | 17 / 246 / 2,698 |
| ReciprocityTheory.L2DbarEstimates | 220 | 1865 | 28,318 | 167 / 1275 / 20,550 | 167 / 1275 / 20,550 |
| Formalism.WachLatticeTwists | 260 | 1573 | 31,742 | 109 / 519 / 8,984 | 109 / 519 / 8,984 |
| ReciprocityTheory.DualLattices | 183 | 1483 | 19,481 | 151 / 976 / 14,581 | 152 / 983 / 14,608 |
| Formalism.AdmissibleDesigns | 93 | 1477 | 13,711 | 91 / 1323 / 12,631 | 91 / 1324 / 12,634 |
| CompanionTheory.HarishChandraModules | 130 | 1475 | 16,747 | 111 / 1091 / 13,410 | 111 / 1091 / 13,410 |
| Development.DiscreteGroups | 213 | 1371 | 18,304 | 101 / 585 / 7,480 | 101 / 588 / 7,494 |
| Formalism.MahlerMeasure | 54 | 1301 | 13,463 | 47 / 1139 / 11,368 | 47 / 1139 / 11,368 |
| CompanionTheory.RealGroups | 155 | 1198 | 10,810 | 130 / 940 / 9,083 | 130 / 940 / 9,083 |
| Formalism.PadicSubsetSums | 82 | 1100 | 12,461 | 45 / 359 / 6,112 | 45 / 359 / 6,112 |
| Formalism.SatakeDualWeyl | 85 | 1076 | 11,991 | 80 / 903 / 10,318 | 80 / 903 / 10,318 |
| ReciprocityTheory.ClassFieldTheory | 91 | 1058 | 9,059 | 79 / 837 / 7,382 | 79 / 837 / 7,382 |
| Formalism.RealPlaceAnalysis | 54 | 1056 | 8,798 | 51 / 921 / 7,905 | 51 / 921 / 7,905 |
| Formalism.DistinguishedUnitIdeals | 44 | 1044 | 11,553 | 1 / 2 / 5 | 3 / 4 / 13 |
| Formalism.PolynomialDimension | 41 | 1044 | 13,589 | 32 / 738 / 8,967 | 32 / 738 / 8,967 |
| ReciprocityTheory.SemistableReduction | 118 | 891 | 12,446 | 102 / 689 / 10,011 | 102 / 689 / 10,011 |
| Formalism.QuotientMetricDivisors | 63 | 824 | 11,675 | 34 / 218 / 2,581 | 34 / 218 / 2,581 |
| GroundTheory.TateCohomology | 56 | 797 | 6,257 | 35 / 382 / 3,399 | 35 / 384 / 3,420 |

## Directories (three components, >=20 modules) with zero reachable declarations

3 of 158 such directories; zero under rule A and rule B alike. Together 72 modules.

| directory | modules |
|---|---|
| Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs | 26 |
| Formalism.JumpKernelCokernel.JumpShiftProofs | 23 |
| GroundTheory.AutomorphicForms.PartialDifferential | 23 |

So essentially no whole directory is unreachable at name level: the dependency cone covers 58% of declarations and 68% of modules; the unused material is spread within directories (see `reach/reachable-modules.txt`, which lists every module with reachable declarations and its counts; modules absent from it have none).

## 40 modules with the most reachable declarations (rule B)

| module | A | B | total decls |
|---|---|---|---|
| Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist | 1175 | 1175 | 1351 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant | 704 | 704 | 807 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving | 548 | 548 | 559 |
| Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals | 509 | 509 | 642 |
| Formalism.SharpRestriction.GrowthBounds.WittFrameLocaliserOrders | 409 | 409 | 433 |
| Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation | 325 | 331 | 358 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.ConnectionRaisingConstantEq | 303 | 303 | 313 |
| Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant | 292 | 292 | 461 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts | 284 | 284 | 301 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne | 281 | 281 | 283 |
| Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf | 268 | 268 | 304 |
| Formalism.SharpRestriction.GrowthBounds.LatticeSystems | 266 | 267 | 283 |
| Formalism.SharpRestriction.GrowthBounds.CountingStatementReduction | 267 | 267 | 297 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass | 250 | 250 | 256 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain | 246 | 246 | 267 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferRtt | 239 | 239 | 251 |
| Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap | 216 | 216 | 216 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseModel | 215 | 215 | 222 |
| Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin | 196 | 196 | 196 |
| Formalism.PolynomialDimension.MultinomialDepth.TieOps | 196 | 196 | 206 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian | 195 | 195 | 199 |
| Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition | 191 | 193 | 204 |
| Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor | 183 | 189 | 255 |
| Formalism.SharpRestriction.GrowthBounds.InitialMinorTransposeMemHighestWeight | 185 | 185 | 212 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv | 184 | 184 | 522 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator | 182 | 182 | 286 |
| Formalism.HermitianCurvature.StatementMA | 176 | 176 | 199 |
| Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds | 174 | 174 | 233 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds | 172 | 172 | 176 |
| Formalism.HermitianCurvature.StatementQ | 167 | 167 | 193 |
| Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant | 167 | 167 | 192 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity | 165 | 165 | 171 |
| Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth | 162 | 163 | 196 |
| Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField | 160 | 160 | 169 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting | 158 | 158 | 165 |
| Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead | 155 | 155 | 159 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent | 153 | 153 | 183 |
| Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightVariableFormula | 152 | 152 | 152 |
| Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective | 145 | 151 | 213 |
| Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure | 149 | 149 | 159 |

## Literature and published statements

- `literature.json`: 242 rows. Theorem rows reachable: 242 (A) / 242 (B). Distinct statement constants: 182, reachable 177 (A) / 177 (B). Per-row detail: `reach/lit_rows.tsv`.
- `UpperTheory.LiteratureTheorems.*`: 259 declarations (257 theorems); reachable 259 (A, B and C alike), theorems 257.
- `GlobalTheory.Published.*`: 1549 declarations (910 theorems/statement defs counted as theorems); reachable 656 (A) / 698 (B) / 647 (C); theorems reachable 284 (A) / 287 (B).
- All 242 literature theorems are reachable because the single theorem `every_character_of_literature_of_vWin` (and `published_results_arithmetic`) mentions them or their hypothesis structures; at name level a mention in a hypothesis bundle is enough, so this says that each is named in the cone, not that its proof is consumed.

## Never-used structures/classes

8265 structures/classes declared; **151** whose last name component appears in no other declaration, instance or command text anywhere in the tree (list: `reach/never-used-structures.txt`). This is a lower bound (a same-named structure elsewhere, or an extending structure, counts as use). Examples:

- `UpperTheory.V.Sd.MixedUnitPublishedTheorems` (MixedUnitPublishedTheorems:7)
- `Formalism.MainNotions.V.Pf.V3.P4.StepsA` (GradedDegreeZeroLocal:135)
- `GlobalTheory.LocWCompare.SecondOnly` (IntegralTransport:221)
- `Formalism.BasicNotions.Examples₂.NZ.GatBasis` (NZColA:9)
- `Formalism.L2.SG.Pf.ColDictPf.TrFacts` (ColDictPf:69)
- `GlobalTheory.SeeSaw.XPins` (FrameTop:203)
- `GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.Input.Weighted` (SectionInputData:132)
- `Formalism.L2.S.SiegelLatticeAgreement` (EFSymmCont:50)
- `UpperTheory.V.Ws.UIn` (IsAlgClosureField:62)
- `GroundTheory.Arith.Etale.IsAdicCompletionMap` (ArtinApproximationData:12)
- `UpperTheory.V.Sd.Hypotheses4L` (Hypotheses4L:6)
- `UpperTheory.V.Af.MinimalHyp2` (MinimalHyp2:10)
- `GroundTheory.Heights₂.Heights.LowerBoundFree.PlueckerData.DetWFrameAt` (HasCoverByOne:133)
- `GroundTheory.ProfCoh.PoitouTateHypotheses` (Abstract:78)
- `Formalism.L2.DIV.IsTupleMapTW` (Tuples:208)
- `GlobalTheory.TrivDescentCompare.TrivializationThickPoints` (LiftConnectedOfTrivialUnique:390)
- `Formalism.MainNotions.V.Lang.PsR.DetMon` (ScaleEps:29)
- `Formalism.HC.PreHostAn` (Analytic:170)
- `Formalism.L2.Col.SizeIn` (SummandSlopeAtDecoratedLattice:384)
- `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.IsVerticalCartier` (IsVerticalCartier:128)
- `GroundTheory.Heights₂.Heights.NormedBundle.` (ReducedTensors:31)
- `GlobalTheory.TrivDescentCompare.TrivializationClauses` (LiftConnectedOfTrivialUnique:593)
- `GlobalTheory.CovTop.Idle` (NefProd:82)
- `HostParam.HostFamily` (ExceptionalCharacterCondition:71)
- `Formalism.L2.G.RelativeIndexFlags.ChosenDataCompatibility` (IntegralWeylLatticeSpan:38)
- `Formalism.MainNotions.Gaps.LG.Par.AllOK` (LevGap:245)
- `Formalism.L2.G.LeftD` (TieFin:41)
- `Formalism.IndefR.CoreT.OMIn` (CoreTExist:725)
- `GlobalTheory.WeilTieCompare.Beyond` (OffCharsSeparates:413)
- `ReciprocityTheory.ChartRestriction.G.PullbackSections.VtFr` (VtfValPullGen:132)

Of the three known names, `GeneralHyps` and `GeneralHypV` are in the list; `GeneralHypU` is not because `GeneralHypV extends GeneralHypU` mentions it (so it is a dead pair in practice).

## Sanity checks

(a) Required declarations in the reachable set:

- `UpperTheory.FinalTheorems.everyCharacter`: declared 1, reachable A=True B=True C=True
- `Formalism.VW.rh_of_every`: declared 1, reachable A=True B=True C=True
- `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`: declared 1, reachable A=True B=True C=True
- `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin`: declared 1, reachable A=True B=True C=True

(b) After pre-filtering to tokens containing a component that is the last component of some project name, the traversal examined 17948517 tokens in 612472 reachable/instance declarations; 3325907 resolved to a project declaration; 36475 (1.1%) of the resolved tokens were ambiguous after the import-closure filter (222189, 6.7%, before the filter). Parser: 1,175,438 command segments, 0 declarations without a parseable name, 59 `end X` mismatches (only in files holding 563 segments, i.e. 0.05% of segments); declarations are all attributed to a namespace by the stack (no namespace is dropped), and unclosed trailing sections/namespaces at end of file are accepted as Lean allows.

(c) Reference chains (rule A, shortest-path tree from the roots) to five reachable declarations at depth quantiles 10/30/50/70/90%:

1. depth 5:
   - `LFunction_ne_zero_of_half_lt_re` (theorem, Main:8)
   - `allChi` (theorem, MainTheorems:7)
   - `UpperTheory.FinalTheorems.everyCharacter` (theorem, MainConclusion:10)
   - `UpperTheory.FinalTheorems.everyCharacter_of_row` (theorem, MainConclusion:7)
   - `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (theorem, EveryCharacterOfLiteratureOfVWin:810)
   - `UpperTheory.LiteratureTheorems.published_results_arithmetic` (theorem, EveryCharacterOfLiteratureOfVWin:781)
2. depth 15:
   - `LFunction_ne_zero_of_half_lt_re` (theorem, Main:8)
   - `allChi` (theorem, MainTheorems:7)
   - `UpperTheory.FinalTheorems.everyCharacter` (theorem, MainConclusion:10)
   - `UpperTheory.FinalTheorems.everyCharacter_of_row` (theorem, MainConclusion:7)
   - `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (theorem, EveryCharacterOfLiteratureOfVWin:810)
   - `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (theorem, SiegelEisensteinSecondTermHypotheses:69)
   - `UpperTheory.Top.every_character_of_green_v_win` (theorem, TopPlug:16)
   - `UpperTheory.Top.zero_free_all_of_green_v_win` (theorem, TopPlug:12)
   - `UpperTheory.Top.shape_closed_link_n_of_green` (theorem, TopShape:33)
   - `GlobalTheory.Top.closed_linkG_of_duty` (theorem, LinkG:13)
   - `Formalism.L2.G.linkG_concrete5` (theorem, LinkGConcreteNoKer:54)
   - `Formalism.L2.G.linkG_concrete_noKer` (theorem, LinkGConcreteNoKer:48)
   - `Formalism.L2.G.link_of_local_closed` (theorem, AdmissibleFamilyNoKernel:272)
   - `Formalism.L2.G.local_model_results` (theorem, AdmissibleFamilyNoKernel:43)
   - `Formalism.L2.G.Model.products_sections_integral` (theorem, MulMemRiemannRochSpaceAdd:97)
   - `Formalism.L2.G.Model.lamAt_add` (theorem, MulMemRiemannRochSpaceAdd:76)
3. depth 26:
   - `LFunction_ne_zero_of_half_lt_re` (theorem, Main:8)
   - `allChi` (theorem, MainTheorems:7)
   - `UpperTheory.FinalTheorems.everyCharacter` (theorem, MainConclusion:10)
   - `UpperTheory.FinalTheorems.everyCharacter_of_row` (theorem, MainConclusion:7)
   - `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (theorem, EveryCharacterOfLiteratureOfVWin:810)
   - `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (theorem, SiegelEisensteinSecondTermHypotheses:69)
   - `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` (theorem, SiegelEisensteinSecondTermHypotheses:44)
   - `GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt` (theorem, HypothesesNonemptyOfUnramifiedExponents:41)
   - `GlobalTheory.T.large_unramified_exponent_bundles_exist_alt` (theorem, MemberBundlesLargeUnramifiedExponents:69)
   - `GlobalTheory.Fc.StageOneU.member_bundles_large_unramified_exponents_alt` (theorem, MemberBundlesLargeUnramifiedExponents:34)
   - `GlobalTheory.T.member_exists_baseLattice_alt` (theorem, ExistsBaseLatticeOfPrime:80)
   - `GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt` (theorem, ExistsBaseLatticeOfPrime:57)
   - `GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_pair_alt` (theorem, ExistsBaseLatticeOfPrime:36)
   - `GlobalTheory.Mem.Top.Closing.memberE_closing_alt_alt` (theorem, MemberEClosing:17)
   - `GlobalTheory.T.exists_member_of_construction_steps_secondPass` (theorem, ExistsMemberOfConstructionStepsSecondPassStatement:12)
   - `GlobalTheory.Mem.Top.Bl.memberE_of_steps2` (theorem, ExistsMemberOfConstructionStepsSecondPass:38)
   - `GlobalTheory.T.exists_constructedCore_of_all_construction_stages` (theorem, ExistsConstructedCoreOfAllConstructionStagesStatement:12)
   - `GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core` (theorem, ExistsConstructedCoreOfAllConstructionStages:67)
   - `GlobalTheory.T.exists_latticeLayer_kernelDatum_trueColumns` (theorem, ExistsLatticeLayerKernelDatumTrueColumnsStatement:12)
   - `GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC` (theorem, ExistsLatticeLayerKernelDatumTrueColumns:21)
   - `GlobalTheory.T.levels_kernelData_at_served_place` (theorem, LevelsKernelDataAtServedPlaceStatement:11)
   - `GlobalTheory.Mem.Top.KerOne.kerData_at_served` (theorem, LevelsKernelDataAtServedPlace:18)
   - `GlobalTheory.T.served_place_levels_classes_comparison_maps` (theorem, ServedPlaceLevelsClassesComparisonMapsStatement:13)
   - `GlobalTheory.Mem.Top.KerOne.levels_cls_cmp_at_served` (theorem, ServedPlaceLevelsClassesComparisonMaps:15)
   - `GlobalTheory.T.comparison_data_steps_non_reference_tuple` (theorem, ComparisonDataStepsNonReferenceTupleStatement:12)
   - `GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne` (theorem, ComparisonDataStepsNonReferenceTuple:74)
   - `GlobalTheory.T.served_place_no_chain_place_or_type_prime_over` (theorem, ServedPlaceNoChainPlaceOrTypePrimeOverStatement:16)
4. depth 37:
   - `LFunction_ne_zero_of_half_lt_re` (theorem, Main:8)
   - `allChi` (theorem, MainTheorems:7)
   - `UpperTheory.FinalTheorems.everyCharacter` (theorem, MainConclusion:10)
   - `UpperTheory.FinalTheorems.everyCharacter_of_row` (theorem, MainConclusion:7)
   - `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (theorem, EveryCharacterOfLiteratureOfVWin:810)
   - `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (theorem, SiegelEisensteinSecondTermHypotheses:69)
   - `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` (theorem, SiegelEisensteinSecondTermHypotheses:44)
   - `GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt` (theorem, HypothesesNonemptyOfUnramifiedExponents:41)
   - `GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0_alt` (theorem, LinkROfIsLinked:50)
   - `GlobalTheory.T.hServ_of_linkR` (theorem, RowHServOfLinkStatement:14)
   - `GlobalTheory.row_hServ_of_link_alt` (theorem, RowHServOfLink:17)
   - `GlobalTheory.T.reciprocity_kernel_of_artin` (theorem, ServHRowLinkRStatement:14)
   - `GlobalTheory.Svd.servH_row_linkR_alt` (theorem, ServHRowLinkR:14)
   - `GlobalTheory.T.bundle_bothParts_of_standardKernel_of_globalArtinReciprocity` (theorem, BundleBothPartsOfStandardKernelOfGlobalArtinReciStatement:7)
   - `GlobalTheory.Svd.servH_row_of_artin` (theorem, BundleBothPartsOfStandardKernelOfGlobalArtinReci:15)
   - `GlobalTheory.T.bundle_bothParts_of_standardKernel_and_six_hypotheses` (theorem, BundleBothPartsOfStandardKernelAndSixHypothesesStatement:11)
   - `GlobalTheory.Svd.servH_row` (theorem, BundleBothPartsOfStandardKernelAndSixHypotheses:15)
   - `GlobalTheory.T.tuplesHaveLocalModels_at_constructedPoint_over_trueColumns` (theorem, TuplesHaveLocalModelsAtConstructedPointOverTrueCStatement:7)
   - `GlobalTheory.Svd.modelsAt_bpt` (theorem, TuplesHaveLocalModelsAtConstructedPointOverTrueC:10)
   - `GlobalTheory.T.tuplesHaveLocalModels_of_standardColumnObjects` (theorem, TuplesHaveLocalModelsOfStandardColumnObjectsStatement:7)
   - `GlobalTheory.Svd.modelsAt_of_part` (theorem, TuplesHaveLocalModelsOfStandardColumnObjects:11)
   - `GlobalTheory.T.thetaLocalModels_of_splitUnramified_joints` (theorem, ThetaLocalModelsOfSplitUnramifiedJointsStatement:8)
   - `GlobalTheory.TwV.modelsOK_of_joints` (theorem, ThetaLocalModelsOfSplitUnramifiedJoints:11)
   - `GlobalTheory.T.jointSite_chain_compared_carries_admittedSystem` (theorem, JointSiteChainComparedCarriesAdmittedSystemStatement:8)
   - `GlobalTheory.TwV.site_cmpLite_siteAdm` (theorem, JointSiteChainComparedCarriesAdmittedSystem:77)
   - `GlobalTheory.TwV.admissible_at_each_site` (theorem, JointSiteChainComparedCarriesAdmittedSystem:29)
   - `GlobalTheory.T.kernelSite_arithmeticGroup_moves_frames` (theorem, KernelSiteArithmeticGroupMovesFramesStatement:8)
   - `GlobalTheory.TwV.move_at_site` (theorem, KernelSiteArithmeticGroupMovesFrames:13)
   - `GlobalTheory.T.kernelSite_arithmeticGroup_move` (theorem, KernelSiteArithmeticGroupMoveStatement:7)
   - `GlobalTheory.TwV.Xc.site_move` (theorem, KernelSiteArithmeticGroupMove:18)
   - `GlobalTheory.T.kernelSite_move_latticeTuple_at_succStep` (theorem, KernelSiteMoveLatticeTupleAtSuccStepStatement:7)
   - `GlobalTheory.TwV.Xc.moveBy_succ` (theorem, KernelSiteMoveLatticeTupleAtSuccStep:50)
   - `GlobalTheory.TwV.Xc.Mv0.frm_gen` (theorem, StepZeroLatticeTupleMoveByRationalIsometry:13)
   - `Formalism.L2.G.stdG` (theorem, FillInstRecEqWj:166)
   - `Formalism.L2.G.fillsG` (def, FillInstRecEqWj:94)
   - `Formalism.L2.G.cloudBound` (theorem, WLeWjOne:130)
   - `Formalism.L2.G.w''_le_wj_one` (theorem, WLeWjOne:116)
   - `Formalism.MainNotions.Inhab.scale_b'_nonneg` (theorem, VVEqEmptyOfNotIsResidueClassZero:169)
5. depth 47:
   - `LFunction_ne_zero_of_half_lt_re` (theorem, Main:8)
   - `allChi` (theorem, MainTheorems:7)
   - `UpperTheory.FinalTheorems.everyCharacter` (theorem, MainConclusion:10)
   - `UpperTheory.FinalTheorems.everyCharacter_of_row` (theorem, MainConclusion:7)
   - `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (theorem, EveryCharacterOfLiteratureOfVWin:810)
   - `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (theorem, SiegelEisensteinSecondTermHypotheses:69)
   - `UpperTheory.Top.every_character_of_green_v_win` (theorem, TopPlug:16)
   - `UpperTheory.Top.zero_free_all_of_green_v_win` (theorem, TopPlug:12)
   - `UpperTheory.Top.shape_closed_link_n_of_green` (theorem, TopShape:33)
   - `GlobalTheory.Top.closed_linkG_of_duty` (theorem, LinkG:13)
   - `Formalism.L2.G.linkG_concrete5` (theorem, LinkGConcreteNoKer:54)
   - `Formalism.L2.G.linkG_concrete_noKer` (theorem, LinkGConcreteNoKer:48)
   - `Formalism.L2.G.link_of_local_closed` (theorem, AdmissibleFamilyNoKernel:272)
   - `Formalism.L2.G.local_flatness_results` (theorem, AdmissibleFamilyNoKernel:62)
   - `Formalism.MainNotions.G.GramWindowAlt.theorem_A_closed_form_holds` (theorem, FockGramWindow:24)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_minimal_vector` (theorem, ClosedOfMinimalVector:8)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_splitting_matrix` (theorem, ClosedOfSplittingMatrix:8)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_orthogonal_splitting` (theorem, ClosedOfOrthogonalSplitting:8)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.integralityFromMetric_of_orthBasisLat` (theorem, IntegralityFromMetricOfOrthBasisLat:29)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_orthogonal_basis` (theorem, ClosedOfOrthogonalBasis:8)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_orthogonal_lattice` (theorem, ClosedOfOrthogonalLattice:8)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_symmetric_dims` (theorem, SymmetryWindowOnAdmissible:22)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_symmetric_windows` (theorem, SymmetryWindowLevelDimOnAdmissible:23)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_coefficient_function` (theorem, ClosedOfCoefficientFunction:8)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_symmetric_finite` (theorem, SymmetryFinitenessWindowLevelDimOnAdmissible:29)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.integrality_from_metric_of_orthogonality_window` (theorem, IntegralityFromMetricOfOrthogonalityWindow:23)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.theorem_A_closed_of_nine_open_bounds` (theorem, RestrictedBoundsWeakenFromNineToEight:23)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.theorem_A_closed_of_eight_open_bounds` (theorem, RestrictedBoundsWeakenFromEightToSeven:23)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_open_base_dims` (theorem, RestrictedBoundsWeakenFromSevenToSix:24)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_open_dimensions` (theorem, PositiveOfDimensionChange:23)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_open_positive` (theorem, DirectionsOfPositivePart:23)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.closed_of_open_directions` (theorem, ThresholdsMonoNormalized:50)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.openE_of_open4` (theorem, ThresholdsMonoNormalized:40)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.restTM_closed` (theorem, EpsilonBoundMConstant:228)
   - `Formalism.MainNotions.G.SymmetricFormBlocks.restTM_exists` (theorem, RestTMExists:14)
   - `Formalism.MainNotions.G.CountingStatementReduction.alternative_mean_value_theorem` (theorem, CountingStatementReduction:19)
   - `Formalism.InvariantFactorPaths.MC.Top.theoremMV7` (theorem, LatticeTheoremEps28Valid:7)
   - `Formalism.InvariantFactorPaths.MC.theoremMV7` (theorem, GramHypothesisOfLogBound:188)
   - `Formalism.InvariantFactorPaths.MC.gram_hypothesis_of_log_bound` (theorem, GramHypothesisOfLogBound:83)
   - `Formalism.InvariantFactorPaths.L4.graded_bound_pos_of_proj` (theorem, GramBoundPosOfProjSat:51)
   - `Formalism.InvariantFactorPaths.L4.projAt2_of` (theorem, GramBoundPosOfProjSat:9)
   - `Formalism.InvariantFactorPaths.L4.grSpan_eq` (theorem, GramBoundOfRestrictionOfProj:200)
   - `Formalism.InvariantFactorPaths.L4.restriction_min_max_holds` (theorem, RestrictionMinMaxIntHolds:523)
   - `Formalism.InvariantFactorPaths.L4.restriction_into_holds` (theorem, ResInto:430)
   - `Formalism.InvariantFactorPaths.L4.condition_drop_holds` (theorem, ResInto:426)
   - `Formalism.InvariantFactorPaths.L4.mem_cond_of_euler_eigen` (theorem, ResInto:393)
   - `Formalism.InvariantFactorPaths.L4.mulX_ycond` (theorem, ResInto:362)
   - `Formalism.InvariantFactorPaths.L4.X_last_mul_mem_restrictSupport_wt_le` (theorem, ResInto:343)
