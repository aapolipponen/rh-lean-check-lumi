# 2. Proof map

This page lays out the whole argument top down as the reports currently understand it, one row per step, each with its declarations, file, a plain statement, the nearest classical analogue and a status marker. It is a map of what the AI reviewers have read, not a check of the mathematics; the strand pages 03 to 06 give the detail and the quoted statements.

Status markers (fixed set): **[statement read]** the Lean statement was read; **[proof outline read]** the proof term or its `have`/`obtain` skeleton was read; **[proof read in full]**; **[inferred from names]** declaration names, imports or statement shape only; **[unread]**. A step's marker is the strongest that the cited report gives for that step's main declaration; sub-steps may be weaker, and page [10](10-open-frontier.md) lists them.

File paths are abbreviated to their last components; the strand pages give fuller paths. `AV/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/`, `GR/` = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/`; most other short paths are under `Development/AutomorphicArithmetic/` or `Formalism/`.

## Terms

A *Dirichlet character* χ mod N gives an L-function L(s, χ). *Zero-free for Re s > θ* means L(s, χ) ≠ 0 there. Ш¹ is a Tate–Shafarevich-type group: global Galois cohomology classes that are locally trivial at a set of places. A *window* is an interval [Y, Y^{la}] with la > 1 and Y arbitrarily large. Other terms are defined on the strand pages and in the [glossary](glossary.md).

## The map

```
 RiemannHypothesis, four Dirichlet GRH statements            Main.lean                      [01]
          ▲  functional equation, primitive characters (short)
 UpperTheory.EveryCharacter   L(s,χ) ≠ 0 for Re s > 1/2
          ▲  imprimitive
 ZeroFreeAll  ◄── FormB: localized Landau theorem on windows                                 [03]
          ▲
 Gm(x) ≤ x^{1/2+9ε} on windows [Z, Z^{3/2}]     core_gm                                     [04]
     ▲                         ▲
 EAtH (good twists)        CoreAtH / ChainTied: m ≈ √x lifts, slope inequality, DIV
     ▲                         ▲            ▲
 PairEx: good prime     LinkG, LinkS,    LinkN: congruence module of each lift
 pairs (q, d)           divisor ineq.          ≤ Selmer + v(h_E) + Σ_e len Ш¹(ℚ_ℓ/ℤ_ℓ(−e))   [04]
 zero density +                                     ▲
 mean square  [03]                     VWin: Σ_ℓ log ℓ Σ_{e<x^401} len Ш¹ ≤ exp(x^ε/2)       [06]
                                            ▲
                     minus part: Euler systems │ plus part: U(3)/GSp4 congruences, modularity
                     ℓ = 2, bad ℓ: Iwasawa μ = 0, pigeonhole, LemmaK
                                            ▲
 Row0b: Galois representations for RACSDC π on CM fields; IsRecT: partial local Langlands  [05]
     ▲  Kuga–Sato cohomology of a Harris–Taylor-type PEL variety (seeds)
     ▲  ℓ-adic congruences + pseudo-characters (all odd rank)
     ▲  two theta lifts + subtraction (even rank)
```

## Step 0. The final reduction

| Step | Declarations | File | Plain statement | Classical analogue | Status |
|---|---|---|---|---|---|
| 0.1 | `Main.riemannHypothesis := rhOfAll`, `Formalism.VW.rh_of_every allChi` | `Main.lean`; `Formalism/GammaFactorNonvanishing/CritLine.lean` | RH follows from `EveryCharacter` with N = 1 | functional equation of ξ(s) | [proof outline read] (skeleton.md §1) |
| 0.2 | `critLine`, `Claim.strip` | same area | Dirichlet GRH statements follow from `EveryCharacter` | functional equation of Λ(s, χ); primitive characters | [proof outline read] (skeleton.md §1) |
| 0.3 | `UpperTheory.FinalTheorems.everyCharacter := everyCharacter_of_row galoisLocalGlobalStrong_recParameter` | `…/CharacterBoxes/MainConclusion.lean` | `EveryCharacter` from the three inputs | none | [proof outline read] (skeleton.md §2) |
| 0.4 | `every_character_of_literature_of_vWin` | `…/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810` | proves all literature bundles and passes them with `VWin` to the analytic endgame | none | [proof outline read] (vacuity-check.md Q1; skeleton.md §3) |

## Step 1. The three inputs

| Step | Declarations | File | Plain statement | Classical analogue | Status |
|---|---|---|---|---|---|
| 1.1 | `Row0b recT`, `PropsB`, `AwayB`, `AboveB` | `…/GaloisRepresentations/TypeConditions/WeightsConjBis.lean` | Galois representations for regular algebraic polarized cuspidal π on GL_a over CM fields, with weak local–global compatibility | Harris–Taylor, Shin, Chenevier–Harris, Caraiani (stronger) | [statement read] (statements-review.md row 20) |
| 1.2 | `IsRecT`, `RecTExists` | `…/Foundations/LocalLanglands/IsRecTOfIsRec.lean` | a local Langlands map pinned down only on "Good" representations | local Langlands for GL_n (much stronger) | [statement read] (statements-review.md row 21) |
| 1.3 | `VWin := ∀ ψ, VWinAt ψ 401`, `VVle`, `WinPair` | `…/CharacterBoxes/ExistsPageN.lean` | log-weighted sum over ℓ and over twists e' < x^{401} of lengths of Ш¹(G_{E,S}, ℚ_ℓ/ℤ_ℓ(−e')) for a family of abelian CM fields is ≤ exp(x^ε/2) | none published; reviewer's impression: "Bernoulli-number size" bound | [statement read] (statements-review.md row 19) |
| 1.4 | `QH.pairEx`, `ldataExists`, `exists_locPrime_tied`, `exists_locBridge` (non-vacuity) | `MeanSquareBounds/pairEx.lean:112`; `…/GaloisCohomologyProofs/LdataNonempty.lean:48`; `…/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281`, `FiniteDimensionalAdjoinRange.lean:303` | `WinPair`s exist (`QH.pairEx`); `LData`, `LocTied`, `LocBridge` are inhabited | none | [statement read] (vacuity-check.md Q1–Q3) |

## Step 2. The analytic endgame (page [03](03-analytic-endgame.md))

| Step | Declarations | File | Plain statement | Classical analogue | Status |
|---|---|---|---|---|---|
| 2.1 | `QH.pairEx : PairEx`, `PairGood` | `MeanSquareBounds/pairEx.lean:112`; `CharacterBoxes/PairGood.lean` | for every large Y there are primes q ≡ 3 mod 8, d ≡ 7 mod 16 such that all quadratic twists by (·/q), (·/d) have zero-free boxes of width 1/400 and square-root bounds on G_χ(y) for y ∈ [Y, Y^A] | zero-density estimates and mean values over families | [proof outline read] (analytic-core.md Q2) |
| 2.2 | `QH.stage` | `MeanSquareBounds/StagePow.lean:41` | in a progression of primes, all but a share η are good | Montgomery zero detection, large sieve, Markov | [proof read in full] (analytic-core.md Q2) |
| 2.3 | `zero_density_box`, `meanSqK`, `twistK`, `kappa4`, `tailK` | `Formalism/GL3MeanSquares/…`, `MeanSquareBounds/…` | zero density at σ = 1 − 1/400; mean square over q; PNT in progressions with Siegel | Montgomery; Page; Siegel | [statement read]; several proofs [proof outline read] (analytic-core.md Q2) |
| 2.4 | `winPairs`, `WinDatum` | `CharacterBoxes/WinPairs.lean:5` | for x in windows [Z, Z^{3/2}] there are a good pair and host fields on which the Ш bound holds; 401 = 400 + 1 arises here | none | [proof read in full] (analytic-core.md Q3) |
| 2.5 | `supplyOfAdmOf`, `supplyChi`, `HostExW (3/2)`, `EAtH` | `ShortNorms/supplyOfAdmOf.lean`; `CharacterBoxes/SupplyChi.lean` | packages good pairs and the Ш bound as host data | none | [statement read]; `supplyOfAdm` [unread] (analytic-core.md Q3) |
| 2.6 | `core_gm` (see step 3) | `PrimitiveCosets/CoreGm.lean:12` | Gm(x) ≤ x^{1/2+9ε} on windows | Chebyshev-type upper bound | [proof read in full] (core-gm.md Q1) |
| 2.7 | `formB`, `FormBAt`, `landau_window` | `PrimitiveCosets/Imports.lean:8`; `DedekindLFunctions/LandauTheorems/landauWindow.lean:83` | a one-sided bound Gm ≤ x^θ on windows implies zero-freeness for Re s > θ | Landau / Pólya Ω± method | [proof outline read] (analytic-core.md Q3) |
| 2.8 | `zeroFreeAll_of_topG`, `zeroFreeOn_of_tiedWin_cyc` | `CharacterBoxes/ZeroFreeAllOfTopG.lean:26`; `…/TotientGaloisClasses/TopWin.lean:90` | direct limit ε → 0; no induction on the zero-free width | none | [proof outline read] (analytic-core.md Q3) |

> **Correction carried on this page.** The auxiliary-prime existence proof (`pair_share`) was first flagged as a place where RH-strength content could hide (vacuity-check.md). analytic-core.md found it classical: zero density plus mean square. The weight is in `core_gm` / `CoreAtH` and what feeds them (steps 3 and 4).

## Step 3. The chain of m ≈ √x lifts and the exponent 1/2 (page [04](04-chain-and-one-half.md))

| Step | Declarations | File | Plain statement | Classical analogue | Status |
|---|---|---|---|---|---|
| 3.1 | `core_gm`, `ch_core`, `ch_top` | `PrimitiveCosets/CoreGm.lean:12`; `DedekindLFunctions/LandauTheorems/ChCore.lean:343`, `ChTop.lean` | finite Fourier analysis on the host's Galois group plus a size lemma turns per-unit bounds into Gm ≤ x^{1/2+O(ε)} | none | [proof read in full] (core-gm.md Q2) |
| 3.2 | `CoreAtH`, `RestSize`, `SizeData₂` | `PrimitiveCosets/CoreAtH.lean`; `Formalism/SizeWindowBrackets/SChain.lean` | hypothesis bundle: m lifts with x^{1/2−ε} ≤ m, eleven inequalities about slopes, heights, gains | none | [statement read] (core-gm.md Q1) |
| 3.3 | `each_unit_bound_statement` | `Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175` | ASK(u) ≤ Main(u) + Err(u): a Legendre-shaped prime sum bounded by m copies of a Stirling term | Chebyshev's log(a!) method | [proof outline read] (core-gm.md Q2) |
| 3.4 | `proposition_size_bound` | `…/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507` | error per unit ≈ x/m + m, balanced at m ≈ √x, gives exponent 1/2 | none | [proof outline read] (core-gm.md Q3) |
| 3.5 | `divisor_inequality_explicit : DivIneqRecord` | `Formalism/QuotientMetricDivisors/…/GlobalBoundRefinements.lean:91` | real-variable lemma; m copies of a log a − a from summing per-lift height bounds | none | [proof read in full] (frontier-a-divisor.md Q1) |
| 3.6 | `DivClauses`, `divClauses_of`, `height_chain` | `Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:553,752,641` | integrality of a chain map twisted by a divisor of gains, archimedean height of a composite of m steps | Bost's slope method | [proof read in full] for `divClauses_of` (frontier-a-divisor.md Q2) |
| 3.7 | `Formalism.HN.SlopeIneq` | `Formalism/HarderNarasimhan/Statement.lean:91` | slope inequality for Hermitian lattices | Bost's slope inequality | [statement read] (frontier-a-divisor.md Q1c) |
| 3.8 | `WeilJacquetShalikaLaw.Conclusion1`, `Proof.stmt_proved`, `FormalGroupSystem.Pf.stmt_proved` | `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:101`; `…/AdmissibleIntegers.lean:15` | the chain's columns are divisible at inert p to order Σ_j gain_j(p); proved by a p-adic analysis of theta kernels on the height-2 Lubin–Tate formal group at supersingular CM points | Dwork, Katz; Legendre's formula; vanishing order of an auxiliary section | [proof outline read]; global-to-local kernel bridge [unread] (frontier-f-divisibility.md Tasks 1–3) |
| 3.9 | `LinkS`, `link_alt_alt_bis`, `TheoremSSelected` | `Formalism/SharpRestriction/GlobalTheoremInputs.lean:145`; `ThirdPlaceSeries/LinkAltAltBis.lean:16`; `…/FlagStabilizerTensors/ThmSOwn.lean:669` | near-orthogonality of period vectors across words u, defects ≤ exp(−x^{ε/8}) | Poincaré-series and mass-formula estimates | [statement read]; provider [proof outline read], content [inferred from names] (frontier-a-divisor.md Q4; frontier-f-divisibility.md Task 4) |
| 3.10 | `LinkG`, `LossBounds` | `GlobalTheoremInputs.lean`; `LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean:86` | ASK ≤ Ga + lower-order loss | none | [statement read]; partly [proof outline read] (frontier-b-links.md Q3) |
| 3.11 | `mAt := evenCeil (sqrt (x·x^{−ε/8}))` | `Definitions/AutomorphicMembership/EvenCeil.lean` | the chain length m ≈ x^{1/2−ε/16} | none | [statement read]; whether it is on the compiled path is open (theta-chain.md Q3) |

## Step 4. The Ribet-style link from congruence modules to Ш (page [04](04-chain-and-one-half.md))

| Step | Declarations | File | Plain statement | Classical analogue | Status |
|---|---|---|---|---|---|
| 4.1 | `HypV`, `divinN_of_hypV`, `LinkN`, `DIVinN` | `CharacterBoxes/DivinNOfHypV.lean:117`; `GlobalTheoremInputs.lean` | each lift's excess local divisibility etaSum is ≤ Ш¹ lengths + O(f·m·b·L²); `VWin` supplies the Ш term with room to spare | none | [proof read in full] (frontier-b-links.md Q1) |
| 4.2 | `etaJ`, `etaLoc`, `vcc`, `TwistedPlaces.adm1` | `Divisibility/LiftLat.lean:116-147`; `LevelLetterCocycles/DataN.lean:219`; `ResidueCharacters/TwistedPlaces.lean:133` | etaJ is the length of a congruence module, bounded by Σ multiplicity × congruence number | Ribet, Hida congruence modules | [statement read] (frontier-b-links.md Q1) |
| 4.3 | `GlobalTheory.CutCoreUnit.main` | `Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:44` | congruence number ≤ Selmer length + Σ_e len Ш¹(ℚ_ℓ/ℤ_ℓ(−e)) + v_ℓ(h_E) + tame terms, block by block in r_π = ρ ⊕ χ ⊕ χε^{−1} ⊕ … | Mazur–Wiles, Urban, Bellaïche–Chenevier | [proof read in full] (frontier-b-links.md Q2; frontier-e-ribet.md §7) |
| 4.4a | `length_heckeValueIdeal_le_determinant_bound` (= `CutDetOrd.main`), `Cut.ShaBound.main` | `Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean`; `…/LengthCyclotomicBlockCocyclesLeSha.lean:372` | congruence ideal ⊆ Fitting ideal of off-diagonal extension data (generalized matrix algebra); locally trivial classes lie in Ш¹ | Fitting-ideal / GMA method (not Ribet's lattice construction) | [proof read in full] (frontier-e-ribet.md §1, §3) |
| 4.4b | `KillAt`, `TwistingCharacterExistence` | `…/CommutingEndomorphismCondition.lean:45`; `IntegralHeckeForms.lean:166` | the ρ-block Selmer length is made nearly trivial by choosing auxiliary anticyclotomic twists | Ramakrishna / Kolyvagin auxiliary primes; near Bloch–Kato plus mod-ℓ nonvanishing of twisted L-values | [statement read]; chain [proof outline read]; decisive sub-lemmas [unread] (frontier-e-ribet.md Q3, Q4) |
| 4.5 | `NLink.Hypotheses₂`, `published_results_local O`, `UseLoc.main`, `TopCore` | `NonGaloisDescent/BoundAtTwoAndThreeForFamily.lean:18`; `EveryCharacterOfLiteratureOfVWin.lean:658`; `…/AdmissibleOfLargeResidueChar.lean:24` | an integral Wach / Herr-complex theorem gives the local conditions above ℓ; the named `BlochKatoLocal` input is discarded in the closing proof | integral p-adic Hodge theory (Fontaine–Laffaille, Wach, Berger) | [proof read in full] for `UseLoc.main` (frontier-b-links.md Q4; frontier-e-ribet.md §6) |

## Step 5. The Galois representations (page [05](05-galois-representations.md))

| Step | Declarations | File | Plain statement | Classical analogue | Status |
|---|---|---|---|---|---|
| 5.1 | `galoisRepresentations_of_thetaLift`, `galoisLocalGlobal_of_geometry_lift` | `…/GaloisRepresentations/IntegralStructures/…` | `Row0b` from a geometric input `geoOne_holds` and the theta-lift input `TLiftK` | none | [proof outline read] (theta-chain.md Q1–Q2) |
| 5.2 | `geoOne_holds`, `KS`, `GenModel`, `HTGroup` | `…/GeometricFlagBases/…`; `Definitions/Divisors/ExistsGDatumOneOneOne.lean:181` | seed forms on a definite unitary group have Galois representations in the étale cohomology of a Kuga–Sato variety over a PEL unitary Shimura variety | Harris–Taylor, Kottwitz | [proof outline read] (frontier-c-galois.md Q1) |
| 5.3 | `Cover.Cong`, `ESGen` | `…/GeometricFlagBases/IsGrRefl.lean:114`; `BasicOpenSections/BaseFacts.lean:45` | Eichler–Shimura congruence relation from ordinary points of the special fibre | Eichler–Shimura, Wedhorn | [statement read] (frontier-c-galois.md Q2) |
| 5.4 | `planEx_holds`, `specTopG`, `ksHodge_of_geo`, `FixK_holds`, `move_definite`, `cls_equiv_dcls_irr` | `…/PrimeLevelLocalization/SpecTopHolds.lean`; `GR/LefschetzSigmaSums/KsHodgeOfGeo.lean:7`; `…/DivisorProofs/MarkedFieldPairsEquivDefiniteFieldPairsOdd.lean:81` | transfer by a simple trace formula over ℂ: complex uniformisation, move of regular elliptic classes to definite inner forms (n odd), algebraic holomorphic Lefschetz | Harris–Taylor simple trace formula; Atiyah–Bott | [proof outline read]; bijection [proof read in full]; local terms and uniformisation [unread] (frontier-c-galois.md Q3; frontier-g-deep-inputs.md §I) |
| 5.5 | `CongFinOdd`, `CongUW4`, `PolyApprox` | `Definitions/GaloisGeometry/LimWU4OfLimWU3.lean:37` | every odd-rank eigensystem is an ℓ-adic limit of seed eigensystems | Serre, Gross, Chenevier interpolation | [proof outline read] (frontier-c-galois.md Q4) |
| 5.6 | `exists_limit_rep`, `PsChar.exists_ssRep`, `closedAtL` | `Proofs/InertiaEigenvalues/ExistsLimitRep.lean`; `Proofs/SatakeParameters/ClosedAtL.lean:25` | pseudo-character limit gives a semisimple representation; crystallinity passes to the limit | Taylor, Rouquier pseudo-characters; Kisin closedness | [proof outline read] (theta-chain.md Q2; frontier-c-galois.md Q5) |
| 5.7 | `TLiftK`, `TwoUp`, `Subtract`, `PeelAll` | `…/ThetaParseval/…` | even rank: two disjoint stable-range theta lifts to odd rank, then subtract the auxiliary characters | Rallis inner product, Siegel–Weil | [proof outline read] (theta-chain.md Q1; frontier-c-galois.md Q6) |

## Step 6. The window bound (page [06](06-window-bound.md))

| Step | Declarations | File | Plain statement | Classical analogue | Status |
|---|---|---|---|---|---|
| 6.1 | `vwin_of_row`, `vwin_of_hypotheses_H_E_alt`, `vwin_of_counts` | `…/DenseThresholdCases/VwinOfRow.lean`, `WindowBoundOfLiteratureLevel.lean`; `AV/HeightAndVanishing/JointWinOfCounts.lean` | `VWin` from Poitou–Tate, local finiteness and duality, `LemmaK`, `ThmBab`, `ThmBcFree` and five counts | none | [proof outline read] (frontier-d-window.md Q1) |
| 6.2 | `vvle_of_parts`, `ShaPlus`, `ShaMinus` | `LengthEqAddEigen.lean` | split into ℓ = 2, minus part, plus part | eigenspaces of complex conjugation | [statement read] (frontier-d-window.md Q1) |
| 6.3 | `ThmBcFree`, `PsiBound`, `ML.iv` | `AV/OddResidueBounds/…` | minus part ≤ v(Bernoulli numbers) | Mazur–Wiles; Kolyvagin–Rubin | [proof outline read] (frontier-d-window.md Q2) |
| 6.4 | `CountI`, `PropGK`, `OneCharU`, `LemmaM`, `LemmaM'` | `AV/HeightAndVanishing/CountI.lean`; `AV/UnitaryThreeGroups/KatoUse.lean`; `AV/CommutativeAlgebra/OrbitVanishingLocal.lean` | plus part over all ℓ ≤ 2 log\|NN\| for a nonzero integer NN of controlled size | Ribet's method; Bellaïche–Chenevier; Wiles–Lenstra numerical criterion | [proof outline read] (frontier-d-window.md Q2; frontier-g-deep-inputs.md §II.3) |
| 6.4b | `AutomorphyUnramifiedCoefficientsAlt`, `AutEnd3Alt`, `PfromAut`, `HidaUAlt` | `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/…`; `AV/PatchingModules/TaylorWilesObstructionBound.lean:150` | every ordinary strongly irreducible lift of the Eisenstein residual representation for U(3) is automorphic, via Hida theory, Taylor–Wiles patching for pseudo-deformation rings, seeds and linking | Skinner–Wiles, Thorne, Allen–Newton–Thorne (stated here in greater generality) | [statement read]; top level [proof outline read]; patching and linking bodies [unread] (frontier-g-deep-inputs.md §II) |
| 6.5 | `ThmBab`, `FW.ferreroWashington`, `towerTwo`, `LemmaK` | `AV/GaloisLibrary/FerreroWashingtonIndex/`; `AV/QuadraticExtensions/IsAlgClosureRat.lean:87`; `GeneratorCountTuples/LemmaK.lean` | ℓ = 2 and bad ℓ: Iwasawa μ = 0, uniform rank, pigeonhole over scales, Soulé-type bound | Ferrero–Washington, Sinnott, Soulé | [proof outline read] (frontier-d-window.md Q4; frontier-g-deep-inputs.md §III) |

## Where the weight sits

| Part | Reports' assessment | Source |
|---|---|---|
| reduction to `EveryCharacter` | a page, classical | skeleton.md |
| good pairs (`PairEx`) | classical: zero density plus mean square | analytic-core.md |
| localized Landau (`FormB`) | classical method with an explicit window | analytic-core.md |
| reaching 1/2 (`core_gm`) | bookkeeping and a size lemma; the content is in the hypotheses `SizeData₂`: the chain divisibility `Conclusion1` (proved by a Dwork-type p-adic analysis; the bridge from global lift kernels to p-adic power series is unread), the slope lower bound via `LinkS` (provider read at skeleton level), and `LinkN` | core-gm.md; frontier-a-divisor.md; frontier-f-divisibility.md |
| Ш enters each lift | Fitting-ideal / GMA method, classical in method; the near-vanishing of twisted Selmer groups (`TwistingCharacterExistence`) is "the most conjecture-shaped statement on this strand" | frontier-b-links.md; frontier-e-ribet.md |
| Galois representations | classical Shimura-variety route, formalized; transfer is a simple trace formula over ℂ, read at bijection level; local-term matching and uniformisation unread | theta-chain.md; frontier-c-galois.md; frontier-g-deep-inputs.md |
| window bound | minus part and Iwasawa part classical (Ferrero–Washington read and judged faithful); plus part rests on a residually reducible modularity theorem whose patching step `PfromAut` is stated in greater generality than the published literature | frontier-d-window.md; frontier-g-deep-inputs.md |

## Sources

- rhcheck/results/skeleton.md (with the theta-lift correction)
- analysis/statements-review.md (rows 19–21), analysis/vacuity-check.md
- analysis/analytic-core.md, analysis/core-gm.md
- analysis/frontier-a-divisor.md, analysis/frontier-b-links.md, analysis/frontier-c-galois.md, analysis/frontier-d-window.md
- analysis/frontier-e-ribet.md, analysis/frontier-f-divisibility.md, analysis/frontier-g-deep-inputs.md
- analysis/theta-chain.md
