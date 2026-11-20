# Glossary of the archive's internal names

The archive uses short, often opaque names of its own. This glossary gives each one that appears in these documents a one- or two-sentence meaning, the file where it is defined when a report gives it, and the report it comes from.

Meanings are as read by the AI reviewers, at the status the cited report gives; nothing here upgrades that. Paths are relative to the archive's `src/`. `CB/` = `Development/AutomorphicArithmetic/CharacterBoxes/`, `GR/` = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/`, `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`, `AV/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/`.

## Libraries and namespaces

Top-level libraries are directories of files; namespaces are prefixes of declaration names. They overlap but are not the same thing: a file in the `Development` library can declare names in `UpperTheory` or `GlobalTheory`.

| Name | Kind | Meaning |
|---|---|---|
| `Development` | library | 141,928 modules, about 70% of the lines; the bulk of the archive (structure.md) |
| `Formalism` | library and namespace | 18,254 modules; abstract machinery such as `Formalism.HC` (zero-free statements, levels), `Formalism.L2`, `Formalism.HN` (slopes), `Formalism.DivisionValues` (structure.md; core-gm.md) |
| `GroundTheory` | library | 8,507 modules of foundational material, median import closure 19 (structure.md) |
| `ReciprocityTheory` | library and namespace | 3,845 modules: Galois cohomology (`ReciprocityTheory.Gal.*` finiteness, Euler characteristic, Tate duality), local fields, class field theory (structure.md; literature.json) |
| `CompanionTheory` | library and namespace | 2,027 modules; `GlobalTheory.CompanionTheory.*` holds some complex-geometric literature bundles (structure.md; literature.json) |
| `PositivityTheory` | library and namespace | 449 modules with a median import closure of 21,541; some `…_holds` proofs of literature statements, e.g. `PositivityTheory.Prw.ellipticMainTheoremCM_holds` (structure.md; skeleton.md) |
| `UpperTheory` | namespace | the top layer of the argument: `UpperTheory.EveryCharacter`, `UpperTheory.Top.*` (window and analytic endgame), `UpperTheory.GalStar.*` (Galois statement), `UpperTheory.LiteratureTheorems.*` |
| `GlobalTheory` | namespace | middle layer: `GlobalTheory.Published.*` (named classical statements), and many proof namespaces such as `GlobalTheory.CutCoreUnit`, `GlobalTheory.Cong`, `GlobalTheory.T` |
| `Statements`, `Main`, `Supplements` | libraries | the four final definitions; the five final theorems; three thin wrapper modules (`Supplements.Kernels.MainTheorems*`) |
| `Lemmata`, `BuildAid` | libraries | 167 small helper files; 5 build stubs |

## Names

| Name | Meaning | Defined in / source |
|---|---|---|
| `AboveB` | the part of `Row0b` about places above ℓ: crystalline / de Rham with the right Hodge–Tate jumps at spherical places, potentially semistable plus `AwayB` in abelian or tame cases | `GR/TypeConditions/WeightsConjBis.lean` (statements-review.md row 20) |
| `ASK` | the prime sum bounded in `core_gm`: Σ over primes p inert in ℚ(√±d) of 2 log p · Σ_{odd i} (a/p^i − w)⁺, plus a term at d; the threshold w depends on the Frobenius class of p^i. Legendre-shaped, and equal to a Riesz-smoothed explicit-formula sum at y = a/w | `DedekindLFunctions/RunBaseDimensionLeRankAddGenusTerm.lean:105` (core-gm.md Q2; frontier-a-divisor.md Q3) |
| `AwayB` | the weak local–global compatibility away from ℓ: equality of Weil–Deligne representations only for abelian N = 0 parameters, inertia characteristic polynomials in a tame square-free case, otherwise only dimensions | statements-review.md row 20 |
| `AutEnd3Alt`, `AutomorphyUnramifiedCoefficientsAlt` | every ordinary, strongly irreducible characteristic-zero lift of the Eisenstein residual representation for U(3) is automorphic; the modularity input of the window bound | `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/AutEnd3AltAlt.lean`, `AutomorphyUnramifiedCoefficients.lean:23` (frontier-g-deep-inputs.md §II.2) |
| `CM2`, `CM3` | good models of CM elliptic curves (from global Artin reciprocity), and supersingular reduction at inert primes with the height-2 Lubin–Tate logarithm Σ_j x^{ℓ^{2j}}/ℓ^j (Honda theory) | `Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean:45` (frontier-f-divisibility.md Task 1) |
| `ChainTied` | `CoreAtH`'s data tied to a concrete family on its windows; built by `topDesWin` from the `Link*` inputs | `Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97` (core-gm.md Q2) |
| `Conclusion1` | the m-step chain's column at an inert place w is divisible to order Σ_j gain_j(w) (plus type and excess terms); proved via `FormalGroupSystem` | `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:101` (frontier-a-divisor.md Q2; frontier-f-divisibility.md Task 1) |
| `CongFinOdd` (`CongUW4`) | every Hecke eigensystem of an odd-rank definite unitary form is an ℓ-adic polynomial limit of eigensystems of "seed" forms | `Definitions/GaloisGeometry/LimWU4OfLimWU3.lean:37` (theta-chain.md Q2; frontier-c-galois.md Q4) |
| `core_gm` | the theorem Gm(x) ≤ x^{1/2+(eD+eL+7)ε} from `EAtH` and `CoreAtH`; the step that reaches 1/2 | `Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12` (core-gm.md Q1) |
| `CoreAtH` | the hypothesis bundle of `core_gm`: m lifts, a ~40-field numerical record, `SizeData₂`, `RestSize` and other size conditions | `PrimitiveCosets/CoreAtH.lean` (core-gm.md Q1) |
| `CountI`, `CountII`, `CountIII`, `CountV`, `CountZ` | the case split of the plus part of Ш in the window bound, by whether ℓ − 1 divides 2e' and whether ℓ is in a fixed bad set | `AV/HeightAndVanishing/Counts.lean` (frontier-d-window.md Q1) |
| `CutCoreUnit.main` | congruence number at an Eisenstein-type π ≤ Selmer length + Σ_e len Ш¹(ℚ_ℓ/ℤ_ℓ(−e)) + v_ℓ(h_E) + tame terms; its core is a Fitting-ideal argument on a generalized matrix algebra (`length_heckeValueIdeal_le_determinant_bound`) | `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:44` (frontier-b-links.md Q2; frontier-e-ribet.md §1) |
| `cxTotalM`, `FixK` | the group-theoretic count of fixed points of a Hecke correspondence on the complex points of the Kuga–Sato variety (classes of forms, points of the complex ball, fixing elements), and the theorem equating it with the Lefschetz fixed-point sum | `Development/AbelianVarietyTheory/Statements/PlaceShiftStatements/MarkWeightedFixedPointEqDefinitePairOdd.lean:31`; `GR/LefschetzSigmaSums/HodgeTraceFromLefschetzAndGroupSide.lean:125` (frontier-g-deep-inputs.md §I.1) |
| `D7` | the family datum at one point: host primes, field, lattices, theta and period data (`what₂.*`, `div.*`, `besS`) | frontier-a-divisor.md Q6; core-gm.md Q1 |
| `DIV` | the divisor inequality in `SizeData₂`: dual slope + height − Fo ≤ m·Σ_t(ph(a_t) − a_t logΩ) − Σ_t a_t log T + errors | `Formalism/RankGapBounds/MeanBoundSecondForm.lean:118` (core-gm.md Q2; frontier-a-divisor.md Q1c) |
| `DIVinN` | the excess local divisibility of each lift (etaSum) is O(x^ε·(B0 + Nc)); produced by `divinN_of_hypV` from `HypV` and `LinkN` | `CB/DivinNOfHypV.lean:117` (frontier-b-links.md Q1) |
| `DivIneqRecord`, `divisor_inequality_explicit` | the real-variable lemma behind `DIV`; m copies of a log a − a arise by summing per-lift height bounds | `Formalism/QuotientMetricDivisors/ScalarLiftLowerBoundFull.lean:53`; `…/GlobalBoundRefinements.lean:91` (frontier-a-divisor.md Q1) |
| `EAtH` | explicit-formula error conditions for a host: equidistribution, G-bounds and \|L'/L(1)\| bounds for the twisted characters | `…/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:144` (analytic-core.md Q3) |
| `etaJ`, `etaSum` | etaJ(j, w): length of the congruence module of the j-th lift's forms at a twisted place w; etaSum: its weighted sum over w | `Divisibility/LiftLat.lean:116-147`; `Formalism/SharpRestriction/GlobalTheoremInputs.lean` (frontier-b-links.md Q1) |
| `EveryCharacter` | L(s, χ) ≠ 0 for every Dirichlet character and Re s > 1/2, except the pole of the trivial character; all five final theorems follow from it | `UpperTheory.EveryCharacter` (skeleton.md §1) |
| `FormB`, `FormBAt` | the localized Landau theorem: Gm ≤ x^θ on windows [Y, Y^{la}] implies zero-freeness for Re s > θ | `…/TotientGaloisClasses/Window.lean:30`; `PrimitiveCosets/Imports.lean:8` (analytic-core.md Q3) |
| `FerreroWashington` | bounded l-rank of class groups up the cyclotomic tower of an abelian field containing μ_l (μ_4 if l = 2), i.e. μ = 0 in rank-bound form; proved in the archive by Sinnott's method | `UpperTheory.V.Published.FerreroWashington`, `AV/PublishedTheorems/FerreroWashington.lean:7` (frontier-g-deep-inputs.md §III) |
| `FormalGroupSystem` (`Sys`, `Pend`, `LowAt`) | the local p-adic model at an inert prime: lattice-tuple form spaces, chain steps as sums of differential operators applied to theta kernels on the supersingular formal group, and the valuation bound `LowAt` | `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean` (frontier-f-divisibility.md Task 2) |
| `Gm` | Gz(y) + Σ_ψ wt(ψ)·Re gChi(ψ, y) over the characters of the cyclic level of ψ, weight 1 for the exceptional character and 1/(3o+1) for the others | `…/ExplicitFormulaErrorOfHostConditions.lean:36-38` (core-gm.md Q1) |
| `gChi`, `Gchi`, `GPsi` | G_χ(y) = Σ_{n≤y} Λ(n)χ(n)(y/n − 1) + y·L'/L(1, χ), a Riesz-smoothed prime sum | `…/TotientGaloisClasses/Analytic.lean:23` (analytic-core.md Q1) |
| `geoOne_holds`, `GeoOne` | the geometric source of the Galois representations: seed forms appear in the étale cohomology of a Kuga–Sato variety over a PEL unitary Shimura variety | `GR/IntegralStructures/GeometricFlagBases/HodgeTrAt.lean:79` (frontier-c-galois.md Q1) |
| `GenModel` | a fine moduli scheme for PEL objects of unitary type | `Development/AbelianVarietyTheory/Definitions/Divisors/ExistsGDatumOneOneOne.lean:181` (frontier-c-galois.md Q1) |
| `HostExW` | host data on windows, output of `supplyChi`: `EAtH` plus the Ш bound `VVle` | `CB/SupplyChi.lean` (analytic-core.md Q3) |
| `HTGroup` | a Harris–Taylor / Kottwitz PEL datum: central simple algebra of rank n² over a CM field with an involution of the second kind and signature (1, n−1) or (0, n) | `…/Divisors/IsCyclotomicExtensionQI.lean:395` (theta-chain.md Q2) |
| `HTower` | a scheme Z over a number field with correspondences; `Nice` means smooth, projective, finite étale correspondences | `Development/AbelianVarietyTheory/Definitions/Divisors/IdTower.lean` (theta-chain.md Q2) |
| `HypV` | the family form of the window bound: for large x and each family point, `VVle` with bound √b | `CB/DivinNOfHypV.lean` (core-gm.md Q2) |
| `IsChiField ψ e q d E` | E is a host field cut out of a cyclotomic field by ψ, the Jacobi symbols mod q and d, and the 2-power level 2^{e+2} | used in `WinDatum` (analytic-core.md Q3); definition not quoted |
| `IsRecT`, `RecTExists` | a partial local Langlands correspondence for GL_n, pinned down only on "Good" representations (cuspidal support of characters, or depth zero over ℚ_g) | `…/Foundations/LocalLanglands/IsRecTOfIsRec.lean` (statements-review.md row 21) |
| `KillAt` | sPi ≤ nuL(ℓ) + ε_ℓ: the ρ-block Selmer length is bounded by an H⁰-type quantity after choosing a good auxiliary twist | `JointConditionsZpowers/CommutingEndomorphismCondition.lean:45` (frontier-e-ribet.md Q3) |
| `LData` | local data for Ш¹ at ℓ: S = places above ℓ, chosen places, and the cyclotomic character on G_S; proved inhabited and essentially canonical | `Formalism/GaloisCohomology/Statement.lean`; `ldataExists` (vacuity-check.md Q2) |
| `LemmaK` | H²(O_L[1/ℓ], ℤ_ℓ(e+1)) is finite with log-order ≤ exp(poly(e·n)·log D), Soulé-shaped | `GeneratorCountTuples/LemmaK.lean` (frontier-d-window.md Q1) |
| `LinkG` | at each inert prime, the sum of the lifts' local gains is at least the von Mangoldt class sums minus errors; gives ASK ≤ Ga + loss | `GlobalTheoremInputs.lean` (frontier-b-links.md Q1) |
| `LinkN` | each lift's etaSum ≤ (Ш¹ lengths) + O(f·m·b·L²) | `GlobalTheoremInputs.lean` (frontier-b-links.md Q1) |
| `LinkS` | Hilbert–Schmidt near-orthogonality of the period vectors across words u, defects ≤ exp(−x^{ε/8}); supplied by `link_alt_alt_bis` from `TheoremSSelected` and counting inputs | `GlobalTheoremInputs.lean:145,152` (frontier-a-divisor.md Q4; frontier-f-divisibility.md Task 4) |
| `LinkDIV`, `LinkIRR`, `LinkMu`, `LinkEta`, `LinkGLOBAL` | other inputs; `GlobalTheoremInputs := LinkG ∧ LinkS ∧ LinkIRR ∧ LinkDIV ∧ LinkMu`, and `LinkGLOBAL` turns them into `ChainTied` | `GlobalTheoremInputs.lean` (core-gm.md Q2) |
| `LiteratureTheorems` | namespace `UpperTheory.LiteratureTheorems`: the `_of_literature` theorems that prove each named statement, and the final `every_character_of_literature_of_vWin` | `TPS/EveryCharacterOfLiteratureOfVWin.lean` (literature.md; static-reachability.md) |
| `LocPrime`, `LocTied`, `LocBridge` | an abstract package of period rings; its tie to the archive's concrete Fontaine rings; an embedding identifying a completion with a finite extension of ℚ_ℓ. All proved inhabited | `…/LevelLetterCocycles/DataNLoc.lean:527,574`; `…/AdicCompletionLocal/LocTied.lean:11` (vacuity-check.md Q3) |
| `MAIN`, Main term | the Stirling-type main term a(log a − 1 − γ + …) of ASK; in `DIV` it carries the factor m, one copy per lift | `RunBaseDimensionLeRankAddGenusTerm.lean:110`; `LocalRingCardinality/DataParams₂.lean:232` (core-gm.md Q2) |
| `mAt` | the chain length m = evenCeil(√(x·x^{−ε/8})); its module is statically unreachable | `…/AutomorphicMembership/EvenCeil.lean` (theta-chain.md Q3) |
| `move_definite` | moves a regular elliptic fixed-point class to a definite inner form by changing the Hermitian form within F[γ]; uses that n is odd (Hilbert reciprocity) | `GlobalTheory.LKDef.move_definite`, `…/DivisorProofs/ExistsPolynomialMoveDefiniteSimilitudePairMarked.lean:750` (frontier-g-deep-inputs.md §I.2) |
| `OpenImageCondition` | a structure with one field, the Galois statement `Row0b` as `RowT`; many `_of_literature` theorems take it as `O` | skeleton.md §3; frontier-d-window.md Q5 |
| `PageN`, page e(x) | the 2-power level with 2^e ≈ x^{2+8ε} | `CB/ExistsPageN.lean` (analytic-core.md Q5; statements-review.md row 19) |
| `PairEx`, `PairGood` | existence, for every large scale Y, of a window pair (q, d) whose quadratic twists have zero-free boxes and square-root bounds | `CB/PairGood.lean:28`; proved as `QH.pairEx` (analytic-core.md Q1) |
| `PfromAut` | Taylor–Wiles patching for universal ordinary determinant rings: components through nice modular points are modular, and modularity propagates along linked components; stated for all n | `AV/PatchingModules/TaylorWilesObstructionBound.lean:150` (frontier-g-deep-inputs.md §II.2) |
| `PropGK` | a nonzero integer NN of controlled size whose ℓ-valuations bound the plus part of Ш for all ℓ at once | `AV/UnitaryThreeGroups/KatoUse.lean` (frontier-d-window.md Q2) |
| `PropsB` | the property bundle of `Row0b`: `cont`, `ss`, `away`, `weights`, `weights_conj`, `above` | `GR/TypeConditions/WeightsConjBis.lean` (statements-review.md row 20; vacuity-check.md Q4) |
| `Published` | namespace `GlobalTheory.Published`: about 155 named classical theorems stated as `Prop`s; each is proved in the archive, none is assumed | literature.md; page [07](07-named-theorems.md) |
| `PsChar`, `IsPsChar` | pseudo-characters; `GlobalTheory.PsChar.exists_ssRep` turns one into a semisimple representation | theta-chain.md Q2 |
| `RestSize` | size conditions in `CoreAtH`, including x^{1/2−ε} ≤ m (chain length about √x) | `Formalism/SizeWindowBrackets/SChain.lean` (core-gm.md Q1) |
| `Row0b`, `RowT` | the Galois-representation statement for regular algebraic polarized cuspidal π on GL_a over CM fields; `RowT` is the form passed downstream | `UpperTheory.GalStar.Row0b` (statements-review.md row 20) |
| `Row0`, `Row`, `RowAt` | intermediate forms of the Galois statement in its construction (`Row0.row0b`, `RowAt` per rank) | theta-chain.md Q2; frontier-c-galois.md Q6 |
| `shaLen` | `Module.length ℤ_[l] (Sha D e)`, the ℤ_ℓ-length of Ш¹(G_{E,S}, ℚ_ℓ/ℤ_ℓ(−e)), valued in ℕ∞ | `Formalism/GaloisCohomology/Statement.lean:54-78` (vacuity-check.md Q2) |
| `sPi` | the Bloch–Kato Selmer length of the ρ-block ρ_π ⊗ χ₁^{−1}, normalized by len(O/ℓ) | `BaseSizes.lean` (frontier-e-ribet.md Q3) |
| `SizeData₂` | about eleven real inequalities about slopes, heights, gains, `DIV` and counts: the arithmetic content of `CoreAtH` | `SChain.lean:17` (core-gm.md Q2) |
| `SlopeIneq` | Bost's slope inequality for Hermitian lattices (`Formalism.HN`); its data-level form gives a lower bound for a dual slope | `Formalism/HarderNarasimhan/Statement.lean:91` (frontier-a-divisor.md Q1c) |
| `TheoremSSelected` | the off-diagonal Hilbert–Schmidt bound feeding `LinkS`. Not the same as `ThmSUniform` | `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/ThmSOwn.lean:669` (frontier-f-divisibility.md Task 4) |
| `ThmSUniform`, `theorem_s_uniform` ("Theorem S") | the theta kernel exp(−Σβ)·U, in Lubin–Tate log coordinates, lies in a class Σ_i p^{−i}·hh^i·(integral); the p-adic heart of `Conclusion1` | `…/UniformThetaSubstitution/ThmSUniform.lean:14` (frontier-f-divisibility.md Task 2) |
| `TLiftK` | non-vanishing of the stable-range global theta lift from a definite U(n) to U(d); used only for the even-rank step | `GR/ThetaParseval/HalfIndexLattices/TLiftK.lean:12` (theta-chain.md Q1) |
| `TwistingCharacterExistence` | for every ε′ and finite set of places, an anticyclotomic auxiliary twist with nearly trivial twisted Selmer group and nonvanishing twisted theta elements exists; "the most conjecture-shaped statement" on the Ш-link strand | `IntegralHeckeForms.lean:166` (frontier-e-ribet.md Q3, Q4) |
| `TwoUp`, `Subtract`, `PeelAll` | the even-rank device: two disjoint lifts to odd rank, then remove the auxiliary characters | `GR/ThetaParseval/SplitLineSubtraction/…` (theta-chain.md Q2; frontier-c-galois.md Q6) |
| `vcc` | congruence number at π: length of O modulo the congruence ideal ker(T → ∏_{x∉Z} O) | `LevelLetterCocycles/DataN.lean:219` (frontier-b-links.md Q1) |
| `vdel`, `lStar` | vdel: valuation of the root differences of the χ-block characters, booked as an error for medium ℓ; lStar ≈ m·b/poly: above it the root differences are units | `DataN.lean:232`; `Formalism/LocalRingCardinality/DataParams.lean:38` (frontier-e-ribet.md Q1) |
| `VAt` | not described in any report used for these documents; not placed | |
| `VVle E t B` | for all `LData`, each Ш¹ length is finite for 0 < e < t, and Σ_ℓ log ℓ Σ_e length ≤ B | `CB/ExistsPageN.lean:12` (vacuity-check.md Q2) |
| `vvTerm` | log ℓ · Σ_{1≤e<t} shaLen_ℓ(e), the per-prime Ш term | `GlobalTheoremInputs.lean` (frontier-b-links.md Q1) |
| `VWin` | `∀ ψ, VWinAt ψ 401`: the window bound on Ш¹ lengths; no published analogue | `CB/ExistsPageN.lean` (statements-review.md row 19) |
| `VWinAt ψ Ct` | the window bound for one character ψ with twist range up to x^{Ct} | `CB/ExistsPageN.lean` (statements-review.md row 19) |
| `WeilJacquetShalikaLaw` | namespace of the global valuation statements (`Conclusion1`, `Conclusion₂`); the name is not descriptive, no Jacquet–Shalika identity was found in it | frontier-f-divisibility.md Task 2(d) |
| `WinDatum` | for a window point x: a good pair at scale Y ∈ [x^{1/J}, x], a page e, and the Ш bound on every `IsChiField` | `CB/WinPairs.lean` (analytic-core.md Q3) |
| `WinPair eps Y q d` | q ≡ 3 mod 8, d ≡ 7 mod 16 primes of sizes log q ≈ T, log d ≈ T log²Y, with q \| d+1 and every odd p ≤ T dividing d+1, where T = Y^{ε/5} | `CB/ExistsPageN.lean:27-49` (vacuity-check.md Q1) |
| `ZeroBox`, `ZeroFreeBox` | no zero with Re s > 1 − 1/400 and \|Im s\| ≤ Q | `CB/PairGood.lean`; `Formalism/GL3MeanSquares/…` (analytic-core.md Q1) |
| `ZeroFreeAll` | the zero-free statement produced by the analytic endgame, before passing to imprimitive characters | `…/ExplicitFormulaErrorOfHostConditions.lean` (analytic-core.md Q4) |

## Suffix conventions

| Suffix | Meaning in practice |
|---|---|
| `_of_literature` | a theorem in `UpperTheory.LiteratureTheorems` establishing a `Published` statement; may take `O : OpenImageCondition` without using it (literature.md; statements-review-3-geometry.md) |
| `_holds`, `_outright` | a hypothesis-free proof of a named statement (skeleton.md §3) |
| `…Statement` (file names) | about 26.6% of file names; often thin wrappers whose proof sits one file lower (archive-stats.md; frontier-c-galois.md Q1) |
| `_alt`, `_alt_alt`, `_bis` | parallel versions of a declaration; the main path often uses the `_alt` one (archive-stats.md §4; frontier-d-window.md) |

## Sources

rhcheck/results/skeleton.md, rhcheck/results/structure.md, rhcheck/results/literature.md, analysis/statements-review.md, analysis/vacuity-check.md, analysis/analytic-core.md, analysis/core-gm.md, analysis/theta-chain.md, analysis/frontier-a-divisor.md, analysis/frontier-b-links.md, analysis/frontier-c-galois.md, analysis/frontier-d-window.md, analysis/frontier-e-ribet.md, analysis/frontier-f-divisibility.md, analysis/frontier-g-deep-inputs.md, analysis/archive-stats.md, analysis/static-reachability.md.
