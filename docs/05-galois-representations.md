# 5. The Galois representations (`Row0b`)

The first input of the final theorem, `Row0b`, attaches ℓ-adic Galois representations to regular algebraic polarized cuspidal automorphic representations of GL_a over CM fields, with weak local–global compatibility. The reports find a classical Shimura-variety route formalized inside the archive: étale cohomology of a Harris–Taylor-type Kuga–Sato variety for "seed" forms, extension to all odd-rank forms by ℓ-adic congruences and pseudo-characters, and a theta-lift device that reduces even rank to odd rank.

Status markers: [statement read], [proof outline read], [proof read in full], [inferred from names], [unread]. `GR/` abbreviates `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/` and `GFB/` abbreviates `GR/IntegralStructures/GeometricFlagBases/`.

> **Correction.** skeleton.md (item 1) said the Galois representations are "built from theta lifts inside the archive", because the proof of `Row0b` is the one line `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK`. theta-chain.md read the chain below that line and frontier-c-galois.md read the geometric source. The theta lift (`TLiftK`) is used exactly once, in the even-rank step. The representations themselves come from ℓ-adic étale cohomology of a PEL Shimura variety, congruences and pseudo-characters. The file name overstates the role of the theta lift. [proof outline read] (theta-chain.md Q1–Q2; frontier-c-galois.md overview)

## Terms used on this page

| Term | Meaning |
|---|---|
| CM field | a totally imaginary quadratic extension E of a totally real field E⁺ |
| definite unitary group U(n) | the unitary group of a positive definite Hermitian form over E/E⁺; its automorphic forms are functions on a finite set at each level ("algebraic modular forms") |
| PEL Shimura variety | a moduli space of abelian varieties with polarization, endomorphisms and level structure (Kottwitz) |
| Harris–Taylor group | a unitary group from a division algebra with involution of the second kind, signature (1, n−1) or (0, n) at infinity |
| Kuga–Sato variety | a fibre power of the universal abelian scheme over a Shimura variety |
| pseudo-character | a function on a group satisfying the identities of a trace; over a field of characteristic 0 it is the trace of a unique semisimple representation |
| Eichler–Shimura relation | Frobenius on the cohomology of a Shimura variety's reduction satisfies a polynomial whose coefficients are Hecke operators |
| Weil–Deligne representation (WD) | the local Galois-side object in the local Langlands correspondence |

## What `Row0b` states

`UpperTheory.GalStar.Row0b recT` / `PropsB` (`Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean`). [statement read, to depth 2] (statements-review.md row 20)

For a CM field E, a prime ℓ, ι : Q̄_ℓ ≅ ℂ and a regular algebraic polarized cuspidal π of GL_a(𝔸_E), there is a continuous semisimple r : G_E → GL_a(Q̄_ℓ) with Hodge–Tate weights HT(τ) = (a−1)/2 − (infinitesimal character) and HT(τ∘c) = wt − HT(τ). Local–global compatibility away from ℓ is weak:

```lean
structure AwayB (x y : WD h) : Prop where
  dim  : x.lpDim = y.lpDim
  tor  : Tor y → y.mono0 → x = y
  tame0 : IsQpBig w y.lpDim → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g, deg g = 0 → x.charPol g = y.charPol g
```

Full compatibility (x = y) is asserted only when the local parameter is abelian with N = 0. A second case covers tame, "square-free" parameters at places with E_w ≅ ℚ_g and g > 16a², where only inertia characteristic polynomials and N = 0 are asserted. Otherwise only dimensions match. Above ℓ (`AboveB`) the statement asserts crystalline / de Rham behaviour with the HT jumps at spherical places, and potentially semistable behaviour in the abelian or tame cases. Verdict: **weakened**, in the safe direction (less is claimed). (statements-review.md row 20)

The partial local Langlands input `IsRecT` / `RecTExists` (`…/Foundations/LocalLanglands/IsRecTOfIsRec.lean`) pins the correspondence down only on "Good" representations, whose cuspidal support consists of characters (or depth-zero cuspidals when E_w ≅ ℚ_g). On positive-depth supercuspidals it is almost unconstrained. Verdict: **weakened**. [statement read] (statements-review.md row 21) Because `away` quantifies over every rc satisfying `IsRecT`, a looser `IsRecT` makes `Row0b` harder to prove, not easier to use. (vacuity-check.md Q5)

### Is it vacuous, and what downstream uses

- The `above` clause quantifies over abstract period-ring packages `LocPrime`, ties `LocTied` and bridges `LocBridge`. These are proved inhabited: `GlobalTheory.MemLoc.exists_locPrime_tied` and `GlobalTheory.PlaceBridge.exists_locBridge`. `LocTied` forces the package to be isomorphic to the archive's concrete Fontaine rings. [statement read] (vacuity-check.md Q3)
- Consumers use `above` with concrete data. An unbroken chain from `Row0b.above` to a concrete bridge on the VWin path was not traced. [proof outline read], gap [unread] (vacuity-check.md Q3)
- Fields projected downstream: `cont`, `ss`, `away` (only its `.tor` case was seen), `weights`, `weights_conj` (copied, no final use seen), `above` (`.nice`, `.crys`). `away.tame0` did not appear. (vacuity-check.md Q4)
- Consumers apply local–global compatibility only in the abelian case, where `IsRecT` does constrain rc. Nothing downstream was seen to assume local Langlands for wild supercuspidals. This is an impression from the consumers read, not an exhaustive check. (vacuity-check.md Q5)

> **Note on an earlier report.** statements-review-3-geometry.md (§2) did not find a theorem constructing a `LocTied`, and flagged that five statements would be vacuous without one. vacuity-check.md located it: `exists_locPrime_tied` (`Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281`). (vacuity-check.md Q3)

## The construction, top down

[proof outline read] at the one-line level (theta-chain.md Q2)

| Step | Declaration | File | Content |
|---|---|---|---|
| 0 | `galoisRepresentations_of_thetaLift (up : TLiftK) : Row0b recT` | `GR/IntegralStructures/GaloisRepresentationsOfThetaLift.lean` | `galoisLocalGlobalStrong_of_geometry_lift geoOne_holds up`. A second input, `geoOne_holds`, is supplied inside the proof |
| 1 | `galoisLocalGlobalStrong_of_geometry_lift` | `IntegralStructures/Development.lean` | `Row0.row0b` applied to step 2 |
| 2 | `galoisLocalGlobal_of_geometry_lift` | same | `rest (coreAll_of (seedFinOdd_of_geoOne geo) (congFinOdd_of_ex wtLacEx_holds) up)` |
| 3 | `rest : CoreAll → Row0 recT` | same | local–global compatibility from the spherical-place statements |
| 4 | `coreAll_of_core` | `CrystallineInputs/CoreAllOfRowStarCore.lean` | from a restricted scope of CM fields to all CM fields; [unread] |
| 5 | `toCoreK up …` | `CrystallineDescent/ToCoreK.lean` | **the only use of `TLiftK`** |
| 6 | `toCore`, `core_of_limU`, `rowCsd_of` | `CrystallineDescent/LimOddOfLimFinOdd.lean` | combines odd rank (`LimU`) with the even-rank device `TwoUpOK`, plus Jacquet–Shalika and quadratic base change |

### (c) The geometric source: `geoOne_holds`

`GeoOne` (`GFB/HodgeTrAt.lean:79`) [statement read]: for a CM field E, ℓ, odd a, auxiliary data and a form U on the definite unitary group `UA E a` of a special type `TyEll` at a place w₀ | ℓ and with lacunary weight at a place v′ | ℓ, there is a continuous semisimple ρ of some dimension dd (not necessarily a) containing the expected eigensystem. The a-dimensional piece is cut out later in `seedFinOdd_of_geoOne` using the lacunary weights ([proof outline read]; mechanism [inferred from names]). (frontier-c-galois.md Q1)

**The geometric input is formalized, not assumed.** `geoOne_holds` is a theorem (frontier-c-galois.md Q1):

```lean
theorem geoOne_holds : GeoOne := geometric_realization_of_weight_one weight_one_geometric_realization
theorem kodaira_spencer_of_weight_one hW : KSAll :=
  ⟨CovMain.stdEx_holds, G3.kSEx_holds, G3.kSNice_holds, FiniteEtaleModels.ksGood_holds, CovMain.ksCong_holds, ksHodge_of_geo hW FixZ.FixK_holds⟩
```

- **The variety** (`KS`, `GFB/IntegOfMem.lean:48`) [statement read]: each level of a tower is the k-fold Kuga–Sato fibre power of the universal abelian scheme over `GenModel`, with Hecke maps induced by prime-to-p quasi-isogenies.
- **The moduli scheme** `GenModel` (`Development/AbelianVarietyTheory/Definitions/Divisors/ExistsGDatumOneOneOne.lean:181`) [statement read] is a fine moduli scheme for abelian schemes with an action of an order O, a rigidified symmetric relatively ample polarization with a Rosati condition, a Kottwitz-type Lie condition, and level-N structure compatible with the Weil pairing: a genuine PEL datum of unitary type. `HTGroup` (`…/Divisors/IsCyclotomicExtensionQI.lean:395`) is a central simple algebra of rank n² over a CM field with an involution of the second kind and signature (1, n−1) or (0, n) (theta-chain.md Q2).
- **Existence of the moduli scheme** goes through `harrisTaylorIntegralModel_nonempty`, the Zarhin trick, Siegel moduli and "theta uniformisation of complex abelian varieties". It was followed about seven levels; the Siegel / theta-function bottom is [unread]. [proof outline read] (frontier-c-galois.md Q1)
- **Étale cohomology** is the archive's own [statement read]: sheaves of ℤ/ℓ^k-modules on Mathlib's big étale site, cohomology through injective resolutions, a limit over k tensored with ℚ_ℓ. Proper base change (`UpperTheory.Et.proper_base_change`) is assembled from about 15 `…Statement` lemmas, which are [unread]. Finiteness `DegFin` is [unread]. (frontier-c-galois.md Q1)
- **Eichler–Shimura relation** `Cover.Cong` (`GFB/IsGrRefl.lean:114`) [statement read]: a point identity at generic (ordinary) points of the special fibre, which on cohomology becomes Σ_j (−1)^j q^{j(j−1)/2} T_j Frob^{n−j} = 0 (`ESGen`). Inputs: integral Hecke correspondences from isogenies with prescribed kernel, quotient objects, ordinariness at generic points of the special fibre (a Kodaira–Spencer / Hodge-filtration argument in the spirit of Wedhorn, [inferred from names]), and an elementary q-binomial count. Most proofs are [unread]. (frontier-c-galois.md Q2)

### The transfer to the Shimura variety: `planEx_holds`

```lean
theorem specTop_holds : SpecTop := UpperTheory.Gal.Spc.specTopG wtOf_holds
theorem planEx_holds : PlanEx := exists_unitaryGroupDatum_of_vector_exponent_spectral vecEx_holds expOf_holds specTop_holds
```

[proof outline read] (frontier-c-galois.md Q3). There is no Arthur trace formula and no analytic Jacquet–Langlands. The comparison is a simple trace formula:
1. `Frame` identifies the finite-adelic points of the Harris–Taylor group with those of a unitary group of the same rank (`F.surj`, [statement read]; fields not read in full).
2. A supercuspidal type at w₀ and regular support elsewhere force a regular elliptic test function (`auxFn`, `Good`).
3. The group side `dTrace` is a finite sum over classes of definite Hermitian forms (definite inner forms), each a trace of a Hecke operator on a finite-dimensional space. [proof outline read]
4. The geometric side uses a **holomorphic Lefschetz (Atiyah–Bott) fixed-point formula** for finite étale correspondences on the compact Kuga–Sato variety (`HolomorphicLefschetzFormula`, `GR/LefschetzSigmaSums/HodgeTraceFromLefschetzAndGroupSide.lean:102`, [statement read]), giving occurrence of the eigensystem in Hodge cohomology H^b(Ω^a).
5. Hodge to étale via a Hodge–Tate comparison (`JumpStep`); see below.

> **Correction.** frontier-c-galois.md (Q3, Q7) left the matching of the fixed-point sum with `dTrace`, and the Lefschetz formula itself, unread and called the matching the crucial transfer step. frontier-g-deep-inputs.md read both, as follows. (frontier-g-deep-inputs.md §I)

**How the transfer is done.** `ksHodge_of_geo` (`GR/LefschetzSigmaSums/KsHodgeOfGeo.lean:7`) [proof read in full] derives Hodge occurrence from four inputs: (a) the holomorphic Lefschetz formula; (b) `FixK`, fixed points of a correspondence = a group-theoretic count `cxTotalM`; (c) `cxTotalM` = a sum over definite pairs; (d) that sum = `dTrace`. **There is no Kottwitz-style point count over finite fields**; the comparison is made entirely over ℂ (frontier-g-deep-inputs.md overview, §I.1–I.2):
1. Fixed points of a Hecke correspondence on the complex points of the Kuga–Sato variety are put in bijection with group-theoretic data on G(ℚ) and the complex ball, via a complex uniformisation of the PEL moduli scheme by period lattices (`FixK_holds` = `tower_fixed_points_of_isogeny_data`, [proof read in full] at the top; about 70 `…_holds` lemmas in `GR/SphericalCoordinates/`, [proof outline read]).
2. Each regular elliptic fixed-point class (β, γ) is moved to a definite inner form by multiplying the Hermitian form by A(γ) ∈ F[γ] (`GlobalTheory.LKDef.move_definite`, `…/DivisorProofs/ExistsPolynomialMoveDefiniteSimilitudePairMarked.lean:750`, [proof outline read]). This needs an element of the totally real subfield with prescribed signs that is a local norm at every finite place; it exists by Hilbert reciprocity **because n is odd** (|S| = 2(n−1) is divisible by 4). This is exactly where `Odd n` is used. `cls_equiv_dcls_irr` gives the bijection of classes and preserves the orbital terms [proof read in full].
3. The definite side is a trace identity for a compact group (`trace_definite_forms_identity`, [proof read in full]), which is elementary.
4. Hodge cohomology is algebraic coherent cohomology of Ω^a (`hodgeH s j q := coh (Omega s j) q`), and the Atiyah–Bott formula is proved **algebraically** (Noether normalisation, Čech cocycles, Koszul complexes), not analytically (`lefschetz_fixedPoint_finite_etale_correspondence`, `…/EtaleClopenDescent/LefschetzFixedPointFiniteEtaleCorrespondence.lean:255`, and `holomorphic_lefschetz_finiteEtale_integral`, [proof outline read]).
5. Hodge to étale goes through an in-archive ℓ-adic Hodge–Tate comparison for smooth projective varieties with good reduction (`HTSpecGood`, Faltings-style, [statement read]; it lives in `Development/WeilBound/CoreStatements/PadicHodgeComparison/`, 538 files, proof [unread]). No Artin comparison and no singular cohomology are involved.

The reviewer's assessment: this is the Harris–Taylor "simple trace formula" special case. Regular elliptic test functions and a supercuspidal type kill the non-elliptic and reducible terms, so endoscopy, the boundary and stabilisation are sidestepped legitimately. The transfer is "a classical but genuine argument", not an assumed Jacquet–Langlands, and "mathematically sound in shape" at the bijection level. Still unread: the body of `complex_count_regular_marked_points` (571 lines), the uniformisation layer (`UnifG`, `GUnif`, and below them the Siegel / theta construction), the local computation `exists_chart_lift_of_finite_cover`, the Hodge–Tate comparison, and the matching of the Lefschetz local terms with the Weyl character (`FixLoc_holds`), which the reviewer flags as the subtle point to check by hand. (frontier-g-deep-inputs.md §I.4)

### (a) Congruences: `CongFinOdd`

`CongUW4` (`Definitions/GaloisGeometry/LimWU4OfLimWU3.lean:37`) [statement read]: every Hecke eigensystem θ of an odd-rank definite form U is an ℓ-adic polynomial limit (`PolyApprox`) of eigensystems of seed forms, with the same weights as U away from w₀, v′. The mechanism [proof outline read] (frontier-c-galois.md Q4):
- **type change at w₀**: characters of ℓ-power order on a small torsion-free open compact J, which are ≡ 1 modulo the maximal ideal;
- **weight change at v′**: ℓ-adic weight interpolation on the finite-dimensional spaces of algebraic modular forms of the definite group (Serre-letter / Gross / Chenevier style).

It is not Hida or Coleman theory and not the theta lift. `congUWG_of`, `famEx_of` and related bodies are [unread].

### (b) The limit: pseudo-characters and closedness

`limWU4_of` (`GR/TraceLimits/LimFinOddOf.lean`) builds the limit trace function, and `GlobalTheory.Cong.exists_limit_rep` (`Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLimitRep.lean`) [proof outline read] takes a locally-Cauchy extension, shows it is a pseudo-character, and gets a semisimple representation (`GlobalTheory.PsChar.exists_ssRep`). (theta-chain.md Q2)

Crystallinity of the limit at w | ℓ (away from w₀, v′) uses `ClosedAtL` [statement read]: if every member of a trace-approximating family is semistable at w with Hodge–Tate jumps exactly J, the limit is de Rham with jumps J, and crystalline if all members are. Its proof `closedAtL` goes through Breuil–Kisin frames of bounded height ([proof outline read]; details [inferred from names]). This is a Kisin-type closedness theorem, not the prismatic route. (frontier-c-galois.md Q5)

Weak compatibility `AwayB` is derived from spherical-place data by solvable base change and descent (`galoisCompat_unlinkedSupport_of_spherical`, [proof outline read]); the Iwahori-fixed case `localGlobalCompatAtIwahoriFixed_of_unlinked` is [unread]. (frontier-c-galois.md Q5)

### The even-rank device: `TLiftK`, `TwoUp`, `Subtract`

- `TLiftK` (`GR/ThetaParseval/HalfIndexLattices/TLiftK.lean:12`) [statement read]: for every automorphic π on the definite unitary group of an n-dimensional Hermitian space over a CM field, and all d large enough with a weight condition, the global theta lift of π to U(d) is nonzero, has the predicted archimedean weight, and is locally the theta lift at split places. This is classical stable-range non-vanishing, proved by the doubling method (Rallis inner product, Siegel–Weil, local bump functions). [proof outline read] (theta-chain.md Q1)
- `TwoUp E n` (`ThetaParseval/SplitLineSubtraction/RowDefOfOdd.lean:98`) [statement read]: every automorphic U on U(n) has two lifts to U(n+t), n+t odd, with Satake parameters Satake(U)·κ⁻¹ ⊞ (ψ_{i,1}, …, ψ_{i,t}) and disjoint character sets. `twoUpOK_of_steps` applies `TLiftK` twice. (theta-chain.md Q2)
- `Subtract` / `SubtractQ` [statement read] and `subtractQ_of` [proof outline read]: apply the odd-rank result to both lifts, then `PeelAll` (`SplitLineSubtraction/SubtractOf.lean:115`) removes the auxiliary characters from the characteristic polynomial, using their disjointness. (frontier-c-galois.md Q6, which reads the subtraction that theta-chain.md had left unread)

## Where `Row0b` is used

`Row0b` reaches the rest of the argument as `OpenImageCondition.galoisRepOfPolarizedPairLit : RowT` and as `gal : RowT` in `automorphic_window_of_inputs` (`TopMainZj.lean:71`) (vacuity-check.md Q4). On the window side it supplies local–global compatibility for the GL₂ representations in Kato's Euler system, Galois representations attached to U(3) forms, and a modularity input (frontier-d-window.md Q2). On the `core_gm` side, which `TopShapeAlt` fields it feeds was not traced [inferred from names] (core-gm.md Q2).

The "chain of theta lifts U(X₀) → … → U(X_m)" of the announcement is a separate body of code on the window / `core_gm` side, not on the `Row0b` path (theta-chain.md Q3; page [04](04-chain-and-one-half.md)). `kerSide_chainS` belongs to that side too (frontier-c-galois.md Q6).

## Summary for a number theorist

| Piece | Classical analogue | What the archive does | Status |
|---|---|---|---|
| base case | Harris–Taylor, Kottwitz | étale cohomology of a Kuga–Sato variety over a PEL unitary Shimura variety, built in the archive | [proof outline read]; bottom of moduli construction [unread] |
| Frobenius traces | Eichler–Shimura congruence relation | point identity at ordinary points of the special fibre | [statement read]; internals [unread] |
| transfer | trace-formula comparison (Kottwitz, Harris–Taylor) | simple trace formula over ℂ: complex uniformisation, move to definite inner forms (n odd), algebraic holomorphic Lefschetz | [proof outline read]; local-term matching and uniformisation [unread] |
| all odd-rank forms | Chenevier, Bellaïche–Chenevier | ℓ-adic weight and type interpolation on definite groups, pseudo-character limit | [proof outline read] |
| p-adic Hodge properties | Kisin closedness | closedness via Breuil–Kisin frames with fixed jumps | [proof outline read] |
| even rank | theta-lift tricks (cf. Shin, Chenevier–Harris) | two disjoint stable-range theta lifts, then subtract characters | [proof outline read] |

## Sources

- analysis/theta-chain.md (Q1, Q2, Q3, Q4)
- analysis/frontier-c-galois.md (all sections)
- analysis/frontier-g-deep-inputs.md (§I, the trace comparison; corrects frontier-c on what was unread)
- analysis/vacuity-check.md (Q3, Q4, Q5)
- analysis/statements-review.md (rows 20, 21)
- analysis/statements-review-3-geometry.md (§2, superseded on `LocTied`)
- analysis/frontier-d-window.md (Q2, uses of `Row0b` on the window side)
- rhcheck/results/skeleton.md (item 1, corrected here)
