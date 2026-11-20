# The theta-lift strand behind `Row0b`

Date: 2026-11-20. This is a read-only source study of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled or
run. Paths are relative to `src`. Tags: **[stmt]** means I read the statement, **[proof]** means I read the proof
term or tactic skeleton, **[names]** means the claim is inferred from declaration names only. "Reachable" means
the static name-level over-approximation in `analysis/static-reachability.md` (module rows in
`/bulk/shared/rieman/analysis/reach/reachable-modules.txt`, rule A / rule B declaration counts). It is not the
compiled dependency set.

A by-product: I built a flat declaration index on chili,
`/bulk/shared/rieman/analysis/reach/decl-index.tsv` (name, kind, module, line; 1,041,799 rows, from the existing
shards). `grep -P "^Full.Name\t"` finds any declaration instantly.

## Overview (for a number theorist)

The one-line proof `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK` hides a mostly classical
construction. The theta lift does **not** supply the Galois representations. It enters only in the
**even-rank step**. `TLiftK` is non-vanishing of the global theta lift from a definite unitary group U(n) to U(d)
in the stable range d ≥ d₀, proved by the doubling method (Rallis inner product, Siegel–Weil, local bump
functions). It is used to put π (n even) into two automorphic forms on U(n+t), n+t odd, with Satake parameters
π⊗κ⁻¹ ⊞ (ψ₁,…,ψ_t). The two choices of Hecke characters are disjoint. The characters are then "subtracted"
from the odd-rank Galois representations. The odd-rank representations come from:
(c) l-adic étale cohomology of PEL-type Shimura varieties for a Harris–Taylor-type group (`HTGroup`: a division
algebra with involution of the second kind over a CM field, signature (1,n−1) or (0,n) at infinity). This is
done for "seed" forms with a special local type and lacunary weights. Frobenius traces are identified by an
Eichler–Shimura-type congruence relation on integral models.
(a)+(b) Every other odd-rank form is a p-adic limit of seeds via congruences (`CongFinOdd`). The limit trace
function is a pseudo-character, which gives a semisimple representation (`GlobalTheory.Cong.exists_limit_rep`).
So the route is the classical Shimura-variety route (Harris–Taylor / Shin / Chenevier–Harris style, including
a theta-lift device for even n), not a theta-congruence construction. The "chain of theta lifts U(X₀)→…→U(X_m)"
of the announcement is a **separate** body of code on the VWin side (`IteratedLiftChains`, `Ranks.m`, `D7`,
`NumDatum`). There the chain length is defined as m = evenCeil(√(x·x^{−ε/8})). That definition's module has 0
statically reachable declarations under rule A.

## Q1. `galoisRepresentations_of_thetaLift` and `tLiftK`

`…/GaloisRepresentations/IntegralStructures/GaloisRepresentationsOfThetaLift.lean` **[stmt+proof]**:
```lean
theorem galoisRepresentations_of_thetaLift (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0b recT :=
  galoisLocalGlobalStrong_of_geometry_lift UpperTheory.Gal.Int.Geo.geoOne_holds up
```
Hypothesis: `TLiftK`. Conclusion: `Row0b recT` (see statements-review.md row 20). A second, independent input,
`geoOne_holds` (geometric realization), is supplied inside the proof. So the file name overstates the role of
the theta lift.

`…/ThetaParseval/ThetaKernels/TLiftK.lean` **[proof]**: `theorem UpperTheory.TP.K.tLiftK : TLiftK := UpperTheory.TP.tLift_holds_k`.

`TLiftK` (`…/ThetaParseval/HalfIndexLattices/TLiftK.lean:12`) **[stmt]**, trimmed:
```lean
def TLiftK : Prop := ∀ E [IsCMField E] (B : Base E⁺ E), W.GoodK (cj E) B → ∀ n ≥ 1, ∀ X : Spc E⁺ E n, X.J = 1 → X.IsHerm (cj E) B n 0 →
  ∃ d₀, ∀ d ≥ d₀, ∀ (W : Spc E⁺ E d) δ, W.J = δ • 1 → W.IsSkew (cj E) B d 0 → ∀ χX χW mX mW, IsHecke χX → IsHecke χW →
    ResEtaPow … χX n → ResEtaPow … χW d → HasExp B.emb χX mX → HasExp B.emb χW mW →
    ∀ U lam, IsAutRepU U → (∀ w, HasWeightAt U (B.emb w).1 (lam w)) → (∀ w k, d + mW w ≤ 2 * (lam w).w k) →
    ∃ U' : Submodule ℂ (UA E d → ℂ), IsLift B χX χW mX mW lam U U'
```
`IsLift` (`…/ThetaParseval/SchurStep.lean:106`) **[stmt]**: U' is an automorphic representation of U(d). Its
weights are given by `IsLiftWt`, i.e. 2λ'_k = 2λ_k − d − mW + n + mX for k < n, and n + mX otherwise. At every split
place the local components are related by a nonzero Weil-representation intertwiner (`LocPair`, the local
theta correspondence for GL_n × GL_d with splitting characters χX, χW).

Plain language: for every automorphic π on the definite unitary group of an n-dimensional Hermitian space over a
CM field, and for all d large enough with a mild weight condition, the global theta lift of π to U(d) (with
splitting characters χX, χW) is nonzero, has the predicted archimedean weight, and is locally the theta lift at
split places. This is classical stable-range non-vanishing. "Definite" is **[names]**: the form has signature
parameter 0, and the code imports `BaseChangeDefiniteUnitary`.

The proof (`ThetaKernels/TPGHolds.lean`, `TPGTop.lean`) **[proof skeleton]** runs as follows.
`tLift_of_tools_k` is assembled from `nonVan_k (rallis_k) (decomp_k) (bumpAny_k) (datum_k) (tail_k) absNe (schurStep_k)`
and `liftAut_k`. The `Tools_k` bundle contains the Siegel–Weil formula (`siegelWeilStd_k`), doubling
(`dblX_k`), Eisenstein-series continuation, compactness, `pairEx`, and `lieFirst/lieSecond` (archimedean).
`Rallis` (`SchurStep.lean:142`) **[stmt]** says that if the lift vanishes, then the doubling integral of the
Weil-representation matrix coefficient against the matrix coefficient of φ vanishes. `NonVan` (`:225`)
**[stmt]** says that for d ≥ 2n the lift is nonzero for some factorizable Schwartz datum. The local bump data
(`Datum`, `BumpAny`, `Tail`, `AbsNe`) make the doubling integral nonzero. This is the Rallis inner-product /
doubling-method argument.

## Q2. From theta lifts to Galois representations

Chain of lemmas, all **[proof]** at the one-line level:

| step | declaration | file | one-sentence content |
|---|---|---|---|
| 1 | `galoisLocalGlobalStrong_of_geometry_lift geo up` | `IntegralStructures/Development.lean` | `Row0.row0b` applied to `galoisLocalGlobal_of_geometry_lift`. |
| 2 | `galoisLocalGlobal_of_geometry_lift` | same | `rest (coreAll_of (seedFinOdd_of_geoOne geo) (congFinOdd_of_ex wtLacEx_holds) up)`. |
| 3 | `rest : CoreAll → Row0 recT` | same | derives local–global compatibility (`galoisCompat_unlinkedSupport_of_spherical`, Iwahori-fixed case) from the spherical-place statements. |
| 4 | `coreAll_of_core` | `CrystallineInputs/CoreAllOfRowStarCore.lean` | extends from the restricted scope `.csd` to all CM fields. |
| 5 | `toCoreK up congPhi_holds descOffT (limFinOdd_of seed cong) : Core` | `CrystallineDescent/ToCoreK.lean` | `toCore (twoUpOK_of_k up)`. **This is the only use of `TLiftK`.** |
| 6 | `toCore`/`core_of_limU`/`rowCsd_of` | `CrystallineDescent/LimOddOfLimFinOdd.lean` | `joinGL_holds hD (joinAll_holds hT (joinU_holds hL))` plus Jacquet–Shalika, quadratic base change. `joinAll_of oneUs_holds subtractQ_holds` combines odd rank (`LimU`) with `TwoUpOK`. |

`Core` / `CoreAll` (`AbelianVarietyTheory/Definitions/GaloisGeometry/CyclicStrongAtCusp.lean:94,96`) **[stmt]**:
`Ex s ∧ ∀ c, SphericalLevelCondition s c`. `Ex s` (`…/GaloisGeometry/IsWeight.lean:70`) asserts, for π in scope
(`.csd`: E ∋ √−d, [E⁺:ℚ] even, E/E⁺ unramified, polarization χ = quadChar^a), the existence of r continuous with
`AttC ι r π`. The spherical conditions give Frobenius eigenvalues, de Rham, crystalline and φ at good places.

**The theta step (even rank)**:
- `TwoUp E n` (`ThetaParseval/SplitLineSubtraction/RowDefOfOdd.lean:98`) **[stmt]**: every automorphic U on U(n)
  has two lifts U₁, U₂ to U(n+t) with n+t odd (`IsUp`). Each satisfies Satake(Uᵢ) = Satake(U)·κ⁻¹ ⊞ (ψᵢ,1,…,ψᵢ,t)
  at split places (the `sat` field), with shifted weights, and ψ₁ i ≠ ψ₂ j for all i, j.
- `twoUpOK_of_steps` (`ThetaParseval/TwoUpOKOfSteps.lean`) **[proof]**: take t = 2(d₀+n)+1, choose character data
  with `chrPairs_holds`, and apply `TLiftK` twice (j = 0, 1). `upOf` then turns `IsLift` into `IsUp`.
- `Subtract` / `rowDef_of_odd` (same file as TwoUp) **[stmt]**: `RowAt` for all odd d plus `TwoUp E n` give `RowAt` for n.
  The proof (`subtractQ_holds`, `CoreAtQIffRowQ.lean:195`) is **unread**. By the shape it divides the characteristic
  polynomial of r_{U₁} by ∏(X−ψ₁ᵢ). The disjointness of ψ₁, ψ₂ identifies the common factor **[names/stmt shape]**.

**The odd-rank source** (`GlobalTheory.CongL`, `…/GaloisGeometry/LimWU4OfLimWU3.lean`) **[stmt]**:
- `SeedFinOdd = SeedWU4 Odd TyEll (GenOf DGen) WtLac`: for U' of a fixed local type `TyEll` at w₀ | l and with
  lacunary weights, there is a continuous semisimple r whose Frobenius characteristic polynomials match on a
  dense open set of Frobenii, with crystalline/de Rham/φ properties.
  It comes from `GeoOne` via `seedFinOdd_of_geoOne` (`ZetaCharacterDivisibility/MainFin.lean`).
- `GeoOne` (`GeometricFlagBases/HodgeTrAt.lean:79`) **[stmt]**: such U' has a representation ρ of some dimension dd
  with `VBase` (contains the expected eigen-system). This is built from a `Pack`: an `HTower` H plus an eigenvalue
  system θ, congruent to U' at almost all places (`CongFor`).
  - `HTower` (`AbelianVarietyTheory/Definitions/Divisors/IdTower.lean`) **[stmt]**: a scheme Z over the number
    field with correspondences Y_g ⇉ Z. `Nice` means smooth, projective, finite étale correspondences.
    `IsMat`/`piece` (`GeometricFlagBases/IsGrRefl.lean:52-63`) **[stmt]**: ρ is the Galois action on the
    simultaneous θ-eigenspace of the correspondences acting on total l-adic étale cohomology `Htot l` of Z_Ω.
    So this is **(c) cohomology of a variety defined in the project**.
  - `Cover`/`CongAt` (`IsGrRefl.lean:85-140`) **[stmt]**: a smooth projective integral model over O_w, a finite
    étale Galois cover, and `Cover.Cong` (via `crystallineComparison.PtId`, a point/Frobenius identity mod p). This is
    an Eichler–Shimura-type congruence relation **[names]**. `ESStep`, `CrysStep`, `JumpStep`, `PhiStep` (`HodgeTrAt.lean`)
    derive Frobenius eigenvalues, crystallinity, HT weights and φ.
  - `Plan` / `PlanEx` (`GeometricFlagBases/PackExOf.lean`) **[stmt]**: the variety is `T.tower N g` from a
    `KSAll` package for `Datum p`, `HTGroup p`, `Link`. `HTGroup` (`…/Divisors/IsCyclotomicExtensionQI.lean:395`)
    **[stmt]** is a central simple algebra C of rank n² over a CM field F with an involution of the second kind and
    signature (1,n−1) or (0,n) at each infinite place, i.e. a Harris–Taylor/Kottwitz PEL datum. The eigenform f on
    G(𝔸_f) must be congruent to U (`CongP`). The existence of such f is `planEx_holds :=
    exists_unitaryGroupDatum_of_vector_exponent_spectral vecEx_holds expOf_holds specTop_holds`
    (`PrimeLevelLocalization/SpecTopHolds.lean`). **Unread**: how f on the HT group is produced from U. This is the
    transfer step that classically needs a trace-formula comparison.
  - Hodge–Tate weights: `KSHodge`, from `LocalSmoothExtension.HolomorphicLefschetzFormula` =
    `GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence` (`GeometricFlagBases/WeightOneGeometricRealization.lean`).
- `CongFinOdd = CongUW4 …` **[stmt]**: for every U there is a level such that each Hecke eigen-system θ of U is a
  polynomial p-adic limit (`PolyApprox`) of eigen-systems of seed forms U' (type `TyEll`, weights `WtLac`,
  generic). This is **(a) congruences between forms**. It is proved from `wtLacEx_holds`
  (`WeightCharacters/LadicWeightEmbeddingOverPlace.lean:73`, a "family" construction) and `exists_ellType`.
  The proof is unread.
- `LimFinOdd` via `limWU4_of` (`TraceLimits/LimFinOddOf.lean`) **[proof skeleton]**: `exists_trace_limit` builds the
  limit trace function t, and `GlobalTheory.Cong.exists_limit_rep`
  (`AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLimitRep.lean`) **[proof]** finishes. It takes a
  locally-Cauchy extension, then `isPseudoCharacter_of_approximatedByTraces`, then
  `GlobalTheory.PsChar.exists_ssRep` (pseudo-character to semisimple representation), then continuity from the
  trace. This is **(b) a pseudo-character with Chebotarev density** ("dense range" of Frobenius).

Answer to "what is the source": (c) + (a) + (b). The base case is étale cohomology of Harris–Taylor-type PEL
Shimura varieties, which the archive builds itself (`CovMain.lean`: isogeny classes, quotient moduli objects,
Hecke correspondences). It is extended by congruences and pseudo-character limits. The theta lift reduces even n
to odd n. No CM/automorphic-induction base case and no Chenevier determinant appear on this path. The word used is
`PsChar`/`IsPsChar`.

## Q3. The chain

**Not on the `Row0b` path.** I found no chain, ⊞μ_j[t], or Chowla–Selberg in `GaloisRepresentations/`
(keyword grep: chowla 0, behrend 0, siegelmass 0 files).

On the VWin side:
- `GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains` (`Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IteratedLiftChains.lean`)
  **[stmt]** defines `inductive IsIterLift : ∀ k, (GA D (Yc D k) → ℂ) → Prop` (base: a cusp form in σ on Y₀; step:
  `fun h => ∫ g in 𝓕 k, th k g h Φ * u g`, a theta integral against an admissible lattice datum Φ). It also defines
  `liftSpace k` and `MeetsLift`. `NodeChainStatement D` says that for k < D.R.m, every cuspidal π on Y_k meeting the
  k-th iterated lift satisfies `Conclusion`. That is, at split places its Satake parameters divided by the step
  character `chrStep μ η (k+1)` avoid `excluded q t = {q^{±(t−1)/2}, q^{±(t+1)/2}}`. In other words, π does not contain
  the boundary of a t-dimensional Speh-type segment. Only 1 of the 20 declarations in this module is statically
  reachable. Its consumers are in `Proofs/TwistedOperators/NoExcludedParameterOfLiftParameters.lean` (2 of 5 reachable).
- `Formalism.BasicNotions.Ranks` (`Formalism/LocalRingCardinality/Params.lean`) **[stmt]**: k, m, t with m even ≥ 2,
  t odd, `rankY j = r + j·t` (each step adds a t-dimensional block, matching π ↦ π ⊞ μ_j[t]), `sigW j = (k+j−1, m−j)`,
  and m² ≤ k + m(t+1). `Formalism.L2.DIV.NumDatum` (`Formalism/LocalToGlobal/Divisibility/Numbers.lean`) **[stmt]**
  ties R to the window: host primes q, d, χ_d, `logDerivativeAtOne` = L'/L(1,χ_d), `lifts = Icc 1 m`, `eta = m·h0`,
  `B0 = f·m·b·x^ε`.
- **Choice of m**: `GlobalTheory.Mem.Num.mAt s := evenCeil (Real.sqrt (s.x * s.delta1))` with `delta1 = x^{−ε/8}`
  (`Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean`;
  `Formalism/LocalRingCardinality/DataParams₂.lean:45`) **[stmt]**. So m ≈ x^{1/2−ε/16}, i.e. "m like √X". The
  same file sets k ≈ x^{9/2+10ε} and n = 2^{e(x)} with 2^e ≈ x^{2+8ε} (the "page" of VWin). **Caveat**: this module
  has 0/38 reachable declarations (rule A), 1 (rule B). The reachable `Ranks` lemmas (`RankBoundMonotoneInDimension`)
  are generic in R. Other concrete instantiations (`HostFam.Rt`: m = 2; `SmallHostRootDiscriminantLe`: m = 2^α,
  2^119925) are unreachable. Whether the √x choice is on the compiled path is **open**.
- "What is won per step": I did not find a single statement saying "multiplicity m". The reachable consumer
  `GlobalTheory.KernelHalfS.kerSide_chainS` (`Proofs/DivisorProofs/KernelHalfChainNumbersAnyLevelPrime.lean:219`)
  **[stmt, skimmed]** bounds `KerSide … (FactorBounds (KerChain.ofCol …))` uniformly in the chain data, with
  per-index lemmas `log_eight_leS`/`log_nu_leS` for i < N.R.m. It cites `meanLogPeriod_chowlaSelberg`. The precise
  gained quantity (a divisibility order of a period) is **not established** by my reading.

## Q4. Named classical inputs

| input | where | role (as far as statements show) |
|---|---|---|
| Rallis inner product / doubling | `ThetaParseval/SchurStep.lean:142` `Rallis`; `ThetaKernels/TPGNonVan.lean` `nonVan_k`; `WeilBound/ThetaLifts/FrameEstimates/TowerRallisLemma` | non-vanishing of the stable-range lift in `TLiftK` (Row0b path). |
| Siegel–Weil | `PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_k` in `tools_holds_k` | identifies the doubling theta integral with an Eisenstein series (Row0b path). |
| Seesaw | `ThetaKernels/WeilPairGlobalCharacter*.lean` import `…/WeilDatumDoubleSpaceActsUnitScalarSeesawCM` | splitting/character compatibility of the Weil pair **[names]**. |
| Chowla–Selberg | `GlobalTheory.T.meanLogPeriod_chowlaSelberg : MeanPeriod` (`Proofs/DivisorProofs/MeanLogPeriodChowlaSelbergStatement.lean`), used in `kerSide_chainS` | mean of log periods of CM lattices in the chain-kernel bounds (VWin side, reachable). |
| Weyl | 69 files in `GaloisRepresentations/` mention "Weyl" (mostly Weyl group/character in `LefschetzSigmaSums`, `BlockDeterminants`) | not traced. |
| Siegel mass | 0 hits for `SiegelMass` in `GaloisRepresentations/`; 140 files elsewhere | not traced. |
| Bessel periods | 1 file in `GaloisRepresentations/` (`SeparatingAlgebras/HSPf.lean`); 3143 elsewhere | not traced. |
| Bost slope | 0 files contain `Bost` | absent by that name. |
| Behrend | 17 files, none statically reachable | off the proof path. |

## Q5. Hand-off to the analytic side

`UpperTheory.One.vwin_of_row h := automorphic_window_of_inputs (OpenImageCondition.mk h) baseChangeN h`
(`…/DenseThresholdCases/VwinOfRow.lean`) **[proof]**. Then `v_window_of_depth_zero_residual_bc_cm` (`TopMainZj.lean:55`)
builds `LiteratureRankNHypothesis` from four bundles (local, automorphic with `gal := h`, Galois cohomology, CM), and
`v_window_of_literal_automorphy_n` (`WindowBoundOfLiteratureLevel.lean:33`) runs `published_hypotheses_from_patching_alt`
(patching) to get `HypothesesH'`, then `vwin_of_hypotheses_H_E_alt`, then `UpperTheory.V.HV.Core.of_four_alt`
(`HVCore.lean:18`) **[proof]**:
```lean
obtain ⟨B, hB⟩ := Win.thmBab_of_lemmaK … FW.ferreroWashington hK
exact vwin_of_counts … hL (hB 401 _) (Odd.thmBcFree_of …) h1 h2 h3 h5 (countZ X.propZ)
```
`vwin_of_counts` (`AutomorphicVarieties/HeightAndVanishing/JointWinOfCounts.lean`) **[proof]** takes Poitou–Tate
duality, local finiteness and local Tate duality, `LemmaK`, `ThmBab` (via Ferrero–Washington), and `CountI`,
`CountII`, `CountIII`, `CountV`, `CountZ`.

**Where lengths are bounded** (`HeightAndVanishing/Counts.lean`) **[stmt]**. `CountI` bounds
Σ_{l∈Ls} log l · Σ_{ψ∈X} Vn(c l, e, ψ) ≤ (N·t)^C, with the length finite (`Vlen ≠ ⊤`), in "case I". `CountShape`
(cases II, III, V, Z) gives `VLe Ω c e ψ ((l·N·e)^C)` per ψ-isotypic piece. So the Ш¹ length is split by
character ψ and by case, and each piece is bounded polynomially in l·N·e.
- Case I: `count_i_of_printed_bound_k_kato_automorphy` (`LinkedUnlE.lean:49`): `KatoTwoW`, `oneCharU`, rigidity
  (`rigIUE_alt`, `rigII_a_alt` from `adjoint_lifting_of_cohomology`), and `numberU3U` **[names]**.
- Case V: `count_v_of_printed_bound_k_reduced_unitary_lift` (`:55`): `countV_of_finiteness_duality_euler_host`
  (finiteness, Poitou–Tate duality, Euler characteristic), `unitary_lift_of_reduced_core`,
  `residual_bernoulli_nonvanishing`, and host rigidity **[names]**.
- `Row0b` enters through `gal : RowT` inside `automorphic_inputs_from_literature`. Its consumers (vacuity-check.md Q4)
  are the U(3)/"unitary_three_automorphy" and modularity/Hida lemmas (`modularity_unitary_of_automorphy_hida_unitary`).
  **[names]** suggest a modularity-lifting (patching, adjoint-Selmer vanishing) plus Euler-characteristic argument
  over U(3)-type representations. I did not open these proofs. Nothing on this path is a Bost slope inequality.

## Q6. Unread (on the path)

- `UpperTheory.Gal.TP.subtractQ_holds` / `SubtractQ` (`ThetaParseval/CoreAtQIffRowQ.lean:195`), the character subtraction.
- `UpperTheory.Gal.Int.Div.seedFinOdd_of_geoOne` (`ZetaCharacterDivisibility/MainFin.lean`) and the ~40 `P*.lean` lemmas there.
- `planEx_holds` / `exists_unitaryGroupDatum_of_vector_exponent_spectral` and `UpperTheory.Gal.Spc.specTopG`
  (`ScalarCommutation/SpecTopG`), i.e. how a congruent eigenform on the HT group is produced.
- `KSAll` components (`CovMain.lean`, `FinModel.lean`): the Shimura-variety tower construction.
- `congFinOdd_of_ex`, `wtLacEx_holds` and its `fam*` lemmas (`WeightCharacters/`).
- `Row.galoisLocalGlobal_of_localGlobalCompatibility` (`InertCharpoly/…:192`), `coreAll_of_core`, `joinUp_holds`, `joinGL_holds`.
- `tLift_of_k`, `nonVan_k`, `datum_k`, `liftAut_k` (`ThetaKernels/TPG*.lean`), and the check that `TLift_k` ≡ `TLiftK`.
- VWin side: `published_hypotheses_from_patching_alt`, `thmBab_of_lemmaK`, all `Count*` proofs, `kerSide_chainS`
  in full, and `NoExcludedParameterOfLiftParameters`.

## What to read next

1. `ThetaParseval/CoreAtQIffRowQ.lean` (`SubtractQ`, `subtractQ_of`): confirm the even-rank subtraction.
2. `GeometricFlagBases/PrimeLevelLocalization/ExistsUnitaryGroupDatumOfVectorExponentSpectral.lean` and
   `ScalarCommutation/SpecTopG.lean`: the transfer to the Harris–Taylor group. This is the least classical-looking
   step and the place where a trace-formula comparison would be expected.
3. `GeometricFlagBases/CovMain.lean` + `FinModel.lean`: what `T.tower` is (moduli of abelian varieties with
   PEL structure?) and whether `Cover.Cong` is a genuine Eichler–Shimura relation.
4. `Development/AbelianVarietyTheory/Proofs/DivisorProofs/KernelHalfChainNumbersAnyLevelPrime.lean`
   (`kerSide_chainS`) and `Formalism/LocalToGlobal/Divisibility/Numbers.lean`: the reachable part of the theta chain.
   Find where `Ranks.m` is instantiated on the compiled path.
5. `AutomorphicVarieties/HeightAndVanishing/Counts.lean`, `JointWinOfCounts.lean`, and
   `…/DenseThresholdCases/LinkedUnlE.lean`: the Ш¹ bounds by case.
