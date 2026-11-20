# Frontier (g): three deep inputs — the trace comparison, residually Eisenstein modularity, Ferrero–Washington

Date: 2026-11-20. This is a read-only source study of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled or
run. About 85 ssh reads. This report continues `frontier-c-galois.md` (inputs I) and `frontier-d-window.md` (inputs II
and III).

Path abbreviations (relative to `src/`):
- `GR/` = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/`
- `ECD/` = `Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/`
- `DP/` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/`
- `PSS/` = `Development/AbelianVarietyTheory/Statements/PlaceShiftStatements/`
- `AV/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/`
- `DTC/` = `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/`

Tags:
- **S**: I read the statement.
- **P**: I read the proof.
- **P-skel**: I read the term, or the have/obtain skeleton, but not every line.
- **N**: inferred from declaration names or imports only.

One more convention applies throughout. Many deep facts are routed through `…Statement.lean` wrappers of the form
`first | exact @X.foo | …`. The real proof `X.foo` then sits in a sibling file without the `Statement` suffix. Where I
say "proved in F", I followed the wrapper to F.

## Overview

**(I) No Kottwitz-style point count over finite fields.** The comparison between the compact (1, n−1) Shimura variety
and the definite inner forms is made entirely over ℂ:
1. The fixed points of a Hecke correspondence on the complex points of the Kuga–Sato variety are put in bijection with
   group-theoretic data on G(ℚ) and the complex ball. This uses a complex uniformisation of the PEL moduli scheme by
   period lattices.
2. Each regular elliptic fixed-point class (a pair (β, γ)) is moved to a definite inner form. Multiplying the hermitian
   form by A(γ) ∈ F[γ] does this (`move_definite`). It needs an element of the totally real subfield with prescribed
   signs that is a local norm at every finite place. That element exists because n is odd and Hilbert reciprocity
   holds. A local adelic isometry commuting with γ then identifies the orbital terms.
3. The definite side is a finite-group trace identity.
4. Hodge cohomology is algebraic (Zariski) coherent cohomology of Ω^a. The Atiyah–Bott formula is proved
   *algebraically*: Noether normalisation, Čech cocycles and local parameters (Koszul complexes). It is not proved
   analytically.
5. The passage from Hodge cohomology to étale cohomology uses an in-archive ℓ-adic Hodge–Tate comparison for smooth
   projective varieties with good reduction. No Artin comparison and no singular cohomology are involved.

This is the Harris–Taylor "simple trace formula" special case. The test functions are regular elliptic at a finite
place, and the non-elliptic terms are killed by a supercuspidal type. Endoscopy, the boundary and stabilisation are all
sidestepped by the choice of test functions. The transfer is a classical but genuine argument. It is not an assumed
Jacquet–Langlands.

**(II) A genuine modularity-lifting statement, not a tautology.** "All type-I points are automorphic" is derived from
four pieces:
- a Hida-theoretic modular ideal J in a universal *ordinary determinant* (pseudo-deformation) ring over an auxiliary CM
  field;
- a Taylor–Wiles patching theorem (`PfromAut`): every irreducible component through a nice modular point is modular,
  and modularity propagates along chains of components linked through "thick" or "stable" primes;
- existence of automorphic seed points, built from adjoint lifts of GL2 forms congruent to Eisenstein series;
- descent.

This is the Skinner–Wiles / Thorne / Allen–Newton–Thorne strategy, formalised for general n and residually reducible
r. The ring is Galois-theoretic, so this is not "R defined from automorphic data", and it is not Row0b run in reverse.
`LemmaM`/`LemmaM'` are a graded-ring version of "cotangent length (≈ Selmer) ≤ congruence depth at the irreducible
points". This is closest to Bellaïche–Chenevier (reducibility ideal) combined with a Wiles/Lenstra-type numerical
inequality.

**(III) Ferrero–Washington via Sinnott.** It is formalised as bounded l-rank of Cl(K(μ_{l^n})) for abelian K ⊇ μ_l
(μ_4 if l = 2), for all n. l = 2 is included. The analytic-to-algebraic link is Stickelberger annihilation plus genus
theory plus Leopoldt reflection. No main conjecture and no class number formula are used. Sinnott's independence lemma
appears in a "measure/support" (Fourier-dual) form, about 280 lines in total. It is short, but it is the right
argument.

---

## (I) Fixed points of Hecke correspondences, definite inner forms, holomorphic Lefschetz

### I.1 Top-level statements

`ksHodge_of_geo` (`GR/LefschetzSigmaSums/KsHodgeOfGeo.lean:7`) **[P]**:
```lean
theorem ksHodge_of_geo (hW : HolomorphicLefschetzFormula) (hF : FixK) : KSHodge :=
  ksHodge_of_inputs hW hF UpperTheory.Gal.Cnt.weighted_count_definite_unitary UpperTheory.Gal.Cnt.trace_definite_forms_identity
```
So `KSHodge` (θ occurs in H^b(Ω^a) of the Kuga–Sato variety) follows from four inputs:
- **(a)** the holomorphic Lefschetz formula;
- **(b)** `FixK`: fixed points of a correspondence equal a group-theoretic count `cxTotalM`;
- **(c)** `MarkWeightedFixedPointEqDefinitePairOdd`: `cxTotalM` equals a sum over definite pairs;
- **(d)** `TraceDefinitePairsEqAutomorphicTrace`: that sum equals `dTrace`, the trace on forms of the definite inner
  forms.

The intermediate `HodgeTraceFromLefschetzAndGroupSide` (`GR/LefschetzSigmaSums/HodgeTraceFromLefschetzAndGroupSide.lean:~165`)
**[S]** has exactly this shape: `HolomorphicLefschetzFormula → KSProj → FixK → MarkWeighted… → TraceDefinite… → HodgeTr ∧ HodgeEig ∧ KSHodge`.
Here `HodgeTr` **[S]** reads
`altTr (hk f ∘ cutD c) y = dTrace G ξ K f · Σ_i y^{h_i}`, i.e. the alternating Hodge trace of a Good test function
(cut by a Kuga–Sato projector `cutD`) equals the definite trace times the Hodge-weight polynomial.

**`FixK`** (same file, `:125`) **[S]**. Take:
- G an HT group;
- v the unique infinite place with `sigPosH = 1`, i.e. signature (1, n−1);
- a Hecke element h whose double coset is supported on `RegAf` elements. `RegAf` means: at some finite place w ∤ p the
  commutant of g_w is commutative, i.e. g_w is regular;
- a Kuga–Sato "twist" α with every α_s nonzero and divisible by 2.

Then:
- the correspondence (tr_1, tr_h ≫ al_α) on the complex points of `T.X.Z` is finite étale;
- its fixed points form a finite set F with non-degenerate tangent matrices A_x (det(1−A_x) ≠ 0);
- Σ_{x∈F} lefTerm(A_x)(y) = [K_{N'} : K_N ∩ h…] · `cxTotalM` G v (cW L i₀ v α y) K_N (1_{K h⁻¹ K}) K_p 1.

**`cxTotalM`** (`PSS/MarkWeightedFixedPointEqDefinitePairOdd.lean:31`, built on
`Development/AbelianVarietyTheory/Definitions/Divisors/PointsNonemptyUnitaryRankOne.lean:13-145`) **[S]**. It is the
sum over three layers:
1. classes of forms β (`FCls`): symmetric β ∈ C^× that are trivial over A_f^p and over ℝ, up to similitude
   (Kottwitz's ker¹-type indexing);
2. points q ∈ `Pts` = grp(β) \ (G(A_f^p) × G_p × PosV)/K. Here `PosV` is the set of vectors of positive norm for the
   hermitian form gram_v·ψ_v(β⁻¹) of signature (1, n−1), up to ℂ^×, i.e. the complex ball;
3. y ∈ grp(β) fixing q up to K and having the ball point as an eigenline (`FixL`).

Each term is weighted by 1/|Stab| and by c(minpoly(y), eigenvalue of y on the line). So `cxTotalM` is the classical
"fixed points = Σ over γ ∈ G(ℚ) of orbital terms × local contribution at the fixed point of γ on the ball".

**`MarkWeightedFixedPointEqDefinitePairOdd`** (`PSS/…:50`) **[S]**. Assume:
- G.a = 1 and n odd;
- f is a test function supported on `RegAf`;
- every "marked" pair whose characteristic polynomial is *not irreducible* has vanishing term. This is supplied from
  the cuspidal type; see `vanPairs` in frontier-c Q3.

Then `cxTotalM G v c … = dSumIrr G (rootSum G v c) …`, a sum over classes of *definite pairs* (β′ definite at every
infinite place, γ regular with irreducible char. poly), weighted by the sum over all roots at v.

**`TraceDefinitePairsEqAutomorphicTrace`** (`PSS/TraceDefinitePairsEqAutomorphicTrace.lean:87`) **[S]**:
`dSumIrr G wt … = dTrace G ξ …`. It holds when:
- tr ξ(y) = wt(minpoly y) on regular elements (Weyl character formula, `IsWt`);
- f and f′ are bi-invariant;
- orbital integrals of non-`RegIrr` elements vanish.

Here `dTrace` = Σ over definite classes B (`DFCls`, `DForm` with `posR`: positive definite at v, negative definite at
the other infinite places, trivial over A_f^p) of the trace of the Hecke operator on
`forms(B) = {φ : G(A_f)×G_p → V | φ(γ g) = ξ(γ)φ(g), right K-invariant}`. These are the algebraic modular forms of
the definite inner forms grp(B).

### I.2 Proof skeleton, two levels down

- **(d)** `GlobalTheory.LKDef.trace_definite_forms_identity` (`DP/LieModelBaseChangeMap.lean:14`) **[P]**. It is a
  finite rewrite:
  - `bi_invariant_test_function_sum`;
  - `heckeTrace_definiteForm_eq_sum_conjClasses`: the trace on a finite double-coset space equals the sum over
    conjugacy classes of orbital sums;
  - `centSum_eq_zero_of_orbitalIntegral_eq_zero` (each via a `…Statement` wrapper; **N** below).

  This is the trace formula for a *compact* (definite) group, which is elementary. Each of the three helper files is
  ~20 lines plus its implementation.
- **(c)** `markWeightedFixedPoint_definitePair_odd_of_counts` (`DP/MarkWeightedFixedPointDefinitePairOddOfCounts.lean:32`,
  113 lines) **[P]**. Its inputs are `MoveDefInv`, `CxCountRegMark` and `FinitelyManyMarkedClassesTermDegreeOne`. The
  steps:
  1. Rewrite `cxTotalM` as `markSumC`, a sum over marked pairs (β, γ, μ) with μ an eigenvalue of γ at v on a
     *positive* vector. This is `UpperTheory.Cb.complex_count_regular_marked_points`
     (`ECD/ComplexCountRegularMarkedPoints.lean`, 571 lines) **[S; body N]**. It is a group-theoretic regrouping of
     the fixed-point sum by conjugacy class.
  2. Enumerate roots via `sel i`. For each root choice, move to definite pairs
     (`marked_field_pairs_sum_eq_definite_pairs_sum`, `DP/MarkedFieldPairsSumEqDefinitePairsSum.lean:11`).
- **The transfer itself.** `GlobalTheory.LKDef.cls_equiv_dcls_irr` (`DP/MarkedFieldPairsEquivDefiniteFieldPairsOdd.lean:81`,
  187 lines) **[P]**. It gives an explicit bijection
  {classes of marked pairs with irreducible char. poly} ≃ {classes of definite pairs with irreducible char. poly}.
  The bijection preserves the char. poly and preserves `term` (the adelic orbital sum `pointSum` over
  centraliser \ (G(A_f^p) × G_p)/K). The two ingredients:
  - `exists_polynomial_move_definiteSimilitudePair_marked` = `GlobalTheory.LKDef.move_definite`
    (`DP/ExistsPolynomialMoveDefiniteSimilitudePairMarked.lean:750`, 779 lines) **[S, P-skel]**. For G.a = 1, n odd
    and an irreducible P₀ with root μ at v, there is a polynomial A such that β ↦ A(γ)·β turns every definite pair
    (β, γ) into a marked pair (signature (1, n−1) with μ on a positive eigenvector) and back. The same u ∈ (A_f^p ⊗ C)^×
    commutes with γ and carries β to A(γ)β. Its inputs (all **S**):
    - `exists_totallyReal_even_neg_places_local_norm` = `NormSign.exists_neg_even_norm_away`
      (`DP/ExistsTotallyRealEvenNegPlacesLocalNorm.lean`, 128 lines). For a CM field M = F[γ] and a conjugation-stable
      set S of complex embeddings with 4 | |S|, there is a ∈ M⁺ that is negative exactly on S and is a norm from
      A_f^p ⊗ M. It is proved by induction on S from `exists_realSubfield_negative_twoPlaces_normEverywhere`
      (152 lines), which uses `QuadSymbol.normGroup`, `ExistsGlobalIffEtaProd` and finite-adele approximation. The
      evenness is Hilbert reciprocity. Here |S| = 2(n−1) is divisible by 4 because n is odd. **This is exactly where
      `Odd n` is used.**
    - `exists_adelicUnit_carrying_form_to_normMultiple` (`adelic_norm_move`, 41 lines): a local norm gives an adelic
      isometry commuting with M.
    - The real-place sign bookkeeping: `dreal_move`, `real_back`, `core` (lines 443–750).
  - `kottwitzTerm_eq_definitePair_of_local_isometry` = `LKDefTerm.term_eq_of_local_isom`
    (`DP/KottwitzTermEqDefinitePairOfLocalIsometry.lean:185`, 201 lines) **[S]**. If P and Q share γ and c, and the
    forms are adelically isometric via u commuting with γ, then `P.term = Q.term`. The centraliser tori are the same
    torus inside both inner forms, and only the finite-adelic conjugation matters.

  So the "Jacquet–Langlands-type transfer" is the classical fact that a regular elliptic γ (centraliser a CM torus
  F[γ]^×) lies in every inner form that is locally isomorphic at finite places. The archive constructs the needed
  inner form explicitly by changing the hermitian form within F[γ]. "The finite adèles of the two groups are
  identified" is literally the `Triv G (AfP p) β x t` condition carried by every `Form`/`DForm`.
- **(b)** `FixK_holds` = `tower_fixed_points_of_isogeny_data` (`GR/IsogenyEtaleTranslation/TranslationFiniteEtaleOfIsogenyData.lean:24`)
  **[P]**. It is `bridge_of (translation_finite_etale…) … W2.fixedPoints_int_base_holds W2.FixZ_holds`.
  - The core is `W2.HeckeFixedPointCMCycleClass` (`GR/SphericalCoordinates/HeckeFixedPointCMCycleClass.lean:~108`)
    **[S]**: the same identity at the level of `GenModel`, with `cxTotalM` weighted by `wtFix`.
  - It is proved by `fixedPoints_integral_base_of_uniformisation` from about 70 `…_holds` lemmas
    (`GR/SphericalCoordinates/FixedPointsIntBaseHolds.lean:256`) **[P-skel]**. Among them:
    - `GUnif`: the complex points of the generic fibre have a `Unif`ormisation by polarized O-lattices with periods;
    - `UnifG` **[S]**: a bijection Φ : complex points ≃ `AllPts G v K K_p` (the double-coset/ball description, over
      all `FCls`);
    - `StabTriv` (stabilisers are trivial at level N ≥ 3);
    - `FixFwd`, `FixGa`, `FixEq`: a fixed point corresponds to y with an eigenline;
    - `FixLoc` / `TanExists`: the local tangent matrix at a fixed point is given by eigenvalue data, giving
      `lefTerm = wtFix`.
  - `GUnif` rests on `ModelEx_holds := model_nonempty`, `GenPts := complexModel_points_of_genericFiber_embedding` and
    `GFine`. Behind these sits the Siegel/theta-uniformisation construction that frontier-c Q7.4 left unread.
  - Size: `GR/SphericalCoordinates/` has 147 files, 16,605 lines. `GR/IsogenyEtaleTranslation/` has 18 files,
    1,289 lines.
- **(a)** `UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence` (`ECD/LefschetzFixedPointFiniteEtaleCorrespondence.lean:255`,
  358 lines) **[P-skel]**. It reduces to integral clopen pieces (`exists_integral_clopen_decomposition_of_smooth`,
  `fixed_part`) and then to `holomorphic_lefschetz_finiteEtale_integral` (`ECD/HolomorphicLefschetzFiniteEtaleIntegral.lean:74`,
  245 lines) **[P-skel]**. That proof is entirely algebraic:
  - `exists_finiteCover_projSpace_reduced_fibre_origin`: a finite map to projective space with reduced fibre at the
    origin;
  - `exists_hodge_cohomology_equiv_cech_differentials`: H^b(Ω^a) via a Čech complex on the affine cover;
  - `etaleCorrespondence_{complexPoints,differentials,local_parameters,sections,family}_statement`;
  - `exists_regular_parameters_of_reduced_quotient`;
  - the core local computation `UpperTheory.Cb.exists_chart_lift_of_finite_cover`
    (`ECD/ExistsChartLiftOfFiniteCover.lean:199`, 223 lines). It imports about 20 `GR/LocalMaximality/` files
    (Koszul action, edge maps, cube signs, CRT for finite covers). `GR/LocalMaximality/` has 100 files, 16.5k lines.

  `hodgeH s j q := coh (Omega s j) q` (`Development/AbelianVarietyTheory/Definitions/GaloisGeometry/CoeEqAlgebraMapZeroEquiv.lean:50`)
  **[S]**: sheaf cohomology of the sheafified algebraic j-forms on the scheme. So "Atiyah–Bott" here is an algebraic
  Woods-Hole-type trace formula for coherent cohomology, for *finite étale* correspondences with simple fixed points.
  This is a reasonable special case that avoids analytic Dolbeault theory. `ECD/` has 83 files, 14,457 lines.

### I.3 Hodge to étale

frontier-c records `JumpStep := G3.jumpStep_of Seam.HT.htSpecGood Seam.crysStep_holds repEx_holds`.
`Seam.HT.htSpecGood` (`GR/CrystallineTowers/ClosedHT.lean:21`) **[P one line]** is
`Spec.htSpecGood_of htBij hodge_iso_natural_cech etFin_holds`, with `hodgeTate_comparison_smooth_projective := hodgeTate_of_etale_side etSideS`.

`HTSpecGood` (`Development/WeilBound/CoreStatements/PadicHodgeComparison/…/HTSpecGood.lean:15`) **[S]**: for smooth
projective models over the ring of integers of a finite extension of ℚ_ℓ, there are compatible Hodge–Tate period
matrices relating étale cohomology and Hodge cohomology, natural in morphisms. That is a **Faltings-style Hodge–Tate
decomposition for good reduction**. It lives in `Development/WeilBound/CoreStatements/PadicHodgeComparison/` (538 files,
50,512 lines; proof unread).

The ℂ-side Hodge cohomology reaches the ℓ-adic side through algebraic base change: `KSBc` and the field embedding
τ : R → ℂ. Hodge cohomology is algebraic, so no Artin (étale ↔ singular) comparison and no analytic Hodge decomposition
are needed **[S for KSBc; N for the exact transport]**.

### I.4 Assessment (I)

**What is classical.** The classical proofs (Kottwitz 1992; Harris–Taylor) count points over F_q and compare with a
twisted trace formula. The archive instead:
1. computes the Hecke *Lefschetz number* on Hodge cohomology over ℂ;
2. turns fixed points into elliptic G(ℚ)-classes by complex uniformisation;
3. transfers each regular elliptic class to a definite inner form by an explicit hermitian-form change;
4. takes Frobenius information from the separate Eichler–Shimura relation (frontier-c Q2).

**Strength.**
- It is a special case that avoids the hard part *legitimately*. Only regular elliptic test functions are used, and
  the non-elliptic and reducible-char.-poly contributions are killed by the supercuspidal type (hypothesis `h0`).
  There is no stabilisation, no endoscopy and no boundary.
- n must be odd and the HT group must have signature (1, n−1) at exactly one place. This matches the `SeedFinOdd`
  scope.
- The transfer argument is mathematically sound in shape (**P** at the bijection level).

**What remains unread.**
- the body of `complex_count_regular_marked_points` (571 lines);
- the uniformisation layer (`UnifG`, `GUnif`, and below them the Siegel/theta construction);
- the core local computation `exists_chart_lift_of_finite_cover`;
- the Hodge–Tate comparison.

A subtle point to check by hand is the matching of `lefTerm(A_x)` with `wtFix`/`cW`: the tangent action of y on the
ball times the Kuga–Sato fibre directions, against the Weyl character. This is `FixLoc_holds` (inputs `CspDim`,
`EigTop`, `LocSum`, `CorrChart`) and is unread **[N]**.

---

## (II) Modularity of residually Eisenstein U(3) points; `LemmaM`/`LemmaM'`

### II.1 The deformation ring and its points

`UpperTheory.V.U3.Dat` (`AV/UnitaryThreeGroups/RhoKApply.lean:16`) **[S]** contains:
- the imaginary-quadratic/CM field K with η : G_ℚ → {±1} (η.ker = G_K);
- a complex conjugation cc;
- an embedding ι : G_{ℚ_l} → G_ℚ;
- Ψ = χ_cyc^e·ψ, continuous, with Ψ|_{I_l} = cyc^e·ψ_l.

The ring is `D.Ring U g₁ := SRing D.Kill D.ι_cont U (D.loc.It U) D.cc g₁` **[S]**. It is a normalised (`Marked g₁`,
`Normalised cc g₁`) deformation ring of representations r : G_ℚ → GG 3 with:
- **the 𝒢₃-valued form.** GG 3 is the group-scheme form: a pair (matrix, sign) with multiplier η (`HasMult`), i.e.
  the C-group form of U(3).
- **the residual representation.** It is `r0 η Ψ g = ⟨tor(Ψ g), η g⟩` (`AV/UnitaryThreeGroups/UnitaryThreeReflectionRight.lean:291`)
  **[S]**: the diagonal torus element attached to Ψ. That is ψ ⊕ 1 ⊕ ψ⁻¹ after twisting, as frontier-d says.
- **the local conditions.**
  - Away from l: r is trivial on `Kill` (inertia at l-prime places where the residual representation is trivial).
  - At l: the point comes from the universal local ring U modulo the ideal `D.loc.It U` (`Loc.Dat3`). Its exact
    meaning is **N**. Elsewhere the "point" conditions are `OrdPt.ord : CondT` on the decomposition group at l, an
    ordinary/flag condition with the characters Ψ.

**Type-I and type-II points** (`AV/UnitaryThreeGroups/BaseRepGL3NormalisedOfPsiEqOne.lean:20,30`) **[S]**:
- `TypeI η r` = `MatIrr η.ker (mats r)`, i.e. r|_{G_K} is irreducible;
- `TypeII` = block-diagonal 2+1 shape with an irreducible 2×2 corner.

**What "automorphic" means.** `IsAutI ι r` = `Af.IsAutCsd ι (ρ_K ⊗ cyc⁻¹)` (`RhoKApply.lean:88`) **[S]**: there is a
regular algebraic conjugate-self-dual cuspidal automorphic representation of GL3(A_K) whose ι-Galois representation is
ρ_K ⊗ cyc⁻¹.

### II.2 What is assumed and what is proved

`AutomorphyUnramifiedCoefficientsAlt` (`DTC/AutomorphyUnramifiedCoefficients.lean:23`) **[S]**: for every `Dat` with
unramified coefficients (eO = 1) there is a marking g₁ with three properties:
- `FinA` (finiteness);
- `AutBAlt`: every Q̄_l-point ξ of the (trace-generated) ring `entAlg c.O S.r.hom` whose r is **type I** is `IsAutIAlt`,
  i.e. automorphic;
- `LemWAlt`: every **type-II** point has its 2-dimensional piece W modular (a newform of weight 2e+1).

It is proved by `automorphyUnramified_of_locPrints_kisin_gdEnd : LocalPublishedTheorems → GdEndAlt → …`
(`DTC/AutomorphyU3OfEndoscopy.lean:27`) **[P]**. Each point is conjugated into an `OrdPt` over a finite DVR A
(`exists_ordPt_of_point`), and then the clause `AutEnd3Alt` of `GdEndAlt` is applied.

`AutEnd3Alt` (`DTC/AutEnd3AltAlt.lean`) **[S]**: every A-valued r : G_ℚ → GG3(A) with three properties is automorphic
(`IsAutCsdA`). The properties are:
- `OrdPt` (`AV/CurveDVRSpecialization/RatTorsionFree.lean:21`): residually r0, continuous, normalised, unramified
  where the residual representation is, ordinary at the place B | l;
- irreducible on every open subgroup of G_K.

So the statement is: **every ordinary, strongly irreducible characteristic-zero lift of the Eisenstein residual
representation is automorphic.** That is a residually reducible ordinary modularity-lifting theorem for
U(3)/GL3 over CM K.

How `GdEndAlt` is proved (`ends_u_alt`, `DTC/DnEnds.lean:40`) **[P-skel]**:
`gdEnd_of_frame_linkedEnd_downCsdK_descent` takes local inertia/flag lemmas and `ends_rank_three_of_local'`
(`LinkedUnlE`), together with these inputs:
- **(i) `LinkedEndEAlt`**, from `linked_endomorphism_dense` (`DTC/LinkedEndE.lean:18`, 68 lines) **[S, P-skel]**. After
  base change to an auxiliary CM field L with a `Frame` Φ (`GalLink`), points are automorphic (`AutPtAlt k 3`). Its
  inputs (each **S**):
  - `ModUAlt` (`DTC/PointTheoremBaseObject.lean:44`). For the **universal ordinary determinant ring** B of *any*
    residual n-dimensional pseudo-representation r over L, there is an ideal J with these properties:
    - `Dense`: classical points are dense in B/J;
    - `PointTheoremBaseObject`: automorphic ordinary points lie in V(J), for n ≤ 4;
    - `arithmeticPointClassicality`: irreducible arithmetic points in V(J) are automorphic;
    - `TwistOk`;
    - `P1core` and `P3core` (`AV/WeilGroupCharacters/UniversalOrdinaryDeterminantRing.lean:284,293`):
      - `P1core`: if a "NiceI" point is modular (J ≤ ker f), then every prime q ⊆ ker f contains J. In other words,
        every irreducible component through a nice modular point is modular.
      - `P3core`: modularity propagates along a chain of points x₀ … x_h whose consecutive points share a "thick"
        prime, starting from a "stable" modular prime.

    `ModUAlt` is obtained from `HidaUAlt` (Hida theory: J with these properties plus `HasAut`) and **`PfromAut`**.
  - `PfromAut` (`AV/PatchingModules/TaylorWilesObstructionBound.lean:150`) **[S]**: `HasAut B J → B.P1core J ∧ B.P3core J`.
    It is proved by `pFromAut := pFromAut_of norm choice arPl b1Ar b2Ar raw` (`AV/PatchingModules/AutomorphicDetection/PfromAut.lean:9`,
    `ChebotarevFamilies/PFromAutOf.lean:116`) **[P-skel]**. Its inputs are Taylor–Wiles groups `TWGrp`, patched
    automorphic data `TWAut`, `TaylorWilesObstructionBound` and `FirstOrderDualArithmeticBound`. **This is Taylor–Wiles
    patching for pseudo-deformation rings.** `AV/PatchingModules/` has 441 files, 50,353 lines.
  - `UnitaryThreeAutomorphyDense` (`DTC/SymUse.lean:27`) **[S]**, which supplies seeds. For arbitrarily large
    m ≡ j (mod l−1) there is an automorphic, open-irreducible 3-dimensional r over L with residual
    (cyc^j χ′, 1, (cyc^j χ′)⁻¹) and weights (m, 0, −m). It is proved by `adjoint_lift_from_eisenstein_of_propagation`,
    `seedInW_alt` and `adjoint_automorphy_w_of_printed_hida_window` (`DTC/UnitaryThreeInputsOfLiterature.lean`)
    **[P one line]**. These are adjoint (Gelbart–Jacquet) lifts of GL2 Hida-family forms congruent to Eisenstein
    series.
  - `Seed2Alt` (`DTC/SdStmt.lean:14`): the GL2 analogue.
- **(ii) descent.** `downCsdK_of_printsH`, `rankTwoAutomorphyDescends_of_printsH`, `GalRepDescentAlongQuadraticExtension`
  (**N**): from L back to K.

**What the claim rests on.** "All type-I points are automorphic" rests on:
1. Hida theory for unitary groups (`HidaUAlt`; where it is proved is **undetermined**, since I did not trace the
   theorem inhabiting it);
2. a patching theorem for universal ordinary determinant rings in the residually reducible case (`PfromAut`, in-archive);
3. the seed construction (adjoint lifts of Eisenstein-congruent GL2 Hida forms);
4. the linking argument (`twoRuns_alt`, `seedPtOf_alt`, `DTC/TwoRuns.lean:80`, `DTC/PrSeedPtOf.lean:255`; **N**). This
   argument guarantees that every relevant component meets a seed or is linked to one.

Size: `DTC/` has 532 files, 49,736 lines. `AV/ModularityArgument/` has 2,515 files.

**Is it R = T, a tautology, or Row0b reversed?**
- It is a genuine R^red = T-on-components statement for characteristic-zero points. The ring is Galois-theoretic: a
  framed or determinant deformation ring with local conditions. It is not defined from automorphic data. The
  automorphy of points is *derived* via Hida theory, patching and linking.
- Row0b (automorphic → Galois) is used only to attach ρ to automorphic forms: `Adm3U`, local–global compatibility,
  `rowOf'`. It is not run in reverse.
- The strategy is that of Skinner–Wiles, Thorne (JAMS 2015) and Allen–Newton–Thorne. The formalised `PfromAut` is
  stated for **all n ≥ 1 and arbitrary residual pseudo-representations** over CM L (with an "ε nontrivial mod l"
  condition, `LocCFT`, `CohP`). In the published literature such statements require extra hypotheses: the shape of
  ρ̄, Schur or "nice" conditions, and n = 2 in ANT. The archive's "Nice"/"thick"/"stable" predicates may encode these
  hypotheses. I did not verify that they are faithful. **This is the single place in (II) most worth an expert's
  time.**

### II.3 `LemmaM` and `LemmaM'`

`AV/CommutativeAlgebra/OrbitVanishingLocal.lean:111,120` **[S]**.

**`LemmaM`.** The setting:
- O is a complete DVR of characteristic 0, K is algebraically closed, and v is a normalised valuation on K;
- A is a ℤ-graded O-algebra. Here the grading is the weight decomposition under conjugation by the diagonal torus
  t ↦ diag(t, 1, t⁻¹), so entries above or below the diagonal have weight ±1, ±2;
- 𝒜₀ is complete Noetherian (`IsWRing`), and A is generated by 𝒜₀ plus finitely many elements of degree ±1, ±2;
- x : A → O is the reducible base point. It kills every nonzero degree.

The ideal I is generated by "equations" F (degree −1), G (−2), E (1), E′ (2) and Z (degree 0, x(Z) = 0). The
hypotheses:
- **M1**: x is a smooth point of the ambient algebra with r, s, r′+1, s′+1, m generators in degrees −1, −2, 1, 2, 0, and
  F, G, Z span the corresponding cotangent pieces;
- **M2**: 𝒜₀/I is finitely generated;
- **M3**: a one-sidedness condition at reducible points other than x;
- **M4**: at each two-signed point, the I-tangent space is at most 1-dimensional modulo scaling (unobstructedness or
  rigidity);
- **M5**: a ∈ 𝒜₀ with x(a) = 0 that does not vanish at any two-signed point of V(I).

The conclusion:
- a finite set T of two-signed points covering V(I) up to torus orbits exists;
- the degree −1 cotangent length `cotLen x 𝒜 (-1) F` is finite;
- for every such T, `cotLen ≤ 2·Σ_{ξ∈T} v(ξ(a))`.

**`LemmaM'`.** Let D : M ↪ (A → O/c) send each μ to a weight-j point derivation at x, killing F. Then
`length_O M ≤ cotLen x 𝒜 j F`. This is the algebraic form of "Selmer group ↪ tangent space of the weight-j piece".

**How they are used** (`FOneCharU.lean`, `oneChar_unramU`) **[P]**:
- the two-signed points of V(I) are exactly the type-I and type-II points (`twoPt_shape`);
- a = the trace difference tr ρ(σ) − (Ψ(σ) + 1 + Ψ(σ)⁻¹) (`trDiff`);
- `model_upper` applies `LemmaM`, and `vlen_le` applies `LemmaM'` with M the ψ-part of the Ш/Selmer group.

The result is Vn ≤ 2·Σ_{ρ∈X} v(tr ρ(σ) − t).

**Which classical criterion this resembles.** It is closest to **Bellaïche–Chenevier**, *Families of Galois
representations and Selmer groups*, §1.5–1.8: the reducibility ideal and the bound of Ext/Selmer groups by
length(O/I_red). There, the generic "two-sided" points are the irreducible ones and the factor 2 comes from the B·C
pairing. It combines this with a **Wiles/Lenstra numerical-criterion-style** inequality. Here the "congruence module"
is replaced by Σ v(ξ(a)) over the finitely many irreducible points. This is the Eisenstein-ideal measure of Mazur
(length of T/I_Eis), read at one Frobenius. It is not Diamond's freeness criterion.

Proofs: `Alg.M.main_holds` (`AV/CommutativeAlgebra/GradedModulesLength/MainCotSpan.lean:32`, 70 lines plus helpers)
and `mprime_holds` (`Mprime.lean:38`, 80 lines) are short top-level proofs **[P-skel]**.
`AV/CommutativeAlgebra/GradedModulesLength/` has 50 files, 6,625 lines. These are plausible, self-contained commutative
algebra, and much less of a risk than II.2.

### II.4 Assessment (II)

The input is what its name says: a modularity statement for all ordinary irreducible points of a residually
Eisenstein deformation ring. It is derived by a modern R = T strategy whose top-level components are all proved
in-archive. It is not weaker than its name. Whether it is *correct* depends on two places:
1. the patching theorem `PfromAut` for residually reducible pseudo-deformation rings in general dimension, which is at
   or beyond the published frontier;
2. the linking/seed argument that every component is reached.

Both are unread below the top level.

---

## (III) Ferrero–Washington via Sinnott

### III.1 Statement

`UpperTheory.V.Published.FerreroWashington` (`AV/PublishedTheorems/FerreroWashington.lean:7`) **[S]**:
```lean
∀ l [Prime] K [NumberField] [IsAbelianGalois ℚ K], (∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l)) →
  ∃ r, ∀ n K' [IsCyclotomicExtension {l^n} K K'], #(Cl(K') / Cl(K')^l) ≤ l^r
```
In words: for abelian K containing μ_l (μ_4 if l = 2), the l-rank of the class group is bounded up the cyclotomic
tower K(μ_{l^n}). By Iwasawa's structure theory this is equivalent to μ = 0 for the cyclotomic ℤ_l-extension. The
equivalence itself is not formalised; the rank bound is what is used. **l = 2 is included.**

Proof: `FW.ferreroWashington` (`AV/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104`) **[P]**. It
embeds K in ℚ(μ_{f·l^m}) with f > 1 prime to l (`embed`) and descends the bound (`desc`). The case K = ℚ(μ_{f l^n}) is
`FW.cyc` (`:18`) **[P]**.

### III.2 Skeleton of `FW.cyc` (each lemma **S**; bodies P-skel where noted)

1. **`memZ`** (`ToKOf.lean:13`). There are N and n₀ such that for n ≥ n₀ there is a γ ≡ 1 + f·l^e generating the
   l-part of the Galois group with
   (γ − 1)^N ∈ (θ_H, 1 + [−1], l) in ℤ[(ℤ/f l^n)^×].
   Here θ_H = Σ_{s < M/2} gc(M,c,s)·[s] is the c-smoothed half Stickelberger element (`TwSingle.lean:44`). In Λ-adic
   language: on the minus part, the Stickelberger element is ≢ 0 mod l in every character branch, so it is a unit
   times T^λ mod l. **This is "analytic μ = 0".** It comes from `nonvan` (`Nonvan.lean:12`, 60 lines): for every odd
   character χ with values in a field of characteristic l, the χ-twisted projection of θ_H at level n₀ is nonzero for
   n ≥ n₀. That in turn uses `sinnott`.
2. **`sinnott`** (`Sinnott.lean:10`, 44 lines) **[P]**. Take η_i ∈ ℤ_l^× that are pairwise ℚ-independent
   (aη_i = bη_j ⇒ a = 0) and N ≠ 0. Then for n ≫ 0, any α : ℤ/l^n → k (k any commutative ring) satisfying both
   - α(y) − α(y − N) = P(y) supported on [0, N) (α is the distribution of a rational function with denominator
     1 − x^N), and
   - Σ_i α(η_i⁻¹ y) = 0

   forces P ≡ 0. The proof:
   - `sinSupp` (56 lines): the associated element `sinE` of k[ℤ_l] has finite support S;
   - `sep` (`SepPair.lean`, 25 lines): reduction mod l^n is injective on S for n ≥ n₀;
   - `sinFin` (64 lines) and `sinMap` (10 lines): the finite-level hypothesis kills the image;
   - so `sinE = 0`;
   - `sinLem` (`SinLem.lean:18`, 78 lines): if the dilations η_i are pairwise ℤ-independent and torsion-free, the
     supports ℤη_i cannot cancel, so P = 0.

   This is a Fourier-dual form of **Sinnott's independence lemma** (Sinnott 1984; Washington §16.2): Σ R((1+T)^{η_i})
   cannot be trivial for ℚ-independent η_i. Sinnott's pole argument becomes a support argument for distributions on
   ℤ_l. **No normal-number or equidistribution input** (the original Ferrero–Washington method) appears anywhere. The
   ℚ-independent representatives come from `reps` (**N**).
3. **`stickH`** (`StickH.lean:8`) **[S]**: θ_H·(1 − [−1]) acts as 0 on Cl(ℚ(μ_M)). This is Stickelberger's theorem,
   via `GaloisLibrary/StickelbergerTheorem/` (**N**; in-archive).
4. **`ambCyc`** (`AmbCyc.lean:9`, 75 lines) **[S]**: [Cl : Cl^l·(γ−1)Cl] ≤ B uniformly in n. This is genus theory /
   ambiguous classes in a cyclic l-extension, and it bounds the number of Λ-generators by Nakayama.
5. **`core`** (`CardRangeInfTorsionLeIndexPow.lean:64`) **[S]**. Pure group-ring algebra: if θ(1−J) acts as 0 and
   (γ−1)^N ∈ (θ, 1+J, l), then #((1−J)Cl ∩ Cl[l]) ≤ [Cl : Cl^l·(γ−1)Cl]^N. This bounds the minus-part l-rank.
6. **The plus part.**
   - For odd l: `reflOdd` (`ReflOdd.lean:30`, 113 lines). This is Leopoldt's Spiegelungssatz: l-rank(plus) ≤ 1 +
     l-rank(minus-ish), using ζ_l ∈ K.
   - For l = 2: `sgnCyc`/`pTwo` (2-rank of Cl ≤ (2-rank of (1−J)-part)·…, with the sign/unit index).

Size: `FerreroWashingtonIndex/` has 62 files, 4,672 lines. The Sinnott core (`Sinnott`, `SinLem`, `SinSupp`, `SepPair`,
`SinFin`, `SinMap`, `SinSign`, `Nonvan`) is about 365 lines.

### III.3 From analytic μ to algebraic μ

The link is proved, by the cheap classical route. It does **not** use the main conjecture or the class number formula
up the tower. Stickelberger annihilation (step 3) plus "Stickelberger ≢ 0 mod l up to T^N" (step 1) bound the minus
part, given a uniform bound on the number of generators (step 4, genus theory). Reflection (step 6) bounds the plus
part. This is exactly how μ = 0 for the minus part follows from μ = 0 of the Stickelberger/p-adic L-function element.
It is a one-sided inequality, and that is all μ = 0 needs.

### III.4 Assessment (III)

This is the full classical theorem for abelian K (with μ_l ⊆ K, which costs nothing because K(μ_l) is still abelian),
including l = 2, in its rank-bound form. The proof follows Sinnott's algebraic route faithfully at the level of
skeleton and statements. The short length is plausible: Sinnott's proof *is* short once Stickelberger, genus theory
and reflection are available.

Unread bodies:
- `memZ` (the passage from `nonvan` to the group-ring membership via `ToKOf`/`AlgK`/`Struct`);
- `reps`;
- the Stickelberger theorem directory.

---

## What to read next

1. **The (II) patching theorem.** Read `UpperTheory.V.Pa.pFromAut_of` and `chain_of`
   (`AV/PatchingModules/ChebotarevFamilies/PFromAutOf.lean`), `TaylorWilesObstructionBound`,
   `FirstOrderDualArithmeticBound` (`AV/PatchingModules/AutomorphicDetection/`), and the predicates
   `Point.NiceI/NiceE`, `IsThick`, `IsStable` (`AV/WeilGroupCharacters/UniversalOrdinaryDeterminantRing.lean`).
   Question: what residual hypotheses do they impose, compared with Thorne 2015 and ANT?
2. **The (II) linking argument.** Read `UpperTheory.Gal.projectedFormsSystemPart.twoRuns_alt` (`DTC/TwoRuns.lean:80`),
   `UpperTheory.V.Pr.seedPtOf_alt` (`DTC/PrSeedPtOf.lean:255`), and `gdEnd_of_frame_linkedEnd_downCsdK_descent`.
   Question: why does every ordinary type-I point lie on a component reached from a seed?
3. **Hida theory.** Find the theorem inhabiting `UpperTheory.V.W.HidaUAlt` (`DTC/HidaU.lean:12`), and read
   `arithmeticPointClassicalityDense` and `Dense`.
4. **(I) local terms.** Read `UpperTheory.Gal.W2.FixLoc_holds` and its inputs (`GR/SphericalCoordinates/`), plus
   `UpperTheory.Cb.complex_count_regular_marked_points` (`ECD/ComplexCountRegularMarkedPoints.lean`, 571 lines).
   Question: are the Lefschetz local terms correctly matched with Weyl characters (`wtFix`, `cW`, `IsWt`)?
5. **(I) uniformisation.** Read `UpperTheory.Gal.W2.unifG_of`, `gUnif_of` and `complexModel_points_of_genericFiber_embedding`.
   Question: is the bijection between complex points and `AllPts` (over all `FCls`) right, ker¹ included?
6. **(I) algebraic Atiyah–Bott core.** Read `UpperTheory.Cb.exists_chart_lift_of_finite_cover` (`ECD/ExistsChartLiftOfFiniteCover.lean:199`).
7. **(I) Hodge–Tate.** Read `CrystallineSemistableComparison.HT.hodgeTate_of_etale_side` and `Onto.htBij_of`
   (`Development/WeilBound/CoreStatements/PadicHodgeComparison/`).
8. **(III).** Read `UpperTheory.V.FW.memZ` (`ToKOf.lean`), `reps`, `reflOdd`, `ambCyc`, and
   `GaloisLibrary/StickelbergerTheorem/`.
