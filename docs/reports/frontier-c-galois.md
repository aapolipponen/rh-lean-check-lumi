# Frontier (c): the geometric source of the Galois representations in `Row0b`

Date: 2026-11-20. This is a read-only study of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled or run.
Paths are relative to `src`. `GFB/` abbreviates
`Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/`, and
`GR/` abbreviates `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/`.

Tags:
- **S**: I read the statement.
- **P**: I read the proof. "P-skel" means I read only the term or the have/obtain skeleton.
- **N**: inferred from declaration names or imports only.

This continues `analysis/theta-chain.md`, which you should read first.

## Overview (for a number theorist)

The geometric input is formalized, not assumed. `geoOne_holds` is a theorem. Its proof builds an actual PEL
moduli scheme, and the archive's own étale cohomology is applied to it.

- **The moduli scheme.** `GenModel` is a fine moduli scheme. It represents abelian schemes with an action of an
  order O, a polarization given as a line bundle on A×A with a Rosati condition, a Kottwitz-type Lie condition,
  and a level-N structure compatible with the Weil pairing.
- **Where the moduli scheme comes from.** Its existence is a chain of theorems that ends in Siegel moduli
  built with Mumford-style theta functions, plus the Zarhin trick.
- **The variety.** It is the k-fold Kuga–Sato fibre power of the universal abelian scheme over this moduli
  scheme. Hecke correspondences come from prime-to-p quasi-isogenies.
- **Cohomology.** ℓ-adic cohomology is defined in the archive. The coefficients are sheaves of ℤ/ℓᵏ-modules on
  Mathlib's big étale site, cohomology is taken through injective resolutions, and the result is a lim over k
  tensored with ℚ_ℓ. Proper base change and finiteness are proved in the archive.
- **Eichler–Shimura relation.** It is proved as a point identity at the generic (ordinary) points of the special
  fibre. On cohomology it becomes Σ_j(−1)^j q^{j(j−1)/2} T_j Frob^{n−j} = 0.
- **Transfer to the Shimura variety.** This is not an Arthur-style trace-formula comparison. A definite form
  becomes a test-function statement on the Harris–Taylor group:
  - The finite adèles of the two groups are identified (`Frame`).
  - A test function with a cuspidal type is regular elliptic.
  - Its "group-side trace" is a sum of traces on spaces of forms on the finitely many *definite* inner forms.
  - This sum is linked to Hodge cohomology H^b(Ω^a) of the compact Kuga–Sato variety by a *holomorphic
    Lefschetz (Atiyah–Bott) fixed-point formula* for finite étale correspondences.

  The step that matches fixed points with the group-side sum is the main piece I did not read.
- **Congruences.** They are made on the definite unitary group. Weights are interpolated ℓ-adically by moving
  the weight to a place v′ | ℓ (Serre/Gross/Chenevier style). The type at w₀ | ℓ is changed with characters of
  ℓ-power order.
- **The limit.** Crystallinity is obtained by matching weights. At every place above ℓ other than w₀, v′, the
  seeds have exactly the target's Hodge–Tate jumps. An in-archive closedness theorem (`closedAtL`, proved via
  Breuil–Kisin frames of bounded height) then passes "semistable/crystalline with jumps J" to the trace-limit.
- **Weak local–global compatibility.** It is derived from spherical-place data. Base change makes the local
  components unramified ("plain torus" / Iwahori-fixed cases), and jumps and characters are then descended.

## Q1. `geoOne_holds`, the variety and its cohomology

**Statement.** `GeoOne` (`GFB/HodgeTrAt.lean:79`) **[S]**, paraphrased: for a CM field E, ℓ, ι, odd a, an
auxiliary imaginary quadratic x = √−d (`FieldOK`), a nonsplit set T, two places w₀, v′ | ℓ with `Apart v' w₀`,
`OneK x w₀ v'`, and a form U on the definite unitary group `UA E a` such that
- U is automorphic off T,
- U has the type `TyEll` at w₀,
- U is spherical off w₀ and S,
- U has lacunary weight at v′ (`LacWtAt`),

there exist a dd and a continuous semisimple ρ : G_E → GL_dd(Q̄_ℓ) with `VBase` (`ZetaCharacterDivisibility/InsideRefl.lean:73`)
**[S]**: at almost all split unramified w the Hecke data of U satisfy `ESAt`, and `HTRichEx ρ a` holds.
Per place there are versions with `ESAt` at a given w ∤ ℓ, and `CrysAt` + `JumpsOcc` and `PhiKilled` at w | ℓ.
Note that dd is not a. The a-dimensional piece is cut out later, in `seedFinOdd_of_geoOne`
(`ZetaCharacterDivisibility/MainFin.lean`, by `divAll_holds`, `gapLac_of`, `dGenMul_of`), using the lacunary
weights **[P-skel, N for the mechanism]**.

**Proof outline** (`GFB/WeightOneGeometricRealization.lean`, `GeometricRealizationOfWeightOne.lean`,
`GeoOneOfParts.lean`, `PackExOf.lean`) **[P]**:
```lean
theorem geoOne_holds : GeoOne := geometric_realization_of_weight_one weight_one_geometric_realization
-- weight_one_geometric_realization := GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence
theorem geometric_realization_of_weight_one hW : GeoOne := geoOne_of_parts steps_holds (kodaira_spencer_of_weight_one hW) Pl.planEx_holds
theorem kodaira_spencer_of_weight_one hW : KSAll :=
  ⟨CovMain.stdEx_holds, G3.kSEx_holds, G3.kSNice_holds, FiniteEtaleModels.ksGood_holds, CovMain.ksCong_holds, ksHodge_of_geo hW FixZ.FixK_holds⟩
theorem geoOne_of_parts (h₁ : Steps) (h₂ : KSAll) (h₃ : PlanEx) : GeoOne := geoOne_of h₁ (packEx_of h₂ h₃)
```
- `PlanEx` gives a `Plan`, which consists of:
  - a prime p and a `Datum p`;
  - an `HTGroup p` G with a `Link`;
  - `Sc D G`, meaning `D.a = 1`, `D.m = 1`, `G.a = 1`, odd `G.n` and `D.CompactB`;
  - a level N and Hecke elements `g : J → Mem L N`;
  - eigenvalues θ;
  - an algebraic Hecke character κ;
  - a weight λ;
  - a test function f with `Spec L lam K ψ θ f`;
  - congruence to U at almost all places (`CongP`).
- `Plan.pack` (`PackExOf.lean:113`) **[P]** turns a Plan into a `Pack` whose variety is `T.tower N g`. Here
  `T : KS L gb k` comes from `KSEx`. Each `KSAll` field supplies one property: `Nice` (smooth, projective, finite
  étale correspondences), `GoodAtW`, `CongAtW` (the Eichler–Shimura data) and the Hodge occurrences (`KSHodge`).

**What the variety is** (`GFB/IntegOfMem.lean:48`) **[S]**:
```lean
structure KS (gb : GBase D.toG R) (k : ℕ) : Type 1 where
  X : G3.Tower (Sp R) G.GAf
  M : ∀ N : Lv p, GenModel gb N.1
  e : ∀ N, X.Z (lev N) ≅ (GlobalTheory.KS.pow (M N).univ.A k).left     -- k-fold fibre power of the universal abelian scheme
  tr_eq : ∀ N' N h a b, ∃ π o ψ φ hw, ... IsTrans L h (M N').univ o ψ ∧ X.tr ... = ... powMap π (ψ.left ≫ φ.φ) hw k
```
So each level of the tower is the Kuga–Sato variety over the moduli scheme `GenModel`. The Hecke maps `tr` are
induced by quasi-isogenies ψ, with prime-to-p degree, a polarization pullback c·P and a Tate-module condition
(`IsTrans`).

`GenModel` (`Development/AbelianVarietyTheory/Definitions/Divisors/ExistsGDatumOneOneOne.lean:181`) **[S]** is a
**fine moduli scheme**. `rep` asserts that any `GObj` over any S is a unique pullback of `univ`. A `GObj` is a
genuine PEL object:
- an abelian scheme A/S (`IsAbelianScheme`);
- an O-action;
- a line bundle P on A×A that is rigidified, symmetric and relatively ample;
- the Rosati condition `rosati`;
- a Kottwitz-type condition on Lie A (`lie`, `lieRank`);
- level-N points `eta`, which on geometric fibres are a Tate-module isomorphism compatible with the Weil
  pairing (`geom`).

`GDatum` contains a CM field F, an order O with an involution, a lattice La of rank m·n·[F:ℚ] with an
alternating form, and a complex structure J with the trace condition. In other words, it is a PEL datum.
- **[S]** `Sc` forces m = 1, so O is an order of F and the moduli problem is of unitary type.
- **[N]** With a = 1 it presumably has signature (1, n−1) at one embedding.

**Existence of the moduli scheme** (each step **[P]** at the one-line or skeleton level):
- `G3.pKSEx` (`GR/PAdicWittLattices/ExistsDeeperNormalLevel.lean:100`) builds the `Tower` explicitly from
  `unitaryCharZeroGenericModel_nonempty` and the `Wit*` lemmas.
- Next comes `genModel_nonempty`, then `harrisTaylorIntegralModel_nonempty`. The latter gives an integral `Model`
  over any Noetherian R with N ≥ 3, (N, p) = 1.
- `model_nonempty` (`Development/AbelianVarietyTheory/Proofs/DivisorProofs/HarrisTaylorIntegralModelNonempty.lean`)
  produces a quasi-projective representing family plus smoothness.
- `exists_repFam_qproj` uses the Zarhin trick and represents PEL inside the Siegel space at an auxiliary prime
  level M (`harrisTaylor_auxiliary_symplectic_level_representable`).
- `sdRep_of_coprime` goes through `exists_zarhinTrick_family_siegel_kernelKilled` and then
  `exists_rep_principalSiegel_adjoint_orderAction`.
- `exists_sFam_cycAway` goes through `exists_sFam_primePow_sq`, which uses `abelianSchemeLaws_all`,
  `SiegelArithFamily.nonempty_sFam`, `Moduli.cube_of_isLB` (theorem of the cube) and `thetaUnifAV_closed`
  ("theta uniformisation of complex abelian varieties").

I stopped there. The bottom of the Siegel construction is unread (see Q7).

**Smoothness and projectivity.** `KSNice` (`G3.kSNice_holds`) comes from `GenSm`/`PowSm`
(`PAdicWittLattices/TransCancel.lean:199`, **[S]**: smooth, separated, quasi-compact, and projective when
`D.CompactB`). Their proofs `pGenSm`/`pPowSm` are unread.

**Étale cohomology** **[S]**. It is the archive's own construction, not Mathlib's and not an axiomatized
"cohomology theory":
- `GlobalTheory.EtC.Shv R` = `Sheaf Scheme.etaleTopology (ModuleCat (ULift R))` (Mathlib's big étale site).
- `H E F n` = cohomology classes from the chains of the free sheaf on a simplicial presheaf E to the injective
  resolution of F (`Definitions/Divisors/GalMapMul.lean:105-129`). So for E = `sch.obj X` this is Ext^n(ℤ[h_X], F).
- `tw q i` is the Tate twist sheaf built from primitive q-th roots.
- `Hl` is the ℤ_ℓ-module of compatible systems over ℓ^k, and `HQ = ℚ_ℓ ⊗ Hl`. `Htot` is the direct sum over
  degrees (`Definitions/Divisors/PullHlComp.lean:205-239`, `IsCorrOpOfAvg.lean:11`).
- The Galois action is pullback along `galMap`.
- The Hecke operator `hop` is `if ∃ T, IsCorrOp … T then choose else 0`. `IsCorrOp` characterizes the
  correspondence trace through a Galois cover on which it splits.
- ρ is the Galois action on the simultaneous θ-eigenspace `piece` (`GFB/IsGrRefl.lean:54-63`).
- Finiteness is `HtotFin`, which follows from `DegFin` (`GFB/PHtotFin.lean`); `DegFin` itself is unread.
- Proper base change is `UpperTheory.Et.proper_base_change` (`CommutativeAlgebra/EtaleCohomology/AffineProperBaseChange.lean`)
  **[P-skel]**. It is assembled from about 15 `…Statement` lemmas: hypercohomology, Mayer–Vietoris,
  strict henselian acyclicity, Čech descent, and others. These are unread.

**Verdict for Q1:** this formalizes a Harris–Taylor/Kottwitz-type setup. `KSAll` is a structure of Props, but all
six fields are proved, and the variety is constructed from a moduli problem. It is not an existence statement
about an abstract tower. Two caveats:
1. I followed the moduli-existence chain about 7 levels and stopped above the Siegel/theta-function bottom.
2. The archive routes many deep facts through `…Statement.lean` wrappers of the form
   `first | exact @X.foo | …`, so the real proofs sit one file lower.

## Q2. The Eichler–Shimura congruence relation `Cover.Cong`

**Statement** (`GFB/IsGrRefl.lean:114`) **[S]**:
```lean
def Cover.Cong (C : Cover H θ O) (p f n : ℕ) (ϑ : ℕ → L) : Prop :=
  ∃ (ϖ : O) (T : Fin (n + 1) → crystallineComparison.Corr p C.Y) (γ : Fin (n + 1) → H.Γ) (m : Fin (n + 1) → ℕ), Irreducible ϖ ∧
    crystallineComparison.PtId p (p ^ f) n (crystallineComparison.fn C.p ϖ) T ∧
    ∀ j, (T j).r ≫ C.p = (T j).p ≫ C.p ∧ C.Lies (γ j) (T j).p (T j).r (m j) ∧ θ (γ j) = m j * ϑ j
```
Here `Cover` is a smooth projective model Y/O_w with a finite étale Galois cover from Z.

`PtId` (`GR/AnnihilatorModels/GenericMulOfProd.lean:149`) **[S]** says the following. Take a valuation ring V
with algebraically closed fraction field and a point y : Spec V → Y whose closed point is a *generic point of the
special fibre*, and let φ be the q-power map on the residue field. Then
`AltId q n (twist φ) (images of the T_j-fibres)`, i.e.
Σ_{j even} F^{n−j}(T_j-points) = Σ_{j odd} F^{n−j}(T_j-points) as multisets. `OrdRead`/`OrdPt` describe the
ordinary situation: H = F_q^n with a line C (the connected part), and the T_j are indexed by j-dimensional
subspaces D. If C ≤ D the image is F of the quotient, otherwise the image is the quotient.

**Proof** **[P-skel]**:
- `CovMain.mIn.cong := crystallineComparison.Mod.congKS_link` (`GFB/CovLink.lean`), with
  `congKS_link := congKS_holds esNorm_link esGen_link ordGen_link quotObj_link`
  (`AnnihilatorModels/QuotObjLink.lean`). `congKS_of` (`CongKSOf.lean`) assembles `TjExF`, `TjEEx`, `OrdKSE`
  and `PtIdOfOrd`.
- `EsGen` (`AnnihilatorModels/FrobKill.lean:128`) **[S]**: on the integral model there is a Hecke correspondence
  (Y₀; s₀, t₀), finite étale on the generic fibre, carrying a p-power isogeny ψ₀ with a `T_j`-type kernel
  (`IsTj`). It is proved by `UpperTheory.Cb.exists_heckeCorrespondence_on_integral_shimuraModel` (unread).
- `QuotObj` **[S]**: quotients of the universal object by finite étale O-stable subgroups killed by w, of the
  right degree, exist in the moduli problem (`exists_pIsogeny_kernel_eq_subgroupScheme`, unread).
- `OrdGen` **[S]**: every geometric point lying over a *generic* point of the special fibre is w-ordinary
  (`IsWOrd`). Proof: `UpperTheory.Gal.Ord.ordGen` (`GR/RadicalStalks/OrdGen.lean:68`) **[P-skel/N]**. Its
  imports are `HarrisTaylorExistsDeRhamPairing`, `HodgeFiltrationLiftDeterminesModFil`,
  `HarrisTaylorRealiseKodairaSpencerDirection` and `CrystallinePull2SumCup`. This is a deformation-theoretic
  (Kodaira–Spencer / Hodge-filtration-lift) density-of-ordinary-locus argument in the spirit of Wedhorn.
- `PtIdOfOrd` is pure combinatorics: the alternating q-binomial count over subspaces containing or not
  containing C.

**From points to cohomology.** The `ESStep` field is `Mod.esStep_holds := esStep towES_holds placeData grPass`
(`GR/BasicOpenSections/EsStepHolds.lean`), with `esGen_all := esGen_holds specGood` and
`specGood := spSpecIf proper_base_change etale_base_change_of_duality` **[P]**. `ESGen` (`BasicOpenSections/BaseFacts.lean:45`) **[S]**:
for smooth proper Y/O with correspondences satisfying `PtId`, inertia acts trivially on H^k(Y_Ω̄, ℚ_ℓ), and for
a Frobenius lift σ
```lean
∑ j : Fin (n + 1), ((co (p ^ f) j : ℤ) : ℚ_[l]) • ((c j).opQ l k 0 * galHQ … σ⁻¹ ^ (n - j)) = 0      -- co q j = (-1)^j q^(j choose 2)
```
The inputs are specialization (`SpecGood`), absolute Frobenius acting as the identity (`FrobQ`), density of
generic points of the special fibre (`DenseGen`), base change of correspondences (`CorrPull`, `CorrComm`) and
`esPt_holds`. All of them are named; their proofs are unread.

**Answer.** The congruence relation rests on reduction mod p of the moduli problem. It uses:
- integral Hecke correspondences built from isogenies with prescribed kernel;
- quotient objects by finite subgroup schemes;
- ordinariness at generic points of the special fibre, proved by a Kodaira–Spencer/Hodge-filtration argument;
- an elementary subspace count at ordinary points.

It does not use an abstract congruence axiom. Serre–Tate, Grothendieck–Messing and Dieudonné theory do not
appear *by name* on the parts I read. The ordinary-locus proof touches de Rham pairings and Hodge-filtration
lifts **[N]**.

## Q3. `planEx_holds` / `specTopG`: from a definite form to the Harris–Taylor variety

```lean
theorem specTop_holds : SpecTop := UpperTheory.Gal.Spc.specTopG wtOf_holds
theorem planEx_holds : PlanEx := exists_unitaryGroupDatum_of_vector_exponent_spectral vecEx_holds expOf_holds specTop_holds
```
(`GFB/PrimeLevelLocalization/SpecTopHolds.lean`) **[P]**

**The forms.** U is a `Submodule ℂ (UA E a → ℂ)` with `IsAutRepU`. `UA E n := UJ (conjAd E) 1`
(`Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:71`)
**[S]** is the unitary group of the identity Hermitian form, i.e. the *definite* U(n).

**Seed forms** (`SeedFinOdd = SeedWU4 Odd TyEll (GenOf DGen) WtLac`) **[S]**:
- automorphic representations U′ of the definite U(a), a odd;
- of type `TyEll` at w₀ | ℓ. That is, U′ has a vector on which an open compact torsion-free J ⊂ GL_a(E_{w₀})
  acts by χ∘θ, where θ : J ↠ ℤ/ℓ^m and χ ≠ 1, and every smooth irreducible σ containing such a vector is
  supercuspidal (`Definitions/Divisors/GenOf.lean:14`);
- with lacunary weight at the embeddings over v′;
- spherical off S and generic (`GenOf DGen`) at chosen places.

**The transfer** (`specTopG`, `GR/ScalarCommutation/SpecTopG.lean`; `specData`, `SpecData.lean:64`; `specOfF`,
`SpecOfF.lean:179`) **[P-skel]**:
1. **Choice of auxiliary data.** `auxiliary_prime_holds` picks an auxiliary prime r₀. `tyEx` and `tyTop` build a
   type (open compact Ty.J at w₀ and a character ψ) for which every σ containing ψ is cuspidal.
2. **Identifying the adelic groups.** `Frame S` (`PrimeLevelLocalization/PrimeProj.lean:23`) gives
   `F.j : GUf E n → G.GAf`, which is surjective (`F.surj`). The finite-adelic points of the HT group are
   identified with those of a unitary group of the same rank (**[S]** for `F.surj`, `F.j`; I did not read the
   `Frame` fields in full).
3. **Test function and eigenvector.** `auxFn` (`ExistsIdempotentHeckeOperatorWithRegularSupport`) gives an
   idempotent u in the Hecke algebra at level `Ty.K₀`. Its powers u^m·e are supported on elements whose
   components at the places in W have separable characteristic polynomial (regular semisimple). `memFn` and
   `memComm` give commutation, and `eigEx` gives `HasEig` for the eigen-system θ on the forms.
   - The definition `PhiEx` (`ExistsIdempotentHeckeOperatorWithRegularSupportAlt.lean`) **[S]** shows the shape:
     a functional φ on G.GAf with φ(F.j g) = V.Φ(F.th g), where V.Φ is a vector of U.
   - The proof of `eigEx` is unread **[N]**.
4. **The spectral side.** `specOfF` proves `Spec L lam K ψ θ (powFn u e n)`. `Spec`
   (`GR/LefschetzSigmaSums/HeckeTraceSemi.lean:24`) **[S]** asks for a finite-dimensional algebraic
   representation ξ of G.Cˣ×ℚˣ that satisfies `IsWt` and passes two tests:
   - `IsWt`: on regular elliptic elements, the trace of ξ is the Schur polynomial of weight λ, i.e. the Weyl
     character formula.
   - For every Hecke polynomial s with `wop θ s ≠ 0` there is an a such that the test function
     `polyFn (wmul a s) f` is `Good` and `dTrace G ξ K (…) ≠ 0`.

   `Good` **[S]** has three conditions: support on regular elements, vanishing of the "pair" terms with
   reducible characteristic polynomial, and vanishing of orbital terms of non-regular-irreducible elements.
   `vanPairs`/`vanForms` prove them from the cuspidal type (`cuspIdeal`, `C_poly`). The proof **[P]** unfolds
   `dTrace` as a finite sum over `DFCls G` (classes of *definite Hermitian forms* B, i.e. definite inner forms).
   Each summand is the trace of the Hecke operator on `HeckeTraceForms.forms` of `grp G B.β`, a
   finite-dimensional space by `finite_doubleCoset_definiteHermitianForm_level`. Nonvanishing then follows from
   the linear-algebra lemma `specAlg` and the eigenvector Φ₀ on class q₀ (`clsMove`).
5. **From the spectral side to the variety.** `KSHodge` (`PackExOf.lean:22`) turns `Spec` into `HOcc`: θ occurs
   in the Hodge cohomology `hodgeH` of the Kuga–Sato variety in the degree a given by the HT weight. It is
   proved by `ksHodge_of_geo hW FixZ.FixK_holds`, from
   `HolomorphicLefschetzFormula` (`LefschetzSigmaSums/HodgeTraceFromLefschetzAndGroupSide.lean:102`) **[S]**:
   for a smooth projective Z/ℂ and a finite étale correspondence (c1, c2) with finitely many fixed points that
   are non-degenerate (tangent matrix A, det(1−A) ≠ 0),
   Σ_b(−1)^b tr(c1_* c2^* | H^b(Ω^a)) = Σ_{fixed y} coeff_a det(1+X·A_y)/det(1−A_y).

   That is the Atiyah–Bott holomorphic Lefschetz formula. Its proof (`UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence`,
   `EtaleClopenDescent/LefschetzFixedPointFiniteEtaleCorrespondence.lean:255`) is unread. Matching the
   fixed-point sum with `dTrace` (the `summ` function, `FixK`, and `GR/IsogenyEtaleTranslation/TrFEtHolds.lean`)
   is also **unread**. That matching is where CM points of the Shimura variety must be counted against
   definite-group conjugacy classes, i.e. where the Kottwitz/Jacquet–Langlands-type content lives.
6. **From Hodge to étale.** `JumpStep := G3.jumpStep_of Seam.HT.htSpecGood Seam.crysStep_holds repEx_holds`
   (`GeometricRealizationOfWeightOne.lean`) **[P]**. **[N]** It uses a Hodge–Tate comparison so that Hodge
   occurrence gives a nonzero étale θ-piece with the right jumps.

**Answer.** There is no Arthur trace formula and no analytic Jacquet–Langlands. `BaseChangeDefiniteUnitary`
supplies only the definitions (`UA`, `IsAutRepU`). The comparison is a simple "trace formula" with the following
pieces:
- the finite-adelic groups are identified (`Frame`);
- a regular elliptic test function is forced by a supercuspidal type at w₀ and regular support elsewhere;
- the group side is a finite sum over definite inner forms;
- the geometric side is the holomorphic Lefschetz formula on the compact Kuga–Sato variety.

The seeds are those definite forms whose type at w₀ makes this simple-trace-formula argument work and whose
weights are lacunary at v′. They suffice because `CongFinOdd` approximates every odd-rank definite form by them
(Q4).

## Q4. `CongFinOdd`

**Statement.** `CongUW4` (`Definitions/GaloisGeometry/LimWU4OfLimWU3.lean:37`) **[S]**: take U automorphic on the
definite U(a), a odd, and w₀, v′ | ℓ split and apart. Then there are levels Kw, hyperspecial (`KGL`) at split
places away from w₀, v′ where U is spherical, such that for finite sets Z, W of places, every eigen-system θ of
U for a family of local Hecke operators `O : LocOps l ι Kw J` satisfies the following, after it is extended by
Satake power sums at W:
```lean
PolyApprox θ⁺ {ϑ | ∃ U' θ', … SameWtOff ι w₀ v' U U' ∧ Wt … U U' ∧ TyEll … w₀ U' ∧ GenAtU … ∧ IsSysU O U' θ' ∧ ϑ = θ'⁺}
```
`PolyApprox` (`PolyApproxZeroPadic.lean:10`) **[S]**: for every ε there are finitely many seed systems η and
coefficients c with |P(θ) − Σ c_η P(η)| ≤ ε for *all* integer polynomials P. So θ lies ℓ-adically in the
closure of the span of seed systems, uniformly over polynomial Hecke expressions. The seeds have the same weights
as U off {w₀, v′}.

**Mechanism.** `congFinOdd_of_ex wtLacEx_holds = CongUWG.congUW4 (congFinG_of_step (stepSt_of_ex ellSt_holds H)) Odd`
(`CongruenceOddLevel/CongFinOddOfLvLac.lean`) **[P]**.
- **Type change at w₀** (`EllSt`, `exists_ellType`) **[S]**: arbitrarily small torsion-free J ⊂ GL_a(E_{w₀}),
  where w₀ | ℓ, with θ : J ↠ ℤ/ℓ^m (m ≥ m₀ arbitrary) such that every nontrivial χ∘θ is a cuspidal type. The
  characters have ℓ-power order, so they are ≡ 1 modulo the maximal ideal. **[N]** This is the classical trick
  that makes forms with the cuspidal type congruent to forms with trivial J-type.
- **Weight change at v′** (`WtLacEx := WtTo GapWt`, `CongruenceOddLevel/WtDefs.lean:32`) **[S]**: every
  eigen-system of weight λ is a `PolyApprox` limit of systems of weight μ, where μ differs from λ only at
  embeddings over v′ and μ(τ₀) is lacunary (`GapWt`). The proof
  (`WeightCharacters/LadicWeightEmbeddingOverPlace.lean:73`, `top_of famEx famProj famWt`) **[P-skel; defs S]**
  runs as follows:
  - `Kap0`: a homomorphism κ : U(𝔸) → GL_a(ℂ) that equals τ on rational points, is trivial at ∞, factors
    through the v′-component and is ℓ-adically continuous and integral.
  - `NrmAut`/`AutCrit`: functions g ↦ p(κ(g)·y) are automorphic, because the group is definite.
  - `Kapl`/`KaplFin`: p-adic polynomial approximation of characteristic-function-like functions.
  - `FamEx`: any algebraic form f is ε-close to a member of a family B of forms of weight ν with bounded spread
    d, for every ν.
  - `FamWt`: the constituents have weight within 2d of ν at τ and unchanged elsewhere.

  This is ℓ-adic weight interpolation on a definite group (Serre-letter/Gross/Chenevier style).

So the mechanism is ℓ-adic interpolation on the finite-dimensional spaces of algebraic modular forms of the
definite group, plus ℓ-power-order type characters. It is not Hida/Coleman theory, not a Hasse invariant, and not
the theta lift.

## Q5. p-adic Hodge and local–global properties of the limit

**Limit construction.** `limWU4_of` (`GR/TraceLimits/LimFinOddOf.lean`) **[P-skel]** combines `SeedWU4` and
`CongUW4`. It uses `frobOpsIdx` (Frobenius operators at level Kw) and `exists_trace_limit` /
`Cong.exists_limit_rep` (pseudo-character, see theta-chain.md).

**Crystalline and de Rham at w | ℓ.** `LimWU4` (`LimWU4OfLimWU3.lean:57`) **[S]** asserts `CrysDRU U ι r w` only
for w | ℓ with `Apart w w₀` and `Apart w v'`. At those places the seeds have the *same* weights as U
(`SameWtOff`) and are spherical, so they are crystalline with the target's jumps J. The limit step is
```lean
refine GlobalTheory.CongL.crysDRU_of_linApprox GlobalTheory.LimitTop.closedAtL …        -- LimFinOddOf.lean:167
```
`ClosedAtL` (`Development/AbelianVarietyTheory/Statements/EllipticCurveLevels/ClosedAtLConclusionOfMem.lean:105`)
**[S]**: suppose r is continuous and semisimple, and r is a `LinApprox` trace-limit of a set C of continuous
representations. Suppose every ρ ∈ C is semistable at w (`IsSstAt`) with Hodge–Tate jump multiset exactly J.
Then r is de Rham at w with jumps J, and if all ρ are crystalline, r is crystalline.

The proof `closedAtL` (`Proofs/SatakeParameters/ClosedAtL.lean:25`) **[P-skel]** goes through
`TraceConjugationCover.cover_exists`, `BKLim.cover_pull` and `CovClose.closed_of_cover`
(`Proofs/InertiaEigenvalues/ClosedOfCover.lean:159`). That proof bounds |n| ≤ N for n ∈ J and then uses
`nonempty_bk_of_finExt`, `ExistsBreuilKisinFrameSemistableBoundedJumps`, `ExistsDeRhamFrameLimitLatticeBreuilKisinTower`,
`DeRhamCrystallineOfLatticeReads` and `TracePowEqAlongLatticeTowerCover` **[N from imports]**.

So this is a Kisin-type closedness theorem with bounded (here fixed) weights, proved in the archive via
Breuil–Kisin frames. It is not the prismatic route. The Frobenius-on-D_cris clause is handled the same way, by a
`JointApprox` between r and the crystalline seeds.

The auxiliary places w₀, v′ are excluded in each instance. **[N]** Presumably all places above ℓ are covered
by varying the pair (w₀, v′), which is why `FieldOK`/scope conditions demand enough split places. The
restriction to scope `.csd` and the extension to all CM fields (`coreAll_of_core`) were not read.

**Weak compatibility `AwayB`.** The limit carries Frobenius eigenvalues only at almost all split unramified
places (`FrobEig`). `rest` (`IntegralStructures/Development.lean:24`) **[P]** calls
`Row.galoisLocalGlobal_of_localGlobalCompatibility` with two inputs:
- `R1 := galoisCompat_unlinkedSupport_of_spherical`
  (`SphericalGaloisCompatibility/ToralDeRham/GaloisCompatUnlinkedSupportOfSpherical.lean:69`) **[P-skel]**.
  `R1` (`Statements/EllipticCurveLevels/IsQg.lean`) **[S]** says: at w where the local component is a "plain
  torus" (`PlainTor`, built from characters), the Weil–Deligne representation of r equals rc(σ) for every
  `IsRecT` rc when w ∤ ℓ. When w | ℓ, r is de Rham and pst, with equal WD characteristic polynomials.
  - It is proved from `CoreAll`'s spherical clauses (`.unr`, `.dR`, `.crys`, `.phi`) via `away_eq_of_plainTor`,
    `toralAbove_of_holds`, `plainTor_exists_chars`, `jumps_descend` (base change to a field M where the
    component becomes unramified, then descent) and `rc_unlinked_chars` (local Artin map, `IsRecT` on
    characters).
- `R2 := localGlobalCompatAtIwahoriFixed_of_unlinked`, for Iwahori-fixed components that are plain torus or
  have E_w ≅ ℚ_g. **[S]** It gives inertia characteristic polynomials. Its proof is **unread**.

This matches the shape of `AwayB` (statements-review row 20): full compatibility in the abelian case and
inertia characteristic polynomials in the tame case. It is obtained by solvable base change plus spherical data,
not by geometry at ramified places.

## Q6. `Subtract`, `SubtractQ`, `kerSide_chainS`

- `Subtract` (`GR/ThetaParseval/SplitLineSubtraction/RowDefOfOdd.lean:111`) **[S]**:
  `(∀ d, Odd d → RowAt E Ω ι d) → TwoUp E n → RowAt E Ω ι n`. `SubtractQ` (`ThetaParseval/CoreAtQIffRowQ.lean:195`)
  **[S]** is the same with `CoreAtQ` at places in a guard set Q.
- `subtractQ_holds` (`IntegralStructures/CrystallineDescent/LimOddOfLimFinOdd.lean:31`) is `subtractQ_of …` with
  ten small lemmas **[P]**. `subtractQ_of` **[P]** goes through `atPlaceQ` (`CoreAtQIffRowQ.lean:103`, **[P-skel]**):
  1. Take U₁, U₂ from `TwoUp`, together with κ and the characters ψ₁, ψ₂.
  2. `CharEx` gives injective ℓ-adic realizations L(ψ, p).
  3. Apply the odd-rank result to U₁ and U₂.
  4. `PeelAll` (`SplitLineSubtraction/SubtractOf.lean:115`) **[S]**. Suppose r has dimension n+t, r′ is given,
     and cp(r)·∏(X−a′_j) = cp(r′)·∏(X−a_i) with all a_i ≠ a′_j. Then there is a continuous semisimple
     n-dimensional s whose local data `Cl` are those of r minus the characters a_i.
  5. Then `weakIsoQ` and `sphG_iff_cl` follow.

  Role: this is the even-rank step. It removes the theta-lift's auxiliary Hecke characters, using the
  disjointness of the two character sets. `SSLeft`/`ContLeft` give semisimplicity and continuity of summands.
- `kerSide_chainS` (`Development/AbelianVarietyTheory/Proofs/DivisorProofs/KernelHalfChainNumbersAnyLevelPrime.lean:219`)
  **[S, P-skel]**: ∀ CY ∃ C ≥ 0 such that for all chain data (D7, NumDatum, fields, primes, weights, characters,
  …) satisfying the tie hypotheses, `KerSide R … C (FactorBounds (KerChain.ofCol …))`. `KerSide`
  (`Definitions/Divisors/FactorBounds.lean:50`) **[S]** bounds log-sizes polynomially in f, m², N_n², L and log T:
  - main terms;
  - mean log-period = R.logOm;
  - log θ₀;
  - log heights h, h′;
  - log(8 + 32·#Pl·g₀·vv) ≤ C·La.

  Ingredients: `norms_matrixSteps_coupledFactor_bounded_anyLevelPrime`, normalized theta-vector families,
  `meanLogPeriod_chowlaSelberg`, `classNumbers_leS`, `card_matrixStep_indices_le_exp` and `ncard_ybSet_le`.

  Role: a size/height estimate for the theta-lift kernel chain on the **VWin** side. It is **not** on the
  `Row0b` path. Its only other reference is its own `…Statement.lean` wrapper.

## Q7. Unread on this path

1. **Matching the Lefschetz fixed-point sum with `dTrace`.** This is the crucial transfer step. Read
   `UpperTheory.Gal.LocalSmoothExtension.ksHodge_of_geo` (`GR/LefschetzSigmaSums/KsHodgeOfGeo.lean`),
   `UpperTheory.Gal.FixZ.FixK_holds` (`GR/IsogenyEtaleTranslation/TrFEtHolds.lean`), and `summ`/`FixK`/`FixL` in
   `GR/LefschetzSigmaSums/HodgeTraceFromLefschetzAndGroupSide.lean` and `HeckeTraceSemi.lean`.
2. **The holomorphic Lefschetz formula itself:** `UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence`
   (`Development/AutomorphicArithmetic/Foundations/EtaleClopenDescent/LefschetzFixedPointFiniteEtaleCorrespondence.lean:255`),
   and the definition of `hodgeH` (`GlobalTheory.HodgeCoh`).
3. **The eigenvector transfer** `UpperTheory.Gal.Spc.eigEx`, `clsMove`, and the `Frame` structure
   (`PrimeLevelLocalization/PrimeProj.lean:23`), with `frameEx`/`vecEx_holds`/`wtOf_holds`/`expOf_holds`
   (`GR/ProjectiveAutomorphicHecke/CharConjHolds.lean`).
4. **The bottom of the Siegel moduli construction:** `GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam`,
   `GlobalTheory.thetaUnifAV_closed`, `GlobalTheory.abelianSchemeLaws_all`, and the import
   `PublishedTheorems/AutomorphicForms₂/SiegelToroidalIntegral` (check whether it is a hypothesis-free theorem or
   a named "published" input). Also `pGenSm`/`pPowSm` (smoothness, projectivity).
5. **Étale foundations:** `DegFin` (finiteness), the ~15 `…Statement` inputs to `UpperTheory.Et.proper_base_change`,
   `etale_base_change_of_duality`, and `Seam.HT.htSpecGood` / `Seam.crysStep_holds` (Hodge–Tate and crystalline
   comparison for smooth projective varieties with good reduction; `CommutativeAlgebra/EtaleCohomology/SmoothModelCrystalline`).
6. **Eichler–Shimura internals:** `exists_heckeCorrespondence_on_integral_shimuraModel`,
   `exists_pIsogeny_kernel_eq_subgroupScheme`, the body of `ordGen`, and `esPt_holds`/`denseGen`/`frEx`.
7. **The cut from dimension dd to a:** `seedFinOdd_of`, `divAll_holds`, `gapLac_of` (`ZetaCharacterDivisibility/`).
8. **Congruence internals:** `congUWG_of` (body), `combine_holds`, `famEx_of`, `ladic_weight_at_embedding_over_place`.
9. **The limit:** `closed_of_cover` (body), `exists_trace_limit`, `crysDRU_of_linApprox`, `JointApprox` for φ.
10. **Local–global compatibility and scope:** `localGlobalCompatAtIwahoriFixed_of_unlinked` (R2),
    `coreAll_of_core` (scope `.csd` → all CM fields), and `toCoreK` / `twoUpOK_of_k`.

## What to read next (in order)

1. `GR/LefschetzSigmaSums/KsHodgeOfGeo.lean` and `HodgeTraceFromLefschetzAndGroupSide.lean`
   (`ksHodge_of_geo`, `FixK`, `summ`), plus `GR/IsogenyEtaleTranslation/TrFEtHolds.lean`: the identity
   "fixed points of regular elliptic Hecke correspondences = Σ over definite classes", i.e. the archive's
   substitute for the trace-formula comparison.
2. `GR/ScalarCommutation/` (`eigEx`, `clsMove`, `FrameTh.lean`) and `PrimeLevelLocalization/PrimeProj.lean`
   (`Frame`): how U on the definite U(n) gives an eigenvector on the definite inner forms of the HT group, and
   why `F.j` is surjective.
3. `EtaleClopenDescent/LefschetzFixedPointFiniteEtaleCorrespondence.lean`: whether the Atiyah–Bott formula is
   really proved, and what `hodgeH` is.
4. `Proofs/DivisorProofs/ExistsSFamPrimePowSq.lean` → `ModuliProofs/NonemptySiegelFamilyOverArithmeticBase`,
   `ThetaUniformisationComplexAbelianVarieties`: the bottom of the moduli construction.
5. `Proofs/InertiaEigenvalues/ClosedOfCover.lean` (body): the closedness of the crystalline locus.
