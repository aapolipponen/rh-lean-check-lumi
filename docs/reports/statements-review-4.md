# Review of `GlobalTheory.Published` statements, batch 4: automorphic analysis, real/p-adic representation theory, CM and class fields, algebraic geometry

Date: 2026-11-20. Read-only source review of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled or executed.
Method and conventions follow `statements-review.md`, `statements-review-2-reptheory.md` and `statements-review-3-geometry.md`.
Paths are relative to `src`, and `PT/` abbreviates `Development/AbelianVarietyTheory/PublishedTheorems/`.
**Verified** means I read the Lean text of the statement and of the project notions named, to the depth stated.
**Impression** means my mathematical judgement without a full read. This review asks only whether each statement says what its
name claims. It does not judge the proofs or whether RH is proved.

All 30 statements appear in `out/literature.json` as `*_of_literature` rows consumed in
`Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`.
Definitions were located with one fast `grep -rnE '^(def|abbrev|structure) Name'` over the tree (about 1 s). The `reach/`
index is pickled shards, so it was not greppable.

Shared notions reused from earlier batches without re-deriving them: `D7` / `HSp D` / `GA D V` (the unitary group U(V) of a
hermitian space over a CM extension, adelic points), `IrrGL`, `IsAdmissible`, `IsDS` / `IsHCParam` / `lowK` (discrete series of
U(p,q)), `CuspSub` / `CG`, `HChar`, `IsGlobalArtin`, `IsSelfInter`, `HermLB`, `IsSemiAbelian`.

## 1. Summary table

| # | Statement | Verdict | One-line reason |
|---|---|---|---|
| 1 | `CuspRapidDecay` | special case (U(V), CM) | smooth cusp forms of uniform moderate growth decay faster than any power of the height on G(F)\G(𝔸) |
| 2 | `CuspTraceClass` | special case (U(V), CM) | R_cusp(f) is trace class for f ∈ C_c^∞(G(𝔸)) (smooth at ∞, locally constant at finite places); trace class = finite sum of products of Hilbert–Schmidt operators |
| 3 | `CuspidalMirabolic` | faithful | GL_{n+1}(𝔽_q): a cuspidal irreducible exists, and every cuspidal irreducible restricts to the mirabolic as ind_N^P ψ (Gelfand–Kazhdan/Bernstein–Zelevinsky) |
| 4 | `DixmierMalliavinFactorisation` | faithful | for a closed linear group G ⊆ GL_n(ℂ), every f ∈ C_c^∞(G) is a finite sum g_i ∗ h_i with supp g_i ⊆ V and supp h_i ⊆ supp f; `conv` not traced |
| 5 | `FlathFactorisation` | special case (U(J), CM) | every irreducible unitary rep of U(J)(𝔸) is a restricted tensor product of local irreducible unitaries; finite factors smooth-irreducible admissible, spherical line = ℂξ_v a.e. |
| 6 | `FlathTensorProduct` | special case (U(J), CM) | #5 without the admissibility/sphericity clauses (strictly weaker than #5) |
| 7 | `GenericUnitaryDualGL` | faithful (one direction) | char-0 p-adic GL_N: generic unitary irreducible ⇒ product of unitary discrete series δ_i and complementary pairs δν^{±s}, 0<s<1/2 (Tadić/Bernstein) |
| 8 | `IrreducibleAdmissibleGL` | faithful | smooth irreducible ⇒ admissible for GL_n over a nonarchimedean local field (Jacquet/Bernstein) |
| 9 | `KFiniteVectorsUnitary` | faithful (U(p,q)) | Harish-Chandra: irreducible unitary ⇒ admissible, K-finite vectors analytic, dense, 𝔤-stable and algebraically irreducible under 𝔤 |
| 10 | `MetaplecticRepresentation` | faithful | real Weil representation: a double cover of Sp_{2n}(ℝ), unitary on L², preserving 𝒮, intertwining Schrödinger, −1 on the kernel, Gaussian coefficient formula |
| 11 | `SchurOrthogonalitySquareIntegrable` | faithful | unimodular lc group, irreducible unitary with one nonzero L² coefficient ⇒ all coefficients L², orthogonality with formal degree d>0 |
| 12 | `SiegelEisensteinContinuation` | faithful (unitary Siegel parabolic) | Siegel Eisenstein series on U(V⊕−V) from flat sections continue meromorphically; at every s₀ a finite-order pole with locally uniform moderate growth |
| 13 | `SiegelToroidalIntegral` | faithful (Faltings–Chai) | for g ≥ 1, odd n ≥ 3: smooth projective toroidal compactification of A_{g,n} over ℤ[ζ_n,1/n] with semi-abelian extension, charts, ω^N globally generated, ω^{Nk}(−D) ample |
| 14 | `WeilThetaConvergence` | special case (unitary dual pairs) | ∫|θ(g,Φ)| over U(V)(F)\U(V)(𝔸) is finite when V is anisotropic or n + witt(V) < dim V |
| 15 | `ThetaRationalInvariance` | undetermined (proved in-tree) | invariance of a project-built adelic theta action `WeilO.Om` under rational elements up to determinant characters; project-specific, and proved inside the archive |
| 16 | `WeylBranching` | faithful | GL_{n+1}(ℂ) ↓ GL_n(ℂ) and ↓ U(n): multiplicity-free, constituents = interlacing weights |
| 17 | `HolomorphicDiscreteSeries` | faithful (U(p,q)) | for HC parameter in the holomorphic chamber: K-types = lowest + ℕ-span of 𝔭⁺ roots, 𝔭⁻ kills the lowest K-type, K-finite vectors = U(𝔭⁺)·lowest K-type |
| 18 | `DiscreteSeriesExists` | faithful (U(p,q)) | for every HC parameter and every signature pattern a discrete series with Blattner-minimal lowest K-type exists |
| 19 | `HermitianLocalGlobal` | faithful (proved in-tree) | local classification of hermitian forms by det mod norms (char ≠ 2) plus Landherr's Hasse principle over CM fields |
| 20 | `LandherrSt` | faithful (CM) | same signatures at every τ and det ratio a global norm ⇒ isometric |
| 21 | `WeberRayFieldSt` | faithful | K imaginary quadratic, disc < −4: K(j, Weber values of E[n]) is abelian and is the ray class field mod n (characterised by Frobenius splitting) |
| 22 | `ComplexMultiplicationJSt` | faithful | H = K(j(𝔞)) is the Hilbert class field, Artin isomorphism Cl(K) ≅ Gal(H/K), and art(𝔟)·j(𝔞) = j(𝔟⁻¹𝔞) |
| 23 | `RegularAlgebraicPurity` | special case (CM) | regular algebraic cuspidal π on GL_a over CM E: purity of the infinity type and cohomological |
| 24 | `HeckeLAdicCharacter` | faithful | for an algebraic Hecke character (∞-type n on totally positive E^×) there is a unique continuous ℓ-adic character given by Weil's formula through a global Artin map |
| 25 | `SemiAbelianHomExtension` | faithful | Faltings–Chai I.2.7: homomorphisms of semi-abelian schemes over a dense open of a normal noetherian base extend uniquely |
| 26 | `VolNef` | faithful (depth 1) | arithmetic volume of a nef hermitian line bundle = its arithmetic self-intersection (with the (D+1)! normalisation) |
| 27 | `PointSeparationPair` | **weakened** (mild) | Angehrn–Siu/Kollár-type criterion, but the conclusion is one-sided: some section vanishes at exactly one of x₁, x₂ (an "or"), not separation in both orders |
| 28 | `RadfordShufflePolynomial` | faithful (proved in-tree) | char 0: the shuffle algebra is the polynomial algebra on Lyndon words |
| 29 | `InducedSimpleLowestAlcove` | faithful | char p: H⁰(λ) is simple as a GL_N-module when ⟨λ+ρ, α^∨⟩ ≤ p for all positive α (closure of the lowest alcove) |
| 30 | `IdealInvariantsOneOrbitSt` | faithful (derived in-tree from #22) | j(𝔞) is algebraic over K and its Aut(ℂ/K)-orbit is {j(𝔟)} |

Counts (30 rows): faithful 22 (3 proved in-tree, 1 derived in-tree from another Published statement), special case 6,
weakened 1, undetermined 1, vacuous-looking 0. No statement in this batch contains a `True` clause or a field of type `True`.

## 2. Per-statement notes

### 1. CuspRapidDecay. `PT/AutomorphicForms₂/ExistsNormLeHeightPow.lean:28` (verified to depth 2)
```lean
∀ D θ, IsInfFam θ → ∀ V e, IsExpFam θ V e → ∀ φ, IsAutFun V φ → IsSmoothInf V e φ → IsUnifModerate θ V e φ →
  IsCuspFun V φ → IsRapidDecay θ V φ
```
`IsRapidDecay`: ∀ N, ∃ C, ‖φ g‖ · quotHeight(g)^N ≤ C, with quotHeight = inf over γ ∈ G(F) of the adelic height (∏ archimedean
heights × ∏ᶠ finite heights, ≥ 1). `IsAutFun` (`Formalism/LocalToGlobal/BesselHermitianTheta/IsAutFunDef.lean:43`): left
G(F)-invariance, right-invariance under an open subgroup of G(𝔸_f), continuity. `IsUnifModerate`: one exponent N bounds all
iterated Lie derivatives. `IsCuspFun`: the integral over N_C(F)\N_C(𝔸) vanishes for the unipotent radical of every isotropic
frame (every proper F-parabolic). No K- or Z-finiteness is required, which is the smooth version (Moeglin–Waldspurger I.2.18).
If V is anisotropic, `IsCuspFun` is vacuous and the conclusion is boundedness on a compact quotient. That is correct. Special case
of rapid decay for reductive groups.

### 2. CuspTraceClass. `PT/TwistedTraceFormula/CuspDiscreteDecompositionOfTraceClass.lean:21` (verified to depth 2)
`∀ D V μ (Haar, right-invariant), ∀ f ∈ CcGA V, IsTraceClass (RcuspOp V μ f)`. `CcGA = CcAd` is the span of a ⊗ b with
a ∈ `CcSmooth` (compact support, a restriction of a C^∞ function of the archimedean matrix coordinates) and b locally constant
with compact support (`Definitions/Foundations/ExistsAuxiliaryPlaceNotMemFinset.lean:93`, `ContinuousOfMemCcSmooth.lean:150`).
`IsTraceClass T := ∃ n B C, all B i, C i Hilbert–Schmidt ∧ T = Σ B i ∘ C i` (`IsHilbertSchmidtOfFiniteDimensional.lean:32`).
That is a correct characterisation. L²_cusp is the closure of continuous cusp forms. This is the classical trace-class property
of the cuspidal spectrum (Gelfand–Graev–Piatetski-Shapiro, Donnelly). Special case (U(V)).

### 3. CuspidalMirabolic. `PT/PublishedFoundations/BlockTriangularOfSubOne.lean:225` (verified)
`CuspidalExists ∧ CuspidalRestrictsToInduced`. The first says GL_{n+1}(k) for finite k has an irreducible cuspidal
representation. The second says such a representation restricted to the mirabolic is isomorphic to
`coind_{U}^{P}(ψ_generic)` for any ψ₀ ≠ 1. `IsCuspidal`: no nonzero vector is fixed by the unipotent radical of any proper
standard block parabolic. That is the right definition for finite fields. Faithful.

### 4. DixmierMalliavinFactorisation. `PT/TwistedTraceFormula/IsClosedEmbeddingOfLocallyCompact.lean:14` (verified to depth 1)
G is any topological group with a closed embedding into GL_n(ℂ), so G is a closed linear Lie group. `CcMat ι` = compactly
supported restrictions of C^∞ functions on matrices. That equals C_c^∞(G) for a closed embedded submanifold. Conclusion: f = Σ
conv μ (g i) (h i), with tsupport g_i ⊆ V (any neighbourhood of 1) and tsupport h_i ⊆ tsupport f. That is the
Dixmier–Malliavin theorem for the regular representation. The support condition on h_i holds in their proof, since h_i is a
differential operator applied to f. I did not locate the measure-based `conv` definition (`GlobalTheory.AutomorphicL2Unitary.conv`).
Faithful, with that caveat.

### 5–6. FlathFactorisation / FlathTensorProduct. `PT/TwistedTraceFormula/ExistsFactorisationCuspidal.lean:36`, `FlathTensorProduct.lean:12` (verified to depth 2)
For σ a CM involution, J hermitian nondegenerate, and π an irreducible unitary rep of U(J)(𝔸) (`IsIrrUnitary`: complete,
unitary, topologically irreducible), the conclusion is ∃ local irreducible unitaries R_v, vectors ξ_v and a map B with
`IsRestrTensor` (`Definitions/Foundations/ToContinuousLinearMapMemHomIn.lean:116`). Its fields are:
- ‖ξ_v‖ = 1 a.e.;
- each g fixes ξ_v for almost all v;
- B is isometric on pure tensors (finite product of inner products);
- the span of pure tensors is dense;
- B intertwines.

This is the honest restricted tensor product. #5 adds that the smooth part of each finite factor is irreducible admissible,
and that for every lattice L the stabiliser-fixed vectors are exactly ℂ·ξ_v for almost all v. #6 is the bare factorisation.
These are the unitary-dual version of Flath's theorem (it holds because the groups are type I), for unitary groups over CM fields.
Special case.

### 7. GenericUnitaryDualGL. `PT/GaloisCohomology₂/IsComplementaryProductOfIsCuspidal.lean:29` (verified to depth 2)
Smooth, irreducible, unitarisable (positive-definite invariant hermitian form) and generic (nonzero Whittaker functional for some
continuous ψ ≠ 1) imply π ≅ ×δ_i × ×(τ_j ν^{s_j} × τ_j ν^{−s_j}) with 0 < s_j < 1/2. Here δ_i, τ_j are unitarisable and `IsLSeg`, i.e.
the unique irreducible quotient (`IsCosocle`) of ρ×ρν×…, which is the Zelevinsky L(Δ), essentially square-integrable
(`Definitions/NonGaloisDescent/NonemptyEquivMultiProdOne.lean:543`). This is the Tadić–Bernstein description of the generic unitary
dual, in one direction only (it does not assert that these products are irreducible unitary). char k = 0. Faithful.

### 8. IrreducibleAdmissibleGL. `PT/Divisors₂/IrreducibleAdmissibleGL.lean:10` (verified)
`IsSmooth π → π.IsIrreducible → IsAdmissible π` for GL_n over any nonarchimedean local field. Faithful. It is also a conjunct of
batch 1's `BernsteinZelevinskyFiniteness`.

### 9. KFiniteVectorsUnitary. `PT/TwistedTraceFormula/IsIrrKSubOfIsKTypeOf.lean:64` (verified to depth 2)
For σ an irreducible unitary rep of U(p,q) (`IsURepOn`: isometric on the group and strongly continuous; `IsIrredOn`: no closed
invariant subspaces), the statement asserts five things:
- admissibility (each K-isotypic component is finite-dimensional);
- g ↦ σ(g)v is analytic for K-finite v;
- the K-finite vectors are dense;
- they are 𝔤-stable;
- every 𝔤-stable subspace of them is 0 or everything.

The last clause asks only for 𝔤-stability, not K-stability. Since K = U(p)×U(q) is connected, this is equivalent to (𝔤,K)-irreducibility,
so it is not too strong. This is Harish-Chandra's theorem. Faithful for U(p,q).

### 10. MetaplecticRepresentation. `PT/TwistedTraceFormula/MetaplecticRepresentation.lean:94` (verified)
For every finite ι, there exist a topological group G, a covering surjection pr : G → Sp(ι⊕ι, ℝ) with |ker| = 2, a unitary,
strongly continuous Ω on L²(ℝ^ι), and a jointly continuous ω on 𝒮(ℝ^ι) agreeing with Ω. They satisfy:
- ω(g)ρ(w)ω(g)⁻¹ = ρ(g·w) for the Schrödinger rep ρ (explicit formula);
- the nontrivial kernel element acts by −1;
- for φ₀ the Gaussian, ⟨ω(g)φ₀, φ₀⟩² · det(holPart(pr g)) = ‖φ₀‖⁴;
- on the maximal compact (gᵀg = 1), ω(g)φ₀ = c·φ₀ with c² det(holPart) = 1.

This characterises the Segal–Shale–Weil representation with its standard Gaussian normalisation. It is substantive, and the −1
clause rules out the split cover. Faithful.

### 11. SchurOrthogonalitySquareIntegrable. `PT/TwistedTraceFormula/SchurOrthogonalitySquareIntegrable.lean:14` (verified)
μ is a left Haar measure that is also right-invariant, so G is unimodular (for non-unimodular G the hypothesis is unsatisfiable,
which is the correct domain). Take π irreducible unitary, strongly continuous, with one nonzero L² coefficient. Then every
coefficient is in L², and ∫⟨w,π v⟩·conj⟨w',π v'⟩ = ⟨v',v⟩⟨w,w'⟩/d for some d > 0. This is Godement/Harish-Chandra's theorem. Faithful.

### 12. SiegelEisensteinContinuation. `PT/SiegelWeil₂/SiegelEisensteinContinuationOfDoublingMethod.lean:14` (verified to depth 2)
For V of positive rank, majorant data a with an Iwasawa decomposition for the doubled space, μ a Hecke character with
μ|_{𝔸_F^×} = η^b (`ResEta`), and φ in the degenerate principal series at s₁, the conclusion has two parts:
- `EisContinues` of the flat family: an Eisenstein family whose value at each g continues;
- for every s₀, ∃ k with `EisRegularAt … s₀ k`. Here (s−s₀)^k E(s,g) agrees near s₀ with H(s,g), holomorphic in s, jointly
  continuous, and bounded by C·height(g)^N uniformly (`PT/TwistedTraceFormula/EisRegularAtOfEisPoleLE.lean:17`).

The "∃ k" is not trivial: it forces finite pole order and uniform moderate growth. This is Langlands' meromorphic continuation for
the Siegel Eisenstein series of U(n,n) (Tan; Kudla–Rallis setting). It is the first conjunct of `Published.DoublingMethod`, as
batch 2 noted. Faithful.

### 13. SiegelToroidalIntegral. `PT/AutomorphicForms₂/SiegelToroidalIntegral.lean:145` (verified to depth 1)
For g ≥ 1 there is a polyhedral fan φ (`IsPolFan`). For every odd n ≥ 3 there is an `SFam g n` (the level-n Siegel moduli
scheme over ℤ[ζ_n, 1/n]), and a compactification S that is projective and smooth of relative dimension g(g+1)/2, with the
open part dense in every fibre. G is a semi-abelian scheme of relative dimension g extending the universal abelian scheme,
with abelian locus exactly the open part. Each point has a toroidal chart (`HasChart`: étale-local charts, boundary ideal
generated by the product of the t_i). ω^N is globally generated and ω^{Nk} ⊗ O(−BD) is ample for k ≫ 0. This is
Faltings–Chai's main compactification theorem.

Caveat: `SFam` (`Definitions/ModuliSpaces/IsSeparatedOfIsQProjOver.lean:18`) represents the moduli problem only over reduced
bases with dense generic fibre, plus injectivity on local points. That is weaker than fine moduli, but it pins the space down
enough that the existential cannot be filled by an arbitrary family. `HasChart` and `IsPolFan` were read only at the
statement level. Faithful.

### 14. WeilThetaConvergence. `PT/Divisors₂/WeilThetaConvergence.lean:18` (verified to depth 1)
For n ≥ 1 and V either anisotropic (`wittIdx V = 0`) or with n + witt(V) < dim V: `absThetaInt V ν Φ < ⊤` for every adelic
Schwartz function on V^n. `absThetaInt` is the lower integral of |θ| over the automorphic quotient. This is Weil's convergence
criterion (m − r > n) for the unitary dual pair (U(n,n), U(V)). Special case (unitary pairs).

### 15. ThetaRationalInvariance. `PT/GlobalTheta/ThetaRationalInvarianceHolds.lean:10` (verified at statement level)
The quantifiers run over `WeilO D cc δ N N' e0`. This is a structure (`Formalism/SharpRestriction/GlobalSchurBounds/StandardLatticesGL3.lean:443`)
whose fields axiomatise an action `Om` of GL_N(𝔸_E)×GL_{N'}(𝔸_E) on theta functions. The fields are linearity, `one`, `mul`,
compatibility with translations (`lift`), invariance of e0 under integral inert elements, and an explicit formula at split
elements. The conclusion says rational elements act as ∏_τ τ(det γ)^{−a_τ} τ(det γ')^{−a'_τ} times pull-back. The statement is
**proved in the same file** (`thetaRationalInvariance_holds`, via `GlobalTheory.OddRank.oddEq_of_mem`), so it is not an external
input. I cannot map it to a single published theorem, and I did not check the structure fields against Mumford/Shimura.
Undetermined.

### 16. WeylBranching. `PT/PublishedFoundations/FiniteIntertwining.lean:129` (verified to depth 2)
`BranchesAlong` for both GL_n(ℂ) ⊂ GL_{n+1}(ℂ) and U(n) ⊂ GL_{n+1}(ℂ) gives two things:
- res(∇(λ)) ≅ ⊕_{μ ≺ λ} ∇(μ);
- mult(μ) = 1 if μ interlaces λ (μ_i ≤ λ_i, λ_{i+1} ≤ μ_i) and 0 otherwise.

`nablaSq` is the dual Weyl module built from λ − λ_N (natW), and `sqRep` twists by det^{λ_N}, so negative weights are handled
correctly. Faithful.

### 17. HolomorphicDiscreteSeries. `PT/TwistedTraceFormula/HolomorphicDiscreteSeries.lean:43` (verified to depth 1)
For λ an HC parameter in the holomorphic chamber (λ_b < λ_a whenever ε_a = true and ε_b = false) and any σ with `IsDS ε λ σ`,
`IsLowestWeightOver` asserts four things:
- every K-type is lowK + an ℕ-combination of 𝔭⁺ roots;
- K-finite vectors are smooth;
- 𝔭⁻ kills the lowest K-type;
- K-finite vectors = span of 𝔭⁺-words applied to the lowest K-type.

This is Harish-Chandra's description of holomorphic discrete series. Faithful for U(p,q).

### 18. DiscreteSeriesExists. `PT/AutomorphicForms₂/DsExistsOfDiscreteSeriesExists.lean:13` (verified)
`:= DiscreteSeriesUpqExists`, unfolded by `discreteSeriesExists_iff` to: for every n, every ε and every HC parameter λ (strictly
decreasing, in ℤ + (n−1)/2), ∃ H σ, IsDS ε λ σ (complete, nontrivial, unitary, irreducible, square-integrable, with K-type lowK
λ = λ + ρ_n − ρ_c, and that K-type is norm-minimal). Since ε ranges over all patterns, every Weyl chamber is covered.
There is also a homonymous `def DiscreteSeriesExists` in `Formalism/SharpRestriction/CuspSpanNormBounds/DiscreteSeriesWeylDimension.lean:102`
in another namespace, which I did not review. Faithful for U(p,q).

### 19. HermitianLocalGlobal. `PT/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean:395` (verified)
The local half: over a nonarchimedean local K with 2 ≠ 0 and a quadratic L/K with σ ≠ 1, two nondegenerate hermitian
forms are congruent iff det G / det G' ∈ N(L^×). That is Jacobowitz, valid including dyadic fields of char 0. The global half:
over a CM field E, congruence at every finite place of E⁺ together with congruence at every complex embedding implies global
congruence (Landherr). The statement is **proved in-tree** (`hermitianLocalGlobal_holds`). Faithful.

### 20. LandherrSt. `PT/Landherr₂/LandherrStIffLandherr.lean:12` (verified)
CM E, hermitian G, G' nondegenerate, the same signature p₀ at every τ, and det G' = z z̄ det G for a global z imply an isometry
γ ∈ GL_r(E). This is Landherr's classification (rank, discriminant mod norms, signatures), with the global-norm form of the
discriminant condition. Faithful.

### 21. WeberRayFieldSt. `PT/WeberRayClassFields/WeberRayFieldSt.lean:10` (verified to depth 2)
K is imaginary quadratic with disc < −4 (so 𝒪_K^× = ±1, the classical Weber restriction), and the lattice is 𝒪_K. `weberSet L n` =
{j/1728} ∪ {g₂g₃/Δ · ℘(z/n) : z/n a nonzero n-torsion point}. The conclusion says K(weberSet) is an abelian number field
satisfying `IsRay … (n)` (`Definitions/HeightFunctions/FiniteDimensionalOfSz.lean:16`), which has three parts:
- it is unramified outside n;
- Frobenii generate the Galois group;
- an ideal I coprime to n has trivial Frobenius iff I ∈ P_{n,1}.

The last clause characterises the ray class field mod n. Faithful.

### 22. ComplexMultiplicationJSt. `PT/PublishedFoundations/ComplexMultiplicationJPremises.lean:38` (verified)
For imaginary quadratic K ⊂ ℂ, the statement gives four things:
- an H with `IsHilbertClassField` (maximal unramified-at-finite-primes abelian extension inside ℂ);
- an isomorphism art : Cl(K) ≃ Gal(H/K) sending [𝔭] to the arithmetic Frobenius;
- K(j(𝔞)) = H for every ideal lattice;
- art([𝔟])·j(𝔞) = j(𝔟⁻¹𝔞).

This is Silverman, Advanced Topics II.4.3. Faithful.

### 23. RegularAlgebraicPurity. `PT/GaloisGeometry₂/RegularAlgebraicPurity.lean:14` (verified to depth 1)
For CM E and a cuspidal π on GL_a with regular algebraic infinity type (`IsRegAlg`: the exponents at each τ are distinct and lie in
ℤ + (a−1)/2), there are two conclusions: ∃ w₀ with infChar(τ̄) = w₀ − infChar(τ), and `IsCohomological π`. This is Clozel's purity
lemma plus cohomologicality. It overlaps batch 2's `ClozelPurity`/`ClozelCohomological`, which are stated for totally complex
fields, so this one is narrower. Special case (CM).

### 24. HeckeLAdicCharacter. `PT/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:74` (verified to depth 2)
∃ art with `IsGlobalArtin` (batch 1), and for every ℓ, ι : ℚ̄_ℓ ≅ ℂ, χ ∈ HChar and n with `IsAlgPos χ n`, there is ∃! continuous
r : G_E → ℚ̄_ℓ^× with r(σ) = ι⁻¹(χ(x)·infPow(x)⁻¹)·lPow(x) whenever art(x) = σ|^{ab}. `IsAlgPos` only constrains χ_∞ on totally
positive k ∈ E^×. By weak approximation these are dense in the identity component of E_∞^×, so the condition is equivalent
to "algebraic of ∞-type n on the identity component". That is exactly what Weil's construction needs. Faithful.

### 25. SemiAbelianHomExtension. `PT/SemiabelianTori/GeometricallyConnectedSplitTorusAff.lean:15` (verified at statement level)
S noetherian normal, U ⊆ S dense open, G and H semi-abelian over S: every homomorphism over U extends uniquely to a homomorphism
over S. This is Faltings–Chai I.2.7. Faithful (`IsSemiAbelian` as in batch 3).

### 26. VolNef. `PT/Divisors₂/VolHomog.lean:12` (verified to depth 1)
`IsArithVar p D` requires k to be a domain finite over ℤ, X integral, and so on (`Definitions/Divisors/ExistsIsClosedImmersionGenericPoint.lean:578`).
`arVol L D = limsup log #smallSec(L^m) · (D+1)!/m^{D+1}` (`Definitions/Divisors/NefFibOfIsNef.lean:52`). The statement: nef with
self-intersection a ⇒ arVol = a. This is Moriwaki's vol = self-intersection for nef bundles, a consequence of arithmetic
Hilbert–Samuel (batch 1, row 17). Faithful.

### 27. PointSeparationPair. `PT/Divisors₂/PointSeparationPair.lean:15` (verified at statement level)
The setting is X normal projective over ℂ of dimension n with a klt ℚ-divisor Δ, and m(K_X+Δ) ~ G Cartier. M is numerically
(G/m + N₀/r) with N₀ nef and big. x₁ ≠ x₂ are closed points, and constants c_e > 0 satisfy (N₀/r)^e·Z > c_e^e for every
irreducible Z ∋ x_i of dimension e, together with Σ_e 2^{1/e}·e/c_e ≤ 1. This is the shape of the Angehrn–Siu / Kollár
(Singularities of pairs §6) two-point criterion.

The conclusion is ∃ s ∈ H⁰(M) with (s(x₁) ≠ 0 ∧ s(x₂) = 0) **or** (s(x₂) ≠ 0 ∧ s(x₁) = 0). The literature conclusion is that
H⁰(M) → M_{x₁} ⊕ M_{x₂} is surjective, which gives both orders. Since the hypotheses are symmetric, the Lean conclusion cannot
recover both orders. This is a weakening in the safe direction, since less is assumed. I did not compare the exact constants
with Kollár's (impression). Weakened (mild).

### 28. RadfordShufflePolynomial. `PT/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean:675` (verified)
In char 0, `aeval` from ℚ[Lyndon words] to the shuffle algebra is bijective. The statement is **proved in-tree**
(`radfordShufflePolynomial_holds`). I did not open the `ShuffleAlgebra` definition. Faithful.

### 29. InducedSimpleLowestAlcove. `PT/GlobalTheta/WeylDualWeylLatticesAgreeOfLowestAlcove.lean:19` (verified)
In char p, if λ_i − λ_j + (j − i) ≤ p for all i < j (i.e. ⟨λ+ρ, α^∨⟩ ≤ p for every positive root, the closure of the lowest alcove),
then ∇(λ) ≠ 0 and every subspace stable under GL_N(A) for all k-algebras A (`IsGLSubmodule`, a group-scheme submodule) is 0
or ∇(λ). This is Jantzen II.5.6 (via the linkage principle). Faithful.

### 30. IdealInvariantsOneOrbitSt. `PT/GlobalTheta/ExistsMemIdealInvariants.lean:14` (verified)
j(𝔞) is algebraic over K, and its Aut(ℂ/K)-orbit equals {j(𝔟) : 𝔟 a fractional ideal}. This is derived in-tree from #22
(`ComplexMultiplicationJSt.oneOrbit`). Faithful.

## 3. `True`-stub search

I ran one whole-tree search:
`grep -rn --include=*.lean -E 'Prop := True\b|: True :=|∧ True\b|→ True\b'`. It returned 81 hits.

| Kind | Hits | What they are (I inspected all `Prop := True` and `: True :=` hits and every 4th of the rest) |
|---|---|---|
| `Prop := True` | 8 | Definitions that are literally True (listed below) |
| `: True :=` | 11 | `example : True := …` scratch blocks, `have h : True := trivial`, and one lemma whose type is True. All are harmless |
| `∧ True` | 41 | Mostly inside proof terms (`if … ∧ True then`, `⟨by omega, trivial⟩`). Some are statement clauses (below) |
| `→ True` | 21 | Mostly hypotheses of type `True` (former slots), plus local `have … → True` |

The 9 hits that mention `Published`:
- `UnusedSlot72 := True`, already reported in batch 2.
- The `DoublingMethodLocalZetaIntegrals` middle conjunct `∧ True` (`…/AnisotropicGlobalForms/DmOfHyp.lean:18`), already reported in batch 2.
- 6 theorems that take `True` in place of a Published hypothesis:
  - `hasDSComp` and `copyFinDS` (`Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDSComp.lean`): `DiscreteSeriesClassification → True → True → …`;
  - `specTrace` (same file): `… → CuspTraceClass → True → …`;
  - `archTrace` (`IrrUnitaryTraceNeZeroCopyFinDSX.lean:21`);
  - `dm_of_two` (`DmOfHyp.lean:24`);
  - `true_of_artin_reciprocity_of_recTExists` (`ThirdPlaceSeries/GlobalArtinReciprocityTrivial.lean:15`).
  
  A `True` hypothesis is a slot that was removed. That is the safe direction: less is assumed.
- `example (H : SmoothNearbyCycles) (n : ℕ) : True`, harmless.

The 8 `Prop := True` definitions:
- `UnusedSlot72`;
- `UpperTheory.GalS.UnusedSlot55`, `UpperTheory.GalS.NoCondition`, `UpperTheory.One.M.TrivialCondition`;
- `TrivialRankCondition`;
- `trivialClassCondition`, three copies.

Their use, from a name grep:
- `trivialClassCondition`: 27 files.
- `TrivialCondition`: 8 files.
- `NoCondition` and `UnusedSlot55`: 4 files each, used as *conclusions*. Examples are `noLgc`/`noLgc_alt` in
  `…/TypeConditions/HubXTypePrimeConditions.lean`, which "proves" `NoCondition D`, and `SClose.lean:24` / `NoG4Restrict.lean:11`,
  which prove `UnusedSlot55 … := trivial`. A name like `noLgc` suggests a local–global-compatibility condition that has been
  emptied out. This is inside the upper theory, not in a Published statement, and it does not affect soundness of the final
  Mathlib-level theorems. But a reader should not take those names at face value.
- `TrivialRankCondition`: used as the input of `Row.of_noE`, so `Row` with the trivial condition implies `Row E`. That is the strong direction.

Among the 30 statements reviewed here, none contains a `True` clause, a `True`-typed field, or a conclusion implied trivially by a
hypothesis. Three are proved inside the archive (#15, #19, #28) and one is derived from another Published statement (#30). For
those four the `_of_literature` row does not represent an external input.

Limitation: the regex misses `Prop :=` with `True` on the next line, `True` as a structure-field type (`field : True` with no `:=`),
and `fun _ => True` predicates. I did not run a second whole-tree search for those.

## 4. What I could not check
- `conv` (DixmierMalliavin), `ShuffleAlgebra` (Radford), `HasChart`/`IsPolFan` (Faltings–Chai), `mirabSub` (CuspidalMirabolic) and
  `IsCohomological`'s cohomology were read only at the name/statement level.
- ThetaRationalInvariance (#15): whether `WeilO`'s axioms match a published theta-function formalism.
- PointSeparationPair (#27): the exact constants against Kollár's/Angehrn–Siu's statement.
- Sign and normalisation conventions (Artin map arithmetic vs geometric, Gaussian normalisation in #10) were not checked.
