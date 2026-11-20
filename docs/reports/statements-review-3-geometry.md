# Review of `GlobalTheory.Published` statements, batch 3: arithmetic geometry, p-adic Hodge theory, complex/Arakelov geometry, class field theory

Date: 2026-11-20. Read-only source review of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled or executed.
Method and conventions follow `statements-review.md`. Paths are relative to `src`. **Verified** means I read the Lean
text of the statement and of the project notions named, to the depth stated. **Impression** means my mathematical
judgement without a full read. This review asks only whether each statement says what its name claims. It does not
judge the proofs or whether RH is proved.

Most statements live in `Development/AbelianVarietyTheory/PublishedTheorems/` (abbreviated `PT/` below). All are
consumed in `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`.
In `literature.json`, `uses_O = True` (BhattScholzeCrystallineLattices, GrothendieckMessing/Deformation,
HeckeLAdicCharacterCrystalline) only means the `_of_literature` term is built from other `_of_literature` terms.
For example, `bhatt_scholze_crystalline_lattices_of_literature O := bhattScholze_coeff (bhatt_scholze_integral_of_literature O)`,
and `bhatt_scholze_integral_of_literature O := GlobalTheory.BSP.bhattScholzeIntegral`. None of the statements below is
taken as an assumption.

## 1. Summary table

| # | Statement | Verdict | One-line reason |
|---|---|---|---|
| 1 | `BhattScholzeIntegral` | faithful | Crystalline ℤ_ℓ-lattices of G_K are realised by prismatic F-crystals on (O_K)_Δ (the site is encoded honestly), and the étale realisation is fully faithful |
| 2 | `BhattScholzeCrystallineLattices` | faithful | Same theorem, for O_L-lattices (finite coefficient extension) |
| 3 | `PrismaticDieudonneHodge` | **weakened** | Only ∃ a functor from p-divisible groups over O_C to BKF modules with a Hodge filtration and two normalisations. No equivalence, no comparison with T_pG |
| 4 | `FontaineBcris` | faithful | Fontaine's structure theorems for the explicitly built B_cris (A_cris = p-adic completion of the PD envelope), for every admissible choice of embeddings |
| 5 | `BlochKatoLocal` | faithful | dim H¹_f formula, rational orthogonality of H¹_f under cup product, integral version. H¹_f = ker(H¹ → H¹(V⊗B_cris)) |
| 6 | `DeRhamPotSemistable` | faithful | de Rham ⇒ potentially semistable (Berger). B_st = B_cris[X] with Kummer-cocycle Galois action |
| 7 | `GrothendieckMessing` | faithful (with a definitional caveat) | Lifts of abelian schemes over nilpotent PD thickenings (p nilpotent) ↔ admissible Hodge filtrations, plus lifting of homomorphisms. H¹_dR/H¹_cris is the project's "categorical cohomology" |
| 8 | `GrothendieckDeformation` | faithful (same caveat) | Item 7 without "p nilpotent": the abelian-scheme form (Mazur–Messing), any nilpotent PD ideal |
| 9 | `AbelianDeRham` | faithful (same caveat) | H¹_dR locally free of rank 2g, ∧²H¹ ≅ H², Hodge filtration of rank g, base change, crystalline rigidity, polarisation pairing |
| 10 | `AbelianLifting` | faithful | The LiftObj ∧ LiftHom half of item 8. The name suggests more than the content: a lift must already exist |
| 11 | `SemistableReductionSt` | special case | Grothendieck semistable reduction for polarised abelian varieties over p-adic fields only |
| 12 | `ToroidalCompactification` | special case | Unitary PEL Shimura varieties over a CM field, characteristic 0 only: a smooth projective normal compactification with SNC boundary, semi-abelian extension and log Kodaira–Spencer iso. No integral model |
| 13 | `Principalisation` | faithful | Hironaka principalisation for a nonzero ideal on a smooth projective variety over a char-0 field, using smooth-centre blow-ups |
| 14 | `ResolutionCharZero` (used as `resolution_char_zero`) | faithful | Hironaka resolution (strong form) for reduced, separated, finite-type schemes over a char-0 field |
| 15 | `PrincipalisationCharZero` (used as `principalisation_char_zero`) | faithful | Principalisation on smooth, separated, quasi-compact X with an SNC boundary E carried along |
| 16 | `L2ExtensionLogCanonical` | special case | Ohsawa–Takegoshi/Demailly L² extension with constant 34/δ, but only from a finite reduced point set (common zeros of n sections) |
| 17 | `ChowFormExists` | faithful (statement level) | The Chow form of a geometrically irreducible projective variety exists and is unique up to a scalar (char 0) |
| 18 | `CycleHeights` | faithful | Bost–Gillet–Soulé heights: existence (axiomatised by vertical/point/recursion clauses), the recursion formula, the projection formula |
| 19 | `NefNumerics` | faithful | Kleiman nonnegativity; for nef N, big ⇔ N^D > 0; h⁰(mL) = L^D m^D/D! + O(m^{D−1}) for nef L |
| 20 | `SerreHolomorphicSections` | special case | GAGA for H⁰ of line bundles on smooth projective complex varieties |
| 21 | `FormalAlgebraisation` | faithful | Grothendieck existence theorem: full faithfulness, and algebraisation of a formal proper scheme with an ample line bundle |
| 22 | `GoodChernWeil` | undetermined | Mumford-proportionality-shaped (good metrics, flag push-forward). Key predicates not traced |
| 23 | `ChebotarevDegreeOne` | weakened (qualitative) | Each g ∈ Gal(L/F) is the Frobenius at some unramified degree-1 prime outside any finite S. Infinitude, no density |
| 24 | `HasseNormSt` | special case | Hasse norm theorem for quadratic extensions |
| 25 | `HermitianHassePrinciple` | faithful | Landherr: nondegenerate hermitian forms for a quadratic E/F that are locally equivalent everywhere are globally equivalent |
| 26 | `QuadraticClassFieldTheory` | faithful (quadratic) | Norm-residue symbol multiplicative, Hasse norm theorem, idelic exact sequence onto ±1, product formula, norm functoriality |
| 27 | `HeckeLEntireAndNonzeroAtOne` | faithful | Hecke: L(s,χ) is entire for unitary χ ≠ \|·\|^{it}, and L(1,χ) ≠ 0 for χ ≠ 1 |
| 28 | `HeckeLAdicCharacterCrystalline` | faithful | The ℓ-adic character of an algebraic Hecke character is crystalline at every w \| ℓ where χ is unramified |

Counts (28 rows): faithful 20 (3 of them carry the de Rham/crystalline-cohomology definitional caveat), special case 5,
weakened 2, undetermined 1, vacuous-looking 0.

## 2. Shared notions unpacked (verified)

**Prisms and prismatic F-crystals.** Source: `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean`.
- `Obj l R` is a bounded prism over R. It consists of a δ-ring A (`Delta`, with the full δ-ring axioms and φ(a) = a^l + l·δ(a)),
  an invertible ideal I, (l, I)-adic completeness, l ∈ I + φ(I)A, bounded l^∞-torsion of A/I, and a structure map R → A/I.
- `Hom` consists of δ-maps sending I into I' that are compatible with the structure maps.
- `FCrys l R` assigns to every prism a finite projective module. The transition maps are base-change isomorphisms
  (`SemiBC` is the universal property of base change), satisfy identity and composition, and come with
  a Frobenius φ*M[1/d] ≅ M[1/d] (`Φ_bc`) natural in the prism.
This is an honest encoding of prismatic F-crystals in vector bundles on the absolute prismatic site of O_K. It is not a stub.

**A_inf realisation.** Source: `…/NonGaloisDescent/NormLeOneOfMemOL.lean:197,291`.
- `IsAinf` says that P₀ ≅ A_inf compatibly with φ, I ↔ ker θ, and the O_K-structure. It is realised by `ainfObj` (`exists_isAinf`).
- `Realises K E P₀ e T ρ j` asks for a base-change isomorphism j : W(C♭) ⊗ E(A_inf) ≅ W(C♭) ⊗ T. It must be compatible with
  Frobenius (up to the d^k denominators) and G_K-equivariant. This is the étale realisation.

**Period rings.**
- `Per.Acris l` is the p-adic completion of the A_inf-subalgebra of A_inf[1/p] generated by the divided powers γ_n of
  ker θ (`Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean:186`).
- `Per.Bcris` is the localisation of B_cris⁺ at the period submonoid (same file, line 280). `Per.BdR` is the fraction
  field of the ker θ-adic completion. These are the genuine rings.
- A `LocPrime l` is an abstract package of period rings (`PeriodData`) with Galois action, φ, Fil, t and χ
  (`Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean:527`).
- `LocTied` / `IsStd` pins that package to the concrete rings by ring isomorphisms compatible with every structure
  (`Formalism/LocalRingCardinality/AdicCompletionLocal/LocTied.lean`).
- `IsCrys PD ρ` means dim_LL D_cris = [K₀:ℚ_ℓ]·dim_LL V, where D_cris = (V ⊗ B)^{G_K}
  (`Formalism/WeaklyAdmissibleFiltrations/Statement.lean:169`). This is the standard definition.
- *Not verified:* I did not find a theorem that constructs a `LocTied` for some `P`. Statements 1, 2, 5, 6 and 28
  quantify over P with `IsStd`/`LocTied`. They would be vacuous if no such P existed. That is very unlikely, since it
  amounts to taking P built from the concrete rings, but I could not locate the construction within budget.

**Abelian-scheme de Rham/crystalline cohomology.** Sources: `…/Definitions/Divisors/Pullback1MemHodgeFiltration.lean`,
`…/IsKSValueOneOfRetraction.lean`.
- `Thick γ s` is an affine nilpotent PD thickening (B, J, δ) with B/J → X over the base.
- `Cris.H1 γ s := CatCoh.H1 (O γ s)` is the first cohomology of the functor T ↦ B on the category of such thickenings
  (cocycles f(φ≫ψ) = ψ(f φ) + f ψ, modulo coboundaries). `FirstDeRham` is the case of trivial PD on the base (`dp0`).
- `HdR A` is the R-dual of the primitive classes. `Fil` is the annihilator of F¹ = ker(H¹ → H¹ over trivial thickenings).
- These are project-made definitions, a Čech-free "crystalline site as an indexing category" model. I did not try to
  verify that they agree with Berthelot's crystalline cohomology or with algebraic de Rham cohomology. The three
  statements that depend on them are therefore faithful in form, and their content rests on that identification.
  The definitions are not stubs: AbelianDeRham asserts rank 2g, which an empty or trivial definition could not satisfy.

## 3. Per-statement notes

### 1–2. BhattScholzeIntegral / BhattScholzeCrystallineLattices. `PT/GaloisCohomology₂/BhattScholzeIntegral.lean:12`, `…/BhattScholzeCrystallineLattices.lean:12` (verified to depth 2)
```lean
∀ l K (P₀ : Obj l (OL K)) (e : P₀.A ≃+* Ainf l), IsAinf K P₀ e →
  (∀ P AI, IsStd P AI → ∀ V ρ (L : Lattice ρ), continuous → IsCrys (P.PD K) ρ →
     ∃ (E : FCrys l (OL K)) j, Realises K E P₀ e L.T (actT L) j) ∧
  (∀ T T' ρ ρ' E E' j j', Realises … j → Realises … j' → ∀ f G_K-equivariant,
     ∃! u : FHom E E', j' ∘ u = (W(C♭) ⊗ f) ∘ j)
```
This is "every crystalline ℤ_ℓ-lattice comes from a prismatic F-crystal on (O_K)_Δ" together with full faithfulness of
the étale realisation. That is the Bhatt–Scholze theorem (Prismatic F-crystals and crystalline Galois representations,
Thm 1.2), stated as essential surjectivity plus full faithfulness instead of as an equivalence of categories. The
second file is the version with O_L-coefficients and is derived from the first in the archive. The site and the
crystals are encoded faithfully (§2). This is the most striking item in the batch: a deep 2021 theorem stated in
substantially full strength. Caveats: universes (prisms with A : Type 0), and the `IsStd` satisfiability noted in §2.
**Faithful.**

### 3. PrismaticDieudonneHodge. `PT/Divisors₂/InjectiveOfSmulMemRange.lean:62` (verified to depth 1)
For C algebraically closed of char 0 with p-adically complete valuation subring O and a compatible system ε of p-power
roots of unity, there **exist**
- a contravariant additive functor M from `PDivGroup p O` to A_inf-modules,
- a functor D to O-modules,
- φ, r and the maps ι, π,

such that the following hold:
- M(G) is free of rank height(G), and φ(ξ̃)·M ⊆ im φ (the BKF condition);
- r : M → D is surjective with kernel ξM;
- 0 → ω_G → D(G) → Lie(G^∨) → 0 is exact and natural;
- M(ℚ_p/ℤ_p) ≅ (A_inf, φ) and M(μ_{p^∞}) ≅ (A_inf, φ(ξ)·φ);
- every φ-map M(μ) → M(ℚ_p/ℤ_p) comes from a unique G-map ℚ_p/ℤ_p → μ_{p^∞}.

`PDivGroup` is substantive: a tower of finite locally free cocommutative Hopf algebras of rank p^{nh}, with surjective
restrictions whose kernels are the p^n-torsion (`…/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean:12`).

What is missing compared with Scholze–Weinstein (classification over O_C) or Anschütz–Le Bras (prismatic Dieudonné theory):
- full faithfulness in general (it is required for only one Hom set);
- essential surjectivity;
- any link between M(G) and T_pG.

Impression on non-vacuity: the cheap choice M(G) = A_inf ⊗ T_p(G)^∨ fails both the μ_{p^∞} normalisation and integral
exactness of the Hodge sequence (the Hodge–Tate sequence is not exact integrally). So the statement does not look
trivially satisfiable. It is still a much thinner statement than the name suggests. **Weakened.**

### 4. FontaineBcris. `PT/GaloisCohomology₂/OneSubPhiOntoOfFilZero.lean:18` (verified to depth 2)
`∀ l (C : Core l)`, the following hold:
- `TensorInj`: K₀^ur-linearly independent elements of Ω stay independent over B_cris inside B_dR;
- `PhiInj`;
- `IotaInj` (B_cris ↪ B_dR);
- `Fund`: B_cris^{φ=1} ∩ Fil⁰ = ℚ_ℓ;
- φ−1 is onto, even from Fil⁰;
- `FundOnto`: B^{φ=1} → B_dR/Fil⁰ is onto;
- `Regular`: G_K-regularity.

A `Core` is a choice of ζ, ε, the embeddings o : Ω → B_dR⁺, j : A_cris → B_dR⁺ (`IsCrisP`) and ι, a log t of ε, and
Frobenius/χ data (`…/Definitions/AutomorphicMembership/IsCrisP.lean:52`). `nonempty_core` is proved. These are
Fontaine's basic theorems about the genuine B_cris (§2). Quantifying over all Cores makes the statement at least as
strong as the standard one. **Faithful.**

### 5. BlochKatoLocal. `PT/GaloisCohomology₂/RationalDualityOfAllCoefficients.lean:60` (verified at statement level plus `finiteCocycles`)
The statement assumes `LocTied` (standard period rings) and finite K/ℚ_ℓ. Its three parts:
- `DimFormula`: for de Rham V, dim H¹_f = dim H⁰ + dim D_dR − dim Fil⁰D_dR (Bloch–Kato Cor. 3.8.4).
- `RationalDuality`: H¹_f(V) and H¹_f(V′) are exact annihilators under the cup product into H²(ℚ_ℓ(1)), for a
  pairing V × V′ → ℚ_ℓ(1).
- `IntegralDuality`: the lattice/divisible version.

`finiteCocycles` = continuous cocycles c with c(g) ⊗ 1 = (g−1)x in V ⊗ B_cris. This is the correct H¹_f
(`Formalism/WeaklyAdmissibleFiltrations/Statement.lean:190`). Not traced: `IsDR`, `IsDual1`, `IsDualLat1`, `HfD`,
`CobO`. **Faithful.**

### 6. DeRhamPotSemistable. `PT/AutomorphicForms₂/DeRhamPotSemistable.lean:13` (verified to depth 2)
`IsDR (P.PD K) ρ → IsPst P ρ`, where:
- `IsPst` means rank over ℚ_ℓ^ur of D_pst equals dim V (`…/AutomorphicMembership/EqOfPowEqOneOfNormSubLt.lean:374`);
- D_pst = ⋃_{K'} (V ⊗ B_st)^{G_{K'}};
- `Bst P = Polynomial P.R.B`, with g acting by X ↦ X + kummer(g)·t (`LocalPrimeGaloisActionPeriodT.lean:187,208`).

That is the standard B_st = B_cris[log [ℓ♭]] with the Kummer cocycle. This is Berger's p-adic monodromy theorem
(de Rham ⇒ potentially semistable). **Faithful.**

### 7–8. GrothendieckMessing / GrothendieckDeformation. `PT/Divisors₂/CanonicalOfAbelianDeRham.lean:59`, `…/GrothendieckDeformation.lean:12` (verified to depth 2)
Setting: R → R₀ surjective with kernel I, a PD structure κ on I with nilpotent divided powers (`IsNilDP`), and
(for Messing) p nilpotent in R. `At κ π` is the conjunction of three parts:
- `Canonical`: for every lift A of A₀, the crystal of A₀ evaluated at R is ≅ HdR(A), and Fil(A) is admissible
  (a direct summand lifting Fil(A₀)).
- `LiftObj`: if one lift A′ exists, every admissible F comes from some lift A.
- `LiftHom`: f₀ lifts uniquely iff its crystal map preserves the filtrations.

This is Grothendieck–Messing for abelian schemes over affine bases. `GrothendieckDeformation` drops the p-nilpotence
hypothesis. Impression: that is the Mazur–Messing form for abelian schemes, where nilpotent divided powers suffice. The
archive also specialises it to dual numbers (Kodaira–Spencer). The caveat from §2 applies: everything is stated with
the project's categorical crystalline cohomology. **Faithful in form.**

### 9. AbelianDeRham. `PT/Divisors₂/CrysToDRBijective.lean:65` (verified at statement level)
For an abelian scheme A/R of relative dimension g, five parts:
- `Free`: all classes are primitive, H¹_dR is finite projective of rank 2g, and ∧²H¹ ≅ H² via cup.
- `Hodge`: the Lie sequence is exact, and the Hodge piece is a direct summand, projective of rank g.
- `BaseChange`.
- `Rigid`: crystal-to-de Rham is bijective for every nilpotent PD lift.
- `Duality`: the polarisation form is isotropic on Fil, and perfect when K(L) is trivial.

These are the standard facts (BBM, Mazur–Messing), with the same caveat. **Faithful in form.**

### 10. AbelianLifting. `PT/Divisors₂/AbelianLifting.lean:15` (verified)
Exactly `LiftObj κ π ∧ LiftHom κ π` from item 7, for any nilpotent PD thickening. It is not a statement that abelian
varieties lift (Grothendieck/Norman–Oort). `LiftObj` presupposes one lift A′. **Faithful** to the Grothendieck–Messing
lifting criterion.

### 11. SemistableReductionSt. `PT/SemistableReduction₂/SemistableReductionSt.lean:15` (verified at statement level)
For K/ℚ_p finite inside ℚ̄_p and a polarised abelian variety P over K, there is a finite K′ ⊇ K and a semi-abelian
group scheme G over O_{K′} whose generic fibre is A_{K′} (`IsGrpPullback`). This is Grothendieck's theorem (SGA 7 IX),
restricted to p-adic local fields. `IsSemiAbelian` not traced. **Special case.**

### 12. ToroidalCompactification. `PT/Divisors₂/DenseInterior.lean:146` (verified to depth 2)
For each of the following:
- a CM field E,
- a hermitian datum with signature p + q ≥ 1,
- a level,
- `Xo : Moduli Dw l`, a smooth quasi-projective scheme over the reflex field that represents the PEL moduli problem on
  reduced schemes, with a universal object and an unramifiedness clause (`ReciprocityTheory/…/ToroidalCompactification/PushInvertible.lean:29`),
- a coefficient field c,

there is a `Model Y` with these properties:
- Y is normal, projective and flat;
- it contains Xo_F as a dense open subscheme;
- the universal object extends to a semi-abelian `SAB` family over all of Y, with O_E-action, cubical symmetric
  polarisation and Rosati compatibility, and its abelian locus equals the interior;
- Y is smooth of the right dimension;
- the boundary is SNC (`Snc`, verified: regular local rings, with the ideal locally a product of part of a regular
  system of parameters);
- log Kodaira–Spencer is an isomorphism.

This is a real characteristic-0 toroidal compactification theorem (Faltings–Chai/Lan style) for unitary PEL Shimura
varieties, over the coefficient field (β = id, so no integral model). It quantifies over every fine moduli scheme Xo,
and I did not check that one is constructed. **Special case.**

### 13–15. Principalisation, ResolutionCharZero, PrincipalisationCharZero (verified to depth 2)
- `Principalisation`, `PT/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean:118`. Hypotheses: Y integral, smooth
  and projective over a char-0 field, I ≠ ⊥. Conclusion: there is s : Y′ → Y with these properties:
  - Y′ is integral, smooth and projective;
  - s is an `IsSmoothBlowupSeq`, an inductive sequence of `Blowup`s whose centres are smooth over k and lie over
    supp I;
  - s is an isomorphism off supp I;
  - I·O_{Y′} is an effective Cartier divisor (`EffCartier`), with SNC support.

  `Blowup π J` is the universal property (J·O invertible, terminal with that property), and `Snc` is as in item 12.
  All of these were read in `ReciprocityTheory/AnalyticForms/RegularLocalRings/FinalTheorems.lean`.
- `ResolutionCharZero`, `Development/AutomorphicSpectrum/PublishedTheorems/Geometry₂/ConclusionOfSmooth.lean:53`.
  For X reduced, separated and of finite type over a char-0 field, there is a blow-up sequence s with X′ smooth, s an
  isomorphism over the smooth locus, and the reduced preimage of the singular locus SNC. This is Hironaka's strong
  resolution. `IsBlowupSeq` was not opened, so I do not know whether its centres are constrained.
- `PrincipalisationCharZero`, `…/Geometry₂/NotSubsetOfDenseCompl.lean:57`. Non-projective (smooth, separated,
  quasi-compact) version, with an SNC boundary E carried through `IsSncBlowupSeq`.

All three are full-strength statements of Hironaka's theorems. **Faithful.** As with Bhatt–Scholze, a genuine proof of
these would be notable on its own. The statements are not thin shadows.

### 16. L2ExtensionLogCanonical. `PT/Divisors₂/L2ExtensionLogCanonical.lean:32` (verified at statement level)
The setting is a compact complex manifold given by a project `WeightedAtlas`, with a positive line bundle H, and n
sections s of L that have a finite common zero set and nonzero Jacobian there, with |s|² ≤ 1. The curvature hypothesis
is that i∂∂̄(φ_E + αψ) ≥ 0 for α ∈ [1, 1+δ]. The conclusion is that every f on the zero set extends to a section F of
K + E satisfying
∫ 2^n |F|² e^{−ψ} / (1 + δ²ψ²) ≤ (34/δ) · (2^{r+1}π^r/(r−1)!) · Σ_P |f(P)/Jac(P)|² e^{−φ_E + nφ_L}.
This matches the shape of Demailly's version of Ohsawa–Takegoshi, including the constant 34/δ, but only for a
zero-dimensional reduced centre. `WeightedAtlas` and `IsSec` were not traced. **Special case.**

### 17. ChowFormExists. `PT/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean:104` (verified at statement level)
Hypotheses: a homogeneous ideal I ⊂ k[x₁..x_N] in char 0 that stays prime over k̄, with Krull dimension D+1. Conclusion:
there is a multihomogeneous f in D+1 blocks with `IsChowForm I D (hilbertDegree I) f`, unique up to a nonzero scalar.
I did not find and read `IsChowForm` within budget. Its parameters (degree = Hilbert degree) and the hyperplane-section
helper functions in the same file look substantive. **Faithful at statement level.**

### 18. CycleHeights. `PT/Divisors₂/ResidueDegreeOfIsClosedImmersion.lean:109` (verified to depth 1)
`ArExists ∧ ArMix ∧ HeightProjection`.
- `IsArithHeight h` (`…/Definitions/Divisors/ExistsIsClosedImmersionGenericPoint.lean:801`) has three clauses. For
  vertical subvarieties over 𝔽_q, h = deg·log q. For arithmetic curves, h = arithmetic degree via a rational section.
  For higher dimensions there is a recursion through div(r) and the archimedean integral. Together these pin h down,
  so the existence claim is substantive.
- `ArMix` is the Bost–Gillet–Soulé recursion formula.
- `HeightProjection` is the projection formula with the residue degree.

**Faithful.**

### 19. NefNumerics. `PT/Divisors₂/ExistsAlgClosedBaseChange.lean:32` (verified at statement level)
Three parts:
- (Kleiman) nef line bundles have nonnegative top intersection on a projective scheme of dimension d;
- on integral X, a nef N is big iff N^D > 0;
- for nef L, h⁰(mL) − L^D m^D/D! = O(m^{D−1}).

All standard (Lazarsfeld 1.4.x, 2.2.16). `interNum` and `IsNef` were not traced here. The first report found `IsNef`
and `IsBig` substantive in KawamataViehweg. **Faithful.**

### 20. SerreHolomorphicSections. `PT/Divisors₂/SerreHolomorphicSections.lean:15` (verified to depth 1)
For Y smooth projective over ℂ, every `AnRead` (a covering family of algebraic étale charts) and every line bundle B,
the map from algebraic sections to holomorphic sections is bijective. `AnRead` is inhabited (`AnRead.all`), and
holomorphy is tested chart by chart. GAGA, restricted to H⁰ of line bundles. **Special case.**

### 21. FormalAlgebraisation. `PT/Divisors₂/FormalAlgebraisation.lean:43` (verified)
R is noetherian and I-adically complete.
- `Morphisms`: for X proper, morphisms X → Z (Z separated of finite type) correspond bijectively to compatible
  systems of morphisms on the thickenings X ×_R R/I^{e+1}.
- `Schemes`: a compatible system of proper Y_e with compatible line bundles, ample on Y₀, algebraises to a proper X
  with an ample M.

This is the Grothendieck existence theorem (EGA III 5.1.4, 5.4.5). **Faithful.**

### 22. GoodChernWeil. `PT/AutomorphicForms₂/MumfordProportionality.lean:30` (statement only)
`GoodChernNumbers ∧ FlagPushForward`. For a filtered bundle E with a metric that is `IsGood` on an open O, the Chern
forms are integrable and `HasChernIntegral` equals the intersection polynomial on a flag bundle Y. The second part is a
splitting-principle push-forward identity. This has the shape of Mumford's theorem on good singular metrics, but I
traced none of `Fr`, `Refines`, `IsGood` or `HasChernIntegral`. **Undetermined.**

### 23. ChebotarevDegreeOne. `PT/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:12` (verified)
For finite Galois L/F, g ∈ Gal(L/F) and a finite set S of places, there is v ∉ S of residue degree 1 over ℚ, unramified
in L, with a Frobenius at a place above v that restricts to g. This is the qualitative consequence of Chebotarev
(infinitely many degree-1 primes with any given Frobenius), not the density statement. It is proved equivalent to
`TwSys.Cheb` in the same file. **Weakened (qualitative)**, and correct as stated.

### 24. HasseNormSt. `PT/Landherr₂/ExistsNormTensor.lean:12` (verified)
For x, δ ∈ F^×: if x = a² − δb² is solvable at every real place and in every F_v (finite v), then it is solvable in F.
This is the Hasse norm theorem for F(√δ)/F. It is trivially fine when δ is a square. **Special case** (quadratic/cyclic
of degree 2).

### 25. HermitianHassePrinciple. `PT/GlobalTheta/HermitianHassePrincipleHolds.lean:437` (verified at statement level)
Nondegenerate σ-hermitian G, G′ over a quadratic E/F that are congruent over every completion of F (finite and
infinite) are congruent over E. This is Landherr's theorem. `CongrOver` not traced. **Faithful.**

### 26. QuadraticClassFieldTheory. `PT/TwistedTraceFormula/QuadraticClassFieldTheory.lean:241` (verified to depth 1)
`eta K L A x := if x ∈ normGroup K L A then 1 else −1`. For quadratic L/K the statement contains:
- multiplicativity of η_v at all places (local CFT for index-2 norm groups);
- the Hasse norm theorem;
- the idelic exact sequence: almost-everywhere norms, and K^×·norms = ker ∏η, with ∏η surjective onto ±1;
- the product formula;
- norm functoriality of η under base change.

This is class field theory for quadratic extensions, stated substantively. **Faithful (quadratic).**

### 27. HeckeLEntireAndNonzeroAtOne. `PT/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean:28` (verified)
For unitary χ ∈ `HChar K` and any number field K:
- if χ is not of the form |·|^{it}, there is an entire Λ (`IsHeckeL` = `Differentiable ℂ Λ` ∧ Euler product for
  Re s > 1, `…/Definitions/Divisors/EntireEqOfHalfPlane.lean:56`);
- if χ ≠ 1, there is a Λ analytic at 1 that agrees with the Euler product on Re s > 1 and has Λ(1) ≠ 0.

Analyticity at 1 plus agreement on the overlap with Re s > 1 determines Λ(1), so the nonvanishing is not cheap.
**Faithful.**

### 28. HeckeLAdicCharacterCrystalline. `PT/GaloisCohomology₂/HeckeLAdicCharacterCrystalline.lean:11` (verified at statement level)
Inputs:
- `LocTied` period rings;
- `art` with `IsGlobalArtin` (verified in the first report);
- an algebraic Hecke character χ with ∞-type n (`IsAlgPos`) and its ℓ-adic avatar μ (`IsLAdicOf`);
- a place w with a `LocBridge` identifying E_w with a finite extension of ℚ_ℓ (so w | ℓ).

Conclusion: if χ is unramified at w, then μ restricted to the decomposition group is crystalline (`IsCrysAt`). This is
the standard result. **Faithful.**

## 4. What I could not check

- Satisfiability of `IsStd`/`LocTied` (§2). This affects items 1, 2, 5, 6 and 28.
- Whether the project's categorical H¹ over nilpotent PD thickenings agrees with crystalline/de Rham cohomology
  (items 7–9).
- Not opened: `IsChowForm`, `IsSemiAbelian`, `IsBlowupSeq`/`IsSncBlowupSeq`, `WeightedAtlas`, `IsDR`, the
  `GoodChernWeil` predicates, and the existence of a `Moduli` object for item 12.
- No proof was examined.
