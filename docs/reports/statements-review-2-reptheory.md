# Review of intermediate statements, batch 2: representation theory and automorphic forms

Date: 2026-11-20. This is a read-only source review of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled or executed.
It follows the method and conventions of `statements-review.md` (batch 1). Paths are relative to `src`.
"Verified" means I read the Lean definition and the project notions it uses, to the depth stated.
"Impression" means my own mathematical judgement without a full read. All 26 statements are consumed in
`Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`
(per `out/literature.json`). Abbreviation: "tc" means the statement is only for number fields that are totally complex.

Shared notions reused from batch 1 without re-deriving them: `CuspSub` (a nonzero irreducible stable subspace of cusp forms,
with `IsAutForm` having 5 fields), `CG E a` (isomorphism classes of `CuspSub`), `HChar`, and `IrrGL`/`IrrRep` (smooth
irreducible representations of GL_n over a nonarchimedean local field).

## 1. Summary table

| # | Statement | Verdict | One-line reason |
|---|---|---|---|
| 1 | `BaseChangeIsobaricTransfer` | special case | weak base change from the *definite* U(n) (form = identity) to GL_n over CM E, with E/E⁺ unramified at every finite place; the image is an isobaric sum of csd Speh-type discrete pieces, with local compatibility at split places, unramified inert places and ∞ |
| 2 | `BaseChangeDefiniteUnitaryGroup` | special case | same as #1, but the local component is the full induced product, which must be irreducible at split places; derived from #1 (`definiteN_of`) |
| 3 | `ClozelPurity` | faithful (tc) | algebraic cuspidal π ⇒ ∃ w₀ with infChar(τ∘c) = w₀ − infChar(τ); regularity is not even assumed |
| 4 | `ClozelCohomological` | special case (tc) | regular algebraic cuspidal ⇒ (𝔤,K)-cohomology ≠ 0 with some algebraic coefficient system; one direction of Clozel 3.14 |
| 5 | `CuspidalMultiplicityOne` | special case (tc) | isomorphic `CuspSub`s are equal as subspaces |
| 6 | `CuspidalSpectrumGL` | special case (tc) | L²_cusp is a Hilbert sum of irreducibles with finite multiplicities; every irreducible closed piece is the closure of some `CuspSub`; cusp forms are bounded |
| 7 | `HarishChandraFinite` | special case | Harish-Chandra finiteness (level, K∞-type, eigenvalues of the Gelfand central elements) for unitary groups over CM fields |
| 8 | `DiscreteSeriesClassification` | faithful (for U(p,q)) | Harish-Chandra parametrisation by (ε, λ), infinitesimal character λ, lowest K-type λ+ρ_n−ρ_c of multiplicity one, and exhaustion |
| 9 | `GLHoweDuality` | faithful | (GL_n, GL_n′) and (U_n, U_n′) duality on polynomials on n′×n matrices; the pieces are irreducible and pairwise distinct |
| 10 | `HoweDualityReal` | special case | only Θ(**trivial** rep of U(X)): finite length plus a unique irreducible quotient, at the archimedean places |
| 11 | `LanglandsExhaustionGL` | faithful | every irreducible smooth rep of GL_n(k), char k = 0, has a Langlands multisegment |
| 12 | `LanglandsMultisegments` | faithful | the multisegment is unique, and L(𝔪+𝔫) is a subquotient of L(𝔪)×L(𝔫) |
| 13 | `MoyPrasadJacquetIso` | faithful | V^{K₁·N(𝒪)} → J_N(V)^{M∩K₁} is bijective for admissible V (depth zero, standard vertex) |
| 14 | `GreenRegularCharacters` | special case | Green's cuspidal characters of GL_d(𝔽_q), only for q = p prime |
| 15 | `WeilRepresentationExists` | faithful (depth 2) | Kudla-type existence of a global Weil representation of U(X)×U(W) attached to the splitting characters χ_X, χ_W |
| 16 | `WeilSiegelFormulaUnitary` | faithful | Weil's convergence criterion, then Siegel–Weil in the absolutely convergent range 2·rk A < rk B |
| 17 | `SiegelWeilUnitaryConvergent` | special case | Siegel–Weil at s₀ in Weil's convergent range rk A < rk B ≤ 2 rk A, for Fock (Gaussian-type) vectors only |
| 18 | `DoublingMethodLocalZetaIntegrals` | **weakened / misnamed** | contains no local zeta integrals; it is the global doubling basic identity plus continuation, and the pole clause of `Published.DoublingMethod` is replaced by `True` |
| 19 | `RallisInnerProductConvergent` | special case | Rallis inner product formula (global doubling-zeta form) in Weil's convergent range, assuming earlier lifts vanish |
| 20 | `CasselmanWallach` | special case | automatic extension and closed range for (𝔤,K)-maps from an irreducible **unitary** rep of U(p,q) into smooth moderate-growth Fréchet reps |
| 21 | `BorelCasselman` | faithful | V^I → J_B(V)^{T(𝒪)} is bijective for admissible V |
| 22 | `ZelevinskyPolynomialRing` | faithful | Groth(GL) ≅ ℤ[segments] as rings, with Z(Δ) ↦ X_Δ |
| 23 | `JacquetShalikaRigidity` | special case (tc) | already reviewed in batch 1, row 11 |
| 24 | `StrongApproxSU` | faithful | SU(J), J hermitian nondegenerate over CM E/F, M ≥ 2: G(F)·G_S is dense in G(𝔸) when G_S is noncompact |
| 25 | `GelfandKazhdanDual` | special case (tc) | global form: a nondegenerate pairing between π and π∘(g ↦ ᵗg⁻¹), i.e. π̃ ≅ π^θ |
| 26 | `DepthZeroInduction` | faithful | if the cuspidal support has depth zero, so does the representation |

Counts (26 rows): faithful 12 (one only to depth 2), special case 13 (5 of them only because of the restriction to totally complex
fields), weakened 1, undetermined 0, vacuous-looking 0.

Side finding, outside the list: `GlobalTheory.Published.UnusedSlot72 : Prop := True`
(`Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`)
appears in `literature.json`, so the "~155 Published statements" include at least one placeholder that is literally `True`.
This is harmless, but such a slot should not be counted as a literature input.

## 2. Per-statement notes

### 1. BaseChangeIsobaricTransfer (verified to depth 2)
`abbrev Published.BaseChangeIsobaricTransfer := PositivityTheory.Rg.BcN.BaseChangeIsobaricN`
(`…/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:8`). The definition is in
`Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/BaseChangeIsobaricNOf.lean:39`:
```lean
∀ E [IsCMField E], (∀ w, Algebra.IsUnramifiedAt (𝓞 E⁺) w.asIdeal) → ∀ n ≥ 1, ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
  ∃ c N (h : ∑ N i = n) V σ m P, IsBaseChangeN π h V σ m P
```
- `UA E n = UJ (conjAd E) 1` is the unitary group of the identity hermitian form, which is definite at ∞
  (`…/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:71`).
- `IsAutRepU` asks for a nonzero irreducible stable subspace of `IsAutFormU` functions (continuous, left U(E)-invariant,
  open level, K∞-finite). No growth condition is needed because the quotient is compact.
- `IsBaseChangeN` has the following fields:
  - each piece Vᵢ is `IsDiscrete` and `CsdAsc`, meaning it is attached (`AscEmb`) to a unitary, normalised, conjugate-self-dual cuspidal P;
  - the local components σᵢ_w are compatible with Vᵢ;
  - P_w is a subquotient of the induced product;
  - at unramified places P_w is spherical;
  - at inert unramified places the Satake parameters match via `bcParam`;
  - at every split place (ramified ones included) π_w ≅ P_w;
  - at ∞ the infinitesimal character matches the weight.

This is the Labesse / Kaletha–Minguez–Shin–White weak base change, specialised to the definite group with J = 1 and to E/E⁺ unramified
at every finite place. That hypothesis makes U(n) quasi-split at all finite places. It is substantive (`isAutRepU_const` shows the
hypothesis can be satisfied). Special case.

### 2. BaseChangeDefiniteUnitaryGroup (verified)
`abbrev … := UpperTheory.BaseChangeIdentities.DefiniteN` (`Development/AutomorphicArithmetic/Foundations/BaseChangeIdentities/Narrow.lean:28`).
The fields are the same as in #1, except that the local component is `locProd h w (σ · w)` itself. `IsCompAlong` requires that product
to be irreducible at split places. The file proves `BaseChangeIsobaricN → DefiniteN`, using the irreducibility of unitary products
(Bernstein). There is also a parallel `Published.BaseChangeDefiniteUnitary` with the weaker `IsCsdGL` instead of `CsdAsc`. Special case.

### 3. ClozelPurity. `Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/ClozelPurity.lean` (verified to depth 2)
```lean
∀ E [IsTotallyComplex E] a ≥ 1, ∀ π : CuspSub E a,
  (∀ τ, ∀ z ∈ (CG.mk π).infChar τ, ∃ n : ℤ, z = n + (a-1)/2) →
  ∃ w₀ : ℤ, ∀ τ, infChar (conj ∘ τ) = (infChar τ).map (w₀ - ·)
```
`infChar π τ` is the unique multiset m with `HasInfChar` (Capelli-type central elements act by ∏(u + mᵢ)). If no such m exists,
it defaults to `replicate a 0` (`Definitions/AutomorphicMembership/ExpoConjOfIsCsd.lean:565`). That default would make both
sides consistent with w₀ = 0, so the junk value cannot create a false positive. It is also only a default: every cuspidal
representation has an infinitesimal character.

Regularity is **not** assumed. My impression is that the statement is still true over totally complex fields. At a complex place a
unitary generic component has exponent pairs (p, q) with |Re(p+q)| < 1 by Jacquet–Shalika. Algebraicity forces p+q ∈ ℤ, so p+q = 0.
Twisting by |·|^t shifts every exponent by t, which gives w₀ = 2t. Faithful (tc), and slightly more general than the "regular
algebraic" form usually quoted.

### 4. ClozelCohomological. `…/GaloisGeometry₂/ClozelCohomologicalModel.lean` (verified to depth 2)
`∀ E tc, ∀ π : CuspSub E a, (CG.mk π).IsRegAlg → GKCoh.IsCohomological π`.
- `IsRegAlg ⇔` for every τ, infChar τ has no repeated entries (Nodup) and lies in ℤ + (a−1)/2.
- `IsCohomological π := ∃ Ξ : AlgRep, HasCohomology (π.V ⊗ Ξ)`. Here `AlgRep` is a finite-dimensional irreducible rational
  representation of GL_a(E⊗ℝ).
- `HasCohomology` is relative Lie algebra cohomology computed with K-equivariant alternating cochains on 𝔭 = Herm
  (`IsTemperedGLOfIsUnitaryLSeg.lean:205`).
- Sanity lemmas exist: the trivial a = 1 representation is cohomological for trivial Ξ but not for the standard one.

This is one direction of Clozel's Lemma 3.14. Special case (tc).

### 5. CuspidalMultiplicityOne. `…/GaloisCohomology₂/CuspidalMultiplicityOne.lean` (verified)
`∀ E tc, ∀ π π' : CuspSub E a, CG.mk π = CG.mk π' → π.V = π'.V`. This is multiplicity one for the cuspidal spectrum
(Shalika, Piatetski-Shapiro). Special case (tc).

### 6. CuspidalSpectrumGL. `…/AutomorphicForms₂/CuspDiscreteDecompositionGL.lean:117` (verified to depth 2)
The statement is the conjunction of three parts:
- `IsDiscreteSum (Rcusp μ)`: a Hilbert sum of `IsIrredSubrep`s, which are closed (`IsSubrep` includes `IsClosed`), and every
  `IrrU` occurs with multiplicity < ℵ₀.
- Every irreducible closed H ≤ L²_cusp is the closure of the classes of some normalised `CuspSub`, and its K-finite vectors are exactly those classes.
- A cusp form whose absolute value is invariant under the split centre is bounded.

The quotient is by GL_a(E)·t^ℤ (`latticeGL` adds `zpowers (splitCentre 1)`) instead of by A_G ≅ ℝ_{>0}. This is a harmless variant.
Special case (tc).

### 7. HarishChandraFinite. `…/AutomorphicForms₂/HarishChandraFinite.lean:50` (verified to depth 2)
For unitary groups G = U(V) over a CM extension (`D : D7`, `V : HSp D`), the setting fixes an open U, frames at each τ,
finite-dimensional continuous K∞-types ρ_τ, and eigenvalues c τ k. The space of `IsAutFunSm` forms of level U and K-type ρ with
`gelf θ V τ k φ = c τ k • φ` is then finite-dimensional.
- `IsAutFunSm` requires smoothness, 𝒵-finiteness under `gelf`, and moderate growth (`Formalism/LocalToGlobal/BesselHermitianTheta/TiedSmooth.lean:42`).
- `gelf … k` = Σ over cyclic words E_{i₀i₁}⋯E_{i_k i₀}. These are the Gelfand generators tr(X^{k+1}) of 𝒵(𝔤𝔩_n).

This is Harish-Chandra's finiteness theorem for these groups. Special case.

### 8. DiscreteSeriesClassification. `…/DiscreteSeriesUnitary₂/DiscreteSeriesClassificationIff.lean:11` (verified to depth 1)
For every n there are Hilbert representations π(ε, λ) of U(ε) = U(p,q) (signature pattern ε : Fin n → Bool) with the following
properties for every strictly decreasing λ ∈ (ℤ + (n−1)/2)ⁿ:
- π(ε, λ) is unitary, irreducible and square-integrable (`IsSqIntOn`: all matrix coefficients are in L²);
- its infinitesimal character is λ;
- the K-type λ + ρ_n − ρ_c occurs exactly once (`∃!`);
- every K-type has the form λ + ρ_n − ρ_c + Σ c_ab(e_a − e_b) with a < b.

Exhaustion: every square-integrable irreducible unitary σ is isomorphic to some π(ε∘s, μ). The permutation s preserves order
within each ε-class, so the pairs (ε, λ) run over W_G/W_K exactly as in Harish-Chandra. The K-type support clause allows all
positive roots, not only the noncompact ones. That is weaker than Blattner but true. Faithful for U(p,q).

### 9. GLHoweDuality. `…/TwistedTraceFormula/IrreducibleDistinctUnitary.lean:139` (verified to depth 1)
`DualAlong` asks that ⊕_{partitions a with ≤ min(n,n′) parts} smallRep(a) ⊗ smallRep′(a) ≅ the action on `MvPolynomial (Fin n′ × Fin n) ℂ`,
and that the pieces are irreducible and pairwise non-isomorphic. This is asked for GL and for U. The U case is derived from the GL
case by restriction (Weyl's unitary trick). Dual-versus-non-dual conventions in `matRep` were not checked. Faithful.

### 10. HoweDualityReal. `…/Divisors₂/HoweDualityReal.lean:21` (verified to depth 1)
`ThetaSubInf N` requires the following of a subspace N of the K-finite (Fock) model `M.Pol`:
- every derivative along a one-parameter subgroup of U(X)_∞ maps all of Pol into N;
- (k − 1)·Pol ⊆ N for k ∈ K_X;
- N is (𝔤, K)-stable for U(W)_∞.

So Pol/N is a quotient of the U(X)-coinvariants Θ(**1**). The conclusion bounds the length of chains of such N (finite length).
It also says the join of two proper ones is proper, which is the same as a unique irreducible quotient θ(1). This is Howe duality
only for the trivial representation of U(X), jointly over all real places of a CM pair. It is not the full archimedean Howe
duality theorem. Special case.

### 11. LanglandsExhaustionGL. `…/GaloisCohomology₂/LanglandsExhaustionGL.lean` (verified to depth 2)
`∀ k (char 0), ∀ x : IrrGL k, ∃ 𝔪, IsL 𝔪 x.rep`. `IsL` means x.rep is the `IsCosocle` of a product of L(Δᵢ) taken in a
non-preceding order. `IsCosocle` is irreducible plus a surjection whose kernel is the unique maximal subrepresentation
(`NonemptyEquivOfRangeEq.lean:94`). A `Segment` is a cuspidal starting point and a length ≥ 1. Faithful.

### 12. LanglandsMultisegments. `…/GaloisCohomology₂/LanglandsMultisegments.lean` (verified to depth 2)
The multisegment of x is unique, and L(𝔪+𝔫) is a subquotient of L(𝔪)×L(𝔫). These are standard facts in Zelevinsky / Langlands
classification theory. Faithful.

### 13. MoyPrasadJacquetIso. `…/GaloisGeometry₂/MoyPrasadJacquetIsoTrivial.lean:10` (verified)
For admissible π of GL_n(k) and the block parabolic given by a composition and a reindexing e, quotient by N is a bijection from
V^{K₁ ⊔ (N∩GL_n(𝒪))} onto J_N(V)^{(same group)∩M}. This is the depth-zero Moy–Prasad / Jacquet isomorphism at the standard vertex
(V^{G_{x,0+}} has N(𝔽_q)-coinvariants equal to J_N(V)^{M_{x,0+}}). The file's sanity example is only the trivial representation.
Faithful.

### 14. GreenRegularCharacters. `…/GaloisCohomology₂/GreenRegularCharacters.lean` (verified to depth 2)
For g prime and K = 𝔽_{g^d}: θ ↦ τ θ sends regular characters to cuspidal irreducible characters of GL_d(𝔽_g).
- The degree is ∏_{i=1}^{d−1}(g^i − 1).
- On an elliptic regular y with eigenvalue z the value is (−1)^{d−1}Σθ(z^{g^i}).
- τ θ = τ θ′ ⇔ θ′ is a Frobenius conjugate of θ.
- Every cuspidal character arises this way.

`IsCusp` means irreducible (`IsIrr`: the character of a simple `FDRep`) and `res a (d−a) χ 1 1 = 0`. `res` is the honest parabolic
restriction averaged over N, so this is the dimension of the N-invariants. This is Green's theorem, but only over prime fields
(q = p). Special case.

### 15. WeilRepresentationExists. `…/Divisors₂/WeilRepresentationExists.lean` (verified to depth 2)
`∃ om, M.IsWeil ψ χX χW om` for hermitian X and skew-hermitian W over a CM extension, with Hecke characters χ restricting
correctly. `IsWeil` = `IsUWeilPair` (`Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean:435`), which requires the following
of each factor:
- it is an `IsUSplitting`: it preserves the test class, intertwines the Heisenberg action (om(g)ρ(w) = ρ(g·w)om(g)), and is unitary and continuous;
- it is compatible with the χ-splitting on the doubled space (`IsUWeilSplit`, not opened).

The Heisenberg intertwining pins om(g) down up to scalars, and the χ-condition fixes the scalars. So the condition is substantive,
not a stub. This is Kudla's splitting / global Weil representation. Faithful, to depth 2.

### 16. WeilSiegelFormulaUnitary. `…/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean:56` (verified to depth 1)
Under Weil's condition (B anisotropic, or rk A + witt(B) < rk B):
- the absolute theta integral is bounded by a continuous Schwartz seminorm;
- each theta integral is integrable;
- if 2·rk A < rk B, the Siegel Eisenstein series of the section from f (a coset sum over the Siegel parabolic) converges and equals
  the normalised average ⨍ of the theta integral.

This is Weil's 1965 Siegel formula for the dual pair (U(A⊕−A), U(B)). Faithful.

### 17. SiegelWeilUnitaryConvergent. `Development/…/PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18` (verified to depth 1)
This is the `GlobalTheory.Published` one. A homonym in `Formalism/UnipotentAdelicQuotients/` lives in another namespace.
In the range rk A < rk B ≤ 2·rk A, under Weil's condition, and for `IsFockVec` f only, it asserts two things. The theta integral is
integrable. The Eisenstein series has value `thetaMean` at s₀. `EisValueAt` means `IsEisFamily` and a holomorphic value at s₀
(`Definitions/Foundations/EisValueAtIffEisPoleLE.lean:46`). This is Siegel–Weil beyond absolute convergence (Ichino and
Kudla–Rallis style), restricted to Fock vectors. Special case.

### 18. DoublingMethodLocalZetaIntegrals (verified)
`abbrev … := ResidueKilled.DM`
(`Development/WeilBound/RepresentationTheoryGL/EisensteinResidues/AnisotropicGlobalForms/DmOfHyp.lean:13`):
```lean
(EisContinues V (flat V a φ s₁) ∧ ∀ s₀, ∃ k, EisRegularAt …) ∧ True ∧
  ∀ θ … f₁ f₂ ∈ A0, (∀ s, rk/2 < Re s → BasicIdentity V μ m (flat …) f₁ f₂) ∧ ZetaContinues V μ m (flat …) f₁ f₂
```
`BasicIdentity` is the *global* doubling unfolding: ∫∫ E·f₁·f̄₂ = ∫ Φ · (matrix coefficient)
(`…/TwistedTraceFormula/EisRegularAtOfEisPoleLE.lean:26`).

Nothing in the statement concerns local zeta integrals: no factorisation, no unramified computation, no local meromorphy or
nonvanishing. It is also a strict weakening of the sibling `Published.DoublingMethod` (same file, line 36). There the middle
conjunct is the simple-pole bound `rk V < b → EisPoleLE … ((b − rk)/2) 1`. Here that conjunct is `True`. `dm_of_two` proves DM
from `CuspRapidDecay` and `SiegelEisensteinContinuation` (plus a `True` argument). The weakening is in the safe direction, since
less is assumed. But the name overstates the content. Weakened and misnamed.

### 19. RallisInnerProductConvergent. `…/TwistedTraceFormula/LowerLiftsZeroOfWittIdxEqZero.lean:41` (verified to depth 1)
Hypotheses:
- Weil's convergent range rk A < rk B ≤ 2 rk A;
- U is an irreducible closed piece of L²_cusp(U(A));
- `LowerLiftsZero`: the theta lifts of U to every lower member of the Witt tower vanish;
- Φ₁ ⊗ Φ₂ is K-finite after doubling.

Conclusions: the lifts converge and are L². The doubling zeta integral of f₁, f₂ against the Siegel–Weil section of δ(Φ₁, Φ₂)
has value at s₀ equal to vol⁻¹·⟨θ(Φ₁,f₁), θ(Φ₂,f₂)⟩. This is the Rallis inner product formula in the convergent range and in its
global-zeta form, before factorisation into L-values. Special case.

### 20. CasselmanWallach. `…/AutomorphicForms₂/HasDRepIffHasDerivAt.lean:98` (verified to depth 1)
Setting: σ is an irreducible unitary Hilbert representation of U(p,q), and E is a complete, separated, smooth representation of
moderate growth (`IsSmoothModRep`). Every (𝔤,K)-map T₀ on K-finite vectors then extends to a continuous G-map T on smooth
vectors with three properties:
- the extension is unique;
- it has closed image;
- if T₀ ≠ 0, every Sobolev norm is bounded by a continuous seminorm of Tw (T is a topological embedding).

This is the automatic-continuity half of Casselman–Wallach (compare Bernstein–Krötz), with the source restricted to unitary
irreducibles of U(p,q). Special case.

### 21. BorelCasselman. `…/TwistedTraceFormula/BorelCasselman.lean` (verified)
`IsAdmissible π → Bijective (iwahoriProj π)`, where `iwahoriProj : V^I → (V_{N_B})^{T(𝒪)}` is the quotient map
(`Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean:509`). The Iwahori subgroup is taken relative to the
`LinearOrder n`. This is Borel's / Casselman's theorem. Faithful.

### 22. ZelevinskyPolynomialRing. `…/TwistedTraceFormula/ExistsCellOfIsSubquotient.lean:209` (verified to depth 2)
The statement gives Z : Segment → IrrCl and an additive equivalence Ψ : Groth(GL) ≃ ℤ[X_Δ], with Ψ(Z Δ) = X_Δ and the following properties:
- `IsProductIso`: Ψ(1) = 1 and Ψ is multiplicative for parabolic induction of finite-length smooth reps.
- `IsSegmentClass`: π ≅ Z(Δ) ⇔ π embeds in σ×σν×…×σν^{l−1} ⇔ J(π) ≅ σ⊗…⊗σν^{l−1}.

This is Zelevinsky's theorem (Zelevinsky 1980, Cor. 7.5). There is no char-0 hypothesis, which is fine. Faithful.

### 23. JacquetShalikaRigidity. `…/GaloisCohomology₂/StrongMultiplicityOne.lean:189` (verified, batch 1 row 11)
Equal sums of Satake multisets at cofinitely many places imply a bijection of the cuspidal families. This is Jacquet–Shalika
strong multiplicity one for isobaric sums. Special case (tc).

### 24. StrongApproxSU. `…/TwistedTraceFormula/NotIsCompactUnivFv.lean:33` (verified to depth 1)
This is the `Published` one. The other `StrongApproxSU`s are in `Formalism.L2.SG…` and `IndefiniteReal`. The setting is a CM
extension, a nondegenerate hermitian J with M ≥ 2, and S given by an idempotent ε of 𝔸 (`IsPlacesIdem`). If SU_S
(`SUSupp`: elements trivial outside S) is not compact, then every g ∈ SU(𝔸) lies in the closure of SU(F)·SU_S. This is
Kneser/Platonov strong approximation for the simply connected SU. Faithful.

### 25. GelfandKazhdanDual. `…/GaloisGeometry₂/GelfandKazhdanDual.lean` (verified)
`∀ E tc, ∀ π : CuspSub E n, Paired π π invTOp`. `Paired` asks for a bilinear form B on π.V × π.V with three properties:
- it is nondegenerate on both sides;
- B(π(k)φ, π(θk)ψ) = B(φ, ψ) for k in G(𝔸_f) and in K∞, with θ = transpose-inverse (on K∞ that is k̄);
- B(Xφ, ψ) + B(φ, θ(X)ψ) = 0 for X in the Lie algebra.

So π̃ ≅ π∘θ. This is the global consequence of Gelfand–Kazhdan, not the local theorem itself. Special case (tc).

### 26. DepthZeroInduction. `…/GaloisCohomology₂/DepthZeroInduction.lean` (verified to depth 2)
`HasSupport x s` requires x irreducible and a subquotient of the product of the cuspidals in s (`IsCuspSupport`). If every
element of s has a nonzero K₁-fixed vector, then x has one too. This is the Moy–Prasad depth-preservation statement for depth
zero. The char-0 hypothesis is unnecessary but harmless. Faithful.

## 3. What I could not check

- Deeper layers:
  - `IsUWeilSplit` (#15);
  - `IsFockVec`, `IsEisFamily`, `ZetaValueAt`/`IsZetaFamily`, `ThetaClause`, `IsWittLower` (#17, #19);
  - `IsDiscrete`/`AscEmb` (#1);
  - `IsKTypeOf`, `HasInfChar` for U(p,q) (#8);
  - `Acts`/`ActsD` semantics in detail (#10). My reading of #10 rests on their evident meaning: f₁ is the action, or the derivative of the action, applied to f.
- The sign and duality conventions in `matRep` (#9) and the normalisation of `bcParam` (#1).
- Whether "algebraic but not regular" in #3 is how Clozel states his purity lemma. My argument that the statement is true is an
  impression, not a verified proof.
- I did not check whether any hypothesis of #17 or #19 (e.g. `IsMaj`, `HasIwasawa`, the `IsCartan*` frames) is unsatisfiable.
  Each looked like ordinary normalisation data. No statement in this batch looked vacuous.
