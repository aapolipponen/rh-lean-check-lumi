# Three deep inputs of the window bound: the minus-part Euler system, Kato, and `LemmaK`

Date: 2026-11-21. Read-only source study of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled or run;
about 60 ssh reads. It extends `frontier-d-window.md` (Q2 "Minus part", the Kato bullet, and the `LemmaK` row of Q5).
Paths: `AV/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/`, `PFF/` = `AV/PrimitiveFrobeniusFixed/`,
`KQC/` = `AV/ModularityArgument/KatoQuadraticCharacters/`, `CC/` = `AV/ModularityArgument/ClassCounting/`,
`FD/` = `Development/AbelianVarietyTheory/Definitions/Foundations/`.
Tags: **S** = statement read; **P** = proof read in full; **P-skel** = statement, opening, closing and the
have/obtain/refine skeleton read; **N** = inferred from names only.

## Overview

All three inputs turn out to be real, recognisably classical arguments, each formalised in a **special case shaped to
its use**, not as the general theorem. (I) `PsiBound` is a faithful **Kolyvagin–Rubin Euler-system argument over ℚ
using Jacobi sums (the Gauss-sum Euler system of Rubin's appendix to Lang)**, worked at finite level ℚ(μ_{N₀·l^m}). The
Tate twist e comes from the eigen-projection at level l^m together with a Kummer-type congruence that turns the twisted
Stickelberger sum into (1 − χ(b)b^{e+1})·B_{e+1,χ}. There are no cyclotomic units, no K-theory and no Iwasawa tower.
l = 2 and l | [E:ℚ] are excluded. The only external inputs are Poitou–Tate duality (which gives the reciprocity law
`Rec`), a Chebotarev statement and an unramified-orthogonality lemma. (II) "Kato" is a formalisation of **Kato's
Euler system for weight-(2e+1) newforms, in the ordinary, good-reduction, l odd case**. Siegel units sit in an
axiomatised modular-function tower with q-expansions. The explicit reciprocity law is proved through Coleman power
series and a Kummer-equals-dlog law for local units. The conclusion is rational **Bloch–Kato Selmer vanishing**
H¹_f(ℚ, V) = 0, with no bound toward the main conjecture. It is consumed only as `RigII`: adjoint-Selmer vanishing,
that is unobstructedness, at the "type II" (2+1 reducible) points of the U(3) deformation ring. (III) `LemmaK` is a
**Soulé-style argument run directly on group homology of GL_N(O_L) and on Galois cohomology. Algebraic K-theory is
never defined.** Kummer classes in an eigenspace of F^×/l^ν are detected by explicit cyclotomic homology cycles
(Soulé 1979, without the Chern-class language). Their number is bounded by a weak Borel-type rank bound (proved
in-archive by an invariant-forms/Stokes argument) and a reduction-theory torsion bound (via Hermite normal forms, not
Voronoi). Poitou–Tate then converts the result into a bound on #H². Quillen–Lichtenbaum and Voevodsky–Rost are not
used. The resulting bound (log #H² ≤ (2|D|)^{(2en)^C}) is far weaker than Soulé's.

---

## I. `PsiBound`: the minus part via a Jacobi-sum Euler system

### Statement **[S]**
`AV/OddResidueBounds/ZeroMemUnrHom.lean:116`
```lean
def PsiBound : Prop := ∀ E Ω … [IsCMField E] [IsAbelianGalois ℚ E] (N) (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ →
  ∀ l [Fact l.Prime], l ≠ 2 → ¬ l ∣ finrank ℚ E → ∀ (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [DVR] [finite] (e ≥ 1),
  ∀ ψ : Gal(E/ℚ) →* Oˣ, chiOf ρ ψ (-1) = (-1)^(e+1) →
  ∀ a : O, a = alN (e+1) (chiOf ρ ψ) → psiLen Ω e ψ ≤ addVal O a
```
In words: for an abelian CM field E, an odd prime l ∤ [E:ℚ], e ≥ 1 and a character ψ of Gal(E/ℚ) with
ψ(−1) = (−1)^{e+1}, the O-length of the ψ-eigenspace of Ш¹(G_ℚ, (K/O)(χ_cyc^{−e}) restricted along E) is at most
v(den·B_{e+1,ψ}). Here `alN k χ = den N k · Bprim k χ`. The factor `den` was not unpacked, so it is undetermined
whether it ever contributes l-adically. Only the upper-bound half of the main conjecture appears; no equality and no
class group statement.

### Assembly **[P]**
- `PFF/Iv.lean:4` `ML.iv : PoitouTateDuality → UnramifiedOrthogonality → PsiBound := psiOf (recip h₁ h₂)`.
- `PFF/PsiOf.lean` (64 lines) **[P]**. It converts ψ to a Dirichlet character ψ' mod N. l ∤ ord ψ' follows from
  l ∤ [E:ℚ]. It applies `vChar` and transports eigenspaces through `Chr.eigV`. **This is the only place l ∤ [E:ℚ] is
  used: to get l ∤ ord ψ.**
- `PFF/PrimCase.lean` (209 lines) **[P]**. `vChar` reduces to the primitive character (`lev_case`, Bernoulli
  denominators divide). `prim_case` then splits into two cases.
  - **Exceptional case.** If no g makes Ψ^{−1}(g) − χ_cyc(g) a unit (the twisted character is residually
    cyclotomic), `exc` (`PFF/RatPlace.lean:145`) gives Ш = 0.
  - **Main case.** Otherwise it picks δ lifting −1. `shaToShT` (`PFF/ShaToShT.lean:125`) bounds Ш by the a₀-torsion
    "strict" Selmer modules `ShT`. Then `zEval` picks a level m and b, and `count` gives
    length(ShT[a₀]) ≤ v(zVal) with zVal | a.

### The Euler system, as formalised **[S on all, P-skel on construction]**
Definitions in `PFF/IsAdmissiblePrimeListNil.lean` (156 lines) **[P]**:
- **Kolyvagin primes**: `AdmP l F r q` means q prime, q ≡ 1 mod F, q ≠ r, and l ∤ ord(r mod q). Squarefree products
  of these are `admitted`.
- **Euler-system axioms** `Sys l F r x s` (and `Lax`, the same up to roots of unity). The elements x_d lie in
  ℚ(μ_{F·d}), are nonzero, and are units away from r. The norm relation is
  N_{q}(x_{qd}) = (x_d / Frob_q^{-1} x_d)^{s(d,q)}. The congruence is x_{qd} ≡ Frob_q^{-1}(x_d)^{s} at the primes
  above q.
- **Construction.**
  - `laxEx` (`PFF/PlaceEmb.lean:189`) builds X_d for every d, with X_1 having divisor the minus Stickelberger element
    θ_b = Σ_t (⌊tb/F⌋ − ⌊−tb/F⌋)σ_t^{−1} at a prime A₀ above an auxiliary r ≡ 1 mod F (`HasOrd … th F b`).
  - The elements are **Jacobi sums**: `xJac` (`PFF/XJacPowNe.lean:130`) shows
    conj(∏_{j<b} J(χ, χ^j)) / ∏_{j<b} J(χ, χ^j) satisfies `IsX`. That is, X·X̄ = 1 and the ideal factorisation is the
    minus Stickelberger element.
  - `xEx` gives existence for any ideal, using degree-one primes in a class.
  - `xNormDiv` and `xCong`/`xCongJac`/`xCongPrin` prove the norm and congruence relations.
  - `sysOfLax` raises to (δ·/·^a)^{2N₀d} to kill roots of unity.
  - This is Rubin's Gauss/Jacobi-sum Euler system for the minus part (Rubin's appendix to Lang; Kolyvagin's
    "Euler systems" for class groups). It is **not** cyclotomic units.
- **Derivative operators**: `der1 q τ u = ∏_{i<q−1} τ^i(u)^i`, i.e. D_q = Σ i·τ^i, iterated over a list L as
  `der τ L`. τ_q generates the inertia/tame Galois group at q (`IsTau`, `ineTau`). `derBasic`/`derInv` prove the
  usual (σ−1)D_q = q−1−N_q telescoping and that the derivative is invariant modulo l^m-th powers.
- **Classes κ_r**: `IsKol` gives κ : G → ℤ/l^m as the Kummer cocycle of an l^m-th root of
  opP δ a (der τ L x_{∏L}) (`kolEx`, `kolHom`, `kolUnr`). It is unramified outside F·r·∏L.
  `nu … = Σ_t κ(σ_t^{-1} u σ_t)·β(σ_t)·w` projects it to the β = χ_cyc·α^{−1} eigenspace with values in K/O. The
  initial class is controlled at r (`kolInit`, `NuSys.init`).
- **Finite–singular comparison**: `kolStep` (`PFF/KolStep.lean:135`) **[S]**. For t in inertia at q acting on μ_q
  like τ_q, and φ = Frob_q, κ_{qL}(t) = −s(L,q)·κ_L(φ). This is the classical φ_q^{fs} identity.
- **Reciprocity**: `Rec` (`PFF/IsAdmissiblePrimeListNil.lean:141`) **[S]**. Let c be an α-cocycle and n a dual
  cocycle, both killed by a, unramified outside Nq, with c locally trivial at places over N other than q. Then
  y·c(g) = 0 for g in the decomposition group at q whenever n(τ) = y·w₀. `recip` (`PFF/OverIff.lean:297`) **[P-skel]**
  proves it from `PoitouTateDuality` (exactness of the nine-term sequence, i.e. sum of local invariants = 0, through
  `glob`: a cup-product 2-cocycle that is a local coboundary everywhere but at one place is a coboundary there too)
  and `UnramifiedOrthogonality` (proved: `unramifiedOrthogonality_holds`). `step` (`PFF/ChiDvd.lean:37`) combines
  `Rec` with `kolStep`.
- **Chebotarev step**: `pick` (`PFF/AddPowNsmul.lean:175`) **[S]**. Given a nonzero Selmer cocycle c and a derivative
  class ν, it finds an admissible q ∤ T, a place A above q and φ = Frob_A with c(φ) ≠ 0 and ν(Fix μ_F) ⊂ O·ν(φ).
  This uses `chebQ` → `Published.chebotarevDegreeOne'` (a theorem) and the "not a union of three subgroups" lemma
  (`two_sub`/`three_sub`).
- **Induction**: `count` (`PFF/FrobFix.lean:143`) **[P]**.
  - It builds ν from `nuSysEx` (`PFF/NuSysEx.lean:79`, **[P-skel]**: `laxEx` → `sysOfLax` → `derBasic`/`derInv` →
    `kolEx`/`kolHom`/`kolUnr`/`kolStep`/`kolInit`).
  - It then runs the abstract chain lemma `chain` (`PFF/Imports.lean:6`). Each step chooses q by `pick`. `key` shows
    that the annihilator aL of ν grows by e with e·c(φ) = 0, and that
    length(S_n) ≤ length(S_{nq}) + v(e), where S_n is the Selmer module with extra strictness at n.
  - The conclusion is length(ShT[a₀]) + v(e₀) ≤ v(zVal(α, σ, b)) whenever a₀·zVal | l^m.
  - This is Rubin's version of Kolyvagin's argument (Rubin, appendix to Lang; Euler Systems ch. 4) for one
    eigencomponent.
- **Bernoulli link (the twist)**: `zCong` (`PFF/GenBUnits.lean:103`) **[S]** states that, modulo l^m,
  d_{e+1}·(b^eχ(b)·Σ_t th(F,b,t)·t^eχ(t) − 2(χ(b)b^{e+1} − 1)·B_{e+1,χ}/(e+1)) ≡ 0.
  `zEval` (`PFF/ZeNorm.lean:163`) **[S]** uses it to choose m, b with Dat (α ≡ 1 mod l^m on G_{ℚ(μ_F)},
  α(−1) ≡ −1) and zVal | a·(unit), a₀·zVal | l^m.

### Answers for (I)
- **Which Euler system.** Jacobi sums (Stickelberger-type), for the minus part. Neither cyclotomic units nor K-theory
  elements (Soulé, Coates–Sinnott) appear.
- **What is concluded.** Only the upper bound length(Ш_ψ) ≤ v(den·B_{e+1,ψ}), for the strict (Ш) Selmer group, one
  character at a time. The main conjecture is not stated and no lower bound is proved.
- **Twists e' > 0.** No Soulé twisting and no descent from the ℤ_l-tower. The argument works over ℚ(μ_{N₀l^m}),
  where χ_cyc^e ≡ 1 mod l^m, projects the Kummer classes to the α = (χ_cyc^e·ψ)^{−1} eigenspace modulo l^m (`Dat`),
  and recovers B_{e+1,ψ} through the twisted Stickelberger congruence `zCong`, letting m grow with the target.
  This is the classical "twisting at finite level" device (as in Kurihara or Rubin, Euler Systems §6) and is
  correct in outline.
- **l = 2.** Excluded (`Dat.odd_l`, `PsiBound`'s l ≠ 2). l = 2 is handled in `ThmBab` by Iwasawa theory.
- **l | [E:ℚ].** Excluded. It is handled by `StickBound` (`AV/OddResidueBounds/ThmBcOfPsiBound.lean:291`,
  `stick_of killPow lenPow gen`) **[S]**: Stickelberger gives l^r·ShaMinus = 0 with
  r·log l ≤ C·n(e+1)·log(eln) (`KillPow.lean:31`), times an H¹[l] generator count. `OddResidueBounds/` has 36 files
  and 2,335 lines.
- **Assessment.**
  - It is a special case sufficient for the application: an upper bound per eigencomponent, l odd, l ∤ ord ψ, over ℚ.
    The classical theorem it matches is Mazur–Wiles/Kolyvagin–Rubin's divisibility for Ш of twisted Tate modules.
  - The skeleton follows the textbook argument step by step, and I saw nothing conjecture-shaped.
  - In Lean it is plausibly a first formalisation of a Kolyvagin-style Euler-system bound.
  - Size: `PFF/` is 52 files and 7,350 lines, plus Stickelberger (`AV/GaloisLibrary/StickelbergerTheorem/`, not
    measured) and Bernoulli helpers.

---

## II. Kato's Euler system

### What is stated **[S]**
`KQC/SphericalDecomposition/KatoTwoW.lean:10` (same type as `KatoTwo`, `KQC/KatoTwoOfUseN.lean:43`):
```lean
def KatoTwoW : Prop := ∀ l Ω K e N θ ψ (W : G ℚ Ω →* GL 2 (Qbar l)), Used l Ω K e N θ ψ W →
  ∀ ι (f : Af.Newform (2*e+1)), f.Att ι (tw W χ_cyc^{-e}) → WitAQ ι W →
    BlochKatoSelmerVanishes l (colRep (tw W 1)) ∧ BlochKatoSelmerVanishes l (colRep (tw W θ))
```
- `Used` (`KatoTwoOfUseN.lean:11`) holds the following conditions.
  - l odd, e ≥ 1, (l−1) ∤ 2e.
  - K is imaginary quadratic with l ∤ disc(K)·h(K), and θ is its quadratic character, θ = det W.
  - W has Hodge–Tate weights (e, −e), is ordinary (a flag at l with inertia acting by χ^e·χ', χ^{−e}·χ'), and has
    level N·|disc K|.
  - W is **residually Eisenstein**: ‖tr W − (θΨ + Ψ^{−1})‖ < 1 with Ψ = χ_cyc^e ψ.
  - W restricted to G_{K(μ_{l^∞})} is irreducible.
- `BlochKatoSelmerVanishes l ρ` (`AV/AutomorphicForms/BlochKatoSelmerVanishes.lean:144`) **[S]**: every continuous
  cocycle with Q̄_l coefficients that is unramified away from l and "finite" at l (`Loc.finiteCocycles`) is a
  coboundary. That is **H¹_f(ℚ, V) = 0 for the rational representation**: finiteness, not an integral bound.
- In words: for the l-adic representation of a weight-(2e+1) newform twisted to Hodge–Tate weights (e, −e), and for
  its twist by the quadratic character of K, the rational Bloch–Kato Selmer group vanishes. The relevant L-value is
  at the edge of the critical strip (the s = 1 line in unitary normalisation), so its nonvanishing is classical.
  Classically this is Kato 2004, Theorem 14.2, in the ordinary case. No main-conjecture divisibility is stated.

### Who consumes it, and "unobstructedness" **[P]**
`rigII_of : CohInp → AdVanishQ → NewformAut → KatoTwo → RigII` (`KQC/ReducibleThreeDim.lean:265`):
- `RigII` (`KatoTwoOfUseN.lean:49`) **[S]**: at every **type-II point** r of the U(3) Eisenstein deformation ring
  (r is block-diagonal: W in the corner entries {0,2}, and a character), whenever the 2-dimensional piece W is
  modular, `BlochKatoSelmerVanishes l (adRep r)`.
- ad r splits into ad W (from `AdVanishQ`) and the off-diagonal pieces, which are twists of W and W⊗θ (from `KatoTwo`).
- So "unobstructedness" means concretely: **the adjoint Bloch–Kato Selmer group vanishes at type-II points**. This
  feeds the smoothness hypothesis (M4) of `LemmaM` through `InpZ.rigII` (`KatoTwoOfUseN.lean:55`) and
  `corGK_of`/`caseI` (`RigIIOfHypotheses.lean`), and so feeds `CountI` (U(3) congruences).
- The main path calls `katoTwoW_of_printsH` (`AV/…/DenseThresholdCases/KatoTwoWOfPublishedH.lean:48`) **[P]** →
  `twoS` (`KQC/SphericalDecomposition/SphAtTw.lean:16`) **[P]**. That applies
  `VanishOrdL ← vanishOrdL_of_zetaUr hC Final.zetaUr` to W and to its determinant twist
  (`admissible_twist_by_det`).

### Proof skeleton
- `FD/VanishOrdL.lean:23` `VanishOrdL` **[S]**: for l odd, e ≥ 1, an `admitted` W with source newform conditions
  (`SrcL`: l ∤ level, |a_l| = 1, i.e. **ordinary and good at l**, and a flag at l), H¹_f(W) = 0.
- `vanishOrdL_of_zetaUr` (`…/Proofs/FoundationProofs/VanishOrdLOfZetaUr.lean:20`) **[P]**. It puts W in normal
  form W' (`exists_ordinary_normal_form_unramified_source`), gets `ES W' A` from `ZetaUr`, and applies
  `es_vanish hC` (**unread**).
- `ES W A` (`FD/FinalTheorems.lean:98`) **[S]** is the **axiomatised Euler-system output**. It asks for:
  - an integral class y ∈ H¹(ℚ, W), unramified away from l, **not in the Greenberg (ordinary) local condition at l**
    (`¬ Gr`);
  - for each n and each prime w ∉ S' with l^n | w − 1, a tame family `Tame`: a cochain Y valued in functions on
    ℤ/l^n with Σ_x Y = P·y + coboundary, P ≡ u·det(Frob_w − 1) mod l^n (the Euler factor), and Y unramified outside
    w up to coboundary.
  - Only **one auxiliary prime at a time** appears. That is enough for finiteness of a Selmer group (Rubin's
    exponent-bound argument) but not for the order bound.
- `Final.zetaUr` (`KQC/UnramifiedZeta/ZetaUr.lean`) **[P]** =
  `zetaUr_of_halves2 _ (kato_global_unit_law_of_smoothed_classes kato_eulerSystem_integrality smoothedZetaClass_hodgeTateLaw (…hecke_projection_nonvanishing)) pLocu`.
  The two halves are `ExistsZetaEulerSystemIwasawaData Pin7` and `ZetaEulerSystemNonvanishing Pin7`
  (`FD/ZetaElementsUnramifiedOrdinaryOfEulerSystemInert.lean`). `Pin7` (`FD/HTPresNuOfPolys.lean:24`) carries the
  reciprocity data shared between the halves.
- **Existence half.**
  - `KatoEulerSystemIwasawaClassStatement`
    (`KQC/FrobeniusHodgeTateLaws/SmoothedZetaClassHodgeTateLawStatement.lean:11`) **[S]**, proved by
    `Kd.K4.top` (`AV/../Foundations/IwahoriReduction/NormProducts/AdmissibleWeightedDataMonoCoef.lean:132`,
    **P-skel**: `kato_tame_relation_projected` supplies the tame relations).
  - It gives a compatible system Y_r of Shapiro cocycles in H¹(ℚ, ρ_K ⊗ Λ/l^r) (`ShCoc`, norm-compatible under
    `push`), built (`IsZWc`/`IsZetaSystemFixedExponent`, `FD/IsZetaSystemFixedExponent.lean`) from Kummer classes
    `clsBmu … c d k` of **(c,d)-smoothed Siegel units** in a modular-function tower `KZ.Tower`
    (`FD/ExpUpper.lean:42`: a field with SL₂/GL₂⁺(ℚ) action, q-expansion into Hahn series, Shimura reciprocity
    `recip`, and j).
  - Its specialisation y = Σ_u u^{−e}χ(u)Y_r(u) is the weight-(2e+1) class (`spec`), together with `Sys`
    (Euler-system tame relations), `IwSys2` (Iwasawa compatibility along the decomposition group at l) and `SpLink`.
  - Whether the classes are Kato's K₂ cup products {g_c, g_d} or Kummer classes of single units pushed to weight
    2e+1 through symmetric-power "symbols" (`KQC/SymmetricPowerSymbols/`, 3.9k lines) is **undetermined**.
- **Explicit reciprocity.** `SmoothedZetaClassHodgeTateLawStatement` (same file:31) **[S]**, proved by
  `K5.top := law_of_inputs K5.hco Smooth.exists_pres_smoothed` (`KQC/SmoothedZetaClasses/Imports.lean:11`) **[S]**.
  - Statement: for primitive ψ mod l^m, the "Hodge–Tate value" of the d₀-smoothed class, presented by polynomials in
    ζ_{l^m} (Coleman-type `HTPresNuOfPolys`/`KumPres`), equals modulo l^{m−c} the quantity
    (1 − d₀ψ^{−1}(d₀))·v_m·κ·(Gauss sum)·ψ^{−1}(N)·λ(Σ_x c_w(x)·chiProj(…(2e+1), ψ, χ_d, c, d, x)).
  - Here λ is an ordinary Eisenstein eigenfunctional (`IsLamFR2`) applied to an Eisenstein-type product. This is
    the shape of Kato's explicit reciprocity law (zeta element ↦ product of Eisenstein series ↦ L-values) in the
    ordinary case.
  - Underneath is the Kummer = dlog law for local units, `kummerCochain_eq_dlog_explicitReciprocity`
    (`…/FoundationProofs/KummerCochainEqDlogExplicitReciprocityStatement.lean`) **[S]**: for a unit P(ζ), the Kummer
    cocycle equals t·ζP′(ζ)/P(ζ) up to l^c and coboundary (Artin–Hasse–Iwasawa / Coates–Wiles). It is proved by
    `RecOne.kummer_eq_dlog_one` (193 lines, unread). Coleman series appear as `Col.exists_coleman_series`.
  - So the reciprocity law **is proved, not assumed**, in the ordinary, l ∤ N, l odd case via Coleman power series
    at the cusp. There is no general (supersingular or de Rham) explicit reciprocity.
- **Nonvanishing half.** `Kd.C7.pLocu` (`…/IwahoriReduction/LangPolynomials/NormFactorLeOne.lean:162`) **[S]** :=
  `LocalUnitsRoots.main nonvanishing_transfer_characterSums_powerSeries …`. `Pin7` requires that a twisted moment
  Σ φ(x)x^e·mass(L, r, ξ, x) of the Coleman series L is nonzero mod l^{n₀+r}. That is the p-adic L-value input,
  presumably supplied by `exists_admissible_hecke_projection_nonvanishing` **[N]**.

### Sizes
- `KQC/`: 200 files, 23,405 lines. Of these, EulerFactorBounds is 8.8k, SymmetricPowerSymbols 3.9k,
  FrobeniusHodgeTateLaws 3.7k, NewformTwistNorms 2.4k and SphericalDecomposition 1.1k.
- The proof also lives in `AV/../Foundations/IwahoriReduction/`: 87 files, 16.3k lines (LangPolynomials 7.0k,
  NormProducts 4.5k, SiegelFixedPoints 4.7k). The directory names do not describe the content.
- Further pieces sit in `AbelianVarietyTheory/Proofs/FoundationProofs/*Statement.lean` (Siegel units, Coleman norm
  operator, dlog law).
- The total is therefore **well above 23k lines (at least ≈40k)**. An exact total needs a reachability closure.
- The explicit-reciprocity part alone (HT laws, smoothed classes, Coleman, dlog) is roughly ≥4k lines inside `KQC/`
  plus unknown amounts elsewhere: **undetermined**.

### Assessment for (II)
- **Special case.** The formalised result is Kato's rational Selmer vanishing for ordinary, good-reduction, l odd,
  weight-(2e+1) forms that are residually Eisenstein for an imaginary quadratic θ. That is the case the application
  needs. It is not Kato's main-conjecture divisibility.
- **First formalisation.** If faithful, it would be the first formalisation of Kato's Euler system and of an explicit
  reciprocity law of this kind, a major result.
- **Flag (worth checking).** `ES W A` yields H¹_f(W) = 0 for **the same** W that carries the Euler-system class
  (`es_vanish`). Classically an Euler system in H¹(ℚ, V) bounds the Selmer group of V*(1). Here W*(1) ≅ W⊗θ⁻¹(1)
  has Hodge–Tate weights (1−e, 1+e), not (e, −e). Either the normal form `Nf` or `es_vanish` handles the
  duality/twist, or something is mis-stated. Undetermined; `es_vanish` is the first thing to read.
- Residual reducibility (W ≡ θΨ ⊕ Ψ^{−1}) normally obstructs Euler-system arguments, because the Chebotarev step
  needs big residual image. `Used.irr` is irreducibility in characteristic 0 only. How `es_vanish` handles a
  reducible residual representation is undetermined. Since only rational vanishing is claimed, residual
  reducibility costs only bounded torsion, so this is plausible but unverified.

---

## III. `LemmaK`: Soulé-type bound on H²

### Statement **[S]**
`AV/GeneratorCountTuples/LemmaK.lean:13`
```lean
def kBound (C : ℝ) (e n D : ℕ) : ℝ := exp ((2 * e * n) ^ C * log (2 * D))
def LemmaK (CK : ℝ) : Prop := ∀ l L Ω (D : LData L Ω l), IsTotallyComplex L → HasMuQ l L → ∀ e ≥ 1,
  Finite (H2 (zlTw D (e+1))) ∧ log (Nat.card (H2 (zlTw D (e+1)))) ≤ kBound CK e [L:ℚ] |disc L|
```
In words: for a totally complex L containing μ_l (μ_4 if l = 2), H²(O_L[1/l], ℤ_l(e+1)) is finite and
log #H² ≤ (2|D_L|)^{(2en)^{C}}. That is **double-exponential in poly(e·n)·log D**, far weaker than Soulé's bounds.
The bound depends only on e, n = [L:ℚ] and D = |disc L|, and is uniform in l. l = 2 is included (via μ_4).

### Proof skeleton **[P-skel]**
- `lemmaK_litN_alt hN := lemmaK_of_litN_alt hN bOdd` (`…/DenseThresholdCases/KFinal.lean`) →
  `lemmaK hB (pt_s hN) lfK ltK` (`CC/LemmaKOfLitN.lean`) → `lemmaK_of_steps` (`CC/LemmaKOfSteps.lean:170`, 178 lines,
  **[P]**: a pure composition of 21 step propositions):
  - **Chain-level group homology.** `SChain`, `SPrism`, `SPrismMul`: bar-complex identities and prism operators for
    conjugation.
  - **Soulé's cyclotomic cycles.** `SZc`: `zc q e` is a (2e+1)-cycle for ℤ/q. `SRel`: a linear relation among the
    images of zc under dilations. `SEta`: a combinatorial identity with powers of 1+l^c (Soulé's trick for the
    eigen-projection).
  - **Detection on finite fields.** `STrans`, `SCoc`, `STheta`: for a finite field k with μ_q ⊂ k, an additive
    family θ of functionals on H_{2e+3}(GL_n(k), ℤ/q) with θ(prism·χ_x(zc)) = x^{e+1}·v(g). This is Soulé's
    detection by characters and a transfer to k^×, done without Quillen's computation of K(F_q). `SPhi`: pullback
    along reduction O → k gives a "primitive family" compatible with stabilisation and ψ-operations.
  - **Construction (the K → H¹ surjectivity, in homology form).** `SClass`: for L ⊂ F = L(μ_{l^ν}) with generator γ
    of Gal(F/L) acting by 1+l^c (`Lay`), and α ∈ F^× whose divisor is an eigen-divisor (`DivDel`), there is a cycle
    y ∈ H_{2e+3}(GL_N(O_L), ℤ/l^ν) whose reduction at almost every prime r evaluates under θ to
    pe(…)·(the residue symbol of the γ-eigen-norm of α). `SStein`: a Steinitz-type lattice lemma.
    `SDetect`: if β is an l^ν-th power modulo almost all split primes, then β is a global l^ν-th power.
  - **Counting.** `SUpper`: the number of distinct l^k·Φ(cycles) is at most
    (l^ν)^{r₂}·tc(N, k+1)·tc(N, k). This combines `BOdd` (rank of the span of the "Adams-type" sequence zSeq in
    H_{k+1}(GL_n(O_L)) is at most r₂) with the torsion tc of H_*(GL_N(O_L)). `SFew`/`SCount` then give
    #EqHom(γ, (1+l^c)^{e+1}, l^ν) ≤ B. That is the number of Kummer classes in the χ^{e+1}-eigenspace, i.e.
    #H¹(O_F[1/l], μ^{⊗e+1})^{Gal} up to bounded factors.
  - **Bounds and descent.** `SSha` → `shaInv L l E` is at most log_l B. `SLayer` adjoins μ_{l^c} with controlled
    degree and discriminant. `STors` (`CC/ExponentLe.lean:122`, via `torsAll`) gives
    log #tors H_m(GL_N(O_L)) ≤ kBound C. `SNum` assembles these into `ShaK`. `SFinal`
    (`PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ShaK → LemmaK`) converts the Ш bound into the H²
    bound by duality.
- **Borel input.** `bOdd_zk` (`AV/LiteratureResults/KTheoryStability/ReductionBoundsTorsion/TorsionIntegers/Bridge.lean:34`)
  → `bStarOdd` (`…/FinalOdd.lean`) **[S]** = `sBStarOdd_of sChain sSep' sBridge sStab (sSurj_of …Hecke, PU, Mom, Whit,
  Cen, Gap, Loc, Mean, Inv) (sWtOdd_of … sStokes_of)`. `SWtOdd` **[S]** says that integrating any G-invariant
  (k+1)-form on the symmetric space over a cycle decomposes as Σ_{w ∈ r₂ places} c_w·τ_w plus higher-weight parts
  that the zSeq recursion kills. This is a van Est / Borel-regulator argument with Stokes, partitions of unity,
  Whittaker smooth forms and Hecke operators.
  - It is **not** Borel's full computation of H^*(GL(O_L), ℝ). It is only the rank bound ≤ r₂ for the
    zSeq-subspan, which is all `SUpper` needs.
- **Reduction theory.** `KT.tors_le` (`AV/HermiteNormalForms/Assembly.lean:25`) **[S]** applies
  `KH.mainFace (Gm L N) (Sx L N) …`. GL_N(O_L) acts on an exact complex `Sx` built from **Hermite normal forms**,
  with orbit counts bounded by `orbnum` (≤ (2|D|·nN)^{24·m·(nN)³·N}) and bounded stabilisers. The torsion bound
  follows (Soulé's equivariant method, with Hermite normal forms in place of Voronoi/Ash–Rudolph perfect forms).
  `HermiteNormalForms/` has 42 files and 2,454 lines.
- **Homological stability.** `KTheoryStability/HomologicalStability/` (71 files, 5.7k lines, unread) presumably
  feeds `SStab` (stabilisation, n ≥ 2(k+1)+4) **[N]**.

### Answers for (III)
- **Group.** H²(O_L[1/l], ℤ_l(e+1)), étale/Galois cohomology. **No algebraic K-groups are defined.** The archive has
  no K_n(O_L), no plus-construction and no Hurewicz map. Soulé's argument is run directly on group homology of
  GL_N(O_L) and GL_n(k) with explicit cyclotomic cycles, and Galois cohomology enters through Kummer theory and
  Poitou–Tate.
- **Link to cohomology.** It uses the direction Soulé proved in 1979: Kummer classes are hit by homology classes,
  made explicit as detection by finite-field characters plus Chebotarev-type detection. It does **not** use
  Quillen–Lichtenbaum, Voevodsky–Rost or Dwyer–Friedlander. Only "few Kummer classes ⇒ small Ш ⇒ small H²" is needed.
- **Pieces present.** Reduction theory (Hermite normal forms rather than Voronoi), an equivariant torsion bound, a
  partial Borel rank theorem and stability. Hurewicz: no.
- **Assessment.**
  - It is weaker than its name. The bound is double-exponential, much cruder than Soulé's. Its input is a weak
    Borel-type rank statement, and it needs μ_l ⊂ L (L totally complex).
  - It is sufficient for the application: `ThmBab` needs exp(x^{4ε/5}) only for a few small twists e'.
  - It contains genuine first-formalisation content: Soulé's cyclotomic-cycle detection, an equivariant torsion bound
    for GL_N(O_L) and a Borel-type regulator argument.
  - Sizes: `KTheoryStability/` 286 files, 34.4k lines (ReductionBoundsTorsion 28.5k, HomologicalStability 5.7k);
    `CC/` 26 files, 8.95k lines; `HermiteNormalForms/` 2.45k.
  - Nothing is conjecture-shaped. The Borel step is unusual (Whittaker forms, Hecke operators) and was not read.

---

## Conjecture-shaped or unusual items, and where the trail went

| item | finding |
|---|---|
| `Rec` (reciprocity) | proved from `PoitouTateDuality` + `UnramifiedOrthogonality` (`recip`). `PoitouTateDuality` reaches `ML.iv`/`lemmaK` from the `HypothesesH'` / `LiteratureRankNHypothesis` bundles (`pt_s hN`); which theorem inhabits it was not traced here |
| `Pin7` free predicate in `zetaUr_of_halves2` | instantiated with the concrete `KZ.Pin7` (reciprocity + p-adic L nonvanishing); not a trivialising choice |
| `ES` with single-prime tame relations | sufficient for rational vanishing only; matches the claimed conclusion |
| Euler system on W bounding H¹_f(W) | duality bookkeeping unchecked (see II); **highest-priority check** |
| `BOdd` | a custom, weakened Borel rank statement; proved in-archive by an unusual route; unread |
| `LemmaK` bound | double-exponential, so much weaker than Soulé; enough for its use |

## What to read next (priority order)

1. `GlobalTheory.Ord2.es_vanish` (called in `…/FoundationProofs/VanishOrdLOfZetaUr.lean:23`) and
   `exists_ordinary_normal_form_unramified_source`: how an Euler-system class in H¹(W') yields H¹_f(W') = 0
   (duality, twist, residual reducibility).
2. `kato_tame_relation_projected` (`UpperTheory.V.Z.Kato.Nb`) and `clsBmu`/`LiftB` (`FD/IsZetaSystemFixedExponent.lean`):
   what the zeta classes are (K₂ cup products, or moments of Kummer classes of Siegel units).
3. `K5.hco` (`KQC/SmoothedZetaClasses/Hco.lean`, 322 lines) and `law_of_inputs`; `RecOne.kummer_eq_dlog_one`
   (`…/FoundationProofs/KummerCochainEqDlogExplicitReciprocity.lean`, 193 lines): the explicit reciprocity proof.
4. `Kd.C7.LocalUnitsRoots.main` and `nonvanishing_transfer_characterSums_powerSeries`: where L-value nonvanishing
   enters Kato.
5. `bStarOdd` components (`sSurj_of`, `sWtOdd_of`, `sStokes_of` in `KTheoryStability/ReductionBoundsTorsion/`):
   the Borel-type rank bound.
6. `SClass` proof (`CC/SClassOf.lean`) and `sFinal` (`CC/SFinal.lean:100`): Soulé's construction and the Ш → H² step.
7. `PFF/`: `nuSysEx` body (lines 140–275), `key` (`FrobFix.lean:68–142`), `pick` body, `exc`. Then check `den` in
   `alN` for extra l-power.
8. `StickBound` pieces `lenPow`, `gen`.
9. `KT.tors_le` / `KH.mainFace` (HermiteNormalForms) and `HomologicalStability/`.
