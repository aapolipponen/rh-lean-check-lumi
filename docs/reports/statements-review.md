# Review of intermediate statements in the Alpöge RH archive

Date: 2026-11-20. Read-only source review of `/bulk/shared/rieman/lean/src` on chili (nothing compiled, nothing executed).
Paths below are relative to that `src` directory. "Verified" means I read the Lean definition (and the
definitions it uses, to the depth stated). "Impression" means my mathematical judgement without a full read.

Scope: the four definitions in `Statements.lean`, 18 `GlobalTheory.Published.*` statements spread over six areas,
and the three load-bearing statements (`VWin`, `Row0b`/`PropsB`, `IsRecT`). This review does not judge whether
the proofs are correct or whether RH is proved. It only asks whether each statement says what its name claims.

## 0. `Statements.lean` (verified)

All four definitions use only Mathlib objects and are standard:
`RiemannZetaZerosOnLine` says every zero of `riemannZeta` that is not a trivial zero `-2(n+1)` (and is not `s = 1`)
has real part 1/2. `DirichletLNonvanishingRightOfHalf` says `L(χ,s) ≠ 0` for every Dirichlet character, `Re s > 1/2`,
except at the pole (χ = 1, s = 1). `DirichletLZerosOnLine` and `PrimitiveDirichletLZerosOnLine` say zeros in the open
critical strip lie on `Re s = 1/2`, for all characters and for primitive characters. These are faithful
statements of RH and GRH for Dirichlet L-functions. The extra hypothesis `s ≠ 1` in the first one is harmless.

## 1. Summary table

| # | Statement | Area | Verdict | One-line reason |
|---|---|---|---|---|
| 1 | `Published.Linnik` | analytic NT | faithful | ∃ C,L>0 with least prime ≡ a mod q ≤ C q^L for all coprime a, q ≥ 1 |
| 2 | `Published.PartialZetaFunctionalEquation` | analytic NT | special case | Hecke FE for partial zeta of wide ideal classes, totally real fields only; `IsPartialZeta` requires analytic continuation, so not vacuous |
| 3 | `Published.HeckeTateFunctionalEquation` | analytic NT | special case | CM fields, unitary algebraic Hecke characters with nonzero ∞-type; Λ entire with explicit ε (Gauss sums); `ExpAt` not traced |
| 4 | `Published.GlobalArtinReciprocity` | CFT | faithful (strong form) | Open surjection from ideles to G^ab with kernel closure(E^×·connected comp.), inertia, Frobenius, decomposition compatibilities |
| 5 | `Published.RayClassFieldSt` | CFT | faithful (finite moduli only) | For each nonzero integral 𝔪 an abelian L/K with Gal ≅ ray class group mod 𝔪, unramified outside 𝔪, Frobenius compatible |
| 6 | `Published.HilbertClassFieldJ` | CFT / CM | faithful | K(j(𝒪_K)) is the Hilbert class field, degree h_K, j(𝔞) separate classes, conjugates = all j(𝔞) |
| 7 | `Published.EllipticMainTheoremCM` | arithmetic geometry | faithful | Shimura's main theorem of CM for analytic ℂ/𝔞 ≅ E(ℂ), stated against any `IsGlobalArtinMap` |
| 8 | `Published.StoneVonNeumann` | rep. theory | faithful | p-adic (char ≠ 2) Heisenberg group: smooth irreducible rep with central char ψ exists and is unique |
| 9 | `Published.LocalConverseGL` | rep. theory | faithful | Henniart-type n×(n−1) converse theorem for cuspidals of GL_{m+1}, char-0 local field; ε defined by JPSS functional equation at s=1/2 |
| 10 | `Published.BernsteinZelevinskyFiniteness` | rep. theory | faithful | irreducible smooth ⇒ admissible; Jacquet functor and parabolic induction preserve finite length; induction commutes with contragredient |
| 11 | `Published.JacquetShalika` | automorphic | special case | strong multiplicity one for isobaric sums + JS bound q^{-1/2}<|α|<q^{1/2}; totally complex fields only |
| 12 | `Published.DeligneRibet` (+ `SiegelKlingen`) | analytic/ℓ-adic | special case | ℓ-integrality of c-smoothed partial zeta values at 1−k on narrow ray classes mod ℓ^n (no tame part of the conductor) |
| 13 | `Published.DualAbelianScheme` | arithmetic geometry | undetermined | claims the dual exists as an abelian *scheme* over an arbitrary base S, with no projectivity or noetherian hypothesis |
| 14 | `Published.SerreTate` (= `HomLift ∧ Lift`) | arithmetic geometry | faithful | Serre–Tate deformation theorem (p nilpotent, I nilpotent), incl. lifting of a relatively ample bundle |
| 15 | `Published.KawamataViehweg` | complex geometry | faithful | H^q(X, K_X⊗N)=0, q>0, X smooth projective over alg. closed char-0 k, N nef and big |
| 16 | `Published.NadelVanishingAndNonKltDivisor` | complex geometry | weakened | vanishing for *some* ideal sheaf whose support is the non-klt locus, not the multiplier ideal |
| 17 | `Published.ArithHilbertSamuel` | Arakelov | faithful | log #{small sections of mL+N} = (a/(D+1)!) m^{D+1} + o(m^{D+1}) for nef hermitian L with self-intersection a |
| 18 | `Published.PoitouTateNormalised` | Galois cohomology | special case | nine-term sequence, Ш duality, H^{≥3}=0; requires ℓ odd or F totally complex (the usual simplification) |
| 19 | `UpperTheory.Top.VWin` | load-bearing | undetermined (no published analogue) | custom bound on Σ_ℓ log ℓ · Σ_e length Ш^1(ℚ_ℓ/ℤ_ℓ(−e)) over large abelian fields; many magic constants; quick vacuity checks pass |
| 20 | `UpperTheory.GalStar.Row0b recT` | load-bearing | weakened | Galois reps for RACSDC π on CM fields, but local–global compatibility away from ℓ only in narrow cases |
| 21 | `IsRecT` / `RecTExists` | load-bearing | weakened | a "partial LLC": pinned down only on "Good" representations; elsewhere only dimension, irreducibility, twist and |central char| constraints |

Counts (21 rows): faithful 10, faithful with a restriction 1 (row 5), special case 5, weakened 3, undetermined 2,
vacuous-looking 0.

## 2. Per-statement notes

### 1. Linnik. `Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/PrimesInProgressionNonempty.lean` (verified)
```lean
def Linnik : Prop :=
  ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
    (leastPrimeMod a q : ℝ) ≤ C * (q : ℝ) ^ L
```
`leastPrimeMod a q = sInf {p | p.Prime ∧ p ≡ a [MOD q]}`. The file also proves the set is non-empty (Dirichlet),
so `sInf` is not the junk value 0. This is exactly Linnik's theorem. Faithful.

### 2. PartialZetaFunctionalEquation. `…/PublishedTheorems/Divisors₂/PartialZetaFunctionalEquation.lean` (verified to depth 1)
For a totally real F, wide ideal classes C, C' with C·C' = [different], there exist partial zetas Z, Z' with
`d_F^{s/2} Γ_ℝ(s)^n Z(s) = d_F^{(1-s)/2} Γ_ℝ(1-s)^n Z'(1-s)` away from Γ poles. The non-vacuity check matters here:
`IsPartialZeta C Z := DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s, 1 < s.re → HasSum (Σ_{J∈C} N J^{-s}) (Z s)`
(`Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean:95`). Holomorphy on ℂ∖{1}
pins Z down uniquely, so the existential is not trivially satisfiable. This is Hecke's functional equation,
restricted to totally real fields and wide classes. Special case.

### 3. HeckeTateFunctionalEquation. `…/Divisors₂/HeckeTateFunctionalEquationCM.lean:244` (verified to depth 2)
For a CM type φ on a totally complex E and a unitary Hecke character χ with ∞-type n ≠ 0, there exist entire Λ, Λ'
(`IsCompletedL`: `Differentiable ℂ Λ ∧` for Re s > 1, Λ = archFactor·(Euler product)) with
`Λ(s) = archEps n · finEps χ a s · Λ'(1-s)`, where `finEps` is an explicit product of local Gauss-sum epsilon factors.
`HChar E` is the subgroup of continuous characters of `(AdeleRing (𝓞 E) E)ˣ` trivial on E^×
(`Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean`). That is substantive. Not traced: `ExpAt χ w (a w)`
(it should mean a(w) is the exact conductor exponent) and the `HChar` Euler factor. Excluded: finite-order
characters and non-CM fields. Special case.

### 4. GlobalArtinReciprocity. `…/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70` (verified)
`∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art`, where `IsGlobalArtin` has five fields: `IsOpenQuotientMap`, kernel =
closure of (E^× ⊔ connected component at ∞), local units ↔ inertia, uniformizer ↦ (geometric) Frobenius,
closure of the local image = decomposition group. Here `Gab` is `TopologicalAbelianization`. This is a full-strength statement. Faithful.
(A second formulation, `IsGlobalArtinMap` in `ReciprocityTheory/NeutralLocalFields/Reciprocity.lean:127`, uses the
arithmetic normalisation and `ker = connectedComponent 1`. It is also correct.)

### 5. RayClassFieldSt. `…/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean` (verified at the `_iff` restatement)
`rayClassFieldSt_iff_artinIso` restates it as: for each K and nonzero integral 𝔪, an abelian L/K and an isomorphism
RayClassGroup 𝔪 ≃* Gal(L/K) with L unramified at primes not dividing 𝔪 and with matching Frobenius. Moduli
are finite only (no real places), so this is the "wide" ray class field. Faithful for finite moduli. I did not
open `RayClassGroup` itself.

### 6. HilbertClassFieldJ. `…/Divisors₂/ExistsEqOfNatCastMulMem.lean:66` (verified at the statement level)
For imaginary quadratic K: K(j(𝒪_K)) is the Hilbert class field, [K(j):K] = h_K, j(𝔞) = j(𝔟) ⇔ [𝔞] = [𝔟],
#{j(𝔞)} = h_K, and the Galois conjugates of j are exactly the j(𝔞). This is the classical theorem in full. Faithful.

### 7. EllipticMainTheoremCM. same file, line 56 (verified)
For every `Art` with `IsGlobalArtinMap`, σ ∈ Aut(ℂ/K), an idele s with Art(s) = σ|K^ab, and an analytic isomorphism
ξ : ℂ/𝔞 ≅ E(ℂ), there is a unique analytic ξ' : ℂ/s^{-1}𝔞 ≅ E^σ(ℂ) with σ(ξ(x)) = ξ'(s^{-1}x) on K/𝔞. This is
Shimura's main theorem (Silverman, Advanced Topics, II.8.2). The hypothesis on `Art` is satisfiable, since
`GlobalReciprocity` is the existence statement, so the statement is not vacuous. The proof ignores `O`
(skeleton.md). Faithful. Sign conventions were not checked.

### 8. StoneVonNeumann. `…/GlobalTheta/PlaneFormNondegenerate.lean:59` (verified)
Heisenberg group on (W, B), with B alternating and nondegenerate over a nonarchimedean local field F of char ≠ 2. For ψ ≠ 1
continuous: a smooth (`IsSmooth`: open stabilisers) irreducible representation with central character ψ exists,
and any two such are isomorphic. This is the smooth p-adic Stone–von Neumann theorem. Faithful.

### 9. LocalConverseGL. `…/GaloisCohomology₂/LocalConverseGL.lean` (verified to depth 2)
```lean
∀ π₁ π₂ : IrrRep (GL (Fin (m + 1)) k), IsCuspidal π₁.ρ → IsCuspidal π₂.ρ →
  (∀ τ : IrrRep (GL (Fin m) k), ∃ e : ℂ, HasPairEps ψ π₁.ρ τ.ρ e ∧ HasPairEps ψ π₂.ρ τ.ρ e) →
  Nonempty (π₁.ρ.Equiv π₂.ρ)
```
`HasPairEps` (`…/AutomorphicForms₂/HasExponentZeroIff.lean:100`) is the JPSS local functional equation at s = 1/2,
including the factor ω_τ(−1)^m. It must hold for all Whittaker functionals and for every linear functional I that is
right-invariant on test functions (`IsInvIntegral`). I checked the vacuity risk: for cuspidal π the integrands are
N-invariant, locally constant and compactly supported mod N, so I acts on them as a multiple of Haar measure. Hence an
e exists (the ε-factor, which equals γ since L(π×τ) = 1), and for non-generic τ any e works. Twisting τ by |det|^t
recovers every s. Restrictions: char-0 field, cuspidal π, twists by GL_{n−1} only. This is the classical
n×(n−1) converse theorem. Faithful.

### 10. BernsteinZelevinskyFiniteness. `…/TwistedTraceFormula/HasFiniteLengthOfIsIrreducible.lean:49` (verified)
A conjunction of `IrreducibleAdmissible` (smooth irreducible ⇒ admissible), `JacquetFiniteLength`,
`InductionFiniteLength` and `InductionContragredient` (an explicit integral pairing). All are for GL_n over a
nonarchimedean local field. These are standard Bernstein–Zelevinsky facts. Faithful.

### 11. JacquetShalika. `…/GaloisCohomology₂/StrongMultiplicityOne.lean:202` (verified to depth 2)
`JacquetShalikaRigidity`: if the Satake multisets of ⊞π_i and ⊞π'_j agree at cofinitely many places, then the
families agree up to a bijection. `JacquetShalikaBound`: for unitary cuspidal π, every Satake parameter α satisfies
q^{-1/2} < |α| < q^{1/2}. `CG E a` is the set of isomorphism classes of `CuspSub`. A `CuspSub` is a nonzero
irreducible stable subspace of cusp forms, and `IsAutForm` has five fields (left-invariance, open level, K-finiteness,
Z-finiteness, moderate growth), with constant terms vanishing on every maximal parabolic. Substantive. Restriction:
E totally complex. Special case.

### 12. DeligneRibet. `…/Divisors₂/SiegelKlingenDeligneRibet.lean:45` (verified to depth 2)
For totally real F, modulus ℓ^n, and ε a ℚ-valued, ℓ-integral function on ray classes: for 𝔠 coprime to ℓ and k ≥ 1,
`L(ε,1−k) − N𝔠^k · L(ε(𝔠·),1−k) ∈ ℤ_ℓ`, with L the holomorphic continuation (`IsRayL`). `RayRel`
(`Formalism/SharpRestriction/GlobalSchurBounds/ShortIntervalPrimes.lean:25`) uses totally positive a, b ≡ 1, i.e.
*narrow* ray classes, which is the correct setting. The conductor is restricted to a pure ℓ-power (no tame part
𝔣₀). Special case, faithful otherwise.

### 13. DualAbelianScheme. `…/Divisors₂/ExistsCrystalPairing.lean:25` (verified to depth 2)
```lean
∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
  ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧ … ∧ IsDual A B P ∧ IsDual B A (swap P)
```
`IsAbelianScheme` (`ReciprocityTheory/…/AbelianSchemeQuotients/IsAbelianScheme.lean:13`) is a commutative group
object that is smooth, proper and geometrically connected over an *arbitrary* scheme S. `IsDual` (`…/Divisors₂/IsAdditiveOfUniversal.lean:73`)
asks for an additive Poincaré bundle that is trivial along 0 and universal for additive line bundles on A×T.
That is a genuine representability statement. My impression, not verified: the standard references (Faltings–Chai
I.1.9, Raynaud) construct the dual in general as an algebraic space, and as a scheme under projectivity or
base hypotheses. This statement has no such hypothesis, so it is either a known-but-less-standard fact or something
stronger than the usual literature. I could not decide within the budget. A specialist should look at it.
Verdict: undetermined, not an error claim.

### 14. SerreTate. `Development/AbelianVarietyTheory/Definitions/Divisors/TowerRedToBaseIff.lean:61` (verified)
`HomLift`: homomorphisms lift uniquely given compatible maps of p-divisible groups. `Lift`: given a projective lift
A' of A₀, any lift G of the p-divisible group comes from an abelian scheme A that also carries a relatively ample
bundle. At first I suspected the ample-bundle clause was too strong. It is fine: with p and I nilpotent, a
p-power of an ample bundle lifts, because the obstruction is killed by p. Faithful.

### 15. KawamataViehweg. `…/Divisors₂/KawamataViehweg.lean` (verified to depth 2)
H^q(X, K_X ⊗ N) = 0 for q > 0. Here X is integral, smooth of dimension D and projective over an algebraically closed
field of characteristic 0, and N is nef (degree ≥ 0 on complete curves) and big (`∃ᶠ m, c·m^D ≤ h^0(mN)`, i.e. limsup > 0).
`K` is a `CanonLB`, a line bundle trivialised locally by D-forms. The file contains an `example` showing that ℙ^D
with 𝒪(1) satisfies every hypothesis, which is a non-vacuity check. Faithful.

### 16. NadelVanishingAndNonKltDivisor. `…/Divisors₂/IsLogCanonicalMultipleCanonical.lean:545` (verified at the statement level)
`NadelVanishingPair` concludes `∃ J : X.IdealSheafData, (support J = non-klt locus) ∧ H^i(J ⊗ N) = 0`. Nadel's theorem
is about the specific multiplier ideal 𝒥(Δ). Here only *some* ideal with the right support is asserted, which is
weaker, though plausibly enough for the downstream use (the Angehrn–Siu style point separation in
`IsolatedNonKltDivisor`). `IsolatedNonKltDivisor` (Kollár/Angehrn–Siu concentration with explicit constants c_e)
was only skimmed. Weakened.

### 17. ArithHilbertSamuel. `…/Divisors₂/SmallSecTensTriv.lean:14` (verified to depth 2)
Here `IsArithVar` means k is a domain finite over ℤ and X is integral and projective of relative dimension D.
`HermLB` is a line bundle with C^∞ metrics at every σ : k → ℂ. `IsNef` means semipositive metrics plus nonnegative
degree on vertical curves. `IsSelfInter a` gives the arithmetic height of the generic point. The conclusion is
finiteness of small sections and log #smallSec(mL+N) = a/(D+1)!·m^{D+1} + o(m^{D+1}). This is the nef arithmetic
Hilbert–Samuel theorem (Gillet–Soulé, Zhang, Moriwaki). Faithful.

### 18. PoitouTateNormalised. `…/GaloisCohomology₂/PoitouTateNormalised.lean` (verified at the statement level)
Normalised local invariants exist and are bijective. For S containing the places above ℓ and a finite discrete
ℤ/ℓ^r G_S-module M: the nine-term exact sequence, Ш duality, and H^n = 0 for n ≥ 3. The hypothesis ℓ ≠ 2 or F
totally complex is the standard way to avoid real places. I did not open `NineTermExact`/`ShaDual`. Special case.

## 3. Load-bearing statements

### 19. `UpperTheory.Top.VWin`. `Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` (verified to depth 2)
In plain terms: for every primitive Dirichlet character ψ (`PChar`), every ε ∈ (0, 1/52) and every choice of
"page" e(x) with 2^{e(x)} ≈ x^{2+8ε}, there is J ≥ 1 and X₀ with the following property. For X ≥ X₀ and every prime
pair (q, d) in the window at scale X^{1/J}, there is Y ∈ [X^{1/J}, X^{1/2}] such that for every x ∈ [Y, Y²] the
following holds:

for every number field E that is the fixed field, inside ℚ(ζ_N), of
{a : a ≡ ±1 mod 2^{e+2}, ψ(a) = 1, (a/q) = 1, (a/d) = 1},
```
Σ_{ℓ ∈ S} log ℓ · Σ_{e'=1}^{⌊x^401⌋−1} length_{ℤ_ℓ} Ш¹(G_{E,S_ℓ}, ℚ_ℓ/ℤ_ℓ(−e'))  ≤  sqrt(exp(x^ε))
```
for every finite set S of primes. Each Ш¹ must also be finite.

The window pair (q, d) is defined by these conditions: q ≡ 3 mod 8 prime, d ≡ 7 mod 16 prime, log q ∈ (T/2, T], log d ≈ T·(log Y)²,
q | d+1, and every odd prime ≤ T divides d+1, where T = Y^{ε/5}.

`shaLen` is `Module.length ℤ_ℓ (Sha1 …)`, with the twist given by the ℓ-adic cyclotomic character on G_S, S = places
above ℓ (`Formalism/GaloisCohomology/Statement.lean:54-78`).

Flags:
- **Magic constants**: Ct = 401, ε < 1/52, the exponent 2+8ε, ε/5, the residues mod 8 and 16, and the requirement
  that every odd prime ≤ Y^{ε/5} divides d+1. This is the shape of an analytic argument's parameter bookkeeping, not
  of any published theorem. It is not a literature statement.
- **Vacuity checks I did**:
  - `VVle` quantifies over *all* `ld : ∀ p, LData E Ω p`. If `LData` could be empty, VVle would hold trivially.
    But `LData` (S = places above ℓ, chosen places A, and χ with χ ∘ toGS = cycZ) is proved nonempty by
    `theorem ldataExists : LDataExists` (`Formalism/GaloisCohomology/GaloisCohomologyProofs/LdataNonempty.lean:48`).
    So it is not vacuous for that reason.
  - `WinPair` could in principle be unsatisfiable, which would make VWin hold vacuously. My heuristic:
    d ≡ −1 mod (q·∏_{p≤T} p) with modulus ≈ e^{2T} and d ≤ e^{T(log Y)²} needs only a Linnik-type prime in a
    progression with growing exponent, so pairs should exist for large Y. I did not verify that the archive
    proves existence.
- The quantifier order (∀ e(·) ∃ J ∃ X₀ ∀ X ∀ (q,d) ∃ Y ∀ x) is unusual but not suspicious by itself. J must be ≥ 2
  for Y to exist.
- What it measures (my impression): lengths of Ш¹(ℚ_ℓ/ℤ_ℓ(−e)) are, via Poitou–Tate, ℓ-parts of étale
  K-groups / H²(ℤ_ℓ(1+e)). Their product over ℓ is tied to zeta values at negative integers of the abelian field E.
  So VWin is a quantitative bound of "Bernoulli-number size" type over a huge family of abelian fields.
  That is the real content of the argument and should be reviewed by number theorists.
  Undetermined.

### 20. `Row0b` / `PropsB`. `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean` (verified to depth 2)
For a CM field E, ℓ, ι : Q̄_ℓ ≅ ℂ, and a regular algebraic polarized cuspidal π of GL_a(𝔸_E), there is r : G_E → GL_a(Q̄_ℓ)
that is continuous and semisimple, with Hodge–Tate weights HT(τ) = (a−1)/2 − (infinitesimal character) and
HT(τ∘c) = wt − HT(τ). The local conditions are much weaker than the published theorem
(Harris–Taylor, Shin, Chenevier–Harris, Caraiani):
```lean
structure AwayB (x y : WD h) : Prop where
  dim  : x.lpDim = y.lpDim
  tor  : Tor y → y.mono0 → x = y
  tame0 : IsQpBig w y.lpDim → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g, deg g = 0 → x.charPol g = y.charPol g
```
Away from ℓ, full local–global compatibility (x = y) is asserted only when the local parameter y is *abelian*
(`Tor y`: Weil-group commutators act trivially) with N = 0. A second case covers tame (`TmW`), "square-free"
(`Sqf`) parameters at places with E_w ≅ ℚ_g and g > 16a². There only the inertia characteristic polynomials and
N = 0 are asserted, not Frobenius. In every other case only dimensions match. Above ℓ (`AboveB`), crystalline and
de Rham behaviour with the HT jumps is asserted at spherical places, and potentially semistable behaviour plus
`AwayB` for the Weil–Deligne representation in the abelian or tame cases. The `above` field quantifies over
`LocPrime`/`LocTied`/`LocBridge` data that I did not open. If those were unsatisfiable, the ℓ-adic Hodge part
would be vacuous. That is not checked.
Verdict: weakened, though the weakening goes in the "safe" direction (less is claimed). Note also that `away`
quantifies over *every* rc satisfying `Rc` (= `recT`), so it is stronger when `IsRecT` is looser. See row 21.

### 21. `IsRecT` / `RecTExists`. `Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean` (verified)
`IsRecT h rc := ∃ a (local Artin map) ha, LawsT a ha rc`, where rc : Irr(GL_n(E_w)) → WD. `LawsT` asserts:
- dimension;
- class field theory for n = 1;
- compatibility with Langlands classification by segments;
- cuspidal ↦ irreducible;
- unramified twists ↦ |·|^s twists;
- |det rc(x)| = |central character|.

Only for **"Good"** x does it assert twist compatibility, det = central character, contragredient ↦ dual,
injectivity, and depth-zero ↦ tame. `Good` means the cuspidal support consists of characters, or, when E_w ≅ ℚ_g,
of twists of depth-zero cuspidals. A `TypeLaw` pins down depth-zero cuspidals via Green/Deligne–Lusztig characters θ.
`RecTUnique` likewise claims uniqueness only on Good x.

So `RecTExists` is a much weaker statement than the local Langlands correspondence (Harris–Taylor, Henniart,
Scholze). On positive-depth (wild) supercuspidals rc is almost unconstrained. This is why the downstream
LGC in `AwayB` only says something in the abelian or tame cases. Not suspicious as a statement, but anyone citing
"the archive uses local Langlands" should know that it states and uses this partial version. Weakened.

## 4. What I could not check

- Deeper layers: `ExpAt` and the `HChar` Euler factor (row 3), `RayClassGroup`/`IsFrob` (row 5), `NineTermExact`/`ShaDual`/`GS`
  (row 18), `LocPrime`/`LocTied`/`LocBridge`/`WD` (row 20), and the `IsArithHeight` characterisation (row 17).
- Whether the archive proves `WinPair` is satisfiable (row 19). My heuristic says it should be.
- Whether row 13 (dual abelian scheme over an arbitrary base) goes beyond the literature.
- I sampled 18 of ~155 `Published` statements. None looked vacuous. The recurring pattern is "faithful, often
  restricted to the special case the argument needs" (CM/totally real/totally complex fields, char 0, ℓ odd).
