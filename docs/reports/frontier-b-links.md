# Frontier B: the `Link*` inputs, i.e. how Ш¹ lengths control each lift's local excess

Date: 2026-11-20. This is a read-only source study of `/bulk/shared/rieman/lean/src` on chili. I used only cat, sed and
grep over ssh, plus the declaration index `/bulk/shared/rieman/analysis/reach/decl-index.tsv`. Nothing was compiled or
run. Paths are relative to `src/`. It follows `core-gm.md`, `theta-chain.md`, `vacuity-check.md` and
`rhcheck/results/skeleton.md`. About 66 tool calls.

Tags:
- **[S]** means read in the statement or definition.
- **[P]** means read in the proof (in full, or the `have`/`obtain` skeleton as noted).
- **[N]** means inferred from names or from the shape of a statement.

## Overview (for a number theorist)

For each lift j and each "twisted" place w of the coefficient field, the archive's "local excess" `etaJ(j,w)` is the
length of a **congruence module**. Take the integral lattice M of the j-th lift's forms. Compare its projection onto the
Hecke eigenspaces of a distinguished set Zgood of eigensystems with its intersection with those eigenspaces. The length
of the quotient (projection / intersection) is `etaJ(j,w)`. This is the classical Ribet/Hida congruence-module index.
`etaJ` is bounded in two steps:
- (i) by Σ multiplicity × v(congruence ideal at π) (`adm1`);
- (ii) the congruence ideal at π is then bounded by a **Ribet-style lattice argument** (`GlobalTheory.CutCoreUnit.main`,
  read in full). The Galois representation attached to π is reducible, r_π = ρ_π ⊕ χ ⊕ χε^{-1} ⊕ … ⊕ χε^{-(t-1)}. A
  congruence of depth n between π and eigensystems outside Z produces cocycles cut out by idempotents of the Hecke
  algebra, one per off-diagonal block. Their lengths are bounded block by block:
  - the ρ-block by a Bloch–Kato Selmer length `sPi`;
  - the χ-block by v_ℓ(h_E), via class field theory;
  - each cyclotomic block ε^{-e} (1 ≤ e < t) by **len Ш¹(E, ℚ_ℓ/ℤ_ℓ(−e))**;
  - tame places Q by v(ζ_q − 1).

That is how the global Ш bound of VWin enters. It is neither Poitou–Tate nor Iwasawa theory. It is "congruence ideal ≤
Selmer/Ш" via generalized-matrix-algebra cocycles. The p-adic Hodge theory (Fontaine, Bloch–Kato, Tate duality, Euler
characteristic, Bhatt–Scholze/Wach modules) is used only to prove that the cut cocycles satisfy the right **local
conditions at places above ℓ**. Then (`export_bound_of_admissible`, read) everything is summed over ℓ with weight log ℓ.
The Ш terms give exactly Σ_ℓ vvTerm(ℓ) ≤ √b. The local terms give the per-lift loss **f·m·b·L²**. Here f = 2n = |PhiSet|
(the number of embedding labels τ), b = e^{x^ε} and L = x^ε. The factor m comes from the Hodge–Tate shape of each lift:
`ShapeJumps k m t` has exactly m "small" jumps, and `JumpConditions` requires jW ≤ deg(u)·m. Each such jump costs about
b/ℓ + log_ℓ b in local length. The constants are uniform in j by quantifier order. `QuadraticLogDerivCongr.lean` contains
no arithmetic congruence. Its namesake is a one-line Lean `congr` lemma (`subst; rfl`). `linkGLOBAL_of` is pure assembly.
L'/L(1, χ_d) enters only as the archimedean period term logΩ = γ + log(π/v) − L'/L(1, χ_d) inside MAIN, which has the
shape of a Chowla–Selberg/Kronecker-limit period.

---

## Q1. The statements

All of the following are in `Formalism/SharpRestriction/GlobalTheoremInputs.lean` unless noted [S].

```lean
def etaSum (L : SizeData₂ D) (j) := ∑ w ∈ L.supp.filter (muAt w ≠ mu0), lwP w * ramIdx w * D.what₂.etaJ j w
def vvTerm D l := if l.Prime then (∑ e ∈ Ico 1 D.R.t, D.what₂.shaLen l e) * log l else 0
def LinkN_at L j C := Summable (vvTerm D) →
  etaSum L j ≤ dZ0 j * (C * (f * m * b * L^2 + log x ^ 2 * Nc) + ∑' l, vvTerm D l)
def LinkN Fm := ∃ C x0, ∀ x ≥ x0, ∀ i, ShaFinOdd (Fm.D x i) → ∀ j ∈ lifts, LinkN_at (Fm.L x i) j C
def DIVinN_at L j C := etaSum L j ≤ D0 * (C * x^eps * (B0 + Nc))        -- B0 = f·m·b·x^ε
def LinkG_at X K C bo := (local lattice conditions at non-inert w) ∧ (Sv bounds) ∧
  ∀ w inert, p(w) ≤ X'' → (∀ j, 0 ≤ gain j w ≤ 4|TT|a/p) ∧
    (∑ j ∈ lifts, ∑ t ∈ TTw w, (vonMangoldtClassSum j t p − loG L C bo p)) − m·flG L C p ≤ (∑ j, gain j w) − tau w
  ∧ ServedOrbitsContained ∧ MeanKappaBound
def LinkG Fm := ∃ C x0 δ, δ → 0 ∧ ∀ x ≥ x0, ∀ i, LinkG_at (Fm.Gx x i) Fm.GK C (b ^ δ x)
def LinkS_at L C0 Γ η0 η1 e0 := (duS-normalisation) → (∀ u ≠ u', hsSq u u' ≤ (1+η0) duS u duS u'/D*) ∧
   (∀ u, hsDiagFull u ≤ e0 duS u) ∧ Dall ≤ (1+η1) D*        -- near-orthogonality of the period vectors
def LinkS Fm C0 := … η0, η1, √e0 ≤ exp(−x^{ε/8}) ∧ LinkS_at … (Γ = exp(C·m^5·f·L))
def GlobalTheoremInputs := LinkG ∧ LinkS ∧ LinkIRR ∧ LinkDIV ∧ LinkMu
def LinkGLOBAL Fm … := ChosenE → GlobalTheoremInputs → ∃ K cHH eK CL x0, ∀ x ≥ x0, x ∈ Win → ChainTied …
```
`LossBounds` (`Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:34`) is ASK(u0) − Ga(u0) ≤ LoP = cLoss·nT·m·b·x^{eLoss·ε},
together with IO ≤ LoP (core-gm.md). Its family form is `Lnk.Loss_at`
(`GlobalSchurBounds/QuadraticLogDerivCongr.lean:203`) [S]:
`IOsum ≤ C·|TT|·m·b·x^{eL ε}` and `Σ_t Σ_j ASK(a_t, t, w_j) − Ga ≤ C·|TT|·m·b·x^{eL ε}`.

**`divinN_of_hypV`** (`Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:117`) [S, P read in full]:
`HypV → LinkN → SmallLevelRankEq → DIVinN`. `vvRecord` turns `VVle E t √b` into Σ_ℓ vvTerm ≤ √b. `divinN_at` then uses
√b ≤ b ≤ B0 and log²x ≤ x^ε to absorb both the Ш term and f·m·b·L² = x^ε·B0 into D0·C'·x^ε·(B0+Nc). **The Ш term is
lower order: it only has to be ≤ b, and VWin supplies √b.**

**`etaJ`, concretely** [S]. `Rows.Data.etaJ : ℕ → Pl → ℚ` is an abstract field (`LocalRingCardinality/DataRows.lean:162`).
`NumTie.etaJ` (`LocalToGlobal/Divisibility/RowSideTie.lean:244`, `TupUsed.lean:102`) ties it to
`DefFam.etaJ = (F.L j t).etaU (lvlA P ψ) (Zs.Zl j t) w` (`Divisibility/LiftLat.lean:147`). Here
`etaW w = locLen w (Tl ℓ Z) (cutZ ℓ Z)` (`LiftLat.lean:116`), and in `RowLat.lean:153-155`:
- `Tl = matLat (lPr) (lvlNab)`: the image of the integral (`Nab`, integral-valued forms on the class set) ψ-level lattice
  under the orthogonal projection onto the Hecke-stable subspace Z;
- `cutZ = cutLat (fE) nabLat`: Z ∩ the integral lattice.

So etaJ(j,w) = length_w(projection lattice / intersection lattice). That is **the congruence module of Z inside the
algebraic automorphic forms of the j-th lift** (forms on a definite group: `CSD`, functions Cl → V). It is not a
Galois-lattice quotient or a Bloch–Kato condition. The same quantity on the Galois side is `NData.etaLoc i`
(`SharpRestriction/LevelLetterCocycles/DataN.lean:219`) [S]:
```lean
MtUp i  := eigSum(Zgood) ⊓ (MtIn ⊔ eigSum(Zgoodᶜ));   MtLow i := MtIn ⊓ eigSum(Zgood)
etaLoc i := lenUnit ℓ (MtUp / MtLow)                      -- congruence module, normalised by len(O/ℓ)
vcc i π  := lenUnit ℓ (O ⧸ ccAt T Z π)                    -- ccIdeal = ker(T → ∏_{x∉Z} O): congruence ideal at π
```
`TwistedPlaces.adm1` (`ResidueCharacters/TwistedPlaces.lean:133`) [S]: etaLoc i ≤ Σ_{π∈Zgood} mult(i,π)·(vcc(i,π) +
v_ℓ|level group|). This is the standard "congruence module ≤ Σ mult × congruence number" inequality.

## Q2. The global-to-local passage

**Lemma: `GlobalTheory.CutCoreUnit.main`**
(`Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:44`;
wrapper `GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit`) [S, P read in full]. Trimmed:
```lean
GlobalArtinReciprocity → GoodR r → IsOrthogonalIdempotentDecomposition r ρ π S → π ∈ Z → NoChiOff → UnrOut →
 (conditions at S, Q) → (∀ w | ℓ, LocBound (WpO ρ π) ∧ (∀ c ∈ [2,t], cutCoc(chiRatO c) ⊆ BD(locLat)) ∧ cutCoc(chiRatO 1) ⊆ Z1ur) →
 sFin → (∀ e ∈ (0,t), shaLen ℓ e < ⊤) →
 vcc i π ≤ sPi ρ π + ∑_{0<e<t} shaLen ℓ e + v_ℓ(h_E) + t·∑_{q∈Q} len(O/(ζ_q − 1))
```
Proof skeleton:
1. `length_heckeValueIdeal_le_determinant_bound`: len(O/cc(π)) ≤ len(cocRho) + Σ_{c<t} len(cocChi c). The cocycle modules
   `cocW` (`NonGaloisDescent/GlobalCore.lean:41`) are spanned by maps φ out of the generalized matrix algebra
   (S.X' → MatN) that are equivariant for the idempotents ψρ, ψχ_c and vanish on eigensystems outside Xs. This is the
   Bellaïche–Chenevier/Ribet "reducibility ideal ≤ off-diagonal cocycles" step.
2. ρ-block: `length_global_cocycles_le_sum_places_over`, `localCocycles_aboveEll_inCut_unitDelta`,
   `LocalGlobalSelmer.main` (unramified outside ℓ) and coboundaries = 0 give len(cocRho) ≤ len Sel = `sPi`.
3. χ-block, c = 0: the classes are unramified everywhere (above ℓ by `CutTrivIne.main` from the Z1ur condition). Then
   `UnramHom.length_le_classNumber hArtin` bounds them by v_ℓ(h_E).
4. Cyclotomic blocks, c ≥ 1 (character χ_{c+1}/χ_1 = ε^{-c}, `chiRatO`): the classes are unramified away from ℓ (the Q
   places are peeled off by `Cut.Peel.main`), and at w | ℓ their restrictions lie in `BD(locLat)`. Then
   `length_cyclotomic_block_cocycles_le_sha` (= `Cut.ShaBound.main`, statement read) gives len ≤ len(O/ℓ)·shaLen(ℓ, c).
5. The Q places give `inertiaCocycleBlock_length_le_of_quadraticRelation`. The final step is arithmetic.

So the global-to-local passage is **a Ribet/Urban-type lattice construction**. A congruence ideal of the j-th lift's
Hecke algebra at a twisted place is bounded by global Galois-cohomology lengths of the off-diagonal blocks of
r_π = ρ ⊕ ⊕_c χε^{-(c-1)}. The cyclotomic differences of the χ-blocks are exactly ℚ_ℓ/ℤ_ℓ(−e), 1 ≤ e < t. Ш¹ appears
because the local conditions at ℓ make these classes locally trivial in the relevant sense. Poitou–Tate,
Euler-characteristic and Iwasawa arguments do not appear in this lemma. The Euler characteristic and Tate duality are used
only locally (Q4). The page 2^e / VWin's t enters as the range 0 < e < t = `D.R.t`.

**The chain to `LinkN`** [P skeletons]:
- `UpperTheory.GalC.linkN_of_twGood_galoisPreconditions`
  (`ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean`) calls
  `linkN_along_family_of_localBounds (conclF_of_family_facts_and_bound_at_two_three hP … (at23_family_alt hP _))`.
- `GlobalTheory.LinkFam.main` (`Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean`):
  `ConclF → AdmF` (via `admittedStatements_of_localBoundsConclusion_alt`) and
  `→ LinkN` (via `N.linkN_of … TwistedPlaces.stmtF_holds`).
- `stmtF_holds` → `export_bound_of_admissible` (`LevelLetterCocycles/ExportBoundOfAdmissible.lean:1023`) [P] →
  `etaSum_le` (`MemPrimesOverOfMem.lean:558`) [P]:
  etaSum_j ≤ dZ0·(6 + nuBudget + log h_E + log|level group| + Σ_ℓ log ℓ·lamG ℓ) + dZ0·Σ vvTerm. Then `point_bound`
  shows that the bracket is ≤ 2000(C+1)³·f·m·b·L². The Ш term is passed through **verbatim**
  (Σ_ℓ log ℓ·VVr ℓ = Σ vvTerm), and h_E is summed by Σ_ℓ log ℓ·v_ℓ(h_E) ≤ log h_E.
- `GlobalTheory.NLinkClose.main_alt_alt` (`ThirdPlaceSeries/ImportsFurtherTail.lean:22`) [P skeleton] supplies the
  `Concl` record. Its pieces:
  - `large` (StarE, ℓ > lStar): `localBoundZeroAtLargePrimes_of_congruenceBound` from `CongBound_at`
    (`BlockTheory/NonGaloisCusps/BaseSizes.lean:87`: vCC ≤ sPi + shaSum + vClass + epsQ). That is proved by
    `NLinkE.main_alt_alt` (`ThirdPlaceSeries/AdmissibleParameterEventually.lean:30`) [P, read in full], which ends in
    `CutCoreUnit.main`.
  - `mid` (StarAD, medium ℓ): `star_ad_and_bb_le_of_joint_cond` (vcc ≤ sPi + Σ_λ len0 + VV + vhE + errorBound + 1/ℓ²).
    The table entries `len0` are the local lengths.
  - `two` (ℓ = 2, 3): `BoundAtTwoThree` with midF = C·f·m·b·log x + C x^C L².
  - `ram` (ℓ = q, d): `starG_of_thmB` with midG ≤ 2C·f·m·b.
  - `kill`: `KillAt` (`JointConditionsZpowers/CommutingEndomorphismCondition.lean`) [S], sPi ≤ nuL(ℓ) + 1/ℓ². Here nuL
    is a cyclotomic-tower quantity `KStar.Tree.nuOf ℓ (cyc ℓ E) (t·r)`, summed to `nuBudget = log QS + log(t·r)`.

## Q3. `QuadraticLogDerivCongr.lean` and `linkGLOBAL_of`

`Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean` (1892 lines) [S; P skeleton of `linkGLOBAL_of`]:
- **The name is misleading.** `quadratic_log_deriv_congr` (line 121) states: d = d' → quadraticLogDerivL d s =
  quadraticLogDerivL d' s, proved by `subst h; rfl`. `quadraticLogDerivL d s = Re(L'/L(s, (·/d)))` (line 113). It is a
  Lean "congr" lemma and asserts **no p-adic congruence**. Nothing in this file mentions D^aΩ·θ(0), divisibility by
  p^{a/p+…}, or Chowla–Selberg.
- The file defines the family-level provider predicates `Count_at`, `SlopesM_at`, `SlopesN_at`, `Lat_at`, `Frame_at`,
  **`Loss_at`**, `Nodes_at`, `Char_at` and `Win_at`, and the model `Mod` that turns a family point into the abstract
  `Data` of `CoreAtH`. **`linkGLOBAL_of` (853)** takes the providers as hypotheses (`hLoss : … → LinkG Fm → LossF Fm eL`,
  `hSN : LinkG → LinkMu → SlopesNF`, `hFr : … LinkS … → FrameF`, …). It `obtain`s everything and builds
  `ChainTied` with constants mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH. It records `B0 = (2·|A|)·m·b·x^ε`
  (`BNBounds`, so f = 2n) and the window `RestSize`. This is bookkeeping only. `linkGLOBAL` (1879) plugs in `latF`,
  `nodesF` and `size_windows_of_thick_set`.
- **Where L'/L(1, χ_d) actually acts** [S]: `logOm := γ + log(π/v) − logDerivativeAtOne` (`LocalRingCardinality/DataParams₂.lean:224`),
  and MAIN u = Σ_t (m·(ph(a_t) − a_t·logΩ) − a_t·log T). So the quadratic log-derivative is the archimedean
  period normalisation of the divisor main term. log Ω = γ + log(π/v) − L'/L(1, χ_d) has the shape of the
  Chowla–Selberg/Kronecker-limit expression for a CM period [N for that identification]. It is a **one-off** term,
  multiplied by a_t and occurring once per lift. It is matched against ASK's main term a(log a − 1 − γ + κ − …).
  `Char_at` (line 221) supplies ell ψ = L'/L(1, χ) for primitive χ.
- **The LinkG → LossBounds path** [S, P partly]: `Loss7.losses_of_small_share_weight`
  (`LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean:86`) takes `LinkG` and gives `LossesSmallShares`,
  i.e. `Loss_at` with error (3|K|+13)·|TT|·m·b. The unit is `unitU = |TT|·m·b` [P]. The work is in
  `loss_setting_family` and in the abstract `joint_discriminant_eventually` (not read). `LinkG_at` gives at each inert p
  that Σ_j Σ_t (vonMangoldtClassSum − loG) − m·flG ≤ Σ_j gain_j(w) − τ(w), with
  flG = C f N(m)² log_p a + C f (log_p a)². Summed with the weights sz(w) = 2·lw·ramIdx, this gives ASK − Ga ≤ O(|TT|·m·b).
  **LossBounds is therefore not the dominant loss.** Per unit it costs O(x^{eLε}).

## Q4. Where each literature input is used (all via `GlobalTheory.NLink.Hypotheses₂`, `NonGaloisDescent/BoundAtTwoAndThreeForFamily.lean:18`)

| Input | Consuming declaration | Use |
|---|---|---|
| **BhattScholzeIntegral** | `GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze` (`Proofs/InertiaEigenvalues/ExistsWachFunctorComparisonOfBhattScholzeStatement.lean`), called in `NLinkE.main_alt_alt` | Produces the Wach-module functor HW, the Fontaine functor F and the comparison Cm. These are the integral crystalline-lattice dictionaries in which the local conditions on cut cocycles are computed [S; N for the role]. |
| **BlochKatoLocal + LocalTateDualityK + LocalEulerCharK** | `GlobalTheory.T.blochKatoTop_of_localTateDuality_eulerChar` → `tableLineDegreeTwo.aux₃ = TopTheoremLocal` (per Wach lattice: `TopCore`), consumed by `GlobalTheory.UseLoc.main` (`AdmissibleOfLargeResidueChar.lean:24`) → `unramifiedEnlargement_cut_cocycles_blochKato` | Shows that the local restrictions at w \| ℓ of the cut cocycles satisfy the Bloch–Kato conditions (LocBound for ρ, BD for ε^{-e}, unramified for χ). These are the hypotheses that make the blocks count as Selmer and Ш classes in `CutCoreUnit.main` [S, P skeleton]. |
| same triple | `GlobalTheory.T.theoremE_corollaryA_closing_all_data` → `WachCoordinates.Conclusion1/2` (`LiftingTheoremLocalTheory`, `LocalCorollaryLifting`: `ThmELiftAt`, `CorAAt` with constant C₂), consumed by `star_ad_and_bb_le_of_joint_cond` | Local lifting bounds that give StarAD/BBLe at medium ℓ, i.e. the local lengths `len0` and error terms [S]. |
| **FontaineBcris** | `big_image_second_condition hP.font` (admG2) in `NLinkE.main_alt_alt`; `HTW.RecS.fam_jointBCD_closed_alt hP.font` in `NLinkClose.main_alt_alt` | Crystalline/de Rham properties of r_π at ℓ and the "BCD" band conditions [S; N for content]. |
| **GlobalArtinReciprocity** | `CutCoreUnit.main` → `UnramHom.length_le_classNumber` (`IndexDvdClassNumber.lean:172`) | Bounds the everywhere-unramified χ-block cocycles by v_ℓ(h_E) [P]. |
| LocalFinitenessK | not located on the lines I read | — |

## Q5. The losses, and uniformity in j

- **f and b** [S]. b = e^{L} with L = x^ε. f = |Tau| = |PhiSet| = 2·ord(H) = 2n (`card_Tau`, `card_PhiSet`, and
  `BNBounds` in `linkGLOBAL_of`: B0 = 2|A|·m·b·x^ε).
- **Origin of f·m·b·L²** [P for `export_bound_of_admissible`, `point_bound`, `etaSum_le`; S for the table predicates].
  Per prime ℓ, the local budget is `lamB`:
  - small ℓ, and ℓ = 3: C f m b log x;
  - ℓ = q, d: 2C f m b;
  - ℓ ≤ lStar: `bbB + lenB ℓ`, where lenB = (2f·m + f)·eP(ℓ) at split ℓ and (inert) 4f·C r·(…) + 2f·C·m·eP(ℓ).

  Here eP(ℓ) = C(1 + hB/ℓ + log_ℓ hB) and hB = b + Sc + etaSz + t + 2 ≈ b. Summing log ℓ·f·m·b/ℓ over ℓ ≤ lStar gives
  ≈ f·m·b·log lStar ≤ f·m·b·L².
- **Why the factor m.** The table entry at λ | ℓ is literally `lenA = (2·deg λ·m + 1)·e'` with e' = eA ≈ C(1 + 2b/ℓ +
  log_ℓ b) (`JointConditionsZpowers/LocalErrorBoundPlaces.lean:20-28`) [S]. Its justification is
  `EmbeddingTypes.JumpConditions`, jW(ρ, π, u) ≤ deg(u)·m, together with `ColengthRowPlaceBound`, which uses
  rowNum = deg·m·e' + r·c0 (`EmbeddingTypes.lean:280-296`) [S]. `ShapeJumps k m t` (line 99) fixes the Hodge–Tate jump
  shape of a lift: k−1 large jumps, **exactly m small jumps**, and the t weights 0..t−1. So each lift's Galois data has
  about m Hodge–Tate jumps per embedding. Each jump costs about b/ℓ + log_ℓ b of local lattice index, which has the shape
  of a Fontaine–Laffaille/Wach torsion bound in the weights [N]. That gives B0 ∝ m **per lift**. `DIV` and `SlopesN`
  carry C·m·B0 (one B0 per lift), so the total is ∝ m². With the x·b one-off terms this gives the x/m + m balance of
  core-gm.md.
- **Uniformity in j** [S, P]:
  - `LinkN := ∃ C x0, ∀ x ≥ x0, ∀ i, … ∀ j ∈ lifts, LinkN_at … j C`, so C is uniform in j by statement.
  - In the proof, `NLinkClose.main_alt_alt` fixes `Cs` from Hypotheses₂ constants (C₀ of `theoremE_corollaryA`), from
    family constants (C1, Ca, Cb, CT) and from `rowC C₂`, all before choosing x, i or a local index (each local index
    carries its own j). `export_bound_of_admissible` outputs 2000(|C|+1)³, which does not depend on j.
  - The j-dependent inputs are bounded by quantities that do not depend on j: jW ≤ deg·m (the m of the family, not j) and
    `SmallLevelRankEq` (dZ0 j = D0 for every j).
  - The family-level provider of the jump bound is `GlobalTheory.T.jump_bound_family_large` (not read). That is where
    uniformity of the Hodge–Tate shape across the m lifts must actually be proved.

## Q6. Unread on this path

- `GlobalTheory.T.length_heckeValueIdeal_le_determinant_bound` (`Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBoundStatement.lean`). This is the Ribet/GMA core inequality. Statement name only.
- `GlobalTheory.Cut.ShaBound.main` (`length_cyclotomic_block_cocycles_le_sha`): statement read, proof not.
- `GlobalTheory.UseFive.objects_globalStep_gen` (the idempotent decomposition S), `UnramHom.length_le_classNumber`, `Cut.Peel.main`, `CutTrivIne.main`, `LocalGlobalSelmer.main`.
- `GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt`, `GlobalTheory.ThmECorA.closing`, `GlobalTheory.HWL.exists_hw_fon_cmp_of_integral`, `unramifiedEnlargement_cut_cocycles_blochKato`, `exists_exactLocalConditionData_at_place`.
- `GlobalTheory.NLink.rowsAD_in_setting_alt` (`ThirdPlaceSeries/RowsADInSetting.lean:15`): the StarAD proof at medium ℓ.
- `GlobalTheory.T.jump_bound_family_large`, `eventually_prvJ_of_facts`: the jW ≤ deg·m input.
- `UpperTheory.N.at23_family_alt`, `UpperTheory.N.starSF_of_prints`, `NLink.starG_of_thmB`: ℓ = 2, 3, small ℓ, q, d.
- `GlobalTheory.T.exists_hubData_admJ_setup` (provides `KillAt`, i.e. sPi ≤ nuL), `SignatureChoiceCondition` → `BlochKatoReduction.Gen.sLen`, and `KStar.Tree.nuOf`.
- `GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt`, `N.linkN_of`.
- `Loss7.loss_setting_family`, `joint_discriminant_eventually`, `Loss.loss_points_of_choices` (`PowFourLtCeilThresholdPrime.lean:2039`).
- Who supplies `hLoss`, `hSN` and `hFr` to `linkGLOBAL`. `GlobalTheory.Top.link_gl` / `famGLmin_of_realPlaceSecondLayer … .link8` is still unopened.

## What to read next

1. `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound*.lean`
   (`length_heckeValueIdeal_le_determinant_bound`) and `NonGaloisDescent/GlobalCore.lean` (`cocW`, `ccOff`). This is the
   step "congruence ideal ≤ Σ cocycle lengths". If any real gap hides in the Ш → local link, it is here or in the
   idempotent decomposition `UseFive.objects_globalStep_gen`.
2. `Cut.ShaBound.main` (`LengthCyclotomicBlockCocyclesLeSha*.lean`): check that "BD at ℓ" really forces classes into
   Ш¹(ℚ_ℓ/ℤ_ℓ(−e)) with S = places above ℓ, up to len(O/ℓ).
3. `GlobalTheory.T.jump_bound_family_large` and `EmbeddingTypes.ShapeJumps`: the source of the per-lift factor m and its
   uniformity in j.
4. `GlobalTheory.UseLoc.main` → `unramifiedEnlargement_cut_cocycles_blochKato` and `TopClosing.blochKatoTop_…_alt`: how
   Bloch–Kato, Tate duality and the Euler characteristic give the local conditions.
5. `LossRequirementsOfSmallShares.lean` (`loss_setting_family`) together with `joint_discriminant_eventually`: the
   LinkG → LossBounds analytics, which are lower order.
