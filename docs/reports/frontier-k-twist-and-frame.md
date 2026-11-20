# Frontier K: the good auxiliary twist (`TwistingCharacterExistence`) and the near-isometric frame (`LinkS`)

Read-only source study, 2026-11-21, about 85 ssh/grep/sed calls on chili (`/bulk/shared/rieman/lean/src`), nothing
compiled or run. Extends frontier-e-ribet.md (Q3–Q5), frontier-a-divisor.md (Q4–Q5) and frontier-f-divisibility.md
(Task 4). Tags: **S** statement read, **P** proof read in full, **P-skel** have/obtain/refine skeleton read,
**N** inferred from names or shapes. Paths: `IE/` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`,
`NGD/` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/`, `SLT/` =
`Formalism/LocalToGlobal/SiegelLatticeTheory/`, `LLC/` = `Formalism/SharpRestriction/LevelLetterCocycles/`.

## Overview

**Target 1.** `TwistingCharacterExistence` is an Iwasawa-style argument over an auxiliary-twist group ring
O[(ℤ/ℓ^M)^{2R}], not a mod-ℓ non-vanishing theorem in families. (1) Chebotarev auxiliary primes in two families are
chosen. The "inl" primes have Frobenius conjugate to a tame-inertia element z that acts as a non-±1 scalar, and the
twisting characters ramify there. The "inr" primes have prescribed Frobenius φ_a, chosen to kill dual Selmer classes
(Ramakrishna/Taylor–Wiles style). (2) The Selmer group of the universal twist is presented as the kernel of a matrix Φ, and
for each specialisation ψ the twisted Selmer length equals the valuation of det Φ evaluated at (u_q − 1). (3) A
residual first-order (dual-number) computation shows that det Φ has a unit coefficient of bounded degree when ν = 0, or a
coefficient of valuation ≤ v(ℓ^ν) when ν > 0 ("μ ≤ ν"). (4) The twisted theta elements are class-group sums of Hecke
L-values. They satisfy an Euler-system norm relation (`adm10`). The Euler factors at the chosen primes are ℓ-adic units, so
the theta polynomial's constant term has the untwisted valuation c0, where c0 is the valuation of a Hecke L-value at an
integer s ≥ 1, nonzero by the classical nonvanishing on Re s ≥ 1. (5) A single lemma then evaluates all these
polynomials at ζ^{ℓ^{e_q}} − 1 for one root of unity ζ of large ℓ-power order. This is a Washington-type "valuation at
high-order roots of unity tends to μ" argument, and it gives every bound with error ε at once. The rank bound r ≥ 100
appears to be used only as r ≥ 2 in the places read.

**Major caveat.** By the archive's static name-level reachability (an over-approximation), **none of the modules that
prove this chain is reachable from `Main.lean`**. The unreachable modules include `admAB…` (only 4 of 31 declarations
reachable), `galois_export…`, `residual_bound_of_parts`, `resBound`, `thmC_of_parts`, `chooseH`, `spanOdd`, the
`KillAt` producer `twist_kills_selmer`, `exists_setup_large(_alt)`, `LinkNFam`, and also the "Ribet-step" modules
`CutCoreUnit.main` and `CutDetOrd.main` read in frontier-e. Undetermined: how the main path obtains `LinkN`.

**Target 2.** The normalised Gram matrix is K(u,u′) = (c0(u)c0(u′))^{−1/2} P_u^* P_{u′}, with c0 = volN·volH/dimPi
(volume × volume / formal degree). Its geometric expansion over "terms" has an **identity cell that equals id exactly on
the diagonal and 0 off it** (`IdCellDiagC_holds`, `IdCellOffC_holds`, proved by Schur orthogonality and matching
fundamental-domain volumes). The rest of the expansion is bounded by Poincaré-series and orbit-counting estimates, and
these bounds carry the conjecture-shaped content. The diagonal "lower bound" is therefore a normalisation plus the
identity orbit; it is not an L-value or Rallis inner product. `BesselId`'s nonzero scalar comes from an unfolding of the
period pairing against a Poincaré series (`kerJoinS_of_parts`), with the scalar supplied by an unread hypothesis
`KerSide`. This side **is** statically reachable.

---

## Target 1: existence of a good auxiliary twist

### 1.1 The statement

`Formalism.MainNotions.IntegralHeckeForms.TwistingCharacterExistence` (`LLC/IntegralHeckeForms.lean:166`, file 335 lines) [S]:

```lean
def TwistingCharacterExistence (N0 : X.Tw → ℕ) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → SetHyp bkP i → ∀ eps' > 0, ∀ F : RFam Y i, (∀ j ∈ Icc 1 m, ∀ b, ABHyp Y i F j b) →
  ∀ A0, ∃ Q k' (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A0 Q k' ψ' ∧ partAT bkP i Q k' ψ' eps' ∧ partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps' ∧ partAB Y i F Q k' ψ' eps'
```

The parts are in `LLC/BlochKatoPhases.lean:180–345` [S]:
- **PsiOk**: Q is a set of split, degree-1, unramified primes avoiding S0 ∪ A. The character ψ′ is anticyclotomic
  (`AntiHom X.cc`), has open kernel, takes values in ⟨ζ_{ℓ^{k′}}⟩, is ramified exactly at Q, and is trivial on
  decomposition groups above ℓ.
- **partAT**: for every "good" signature s, sLen(ψ′-twist) ≤ ν + ε_s with Σ ε_s ≤ ε′. Here sLen is the length, in units
  of v(ℓ), of the Bloch–Kato Selmer group `selT` of Tgl ⊗ ψ (ρ_s ⊗ χ_s^{−1} ⊗ ψ, with K/O coefficients, local conditions
  `bk` above ℓ and relaxed at `Spl i ∪ Q`). ν = `nuOf ℓ cyc (t·r)` = v_ℓ(w_{tr}(E)), the H⁰(E, ℚ_ℓ/ℤ_ℓ(tr)) size.
- **partC** ("theta elements keep their valuation"): for each λ, thEval(λ, ψ′^{±}) = Σ_δ θ_Q(λ, δ)·ψ′(δ) is ≠ 0, with
  −N0 ≤ v(thEval) ≤ c0(λ) + ε′, where c0(λ) = v(Σ_δ θ_∅(λ, δ)) is the valuation of the **untwisted** theta element.
- **partD**: t·Σ_{P∈Q} tameVal(ψ′, P) ≤ ε′. tameVal is the normalised valuation of ψ′(σ) − 1 on inertia, so the tame
  values ζ − 1 are tiny because ψ′ has huge ℓ-power order.
- **partAB** (in IntegralHeckeForms): the lattice index of twisted theta vectors in each lift space (j, b) is at most the
  untwisted index plus ε. This is the automorphic counterpart of partC.
- **SetHyp** (hypothesis): `True ∧ SelfDual ∧ NoJump ∧ (∀λ, Σ_δ θ_∅(λ, δ) ≠ 0) ∧ (∀λ, ∃ s, SOk) ∧ 100 ≤ r ∧ ∀k, 2r ≤ g_k`.
  The nonvanishing of the untwisted theta element is therefore an *input*, discharged separately (§1.6).

### 1.2 The top proof: `admAB_of_toric_parts`

`GlobalTheory.TwistChoice.admAB_of_toric_parts` (`IE/IsAuxiliaryPlaceFamilyAtLevelMono.lean:355`, file 471 lines) [P-skel, ~115 lines]:
inputs `DelUTie`, `PropABCD`, `GaloisSideTwistedSelmerAuxiliaryPrimes`, `AdmACD = adm1 ∧ adm2 ∧ adm3 ∧ ArchSig ∧ adm9 ∧ adm10`.

The skeleton:
1. Take a tame-inertia element z (`exists_tameInertiaElementAtAuxiliaryPrime`).
2. From `GaloisSideTwistedSelmerAuxiliaryPrimes`, get R, Dd, M₀. For every M ≥ M₀ there are auxiliary primes
   P : Fin R ⊕ Fin R → places and, for each good s, a polynomial F_s ∈ O0[X_q] whose evaluation computes the twisted Selmer
   length (`SelPoly`). F_s has a coefficient of degree ≤ Dd with valuation ≤ v(ℓ^ν).
3. From `propE_of_admissible` (`PropE`), get for each λ a polynomial f_λ with `OrdHyp … nmax=2 (c0+N0)` and
   f_λ(u − 1) = ℓ^{N0}·thEval(λ, ψ).
4. From `PropABCD`, get the analogous polynomials for the lattice indices (partAB).
5. **`exists_level`** (`:321`, wrapping `T.exists_level_order_exponents_small_valuation_determinants`, [S]; proof
   unread). For finitely many such polynomials there are M, k ≤ M and exponents e_q with ℓ^{e_q}/φ(ℓ^k) ≤ ε such that for
   *every* primitive ℓ^k-th root ζ each polynomial evaluated at (ζ^{ℓ^{e_q}} − 1)_q is nonzero with normalised valuation
   ≤ μ/v(ℓ) + ε. This is the Washington/Sinnott mechanism: a power series with small μ and bounded λ, evaluated at ζ − 1 for
   ζ of order ℓ^k, has valuation μ + O(λ/φ(ℓ^k)).
6. Define ψ′ from χ(x) = ∏_q (ζ^{±ℓ^{e_q}})^{x_q} (`exists_factor`). Then `psiOk_partD` gives PsiOk and partD
   (|Q| ≤ 4R, and each tame value ≤ ε). partAT, partC and partAB follow from step 5.

**Simultaneity** comes from step 5: one root of unity ζ and one exponent vector serve every signature s, every λ and
every (j, b) at once. All the polynomials live in the same auxiliary group ring, and the lemma takes finite families
I, J. No averaging over a family of characters and no gcd over Hecke characters occurs on these lines. "Division" in the
announcement's sense is not visible here either.

### 1.3 The Selmer side: `GaloisSideTwistedSelmerAuxiliaryPrimes`

The definitions are in `NGD/GaloisSideTwistedSelmerAuxiliaryPrimes.lean` (145 lines) and
`NGD/IsTameInertiaElementAtTwistPrime.lean` (124 lines) [S, all read].
- `AdmFam`, `GoodChar`: a character d_P : G_E → ℤ/ℓ^M per split place, anticyclotomic, trivial above ℓ, unramified
  outside P and P̄, and surjective on inertia at P.
- `SlopeTestRemainingChoices`: the primes are split, degree 1, outside S0 ∪ A, with N v ≡ 1 mod 2ℓ^M.
  `Steps`: Frob_{P(inl a)} is conjugate to z modulo H, and d_{P(inl b)}(Frob_{P(inr a)}) = δ_ab (a dual-basis condition).
- `Computes Φ`: ker(Φ acting on B^a) ≅ selOn(Tgl, universal twist delInv, B) naturally in every ℓ-torsion
  O[Δ]-module B. `SelPoly`: sLen(ψ) = v(F(u − 1)) whenever ψ = ∏ u_q^{d_q}.
- `ThmS`: such a presentation exists with Φ having no unit entries. `SelmerLengthsByDeterminant`: det Φ computes sLen.
  `ResidualBoundOddPrimes` (ν = 0) and `ThmC` (ν > 0) are each `OrdBound` with μ = v(ℓ^ν). `GalHyp` =
  `IsotypicValuationAtRing ∧ ValuationStabilityAtRing ∧ SelfDual ∧ NoJump ∧ True ∧ adm3 ∧ 100 ≤ r`.

`galois_export_of_matrix_det_bounds` (`NGD/GaloisExportOfMatrixDetBounds.lean:98`, 21 lines) [P]: pure assembly. It
splits on ν = 0 or ν > 0, takes Φ from ThmS and F with toLam F = det Φ (surjectivity of toLam, proved there), and applies
SelmerLengthsByDeterminant.

### 1.4 The ν = 0 case: `residual_bound_of_parts`

`GlobalTheory.ResSel.residual_bound_of_parts` (`IE/ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21`, 33 lines) [P]. It
takes Cheb, Poitou–Tate, cd 2, TameLocal, local finiteness, local Tate duality, local and global Euler characteristic,
global finiteness, UnramifiedOrthogonality and ArchimedeanSignatureMatching, and **discards GreenbergWiles (`_`)**. It
calls `T.residual_selmer_finrank_eq_dual` (dim Sel(ρ̄) = dim Sel(ρ̄^*), "EqDim"), `exists_auxiliary_primes_prescribed_frobenius`
(StepAB), `exists_elements_selmerForms_small_corank` (ChooseH), `firstHalfLocalCohomologyVanishing…` (FirstHalf),
`reciprocity_auxiliaryPlaces_secondHalf` (Recip) and `residual_selmer_determinant_order_bound` (ResBound). It passes all of
these to `OddBound.residual_bound_of_parts` (`IE/ResidualBoundOfComponents.lean:28`, [P]). That proof picks the
subgroup L, picks h_a from ChooseH and the primes P from StepAB, notes Frob_{P(inr a)} ∈ L, builds `Position`, and reads
off a unit coefficient of degree ≤ 4rR from ResBound.

The decisive definitions are in `NGD/IsDualDualRep.lean` [S]:
- `FirstHalf`: at the inl primes (Frobenius ~ z, and z acts by a scalar d with d ≠ 1, d² ≠ 1) the local H⁰, H¹ and H² of
  ρ ⊗ κ and of its dual vanish for every coefficient module. The inl primes are "Taylor–Wiles-neutral" for the residual
  Selmer group; they only carry the twist ramification.
- `Recip`: global reciprocity (the sum of local invariants) gives Σ_a c_a·⟨x(γ_a), y(φ_a)⟩ = 0 for a Selmer class x of
  ρ (relaxed at Q) and a dual Selmer class y, where γ_a is a tame generator at P(inr a).
- `Corank e`: after imposing vanishing of the pairings at the chosen Frobenii φ_b, at most e Selmer classes stay
  independent. `ChooseH`: R and elements h_a ∈ L exist so that any φ conjugate to h_a mod U gives Corank 0 if ν = 0 and
  Corank 1 if ν > 0.
- `ResBound`: if 4rR + 2 < ℓ^M, then Corank 0 implies det Φ has a **unit** coefficient of degree ≤ 4rR, and Corank 1
  implies some adjugate entry does.

**`T.residual_selmer_determinant_order_bound`** (statement file 10 lines; proof `GlobalTheory.ResOrder.resBound`,
`IE/ResidualSelmerDeterminantOrderBound.lean:324`, file 352 lines) [P-skel of `core` (`:118`, ~200 lines) and `resBound`]:
1. Restrict Φ to a line u_q − 1 = b_q·X over the residue field k, giving Ψ ∈ M_a(K[X]).
2. Read ker Ψ(0) as residual Selmer classes, by `matrixComputesTwistedSelmer_residual_transfer` with the augmentation.
3. Over the dual numbers K[ε]/ε², a first-order deformation x0 + εx1 of a kernel vector is a cocycle for the twist by
   1 + ε·lam. Here lam(φ_a) = −1 and lam(γ_a) = −β_a, from the `Steps` dual-basis condition. Its values at γ_a are forced
   to be sl_a·x0(φ_a).
4. `Recip` and `Corank` then show that at most e such x0 stay independent (`hdeg`). Also dim ker Ψ(0) ≤ 2rR + e
   (`finrank_ker_map_le_of_first_order_kernel_ext`).
5. `laurent_degeneration_first_order_kernel`, `not_X_pow_succ_dvd_det_of_first_order_kernel` and
   `exists_unit_coeff_of_not_X_pow_dvd_line` give X^{4rR+1} ∤ det Ψ, hence a unit coefficient of degree ≤ 4rR. The
   ν > 0 case uses the adjugate.

This is a genuine argument, the classical "first-order kernel bounds the order of vanishing of the characteristic
ideal along a line" (as in Mazur–Rubin / Greenberg-style μ = 0 arguments in auxiliary directions). The Galois inputs
are standard. The three helper lemmas of step 5 are unread.

**`ChooseH`** ⇐ `GlobalTheory.ChooseForms.chooseH` (`IE/ExistsElementsSelmerFormsSmallCorank.lean:557`, file 581 lines)
[P-skel of `single_field`, `single`, `chooseH`]:
- If ρ̄ is **not** residually isomorphic to its conjugate dual twist (¬ResIso), then `abs_odd` with `SpanOdd` gives
  Corank 0.
- If it is (ResIso), a symmetric pairing remains and `abs_two` with `SpanTwo` gives only Corank 1. ResIso forces ν > 0
  (`nu_pos_of_resIso`: comparing determinants gives ε^{tr} ≡ 1 mod 𝔪).

So **"ν > 0" is exactly the obstruction from a self-dual residual pairing**, and ThmC handles it.
`SpanOdd` ⇐ `ResSel.SpanOddPf.spanOdd` (`IE/CocycleFormsSpanOddResidueChar.lean:231`, 365 lines) [P-skel first 60 lines]:
the cocycle pairings are linearly independent as functions on L. This uses (a) the image of ρ̄ spanning M_r(k), i.e.
absolute irreducibility via Burnside (`ValuationStabilityAtRing.1`), and (b) the tame-inertia element z acting by a
scalar d with d ≠ 1 and d² ≠ 1. That is a "big image" substitute supplied by auxiliary ramification at `pD` primes, not by
a large-image theorem.

### 1.5 The ν > 0 case: `thmC_of_parts`

`GlobalTheory.StepTwo.TwoBound.thmC_of_parts` (`IE/AddValLeOfNotMem.lean:87`, about 60 lines; file 146) [P-skel]:
- It takes ChooseH with Corank 1 for R₀ primes, plus t extra "Grow" slots, one per signature.
- Starting from `Start` (`start_of_resBound`: NFit, an adjugate entry with a unit coefficient of degree ≤ 4rR₀),
  `induct` applies `Step` (add a new prime pair, giving NF: a det coefficient outside idl = ℓ^ν·𝔪) and `Grow`
  (degree + 2r per added prime).
- The result is a det coefficient of degree < bound(4rR₀, e, r, t) not in ℓ^ν𝔪, i.e. valuation ≤ v(ℓ^ν)
  (`addVal_le_of_notMem`).

The definitions are in `NGD/Small2.lean` [S]. The provider is `StepTwo.Dyadic.bound_mod_two_of_hypothesis`
(`IE/BoundModTwoUniformizerAtTwoOfChebotarev.lean:25`) [P]: Start ⇐ `resBound`; Grow ⇐ `Growth.grow`
(`IE/ChebotarevInductionGrowBoundOfPresentation.lean:462`, 504 lines, unread); Step ⇐ `NewPrime.step` (`IE/AntiOfKer.lean:153`,
unread). The standard Galois-cohomology inputs are the same as in §1.4.

### 1.6 The theta side: `PropE` and why "theta elements keep their valuation"

`PropE` (`NGD/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:31`) [S]: for each λ with Σ_δ θ_∅(λ, δ) ≠ 0 there are an open
normal H and v with v/v(ℓ) = c0(λ) + N0 such that, for any admissible auxiliary primes, there is f with
`OrdHyp … nmax=2 v f` and f(u − 1) = ℓ^{N0}·thEval(λ, ψ). `OrdHyp` is a Weierstrass-preparation shape: f ≡ Dd·g mod
(X_inr, (1 + X_inl)^{ℓ^M} − 1), with v(g(0)) ≤ v and Dd ≡ unit × ∏ X_inl^{n_i}, n_i ≤ 2, mod p.

`T.propE_of_admissible : adm9 X N0 → adm10 X → PropE X N0` ⇐ `ToricFactor.propE` (`IE/PropEOfAdmissible.lean:420`,
file 565 lines) [P-skel]:
- **`adm9`** (`BlochKatoPhases.lean`) [S]: ℓ^{N0}·θ_Q(λ, δ) is integral.
- **`adm10`** [S]: an Euler-system **norm relation**. Restricting the theta element of level Q to characters trivial at
  a conjugate pair {P, P̄} gives eq′(X_v(λ, P)·ψ(Frob_P), N P^{−s}) × (theta element of level Q∖{P, P̄}), where
  eq′(Y, q) = (1 − Yq)(1 − Y^{−1}q) + (N P − 1)q². This is the classical distribution relation of Stickelberger /
  Mazur–Tate / Bertolini–Darmon theta elements.
- The proof iterates `thEval_remove` (adm10) over all auxiliary primes. At the trivial character the theta polynomial's
  constant term is ∏_a eR(λ(Frob_{P(inl a)}))·Σ_δ y_δ. The Euler factors at the inl primes are **units**, because
  Frob_{P(inl a)} ~ z and `resChar_ne_one` (λ(z) ≢ 1 mod 𝔪, proved from the tame scalar δ(z)² ≢ 1). This gives
  v(constant term) = c0 + N0. At the inr primes N P ≡ 1 mod ℓ, the Euler factor reduces to (1 − Y)(1 − Y^{−1}) with Y
  a unit, and that gives n ≤ 2.

So partC is **not** a deep non-vanishing modulo ℓ in families. It follows from (i) the untwisted value c0, (ii) the
norm relations and integrality adm9/adm10, (iii) choosing the auxiliary primes so that their Euler factors are units,
and (iv) the Washington-type evaluation lemma of §1.2. The deep inputs are pushed into adm10 and into the untwisted
nonvanishing.

**Untwisted nonvanishing.** `LamTie.sum_th_empty_ne_zero` (`IE/SumThEmptyNeZero.lean:10`, 25 lines) [P]. The untwisted theta
element equals u·ι(T), where T is a toric sum (`IsLamTie0`, `NGD/IsAuxiliaryHeckeCharacter.lean`). The theta elements are
class-group sums over Pic(cond) of `IsClassTerm` values for a unitary Hecke character χ = μ0·del·χ_a^{−1} of
prescribed infinity type κ = ⌊eExp⌋ + c − s. `T.exists_heckeL_eq_toricSum_ne_zero` ⇐ `ToricValue.exists_heckeL_toricSum`
(`IE/ExistsHeckeLEqToricSumNeZero.lean:11`, 18 lines) [P]: T = Λ(s) for the completed Hecke L-function Λ of χ
(entire, since χ is not a norm power), and **Λ(s) ≠ 0 because s ≥ 1** (`IsHeckeL.ne_zero_of_one_le`). This is the
classical nonvanishing on Re s ≥ 1. The callee `toricSumFormula` (the identification of the toric sum with Λ(s)) is
unread. So partC is about twisted Hecke L-values L(λψ′, s) at an integer s ≥ 1, and "keeping valuation" means
v(L(λψ′, s)) ≤ v(L(λ, s)) + ε.

### 1.7 Why rank ≥ 100

`100 ≤ D.R.r` sits in `SetHyp` and `GalHyp`. In the uses read, `SelObstruction.selObs`
(`IE/SelmerObstructionLeResidualSelmerSimpleExtension.lean:539`) and `NoGlobalInv.noInv`
(`IE/NoGaloisInvariantsTorsionCoeffOfSelmerSetup.lean:123`), it enters through `by omega` into
`ResComm.eq_zero_of_comm` and `invariants_eq_bot`, whose hypothesis is **2 ≤ r**. Other uses
(`SelmerIffSelmerMatrixAtPrimes`, `NGD/UnivChar`, `OfFirstStepLoc`, `LLC/StmtLocFOfCountsAll`, `LocalShareBounds`) were
not read. Whether any argument needs more than r ≥ 2 (for example a count with 2r ≤ g_k) is **undetermined**. On the
lines read, 100 looks like a generous constant.

### 1.8 Is any of this on the path to `Main`? (static reachability)

`/bulk/shared/rieman/analysis/reach/reachable-modules.txt` (rule A/B name-level over-approximation; see
static-reachability.md) lists **none** of the following modules (0 reachable declarations):
- the twist chain: `ResidualSelmerBoundOfAuxiliaryPrimesOdd`, `ResidualBoundOfComponents`, `ResidualSelmerDeterminantOrderBound`,
  `AddValLeOfNotMem`, `BoundModTwoUniformizerAtTwoOfChebotarev`, `GaloisExportOfMatrixDetBounds`,
  `ExistsElementsSelmerFormsSmallCorank`, `CocycleFormsSpanOddResidueChar`, `ExistsAuxiliaryPrimesPrescribedFrobenius`,
  `IsTameInertiaElementAtTwistPrime`, `Small2`, `IsDualDualRep`, `SetHypOfIsTripleOfGalHodge`, `SumThEmptyNeZero`,
  `ExistsHeckeLEqToricSumNeZero`, `ExistsLevelOrderExponents…`, `IsLatInOfIndexLe` (`export_at_setting`);
- the `KillAt` producers: `ChosenTwistAnnihilatesSelmerGroups(Statement)` (`twist_kills_selmer`),
  `ThirdPlaceSeries/ExistsSetupLarge(Statement)`, `IE/ExistsHubDataFamily(Statement)`, `ThirdPlaceSeries/ImportsFurtherTail`,
  `MainOfAltAlt`, `RowAtOfSetup`, `ThirdPlaceSeries/LinkNFam` (`linkN_of_boundAtTwoThree_slot`);
- frontier-e's core Ribet-step modules: `GlobalCongruenceCountOfRootDifferenceUnit` (`CutCoreUnit.main`),
  `LengthHeckeValueIdealLeDeterminantBound` (`CutDetOrd.main`), `RowsADInSetting`, `StarInequalityRowsADOfGlobalTheorems`,
  `JumpBoundFamilyLargeStatement`, `ExistsGlobalStepObjectsOfCyclotomicGeneratorIner`.

The following are reachable: `IsAuxiliaryPlaceFamilyAtLevelMono` (4 of 31 declarations), `PropEOfAdmissible` (5 of 29),
`IntegralHeckeForms` (26 of 59), `BlochKatoPhases` (55 of 104), `CommutingEndomorphismCondition` (12 of 28),
`DivinNOfHypV` (6 of 6), `DesWin`, `TopPlug`, `TopShape`, `MainTyzTer`.

On the main path, `LinkN` is consumed in `TopPlug.lean:13` as `Nonempty (Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) …)`
inside `zero_free_all_of_green_v_win`. The `SetupAlt` structure (which carries `kill : KillAt`) occurs on the path only
as the *antecedent* of `BoundAtTwoThreeFamilyFonAlt`, and its producer is unreachable.

Calibrated reading: static reachability can miss edges (notation, macros, generalized field notation, misparsed headers).
But an over-approximation that finds no reference at all to a whole proof chain is strong evidence that the chain is
not used by `Main`. **Whether `Main` depends on `TwistingCharacterExistence`, `KillAt` or `CutCoreUnit.main`, and if not,
how `Nonempty (HypsAlt … LinkN …)` is inhabited, is undetermined and is now the top question on this strand.** It should
be settled from the compiled environment (a constant-dependency closure of `Main.riemannHypothesis`), not by more
reading.

---

## Target 2: the near-isometric frame (`LinkS`, `BesselId`, the diagonal)

### 2.1 Statements

`Formalism/SharpRestriction/GlobalTheoremInputs.lean` (168 lines) [S]:
- `LinkS_at L C0 Gam η0 η1 e0` is an implication. **If** C0^{−1} ≤ duS(u)·Gam²/D* ≤ C0 for all u, **then** three bounds
  hold:
  - ‖K(u,u′)‖²_HS ≤ (1 + η0)·duS(u)·duS(u′)/D* for u ≠ u′;
  - hsDiagFull(u) = ‖K(u,u) − id‖²_HS ≤ e0·duS(u);
  - Dall ≤ (1 + η1)·D*.

  `LinkS Fm C0` requires η0, η1, √e0 ≤ exp(−x^{ε/8}), with Gam = GamOf L = exp(CGam·m⁵·f·L). Here duS(u) =
  dim_ℂ Mu0(u) (`D7.duS`, `LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:345`).
- `BesselId D := BuRational ∧ ∃ V isometry of EE, ∀ u, ∃ a ≠ 0, ∃ U isometry of Mu u, ∀ φ F, Bu u φ F = a·besS u (Uφ) (VF)`,
  with **besS u φ F = ⟪sEE F, Pu u φ⟫** (`D7.besS`, same file `:353`). B_u is therefore a nonzero multiple of the
  inner product of F (embedded in the automorphic space HH) with P_u φ. `BuRational` says B_u is the complexification of
  the rational pairing Bk u.
- `LinkDIV_at` bundles `OneMapIntoCC ∧ (sFrame + μ_max ≤ x^{CH}·b) ∧ ZeroAbove ∧ BesselId ∧ RRFull ∧ height clause`.

**The Gram matrix** (`Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean:335–378`) [S]:

```lean
def c0 (u) : ℝ := s.volN u * s.volH u / dimPi u          -- dimPi = ∏_τ dim of the K-type (Weyl dimension, dimPiU)
def Kmat (u u') := ((c0 s u * c0 s u') ^ (-(1/2))) • (adjoint (s.Pu u)).comp (s.Pu u')
def KExpansion u u' := HasSum (fun t => s.aTerm u u' t) (Kmat s u u')
def IdCellDiag u := HasSum (fun t : {t // s.isId t} => s.aTerm u u t) id      -- identity cell = id
def IdCellOff u u' := HasSum (fun t : {t // s.isId t} => s.aTerm u u' t) 0
```

So K(u,u′) is P_u^* P_{u′} normalised by volume × volume / formal degree, and it expands over geometric "terms" (orbits).
The terms split into the identity cell, degenerate terms with Gterm = 0 (`Kpp`, `RelevantZeroGramTerms`), non-generic
terms (`famNG`) and generic terms (`famG`). `ThmSOwn.lean:37–49` [S] gives the clause form: `ClKppOff` (Kpp = 0 off the
diagonal), `ClKppDiag` (‖Kpp(u,u)‖² ≤ du·xK), `ClOff` (‖K − Kpp‖² ≤ (1 + η0)du·du′/D*) and
`ClDiag` (‖K(u,u) − Kpp − id‖² ≤ Gam·du²/D*).

### 2.2 Where the diagonal comes from

- **Identity cell = id**: `Formalism.L2.SG.Closed.IdCellDiagC_holds` (`SLT/ClosedVolumeStatements/UnipotentInLevelSubgroup.lean:98`)
  [P] := `idCellDiagC_of_steps3 nLamNinf_holds VolPosC_holds idMeetOneC_holds idMeetPhaseC_holds idMeetVolC_holds NeatC_holds`
  (`SLT/ClosedLocalOrbits/GaugeLatticeShifts/DistinctWordsDistinctParameters.lean:894`, [P]). Its ingredients are:
  - `idDiagBlocks_of` (`…/IdBlocks.lean:762`): **Schur orthogonality** for the irreducible K-type (`PiIrr`), plus
  - `IdMeetVol` (`IdBlocks.lean:757`, [S]): the fundamental domain of each identity term has the same μ_N-volume as
    the reference domain FdN. It is proved by `idMeetVolC_of idMeetKeyC_holds volColC_holds`
    (`IdMeetPf.lean:27`, [P]). `volColC_holds` comes from ten volume and index lemmas
    (`noinfEqC`, `gcCountC`, `fundMeasEqC`, `indexVolC`, `indexTransferC`, …; unread).
  - `IdCellOffC_holds` likewise gives identity terms vanishing for u ≠ u′, under hypotheses `IdOffConjC` and
    `IdOffLiftC`.
- **Non-identity diagonal terms are small**: `RowsOther.DiagRow` (‖K0 − one‖² ≤ Gm·dd, with dd = du·du′/D*) and `KppDiag`
  (‖degenerate part‖² ≤ du·exp(−k·f·log k)), from `RowsConc.DiagC` and `KppDiagC` (`SLT/CokernelGLCounts/RowsConc.lean:73,98`,
  [S]). These feed `hypOwn_diag` and `hypOwn_kppDiag` in ThmSOwn (`:469`, `:526`, unread).
- **Size of e0.** e0·du ≈ Gam·du²/D*, and LinkS_at's antecedent is du·Gam²/D* ≈ 1, so e0 ≈ 1/Gam = exp(−CGam·m⁵fL).
  The diagonal defect is tiny because **Gam is chosen enormous and the normalisation du·Gam²/D* ≈ 1 is assumed** (the
  antecedent; its discharge via `TuSize` / `SizesRowS` is unread).

**So the "lower bound on the dual slope" does not come from an L-value or a Rallis inner product.** P_u^*P_u ≈ c0(u)·id,
where c0 = volN·volH/dim(K-type) is a volume over formal degree: the identity-orbit main term of an unfolded inner product,
as in Petersson/Kuznetsov. Genus-mass volumes (`GenusMassVolumes.VolSigIndep`, `ClassItemsAt`, passed to
`instTie_of_record` in `link_alt_alt_bis`) enter as the normalisations volN and volH and in `IdMeetVol`. They cancel inside
K. The frame-tightness clause Dall ≤ (1 + η1)D* is a dimension count (the total dimension against D*). Its provider
(`CountAllPointsClass`, `TFrame`) is unread, so the role of a Weyl-law count there is [N]. **No Chowla–Selberg input
appears on these lines.** logΩ (frontier-a) remains the only Kronecker-limit-shaped quantity, and it lives in the
divisor inequality, not here.

### 2.3 The off-diagonal bound (`TheoremSSelected`) and its provider

- `TheoremSSelected Fm C0 s` (`SLT/FlagStabilizerTensors/ThmSOwn.lean:669`) [S]: under `AdmissibleBoundsFromSource.hyp`, for
  u ≠ u′, ‖(Y.tO u u′).K0‖² ≤ (1 + b^{−6})·duS(u)·duS(u′)/D*.
- `TheoremSSingle` (`:977`) [S] is the same bound for one datum (`TheoremSAtDataAlt`, `:968`), under the hypotheses
  `PoincareAmplitudeLowerBounds.SizesAt`, `Cnt.Hyp0`, `Cnt.Stand`, `KTwoHypotheses`, `GapHyp`, `LocTied`, `TFrameAt` and
  the two row conditions `RowBig` and `RowNotScalar`. `theoremS_single_of_closed` (`:996`, [P]) projects it from
  `TheoremSClosedHypotheses`.
- `LoopRowS` (`:1015`) [S]: under `Cnt.Hyp`, `ConcTie` and `AbsConv`, each (u, u′) row satisfies `RowBig` and
  `RowNotScalar`. The provider is `T.loopRows_of_large_gap_discreteSeries` (unread; module reachable, 7 of 7).
- `theoremS_selected_of_loops` (`:1026`) feeds `LoopRowS` into `TheoremSSingle` [P-skel per frontier-f].
- The actual proof of the closed form is `PoincareAmplitudeLowerBounds.theoremS_closedP` (`SLT/FlagStabilizerTensors/TheoremSClosedP.lean:256`,
  file 320 lines) [P-skel]. It takes about 20 closed hypotheses: `LocalModelAt`, `DensInputAt`, `RowsInputP`, `RowNGP`,
  `KppOffC`, `CarrierP`, `KernelExponentAgreement`, `FoldOKC`, `OOIntAllC` (orbital integrals), `AbsConvC`, `FinXC`,
  `WuDecayOfGap`, `ChoicesC`, `FormulaC`, `RowsSumC`, `RowFormAllP`, `MassDataHypAll`, `LinkAll`, `SplitAll`. The core is
  `theoremS_rec3P` (unread). The tail kills the degenerate part (`kppOff_of_termZero`) and applies the row bound.
- `link_alt_alt_bis` (`ThirdPlaceSeries/LinkAltAltBis.lean:16`, 50 lines) [P]: it is a direct call to
  `ThmSOwn.theoremS_transport_link_zero` (`SLT/FlagStabilizerTensors/LinkSPos.lean:131`, 163 lines, unread). The genus-mass
  input `hInstR` goes into `instTie_of_record`, and `residEv_closed_free` is used.
- `WuDecayOfGap` (`SLT/FlagStabilizerTensors/RootLatticeThresholds/WuDecayAll.lean:25`) [S]: `GapHyp D → ∀ X, WuDecay X ∧
  Integrable X.ph (muInf)`. This is decay and integrability of the archimedean test function on the Hida setting. Module
  94 of 97 declarations reachable; proof unread.

**Conjecture-shaped (flag).** `TheoremSSelected` says that for distinct words the Hilbert–Schmidt norm of P_u^*P_{u′}
is at most the **random-subspace prediction du·du′/D* times (1 + b^{−6})**, with b = exp(x^ε). This is an
approximate-orthogonality statement with an exponentially small relative error, in a regime where the number of words
and the dimensions are astronomically large. It is equidistribution-shaped: off-diagonal orbital contributions must
cancel down to the random-matrix level, up to a relative error of b^{−6}. Its proof is `theoremS_closedP` → `theoremS_rec3P`
plus the ~20 closed hypotheses (each with its own `*_holds`). None of those bodies was read here. The Poincaré-series
names (`PoincareSeriesHypotheses`, `PuFun`, `PoincareAmplitudeLowerBounds`) and orbit names (`OOIntAll`, `FundExists`)
fit announcement item 16: a relative trace formula reduced by Cauchy–Schwarz to the norm of a projected Poincaré
series [N].

### 2.4 `BesselId`'s nonzero scalar

- `Formalism.L2.SG.KerJoinS.besselId_of_joins` (`SLT/FlagStabilizerTensors/KerJoinS.lean:133`, file 149 lines) [P]: it
  builds `adm13` (= BesselId) from `KerJoinS`, `ColJoinS`, the row identification `hRow` and `BuDefQ`.
- `KerJoinS` (`:70`) [S]: perCol u μ0 φ F = **a·⟪conjHH(j(V(ι F))), PuFun u T⟫** with a ≠ 0. The period column of φ
  against F is a nonzero multiple of the L² inner product of F with the Poincaré-series function PuFun built from the
  column T.
- `kerJoinS_of_parts` (`:78`) [P]: it is `PoincareSeriesHypotheses` plus `BesselUnfold` (the unfolding identity) plus
  **`KerSide X G j Tr hK Fs`, which supplies V, a ≠ 0 and U**. `KerSide`'s definition and provider are unread.

So a ≠ 0 traces to `KerSide`. By its shape it is probably a local or archimedean Bessel-functional constant (local
uniqueness of Bessel models: `CompanionTheory…BesselMapUniqueness` and `LocalBesselUniqueness` modules exist, [N]). No
seesaw identity and no global L-value were seen on this path. Whether `KerSide` hides a seesaw to a character-independent
Bessel period (announcement item 12) is **undetermined**.

### 2.5 `matSF_of` / `Frame_at`

Read in frontier-a (Q4) and not re-read here. `Frame_at` turns the near-isometric frame into the slope bound
sFrame − log|W| − (1 − δ)^{−1}(4uF·log(1 + HH/uF) + (η + 4√e)HH) ≤ μ_dual. Combined with §2.2, the slope lower bound
needs (i) the identity-cell normalisation, (ii) tiny off-diagonal and diagonal defects, and (iii) the tightness
Dall ≈ D*.

---

## What to read next (priority order)

1. **Settle reachability of the Ribet/twist strand by machine.** Compute the constant-dependency closure of
   `Main.riemannHypothesis` in the compiled environment and test for `TwistingCharacterExistence`,
   `KillingConditions.KillAt`, `CutCoreUnit.main`, `NLink.twist_kills_selmer` and `TwSys.Test.galois_export_of_matrix_det_bounds`.
   If they are absent, find how `Nonempty (Fc.HypsAlt (Closed … LinkN) …)` is built for `TopPlug.lean:13`: start from
   `UpperTheory.Lit.every_character_of_theta_integrals_local_matching`
   (called at `ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810`) and `ThirdPlaceSeries/TopShape.lean:33`.
2. `PoincareAmplitudeLowerBounds.theoremS_rec3P` and the `*_holds` behind `theoremS_closedP`
   (`SLT/FlagStabilizerTensors/TheoremSClosedP.lean`), especially `MassDataHypAll`, `LinkAll`, `RowFormAllP` and `RowsSumC`.
   This is the conjecture-shaped off-diagonal bound.
3. `ThmSOwn.theoremS_transport_link_zero` (`SLT/FlagStabilizerTensors/LinkSPos.lean:131`) and
   `T.loopRows_of_large_gap_discreteSeries` (`Development/AbelianVarietyTheory/Proofs/FlagMeasures/LoopRowsOfLargeGapDiscreteSeries.lean`).
4. `KerSide` and its provider (the origin of BesselId's a ≠ 0), and the discharge of the `LinkS_at` antecedent
   du·Gam²/D* ≈ 1 (`TuSize`, `SizesRowS`) and of Dall ≤ (1 + η1)D* (`CountAllPointsClass`, `TFrame`).
5. If item 1 shows the twist chain is used: `T.exists_level_order_exponents_small_valuation_determinants` (the
   simultaneous Washington-type lemma); `Growth.grow` (`IE/ChebotarevInductionGrowBoundOfPresentation.lean:462`) and
   `NewPrime.step` (`IE/AntiOfKer.lean:153`); the three first-order-kernel lemmas used by `resBound`; where `adm10` (the
   theta norm relation) and `adm9` are discharged; and `ToricAssembly.toricSumFormula`.
6. The other uses of `100 ≤ r` (`SelmerIffSelmerMatrixAtPrimes`, `NGD/UnivChar`, `OfFirstStepLoc`, `LLC/StmtLocFOfCountsAll`,
   `LLC/LocalShareBounds`), to see whether anything needs more than r ≥ 2.
