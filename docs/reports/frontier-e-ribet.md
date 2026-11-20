# Frontier E: the Ribet-type congruence inequality and its inputs

Date: 2026-11-20. This is a read-only source study of `/bulk/shared/rieman/lean/src` on chili. I used only cat, sed and
grep over ssh, plus `/bulk/shared/rieman/analysis/reach/decl-index.tsv`. Nothing was compiled or run. Paths are relative
to `src/`, and `IE/` abbreviates `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`. The report follows
`frontier-b-links.md`, `core-gm.md` and `theta-chain.md`. About 70 tool calls.

Tags:
- **[S]** means read in the statement or definition.
- **[P]** means read in the proof (in full, or the skeleton as noted).
- **[N]** means inferred from names or from the shape of a statement.

No `sorry` or `axiom` occurs in the five core files I grepped.

## Overview (for a number theorist)

`GlobalTheory.CutCoreUnit.main` bounds the congruence number of an "Eisenstein-type" eigensystem π. Here r_π = ρ ⊕ χ ⊕
χε^{-1} ⊕ … ⊕ χε^{-(t-1)}, and the bound is a sum of lengths of extension-class modules. The direction is the classical
one: a congruence produces extensions, so **congruence ideal ≤ Selmer/Ш**. The core inequality
(`length_heckeValueIdeal_le_determinant_bound`) is not Ribet's lattice construction inside an irreducible
representation. It is a **determinant / Fitting-ideal argument on a generalized-matrix-algebra presentation**, in the
spirit of Mazur–Wiles, Urban and Bellaïche–Chenevier:
- Take A, the O-algebra spanned by the Galois images, made block-diagonal at π.
- Take the A-module Y spanned by the "column" cocycles yg(γ) = (χ₁^{-1}r(γ) − 1)·E, where E is a Lagrange-type
  projector onto the χ₁-line.
- A general DVR lemma then gives len(O/I) ≤ Σ_blocks len(solutions of the block relations), for any ideal I that
  contains all coefficients of the products of the generic block determinants of relations.

Four non-degeneracy inputs are needed:
- (a) For non-Z eigensystems, χ₁ is not a Galois-stable line (characteristic 0).
- (b) ρ̄ is absolutely irreducible (residual span = all matrices).
- (c) A Galois-closure/splitting algebra of the t character values.
- (d) For the "Unit" version used at large ℓ, the root differences χ₁(g₀) − χ_c(g₀) are **units**.

Input (d) forces ℓ > t+1. It is discharged only for ℓ > lStar ≈ m·b/poly(n, t, k, L), with b = e^{x^ε}, so lStar ≫ t.
For ℓ ≤ lStar ("rows A–D") the archive uses a non-unit variant: the root-difference valuation
vdel = Σ_{0<k<t}(s₀ + v_ℓ(k)) is booked as an error term.

The Ш block bound `Cut.ShaBound.main` is formal. Classes that are unramified outside ℓ and coboundaries at ℓ lie in
Ш¹(G_{E,{v|ℓ}}, ℚ_ℓ/ℤ_ℓ(−e)). The local fact that cut cocycles are coboundaries at ℓ comes from an integral
Wach/Herr-complex local theorem (`TopCore`). The proof of that theorem discards the `BlochKatoLocal` input it is given.

The ρ-block Selmer length `sPi` is not bounded by an L-value. It is bounded by **choosing the lifts as twists by an
auxiliary character for which the twisted Bloch–Kato Selmer group is almost trivial** (`KillAt`: sPi ≤ v_ℓ(w_{tr}(E)) +
ε_ℓ). The existence of such twists (`TwistingCharacterExistence`) is the most conjecture-shaped statement on this strand.
It is proved by an auxiliary-prime (Ramakrishna/Kolyvagin-style) determinant argument from standard Galois-cohomology
hypotheses. I read its skeleton but not its decisive sub-lemmas.

---

## 1. `GlobalTheory.T.length_heckeValueIdeal_le_determinant_bound`

**Location.** `IE/LengthHeckeValueIdealLeDeterminantBoundStatement.lean:8`. It forwards to `GlobalTheory.CutDetOrd.main`
(`IE/LengthHeckeValueIdealLeDeterminantBound.lean`, 144 lines). A twin, `GlobalTheory.CutDet.main`
(`IE/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:376`), takes `GoodCongruenceObjects` instead. [P, read in full]

**Statement** (trimmed) [S]:
```lean
∀ D i r ρ π Xs (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IsOrthogonalIdempotentDecomposition D.nd r ρ π S →
  π ∈ Xs → π ∈ D.nd.Z i → NoChiOff i r Xs →
  length_O (O ⧸ ccOff i Xs π) ≤ length_O (cocRho i r S Xs) + ∑ c : Fin t, length_O (cocChi i r S Xs c)
```

**Notions, unpacked one level** [S]:
- **X i** is the finite set of Hecke eigensystems. **T i** ⊆ (X i → O) is the Hecke algebra.
- **Z i** is the distinguished (reducible, "Eisenstein") eigensystems. `D.Z_tie` together with `galois_condition_six_of`
  give: x ∉ Z ⇒ χ₁ ⊄ r_x.
- **GoodR**: every x has a continuous r_x : G_E → GL_{nV}(O), semisimple over K, with Frobenius charpoly equal to the
  Hecke polynomial at split places (`DataN.lean:1232`).
- **Hecke value ideal** `ccOff i Xs π` = (f(π) : f ∈ T, f = 0 on Xs∖Z) (`NonGaloisDescent/GlobalCore.lean:21`). With
  Xs = univ it equals `ccAt (T, Z, π)`, the image at π of ker(T → ∏_{x∉Z} O) (`CutCoreUnit.ccOff_univ`, [P]). This is the
  classical congruence ideal.
- **vcc i π** = lenUnit(O/ccAt). That is the length normalised by len(O/ℓ), i.e. the ℓ-adic valuation of the congruence
  number.
- **IdempotentChoiceData** (`QuotientHomNonvanishingBound.lean:444`) has the following fields:
  - idempotents eB (rank t, the χ-block) and e1 (rank 1) in O[r(G)]⊗T;
  - an element g₀ ∈ inertia at some w | ℓ;
  - X₀ = eB·r(g₀)·eB;
  - a cover p : X' → X with T' ⊇ T, adjoining roots rr₁, …, rr_t of the charpoly of X₀ on the eB-block (a splitting
    algebra of rank t!);
  - a K-isomorphism e : K^{nV} ≅ K^r × K^t;
  - block maps ψρ : A → M_r(O) and ψχ_c : A → O at the base point π'.
- **Eel** = ∏_{c=2..t}(X₀ − rr_c·eB). This is a Lagrange projector onto the χ₁-line, with Eel² = del51·Eel and
  del51 = ∏_{c=2..t}(rr₁ − rr_c). At π', rr_c = χ_c(g₀) = χ₁ε^{-(c-1)}(g₀) (`chi_def`, `DataN.lean:126`).
- **yg γ** = χ₁(γ)^{-1}·r(γ)·Eel − Eel. This is the column of the generalized matrix algebra (GMA) that carries
  extensions of the χ₁-line by the other blocks.
- **cocW ψ** (`GlobalCore.lean:31`) is the span of the functions γ ↦ φ(yg γ). Here φ runs over the O-linear maps to
  (K/O)^k that are A-equivariant through ψ and vanish on the Xs-zero part of Y.
  - **cocRho** is cocW ψρ: cocycles with values in ρ ⊗ χ₁^{-1} ⊗ K/O.
  - **cocChi c** is cocW ψχ_c: values in χ_cχ₁^{-1} = ε^{-c}.
- **NoChiOff** (`GlobalCore.lean:68`): for x ∈ Xs∖Z, χ₁^{-1}r_x has no nonzero invariant vector over K.

**Proof skeleton** [P]:
1. `value_mem_ccOff` (= `Cut.value_mem_ccOff`): an element of T' that vanishes on all non-Z points of the cover has its
   value at π' in ccOff. The proof uses a unique T-basis b of T' of size t! (the splitting algebra is free).
2. `exists_ne_zero` (= `Cut.ResidualSelmer.main`, `IE/ResidualSelmer.lean`, 29 lines; the name is misleading): for x'
   over Xs∖Z some η, γ give yg(γ, x')η ≠ 0. The proof combines NoChiOff with rank Eel(x') = 1. This is the characteristic-0
   non-degeneracy.
3. `exists_gens`, `exists_conj`, `exists_homs` (`LengthHeckeQuotientLeCocycleSpanDeterminant.lean`): finitely many
   generators yg(γ_q) of Y, and A acting block-diagonally at π'. The ρ-block ψρ is surjective onto M_r(O) (field
   `hsurj`).
4. `GlobalTheory.BlockDetPoly.main` (`IE/CMemCoeffSub.lean:99`): the coefficients of det(Σ X_k θ_k) lie in T'.
   `det_generic_eq_zero` makes them vanish at non-Z points, because of the kernel vector from step 2. Step 1 then puts
   their values at π' in ccOff. `det_generic_blocks` factors the determinant at π' as ∏_blocks det.
5. `GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound` (= `DetGen.length_quot_le_sum_length`,
   `IE/DeterminantLemmaDiscreteValuationRingQuotientLen.lean:259`, file 273 lines; skeleton plus sub-statements read):
   - Setting: O is a DVR, ψ_j : A ↠ M_{d_j}(O), Rel ⊆ A^g, and I ⊇ all coefficients of ∏_j det(Σ_k X_k ψ_j(θ_k)) for
     θ ∈ Rel.
   - Conclusion: len(O/I) ≤ Σ_j len{w ∈ ((K/O)^{d_j})^g : Σ_q ψ_j(θ_q)w_q = 0 ∀θ ∈ Rel}.
   - `exists_relations` picks relations whose block determinant has valuation ≤ the length of the solution module.
     `addVal_det_le_length` is "valuation of det = length of cokernel". This is the Fitting-ideal identity over a DVR.
6. `length_sol_le` (the same file as step 3, line 77): the solution module injects into the cocycle module cocW. It uses
   that K/O is injective (`baer_KOG`, `exists_ext`).

**Assessment.** This is **congruence ideal ⊆ Fitting ideal of the module of off-diagonal extension data**, in the
Mazur–Wiles/Urban style. It is phrased with a GMA-like algebra and a reducibility-type ideal, as in Bellaïche–Chenevier.
It is not Ribet's lattice-in-an-irreducible-representation construction. [P for the mechanism; the literature match is
mine.] The bound holds over any DVR O and does not need del51 to be a unit: del51 ≠ 0 in O suffices, through the rank-1
condition on Eel.

## 2. `GlobalTheory.UseFive.objects_globalStep_gen` (the "five objects")

**Location.** `IE/ExistsGlobalStepObjectsOfCyclotomicGeneratorIner.lean:138` (185 lines). The wrapper is
`GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia`. [S, P skeleton]

**Statement** [S]:
```lean
GoodR → admG1 (charpoly coeffs ∈ T) → admG3 → FamilyContinuous → admSS → SemisimpleDecomposition i r ρ π →
CyclotomicInertiaImage → ResSpan i ρ π → π ∈ Z → (∀ v | ℓ, e(v/ℓ) = 1) → D.R.t + 1 < ℓ →
∃ S, IsOrthogonalIdempotentDecomposition D.nd r ρ π S
```

**What the "five objects" are.** `IsOrthogonalIdempotentDecomposition` (`Formalism/SharpRestriction/LevelLetterCocycles/
IdempotentChoiceDepthZero.lean:18`, section `Obj51`) [S] packages the following:
1. the orthogonal idempotents eB, e1 in the T-span of r;
2. the decomposition e with r_π ≅ ρ_π ⊕ χ₁ ⊕ … ⊕ χ_t over K;
3. the block maps ψρ (surjective onto M_r(O)) and ψχ_c;
4. g₀ ∈ inertia at w | ℓ with **ord(ε(g₀) mod ℓ) = ℓ − 1**, and X₀ = eB r(g₀) eB;
5. the splitting algebra T' (free of rank t! over T) with ordered roots, the charpoly identity, Eel of rank 1 and
   **IsUnit(del51(π'))**.

The names `Obj51`, `h51`, `h52`, `h54` suggest displays (5.1)–(5.4) of a source text. [N]

**Proof skeleton** [P]:
- `exists_inertia_cyclotomic_generates_units_mod` gives g₀. It needs e(v/ℓ) = 1 and CyclotomicInertiaImage.
- **`isUnit_sub_charValues_of_cyclotomic_generator … ht`** turns t+1 < ℓ into the statement that the χ_c(g₀) are pairwise
  distinct mod λ.
- `span_repMatrix_eq_top_of_residue_span_eq_top` turns ResSpan (ρ̄ spans M_r(k), i.e. Burnside) into the statement that
  the O-span of ρ(G) is M_r(O).
- `exists_injective_roots_of_distinct_units_roots` and `SplittingAlgebra.main` build the splitting algebra.
- `exists_block_action_of_decomposition` gives ψρ and ψχ. `exists_good_gen` assembles S, and del51 is a unit because the
  roots differ by units.

**Assessment.** This is the standard set-up for a reducible GMA: residual absolute irreducibility of the ρ-block, plus
residually distinct characters, made explicit through a generator of inertia acting by a primitive root mod ℓ. [P]

## 3. `GlobalTheory.Cut.ShaBound.main` (= `T.length_cyclotomic_block_cocycles_le_sha`)

**Location.** `IE/LengthCyclotomicBlockCocyclesLeSha.lean:372` (file 421 lines). [S, P read in full]

**Statement** [S]:
```lean
∀ D i c (C ≤ Z¹(K/O(ε^{-(c-1)}))), 2 ≤ c ≤ t → (∀ f ∈ C, ∀ w | ℓ, loc_w f ∈ BD (locLat w)) →
  (∀ v ∤ ℓ, C|_{I_v} = 0) → len C ≤ lenCob C + len(O/ℓ) · shaLen(ℓ, c−1)
```

`BD(lat)` is the set of local cochains of the form g ↦ (M(g) − 1)y mod lattice, with y in the rational space. It is the
local coboundaries in V/T (`cob_of_bridge`). [P]

**Proof** [P]:
- Fix a ℤ_ℓ-basis of O (`exists_coord`). Each coordinate of a class is a 1-cocycle of G_E with values in
  ℚ_ℓ/ℤ_ℓ(−(c−1)) that satisfies `LocTriv`: it is zero on inertia away from ℓ and a coboundary on decomposition groups
  above ℓ.
- `LocTriv.vanish` and `mem_range` show that it factors through G_{E,S}, with S = places over ℓ.
- `mk_mem_Sha` shows that its class lies in `Sha` (locally trivial at every v ∈ S).
- The kernel of the map to Ш^{rank O} is the coboundaries. `length_le` and `length_quot` (len_O(O/ℓ) = rank) finish the
  proof.

**Assessment.** This is the formal identification of {classes unramified outside ℓ, trivial at ℓ} with
Ш¹(G_{E,S}, ℚ_ℓ/ℤ_ℓ(−e)), up to coboundaries. I see nothing deep and no gap here. The content lies in the hypotheses:
(i) the cut cocycles are BD at ℓ (§6), and (ii) Ш is small (VWin's `VVle`). [P]

## 4. `GlobalTheory.T.jump_bound_family_large`

**Location.** `IE/JumpBoundFamilyLargeStatement.lean:19`, which forwards to
`GlobalTheory.LargeJumps.jump_bound_of_facts_large_family` (`IE/JumpBoundFamilyLarge.lean`, 38 lines). [S, P in full]

**Statement** [S]:
```lean
∀ {eps} (Fm : FamP eps), ∃ x0, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x),
  NFacts.Facts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a)
```

The **family** is `FamP eps`: for each window point x and index a it gives data D7 and SizeData₂. **"Large"** means
large scale x ≥ x0.

**JumpConditions** (`Formalism/SharpRestriction/LevelLetterCocycles/AdmissibleParameterJ.lean:173`) [S] is a conjunction
about the Hodge–Tate weight multiset of the j-th lift at each embedding ρ: PPm(j, ρ) = {v_a}_{a<k−1} ∪ {−b_a}_{a<m} ∪
{t consecutive weights shifted by sz(j, ρ) = e_{j−1}}. Its parts:
- `ConclusionJa`: the actual Hodge–Tate jumps of WpO = ρ_π ⊗ χ₁^{-1} and of its dual equal the explicit sets JW.
- Interval bounds:
  - the cloud lies in [sz, sz + Sc];
  - the lows lie in [(t+3)/2, etaSz];
  - every jump satisfies |q| ≤ b + Sc + etaSz + 1 + c₀ ≤ 2b.
- `JumpLowsSignCount`: of the m small jumps of lift j, **exactly j are positive and m − j negative**. This sign pattern
  is what distinguishes lift j.

**Proof** [P]:
- `HTW.admissibleParameters_of_large_scale eps (PK[7])` gives AdmPar for x ≥ x0: etaSz + t + Sc < w''(n),
  3w'' ≤ b and t ≤ etaSz.
- `hF.admJ` (a field of `Facts`) supplies AdmJ: de Rham/crystalline dictionaries plus `AdmDict`/`AdmRead`, the
  automorphic HT weights read through local–global compatibility.
- `JumpStatement.holds_all = JumpSets.stmtJ_holds`
  (`Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/JumpSetDistinctOfRealPlaceFacts.lean:1185`, file
  1198 lines; I read the closing proof and `jFacts_of`) derives `JFacts L j ρ` for every 1 ≤ j ≤ m from:
  - the family's Hodge-cocharacter record `D.hc ρ` (monotone b, antitone v, interlacing axioms `gap_be` and `gap_eb`);
  - the SizeData₂ fields `cloud_v`, `be_close` and `win_thick`.

  Seven elementary lemmas then give the seven conjuncts.

**Uniformity** [P]:
- In j: every JFacts bound is in terms of b, Sc, etaSz and t only, and `jFacts_of` is proved for arbitrary j ≤ m.
- In ℓ: JumpConditions does not mention ℓ. It is a statement about rational weight sets. The ℓ-dependence sits inside
  `ConclusionJa`, which comes from AdmDict/AdmRead for all ℓ at once.
- x0 depends only on eps and the family constant `PK[7]` (a bound on CLw).

**Assessment.** These are combinatorics of Hodge–Tate weights. It is the bookkeeping that later converts "each lift has
m small jumps" into the per-lift local length ∝ m (frontier-b Q5). It contains no arithmetic estimate. [P]

## 5. `GlobalTheory.NLink.rowsAD_in_setting_alt` (rows A–D)

**Location.** `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RowsADInSetting.lean:15`
(34 lines). [S, P in full]

**Statement** [S]:
```lean
Hypotheses₂ → ∀ D L P nch HW F Cm X C₂, SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ →
  JointParametersHubConditions L HW X (rowC C₂) → StarAD L X ∧ BBLe L X 7200
```

Definitions in `JointConditionsZpowers/CommutingEndomorphismCondition.lean:132-195` [S]:
- **StarAD**: for twisted ℓ in **RangeAD** (not small, not 3, not q or d, and not "ℓ > lStar off the exceptional set"),
  for every π ∈ Zgood:
  vcc ≤ sPi + Σ_{λ|ℓ} len0(λ) + VVr(ℓ) [Ш terms] + vhE(ℓ) + errorBoundHub + epsL(ℓ).
- **BBLe**: errorBoundHub ≤ 7200·f·n·t²·nV·large₂².
- **"Rows"** are the rows of the local-length table in `DataAD`:
  - row A: split ℓ, len0 = lenA = (2·deg·m + 1)·eA, eA ≈ C(1 + 2b/ℓ + log_ℓ b);
  - row B: inert ℓ with ℓ < lA and 4Lw < ord_H(ℓ), len0 = lenRowB;
  - rows C/D: the other inert ℓ, len0 = lenRowCD with a "band".
- The inert error is `localErrorBoundDecomposition` = t·Σ_row(deg+2)cB + **4·nV·(|col|+1)·vdel** + t·|col|·h0.

**Proof** [P, skeleton]: `StepAD` (a09 from `adm_at_inert_of_range`, a78, goodR) →
`starInequality_rowsAD_of_global_theorems` (`IE/StarInequalityRowsADOfGlobalTheorems.lean`, 111 lines; grep-skimmed). In
the split case that proof books, per column u, **deg(u)·m·(eS + vdel) + 2·vdel**. BBLe comes from
`nonPlacePart_localBound_le_middleRange` (constant 60·120 = 7200).

**Assessment.** This is the medium-ℓ version of the same congruence bound. The root differences need not be units here,
and their valuation vdel = Σ_{0<k<t}(s₀ + v_ℓ(k)) (`DataN.lean:232`) enters as an error. [S/P skeleton; I did not read
which core lemma replaces `CutCoreUnit.main` here.]

## 6. `TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt` and `UseLoc.main`

**`blochKatoTop…_alt`** (`IE/BlochKatoTopOfLocalTateDualityEulerChar.lean:25`, 44 lines) [S, P in full]:
- Statement: `BlochKatoLocal → LocalTateDualityK → LocalEulerCharK → ∀ D HW F Cm, tableLineDegreeTwo.aux₃ D HW F`.
- **The first hypothesis is discarded** (`intro _ hdual heul …`).
- The proof collects about 24 Wach-lattice, Herr-complex, Fontaine-decompletion, Sen and crystalline clauses, all proved
  in the archive (`wachLattice_laterClauses_hold`, `herr_part_a_every_record`, `fontaine_and_decompletion`, `stmtSen`,
  `crysLit_all`, …), plus Tate duality and the Euler characteristic.
- It closes with `TopBridge.twistedLatticeCohomology_theoremTOP` (`IE/TwistedLatticeCohomologyTheoremTOP.lean`, 84
  lines, unread).

**`aux₃` = TopTheoremLocal**, i.e. `TopCore` for every Wach lattice (`TableLineDegreeTwo.lean:193`) [S]:
- Setting: p ≥ 5, a crystalline lattice T₀ ⊂ V with χ_c = χ₁ε^{-(c−1)}, and Hodge–Tate positions satisfying
  `PositionHyps`. These include η + 4·sg + 6 < ℓ, so the weights involved are in a Fontaine–Laffaille-type window.
- Conclusion: for every finite X, a cocycle is "admissible" (a condition in terms of jump data and the residual
  polynomial) iff the following holds:
  - ρ-block: it lies in H¹_f (`InHfX`);
  - c ≥ 2 blocks: it is a coboundary;
  - c = 1 block: it is unramified.

**`UseLoc.main`** (`IE/AdmissibleOfLargeResidueChar.lean:24`, 54 lines) [S, P in full]:
- Hypotheses: TopCore, `adm20`, ConclusionJa, GoodR, admG2/3, the decomposition, CyclotomicInertiaImage, ℓ ≥ 5,
  ℓ ∉ small, ℓ ≠ q, d, and the position data.
- Conclusion: for all w | ℓ, LocBound(WpO) with error 0, and cut cocycles in BD for c ∈ [2, t], and in Z¹_ur for c = 1.
  These are exactly the local hypotheses of `CutCoreUnit.main`.
- Proof:
  1. `exists_exactLocalConditionData_at_place` finds a coefficient extension C and a lattice.
  2. `unramifiedEnlargement_cut_cocycles_blochKato` applies TopCore.
  3. Descent lemmas (`mem_finite_part_of_lift`, `coboundary_descent_enlargement_coefficients`,
     `unramifiedCocycle_descent_enlargement`) return to O.

**Assessment.** This is integral p-adic Hodge theory in the style of Fontaine–Laffaille/Wach/Berger: "H¹_f of a lattice,
and H¹_f = 0 integrally for negative twists in the FL range". The "Bloch–Kato" in the name refers to local conditions.
The `BlochKatoLocal` literature hypothesis itself is unused in this closing proof. [P]

## 7. `GlobalTheory.UseLoc.main` in context, and `CutCoreUnit.main` assembly

In `NLinkE.main_alt_alt` (`ThirdPlaceSeries/AdmissibleParameterEventually.lean:30`, read in full), for ℓ > lStar:
- `exists_localPositionData_off_exceptional_primes` (`IE/ExistsLocalSlotDataOffExceptionalPrimesStatement.lean:11`) [S]
  concludes **5 ≤ ℓ, t + 1 < ℓ, ℓ ≠ q, d, ℓ ∉ small**, and the position data.
- admG3 comes from `AdmGThreeRest.main_alt_alt`: from `fa.rhoBar` (residual irreducibility in `NormChoiceFacts`) and
  `litBurnside_host`.
- NoChiOff and UnrOut come from `UnrNoChi.main_alt_alt`, through `galois_condition_six_of` (`ConclusionG6` plus
  `D.Z_tie`).
- These feed `objects_globalStep_gen` → `UseLoc.main` → `CutCoreUnit.main`.

Inside `CutCoreUnit.main` [P]:
- `hd : lenQ(del51) = 0` (the unit root difference) kills the coboundary terms through
  `length_cutCoboundaryModule_le_unitDelta`.
- ρ-block: `length_global_cocycles_le_sum_places_over` + `LocalGlobalSelmer.main` +
  `length_cocycles_le_coboundaries_add_selmer` give len cocRho ≤ s, with sPi = s/L.
- c = 0 block: `Cut.Peel.main` (peels Q) → `CutTrivIne.main` → `UnramHom.length_le_classNumber` (Artin reciprocity)
  give v_ℓ(h_E).
- c ≥ 1 blocks: `ShaBound.main`.
- Q places: `inertiaCocycleBlock_length_le_of_quadraticRelation` gives len(O/(ζ_q − 1)) per block.

---

## Answers

### Q1. Direction, non-degeneracy, and small ℓ

- **Direction** [P]: len(O/ccOff) ≤ len(cocRho) + Σ_c len(cocChi c).
  - The left side is the congruence ideal at π (π ∈ Z, the reducible eigensystems) against the eigensystems outside Z.
  - The right side is the lengths of the modules of extension classes. These are cocycles of χ₁^{-1}ρ, and of ε^{-e}
    for 0 ≤ e < t, with values in K/O, cut out by the GMA idempotents.
  - So the congruence ideal is bounded **above** by Selmer/Ш-type groups: the classical direction.
- **Non-degeneracy actually used.** The first four items are needed for the core inequality; the fifth only for
  `CutCoreUnit`.
  - (i) **NoChiOff (characteristic 0)**: for x ∉ Z, χ₁ is not a Galois-stable line in r_x ⊗ K. It is used to show that
    determinants vanish at non-Z points. It is discharged by `UnrNoChi.main_alt_alt` from `ConclusionG6` and `D.Z_tie`
    (Z is tied to "contains χ₁").
  - (ii) **Rank-1 Lagrange projector Eel**, coming from distinct roots in characteristic 0 (del51 ≠ 0).
  - (iii) **ψρ surjective onto M_r(O)** ⇐ ResSpan (ρ̄ absolutely irreducible), discharged by `admG3`
    (`AdmGThreeRest.main_alt_alt`: `fa.rhoBar` and `litBurnside_host`).
  - (iv) GoodR (semisimplicity and charpoly = Hecke polynomial). admG3 also contains `AbsIrrDistinct` over K: the
    constituents of r_x are absolutely irreducible and pairwise non-isomorphic. That is a characteristic-0
    multiplicity-one statement.
  - (v) For `CutCoreUnit`: **IsUnit(∏_{c≥2}(χ₁(g₀) − χ_c(g₀)))**, i.e. the χε^{-e} are distinct mod λ on a single inertia
    element g₀ with ε(g₀) a primitive root mod ℓ. This is equivalent to ℓ − 1 > t − 1.
  - I saw **no residual multiplicity-one hypothesis** for the whole r̄_x.
- **Small ℓ.**
  - **Excluded on the Unit route:** `objects_globalStep_gen` requires t + 1 < ℓ. That hypothesis is discharged only for
    ℓ > lStar (`exists_localPositionData_off_exceptional_primes`, a proved theorem).
  - Why this is enough: lStar = m·b / (n·t²·(N(m)+t)·L² + k·n²·(Sc + t + L)) (`Formalism/LocalRingCardinality/
    DataParams.lean:38`) with b = e^{x^ε}, so lStar exceeds any polynomial size of t. A t of order x^401 is harmless.
  - For **ℓ ≤ lStar** (RangeAD), the bound is StarAD. There the root differences are nonzero but not units, and
    vdel = Σ_{0<k<t}(s₀ + v_ℓ(k)) ≈ t·s₀ + t/(ℓ−1) is paid as an error. It costs deg·m·vdel per column, or 4nV(|col|+1)·vdel
    when ℓ is inert. BBLe caps the total at 7200·f·n·t²·nV·large₂² per ℓ, and lStar is calibrated so that the log ℓ-weighted
    sum over ℓ ≤ lStar stays O(f·m·b·L²) [P skeleton, S].
  - ℓ = 2, 3, small ℓ, q and d have separate routes (frontier-b).
  - **The t·Σ_Q len(O/(ζ_q − 1)) term is unrelated to small ℓ.** ζ_q = χ₁(γ_q) is the tame value of χ₁ at the auxiliary
    split places Q, where χ₁ ramifies (`chi_ram_Q`). The term comes from peeling the Q-ramified part of each χ-block, and
    `KillAt`/`partD` bound it by epsL(ℓ).

### Q2. `jump_bound_family_large`

See §4.
- **Family:** `FamP eps`, indexed by the window point x and index a.
- **"Large":** x ≥ x0(eps, PK[7]).
- **Conclusion:** the explicit Hodge–Tate jump-set conditions for every lift 1 ≤ j ≤ m.
- **Uniformity:** in j, because `jFacts_of` is proved for arbitrary j ≤ m from family-wide records (`hc ρ` interlacing
  axioms, SizeData₂ bounds) with bounds in b, Sc, etaSz and t only. In ℓ, because JumpConditions does not mention ℓ, and
  the ℓ-indexed `ConclusionJa` is a single family fact (from `Facts.admJ`).
- There is no analytic content. The j-dependence is only in the sign split j / (m − j) of the m small jumps.

### Q3. Where `sPi` (Bloch–Kato Selmer length of the ρ-block) is bounded

1. `sPi D i π ρ` = nlen(`Br.selPi`): the length of the BK Selmer group of ρ_π ⊗ χ₁^{-1} with K/O coefficients,
   normalised by len(O/ℓ) (`BaseSizes.lean`, `QuotientHomNonvanishingBound.lean:857`) [S].
2. In CutCoreUnit and StarAD, sPi is passed through unchanged [P].
3. It is then bounded by **`KillAt`**: sPi ≤ nuL(ℓ) + epsL(ℓ) (`CommutingEndomorphismCondition.lean:45`) [S].
   - nuL(ℓ) = `KStar.Tree.nuOf ℓ cyc (t·r)` = min_g v_ℓ(ε(g)^{tr} − 1). This is v_ℓ of w_{tr}(E), the order of
     H⁰(E, ℚ_ℓ/ℤ_ℓ(tr)) (`CyclotomicTotient/NuInf.lean:9`) [S].
   - Summed: Σ_ℓ log ℓ·nuL ≤ log QS + log(t·r). The Selmer group is thus bounded by an **H⁰-type quantity**. That makes
     it essentially trivial. It is neither an L-value nor a trivial bound.
4. `KillAt` ⇐ `chosenTwist_annihilates_selmerGroups` = `NLink.twist_kills_selmer` (`IE/ChosenTwistAnnihilatesSelmerGroups.lean`,
   34 lines) [P], which needs:
   - `SignatureChoiceCondition`: sPi(ρ_π) ≤ sLen(ρ_s ⊗ χ_s ⊗ ψ_w) for the twist ψ_w chosen by `NChoice`. It is proved
     by `JointSix.main` (`IE/PsiAtPsiAt.lean`, 43 lines) through `PtSel.selCore` and Chebotarev [P skeleton]. That is,
     the lifts are built so that their ρ-block **is** a chosen twist.
   - `TwGoodAt` → `GoodTw` → `partAT`: sLen(twist) ≤ ν + ε_s with Σε_s ≤ twEps = epsL.
5. **Discharge chain for the good twist** [S for the statements, P for skeletons; decisive sub-lemmas unread]:
   - `IntegralHeckeForms.TwistTheoremAtIndex` ⇐ `export_at_setting` (`IE/IsLatInOfIndexLe.lean:456`, file 498 lines),
     which takes `TwistingCharacterExistence` as a hypothesis.
   - `TwistingCharacterExistence` (`IntegralHeckeForms.lean:166`) [S] states: for every ε' > 0 and every finite set A of
     places there are Q, k' and a character ψ' such that:
     - PsiOk: ψ' is anticyclotomic, ramified exactly at split Q, of ℓ-power order, and trivial above ℓ;
     - **partAT**: Selmer(twist) ≤ ν + ε';
     - **partC**: the twisted theta elements are nonzero with valuation ≤ c₀ + ε';
     - **partD**: t·Σ_Q tame value ≤ ε'.
   - It is proved by `admAB_of_toric_parts` (`IE/IsAuxiliaryPlaceFamilyAtLevelMono.lean:355`, file 471 lines) from
     `DelUTie`, `PropABCD`, `AdmACD` and **`GaloisSideTwistedSelmerAuxiliaryPrimes`**
     (`NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:70`).
   - That last statement says: there are Chebotarev auxiliary primes P such that the Selmer groups of all ℓ^M-twists
     ramified at P are presented by a matrix over O[(ℤ/ℓ^M)^R]. Its determinant polynomial F has a coefficient of
     degree ≤ Dd with valuation ≤ ν. This is "μ ≤ ν" for an auxiliary-twist Iwasawa algebra.
   - It is proved by `galois_export_of_matrix_det_bounds` (`NonGaloisDescent/GaloisExportOfMatrixDetBounds.lean:98`, file
     119 lines) from ThmS, SelmerLengthsByDeterminant, `ResidualBoundOddPrimes` and ThmC.
   - `ResidualBoundOddPrimes` ⇐ `residual_bound_of_parts` (`IE/ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21`, 33
     lines). Its hypotheses are Cheb, Poitou–Tate, cd 2, TameLocal, local finiteness, Tate duality, local and global Euler
     characteristic, global finiteness, UnramifiedOrthogonality, ArchimedeanSignatureMatching and **GreenbergWiles
     (discarded, `_`)**. It calls `exists_auxiliary_primes_prescribed_frobenius` and
     `residual_selmer_determinant_order_bound`.
   - `ThmC` ⇐ `thmC_of_parts` (`IE/AddValLeOfNotMem.lean:87`, file 146 lines), from StepAB, ChooseH, Start, Grow and Step.

   **Assessment:** this is a Ramakrishna/Kolyvagin-style "kill the Selmer group by twisting at Chebotarev auxiliary primes",
   combined with a determinant (Fitting) presentation and a nonvanishing-mod-ℓ statement for twisted theta elements
   (partC, through `PropE`). [N for the literature match.]

### Q4. Conjecture-shaped statements on this strand

1. **`TwistingCharacterExistence` / `partAT` + `partC`.**
   - Content: for representations of rank r ≥ 100 (`SetHyp`: `100 ≤ D.R.r`) at every twisted ℓ, some auxiliary twist
     has Bloch–Kato Selmer length ≤ v_ℓ(w_{tr}(E)) + ε, and its theta elements keep their valuation.
   - Classically this sits near Bloch–Kato together with nonvanishing mod ℓ of twisted L-values (Vatsal/Hida/Finis type).
   - Its proof is the chain in Q3.5, about 1,300 lines across the files named there. It reduces to standard
     Galois-cohomology inputs, plus two archive lemmas I did not open: `residual_selmer_determinant_order_bound` and the
     `thmC_of_parts` components.
   - The Galois side looks like a genuine argument (auxiliary primes, determinants), not a one-line discharge. Whether it
     is correct at this generality is **the** item to check on this strand.
2. **`Cut.ShaBound.main` is not conjecture-shaped.** The deep input is the Ш¹ bound `VVle` (VWin, theta-chain Q5), which
   is outside this strand. Here Ш enters only as an upper bound, and frontier-b showed that only √b is needed.
3. **Discarded literature hypotheses:** `BlochKatoLocal` in `blochKatoTop…_alt` and `GreenbergWiles` in
   `residual_bound_of_parts`. This is harmless for validity, but those named inputs do no work.
4. I found **no** finiteness hypothesis of Selmer groups that is discharged in one line. `sFin` comes with
   SignatureChoiceCondition, and `shaLen < ⊤` comes from `hSha` in StarAD.

### Q5. Unread (with paths)

- `TopBridge.twistedLatticeCohomology_theoremTOP` (`IE/TwistedLatticeCohomologyTheoremTOP.lean:67`),
  `unramifiedEnlargement_cut_cocycles_blochKato`, `exists_exactLocalConditionData_at_place`.
- `LocalGlobalSelmer.main`, `length_cocycles_le_coboundaries_add_selmer`, `length_cutCoboundaryModule_le_unitDelta`,
  `localCocycles_aboveEll_inCut_unitDelta`, `Cut.Peel.main`, `CutTrivIne.main`, `UnramHom.length_le_classNumber`,
  `inertiaCocycleBlock_length_le_of_quadraticRelation`.
- `isUnit_sub_charValues_of_cyclotomic_generator`, `exists_inertia_cyclotomic_generates_units_mod`,
  `SplittingAlgebra.main`, `exists_block_action_of_decomposition`.
- `starInequality_rowsAD_of_global_theorems` in full (`IE/StarInequalityRowsADOfGlobalTheorems.lean`): which core lemma
  (`GlobalCore`/`CutDet.main` with vdel) is used at medium ℓ. Also `nonPlacePart_localBound_le_middleRange`,
  `adm_at_inert_of_range`.
- `SumRepresentations.ConclusionG6` and `NormChoiceFacts.rhoBar` (sources of NoChiOff and ρ̄ irreducibility).
- `JumpSets` lemmas `jumpSetBound_…` to `jumpSetGap_…` (elementary). `jumpLemma_a_of_admissible` (the Galois content of
  ConclusionJa).
- The good-twist chain: `residual_selmer_determinant_order_bound`, `exists_auxiliary_primes_prescribed_frobenius`,
  `thmC_of_parts` parts, `PropE`/`propE_of_admissible`, `PtSel.selCore`, `SelMatrix`/`thmS_of_selMatrix`, `Computes`,
  `SelPoly`.

## What to read next

1. `IE/IsAuxiliaryPlaceFamilyAtLevelMono.lean:355` (`admAB_of_toric_parts`), then
   `IE/ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean` → `GlobalTheory.T.residual_selmer_determinant_order_bound`, and
   `IE/AddValLeOfNotMem.lean:87` (`thmC_of_parts`). This is the proof that twisted Selmer groups can be made nearly trivial.
   It is the most load-bearing and least standard step on the strand.
2. `PropE` (`NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean`) and `GlobalTheory.T.propE_of_admissible`.
   These are the theta-element side (partC): nonvanishing with controlled valuation of twisted theta elements.
3. `IE/PsiAtPsiAt.lean` → `GlobalTheory.PtSel.selCore`: why the ρ-block of each lift is a chosen twist, so that
   sPi ≤ sLen(twist).
4. `IE/StarInequalityRowsADOfGlobalTheorems.lean`: the medium-ℓ core with non-unit root differences (vdel).
5. `IE/TwistedLatticeCohomologyTheoremTOP.lean` (`twistedLatticeCohomology_theoremTOP`) and
   `Formalism/SharpRestriction/LevelLetterCocycles/TableLineDegreeTwo.lean` (`TopCore`, `PositionHyps`): the integral
   local theorem behind "cut cocycles are BD at ℓ".
