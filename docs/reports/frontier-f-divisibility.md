# Frontier F: where the divisibility `WeilJacquetShalikaLaw.Conclusion1` is proved

Date: 2026-11-20. Read-only study of `/bulk/shared/rieman/lean/src` on chili, using `ssh` with `sed`, `grep` and `cat`, plus
`analysis/reach/decl-index.tsv`. Nothing was compiled or run. Paths are relative to `src/`. This report continues
`frontier-a-divisor.md`, `core-gm.md` and `frontier-b-links.md`. About 75 tool calls.

Tags:
- **[S]** means read in the statement or definition.
- **[P]** means the proof was read in full.
- **[P-skel]** means the `have`/`obtain`/`refine` skeleton of the proof was read.
- **[N]** means inferred from names or from the shape of a statement.

## Overview (for a number theorist)

The divisibility is proved. It is not a hypothesis of the top theorems. The only assumed input on its path is the
literature statement `GlobalArtinReciprocity`; everything below it is a theorem in the archive.

The trail runs as follows:
- **The global statement.** `Conclusion1` is the first conjunct of `WeilJacquetShalikaLaw.Conclusion₂`.
  `WeilJacquetShalikaLaw.Proof.stmt_proved` proves `Conclusion₂` from a list of local hypotheses (`admitted`).
- **The local inputs.** These hypotheses are supplied by `sum_over_primes_service`. That function reduces them to a
  local p-adic theorem, `FormalGroupSystem.Stmt`, at each prime w | p inert in the CM field.
- **The local theorem.** `FormalGroupSystem.Stmt` is proved as `FormalGroupSystem.Pf.stmt_proved`.
- **Tying the global chain to the local models.** The map between the global chain and these local models comes from
  CM elliptic curves. Good reduction (`CM2`) follows from `GlobalArtinReciprocity`. Supersingular reduction at inert ℓ
  (`CM3`, Honda theory) is a proved theorem: there the formal group becomes the height-2 Lubin–Tate group with logarithm
  Σ_j x^{ℓ^{2j}}/ℓ^j.

The mechanism is a **Dwork/Katz-type p-adic analysis of a theta kernel** on a power of the supersingular formal group:
- Each lift step is written locally as a sum over lattice tuples at the inert place. The summand is a **differential
  operator (products of minors) applied at the origin** to the theta kernel exp(−Σ_e β(x_e, y_e))·U. Here β is the
  canonical biadditive pairing on the height-2 formal group, and the period normalization is δ = Δ^{1/12}.
- **"Theorem S"** shows that in Lubin–Tate log coordinates this kernel lies in a class Σ_i p^{−i}·hh^i·(integral). Here
  hh = Σ_s u_s·s_s^p·s_{s+1} couples Frobenius-adjacent coordinates.
- A **jet bound** (Hasse derivatives plus a factorial inequality) then gives the valuation of any degree-a derivative at
  0. The bound is ≥ Σ_{odd e} (a/p^e − cap(s+e))⁺ − O(log terms).

This is literally the announced "D^a Ω·θ(0) divisible by p^{a/p + a/p³ + ⋯ − O(log a)}", with a correction for the
weight of the partner variable s+e, which is the Frobenius-shifted place.

The m lifts are handled **one step at a time**, by induction over j (`main_ind`), and the per-step gains are added up.

## Task 1. Where `Conclusion1` is proved, and the main path

### 1a. The proposition [S]

`Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:101`:
```lean
def Conclusion1 D L X Y K c Dx T lev Xe ce sp : Prop :=
  Ties9 D L X Y c → ErrDefs D L Xe lev K ce → ∀ u w, resChar w ≠ (D.mem u).A.T → resChar w ∉ {g 0, g 1} →
    ∀ μ, DV.Used D μ → resChar w ∉ Dx.Qp μ → ∀ x, InNP X Y K c u w x → ColGe T u μ w x (totS X K Xe ce sp u w)
```
- `ColGe` (`:37`) says that the image of x under the full column (`(D.mem u).C.col`, the m-step chain from level 0 to
  level `D.R.m`) is a·z with z in the w-local lattice and v_w(a) ≥ the threshold, up to the ramification index `ur`.
- `totS` (`:80`) is Σ_j (gainS_j + F_j − ES_j) + sp·v_p(DGam).
- `gainS` (`:53`) is `gainP` at inert or "Sg" primes, and 0 at excluded, split ("Cs") and other primes.

The containers are as follows [S]:
- `Conclusion₂` (`:233`) = `Conclusion1 ∧ ZeroGainValuation ∧ ColumnValuationAwayFromTypePrimes ∧ TupleLatticeValuation`.
- `Stmt` (`:238`) = ∀ T W lev Xe ce, CmpV → ∀ sp ∈ {0,1}, `admitted` → `Conclusion₂`.
- `Serv` (`:245`) = `TypePrimeSizeConds ∧ Conclusion1 (sp=1) ∧ ColumnValuationAwayFromTypePrimes`.
- `ServF` (`:256`) is the family version of `Serv`.

The consumer is `off_level_bound_family` (`:618`) [P]. It turns `Conclusion1` together with `PairInt`, which says the
period pairing has bounded denominators v_p(DGam), into the `adm2`-type integrality of `perCol` at valuation `L.sg u w`.
It does this through `period_ge` (`:423`, [P]: valuation of the product, `val_step`).

### 1b. The theorem that proves it [P]

`Formalism/SharpRestriction/GrowthBounds/AdmissibleIntegers.lean:15`:
```lean
theorem stmt_proved D L X Y K c Dx : Stmt D L X Y K c Dx := stmt_of_rest restComp_proved D L X Y K c Dx
```
Inside it [P-skel]:
- `stmt_of_rest` (`…/AdmissibleIntegers/StatementsOfRemainingBound.lean:206`) calls `statements_of_remaining_bound` (`:194`).
- That obtains `⟨hU, _, _, hNo, hC, hD⟩ := hA` from `admitted`.
- It sets `hGt := first_in_local_models W hU` (`:111`), which goes from `unitBoundAtTwistedPlaces` to
  `TupleLatticeValuation`.
- **`Conclusion1 := baseChange_preserves_unitary_of W hV hGt hNo hc`** (`:162`). This uses `kernel_valuation_served`
  (WJS `:352`, [P]): the lattice growth ≥ Σ_j gainP + low at the local model, transported by `CmpV`, gives `ColGe` with
  `totS`, because gainS ≤ gainP.

So `Conclusion1` holds **under `admitted`** (WJS `:228`). Its arithmetic clause is
**`unitBoundAtTwistedPlaces`/`UAt` (`:165`)**: in the local lattice model at w, every F has
`vKge(yProd … F) ≥ Σ_j [Σ_{t0∈VV'} max(gU − Pr, g0) + Σ_{rest} g0] + low`.

### 1c. Who supplies `admitted`, and so `ServF` [P]

`Formalism/SharpRestriction/SmoothDesignExistence/SumOverPrimesHypotheses.lean:187`, `sum_over_primes_service`, read in
full:
```lean
have hU := G.Joints.unit_bound_of_sum_over_primes … (reW (Fm.Gy x i) LC) … 1 (FormalGroupSystem.Pf.stmt_proved _) hSys
  (num_re LC (hnum x en i)) (G.TopChoiceBounds.hLarge_proved …)
…
have hAdm : WeilJacquetShalikaLaw.admitted … := ⟨hU, local_theorem_of_statement _ (FormalGroupSystem.Pf.stmtAt_proved _), it, n, c, d⟩
exact serv_re LC (WeilJacquetShalikaLaw.serv_of (WeilJacquetShalikaLaw.Proof.stmt_proved …) (reW …) hV hAdm (ha x ea h1 i))
```
- `unit_bound_of_sum_over_primes` (`Formalism/SharpRestriction/GrowthBounds/JointsTw.lean:243`) [S, P-skel] gives `UAt`
  from three inputs:
  - (i) the **local theorem `FormalGroupSystem.Stmt D`** applied to the local system `Y5` at w;
  - (ii) `SysTw`, the hypothesis that an admitted local system exists at w and that the small-orbit gains `Fn` cover
    `lowS`;
  - (iii) `SmallResidueCharComparison`, from `FormalGroupSystem.Pf.stmtNumE`. This says that the global gains are at
    most the local ones: gU ≤ gB, g0 ≤ gA, and local Pr ≤ global Pr.
- Primes p > 2a give no gain (`hLarge`).

The upward chain to the top theorems is as follows [S unless marked]:
```
ServF  ← sum_over_primes_service 𝒞 hD (SumOverPrimesHypotheses)                     SumOverPrimesHypotheses.lean:187 [P]
       ← closed_servF_of_servT_of_dGamSize sel hDG hServ                                  ThirdPlaceSeries/GServT.lean:31
       ← closed_family_admissible_twist_link_alt (field `serv`, hServ : SelectionServed)  ClosedFamilyAdmissibleTwistLink.lean:24-29
       ← Hyps.hServ : GlobalTheory.Cp.SelectionServed …                                   ThirdPlaceSeries/Hyps.lean:76
       ← nonempty_hyps_of_allRows_alt (hServ := hServ)                                    ThirdPlaceSeries/NonemptyHypsOfAllRows.lean:43,93
       ← allRows_of_open0_alt … hServ := LinkedAt.of_row (T.hServ_of_linkR hA …)         ThirdPlaceSeries/LinkROfIsLinked.lean:50,76
       ← hypotheses_nonempty_of_unramified_exponents_alt (P.globalArtinReciprocity)       HypothesesNonemptyOfUnramifiedExponents.lean:41,54
```
The fields `twU` (= `RowTwU`: `CmpV ∧ SysTw`) and `pdv` of `SelectionServed` come from GlobalArtinReciprocity:
```
hServ_of_linkR → row_hServ_of_link_alt → row_hServ_of_kerServ_alt ← Row … (Svd.ServH ker)      RowHServOf*.lean [P]
ServH := (Closed 𝒜 RowTwU) ∧ AtAll (Pdv.At …)                         Definitions/GaloisGeometry/HasPartAnd.lean:45 [S]
reciprocity_kernel_of_artin → servH_row_linkR_alt → T.bundle_bothParts_of_standardKernel_of_globalArtinReciprocity
  → Svd.servH_row_of_artin   (Proofs/SatakeParameters/BundleBothPartsOfStandardKernelOfGlobalArtinReci.lean) [P]:
      h2 : CM2 := cmGoodModel_of_globalArtinReciprocity hA
      servH_row (torsionTaylorAlgebraic_latticeExists_of_cm h2) … (intInert_of_complexMultiplication_condition h2)
                (inert_theta_admissibility_of_complex_multiplication h2 : AdmAtEnt2)
                (exists_genusOne_formal_iso_of_unramified_good_reduction h2 : CurveEx)
  → servH_row (…AndSixHypotheses.lean) [P]: Row.and (Svd.rowTwU Q Lk hM) (Pdv.rowAt_of_stdTie …),
      hM : ModelsAt from T.tuplesHaveLocalModels_at_constructedPoint_over_trueColumns hE hX
  → rowTwU (RowTwUHolds.lean:15) → rowTwU_of_models (UnitaryWeightModels.lean) [P]:
      CmpV := cmpV_of_cmpLite …;  SysTw := T.local_systems_lower_bounds_second_real_place … (fun … => SiteAdm …)
```
- `SiteAdm` (`Definitions/GaloisGeometry/IsPlaceCofactorValuationLowerBound.lean:10`) [S] says: there exists a local
  formal-group system `Pend` with `FormalGroupSystem.admitted`, dG 0 = 0, and dG_j ≤ v_p(DGam).
- `AdmAtEnt2` (`ThetaSeriesDataHypothesesBelowMaximalLevel.lean`, about line 105) [S] says: for every chain at an inert
  place, given a CM curve (`CurveIn`), the theta-series data, `XiIn`, `LawInLt` and `TiesAt`, the local system `pendG …`
  is `admitted`.
- `AdmAtEnt2` is proved by `inert_theta_admissibility_of_complex_multiplication`
  (`Proofs/SatakeParameters/InertThetaAdmissibilityOfComplexMultiplication.lean:8`) =
  `AdmLoc2.admissible_entries_small_chain` (`Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/AdmissibleEntriesOfKernelLaw.lean:106`)
  [P-skel], using `KGLt.first_kernel_law_global_small : TranslatesOfInertKernelAtPlace` (`FirstKernelSmallOfFrameTwist.lean:124`).
- The CM inputs [S]:
  - `CM2` (`Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean:45`): every lattice with CM by
    ℚ(√−d), d ≡ 3 mod 4 squarefree, has a good model over the maximal unramified extension of ℚ_ℓ for ℓ ≥ 5, ℓ ∤ d.
    It is proved from GlobalArtinReciprocity (`CmGoodModelOfGlobalArtinReciprocity.lean:10`).
  - `CM3` (same file), proved as `GlobalTheory.HondaCM3.cm3` (`DecoratedLatticeProofs/OneSubTwoOmegaSq.lean:77`) with no
    further hypotheses: at **inert** ℓ (−d not a square mod ℓ), the formal parameter composed with ε·`ltLog` is
    integral. Here `ltLog` = Σ_j x^{ℓ^{2j}}/ℓ^j is the height-2 Lubin–Tate logarithm. This is supersingular reduction,
    made explicit.
  - `CurveEx` is proved as `curveEx_of_cm h2 cm3`.

**Conclusion of Task 1.** On the main path, `Conclusion1` is proved for every family point, assuming only
`GlobalArtinReciprocity`, which is passed in as `P.globalArtinReciprocity` from the literature bundle. I did not open
`hypotheses_nonempty_of_unramified_exponents_alt` past line 57. I take the link from it up to
`every_character_of_literature_of_vWin` (via `published_results_eigen`) from the earlier reports [N].
`sum_over_primes_service` also needs `hD : DGamSize`, which `ClosedFamilyAdmissibleTwistLink` supplies as `hDG`; I did
not trace it. It also needs the `pdv` kernel conditions (`EvenConditionsInert`, `OrbitBoundWithoutOperator`,
`JetIntegralityBis`, …), which feed `OrbitsWithoutOperator`/`MediumInertPrimeLengthBound`, the non-served primes.

## Task 2. What object is bounded, and the mechanism

### 2a. The local object [S]

`Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`:
- `Sys p` (`:264`) is the local model at w | p. It has these parts:
  - lattice-tuple levels `Lv`;
  - form spaces `Fm j`, the functions on lattice tuples at w, one per lift j;
  - integral lattices `Int j`;
  - a chain `Kz j : Fm j → Fm (j+1)`;
  - a uniformizer `vp`;
  - an `OmBasis` of W(F̄_p) elements that is σ-twisted;
  - `std : Std p n' k1 t m c r …`, which requires **p ≥ 5**, n' even, 2r ≤ k1+1 and m ≥ 1, w_1 ≥ c, and **w monotone in
    the lift index** (`w_mono`).
- `KerAtMu` (`…/LatticeMultiplicityCheck/Retype.lean:9`) [S] ties this to the global chain:
  - the j-th lift's class set corresponds to lattice tuples modulo Γ;
  - the stabilizer orders divide `DGam`;
  - `cmp j` sends the global lattice onto `Int j`;
  - `cmp_K` intertwines the global step `K j` with `Kz j`.
- `Pend X` (`:447`) is the "pending" analytic data. It has these parts:
  - a p-adic field `Kc` with valuation ring `Oc`;
  - a power series `be` in two variables, a biadditive pairing on the formal group (`BeProp`, `:147`: biadditive modulo
    integral series, and σ-semilinear for W(F_{p²})-scalars);
  - per step j and lattice pair (La, La'), a theta kernel `ThA` and its coordinate version
    `ThF = linSub bc (ThZA ThA)`;
  - a degree-constrained **differential operator** `DelF` (`Del_deg`: only monomials of total degree
    Σ_i ν(j+1, s, i), the lift's weight vector, survive).

The chain step is a kernel sum. `ExpansionEquality` (`:566`), a clause of `admitted`, states:
`Kz j F (c', L') = Σ_{La ∈ Rep j} stab(La)^{-1}·cK · ker j La (c', L') (F La)`, where
`ker = (eS/eT)·DelF j G (ThF j La La')`.

**So each lift step is a sum over lattices of a differential operator applied to a theta kernel in formal coordinates at
the CM point, normalized by p-powers of lattice lengths.** That is the "D^a Ω·θ(0)" of the announcement.

The bounded quantity is `Pend.LowAt` (`:529`):
```lean
def LowAt j v g := ∀ U, IntR Oc (inParamK p Kc U) → ∀ (I : X.ColCh j) n,
  geC (coeff n (applyD (X.PIv j I v) (X.ThZA Kc j (map (expS p (-Y.PhAt j v)) * U)))) g
```
- `applyD P f` = Σ_n (∏ n_x!)·coeff_n(f)·coeff_n(P). This is "apply the constant-coefficient differential operator P
  and evaluate at 0".
- `PIv` is a product of minors (`eb_jet`: it equals `DworkPowerSeriesWeights.frameJet` of `minorProd`, a Cayley/Shimura
  type operator).
- `PhAt j v` = Σ_e be(x_e, y_e) is the exponent of the theta kernel.

So the object is **the value at the origin of a determinantal differential operator applied to
exp(−Σ β(x_e, y_e))·U**, with U integral in log coordinates.

### 2b. The mechanism [S for statements, P-skel for wiring]

It is option (a), realized via Lubin–Tate/Dwork power series, combined with (b) the factorial count.

1. **Supersingular formal group.** `logF` (`FormalGroupSystem.lean:126`) and `lgF` (`ThetaLogCoordinates/UniformThetaSubstitution/OddLogRelation.lean:13`)
   are both Σ_j x^{p^{2j}}/p^j. `CM3` identifies the CM curve's formal group at inert p with this height-2 law. `LTIso`
   and `GL3Theta.G1` carry the isomorphism [S, N for the identification of GL3Theta].
2. **The canonical pairing.** `ThmSUniform` (`…/UniformThetaSubstitution/ThmSUniform.lean:14`), proved as
   `theorem_s_uniform` (`FrobeniusLiftNorms/OmegaOfTraceDuality.lean:31`) [S], shows:
   - any `be` satisfying `BetaHyp` is ≃ `Gser p c (σc)` = c·A − σ(c)·A′, where
     A = Σ_{i≤j} x^{p^{2i}} y^{p·p^{2j}} / p^{i+j+1};
   - **"Theorem S"**: for the theta kernel `mvExp(−Φ)·U0` with Φ ≃ Σ_e be(x_e, y_e) and U0 integral, after the
     substitution into ϖ-scaled log coordinates (ϖ^{p²−1} = p, the Lubin–Tate uniformizer), the result is in
     ```lean
     InClass p (hhS p (uS c (σ c))) F  :=  ∃ U_i integral, coeff_n F = Σ_{i ≤ deg n} p^{-i} · coeff_n (hh^i · U_i)
     hhS p u = Σ_s u_s · Σ_ab sPos_s^p · sPos_{s+1},   sPos_s = Σ_l (−1)^l X_{s−2l}^{p^{2l}}     (CyclicPowerClassOfExpEquiv.lean:85)
     ```
     The index s ∈ ℤ/2ν labels the Frobenius conjugates of the CM type. hh couples the p-th power of coordinate s with
     coordinate s+1, and sPos brings in X_{s−2l}^{p^{2l}}.

     **Dwork's integrality lemma** (`DworkLemma`, `FormalGroupSystem.lean:225`: exp(P) is integral iff
     P^σ(x^p) − pP ∈ pW[[x]]) is an input to this step. It is **proved**: `positivity_condition_holds : adm1 D := sx_dwork p`
     (`MultisetValuation/PositivityConditionHolds.lean:115`), despite the name.
   - Its global analogue is `RestGc` (`MultisetValuation/DworkExponentialRestrictions.lean:19`), proved as `restGc`
     (`CommonEigenvectorThird.lean:21`). It says that exp(−G_t(c, σc)) in these coordinates is
     exp(−(ϖ^{p+1}/p)·hhS(u))·V with V integral.
3. **The jet bound** (`Formalism.InvariantFactorPaths.G7`) [S]:
   ```lean
   def KernelValuationBoundUltrametric := … InClass p (hhS p u) (subst (ϖ·X) Th) →
     ∀ n, ‖coeff n (frameJet colN hts hp I Th)‖ ≤ p ^ (-(excessGain p TT (dSet TT) (alG …) (capG …) (deLoss …)))
   excessGain p TT D al cap de = Σ_{s∈TT} Σ'_e (if 2e+1 ∈ D s then 0 else max (al s / p^(2e+1) − cap (s + (2e+1))) 0) − de
                                                                            (GrowthSums/StatementA.lean:108)
   ```
   - It is proved by `kernel_a_one_generic` (`FrobeniusLiftNorms/EGaussK.lean:213`) [P-skel]. The chain is
     `kernel_a_one_generic_of_gauss gauss_a_one_generic` ← `gauss_a_one_generic_of_entry Top.entry_a_one`.
   - The generic-element (Gauss norm) reduction is `EGaussK.reduce`.
   - `Top.entry_a_one` (`UniformThetaSubstitution/KOneConsequence.lean:43`) [P] is
     `entryExcessBound_of entryStar hitsCapPos excessGainBound cyclicShiftLeast`.
   - `EntryStar` (`StatementE.lean`) [S] gives the bound p^{−(γ_p·Σ_s al_s − Σα − Σβ − deLoss + …)}. Here
     γ_p = p/(p²−1) = Σ_{odd e} p^{−e} (`gamP`, `GammaIdentity`), and α, β count the Hasse-derivative uses
     (`hasseDir`, `HasseDerivProdVanish`). Its ingredients are `JetPairingHasseIdentity`,
     `HasseDerivIntegralHomogeneous`, `HasseDerivProdVanish`, `gainFactorialInequality` (`starArith`) and
     `decomposition_of_hh`.
   - `excessGainBound` with `cyclicShiftLeast` turns γ_p·a − (uses) into the truncated positive parts
     Σ_{odd e}(a/p^e − cap(s+e))⁺.
4. **The local gain equals the global gain formula.** `ea_A1U` (`MultisetValuation/EaGeCOfNorm.lean:198`) [P] applies
   `kernel_a_one_generic` to `LowAt`, using `ea_BrNum`. `ea_BrNum` identifies `excessGain(alG, capG, deLoss)` with
   `X.g0v v (j+1)` = `gA` (`FormalGroupSystem.lean:66`):
   ```lean
   gA p t TT lam0 w j = Σ_{s∈TT} Σ' e, (if 2e+1 ∈ dSet TT s then 0 else max (al s / p^(2e+1) − cap t TT lam0 w j (posAdd s (2e+1))) 0) − de …
   al s = λ_s(1) − λ_s(2)   (top Harish-Chandra gap at s ∈ TT);   cap … j s' = ν(j, s', 2 or 1) = w_j(s') + λ-shift
   ```
   This is `VolumeRatio₂` (`:658`): `∀ v, ∀ j < mm, LowAt j v (g0v v (j+1))`. It is proved in
   `FormalGroupSystem.Pf.rests` as `U2 := auxU_of_firstTheoremPlaceBound … (first_theorem_place_bound X Y D (restGc p) (eb_brJet X))`
   (`PrvAndKernelCommutationUpToUnitsOfRests.lean`) [P].

**Answers to (a)–(d).**
- **(a) Yes, in substance.** The p-nilpotence of the invariant derivation does not appear as a lemma. Its role is played
  by the explicit structure of the height-2 Lubin–Tate formal group (`CM3`, `lgF`) and the Dwork exponential lemma. The
  canonical pairing then has only p^{−i} denominators attached to hh^i, and hh has p-th-power leading terms.
- **(b) Yes, as the counting mechanism.** `applyD` carries the n! factors, and `gainFactorialInequality` is a Legendre
  type estimate. γ_p = Σ_{odd e} p^{−e} is the odd-power half of Legendre's 1/(p−1) (`GammaIdentity`:
  γ_p = 1/(p−1) − 1/(p²−1)). Odd exponents arise because Frobenius on the inert residue field is an involution on the
  ℤ/2ν index, and hh links s to s+1.
- **(c) Lattice and Weil models.** These enter only as the local lattice-tuple model (`KerAtMu`, `ExpansionEquality`,
  `MinkowskiCounting`). I saw no Schrödinger or Fock model in what I read.
- **(d) The name is not descriptive.** "WeilJacquetShalikaLaw" names the namespace of the global valuation statements.
  I found no Jacquet–Shalika identity in it. The "law" consumed is the **kernel law** `TranslatesOfInertKernelAtPlace`
  (`Formalism/LocalToGlobal/InertKernelTheory/TranslatesOfInertKernelAtPlace.lean:20`) [S]. Given a CM curve with a
  Lubin–Tate isomorphism (`GL3Theta.At`, `InertK`, `ModelOverW`), a curve ideal cc, δ a 12th root of the discriminant
  (`IsDiscriminantTwelfthRootOfIdealLattice`), and the frame and lattice data, the actual lift kernels satisfy:
  - `adm2`: each ThV is `expS(−Ph)·U` with U integral in log parameters and Ph ≃ Σ_e be(x_e, y_e);
  - `adm2b`;
  - `adm3`: integrality with zero operator.

  It is proved as `first_kernel_law_global_small` (`FirstKernelSmallOfFrameTwist.lean:124`), whose proof I did not read
  beyond line 130.

## Task 3. Accumulation over the chain

- **One lift at a time, then summed** [P-skel]. `lift_bound_of_integrality`
  (`MultisetValuation/LiftBoundOfIntegrality.lean:103`) proves `LowTermBound` (`FormalGroupSystem.lean:708`) by span
  induction over generators of `Iprod S VV`, calling `main_ind`. `main_ind` is an induction over j that composes
  `Kz 0, …, Kz (mm−1)`. The per-step hypothesis is `LowAt j v (G0n v (j+1))`. The output is:
  ```lean
  X.vGe X.mm (X.chainK X.mm F) (Σ_{j=1}^{mm} (Σ_{v∈VV} max (Gn v j − PRn v j) (G0n v j) + Σ_{v∉VV} G0n v j) − Σ_{j<mm} dG j)
  ```
  `Conclusion5` (`:697`) is this with Gn = gv, the "served" gain with Hecke-operator correction `Pr`. `basic₂` [P] is the
  real-number bookkeeping that splits off the served places.
- **Why step j uses w_j at the Frobenius-shifted place.** The per-step kernel `ThF j La La'` maps level j to level j+1.
  The operator `DelF j` has the degree pattern of ν(j+1, s, i) = λ_s(i) + w_{j+1}(s) (`nu`, `:28`). In
  `excessGain`, the cap at the partner index s+(2e+1) is the (j+1)-st lift's weight there:
  `cap t TT lam0 w j (posAdd s (2e+1))`. On the global side (`IsResidueClassZero.lean`, `capU … j s e = fill j (partner p s e)`)
  the same index shift is "translate by e·Frob_p and flip conjugation for odd e".
- **Where m shows.**
  - The sum Σ_{j=1}^{mm} is over the steps.
  - The loss `de` (`:46`) contains NN(j−1)·NN(j)·lgp(lsz) with NN(j) = k1+1+j(t+1). So the per-step O(log) loss grows
    like j²·log_p a. That is consistent with the m³ term in `RecNums.hB`.
  - dG_j ≤ v_p(DGam) is lost at every step.
  - The cap `RelativePresentationLiterature` (Sv ≤ m·γ_p·Σ al), proved as `relative_presentation_of_d7`, bounds the
    served excess by m copies of γ_p·a.
- **Restrictions** [S]:
  - p ≥ 5 (`Std.five_le`, also in `CM2`/`CM3`);
  - w_l(s) nondecreasing in l (`w_mono`), so the lifts' weights may only grow along the chain;
  - 2r ≤ k1+1;
  - primes with log_p(2a) < 1, i.e. p > 2a, give no gain (`hLarge` in `unit_bound_of_sum_over_primes`);
  - GIdx/`Exc` exclude the level and type primes.

  I saw no explicit upper bound on m in terms of a or p in the local theorem. m is only constrained globally
  (x^{1/2−ε} ≤ m ≤ x^{1/2+ε/2}).

## Task 4. The nonvanishing side

- `LinkS` comes from `GlobalTheory.Top.link_alt_alt_bis` (`ThirdPlaceSeries/LinkAltAltBis.lean:16`) [S]. Its inputs are:
  - `sO : TheoremSSelected`;
  - `sLp : LoopRowS`;
  - `h30 : CountAllPointsClass`;
  - `hInstR : VolSigIndep ∧ ClassItemsAt` (genus-mass volumes);
  - `hTF : TFrame`;
  - `hWu : WuDecayOfGap`;
  - `hRF : RowsFinDim`.
- **`TheoremSSelected`** (`Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/ThmSOwn.lean:669`) [S]. It
  is the **off-diagonal** half: for words u ≠ u′,
  ```lean
  ‖((s.2 x hx h0 i).Y.tO u u').K0‖ ^ 2 ≤ (1 + b⁻⁶) * (duS u * duS u' / Dstar)
  ```
  It is proved by `theoremS_selected_of_loops` (`:1026`, P-skel). The inputs are `TheoremSSingle` (`:977`, data form
  `TheoremSAtDataAlt` `:968`), `LoopRowS` (rows "big" and "not scalar"), size rows and `AbsConvTied`.
  - The hypotheses of `TheoremSAtDataAlt` name `PoincareAmplitudeLowerBounds.SizesAt`, `GapHyp`, `KTwoHypotheses`,
    `TFrameAt` and `LocTied`.
  - `LoopRowS` comes from `T.loopRows_of_large_gap_discreteSeries` (`Proofs/FlagMeasures/LoopRowsOfLargeGapDiscreteSeriesStatement.lean:16`)
    via `GapIn.Hyp`, `BesselOfW`, `ThmBpDS` (discrete series) and `WuDecayOfGap`.
  - The names (Poincaré amplitudes, Wu decay, fundamental domains `FundExists`, orbital integrals `OOIntAll` in
    `PoincareConstantEq.lean:130`) point to a **geometric-side/Poincaré-series estimate of the Hilbert–Schmidt
    cross-terms** plus point counting and mass formulas [N]. This is a counting argument, not a Rallis inner product
    with an L-value.
- `BesselId` (`Formalism/SharpRestriction/GlobalTheoremInputs.lean:65`) [S]: B_u(φ, F) = a·besS_u(Uφ, VF) with a ≠ 0 and
  U, V isometries. It is a clause of `LinkDIV_at`. I did not trace its provider.
- I found no use of a nonvanishing central L-value or of the Rallis inner product formula on the lines I read. Whether
  the diagonal term ‖K_D(u,u) − id‖ (e0) and `BesselId`'s a ≠ 0 rest on a seesaw to a character-independent Bessel
  period (announcement item 12) remains open.

## Task 5. Unread on this path, in priority order

1. `KGLt.first_kernel_law_global_small` / `first_kernel_small_of_frame_twist`
   (`Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/FirstKernelSmallOfFrameTwist.lean:124` and callees).
   This is the claim that the **actual** global lift kernels, written in Lubin–Tate coordinates at the CM point, have
   the form exp(−Σβ)·U with U integral. It is the bridge from automorphic theta lifts to the p-adic power series.
2. `T.thetaLocalModels_of_splitUnramified_joints` and `Svd.jointsAt_all_std` (via `modelsAt_of_part`,
   `Proofs/SatakeParameters/TuplesHaveLocalModelsOfStandardColumnObjects.lean:11`), together with
   `TwTie.KerAtMu`/`admissible_third_instance`/`admissible_fourth_instance` (`SecondKernelInstances.lean:128`). These
   prove that the global chain steps K_j equal the lattice-sum kernel expansion (`ExpansionEquality`), with stabilizers
   dividing DGam.
3. `theorem_s_uniform` (`OmegaOfTraceDuality.lean:31`) and `gcCondition_of_twoSums`/`restTwoSums` (`CommonEigenvectorThird.lean`).
   This is "Theorem S", the InClass structure of the theta kernel.
4. `EntryStar_of`, `gainFactorialInequality`, `excessGainBound`, `cyclicShiftLeast`, `HasseDerivProdVanish`
   (`UniformThetaSubstitution/FrobeniusLiftNorms/*`, `GrowthSums/*`). This is the jet/factorial inequality: where
   Σ_{odd e}(a/p^e − cap)⁺ is actually derived.
5. `GlobalTheory.HondaCM3.cm3` (`OneSubTwoOmegaSq.lean:77`) and `cmLattice_good_model_unramified`. These are
   supersingular reduction and good models.
6. `sysTw_sites` (`LocalSystemsLowerBoundsSecondRealPlace.lean:48`), `FormalGroupSystem.Pf.stmtNumE` (global ≤ local gain
   comparison) and `main_ind`.
7. The `pdv` kernel conditions and `J.four_orbit_conditions_of_proof` (`AdmissibleParameterJoins/GandSab.lean:11`) for the
   non-served primes, together with `DGamSize`.
8. Task 4: `TheoremSSingle`'s provider, `loop_rows_closed_gap`, the diagonal e0 bound and `BesselId`'s provider.

## What to read next

- `Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/FirstKernelSmallOfFrameTwist.lean`
  (`first_kernel_small_of_frame_twist`, `first_kernel_law_global_small`). This is the decisive global-to-local
  identification.
- `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:447-780` (`Pend`, `LowAt`, `admitted`, `Conclusion5`)
  next to `Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/AdmissibleEntriesOfKernelLaw.lean:62`. This shows
  which admissibility clause comes from which lemma.
- `Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/OmegaOfTraceDuality.lean` (`theorem_s_uniform`)
  and `KOneConsequence.lean` (`entry_a_one`). These are the p-adic heart.
- `Formalism/SharpRestriction/GrowthBounds/MultisetValuation/LiftBoundOfIntegrality.lean` (`main_ind`). This is the
  accumulation over the chain.
- `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/ThmSOwn.lean:968-1060` and
  `Development/AbelianVarietyTheory/Proofs/FlagMeasures/LoopRowsOfLargeGapDiscreteSeries.lean`. These are the
  nonvanishing (LinkS) side.
