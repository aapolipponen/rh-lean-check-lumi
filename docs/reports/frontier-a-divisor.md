# The divisor inequality: `divisor_inequality_explicit`, `DivIneqRecord`, `DIV`

Date: 2026-11-20. Read-only study of `/bulk/shared/rieman/lean/src` on chili, using ssh with `sed`, `grep` and `cat`, plus
lookups in `analysis/reach/decl-index.tsv`. Nothing was compiled or run. Paths are relative to `src/`. This report continues
`core-gm.md` and `analytic-core.md`. About 65 tool calls.

Tags:
- **[S]** means read in the statement.
- **[P]** means read in the proof (in full, or the skeleton as stated).
- **[N]** means inferred from names or from the shape of a statement.

## Overview (for a number theorist)

`divisor_inequality_explicit` contains no arithmetic. It is a 30-line real-variable lemma. It says that if one has upper
bounds for three quantities, then one has the bound `DIV`: μ_dual(RR) + h(B_u) − Fo ≤ m·Σ_t(a_t log a_t − a_t − a_t logΩ) −
Σ_t a_t log T + errors. The three quantities are:
- the dual slope of a target Hermitian lattice RR;
- the Arakelov height of a map B_u that factors as a chain of m linear steps, one step per "lift" j;
- the archimedean size of each step.

The m copies of a log a − a appear because the height bound for **each step j** is Σ_ρ Σ_i ph(ν_{jρi}) − ν·logΩ, with
ph(y) = y log y − y. This is a Stirling/log Γ size of Harish-Chandra-type parameters ν. The top entry of every step's
parameter vector is the same a_t, and a_t is itself an archimedean weight of the form. A k·w·logΩ part cancels against a
covolume bound for the target. Here Ω is a Chowla–Selberg-type constant: logΩ = γ + log(π/v) − L'/L(1, χ_d).

The surrounding structure is Bost's slope method for Hermitian 𝓞_K-lattices over a CM field K:
- The map B_u sends the lattice Nu_u, **shifted by a finite-place divisor sg** (the "gains"), into the dual of RR.
- The dual slope of RR is bounded **below** by averaging over the words u, using Hilbert–Schmidt near-orthogonality of the
  B_u (`LinkS` → `SlopeIneq`).
- The dual slope of RR is bounded **above** by `DIV`.

The arithmetic content is outside the divisor inequality, in hypotheses that the chain receives from the "TopShapeAlt"
bundle:
1. A valuation statement for the columns of the lift chain at inert places: `Conclusion1`, giving a divisibility of order
   Σ_j gain_j(p). Here gain_j(p) is an explicit formula of the shape Σ_{odd e}(a/p^e − w_j(Frob-shifted place))⁺.
2. The per-step archimedean norm bounds (`nKcb`, `CBHyp`).
3. The covolumes of the m lift lattices (`L3main` / `adm3`).
4. The near-orthogonality `LinkS`.

The argument is additive in the lifts. The only "interaction" is composition of the m steps (subadditivity of heights) and
near-orthogonality across the words u, not across the lifts j.

## Q1. What `divisor_inequality_explicit`, `DivIneqRecord` and `DIV` state

### 1a. `DivIneqRecord` (`Formalism/QuotientMetricDivisors/ScalarLiftLowerBoundFull.lean:53`) [S, read in full]

This is a statement about real numbers only. J has |J| = m (the lifts) and Pl is a finite set of archimedean
places/characters ρ (|Pl| ≤ f). TT ⊆ Pl is the set of "top" places. The hypotheses are:
```lean
muC ≤ mu0 + Lpass →
mu0 ≤ ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
hu = hP + ∑ j, hK j - mlam →
(∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
(∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ) →
(∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
L = x ^ eps → b = exp L → a = x * b → … (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La → … size bounds on eK, eE, δ, Eb, eP, e6 …
```
The conclusion is:
```lean
muC + hu - 2 * Fo ≤ ∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)
    + ((50 * C0 + 10) * (TT.card * a * La) + 60 * ce * (m * (x ^ eps * B0 + (log x) ^ 2 * Nc)))
```

**`divisor_inequality_explicit : DivIneqRecord := divIneqRecord_of divisor_inequality`**
(`…/HermitianTwistDivisors/GlobalBoundRefinements.lean:91`) [P, read in full]. `divIneqRecord_of` only rescales constants
(`recAux`, `constant_factor_le_sixty`) and calls `divisor_inequality : TheoremDivIneq`
(`…/TheoremDivIneq.lean:12`) [P]. That in turn calls
- `divisor_inequality_assembly : DivAssembly` (`…/DivAssembly.lean:11`) [P, read in full], which does the following:
  1. Termwise, pq_j·w·logΩ + phν − fa − nν·logΩ ≤ [ph(a_ρ) − a_ρ logΩ]·1_TT + eE + |pq_j − k||w||logΩ| + |δ||logΩ|. This
     uses nν = a·1_TT + k·w + δ, so the k·w·logΩ coming from the target cancels the one coming from the step.
  2. Sum over (j, ρ). The sum over j of the TT-indicator gives **m·Σ_t (ph(a_t) − a_t logΩ)**.
- `error_absorption`, which is bookkeeping.

**So the m copies come from summing the per-lift hypothesis hK_j ≤ Σ_ρ(phν_jρ − nν_jρ logΩ) + eK_j over the m lifts, where
each ν_j has the same top mass a_ρ at ρ ∈ TT.** [P]

### 1b. What the abstract numbers are (`RecNums`, `Formalism/LocalToGlobal/Divisibility/Inputs.lean:18`) [S]

`RecNums.divIneq` (`…/Divisibility/DivisionHeightBoundStatement.lean:131`) [P] instantiates `divIneqRecord` with:
- phν j ρ := Σ_i ph(ν j ρ i) and nν j ρ := Σ_i ν j ρ i, for a vector ν j ρ : Fin r → ℝ;
- fa := logH;
- hK := `RecNums.hB`, defined as Σ_ρ(Σ_i ph ν − (Σ_i ν)·logΩ) + Ch·f·N²(La + m³L);
- hP := `RecNums.hA` := −Σ_t a_t log T + (error).

`RecNums.ofNum` (`…/Divisibility/NumbersLink.lean:541`) [S] builds this record from `NumDatum` (`…/Divisibility/Numbers.lean`) [S]:
- `ν j ρ i = nuPad … = nu δ j z i = srcPar δ z i + eQ j z − (N(j−1) + N(j) − 1 − 2i)/2`. These are Harish-Chandra
  parameters (`hc z : HCParam`, with fields u, v, b, e), shifted by the j-th lift's e-parameter `eQ j z = (hc z).e(j−1)`
  and by a ρ-shift (n−1−2i)/2.
- `w j z = eQ j z`, the j-th lift's weight at place z ∈ RPl = Bool × A (the two CM embeddings over each element of H).
- `aT t = (hc (false,t)).u 0 − (k−1)/2`, the **top** Harish-Chandra parameter. `SizeData₂.top_u` ties it to the
  `aT ∈ [a, a(1+…)]` of `core_gm`.
- `logHook j z = log hookProd(apDiag j z)`, the hook-length product of a Young diagram built from the parameters.
- `logOm = γ + log(π/v) − L'/L(1, χ_d)` with χ_d = (·/d) (`NumDatum.logOm`, `SizeData₂.logOm`) [S].

Important caveat [P]. In `ofNum`, the residuals are **defined** as differences, so the record fields
`weight_height_sum_le` (`unfold eEN; linarith`) and `weight_sum_eq` (`unfold dN; ring`) are tautologies:
```lean
eEN δ j ρ := (∑ i, ph (nuPad δ j ρ i)) - logHook j ρ - (if ρ ∈ topsPl then ph (aTPl ρ) else 0)
dN  δ j ρ := (∑ i, nuPad δ j ρ i) - (if ρ ∈ topsPl then aTPl ρ else 0) - k * w j ρ
```
The real numerical content is the error bounds `sE` and `sδ`:
- eE ≤ C0(w + S + N² + m(t+1)η)La;
- |δ| ≤ C0(w + k(N+S) + …).

They are derived from `NumDatum.NumFacts` (`NumbersLink.lean:43`): window, interlacing (`inter`), block (`blk`) and
off/top conditions on the Harish-Chandra parameters. The proofs are at `NumbersLink.lean:120-535`, which I did not read.
`NumFacts` is a hypothesis (`H`) of `pkg_of_rowsK_alt`.

### 1c. Objects, and the classical analogue

`DivClauses P R u Nu sg` (`DivisionHeightBoundStatement.lean:553`) [S] is the real statement for one word u. The setting is
a CM number field K = `D.what₂.LL` (totally complex), Hermitian 𝓞_K-lattices `Nu ⊆ K^a` and `RR`, and a K-linear map
`B u = P.cols.col.B u : K^a → (K^D)^∨`. The clauses are:
1. `∀ φ ∈ shiftLat Nu sg, B u φ ∈ dualLat RR`: B maps the lattice Nu, **twisted by the fractional ideal
   ∏_w 𝔭_w^{−⌊sg w⌋}**, into the dual lattice. This is integrality of B with "vanishing order" sg.
2. The archimedean bound: ‖B u‖²_v ≤ cu_v with mean log cu = hu − meanLog κ.
3. **DIV**: `muCC − meanLog κ + hu − 2·Fo ≤ rhs`.
4. `μ(shiftLat Nu sg) = μ(Nu) + 2Σ_w lw(w)·⌊sg w⌋`. The degree of the divisor adds to the slope.

`Formalism.HN.SlopeIneq` (`Formalism/HarderNarasimhan/Statement.lean:91`) [S] is literally Bost's slope inequality:
```lean
∀ (φ : L →ₗ[R] M) (C : ℝ), 0 < C → (∀ x, ‖ρ' (φ x)‖ ≤ C * ‖ρ x‖) →
  (φ ≠ 0 → muMin ρ L - log C ≤ muMin ρ' (range φ) ∧ muMin ρ L ≤ muMax ρ' M + log C) ∧ …
```
**Classical reading** [N, from the S clauses]. This is the Arakelov/Bost slope method, which is the Hermitian-lattice
version of "a nonzero section that vanishes to order sg cannot have deg(sg) exceeding the degree". Clauses 1 and 4 give
μ(Nu) + deg(sg) ≤ μ_max(RR^∨) + h(B). Clauses 2 and 3 and `DIV` bound the right-hand side by MAIN. It is not a Siegel-lemma
construction (I saw no auxiliary-polynomial existence step), and it is not a comparison of heights of points. The
vanishing is not proved here. It is imported as `val2` (Q2).

The **`DIV`** predicate of `core_gm` (`Formalism/RankGapBounds/MeanBoundSecondForm.lean:118`) [S] is the same inequality
written in `Data` fields. It is supplied by `LinkDIV_at`'s clause (`Formalism/SharpRestriction/GlobalTheoremInputs.lean:77`) [S]:
```lean
(∀ u, D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u + C * TT.card * a * La + C * m * (B0 + Nc) * x ^ (Cabs * eps))
```
where `MAIN u = Σ_t (m·(phF a_t − a_t logΩ) − a_t·log T(u))` (`Formalism/LocalRingCardinality/DataParams₂.lean:232`) [S].

## Q2. Proof outline: what produces the divisibility, and what produces the "degree"

The chain that consumes `divIneqRecord` [S/P as marked]:
```
divisor_inequality_explicit (real arithmetic)                                   [P]
 ← RecNums.divIneq (instantiation)                                              [P]
 ← divClauses_of : DivInputs → DivClauses   (DivisionHeightBoundStatement:752)  [P]
 ← division_height_bound_statement (:991)  (DivInputs is a HYPOTHESIS)          [S]
 ← DivisionPackageColumns.ofTied / DivisionPackageFace.ofOpen                   [S]
 ← pkg_of_rowsK_alt (…/ThirdPlaceSeries/DIVRecBridgeSel.lean:113)               [S, P skeleton]
     hypotheses: NumFacts H, hOpen (gives DivInputs0R, ChainTie, FirstCols), hh : h u = hExpl6 …, hF …
 ← DivisionKernelConstantBounds.pkg / adm2  ← TopShapeAlt hypotheses
     (shape_closed_link_n_of_green, …/ThirdPlaceSeries/TopShape.lean:33; wire_sel_alt, WireSel.lean:20;
      wire4F_alt, Wire4F.lean:26)                                               [S]
 → linkDIVt_of_bridge_kernel → LinkDIVt (LinkEta → DIVinN → LinkDIV) → ChainTied → core_gm
```

### Level 1: `divClauses_of` [P, read in full]

- **Clause 1, integrality**: `P.cols.intoDual divIntoDualShift latticeGlue … I.val2`. Here `val2` is a field of `DivInputs`
  (`Inputs.lean:469`):
  ```lean
  val2 : ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt (P.cols.μ w), Dc.Pt u (P.cols.μ w) φ F = 0 ∨ sg w ≤ vw w (Dc.Pt u (P.cols.μ w) φ F)
  ```
  The **pairing Pt (a period column) of the lattice against the integral forms has w-adic valuation ≥ sg(w)**.
- **Clause 2, archimedean**: `height_chain_at` (`:691`, the pointwise version of `height_chain`, `:641`) [S, P for
  `height_chain`]. B factors through a `ColChain` of m matrices K_0,…,K_{mm−1} followed by PtL. Then htMap(B) ≤ hP +
  Σ_j (mean_v hK_j v) − Σ_j l6_j − meanLog κ. This is proved via `complex_height_cast` (`HeightRecord`,
  `ScalarLiftLowerBoundFull.lean:20`) [S]: the height of a composite is at most the sum of the operator-norm heights, minus
  the log-eigenvalues λ of a scalar action on the target. The per-step bounds come from `nK_of_cb I.cb` with
  `I.nKcb : log(cb.sq j v) ≤ Σ_{l↦j} hn.sz l v`.
- **Clause 3, DIV**: `P.base.boundsMu Formalism.DivisorInequality.boundsMu …` bounds the base dual slope. `passage` moves
  it to the column side. `I.L3main` bounds Σ_j l3_j by Σ_j Σ_ρ pq_j·w_jρ·logΩ + El3. `R.divIneq` closes the argument.
- **Clause 4**: `shiftMu`, the slope of the ideal-twisted lattice.

### Level 2: the "vanishing" side (what produces divisibility of order sg at w)

- `sg = sgRec L u w = ⌊ramIdx(w)·L.sg u w⌋` with `L.sg u w = Σ_j (gainD j w + F j w − E u j w)`
  (`DataParams₂.lean:215`, `Divisibility/RecBridge.lean:387`) [S]. So the divisor is **a sum over the m lifts** of:
  - the local gain_j(w);
  - a "type" term F_j(w), with `FInert` = (k−1)·Σ_z w_j(z)·p/(p²−1)-type expressions (`Numbers.lean:163-200`);
  - minus the excess E_{u,j}(w).

  The excess at twisted places is controlled by `LinkN`/`DIVinN`. Those bound etaSum, which comes from the local lengths
  etaJ(j, w), by Ш¹-lengths plus O(f·m·b·x^{2ε}) [S, `GlobalTheoremInputs.lean:44-62`].
- `val2` comes from `ServJointF.val2AllAtRF` (`Formalism/LocalToGlobal/GroupLattices/ServJointF.lean:84`) [P]. That is
  span-induction bookkeeping around `LocalQuadraticParts.adm2`
  (`Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean:206`) [S]:
  ```lean
  def adm2 D L := ∀ u w φ, φ ∈ L.NuLat u → ∀ F ∈ Mtilde (muAt w), F ∈ V0 (muAt w) →
    ∃ y, embLL y = D.what₂.perCol u (muAt w) (D.jN u φ) F ∧ (y = 0 ∨ ⌊ur D w (L.sg u w)⌋ ≤ vAdd (plEq w) y)
  ```
  This is the integrality of a **period pairing `perCol`** between a lattice vector of the u-th member and integral
  forms. Its value lies in K, and its valuation is ≥ the divisor.
- `adm2` comes from `Adm2InU` → `admissible_family_of_inclusion`
  (`Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean:315`), using `admissible_level_two` (`:214`)
  [P skeleton]. It splits places three ways:
  1. **Off the twist and generator primes** (`admissible_off_twist_places`, `:171`) [P]. The source is
     `WeilJacquetShalikaLaw.Conclusion1` (`Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97`) [S]:
     ```lean
     … ∀ x, InNP X Y K c u w x → ColGe T u μ w x (totS X K Xe ce sp u w)
     totS … u w = (∑ j ∈ lifts, (gainS X K (resChar w) j + L.F j w - ES … u j w)) + sp * vDG D u w
     ```
     **The column of the chain at w lies in the w-adic lattice scaled by totS, which includes Σ_j gain_j.** This is
     combined with the bounded-denominator integrality of the periods (`PeriodClassSumWeyl`, `TwistedPeriodAdmissible`,
     `Formalism/SharpRestriction/Divisibility/WeightDegreeSizes.lean:723`; valuation ≥ −ur(vDG), where vDG = v_p(DGam)).
     `GainLe` (`gainLe_of_fills`) ties `L.gain` to the formula `gainP`.
  2. At the twist prime T: `admissible_at_twist_places` [N].
  3. At the generator primes g0, g1: `admissible_at_generator_places` [N].

  `Conclusion1` reaches this point through the `Serv` structure (`hS.2.1`). `Adm2InU`'s fields `pt0`, `ptTw`, `per0`,
  `perTw`, `p10`, `atG` and `serv` are hypotheses of `closed_family_admissible_twist_link_alt`
  (`…/ThirdPlaceSeries/ClosedFamilyAdmissibleTwistLink.lean:12`) [S]. They are passed in from the `TopShapeAlt` bundle.
  **I did not find where `Conclusion1` is proved.** This is the single most important unread statement: it is the
  "vanishing to order Σ_j gain_j(p)" for the composite of the m theta-lift steps.

### Level 2: the "degree" side (upper bounds)

- **Per-step archimedean size** [S]. `CBHyp` (`Formalism/ThetaSupremumBounds/StatementCB.lean:148`) decomposes each step
  K_j at each infinite place into blocks: weights γ ∈ (0,1], unimodular phases ε, and block operators T with
  ‖T‖² ≤ tmax_j(v). Then ‖K_j‖² ≤ cbSq = |AA_j|·|AA_{j+1}|·hcl·hcl'·tmax. `nKcb` bounds
  log cbSq ≤ `liftedMapLogSize` (`DivIneqExplicit6.lean:15`) = Σ_τ[Σ_i ph(ν_jτi) − (Σ_i ν_jτi)·logΩ_τ(s)] + lower-order
  terms. So **the log-norm of the j-th lift operator is Σ log Γ(ν) − ν·logΩ**. I read this as Gamma factors of archimedean
  local integrals, normalized by a CM period [N]. The subtracted `hX`/`l6`, through the eigenvalue sum `eig6`, is where
  `logHook` (hook lengths, i.e. a dimension count) enters.
- **Target dual slope** [S]. `Formalism.DivisorInequality.boundsMu := slope_bounds`
  (`Formalism/DivisorInequality/BaseLevelBoundsWithCovolume.lean`, statement in `StatementObj.lean:17`) is a theorem in
  the archive. It is a covolume computation:
  ```lean
  muDef (dual R) ≤ meanLog κ + Σ_j lcv (XW j) (M j) / D + 2 Σ_j Σ_{y∈Tw} lw y·Fy y j + LG + Σ_j (E1 j + E2 j) + E3
  ```
  It holds under the determinant factorization `detRatio (XQ μ0) XE ι v = κ v^D · ∏_j detRatio (XT j μ0) (XW j) (θ j μ0) v`
  and local index conditions. So the target's covolume **factorizes over the m lifts j**. The covolume of each lift
  lattice M_j is then bounded by `L3main`/`adm3` (`LocalQuadraticParts.lean`, after `:228`) [S]:
  lcv(M_j)/D0 ≤ Σ_ρ (sigW…)·wSz·logΩ + …. **This is the Chowla–Selberg-type "degree"**: weights times
  logΩ = γ + log(π/v) − L'/L(1, χ_d).
- `height_bound_at_set` (`Formalism/DivisorInequality/DivisorInequalityProofs/EvenDegreeWeightBounds.lean:154`) and
  `stepDiiiRecord` give hPn ≤ hA = −Σ_t a_t log T + O(…). These are the final-pairing bounds. I did not read them.

**Summary of the mechanism.**
- Vanishing comes from a valuation statement for chain columns (`Conclusion1`), combined with bounded-denominator
  integrality of periods.
- It is not a length of a Galois-cohomology module. Ш enters only as an upper bound on the **excess** E (`LinkN`).
- The degree side is an archimedean Gamma-factor norm bound per step plus covolumes of the lift lattices (CM periods).
- It is not Hilbert–Samuel.

## Q3. Inert primes, odd exponents, and what a, w, k are

- **The prime sum** (`ASK`, `DedekindLFunctions/RunBaseDimensionLeRankAddGenusTerm.lean:105`) [S] is
  Σ_{p inert} 2 log p Σ_{odd i}(a/p^i − w(partner τ (frob p^i)))⁺ + log d·Σ_i(…). For inert p, χ_d(p^i) = (−1)^i, so
  2 log p·1_{i odd} = Λ(p^i)(1 − χ_d(p^i)). That is the von Mangoldt function of ζ(s)/L(s, χ_d) on inert primes [N, my
  gloss].
- **Why the shape (a/n − w)⁺.** `Deduction.ch_balance` (`DedekindLFunctions/LandauTheorems/ChBalance.lean:200`) [S, P first
  lines] proves the **identity** ASK − MAIN = De. It uses
  `Σ_{n≤N} Λ(n)·primVal ψ n·(a/n − w)⁺ = w·GPsi(ψ, a/w) + (a log a − a log w − (1+γ)a  or  −a·ell ψ)`. In other words,
  (a/n − w)⁺ = w·(y/n − 1)⁺ with y = a/w, which is the Riesz-smoothed explicit-formula sum G_χ(y). So the "Legendre"
  shape is chosen so that it is exactly G at the point y = a/w ≈ x.
- **On the divisor side** the same shape is the definition of the local gain
  (`Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean:247-358`) [S]:
  ```lean
  g0 X K a b p j t0 := (∑ s ∈ topsOn X p t0, ∑' e, if Odd e ∧ ¬ Excl D p s e then max 0 (al L a s / p^e - capU X b p j s e) else 0) - dl …
  gU … := gam p * ∑ s, al L a s - ∑ s (not V), ∑' e odd, min (al a s / p^e) (capU …) - dl …   -- gam p = p/(p²−1) = Σ_{odd e} p^{−e}
  gainP … p j := if (inert ∧ hP p = 0) ∨ X'' < p then 0 else Σ_{t0∈VV} max (gU − Pr) (max g0 0) + Σ_{t0∉VV} max g0 0
  capU X b p j s e := fill X b j (partner D p s e) − kaJ D j + cG L;   partner D p s e := (flip if signal ∧ e odd, s + e • hP p)
  ```
  `ParametersFill` (`IsResidueClassZero.lean:401`) [S] sets `L.gain j w = gainP …`, `L.wPart j t p e = fill X b j (partner D p t e)`
  and `fill … j z = wj D j τ` (the e-parameter of the j-th lift at place z). `LinkG_at` [S] then gives Σ_j gain_j(w) − τ(w) ≥
  Σ_j Σ_t (vonMangoldtClassSum_j(t, p) − loG) − m·flG, which is nearly a restatement given these ties.
- **Concretely**:
  - **a = a_t** is the top Harish-Chandra parameter at the top place (false, t), an integer in [a, a(1+…)] with a = x·b,
    b = e^{x^ε}.
  - **w = w_j(z)** is the j-th lift's e-parameter at the place z = partner(s, e). That place is obtained by translating the
    H-coordinate by e·Frob_p and flipping the CM conjugate when p is a "signal" prime and e is odd. On thick places
    w ∈ [b, b+η+1] (`win_thick`); on top places w ≈ b_t + b'/x; on thin places w ≈ w''.
  - **k = R.k** is a rank: the number of "u" entries of the Harish-Chandra parameter. It satisfies x·m ≤ k ≤ n²x^{1/2−ε}.
    The lift weights are pq_j = k + 2j − 1 − m.
  - **Odd e** arises from inertness: v_p of norms from an inert quadratic extension sees odd powers (Σ_{odd} p^{−e} =
    p/(p²−1) appears in gU, FInert and lpF). The divisibility by (a/p^e − w)⁺ per odd e is asserted by `Conclusion1`.
- **What it is not.** In what I read it is **not** literally the valuation of a factorial or binomial. `gainP` is a defined
  real number, and its arithmetic meaning (a column valuation) is the unread `Conclusion1`. My reading [N] is that
  ph(ν) = ν log ν − ν stands in for log Γ, MAIN is Stirling for Γ(a)Ω^{−a}, and the gains are a Legendre-type p-adic count,
  so the comparison is Chebyshev-type ("ChebyshevInequalityOnWindows" in the archive's own naming).

## Q4. Linear in the lifts, or genuinely interacting?

- **Additive in the lifts j** [P].
  - In `DivAssembly`, `height_chain` and `BoundsMu`, every lift-indexed quantity enters as a sum: Σ_j hK_j, Σ_j l3_j,
    Σ_j lcv(M_j), and sg = Σ_j(gain_j + F_j − E_j).
  - The lifts interact only through (a) composition of the chain, which only gives subadditivity of heights and no
    cancellation, and (b) the multiplicativity over j of the target's determinant (`detRatio … = κ^D ∏_j …`).
  - The single non-additive pairing is between the step's k·w_j·logΩ and the target's pq_j·w_j·logΩ. They cancel up to
    |pq_j − k| ≤ m.
- **Near-orthogonality is across words u, not lifts.**
  - `LinkS_at` (`GlobalTheoremInputs.lean:145`) [S] requires all of the following, with η0, η1, √e0 ≤ exp(−x^{ε/8})
    (`LinkS`, `:152`):
    - ‖K_D(u,u')‖²_HS ≤ (1+η0)·duS(u)·duS(u')/D* for u ≠ u';
    - ‖K_D(u,u) − id‖²_HS ≤ e0·duS(u);
    - Dall ≤ (1+η1)·D*.

    `hsSqD u u' = hsNormSq (KD D u u')` with `KD = Kmat D.s u u'`
    (`Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean:509-519`) [S].
  - `matSF_of` (`GlobalSchurBounds/TopDensityNGeSixteen.lean:862`) [P, read in full] and `matS_at_of` (`:821`) [P]
    repackage this as `MatS_at`. There, the normalized matrices `Ball u` of the B_u at one infinite place factor as
    `Bf u * Vr u`, with Vr an isometry, and the frame (Bf u)_u satisfies `InputSG`, a near-tight-frame condition.
  - `Frame_at` (`QuadraticLogDerivCongr.lean:188`) [S], used through `data_SlopeIneq` (`:699`), is the data-level
    `SlopeIneq`:
    ```lean
    sFrame Nu h − log |Words| − (1 − delp)⁻¹ (4 uF log(1 + HH/uF) + (η + 4√e) HH) ≤ RR.muDual
    sFrame Nu h := (Σ_u rank(Nu u)·(μ(Nu u) − h u)) / Σ_u rank(Nu u)
    ```
    This is a slope lower bound for RR^∨ from a near-isometric family of maps ⊕_u Nu_u → RR^∨: a Hadamard/determinant-type
    comparison with an entropy loss log|W| [N].
  - `LinkS` is supplied by `GlobalTheory.Top.link_alt_alt_bis`
    (`…/ThirdPlaceSeries/LinkAltAltBis.lean:16`) [S, header only] from `TheoremSSelected`, `CountAllPointsClass`,
    `WuDecayOfGap`, `TFrame` and `GenusMassVolumes.VolSigIndep`/`ClassItemsAt`. Point counting and genus-mass volumes
    suggest a Siegel–Weil/mass-formula input [N].

## Q5. The non-vanishing input

- **The divisor inequality itself has no non-vanishing.** In `divClauses_of`, the case `B u = 0` is handled by taking any
  `cu` (`exists_cu … Or.inl`), so clauses 2 and 3 hold trivially. `DivIneqRecord` is pure arithmetic and true for any
  inputs satisfying its hypotheses. [P]
- **The bite comes from the slope lower bound**, which needs the B_u to be jointly non-degenerate:
  - `Frame_at`/`MatS_at`: the stacked B_u form a near-isometric frame onto a space of dimension
    ≥ (1−δ)·rank RR (`(1 − delp)·|RR.ι ⊕ κ₁| ≤ |RR.ι|`, `InputSG` with η0, η1, e0 tiny, rank deficiency `de` with
    √de ≤ exp(−x^{ε/8})) [S].
  - `LinkDIV_at` adds the following [S]:
    - `OneMapIntoCC`: each B_u maps Nu_u into the lattice `cc` (`Formalism/LocalRingCardinality/DataArith.lean:180`);
    - `BesselId`: `Bu u φ F = a · besS u (U φ) (V F)` with **a ≠ 0** and U, V isometries;
    - `RRFull`, `BuRational`, `ZeroAbove`;
    - the height clause `∀ u, Bk u ≠ 0 → htMap … ≤ h u`.
  - `HHBound`/`FactHHcc` gives s − μ_min^∨ ≤ HH ≤ x^{cHH}·b.
- **What it rests on.** The near-orthogonality `LinkS` (Hilbert–Schmidt Gram estimates for Bessel/theta vectors across the
  words u) with exponentially small defects. Its provider uses "Theorem S" plus point counting plus genus-mass volumes
  [S names, N content]. I found **no** use of a lower bound for L(1, χ_d), the class number formula or the Rallis inner
  product as the non-vanishing input in what I read. L'/L(1, χ_d) appears only inside logΩ, where it cancels between the
  two sides except in MAIN, which `ch_balance` matches with `ell ψ`.
- **Why the comparison is not trivial for large m.**
  - The ASK lower bound for the gains (ASK − Ga ≤ LoP, via `LinkG` → `LossBounds`) grows like m·(prime sum).
  - MAIN grows like m·(a log a − a).
  - The per-lift costs B0 = f·m·b·x^ε also grow with m, so the total error is ≈ m²·b.
  - The one-off cost (a·La ≈ x·b·x^ε, from the final pairing hP and from TT) is shared, so per lift it is ≈ x·b/m.

  Hence the balance x/m ↔ m and the exponent 1/2. That is consistent with `core-gm.md`.

## Q6. Unread on this path

Proofs and statements I did not open:
- **`WeilJacquetShalikaLaw.Conclusion1`'s provider** (via `Serv`, `hServ : SelectionServed`) and
  `admissible_at_twist_places` / `admissible_at_generator_places` (`AdmissibleAtGeneratorPlaces.lean:92,134`). These are the
  actual "divisibility of the lift chain by gain_j(p)".
- `NumbersLink.lean:120-535`: the derivations of the `sE`/`sδ` bounds from `NumFacts`, and the source of `NumFacts`
  (`H u` in `pkg_of_rowsK_alt`).
- The providers of `DivInputs0R`:
  - `hn : HtNums`, `nKcb`, `cb : CBData` and `L3main`, via `DivInputsDef3.toDivInputs0R`
    (`Divisibility/TwistedPlaceEtaSumLeExtended.lean:247`) and `DivisionInputsWithoutNorm.ofRows`
    (`ConstantGeTwentyEightAlt.lean:37`);
  - `hOpen` in `wire4F_alt` (`…/ThirdPlaceSeries/Wire4F.lean:26`).
- `adm3` (the covolume of the lift lattices M_j in terms of logΩ) and its provider.
- `slope_bounds` (`DivisorInequalityProofs/BaseLevelBoundsWithCovolumeHolds`), `height_bound_at_set`,
  `stepDiiiRecord`, `complex_height_cast`.
- `MatK_at`, `InputSG` and the `LinkS` provider chain (`TheoremSSelected`, `CountAllPointsClass`, `VolSigIndep`).
- The rest of `ch_balance` (`askExp`, `sum_cut`, `inner_eq`) and `UpperTheory.N.at23_family_alt`
  (`…/ThirdPlaceSeries/At23OfAll.lean:19`, read as a one-liner calling `boundAtTwoThree_of_local_bounds_at_two_three`).
- `D7` itself: `what₂.perCol`, `thetaP`, `Mt`, `MtLat`, `hc : HCParam`, `div.Bk`, `div.RR`, `besS`. These are what the
  abstract records name.

## What to read next

1. **`Formalism.MainNotions.WeilJacquetShalikaLaw.Conclusion1`**
   (`Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97`) and whatever discharges the `Serv`/`SelectionServed`
   hypothesis feeding `admissible_level_two`
   (`Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean:214`). This is where "the m-step chain is divisible by
   p^{Σ_j gain_j(p)} at inert p" must be proved. Everything downstream is bookkeeping or classical.
2. **The per-step Gamma-size bound** `nKcb` / `CBHyp` (`Formalism/ThetaSupremumBounds/StatementCB.lean:148`,
   `DivIneqExplicit6.lean:15`) and its provider. Check that log‖K_j‖ ≤ Σ ph(ν) − ν logΩ really holds with the **full** top
   entry a_t in every step j. That is the source of the m copies of a log a − a.
3. **`adm3` / `L3main`** (`Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean`, after line 228) and `slope_bounds`.
   This is the target covolume via CM periods.
4. **`LinkS`** → `link_alt_alt_bis` (`…/ThirdPlaceSeries/LinkAltAltBis.lean:16`) → `TheoremSSelected` / `CountAllPointsClass`.
   This is the non-degeneracy that makes the slope lower bound bite.
5. **`NumbersLink.lean:120-535`** for the residual bounds `sE`, `sδ` from Harish-Chandra parameter windows (`NumFacts`).
