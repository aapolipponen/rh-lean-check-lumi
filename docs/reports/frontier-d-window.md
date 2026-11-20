# How the archive bounds the window Ш¹ lengths (`VWin`)

Date: 2026-11-20. This is a read-only source study of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled
or run. Paths are relative to `src/Development/AutomorphicArithmetic/AutomorphicVarieties/` (written `AV/`) unless
they start with `Development/`. Tags: **S** = I read the statement, **P** = I read the proof (term or tactic
skeleton), **N** = inferred from names only. About 70 ssh reads.

## Overview (for a number theorist)

`VWin` is proved by splitting Ш¹(G_{E,S}, ℚ_l/ℤ_l(−e')) into three pieces and bounding each by a different classical
method. The three pieces are l = 2, the complex-conjugation "minus" part for odd l, and the "plus" part for odd l
(`vvle_of_parts`).

1. **Minus part** (the eigenvalue of c is (−1)^{e'+1}; this is the L-value or Bernoulli side). It is bounded by an
   **Euler-system upper bound in Kolyvagin–Rubin style**. For l ∤ [E:ℚ], the ψ-part of Ш has length at most
   v_l(B_{e'+1,ψ}) (`PsiBound`). This is proved from a Poitou–Tate reciprocity law and Kolyvagin derivative classes
   built from Gauss/Jacobi sums. For l | [E:ℚ] a cruder bound comes from Stickelberger annihilation.
2. **Plus part** (the eigenvalue of c is (−1)^{e'}; this is the Vandiver side, with no L-value). The sum over **all**
   l is controlled at once by a **nonzero integer annihilator**. For each auxiliary prime p, a nonzero integer NN
   satisfies log|NN| ≤ poly(N·e')·log p, and length(Ш^+_ψ) ≤ 2·v_l(NN) for every l ≠ p. NN is a product of
   tr ρ(Frob_p) − (Ψ(Frob_p) + 1 + Ψ(Frob_p)^{−1}) over all cohomological U(3) Galois representations ρ of bounded
   level and weight, over an auxiliary imaginary quadratic field K = ℚ(√−p_K). The comparison "Selmer ≤ congruence
   depth" is a graded deformation-ring argument. It is a Ribet/Bellaïche–Chenevier lattice construction turned into an
   upper bound by an R = T statement at every point (`LemmaM`, `LemmaM'`, modularity). Kato's Euler system enters as
   unobstructedness input. GSp4 (cases II/III) and ℚ(i)-U(3) (case V) variants handle the finitely many l with
   l − 1 | 2e' or l in a fixed bad set. One small case is shown to be zero (`PropZ`).
3. **l = 2 and the fixed bad primes.** These are bounded by Iwasawa theory in the **cyclotomic ℤ_l-tower**. Ingredients:
   - μ = 0, from an in-archive proof of Ferrero–Washington via Sinnott's method, about 4.7k lines;
   - a uniform generator bound R for the Iwasawa module, uniform in the window primes q, d (this is where q ≡ 3 mod 8
     and d ≡ 7 mod 16 enter);
   - an l-adic "root avoidance" lemma (at most R exceptional twists e');
   - a **pigeonhole** over J ≈ 2^R·(…)^R scales [Y, Y²] to find a window free of exceptional twists;
   - `LemmaK`, a Soulé-type bound exp(poly) on H²(ℤ_l(e+1)), proved by group homology of GL_n(O_L) (34k lines), for
     the few small exceptional twists.

The target sqrt(exp(x^ε)) is far larger than any of these bounds. The polynomial bounds are polynomial in N, the
conductor, which contains q·d with log(qd) ≤ x^{ε/4}. No vanishing "for all but few (l, e')" is needed or proved
beyond the integer-annihilator statement. Behrend is not on this path.

## Q1. The statements

### Top assembly
`AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/WindowBoundOfLiteratureLevel.lean` **[P]**:
```lean
theorem vwin_of_hypotheses_H_E_alt (hH : HypothesesH') : VWin :=
  have hK := lemmaK_litN_alt hH.litN
  have hE := ends0_alt hH
  have h4 := countII_and_countIII_of_printsH_of_sp4In hH hK (sp4In0_alt hH)
  of_four_alt hH.litN hK (count_i_of_printed_bound_k_kato_automorphy hH hK (katoTwoW_of_printsH hH)
      (automorphyUnramified_of_litN_of_gdEnd hH.litN hE.1)) h4.1 h4.2 (count_v_of_printed_bound_k_reduced_unitary_lift hH hK hE.2)
```
`published_hypotheses_from_patching_alt` (`PublishedHypothesesFromPatching.lean`) **[P]** contains no patching. It
only fills the structure `HypothesesH'` with proved components: Clozel cohomology and conjugation, Borel injectivity,
GL2 Galois representations over totally real fields via base change, strong multiplicity one, Gelfand–Kazhdan,
newforms, descent, cyclic base change, and quaternion-algebra existence. The modularity-lifting content sits elsewhere,
in `automorphyUnramified_of_locPrints_kisin_gdEnd`, `ends_u_alt` and `unitary_three_automorphy_dense_of_prints`.

`HVCore.lean:18` `of_four_alt` **[P]**: `thmBab_of_lemmaK … FW.ferreroWashington hK` gives the Iwasawa/pigeonhole
bound `ThmBab`. Then
`vwin_of_counts … (hB 401) (Odd.thmBcFree_of (ML.iv pt uo)) h1 h2 h3 h5 (countZ X.propZ)`.

`HeightAndVanishing/JointWinOfCounts.lean` **[P]**:
```lean
theorem vwin_of_counts (hP : PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) (hK : LemmaK CK)
    (hB : ThmBab K 401) (hc : ThmBcFree) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) (hZ : CountZ) : VWin :=
  vwin_of_joint (jointWin_of_counts …) ((thmBc_iff _).2 hc)
```
Here `pointHV_of_counts := point (sumIn h2 h5 (countVs hP hF hT CK hK) countIV) (sumOut h1 hZ h2 h3)`. **CountIV and
CountVs are proved internally.** CountIV takes no hypotheses. CountVs needs Poitou–Tate, local finiteness, local
duality and LemmaK.

### The three-way split (`LengthEqAddEigen.lean`, `PrimeSetBoundDataOfPrimitiveChar.lean`) **[S]**
- `ShaPlus D e = Sha D e ⊓ (cAct D e).eigenspace ((-1)^e)` and `ShaMinus` (eigenvalue (−1)^{e+1}). Here c is complex
  conjugation of the CM field E. `vvle_of_parts` gives VVle(E, t, B₂·log 2 + B_m + B_p) from three inputs:
  `BoundedHeightTwoPlaceCondition` (l = 2, `VVat 2`), `VVminusLe` and `VVplusLe` (odd l, Σ_{l∈S} log l Σ_{e<t}).
- `ThmBcFree` (minus part): for every E = `IsCompField M e q d`, `VVminusLe E t (minusBound C deg [E:ℚ] condF t)`,
  where `minusBound = 3·n·t²·log(tN) + C·Σ_{l | o, l odd} l·n²·t²·log(t·l·N)²`. This is polynomial.
- `ThmHV` (plus part): `VVplusLe E (t x) ((condF E · t x)^C + C·exp(x^{4ε/5}))`, under `IsBWindow` and the size
  conditions q, d > 2X^{Ct} + 1 and q, d > (ψ.N, ord ψ, p_K, h(ℚ(√−p_K)), p_1, r₁, r₂).
- `ThmBab` (l = 2 and bad l): there is a Y with X^{1/J} ≤ Y, Y² ≤ X, such that for every x ∈ [Y, Y²] the l = 2 sum is
  at most exp(x^{4ε/5}). For each l ∈ `Bchi ψ` the same bound holds on the l-cyclotomic layer of ℚ(μ_{l·ψ.N}) at
  height log_l R + 3. J = 2^{R+2}(2·C_K·Ct/ε)^R.

### `LemmaK` (`GeneratorCountTuples/LemmaK.lean`) **[S]**
```lean
def LemmaK (CK : ℝ) : Prop := ∀ l L Ω (D : LData L Ω l), IsTotallyComplex L → HasMuQ l L → ∀ e ≥ 1,
  Finite (H2 (zlTw D (e+1))) ∧ Real.log (Nat.card (H2 (zlTw D (e+1)))) ≤ exp((2·e·[L:ℚ])^CK · log(2·|disc L|))
```
In words: H²(O_L[1/l], ℤ_l(e+1)) is finite, and its log-order is at most exp(poly(e·n)·log D). This is the shape of
Soulé's torsion bounds for K_{2e}(O_L).

### The counts (`HeightAndVanishing/Counts.lean`, `DirichletPrimeToLPartMulLPowerPart.lean`) **[S]**
Setting. `Host`: χ = ψ (a primitive character of conductor q_χ), ex = e, window primes q1 ≡ 3 (mod 8) and
d ≡ 7 (mod 16). N = lcm(2^{e+2}, q_χ)·q1·d. H ≤ (ℤ/N)^× is {a ≡ ±1 mod 2^{e+2}, χ(a) = 1, (a/q1) = (a/d) = 1}, so E is
the fixed field of H. `h.X c e` is the set of Dirichlet characters ψ mod N, trivial on H, with ψ(−1) = (−1)^e. These
are exactly the characters carrying the plus part. `Vlen Ω c e ψ = Chr.V' l N e (dirG ψ)` is the O-length of
Ш¹_{S={l·N}}(G_ℚ, (K/O)(ψ⁻¹χ_cyc^{−e})), the ψ-isotypic piece over ℚ. `VLe … B` means `Vlen ≠ ⊤ ∧ Vn·log l ≤ B`.
`Bchi ψ = {3} ∪ odd prime factors of ord(ψ)·ψ.N·p_K·h(ℚ(√−p_K))·p_1`, a finite set fixed by ψ. Here p_K is the least
prime ≡ 3 (mod 4), ≥ 7, coprime to ψ.N, and p_1 is an auxiliary prime ≡ 1 mod the odd part of ord ψ.
`Big t`: 2t+1 < q1, d, and q1, d exceed the constants above.

| count | covers (l odd, 0 < e' < t, ψ ∈ X) | bound |
|---|---|---|
| `CountI` | l ∉ Bchi and (l−1) ∤ 2e' (the generic case) | **Σ over any finite set Ls of such l**: Σ_l log l · Σ_ψ Vn ≤ (N·t)^C, and each length is finite. Constants C, r₁, r₂ depend only on χ. |
| `CountZ` | l ∉ Bchi, (l−1) ∣ 2e', ψ = 1 | per ψ: VLe (l·N·e)^C. Actually 0 (see Q3). |
| `CountII` | e' ≥ 2, chiP(l,ψ) of even order, and (l ∈ Bchi or (l−1) ∣ 2e') | per ψ: VLe (l·N·e')^C |
| `CountIII` | l ∉ Bchi, (l−1) ∣ 2e', ord ψ odd, ψ ≠ 1 | per ψ: VLe (l·N·e')^C |
| `CountV` | l ∈ Bchi, e' = 1, R1(l,ψ) ≤ 2^{c2(ψ)} | per ψ: VLe (l·N·e')^C |
| (`CountVs`, internal) | l ∈ Bchi, e' = 1, R1 > 2^{c2} | proved from LemmaK + duality |
| (`CountIV`, internal) | l ∈ Bchi, e' ≥ 2, chiP of odd order | proved, no hypotheses |

So "regular versus irregular" plays no role. The split is by whether l − 1 divides 2e' (whether ω^{2e'} = 1) and
whether l lies in the fixed bad set Bchi. `CountShape` (cases II, III, V, Z) bounds each piece by (l·N·e')^C. Only
`CountI` bounds a sum over arbitrary sets of primes. Every other case has l ≤ 2t+1 or l ∈ Bchi, so only finitely
many l occur.

## Q2. Mechanisms, one or two levels down

### CountI: integer annihilator from U(3) congruences **[P at two levels, S below]**
- `LinkedUnlE.lean:49` `count_i_of_printed_bound_k_kato_automorphy` gives
  `U3.countI (U3.corGK (propGK_of_numberU3U_of_oneCharU (numberU3U_of_prints …) (oneCharU_of_katoTwoW_rig_admI_automorphy hC main_holds mprime_holds lemmaP hKa rigI rigII admI h3)))`.
- `HeightAndVanishing/CountI.lean` `countI : CorG → CountI` **[P]**. It applies `CorG` to the fixed imaginary quadratic
  field K = `Kstar (pK χ)` = ℚ(√−p_K), with two auxiliary primes r₁ < r₂ chosen after 30 + χ.N + p_K. It then absorbs
  constants: 4·c5·φ(index)·disc^5·N^{18}·e^7·(log r₁ + log r₂) ≤ (N·t)^{k+19}. The hypothesis `GD` is supplied by
  `gdOfHost` **[N]**: l odd, l ∤ ord ψ, ψ quadratic on the l-part, parity, K imaginary quadratic,
  l ∤ disc(K)·h(K), a disjointness condition η, and (l−1) ∤ 2e.
- `UnitaryThreeGroups/KatoUse.lean` **[S]**:
  ```lean
  def PropGK := ∀ K, ∃ c₅ A, ∀ e N H p, 1 ≤ e → p.Prime → ¬ p ∣ 30·N·disc K →
    ∃ NN : ℤ, NN ≠ 0 ∧ log|NN| ≤ c₅·φ([(ℤ/N)ˣ:H])·(N(e+1))^A·log p ∧
      ∀ l ≠ p, ∀ c, (∃ ψ ∈ orb c H, GD …) → (∀ ψ ∈ orb, Vlen ≠ ⊤) ∧ Σ_{ψ ∈ orb c H} Vn ≤ 2·v_l(NN)
  ```
  `CorGSumLog.lean` `corGK : PropGK → CorGK` **[P]** uses the elementary inequality Σ_l log l · v_l(NN) ≤ log|NN|
  (`corG_sum_log`). Two auxiliary primes p ≠ p' cover the case l = p. **This is the step that makes a bound over all
  primes l at once possible.**
- `OneCharU` (`…/WeightInfinitesimalCharacters/AdmissibleUnitaryThreePoint.lean:116`) **[S]**. Take σ ∈ G_K and
  t = Ψ(σ) + 1 + Ψ(σ)^{−1} with Ψ = χ_cyc^e·ψ. Assume no ρ : G_K → GL₃(Q̄_l) that is `Adm3U` (attached to a regular
  algebraic conjugate-self-dual cuspidal form on U(3)/GL₃ over K of level N and weight e) or `Adm2` (endoscopic 2+1)
  has tr ρ(σ) = t. Then Vlen < ⊤, and Vn ≤ 2·Σ_{ρ∈X} v_l(tr ρ(σ) − t) over a finite set X of pairwise non-isomorphic
  such ρ.
- Proof of `OneCharU` (`FOneCharU.lean`) **[P skeleton]**:
  - `exists_dat`, then `exists_ring`. S.R is a deformation ring (framed, universal: `LemmaP`/`IsUnivFramed`) of the
    residually reducible 3-dimensional representation with an η-grading.
  - `exists_model` gives a weighted graded presentation.
  - Every Q̄_l-point of S.R of "type I" is automorphic (`AdmI`, from `AutomorphyUnramifiedCoefficientsAlt`; this is the
    modularity / R = T input). Every "type II" point (2+1 reducible) is the extension of a modular GL2 representation
    (`adm2B_rhoK_of_typeII_of_modular_extensions`).
  - `model_upper` (LemmaM, using the rigidity results `RigidityFirstCase`/`SecondCase` and Kato) bounds the cotangent
    length in degree −1 by 2·Σ_{points ξ} v(ξ(a)), where a is the trace difference.
  - `vlen_le` (LemmaM') bounds Vlen by that cotangent length: the Selmer group injects into weight-graded point
    derivations.
- `LemmaM` and `LemmaM'` (`CommutativeAlgebra/OrbitVanishingLocal.lean:111,120`) **[S]** are pure commutative algebra
  about ℤ-graded complete O-algebras. The equations lie in degrees −1, −2, 1, 2, 0 (`Eqns`, `M1…M5`). Conclusion:
  `cotLen x 𝒜 (-1) F ≤ 2·Σ_{ξ∈T} v(ξ a)` for any finite covering set of points T. Proofs `Alg.M.main_holds`,
  `Alg.M.mprime_holds` and `Alg.lemmaP` are unread. The `CommutativeAlgebra/` directory has 127 files and 19.4k lines.
- `NumberU3U`/`CountKU` (`AdmissibleUnitaryThreePoint.lean:~85`) **[S]**: the eigen-systems of level M and weight ≤ H
  number at most c·(M(H+1))^A, and are classified. `numberU3U_of_prints` (`KeepNumU.lean`) **[P one line]** assembles
  this from level/newform lemmas. Bounding log|NN| by (number of ρ)·O(e·log p) presumably uses purity (Ramanujan) of
  `Adm3U` representations **[N]**. NN ≠ 0 needs tr ρ(Frob_p) ≠ t, which follows from weights (t has eigenvalues of
  absolute value p^e, 1, p^{−e}) **[N]**.
- **Mechanism in one sentence:** a Ribet-style congruence argument. A nonzero class in the plus part of Ш gives a
  non-split residually Eisenstein deformation of ψ ⊕ 1 ⊕ ψ^{−1}. By modularity of all points of the deformation ring,
  its size is at most the congruence depth between cuspidal U(3) forms and the Eisenstein system, measured at
  Frob_p. The approach is not Bloch–Kato via L-values and not a main conjecture. It is "Selmer ≤ congruence module",
  computed at one Frobenius.
- **Kato** (`KatoQuadraticCharacters/`, 200 files, 23.4k lines). `KatoTwoW` **[S]**: for a newform f of weight 2e+1
  attached to W ⊗ χ_cyc^{−e}, the Bloch–Kato Selmer groups of W and of W⊗θ vanish. `twoS` **[P]** derives it from
  `VanishOrdL`, which comes from `ZetaUr` (Kato zeta elements are an Euler system, `ES W A`). `Final.zetaUr` **[P one
  line]** uses `kato_eulerSystem_integrality`, `smoothedZetaClass_hodgeTateLaw` and Hecke-projection non-vanishing.
  So Kato's Euler system is formalised. Here it serves as the unobstructedness (smoothness) input for the type-II
  locus, not as the bound itself **[N for the role]**.
- **Row0b (`gal : RowT`)** enters in three places:
  1. `katoTwoW_of_printsH` uses `rowOf' P.litN.aut.gal` **[P]** (local–global compatibility for the GL2 representations
     in Kato);
  2. `linkedUnlE_alt` and `unitary_three_automorphy_dense_of_prints` **[N]** attach ρ to U(3) forms (the `Adm3U`
     representations whose traces form NN);
  3. `modularity_unitary_of_automorphy_hida_unitary` (`modU_of_printsH`) **[S one line]**.

  So the automorphic-to-arithmetic step is the pair `OneCharU` (Selmer ≤ Σ v(tr ρ(σ) − t)) plus `AdmI`/`AutBAlt` (all
  type-I points of the deformation ring are automorphic).

### CountII / CountIII: the same mechanism with GSp4 **[S]**
`AdjointLiftingOfCohomology.lean` `countII_and_countIII_of_printsH_of_sp4In` gives
`Th.sp4Main_alt hS coh main_holds mprime_holds lemmaP numberSp4 rigSp4 (corX lemmaX residual_bernoulli_nonvanishing) (soBar, soFin)`.
The inputs:
- `SymplecticFourImageDense` (`sp4In_alt`, which uses FW, `seedIIs`, `fourth_initial`, `pmEx`);
- `NumberSp4Alt` (counting GSp4 forms);
- rigidity;
- `CorX` (Bernoulli units give trivial unramified cocycles).

Per ψ the bound is (l·N·e')^C, or the explicit `leSqrtOfDivSqGeOne` shape in the unused `ColumnFamilyStandardVectorsBasis`.

### CountV: U(3) over ℚ(i) **[S]**
`CountVOf.lean` `countV_of_finiteness_duality_euler_host` takes:
- `ThmS6_s` (automorphy, from `unitary_lift_of_reduced_core`);
- LemmaM and LemmaM';
- local and global finiteness, local and global Euler characteristic, Poitou–Tate;
- `HostVanE`, from LemmaK;
- `HostXpp`, from `residual_bernoulli_nonvanishing`;
- host rigidity and a host form count.

The proof picks K with `gaussian_field_range_eq_ker_quartic_char`, i.e. ℚ(i) and the quartic character, and builds a
universal ring (`exists_isUniv`). The mechanism matches CountI.

### CountZ (`HeightAndVanishing/CountZ.lean`, `LevelCohomology/PropZ.lean`) **[P]**
`PropZ`: for l ≥ 5, e even ≥ 2 and (l−1) | 2e, `Chr.V l e 1 = 0`. Proof: if (l−1) | e, use `zOne` (the twist is
trivial mod l). Otherwise use `zQuad` (the twist is the quadratic character of ℚ(√±l)) **[N for zOne/zQuad]**.
`countZ` turns this into length 0.

### Minus part (`OddResidueBounds/ThmBcOfPsiBound.lean`, 297 lines) **[S, P skeleton]**
`thmBcFree_of h := thmBc_of deg stickBound (primeBound_of h)`.
- `PsiBound` (`OddResidueBounds/ZeroMemUnrHom.lean:97`) **[S]**: for E abelian CM, l odd, l ∤ [E:ℚ], ψ a character of
  Gal(E/ℚ) with ψ(−1) = (−1)^{e+1}, the length of the ψ-part of Ш¹(ℚ_l/ℤ_l(−e)) is at most
  v(`alN (e+1) ψ`) = v(den·B_{e+1,ψ}). This is the upper-bound half of the cyclotomic main conjecture with Tate
  twists. Classically it comes from Mazur–Wiles, or from Kolyvagin–Rubin with Euler systems.
- `ML.iv : PoitouTateDuality → UnramifiedOrthogonality → PsiBound := psiOf (recip h₁ h₂)` **[P]**.
  - `Rec` (`PrimitiveFrobeniusFixed/IsAdmissiblePrimeListNil.lean:141`) **[S]** is a global reciprocity law: a class c
    unramified outside Nq and locally trivial at N, paired with a dual class n ramified at q, gives local pairing 0
    at q.
  - `psiOf` (`PsiOf.lean`, 64 lines) **[P]** reduces to `Chr.eigV` and the `PrimCase` (`prim_case`, `lev_case`,
    `vChar`).
  - The directory `PrimitiveFrobeniusFixed/` (7,350 lines) contains `KolStep`, `KolHom`, `KolUnr` (Kolyvagin
    derivatives `der τ L u`), `GenBUnits` and `XCongJac` (Jacobi-sum congruences), and `ValuationKummerElement…`.
  - So this is a **formalised Kolyvagin–Rubin Euler-system argument with Gauss/Jacobi-sum (Stickelberger) Euler
    systems** **[N/P skeleton]**. The main conjecture is **not** stated as such. The 5 modules with "MainConj" in a
    declaration name were not examined.
- `StickBound` covers l | [E:ℚ] **[S]**: minusLen·log l ≤ C·l·n²·(e+1)·log(e·l·N)². It comes from l^r-annihilation of
  ShaMinus (Stickelberger, `killPow`) and an H¹[l] bound (`gen`).

## Q3. How the total is made finite and small

- Sum over l. **There is no "all but few (l, e') vanish" lemma.** Two mechanisms replace it:
  1. **Minus part:** Σ_l log l · length ≤ Σ_ψ log|B_{e+1,ψ}·den| (`PrimeBound`, `prodVal`, `hV` in `prime_of`).
     The ψ-parts vanish at l ∤ B_{e+1,ψ}, and log|B| is polynomial in N and e.
  2. **Plus part, generic l (CountI):** Σ_l log l · length ≤ 2·log|NN| + 2·log|NN'|, polynomial in N·t. Lengths are 0
     for l ∤ NN·NN'.

  The only exact vanishing statement is `PropZ` (ψ = 1, e even, (l−1) | 2e). Every other piece is bounded, not killed.
- Sum over e' < t = ⌊x^{401}⌋. This multiplies by t, which stays polynomial in x.
- Size. N ≈ 2^e·q_χ·q1·d with log(q1·d) ≤ X^{ε/(4J)} ≤ x^{ε/4}. So (N·t)^C ≤ exp(C·x^{ε/4} + O(log x)). The l = 2
  part and the bad-prime part are at most exp(x^{4ε/5}). The final comparison with sqrt(exp(x^ε)) =
  exp(x^ε/2) happens in `thmHV`, `jointWin_of` and `vwin_of_joint` **[S]**.
- **"Weakened Vandiver."** The archive has no declaration named Vandiver, Lichtenbaum or Leopoldt (decl-index hits:
  0). The functional replacement is `PropGK`/`CorG`/`CountI`:

  > For every e ≥ 1 and every orbit of even-parity characters ψ (relative to e) of conductor N, there is a nonzero
  > integer NN with log|NN| ≤ c·(N(e+1))^A·log p such that the ψ-plus-part of Ш¹(ℚ, ℚ_l/ℤ_l(ψ⁻¹)(−e)) has length
  > ≤ 2v_l(NN) for all l ∉ Bchi with (l−1) ∤ 2e.

  This bounds the size of the Vandiver-type eigenspaces. It does not prove they vanish.
- **K-groups.** The decl-index hits for "KGroup" are compact open subgroups. "Quillen" has 3 modules (not read). Algebraic
  K-theory does appear on this path in **`LemmaK`**: `lemmaK hB pt lfK ltK` with `BOdd` (rank of the image of
  H_{k+1}(GL_n(O_L)) ≤ r₂, Borel). `bOdd_zk` comes from `LiteratureResults/KTheoryStability/` (286 files, 34,368 lines:
  `HomologicalStability`, `ReductionBoundsTorsion`, `FinitelyGeneratedTorsion`) **[S/N]**. That is a Soulé-type
  argument via reduction theory and homology of GL_n. No statement about K_n(ℤ) vanishing was found on this path.

## Q4. The window primes, the level and the field E

- **Shape of E** (`IsCompField`, `Host.H`) **[S]**: E is the compositum of the ψ-field, the 2-power cyclotomic layer
  (a ≡ ±1 mod 2^{e+2}, which has degree about 2^e), and two quadratic conditions (a/q1) = (a/d) = 1. These are
  quadratic subfields; q1 ≡ d ≡ 3 mod 4 gives ℚ(√−q1) and ℚ(√−d). So [E:ℚ] ≈ 2^{e+O(1)}·ord ψ, and the only odd primes
  dividing [E:ℚ] divide ord ψ (`thmBc_of` hypothesis `hD`). The "Iwasawa tower" is **the cyclotomic ℤ₂-tower over a
  base L₀ of conductor 4·m·q·d** (`TwoBase`, with layer m ≤ e+2), and for l ∈ Bchi the ℤ_l-tower over ℚ(μ_{l·ψ.N}).
- **Residues** `q ≡ 3 (mod 8)`, `d ≡ 7 (mod 16)` (`PrimePair`) **[S]**: `towerTwo` (`QuadraticExtensions/IsAlgClosureRat.lean:87`)
  **[S]** gives R = 4(g + 6·deg M), **uniform in q and d**. It does this through `quadStep` for √−q and √−d, plus
  `abRk hFW` (FW). The residue conditions fix the 2-adic splitting and ramification so that each quadratic step adds a
  bounded rank, a Kida/Riemann–Hurwitz-type step **[N for quadStep's content; not read]**. Uniform R makes the
  pigeonhole constant J independent of the window.
- **Level 2^e ≈ x^{2+8ε}**: the bound in `ABound` is shaInv(L_m, e') ≤ R'·(max(m, j₀) + c + B), linear in the layer
  m ≈ e. B is the l-adic closeness of e' to one of ≤ R roots s_i (the Iwasawa characteristic-polynomial zeros) **[S]**.
  For e' ≤ Z, at most one e' per root has B > log_l Z (`FirstBound`, `Exc.card ≤ R`). The pigeonhole picks a scale
  [Y, Y²] in which every exceptional e' is ≤ x^{ε/(2C_K)}. Those few are bounded crudely by LemmaK
  (exp(poly(e'·n)·log D) ≤ exp(x^{4ε/5})) (`ThmBabOf.lean`, `partA`/`partB`, `Good`) **[P skeleton]**. This is the
  "pigeonhole on F_{q^n}/F_q" analogy: twists play the role of field extensions, Iwasawa roots play the role of
  Frobenius eigenvalues.
- **Behrend**: 14 modules (`Formalism.BehrendSets.*`). **None is statically reachable.** No Behrend import appears on
  the files read here. Behrend is **not used on this path**, as far as static reachability shows.

## Q5. Sanity of strength (conjecture-shaped inputs)

| statement | classical status | where proved | size / shape |
|---|---|---|---|
| `Published.FerreroWashington`: bounded l-rank of class groups in the ℤ_l-cyclotomic tower of abelian K ∋ μ_l (μ_4) | theorem (Ferrero–Washington 1979; Sinnott 1984) | `GaloisLibrary/FerreroWashingtonIndex/` | 62 files, 4,672 lines. Stickelberger half-system θ (`thetaH`), ambiguous classes (`ambCyc`), `memZ` ((γ−1)^N ∈ (θ, 1+J, l)), `nonvan` from `sinnott` (`Sinnott.lean` + 5 helpers, about 280 lines; pairwise ℚ-independence of units, l-adic separation). Short for FW but follows Sinnott's algebraic route; worth expert reading. |
| `PsiBound` (main-conjecture upper bound, minus part with twists) | theorem (Mazur–Wiles; Kolyvagin–Rubin) | `PrimitiveFrobeniusFixed/` (7,350 lines) from `Rec` (Poitou–Tate reciprocity) | Kolyvagin derivative classes of Gauss/Jacobi-sum units. Classical route. |
| `LemmaK`: exponential bound on #H²(ℤ_l(e+1)) | theorem-shaped (Soulé) | `ClassCounting/LemmaKOfSteps` + `KTheoryStability/` (34k lines) | group homology of GL_n(O_L), stability, reduction bounds |
| `KatoTwoW`: BK Selmer vanishing for weight 2e+1 newform twists | theorem (Kato 2004) when the L-value is non-zero | `KatoQuadraticCharacters/` (23.4k lines) | zeta elements, Euler system integrality |
| `AutomorphyUnramifiedCoefficientsAlt`, `ThmS6`, `SymplecticFourImageDense`: modularity of all type-I points of 3-dim (or GSp4) residually Eisenstein deformation rings | known only in special cases (residually reducible modularity lifting: Skinner–Wiles, Thorne, Allen–Newton–Thorne). **This is the strongest-looking input.** | `automorphyUnramified_of_locPrints_kisin_gdEnd` with `GdEndAlt` from `ends_u_alt (linkedUnlE_holds_alt … (seed2_alt) (unitary_three_automorphy_dense_of_prints))` | **unread**. Proof chain names: Kisin, seeds, linked unramified ends, density. |
| `LemmaM`/`LemmaM'` (cotangent length ≤ Σ point valuations for graded rings) | new commutative algebra, no direct classical analogue | `CommutativeAlgebra/` (19.4k lines) | unread |
| `PropGK` (bound on Vandiver-type eigenspaces by an integer) | **not known classically** in this generality. Classical knowledge bounds plus parts only crudely, e.g. via class number formulas. | assembled from the rows above | this is where the strand's novelty sits |

No structure field encodes Vandiver, Greenberg, Leopoldt or Gross–Kuz'min. FW appears as a `Prop` hypothesis but is
discharged by the in-archive proof `FW.ferreroWashington` (`FerreroWashington.lean:104`) **[P]**. The "Published"
bundles (`LitCoh`, `LitLocAlt`, …) are filled by theorems (`…_of_open O`) in `TemperedProductOfSquareIntegrable.lean`.
`OpenImageCondition` has one field, `RowT`.

## Q6. Unread on this path

- Modularity of type-I/II points: `UpperTheory.V.Pr.automorphyUnramified_of_locPrints_kisin_gdEnd`,
  `UpperTheory.V.Z.Win.Dn.ends_u_alt`, `UpperTheory.V.Z.J.linkedUnlE_holds_alt`,
  `UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints`, `UpperTheory.V.Z.Win.Birth.seed2_alt`,
  `UpperTheory.V.UnitaryThreeInertia.unitary_lift_of_reduced_core`, `UpperTheory.V.Cu.sp4In_alt`.
- Deformation-ring construction and commutative algebra: `exists_dat`, `exists_ring`, `exists_model`,
  `model_upper`, `vlen_le` (`TheoremsMuLinked/GaloisRepresentationTypes/OneChar.lean` and around);
  `Alg.M.main_holds` (`CommutativeAlgebra/GradedModulesLength/MainCotSpan.lean`), `Alg.M.mprime_holds`
  (`…/Mprime.lean`), `Alg.lemmaP` (`CommutativeAlgebra/LemmaP.lean`).
- Rigidity: `UpperTheory.V.Z.J.rigIUE_alt`, `UpperTheory.V.Z.Win.RR.rigII_a_alt`, `UpperTheory.V.Th.adjoint_lifting_of_cohomology`, `rigSp4_alt`.
- Counting: `numberU3U_of_adm2A_imp_adm2B`, `CongruenceNumberUnitaryThree`, `numberSp4_n_alt`, and where NN ≠ 0 and the log|NN| bound are proved.
- `UpperTheory.V.Th.sp4Main_alt` body (`ConductorAtMapInjectiveCoeff.lean:131`), `main_big`.
- Minus part: `prim_case`, `lev_case`, `vChar` (`PrimitiveFrobeniusFixed/PrimCase.lean`), `ML.recip` (`OverIff.lean:297`), `kolStep`, `stickBound` components.
- Tower: `partA`, `partB`, `PropA.aBound_of_isTower` (`AdditiveValuationNorms/ABoundOfIsTower.lean`), `quadStep`, `baseRk`, `abRk`.
- `FW.sinnott` helpers (`SinSupp`, `SepPair`, `SinFin`, `SinMap`, `SinLem`), `FW.struct`, `FW.algK`.
- `lemmaK_of_steps`, `KTheoryStability/*`, `bStarOdd`.
- `X.zOne`, `X.zQuad`, `gdOfHost`, `countIV`, `countVs`, `sumIn`, `sumOut`, `thmHV`, `vwin_of_joint`.

## What to read next

1. **The modularity input for residually Eisenstein U(3) deformations.** This is the strongest claim on this strand.
   - `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/CohInp.lean`, theorem `automorphyUnramified_of_litN_of_gdEnd`
   - `UpperTheory.V.Pr.automorphyUnramified_of_locPrints_kisin_gdEnd` and `UpperTheory.V.Pr.GdEndAlt`
   - `UpperTheory.V.Z.Win.Dn.ends_u_alt` (`DnEndsTop.lean` and its callee)
2. **`LemmaM`/`LemmaM'` and their proofs** (`AV/CommutativeAlgebra/OrbitVanishingLocal.lean:111-130`,
   `GradedModulesLength/MainCotSpan.lean`, `Mprime.lean`). This is the numerical criterion "Selmer ≤ congruence depth".
3. **`FOneCharU.lean` helpers** `model_upper`, `vlen_le`, `twoPt_shape` (`AV/TheoremsMuLinked/GaloisRepresentationTypes/OneChar.lean`).
4. **FW via Sinnott** (`AV/GaloisLibrary/FerreroWashingtonIndex/Sinnott.lean`, `SinLem.lean`, `SepPair.lean`, `Nonvan.lean`):
   check against Sinnott 1984 / Washington §16.
5. **Uniform tower rank** (`AV/QuadraticExtensions/QuadStep.lean`, `IsAlgClosureRat.lean:60-96`), and `partA`/`partB` in
   `AV/LayeredIsomorphisms/`.
6. **Minus part**: `AV/PrimitiveFrobeniusFixed/PrimCase.lean`, `KolStep.lean`, `OverIff.lean:297`.
