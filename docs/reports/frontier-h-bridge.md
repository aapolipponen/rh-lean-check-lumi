# Frontier H: the bridge from the global lift chain to power series on the formal group

Date: 2026-11-21. Read-only study of `/bulk/shared/rieman/lean/src` on chili, using `ssh` with `sed`, `grep`, `cat` and
`analysis/reach/decl-index.tsv`. Nothing was compiled or run. Paths are relative to `src/`. This report continues
`frontier-f-divisibility.md` (its Task 5 list is the target list here). About 65 tool calls.

Tags:
- **[S]** means read in the statement or definition.
- **[P]** means the proof was read in full.
- **[P-skel]** means the `have`/`obtain`/`refine` skeleton of the proof was read.
- **[N]** means inferred from names or from the shape of a statement.

## Overview (for a number theorist)

The bridge is **Katz-style, and it is a theorem in the archive, but its last link is definitional.** Here is what the
archive does:
- **The CM point.** It fixes the CM elliptic curve ℂ/δ·𝔠 (𝔠 an ideal of K = ℚ(√−d), δ¹² = Δ(𝔠), so the lattice has
  unit discriminant).
- **The kernel is a classical theta function on a CM abelian variety.** Each lift kernel is a holomorphic theta function
  on the torus Hom(ℂ^N, ℂ^N′) ⊗ ℂ^Τ modulo (Hom-lattice) ⊗ δ𝔠, which is a CM abelian variety isogenous to a power of that
  curve. The theta function is built from a basic theta by isogeny averaging, a Hecke character χ, and a lattice model of
  the finite Weil representation (`thC`/`xiL`) at a finite set SS of places.
- **Taylor expansion and transport to the formal group.** The theta function is Taylor-expanded at z = 0. Its
  coefficients are algebraic, so they are sent into ℂ_p by λ : Q̄ → ℂ_p (`pSer`). The variable is then substituted as
  z = log_W(t), where log_W is the formal logarithm of an integral Weierstrass model (`atLog`).
- **Integrality.** The archive proves that theta·∏ σ(t_i)⁻¹ is p-integral (`IntInert`). It does so by reducing, through
  pull-backs, Hecke moves and tensor products, to a 2×2 basic theta function.
- **From log_W to the Lubin–Tate logarithm.** The CM curve's formal group is identified with the height-2 Lubin–Tate
  group (`LTIso`, `CM3`). Then `CurveDict` rewrites the kernel as exp(−Σβ(x_e, y_e))·U, with U integral. Here β is the
  biadditive defect of −log(σ(ε·log t)/t), i.e. of a p-adic σ-function.

So "exp(−Σβ)·U" is **proved** of the actual theta function. It is not inserted by definition.

The other half of the bridge says that the **global chain step equals the finite sum over genus classes of a
differential operator applied at 0 to that theta function**. In the "true columns" family this holds **by
construction**. There, the chain's unfolding maps are *defined* as jet maps of the theta kernel (`TC.chIn`), and the
required identity `UnfIsAll` is proved by unfolding definitions (`objOf_unf`). I found no theorem in this part of the
archive that identifies this chain with an adelic theta integral. The complex-to-p-adic transport of the differential
operator (frames, units, adelic lattice-tuple decompositions) is a separate proved step whose main lemmas I did not
open.

The odd powers of p come from the σ-semilinearity of β under μ_{p²−1}. Because of it, β pairs x^{p^{2i}} with
y^{p·p^{2j}}, and in many variables hh couples the embedding index s with s+1 at the cost of a p-th power.

## Target 1. `first_kernel_small_of_frame_twist`: the actual kernels have the exp(−Σβ)·U form

### Location and size [P]

`Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/FirstKernelSmallOfFrameTwist.lean` (135 lines, read in
full):
- `first_kernel_small_of_frame` (`:20`) is the core.
- `first_kernel_small_of_frame_twist` (`:87`) is a wrapper. It truncates Ξ₀ to j < mm and to representatives.
- `first_kernel_law_global_small : TranslatesOfInertKernelAtPlace` (`:124`) is the consumer form.

### Statement (trimmed) [S]

```lean
theorem first_kernel_small_of_frame (D : D7) (h5 : 5 ≤ p) (X : Sys p) (E : CEmbC X.G) (hfin …) (g : GL3Theta.G1 p)
    (hLT : LTIso g) (pos : (Σ v, Fin (n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal 𝓞K) (δ : ℂ) (B : Base D cc δ)
    (χ …) (SS …) (cl) (Ξ₀ …) (muT …) (ρ …)
    (hAt : GL3Theta.At D cc δ g) (hIn : GL3Theta.InertK D p) (hM : ModelOverW g.lam g.abelian₂ g.C)
    (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : IsChi D χ) (hLam …)
    (hAdm : AdmGLt …) (hCl : ClAway p cl) (hXi : XiAway …) (hSc : ScalGLt …) (hρ : LamPosG …) (hMI : MInv …) (hL : FrameLatMapLt …) :
    FirstKernelLawLocalPowerSeries X E hfin (beLT hLT) pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT))
```

**Paraphrase.** Fix an inert prime p ≥ 5 and the CM data:
- 𝔠 is coprime to 2d and to p, and δ¹² = Δ(φ₀(𝔠)), so Λ = δ·𝔠 has unit discriminant;
- `g` is a Weierstrass model of ℂ/Λ over ℂ_p with integral, unit-discriminant coefficients in W(F̄_p) (`At`,
  `ModelOverW`);
- `LTIso g` says: an integral change of variable θ with unit linear term carries the height-2 Lubin–Tate logarithm
  `logF` = Σ x^{p^{2j}}/p^j to ε·log_W, with ε a unit.

Then for every lift step j, every class representative L0 and every target lattice tuple La′, the step-j kernel series
`FrecG …` satisfies `ExtensionGeneratorCondition` with respect to β = `beLT hLT`. This holds in every frame φ (the
kernel is moved to the lattice-tuple frame by `thA φ`). By `adm_two_pendant_iff_representative` this condition is
equivalent to the `adm2` clause of the local system: ThV = expS(−Σ_e β(x_e, y_e))·U with U integral in log parameters.
[S for the statement; the equivalence is used at `:130` and I take its content from the clause name and
frontier-f Task 2d, so N.]

**Project notions, one level down** [S]:
- `kerTh B χ SS c N N′ Ξ` (`PairingIndexBounds/OrthogonalChartLevels/KerTh.lean:26`) =
  `thC (embT) δ d area⁻¹ (aaOf cc) SS N N′ c Ξ (B.eNat χ a b N N′)`. Here:
  - `B.eNat χ` (`KernelLattices/LateralTheory.lean:~170`) = chiFac(χ)·`thMoved`;
  - `thMoved` is the basic theta `thZero = tensPow B.thMM` moved by the isogeny-averaging operators `Iop` (a sum over
    La₂/La₁ of the translates `U`, normalized by √index) from the standard Hom-lattice to Hom(L, L′);
  - `thC … Ξ θ` = `xiV … 1 Ξ θ` (`KernelLattices/XiIndCClass.lean:239`) is a finite sum, weighted by Ξ, over
    representatives of LamC/AC/BC. These are half-lattices at the places in SS, so this is a **lattice model of the
    finite Weil representation**.
- `VC D N N′ = Tau → Mat_{N′×N}(ℂ)`. The theta space `ThSp`/`Th` (`IsDiscriminantTwelfthRootOfIdealLattice.lean:87–92`)
  consists of differentiable G with G(z+x)·exp(−πH(z,x) − πH(x,x)/2)·al(x) = G(z) for x in the lattice
  `La = closure{w·A : w ∈ Λ, A ∈ Hom-lattice}`. These are classical theta functions for the Hermitian form
  H = Σ z·w̄ / area(Λ).
- `pSer D lam G` (`…:211`) has α-coefficient λ(Taylor coefficient of G at 0) (zero if not algebraic).
- `FrecG` (`OrthogonalChartLevels/FdOfCharts.lean:42`) = frame substitution `linSub`, applied to
  p^{Σ vm·(len′−len)} · `serP lam (scalars · kerTh …)`. So it is the Taylor series of the global theta kernel, scaled by
  explicit p-powers of lattice lengths.
- `G1`/`At`/`InertK`/`ModelOverW` (`SharpRestriction/GlobalSchurBounds/GL3Theta.lean:57–117`):
  - `G1` holds λ, Λ, a Weierstrass change C, `wq` and `ex`;
  - `g.l = flog W wq` is the formal logarithm of W = C•(y² = 4x³ − g₂x − g₃ model);
  - `g.ph = −log(ePhi1)` and `g.be a b = ph(a+b) − ph(a) − ph(b)`;
  - `InertK` is Jacobi(−d, p) = −1.
- `ePhi1 = (sgSer(ε·log_W t))/(ε t)` (`IsDiscriminantTwelfthRootOfIdealLattice.lean:245`). Here `sgStar Λ` is the odd
  entire function with G′(0) = 1 and the U1 law G(z+ω)·e^{−πzω̄/A − π|ω|²/2A} = ±G(z). This is the "reduced" Weierstrass
  σ-function σ(z)·e^{−η-quadratic}. `sgSer` is its Taylor series pushed to ℂ_p.
- `LTIso`, `beLT` (`LocalToGlobal/GroupLattices/PendingLemmas/CoeffOneLNe.lean:60,123`) [S].

### Proof skeleton [P for `:20–84`; P-skel one level further]

1. `hFam` rewrites `FrecG` as `linSub S (sclY (ltC g hLT) (pSer …(kerTh …)))`.
2. `hB : BeProp p (beLT hLT)` comes from `inert_facts_first_hold … h5 hIn hM` (`InertKernelTheory/AdmissibleEleventhInert.lean:12`).
   This is the "β is biadditive and σ-semilinear" property [S/N].
3. `hComb0 := combAtLt_of_dataRec …` (`K1RepresentativesLTOfDictionary.lean:196`). The Taylor series of `kerTh` is an
   `IsComb`, i.e. a finite ℂ_p-integral combination of `pSer(U t (eNat χ N N′ L₁ L₁′))`, where the t are prime-to-p
   torsion translates and the L₁ are self-dual lattices p-locally equal to L. Its inputs:
   - `AlgTP.algT_of` (Taylor coefficients of translates are algebraic);
   - `ClAway` and `XiAway` (the Weil-representation data Ξ is integral away from a set not containing p);
   - `dataRec_movD`.
4. `hComb := combAtLt_scalar …` absorbs the scalar factors (`ScalGLt`: χ and μ-values are p-units).
5. `hOnb := onbExLt_of (orthBasisExists_of global_orthonormal_basis_four weakApprox…) h5 hIn hAdm` gives a p-local
   orthonormal basis of the Hom-lattice. This uses p ≥ 5 and inertness.
6. `hTr` (rank/trace ties) and `hFH := frameHypLt_of_lat … (RepFrob.frobTw_of X E h5) …`. The p-adic frame change
   S is a hyperbolic/Frobenius-twisted linear substitution (`IsHypPair σ f f′`, `UnrOK`).
7. `K1_representatives_LT_of_dictionary curve_dictionary kernels_integral_inert …` (`K1RepresentativesLTOfDictionary.lean:253`,
   35 lines, [P]) obtains (g₂, g₃, ε, s₂) and `DictInt` from `CurveDict`. For each step it takes the orthonormal basis
   b and applies `DictInt` to the integrality `IntInert … hCb`. Then `k1gen_of_orth` turns this into the
   ExtensionGeneratorCondition [S].

**Two levels down.**
- `curve_dictionary = BeCob.rdictMain` (`RepDict.lean:301–561`, about 260 lines, [P-skel]: first and last ~40 lines). Its
  inputs are:
  - `Sigma.invAlg'` (g₂, g₃ algebraic);
  - `Sigma.secondEisensteinAlgebraic` (the value s₂ of the second Eisenstein series at the CM lattice is algebraic);
  - `phWAll`, `beta_coefficients`, `coboundary_exact`, `coboundary_equivalence`, `phase_compatibility`, `thetaTie_of`.

  The core is `dict_core` (`RepDict.lean:185`) [S, P-skel]. Its hypotheses:
  - log_W∘h = κ·logF, with h integral (the LT isomorphism);
  - exp(ph) = V·σ̂(h)⁻¹, with V integral (σ̂ = `ePhi1`);
  - atLog(G)·ePh is integral (theta in log_W coordinates divided by ∏σ̂(t_i)).

  Its conclusion: exp(Σ_e ph)·(G in Lubin–Tate parameters) is integral. That is the exp(−Σβ)·U shape.
- `kernels_integral_inert : IntInert` (`InertKernelTheory/KernelsIntegralInert.lean:9`)
  = `integral_inert_of_approx_basis weak_approximation_places local_orthonormal_basis`
  → `integral_inert_of_weakApprox` (`IntegralInertOfWeakApprox.lean:9`) [P]
  → `intInert_of` (`InertCoprimeLemmas/IntAsm.lean:79`, [P-skel]). `intInert_of` takes 11 inputs:
  - `CombFact`, `PairFact`, `WeakApprox`, `PullTors`, `PullFact`, `AlgFact`, `PSerLin`;
  - `StdStep`: the Hecke-moved theta `U t (eNat χ N N′ M M′)` is an integral Q̄-combination of translates of the basic
    `thZero` (`DefsInt.lean:100`);
  - `BasisInv`;
  - `TensFact`: integrality for the 2×2 basic theta implies it for all even N, N′;
  - `ThFourInt`: integrality of `pSer(U s (thZero 2 2))` for prime-to-p torsion s (`DefsInt.lean:133`). This is proved
    by `thFourInt_of (oneCopyLoc_of_isom …) … four_products_from_one …`, a product of one-variable thetas.

  `IntInert` itself (`StatementInt.lean:18`) [S] says: for p ≥ 5 inert and every IsComb F, every integral model C,
  every `wq` and every p-local orthonormal basis b, `atLog(F)·ePh` is p-integral.

### Size

The file is 135 lines. Below it: `K1RepresentativesLTOfDictionary.lean` 288 lines, `RepDict.lean` 565 lines, and a few
hundred more lines in the IntInert reduction (not counted).

### Classical counterpart (my judgement)

- Theta functions on a CM abelian variety have algebraic Taylor coefficients at the origin (Shimura) and the p-adic
  integrality of their expansion in the formal parameter at a good prime. This is the Katz programme (Katz, "p-adic
  interpolation of real analytic Eisenstein series"; Katz, "p-adic L-functions for CM fields") and Mumford's algebraic
  theta functions.
- `sgSer`/`ePhi1` and β = ph(a+b) − ph(a) − ph(b) are the Mazur–Tate p-adic σ-function and its quasi-quadratic
  defect.
- The algebraicity of s₂ is the algebraicity of E₂*(CM point)/Ω² (Masser; Katz).
- The reduction to a 2×2 basic theta via unimodular decompositions is the standard "theta of L ⊗ Λ factors as a product
  of one-variable thetas for an orthonormal basis" argument.

## Target 2. The global chain steps equal the lattice-sum kernel expansion

### `thetaLocalModels_of_splitUnramified_joints` [P]

`Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaLocalModelsOfSplitUnramifiedJointsStatement.lean:8`
(9 lines) forwards to `GlobalTheory.TwV.modelsOK_of_joints` (`…/ThetaLocalModelsOfSplitUnramifiedJoints.lean:11`, 30
lines, [P]):

```lean
theorem modelsOK_of_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ … (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) →
  (∀ u, ex.tw.e0 u mu0 = ex.tw.eMu0 u 0 _) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → TwU.ModelsOK D Gl ex.cmp Dx ex.tw
```

**Paraphrase.** Assume:
- the kernel law (`AdmAtEnt2`, proved in frontier-f via Target 1);
- the existence of CM curves (`CurveEx`);
- a tie `t` between the global chain and its theta kernels;
- "joints" at every served place.

Then at every place w over a non-excluded prime there is a local chain (Lv, Ch) with:
- `CmpLite`: a semilinear comparison map from the global form lattices to the local lattice-tuple spaces that
  intertwines the global step `(D.chTw u μ).K j` with the local `Ch.Kz j`, and transports valuations;
- `SiteAdm`: an admitted local formal-group system exists (`ModelsOK`, `Definitions/GaloisGeometry/ModelsOK.lean:56`).

The local chain is **built from the global one**: `chainAt H hT`.

The proof chooses (Lv, I, H, X) from `JointsAt` and calls `jointSite_chain_compared_carries_admittedSystem` =
`site_cmpLite_siteAdm` (`…/JointSiteChainComparedCarriesAdmittedSystem.lean:72`, [P]). Inside it:
- `CmpLite` comes from the fields of `kaAt X H hT : KerAtMu`.
- `admissible_at_each_site` (`:22`, [P]) applies `AdmAtEnt2` to the pending system `S.Y = pendG … (FrecG …)`.
  - Its first argument (the `Joint.At` data) supplies the kernel law: `S.Y`'s theta kernels are exactly the `FrecG` of
    Target 1.
  - Its second argument is the tie `TiesAt` for each j < m:
    - `FormsSharpAt` (from `J.sharp`);
    - `TieStabAt` (`tieStab_kaAtAny`);
    - `TieReadAt` (`series_reading_entries`);
    - `TieSerAt` (`series_compatibility_of`);
    - **`KernelDifferenceAtLevel`** (from `S.Del j`).

### `jointsAt_all_std` [P]

`…/SatakeParameters/JointsAtAllStd.lean:11` (28 lines). It destructures the family's `Part` data and its `kerTie`, then
calls `T.kernel_relation_true_columns_joints_all_tuples` (`KernelRelationTrueColumnsJointsAllTuplesStatement.lean:14`,
**unread**). It returns a `KerEntTied` and `JointsAt t μ` for all μ.

### `KerAtMu` [S]

`Formalism/SharpRestriction/GrowthBounds/LatticeMultiplicityLemmas/LatticeMultiplicityCheck/Retype.lean:9`. It is a
structure with these fields:
- global classes ↔ lattice tuples mod Γ (`cls_iff`, `cls_surj`);
- stabilizer orders divide `DGam` (`stab_dvd`);
- `cmp j` is injective and its O-span is `Int j`;
- **`cmp_K`**: if emb(y) = K_j(emb x) globally, then cmp(y) = Kz_j(cmp x);
- `val` (valuation transport).

It is pure comparison data. The identification of the steps with kernel sums is not in it; that sits in
`KernelDifferenceAtLevel` and the TiesAt package.

### What the global step is [S, P where marked]

- `ColumnChain` (`Formalism/LocalRingCardinality/DataKernels.lean:14`) [S] holds:
  - finite class sets `cls i` with finite stabilizers dividing `DGam`;
  - vector spaces of functions on `Y i`;
  - unit-modulus ρ factors;
  - **abstract linear maps `unf i c c′ : (Y i → ℂ) → (Y (i+1) → ℂ)`**.

  `K i φ c′ = Σ_c |stab c|⁻¹·ρ·ρ′·divDe(unf i c c′ (sharp (φ c)))` (`GL3Theta.lift_eq`, `GL3Theta.lean:525`). This is
  the classical formula for a theta lift between definite groups, i.e. a Hecke-type sum over genus classes.
- `liftTie` / `lift_formula` (`GL3Theta.lean:575, 584`) [S; `lift_formula` P]. Suppose
  unf(evFr Q) y′ = `applyAt0 (polD dgen Q (frm y′)) (Th c c′)` with Th an `IsKer` (an integral Q̄-combination of
  S-torsion translates of `eNat`). Then
  `K i φ c′ y′ = Σ_c |stab|⁻¹·ρρ′·de^{−sDiv}·applyAt0(polD …)(Th i c c′)`.
  So each step is a sum over classes of a **constant-coefficient differential operator (from polynomial Q) applied at
  z = 0** to the complex theta kernel.
- `KerEntTied` (`LocalToGlobal/KernelLattices/FirstKernelLawReading.lean:395`) [S] carries:
  - the CM data cc, δ, B, χ;
  - lift objects O;
  - `O_Th : (O u μ).Th i c c′ = (rd u μ).Th seam amb i c c′`, where `KerRead.Th` (`:92`) is `s.push (thC … Ξ (A.e …))`.
    This is **the same `thC` as `kerTh` in Target 1**;
  - **`unf : UnfIs (O u μ) i (nuT D u i)`** as a field;
  - the p-adic reading `ent : KerEnt` with the `kform` law (`LocalRingCardinality/DataKerI.lean:76`).
- `entRec` (`InertKernelTheory/K2OfAgreements.lean:132`) [S] is the class summand ρρ′·de^{−sDiv}·applyAt0(polD …)(Th).
  `KernelDifferenceAtLevel` (`InertKernelTheory/SecondKernelEntrywiseLastLevel.lean:46`) [S] requires
  `Rd(entRec …) = cK • Y.DelF j (cmp x) (Sr j La (c′, L′))`. In words: the p-adic reading of the complex class summand
  equals the local differential operator `DelF` applied to the local kernel series, with ‖cK‖ = 1.
  `K2OfAgreements` (`:100`) [S] turns the ties into `ExpansionEquality`.
- `S.Del j` is proved by `tieDel_all_steps` (`…/KernelSiteFrameValuesAllStepsLtM.lean:23`, 74 lines, [P-skel]). Its main
  lemmas are **unread**:
  - `stepDeterminantConstant_unit_independent`;
  - `exists_adelic_latticeTuple_decomposition`;
  - `operatorOnFrame_and_classSummand_polynomial`;
  - `transportedFramePolynomial_complex_values_at_point`;
  - `movedForms_operator_degrees_at_kernelSource`;
  - `FrameB.equiv_frame_b`;
  - `unit_mul_sourceScalar_eq_nextLevelScalar`;
  - `kernelSite_contractionIdentity_operatorHalf`;
  - `latticeTupleReading_eq_of_realising_polynomial`.

  This is where the complex differential operator at the global point is transported into p-adic frame coordinates.

### Where the chain is shown to be the theta lift [P]

`KerEntTied`'s `unf` field is supplied in `kerEntTied_true`
(`Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/KernelEntriesCompatibleTrueColumns.lean:150`) from a
hypothesis `∀ u a i, UnfIsAll (O u a) i`. That hypothesis is discharged by:
- `kernel_inputs` / `unfIsAll_of_same` (`UnfIsAllOfSame.lean:18,41`);
- which take it from `lift_objects` (`MtOfFactors.lean:83`);
- which uses `objOf_unf` (`MtOfFactors.lean:62`).

`objOf_unf`'s proof is a `show … ; rfl`-style unfolding. In the true-column family, the chain is
`(I.rec7 l Z).chTw = I.chain l` (`Definitions/AutomorphicMembership/LatAtLattice.lean:190`), and its chain data is
`TC.chIn` (`LatAtLattice.lean:~70`):

```lean
jet i c c' := jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 (GStep.rep _ c) (GStep.rep _ c'))) 0
```

So **the chain's unfolding maps are defined as the jets at 0 of the theta kernel `I.th`**. The lift formula therefore
holds by construction. In the files on this path I found no theorem relating this chain to an adelic theta integral.
theta-chain.md (Q3) records that `IteratedLiftChains.IsIterLift` is essentially unreachable. Undetermined:
whether some other strand proves that `chTw`'s eigenforms are theta lifts in the automorphic sense. That matters for the
Galois and congruence strands, not for the valuation itself.

### Classical counterpart

- The theta correspondence for definite unitary dual pairs written explicitly: the lift of an algebraic modular form is
  a finite sum over genus classes, weighted by 1/|Aut|, of theta series of Hom(L, L′) with pluriharmonic polynomial
  weights. This is Eichler/Böcherer/Rallis style, the weights realized as Taylor coefficients at z = 0 in the
  CM-elliptic variable.
- The Ξ/`xiL` data is a lattice (Mumford finite-Heisenberg) model of the Weil representation at the places in SS.
- I saw no Schrödinger or Fock model.

## Target 3. `theorem_s_uniform` and `restGc`

### `theorem_s_uniform` [P]

`Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/OmegaOfTraceDuality.lean:31`:
`ThmSUniform_of Top.betaIsG Top.theorem_s_from_k_one Top.mapSimeq`. `ThmSUniform_of` (`:15`, 15 lines, [P]) only
composes these three inputs.

`ThmSUniform` (`ThmSUniform.lean:14`) [S]. Let K₀ be complete ultrametric, with σ an unramified Frobenius lift
(`UnrOK`) and μ_{p²−1} ⊂ K₀. Let F be an integral formal group law with logarithm `lgF` = Σ x^{p^{2j}}/p^j. Then every
`be` satisfying `BetaHyp` is ≃ (equal modulo integral series) `Gser p c (σc)` with |c| ≤ 1 and σ²c = c. Moreover, the
following lies in `InClass p (hhS p (uS c σc))`:
- in variables (Bool × EV ν r0 r1), the theta kernel mvExp(−Φ)·U0 with Φ ≃ Σ_e be(x_e, y_e) and U0 integral;
- substituted by X ↦ ϖ·sSub(om, oms, μ), where ϖ^{p²−1} = p, μ is the inverse of the rescaled log `lamF`, and om/oms
  are Frobenius-compatible dual bases (`OmOK`).

`BetaHyp` (`IsLawOfLog.lean:89`) [S] has these clauses:
- no pure-x or pure-y terms;
- the Čech coboundary d₁(F, be) ≃ 0 in each variable, i.e. biadditive modulo integral;
- **be(ζx, y) ≃ be(x, ζ^p y) for ζ^{p²−1} = 1** (σ-semilinear under Teichmüller multipliers).

`Gser` (`OddLogRelation.lean:28`) = c·A − c′·A′, where:
- A = Σ_{i≤j} x^{p^{2i}} y^{p·p^{2j}} / p^{i+j+1};
- A′ is A with the roles of x and y swapped.

**Skeleton** (`FinalS.lean`, 65 lines, [P] as a list of lemma names; bodies unread):
- `betaIsG = BetaIsG_of zeroCondition stepI stepII stepH stepIII stepIV swapRules simeqRules`. This classifies β. It uses:
  - `LemmaOne`: f with integral coboundary is α·g0F + β·lgF + integral;
  - `LemmaTwo`;
  - `DworkMv` (`dwork_multivariable`).
- `theorem_s_from_k_one = theorem_s_from_k_one_of thmSCore simeqRules`, with
  `thmSCore = ThmSCore_of rescaleCore classSubst classChange classMul twoSums logRescale logRescaleUnique`.

The numerical heart is visible in its statements [S]:
- **`ValTable`**: for i ≤ j, ((p²)^i + p(p²)^j)/(p²−1) − (i+j+1) ≥ 1/(p−1) − 1, with equality only at i = j = 0. So
  after X ↦ ϖX every coefficient of Gser except the leading x·y^p/p is integral after exponentiation. The leading one
  gives ϖ^{p+1}/p·hh.
- **`PiFactorial`**: ϖ^{(p+1)i}/i! is integral.
- **`ExpIntegral`**: |coefficients| ≤ p^{−1/(p−1)} implies exp is integral.
- **`TwoSums`**: hh₁ in the twisted coordinates equals hhS + p·(integral).
- **`LogRescale`**: lamF ≡ X + X^{p²} mod p, and its inverse μ ≡ Σ(−1)^l X^{p^{2l}} = `altF`. This is where sPos's
  alternating signs come from.

### `restGc` [P]

`Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CommonEigenvectorThird.lean:21` (file is 38 lines):
`restGc p := gcCondition_of_twoSums (restTwoSums p)`, where `restTwoSums := restTwoSums_of sx_mu_alt sx_dual sx_frob_sum
frobenius_congruence_witt`.

`RestGc` (`DworkExponentialRestrictions.lean:19`) [S]: for p ≥ 5, c ∈ W with σ²c = c, an `OmBasis` and ϖ^{p²−1} = p,
exp(−G_t(c, σc)) in the coordinates `tOf ϖ μ (coordZ B)` equals exp(−(ϖ^{p+1}/p)·hhS(u))·V, with V integral and
u ∈ R_p. This is the multi-variable restatement of the single-variable `ThmSCore` in the local-system coordinates.
`gcCondition_of_twoSums` is unread.

### Classical counterpart

- Dwork's lemma, and the Hazewinkel functional-equation lemma for lgF (f(x) − p⁻¹ f^{σ²}(x^{p²}) = x).
- Honda/Lubin–Tate theory of the height-2 group for ℚ_{p²} with uniformizer p.
- The classification of σ-sesquilinear "biextension" pairings on it, which is a Mazur–Tate quasi-bilinear-form
  computation.
- The overall style matches Katz's analysis of Eisenstein and theta series at supersingular CM points (the
  "ϖ^{p+1}/p" scale is v = 1/(p−1) − 1).

## Target 4. Where Σ_{odd e}(a/p^e − cap)⁺ is derived

### `EntryStar_of` [P-skel]

`FrobeniusLiftNorms/NormLeOfDvd.lean:309`, about 95 lines. Its inputs are:
- `TermBound`;
- `HhDecomp` (decomposition of hhS into a monomial part Z and an integral part Y);
- `ClassSubst` (InClass is stable under linear substitution `zSub TT ξ`);
- a Hasse-derivative degree lemma (`hD`);
- `StarEntryOperators.lowOp_deg`, `star_norm`.

It returns either jetPair = 0, or multiplicities α (hh-factor uses) and β (Hasse directions), with:
- β hitting the low operator nontrivially;
- ‖jetPair‖ ≤ p^{−(γ_p·Σ_{s∈TT} al_s − Σα − Σβ − deLoss + ρ_p·Σ(al+ls))}.

`EntryStar` is stated at `StatementE.lean:176` [S].

### `gainFactorialInequality : StarArith` [P-skel]

`FrobeniusLiftNorms/ABArith.lean:103`. `StarArith` (`StatementAB.lean:103`) [S] is a real-variable Legendre bookkeeping:
for exponents e, a, i with p^{2e′+1}·i(s, e′) ≤ al_s,

  γ_p·Σ al − i₀ − Σ i − deLoss ≤ Σ v_p(e!) + Σ v_p(i!) + Σ v_p(a!) − ρ_p·Σ(al+ls) − (i₀ + Σ i + i₂).

The proof combines:
- `sum_factorial_ge`, i.e. v_p(m!) ≥ m/(p−1) − lgN_p(m) (`FactorialLg`);
- `oddPowerInvSumIdentity`: γ_p = p/(p²−1) = Σ_e p^{−(2e+1)}, and 1/(p−1) = γ_p + ρ_p with ρ_p = 1/(p²−1)
  (`GrowthSums/StatementA.lean:63–65`).

### `excessGainBound : ExcessGainBound` [P-skel]

`ABArith.lean:193`. Statement [S]: γ_p·Σ al − Σ ch − Σ i − de ≤ v, with
- ch + i ≤ al/p^{2e+1} when 2e+1 ∈ D(s),
- i ≤ min(al/p^{2e+1}, cap(s + (2e+1))) otherwise,

implies excessGain ≤ v. The proof writes γ_p·al_s as HasSum Σ_e al_s/p^{2e+1}, subtracts the finitely many charges and
uses, then truncates termwise. `cyclicShiftLeast : ChargeLemma` (`:185`, [P]) is the elementary least-shift lemma on
ℤ/n. `dSet TT s` (`StatementE.lean`) [S] is the set of shifts from s to elements of TT of the opposite parity; at those
shifts the gain is set to 0.

So the **odd-power Legendre formula** is assembled as follows:
- the factorial inequality gives the γ_p = Σ_{odd} p^{−e} main term;
- each use of an hh-factor that links s to s+(2e+1) is charged at most al/p^{2e+1};
- each such link is capped by the weight at the partner index s+(2e+1).

The Hasse-vanishing lemmas `MinorHits`, `HitsCap` and `HitsColumns` (`StatementAB.lean:59–83`, [S]) supply the
counting: a product of minors is killed by more Hasse derivatives than it has columns.

### Classical counterpart

Legendre's formula v_p(a!) = Σ_k ⌊a/p^k⌋, split into odd and even k (γ_p + ρ_p = 1/(p−1)), together with Hasse
derivatives of determinantal (Cayley/Shimura-type) differential operators.

## Target 5. `HondaCM3.cm3` [P]

`Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/OneSubTwoOmegaSq.lean:77–158` (about 80 lines; the file
is 160).

**Statement `CM3`** (`Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean:49`) [S]. Let d be
squarefree with d ≡ 3 mod 4, L a lattice with CM by ℚ(√−d), ℓ ≥ 5, ℓ ∤ d, and −d a non-square mod ℓ. Suppose (g₂, g₃)
is a good model over ℂ_ℓ. Then there is a unit ε ∈ K̆ = (max. unramified) such that the formal exponential `uSer g₂ g₃`
composed with ε·ltLog has K̆-integral coefficients. Here ltLog = Σ x^{ℓ^{2j}}/ℓ^j.

**Skeleton** [P]:
1. K̆ is complete with a Frobenius lift σ (`kurComplete`, `kurFrob`, `maxUnramified_residueAlgClosed_and_frobeniusLift`).
2. `isIntegralHondaLogarithmPair_shortWeierstrass`: the short Weierstrass formal group over K̆ has an integral
   log/exp pair (`IntLog`).
3. w = ι(ω), ω = (1+√−d)/2, lies in K̆ (`sqrtKur`, inert), with σw = 1 − w and ‖σw − w‖ = ‖1 − 2w‖ = 1, since
   (1 − 2ω)² = −d is a unit.
4. `cmMultiplierIntegralSeriesAtInertPrime_proof`: [w] = exp(w·log) has integral coefficients.
5. Height ≤ 2: `formalGroup_height_le_two_good_reduction` gives n ≤ ℓ² with ‖coeff_n [ℓ]‖ = 1.
6. `heightTwo_formalGroup_unramified_multiplier` (**unread**, the Honda step). A height-≤2 integral formal group over
   K̆ with an integral endomorphism w with σw ≠ w mod ℓ has logarithm ε·ltLog up to an integral change of variable.

**Classical counterpart.** Deuring (inert ⇒ supersingular) together with Honda's classification / Lubin–Tate: the formal
group of a CM curve at an inert prime is the Lubin–Tate group of ℚ_{ℓ²} with uniformizer ℓ.

## Answers

### A. The bridge

**It is Katz-style.** A CM point is chosen: the lattice δ·𝔠 of K = ℚ(√−d), normalized by δ¹² = Δ(𝔠) (`At`,
`IsDiscriminantTwelfthRootOfIdealLattice`). In the true-column family cc = ⊤, i.e. δ·O_K (`kerEntTied_true`). The
kernels are classical holomorphic theta functions on the CM abelian variety (Hom-lattice) ⊗ ℂ/δ𝔠, obtained from a basic
theta by isogeny averaging, a Hecke character and a lattice-model Weil representation at SS. Then:
1. They are Taylor-expanded at 0. The coefficients are algebraic (`AlgP`, `TransAlg`).
2. They are mapped to ℂ_p by λ (`pSer`).
3. They are rewritten in formal-group coordinates t through z = log_W(t) (`atLog`).
4. They are shown integral after division by ∏σ̂(t_i) (`IntInert`).
5. The CM3/LTIso isomorphism turns log_W into ε·Lubin–Tate log (`CurveDict`/`dict_core`).

The exp(−Σβ)·U form is therefore **proved of the actual theta function** (Target 1). It is not inserted by definition.
β is defined from the curve's own σ-function (`G1.be`), and Theorem S then classifies it abstractly.

The remaining link, "global chain step = Σ_classes differential operator at 0 of the theta kernel" (`lift_formula`,
`TiedLift`), has two parts:
- It holds **by construction** for the true-column chains: `TC.chIn` defines `jet` from `I.th`, and `objOf_unf` is
  definitional.
- The p-adic transport of that operator into local frame coordinates is a theorem (`tieDel_all_steps`, main lemmas
  unread).

I found no proof on this path that the `chTw` chain equals an adelic theta integral. That question belongs to how the
family's forms are used elsewhere (Hecke and Galois properties). For the divisibility it is not needed, because the
divisibility is about this chain. Undetermined beyond that.

### B. Why only odd powers of p

The alternation enters through the σ-semilinearity clause of `BetaHyp`, be(ζx, y) ≃ be(x, ζ^p y) for ζ ∈ μ_{p²−1}.
This is the Hermitian (Frobenius-twisted) compatibility of the CM action of the Teichmüller lifts of F_{p²}.

Combined with the height-2 logarithm lgF, which only has exponents p^{2j} (`OddLogRelation`: g0F = p⁻¹·lgF(x^p) and
g0F(x^p) = lgF − x), it forces β ≃ c·A − σ(c)·A′ with A = Σ x^{p^{2i}} y^{p^{2j+1}}/p^{i+j+1}. So **x carries even and
y carries odd p-power layers**.

In many variables, `hhS = Σ_s u_s·sPos_s^p·sPos_{s+1}` couples embedding index s to s+1 at the cost of one p-th power,
and `sPos_s = Σ_l (−1)^l X_{s−2l}^{p^{2l}}` moves 2l steps for p^{2l}. A monomial at s can therefore reach the partner
s+(2e+1) only through an odd total p-power p^{2e+1}. The `uS` sign is c on odd s and −σc on even s.

It becomes visible in these statements:
- `ExcessGainBound` (`StatementAB.lean:120`), with `cap (s + (2e+1))`;
- `excessGain` (`GrowthSums/StatementA.lean:108`);
- `gA` (`FormalGroupSystem.lean:66`), with `posAdd s (2e+1)`;
- on the global side, `ASK` with `frob p ^ i` for odd i.

γ_p = p/(p²−1) = Σ_e p^{−(2e+1)} (`gamP`, `oddPowerInvSumIdentity`).

The archive does not phrase this as "π² = −p". It uses the Lubin–Tate group of ℚ_{p²} with uniformizer p (log
Σ x^{p^{2j}}/p^j) and the totally ramified ϖ with ϖ^{p²−1} = p (`lamF`). One Frobenius (a p-th power) shifts the
embedding index by one.

### C. Uniformity in p and in the step

**p ≥ 5** is used in these places [S/P]:
- `Std.five_le`, giving 2 < p for `EntryHyp` (`ea_two_lt`, `EaGeCOfNorm.lean:194`);
- the hypotheses of `RestBeta`/`RestGc` (`DworkExponentialRestrictions.lean:125`, `EaRestSExpVOf.lean:262`,
  `ExpansionAllPlacesOfPlace.lean:176`, `KernelExpansionOfRestrictions.lean:139`);
- `RelativePresentationOfD7.lean:55`;
- on the bridge side, `CM2`/`CM3` (ℓ ≥ 5: short Weierstrass integrality needs 2 and 3 to be units), `BeProp`
  (`inert_facts_first_hold … h5`), the orthonormal basis (`onbExLt_of … h5 hIn`), the Frobenius twist
  (`frobTw_of X E h5`), and `IntInert`, `CurveDict`, `TranslatesOfInertKernelAtPlace`.

How inert p = 3 (and 2) are booked on the global side is undetermined here. They are not served by the local theorem.

**w nondecreasing** (`Std.w_mono`, `FormalGroupSystem.lean:101`) is used only through `w_le`
(`MultisetValuation/TheoremOfAlternateForm.lean:374`), in:
- `neg_liftWt_le` (`RestrictedHeckeIntegralOfEdges.lean:50`): the lift weights at step j+1 are ≥ −w_{j+1};
- `mu_le` (`TheoremOfAlternateForm.lean:~470`).

That is weight bookkeeping for Hecke integrality and degree bounds. It does not appear in Theorem S, `EntryStar` or the
factorial inequality. I did not trace those lemmas' consumers.

**Hidden constants.** I found no hidden constants:
- Theorem S (`InClass`) is exact. It has no constants, only the integrality of U_i.
- The local losses are explicit: deLoss = Σ(r1·lgN_p(al) + r0·r1·lgN_p(ls)) + Σ lgN_p(al)², with
  lgN_p(x) = ⌊log_p x⌋ + 1 (`StatementAB.lean:95–101`). Here r0, r1 = NN(j), NN(j+1) grow linearly in j
  (frontier-f Task 3).
- ρ_p·Σ(al + ls) is the exact ϖ-normalization.
- The step-to-step unit cK has ‖cK‖ = 1 (`KernelDifferenceAtLevel`).
- Each step loses dG_j ≤ v_p(DGam), a global stabilizer bound.

Everything is quantified over all inert p ≥ 5 and all j < m. So the dependence is through log_p a, j and v_p(DGam)
only. Whether the global sum of these losses over p ≤ 2a and j < m is absorbed is an accounting question for the
`core_gm` errors, not checked here.

### D. Unread, in priority order

1. `T.kernel_relation_true_columns_joints_all_tuples`
   (`Development/AbelianVarietyTheory/Proofs/SatakeParameters/KernelRelationTrueColumnsJointsAllTuplesStatement.lean:14`)
   and the main lemmas of `tieDel_all_steps` (`…/KernelSiteFrameValuesAllStepsLtM.lean`). The most important of these
   are `kernelSite_contractionIdentity_operatorHalf`, `transportedFramePolynomial_complex_values_at_point` and
   `exists_adelic_latticeTuple_decomposition`. They transport the complex operator at 0 to p-adic frames.
2. `BeCob.rdictMain` body (`InertKernelTheory/InertCoprimeLemmas/RepDict.lean:330–530`) and its inputs:
   - `Sigma.secondEisensteinAlgebraic`, `phWAll_of`, `beta_coefficients`, `coboundary_exact`, `thetaTie_of`;
   - `dict_core` body (`:185–300`).
3. The `IntInert` leaves: `ThFourInt` via `thFourInt_of`, `four_products_from_one` (`MMFour.lean:206`),
   `oneCopyLoc_of_isom`, `StdStep`, `pullback_fact` (`IntPull.lean:652`), `AlgP.algebraic_fact_kernels`
   (`AlgKleinPf.lean:566`).
4. `HondaCM3`'s Honda step `T.heightTwo_formalGroup_unramified_multiplier`, and
   `isIntegralHondaLogarithmPair_shortWeierstrass`, `cmMultiplierIntegralSeriesAtInertPrime_proof`,
   `formalGroup_height_le_two_good_reduction` (all in `DecoratedLatticeProofs/*Statement.lean`).
5. The bodies of `BetaIsG_of`, `ThmSCore_of`, `theorem_s_from_k_one_of`, `gcCondition_of_twoSums`, `two_sums`,
   `valuation_table`, `dwork_multivariable` (`UniformThetaSubstitution/FrobeniusLiftNorms/*`).
6. `StarEntryOperators.star_norm`, `HhDecomp`, `TermBound` (the EntryStar internals), and `k1gen_of_orth`
   (ExtensionGeneratorCondition from orthonormal integrality).
7. Whether `chTw` (true columns, `LatAtLattice.lean`) is shown anywhere to be an automorphic theta lift (`IsIterLift`,
   `liftTie_chainTh` in `GaloisGeometry/TrueWtAddSSNonneg.lean:775`, `ChainData.unfTie_of_liftTie`).

## What to read next

- `Development/AbelianVarietyTheory/Proofs/SatakeParameters/KernelSiteFrameValuesAllStepsLtM.lean` and the statements it
  imports (`*ContractionIdentity*`, `*TransportedFramePolynomial*`). This is the last unread step between the global
  class summand and the local `DelF`.
- `Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/RepDict.lean:301–530`. This is where σ, s₂ = E₂* and
  the Lubin–Tate isomorphism produce β.
- `Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeightTwoFormalGroupUnramifiedMultiplier*.lean`. This
  is the Honda step.
- `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/LatAtLattice.lean` (`thAt`, `chain`), for what
  the true-column chain is and whether it is tied to automorphic theta lifts anywhere.
