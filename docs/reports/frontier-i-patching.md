# Frontier (i): the patching theorem `PfromAut`, Hida theory, and the linking argument

Date: 2026-11-21. This is a read-only source study of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled or
run. It used about 50 ssh reads plus one web search, made to check the published hypotheses of Allen–Newton–Thorne.
It continues `frontier-g-deep-inputs.md` (§II) and `frontier-d-window.md`.

Path abbreviations (relative to `src/Development/AutomorphicArithmetic/AutomorphicVarieties/`):
- `PM/` = `PatchingModules/`
- `AD/` = `PatchingModules/AutomorphicDetection/`
- `WGC/` = `WeilGroupCharacters/`
- `DTC/` = `ModularityArgument/ThresholdArguments/DenseThresholdCases/`
- `HA/` = `HeckeAlgebras/`
- `CDS/` = `CurveDVRSpecialization/`
- `FSV/` = `FrobeniusSmoothVectors/`

Tags:
- **S**: I read the statement.
- **P**: I read the whole proof term or tactic block.
- **P-skel**: I read the have/obtain skeleton but not every line.
- **N**: inferred from names or imports only.

Every declaration named here is a Lean theorem or definition in a build that is axiom-clean. So the open question is
never "is this proved?" It is "do the definitions mean what the classical names suggest?", and "is any hypothesis
satisfiable only trivially?"

## Overview (for a number theorist)

`PfromAut` is a real Taylor–Wiles–Kisin patching argument in the residually reducible style of Skinner–Wiles, Thorne
and Allen–Newton–Thorne (ANT). It is not a renamed hypothesis.

**The ring.** B is the universal ordinary *determinant* ring of a residual representation over a CM field L. It
deforms a Chenevier determinant law (written `GDet` in the archive), not a pseudocharacter. The residual
representation is a direct sum of n pairwise distinct characters.

**The points.** Its "points" are representations over K[[t]] with K a finite field. These are the
characteristic-l, dimension-1 "nice primes" of Skinner–Wiles and Thorne.

**The proof splits into a Galois side and an automorphic side.**
- *Galois side, proved inside `PfromAut`'s proof.* This covers:
  - choice of Taylor–Wiles places (Chebotarev);
  - detection of dual-Selmer classes, which replaces "adequacy";
  - Selmer and obstruction bounds from the Greenberg–Wiles formula and Poitou–Tate;
  - an ultrafilter patching of modules over a power-series ring;
  - a dimension argument at each nice point.
- *Automorphic side, a hypothesis `HasAut B J`.* It asks for patching data at every Taylor–Wiles level: modules free
  over the diamond-operator group rings, compatible with level 0. It is discharged by `HidaUAlt`. That theorem builds
  Λ-adic ordinary algebraic modular forms on the definite unitary group U(I_n) over L/L⁺. They are free over
  Λ = O[[n·[L⁺:ℚ]]] because the level is neat at an auxiliary place v₀. Local–global compatibility then turns
  Iwahori-level modules at the Taylor–Wiles places into the patching data.

**What the patching lemma itself assumes.** Only:
- l ≠ 2 and ζ_l ∉ L;
- a residual representation that is a sum of distinct characters;
- a finite set of auxiliary places.

It assumes no residual adequacy and no bound like l > n. The real content moves into the definition of a "nice"
point (see below).

**The linking argument.** The step "every component is modular" is not inside `PfromAut`. It sits in `CDS/` and
`FSV/` and follows Skinner–Wiles:
- base change to an auxiliary CM field whose degree at l is large compared with residual H¹ dimensions (`Frame.Big`);
- the reducible locus then has dimension < n·d, so every large component contains nice primes;
- a preconnectedness theorem for the irreducible locus;
- seeds from adjoint lifts of Eisenstein-congruent GL₂ forms.

**Scope of use.** The general-n lemma is used only for **n = 2 and n = 3** (`Setup.n23`, `CReal.n23`). It is used for
specific residual representations built from powers of Ψ, over an auxiliary CM field L with ζ_l ∉ L. For U(3) the
application runs with l ≥ 5, because `Bchi` contains 3.

**Comparison with published work.** The closest published theorem is ANT 2020, Theorem 1.1. It handles any number of
constituents, but it needs l > 3, l ∤ n, constituents irreducible on G_{F(ζ_l)}, primitivity, no quotient of order l,
and a Steinberg place v₀. The archive's Theorem-level hypotheses differ in kind: it uses Skinner–Wiles degree-growth
instead of a Steinberg place, determinant laws instead of l ∤ n, and in-archive "detection" instead of adequacy. This
difference is the place an expert should look. I found nothing that makes the statements vacuous.

---

## 1. `PfromAut`: statement and proof

### 1.1 Statement (`PM/TaylorWilesObstructionBound.lean:150`) **[S]**

```lean
def PfromAut : Prop :=
  CohP → ∀ l [Fact l.Prime] L Ω [NumberField L] [IsCMField L] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O) [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O]
    (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B),
    0 < n → V0.S' = s.S → LocCFT s →
    (∃ g : V0.frame.G₀, (ε g mod l) ≠ 1) → HasAut B J → B.P1core J ∧ B.P3core J
```

**Hypotheses, unpacked.**

- **`CohP`** (`:23`) is a bundle of eight theorem-shaped Props:
  - `LocalFiniteness`, `LocalTateDuality`, `LocalEulerChar`;
  - `GlobalFiniteness`, `GlobalEulerChar`;
  - `GreenbergWiles`, `PoitouTateNormalised`, `TameLocal`.

  It is discharged by `W.cohP_alt` from `LiteratureRankNHypothesis.coh` (`DTC/LocPublished.lean`) **[P one line]**.
  That bundle is filled by `published_hypotheses_from_patching_alt` (frontier-d). I did not re-trace the proofs of
  these fields.
- **`HidaSetting l L Ω`** (`WGC/ContinuousResP.lean:73`) **[S]**:
  - l ≠ 2, and inertia of L⁺ lies in G_L;
  - every place v | l of L⁺ splits in L (`split`);
  - a finite set St of split places prime to l;
  - an auxiliary split place v₀ ∉ St with N(v₀) = p, where p is an odd prime, p ≠ l and p ∤ disc L;
  - complex conjugation c.
- **`s.Lev`**: a set of places S' ⊇ S = {v | l} ∪ St ∪ {v₀}, all split, with η (the CM sign character) and ε (the
  cyclotomic character of G_{L⁺,S'}). `V0.S' = s.S` puts the level at the minimal set.

  The frame `V0.frame` (`:142`) has:
  - G₀ = G_{L,S};
  - G' = ker ε|_{G₀}, i.e. G_{L(μ_{l^∞})};
  - Iu = inertia at St;
  - D0 = decomposition group at v₀, and I0 = inertia at v₀.
- **`Resid F O n`** (`WGC/UniversalOrdinaryDeterminantRing.lean:109`) **[S]**:
  - n residual characters χ̄_i : G₀ → k^×, pairwise distinct (`chib_inj`);
  - the determinant law of ⊕χ̄_i is polar (conjugate-self-dual up to ε^{1−n});
  - residual local characters ψ̄_{v,i} at v | l;
  - characters θ_{v,i} on the l-part of the local abelianisation.

  So the residual representation is a **multiplicity-free sum of characters**. This is the "pseudo-representation" of
  frontier-g.
- **`UniversalOrdinaryDeterminantRing r`** (`:154`) **[S]** is a structure, not a construction. It holds a complete
  Noetherian O-algebra B and a universal `Pair r B`. A `Pair` (`:138`) consists of:
  - a continuous determinant law D lifting D̄;
  - characters ψ_{v,i} lifting ψ̄_{v,i};
  - polarity (`P`);
  - **ordinarity** (`Ord`): D kills the elements ∏_i([φ_v g_i] − ψ_{v,i}(g_i)) after multiplication by any group
    element. This is the determinant-law form of an upper-triangular flag with diagonal ψ_{v,i}.
  - inertia at St trivial on r.Ip (`I`).

  Its existence is proved elsewhere (`W.b0Ex`, used in `DTC/BaseObjectHomExt.lean`) **[N]**.
- **`LocCFT s`** (`:115`): the local abelianised inertia at each v | l has ℤ_l-rank d_v, and Σ d_v = [L⁺:ℚ]. It is
  proved from Artin reciprocity (`local_class_field_theory_all_of_literal_automorphy`) **[S]**.
- **`∃ g ∈ G_L, ε(g) ≢ 1 mod l`** means ζ_l ∉ L.
- **`HasAut B J`** (`:147`): for every Taylor–Wiles group T with Taylor–Wiles places (`TWPl`) there is
  `TWAut (pairOf B.u) J Empty (n·[L⁺:ℚ]) T`. See §4.

**Conclusion.**
- **`P1core J`** (`:284`): for a `Point` x (a K[[t]]-valued point of B) that is **NiceI** and modular (J ≤ ker f),
  every prime q ⊆ ker f contains J. That is, every irreducible component through a nice modular point is modular.
- **`P3core J`** (`:293`): suppose x₀ … x_h are **NiceE** points, consecutive ones contain a common **thick** prime,
  and some **stable** prime q₁ ⊆ ker f₀ contains J. Then every stable-or-thick prime q ⊆ ker f_h contains J.

### 1.2 Definitions of nice, stable and thick (`WGC/UniversalOrdinaryDeterminantRing.lean:189-298`) **[S]**

**`Point r`** has these fields:
- K a finite field, and ρ : G₀ → GL_n(K[[t]]), continuous;
- a symmetric P with ρ(g)ᵀ P ρ(cgc) = ε(g)^{1−n} P;
- residually D̄;
- trivial on r.Ip(u) at St;
- characters ψ_{v,i} lifting ψ̄;
- **an ordinary flag at every v | l** over Frac K[[t]].

The niceness conditions:

| predicate | definition | classical analogue |
|---|---|---|
| `N1` | at each v \| l, the ψ_{v,i} are pairwise distinct and ψ_{v,i} ≠ ψ_{v,j}·ε for i < j | "p-distinguished / regular ordinary" (Thorne 2015, Geraghty) |
| `TypeI` | ρ ⊗ (Frac K[[t]])‾ is absolutely irreducible on G' = G_{L(μ_{l^∞})} | nice prime: ρ_𝔭 absolutely irreducible (SW99; Tho15 §3) |
| `TypeE` | ρ is a sum r₁ ⊕ r₂ of two polarized pieces, each absolutely irreducible on G', with Hom_{G'}(r₁, r₂) = 0 | "reducible nice point" of two Schur-distinct pieces |
| `N3` | regular semisimple σ ∈ G' (separable char. poly) are dense in every open subset of G' | needed to choose Taylor–Wiles Frobenii |
| `N4` | no X ≠ 0 with ε(g)ρ(g)X = Xρ(g) for g ∈ D_{v₀} | H⁰(G_{v₀}, ad ρ(1)) = 0: the classical role of the auxiliary place v₀ (CHT, Thorne) |
| `NiceI` / `NiceE` | `N1 ∧ TypeI/TypeE ∧ N3 ∧ N4` | |

For primes q of B, with κ(q)‾ the algebraic closure of the residue field:
- **`IsStable q`**: the determinant at q is that of an *absolutely irreducible* representation over κ(q)‾.
- **`IsThick q`**: not stable, and E0 ⊗ κ(q)‾ is not semisimple. Here E0 is the Cayley–Hamilton quotient of B[G₀] by
  the ordinary and inertia relations. So thick means a reducible prime carrying a non-split extension: the generalised
  matrix algebra has nonzero off-diagonal products. This plays the role of the reducibility-ideal picture of
  Bellaïche–Chenevier.

None of these predicates mentions automorphy or J **[S]**. They are Galois-theoretic and match the published "nice
prime" notion in kind, as checked against ANT §4 ("p a dimension 1, characteristic l prime ... the associated
representation to GL_n(Frac R/p) is absolutely irreducible").

### 1.3 Proof skeleton

`pFromAut := pFromAut_of norm choice arPl b1Ar b2Ar raw` (`AD/PfromAut.lean:9`) **[P]**.

`pFromAut_of` and `chain_of` (`PM/ChebotarevFamilies/PFromAutOf.lean:30-133`, 133 lines) **[P]** do the following:

1. **`Norm`** (`norm`, `AD/ConjugationDescendsToSubring.lean:224`, 323 lines) **[S]**. Each nice point is moved
   (finite injective local extension of K[[t]]) to an `NP` point over the frame with Iu re-chosen. It then satisfies N3
   and N4 at D₀, and type I gives full block size a = n.
2. **`Choice`** (`AD/Choice.lean`, 40 lines) **[P]**. It picks finitely many σ_j ∈ G' that are regular semisimple at
   *all* points of the chain simultaneously. It also picks eigenvalue labels α_{j,i} and a Selmer basis κ (`Kap`)
   such that the σ_j **detect** dual Selmer classes. The steps:
   - `Det.omDense`: N3 gives a dense set;
   - `detection`, `Det.detFin`: a finite subset suffices;
   - `Det.onePt`: coefficients are extended so that the eigenvalues are defined.
3. **`Detection`** (`AD/Detection.lean`) **[P]** reduces to **`Det.detAsm`** (`PM/DeterminantPadicFree/DetAsm.lean:160`,
   268 lines) **[S, body unread]**. Its statement: for l ≠ 2 and ζ_l ∉ L, any ε-twisted polarized cocycle
   z ∈ `TwZ` whose functional ℓ_σ(z) = tr(z(σ)ρ(σ))_η vanishes for all σ ∈ G' is, up to a power of t, a coboundary.

   **This is the archive's replacement for adequacy.** It uses no l > 2n+1 bound. It relies on the field `NP.span`
   (the K[[t]]-span of ρ(G') contains t^s times the full block matrix algebra, a Burnside-type condition) and on ζ_l ∉ L.
4. **`ArPl`** (`arPl`, `AD/ArPl.lean`, 179 lines) **[S]**. For any finite list of σ_j ∈ G' there are Taylor–Wiles
   data. These are levels V_N and split places v_{N,j} ∉ S with N(v) ≡ 1 mod l^N, Frobenii converging to σ_j modulo
   the pro-l part, and tame generators τ_{N,j}. This is Chebotarev. It also gives `PhiCond` (Φ-finiteness of G_{L,S}).
5. **`FirstOrderDualArithmeticBound`** (`b1Ar`, `AD/BoundW1Arithmetic.lean`) **[P]**: `b1abs` with `arSys` (from `CohP`)
   and `LocCFT`. Its content `T.B1 k (n[L⁺:ℚ] + n·q)` says that at t-adic level m the Selmer group of the point with
   Taylor–Wiles conditions has size ≤ |boundary| · |K|^{m·D₀ + C}. This is the tangent-space bound
   "dim ≤ n[L⁺:ℚ] + nq". It is derived from Greenberg–Wiles plus detection.
6. **`TaylorWilesObstructionBound`** (`b2Ar`, `AD/TaylorWilesObstructionBound.lean:44`) **[P]**:
   `obstructionBound_of_duality` with local and global Euler-characteristic axioms `cohAxAr`. This is the H² /
   obstruction bound.
7. **`Raw`** (`raw := raw_main coreBC`) **[P]**. `raw_main` (`PM/SeparableMatrixStability/RawMain.lean`, 48 lines)
   passes to a quotient group whose kernel is pro-l (`twquot_ex`, the `ProL` property). `coreBC` (`AD/CoreBC.lean`,
   127 lines) extends coefficients so that all points have the same residue field and the weight variable is a
   parameter. Both reduce to **`core`** (§2).

---

## 2. Patching itself (question B)

`core : Core` (`AD/LiftPt.lean:76-175`, 100 lines) **[P-skel, two levels]**. In order:

1. **Ultrafilter limit.** `s4 : S4` gives `Lim T` (`PM/ThetaCoefficientMapEq.lean:265`) **[S]**. Its data:
   - an ultrafilter U on ℕ with U ≤ atTop;
   - a compact, topologically finitely generated group Ph surjecting onto every G_{S∪Q_N} and onto a limit group G;
   - the limits of Frobenius and tame elements at the Taylor–Wiles places.

   It is proved by `selmer_cocycles_limit_and_descent_properties` **[N body]**. This is the "patching via
   ultrafilters" of Scholze's simplification, applied to the Galois groups.
2. **Patched rings and maps.** `rrEx`, `rmapsEx`, `spoCo`, `piKer`, `piSurj` **[N bodies]**. They build:
   - W.R, the patched deformation ring over S∞ = Λ[[Fin q × Fin n]];
   - a map π : W.R → Spo A, the ring with the Taylor–Wiles eigenvalue variables adjoined;
   - its kernel `ii W`.
3. **Freeness over the Iwasawa algebra.** `patchedModule_free_finite_over_iwasawaAlgebra` (`PM/AnnihilatorBaseChange/`)
   **[N body]** gives the patched module X0, free and finite over Λ.
4. **Patched support.** **`s5 : S5`** (`AD/AnnBc.lean:69`) **[S, P-skel]**. Take level-N modules M_N that are free of
   constant rank over S∞/(augmentation)^k, compatible with X via maps whose compositions are multiplication by a
   nonzerodivisor f (`fEl`, the product of (α_i − α_j)(α_i − Nv·α_j)). Then there is a `PatchedSupportCompletions`
   structure: at each point prime q_i, a completed local ring B_i with an ideal S_i (the patched support) such that
   - every minimal prime of S_i has dimension ≥ d + |σ| = dim(weight space) + nq + 1;
   - S_i ≤ Q ⇔ Ann(X) ≤ Q on the fibre over the augmentation (`fib`);
   - a "move" property between points sharing primes.

   Inputs: `freeN` (freeness at each level), `eventually_exists_patchedModule_quotient_maps`, and the relation
   generators `t3Of` (trace, polarity, ordinarity, inertia, and the q1/q2 relations at the Taylor–Wiles places,
   annihilated up to ex = n!). This is the patched support argument: **Supp M∞ has full dimension because M∞ is free
   over S∞.** The proof is via `pmodEx` and `s5_lemma` **[N]**.
5. **Local dimension argument at a nice point.** `galOut : GalOut` (`AD/GalOut.lean:39`) **[P]**. Its statement: in the
   completion B̂ of the patched ring at a nice point, with K1, K2, K3 (the limit forms of B1, B2 and Selmer generation,
   from `cohLim`), a prime Z on which the representation is irreducible ("DiscSt") and with dim B̂/Z ≥ 1 + D₀ lies
   below every prime Q that is stable or non-semisimple (thick).

   The proof:
   - `s6` builds a generic representation `URep` over a finite B̂-algebra (generalised-matrix-algebra form, with the
     off-diagonal block N; N = 0 in type I);
   - `pres` gives a presentation with ≤ D₀ tangent directions;
   - `presOut0` (type I) and `presOut1` (type E) conclude.

   This is the classical step "R∞ completed at a nice prime has tangent dimension ≤ dim S∞, so the full-dimensional
   patched support fills the unique component". Bodies **[N]**.
6. **The abstract chain argument.** `chainAbs` **[N body]** combines (4) and (5) along a chain of points, using:
   - `nonssT`, which transfers thickness to the patched ring;
   - `patchedModule_annihilator_le_comap_iff_ideal_le`, under which Ann(X) corresponds to J.

   The result is `ChainConcl`.

**What plays the role of the patched module.** At level N the module is `TWRing.M`, the Λ-adic ordinary forms on
U(I_n) at Iwahori-type level at the Taylor–Wiles places. Freeness of M over the diamond-operator ring
S∞/((1+X)^{l^{a_j}} − 1) is a field of `TWRing` (`e : M ≃+ (Fin rk → Sinf ⧸ delIdeal)`). It is *hypothesis data* for
`PfromAut`. It is *produced* in §4 from `LevMod.proj`: the forms invariant under the pro-l Iwahori subgroup are
**projective over Λ[Iw/Iw₁]**, proved via neatness.

**Answer to B.** Yes, there is an actual patching construction:
- Lim, ultrafilter (`PM/ThetaCoefficientMapEq.lean:265`, `AD/Imports.lean:5`);
- the patched module free over a power-series ring, and support of full dimension (`S5`,
  `PM/PatchedSupportCompletions.lean:30-70`, proof `AD/AnnBc.lean`);
- the local dimension argument (`GalOut`, `PM/PatchedSupportCompletions.lean:149`, `AD/GalOut.lean`).

There is no explicit Auslander–Buchsbaum or depth computation in what I read. Dimension and support are compared
directly (`dim`, `fib`). Freeness and balance over diamond operators are proved in §4 from neatness at v₀. That is the
elementary definite-group argument.

Sizes: `PM/` has 441 files and 50,353 lines (frontier-g). `AD/` has 15 files and 1,208 lines. The helper directories
under `PM/` (`AnnihilatorBaseChange` 5.1k, `SelmerScaling` 7.1k, `SeparableMatrixStability` 5.4k, `DeterminantPadicFree`
6.3k, `NilpotentLevelLowering` 5.7k, and others) account for the rest.

---

## 3. Hida theory: `HidaUAlt` (question D)

### 3.1 Statement (`DTC/HidaU.lean:12`) **[S]**

For all l, CM L, `HidaSetting`, V with S' = S and ζ_l ∉ L; for all coefficient rings c that are `Large` (they contain
every embedding of O_L); for all n ≥ 1, r, B, Λ (the universal weight ring `LamObj r`) and ι:

  ∃ J, `B.HidaPropsAlt ι J Λ ∧ Pa.HasAut B J`.

`HidaPropsAlt` (`DTC/PointTheoremBaseObject.lean:32`, and `WGC/ArithmeticPointClassicality.lean`) **[S]** has these
fields:
- `ring` (`RingProps`), which contains:
  - `fin`: B/J is finite over Λ;
  - `tf`: B/J is Λ-torsion-free;
  - polarity;
  - O1–O3: ordinary and inertia relations hold modulo J;
  - `types` at St;
  - `unr0`: unramified at v₀ when the residual representation allows it.
- `dense`: arithmetic points of regular weight are Zariski-dense in V(J).
- `pt` (`PointTheoremBaseObject`): an ordinary automorphic point with a flag and N1-type regularity, unramified at v₀,
  lies in V(J). **Stated only for 2 ≤ n ≤ 4.**
- `end1`: purity of arithmetic points in V(J).
- `end2` (`arithmeticPointClassicality`): an irreducible arithmetic point in V(J) is automorphic (`IsAutCsd`).
- `twist`.

### 3.2 Where it is proved

`UpperTheory.V.Hi.hida_unitary_of_printed_hida : HypothesesH' → HidaUAlt` (`DTC/THidaU.lean:38`, 49 lines) **[P]**.
Its proof:
- `nonempty_unitaryHeckeData` (`DTC/HdEx.lean:20`) **[P]**. It builds `UnitaryHeckeData`, consisting of:
  - an integral type τ₀ at St (`exists_integral_type_for_residual_rep`);
  - a Λ-valued torus character θ with `IsTheta` and `IsWt` (`exists_theta_is_weight_of_lam_obj`,
    `DTC/TThetaEx.lean:160`);
  - Hecke eigenvalues a residually matching r (`exists_is_res_of_residual_rep_and_type`).
- `exists_hecke_ideal` gives J with `IsJ`. `IsJ` (`HA/IsTheta.lean:46`) **[S]** has two cases:
  - either there are no ordinary forms (MK = ⊥) and J = ⊤;
  - or J = ker(B ↠ T_K), where T_K is the Λ-adic ordinary Hecke algebra on MK and B → T_K classifies the
    Hecke-valued Galois determinant (`IsMap` / `IsUniv`).
- `ring_props_of_is_j_unitary_hecke_data`, `dense_of_is_j_unitary_hecke_data` (`DTC/TJDense.lean`) **[P-skel]**,
  `hecke_ideal_point_properties`, `decomposition_and_automorphicAway_of_isJ` (end1 and end2), and `twistOk_of_isJ`.
- `has_automorphy_of_statement` (`DTC/THasAutOf.lean:19`) **[P]**. It feeds `level_of_is_j_unitary_hecke_data`
  (`DTC/TLevelU.lean` → `level_of_isJ_unitaryHeckeData`, `DTC/BaseObjectHomExt.lean:129`) **[P-skel]**.

### 3.3 The group and the forms

The `HSet` is `hset Q τ₀` (`HA/IsTheta.lean:123`) **[S]**:
- Γ = `ratU L n`, the L-rational points of `UA L n = U_J(conjAd, 1)`
  (`AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BaseChangeDefiniteUnitary.lean:71-84`). This is the
  unitary group of the *standard hermitian form I_n* for L/L⁺, so it is definite at every infinite place.
- The level is `Ub`: maximal compact at St, `Kc(v₀, 1)` at v₀ (the principal congruence subgroup, which gives
  neatness), and maximal compact away from S'.
- `Wp` is the set of split unramified places carrying spherical Hecke operators.

The Λ-adic forms (`HA/ContinuousTorusCharacter.lean:151-233`) **[S]**:
- `Frame.Amb` is the set of functions f on G(A_f^l) × ∏_{v|l} GL_n(L_v) with values in A^m that are:
  - left G(ℚ)-invariant;
  - right invariant under the unipotent N of the Iwahori;
  - transformed by θ⁻¹ under the torus T;
  - continuous.

  These are Hida's measure-style Λ-adic forms on a definite group.
- `Ord` is the ordinary part, defined by lim U_z^{n!} (the e-operator).
- `MK` is the localisation at the eigenvalues a.

### 3.4 Freeness and finiteness over Λ

`hiComm` (`HA/OrdinaryHeckeCharacters/HiComm.lean:218`) **[S]** says the ordinary part is Hecke-commutative, finite
and **free over Λ**, and so is each localisation MK. It comes from `ordFree` (`HA/OrdinaryHeckeCharacters/OrdFree.lean:441`,
481-line file) **[N body]**, given:
- `FinLevel`: finitely many double cosets;
- `Free`: stabilisers act through the centre and θ.

`Free` follows from `Neat` (`th_free`, `DTC/TThetaEx.lean:153`) **[P]**. `HA/OrdinaryHeckeCharacters/` has 110 files
and 16,592 lines.

### 3.5 Control and classicality

Density of classical points and "J-points are automorphic" come from:
- `core_hecke_of_automorphic_hecke_dense_weight` (namespace `UpperTheory.V.Z.Ord`) **[N]**;
- `arith_good_iff_hset_of_theta_incr_weight`;
- `isDomain_and_denseWt_of_isTheta`.

I did not open the control theorem itself: the comparison of a Λ-adic specialisation with classical
weight-λ ordinary forms.

### 3.6 Answer to D

Hida theory is formalised *for the definite unitary group U(I_n) over any CM L, any n ≥ 1, with l split in L/L⁺*:
- freeness and finiteness over Λ = O[[n·[L⁺:ℚ]]] via neatness (located, body unread);
- the Λ-adic Hecke algebra and its Galois determinant (`IsMap`);
- density of classical points (`dense_of_is_j…` **[P-skel]**, core lemma **[N]**).

The point theorem `PT` (classical automorphic ⇒ in V(J)) is restricted to n ≤ 4.

### 3.7 From Hida data to `HasAut`

`HasAut` comes from `Level B J` (`PM/Classical.lean:99`) **[S]**: a `TWBase` b (the level-0 module, free and finite over
Λ with Supp = V(J)). For every Taylor–Wiles place set it also gives a `LevMod`, which has:
- a Hecke algebra R with a Galois determinant mapping to B;
- a module P with a ∏_j GL_n(L_{w_j}) action;
- (P)^{Iw₁} finite over Λ and **projective over Λ[Iw/Iw₁]** (`proj`);
- (P)^{GL_n(O)} ≅ b.M (`eM`);
- `Classical`: P is detected by classical points with local–global compatibility at the w_j (`LevPt.lg`).

Then `has_automorphy_of_statement` uses the local Langlands correspondence for GL_n (`LocP`: LLC, Bernstein–Zelevinsky,
geometric lemma, tame) and `locDataT_alt`, `opOf_alt`, `opTransport`, `opToTW` **[N bodies]**. It turns these into the
`TWRing` and `TWMaps` patching data: the U_ϖ eigenvalue decomposition at the Taylor–Wiles places, with the factor `fEl`.

---

## 4. Answer A: `PfromAut` with every hypothesis, and where the classical weight sits

| classical ingredient | status in the archive |
|---|---|
| Residual adequacy / big image | **Absent as a hypothesis on r.** It is replaced by conditions on the *points*: TypeI (absolutely irreducible on G_{L(μ_{l^∞})}), `NP.span` (Burnside spanning) and N3. The dual-Selmer detection is proved (`Det.detAsm`, 268 lines, **body unread**). Only l ≠ 2 and ζ_l ∉ L are used. Published (ANT Thm 1.1): l > 3, l ∤ n, constituents irreducible on G_{F(ζ_l)}, primitive, no quotient of order l, Schur. |
| Existence of Taylor–Wiles primes | **Proved**: `arPl` (Chebotarev), `choice`, `detection`. Classical Taylor–Wiles needs the dual Selmer group killed: here B1 is proved from `CohP` plus detection, at nice points rather than residually (as in SW/Thorne). |
| Dimension bound on the reducible locus | **Not in `PfromAut`.** It is in the linking (§5): `Frame.Big C₀` (Σ_v d_v > 3C₀ + 7 and each d_v > 5, where C₀ bounds residual H¹ dimensions) and `krull_dim_lt_of_not_le_triangular`, giving reducible locus < n·d. This is Skinner–Wiles's base-change-to-large-degree device. ANT instead use a Steinberg place v₀. |
| Local conditions at l | Ordinary with varying weights: `Pair.Ord`, `Point.flag`, and N1 regularity (ψ_i ≠ ψ_j, ψ_i ≠ ψ_j·ε). Expected dimension 1 + n[L⁺:ℚ]: `DimT` and `LocCFT`. The tangent bound D₀ = n[L⁺:ℚ] + nq is proved (`b1Ar`). |
| Local conditions at ramified places St | Inertia acts through the residual characters (`Ip`, `Resid.Ip = Iu ∩ ⋂ ker χ̄_i`), with a matching automorphic type τ₀. This is a minimal-type condition. |
| Auxiliary place v₀ | `HidaSetting.v0` (split, N(v₀) = p odd, p ≠ l) gives a neat level `Kc(1)`. N4 on points is H⁰(G_{v₀}, ad ρ(1)) = 0. In use, all points satisfy N4 (`n4Of`, `CDS/EveryPointSatisfiesFrameConditionAlt.lean:142` **[N body]**). |
| Galois cohomology | `CohP` (an 8-field hypothesis bundle), discharged from `LiteratureRankNHypothesis` (frontier-d says proved). |
| Potential automorphy / soluble descent | **Not in `PfromAut`.** In the overall argument there is base change to the auxiliary L (`GalLink`, `Frame`) and descent back (`downCsdK`, `solvable_descent_of_printed_hida` **[N]**). Seeds over L are automorphic by construction (adjoint lifts). No Khare–Wintenberger potential-automorphy step was seen. |
| l > bound(n) | **Absent** (l ≠ 2 only). Determinant laws (Chenevier) avoid the usual l > n requirement for pseudocharacters. |
| Residual automorphy | In `PfromAut` it is a hypothesis on points (a modular nice point, or a stable modular prime). It is supplied by seeds (§5). |

**Where the weight sits.** It is shared between three places:
1. `Det.detAsm`: detection without adequacy, at the generic point;
2. `GalOut` / `pres` / `presOut0/1`: local smoothness and uniqueness of the component at a nice point;
3. the Hida/`Level` construction of `TWAut`.

All three are in-archive.

---

## 5. Linking and seeds (the connectedness argument)

### 5.1 Where `ModUAlt` is used

`linked_endomorphism_dense` (`DTC/LinkedEndE.lean:18`) **[P-skel]** calls `twoRuns_alt` (`DTC/TwoRuns.lean`, 110
lines) **[P]**:
- For n = 2 and n = 3, `modularity_linked_ends` (`DTC/PrLinkedEnd.lean:22`) **[P]** applies `hMod : ModUAlt` to the
  `CReal` data R (R.s, R.V, R.r with **n ∈ {2, 3}**). It returns J with `ModIn J`. The ModIn fields are:
  - finite over Λ;
  - `DimT`: minimal primes of dimension 1 + n·d (via `dimOf` and `degEq`);
  - `Unr0`;
  - all points satisfy N4;
  - P1core and P3core;
  - a seed point.

  It also returns classicality.
- `absMain` (`CDS/AbsMain.lean:12`) **[P]** applies:
  - `components_good_rank_two` (`CDS/ComponentsGoodRankTwo.lean:129`) **[S]**;
  - `components_good_rank_three` (`CDS/PropagationTheoremGL3.lean:213`) **[P-skel]**.

  Their statements: under `Frame.Ok C₀` and `Frame.Big C₀`, with `FinLam M`, `P1'` (transferred P1core), `P23'`
  (transferred P3core along `ThickLink` chains) and `SeedIn`, the conclusion is `AllGood`: every prime with an
  irreducible (TI) representation contains M. For n = 3 this needs the n = 2 result first, through `l53`.
- `goodPtOf` then converts the result into `GoodPt J`: every characteristic-0 lift that is absolutely irreducible gives
  a point of V(J).
- `autPtO_alt` gives automorphy via classicality and `glueN`. The latter glues two choices of v₀ with coprime p,
  removing the v₀ condition.

### 5.2 Ingredients of the rank-3 propagation (`gd_ok`, `CDS/PropagationTheoremGL3.lean:150`) **[P-skel]**

- **`exists_nice_prime_above_of_large_dim`** (`CDS/ExistsNicePrimeAboveOfLargeDim.lean:7`) **[P]**. A prime of
  dimension ≥ n·d contains a nice prime: characteristic l, dimension 1, not triangular, with distinct ordinary
  characters. It uses `krull_dim_lt_of_not_le_triangular` (the reducible/triangular locus and each coincidence locus
  have dimension < n·d, **using `Big`**) and `nicePrimeEx`, a prime-avoidance lemma for dimension. **This is exactly
  the Skinner–Wiles step.**
- **`preconnected_rank_three`** (`FSV/ExistsNonzeroLowCocycle.lean:144`) **[P]**. The locus BB (reducible-shape
  primes on the special fibre that are not "ee") is nonempty and preconnected, and lies in the closure of its
  non-"ee" part. The proof joins any point to a base point p₀ by explicit **lines**: polynomial families y + X·b of
  low cocycles (`line`, `at_res`). These come from nonzero twisted cocycles that exist under `Frame.Ok` (f4 and f4′:
  H¹(Ψ⁻¹δ) ≠ 0 and H¹(Ψ⁻²δ) ≠ 0). This is the archive's connectedness argument. It is a direct path-connectedness
  argument in the space of extensions. It is *not* Hartshorne's connectedness-dimension theorem as used in SW, Tho15
  and ANT. The sizes of BB and its relation to thick primes (`sharp3`, `l53`, `jac`, `chart_ex`, `globProp`) are
  **unread**.
- **`seedpt`**: a seed component of dimension 1 + 3d contains a nice point. `SeedIn` asks for a TI prime ξ and a prime
  Z ⊇ M of dimension 1 + n·d below it.

### 5.3 `Frame.Ok C₀` (`FSV/ContinuousCoboundaries2.lean:176`) **[S]**: the residual hypotheses actually used

- l ≠ 2, and finite coefficients;
- Ψ(c) = 1 and Ψ(g₀)² ≠ 1;
- f2: ω·Ψ^{±1} ≠ 1 and ω·Ψ^{±2}·δ ≠ 1 on G₀;
- f3: Ψ² nontrivial at each v | l;
- f4, f4′: nonzero H¹ for Ψ⁻¹δ and Ψ⁻²δ;
- f5: ω is not a power of Ψ;
- `gen`, `cl` (local generation and class-group conditions), and the Euler-characteristic inequality `ec`;
- bounds b1, b1p, h1 ≤ C₀ on residual H¹ dimensions.

`Big C₀`: 3C₀ + 7 < d = Σ_v d_v, and d_v > 5 for every v. These are hypotheses about the *specific* residual
representation Ψ ⊕ 1 ⊕ Ψ⁻¹ (and its n = 2 analogue) over the auxiliary L. They are stronger and more concrete than
anything in `PfromAut`.

### 5.4 Seeds

`UnitaryThreeAutomorphyDense` (`DTC/SymUse.lean`) **[S]**: for arbitrarily large m ≡ j (mod l − 1) there is an
automorphic r : G_L → GL₃ that is irreducible on open subgroups, with residual (ω^j χ′, 1, (ω^j χ′)⁻¹) and weights
(m, 0, −m). It is proved by `unitary_three_automorphy_dense_of_prints` → `adjoint_lift_from_eisenstein_of_propagation`
(`prop_eg_w_of_printed_hida`, GL₂ Hida/Eisenstein propagation) and `adjoint_automorphy_w_of_printed_hida_window`
(adjoint lift plus weight compatibility) **[P one line each; bodies N]**. `seedPtOf_alt` (`DTC/PrSeedPtOf.lean:255`)
**[N body]** turns these into `IdealSpecializationPoint J`.

### 5.5 Top-level users (from frontier-g, unchanged)

- `automorphyUnramified_of_locPrints_kisin_gdEnd` (`DTC/AutomorphyU3OfEndoscopy.lean:27`) **[P, frontier-g]** applies
  `AutEnd3Alt` to each type-I point after conjugating it into an `OrdPt` over a DVR.
- `ends_u_alt` (`DTC/DnEnds.lean:40`) **[P-skel, frontier-g]** combines `LinkedEndEAlt` (above) with descent from L to K.
- `OneCharU` (`…/AdmissibleUnitaryThreePoint.lean:116`) **[S, frontier-d]** consumes the result as `AdmI`.

Sizes: `CDS/` has 89 files and 13,495 lines. `FSV/` has 209 files and 21,891 lines.

---

## 6. Answer C: the regime of use

`PfromAut` and `HidaUAlt` are stated for all n. But `ModUAlt` is applied only in `modularity_linked_ends` with
`R : CReal k c₁ f n ka`, whose field `n23 : n = 2 ∨ n = 3` restricts it (`CDS/EveryPointSatisfiesFrameCondition.lean:37`).
The instantiation, from `DTC/TwoRuns.lean` and `DTC/PrLinkedEnd.lean`:

```lean
obtain ⟨J, hJ⟩ := hMod l L Ω R.s R.V R.hV hμ c₁ hL n hn R.r R.B₀ Λ ι   -- n = 2 or 3
-- R.r : Resid V.frame c₁.O n, with ρ.ψ v i = Ψ^{w n i} ∘ k.j (from GalLink, Ψ = Chr.Psi l e ψ)
```

So the regime is as follows:
- n ∈ {2, 3};
- the residual representation is a twist by ka of (Ψ^{w(i)})_i with Ψ = ω^e·ψ, restricted to an auxiliary CM field L
  chosen through `GalLink` / `Frame` with `Ok` and `Big`;
- ζ_l ∉ L (`degEq` gives hμ);
- l odd. In the U(3) `CountI` application, l ∉ `Bchi` ∋ 3, so l ≥ 5. Elsewhere (GSp4, `CountV`) other routes are used
  (`ThmS6`).

The weights are all ordinary weights (Hida families). l is not bounded below in terms of the weights, which is
standard for ordinary arguments.

So the general-n lemma is only *used* at n ≤ 3 for one explicit residual shape. But even at n = 3 with three distinct
characters, the archive's hypotheses do **not** coincide with ANT's:
- ANT needs a Steinberg place and l ∤ n (l ≠ 3, satisfied in CountI);
- each 1-dimensional constituent is trivially irreducible;
- "primitive / no quotient of order l" is not obviously imposed here.

The archive replaces ANT's Steinberg device with the Skinner–Wiles degree trick (`Big`). That device is published
only for GL₂ (SW99) and in Thorne's settings. Whether it suffices for U(3) with three characters is the expert
question. The archive's answer is a proof, and that proof is Lean-checked.

---

## 7. Answer E: could the statements be weaker than they look?

- **Niceness does not involve automorphy.** `NiceI`, `NiceE`, `IsStable` and `IsThick` are purely Galois-theoretic
  **[S]**. P1core *assumes* that the nice point is modular, which is the correct shape.
- **Is `N4` vacuous?** `D0` is the decomposition group at v₀, not ⊥, so N4 is the standard H⁰ condition and is
  satisfiable. In use, `n4Of` proves it for all points.
- **`IsJ` allows J = ⊤** when there are no ordinary forms. Then P1core and P3core hold vacuously and `GoodPt` would
  fail. The argument avoids this because `PointTheoremBaseObject` plus the existence of seeds forces J ≠ ⊤
  (`IdealSpecializationPoint`). So non-vacuity rests on the seeds **[P-skel]**.
- **`B`, `TWAut` and `Lim` are inputs, not constructions.** If no `UniversalOrdinaryDeterminantRing` existed, the
  ∀-statements would be vacuous. But `b0Ex` constructs one, `HidaUAlt` produces `HasAut`, and `s4` produces `Lim`.
- **Points have finite residue fields** (K[[t]] with K finite). That is the normal form of a dimension-1
  characteristic-l prime, so it is not a restriction.
- **Hypotheses with only trivial instances.** I found none. `Big` needs [L⁺:ℚ] large. That is achievable by
  soluble base change, which is what `GalLink` / `Frame` encode **[N for construction]**.
- **`PT` is restricted to n ≤ 4**, and the final automorphy needs irreducibility on all open subgroups. Both are
  honest restrictions, not hidden weakenings.
- **Residual case.** Residually, only "sums of distinct characters" is covered (`chib_inj`). Higher-dimensional
  irreducible constituents are not handled. This makes the general-n lemma narrower than "every residual
  pseudo-representation", though still beyond the n = 3 literature in the absence of a Steinberg place.

---

## 8. Answer F: what remained unread, in priority order

1. `UpperTheory.V.Pa.Det.detAsm`, `Det.detFr`, `isKap` (`PM/DeterminantPadicFree/DetAsm.lean`, 268 lines): detection
   without adequacy. This is the main check against Thorne-style adequacy and the "no quotient of order l" condition.
2. `UpperTheory.V.Fr.krull_dim_lt_of_not_le_triangular`, `Fr.l51` (`FSV/`), `Pr.nicePrimeEx` (`CDS/NicePrimeEx.lean`):
   the reducible-locus dimension bound from `Big`.
3. `Fr.preconnected_rank_three` support lemmas (`at_ex`, `at_uniq`, `exists_nonzero_low_cocycle`), plus `Fr.sharp3`,
   `Fr.l53`, `Fr.seedpt`, `globProp`, `GlobOfCharts`: the connectedness argument.
4. `Pa.s6` (`AD/S6.lean`), `pres`, `presOut0`, `presOut1`, `discImp` (`PM/SelmerScaling/`): local structure at a nice point.
5. `Pa.pmodEx`, `s5_lemma`, `patchedModule_free_finite_over_iwasawaAlgebra`, `freeN`, `chainAbs`, `nonssT`
   (`PM/AnnihilatorBaseChange/`, `AD/AnnBc.lean`): patched module and support.
6. `Pa.b1abs`, `arSys` (`PM/EpsilonEtaMatrices/`, `PM/DegreeCountCohomology/`), `obstructionBound_of_duality`
   (`PM/ArchimedeanH0Cards/`): the Greenberg–Wiles Selmer and obstruction bounds at nice points.
7. `Hi.ordFree` (`HA/OrdinaryHeckeCharacters/OrdFree.lean`), `Z.Ord.core_hecke_of_automorphic_hecke_dense_weight`,
   `decomposition_and_automorphicAway_of_isJ`: Hida freeness and the control/classicality theorem.
8. `Pa.Lev.opOf_alt`, `opTransport`, `opToTW`, `Z.Win.locDataT_alt`, `Hi.levelUR2ModPack_alt`, `Hi.s4` (in
   `BaseObjectHomExt`): the local analysis at Taylor–Wiles places and the projectivity over Λ[Iw/Iw₁].
9. `Pa.norm` (`AD/ConjugationDescendsToSubring.lean`, 323 lines), `selmer_cocycles_limit_and_descent_properties` (the
   ultrafilter limit).
10. Seeds: `adjoint_lift_from_eisenstein_of_propagation`, `prop_eg_w_of_printed_hida`, `Pr.seedPtOf_alt`; plus
    `Pr.n4Of`, `Pr.degEq`, `W.b0Ex`.
11. The provenance of `CohP` fields (`LiteratureRankNHypothesis.coh`), to confirm they are proved theorems.

## What to read next

**Expert first, at Lean depth.**
1. Item 1, detection. Compare it with Thorne 2012 adequacy and with ANT hypothesis (vii) ("no quotient of order l").
2. Items 2–3: is `Big` plus `preconnected_rank_three` a valid substitute for ANT's Steinberg-place control of the
   reducible locus, for U(3) with residual Ψ ⊕ 1 ⊕ Ψ⁻¹?

**Then.**
3. Item 7: the Hida control theorem.
4. Item 4: the local smoothness at nice points.

**Reference.** ANT 2020 (Compositio 156, arXiv 1912.11269), Theorem 1.1 hypotheses (i)–(viii) and Prop. 5.3, were
checked by web search for this comparison. Thorne 2015, Theorem 7.1, and SW99 were not re-read.
