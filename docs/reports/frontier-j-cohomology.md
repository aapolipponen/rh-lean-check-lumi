# Frontier (j): étale cohomology foundations, the Hodge–Tate comparison, and the categorical crystalline H¹

Date: 2026-11-21. This is a read-only source study of `/bulk/shared/rieman/lean/src` on chili. Nothing was compiled or
run. About 85 ssh reads (cat/sed/grep/awk over the source and the declaration index). It extends
`frontier-c-galois.md` (Q1, Q7.5) and `frontier-g-deep-inputs.md` (§I.3), and answers the open item in
`statements-review-3-geometry.md` §4 about the categorical H¹.

Path abbreviations (relative to `src/`):
- `ET/` = `Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCohomology/`
- `ES/` = `Development/EtaleCohomology/EtaleSheaves/`
- `DP/` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/`
- `DD/` = `Development/AbelianVarietyTheory/Definitions/Divisors/`
- `PHC/` = `Development/WeilBound/CoreStatements/PadicHodgeComparison/`
- `ECC/` = `PHC/EtaleCohomologyComparison/`
- `KL/` = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/KunnethLefschetz/`

Tags: **S** statement read; **P** proof read; **P-skel** proof term or have/obtain skeleton read, not every line;
**N** inferred from names, imports or the shape of a statement only.

## Overview

The archive builds étale cohomology as a small axiomatic theory and then proves the axioms. It defines cohomology
with ℤ/q coefficients on Mathlib's big étale site as Ext from the free sheaf on a simplicial presheaf to an
injective resolution. It then states about 35 basic and deep properties as named Props (`GlobalTheory.EtC.A1`…`E8`)
and proves most of them. The "~15 ingredients" of proper base change are the fifteen fields of the hypothesis
structure `t_E2Cut.Hyp`. Each is a property of this cohomology (quasi-isomorphism invariance, Čech descent for
smooth and for integral surjections, vanishing on strictly henselian and on absolutely integrally closed (AIC)
rings, Gabber's affine analogue, and others). Each is discharged by a theorem, via the usual `…Statement` wrapper.

Proper base change (`EtC.E2`) is the theorem for a proper X over a strictly henselian local ring with coefficients
μ_q^{⊗i} (constant twisted coefficients only). Its proof is a long explicit skeleton:
- descent along integral surjections to AIC schemes;
- a Chow-lemma reduction to towers of integral maps and relative ℙ¹'s;
- Stein factorization;
- explicit H⁰/H¹/H^{≥2} computations on relative lines;
- noetherian approximation.

Gabber's affine analogue (`E1`) enters as one hypothesis. Finiteness (`E4`), smooth base change in the form
"generic fibre over an AIC local domain" (`E3`), purity (`E6`) and rational Poincaré duality (`QDual`) are also
proved. The mod-q Poincaré duality chapter `E8` is stated but never discharged, and the path that is actually used
does not need it.

The Hodge–Tate comparison (`HTSpecGood`) is the full Hodge–Tate decomposition for smooth projective X over O_K, in
all degrees, Galois-equivariant (with the χ^a twist), natural, multiplicative and Chern-compatible. The comparison
map is built from étale cohomology into a home-made "A_cris-cohomology", meaning the cohomology of the category of
perfectoid AIC points of X over O_C. That target is then sent to Hodge cohomology via θ. Bijectivity is not proved
by almost purity. It comes from a formal argument:
- Poincaré duality and top-degree Chern classes give injectivity;
- Künneth and the diagonal class give the dimension count.

This is closest to Faltings' or Niziol's "comparison map + Poincaré duality" strategy, with perfectoid test objects
in the style of Bhatt–Morrow–Scholze or Bhatt–Mathew. It is not Tate's p-divisible-group route.

The categorical H¹ over nilpotent PD thickenings is compared with standard cohomology twice:
- `crystallineSmoothLift_of_relations` proves categorical H¹ and H² ≅ Čech hypercohomology of the de Rham complex
  of a smooth lift, naturally and compatibly with cup products;
- `hodge_iso_natural_cech` proves the categorical Hodge groups ≅ sheaf cohomology H^j(X, Ω^a) over fields of
  characteristic 0.

Both proofs are P-skel at most. If they hold, they would be first formalizations: of proper base change, of
ℓ-adic Poincaré duality and finiteness for smooth projective varieties, and of a p-adic Hodge–Tate comparison
theorem.

---

## I. The étale cohomology development

### I.1 Definition (**S**)

`DD/GalMapMul.lean:82–131, 183, 252–263`; `DD/PullHlComp.lean:44–70, 205–251`.
- `Shv R := Sheaf Scheme.etaleTopology (ModuleCat (ULift R))`: Mathlib's big étale site on `Scheme.{0}`. The
  archive proves it is Grothendieck abelian, so injective resolutions exist.
- `Spc := SimplicialObject (Schemeᵒᵖ ⥤ Type)`, and `sch X` is the constant simplicial object on the Yoneda
  presheaf. `chains E` is the alternating face complex of the free sheaves.
- `H R E F n := CohomologyClass (chains E) (res F) n`, i.e. Ext^n(ℤ[h_X], F) for E = `sch X`. That is cohomology of
  the big étale topos restricted to X, which agrees with small-site cohomology by a standard fact; the archive does
  not need this fact, since it never uses Mathlib's small étale site.
- `Eqv f F := ∀ n, Bijective (pull f F n)`: "f induces an isomorphism on all cohomology".
- `tw q i` is the sheafification of A ↦ ℤ/q[primitive q-th roots of A]/relations, i.e. μ_q^{⊗i} where q is
  invertible. `Ht q E n i := H (ZMod q) E (tw q i) n`.
- `Hl l E n i` is the ℤ_l-module of compatible systems (x_k ∈ Ht (l^k)) under the reduction maps, and
  `HQ := ℚ_l ⊗ Hl`. So H^n(X, ℚ_l(i)) = (lim_k H^n(X, μ_{l^k}^{⊗i})) ⊗ ℚ_l. This is the naive limit, not
  continuous/Jannsen cohomology. For proper X over a separably closed field, finiteness (E4) makes the two agree.
- **Galois action** (`DD/PullHlComp.lean:246–255`, `…/GaloisGeometry/IsMatrixForm.lean:67–79`) **S**:
  `galMap σ : X_Ω → X_Ω` is the base change of Spec σ, and `galHl`/`galHQ` are the representations
  σ ↦ pull(galMap σ), with map_one and map_mul proved. Continuity was not looked at here: **undetermined** at this
  level.

### I.2 The list of properties (**S**, `DD/DivisorSupportCondition.lean`, 161 lines)

Paraphrases. Below, "iso" means `Eqv`, and twisted coefficients are tw q i with q invertible.

| Prop | Content |
|---|---|
| A1 | quasi-isomorphic complexes have the same hypercohomology |
| A2 | Čech descent along smooth surjections, for any sheaf |
| A3 | levelwise isos of simplicial objects give isos |
| A4 | Mayer–Vietoris / two-member covers |
| A5 | positive-degree classes die on some étale surjective cover (effaceability) |
| A7 | long exact sequence in the coefficients |
| A8 | invariance under change of coefficient ring |
| A9 | negative degrees vanish; H⁰ = sections, naturally |
| A10 | a sheaf map bijective on sections over the support gives cohomology isos |
| A11 | reduction ℤ/Q → ℤ/q is compatible with cup, unit and c₁ |
| B1 | continuity: H of a filtered colimit of rings = colimit of H |
| B2 | strictly henselian local rings are acyclic, for every sheaf |
| B3 | an iso can be checked after base change to strict henselizations |
| B4 | Čech descent along integral surjective morphisms, for tw q i |
| B5 | AIC domains are tw-acyclic |
| B6h1, Pic | H¹(Spec A, 𝔾_m) = Pic A; an H¹ vanishing criterion |
| B7 | over a field, H = Galois cohomology of the separable closure |
| C1, C2 | cd ≤ 1 for function fields of curves over k = k̄ and for affine Dedekind k-algebras |
| C3 | ind-étale-over-polynomial base change from T to Frac T (T an AIC local domain) |
| C4 | homotopy invariance A → A[x] |
| C5 | Laurent polynomials over strictly henselian A: H^{≥2} = 0, H¹ = ℤ/q |
| D1 | projective bundle formula |
| D2 | Chern classes with Whitney sum and normalization |
| D3 | slant products with group homology |
| E1 | **Gabber's affine analogue of proper base change**: for a henselian pair (A, I), Spec A/I → Spec A is an iso on H(−, tw q i) |
| E2 | **proper base change**: A strictly henselian local, p : X → Spec A proper; the closed fibre X₀ ↪ X is an iso on H(−, tw q i) |
| E3 | **smooth base change / local acyclicity**: T an AIC local domain, X → Spec T smooth; X_{Frac T} ↪ X is an iso on H(−, tw q i) |
| E4 | **finiteness**: X proper over k = k̄; every Ht q X n i is finite |
| E6 | **semi-purity**: for a smooth pair Z ⊂ X of codimension d, H^n(X) → H^n(X∖Z) is bijective for n < 2d−1 and injective for n < 2d |
| E8 | **Poincaré duality** mod q: H^{2d}(X, μ_q^{⊗d}) ≅ ℤ/q and the cup pairing is perfect, for X smooth proper integral over k = k̄ |

`Development/EtaleCohomology/EtaleSheaves/EtaleChapterE{One,…,Eight}.lean` package them as
"A1 → … → D3 → E1 → … → E_k". The development is written as chapters, each conditional on the earlier ones, and
the conditions are then discharged.

### I.3 Proper base change, `UpperTheory.Et.proper_base_change : EtC.E2` (**P-skel**)

`ET/AffineProperBaseChange.lean:29` (32 lines):
```lean
theorem proper_base_change : GlobalTheory.EtC.E2 :=
  E2.main ⟨quasiIso_hypercohomology_bijective (A1), etC_a2 (A2), levelwiseEquivalence_isEquivalence (A3),
    mayerVietoris_equivalence_of_cover (A4), positiveDegreeClasses_die_on_etaleCover (A5), …LongExactSequence (A7),
    …CoefficientRingInvariance (A8), …NegativeVanishingDegreeZero (A9), …BijectiveOfSupportBijective (A10),
    …TwistedFilteredColimitContinuity (B1), strictlyHenselianLocalRing_acyclic_every_sheaf (B2), etC_b3 (B3),
    integralSurjection_cechDescent_tateTwist (B4), absolutelyIntegrallyClosed_domain_tateTwistAcyclic (B5),
    affine_proper_base_change (E1)⟩
```
**These fifteen fields are "the ~15 ingredient lemmas"**: `LateralTheory.E.t_E2Cut.Hyp`
(`ES/LineHigh.lean:8`, **S**) = A1, A2, A3, A4, A5, A7, A8, A9, A10, B1, B2, B3, B4, B5, E1. Each `GlobalTheory.T.…`
name is a `first | exact @X.foo` wrapper over a sibling proof. Samples:
- `b2` (`DP/StrictlyHenselianLocalRingAcyclicEverySheaf.lean`, 27 lines) **P**: from A5 and the fact that étale
  surjections over a strictly henselian local ring have sections.
- `b4` (`DP/IntegralSurjectionCechDescentTateTwist.lean`, 56 lines) **P-skel**: check stalkwise after base change to
  strictly henselian O, then `eqv_cechAug_of_isIntegralHom_of_surjective_of_sh`, which is unread.
- `classes_die_on_etale_cover : A5` (`DP/PositiveDegreeClassesDieOnEtaleCover.lean`, 67 lines): not read beyond its
  signature.

Two instantiations exist: `ET/AffineProperBaseChange.lean:29`, and
`KL/InFormalGroupPoints.lean:32`, which is misleadingly named `duality_diagonalClass_of_affineProperBaseChange : E1 → E2`
and uses alternative proofs of B2 and B4.

**`E2.main`** (`ET/SpecAbsolutelyIntegrallyClosedCohomology.lean`, 511 lines; skeleton lines ~150–511) **P-skel**.
The skeleton is about 100 one-line `theorem nK : … := …_of …` steps and then:
```lean
theorem main (H : Hyp) : E2 := by
  intro q A _ _ hA hq X p _ i
  refine reduce H n1 n9 q i A hq p ?_            -- reduce to AIC schemes integral over X (Desc, Cover)
  intro Z h hh hZ
  obtain ⟨Z', c, hZ', hdom, hc, hcomp⟩ := e2Cut_chow A h p hh hZ     -- Chow: dominant c with IT c, IT (c ≫ h ≫ p)
  have hT : PB q i (c ≫ h ≫ p) := towers H q i A hA hq (c ≫ h ≫ p) hcomp
  refine (proper_base_change_fibre H q i A hq c (h ≫ p) hZ' hZ ?_).1 hT
  …
```
Its cut lemmas are all **S** in `ES/LineHigh.lean`:
- `IT` is an inductive class of "towers": integral morphisms, closed under composing with `IL` maps (an integral
  map into a proper line, a base change of ℙ¹_ℤ).
- `Desc`: proper base change holds if it holds after integral surjective covers.
- `Cover`: it suffices to know it on AIC schemes.
- `Stein`: an AIC Z → S factors as dominant then integral, with AIC middle term.
- `Chow`: integral AIC Z over a proper X admits a dominant tower Z′ → Z.
- `LineZero`: closed fibres of `IL` maps from AIC schemes are connected.
- `LineOne`: their H¹ vanishes.
- `LineHigh`: H^{≥2} vanishes.
- `IntPB`: the integral case.
- `Fib`: compatibility along dominant maps.
- `Cont`, `MV`, `ZLG`: continuity, Mayer–Vietoris, Zariski local-to-global.
- `AICAcyc`, `QuotAcyc`, `HZero`: AIC acyclicity.

The leaf proofs sit in `ES/` (688 files, 51.6k lines) and are unread, apart from names such as
`cohomology_punctured_affine_line`, `projectiveLine_integers_affine_cover_absolutely_integrally_closed`,
`chow_lemma_projective_cover` and `stein_factorization_relative_normalization`.

**Which classical route.** It mixes the routes. The SGA4 XII skeleton is there:
- Chow's lemma;
- reduction to relative curves (ℙ¹);
- Stein factorization;
- explicit H⁰/H¹ of curves;
- noetherian approximation (`Cont`, `etale_finite_presentation_model_exists`).

It is organized by integral (v-type) descent to AIC schemes, in the style of Rydh and Bhatt–Mathew, and it takes
Gabber's affine analogue (E1) as an ingredient. **N**: no Artin approximation appears by name.

**Strength.** The statement is the classical theorem for **constant twisted coefficients μ_q^{⊗i}**, over a strictly
henselian local base, at the closed fibre. It is not proved for arbitrary torsion sheaves or for R^q f_* commuting
with arbitrary base change. That is weaker than SGA4 XII 5.1 as a statement, but it is the case needed for the
specialization comparison of the smooth proper Kuga–Sato family (`specGood := spSpecIf proper_base_change
etale_base_change_of_duality`, frontier-c Q2). **If the leaves are sound, this would be a first formalization of
proper base change in étale cohomology.** The skeleton looks complete (every hypothesis is discharged by a named
theorem), but the leaves are unread.

**Affine analogue `affine_proper_base_change : E1`** (`ET/AffineProperBaseChange.lean:26`) **P-skel**:
`etaleCohomology_descent_of_cech_cover` (`…/CommutativeAlgebra/EtaleCohomologyDescentOfCechCover.lean:61`) applied
to A1, A9, B1, B2, B4 and five `t_E1Cut` leaves (`EtaleAxioms/{EtaleCovers,HenselianIdempotents,EquivalenceQuasiAffine,DescentSteps,CechLevels}`).
Those leaves are all oddly named `intersectionNumber_baseChange`, a misnomer. The E1 cut files are unread.

### I.4 Finiteness, `UpperTheory.Et.e4 : EtaleChapterEFour` (**P-skel**)

`ET/E4.lean` ⇒ `ET/EtaleTopology.lean:top` (270 lines) is a chain of 133 `have`s. In order:
- H⁰ of twists over closed fields;
- curve étale descent;
- units and Picard of curves (normal proper model built by gluing, `curve_picard_of_selmerPicard_of_modelCurve`);
- Kummer sequence (`LeafKum`, with `DivisorPicardCompatibility` as a hypothesis of the section);
- `CurveThroughGenericPointSpreadsToSmoothProperFamily` (a fibration in curves);
- vanishing in degrees ≥ 2 on stalks;
- strictly henselian neighbourhoods.

This is the Arcata/SGA4 XVI fibration-by-curves route to finiteness, with proper and smooth base change used through
E2 and E3. **Statement** (E4): Ht q X n i is finite for every proper X over k = k̄. That is the full classical
statement for constant twisted coefficients.

What the Galois path uses is `DegFin`/`HtotFin` (`GR/IntegralStructures/GeometricFlagBases/FlagBasis.lean:108–112`,
**S**): for smooth projective X over k = k̄, HQ is finite-dimensional and zero outside [0, N]. The proof is
`degFin (h : KunnethLefschetz.Core)` (`…/GeometricFlagBases/RepMain.lean:65`) via `QDual` (**P-skel**, one line).

### I.5 Smooth base change / specialization, `etale_base_change_of_duality : E3` (**P-skel**)

`ET/N81.lean:260` (298 lines). Its hypothesis is `t_E3Cut.Hyp = A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A9 ∧ B1 ∧ B2 ∧ B4 ∧ C3 ∧ C4`.
The proof inducts on polynomial rings T[x₁…x_n]. The base case is C3; the step uses homotopy invariance C4. It then
reaches all smooth X by étale-local charts (`n78 : Global`).

**Statement:** E3 is local acyclicity of smooth morphisms over an AIC local domain, in "generic fibre ↪ total space
is an iso" form. Combined with E2, this gives H(X_s̄) ≅ H(X_T) ≅ H(X_η̄) for smooth proper X over the AIC hull of
a strictly henselian trait. That is the specialization isomorphism the Eichler–Shimura step needs. It is a special
case (constant twisted coefficients; smooth source) sufficient for the application. The name
`etale_base_change_of_duality` is a misnomer: no duality enters.

### I.6 Purity, duality, Künneth

- **E6 semi-purity** is proved: `UpperTheory.Et.E6.intersectionNumber_baseChange : EtaleChapterESix`
  (`ET/EtaleAxioms/A11.lean`, steps a0–a39) **P-skel**. Its leaves are in `Development/EtaleCohomology/CohomologicalPurity/`
  (202 files, 17.2k lines).
- **E8 (mod-q Poincaré duality) is never discharged.** `ES/CupUnitChernKummerLaws.lean:98` proves
  `EtaleChapterEEight` from extra hypotheses (`EtalePrime`, `LeafStep`). The only other occurrences of `EtC.E8` are
  the `Base` bundle (`ET/A6supp.lean`) and the **unused** alternative
  `HT.hodgeTate_comparison_smooth_projective (h4 : E4) (h8 : E8)` (`ECC/HodgeTateResidues/HodgeTateComparisonSmoothProjective.lean:19`).
  The live path uses `hodgeTate_of_etale_side` instead (see II).
- **Rational Poincaré duality `QDual`** (`KL/OneMul.lean:191`, **S**): for X smooth projective integral of
  dimension d over k = k̄ and l invertible:
  - the HQ are finite-dimensional and vanish above 2d;
  - there is a trace iso V^{2d} ≅ ℚ_l;
  - the cup pairing V^n × V^{2d−n} → ℚ_l is perfect.

  `qDual_holds H.inputs trIn_holds` (`KL/EtMain.lean:42`) **P-skel/N**. `QDiag` (diagonal class) and `Kun`
  (Künneth spanning on X×X) are proved alongside. `KL/` has 142 files, 10.9k lines, and is unread.
  `Core` (`KL/EtSideGood.lean:7`) bundles C2, C3, C4, C5 and D1 and derives D2, D3, E3, E4, `inputs`, `qDual`,
  `qDiag`, `diagEt3`, `etSide_sm` and `etFin`. **If sound, this would be a first formalization of ℓ-adic Poincaré
  duality for smooth projective varieties.** It is stated with ℚ_l coefficients, so it is weaker than the integral
  or torsion form, but sufficient for the use.

### I.7 Sizes

| Area | Files | Lines |
|---|---|---|
| `Development/EtaleCohomology/` (all) | 1,398 | 104,525 |
| — `EtaleSheaves/` (E1/E2/E3/E4 leaves) | 688 | 51,640 |
| — `CohomologicalPurity/` | 202 | 17,247 |
| — `TateTwists/` | 239 | 13,674 |
| — `KummerTheory/` | 98 | 7,807 |
| — `EtaleTrace/` | 70 | 5,035 |
| `ET/` (top-level assemblies) | 79 | 9,869 |
| `KL/` (duality, Künneth, diagonal) | 142 | 10,916 |
| `DP/…Etale*` property proofs | not counted | — |

### I.8 Reachability caveat

`analysis/reach/decl-index.tsv` has no rows for `UpperTheory.Et.E2.main` and `UpperTheory.Et.E2.towers`. Both are
declared after an `open … in` line, which the indexer evidently misses. `reachable-modules.txt` correspondingly
omits `SpecAbsolutelyIntegrallyClosedCohomology`, even though `proper_base_change` (reachable) calls `E2.main`.
Name-level reachability numbers for this area undercount.

---

## II. The Hodge–Tate comparison

### II.1 Statement used on the Galois path (**S**)

`UpperTheory.Gal.Seam.HT.htSpecGood : HTSpecB.HTSpecGood` (`GR/CrystallineTowers/ClosedHT.lean:21`) **P**:
```lean
theorem etSideS : EtSideS := fun l _ K _ => Top.etSide_sm_holds l K
theorem hodgeTate_comparison_smooth_projective : HodgeTateMapExists := hodgeTate_of_etale_side etSideS
theorem htBij : Onto.HTBij := Onto.htBij_of hodgeTate_comparison_smooth_projective G.sqEx3 Top.diagEt3_holds Top.etFin_holds
theorem htSpecGood : HTSpecB.HTSpecGood := Spec.htSpecGood_of htBij Om.Nt2F.hodge_iso_natural_cech Top.etFin_holds
```

**Setting** (`ECC/HarishChandraFormulaStatement.lean:82–115`, `ECC/BocksteinBaseChange/EtSide.lean:15–40`, **S**):
- K is a finite extension of ℚ_l inside ℚ̄_l, and l is the residue characteristic, so this is the *p-adic*
  comparison.
- A `Model` is a scheme X → Spec O_K.
- `M.Sm` = `Good` (projective over O_K and strictly semistable for a uniformizer) ∧ `Smooth M.p`. So the setting is
  **smooth projective over O_K: good reduction**.
- `M.V n := HQ l (X_{ℚ̄_l}) n 0`, with Galois action `galHQ`.
- `Hdg q a n := CH.H (gr^a of the PD filtration on the thickening functor of X_K) n` (`ECC/HodgeTateResidues/IsDlogFirstChernClass.lean:116`).
  This is the archive's *categorical* Hodge cohomology (see III). It is identified with H^{n−a}(X_K, Ω^a) by
  `hodge_iso_natural_cech`.

**`HodgeTateMapExists`** (`…/IsEtaleFirstChernUntwisted.lean:76`, **S**): for every l and K there is an `HTPre`,
i.e. ℚ_l-linear maps h : V^n → Hom_K(Hdg(a,n)^∨, ℂ_l), which amount to V^n ⊗ ℂ_l → ⊕_a Hdg(a,n) ⊗_K ℂ_l. These maps
are:
- semilinear;
- Galois-equivariant up to the twist χ(σ)^a;
- natural in morphisms of models;
- compatible with cup products (`cup`, via the Künneth-type formula on Hodge bases);
- unital (`one`);
- **Chern-compatible**: étale c₁ of a line bundle maps to its dlog class in Hdg(1,2), with zero in the other
  graded pieces.

The fields `fin` and `first_chern_class_exists` are also included. For every smooth M the map is injective in all
degrees (`Inj`) and in top degree (`Top`).

**`HTBij`** (`PHC/HodgeSurjectivity/HtBijOfParts.lean:11`, **S**) adds `Surj P M n` and
dim_{ℚ_l} V^n = Σ_{a ≤ n} dim_K Hdg(a, n).

**`HTSpecGood`** (`ECC/HodgeTateResidues/HodgeTateSpectral/HTSpecGood.lean:15`, **S**): for each smooth M of pure
relative dimension and each degree n:
- there is a frame F with Σ_a e_a = d, the dimension count;
- there is a period matrix Φ(M, F) over ℂ_l satisfying `F.IsHT`;
- Φ is natural: étale matrix · Φ_M = Φ_{M′} · Hodge matrix for every morphism u.

**Assessment.** This is the **full Hodge–Tate decomposition**
H^n_et(X_K̄, ℚ_l) ⊗ ℂ_l ≅ ⊕_a H^{n−a}(X_K, Ω^a) ⊗_K ℂ_l(−a), in every degree n. It is Galois-equivariant (`equi`,
with the χ^a twist), natural, multiplicative and compatible with c₁, for smooth projective X over O_K. Its form as
existence of HT period matrices and the exact meaning of `Frame`/`IsHT` were not read: **N** for the exact
encoding in `HTSpecGood`.

It is not just a statement for abelian varieties. It is weaker than Faltings' theorem in one respect: it needs
**good reduction**, and Faltings does not. The Kuga–Sato application has good reduction at the relevant places, so
this suffices. **If the proof is sound, this is a first formalization of a p-adic comparison theorem.**

### II.2 Route of proof (**P-skel** at the top; mechanism partly **N**)

1. **Étale → A_cris cohomology.** `HT.etP` (`ECC/HodgeTateResidues/FirstChernCocycleAllLevels.lean:117`) builds
   `e = E.eFam … : EtFam l K` with `EtP e` (`…/EtDefs.lean:17`, **S**).
   - `EtFam` (`ECC/KummerCupProducts/IsFirstChernClassOfLineBundle.lean:76`, **S**) is a family of maps
     Ht(l^n)(X_{ℚ̄_l}, j) → `M.MH n j` = CH.H (A_cris/l^n-valued functor on `El M.P`) j.
   - `El M.P` is the category of elements of P = `PX(X/O_K)`: pairs (A, y) with A a test object and
     y : Spec(W(A)/ξ) → X over O_C (`AcrisKummerUnits/GaloisTwistIdentitySection.lean:123–190`, **S**).
   - Test objects are `PAlg` (`ECC/MapWXi.lean:20`, **S**): perfect, π-adically complete, π-torsion-free
     O_C^♭-algebras A. `IsTest` = AIC ∧ `VAL` (a valuation-like idempotent condition). So W(A)/ξ ranges over AIC
     perfectoid rings.
   - The conditions in `Good` (**S**): compatible with reduction mod l^n, Galois-equivariant,
     **φ-invariant** (`Phi`), natural, multiplicative, unital, and c₁-compatible after multiplication by the period t.
   - Mechanism (**N**): pull an étale class back to the perfectoid AIC points, where étale cohomology vanishes in
     positive degree (cf. B5). Represent it by a cocycle over the category of points. Map ℤ/l^n-locally-constant
     functions into A_cris/l^n (`lcMor`/`lcA`/`probe`, `KummerCupProducts/MapUgCToUg.lean:150–170`, **S** for the
     definitions).

   This is an arc/v-descent style construction of the étale-to-crystalline map, in the spirit of
   Bhatt–Morrow–Scholze and Bhatt–Mathew, with Artin–Schreier φ-invariants. **It is not Faltings' almost purity by
   name and not Scholze's primitive comparison.** `ECC/PerfectoidPullbacks/` (173 files, 13.4k lines) is presumably
   where this lives; it is unread.
2. **A_cris → Hodge ⊗ ℂ_l.** `Half2` (`IsFirstChernClassInFamily.lean:188`, **S**) is a family
   γ : (A_cris-families) → Hom(Hdg^∨, ℂ_l). It is θ-linear (`θA`), Galois-twisted, natural, cup-, unit- and
   c₁-compatible. `half2Of` (`HalfGaloisOfCompatible.lean:56`) **P-skel** builds it via `toY` into log-crystalline
   cohomology (`GlobalTheory.LogCris`, `pdOm`) of the integral model, along levels `Lv`, with inputs `crisSurj`,
   `rhoEx`, `coEx`, `homRho`, `homMu`, `mulRho`, `firstChern_hodgeTate_rho` and `kForm`, all unread. This is the
   "crystalline cohomology over A_cris, then θ and gr" half (Fontaine–Messing/Faltings style). It needs an
   identification of the A_cris cohomology of the special fibre with crystalline/de Rham cohomology, and how that is
   done is **undetermined**.
3. **Injectivity, formally.** `ht_of` (`HtOf.lean:30`) **P** then `inj_of` (`SumCoord.lean:252`, unread body)
   combine:
   - étale-side Poincaré duality `EtSide.dual` (`BocksteinBaseChange/EtSide.lean:42`, **S**): vanishing above 2d,
     H^{2d} spanned by Galois-permuted lines, and the cup pairing detecting every functional;
   - `KTop`: the d-th power of the dlog class of a tautological line is nonzero in Hodge top degree
     (`KProps.lean:19`, **S**; proved by `kTop`).

   The argument: x ≠ 0 ⇒ ∃ y with x ∪ y ≠ 0 in top degree ⇒ h(x)·h(y) ≠ 0 ⇒ h(x) ≠ 0. This is the classical
   "Poincaré duality forces injectivity" trick. `EtSideS` comes from `KL/Core.etSide_sm` (rational duality `QDual`,
   see I.6), **not** from E8.
4. **Surjectivity and dimension.** `htBij_of_parts` (`HodgeSurjectivity/HtBijOf.lean`) **P-skel** uses `Parts`
   (Künneth on X×X `kunAff`/`KunGlue.slant`, Čech charts, `RelKill`, `ChartBijOf`), `SqEx3`, `DiagEt3`
   (the étale diagonal class) and `EtFin`. This is the Künneth plus diagonal-class dimension argument.
   `HodgeSurjectivity/` has 53 files, 5.6k lines.
5. **Hodge identification.** `hodge_iso_natural_cech` (see III.2) converts `Hdg` into H^j(Ω^a), which is the
   `hodgeH` used by the holomorphic Lefschetz formula (frontier-g §I.2(a)). So the two halves of the Galois path talk
   about the same Hodge cohomology.

**Which route.** Not Tate's p-divisible groups plus Künneth, and not prismatic. The closest classical model is
Faltings' or Niziol's: construct a natural, multiplicative, Chern-compatible period map (here through perfectoid AIC
test objects and A_cris), then get bijectivity from Poincaré duality and Künneth. The archive's Bhatt–Scholze
statements are elsewhere and not on this path, as far as I saw.

**Sizes.** `PHC/` has 538 files, 50.5k lines:
- `ECC/` 456 files, 42.0k lines: PerfectoidPullbacks 13.4k, BocksteinBaseChange 8.5k, HodgeTateResidues 5.9k,
  CechPairings 3.7k, ZariskiEtaleLifting 3.5k;
- `HodgeSurjectivity/` 5.6k lines.

`GroundTheory/PAdicHodge/` (226 files, 64.3k lines) supplies A_inf, A_cris, θ and the periods; it is unread.

---

## III. The categorical H¹ over nilpotent PD thickenings

**Definition** (statements-review-3 §2; `DD/Pullback1MemHodgeFiltration.lean:204, 324`, **S**):
- `Cris.H1 γ s := CatCoh.H1 (O γ s)`: first cohomology of T ↦ B_T over the category `Thick γ s` of affine nilpotent
  PD thickenings;
- `FirstDeRham s := H1 (dp0 R) s`.

The general version `CH.H F n` (`ECC/CechPairings/InstAddCommGroup.lean:195`, **S**) is the cohomology of the
nerve cochain complex of a functor F : C ⥤ Mod, i.e. R^n lim over C.

### III.1 Comparison with de Rham (degrees 1 and 2): proved

- `GlobalTheory.Published.CrystallineSmoothLift` (`PT/Divisors₂/BijectiveCechDeRhamComparisonDegreeOne.lean:130`,
  **S**). For every `Data` D (a smooth, separated, quasi-compact lift X/R of X₀ over a nilpotent PD ideal) there are
  natural R-linear isos
  `CatCoh.H1 (O D.κ D.t) ≃ HH1 D.s` and `CatCoh.H2 … ≃ HH2 D.s`
  onto the Čech hypercohomology of the de Rham complex of the lift. The isos are compatible with cup products, with
  `cmp1`, and with morphisms of data.
- It is **proved**: `GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations`
  (`DP/CrystallineSmoothLiftOfRelations.lean:52`, 74 lines) **P-skel**. Inputs:
  - affine smooth lifts exist on thickenings (`nonempty_smoothLiftAffineThickenings`);
  - a cocycle relation `Rel1/Rel2` between categorical and Čech–de Rham cocycles that is total, surjective,
    detects zero, and is additive and natural (`crystallineCechDeRham_relations_total_detect_zero`, etc.).

  The bodies are unread.
- Corollary `cechDeRham_comparison_bijective_cup_smooth` (`DP/CechDeRhamComparisonBijectiveCupSmooth.lean:43`):
  for smooth separated qc s, `cmp1 : FirstDeRham s → HH1 s` is bijective and H² matches with cup.
- Consumers: `abelianDeRham_of_crystallineSmoothLift`, `AbelianHodgeDeRhamOfCrystallineLift`,
  `AbelianDeRhamFreeOfCrystallineComparison` and others (grep hits in `DP/`). So `AbelianDeRham` and
  Grothendieck–Messing do go through this comparison.

**Answer for III.** The home-made H¹ (and H²) *is* compared with standard algebraic de Rham cohomology (Čech
hypercohomology of Ω^•) of a smooth lift. That is Berthelot's "crystalline = de Rham of a lift" in degrees ≤ 2. The
comparison is a proved theorem, not a hypothesis. This resolves the open item of statements-review-3 §4 at the
statement level. One check remains (**N**): that `HH1`/`HH2` are the usual Čech hypercohomology of Ω^•, judged from
`GlobalTheory.CechDR` names. A comparison with Berthelot's crystalline *site* cohomology as such was not found. The
archive never defines the crystalline site, so "agreement" means agreement with de Rham of a lift.

### III.2 Hodge graded pieces (all degrees, characteristic 0): proved

`Om.hdg_iso` (`ECC/DifferentialFormsCech/HdgAffIso.lean:13`) is a vacuous `P → P` wrapper whose `type_of%` is the
statement. `Om.Nt2F.hodge_iso_natural_cech` (`…/CoverRefinementHodge/FinalC.lean:14`) **P-skel** proves it: for every
characteristic-0 field K and smooth proper X/K there are natural isos
`HT.Hdg q a (a+j) ≃ₗ[K] HodgeC q a j`.
Here `HodgeC = GlobalTheory.HodgeCoh.hodgeH`, which is `coh (Omega s a) j`: genuine sheaf cohomology of the
sheafified algebraic a-forms, the same `hodgeH` as in frontier-g. The inputs are a global-forms iso `glob_iso`,
Čech form bijectivity, cover refinement and pullback naturality, all unread. `DifferentialFormsCech/` has 28 files,
1.6k lines.

So downstream uses are not only formal. On the Galois path the categorical Hodge groups are identified with
H^j(Ω^a) by a proved theorem. The abelian-scheme de Rham package (`AbelianDeRham`, Grothendieck–Messing) rests on
the proved H¹/H² comparison with Čech de Rham.

---

## What remained unread, in priority order

1. **The étale-to-A_cris period map** `E.eFam` / `eM` / `pts` / `probe` / `lcMor`, and `good_eFam`
   (`ECC/KummerCupProducts/*`, `ECC/PerfectoidPullbacks/` 13.4k lines). This is where the deep content of the p-adic
   comparison must sit: why étale classes are represented by cocycles on AIC perfectoid points, and why
   ℤ/l^n → A_cris/l^n is φ-invariant and well defined.
2. **`half2Of` inputs** (`crisSurj`, `rhoEx`, `coEx`, `homRho`, `mulRho`, `firstChern_hodgeTate_rho`, `LvEx`/`lvEx`)
   and `toY`/`gam`: how A_cris cohomology over perfectoid points is mapped to Hodge cohomology of X_K. That is
   implicitly a crystalline comparison for the special fibre.
3. **`inj_of`** (`SumCoord.lean:252`) and **`htBij_of_parts`/`ontoAll_of`**: the formal duality/Künneth argument.
   Check that `Top`/`KTop` really covers every connected component, and that the `Frame`/`IsHT` encoding in
   `HTSpecGood` matches the HT decomposition.
4. **E2 leaves** in `ES/` (51.6k lines): `LineOne` (H¹ of relative lines from AIC schemes), `LineHigh`, `Desc`/`Cover`,
   `e2Cut_chow`, `proper_base_change_fibre`; and the E1 cut (`EtaleAxioms/*`, `EtaleCohomologyDescentOfCechCover`).
5. **Foundational properties** A5 (`classes_die_on_etale_cover`), B4 (`eqv_cechAug_of_isIntegralHom_of_surjective_of_sh`),
   B5 and A2. These carry the identification of this Ext-in-the-big-topos theory with étale cohomology.
6. **`QDual`/`qDual_holds`, `trIn_holds`, `QDiag`, `Kun`** (`KL/`, 10.9k lines): ℓ-adic Poincaré duality and
   Künneth.
7. **`crystallineCechDeRham_relations_total_detect_zero`** and the `HH1`/`HH2` definitions (III.1);
   `glob_iso`/`formToCO_bijective` (III.2).
8. **E4 leaves** (curve Picard, Kummer, spreading curves into smooth proper families) and **E3** leaves (C3, C4).
9. **Continuity** of `galHQ` on the Kuga–Sato cohomology (asserted downstream as `cont`; not located here).

## Notes for the docs

- frontier-c Q1 "about 15 `…Statement` lemmas: hypercohomology, Mayer–Vietoris, strict henselian acyclicity, Čech
  descent, and others" is now named exactly: `t_E2Cut.Hyp` = {A1–A5, A7–A10, B1–B5, E1} (I.2–I.3).
- frontier-g §I.3 "Faltings-style" should read: "Hodge–Tate decomposition for good reduction, proved by a period map
  through A_cris on perfectoid AIC points plus a Poincaré-duality/Künneth bijectivity argument. Almost purity does
  not appear by name."
- statements-review-3 §4 (categorical H¹): a comparison theorem exists and is proved (III.1, III.2). The caveat
  should be downgraded from "not checked" to "comparison proved; bodies unread".
- `E8` (mod-q Poincaré duality) is not proved anywhere on the live path. Its role is taken by rational `QDual`.
- Misnomers: `etale_base_change_of_duality` (= E3, no duality), `duality_diagonalClass_of_affineProperBaseChange`
  (= E1 → E2), `intersectionNumber_baseChange` (several E1/E6 leaves), `EtaleProperBaseChange` (a Prop comparing a
  pro-étale ℤ_l theory `GlobalTheory.Et.H` with `Hl`; unused on the path as far as seen).
