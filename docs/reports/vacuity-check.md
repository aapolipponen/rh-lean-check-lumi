# Vacuity check of the load-bearing statements (VWin, Row0b, IsRecT)

Date: 2026-11-20. This is a read-only follow-up to `statements-review.md`. I read the source on chili with grep and sed
(`/bulk/shared/rieman/lean/src`, paths below are relative to it). Nothing was compiled or run.
"Verified" means I read the Lean text quoted here. "Impression" means a judgement made without a full trace.

## Verdicts

| Q | Question | Verdict |
|---|---|---|
| Q1 | Is `VWin` applied to actual `WinPair`s? | **Non-vacuous, verified.** The archive proves pairs exist (`QH.pairEx`, by counting primes). The main path applies `VWin` to such a pair. |
| Q2 | Is the `VVle` bound trivial? | **Not trivial by definition, verified.** `LData` is inhabited (`ldataExists`) and essentially canonical. `shaLen` is the ℤ_ℓ-length of a genuine Ш¹ of continuous cohomology of G_{E,S} with coefficients ℚ_ℓ/ℤ_ℓ(−e). |
| Q3 | Is the `above` clause of `Row0b` vacuous? | **Not vacuous, verified.** `LocTied` and `LocBridge`+`Pst.Induces` are proved inhabited. **Used with concrete data: partly verified.** A consumer instantiates `above` with concrete `LocPrime`/`LocTied` data. I did not trace the bridge `Bw` through an unbroken chain to a concrete bridge on the VWin path. |
| Q4 | Which `PropsB` fields are consumed? | `cont`, `ss`, `away` (only its `.tor` case in what I read), `weights`, `weights_conj` (passed on), and `above` (`.nice`, `.crys`). All six are projected. |
| Q5 | Does anything downstream need more than `IsRecT`? | **No evidence of that.** Consumers apply local–global compatibility only in the abelian (`Tor`) case, where `IsRecT` constrains `rc`. Elsewhere they use only unconditional laws. This is an impression from the consumers I read, not an exhaustive check. |

## Q1. Non-vacuity of the window

**Definitions** (`Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:27-49`): `WinPair eps Y q d` requires
q prime ≡ 3 mod 8, log q ∈ (T/2, T]; d prime ≡ 7 mod 16, log d ∈ (T(log Y)²/2, T(log Y)²]; q | d+1; every odd
p ≤ T divides d+1; T = Y^{eps/5}. In `VWinAt`, the prover picks `J` and `X0`. Since X^{1/J} → ∞ for every fixed J,
pairs at every large scale Y are enough to rule out vacuity.

**The existence theorem.** `UpperTheory.Top.PairEx` (`CharacterBoxes/PairGood.lean:28`):
```lean
def PairEx : Prop :=
  ∀ (M : ℕ), 0 < M → ∀ eps A : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ A →
    ∃ Y1 : ℝ, ∀ Y ≥ Y1, ∃ q d : ℕ, PairGood M eps Y (Y ^ A) q d
structure PairGood (M : ℕ) (eps Y X : ℝ) (q d : ℕ) : Prop where
  pair : WinPair eps Y q d
  coprime : …   bounds : … (ψ-function and L'/L(1) bounds for twists)   boxes : … (zero-free boxes)
```
This is stronger than plain existence: the pair must also be "good", meaning the twisted characters have zero-free boxes and
explicit-formula bounds. It is proved without hypotheses as `QH.pairEx : UpperTheory.Top.PairEx`
(`MeanSquareBounds/pairEx.lean:112`). That proof uses `QH.pair_exists` (`MeanSquareBounds/PairExists.lean:9`), which uses
`QH.pair_share` (`PairShare.lean:26`):
```lean
∃ G₁ ⊆ primePairSetFirst (Y ^ (ε / 5)), 0 < (primePairSetFirst (Y ^ (ε / 5))).card ∧ (1 - η) * … ≤ G₁.card ∧ ∀ q ∈ G₁,
  GoodQ … q ∧ ∃ G₂ ⊆ primeSetTwoBounds (Y ^ (ε / 5)) z' q, 0 < (primeSetTwoBounds …).card ∧ (1 - η) * … ≤ G₂.card ∧ …
```
where `primeSetTwoBounds z z' q` is the set of primes d ≤ e^{z'} with d ≡ 7 mod 16, `oddM z q ∣ d+1` and d > e^{z'/2}
(`PrimeSetTwoBounds.lean`). So the archive proves that both prime sets are non-empty (`0 < card`) and that a fraction
1−η of them are good. Linnik is not used here. The argument is a counting/density argument. I did not read
`stage1`/`stage2`.

**The consumer applies VWin to such a pair** (verified):
- `CharacterBoxes/WinPairs.lean:5` `UpperTheory.Top.winPairs (…) : … → VWinAt ψ 401 → PairEx → …` contains
  ```lean
  obtain ⟨J, hJ, X0, hX0⟩ := hV eps heps heps52 e he
  obtain ⟨Y1, hY1⟩ := hP ψ.N hN eps J heps heps52 hJ
  obtain ⟨q, d, hpg⟩ := hY1 (X ^ (1 / J)) (hMY1.trans hY0M)
  obtain ⟨W, hW0, hW2, hWV⟩ := hX0 X hXX0 q d hpg.pair
  ```
- `ShortNorms/supplyOfAdmOf.lean:29`: `UpperTheory.Top.winPairs ψ eps c … hV QH.pairEx`. The output includes
  `VVle H.E R.t (Real.sqrt s.b)` for the host field.
- From there through `supplyOfAdm`, `UpperTheory.Top.supplyChi` (`CharacterBoxes/SupplyChi.lean`) and
  `zero_free_all_of_green_v_win … fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)`
  (`ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12`) to `every_character_of_green_v_win`. That is called by
  `UpperTheory.Lit.every_character_of_theta_integrals_local_matching`
  (`…/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69`), which is called by the final
  `every_character_of_literature_of_vWin` (`…/EveryCharacterOfLiteratureOfVWin.lean:810`). `zeroFreeAll_of_topG`
  uses the supply hypothesis (`h la (GChi ψ) hla (hS ψ) …`, `CharacterBoxes/ZeroFreeAllOfTopG.lean:30`).

Conclusion: VWin is used non-vacuously on the path to `EveryCharacter`. (A second, parallel route,
`plugWin`/`plugAll` in `CharacterBoxes/EveryCharacter.lean`, also goes through `supplyChi ψ (hV ψ)`.)

## Q2. Is the `VVle` bound trivial?

`VVle E t B` (`ExistsPageN.lean:12`) quantifies over `ld : ∀ p, LData E Ω p` and asserts `shaLen (ld p) e ≠ ⊤` for
0 < e < t, plus Σ_{ℓ∈S} log ℓ · Σ_{e=1}^{t−1} (shaLen).toNat ≤ B.

- **LData is inhabited.** `theorem ldataExists : LDataExists` (`Formalism/GaloisCohomology/GaloisCohomologyProofs/LdataNonempty.lean:48`)
  is built from `ldata_nonempty`. That takes S = places above ℓ, A v = `placeOf Ω v` (a chosen valuation ring over v) and
  `chi` = the descent of the cyclotomic character through `G → G_S` (`QuotientGroup.lift`, unramified outside ℓ). The data
  are essentially canonical: S is forced, `chi` is forced because `toGS` is surjective, and only the choice of places A varies.
- **shaLen is a genuine Ш¹** (`Formalism/GaloisCohomology/Statement.lean`):
  ```lean
  def Sha (D : LData F Ω l) (e : ℤ) := Sha1 (qzTw D e) (locFam D.S D.A) (continuous_locFam D.S D.A)
  def shaLen (D : LData F Ω l) (e : ℤ) : ℕ∞ := Module.length ℤ_[l] (Sha D e)
  ```
  Here `qzTw D e` is ℚ_ℓ/ℤ_ℓ (discrete topology) with G_S acting by chi^(−e). `Sha1` is the intersection of the kernels of
  restriction to the decomposition groups `Dec A` at places in S
  (`ReciprocityTheory/GaloisValuations/ContinuousConstSMulQuotient.lean:168`). `H1` is continuous cocycles modulo coboundaries
  (`SeparatedDvrSecondCohomologyMem.lean:41-61`: `{f | Continuous f ∧ ∀ g h, f (g*h) = f g + rho g (f h)}`).
  `GS = G F Ω ⧸ NS`, where `NS` is the closure of the normal closure of the inertia groups at places outside S (`GaloisValuations/Global.lean:128`).
  `Inertia` and `IsPlaceOver` are the standard definitions (`Formalism/ConjugateSelfDual/Statement.lean:20-26`). I found
  no local override of the topology on `Ω ≃ₐ[F] Ω`. That it is Mathlib's Krull topology instance is my recollection
  of Mathlib, not something I checked here.
- Remarks. The Ш¹ omits the archimedean places, which only matters for ℓ = 2 and real places. The relevant E are cut
  out by conditions that a = −1 fails, since (−1/q) = −1 for q ≡ 3 mod 4, so E is totally imaginary and this does not arise.
  `.toNat` would turn ⊤ into 0, but VVle separately asserts `≠ ⊤`.

Conclusion: the bound is not trivially true. It is a quantitative statement about Ш¹(G_{E,S}, ℚ_ℓ/ℤ_ℓ(−e)) of
abelian fields. Mathematically these groups are not zero in general (impression).

## Q3. The `above` clause of `Row0b`

Data (verified):
- `LocPrime l` (`Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean:527`) is an *abstract* package of period
  rings B, B_dR with Galois action, φ, t, a χ and filtrations. `LocAinf` (`:786`) gives an embedding of A_inf. `LocTied`
  (`Formalism/LocalRingCardinality/AdicCompletionLocal/LocTied.lean:11`) ties the abstract rings by ring isomorphisms
  to the archive's concrete `Per.Bcris l`, `Per.BdR l`, compatible with the action, φ, the filtration, t = log[ε] and A_inf.
  So `Nonempty (LocTied …)` forces P to be (isomorphic to) the concrete Fontaine rings.
- `LocBridge l E Ω Gw O` (`DataNLoc.lean:574`) is an embedding j : Ω → \bar ℚ_ℓ with E dense in a finite K_w, an isomorphism
  `Dec A ≃ G_{K_w}` compatible with j, and a coefficient ring O ≅ O_L. `Pst.Induces Bw := ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1`
  (`Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/FiniteDimensionalLetter.lean:108`, namespace
  `GlobalTheory.Pst`).

Inhabitedness (verified):
- `GlobalTheory.MemLoc.exists_locPrime_tied : ∀ l [Fact l.Prime], ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI)`
  (`Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281`), from `nonempty_core`.
- `GlobalTheory.PlaceBridge.exists_locBridge` (`…/IwasawaDecomposition/FiniteDimensionalAdjoinRange.lean:303`): for every
  w over ℓ and every A with `IsPlaceOver A w`, there are j and L0 with `∀ x, x ∈ A ↔ ‖j x‖ ≤ 1` and, for every LL ⊇ L0, a
  `Bw : LocBridge … (OL LL)` with `Bw.j = j`, which gives `Pst.Induces Bw`. A packaged version for all w is `exists_bridges`
  (`…/NonemptyWdSideOfTie.lean`).

Use by consumers:
- Verified: `UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT : HypothesesH' → RowT → PolG`
  (`…/DenseThresholdCases/GuPolG.lean`) takes `H` from the row and uses
  `(H.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice …`. Here `Loc.PP l` and `Loc.tiedP l` are concrete
  LocPrime and LocTied data. `Bw, hj` are still universally quantified and are passed into `CompatG.ht : … → HasHTAt r HT w`.
  `HasHTAt` (`AutomorphyLifting/GalUnitaryT.lean:54`) is again "∀ O Bw, Induces Bw → IsdRAt (Loc.PP l) Bw … ∧ IsJumpsAt …".
- Verified: consumer lemmas instantiate such ∀-Bw hypotheses with concrete bridges. For example `UpperTheory.V.Th.purLocS`
  (`AutomorphicVarieties/TheoremsMuLinked/PurityTempered/AlgPowConst.lean:161`) does
  `obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge h hw; … hx O Bw hj`. `PadicHodgeTheory/OrdFlag.lean:154` uses
  `Pst.Test.exists_induces`, and `CharpolySmul.lean:168` and `AutomorphicNewformOfHyp.lean:169` use `exists_locBridge`.
- Not traced: one unbroken chain from `Row0b.above` through `PolG`/`HalfG`/`CompatG.ht` to a call such as `purLocS` on the
  path to VWin. I also did not confirm that `polG_of_printsH_of_rT` is itself on the VWin proof path. It sits in the
  same `DenseThresholdCases` directory as `TopMainZj.lean`.

Conclusion: the clause is not vacuous, because every quantified datum is provably inhabited. The consumers use it with
concrete `LocPrime`/`LocTied` data, and the pattern "∀ Bw ⇒ instantiate with a proved bridge" is common on the consumer
side. That it is used non-vacuously on the VWin path is very likely but not fully traced.

## Q4. Which `PropsB` fields are projected

`Row0b` reaches the downstream argument as `OpenImageCondition.galoisRepOfPolarizedPairLit : RowT`
(`…/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207`). It also arrives as `gal : RowT` in
`automorphic_window_of_inputs` (`TopMainZj.lean:71`). `RowT` is used by more than a dozen theorems (`compatT`, `half_alt`,
`same_of_prints_of_rT`, `locQ_of_alt`, `weight_compatible_descent`, `unitary_three_automorphy_dense_of_prints_and_row`, the
`step` lemmas in `AAcrossOf`/`FirstConditionUp`/`TAAcrossOf`, …). Projections I saw:

| field | where | how |
|---|---|---|
| `cont` | `DenseThresholdCases/FrobOfProps.lean:31`, `SVPatch.lean:34`, `GuPolG.lean` | continuity of r |
| `ss` | `FrobOfProps.lean:47`, `GuPolG.lean` | semisimplicity |
| `away` | `FrobOfProps.lean:30`, `SVPatch.lean:33`, `GuPolG.lean` | always `.tor g.1 g.2`, i.e. x = y for abelian, N = 0 parameters (Frobenius at unramified places) |
| `weights` | `GuPolG.lean` (`H.weights`) | HT weights from the infinitesimal character |
| `weights_conj` | `TypeConditions/OfStar.lean:63`, `ThirdPlaceSeries/SOfStar.lean:36`, `RankTwoPatching/FrobOfProps.lean:34` | copied into repackaged structures (`IsGalUAlt`, …). I saw no final use |
| `above` | `GuPolG.lean` (`.nice`), `SOfStar.lean:39-50` (`.nice …`, `.crys`, and `.nice … .2.2.2`, i.e. `AwayB` of `wdAt` at ℓ, inside `carU_of_star_alt`) | de Rham / pst / HT jumps above ℓ and the WD comparison at ℓ in the abelian case |

`away.tame0` (the tame square-free case) did not appear among the projections I read. Only `.tor` did.

## Q5. Is `IsRecT` exactly what is needed?

The consumers apply `away` only through `.tor`, which needs `Tor y ∧ y.mono0`: the local parameter is abelian with N = 0.
Abelian parameters are exactly those whose cuspidal support consists of characters, which is the "Good" class where `IsRecT`
pins rc down (twist compatibility, det = central character, CFT for n = 1). `nice` is likewise used with `Or.inr g1`, the
`Tor` branch (`GuPolG.lean`). Where a consumer needs an `rc` it gets it from `UpperTheory.Zero.LLC.recTExists E Ω A w h`
(`GuPolG.lean`). Where it uses `LawsT` beyond the Good class, it uses only unconditional laws: `halfG` uses `L.nu`,
unramified-twist compatibility, which `LawsT` asserts for all x (`HalfG.lean`, the `key` step). Because `away`
quantifies over *every* rc satisfying `IsRecT`, a looser `IsRecT` makes `Row0b` harder to prove, not easier to use. So the
weak correspondence is consistent with what the consumers I read actually need. I found nothing downstream that assumes
LLC on wild supercuspidals. This is an impression from the consumers listed above, not an exhaustive search of every `IsRecT` use.

## For a number theorist

The decisive content is in Q1/Q2, not in vacuity. The archive proves that good window pairs exist (`pair_share`: a density-one
share of the primes in each window yields zero-free boxes for every twisted character), and it then needs a *genuine* bound
Σ_ℓ log ℓ · Σ_{e<x^401} len Ш¹(G_{E,S_ℓ}, ℚ_ℓ/ℤ_ℓ(−e)) ≤ exp(x^ε/2) for the abelian fields E cut out by ψ and the
Jacobi symbols mod q, d. Two things deserve the closest scrutiny. The first is the proof of `pair_share` (`stage1`/`stage2` in
`MeanSquareBounds/`), because a density statement about zero-free regions for families of quadratic twists is exactly where
an RH-strength claim could hide. The second is the proof of `vwin_of_row` (`TopMainZj.lean`, `v_window_of_depth_zero_residual_bc_cm`).
