# 3. The analytic endgame

This strand turns three things into zero-freeness of L(s, ψ) for Re s > 1/2: auxiliary "good prime pairs", the window bound `VWin`, and a one-sided bound on a Chebyshev-type function Gm. The reports find that the good-pairs part and the final Landau-type deduction are classical, and that the step which reaches exponent 1/2 is elsewhere, in `core_gm` and what feeds it (page [04](04-chain-and-one-half.md)).

Status markers: [statement read], [proof outline read], [proof read in full], [inferred from names], [unread]. Paths are relative to the archive's `src/`; `CB/` abbreviates `Development/AutomorphicArithmetic/CharacterBoxes/` and `MSB/` abbreviates `Development/AutomorphicArithmetic/MeanSquareBounds/`.

## Terms used on this page

| Term | Meaning |
|---|---|
| Λ(n) | the von Mangoldt function |
| G_χ(y), `gChi` | Σ_{n≤y} Λ(n)χ(n)(y/n − 1) + y·L'/L(1, χ), a Riesz-smoothed prime sum. By the explicit formula it is essentially −Σ_ρ y^ρ/(ρ(ρ−1)), so a bound \|G_χ(y)\| ≤ y^{1/2+δ} is GRH-quality at the point y (analytic-core.md Q1, the reviewer's gloss) |
| zero-density estimate | a bound on how many L-functions in a family have a zero in a given region |
| Jacobi symbol (·/q) | the quadratic character attached to q; "twist by (·/q)" multiplies a character by it |
| window | an interval [Y, Y^{la}] with la > 1, for arbitrarily large Y |
| Landau's theorem | a Dirichlet series with nonnegative coefficients has a real singularity at its abscissa of convergence. Its "Ω±" or Pólya form turns one-sided bounds into zero-free regions |

## Overview of the chain

```
zero_density_box, meanSqK, twistK (PNT in progressions + Page + Siegel), kappa4, tailK
   → stage → stage1, stage2 → pair_share → pair_exists → pairEx : PairEx
landau_window → lemmaL → zeroFree_of_rpow_window → formB : ∀ Λ, Λ.FormB
PairEx + VWinAt ψ 401 → winPairs → supplyOfAdmOf → supplyChi → HostExW (3/2)
HostExW + TopG (Green) + formB + level_gm_le_on_family_scales → zeroFreeAll_of_topG : ZeroFreeAll
   → imprimitive → EveryCharacter → RH
```

The import direction of this chain was checked: good pairs, the Landau-window theorem and the definitions of `VWin` are all upstream of `ZeroFreeAll`, and no file in the closures of `pairEx` or `formB` has `EveryCharacter` or `ZeroFreeAll` as a hypothesis. [proof outline read] (analytic-core.md Q4)

## Step 1. Good window pairs (`PairEx`)

### Statement

`UpperTheory.Top.PairEx` and `PairGood` (`CB/PairGood.lean`). [statement read] (analytic-core.md Q1)

```lean
def tw (ξ : ℕ → ℂ) (q d : ℕ) (i j : Fin 2) (a : ℕ) : ℂ :=
  ξ a * (jacobiSym a q) ^ i * (jacobiSym a d) ^ j
def ZeroBox (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → LFunction χ s ≠ 0
structure PairGood (M : ℕ) (eps Y X : ℝ) (q d : ℕ) : Prop where
  pair : WinPair eps Y q d
  coprime : Nat.Coprime M (q * d)
  bounds : ∀ (ξ : DirichletCharacter ℂ M) (i j : Fin 2), (i ≠ 0 ∨ j ≠ 0) → ∀ N (χ : DirichletCharacter ℂ N),
      An.Induces χ (tw ξ q d i j) (2*M*q*d) →
      ∀ y, Y ≤ y → y ≤ X → ‖An.gChi χ y‖ ≤ y ^ (1/2 + eps/2) ∧ ‖An.logDerivativeAtOne χ‖ ≤ 4 * log y
  boxes : ∀ ρ : PChar, ρ.IsReal → ρ.N ∣ 8 * M → ∀ i j : Fin 2, (i ≠ 0 ∨ j ≠ 0) → ∀ N χ,
      An.Induces χ (tw ρ.val q d i j) (2*M*q*d) → ZeroBox (height M eps Y j) χ
def PairEx : Prop :=
  ∀ M, 0 < M → ∀ eps A, 0 < eps → eps < 1/52 → 1 ≤ A → ∃ Y1, ∀ Y ≥ Y1, ∃ q d, PairGood M eps Y (Y ^ A) q d
```

`WinPair eps Y q d` (`CB/ExistsPageN.lean`) requires, with T = Y^{ε/5}: q prime, q ≡ 3 mod 8, log q ∈ (T/2, T]; d prime, d ≡ 7 mod 16, log d ∈ (T log²Y/2, T log²Y]; q | d + 1; and every odd prime p ≤ T divides d + 1. [statement read] (analytic-core.md Q1; vacuity-check.md Q1)

**In words.** Fix the modulus M of the target character ψ, a small ε < 1/52 and A ≥ 1. For every large Y there are two huge auxiliary primes q, d such that every genuine quadratic twist χ of a character mod M by (·/q) and (·/d):
- has a square-root bound |G_χ(y)| ≤ y^{1/2+ε/2} on the short range y ∈ [Y, Y^A], and |L'/L(1, χ)| ≤ 4 log y;
- if the base character is real, has no zero with Re s > 1 − 1/400 and |Im s| up to roughly its conductor.

These statements concern only twisted characters, whose conductor is divisible by q or d. They never concern ψ itself. [statement read] (analytic-core.md Q1, Q4)

**Size of what is claimed.** The box has fixed width 1/400 up to height of order the conductor, far beyond any unconditional zero-free region for a single character (de la Vallée-Poussin gives width ≍ 1/log(q|t|)), but nowhere near Re s = 1/2. It is a statement for almost all members of a family, of the kind a large-sieve zero-density estimate gives. The bound on G_χ holds only for y ≤ Y^A, while log(conductor) ≈ Y^{ε/5} log²Y, so it comes from a mean square over the family, not from any zero-free region near 1/2. (analytic-core.md Q1)

### Proof

| Declaration | File | Plain statement | Method | Status |
|---|---|---|---|---|
| `QH.pairEx : PairEx` | `MSB/pairEx.lean:112` | packages `pair_exists` as `PairGood` with N₀ = 8M, τ = ε/2, K = A | bookkeeping | [proof outline read] |
| `QH.pair_exists` | `MSB/PairExists.lean:9` | picks one q and one d from `pair_share` with η = 1/2 | bookkeeping | [proof outline read] |
| `QH.pair_share` | `MSB/PairShare.lean:26` | a share 1 − η of the primes q ≡ 3 mod 8 in the window are good, and for each of them a share 1 − η of the admissible d are good; both sets are non-empty | two applications of `stage` | [statement read] |
| `QH.stage1`, `QH.stage2` | `MSB/Stage1Succ.lean:36`, `MSB/CharOf.lean:61` | the q-stage (modulus 8, residue 3) and the d-stage (modulus 16·oddM(T, q)) | instances of `stage` | [statement read] |
| `QH.stage` | `MSB/StagePow.lean:41` | in a progression of primes, all but a share η are good | zero density for one bad set, mean square plus Markov for the other, explicit formula to finish | [proof read in full] |
| `…ZD.zero_density_box` | `Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13` | at most C·Q^{1/4} primitive characters of conductor ≤ Q have a zero in [1 − 1/400, 1) × [−Q, Q] | Montgomery-style zero detection with a mollifier, dyadic blocks, a large-sieve duality inequality | [proof outline read] |
| `QH.meanSqK` | `MSB/meanSqK.lean:51` | mean square over q of the Dirichlet polynomial S(Z, y, q, κ) is ≤ C·y·log y·\|P\| | off-diagonal terms via `twistK` | [statement read]; body [inferred from names] |
| `QH.twistK` | `MSB/twistK.lean:148` | character sums Σ_q (q/s) are small for all odd squarefree s ≤ Y^A except one exceptional n* | PNT in progressions with a Landau–Page exceptional modulus and Siegel's bound | [statement read], first 25 lines of proof read |
| `QH.kappa4` | `MSB/Kappa4Loglog.lean:126` | \|L'/L(1, χ)\| ≤ 4 log Y for good χ | Mertens: the sum is ≈ 1000·log log Q | [proof outline read] |
| `QH.tailK` | `MSB/TailKExp.lean:92` | the explicit-formula tail beyond X^{400} is ≤ Y^ε | explicit formula inside the box | [statement read]; method [inferred from names] |
| `QH.thinH` | `MSB/GaussSumFunctionEq.lean:55` | host characters satisfy \|gChi\| ≤ y·exp(−c x^{ε/8}) for y ≥ exp(x^{ε/3})/3, given `RealBox` | classical PNT in the de la Vallée-Poussin range | [statement read] |

All file and status entries from analytic-core.md Q2.

**How `stage` works.** [proof read in full] (analytic-core.md Q2) A bad prime q lies in one of two sets.
1. B₁: some twist ξ·(·/q) has a zero in the box. `count_bad` gives |B₁| ≤ C·(FU)^{1/4} ≤ C·U^{3/8}, while `count_a` gives at least U^{9/10} primes in the progression. So B₁ is a vanishing share.
2. B₂(ξ): the Dirichlet polynomial S(Z, y, q, ξ) = Σ_{n≤Z} Λ(n)·min(1, y/n)·ξ(n)·(n/q), with Z = (Y^K)^{400}, exceeds y^{1/2+τ}/2 for some y in the window. The mean square `meanSqK` and Markov's inequality (`bad_share`) make B₂ a share at most η/(2(R+1)).
3. Otherwise `box_of_S` turns "zero-free box and small S" into the full bound, using the identity G_χ(y) = −S_Z(y) − y·tail_χ(Z) and `tailK`.

**Strength of the inputs.** The only zero-free statements in this chain are the width-1/400 boxes, and they are outputs of `zero_density_box`, never hypotheses. The `…Hyp` Props in `Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean` (`BoxCountHyp`, `MeanSquareHyp`, and others) are not assumed on this path; the proofs call the theorems directly. There is one ineffective input, Siegel's theorem, through `excBound`. Montgomery's estimate gives roughly Q^{0.03} at σ = 1 − 1/400; the archive needs only Q^{1/4}. [proof outline read] (analytic-core.md Q2)

> **Correction.** vacuity-check.md (Q1 and "For a number theorist") named the proof of `pair_share` as the first place an RH-strength claim could hide, since it is a density statement about zero-free regions for families of quadratic twists. The later analytic-core.md read `stage` in full and the statements of everything below it, and found the argument classical: zero density plus mean square plus the explicit formula, with Siegel's theorem as the only ineffective input. The weight of the argument is in `core_gm` / `CoreAtH` and in what feeds them, not in `pair_share`. (analytic-core.md overview, Q2 "Is any input of unusual strength?")

`pairEx` also settles a vacuity question: `VWin` is a statement "for every window pair", so it would hold vacuously if no pairs existed. `QH.pairEx` proves pairs exist, and the main path applies `VWin` to such a pair. [statement read] (vacuity-check.md Q1, correcting the open point in statements-review.md row 19)

## Step 2. Applying the window bound (`winPairs`)

`UpperTheory.Top.winPairs` (`CB/WinPairs.lean:5`). [proof read in full] (analytic-core.md Q3)

```lean
theorem winPairs : ∀ ψ eps c, 0 < eps → eps < 1/52 → 1 ≤ c → VWinAt ψ 401 → PairEx →
  ∃ J ≥ 1, ∀ y, ∃ Z ≥ y, ∀ x ∈ [Z, Z^{3/2}], ∃ Y q d e, WinDatum ψ eps J c x Y q d e
structure WinDatum ψ eps J c x Y q d e : x^{1/J} ≤ Y ≤ x, PairGood ψ.N eps Y x q d,
  x^{2+8eps} ≤ c·2^e ≤ 2x^{2+8eps},  ∀ E, IsChiField ψ e q d E → VVle E ⌊x^400⌋ (sqrt (exp (x^eps)))
```

The proof: choose the 2-power "page" e(x) with 2^e ≈ x^{2+8ε} (`exists_pageN`); get J and X₀ from `VWin`; take X so large that Y = X^{1/J} is past the `PairEx` threshold; take a good pair at scale Y; apply `VWin` to get W with the Ш bound on [W, W²]; rescale x = k·x' and use [kW, (kW)^{3/2}] ⊆ [W, W²], which needs k³ ≤ W. The threshold ⌊(kx')^{400}⌋ is absorbed into ⌊x'^{401}⌋ using k^{400} ≤ x'. **This is where 401 = 400 + 1 comes from.** (analytic-core.md Q3)

So for every x in windows [Z, Z^{3/2}] there are a good pair (q, d) at a scale Y ∈ [x^{1/J}, x] and host fields E, cut out of a cyclotomic field by ψ, the Jacobi symbols mod q and d and the 2-power level 2^{e+2}, on which both the Ш-length bound and all `PairGood` properties hold.

`UpperTheory.T3.supplyOfAdmOf` (`ShortNorms/supplyOfAdmOf.lean`) and `UpperTheory.Top.supplyChi` (`CB/SupplyChi.lean`) package this as `HostExW (3/2)`, whose content includes `EAtH` (explicit-formula error conditions for the host) and `VVle H.E R.t (sqrt s.b)`. [statement read]; `supplyOfAdm` and the discharge of its supply hypothesis are [unread] (analytic-core.md Q3).

`EAtH Λ H TT x eps C` (`…/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:144`) has fields for bookkeeping (`o_eq`, `kept`, `ps`), equidistribution of a finite set TT in cosets with error x^{−1+ε} (`shares`), pointwise G-bounds for the twisted characters (`bdG`) and |L'/L(1)| ≤ C log x (`bdL`). [statement read] (analytic-core.md Q3)

## Step 3. The function Gm and its one-sided bound

`Gm` (`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:36-38`). [statement read] (core-gm.md Q1)

```lean
def wt (ψ : PChar) : ℝ := if Λ.psK = some ψ then 1 else (3 * (Λ.o : ℝ) + 1)⁻¹
def Gm (y : ℝ) : ℝ := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re
```

Here Λ = `Level.cyc ψ` is the set of characters in the cyclic group generated by ψ, Gz(y) = Σ_{n≤y} Λ(n)(y/n − 1) − y log y + (1+γ)y is the zeta term, and the weight is 1 for the exceptional character and 1/(3o+1) for the others. So Gm is a positive-weight Landau-type combination of the zeta term and the level's characters.

The bound Gm(x) ≤ x^{1/2 + (eD+eL+7)ε} on windows is `ChebyshevInequalityOnWindows`, supplied by `level_gm_le_on_family_scales`, which calls `UpperTheory.Comparison₂.core_gm` (`Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12`). On the main path eD = 2 and eL = 0, so the exponent is 1/2 + 9ε (core-gm.md Q1). **This is the step that reaches 1/2**; it is described on page [04](04-chain-and-one-half.md).

> **Correction.** analytic-core.md (Q3, item 1) guessed that `CoreAtH` "is where the Ш-length bound must enter" [inferred from names]. core-gm.md found that the Ш bound `VVle` does not appear in `core_gm`, `CoreAtH` or `ChainTied` at all; it enters upstream, where `ChainTied` is constructed, through `HypV → DIVinN`. (core-gm.md overview and Q2 level 3)

## Step 4. The localized Landau theorem (`FormB`)

`Formalism.HC.Level.FormBAt` (`…/TotientGaloisClasses/Window.lean:30`) and `UpperTheory.Comparison₂.formB` (`Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean:8`). [statement read], [proof outline read] (analytic-core.md Q3)

```lean
def FormBAt la := ∀ θ ∈ (0,1), HasWindows {x | Λ.Gm x ≤ x^θ} la → Λ.ZeroFreeAbove θ
def HasWindows S la := ∀ y, ∃ Y ≥ y, ∀ x ∈ [Y, Y^la], x ∈ S
```

**In words.** If Gm(x) ≤ x^θ holds on windows [Y, Y^{la}] for arbitrarily large Y and some fixed la > 1, then no L(s, ψ'), ψ' in the level, vanishes for Re s > θ.

**Proof.** `Deduction.zeroFree_of_rpow_window` → `lemmaL` → `landau_window` (`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean:83`). It works with g(u) = Gm(e^u) and its Laplace transform Φ under `PoleData` (Φ meromorphic on Re s > 0, poles exactly at the zeros, real poles with positive residue; `DedekindLFunctions/LandauZeroFreeCriterion.lean:15`). It looks at Taylor coefficients (−1)^kΦ^{(k)}(σ)/k! with k ≈ U at a large real σ > 2. The kernel u^k e^{−σu}/k! concentrates on [U, (1+δ)U], and only the positive part of g matters, since ‖Φ^{(k)}(σ+iγ)‖ + Re Φ^{(k)}(σ) ≤ 2∫ g⁺·kernel. A nearest pole β > θ (`landau_dichotomy`, `landau_nearest`) forces the coefficients to be ≍ (σ−β)^{−k}; the window bound caps them by e^{ηU}(σ−θ)^{−k}; contradiction (`landau_window_contra`). This is the Landau / Pólya Ω± method with an explicit window. `landau_dichotomy` and `landau_nearest` are [unread]. (analytic-core.md Q3)

**Logical shape.** [proof outline read] (analytic-core.md Q3, `level_of_tiedWin` in `TopWin.lean`) Fix ψ and s with Re s > 1/2. Choose ε with (eD+eL+7)ε ≤ (Re s − 1/2)/2. The window family for that ε gives Gm(x) ≤ x^{1/2+(eD+eL+7)ε} on windows [Z, Z^{3/2}], and `FormB` then gives zero-freeness for Re s' > 1/2 + (Re s − 1/2)/2, which includes s. So the deduction is a **direct limit ε → 0, not an induction** on the width of a zero-free region. No zero-free input about ψ itself is used, only about the twists.

The generic engine is `zeroFreeOn_of_tiedWin_cyc` (`…/TotientGaloisClasses/TopWin.lean:90`), applied in `zeroFreeAll_of_topG` (`CB/ZeroFreeAllOfTopG.lean:26`) with la = 3/2 from `zero_free_all_of_green_v_win` (`ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12`). Its third input, `ChebyshevInequalityAtWindowScale`, comes from `TopG` via `shape_closed_link_n_of_green` and Green's theorem, which are [unread] (analytic-core.md Q3).

The announcement's phrase "W(1_(0,1]) + (~X^η)·1_(0,1/X] ≥ 0 gives > 1 − η" fits `landau_window`, where one-sided positivity on a window yields zero-freeness, or the inside of `CoreAtH` / `ChainTied`. [inferred from names] (analytic-core.md Q3)

## Constants and where they come from

From analytic-core.md Q5; "[proof read]" means the reviewer traced the constant in a proof.

| Constant | Where it enters | Role |
|---|---|---|
| 1/400 | `ZeroBox`, `ZeroFreeBox`, `RealBox` | width of the twist boxes. Paired with polynomial length Z = X^{400}: the tail beyond Z is ≈ Z^{−1/400} = X^{−1}, which makes y·tail ≤ Y^ε (`tailK`) [statement read] |
| 400 and 401 | `S((Y^K)^400 …)`, `stage`, `WinDatum` (⌊x^{400}⌋ twists), `VWin := ∀ ψ, VWinAt ψ 401` | 401 = 400 + 1, the 1 absorbing the rescaling constant k in `winPairs` [proof read] |
| ε < 1/52 | `kappa4`, then `PairEx`, `VWinAt`, `HostExW`, `winPairs` | from `kappa4`: \|L'/L(1)\| ≤ log z + O(1) with log z = 1000 log log Q ≤ 200ε log Y + O(log log Y); staying below 4 log Y needs ε < 1/50, and 1/52 leaves slack [proof read] |
| T = Y^{ε/5} | `WinPair`, `height`, `primePairSetFirst`, `admitted` | log q ≈ T, log d ≈ T log²Y; lemmas need Y^{ε/6} ≤ log(conductor) ≤ Y^{ε/4} [statement read] |
| log²Y factor in d | `WinPair`, `admitted` | the d-progression has modulus ≈ e^{3T}; the condition makes the PNT-in-progressions error superpolynomially small [statement read for the condition; purpose inferred from names] |
| q ≡ 3 mod 8, d ≡ 7 mod 16, p \| d+1 for p ≤ T, q \| d+1 | `WinPair`, `ClassSplit` | −q and −d are fundamental discriminants; q and all small primes split in ℚ(√−d), and d ≡ 7 mod 8 splits 2. Used for the CM / norm-prime host construction [statement read for `ClassSplit`; use inferred from names]. Page [06](06-window-bound.md) shows the residues also make an Iwasawa-module rank uniform in q and d |
| 2 + 8ε | `PageN`, `WinDatum` | the 2-power level 2^e ≈ x^{2+8ε}; its role is inside `CoreAtH` [inferred from names] |
| la = 3/2 | `TopPlug`, `winPairs` | any la ∈ (1, 2) works: `FormB` holds for every la > 1 and `VWin` gives windows [W, W²]; 3/2 leaves room for k³ ≤ W [proof read] |
| 1/2 + ε/2 | `PairGood.bounds` (τ = ε/2) | square-root bound on the twists, consumed as `bdG` in `EAtH` |
| Q^{1/4}, U^{9/10}, U^{3/8} | `ZeroDensityBox`, `count_a`, `stage` | bad moduli ≤ C·U^{3/8} ≪ η·U^{9/10} [proof read] |
| 197/200, 3/200 | `CountZDefs.lean` | exponents of the zero-density argument; 197/200 < 2s₀ − 1 = 199/200 leaves room for divisor-function losses [statement read] |

## Where to read next in the source

In the order analytic-core.md recommends: `core_gm` with `CoreAtH` and `ChainTied` (page [04](04-chain-and-one-half.md)); `Deduction.landau_window` with `PoleData` and how `poleData F` realizes Gm with positive real residues; `QH.stage`; `zero_density_box` with `CountZDefs.lean`; `twistK` and `meanSqK` with `pnt_progressions_relative_weak_holds` and `excBound`. The unread proof bodies of this strand are listed in [10-open-frontier.md](10-open-frontier.md).

## Sources

- analysis/analytic-core.md (all sections)
- analysis/vacuity-check.md (Q1; its flag on `pair_share`, corrected here)
- analysis/core-gm.md (Q1 for `Gm`; overview for where Ш enters)
- analysis/statements-review.md (row 19, open point on `WinPair` existence)
