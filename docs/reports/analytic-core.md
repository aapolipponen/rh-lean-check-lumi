# The analytic core: good window pairs and the Landau-window deduction

Date: 2026-11-20. Read-only study of `/bulk/shared/rieman/lean/src` on chili with grep, sed and cat. Nothing from the archive
was compiled or run. The import closures in Q4 were computed by a small Python script of mine that only reads `import` lines.
Paths are relative to `src/`. Calibration tags used throughout:

- **[S]**: read in the statement.
- **[P]**: read in the proof.
- **[N]**: inferred from names, or from how the statement is shaped, without reading the proof.

## Overview

The "good pairs" theorem `QH.pairEx : UpperTheory.Top.PairEx` is a density statement about one family: the quadratic twists
χ = ξ·(·/q)^i·(·/d)^j of characters ξ mod M by Jacobi symbols of two huge auxiliary primes, with (i,j) ≠ (0,0). The primes
satisfy log q ≈ T and log d ≈ T log²Y, where T = Y^{ε/5}. For almost all such q, and then almost all such d, it asserts three
things. (a) Every twist is zero-free in a fixed-width box: Re s > 1 − 1/400, |Im s| ≤ height ≈ conductor. (b) The explicit-formula
remainder obeys |G_χ(y)| ≤ y^{1/2+ε/2} on the short range y ∈ [Y, Y^A], where G_χ(y) = Σ_{n≤y} Λ(n)χ(n)(y/n − 1) + y·L'/L(1,χ).
(c) |L'/L(1,χ)| ≤ 4 log y. The proof is classical. It uses Montgomery-style zero detection with a mollifier, plus duality and a
crude large sieve. That gives a zero-density count: at most C·Q^{1/4} primitive characters of conductor ≤ Q have a zero in the
box. The proof also uses a mean square over the family, made diagonal by the PNT in progressions with a Landau–Page exceptional
modulus (Siegel enters), Markov's inequality, and the explicit formula with the box controlling the tail beyond X^{400}. No
hypothesis anywhere in this chain asserts that zeros are absent. Box (a) concerns only twisted characters, whose conductor is
divisible by q or d, never the target character ψ, and its width 1/400 is far from 1/2. Downstream, the deduction of
`ZeroFreeAll` is a **localized Landau theorem**, not an induction. For each small ε, the window bound VWin together with the good
twists gives a one-sided bound Gm(x) ≤ x^{1/2 + C·ε} for the cyclic level of ψ. Gm is a positive-weight combination of the zeta
term and Re G_{ψ^k}, and the bound only has to hold on windows x ∈ [Z, Z^{3/2}] for arbitrarily large Z. A Taylor-coefficient
(Pólya–Landau) argument then rules out zeros with Re s > 1/2 + C·ε, and ε → 0 finishes. In the files I read, the genuinely new
input is not in the good-pairs file. It is in what turns the Ш-length bound (VWin) into the one-sided Gm bound: `CoreAtH`, `TopG`
and `ChainTied`.

## Q1. Definitions

### `PairEx`, `PairGood`, `ZeroBox`, `height` [S]

From `Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean`:

```lean
def tw (ξ : ℕ → ℂ) (q d : ℕ) (i j : Fin 2) (a : ℕ) : ℂ :=
  ξ a * (jacobiSym a q) ^ i * (jacobiSym a d) ^ j
def ZeroBox (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → LFunction χ s ≠ 0
def height (M : ℕ) (eps Y : ℝ) (j : Fin 2) : ℝ :=
  8 * M * exp (Y ^ (eps / 5)) * exp (Y ^ (eps / 5) * log Y ^ 2) ^ j
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

`WinPair eps Y q d` (`CharacterBoxes/ExistsPageN.lean`) [S] requires all of the following, with T = Y^{ε/5}:
- q is prime, q ≡ 3 (mod 8) and log q ∈ (T/2, T];
- d is prime, d ≡ 7 (mod 16) and log d ∈ (T log²Y / 2, T log²Y];
- q | d + 1, and every odd prime p ≤ T divides d + 1.

`An.Induces χ f M` means that χ is primitive and agrees with f on integers coprime to M. `gChi`
(`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:23`) [S] is defined as follows:

```lean
def gChi χ y := if χ = 1 then G y else sumLamChi χ y + y * logDerivativeAtOne χ
-- sumLamChi χ y = Σ_{n ≤ y} Λ(n) χ(n) max(y/n − 1, 0) ;  logDerivativeAtOne χ = L'(1,χ)/L(1,χ)
```

**In words.** Fix a modulus M (it will be the conductor of ψ), a small ε < 1/52 and A ≥ 1. For every large Y there is a window
pair (q, d) as above such that every primitive character χ induced by ξ·(·/q)^i·(·/d)^j satisfies three conditions. Here ξ is
any character mod M and (i,j) ≠ (0,0), so χ is a genuine quadratic twist.
- **bounds.** G_χ(y) := Σ_{n≤y} Λ(n)χ(n)(y/n − 1) + y·L'/L(1,χ) has |G_χ(y)| ≤ y^{1/2+ε/2} for all y ∈ [Y, Y^A], and
  |L'/L(1,χ)| ≤ 4 log y. By the explicit formula, G_χ(y) is essentially −Σ_ρ y^ρ/(ρ(ρ−1)) (my gloss, not a statement in the
  file), so this is a GRH-quality bound, but only for y in [Y, Y^A].
- **boxes.** When ξ = ρ is a real character mod 8M, L(s,χ) has no zero with Re s > 1 − 1/400 and |Im s| ≤ height. The height
  is ≈ 8M·e^T when only q twists (j = 0), and ≈ 8M·e^{T + T log²Y} ≈ 8M·q·d when d twists (j = 1). In both cases the height is
  of the order of the conductor.

**Size of the region.** The box has fixed width 1/400, independent of the conductor, and extends up to height ≈ conductor. For
a single character this is far beyond any known unconditional zero-free region: de la Vallée-Poussin gives width ≍ 1/log(q|t|).
It is also nowhere near Re s > 1/2. It is a **zero-density statement for almost all members of a family**, of the kind one gets
from a large-sieve zero-density estimate at σ = 1 − 1/400. The G_χ bound is a square-root bound on the very short range
y ≤ Y^A, while log(conductor) ≈ Y^{ε/5} log²Y. So the conductor is astronomically larger than y, and the bound comes from a
mean square over the family, not from any zero-free region near 1/2.

### The `QH` intermediate notions [S]

From `Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean`, which uses definitions in
`Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean`:

```lean
def ZeroFreeBox Q χ := ∀ s, 1 - 1/400 < s.re → |s.im| ≤ Q → LFunction χ s ≠ 0      -- same as ZeroBox
def Gchi χ y := Σ_{n ≤ y} Λ n χ n (y/n - 1) + y * logDerivLAtOne χ             -- same as gChi for χ ≠ 1
def cN (x : ℝ) (n : ℕ) : ℝ := Λ n * min 1 (x / n)
def S (Z y : ℝ) (q : ℕ) (κ : ℕ → ℂ) : ℂ := Σ_{n ≤ Z} cN y n * κ n * (n / q)        -- Jacobi symbol
def GoodC Q ψ := ψ ≠ 1 ∧ (N : ℝ) ≤ Q ∧ ZeroFreeBox Q ψ
def Box Q C τ Y X ψ := GoodC Q ψ ∧ ‖logDerivLAtOne ψ‖ ≤ C * log Y ∧ ∀ y ∈ [Y, X], ‖Gchi ψ y‖ ≤ y ^ (1/2 + τ)
def BoxAll Q C τ Y X f M := ∀ N ψ, Ind ψ f M → Box Q C τ Y X ψ
def primePairSetFirst z := PPset 8 3 (exp z)    -- primes q ≡ 3 mod 8 in (e^{z/2}, e^z]
def primeSetTwoBounds z z' q := primes d ≤ e^{z'} with d ≡ 7 mod 16, oddM z q ∣ d+1, d > e^{z'/2}
       -- oddM z q = q · ∏_{3 ≤ p ≤ z} p
def GoodQ N₀ C τ Y X z q := ∀ ξ mod N₀, BoxAll (N₀ * e^z) C τ Y X (ξ · (·/q)) (N₀ q)
def GoodD N₀ C τ Y X z z' q d := ∀ ξ mod N₀, ∀ a ≤ 1, BoxAll (N₀ * e^{z+z'}) C τ Y X (ξ · (·/q)^a · (·/d)) (N₀ q d)
def MeanSq C Z P A := ∀ y ∈ A, ∀ κ, ‖κ‖ ≤ 1 → Σ_{q ∈ P} ‖S Z y q κ‖² ≤ C · y · log y · |P|
def admitted ε Y U m₀ a₀ : 8 ∣ m₀, a₀ coprime to m₀, (1/4) log²Y · log m₀ ≤ log U, Y^{ε/6} ≤ log U ≤ Y^{ε/5} log²Y
```

The definitions file also contains a set of `…Hyp` Props: `BoxCountHyp`, `BoxTailHyp`, `MeanSquareHyp`, `IntervalHyp` and
`PrimePairOfBoxAndMeanSquareHypotheses`. In the chain I followed none of them is assumed. The proofs call the theorems
directly (`count_bad`, `tailK`, `meanSqK`). [P]

## Q2. `pair_exists`, `pair_share`, `stage1`, `stage2` and the lemmas below them

### Statements [S]

- `QH.pair_share` (`MeanSquareBounds/PairShare.lean:26`). There is a C > 0 such that for all ε < 1/52, τ > 0, K ≥ 1, η > 0 and
  N₀ > 0, and all large Y, X ≤ Y^K and z' ∈ [T log²Y, K²T log²Y], the following holds. There is a set G₁ of primes q, at least a
  1−η share of the non-empty set `primePairSetFirst T`, with every q ∈ G₁ satisfying `GoodQ`. For each such q there is a set G₂,
  at least a 1−η share of the non-empty set `primeSetTwoBounds T z' q`, with every d ∈ G₂ satisfying `GoodD`.
- `QH.pair_exists` (`PairExists.lean:9`) takes η = 1/2 and picks one q and one d. It also returns `Rows` (the congruence and
  size conditions, including q < d and p | d+1 for odd p ≤ T or p = q) and N₀ < q.
- `QH.pairEx` (`pairEx.lean:112`) applies `pair_exists` with N₀ = 8M, τ = ε/2, K = A and z' = T log²Y. It packages the result
  as `PairGood`. The `boxes` and `bounds.1` fields come from `BoxAll` through `pairEx_box`. The ξ mod M are lifted to mod 8M.
  The `bounds.2` field (|L'/L(1)| ≤ 4 log y) comes from `QH.kappa4`, not from the constant C of `Box`. [P]
- `QH.stage1` (`Stage1Succ.lean:36`). For all large Y, `primePairSetFirst T` is non-empty, and every subset B of it consisting
  of non-`GoodQ` primes has |B| ≤ η·|primePairSetFirst T|. [S]
- `QH.stage2` (`CharOf.lean:61`) is the same statement for the d-sets `primeSetTwoBounds T z' q`, for each q in the first set. [S]

### The engine: `QH.stage` (`MeanSquareBounds/StagePow.lean:41`) [S, P, read in full]

Both stages are instances of one theorem. `stage1` applies it with modulus m₀ = 8, residue 3 and U = e^T. `stage2` applies it
with ε' = 6ε/5 and modulus m₀ = 16·oddM(T,q), with a residue class a₀ that forces d ≡ 7 mod 16 and oddM | d+1. In both, Ξ is a
set of primitive characters ξ of bounded conductor F.

```lean
theorem stage : ∃ C > 0, ∀ ε τ K η R, … ∀ Y ≥ Y₀, ∀ U F m₀ a₀ Ξ, admitted ε Y U m₀ a₀ →
  (∀ p prime, p ∣ m₀ → p ≤ Y^{ε/5} ∨ (Y^K)^400 < p) → 1 ≤ F ≤ U^{1/2} → |Ξ| ≤ R → (each ξ ∈ Ξ primitive, cond ≤ F) →
  (PPset m₀ a₀ U).Nonempty ∧ ∀ B ⊆ PPset m₀ a₀ U,
     (∀ q ∈ B, ∃ ξ ∈ Ξ, ∃ M ≠ 0, ¬ BoxAll (F*U) C τ Y (Y^K) (ξ · (·/q)) M) → |B| ≤ η · |PPset m₀ a₀ U|
```

Proof outline [P]. A bad prime q lands in B₁ ∪ ⋃_ξ B₂(ξ):

1. **B₁, zero in the box.** These are the q for which some primitive twist ξ·(·/q) of conductor ≤ FU has a zero with
   Re > 1 − 1/400 and |Im| ≤ FU. `QH.count_bad` gives |B₁| ≤ C_b·(FU)^{1/4} ≤ C_b·U^{3/8}. `QH.count_a` gives
   |PPset| ≥ U^{9/10}. So B₁ is a vanishing share.
2. **B₂(ξ), large Dirichlet polynomial.** These are the q for which the polynomial
   S(Z, y, q, ξ) = Σ_{n≤Z} Λ(n)·min(1, y/n)·ξ(n)·(n/q), with Z = (Y^K)^400, exceeds y^{1/2+τ}/2 for some y ∈ [Y, Y^K].
   `QH.meanSqK` gives the mean square Σ_q |S|² ≤ C·y·log y·|PPset|. `QH.bad_share` (Markov's inequality, uniform in y over the
   window) gives |B₂(ξ)| ≤ η/(2(R+1))·|PPset|.
3. **Good otherwise.** If q is in neither set, `QH.box_of_S` turns "zero-free box + small S" into the full `Box`. This uses the
   identity G_χ(y) = −S_Z(y) − y·tail_χ(Z) (`GFiniteSplit`, with tail_χ(Z) = −L'/L(1,χ) − Σ_{n≤Z} Λχ(n)/n). It uses `QH.tailK`,
   ‖X·tail_χ(X^400)‖ ≤ Y^ε, which bounds the tail beyond X^{400} by the explicit formula inside the zero-free box. It uses
   `QH.kappaC`, |L'/L(1,χ)| ≤ C log Y.

### Key intermediate lemmas and what kind of argument each is

| Lemma | File | Statement (trimmed) | Method |
|---|---|---|---|
| `QH.count_bad`, `count_bad_core` | `MeanSquareBounds/CountBad*.lean` | #{primes q > F : some primitive χ of conductor f·q ≤ Q, f ≤ F, has a zero in the box} ≤ C·Q^{1/4} [S] | Reduces to `zero_density_box` by injectivity q ↦ χ [P] |
| `…ZD.zero_density_box : ZeroDensityBox` | `Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13` | For every finite set S of primitive characters of conductor ≤ Q, each with a zero in [1−1/400, 1) × [−Q, Q]: \|S\| ≤ C·Q^{1/4} [S] (definition in `Formalism/GL3MeanSquares/ZeroDensityBox.lean:8`) | `final_bound_of_assembly (coefficient_square_bound divisor_weight_bound) (zero_detection mollifier_identity) (blockCountOf_statement duality_inequality (pair_twist_bound pair_sum_bound)) numeric_constants` [P]. Montgomery-style zero detection with a mollifier of length Q^4, a partial sum of length 2^{8(log₂Q+1)}, dyadic blocks, a duality (large-sieve) inequality, and the trivial pair-sum bound \|Σ χ χ̄'\| ≤ q·q'. Exponents: Σ\|mco\|²n^{−2s₀} ≤ C·U^{−197/200}, giving count ≤ 8J²C·U^{3/200} with U ≲ Q^{12}, which is ≪ Q^{1/4} (`CountZDefs.lean`) [S] |
| `QH.meanSqK` | `MeanSquareBounds/meanSqK.lean:51` | `MeanSq C ((Y^K)^400) (PPset m₀ a₀ U) [Y, Y^K]` under `admitted` [S] | Mean square over primes q in a progression. Off-diagonal terms reduce to character sums handled by `QH.twistK` [N: proof not read beyond imports `twistK`, `SPsqLe`, `RRLe`, `SumCNLe`, `MeanSqAbs`] |
| `QH.twistK` | `MeanSquareBounds/twistK.lean:148` | There is one exceptional n*, and for every odd squarefree s ≤ Y^A coprime to m₀ with s ≠ n*: \|Σ_{q∈PPset} (q/s)\| ≤ Y^{−B}·\|PPset\| [S] | PNT in progressions with an exceptional-character main term, error A₀(e^{−c log X/log M} + e^{−√(c log X)}) (`pnt_progressions_relative_weak_holds`), Page's theorem across moduli (`page_across zFRDirichlet`) and Siegel's bound (`excBound := excBound_of_siegelLower siegelLower`) [P, first 25 lines]. A Landau–Page–Siegel argument |
| `QH.count_a` | `Formalism/GL3MeanSquares/…/MSqCount.lean:346` | \|PPset m₀ a₀ U\| ≥ U^{9/10} under `admitted` [N, from use in `stage`] | PNT in progressions plus the exceptional-zero bound |
| `QH.bad_share` | `MeanSquareBounds/BadShare.lean:251` | MeanSq ⇒ #{q : ∃ y ∈ [Y,X], \|S\| > y^{1/2+τ}/2} ≤ η\|P\| [S] | Markov's inequality over a geometric grid in y (r = 2^{−τ}) [N] |
| `QH.box_of_S` | `MeanSquareBounds/BoxOfS.lean:28` | GoodC Q χ, χ = κ·(·/q), \|S\| ≤ y^{1/2+τ}/2 on [Y, Y^K], Y^{ε/6} ≤ log Q ≤ Y^{ε/4} ⇒ Box Q C τ Y Y^K χ [S] | Explicit-formula split plus `tailK` and `kappaC` [N] |
| `QH.tailK` | `MeanSquareBounds/TailKExp.lean:92` | GoodC Q χ ⇒ ‖Y^K · tail_χ((Y^K)^400)‖ ≤ Y^ε [S] | Explicit formula inside the box: (X^{400})^{−1/400} = X^{−1} [N] |
| `QH.kappa4` | `MeanSquareBounds/Kappa4Loglog.lean:126` | GoodC Q χ, log Q ≤ A·Y^{ε/5}log²Y ⇒ \|L'/L(1,χ)\| ≤ 4 log Y [S] | \|L'/L(1)\| ≤ Σ_{n≤z} Λ(n)/n + small with z = (log Q)^{1000} (Mertens), so the bound is ≈ 1000·log log Q ≤ 200ε log Y + o(log Y) [P] |
| `QH.thinH : ThinH` | `MeanSquareBounds/GaussSumFunctionEq.lean:55` | Host characters satisfy \|gChi(χ,y)\| ≤ y·exp(−c x^{ε/8}) for y ≥ exp(x^{ε/3})/3, assuming `RealBox` (no real zero > 1 − 1/400 for real characters with q \| N or d \| N) [S] | Classical PNT for characters in the de la Vallée-Poussin range. The `RealBox` hypothesis is supplied by the `boxes` field of PairGood through `HostGood.BoxW` [N] |

### Is any input of unusual strength?

No, as far as the statements show. [S, P]
- The only zero-free conclusions in this chain are `ZeroFreeBox`es of width 1/400, and they are **outputs** of
  `zero_density_box`. They are never hypotheses of the good-pairs theorem.
- The "Hyp" Props in `SecondEstimateOfIntervalHypothesis.lean` are not assumed on this path.
- No structure field carries a zero-free assumption into the proof of `pairEx`. `GoodC` appears only as a hypothesis of
  the local lemmas `box_of_S`, `tailK`, `kappaC` and `kappa4`, and `stage` discharges it by excluding B₁.
- There is one ineffective input: Siegel's theorem through `excBound`, in the PNT in progressions. It is classical.
- The strength of `zero_density_box` is modest. Montgomery's estimate gives roughly Q^{0.03} at σ = 1 − 1/400 and T = Q; the
  archive needs only Q^{1/4} and proves it with a crude version of the same method.

## Q3. How good pairs are consumed

### `winPairs` (`CharacterBoxes/WinPairs.lean:5`) [S, P read in full]

```lean
theorem winPairs : ∀ ψ eps c, 0 < eps → eps < 1/52 → 1 ≤ c → VWinAt ψ 401 → PairEx →
  ∃ J ≥ 1, ∀ y, ∃ Z ≥ y, ∀ x ∈ [Z, Z^{3/2}], ∃ Y q d e, WinDatum ψ eps J c x Y q d e
structure WinDatum ψ eps J c x Y q d e : x^{1/J} ≤ Y ≤ x, PairGood ψ.N eps Y x q d,
  x^{2+8eps} ≤ c·2^e ≤ 2x^{2+8eps},  ∀ E, IsChiField ψ e q d E → VVle E ⌊x^400⌋ (sqrt (exp (x^eps)))
```

The proof proceeds as follows.
1. Choose the 2-power level e(x) with 2^e ≈ x^{2+8ε} (`exists_pageN`), and get J and X₀ from VWin.
2. Choose X so large that Y := X^{1/J} is beyond PairEx's threshold, and take a good pair (q, d) at scale Y with A = J.
3. VWin applied to that pair gives a W with Y ≤ W and W² ≤ X such that the Ш bound holds for all x' ∈ [W, W²].
4. Rescale x = k·x' (with k^{2+8ε} = c) and use [kW, (kW)^{3/2}] ⊆ [W, W²], which needs k³ ≤ W. The threshold ⌊(kx')^{400}⌋
   is absorbed into ⌊x'^{401}⌋ using k^{400} ≤ x'. This is where Ct = 401 = 400 + 1 comes from. [P]

So for every x in windows [Z, Z^{3/2}] there are an auxiliary good pair (q, d) at a scale Y ∈ [x^{1/J}, x] and a host field E,
cut out of a cyclotomic field by ψ, the Jacobi symbols mod q and d, and the 2-power level 2^{e+2}. On these, both the Ш-length
bound and all the PairGood properties hold.

### `supplyOfAdmOf` → `supplyChi` → `HostExW (3/2)` [S]

`UpperTheory.T3.supplyOfAdmOf` (`ShortNorms/supplyOfAdmOf.lean`) calls `winPairs ψ eps c … hV QH.pairEx`. It takes a supply
hypothesis `hSup`: from PairWin, PairGood, FieldRows and admissibility it builds a `Host` H with `HostGood …`. `HostGood`
includes `BoxW`, whose real-zero clause is `RealBox`, plus `ThinOK` and `BadOK`. It concludes:

```lean
HostExW (3/2) (fun _ s R H _ => EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧ VVle H.E R.t (sqrt s.b))
```

`supplyChi ψ : VWinAt ψ 401 → HostExW (3/2) (GChi ψ).req` (`CharacterBoxes/SupplyChi.lean`) discharges `hSup` and `hAdm`
through `supplyOfAdm` and `admissibleClassesTwistedChar`. [S; I did not read `supplyOfAdm` or `hSup`'s discharge.]

`EAtH Λ H TT x eps C` (`…/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:144`) [S] has these fields:
- `o_eq`, `kept`, `ps`: bookkeeping that the host's characters include the level's characters and its exceptional character.
- `shares`: TT is equidistributed in cosets with error x^{−1+ε}.
- `bdG`: pointwise G-bounds for the "bounded" characters, meaning the twisted ones.
- `bdL`: |L'/L(1)| ≤ C log x for the same characters.

### `zeroFreeAll_of_topG` and the Landau-window theorem [S, P]

`zero_free_all_of_green_v_win hG hV h` (`ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12`) is

```lean
zeroFreeAll_of_topG (la := 3/2) _ (forall_goal_of_shape_of_hyps … (shape_closed_link_n_of_green hG) …) (fun ψ => supplyChi ψ (hV ψ))
```

`zeroFreeAll_of_topG` (`CharacterBoxes/ZeroFreeAllOfTopG.lean:26`) applies the generic engine `zeroFreeOn_of_tiedWin_cyc`
(`…/TotientGaloisClasses/TopWin.lean:90`) to Λ = `Level.cyc ψ`, the characters in the cyclic group generated by ψ. The engine
needs three inputs.

1. **`ChebyshevInequalityOnWindows Λ`**, supplied by `level_gm_le_on_family_scales` (proved through `core_gm`,
   `PrimitiveCosets/CoreGm.lean:12`). For each family Fm with `EFamC Λ` (i.e. `EAtH` at every member) and `ChainTied` on its
   windows: Λ.Gm(x) ≤ x^{1/2 + (eD+eL+7)ε} for large x in the window set. [S] Here
   `Λ.Gm(y) = Gz(y) + Σ_{ψ' ∈ Λ, ψ' ≠ 1} wt(ψ')·Re gChi(ψ', y)`, with weight 1 for the exceptional character and
   1/(3o+1) for the others. So Gm is a positive-weight Landau-type combination of the zeta term and the level's characters.
   `core_gm` consumes `EAtH` (from good pairs) and `CoreAtH`, a ~30-field bundle that I did not open. It is where the Ш-length
   bound must enter. [N]
2. **`Λ.FormB`**, supplied by `UpperTheory.Comparison₂.formB` (`PrimitiveCosets/Imports.lean:8`). It is a localized Landau
   theorem [S, P]:
   ```lean
   def FormBAt la := ∀ θ ∈ (0,1), HasWindows {x | Λ.Gm x ≤ x^θ} la → Λ.ZeroFreeAbove θ
   def HasWindows S la := ∀ y, ∃ Y ≥ y, ∀ x ∈ [Y, Y^la], x ∈ S
   ```
   That is: a one-sided upper bound Gm(x) ≤ x^θ, holding only on windows [Y, Y^{la}] for arbitrarily large Y and some fixed
   la > 1, implies that no L(s, ψ'), ψ' ∈ Λ, vanishes for Re s > θ. It is proved by `Deduction.zeroFree_of_rpow_window` →
   `lemmaL` → `landau_window` (`DedekindLFunctions/LandauTheorems/landauWindow.lean:83`). The abstract version is stated for
   g(u) = Gm(e^u) and its Laplace transform Φ, with `PoleData`: Φ is meromorphic on Re s > 0, its poles are exactly the zeros,
   and real poles have positive residue. The argument looks at Taylor coefficients (−1)^kΦ^{(k)}(σ)/k! with k ≈ U at a large
   real σ > 2. The kernel u^k e^{−σu}/k! concentrates on the window [U, (1+δ)U]. The bound used is
   ‖Φ^{(k)}(σ+iγ)‖ + Re Φ^{(k)}(σ) ≤ ∫ (|g| + g)·kernel = 2∫ g⁺·kernel, so only a one-sided bound on g is needed. A nearest
   pole β > θ, located via `landau_dichotomy` and `landau_nearest`, forces these coefficients to be ≍ (σ−β)^{−k}. The window
   bound caps them by e^{ηU}(σ−θ)^{−k}, a contradiction (`landau_window_contra`). This is the Landau/Pólya Ω± method with an
   explicit window.
3. **`ChebyshevInequalityAtWindowScale la Λ`**, from `TopG` (given `HostExW la`) through `FamilyClassConnected`: for each small
   ε a family whose window set `HasWindows … la` carries `ChainTied` and `EFamC`. `TopG` comes from `shape_closed_link_n_of_green`
   and Green's theorem, which I did not read.

**Logical shape** [P for `level_of_tiedWin`, TopWin.lean]. Fix ψ and a point s with Re s > 1/2. Choose ε with
(eD+eL+7)ε ≤ (Re s − 1/2)/2. The window family for that ε gives Gm(x) ≤ x^{1/2+(eD+eL+7)ε} on windows [Z, Z^{3/2}].
`FormB` then gives L(s', ψ') ≠ 0 for Re s' > 1/2 + (Re s − 1/2)/2, which includes s. So the deduction is a **direct limit
ε → 0, not an induction on the width of a zero-free region**. Every ε is handled by its own family. No zero-free input about ψ
itself is used, only about the twists. Three things depend on the scale: the zero-free width 1/400 of the twist boxes is
fixed, the scale Y only needs to be large, and ε enters only through the exponent.

I found no "bootstrap" in the sense of a zero-free region improved step by step. The announcement's
"W(1_(0,1]) + (~X^η)·1_(0,1/X] ≥ 0 gives > 1 − η" fits `landau_window`, where one-sided positivity on a window localized at
scale X yields zero-freeness, or the inside of `CoreAtH`/`ChainTied`, which I did not open. [N]

## Q4. Circularity and dependency direction

I computed import closures by reading `import` lines only. The script follows modules under `src/`; Mathlib is outside the tree
and was not followed.

| Start module | Local closure | Contains EveryCharacter / MainConclusion / CritLine / ZeroFreeAllOfTopG / TopPlug / SupplyChi / WinPairs / RowSrc? |
|---|---|---|
| `MeanSquareBounds.pairEx` | 293 | none. It contains `CharacterBoxes.ExistsPageN` (definitions of `WinPair`, `VWinAt`), which is upstream |
| `DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow` | 30 | none |
| `PrimitiveCosets.Imports` (`formB`) | 132 | none |

Within the union of the closures of `pairEx` and `PrimitiveCosets.Imports` (402 files), I grepped for the following.
- `EveryCharacter|ZeroFreeAll|RiemannHypothesis|GRH`. The hits are definitions in which `RiemannHypothesis` is the
  *conclusion* of an implication Prop: `PowerBoundGivesRiemannHypothesis`, `GrowthBoundGivesRiemannHypothesis`,
  `ChainGivesRiemannHypothesis`, `RiemannHypothesisOfHalfLinks` (`Formalism/SizeWindowBrackets/*`, `Formalism/HalfLinks/Statement.lean`).
  There are also the *definitions* `ZeroFreeOn`/`ZeroFreeAll` themselves (`ExplicitFormulaErrorOfHostConditions.lean`). None of
  these is a hypothesis of `pairEx`, `stage` or `formB`.
- `sorry`, `axiom`. No hits.

Verified direction:
```
zero_density_box, meanSqK, twistK (PNT-AP + Page + Siegel), kappa4, tailK
   → stage → stage1, stage2 → pair_share → pair_exists → pairEx : PairEx
landau_window → lemmaL → zeroFree_of_rpow_window → formB : ∀ Λ, Λ.FormB
PairEx + VWinAt ψ 401 → winPairs → supplyOfAdmOf → supplyChi → HostExW (3/2)
HostExW + TopG(Green) + formB + level_gm_le_on_family_scales → zeroFreeAll_of_topG : ZeroFreeAll
   → imprimitive → EveryCharacter → RH
```
Good pairs, the Landau-window theorem and VWin's definitions are all upstream of `ZeroFreeAll`. The kernel would reject a
genuine cycle anyway, but here the import direction is also consistent.

The mathematically relevant non-circularity point is this: every zero-free statement in PairGood is about twisted characters
whose conductor is divisible by q or d, never about ψ. [S]

## Q5. Constants

| Constant | Where it enters | Role, and what breaks if changed |
|---|---|---|
| **1/400** (width of box) | `ZeroBox`, `ZeroFreeBox`, `s0 = 1 − 1/400`, `RealBox`, `NoExc` | Fixed width of the twist boxes. It is paired with the polynomial length Z = X^{400}: the tail Σ_{n>Z} Λχ(n)/n ≈ Z^{−1/400} = X^{−1}, which makes y·tail ≤ Y^ε (`tailK`) [S]. A wider box would need a stronger zero-density input. A narrower one forces longer polynomials (Z = X^{1/width}) and larger Ct. |
| **400 / 401** | `S((Y^K)^400 …)`, `stage` condition "p ∣ m₀ ⇒ p ≤ Y^{ε/5} or p > (Y^K)^{400}", `WinDatum.bound` uses ⌊x^{400}⌋ Tate twists, `VWin := ∀ψ, VWinAt ψ 401` | 401 = 400 + 1, the extra 1 absorbing the constant k in `winPairs` [P]. Ct is tied to 1/width. The VWin hypothesis would have to be re-proved with the new Ct. |
| **ε < 1/52** | `kappa4`, propagated into `PairEx`, `VWinAt`, `HostExW`, `winPairs`, `supplyOfAdmOf` | From `kappa4` [P]: \|L'/L(1)\| ≤ log z + 2 + O(1) with log z = 1000·log log Q ≤ 200ε log Y + O(log log Y). To stay ≤ 4 log Y one needs 200ε < 4, i.e. ε < 1/50. 1/52 leaves slack (h5: ε·log Y ≤ log Y/52). Changing the constant 4 in `PairGood.bounds` moves this threshold. |
| **Y^{ε/5}** (=T) | `WinPair`, `height`, `primePairSetFirst`, `admitted` | log q ≈ T and log d ≈ T log²Y [S]. Lemmas need Y^{ε/6} ≤ log(conductor) ≤ Y^{ε/4} (`box_of_S`, `tailK`, `kappaC`) [S]. The upper bound keeps explicit-formula losses (powers of log Q) below Y^ε. The lower bound makes all moduli polynomial in Y (s ≤ Y^A in `twistK`) tiny compared with log q, so the PNT in progressions saves any power Y^{−B} [N]. |
| **log²Y factor in d** | `WinPair.d_lo/d_up`, `admitted.log_m : (1/4) log²Y · log m₀ ≤ log U` | The d-progression has modulus m₀ = 16·oddM(T,q) ≈ e^{3T} (`PrimorialBound`). The condition log U ≥ (log²Y/4)·log m₀ makes the PNT-AP error exp(−c log U/log m₀) ≈ exp(−c' log²Y) superpolynomially small [S for the condition, N for the purpose]. |
| **mod 8 = 3, mod 16 = 7, p ∣ d+1 for p ≤ T, q ∣ d+1** | `WinPair`, `Rows`, `ClassAdmissible`, `ClassSplit` | q, d ≡ 3 mod 4, so −q and −d are fundamental discriminants. `ClassSplit` [S] says these congruences make x² − x + (d+1)/4 split mod q and mod every prime ≤ T, i.e. q and all small primes split in Q(√−d). d ≡ 7 mod 8 also splits 2. Used for the CM/norm-prime host construction (`IsNormOne`, `normPrimes`) [N]. The mod-16 refinement presumably interacts with the 2-power cyclotomic level 2^{e+2} [N]. |
| **2 + 8ε** | `PageN`, `WinDatum.n_lo/n_up` | 2-power level 2^e ≈ x^{2+8ε}, so the host field's 2-part has degree ≈ x^{2+8ε} [S]. Its role (equidistribution `Shares` with error x^{−1+ε}, counting) is inside `CoreAtH`, which I did not read [N]. |
| **la = 3/2** | `TopPlug` (`zeroFreeAll_of_topG (la := 3/2)`), `winPairs` windows [Z, Z^{3/2}] | Any la ∈ (1, 2) works for this step: `FormB` holds for every la > 1, and VWin gives windows [W, W²]. 3/2 leaves room for the constant k (needs k³ ≤ W) [P]. |
| **1/2 + ε/2, τ = ε/2** | `PairGood.bounds`; `pairEx` uses τ = ε/2 | Exponent of the square-root bound on the twists. It is consumed as `bdG` in `EAtH` with total loss (eD+eL+7)ε in `core_gm` [S]. |
| **Q^{1/4}, U^{9/10}, U^{3/8}** | `ZeroDensityBox`, `count_a`, `stage_pow` | Bad moduli ≤ C(FU)^{1/4} ≤ C·U^{3/8} ≪ η·U^{9/10} ≤ η·\|PPset\| [P]. A weaker zero-density exponent, up to ≈ 9/10 after accounting for F ≤ U^{1/2}, would still suffice. |
| **197/200, 3/200, Q^4, 2^{8(log₂Q+1)}** | `CountZDefs.lean` | Mollifier length, partial-sum length and block exponents of the zero-density argument. 197/200 < 2s₀ − 1 = 199/200 leaves room for divisor-function losses [S]. |

## Five places a number theorist should read first

1. **`UpperTheory.Comparison₂.core_gm`** (`Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12`), together with
   `CoreAtH` (`PrimitiveCosets/CoreAtH.lean`) and `ChainTied` (`Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97`).
   This is where the one-sided bound Gm(x) ≤ x^{1/2+O(ε)} for ψ's cyclic level is produced from the host data: the Ш-length
   bound VVle plus the good-twist bounds (`EAtH`). It is the step that reaches 1/2. The good-pairs file does not.
2. **`Deduction.landau_window`** (`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean:83`) via
   `UpperTheory.Comparison₂.formB` (`PrimitiveCosets/Imports.lean:8`) and `Formalism.HC.Level.FormBAt`
   (`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean:30`). This is the localized Landau theorem:
   one-sided bounds on windows [Y, Y^{la}] imply zero-freeness. Check `PoleData` (`DedekindLFunctions/LandauZeroFreeCriterion.lean:15`)
   and how `poleData F` realizes Gm with positive real residues.
3. **`QH.stage`** (`Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean:41`). The whole good-pairs argument fits on
   one page here: zero-density for B₁, mean square plus Markov for B₂, and `box_of_S`.
4. **`Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.zero_density_box`**
   (`Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`), with its definitions in `CountZDefs.lean`
   and the statement `ZeroDensityBox` in `Formalism/GL3MeanSquares/ZeroDensityBox.lean`. This is the only zero-free input, and it
   is classical.
5. **`QH.twistK`** and **`QH.meanSqK`** (`MeanSquareBounds/twistK.lean:148`, `meanSqK.lean:51`), with
   `pnt_progressions_relative_weak_holds` (`…/JacobiCharacterSums/PNTFinal.lean:22`) and `excBound`
   (`Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:32`). This is the mean square over the family, including
   the handling of the single exceptional modulus n*. Read it together with `QH.kappa4` (`Kappa4Loglog.lean:126`) for where
   ε < 1/52 comes from.

## Not read

- Proof bodies: `meanSqK`, `bad_share`, `box_of_S`, `kappaC`, `stage1_prim`, `count_a`; the internals of the CountZ*
  lemmas; `landau_dichotomy` and `landau_nearest`.
- `supplyOfAdm` and the discharge of `hSup`; `TopG` and `shape_closed_link_n_of_green`; and `CoreAtH`, read beyond its use in
  `core_gm`.

Everything stated about those is tagged [N] or [S].
