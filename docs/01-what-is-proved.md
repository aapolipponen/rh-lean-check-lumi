# 1. What is proved

The archive ends in five theorems in `Main.lean`: the Riemann Hypothesis in Mathlib's formulation and four statements of the Generalized Riemann Hypothesis (GRH) for Dirichlet L-functions. All five are short consequences of one internal statement, `UpperTheory.EveryCharacter`, so everything difficult in the archive sits underneath that single statement.

This page says what the final statements are, how they reduce to `EveryCharacter`, and how `EveryCharacter` is assembled from three inputs. It does not judge whether the argument is correct. For how the reports were produced and what the status markers mean, see [README.md](README.md).

## A few Lean words for number theorists

| Term | Meaning here |
|---|---|
| declaration | a named item in Lean: a `def` (definition), `theorem`, `structure` (a record type), `abbrev` (a transparent definition) |
| `Prop` | the type of mathematical statements. A `def X : Prop := …` *names* a statement; it asserts nothing |
| `theorem t : X := proof` | a proof of `X` that the Lean kernel has checked |
| hypothesis bundle | a `structure` whose fields are statements. A theorem that takes such a structure as input is conditional on it, unless the bundle is itself proved somewhere (it is, throughout this archive) |
| axiom | an unproved assumption. The final theorems use only Lean's standard three: `propext`, `Classical.choice`, `Quot.sound` |
| Mathlib | the community library of formalized mathematics. `RiemannHypothesis`, `riemannZeta` and `DirichletCharacter.LFunction` are Mathlib definitions, not the archive's |
| namespace | a name prefix such as `UpperTheory.` or `GlobalTheory.`. See [glossary.md](glossary.md) |

## The five theorems

`Main.lean` has 12 lines, 2 direct imports and 5 declarations, and its import closure is the whole archive of 175,187 modules (structure.md; static-reachability.md). The reports name two of the five theorems explicitly:

```lean
Main.riemannHypothesis : RiemannHypothesis        -- Mathlib's definition
  := rhOfAll
LFunction_ne_zero_of_half_lt_re                   -- Main.lean line 8
```

(skeleton.md; static-reachability.md, reference chains.) The other theorems are stated with the four definitions in `Statements.lean`: static-reachability.md records that the statement constants of the five roots live in `Statements`, apart from Mathlib's `RiemannHypothesis`. The reports quote neither `Main.lean` nor `Statements.lean` verbatim, so the definitions below are given as the first statements review describes them. [statement read] (statements-review.md §0)

An alternative entry point used by mirrors is `Supplements/Kernels/MainTheorems.lean`, which proves `allChi : UpperTheory.EveryCharacter` (MainTheorems line 7) and passes it to `Formalism.VW.rh_of_every` (web-briefing.md §C; static-reachability.md).

## The four definitions in `Statements.lean`

`Statements.lean` is 16 lines with 4 declarations (structure.md; static-reachability.md). All four use only Mathlib objects. [statement read] (statements-review.md §0)

| Definition | What it says | Reviewer's remark |
|---|---|---|
| `RiemannZetaZerosOnLine` | every zero of `riemannZeta` that is not a trivial zero −2(n+1), and is not s = 1, has real part 1/2 | the extra hypothesis s ≠ 1 is harmless |
| `DirichletLNonvanishingRightOfHalf` | L(χ, s) ≠ 0 for every Dirichlet character χ and every s with Re s > 1/2, except at the pole (χ = 1, s = 1) | this is the same content as `EveryCharacter` below |
| `DirichletLZerosOnLine` | for every Dirichlet character, zeros in the open critical strip lie on Re s = 1/2 | |
| `PrimitiveDirichletLZerosOnLine` | the same for primitive characters | |

The reviewer's verdict is that these are faithful statements of RH and of GRH for Dirichlet L-functions (statements-review.md §0). "GRH" here means Dirichlet L-functions only, not L-functions of number fields or automorphic forms (web-briefing.md §C, Deicyde notes).

## The working statement: `UpperTheory.EveryCharacter`

Verbatim, as quoted in skeleton.md:

```lean
∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
  1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

In words: for every modulus N ≥ 1, every Dirichlet character χ mod N and every s with Re s > 1/2, the Dirichlet L-function L(s, χ) does not vanish, except that the trivial character is allowed its pole at s = 1. It is stated entirely with Mathlib objects. [statement read] (skeleton.md §1)

## From `EveryCharacter` to the five theorems

The reductions are short and use only classical facts. [proof outline read] (skeleton.md §1)

| Target | Declaration | Argument |
|---|---|---|
| Mathlib's `RiemannHypothesis` | `Formalism.VW.rh_of_every` (`Formalism/GammaFactorNonvanishing/CritLine.lean`); a second copy `riemannHypothesis_of_everyCharacter` (its file is not named in the reports; structure.md lists a module `…/CharacterBoxes/RiemannHypothesisOfEveryCharacter`) | take N = 1, so L(s, 1) = ζ(s). The functional equation of the completed zeta function reflects any zero with Re s < 1/2 to one with Re s > 1/2 |
| zeros on the line, primitive χ | `critLine` | functional equation of the completed L-function of a primitive character |
| zeros in the strip, any χ | `Claim.strip` | pass from χ to the primitive character inducing it; the extra Euler factors do not vanish in the strip |

So the reduction from RH to `EveryCharacter` is about a page of mathematics. The entire weight of the archive sits on `EveryCharacter` (skeleton.md §1).

## How `EveryCharacter` is obtained

```
UpperTheory.FinalTheorems.everyCharacter                   …/CharacterBoxes/MainConclusion.lean
  := everyCharacter_of_row galoisLocalGlobalStrong_recParameter
everyCharacter_of_row h
  := every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)
```

[proof outline read] (skeleton.md §2). The final theorem `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` sits at line 810 of `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, a file of 814 lines with 201 direct imports and 151,286 modules beneath it (structure.md; vacuity-check.md Q1).

It consumes three inputs.

| # | Input | Declaration | Plain statement | Classical analogue | Status |
|---|---|---|---|---|---|
| 1 | Galois representations | `h : UpperTheory.GalStar.Row0b recT`, proved as `galoisLocalGlobalStrong_recParameter` | for a CM field E, a prime ℓ and a regular algebraic polarized cuspidal automorphic π of GL_a over E, there is a continuous semisimple ℓ-adic Galois representation with the expected Hodge–Tate weights, a weak form of local–global compatibility away from ℓ, and p-adic Hodge properties above ℓ | Harris–Taylor, Shin, Chenevier–Harris, Caraiani; the archive's version is weaker (statements-review.md row 20) | [statement read]; construction in [05](05-galois-representations.md) |
| 2 | Partial local Langlands | `recTExists`, with the predicate `IsRecT` | a map from irreducible representations of GL_n over a local field to Weil–Deligne representations, pinned down only on "Good" representations | local Langlands for GL_n (Harris–Taylor, Henniart, Scholze), in a much weaker form | [statement read] (statements-review.md row 21) |
| 3 | Window bound | `vwin_of_row h : UpperTheory.Top.VWin` | a bound on a weighted sum of lengths of Tate–Shafarevich-type groups Ш¹ of large abelian fields | no published analogue | [statement read]; proof in [06](06-window-bound.md) |

The last step from these to `EveryCharacter` goes through `Formalism.HC.ZeroFreeAll`: `VWin` together with a "Green"-type input gives the zero-free statement `ZeroFreeAll`, and `imprimitive` passes from that to all characters (skeleton.md §2; the chain is `zeroFreeAll_of_topG → imprimitive → EveryCharacter` in analytic-core.md Q4). The route through the analytic endgame is in [03](03-analytic-endgame.md).

> **Correction.** skeleton.md says the Galois representations in input 1 are "built from theta lifts", because the one-line proof is `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK`. The later study theta-chain.md, confirmed by frontier-c-galois.md, found otherwise. The representations come from ℓ-adic étale cohomology of a Harris–Taylor-type Shimura variety built in the archive, extended to all odd-rank forms by congruences and pseudo-characters. The theta lift enters only to reduce even rank to odd rank. [proof outline read] (theta-chain.md Q1–Q2; frontier-c-galois.md Q1–Q6)

## The "literature" layer

The two large assembly files collect named classical theorems into hypothesis bundles and then prove the bundles (skeleton.md §3).

- `…/DenseThresholdCases/TopMainZj.lean` (75 lines) builds `VWin` from bundles for local representation theory (18 fields), automorphic forms (15 fields) and CM / abelian varieties (11 fields).
- `EveryCharacterOfLiteratureOfVWin.lean` adds a complex-geometric and Arakelov bundle: resolution of singularities, Kawamata–Viehweg and Nadel vanishing, L² extension, arithmetic Hilbert–Samuel, Chow forms, heights of cycles, Poincaré–Lelong, Zarhin, Siegel's formula and theta-integral matching.

Each named statement lives as a `Prop` in the namespace `GlobalTheory.Published`, and is established by a theorem in `UpperTheory.LiteratureTheorems` with a name ending in `_of_literature`, `_holds` or `_outright` (skeleton.md §3; literature.md). These are theorems, not assumptions: the final theorems have no hypotheses and no axioms beyond Lean's three.

Many `_of_literature` theorems take an argument `O : OpenImageCondition`, a structure with one field, the Galois statement `Row0b` of input 1 (skeleton.md §3; frontier-d-window.md Q5). By a text search, 132 of the 155 `Published` statements are proved without mentioning `O` (literature.md). Where `O` is mentioned, it can mean only that the term is assembled from other `_of_literature` terms that take `O`, not that the Galois statement is used (statements-review-3-geometry.md, introduction). For example `elliptic_main_theorem_cm_of_open O := PositivityTheory.Prw.ellipticMainTheoremCM_holds` ignores `O` (skeleton.md §3).

`out/literature.json` lists 242 `_of_literature` theorems with 182 distinct statement constants, 155 of them in `GlobalTheory.Published` (literature.md; static-reachability.md). 105 named statements have been reviewed for whether they say what their names claim; the consolidated table is [07-named-theorems.md](07-named-theorems.md).

## What this reduction does and does not tell you

- It tells you that if the archive compiles and the kernel accepts it, then `EveryCharacter` is proved from Lean's three axioms, and RH and Dirichlet GRH follow by classical arguments that are themselves formalized.
- It relies on Mathlib's definitions of `RiemannHypothesis`, `riemannZeta` and `DirichletCharacter.LFunction`, and on the four definitions in `Statements.lean`, which the rhcheck README asks a human to read (rhcheck/README.md, "What this does and does not establish"). The first statements review read them and judged them faithful (statements-review.md §0).
- It does not tell you whether anyone understands the argument underneath `EveryCharacter`. That is the subject of pages 02 to 06 and of the open list in [10](10-open-frontier.md).


## Appendix: the two files verbatim

`src/Statements.lean` (imports only Mathlib):

```lean
import Mathlib

def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

`src/Main.lean`:

```lean
import Statements
import Supplements.Kernels.MainTheoremsAll

theorem riemannHypothesis : RiemannHypothesis := rhOfAll

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

`RiemannHypothesis` in the first theorem is Mathlib's own definition (`Mathlib.NumberTheory.LSeries.RiemannZeta`), not a definition from the archive.
The lemma `UpperTheory.riemannHypothesis_of_everyCharacter` is in
`Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean`; the copy used by `Main` is
`Formalism.VW.rh_of_every` in `Formalism/GammaFactorNonvanishing/CritLine.lean`.

## Sources

- rhcheck/results/skeleton.md (§1–§3), with its correction from analysis/theta-chain.md and analysis/frontier-c-galois.md
- rhcheck/results/structure.md, rhcheck/results/literature.md, out/literature.json
- analysis/statements-review.md (§0, rows 20 and 21)
- analysis/statements-review-3-geometry.md (introduction, on `uses_O`)
- analysis/static-reachability.md (roots and reference chains)
- analysis/vacuity-check.md (Q1, final call chain)
- analysis/frontier-d-window.md (Q5, `OpenImageCondition`)
- analysis/web-briefing.md (§C, entry points and the meaning of "GRH")
- rhcheck/README.md (trust base)
