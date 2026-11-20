# Top-level skeleton of the proof (read from the source, not from the compiled terms)

This is a reading of the dozen files at the top of the import tree. It says how the final theorems are
assembled and from what; it is not a judgement of the mathematics. Names are the archive's own.

## 1. From the main statement down

```
Main.riemannHypothesis : RiemannHypothesis                      (Mathlib's definition)
  := rhOfAll
  := Formalism.VW.rh_of_every allChi                            Formalism/GammaFactorNonvanishing/CritLine.lean
allChi : UpperTheory.EveryCharacter
  := UpperTheory.FinalTheorems.everyCharacter                   …/CharacterBoxes/MainConclusion.lean
```

`UpperTheory.EveryCharacter` is the working form of GRH:

```lean
∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
  1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

It is stated entirely with Mathlib objects. Everything after it is short and elementary:

- RH from it: take `N = 1`, then the functional equation of the completed zeta function to reflect a zero
  with real part below 1/2 (`rh_of_every`, and a second copy `riemannHypothesis_of_everyCharacter`).
- Zeros on the line for primitive χ: the functional equation of the completed L-function (`critLine`).
- Zeros in the strip for any χ: pass to the primitive character; Euler factors do not vanish (`Claim.strip`).

So the entire weight of the archive sits on the single statement `EveryCharacter`.

## 2. How `EveryCharacter` is obtained

```
everyCharacter
  := everyCharacter_of_row  galoisLocalGlobalStrong_recParameter
everyCharacter_of_row h
  := every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)
```

Three ingredients:

1. **`h : GalStar.Row0b recT`**, a Galois-representation statement: for every CM field `E`, prime `l`,
   regular algebraic polarized cuspidal `π` of `GL_a` over `E`, there is a continuous semisimple
   `r : Gal → GL_a(Q̄_l)` with prescribed Hodge–Tate weights, local–global compatibility away from `l`
   (in the weakened form `AwayB`) and crystalline / de Rham / potentially semistable behaviour above `l`.
   Its proof is one line: `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK`
   (…/GaloisRepresentations/IntegralStructures/RowSrc.lean). So the Galois representations are built from
   theta lifts inside the archive.
2. **`recTExists`**, existence of a local Langlands correspondence `recT` for `GL` in the form the archive
   needs (`IsRecT`).
3. **`vwin_of_row h : UpperTheory.Top.VWin`**, the "window" statement. `VWin := ∀ ψ, VWinAt ψ 401`. Unfolded,
   it bounds, for suitable auxiliary primes `q ≡ 3 mod 8`, `d ≡ 7 mod 16` in a window and number fields `E`
   cut out of a cyclotomic field by `ψ` and Jacobi symbols, a weighted sum over primes `l` of lengths
   `shaLen` of Galois-cohomology (Tate–Shafarevich-type) groups, by `sqrt(exp(x^eps))`. This is where the
   Iwasawa-tower / Galois-cohomology bound of the announcement's timeline enters.

The last step to `EveryCharacter` (`plugAll`): `VWin` plus a Green-type input give `Formalism.HC.ZeroFreeAll`,
and `imprimitive` passes from that to all characters.

## 3. The "literature" layer

The two big assembly files collect named classical theorems into structures and feed them to the argument:

- `TopMainZj.lean` builds `VWin` from three bundles:
  - **local representation theory** (18 fields): Bernstein–Zelevinsky finiteness and geometric lemma,
    Zelevinsky classification, Moy–Prasad, Langlands classification and exhaustion for `GL`, local converse
    theorem, depth-zero induction, Brauer, Chevalley units, Green's regular characters;
  - **automorphic** (15 fields): rapid decay of cusp forms, Harish-Chandra finiteness, Jacquet–Shalika,
    cuspidal spectrum of `GL`, base change, Gelfand–Kazhdan, Clozel purity, global Artin reciprocity, ray
    class fields, Hecke ℓ-adic characters, de Rham ⇒ potentially semistable (Berger);
  - **CM / abelian varieties** (11 fields): Grothendieck deformation theory, de Rham comparison for abelian
    schemes, dual abelian scheme, period comparison, Gauss–Manin, Serre–Tate, main theorem of CM for
    elliptic curves, Hilbert class field via `j`, Siegel–Klingen / Deligne–Ribet, functional equations of
    partial zeta and Hecke L-functions.
- `EveryCharacterOfLiteratureOfVWin.lean` (814 lines, 201 direct imports, 151,286 modules beneath it) adds
  the **complex-geometric / Arakelov** bundle: resolution and principalisation in characteristic zero,
  Kawamata–Viehweg and Nadel vanishing, L² extension, arithmetic Hilbert–Samuel (Moriwaki), Chow forms and
  heights of cycles, Poincaré–Lelong, Zarhin, Siegel's formula, and the theta-integral matching.

Each of these is a theorem proved inside the archive (`…_holds`, `…_outright`, `…_of_literature O`), not
an assumption: the final theorems have no hypotheses and, per everyone's axiom checks, no axioms beyond
Lean's three. Many carry a hypothesis `O : OpenImageCondition`, a structure with one field, the Galois row
statement of item 1; for several the proof ignores `O` (e.g. `elliptic_main_theorem_cm_of_open O :=
PositivityTheory.Prw.ellipticMainTheoremCM_holds`).

## 4. What this suggests for anyone trying to understand it

- The reduction RH ⇐ `EveryCharacter` is a page. All difficulty is in `EveryCharacter`.
- The natural units to study are the fields of the four bundles above: each is a named classical theorem
  with its own Lean statement under `GlobalTheory.Published.*`, and the dependency map
  (`used.md`, once the build finishes) will say how much code each one actually pulls in.
- Whether every bundled field is used by the final proof term is exactly what the dependency map answers.
