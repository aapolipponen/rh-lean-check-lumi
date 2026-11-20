# Web briefing, 2026-11-20 about 21:15 UTC (web search only; X/browser not used)

## A. Verification
- Sutherland page https://math.mit.edu/~drew/grh/ : the fetched copy says "last updated 19:45 UTC" (may be cached; recheck). Compile 175,187 modules passed (16:43 UTC); five Main.lean theorems use only propext, Classical.choice, Quot.sound; leanchecker replay of all modules passed (~18:17); nanoda accepts the export (19:05:45 UTC, 27m42s, 80 threads); export sha256 bd484ac9... matches Deicyde CI. Lean default and paranoid kernels: running. `lake comparator`: statement comparison and axiom check passed in one run, kernels still running.
- CONFLICT: that page says con-leche and con-ron "declined" (exit 2, not a rejection) because they do not support the reflexive inductive FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate. This contradicts Teżewski's later (20:40-20:58) report that con-leche accepts. lean4lean 4.36 cannot read a v4.33 export (not applicable); Deicyde plans lean4lean built with 4.33.1 on the .oleans.
- Caveat on page: unsandboxed cloud build, files compiled by calling `lean` directly (77-module sample byte-identical to lake build); needs about 100 GB RAM, 70 GB disk to check from oleans.
- Deicyde repo https://github.com/Deicyde/riemann-hypothesis (7 commits): CI green at 15:07 UTC (source identical to tarball; challenge compiles vs Mathlib); static scan finds no sorry/axiom/native_decide/unsafe/implemented_by/opaque; "Comparator on the submission: not yet run, build takes hours". No final verdict seen.
- Not found: any Lean FRO, de Moura, Tao or Anthropic verification statement.

## B. Statements
- Alpöge note: "I believe I have, working with Claude, discovered a proof"; says he texted Dario Amodei late Sunday, there was "a constraint to respect" (IPO, Nasdaq 19 Nov); proof finished 16 Nov (timeline). Expects it to be "massively simplified".
- Anthropic: Verge and getaibook say no official comment/post (as of their writing). Clay: two-year acceptance rule only (Verge/MLQ); no Clay statement found.
- Glazer, Bloom, Buzzard as known. New: Kit Yates (Substack) "claimed is not accepted"; Ayush Khaitan (Princeton): Alpöge deserves as much credit as Claude; Pierre Richemond: "bizarre epistemic zone". SciAm second piece says "preliminary and informal responses" suggest it is correct. No Tao/Gowers/Sarnak/etc. quotes found.

## C. Content
- Note timeline (20 items, Claude-written): Stepanov-style multiplicity via chain of about sqrt(X) theta lifts between definite unitary groups, Iwasawa tower (Behrend), Rallis seesaw/Bessel periods, Bost slope inequality, relative trace formula on sixfold cover of GL5, weakened Vandiver. Alpöge admits he does not master the higher-rank automorphic parts and some summary may "make no sense".
- Pointers from mirror READMEs (https://github.com/CocoSgt/riemann-hypothesis-lean): entry via Supplements/Kernels/MainTheorems.lean -> Formalism.VW.rh_of_every -> UpperTheory.FinalTheorems.everyCharacter. Layout: Development 141,928 files (~81%), Formalism 18,254, GroundTheory 8,507, ReciprocityTheory 3,845, CompanionTheory 2,027, PositivityTheory 449. About 17.4M lines.
- Deicyde notes: riemannHypothesis = rh_of_every allChi, then standard functional-equation step. "GRH" = Dirichlet L-functions only. stateofproof.org has an intake record only. No blueprint or critique found.

## D. Outside math
- Coverage: FT, Quartz/AFP, New Scientist, SciAm (two pieces), Verge, MLQ, Magica, Kingy.ai. HN thread (1234 pts, 811 comments) discusses IPO timing; the note addresses it. No share-price or prediction-market item found.

## E. Replication
- https://github.com/rohanarun/alpoge-rh-replay STATUS "21:03 UTC": full build, axiom audit, kernel check "pending"; Render/Google worker waves, 29,131 modules accounted in the 500-task campaign. No memory/max_map_count/Finland/LUMI reports found. Other mirrors: CocoSgt, TomasOrtega/RH.

Most important new fact: Sutherland's page (19:45 UTC version) says con-leche/con-ron declined the proof (unsupported reflexive inductive type), which conflicts with Teżewski's report that con-leche accepts, while nanoda, leanchecker and the axiom audit pass.
