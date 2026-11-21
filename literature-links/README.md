# Literature Links annotations (worked example, two statements)

Two annotations in the [Literature Links](https://github.com/mathlib-initiative/literature-links) format, each
linking a quoted passage at a fixed revision of a source to a Lean declaration at a fixed commit of
https://github.com/leanprover-community/riemann-hypothesis , with a note on how the two statements differ.
Both validate with `literature-links scan .` (v1.0.2).

| File | Named theorem | Lean declaration | Relation |
|---|---|---|---|
| `linnik.json` | Linnik's theorem | `GlobalTheory.Published.Linnik` | `closeMatch` |
| `radford.json` | Radford's theorem on shuffle algebras | `GlobalTheory.Published.RadfordShufflePolynomial` | `exactMatch` |

For each, the Lean statement and every project definition it uses were read, and the declaration was
confirmed to be a constant the proof of `riemannHypothesis` depends on.

Limits. The sources are Wikipedia revisions, chosen because they are open and quotable; the original papers
would be the proper subjects. This was stopped at two: for most other named statements in the archive the
source is not openly available, and the Lean statement rests on the archive's own definitions, which have to
be compared with the standard ones one by one. That is work for people with access to the literature.

One of these two checks changed a verdict in [`docs/07-named-theorems.md`](../docs/07-named-theorems.md):
the Linnik row was "faithful" there and is a close match, not an exact one, on careful reading.
