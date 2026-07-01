import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.5 explains how the chapter closure of a convex function is read:
  the closure surface is still `cl(·)`, while the exceptional improper case is tracked through the
  existing proper/improper API.
- `core/canonical`: the owner abstractions are the Chapter 2 closure owner
  `lowerSemicontinuousHull`, written `cl(·)`, and the Chapter 1 properness owner
  `Function.IsProper`.
- `bridge/view`: this item should not introduce a second public closure owner. Its mathematical
  content is the bridge from the source's branchwise prose to the already canonical owners
  `cl(·)` and `Function.IsProper`.

Domain-style sampling used here:
- `lowerSemicontinuousHull` and the notation `cl(·)` from `Text_7_0_4`;
- `Function.IsProper` from `Definition_4_6`;
- `Function.IsProper.ne_bot` from `Definition_4_6`;
- `Function.not_isProper_iff` from `Definition_4_7`.

Primitive data vs derived API:
- primitive data: a function `f : E → WithTopBot 𝕜`;
- owner abstractions: the closure operator `cl(f)` and the properness predicate `f.IsProper`;
- derived bridge: properness excludes the value `⊥`, while improperness is exactly empty
  effective domain or bottom attainment somewhere (via
  `Function.not_isProper_iff`).

Layer target: `bridge/view`. Since the chapter already fixed `cl(·)` as the closure surface and
nearby downstream statements use that owner directly, this file keeps only the canonical recalls
needed to read Text 7.0.5 without introducing any parallel closure owner.
-/

/- Text 7.0.5 continues to use the chapter properness owner on extended-codomain functions. -/
recall Function.IsProper

/- Text 7.0.5 continues to use the Chapter 2 closure surface `cl(·)`. -/
recall lowerSemicontinuousHull

/- On the proper branch of Text 7.0.5, the function never takes the value `⊥`. -/
recall Function.IsProper.ne_bot

/- The improper branch is exactly the failure of properness: empty effective domain or bottom
attainment somewhere is the source-facing restatement of the canonical bridge
`Function.not_isProper_iff`. -/
recall Function.not_isProper_iff

end
