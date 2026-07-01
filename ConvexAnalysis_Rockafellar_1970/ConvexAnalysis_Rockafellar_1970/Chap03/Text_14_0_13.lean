import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_12

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.13 repeats the simplex example whose set is given by coordinatewise
  nonnegativity together with the mass bound `∑ i, x i ≤ 1`, and whose polar is described by the
  coordinatewise inequalities `xStar i ≤ 1`.
- `core/canonical`: the owner abstractions are already in the immediately preceding file:
  `unitSimplexSet` for the source-facing set and
  `polar_unitSimplexSet_eq_coordinatewise_le_one` for its polar computation.
- `bridge/view`: this file contributes no additional mathematics beyond reusing that exact
  chapter-level theorem, so it should not keep a second local set name or a renamed duplicate
  theorem.

Domain-style sampling used here:
- the chapter owner `Set.polar`;
- the owner-side membership criterion `Set.mem_polar_iff`;
- the source-facing set `unitSimplexSet`;
- the exact theorem
  `polar_unitSimplexSet_eq_coordinatewise_le_one`.

Primitive data vs derived API:
- primitive data: already owned upstream by `unitSimplexSet`;
- derived API: already owned upstream by
  `polar_unitSimplexSet_eq_coordinatewise_le_one`.

Layer target: `bridge/view`; this numbered item is a direct canonical reuse of the preceding
source-facing simplex-polar theorem.
-/

/- Text 14.0.13 repeats the simplex-polar computation already formalized in Text 14.0.12, so the
canonical chapter theorem is recalled directly instead of introducing a duplicate local set and a
parallel theorem name. -/
recall polar_unitSimplexSet_eq_coordinatewise_le_one
