import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_1_2

/- Source/core/bridge triage:
- `source-facing`: Proposition 4-19 records the additivity and multiplicativity of characters in
  the chapter's compact continuous setting.
- `core/canonical`: `Representation.char_prod` and `Representation.char_tensor`.
- `bridge/view`: none; the Chapter 4 topological hypotheses do not change these formulas.

This item is therefore recall-only: keeping separate local theorem names with unused continuity and
compactness assumptions would duplicate the earlier canonical owner surface without improving
repository reuse.
-/

/- Proposition 4-19 (1): for finite-dimensional complex representations, the character of the
direct-sum representation is the sum of the two characters. In Chapter 4 this is applied to
continuous representations of compact groups, but the formula itself is already the canonical
theorem `Representation.char_prod`. -/
recall Representation.char_prod

/- Proposition 4-19 (2): for finite-dimensional complex representations, the character of the
tensor-product representation is the product of the two characters. In Chapter 4 this is applied
to continuous representations of compact groups, but the formula itself is already the canonical
theorem `Representation.char_tensor`. -/
recall Representation.char_tensor
