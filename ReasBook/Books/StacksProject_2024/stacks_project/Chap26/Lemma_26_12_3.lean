import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

/- Source/core/bridge triage for Lemma 26.12.3:
- `source-facing`: an affine scheme `Spec R` is reduced exactly when `R` is reduced;
- `core/canonical`: the mathlib owner `affine_isReduced_iff`;
- `bridge/view`: recall-only, so this file should reuse the canonical owner directly rather than
  restating it through a local theorem wrapper. -/

/- Semantic recall: mathlib already provides the exact canonical owner
`AlgebraicGeometry.affine_isReduced_iff`, so this Stacks item is a pure recall of the existing
affine reducedness criterion. This file therefore uses the preceding Chapter 26 reducedness API
import and checks the canonical theorem directly, instead of adding a local wrapper or a separate
`recall` dependency. -/

/- Lemma 26.12.3: an affine scheme `Spec R` is reduced if and only if the ring `R` is reduced. -/
recall affine_isReduced_iff

end AlgebraicGeometry
