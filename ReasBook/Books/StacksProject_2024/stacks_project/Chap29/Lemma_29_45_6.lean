import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Properties
import StacksProject_2024.stacks_project.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall: Definition 26.12.5 is the nilradical subscheme `X.nilradical.subscheme` with
-- canonical closed immersion `X.nilradical.subschemeι`; mathlib exposes the universal
-- homeomorphism content through `Surjective`, `UniversallyInjective`, and `UniversallyClosed`,
-- while local Chapter 29 packages the reusable source-facing owner as
-- `UniversalHomeomorphism`.

variable (X : Scheme)

/-- The reduced subscheme `X_red`, formalized as `X.nilradical.subscheme`, is reduced. -/
theorem isReduced_reducedSubscheme :
    IsReduced X.nilradical.subscheme := sorry

/-- The canonical closed immersion `X_red → X`, formalized as `X.nilradical.subschemeι`, is a
universal homeomorphism. This is the canonical Chapter 29 owner for the source-facing properties
recorded below. -/
theorem universalHomeomorphism_reducedSubschemeInclusion :
    UniversalHomeomorphism X.nilradical.subschemeι := sorry

/-- Lemma 29.45.6 (1): the canonical closed immersion `X_red → X`, formalized as
`X.nilradical.subschemeι`, is surjective on the underlying topological space. -/
theorem surjective_reducedSubschemeInclusion :
    Surjective X.nilradical.subschemeι := sorry

/-- Lemma 29.45.6 (2): the canonical closed immersion `X_red → X`, formalized as
`X.nilradical.subschemeι`, is universally injective. -/
theorem universallyInjective_reducedSubschemeInclusion :
    UniversallyInjective X.nilradical.subschemeι := sorry

/-- Lemma 29.45.6 (3): the canonical closed immersion `X_red → X`, formalized as
`X.nilradical.subschemeι`, is universally closed. -/
theorem universallyClosed_reducedSubschemeInclusion :
    UniversallyClosed X.nilradical.subschemeι := by
  infer_instance
