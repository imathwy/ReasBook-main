import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

-- Semantic recall: `lean_leansearch` returned the canonical owner `UniversallyOpen` and
-- `UniversallyOpen.of_flat`; adjacent Chapter 29 files record the needed route through
-- `smooth_flat` and `smooth_locallyOfFinitePresentation`.

/-- Lemma 29.34.10: a smooth morphism is universally open. -/
@[stacks 056G]
theorem smooth_universallyOpen (hf : Smooth f) :
    UniversallyOpen f := sorry

end AlgebraicGeometry
