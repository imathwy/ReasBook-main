import Mathlib.AlgebraicGeometry.Morphisms.Smooth

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: the canonical owner is mathlib's smoothness instance
`AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth`, so this item is best exposed as a
thin source-facing theorem rather than a duplicate local structure or wrapper API. -/

/-- Lemma 29.34.8: a smooth morphism is locally of finite presentation. -/
@[stacks 01VE]
theorem locallyOfFinitePresentation_of_smooth
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : Smooth f) :
    LocallyOfFinitePresentation f := by
  letI : Smooth f := hf
  infer_instance

end AlgebraicGeometry
