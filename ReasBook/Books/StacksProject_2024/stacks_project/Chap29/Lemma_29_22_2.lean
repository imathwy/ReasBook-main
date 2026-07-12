import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

-- Declarations for this item will be appended below by the statement pipeline.

/- Semantic recall / owner check:
- the exact source-facing statement is already the canonical theorem
  `AlgebraicGeometry.Scheme.Hom.isConstructible_image`;
- this file therefore refines to tagging that owner directly, rather than keeping a local
  theorem-shaped recall wrapper.
- Lemma 29.22.2 (Stacks tag `054J`): let `f : X ⟶ Y` be a morphism of schemes. Assume `f` is
  quasi-compact and locally of finite presentation, and `Y` is quasi-compact and quasi-separated.
  Then the image of every constructible subset of `X` is constructible in `Y`.
-/

open AlgebraicGeometry

attribute [stacks 054J] AlgebraicGeometry.Scheme.Hom.isConstructible_image

/- Lemma 29.22.2 is a pure canonical recall item: the source-facing statement is already owned by
`AlgebraicGeometry.Scheme.Hom.isConstructible_image`. -/
#check AlgebraicGeometry.Scheme.Hom.isConstructible_image
