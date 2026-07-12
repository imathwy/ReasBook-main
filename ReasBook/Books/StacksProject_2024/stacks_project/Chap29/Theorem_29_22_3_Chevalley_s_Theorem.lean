import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

-- Semantic recall: `lean_leansearch` found the exact scheme-morphism theorem
-- `AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image`, so this item is a pure canonical
-- recall rather than a redundant local wrapper.

/- Theorem 29.22.3 (Chevalley's Theorem): let `f : X ⟶ Y` be a morphism of schemes. Assume `f` is
quasi-compact and locally of finite presentation. Then the image of every locally constructible
subset is locally constructible. This is exactly the canonical theorem
`AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image`. -/
recall isLocallyConstructible_image
