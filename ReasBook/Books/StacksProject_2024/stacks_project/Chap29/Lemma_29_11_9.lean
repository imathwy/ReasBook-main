import Mathlib.AlgebraicGeometry.Morphisms.Affine

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits

universe u

-- Semantic recall: `lean_leansearch` found mathlib's base-change stability instance
-- `AlgebraicGeometry.isAffineHom_isStableUnderBaseChange`; the source-facing statement here is
-- the corresponding thin theorem for the pullback projection.

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [IsAffineHom f]

/-- Lemma 29.11.9: the base change of an affine morphism is affine. -/
theorem isAffineHom_pullback_snd : IsAffineHom (pullback.snd f g) := sorry

end
