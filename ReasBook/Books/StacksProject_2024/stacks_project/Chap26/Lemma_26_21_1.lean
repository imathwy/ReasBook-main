import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical diagonal closed-immersion owner
-- `AlgebraicGeometry.IsClosedImmersion (CategoryTheory.Limits.pullback.diagonal f)` together with
-- `AlgebraicGeometry.IsSeparated.isClosedImmersion_diagonal` and the affine `Spec.map`
-- separatedness instance. The source item is therefore stated directly for morphisms whose source
-- and target schemes are affine.

/-- Lemma 26.21.1: the diagonal morphism of a morphism between affine schemes is a closed
immersion. -/
@[stacks 01KI]
theorem Scheme.Hom.isClosedImmersion_diagonal_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y] :
    IsClosedImmersion (pullback.diagonal f) := sorry

end AlgebraicGeometry
