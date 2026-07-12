import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the canonical affine separatedness instance
-- `AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine`, and the source-separated morphism
-- instance `AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated`. The source item is recorded
-- as two thin source-facing statements around those canonical owners.

/-- Lemma 26.21.15 (1): an affine scheme is separated. -/
@[stacks 01KN]
theorem Scheme.isSeparated_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    X.IsSeparated := sorry

/-- Lemma 26.21.15 (2): any morphism whose source is an affine scheme is separated. -/
@[stacks 01KN]
theorem Scheme.Hom.isSeparated_of_isAffine_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] :
    IsSeparated f := sorry

end AlgebraicGeometry
