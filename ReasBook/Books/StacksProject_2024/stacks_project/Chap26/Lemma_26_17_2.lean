import Mathlib.AlgebraicGeometry.Pullbacks

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the canonical mathlib instance
-- `Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine` for affine scheme pullbacks.

variable {S X Y : Scheme}

/-- Lemma 26.17.2: let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes with the same
target. If `X`, `Y`, and `S` are affine, then `X ×_S Y` is affine. -/
@[stacks 01JQ]
theorem pullback_isAffine_of_isAffine
    (f : X ⟶ S) (g : Y ⟶ S) [IsAffine X] [IsAffine Y] [IsAffine S] :
    IsAffine (pullback f g) := sorry

end AlgebraicGeometry
