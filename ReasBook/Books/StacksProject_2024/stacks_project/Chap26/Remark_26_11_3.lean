import Mathlib
import StacksProject_2024.stacks_project.Chap26.Example_26_14_3_Affine_space_with_zero_doubled

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced `Scheme.affineOpens` and `IsAffineOpen`; local
-- Chapter 26 precedent in Example 26.14.3 supplies the doubled-origin scheme and its non-affine
-- chart intersection.

variable (k : Type u) [Field k]

/-- Remark 26.11.3: in general the intersection of two affine opens in a scheme is not affine
open. Example 26.14.3 supplies such a pair as the two affine charts of affine space with zero
doubled. -/
@[stacks 01IU]
theorem AffineSpaceWithZeroDoubled.chart_inter_not_isAffineOpen
    (A : AffineSpaceWithZeroDoubled k 2) :
    ¬ IsAffineOpen (A.chart 0 ⊓ A.chart 1) := sorry

end AlgebraicGeometry
