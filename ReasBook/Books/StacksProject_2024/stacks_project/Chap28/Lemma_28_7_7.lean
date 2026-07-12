import Mathlib
import StacksProject_2024.Chap28.Lemma_28_7_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.IsLocallyNoetherian`,
-- `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian`, and `IsIntegral`. Local
-- precedent states the normal-scheme decomposition by pairwise disjoint open subschemes.

/-- Lemma 28.7.7: a locally Noetherian scheme `X` is normal if and only if `X` is a
disjoint union of integral normal schemes, expressed as a pairwise disjoint open cover by open
subschemes that are both integral and normal. -/
@[stacks 033N]
theorem isNormal_iff_exists_pairwiseDisjoint_openCover_normal_integral_of_isLocallyNoetherian :
    X.isNormal ↔ X.HasPairwiseDisjointOpenCoverByNormalIntegral := sorry

end
