import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_16_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme morphism owners
-- `LocallyOfFiniteType` and `Surjective`; local Chapter 29 precedent fixes finite type points as
-- `finiteTypePoints S`.

/-- Lemma 29.16.6: let `f : T ⟶ S` be a morphism of schemes. If `f` is locally of finite
type and surjective, then the image of the finite type points of `T` is exactly the finite type
points of `S`. -/
@[stacks 06EB]
theorem image_finiteTypePoints_eq_of_locallyOfFiniteType_surjective
    {T S : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f] [Surjective f] :
    f '' finiteTypePoints T = finiteTypePoints S := sorry

end AlgebraicGeometry
