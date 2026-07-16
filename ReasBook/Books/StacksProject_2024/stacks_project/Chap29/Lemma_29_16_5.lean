import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_16_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

/- Semantic recall: `lean_leansearch` surfaced `LocallyOfFiniteType` and nearby closed-point
image API; local Chapter 29 precedent fixes finite type points as `finiteTypePoints S`. -/

/-- Lemma 29.16.5: if `f : T ⟶ S` is locally of finite type, then the image of the finite type
points of `T` is contained in the finite type points of `S`. -/
@[stacks 02J3]
theorem image_finiteTypePoints_subset_of_locallyOfFiniteType
    {T S : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f] :
    f '' finiteTypePoints T ⊆ finiteTypePoints S := sorry

end AlgebraicGeometry
