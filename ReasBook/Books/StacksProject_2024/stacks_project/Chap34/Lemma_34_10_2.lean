import StacksProject_2024.Chap34.Definition_34_9_10
import StacksProject_2024.Chap34.Definition_34_10_1

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace StandardFpqcCover

section

variable {T : Scheme.{u}} [IsAffine T]

-- Semantic recall: `lean_leansearch` only surfaced generic valuative-criterion infrastructure,
-- while local Chapter 34 precedent packages standard `V` coverings as `AffineFamilyOver T` with
-- `AffineFamilyOver.IsStandardVCover`; this item is therefore the bridge from
-- `StandardFpqcCover` to that existing owner.

/-- The finite affine family over the base scheme underlying a standard fpqc covering. -/
def toAffineFamily (𝒰 : StandardFpqcCover T) : AffineFamilyOver T where
  n := 𝒰.n
  U := 𝒰.U
  map := 𝒰.map
  isAffine := 𝒰.isAffine

/-- The `j`-th morphism in the affine family underlying a standard fpqc covering is the original
component map. -/
theorem toAffineFamily_map (𝒰 : StandardFpqcCover T) (j : Fin 𝒰.n) :
    (toAffineFamily 𝒰).map j = 𝒰.map j := sorry

/-- Lemma 34.10.2: a standard fpqc covering of an affine scheme is a standard `V` covering. -/
@[stacks 0ETC]
theorem isStandardVCover (𝒰 : StandardFpqcCover T) :
    AffineFamilyOver.IsStandardVCover (toAffineFamily 𝒰) := sorry

end

end StandardFpqcCover

end AlgebraicGeometry
