import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `IsImmersion` as the canonical owner for a
-- locally closed subscheme inclusion and `IsSeparated.instCompScheme` as the composition result.

variable {Z X S : Scheme.{u}}

/-- Lemma 26.23.9: if `X` is separated over `S`, then any locally closed subscheme
`Z ⊆ X`, represented by its immersion into `X`, is separated over `S`. -/
@[stacks 01L8]
theorem Scheme.Hom.isSeparated_comp_of_isImmersion (i : Z ⟶ X) (f : X ⟶ S)
    [IsImmersion i] [IsSeparated f] :
    IsSeparated (i ≫ f) := sorry

end AlgebraicGeometry
