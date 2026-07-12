import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Scheme.IdealSheafData

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` returned `AlgebraicGeometry.IsProper`,
-- `AlgebraicGeometry.IsProper.isStableUnderBaseChange`, and `AlgebraicGeometry.LocallyOfFiniteType`
-- as the relevant canonical owners/API; local Chapter 30 precedent represents a closed subset
-- proper over a base by the properness of its `vanishingIdeal` closed subscheme.

/-- Lemma 30.26.4: in a cartesian diagram of schemes
`X' ⟶ X` over `S' ⟶ S`, if `f : X ⟶ S` is locally of finite type and a closed subset
`Z ⊆ X` is proper over `S`, then its inverse image in `X'` is proper over `S'`. -/
@[stacks 0CYP]
theorem closedSubset_preimage_isProper_over_base
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (Z : TopologicalSpace.Closeds X)
    [IsProper ((vanishingIdeal Z).subschemeι ≫ f)] :
    IsProper ((vanishingIdeal (Z.preimage g'.continuous)).subschemeι ≫ f') := sorry

end AlgebraicGeometry
