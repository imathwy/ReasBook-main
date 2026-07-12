import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Scheme.IdealSheafData

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` returned `AlgebraicGeometry.IsProper`,
-- `AlgebraicGeometry.LocallyOfFiniteType`, and `Scheme.IdealSheafData.vanishingIdeal`.
-- Nearby Chapter 30 precedent represents a closed subset with the reduced induced closed
-- subscheme structure by `vanishingIdeal Z`. The Stacks tag evidence is consistent for `0CYL`.

/-- Lemma 30.26.1: for a locally finite type morphism `f : X ⟶ S` and a closed subset
`Z ⊆ X`, properness over `S` for the reduced induced closed subscheme structure on `Z`,
properness for some closed subscheme structure on `Z`, and properness for every closed
subscheme structure on `Z` are equivalent. -/
@[stacks 0CYL]
theorem closedSubset_isProper_tfae_closedSubschemeStructure
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) :
    List.TFAE [
      IsProper ((vanishingIdeal Z).subschemeι ≫ f),
      ∃ I : X.IdealSheafData, I.support = Z ∧ IsProper (I.subschemeι ≫ f),
      ∀ I : X.IdealSheafData, I.support = Z → IsProper (I.subschemeι ≫ f)
    ] := sorry

end AlgebraicGeometry
