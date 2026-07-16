import StacksProject_2024.stacks_project.Chap26.Definition_26_4_4

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

section

variable {X Y Z : LocallyRingedSpace.{u}}

local notation "𝒪Y" =>
  (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf :
    RingedSpace.Modules Y.toRingedSpace)

variable {𝓘 : Subobject 𝒪Y} {f : X ⟶ Y} {i : Z ⟶ Y}
variable [IsClosedSubspaceAssociatedTo f 𝓘] [IsClosedSubspaceAssociatedTo i 𝓘]

-- Semantic recall: Chapter 26 already packages the source-facing owner
-- `IsClosedSubspaceAssociatedTo` for closed subspaces cut out by an ideal sheaf. This lemma is
-- the uniqueness statement for two realizations of that same associated closed subspace. The
-- present file keeps the source-facing “same ideal sheaf, hence unique comparison/isomorphism”
-- surface, with the class owner used directly as ambient context.

/-- Companion API: for two realizations of the closed subspace associated to `\mathcal I`, there
is a unique comparison morphism over `Y`. -/
theorem existsUnique_hom_of_isClosedSubspaceAssociatedTo
    :
    ∃! g : X ⟶ Z, g ≫ i = f := by
  sorry

/-- Companion API: any two comparison morphisms over `Y` between two realizations of the closed
subspace associated to `\mathcal I` are equal. -/
theorem eq_of_comp_eq_of_isClosedSubspaceAssociatedTo
    {g g' : X ⟶ Z} (hg : g ≫ i = f) (hg' : g' ≫ i = f) :
    g = g' := by
  sorry

/-- Companion API: any comparison morphism over `Y` between two realizations of the closed
subspace associated to `\mathcal I` is an isomorphism. -/
theorem isIso_of_comp_eq_of_isClosedSubspaceAssociatedTo
    (g : X ⟶ Z) (hg : g ≫ i = f) :
    IsIso g := by
  sorry

/-- Lemma 26.4.5: if `f : X ⟶ Y` and `i : Z ⟶ Y` exhibit `X` and `Z` as the closed subspace of
`Y` associated to the same ideal sheaf `\mathcal I`, then there is a unique isomorphism
`X ≅ Z` over `Y`. -/
@[stacks 01HO]
theorem existsUnique_iso_of_isClosedSubspaceAssociatedTo
    :
    ∃! e : X ≅ Z, e.hom ≫ i = f := by
  sorry

end

end AlgebraicGeometry.LocallyRingedSpace
