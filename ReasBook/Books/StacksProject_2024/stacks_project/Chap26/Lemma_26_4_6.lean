import StacksProject_2024.Chap26.Definition_26_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

section

variable {X Y Z : LocallyRingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X.toRingedSpace
local notation "𝒪X" => (SheafOfModules.unit X.toRingedSpace.ringCatSheaf : ModX)
variable (i : Z ⟶ X)
  (𝓘 :
    Subobject
      (SheafOfModules.unit X.toRingedSpace.ringCatSheaf :
        RingedSpace.Modules X.toRingedSpace))
  (f : Y ⟶ X)

-- Semantic recall: `lean_leansearch` surfaced the scheme-level closed-subscheme owners, while the
-- current repository already packages the source-facing locally-ringed-space owner as
-- `IsClosedSubspaceAssociatedTo`. The present lemma therefore keeps the source-facing
-- factorization criterion as the main entry, with the slice-category view exposed only through
-- thin companion lemmas.

/-- Lemma 26.4.6 (1): for a sheaf of ideals `\mathcal I \subset \mathcal O_X` with associated
closed subspace `i : Z ⟶ X`, a morphism `f : Y ⟶ X` factors through `Z` if and only if the map
`f^* \mathcal I \to \mathcal O_Y` is zero. -/
@[stacks 01HP]
theorem exists_lift_iff_pullbackIdealToStructureSheaf_eq_zero
    (hi : IsClosedSubspaceAssociatedTo i 𝓘)
    :
    (∃ g : Y ⟶ Z, g ≫ i = f) ↔ pullbackIdealToStructureSheaf f 𝓘 = 0 := sorry

/-- Companion API: a factorization through the associated closed subspace forces the pulled-back
ideal sheaf map to vanish. -/
theorem pullbackIdealToStructureSheaf_eq_zero_of_exists_lift
    (hi : IsClosedSubspaceAssociatedTo i 𝓘)
    (g : Y ⟶ Z) (hg : g ≫ i = f) :
    pullbackIdealToStructureSheaf f 𝓘 = 0 := by
  sorry

/-- Companion API: if the pulled-back ideal sheaf map vanishes, then a factorization through the
associated closed subspace exists. -/
theorem exists_lift_of_pullbackIdealToStructureSheaf_eq_zero
    (hi : IsClosedSubspaceAssociatedTo i 𝓘)
    (hzero : pullbackIdealToStructureSheaf f 𝓘 = 0) :
    ∃ g : Y ⟶ Z, g ≫ i = f := by
  sorry

/-- Lemma 26.4.6 (2): if the map `f^* \mathcal I \to \mathcal O_Y` is zero, then the induced
factorization `g : Y ⟶ Z` through the associated closed subspace is unique. -/
@[stacks 01HP]
theorem existsUnique_lift_of_pullbackIdealToStructureSheaf_eq_zero
    (hi : IsClosedSubspaceAssociatedTo i 𝓘)
    (hzero : pullbackIdealToStructureSheaf f 𝓘 = 0) :
    ∃! g : Y ⟶ Z, g ≫ i = f := sorry

/-- Companion API: under the vanishing criterion, any two lifts through the associated closed
subspace are equal. -/
theorem eq_of_comp_eq_of_pullbackIdealToStructureSheaf_eq_zero
    (hi : IsClosedSubspaceAssociatedTo i 𝓘)
    (hzero : pullbackIdealToStructureSheaf f 𝓘 = 0)
    {g g' : Y ⟶ Z} (hg : g ≫ i = f) (hg' : g' ≫ i = f) :
    g = g' := sorry

end

end AlgebraicGeometry.LocallyRingedSpace
