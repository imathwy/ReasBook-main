import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}} (U : Opens X) (𝒪 : TopCat.Sheaf RingCat.{u} X)

/-- Restriction and extension by zero for module-valued sheaves: for an open subset `U ⊆ X`, the
restriction functor on sheaves of `𝒪`-modules to `U` is the inverse-image functor along the open
inclusion `j : U ↪ X`, modeled by the pullback of module sheaves along the unit
`𝒪 ⟶ j_* j^{-1} 𝒪`. -/
noncomputable abbrev moduleSheafRestrictionToOpen :
    SheafOfModules 𝒪 ⥤
      SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪) :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪)

-- Proof sketch: this is the module-valued analogue of the open-immersion restriction functor for
-- sheaves of sets and algebraic structures. One proves that for an open inclusion `j : U ↪ X`,
-- restriction of `𝒪`-modules has a left adjoint given by extension by zero, hence the displayed
-- restriction functor is a right adjoint.
/-- Restriction of sheaves of `𝒪`-modules to an open subset is a right adjoint. -/
instance moduleSheafRestrictionToOpen_isRightAdjoint :
    (moduleSheafRestrictionToOpen U 𝒪).IsRightAdjoint := sorry

/-- The extension-by-zero functor for sheaves of `𝒪|_U`-modules along the open inclusion
`j : U ↪ X`, defined as the chosen left adjoint to `moduleSheafRestrictionToOpen U 𝒪`. -/
noncomputable abbrev moduleSheafExtensionByZeroFromOpen :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪) ⥤
      SheafOfModules 𝒪 :=
  (moduleSheafRestrictionToOpen U 𝒪).leftAdjoint

/-- The chosen extension-by-zero functor is left adjoint to restriction to the open subset. -/
noncomputable abbrev moduleSheafExtensionByZeroAdjunction :
    moduleSheafExtensionByZeroFromOpen U 𝒪 ⊣ moduleSheafRestrictionToOpen U 𝒪 :=
  Adjunction.ofIsRightAdjoint (moduleSheafRestrictionToOpen U 𝒪)
