import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import stacks_project.Chap13.Lemma_13_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)

/-- The inverse-image functor on abelian sheaves induced by relocalization along `f`. -/
private abbrev localizedPullback {U V : C} (f : U ⟶ V) :
    Sheaf (J.over V) AddCommGrpCat.{u} ⥤ Sheaf (J.over U) AddCommGrpCat.{u} :=
  J.overMapPullback AddCommGrpCat.{u} f

/-- The direct-image functor on abelian sheaves induced by relocalization along `f`. -/
private abbrev localizedPushforward {U V : C} (f : U ⟶ V) :
    Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf (J.over V) AddCommGrpCat.{u} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u} (J.over U) (J.over V)

/-- The relocalization inverse-image functor on abelian sheaves is additive. -/
local instance instLocalizedPullbackAdditive {U V : C} (f : U ⟶ V) :
    (localizedPullback J f).Additive := sorry

/-- The relocalization inverse-image functor on abelian sheaves preserves finite colimits. -/
local instance instLocalizedPullbackPreservesFiniteColimits {U V : C} (f : U ⟶ V) :
    Limits.PreservesFiniteColimits (localizedPullback J f) := sorry

/-- The relocalization direct-image functor on abelian sheaves is additive. -/
local instance instLocalizedPushforwardAdditive {U V : C} (f : U ⟶ V) :
    (localizedPushforward J f).Additive := sorry

/-- The inverse-image functor on derived categories induced by relocalization along `f`. -/
private abbrev localizedPullbackDerived {U V : C} (f : U ⟶ V) :
    DerivedCategory (Sheaf (J.over V) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (J.over U) AddCommGrpCat.{u}) :=
  Functor.mapDerivedCategory (localizedPullback J f)

/-- The homotopy-to-derived functor attached to localized direct image along `f`. -/
private abbrev localizedPushforwardToDerived {U V : C} (f : U ⟶ V) :
    HomotopyCategory (Sheaf (J.over U) AddCommGrpCat.{u}) (up ℤ) ⥤
      DerivedCategory (Sheaf (J.over V) AddCommGrpCat.{u}) :=
  mapHomotopyCategoryToDerived (localizedPushforward J f)

/-- The unbounded right-derived localized direct-image functor along `f`. -/
private abbrev localizedPushforwardDerived {U V : C} (f : U ⟶ V)
    [Functor.HasRightDerivedFunctor
      (localizedPushforwardToDerived J f)
      (HomotopyCategory.quasiIso (Sheaf (J.over U) AddCommGrpCat.{u}) (up ℤ))] :
    DerivedCategory (Sheaf (J.over U) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (J.over V) AddCommGrpCat.{u}) :=
  Functor.totalRightDerived
    (localizedPushforwardToDerived J f)
    (DerivedCategory.Qh :
      HomotopyCategory (Sheaf (J.over U) AddCommGrpCat.{u}) (up ℤ) ⥤
        DerivedCategory (Sheaf (J.over U) AddCommGrpCat.{u}))
    (HomotopyCategory.quasiIso (Sheaf (J.over U) AddCommGrpCat.{u}) (up ℤ))

variable {X' X Y' Y : C}
variable (i : X' ⟶ X) (p : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

-- Proof sketch: represent an object of `D(\mathcal C/X)` by a K-injective complex of abelian
-- sheaves. Restriction to the smaller slice remains K-injective by the localized K-injectivity
-- argument from the preceding section, so both composites are computed on the nose by applying the
-- underived direct and inverse image functors to the same complex. The resulting equality is the
-- slice-site base-change statement for relocalization.
/-- Lemma 21.21.1: for a cartesian square
`X' ⟶ X`
`↓     ↓`
`Y' ⟶ Y`
in a site `\mathcal C`, inverse image along `Y' ⟶ Y` commutes with the derived direct image along
`X ⟶ Y` after relocalization. Equivalently, the functors
`j_{Y'/Y}^{-1} ∘ Rj_{X/Y,*}` and `Rj_{X'/Y',*} ∘ j_{X'/X}^{-1}` from `D(\mathcal C/X)` to
`D(\mathcal C/Y')` are canonically isomorphic. -/
theorem relocalization_rightDerived_pushforward_inverse_image_isomorphic
    (hcart : IsPullback i p f g)
    [Functor.HasRightDerivedFunctor
      (localizedPushforwardToDerived J f)
      (HomotopyCategory.quasiIso (Sheaf (J.over X) AddCommGrpCat.{u}) (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (localizedPushforwardToDerived J p)
      (HomotopyCategory.quasiIso (Sheaf (J.over X') AddCommGrpCat.{u}) (up ℤ))] :
    IsIsomorphic
      (localizedPushforwardDerived J f ⋙ localizedPullbackDerived J g)
      (localizedPullbackDerived J i ⋙ localizedPushforwardDerived J p) := sorry

end

end CategoryTheory
