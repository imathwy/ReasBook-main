import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.Subcategory
import stacks_project.Chap13.Definition_13_8_1
import stacks_project.Chap13.Definition_13_11_3
import stacks_project.Chap13.Lemma_13_10_6
import stacks_project.Chap13.Lemma_13_11_6
import stacks_project.Chap13.Situation_13_14_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-- The composite `K(\mathcal A) ⟶ K(\mathcal B) ⟶ D(\mathcal B)` induced by the additive
functor `F`. -/
abbrev mapHomotopyCategoryToDerived :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

-- Proof sketch: represent an object of `K^+(\mathcal A)` by a bounded-below cochain complex,
-- apply `F` termwise, and note that its image in the derived category of `ℬ` is still represented
-- by a bounded-below complex, hence lies in `D^+(\mathcal B)`.
/-- The functor `K^+(\mathcal A) ⟶ D(\mathcal B)` induced by `F` lands in the bounded-below
derived category `D^+(\mathcal B)`. -/
theorem mapHomotopyCategoryToDerived_obj_mem_t_plus
    (X : K⁺(𝒜)) :
    (t.plus : ObjectProperty (D(ℬ)))
      ((mapHomotopyCategoryToDerived F).obj X.obj) := sorry

-- Proof sketch: represent an object of `K^-(\mathcal A)` by a bounded-above cochain complex,
-- apply `F` termwise, and note that its image in the derived category of `ℬ` is still represented
-- by a bounded-above complex, hence lies in `D^-(\mathcal B)`.
/-- The functor `K^-(\mathcal A) ⟶ D(\mathcal B)` induced by `F` lands in the bounded-above
derived category `D^-(\mathcal B)`. -/
theorem mapHomotopyCategoryToDerived_obj_mem_t_minus
    (X : K⁻(𝒜)) :
    (t.minus : ObjectProperty (D(ℬ)))
      ((mapHomotopyCategoryToDerived F).obj X.obj) := sorry

/-- The composite `K^+(\mathcal A) ⟶ D^+(\mathcal B)` induced by the additive functor `F`. -/
abbrev mapBoundedBelowHomotopyCategoryToDerivedBelow :
    K⁺(𝒜) ⥤ D⁺(ℬ) :=
  ObjectProperty.lift (t.plus : ObjectProperty (D(ℬ)))
    (ObjectProperty.ι (boundedBelowHomotopyProperty 𝒜) ⋙ mapHomotopyCategoryToDerived F)
    (mapHomotopyCategoryToDerived_obj_mem_t_plus F)

/-- The composite `K^-(\mathcal A) ⟶ D^-(\mathcal B)` induced by the additive functor `F`. -/
abbrev mapBoundedAboveHomotopyCategoryToDerivedAbove :
    K⁻(𝒜) ⥤ D⁻(ℬ) :=
  ObjectProperty.lift (t.minus : ObjectProperty (D(ℬ)))
    (ObjectProperty.ι (boundedAboveHomotopyProperty 𝒜) ⋙ mapHomotopyCategoryToDerived F)
    (mapHomotopyCategoryToDerived_obj_mem_t_minus F)

/-- Situation 13.15.1: an additive functor `F : 𝒜 ⥤ ℬ` between abelian categories determines the
exact-localization setups underlying the four derived functors considered in this section. The
unbounded right and left derived functors share the same localization situation on
`K(\mathcal A) ⟶ D(\mathcal B)`, while the bounded-below and bounded-above cases use the induced
functors `K^+(\mathcal A) ⟶ D^+(\mathcal B)` and `K^-(\mathcal A) ⟶ D^-(\mathcal B)`. -/
class AdditiveFunctorDerivedLocalizationSituation
    extends
      (mapHomotopyCategoryToDerived F).CommShift ℤ,
      (mapHomotopyCategoryToDerived F).IsTriangulated,
      IsSaturatedMultiplicativeSystem (HomotopyCategory.quasiIso 𝒜 (up ℤ)),
      (HomotopyCategory.quasiIso 𝒜 (up ℤ)).IsCompatibleWithTriangulation where
  /-- The bounded-below derived functor setup is exact and compatible with shifts. -/
  boundedBelow_commShift : (mapBoundedBelowHomotopyCategoryToDerivedBelow F).CommShift ℤ
  /-- The bounded-below derived functor setup is triangulated. -/
  boundedBelow_isTriangulated :
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F).IsTriangulated
  /-- The bounded-below quasi-isomorphisms form a saturated multiplicative system. -/
  boundedBelow_isSaturated :
    IsSaturatedMultiplicativeSystem (boundedBelowHomotopyQuasiIso 𝒜)
  /-- The bounded-below quasi-isomorphisms are compatible with triangulation. -/
  boundedBelow_isCompatible :
    (boundedBelowHomotopyQuasiIso 𝒜).IsCompatibleWithTriangulation
  /-- The bounded-above derived functor setup is exact and compatible with shifts. -/
  boundedAbove_commShift : (mapBoundedAboveHomotopyCategoryToDerivedAbove F).CommShift ℤ
  /-- The bounded-above derived functor setup is triangulated. -/
  boundedAbove_isTriangulated :
    (mapBoundedAboveHomotopyCategoryToDerivedAbove F).IsTriangulated
  /-- The bounded-above quasi-isomorphisms form a saturated multiplicative system. -/
  boundedAbove_isSaturated :
    IsSaturatedMultiplicativeSystem (boundedAboveHomotopyQuasiIso 𝒜)
  /-- The bounded-above quasi-isomorphisms are compatible with triangulation. -/
  boundedAbove_isCompatible :
    (boundedAboveHomotopyQuasiIso 𝒜).IsCompatibleWithTriangulation

/-- The bounded-below derived functor setup commutes with shifts. -/
instance boundedBelow_commShift
    [h : AdditiveFunctorDerivedLocalizationSituation F] :
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F).CommShift ℤ :=
  h.boundedBelow_commShift

/-- The bounded-below derived functor setup is triangulated. -/
instance boundedBelow_isTriangulated
    [h : AdditiveFunctorDerivedLocalizationSituation F] :
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F).IsTriangulated :=
  h.boundedBelow_isTriangulated

/-- The bounded-below quasi-isomorphisms form a saturated multiplicative system. -/
theorem boundedBelow_isSaturatedMultiplicativeSystem
    [h : AdditiveFunctorDerivedLocalizationSituation F] :
    IsSaturatedMultiplicativeSystem (boundedBelowHomotopyQuasiIso 𝒜) :=
  h.boundedBelow_isSaturated

/-- The bounded-below quasi-isomorphisms are compatible with triangulation. -/
theorem boundedBelow_isCompatibleWithTriangulation
    [h : AdditiveFunctorDerivedLocalizationSituation F] :
    (boundedBelowHomotopyQuasiIso 𝒜).IsCompatibleWithTriangulation :=
  h.boundedBelow_isCompatible

/-- The bounded-above derived functor setup commutes with shifts. -/
instance boundedAbove_commShift
    [h : AdditiveFunctorDerivedLocalizationSituation F] :
    (mapBoundedAboveHomotopyCategoryToDerivedAbove F).CommShift ℤ :=
  h.boundedAbove_commShift

/-- The bounded-above derived functor setup is triangulated. -/
instance boundedAbove_isTriangulated
    [h : AdditiveFunctorDerivedLocalizationSituation F] :
    (mapBoundedAboveHomotopyCategoryToDerivedAbove F).IsTriangulated :=
  h.boundedAbove_isTriangulated

/-- The bounded-above quasi-isomorphisms form a saturated multiplicative system. -/
theorem boundedAbove_isSaturatedMultiplicativeSystem
    [h : AdditiveFunctorDerivedLocalizationSituation F] :
    IsSaturatedMultiplicativeSystem (boundedAboveHomotopyQuasiIso 𝒜) :=
  h.boundedAbove_isSaturated

/-- The bounded-above quasi-isomorphisms are compatible with triangulation. -/
theorem boundedAbove_isCompatibleWithTriangulation
    [h : AdditiveFunctorDerivedLocalizationSituation F] :
    (boundedAboveHomotopyQuasiIso 𝒜).IsCompatibleWithTriangulation :=
  h.boundedAbove_isCompatible

/-- The derived-localization situation is assembled from the three constituent exact-localization
setups. -/
instance additiveFunctorDerivedLocalizationSituation_of_instances
    [(mapHomotopyCategoryToDerived F).CommShift ℤ]
    [(mapHomotopyCategoryToDerived F).IsTriangulated]
    [IsSaturatedMultiplicativeSystem (HomotopyCategory.quasiIso 𝒜 (up ℤ))]
    [(HomotopyCategory.quasiIso 𝒜 (up ℤ)).IsCompatibleWithTriangulation]
    [(mapBoundedBelowHomotopyCategoryToDerivedBelow F).CommShift ℤ]
    [(mapBoundedBelowHomotopyCategoryToDerivedBelow F).IsTriangulated]
    [IsSaturatedMultiplicativeSystem (boundedBelowHomotopyQuasiIso 𝒜)]
    [(boundedBelowHomotopyQuasiIso 𝒜).IsCompatibleWithTriangulation]
    [(mapBoundedAboveHomotopyCategoryToDerivedAbove F).CommShift ℤ]
    [(mapBoundedAboveHomotopyCategoryToDerivedAbove F).IsTriangulated]
    [IsSaturatedMultiplicativeSystem (boundedAboveHomotopyQuasiIso 𝒜)]
    [(boundedAboveHomotopyQuasiIso 𝒜).IsCompatibleWithTriangulation] :
    AdditiveFunctorDerivedLocalizationSituation F where
  toCommShift := inferInstance
  toIsTriangulated := inferInstance
  toIsSaturatedMultiplicativeSystem := inferInstance
  toIsCompatibleWithTriangulation := inferInstance
  boundedBelow_commShift := inferInstance
  boundedBelow_isTriangulated := inferInstance
  boundedBelow_isSaturated := inferInstance
  boundedBelow_isCompatible := inferInstance
  boundedAbove_commShift := inferInstance
  boundedAbove_isTriangulated := inferInstance
  boundedAbove_isSaturated := inferInstance
  boundedAbove_isCompatible := inferInstance

end

end CategoryTheory
