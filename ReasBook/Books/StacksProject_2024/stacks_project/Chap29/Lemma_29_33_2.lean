import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.Definition_18_34_1
import StacksProject_2024.Chap31.Lemma_31_14_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

local notation "ModX" => Scheme.Modules
local notation:70 A " ⊗ₘ " B => (tensorObj A B : _)

-- Semantic recall: `lean_leansearch` confirmed `SheafOfModules.unitHomEquiv` as the
-- canonical global-section bridge; the tensor-section helper follows the local Chapter 17/31
-- module-sheaf tensor pattern.

/-- Helper comparison: the sheafification model of the structure sheaf module on a scheme is the
ambient tensor unit in its module category. -/
private theorem tensorUnit_eq_sheafification_unit_model
    {X : Scheme.{u}} [MonoidalCategory X.Modules] :
    ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)) ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) =
      (𝟙_ X.Modules) := sorry

/-- Helper comparison isomorphism from the structure sheaf module to the ambient tensor unit. -/
private noncomputable def schemeModuleUnitIsoTensorUnit
    {X : Scheme.{u}} [MonoidalCategory X.Modules] :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ (𝟙_ X.Modules) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app
      (SheafOfModules.unit X.ringCatSheaf : X.Modules))).symm ≪≫
    eqToIso tensorUnit_eq_sheafification_unit_model

/-- The pure tensor of two global sections, expressed through the tensor-unit description of
global sections. -/
private noncomputable def tensorSection
    {X : Scheme.{u}} [MonoidalCategory X.Modules]
    {ℱ 𝒢 : X.Modules} (s : ℱ.sections) (t : 𝒢.sections) :
    ((tensorObj ℱ 𝒢 : X.Modules).sections) :=
  let η : SheafOfModules.unit X.ringCatSheaf ≅ 𝟙_ X.Modules :=
    schemeModuleUnitIsoTensorUnit
  (tensorObj ℱ 𝒢 : X.Modules).unitHomEquiv
    (η.hom ≫ (λ_ (𝟙_ X.Modules)).inv ≫
      @CategoryTheory.MonoidalCategoryStruct.tensorHom X.Modules _
        (inferInstanceAs (MonoidalCategoryStruct X.Modules))
        (𝟙_ X.Modules) ℱ (𝟙_ X.Modules) 𝒢
        (η.inv ≫ ℱ.unitHomEquiv.symm s)
        (η.inv ≫ 𝒢.unitHomEquiv.symm t))

/-- Apply a relative sheaf differential operator to an ordinary global section; restriction of
scalars changes the module structure but not the underlying section type. -/
private abbrev applyRestrictedSection
    {X S : Scheme.{u}} (a : X ⟶ S)
    {ℱ ℱ' : X.Modules}
    (D :
      (SheafOfModules.RingedSite.restrictionAlong
        (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom)).obj ℱ ⟶
        (SheafOfModules.RingedSite.restrictionAlong
          (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom)).obj ℱ')
    (s : ℱ.sections) : ℱ'.sections :=
  show ℱ'.sections from
    SheafOfModules.sectionsMap
      (M := (SheafOfModules.RingedSite.restrictionAlong
        (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom)).obj ℱ)
      (N := (SheafOfModules.RingedSite.restrictionAlong
        (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom)).obj ℱ')
      D
      (show ((SheafOfModules.RingedSite.restrictionAlong
        (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom)).obj ℱ).sections from s)

/-- Lemma 29.33.2: differential operators commute with tensoring by the pullback of a
quasi-coherent module under arbitrary base change. Concretely, an order-`k` differential operator
`D : \mathcal F \to \mathcal F'` on `X/S` induces a unique order-`k` differential operator on
`pr_1^* \mathcal F \otimes pr_2^* \mathcal G` over `X \times_S Y / Y` acting by `D` on the first
factor and the identity on the second factor. -/
@[stacks 0G45]
theorem exists_tensor_pullback_differentialOperator
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [MonoidalCategory (Limits.pullback a b).Modules]
    (ℱ ℱ' : X.Modules) [ℱ.IsQuasicoherent] [ℱ'.IsQuasicoherent]
    (𝒢 : Y.Modules) [𝒢.IsQuasicoherent]
    (k : ℕ)
    (D :
      (SheafOfModules.RingedSite.restrictionAlong
        (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom)).obj ℱ ⟶
        (SheafOfModules.RingedSite.restrictionAlong
          (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom)).obj ℱ')
    (hD : SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder.{u, u}
      (RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom) D k) :
    ∃! D' :
        (SheafOfModules.RingedSite.restrictionAlong
          (RingedSpace.Hom.inverseImageStructureSheafHomComm (Limits.pullback.snd a b).toShHom)).obj
            (((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj ℱ) ⊗ₘ
              ((Scheme.Modules.pullback (Limits.pullback.snd a b)).obj 𝒢) :
                (Limits.pullback a b).Modules) ⟶
          (SheafOfModules.RingedSite.restrictionAlong
            (RingedSpace.Hom.inverseImageStructureSheafHomComm (Limits.pullback.snd a b).toShHom)).obj
            (((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj ℱ') ⊗ₘ
              ((Scheme.Modules.pullback (Limits.pullback.snd a b)).obj 𝒢) :
                (Limits.pullback a b).Modules),
      SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder.{u, u}
          (RingedSpace.Hom.inverseImageStructureSheafHomComm (Limits.pullback.snd a b).toShHom) D' k ∧
        ∀ s : ℱ.sections, ∀ t : 𝒢.sections,
          SheafOfModules.sectionsMap D'
              (tensorSection
                (Scheme.pullbackSections (Limits.pullback.fst a b) s)
                (Scheme.pullbackSections (Limits.pullback.snd a b) t)) =
            tensorSection
              (Scheme.pullbackSections (Limits.pullback.fst a b)
                (applyRestrictedSection a D s))
              (Scheme.pullbackSections (Limits.pullback.snd a b) t) := sorry

end Scheme.Modules

end AlgebraicGeometry
