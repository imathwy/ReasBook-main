import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap17.SheafOfModulesTensorUnit
import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory MonoidalCategory Opposite PresheafOfModules.Monoidal
open CategoryTheory.Limits
open SheafOfModules.RingedSite
  (ringSheaf ringedSiteModuleCategory restrictionAlong unitModule)

noncomputable section

universe u v

/-- The underlying `RingCat`-valued presheaf of a presheaf of commutative rings. -/
abbrev ringPresheaf {C : Type u} [Category.{v} C]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) : Cᵒᵖ ⥤ RingCat.{max u v} :=
  𝒪 ⋙ forget₂ CommRingCat RingCat

section PresheafFlat

variable {C : Type u} [Category.{v} C]

namespace PresheafOfModules

/-- Definition 18.28.1 (1): a presheaf of `\mathcal O`-modules is flat when tensoring with it on
presheaves of `\mathcal O`-modules is an exact endofunctor. -/
@[stacks 03ER]
class IsFlat
    {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) : Prop where
  /-- Tensoring on the right by `ℱ` is exact on presheaves of `\mathcal O`-modules. -/
  exact_tensor :
    exactFunctor
      (PresheafOfModules (ringPresheaf 𝒪))
      (PresheafOfModules (ringPresheaf 𝒪))
      (tensorRight ℱ)

/-- The same-site ring map induced by a morphism of presheaves of commutative rings. -/
abbrev presheafStructureMap
    {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    ringPresheaf 𝒪 ⟶ ringPresheaf 𝒪' :=
  CategoryTheory.Functor.whiskerRight α (forget₂ CommRingCat RingCat)

/-- Definition 18.28.1 (2): a morphism of presheaves of commutative rings is flat when the
target, viewed by restriction of scalars as a presheaf of modules over the source, is flat. -/
@[stacks 03ER]
def IsFlatHom
    {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') : Prop :=
  IsFlat
    ((PresheafOfModules.restrictScalars (presheafStructureMap α)).obj
      (PresheafOfModules.unit (ringPresheaf 𝒪')))

/-- The structure presheaf, viewed as a module over itself, is flat. -/
theorem unit_isFlat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    IsFlat (PresheafOfModules.unit (ringPresheaf 𝒪)) := by
  refine ⟨?_⟩
  -- Proof comment: compare right tensor by the unit object with the identity via the ambient
  -- right unitor, then transport finite-limit and finite-colimit preservation across that
  -- natural isomorphism.
  let e :
      tensorRight (PresheafOfModules.unit (ringPresheaf 𝒪)) ≅
        𝟭 (PresheafOfModules (ringPresheaf 𝒪)) := by
    simpa [CategoryTheory.MonoidalCategory.tensorUnitRight] using
      (rightUnitorNatIso (PresheafOfModules (ringPresheaf 𝒪)))
  letI :
      PreservesFiniteLimits (tensorRight (PresheafOfModules.unit (ringPresheaf 𝒪))) :=
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e.symm
  letI :
      PreservesFiniteColimits (tensorRight (PresheafOfModules.unit (ringPresheaf 𝒪))) :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e.symm
  exact (exactFunctor_iff (tensorRight (PresheafOfModules.unit (ringPresheaf 𝒪)))).2
    ⟨inferInstance, inferInstance⟩

instance (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    IsFlat (PresheafOfModules.unit (ringPresheaf 𝒪)) :=
  unit_isFlat 𝒪

end PresheafOfModules

end PresheafFlat

section PresheafSheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]

namespace PresheafOfModules

/-- The commutative-ring-valued sheafification of a presheaf of commutative rings. -/
abbrev commRingSheafification (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Sheaf J CommRingCat.{max u v} :=
  (presheafToSheaf J CommRingCat.{max u v}).obj 𝒪

private noncomputable abbrev sheafificationRingBridge
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    (presheafToSheaf J RingCat.{max u v}).obj (ringPresheaf 𝒪) ⟶
      ringSheaf J (commRingSheafification J 𝒪) :=
  (CategoryTheory.sheafComposeNatTrans J (forget₂ CommRingCat RingCat)
    (CategoryTheory.sheafificationAdjunction J CommRingCat.{max u v})
    (CategoryTheory.sheafificationAdjunction J RingCat.{max u v})).app 𝒪

/-- The canonical ring map from a presheaf of commutative rings to the underlying `RingCat`
presheaf of its sheafification. -/
abbrev sheafificationRingMap (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    ringPresheaf 𝒪 ⟶ (ringSheaf J (commRingSheafification J 𝒪)).obj :=
  CategoryTheory.toSheafify J (ringPresheaf 𝒪) ≫
    (sheafToPresheaf J RingCat.{max u v}).map (sheafificationRingBridge (J := J) 𝒪)

omit [J.WEqualsLocallyBijective CommRingCat.{max u v}] in
private theorem sheafificationRingMap_eq_whiskerRight
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    sheafificationRingMap J 𝒪 =
      Functor.whiskerRight
        (show 𝒪 ⟶ (commRingSheafification J 𝒪).obj from CategoryTheory.toSheafify J 𝒪)
        (forget₂ CommRingCat RingCat) := by
  simpa [sheafificationRingMap, sheafificationRingBridge, commRingSheafification, ringPresheaf,
    ringSheaf] using
    (CategoryTheory.sheafComposeNatTrans_fac J (forget₂ CommRingCat RingCat)
      (CategoryTheory.sheafificationAdjunction J CommRingCat.{max u v})
      (CategoryTheory.sheafificationAdjunction J RingCat.{max u v}) 𝒪)

instance sheafificationRingMap_isLocallyInjective
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Presheaf.IsLocallyInjective J (sheafificationRingMap J 𝒪) := by
  let η : 𝒪 ⟶ (commRingSheafification J 𝒪).obj := CategoryTheory.toSheafify J 𝒪
  have hη : Presheaf.IsLocallyInjective J η :=
    (J.W_toSheafify (A := CommRingCat.{max u v}) 𝒪).isLocallyInjective
  have hηForget :
      Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (Functor.whiskerRight η (forget₂ CommRingCat RingCat))
          (forget RingCat)) := by
    simpa using ((Presheaf.isLocallyInjective_forget_iff (J := J) (φ := η)).2 hη)
  have hηRing :
      Presheaf.IsLocallyInjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    (Presheaf.isLocallyInjective_forget_iff
      (J := J) (φ := Functor.whiskerRight η (forget₂ CommRingCat RingCat))).1 hηForget
  simpa [sheafificationRingMap_eq_whiskerRight (J := J) 𝒪, η] using hηRing

instance sheafificationRingMap_isLocallySurjective
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Presheaf.IsLocallySurjective J (sheafificationRingMap J 𝒪) := by
  let η : 𝒪 ⟶ (commRingSheafification J 𝒪).obj := CategoryTheory.toSheafify J 𝒪
  have hη : Presheaf.IsLocallySurjective J η :=
    (J.W_toSheafify (A := CommRingCat.{max u v}) 𝒪).isLocallySurjective
  have hηForget :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (Functor.whiskerRight η (forget₂ CommRingCat RingCat))
          (forget RingCat)) := by
    simpa using ((Presheaf.isLocallySurjective_iff_whisker_forget (J := J) η).1 hη)
  have hηRing :
      Presheaf.IsLocallySurjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget
      (J := J) (Functor.whiskerRight η (forget₂ CommRingCat RingCat))).2 hηForget
  simpa [sheafificationRingMap_eq_whiskerRight (J := J) 𝒪, η] using hηRing

/-- Sheafification of presheaves of modules along the canonical map `\mathcal O \to \mathcal O^\#`. -/
abbrev moduleSheafification
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    PresheafOfModules (ringPresheaf 𝒪) ⥤
      ringedSiteModuleCategory J (commRingSheafification J 𝒪) :=
  PresheafOfModules.sheafification (sheafificationRingMap J 𝒪)

end PresheafOfModules

end PresheafSheafification

section SheafFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- The source-facing tensor product of sheaves of modules on a ringed site. -/
noncomputable abbrev moduleTensor
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (ℱ 𝒢 : Mod(𝒪)) :
    Mod(𝒪) :=
  tensorObj ℱ 𝒢

namespace SheafOfModules.RingedSite

scoped infixr:70 " ⊗ " => moduleTensor

end SheafOfModules.RingedSite

open scoped SheafOfModules.RingedSite

/-- Sheafification of module presheaves over a commutative ring sheaf. -/
noncomputable abbrev moduleSheafification (𝒪 : Sheaf J CommRingCat.{max u v}) :
    PresheafOfModules (ringSheaf J 𝒪).obj ⥤ Mod(𝒪) :=
  PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj)

namespace SheafOfModules.RingedSite.Sheafification

/- Textbook notation for sheafification of a presheaf of `\mathcal O`-modules on a fixed ringed
site. The ambient ringed-site data is inferable from the module presheaf, so the source-facing
surface can use `ℱ^#`. -/
set_option quotPrecheck false in
scoped postfix:max "^#" => fun ℱ ↦ Functor.obj (moduleSheafification _) ℱ

end SheafOfModules.RingedSite.Sheafification

namespace SheafOfModules.RingedSite

/-- The tensor morphism induced by morphisms in each factor. -/
noncomputable abbrev moduleTensorMap {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    {ℱ₁ ℱ₂ 𝒢₁ 𝒢₂ : Mod(𝒪)}
    (α : ℱ₁ ⟶ ℱ₂) (β : 𝒢₁ ⟶ 𝒢₂) :
    moduleTensor ℱ₁ 𝒢₁ ⟶ moduleTensor ℱ₂ 𝒢₂ :=
  tensorHom α β

/-- The canonical bridge from the source-facing tensor product `moduleTensor` to the ambient
monoidal tensor on sheaves of modules. -/
noncomputable abbrev moduleTensorIsoTensorObj
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (ℱ 𝒢 : Mod(𝒪)) :
    moduleTensor ℱ 𝒢 ≅
      (MonoidalCategoryStruct.tensorObj ℱ 𝒢 : Mod(𝒪)) :=
  Iso.refl _

/-- The endofunctor given by tensoring on the right by a fixed sheaf of modules. -/
noncomputable abbrev sheafModuleTensorRightFunctor {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (𝒢 : Mod(𝒪)) :
    Mod(𝒪) ⥤ Mod(𝒪) :=
  tensorRight 𝒢

/- Definition 18.28.1 (3) and (4) are already owned upstream by
`SheafOfModules.RingedSite.IsFlat`, `SheafOfModules.RingedSite.IsFlatHom`, and
`SheafOfModules.RingedSite.isFlatHom_iff` from `RingedSiteModuleCategory`. -/

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The structure sheaf, viewed as a module over itself, is flat. -/
theorem unit_isFlat
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [MonoidalCategory (Mod(𝒪))] :
    IsFlat 𝒪 (unitModule J 𝒪) := by
  refine ⟨?_⟩
  -- Proof comment: after unfolding the source-facing `unitModule`, right tensor by the
  -- structure sheaf is the tensor-unit endofunctor, hence naturally isomorphic to the identity.
  let eUnit : (unitModule J 𝒪 : Mod(𝒪)) ≅ (𝟙_ Mod(𝒪)) := by
    simpa [unitModule, ringedSiteModuleCategory, ringSheaf] using
      (SheafOfModules.unitIsoTensorUnit (R := ringSheaf J 𝒪))
  let e : tensorRight (unitModule J 𝒪) ≅ 𝟭 (Mod(𝒪)) :=
    (tensoringRight (Mod(𝒪))).mapIso eUnit ≪≫ rightUnitorNatIso (Mod(𝒪))
  letI : PreservesFiniteLimits (tensorRight (unitModule J 𝒪)) :=
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e.symm
  letI : PreservesFiniteColimits (tensorRight (unitModule J 𝒪)) :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e.symm
  exact (exactFunctor_iff (tensorRight (unitModule J 𝒪))).2 ⟨inferInstance, inferInstance⟩

instance (𝒪 : Sheaf J CommRingCat.{max u v})
    [MonoidalCategory (Mod(𝒪))] :
    IsFlat 𝒪 (unitModule J 𝒪) :=
  unit_isFlat 𝒪

end SheafOfModules.RingedSite

export SheafOfModules.RingedSite (sheafModuleTensorRightFunctor)

end SheafFlat
