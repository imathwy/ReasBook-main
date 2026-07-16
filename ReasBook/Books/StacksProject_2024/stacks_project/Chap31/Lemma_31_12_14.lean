import Mathlib
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap28.Definition_28_7_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

section ReflexiveHullExtension

variable [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

-- Semantic recall note: `lean_leansearch` surfaced generic-localization/stalk analogues such as
-- `ModuleCat.Tilde.toStalk` and `ModuleCat.Tilde.stalkToFiberLinearMap`. For the present sheaf-side
-- statement, the verified owners in the local environment are `Scheme.functionField`,
-- `RingedSpace.moduleStalkHom`, `ModuleCat.restrictScalars`, and `IsLocalizedModule`.

/-- `T` extends to `\mathcal G \to \mathcal F^{**}` at the generic point when the generic stalk of
the extension agrees with `T` after composing with the canonical map
`\mathcal F_\eta \to (\mathcal F^{**})_\eta`. -/

abbrev extendsToReflexiveHullAtGenericPoint
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X)) : Prop :=
  ∃ φ : 𝒢 ⟶ reflexiveHull ℱ,
    RingedSpace.moduleStalkHom (genericPoint X) φ =
      T ≫ RingedSpace.moduleStalkHom (genericPoint X) (toReflexiveHull ℱ)

end ReflexiveHullExtension

/-- The height-one image condition at `x`: after identifying both generic stalks with the
localizations of the stalks at `x`, the image of `\mathcal G_x` under `T` lands in the image of
`\mathcal F_x` inside the generic stalk. This is stated canonically by requiring the range
inclusion for every localization map exhibiting the generic stalk as the localization at the
non-zero-divisors of `\mathcal O_{X, x}`. -/
def heightOneStalkImageConditionAt
    (ℱ 𝒢 : X.Modules)
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X))
    (x : X) : Prop :=
  ∀ (ι𝒢 :
        RingedSpace.stalkModuleCat 𝒢 x ⟶
          (ModuleCat.restrictScalars (algebraMap (X.presheaf.stalk x) X.functionField)).obj
            (RingedSpace.stalkModuleCat 𝒢 (genericPoint X)))
      (_ : IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x)) ι𝒢.hom)
      (ιℱ :
        RingedSpace.stalkModuleCat ℱ x ⟶
          (ModuleCat.restrictScalars (algebraMap (X.presheaf.stalk x) X.functionField)).obj
            (RingedSpace.stalkModuleCat ℱ (genericPoint X)))
      (_ : IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x)) ιℱ.hom),
    (LinearMap.comp
        (((ModuleCat.restrictScalars (algebraMap (X.presheaf.stalk x) X.functionField)).map T).hom)
        ι𝒢.hom).range ≤
      ιℱ.hom.range

/-- The height-one image condition from Lemma 31.12.14, stated independently of any chosen
localization maps from the stalks to the generic stalk. -/
def heightOneStalkConditionForExtension
    (ℱ 𝒢 : X.Modules)
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X)) : Prop :=
  ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
    heightOneStalkImageConditionAt ℱ 𝒢 T x

/-- Pointwise specialization of `heightOneStalkConditionForExtension` to chosen localization maps.
-/
theorem heightOneStalkConditionForExtension_apply
    (ℱ 𝒢 : X.Modules)
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X))
    (hT : heightOneStalkConditionForExtension ℱ 𝒢 T)
    (x : X) (hx : ringKrullDim (X.presheaf.stalk x) = 1)
    (ι𝒢 :
      RingedSpace.stalkModuleCat 𝒢 x ⟶
        (ModuleCat.restrictScalars (algebraMap (X.presheaf.stalk x) X.functionField)).obj
          (RingedSpace.stalkModuleCat 𝒢 (genericPoint X)))
    (hι𝒢 : IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x)) ι𝒢.hom)
    (ιℱ :
      RingedSpace.stalkModuleCat ℱ x ⟶
        (ModuleCat.restrictScalars (algebraMap (X.presheaf.stalk x) X.functionField)).obj
          (RingedSpace.stalkModuleCat ℱ (genericPoint X)))
    (hιℱ : IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x)) ιℱ.hom) :
    (LinearMap.comp
        (((ModuleCat.restrictScalars (algebraMap (X.presheaf.stalk x) X.functionField)).map T).hom)
        ι𝒢.hom).range ≤
      ιℱ.hom.range :=
  hT x hx ι𝒢 hι𝒢 ιℱ hιℱ

section ReflexiveHullExtension

variable [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

/-- Lemma 31.12.14: let `X` be an integral locally Noetherian normal scheme with generic point
`\eta`, let `\mathcal F`, `\mathcal G` be coherent `\mathcal O_X`-modules, and let
`T : \mathcal G_\eta \to \mathcal F_\eta` be a linear map. If `X` is normal, then `T` extends to
a morphism `\mathcal G \to \mathcal F^{**}` if and only if for every `x ∈ X` with
`dim(\mathcal O_{X, x}) = 1`, the image of `\mathcal G_x` under `T` lands in the image of
`\mathcal F_x` inside the generic stalk. -/

@[stacks 0AY7]
theorem extendsToReflexiveHullAtGenericPoint_iff_forall_heightOne
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    (hXnormal : X.isNormal)
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X)) :
    extendsToReflexiveHullAtGenericPoint ℱ 𝒢 T ↔
      heightOneStalkConditionForExtension ℱ 𝒢 T := sorry

end ReflexiveHullExtension

end AlgebraicGeometry.Scheme.Modules
