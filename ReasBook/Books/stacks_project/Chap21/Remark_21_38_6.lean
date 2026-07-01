import Mathlib
import stacks_project.Chap21.Situation_21_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable (X : RingedSite.{u, v}) (P : FibredCategoryOver X)
variable [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]
variable [Functor.IsCocontinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]

local notation "Jₚ" => inheritedTopology X.siteTopology P
local notation "𝒪ₚ" => inheritedStructureSheaf X P

/-- The inverse-image functor `π^{-1}` on module sheaves for the projection
`\pi : \operatorname{Sh}(\mathcal C) \to \operatorname{Sh}(X)` from Situation `21.38.1`. -/
abbrev projectionModuleInverseImage :
    SheafOfModules X.structureSheaf ⥤ SheafOfModules 𝒪ₚ :=
  @SheafOfModules.pushforward _ _ _ _
    Jₚ X.siteTopology P.p 𝒪ₚ X.structureSheaf inferInstance
    (𝟙 _)

/-- The chosen lower shriek functor `π_!` on module sheaves, defined as a left adjoint to the
projection inverse-image functor `π^{-1}` whenever that adjoint exists. -/
abbrev projectionModuleLowerShriek
    [(projectionModuleInverseImage X P).IsRightAdjoint] :
    SheafOfModules 𝒪ₚ ⥤ SheafOfModules X.structureSheaf :=
  Functor.leftAdjoint (projectionModuleInverseImage X P)

/-- The inverse-image functor `π^{-1}` on abelian sheaves for the projection
`\pi : \operatorname{Sh}(\mathcal C) \to \operatorname{Sh}(X)`. -/
abbrev projectionAbelianInverseImage :
    Sheaf X.siteTopology AddCommGrpCat ⥤ Sheaf Jₚ AddCommGrpCat :=
  P.p.sheafPushforwardContinuous AddCommGrpCat.{max u v} Jₚ X.siteTopology

/-- The chosen lower shriek functor `π_!^{Ab}` on abelian sheaves, defined as a left adjoint to
the projection inverse-image functor on abelian sheaves whenever that adjoint exists. -/
abbrev projectionAbelianLowerShriek
    [(projectionAbelianInverseImage X P).IsRightAdjoint] :
    Sheaf Jₚ AddCommGrpCat ⥤ Sheaf X.siteTopology AddCommGrpCat :=
  Functor.leftAdjoint (projectionAbelianInverseImage X P)

/-- The forgetful functor from `\mathcal O_\mathcal C`-modules to underlying abelian sheaves on
the total site of the fibred category. -/
abbrev projectionSourceForget :
    SheafOfModules 𝒪ₚ ⥤ Sheaf Jₚ AddCommGrpCat :=
  SheafOfModules.toSheaf 𝒪ₚ

/-- The forgetful functor from `\mathcal O_X`-modules to underlying abelian sheaves on the base
ringed site. -/
abbrev projectionTargetForget :
    SheafOfModules X.structureSheaf ⥤ Sheaf X.siteTopology AddCommGrpCat :=
  SheafOfModules.toSheaf X.structureSheaf

-- Proof sketch: specialize Lemma `21.38.5 (3)` to the case where the target fibred category is
-- the base site and the comparison morphism is the projection `P.p`. The resulting lower shriek
-- on modules and on abelian sheaves is exactly `π_!`, and the comparison natural isomorphism is
-- the claimed commutativity of the forget square.
/-- Remark 21.38.6 (1): for the projection
`\pi : \operatorname{Sh}(\mathcal C) \to \operatorname{Sh}(X)` attached to a fibred category over
the ringed site `X`, the lower shriek on module sheaves and the lower shriek on abelian sheaves
commute with forgetting module structure, equivalently via a comparison natural transformation
whose components are isomorphisms. -/
theorem projectionLowerShriek_forget_comparison_exists
    [(projectionModuleInverseImage X P).IsRightAdjoint]
    [(projectionAbelianInverseImage X P).IsRightAdjoint] :
    ∃ comparison :
      projectionSourceForget X P ⋙ projectionAbelianLowerShriek X P ⟶
        projectionModuleLowerShriek X P ⋙ projectionTargetForget X,
      ∀ M, IsIso (comparison.app M) := sorry

end

section

variable (X : RingedSite.{u, v}) (P : FibredCategoryOver X)
variable [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]
variable [Functor.IsCocontinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]

local notation "Jₚ" => inheritedTopology X.siteTopology P
local notation "𝒪ₚ" => inheritedStructureSheaf X P

/-- The chosen derived lower shriek functor `L\pi_!` on module sheaves, attached to a chosen
realization of the derived inverse-image functor `π^{-1}`. -/
abbrev projectionModuleDerivedLowerShriek
    (projectionModuleDerivedInverseImage :
      DerivedCategory (SheafOfModules X.structureSheaf) ⥤
        DerivedCategory (SheafOfModules 𝒪ₚ))
    [projectionModuleDerivedInverseImage.IsRightAdjoint] :
    DerivedCategory (SheafOfModules 𝒪ₚ) ⥤
      DerivedCategory (SheafOfModules X.structureSheaf) :=
  Functor.leftAdjoint projectionModuleDerivedInverseImage

/-- The chosen derived lower shriek functor `L\pi_!^{Ab}` on abelian sheaves, attached to a
chosen realization of the derived inverse-image functor `π^{-1}` on abelian sheaves. -/
abbrev projectionAbelianDerivedLowerShriek
    (projectionAbelianDerivedInverseImage :
      DerivedCategory (Sheaf X.siteTopology AddCommGrpCat) ⥤
        DerivedCategory (Sheaf Jₚ AddCommGrpCat))
    [projectionAbelianDerivedInverseImage.IsRightAdjoint] :
    DerivedCategory (Sheaf Jₚ AddCommGrpCat) ⥤
      DerivedCategory (Sheaf X.siteTopology AddCommGrpCat) :=
  Functor.leftAdjoint projectionAbelianDerivedInverseImage

-- Proof sketch: specialize Lemma `21.38.5 (6)` to the projection situation coming from
-- `Situation 21.38.1`. The resulting derived comparison between `L\pi_!` on modules and
-- `L\pi_!^{Ab}` on abelian sheaves is the natural isomorphism between the two forgetful
-- composites below.
/-- Remark 21.38.6 (2): after passing to derived categories, the derived lower shriek on
`\mathcal O_\mathcal C`-modules commutes with forgetting to derived abelian sheaves on the total
site and on the base site, equivalently via a comparison natural transformation whose components
are isomorphisms. -/
theorem projectionDerivedLowerShriek_forget_comparison_exists
    (sourceForgetDerived :
      DerivedCategory (SheafOfModules 𝒪ₚ) ⥤
        DerivedCategory (Sheaf Jₚ AddCommGrpCat))
    (targetForgetDerived :
      DerivedCategory (SheafOfModules X.structureSheaf) ⥤
        DerivedCategory (Sheaf X.siteTopology AddCommGrpCat))
    (projectionModuleDerivedInverseImage :
      DerivedCategory (SheafOfModules X.structureSheaf) ⥤
        DerivedCategory (SheafOfModules 𝒪ₚ))
    (projectionAbelianDerivedInverseImage :
      DerivedCategory (Sheaf X.siteTopology AddCommGrpCat) ⥤
        DerivedCategory (Sheaf Jₚ AddCommGrpCat))
    [projectionModuleDerivedInverseImage.IsRightAdjoint]
    [projectionAbelianDerivedInverseImage.IsRightAdjoint] :
    ∃ comparison :
      sourceForgetDerived ⋙
          projectionAbelianDerivedLowerShriek X P projectionAbelianDerivedInverseImage ⟶
        projectionModuleDerivedLowerShriek X P projectionModuleDerivedInverseImage ⋙
          targetForgetDerived,
      ∀ K, IsIso (comparison.app K) := sorry

end

end FibredCategoryOver
end CategoryTheory
