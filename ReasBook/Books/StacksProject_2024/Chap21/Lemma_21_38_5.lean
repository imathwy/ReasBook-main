import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import StacksProject_2024.Chap21.Situation_21_38_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable {D : RingedSite.{u, v}} (S : inherited_ringed_topos_situation D)

/-- The inherited topology on the source fibred category `\mathcal C'`. -/
abbrev sourceTopology :=
  FibredCategoryOver.inheritedTopology D.siteTopology S.C'

/-- The inherited topology on the target fibred category `\mathcal C`. -/
abbrev targetTopology :=
  FibredCategoryOver.inheritedTopology D.siteTopology S.C

/-- The inherited structure sheaf `\mathcal O_{\mathcal C'}` on the source fibred category. -/
abbrev sourceStructureSheaf :=
  inheritedStructureSheaf D S.C'

/-- The inherited structure sheaf `\mathcal O_\mathcal C` on the target fibred category. -/
abbrev targetStructureSheaf :=
  inheritedStructureSheaf D S.C

/-- The comparison functor `u : \mathcal C' \to \mathcal C` in the inherited ringed-topos
situation. -/
private abbrev comparisonFunctor : S.C'.S ⥤ S.C.S := S.u.G

/-- The opposite comparison functor used in Kan-extension hypotheses. -/
private abbrev comparisonFunctorOp : Opposite S.C'.S ⥤ Opposite S.C.S :=
  (comparisonFunctor S).op

/-- The pullback `g^{-1}\mathcal O_\mathcal C` of the target structure sheaf to the source site. -/
abbrev pullbackTargetStructureSheaf :=
  (Functor.sheafPushforwardContinuous (comparisonFunctor S) RingCat.{max u v}
    (sourceTopology S) (targetTopology S)).obj
    (targetStructureSheaf S)

local notation "JC'" => sourceTopology S
local notation "JC" => targetTopology S
local notation "𝒪C'" => sourceStructureSheaf S
local notation "𝒪C" => targetStructureSheaf S
local notation "g" => comparisonFunctor S
local notation "gInv𝒪C" => pullbackTargetStructureSheaf S

/-- The category `\mathrm{Mod}(\mathcal O_{\mathcal C'})` of module sheaves on the source site,
viewed through the chosen identification `\mathcal O_{\mathcal C'} \cong g^{-1}\mathcal O_\mathcal C`
from Situation `21.38.3`. -/
abbrev sourceModuleCat :=
  SheafOfModules gInv𝒪C

/-- The category `\mathrm{Mod}(\mathcal O_\mathcal C)` of module sheaves on the target site. -/
abbrev targetModuleCat :=
  SheafOfModules 𝒪C

/-- The category `\mathrm{Ab}(\mathcal C')` of abelian sheaves on the source site. -/
abbrev sourceAbelianSheafCat :=
  Sheaf JC' AddCommGrpCat.{max u v}

/-- The category `\mathrm{Ab}(\mathcal C)` of abelian sheaves on the target site. -/
abbrev targetAbelianSheafCat :=
  Sheaf JC AddCommGrpCat.{max u v}

/-- The forgetful functor from `\mathcal O_{\mathcal C'}`-modules, viewed via the chosen
identification with `g^{-1}\mathcal O_\mathcal C`, to underlying abelian sheaves. -/
abbrev sourceModuleForget :
    sourceModuleCat S ⥤ sourceAbelianSheafCat S :=
  SheafOfModules.toSheaf gInv𝒪C

/-- The forgetful functor from `\mathcal O_\mathcal C`-modules to underlying abelian sheaves. -/
abbrev targetModuleForget :
    targetModuleCat S ⥤ targetAbelianSheafCat S :=
  SheafOfModules.toSheaf 𝒪C

/-- The inverse-image functor `g^{-1}` on abelian sheaves in Situation `21.38.3`. -/
abbrev abelianInverseImage :
    targetAbelianSheafCat S ⥤ sourceAbelianSheafCat S :=
  Functor.sheafPushforwardContinuous g AddCommGrpCat.{max u v} JC' JC

/-- The inverse-image functor `g^{-1}` on module sheaves in Situation `21.38.3`. -/
abbrev moduleInverseImage :
    targetModuleCat S ⥤ sourceModuleCat S :=
  @SheafOfModules.pushforward _ _ _ _
    JC' JC g gInv𝒪C 𝒪C inferInstance
    (𝟙 _)

/-- The chosen left adjoint `g^{Ab}_!` of `g^{-1}` on abelian sheaves. -/
abbrev abelianLowerShriek
    [(abelianInverseImage S).IsRightAdjoint] :
    sourceAbelianSheafCat S ⥤ targetAbelianSheafCat S :=
  Functor.leftAdjoint (abelianInverseImage S)

/-- The chosen left adjoint `g_!` of `g^{-1}` on module sheaves. -/
abbrev moduleLowerShriek
    [(moduleInverseImage S).IsRightAdjoint] :
    sourceModuleCat S ⥤ targetModuleCat S :=
  Functor.leftAdjoint (moduleInverseImage S)

-- Proof sketch: apply the site-level lower-shriek existence theorem for modules to the inherited
-- topologies of `\mathcal C'` and `\mathcal C`. The structure-sheaf comparison in Situation
-- `21.38.3` identifies the source ring sheaf with the pullback of the target ring sheaf, so the
-- inverse-image functor on modules is exactly `moduleInverseImage S`.
/-- Lemma 21.38.5 (1): the inverse-image functor `g^{-1}` on module sheaves
`\mathrm{Mod}(\mathcal O_\mathcal C) \to \mathrm{Mod}(\mathcal O_{\mathcal C'})` admits a left
adjoint `g_!`. In the present API this is expressed by saying that `moduleInverseImage S` is a
right adjoint. -/
theorem moduleInverseImage_isRightAdjoint
    [Functor.IsCocontinuous g JC' JC]
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [∀ U' : S.C'.S,
      HasWeakSheafify
        ((targetTopology S).over ((comparisonFunctor S).obj U')) AddCommGrpCat.{max u v}]
    [∀ U' : S.C'.S,
      ∀ F : (Over U')ᵒᵖ ⥤ AddCommGrpCat.{max u v},
        (Over.post g).op.HasLeftKanExtension F] :
    (moduleInverseImage S).IsRightAdjoint := sorry

-- Proof sketch: once `u : \mathcal C' \to \mathcal C` is continuous and cocontinuous for the
-- inherited topologies, the lower shriek on abelian sheaves is the usual sheaf-theoretic lower
-- shriek attached to `u`, equivalently the left adjoint to the inverse-image functor on sheaves.
/-- Lemma 21.38.5 (2): the inverse-image functor `g^{-1}` on abelian sheaves
`\mathrm{Ab}(\mathcal C) \to \mathrm{Ab}(\mathcal C')` admits a left adjoint `g_!^{Ab}`. In the
present API this is expressed by saying that `abelianInverseImage S` is a right adjoint. -/
theorem abelianInverseImage_isRightAdjoint
    [Functor.IsCocontinuous g JC' JC]
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [∀ F : Opposite (S.C'.S) ⥤ AddCommGrpCat.{max u v},
      (comparisonFunctorOp S).HasLeftKanExtension F] :
    (abelianInverseImage S).IsRightAdjoint := sorry

-- Proof sketch: compare both composites on the standard generators `j_{U'!}\mathcal O_{U'}` of
-- the source module category. Lemma `21.38.4` gives the needed local calculation on slices, and
-- Remark `18.41.2` upgrades that generator-level identification to a natural isomorphism of the
-- two functors.
/-- Lemma 21.38.5 (3): after forgetting module structures to underlying abelian sheaves, the
underived lower shriek on modules agrees with the lower shriek on abelian sheaves. Equivalently,
there is a natural isomorphism witnessing commutativity of the square
`Mod(\mathcal O_{\mathcal C'}) \to Mod(\mathcal O_\mathcal C)` over
`Ab(\mathcal C') \to Ab(\mathcal C)`. -/
theorem lowerShriek_forget_comparison_exists
    [(moduleInverseImage S).IsRightAdjoint]
    [(abelianInverseImage S).IsRightAdjoint] :
    ∃ comparison :
      sourceModuleForget S ⋙ abelianLowerShriek S ⟶
        moduleLowerShriek S ⋙ targetModuleForget S,
      ∀ M, IsIso (comparison.app M) := sorry

-- Proof sketch: equip the module categories with their standard derived categories and view
-- `g^{-1}` on modules as the exact functor induced by `moduleInverseImage S`. The derived
-- adjunction theorem applied to the existence result of clause `(1)` gives a left adjoint on
-- derived categories, which is recorded here as right-adjointness of
-- `moduleDerivedInverseImage S`.
/-- Lemma 21.38.5 (4): on derived categories of module sheaves, the functor `g^{-1}` admits a
left adjoint `Lg_!`. Here `gInvMod` denotes a chosen realization of `g^{-1}` on derived
categories of module sheaves. -/
theorem moduleDerivedInverseImageFunctor_isRightAdjoint
    [Abelian (sourceModuleCat S)]
    [Abelian (targetModuleCat S)]
    (gInvMod :
      DerivedCategory (targetModuleCat S) ⥤
        DerivedCategory (sourceModuleCat S)) :
    gInvMod.IsRightAdjoint := sorry

-- Proof sketch: the inverse-image functor on abelian sheaves is exact, so it induces the exact
-- functor `abelianDerivedInverseImage S` on derived categories. The existence of `Lg_!^{Ab}` is
-- then the derived-category adjunction statement corresponding to clause `(2)`.
/-- Lemma 21.38.5 (5): on derived categories of abelian sheaves, the functor `g^{-1}` admits a
left adjoint `Lg_!^{Ab}`. Here `gInvAb` denotes a chosen realization of `g^{-1}` on derived
categories of abelian sheaves. -/
theorem abelianDerivedInverseImageFunctor_isRightAdjoint
    (gInvAb :
      DerivedCategory (targetAbelianSheafCat S) ⥤
        DerivedCategory (sourceAbelianSheafCat S)) :
    gInvAb.IsRightAdjoint := sorry

-- Proof sketch: derive the comparison from clause `(3)` through the exact forgetful functors from
-- module sheaves to abelian sheaves. Equivalently, compare both composites on the generators
-- `j_{U'!}\mathcal O_{U'}` in degree zero and use the uniqueness of left adjoints on derived
-- categories.
/-- Lemma 21.38.5 (6): after passing to derived categories and forgetting module structures, the
derived lower shriek on modules agrees with the derived lower shriek on abelian sheaves.
Equivalently, there is a natural isomorphism witnessing commutativity of the square
`D(\mathcal O_{\mathcal C'}) \to D(\mathcal O_\mathcal C)` over
`D(\mathcal C') \to D(\mathcal C)`. -/
theorem derivedLowerShriek_forget_comparison_exists
    [Abelian (sourceModuleCat S)]
    [Abelian (targetModuleCat S)]
    (sourceForgetDerived :
      DerivedCategory (sourceModuleCat S) ⥤
        DerivedCategory (sourceAbelianSheafCat S))
    (targetForgetDerived :
      DerivedCategory (targetModuleCat S) ⥤
        DerivedCategory (targetAbelianSheafCat S))
    (gInvMod :
      DerivedCategory (targetModuleCat S) ⥤
        DerivedCategory (sourceModuleCat S))
    (gInvAb :
      DerivedCategory (targetAbelianSheafCat S) ⥤
        DerivedCategory (sourceAbelianSheafCat S))
    [gInvMod.IsRightAdjoint]
    [gInvAb.IsRightAdjoint] :
    ∃ comparison :
      sourceForgetDerived ⋙ Functor.leftAdjoint gInvAb ⟶
        Functor.leftAdjoint gInvMod ⋙ targetForgetDerived,
      ∀ K, IsIso (comparison.app K) := sorry

end

end FibredCategoryOver
end CategoryTheory
