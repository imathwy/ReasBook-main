import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_6_1
import stacks_proof.stacks_project.Chap12.Definition_12_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
universe u v

namespace CategoryTheory

noncomputable section

/-- Helper for Proposition 19.8.5: the free Yoneda presheaves form a separating family, so their
coproduct is a separator in the category of presheaves of `\mathcal O`-modules. -/
private theorem presheafOfModules_hasSeparator
    {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v}) :
    HasSeparator (PresheafOfModules.{max u v} 𝒪) := by
  letI : LocallySmall.{max u v} C := inferInstance
  let F : C → PresheafOfModules.{max u v} 𝒪 := fun X ↦
    ((CategoryTheory.yoneda ⋙ PresheafOfModules.free 𝒪).obj X)
  have hF : ObjectProperty.IsSeparating (.ofObj F) := by
    simpa [F, PresheafOfModules.freeYoneda] using
      (PresheafOfModules.freeYoneda.isSeparating (R := 𝒪))
  have hSep : IsSeparator (∐ F) := by
    exact CategoryTheory.ObjectProperty.IsSeparating.isSeparator_coproduct (f := F) hF
  exact ⟨⟨∐ F, hSep⟩⟩

/-- Helper for Proposition 19.8.5: the forgetful functor to presheaves of abelian groups reflects
finite limits, because limits are created pointwise and `ModuleCat → AddCommGrpCat` reflects them. -/
private theorem presheafOfModules_toPresheaf_reflectsFiniteLimits
    {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v}) :
    Limits.ReflectsFiniteLimits (PresheafOfModules.toPresheaf.{max u v} 𝒪) := by
  refine ⟨?_⟩
  intro J _ _
  refine ⟨?_⟩
  intro F
  refine ⟨?_⟩
  intro c hc
  letI (X : Cᵒᵖ) :
      Small (((F ⋙ PresheafOfModules.evaluation 𝒪 X) ⋙
        forget (ModuleCat (𝒪.obj X))).sections) := by
    have hX :
        IsLimit
          ((((PresheafOfModules.evaluation 𝒪 X) ⋙
              forget₂ (ModuleCat (𝒪.obj X)) AddCommGrpCat).mapCone c)) := by
      simpa using
        (isLimitOfPreserves (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat X) hc)
    have hX' :
        HasLimit
          ((F ⋙ PresheafOfModules.evaluation 𝒪 X) ⋙
            forget₂ (ModuleCat (𝒪.obj X)) AddCommGrpCat) := ⟨_, hX⟩
    simpa only [AddCommGrpCat.hasLimit_iff_small_sections] using hX'
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ ?_⟩
  intro X
  have hX :
      IsLimit
        ((((PresheafOfModules.evaluation 𝒪 X) ⋙
            forget₂ (ModuleCat (𝒪.obj X)) AddCommGrpCat).mapCone c)) := by
    simpa using
      (isLimitOfPreserves (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat X) hc)
  exact Limits.isLimitOfReflects (forget₂ (ModuleCat (𝒪.obj X)) AddCommGrpCat) hX

/-- Helper for Proposition 19.8.5: filtered colimits in presheaves of `\mathcal O`-modules are
exact because they are exact after forgetting to presheaves of abelian groups. -/
private theorem presheafOfModules_ab5
    {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v}) :
    AB5OfSize.{max u v, max u v} (PresheafOfModules.{max u v} 𝒪) := by
  letI : Limits.ReflectsFiniteLimits (PresheafOfModules.toPresheaf.{max u v} 𝒪) :=
    presheafOfModules_toPresheaf_reflectsFiniteLimits 𝒪
  refine ⟨?_⟩
  intro J _ _
  exact HasExactColimitsOfShape.domain_of_functor J
    (PresheafOfModules.toPresheaf.{max u v} 𝒪)

/-- Helper for Proposition 19.8.5: the category of presheaves of `\mathcal O`-modules is
Grothendieck abelian. -/
private theorem presheafOfModules_isGrothendieckAbelian
    {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v}) :
    IsGrothendieckAbelian.{max u v} (PresheafOfModules.{max u v} 𝒪) := by
  exact
    { locallySmall := inferInstance
      hasFilteredColimitsOfSize := inferInstance
      ab5OfSize := presheafOfModules_ab5 𝒪
      hasSeparator := presheafOfModules_hasSeparator 𝒪 }

/-- Proposition 19.8.5, owner-level form: presheaves of `\mathcal O`-modules admit functorial
injective embeddings. -/
@[stacks 01DV]
instance presheafOfModules_hasFunctorialInjectiveEmbeddings
    {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v}) :
    HasFunctorialInjectiveEmbeddings (PMod(𝒪)) := by
  -- Install the Grothendieck-abelian owner and apply the Chapter 12 bridge to injective
  -- embeddings.
  letI : IsGrothendieckAbelian.{max u v} (PMod(𝒪)) :=
    presheafOfModules_isGrothendieckAbelian 𝒪
  simpa using
    (hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian (C := PMod(𝒪)))

end

end CategoryTheory
