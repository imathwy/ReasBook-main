import Mathlib
import stacks_project.Chap19.Lemma_19_13_6

open CategoryTheory
open Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- The abelian category of sheaves of abelian groups on a site. -/
abbrev SiteAbelianSheafCat (J : GrothendieckTopology C) :=
  Sheaf J AddCommGrpCat.{max u v}

/-- The sections functor `\Gamma(U,-)` on abelian sheaves over a site. -/
abbrev siteAbelianSectionsFunctor (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{max u v}] :
    SiteAbelianSheafCat J ⥤ AddCommGrpCat.{max u v} :=
  sheafToPresheaf J AddCommGrpCat.{max u v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- The chosen unbounded derived sections functor `R\Gamma(U,-)` on abelian sheaves over a site.
-/
abbrev siteAbelianSectionsDerived (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [(siteAbelianSectionsFunctor J U).Additive]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] :
    DerivedCategory (SiteAbelianSheafCat J) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  additiveFunctorTotalRightDerived (siteAbelianSectionsFunctor J U)

/-- The chosen unbounded derived inverse-image functor on abelian sheaves attached to a
continuous and cocontinuous functor of sites. -/
abbrev siteAbelianInverseImageDerived
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD)]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat JD)] :
    DerivedCategory (SiteAbelianSheafCat JD) ⥤
      DerivedCategory (SiteAbelianSheafCat JC) :=
  additiveFunctorTotalRightDerived
    (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD)

/-- The inverse-image ring sheaf `g^{-1}\mathcal O_\mathcal D` on `\mathcal C`. -/
abbrev inverseImageRingSheaf
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) :
    Sheaf JC RingCat.{max u v} :=
  (u.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪D

/-- The source module category `\mathrm{Mod}(g^{-1}\mathcal O_\mathcal D)`. -/
abbrev SourceModuleCat
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) :=
  SheafOfModules (inverseImageRingSheaf JC JD u 𝒪D)

/-- The target module category `\mathrm{Mod}(\mathcal O_\mathcal D)`. -/
abbrev TargetModuleCat (𝒪D : Sheaf JD RingCat.{max u v}) :=
  SheafOfModules 𝒪D

/-- The inverse-image functor `g^* = g^{-1}` on module sheaves, realized by the identity map on
the inverse-image structure sheaf. -/
abbrev moduleInverseImageFunctor
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) :
    TargetModuleCat 𝒪D ⥤ SourceModuleCat JC JD u 𝒪D :=
  SheafOfModules.pushforward
    (𝟙 (inverseImageRingSheaf JC JD u 𝒪D))

/-- The chosen derived inverse-image functor on module sheaves attached to `u`. -/
abbrev moduleInverseImageDerived
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v})
    [Functor.Additive (moduleInverseImageFunctor JC JD u 𝒪D)]
    [IsGrothendieckAbelian.{max u v} (TargetModuleCat 𝒪D)] :
    DerivedCategory (TargetModuleCat 𝒪D) ⥤
      DerivedCategory (SourceModuleCat JC JD u 𝒪D) :=
  additiveFunctorTotalRightDerived
    (moduleInverseImageFunctor JC JD u 𝒪D)

/-- Sections over `U` on `g^{-1}\mathcal O_\mathcal D`-modules, viewed in abelian groups. -/
abbrev sourceModuleSectionsAsAbelianFunctor
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) (U : C)
    [HasWeakSheafify JC AddCommGrpCat.{max u v}] :
    SourceModuleCat JC JD u 𝒪D ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf (inverseImageRingSheaf JC JD u 𝒪D) ⋙
    sheafToPresheaf JC AddCommGrpCat.{max u v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- Derived sections over `U` on `g^{-1}\mathcal O_\mathcal D`-modules, viewed in
`D(\operatorname{Ab})`. -/
abbrev sourceModuleSectionsAsAbelianDerived
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) (U : C)
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [(sourceModuleSectionsAsAbelianFunctor JC JD u 𝒪D U).Additive]
    [IsGrothendieckAbelian.{max u v} (SourceModuleCat JC JD u 𝒪D)] :
    DerivedCategory (SourceModuleCat JC JD u 𝒪D) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  additiveFunctorTotalRightDerived
    (sourceModuleSectionsAsAbelianFunctor JC JD u 𝒪D U)

/-- Sections over `V` on `\mathcal O_\mathcal D`-modules, viewed in abelian groups. -/
abbrev targetModuleSectionsAsAbelianFunctor
    (𝒪D : Sheaf JD RingCat.{max u v}) (V : D)
    [HasWeakSheafify JD AddCommGrpCat.{max u v}] :
    TargetModuleCat 𝒪D ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf 𝒪D ⋙
    sheafToPresheaf JD AddCommGrpCat.{max u v} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{max u v}).obj (op V)

/-- Derived sections over `V` on `\mathcal O_\mathcal D`-modules, viewed in
`D(\operatorname{Ab})`. -/
abbrev targetModuleSectionsAsAbelianDerived
    (𝒪D : Sheaf JD RingCat.{max u v}) (V : D)
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [(targetModuleSectionsAsAbelianFunctor 𝒪D V).Additive]
    [IsGrothendieckAbelian.{max u v} (TargetModuleCat 𝒪D)] :
    DerivedCategory (TargetModuleCat 𝒪D) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  additiveFunctorTotalRightDerived
    (targetModuleSectionsAsAbelianFunctor 𝒪D V)

section

variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD)]
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat JC)]
variable [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat JD)]

-- Proof sketch: compute the chosen derived inverse image by a K-injective representative of `M`.
-- Lemma `21.37.1` gives acyclicity of inverse images of injective objects for sections over `U`,
-- so `RΓ(U,-)` of the inverse image is computed by ordinary sections. Evaluating the inverse-image
-- sheaf at `U` is the same as evaluating the original sheaf at `u(U)`, giving the comparison.
/-- Objectwise derived sections commute with inverse image on abelian sheaves for a continuous and
cocontinuous functor of sites. -/
theorem inverseImageAbelianDerived_sectionsOverObject_isomorphic
    (U : C)
    [(siteAbelianSectionsFunctor JC U).Additive]
    [(siteAbelianSectionsFunctor JD (u.obj U)).Additive]
    (M : DerivedCategory (SiteAbelianSheafCat JD)) :
    IsIsomorphic
      ((siteAbelianSectionsDerived JC U).obj
        ((siteAbelianInverseImageDerived u).obj M))
      ((siteAbelianSectionsDerived JD (u.obj U)).obj M) := sorry

end

section

variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable (𝒪D : Sheaf JD RingCat.{max u v})
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [Functor.Additive (moduleInverseImageFunctor JC JD u 𝒪D)]
variable [IsGrothendieckAbelian.{max u v} (SourceModuleCat JC JD u 𝒪D)]
variable [IsGrothendieckAbelian.{max u v} (TargetModuleCat 𝒪D)]

-- Proof sketch: represent `M` by a K-injective complex of `\mathcal O_\mathcal D`-modules.
-- Lemma `21.37.1` shows that inverse images of injective modules are acyclic for sections over
-- `U`, so the left-hand derived sections are computed by ordinary sections of the inverse-image
-- complex. Evaluating the inverse-image module at `U` agrees with evaluating the original complex
-- at `u(U)`, which gives the stated comparison in `D(\operatorname{Ab})`.
/-- Lemma 21.37.5: let `u : \mathcal C \to \mathcal D` be a continuous and cocontinuous functor
of sites, let `g : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)` be the associated
morphism of topoi, and let `\mathcal O_\mathcal C = g^{-1}\mathcal O_\mathcal D`. Then for
`U : \mathcal C` and `M : D(\mathcal O_\mathcal D)`, the derived sections of the inverse-image
complex `g^* M = g^{-1} M` over `U`, viewed in `D(\operatorname{Ab})`, are canonically
isomorphic to the derived sections of `M` over `u(U)`. This is the statement-stage form of the
textbook formula `R\Gamma(U, g^* M) = R\Gamma(u(U), M)`. -/
theorem moduleInverseImageDerived_sectionsOverObject_isomorphic
    (U : C)
    [(sourceModuleSectionsAsAbelianFunctor JC JD u 𝒪D U).Additive]
    [(targetModuleSectionsAsAbelianFunctor 𝒪D (u.obj U)).Additive]
    (M : DerivedCategory (TargetModuleCat 𝒪D)) :
    IsIsomorphic
      ((sourceModuleSectionsAsAbelianDerived JC JD u 𝒪D U).obj
        ((moduleInverseImageDerived JC JD u 𝒪D).obj M))
      ((targetModuleSectionsAsAbelianDerived 𝒪D (u.obj U)).obj M) := sorry

end

end

end CategoryTheory
