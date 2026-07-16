import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksProject_2024.stacks_project.Chap13.Definition_13_15_3
import StacksProject_2024.stacks_project.Chap19.AdditiveFunctorTotalRightDerived
import StacksProject_2024.stacks_project.Chap21.SiteAbelianSheaf

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- The sections functor `Γ(U, -)` on abelian sheaves over a site. -/
abbrev siteAbelianSectionsFunctor (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}] :
    Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  (sheafSections J AddCommGrpCat.{w}).obj (op U)

instance siteAbelianSectionsFunctor_additive (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}] :
    (siteAbelianSectionsFunctor J U).Additive := by
  simpa [siteAbelianSectionsFunctor, sheafSections] using
    (show
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)).Additive from
      inferInstance)

instance siteAbelianSectionsFunctor_preservesFiniteLimits
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}] :
    PreservesFiniteLimits (siteAbelianSectionsFunctor J U) := by
  simpa [siteAbelianSectionsFunctor, sheafSections] using
    (inferInstance :
      PreservesFiniteLimits
        (sheafToPresheaf J AddCommGrpCat.{w} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)))

namespace Sheaf

/-- Evaluating the degree-`p` right derived functor of the inclusion
`sheafToPresheaf J AddCommGrpCat` at `U` identifies it with the degree-`p` homology of the
sections complex `Γ(U, I^•)` of an injective resolution `I` of `F`. -/
noncomputable def rightDerivedInclusion_app_obj_iso_homology_sections_complex
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) (U : C) (p : ℕ) :
    ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).obj (op U)) ≅
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p).obj
        (((siteAbelianSectionsFunctor J U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  let K :
      HomologicalComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℕ) :=
    (((sheafToPresheaf J AddCommGrpCat.{max u v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
  let evalU := (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
  let eDerived :
      ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).obj (op U)) ≅
        (evalU.obj
          ((HomologicalComplex.homologyFunctor
            (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℕ) p).obj K)) :=
    evalU.mapIso (I.isoRightDerivedObj (sheafToPresheaf J AddCommGrpCat.{max u v}) p)
  let eHomology :
      (evalU.obj
          ((HomologicalComplex.homologyFunctor
            (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℕ) p).obj K)) ≅
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p).obj
          ((evalU.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) := by
    exact
      (evalU.mapIso
        ((HomologicalComplex.homologyFunctorIso
          (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℕ) p).app K)) ≪≫
        ((K.sc p).mapHomologyIso evalU).symm ≪≫
          ((HomologicalComplex.homologyFunctorIso
            AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p).app
            ((evalU.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).symm
  simpa [K, evalU, siteAbelianSectionsFunctor, sheafSections] using eDerived.trans eHomology

end Sheaf

/-- The chosen unbounded derived sections functor `RΓ(U, -)` on abelian sheaves over a site. -/
abbrev siteAbelianSectionsDerived (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf J AddCommGrpCat.{w})] :
    DerivedCategory (Sheaf J AddCommGrpCat.{w}) ⥤
      DerivedCategory AddCommGrpCat.{w} :=
  let F : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} := siteAbelianSectionsFunctor J U
  letI : F.Additive := by
    simpa [F] using (siteAbelianSectionsFunctor_additive (J := J) (U := U))
  letI :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        (HomologicalComplex.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ)) :=
    mapHomologicalComplexQ_hasRightDerivedFunctor F
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ))

/-- The bounded-below derived sections functor `RΓ(U, -)` on abelian sheaves over a site,
valued in `D⁺(AddCommGrpCat)`. -/
abbrev siteAbelianSectionsBoundedBelowDerived (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (siteAbelianSectionsFunctor J U))
      (boundedBelowHomotopyQuasiIso (Sheaf J AddCommGrpCat.{w}))] :
    D⁺((Sheaf J AddCommGrpCat.{w})) ⥤ D⁺(AddCommGrpCat.{w}) :=
  let F : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} := siteAbelianSectionsFunctor J U
  let _ : F.Additive := siteAbelianSectionsFunctor_additive (J := J) (U := U)
  let _ :
      Functor.HasRightDerivedFunctor
        (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
        (boundedBelowHomotopyQuasiIso (Sheaf J AddCommGrpCat.{w})) := by
    simpa [F] using
      (inferInstance :
        Functor.HasRightDerivedFunctor
          (mapBoundedBelowHomotopyCategoryToDerivedBelow (siteAbelianSectionsFunctor J U))
          (boundedBelowHomotopyQuasiIso (Sheaf J AddCommGrpCat.{w})))
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F)
    (mapBoundedBelowHomotopyToDerivedBelow :
      K⁺((Sheaf J AddCommGrpCat.{w})) ⥤ D⁺((Sheaf J AddCommGrpCat.{w})))
    (boundedBelowHomotopyQuasiIso (Sheaf J AddCommGrpCat.{w}))

/-- The bounded-below derived sections target `F ↦ RΓ(U, F[0])` on abelian sheaves. -/
abbrev sheafToBoundedBelowDerivedSectionsFunctor (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (siteAbelianSectionsFunctor J U))
      (boundedBelowHomotopyQuasiIso (Sheaf J AddCommGrpCat.{w}))] :
    Sheaf J AddCommGrpCat.{w} ⥤ D⁺(AddCommGrpCat.{w}) :=
  single0ToDplus (Sheaf J AddCommGrpCat.{w}) ⋙ siteAbelianSectionsBoundedBelowDerived J U

namespace SiteAbelianSectionsDerived

@[inherit_doc CategoryTheory.siteAbelianSectionsDerived]
scoped[GrothendieckTopologyDerivedSections] notation3:max "RΓ[" J "](" U ")" =>
  CategoryTheory.siteAbelianSectionsDerived J U

end SiteAbelianSectionsDerived

open scoped GrothendieckTopologyDerivedSections

/-- The chosen unbounded derived inverse-image functor on abelian sheaves attached to a
continuous and cocontinuous functor of sites. -/
abbrev siteAbelianInverseImageDerived
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) (u : C ⥤ D)
    [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [HasSheafify JC AddCommGrpCat.{max u v}]
    [HasSheafify JD AddCommGrpCat.{max u v}]
    [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD)]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat JD)] :
    DerivedCategory (Sheaf JD AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf JC AddCommGrpCat.{max u v}) :=
  let F : SiteAbelianSheafCat JD ⥤ SiteAbelianSheafCat JC :=
    u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD
  let _ : F.Additive := by
    simpa [F] using
      (inferInstance :
        Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD))
  letI :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        (HomologicalComplex.quasiIso (SiteAbelianSheafCat JD) (ComplexShape.up ℤ)) :=
    mapHomologicalComplexQ_hasRightDerivedFunctor F
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (SiteAbelianSheafCat JD) (ComplexShape.up ℤ))

end

end CategoryTheory
