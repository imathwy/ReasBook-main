import Mathlib
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap18.Definition_18_7_1
import StacksProject_2024.Chap21.Definition_21_13_4
import StacksProject_2024.Chap21.Lemma_21_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Sheaf
open Opposite
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

/-- The functor sending an `\mathcal O`-module sheaf on a ringed topos presentation `X` to its
sections over the object `U`, viewed as an abelian-group-valued functor. -/
abbrev ringedToposModuleSectionsOverObjectFunctor
    (X : _root_.RingedSite.{u, v}) (U : X) :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{v} ⋙
    (CategoryTheory.evaluation Xᵒᵖ AddCommGrpCat.{v}).obj (op U)

/-- The functor sending an `\mathcal O`-module sheaf on a ringed topos presentation `X` to its
sections over a sheaf of sets `K` on the underlying topos. -/
abbrev ringedToposModuleSectionsOnSheafFunctor
    (X : _root_.RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{v}]
    [HasSheafify X.siteTopology AddCommGrpCat.{v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (K : Sheaf X.siteTopology (Type v))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (localizationTopology K) AddCommGrpCat.{v})] :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    localizationInverseImage K ⋙
    Sheaf.Γ (localizationTopology K) AddCommGrpCat.{v}

section

variable (X : _root_.RingedSite.{u, v})
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{v}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [HasExt.{w} (Sheaf X.siteTopology AddCommGrpCat.{v})]

-- Proof sketch: identify the higher right-derived functors of sections over `K` with the positive
-- cohomology groups `H^p(K, (SheafOfModules.toSheaf X.structureSheaf).obj ℱ)`, and then apply the
-- defining vanishing built into `IsTotallyAcyclicOne`.
/-- Lemma 21.14.3: if the underlying abelian sheaf of an `\mathcal O`-module sheaf on a
ringed topos presentation `X` is totally acyclic, then the module sheaf is right acyclic for the
sections functor over any sheaf of sets `K` on `X`. -/
theorem totallyAcyclicModule_isRightAcyclicForSectionsOnSheaf
    (K : Sheaf X.siteTopology (Type v))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (localizationTopology K) AddCommGrpCat.{v})]
    [Functor.Additive (ringedToposModuleSectionsOnSheafFunctor X K)]
    [((mapHomotopyCategoryToDerived (ringedToposModuleSectionsOnSheafFunctor X K)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (up ℤ)))]
    (ℱ : SheafOfModules X.structureSheaf)
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)] :
    IsRightAcyclicForAdditiveFunctor (ringedToposModuleSectionsOnSheafFunctor X K) ℱ := sorry

-- Proof sketch: the higher right-derived functors of sections over `U` compute the groups
-- `H^p(U, (SheafOfModules.toSheaf X.structureSheaf).obj ℱ)`, so total acyclicity forces them to
-- vanish in positive degree.
/-- A totally acyclic `\mathcal O`-module sheaf on a ringed topos presentation `X` is right
acyclic for the functor `H^0(U, -)` for every object `U` of the underlying site. -/
theorem totallyAcyclicModule_isRightAcyclicForSectionsOverObject
    (U : X) (ℱ : SheafOfModules X.structureSheaf)
    [((mapHomotopyCategoryToDerived (ringedToposModuleSectionsOverObjectFunctor X U)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (up ℤ)))]
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)] :
    IsRightAcyclicForAdditiveFunctor (ringedToposModuleSectionsOverObjectFunctor X U) ℱ := sorry

-- Proof sketch: take `K` to be a terminal sheaf of sets on `X`; sections over such a `K`
-- identify with global sections on the underlying topos, so the previous acyclicity statement
-- specializes to `Γ(X, -)`.
/-- If `K` is a terminal sheaf of sets on the underlying topos of `X`, then a totally acyclic
`\mathcal O`-module sheaf on `X` is right acyclic for global sections. -/
theorem totallyAcyclicModule_isRightAcyclicForGlobalSections
    (K : Sheaf X.siteTopology (Type v)) (_hK : Limits.IsTerminal K)
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (localizationTopology K) AddCommGrpCat.{v})]
    [Functor.Additive (ringedToposModuleSectionsOnSheafFunctor X K)]
    [((mapHomotopyCategoryToDerived (ringedToposModuleSectionsOnSheafFunctor X K)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (up ℤ)))]
    (ℱ : SheafOfModules X.structureSheaf)
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)] :
    IsRightAcyclicForAdditiveFunctor (ringedToposModuleSectionsOnSheafFunctor X K) ℱ := sorry

end

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasWeakSheafify JC AddCommGrpCat.{v}] [HasSheafify JC AddCommGrpCat.{v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasExt.{w} (Sheaf JC AddCommGrpCat.{v})]
variable [HasSheafify JD AddCommGrpCat.{v}] [JD.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable {𝒪C : Sheaf JC RingCat.{v}} {𝒪D : Sheaf JD RingCat.{v}}
variable (fSharp : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{v} JD JC).obj 𝒪C)

-- Proof sketch: by Lemma `18.7.2`, any morphism of ringed topoi may be presented by a morphism
-- of sites, and in that setting the higher direct images are computed by sectionwise cohomology.
-- Total acyclicity kills those positive cohomology groups, so the positive right-derived
-- pushforwards vanish.
/-- In the site-presented form of a morphism of ringed topoi, a totally acyclic `\mathcal O`-module
sheaf is right acyclic for direct image. -/
theorem totallyAcyclicModule_isRightAcyclicForPushforward
    (ℱ : SheafOfModules 𝒪C)
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf 𝒪C).obj ℱ)]
    [Functor.Additive (SheafOfModules.pushforward fSharp)]
    [((mapHomotopyCategoryToDerived (SheafOfModules.pushforward fSharp)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules 𝒪C) (up ℤ)))] :
    IsRightAcyclicForAdditiveFunctor (SheafOfModules.pushforward fSharp) ℱ := sorry

end

end CategoryTheory
