import StacksProject_2024.Chap24.Lemma_24_29_4

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uA vA uA' vA' uA'' vA''

-- Semantic search note: `lean_leansearch` highlighted `Adjunction.rightAdjointUniq` as the
-- canonical uniqueness-of-right-adjoints owner; the owner/API choice here was then checked
-- against the local Chapter 24 predecessors `Lemma_24_28_4` and `Lemma_24_29_4`, plus the
-- generic composition-comparison owner `Chap13/Lemma_13_14_16.lean`.

namespace DifferentialGradedModule

section

variable {DGModA : Type uA} [Category.{vA} DGModA] [Abelian DGModA]
variable [CategoryWithHomology DGModA]
variable {DGModA' : Type uA'} [Category.{vA'} DGModA'] [Abelian DGModA']
variable [CategoryWithHomology DGModA']
variable {DGModA'' : Type uA''} [Category.{vA''} DGModA''] [Abelian DGModA'']
variable [CategoryWithHomology DGModA'']

/-- Lemma 24.29.6: for composable morphisms of ringed topoi together with compatible morphisms of
differential graded algebras, suppose `fPush`, `gPush`, and `compPush` are the induced
pushforward functors on the corresponding categories of differential graded modules, with left
adjoint pullback functors `fPull`, `gPull`, and `compPull`, and suppose `compPull` agrees with
`gPull ⋙ fPull`. Then the derived pushforward for the composite is canonically isomorphic to the
composite derived pushforward `Rg_* \circ Rf_*`, written in Lean as
`Rf_* ⋙ Rg_* : D(\mathcal A, \mathrm d) ⥤ D(\mathcal A'', \mathrm d)`. -/
noncomputable abbrev derivedPushforwardCompIso
    (fPush : DGModA ⥤ DGModA')
    (gPush : DGModA' ⥤ DGModA'')
    (compPush : DGModA ⥤ DGModA'')
    (fPull : DGModA' ⥤ DGModA)
    (gPull : DGModA'' ⥤ DGModA')
    (compPull : DGModA'' ⥤ DGModA)
    [fPush.Additive] [gPush.Additive] [compPush.Additive]
    [fPull.Additive] [gPull.Additive] [compPull.Additive]
    (hAdjf : fPull ⊣ fPush)
    (hAdjg : gPull ⊣ gPush)
    (hAdjcomp : compPull ⊣ compPush)
    (hcomp : compPull ≅ gPull ⋙ fPull)
    [Functor.HasLeftDerivedFunctor
      (pullbackToDerived fPull) (HomotopyCategory.quasiIso DGModA' (up ℤ))]
    [Functor.HasLeftDerivedFunctor
      (pullbackToDerived gPull) (HomotopyCategory.quasiIso DGModA'' (up ℤ))]
    [Functor.HasLeftDerivedFunctor
      (pullbackToDerived compPull) (HomotopyCategory.quasiIso DGModA'' (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (fPush.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (gPush.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA' (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (compPush.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))] :
    derivedPushforward fPush ⋙ derivedPushforward gPush ≅
      derivedPushforward compPush := sorry

/-- The forward and inverse natural transformations of `derivedPushforwardCompIso` compose to the
identity on the composite derived pushforward functor. -/
theorem derivedPushforwardCompIso_hom_inv_id
    (fPush : DGModA ⥤ DGModA')
    (gPush : DGModA' ⥤ DGModA'')
    (compPush : DGModA ⥤ DGModA'')
    (fPull : DGModA' ⥤ DGModA)
    (gPull : DGModA'' ⥤ DGModA')
    (compPull : DGModA'' ⥤ DGModA)
    [fPush.Additive] [gPush.Additive] [compPush.Additive]
    [fPull.Additive] [gPull.Additive] [compPull.Additive]
    (hAdjf : fPull ⊣ fPush)
    (hAdjg : gPull ⊣ gPush)
    (hAdjcomp : compPull ⊣ compPush)
    (hcomp : compPull ≅ gPull ⋙ fPull)
    [Functor.HasLeftDerivedFunctor
      (pullbackToDerived fPull) (HomotopyCategory.quasiIso DGModA' (up ℤ))]
    [Functor.HasLeftDerivedFunctor
      (pullbackToDerived gPull) (HomotopyCategory.quasiIso DGModA'' (up ℤ))]
    [Functor.HasLeftDerivedFunctor
      (pullbackToDerived compPull) (HomotopyCategory.quasiIso DGModA'' (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (fPush.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (gPush.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA' (up ℤ))]
    [Functor.HasRightDerivedFunctor
      (compPush.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso DGModA (up ℤ))] :
    (derivedPushforwardCompIso
          fPush gPush compPush fPull gPull compPull hAdjf hAdjg hAdjcomp hcomp).hom ≫
        (derivedPushforwardCompIso
          fPush gPush compPush fPull gPull compPull hAdjf hAdjg hAdjcomp hcomp).inv =
      𝟙 (derivedPushforward fPush ⋙ derivedPushforward gPush) := sorry

end

end DifferentialGradedModule
