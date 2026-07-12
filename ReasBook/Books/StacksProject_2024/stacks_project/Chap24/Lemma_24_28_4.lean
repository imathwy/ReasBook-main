import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap13.Lemma_13_14_16_Homotopy

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uA vA uA' vA' uA'' vA''

-- Semantic search note: `lean_leansearch` was unavailable in this runner; the owner/API choice
-- was checked against local derived-pullback composition files `Lemma_20_27_2` and
-- `Lemma_21_19_2`.

namespace DifferentialGradedModule

section

variable {DGModA : Type uA} [Category.{vA} DGModA] [Abelian DGModA]
variable [CategoryWithHomology DGModA]
variable {DGModA' : Type uA'} [Category.{vA'} DGModA'] [Abelian DGModA']
variable [CategoryWithHomology DGModA']
variable {DGModA'' : Type uA''} [Category.{vA''} DGModA''] [Abelian DGModA'']
variable [CategoryWithHomology DGModA'']

local notation "KDGModA'" => HomotopyCategory DGModA' (up ℤ)
local notation "KDGModA''" => HomotopyCategory DGModA'' (up ℤ)
local notation "DDGModA'" => DerivedCategory DGModA'
local notation "DDGModA''" => DerivedCategory DGModA''
local notation "QhA'" => (DerivedCategory.Qh : KDGModA' ⥤ DDGModA')
local notation "QhA''" => (DerivedCategory.Qh : KDGModA'' ⥤ DDGModA'')
local notation "QisA'" => HomotopyCategory.quasiIso DGModA' (up ℤ)
local notation "QisA''" => HomotopyCategory.quasiIso DGModA'' (up ℤ)

/-- The homotopy-category pullback-to-derived functor attached to an additive functor between
categories of differential graded modules. -/
abbrev pullbackToDerived (F : DGModA' ⥤ DGModA) [F.Additive] :
    KDGModA' ⥤ DerivedCategory DGModA :=
  F.mapHomotopyCategory (up ℤ) ⋙
    (DerivedCategory.Qh :
      HomotopyCategory DGModA (up ℤ) ⥤ DerivedCategory DGModA)

/-- The left derived pullback functor on derived categories of differential graded modules. -/
abbrev leftDerivedPullback (F : DGModA' ⥤ DGModA) [F.Additive]
    [Functor.HasLeftDerivedFunctor (pullbackToDerived F) QisA'] :
    DDGModA' ⥤ DerivedCategory DGModA :=
  (pullbackToDerived F).totalLeftDerived QhA' QisA'

/-- The canonical identification between the homotopy-to-derived pullback for a composite functor
and the composite of the corresponding homotopy pullback with the target homotopy-to-derived
pullback. -/
private noncomputable abbrev pullbackToDerivedCompIso
    (fPull : DGModA' ⥤ DGModA)
    (gPull : DGModA'' ⥤ DGModA')
    (compPull : DGModA'' ⥤ DGModA)
    [fPull.Additive] [gPull.Additive] [compPull.Additive]
    (hcomp : compPull ≅ gPull ⋙ fPull) :
    pullbackToDerived compPull ≅
      gPull.mapHomotopyCategory (up ℤ) ⋙ pullbackToDerived fPull :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso hcomp)
      (DerivedCategory.Qh :
        HomotopyCategory DGModA (up ℤ) ⥤ DerivedCategory DGModA) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso gPull fPull)
      (DerivedCategory.Qh :
        HomotopyCategory DGModA (up ℤ) ⥤ DerivedCategory DGModA) ≪≫
    Functor.associator
      (gPull.mapHomotopyCategory (up ℤ))
      (fPull.mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory DGModA (up ℤ) ⥤ DerivedCategory DGModA)

/-- The counit natural transformation exhibiting the composite of two derived pullbacks as a left
derived functor of the composite underived pullback. -/
private noncomputable abbrev leftDerivedPullbackCompCounit
    (fPull : DGModA' ⥤ DGModA)
    (gPull : DGModA'' ⥤ DGModA')
    [fPull.Additive] [gPull.Additive]
    [Functor.HasLeftDerivedFunctor (pullbackToDerived fPull) QisA']
    [Functor.HasLeftDerivedFunctor (pullbackToDerived gPull) QisA''] :
    QhA'' ⋙ (leftDerivedPullback gPull ⋙ leftDerivedPullback fPull) ⟶
      gPull.mapHomotopyCategory (up ℤ) ⋙ pullbackToDerived fPull :=
  (Functor.associator
      QhA''
      (leftDerivedPullback gPull)
      (leftDerivedPullback fPull)).inv ≫
    Functor.whiskerRight
      ((pullbackToDerived gPull).totalLeftDerivedCounit QhA'' QisA'')
      (leftDerivedPullback fPull) ≫
    (Functor.associator
      (gPull.mapHomotopyCategory (up ℤ))
      QhA'
      (leftDerivedPullback fPull)).hom ≫
    Functor.whiskerLeft
      (gPull.mapHomotopyCategory (up ℤ))
      ((pullbackToDerived fPull).totalLeftDerivedCounit QhA' QisA')

/-- The composite of two derived pullbacks is the left derived functor of the corresponding
homotopy-category composite pullback-to-derived functor. -/
theorem leftDerivedPullbackComp_isLeftDerivedFunctor
    (fPull : DGModA' ⥤ DGModA)
    (gPull : DGModA'' ⥤ DGModA')
    (compPull : DGModA'' ⥤ DGModA)
    [fPull.Additive] [gPull.Additive] [compPull.Additive]
    (hcomp : compPull ≅ gPull ⋙ fPull)
    [Functor.HasLeftDerivedFunctor (pullbackToDerived fPull) QisA']
    [Functor.HasLeftDerivedFunctor (pullbackToDerived gPull) QisA'']
    [Functor.HasLeftDerivedFunctor (pullbackToDerived compPull) QisA''] :
    (leftDerivedPullback gPull ⋙ leftDerivedPullback fPull).IsLeftDerivedFunctor
      (leftDerivedPullbackCompCounit fPull gPull)
      QisA'' := by
  sorry

/-- The canonical isomorphism from the composite of two derived pullbacks to the derived pullback
of the composite underived pullback. -/
noncomputable abbrev leftDerivedPullbackCompIso
    (fPull : DGModA' ⥤ DGModA)
    (gPull : DGModA'' ⥤ DGModA')
    (compPull : DGModA'' ⥤ DGModA)
    [fPull.Additive] [gPull.Additive] [compPull.Additive]
    (hcomp : compPull ≅ gPull ⋙ fPull)
    [Functor.HasLeftDerivedFunctor (pullbackToDerived fPull) QisA']
    [Functor.HasLeftDerivedFunctor (pullbackToDerived gPull) QisA'']
    [Functor.HasLeftDerivedFunctor (pullbackToDerived compPull) QisA''] :
    leftDerivedPullback gPull ⋙ leftDerivedPullback fPull ≅
      leftDerivedPullback compPull :=
  letI :
      (leftDerivedPullback gPull ⋙ leftDerivedPullback fPull).IsLeftDerivedFunctor
        (leftDerivedPullbackCompCounit fPull gPull)
        QisA'' :=
    leftDerivedPullbackComp_isLeftDerivedFunctor fPull gPull compPull hcomp
  Functor.leftDerivedNatIso
    (leftDerivedPullback gPull ⋙ leftDerivedPullback fPull)
    (leftDerivedPullback compPull)
    (leftDerivedPullbackCompCounit fPull gPull)
    ((pullbackToDerived compPull).totalLeftDerivedCounit QhA'' QisA'')
    QisA''
    (pullbackToDerivedCompIso fPull gPull compPull hcomp).symm

/-- Lemma 24.28.4: the canonical comparison morphism
`leftDerivedPullback gPull ⋙ leftDerivedPullback fPull ⟶ leftDerivedPullback compPull`,
namely the `hom` of `leftDerivedPullbackCompIso`, is an isomorphism. -/
@[stacks 0FTI]
theorem leftDerivedPullback_comp_isIso
    (fPull : DGModA' ⥤ DGModA)
    (gPull : DGModA'' ⥤ DGModA')
    (compPull : DGModA'' ⥤ DGModA)
    [fPull.Additive] [gPull.Additive] [compPull.Additive]
    (hcomp : compPull ≅ gPull ⋙ fPull)
    [Functor.HasLeftDerivedFunctor (pullbackToDerived fPull) QisA']
    [Functor.HasLeftDerivedFunctor (pullbackToDerived gPull) QisA'']
    [Functor.HasLeftDerivedFunctor (pullbackToDerived compPull) QisA''] :
    IsIso (leftDerivedPullbackCompIso fPull gPull compPull hcomp).hom := by
  infer_instance

end

end DifferentialGradedModule
