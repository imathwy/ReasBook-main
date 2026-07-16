import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_7
import StacksProject_2024.stacks_project.Chap19.Theorem_19_12_6

open CategoryTheory
open ComplexShape

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Abelian A]
variable [Category.{v₂} B] [Abelian B]

local instance additiveFunctorDerivedSource_hasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} A :=
  HasDerivedCategory.standard A

local instance additiveFunctorDerivedTarget_hasDerivedCategory :
    HasDerivedCategory.{max u₂ v₂} B :=
  HasDerivedCategory.standard B

local notation "QhA" =>
  (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
local notation "QhB" =>
  (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B)
local notation "QA" => (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
local notation "QB" => (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B)
local notation "QisA" => HomologicalComplex.quasiIso A (up ℤ)
local notation "QishA" => HomotopyCategory.quasiIso A (up ℤ)

/- Domain-style sampling for the additive-functor total right derived owner:
- primary domain: total right derived functors on unbounded derived categories, computed through
  the homotopy-category localization by K-injective resolutions;
- sampled owner declarations:
  `Functor.totalRightDerived`,
  `DerivedCategory.Qh`,
  `hasRightDerivedFunctor_of_kInjective_resolutions`,
  `CochainComplex.exists_functorial_kInjective_resolution`;
- best owner abstraction:
  `source-facing`: the Chapter 19 existence of the canonical total right derived functor attached
    to an additive functor `F : A ⥤ B`;
  `core/canonical`: `Functor.totalRightDerived` applied to the homotopy-level functor
    `F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh`;
  `bridge/view`: the comparison morphism from the cochain-level functor
    `F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q` to the derived functor, obtained by
    whiskering the total-right-derived unit across the quotient `Qh`.

Primitive data are only the additive functor `F` and the Grothendieck-abelian source `A`. The
K-injective resolution and homotopy-to-derived passage are derived API, so the public owner stays
the functor on derived categories rather than a package of chosen replacement data. -/

private abbrev additiveFunctorHomotopyToDerived
    (F : A ⥤ B) [F.Additive] :
    HomotopyCategory A (up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (up ℤ) ⋙ QhB

private instance additiveFunctorHomotopyToDerived_hasRightDerivedFunctor
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    Functor.HasRightDerivedFunctor (additiveFunctorHomotopyToDerived F) QishA := by
  refine hasRightDerivedFunctor_of_kInjective_resolutions
      (additiveFunctorHomotopyToDerived F) ?_
  intro K
  obtain ⟨J, _, hKinj⟩ := CochainComplex.exists_functorial_kInjective_resolution A
  exact ⟨J.toFunctor.obj K, hKinj K, J.ι.app K, J.quasiIso_app K⟩

/-- The canonical total right derived functor of an additive functor between abelian categories
with Grothendieck-abelian source. The owner lives on derived categories, while the K-injective
replacement and homotopy-level localization remain internal. -/
abbrev additiveFunctorTotalRightDerived
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    DerivedCategory A ⥤ DerivedCategory B :=
  Functor.totalRightDerived (additiveFunctorHomotopyToDerived F) QhA QishA

/-- The canonical cochain-level unit for `additiveFunctorTotalRightDerived`. This compares the
naive application of `F` to a complex with the derived functor `RF` evaluated on its image in the
derived category. -/
noncomputable def additiveFunctorTotalRightDerivedUnit
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    F.mapHomologicalComplex (up ℤ) ⋙ QB ⟶
      QA ⋙ additiveFunctorTotalRightDerived F :=
  let η :
      additiveFunctorHomotopyToDerived F ⟶
        QhA ⋙ additiveFunctorTotalRightDerived F :=
    Functor.totalRightDerivedUnit (additiveFunctorHomotopyToDerived F) QhA QishA
  let eSource :
      HomotopyCategory.quotient A (up ℤ) ⋙ additiveFunctorHomotopyToDerived F ≅
        F.mapHomologicalComplex (up ℤ) ⋙ QB :=
    (Functor.associator
        (HomotopyCategory.quotient A (up ℤ))
        (F.mapHomotopyCategory (up ℤ))
        QhB).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryFactors F (up ℤ)) QhB ≪≫
      Functor.associator
        (F.mapHomologicalComplex (up ℤ))
        (HomotopyCategory.quotient B (up ℤ))
        QhB ≪≫
      Functor.isoWhiskerLeft
        (F.mapHomologicalComplex (up ℤ))
        (DerivedCategory.quotientCompQhIso B)
  eSource.inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (up ℤ)) η ≫
    (Functor.associator
      (HomotopyCategory.quotient A (up ℤ))
      QhA
      (additiveFunctorTotalRightDerived F)).hom ≫
    (Functor.isoWhiskerRight
      (DerivedCategory.quotientCompQhIso A)
      (additiveFunctorTotalRightDerived F)).hom

/-- The cochain-level functor induced by an additive functor into an abelian target admits the
canonical total right derived functor obtained by passing through the homotopy-category
localization `Qh`. -/
theorem mapHomologicalComplexQ_hasRightDerivedFunctor
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    (F.mapHomologicalComplex (up ℤ) ⋙ QB).HasRightDerivedFunctor QisA := by
  sorry

end

end CategoryTheory
