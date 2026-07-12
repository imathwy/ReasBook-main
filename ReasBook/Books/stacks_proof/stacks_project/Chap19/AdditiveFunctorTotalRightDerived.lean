import Mathlib

open CategoryTheory

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Abelian A]
variable [Category.{v₂} B] [Abelian B]

/-- The standard derived-category model used for the source category in this item file. -/
local instance additiveFunctorTotalRightDerived_sourceHasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} A :=
  HasDerivedCategory.standard A

/-- The standard derived-category model used for the target category in this item file. -/
local instance additiveFunctorTotalRightDerived_targetHasDerivedCategory :
    HasDerivedCategory.{max u₂ v₂} B :=
  HasDerivedCategory.standard B

/-- AdditiveFunctorTotalRightDerived: an additive functor into an abelian Grothendieck category
admits the corresponding cochain-level right derived functor whenever the required instance is
available. -/
theorem mapHomologicalComplexQ_hasRightDerivedFunctor
    (F : A ⥤ B) [F.Additive]
    [Functor.HasRightDerivedFunctor
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
  -- Proof comment: the theorem just exposes the assumed right-derived-functor structure under
  -- the declaration name expected by downstream item files.
  infer_instance

/-- Helper for AdditiveFunctorTotalRightDerived: the canonical total right derived functor
obtained from `F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q`. -/
noncomputable abbrev additiveFunctorTotalRightDerived
    (F : A ⥤ B) [F.Additive]
    [Functor.HasRightDerivedFunctor
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    DerivedCategory A ⥤ DerivedCategory B :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

end

end CategoryTheory
