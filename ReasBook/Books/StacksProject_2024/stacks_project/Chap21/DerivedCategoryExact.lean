import Mathlib

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-- An exact additive functor carries the degree-`q` homology of a derived object to the
degree-`q` homology of its exact derived-category image. -/
noncomputable def exactFunctor_homology_iso_mapDerivedCategory
    {A : Type u} {B : Type v}
    [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory A) (q : ℤ) :
    F.obj ((DerivedCategory.homologyFunctor A q).obj K) ≅
      (DerivedCategory.homologyFunctor B q).obj (F.mapDerivedCategory.obj K) := by
  let I := DerivedCategory.Q.objPreimage K
  let FI := ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  let eSource :
      ((DerivedCategory.homologyFunctor A q).obj K) ≅ I.homology q := by
    exact
      ((DerivedCategory.homologyFunctor A q).mapIso
        (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors A q).app I
  let eTarget :
      (DerivedCategory.homologyFunctor B q).obj (F.mapDerivedCategory.obj K) ≅ FI.homology q := by
    exact
      (DerivedCategory.homologyFunctor B q).mapIso
          ((F.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctor B q).mapIso (F.mapDerivedCategoryFactors.app I) ≪≫
        (DerivedCategory.homologyFunctorFactors B q).app FI
  let eMap : FI.homology q ≅ F.obj (I.homology q) :=
    (I.sc q).mapHomologyIso F
  exact (F.mapIso eSource) ≪≫ eMap.symm ≪≫ eTarget.symm

end CategoryTheory
