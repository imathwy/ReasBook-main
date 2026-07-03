import Mathlib
import StacksProject_2024.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of modules on a ringed space `X`. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

/-- The additive functor from `\mathcal O_X`-modules to abelian presheaves on `X`, obtained by
forgetting module structure to the underlying abelian sheaf and then forgetting the sheaf
condition. -/
abbrev ringedSpaceUnderlyingAbelianPresheafFunctor (X : RingedSpace.{u}) :
    ringedSpaceModuleCat X ⥤ (Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- The total right derived functor of the underlying-abelian-presheaf functor on a ringed space.
-/
abbrev ringedSpaceUnderlyingAbelianPresheafDerived (X : RingedSpace.{u})
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)] :
    DerivedCategory (ringedSpaceModuleCat X) ⥤
      DerivedCategory ((Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (ringedSpaceUnderlyingAbelianPresheafFunctor X)

/-- The presheaf on `X` sending an open subset `U` to the objectwise cohomology group
`H^q(U, K)` of a derived `\mathcal O_X`-module `K`. -/
abbrev ringedSpaceObjectwiseCohomologyPresheaf (X : RingedSpace.{u})
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    (Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor ((Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u}) q).obj
    ((ringedSpaceUnderlyingAbelianPresheafDerived X).obj K)

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `H^q(K)` on a ringed space
`X`. -/
abbrev ringedSpaceCohomologySheaf (X : RingedSpace.{u})
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj K)

-- Proof sketch: regard `K` as an object of the derived category of the underlying abelian
-- presheaf functor `Mod(\mathcal O_X) ⥤ PSh(X, Ab)`. Its degree-`q` homology presheaf is exactly
-- `U ↦ H^q(U, K)`, and Lemma `20.32.2` identifies this objectwise with `U ↦ H^q(U, K|_U)`.
-- Sheafifying the resulting presheaf recovers the underlying abelian sheaf of the homology object
-- `(DerivedCategory.homologyFunctor (RingedSpace.Modules X) q).obj K`, i.e. the cohomology sheaf
-- `H^q(K)`.
/-- Lemma 20.32.3: for a ringed space `(X, \mathcal O_X)`, an object `K` of `D(\mathcal O_X)`,
and an integer `q`, the sheaf associated to the presheaf `U ↦ H^q(U, K)` is canonically
isomorphic to the degree-`q` cohomology sheaf `H^q(K)`. Equivalently, by Lemma `20.32.2`, it is
the sheaf associated to `U ↦ H^q(U, K|_U)`. -/
theorem objectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    IsIsomorphic
      ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (ringedSpaceObjectwiseCohomologyPresheaf X K q))
      (ringedSpaceCohomologySheaf X K q) := sorry

end AlgebraicGeometry.RingedSpace
