import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a ringed space, viewed as a sheaf of rings. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) :
    TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The underlying abelian sheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev ringedSpaceModuleUnderlyingSheaf {X : RingedSpace.{u}}
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj ℱ

/-- The functor sending a sheaf of `\mathcal O_X`-modules to its degree-`p` cohomology on the
open subset `U`. -/
private noncomputable abbrev ringedSpaceModuleCohomologyAtOpenFunctor
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (p : ℕ) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p ⋙
    (CategoryTheory.evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The canonical map from the cohomology of a product of `\mathcal O_X`-modules on `U` to the
product of the corresponding cohomology groups. -/
private noncomputable abbrev ringedSpaceModuleProductCohomologyMap
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (p : ℕ) {I : Type u}
    (ℱ : I → SheafOfModules (ringedSpaceRingCatSheaf X)) :
    (ringedSpaceModuleUnderlyingSheaf (∏ᶜ ℱ)).H' p U ⟶
      ∏ᶜ fun i ↦ (ringedSpaceModuleUnderlyingSheaf (ℱ i)).H' p U :=
  piComparison (ringedSpaceModuleCohomologyAtOpenFunctor X U p) ℱ

-- Proof sketch: degree-zero cohomology is evaluation of the underlying sheaf on `U`, and products
-- of sheaves of modules are computed objectwise on the underlying sheaves, so the relevant
-- `piComparison` map is an isomorphism.
/-- Lemma 20.11.12 (1): for a ringed space `X`, an open subset `U`, and a family of
`\mathcal O_X`-modules `(\mathcal F_i)`, the canonical map
`H^0(U, \prod_i \mathcal F_i) \to \prod_i H^0(U, \mathcal F_i)` is an isomorphism. -/
theorem ringedSpaceModuleProductCohomologyMap_isIso_degree_zero
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) {I : Type u}
    (ℱ : I → SheafOfModules (ringedSpaceRingCatSheaf X)) :
    IsIso (ringedSpaceModuleProductCohomologyMap U 0 ℱ) := sorry

-- Proof sketch: choose an open cover on which a class in `H^1(U, \prod_i \mathcal F_i)` vanishes,
-- represent it by a Čech cocycle, use injectivity of the Čech-to-cohomology map in degree `1` for
-- each factor, and identify the Čech complex of the product with the product of the Čech
-- complexes to conclude that the cocycle is zero.
/-- Lemma 20.11.12 (2): for a ringed space `X`, an open subset `U`, and a family of
`\mathcal O_X`-modules `(\mathcal F_i)`, the canonical map
`H^1(U, \prod_i \mathcal F_i) \to \prod_i H^1(U, \mathcal F_i)` is injective. -/
theorem ringedSpaceModuleProductCohomologyMap_injective_degree_one
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) {I : Type u}
    (ℱ : I → SheafOfModules (ringedSpaceRingCatSheaf X)) :
    Function.Injective (ringedSpaceModuleProductCohomologyMap U 1 ℱ) := sorry

end AlgebraicGeometry
