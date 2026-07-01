import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The lattice of open subsets of a ringed space has a top element. -/
instance opensOrderTop (X : RingedSpace.{u}) : OrderTop (Opens X.carrier) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The degree-`p` Čech cohomology functor on `\mathcal O_X`-modules for an indexed family of
opens `\mathcal U`. -/
private noncomputable abbrev ringedSpaceModuleCechCohomologyFunctor
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier) (p : ℕ) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤ AddCommGrpCat.{u} :=
  letI : HasFiniteLimits (Opens X.carrier) :=
    hasFiniteLimits_of_semilatticeInf_orderTop
  letI : HasFiniteProducts (Opens X.carrier) := inferInstance
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    CategoryTheory.cechComplexFunctor 𝒰 ⋙
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p)

/-- The degree-`p` sheaf cohomology functor on `\mathcal O_X`-modules over a fixed open
subset `U`. -/
private noncomputable abbrev ringedSpaceModuleCohomologyAtOpenFunctor
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (p : ℕ) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p ⋙
    (CategoryTheory.evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The degree-`p` Čech cohomology group of an `\mathcal O_X`-module for the indexed family of
opens `\mathcal U`. -/
private noncomputable abbrev ringedSpaceModuleCechCohomology
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) (p : ℕ) : AddCommGrpCat.{u} :=
  (ringedSpaceModuleCechCohomologyFunctor 𝒰 p).obj ℱ

/-- The degree-`p` sheaf cohomology group of an `\mathcal O_X`-module over the open subset `U`. -/
private noncomputable abbrev ringedSpaceModuleCohomologyAtOpen
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) (p : ℕ) :
    AddCommGrpCat.{u} :=
  (ringedSpaceModuleCohomologyAtOpenFunctor X U p).obj ℱ

-- Proof sketch: choose an injective resolution `ℱ ⟶ ℐ•`, form the double complex
-- `\check{\mathcal C}^•(\mathcal U, \mathcal I^•)`, and compare both `\Gamma(U, \mathcal I^•)`
-- and `\check{\mathcal C}^•(\mathcal U, \mathcal F)` with its total complex. Lemma `20.11.1`
-- identifies each row with a resolution of the corresponding section group, so Lemma `12.25.4`
-- makes the rowwise comparison a quasi-isomorphism. Passing to cohomology yields a natural
-- transformation `\check H^p(\mathcal U, -) → H^p(U, -)`.
/-- Lemma 20.11.2: if `\mathcal U : U = \bigcup_{i \in I} U_i` is an open covering of `U` in a
ringed space `X`, then for every degree `p` there is a natural transformation from the degree-`p`
Čech cohomology functor `\check H^p(\mathcal U, -)` on `\mathcal O_X`-modules to the degree-`p`
sheaf cohomology functor `H^p(U, -)`. -/
theorem cech_cohomology_to_sheaf_cohomology_natTrans
    {X : RingedSpace.{u}} {ι : Type u}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier) (p : ℕ) :
    iSup 𝒰 = U →
      Nonempty (ringedSpaceModuleCechCohomologyFunctor 𝒰 p ⟶
        ringedSpaceModuleCohomologyAtOpenFunctor X U p) := sorry

-- Proof sketch: evaluate the natural transformation of the previous theorem at the fixed
-- `\mathcal O_X`-module `\mathcal F`; the resulting component is the canonical comparison map from
-- the `p`th Čech cohomology group of the cover to the `p`th sheaf cohomology group on `U`.
/-- The comparison map from Čech cohomology to sheaf cohomology for a fixed
`\mathcal O_X`-module. -/
theorem cech_cohomology_to_sheaf_cohomology_map
    {X : RingedSpace.{u}} {ι : Type u}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier) (p : ℕ)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    iSup 𝒰 = U →
      Nonempty (ringedSpaceModuleCechCohomology 𝒰 ℱ p ⟶
        ringedSpaceModuleCohomologyAtOpen U ℱ p) := sorry

end AlgebraicGeometry.RingedSpace
