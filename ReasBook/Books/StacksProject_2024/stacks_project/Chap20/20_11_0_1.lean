import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Lattice
import StacksProject_2024.stacks_project.Chap06.ClosedSubsetInclusion
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_14_2
import StacksProject_2024.stacks_project.Chap20.«20_9_0_1»
import StacksProject_2024.stacks_project.Chap20.OpensInstances

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for 20.11.0.1:
- primary domain: `\mathcal O_X`-modules on a ringed space, their underlying additive
  sheaf/presheaf bridges, and the associated Čech cohomology owner;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.toSheaf`,
  `SheafOfModules.forget`,
  `PresheafOfModules.toPresheaf`,
  `cechComplexFunctor`,
  `(inferInstance : HasFiniteProducts (Opens X.carrier))`;
- best owner abstraction: the public owners here should be the canonical underlying additive sheaf,
  the corresponding additive presheaf, and the resulting additive-group-valued Čech cohomology
  object;
- primitive data: a ringed space `X`, an `\mathcal O_X`-module `ℱ : RingedSpace.Modules X`, a
  family of opens `𝒰`, and a degree `p`;
- derived API: later vanishing predicates, comparison maps, and cohomology theorems built from
  these owners.

Source/core/bridge triage:
- `source-facing`: the ringed-space owners `moduleUnderlyingSheaf`, `moduleUnderlyingPresheaf`, and
  `moduleCechCohomology`;
- `core/canonical`: `SheafOfModules.toSheaf`, `SheafOfModules.forget`,
  `PresheafOfModules.toPresheaf`, `cechComplexFunctor`, and the canonical finite-product instance
  on `Opens X.carrier`;
- `bridge/view`: forgetting the module structure first to additive sheaves and then to additive
  presheaves.
-/

/-- The forgetful functor from `\mathcal O_X`-modules to sheaves of abelian groups. -/
abbrev moduleUnderlyingSheaf (X : RingedSpace.{u}) :
    RingedSpace.Modules X ⥤ X.carrier.Sheaf AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)

/-- The forgetful functor from `\mathcal O_X|_Z`-modules on a closed subset to sheaves of
abelian groups on `Z`. -/
abbrev closedSubsetModuleUnderlyingSheaf (X : RingedSpace.{u}) (Z : Set X) :
    SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u}
          (TopCat.closedSubsetInclusion (X : TopCat) Z)).obj (RingedSpace.ringCatSheaf X)) ⥤
      (TopCat.of Z).Sheaf AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf
    ((TopCat.Sheaf.pullback RingCat.{u}
      (TopCat.closedSubsetInclusion (X : TopCat) Z)).obj (RingedSpace.ringCatSheaf X))

/-- The forgetful functor from `\mathcal O_X`-modules to sheaves of abelian groups is additive. -/
instance moduleUnderlyingSheaf_additive (X : RingedSpace.{u}) :
    (moduleUnderlyingSheaf X).Additive := by
  change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).Additive
  infer_instance

/-- The forgetful functor from `\mathcal O_X|_Z`-modules to sheaves of abelian groups is
additive. -/
instance closedSubsetModuleUnderlyingSheaf_additive (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetModuleUnderlyingSheaf X Z).Additive := by
  change
    (SheafOfModules.toSheaf
      ((TopCat.Sheaf.pullback RingCat.{u}
        (TopCat.closedSubsetInclusion (X : TopCat) Z)).obj (RingedSpace.ringCatSheaf X))).Additive
  infer_instance

/-- The forgetful functor from `\mathcal O_X`-modules to sheaves of abelian groups is faithful. -/
instance moduleUnderlyingSheaf_faithful (X : RingedSpace.{u}) :
    (moduleUnderlyingSheaf X).Faithful := by
  change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).Faithful
  infer_instance

/-- The forgetful functor from `\mathcal O_X|_Z`-modules to sheaves of abelian groups is
faithful. -/
instance closedSubsetModuleUnderlyingSheaf_faithful (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetModuleUnderlyingSheaf X Z).Faithful := by
  change
    (SheafOfModules.toSheaf
      ((TopCat.Sheaf.pullback RingCat.{u}
        (TopCat.closedSubsetInclusion (X : TopCat) Z)).obj (RingedSpace.ringCatSheaf X))).Faithful
  infer_instance

/-- The forgetful functor from `\mathcal O_X`-modules to sheaves of abelian groups preserves
finite limits. -/
instance moduleUnderlyingSheaf_preservesFiniteLimits (X : RingedSpace.{u}) :
    PreservesFiniteLimits (moduleUnderlyingSheaf X) := by
  change PreservesFiniteLimits (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))
  infer_instance

/-- The forgetful functor from `\mathcal O_X|_Z`-modules to sheaves of abelian groups preserves
finite limits. -/
instance closedSubsetModuleUnderlyingSheaf_preservesFiniteLimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteLimits (closedSubsetModuleUnderlyingSheaf X Z) := by
  change
    PreservesFiniteLimits
      (SheafOfModules.toSheaf
        ((TopCat.Sheaf.pullback RingCat.{u}
          (TopCat.closedSubsetInclusion (X : TopCat) Z)).obj (RingedSpace.ringCatSheaf X)))
  infer_instance

/-- The forgetful functor from `\mathcal O_X`-modules to sheaves of abelian groups preserves
finite colimits. -/
instance moduleUnderlyingSheaf_preservesFiniteColimits (X : RingedSpace.{u}) :
    PreservesFiniteColimits (moduleUnderlyingSheaf X) := by
  change PreservesFiniteColimits (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))
  infer_instance

/-- The forgetful functor from `\mathcal O_X|_Z`-modules to sheaves of abelian groups preserves
finite colimits. -/
instance closedSubsetModuleUnderlyingSheaf_preservesFiniteColimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteColimits (closedSubsetModuleUnderlyingSheaf X Z) := by
  change
    PreservesFiniteColimits
      (SheafOfModules.toSheaf
        ((TopCat.Sheaf.pullback RingCat.{u}
          (TopCat.closedSubsetInclusion (X : TopCat) Z)).obj (RingedSpace.ringCatSheaf X)))
  infer_instance

/-- The forgetful functor from `\mathcal O_X`-modules to additive presheaves. -/
abbrev moduleUnderlyingPresheaf (X : RingedSpace.{u}) :
    RingedSpace.Modules X ⥤ X.carrier.Presheaf AddCommGrpCat.{u} :=
  moduleUnderlyingSheaf X ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- The forgetful functor from `\mathcal O_X`-modules to additive presheaves is additive. -/
instance moduleUnderlyingPresheaf_additive (X : RingedSpace.{u}) :
    (moduleUnderlyingPresheaf X).Additive where
  map_add := by
    intro M N f g
    change
      (sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
          ((moduleUnderlyingSheaf X).map (f + g)) =
        (sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
            ((moduleUnderlyingSheaf X).map f) +
          (sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
            ((moduleUnderlyingSheaf X).map g)
    rw [(moduleUnderlyingSheaf X).map_add]
    rfl

/-- The degree-`p` Čech cohomology group of an `\mathcal O_X`-module with respect to a family of
opens `𝒰`. -/
abbrev moduleCechCohomology
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℱ : RingedSpace.Modules X) (p : ℕ) : AddCommGrpCat.{u} :=
  let _ : HasFiniteLimits (Opens X.carrier) :=
    CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_orderTop
  let _ : HasFiniteProducts (Opens X.carrier) := inferInstance
  let _ : (moduleUnderlyingPresheaf X).Additive := moduleUnderlyingPresheaf_additive X
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
    ((cechComplexFunctor 𝒰).obj ((moduleUnderlyingPresheaf X).obj ℱ))

end AlgebraicGeometry.RingedSpace
