import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

/- Domain-style sampling for the generic Čech owner used below:
- primary domain: presheaves of modules on a ringed site, restriction to the slice category
  `Over U`, and the canonical Čech cochain-complex functor;
- sampled owner declarations:
  `PresheafOfModules`,
  `PresheafOfModules.pushforward₀`,
  `PresheafOfModules.forgetToPresheafModuleCat`,
  `CategoryTheory.cechComplexFunctor`;
- best owner abstraction: the intrinsic owner is the ringed-site functor built from a sheaf of
  rings `𝒪` and an object `U`, with the ringed-space construction only a specialization to
  `X.ringCatSheaf`.

Source/core/bridge triage:
- `source-facing`: the later ringed-space specialization `ringedSpaceModuleCechComplexFunctor`;
- `core/canonical`: `ringedSiteModuleSectionsOnOverPresheaf`,
  `ringedSiteModuleCechComplexFunctor`, and `ringedSiteModuleCechCohomology`;
- `bridge/view`: the opens-site specialization from `X.ringCatSheaf` to the ringed-space owner.
-/

private abbrev overMkIdInitial
    {C : Type u} [Category.{v} C] (U : C) :
    Limits.IsInitial (op (Over.mk (𝟙 U))) :=
  Over.mkIdTerminal.op

/-- The presheaf on `Over U` of `𝒪(U)`-modules obtained from a presheaf of `𝒪`-modules by
restricting scalars along the maps `𝒪(U) ⟶ 𝒪(V)`. -/
abbrev ringedSiteModuleSectionsOnOverPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat) (U : C) :
    PresheafOfModules 𝒪.obj ⥤ (Over U)ᵒᵖ ⥤ ModuleCat (𝒪.obj.obj (op U)) :=
  PresheafOfModules.pushforward₀ (Over.forget U) 𝒪.obj ⋙
    PresheafOfModules.forgetToPresheafModuleCat
      (op (Over.mk (𝟙 U))) (overMkIdInitial U)

private abbrev moduleCatHasProducts {R : Type u} [Ring R] :
    HasProducts.{u} (ModuleCat.{u} R) := by
  let _ : HasLimits (ModuleCat.{u} R) := ModuleCat.hasLimits'
  infer_instance

/-- The Čech complex of a presheaf of `𝒪`-modules with respect to a covering family
`family : ι → Over U`, computed in `ModuleCat (𝒪(U))`. -/
abbrev ringedSiteModuleCechComplexFunctor
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U) :
    PresheafOfModules 𝒪.obj ⥤
      CochainComplex (ModuleCat.{w} (𝒪.obj.obj (op U))) ℕ :=
  let ModU := ModuleCat.{w} (𝒪.obj.obj (op U))
  let _ : HasProducts.{w} ModU := moduleCatHasProducts
  ringedSiteModuleSectionsOnOverPresheaf 𝒪 U ⋙ cechComplexFunctor family

/-- The degree-`p` Čech cohomology of a presheaf of `𝒪`-modules on a ringed site, viewed as an
`𝒪(U)`-module. -/
abbrev ringedSiteModuleCechCohomology
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U)
    (M : PresheafOfModules 𝒪.obj) (p : ℕ) :
    ModuleCat.{w} (𝒪.obj.obj (op U)) :=
  (HomologicalComplex.homologyFunctor
      (ModuleCat.{w} (𝒪.obj.obj (op U))) (ComplexShape.up ℕ) p).obj
    ((ringedSiteModuleCechComplexFunctor 𝒪 U family).obj M)

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for 20.10.0.1:
- primary domain: presheaves of `𝒪_X`-modules on a ringed space, restriction to the slice
  category `Over U`, and the canonical Čech cochain-complex functor;
- sampled owner declarations:
  `CategoryTheory.ringedSiteModuleSectionsOnOverPresheaf`,
  `CategoryTheory.ringedSiteModuleCechComplexFunctor`,
  `RingedSpace.PresheafModules`,
  `RingedSpace.ringCatSheaf`;
- best owner abstraction: the intrinsic owner is the generic ringed-site Čech functor
  `CategoryTheory.ringedSiteModuleCechComplexFunctor`; the ringed-space construction is only its
  opens-site specialization through `X.ringCatSheaf`.

Source/core/bridge triage:
- `source-facing`: the resulting Čech complex functor for presheaf `𝒪_X`-modules;
- `core/canonical`: `CategoryTheory.ringedSiteModuleSectionsOnOverPresheaf` and
  `CategoryTheory.ringedSiteModuleCechComplexFunctor`;
- `bridge/view`: the specialization from the ringed-site owner `X.ringCatSheaf` on
  `Opens.grothendieckTopology X` to the ringed-space owner below.

This file should therefore reuse the generic ringed-site owner directly and keep only the
ringed-space specialization source-facing. -/

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

/-- The presheaf on `Over U` of `𝒪_X(U)`-modules obtained from a presheaf of `𝒪_X`-modules by
restriction of scalars. -/
abbrev ringedSpaceModuleSectionsOnOverPresheaf :
    RingedSpace.PresheafModules X ⥤
      (Over U)ᵒᵖ ⥤ ModuleCat.{u} (X.presheaf.obj (op U)) :=
  CategoryTheory.ringedSiteModuleSectionsOnOverPresheaf (RingedSpace.ringCatSheaf X) U

@[simp] theorem ringedSpaceModuleSectionsOnOverPresheaf_eq :
    ringedSpaceModuleSectionsOnOverPresheaf U =
      CategoryTheory.ringedSiteModuleSectionsOnOverPresheaf (RingedSpace.ringCatSheaf X) U :=
  rfl

variable {ι : Type u} [HasFiniteProducts (Over U)]

/-- 20.10.0.1: for an indexed family of objects of `Over U`, the Čech construction defines a
functor from presheaves of `𝒪_X`-modules to bounded-below cochain complexes of
`𝒪_X(U)`-modules. This is obtained by viewing a presheaf module as a presheaf of
`𝒪_X(U)`-modules on `Over U` via restriction of scalars, then applying the generic ringed-site
Čech complex functor to the opens site of `X`; equivalently, it is the direct specialization of
`ringedSiteModuleCechComplexFunctor` along `X.ringCatSheaf`. -/
@[stacks 01EI]
abbrev ringedSpaceModuleCechComplexFunctor (𝒰 : ι → Over U) :
    RingedSpace.PresheafModules X ⥤
      CochainComplex (ModuleCat.{u} (X.presheaf.obj (op U))) ℕ :=
  ringedSiteModuleCechComplexFunctor (RingedSpace.ringCatSheaf X) U 𝒰

@[simp] theorem ringedSpaceModuleCechComplexFunctor_eq (𝒰 : ι → Over U) :
    ringedSpaceModuleCechComplexFunctor U 𝒰 =
      CategoryTheory.ringedSiteModuleCechComplexFunctor (RingedSpace.ringCatSheaf X) U 𝒰 :=
  rfl

/-- The degree-`p` Čech cohomology of a presheaf of `𝒪_X`-modules for the family `𝒰`, viewed as
an `𝒪_X(U)`-module. -/
abbrev ringedSpaceModuleCechCohomology (𝒰 : ι → Over U)
    (M : RingedSpace.PresheafModules X) (p : ℕ) :
    ModuleCat.{u} (X.presheaf.obj (op U)) :=
  CategoryTheory.ringedSiteModuleCechCohomology (RingedSpace.ringCatSheaf X) U 𝒰 M p

@[simp] theorem ringedSpaceModuleCechCohomology_eq
    (𝒰 : ι → Over U) (M : RingedSpace.PresheafModules X) (p : ℕ) :
    ringedSpaceModuleCechCohomology U 𝒰 M p =
      CategoryTheory.ringedSiteModuleCechCohomology (RingedSpace.ringCatSheaf X) U 𝒰 M p :=
  rfl

end AlgebraicGeometry.RingedSpace
