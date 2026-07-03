import Mathlib
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import StacksProject_2024.Chap17.Lemma_17_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open PresheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for 20.10.0.1:
- primary domain: presheaves of `\mathcal O_X`-modules on a ringed space, restriction to the slice
  category `Over U`, and the canonical Čech cochain-complex functor;
- sampled owner declarations:
  `ringedSpaceRingCatSheaf`,
  `PresheafOfModules.pushforward₀`,
  `PresheafOfModules.forgetToPresheafModuleCat`,
  `CategoryTheory.cechComplexFunctor`;
- best owner abstraction: the ambient ring-valued owner is the chapter-level
  `(RingedSpace.ringCatSheaf X)`, and presheaf modules should be organized directly as
  `PresheafOfModules ((RingedSpace.ringCatSheaf X)).obj`; the restricted-sections functor and the
  Čech complex functor are then derived bridge API.

Source/core/bridge triage:
- `source-facing`: the restricted-sections functor on `Over U` and the resulting Čech complex
  functor for presheaf `\mathcal O_X`-modules;
- `core/canonical`: `ringedSpaceRingCatSheaf`, `PresheafOfModules.pushforward₀`,
  `PresheafOfModules.forgetToPresheafModuleCat`, and `CategoryTheory.cechComplexFunctor`;
- `bridge/view`: the short reusable vocabulary name `ringedSpacePresheafModules X` for the ambient
  category of presheaf modules on `X`.

This file should therefore reuse the chapter owner `(RingedSpace.ringCatSheaf X)` directly and avoid
the exact-interface alias `ringedSpaceRingPresheaf X`. -/

/-- The category `PMod(\mathcal O_X)` of presheaves of `\mathcal O_X`-modules on a ringed space. -/
abbrev ringedSpacePresheafModules (X : RingedSpace.{u}) :=
  PresheafOfModules ((RingedSpace.ringCatSheaf X)).obj

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

local notation "PModX" => ringedSpacePresheafModules X
local notation "ModU" => ModuleCat (X.presheaf.obj (op U))

/-- A presheaf of `\mathcal O_X`-modules yields a presheaf of `\mathcal O_X(U)`-modules on the
slice category `Over U` by restriction of scalars along the maps `\mathcal O_X(U) → \mathcal O_X(V)`. -/
noncomputable abbrev moduleSectionsOnOverPresheaf :
    PModX ⥤ (Over U)ᵒᵖ ⥤ ModU :=
  pushforward₀ (Over.forget U) ((RingedSpace.ringCatSheaf X)).obj ⋙
    forgetToPresheafModuleCat
      (op (Over.mk (𝟙 U)))
      (show Limits.IsInitial (op (Over.mk (𝟙 U))) from Over.mkIdTerminal.op)

variable {ι : Type u} [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat (X.presheaf.obj (op U)))]

/-- 20.10.0.1: for an indexed family of objects of `Over U`, the Čech construction defines a
functor from presheaves of `\mathcal O_X`-modules to bounded-below cochain complexes of
`\mathcal O_X(U)`-modules. This is obtained by viewing a presheaf module as a presheaf of
`\mathcal O_X(U)`-modules on `Over U` via restriction of scalars, then applying the canonical
mathlib Čech complex functor. -/
noncomputable abbrev ringedSpaceModuleCechComplexFunctor (𝒰 : ι → Over U) :
    PModX ⥤ CochainComplex ModU ℕ :=
  moduleSectionsOnOverPresheaf U ⋙ cechComplexFunctor 𝒰

end AlgebraicGeometry.RingedSpace
