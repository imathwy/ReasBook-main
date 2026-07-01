import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap18.Lemma_18_23_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.9.2:
- primary domain: finite-type sheaves of modules on ringed spaces and their behavior under the
  canonical pullback functor;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.RingedSite.pullback_isFiniteType`;
- best owner abstraction: the Chapter 18 owner theorem
  `SheafOfModules.RingedSite.pullback_isFiniteType`, specialized to the ringed-space pullback
  owner `RingedSpace.Hom.pullback`, with the source-facing bridge theorem living naturally in the
  `RingedSpace.Hom` namespace and the owner predicate `SheafOfModules.IsFiniteType` on
  `Y.Modules`;
- primitive data: a ringed-space morphism `f : X ⟶ Y` and a module sheaf
  `𝒢 : Y.Modules`;
- derived API: the source-facing ringed-space specialization asserting that pullback carries
  finite-type modules to finite-type modules.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that pullback along a morphism of ringed spaces preserves
  finite type;
- `core/canonical`: `SheafOfModules.RingedSite.pullback_isFiniteType`,
  `SheafOfModules.IsFiniteType`, and the pullback owner `f^*`;
- `bridge/view`: the specialization along `Opens.map f.hom.base` and
  `RingedSpace.Hom.toRingCatSheafHom f`, exposed below at the `RingedSpace.Hom` owner layer. -/

variable {X Y : RingedSpace.{u}}

namespace RingedSpace.Hom

private theorem pullback_isFiniteType_aux
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsFiniteType] :
    ((f^*).obj 𝒢).IsFiniteType := by
  simpa using
    (SheafOfModules.RingedSite.pullback_isFiniteType.{u, u, u, u, u, u, u, u, u, u, u, u, u}
      (TopologicalSpace.Opens.map f.hom.base) (toRingCatSheafHom f) 𝒢)

-- Proof sketch: this is the ringed-space specialization of the Chapter 18 owner theorem on
-- pullback preserving finite type for sheaves of modules on ringed sites, applied to the site of
-- opens of `Y` and `X` and the canonical structure-sheaf map `toRingCatSheafHom f`.
/-- Lemma 17.9.2: for a morphism of ringed spaces
`f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`, the pullback of a finite type
`\mathcal O_Y`-module is a finite type `\mathcal O_X`-module. -/
theorem pullback_isFiniteType
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsFiniteType] :
    ((f^*).obj 𝒢).IsFiniteType :=
  pullback_isFiniteType_aux f 𝒢

end RingedSpace.Hom

end AlgebraicGeometry
