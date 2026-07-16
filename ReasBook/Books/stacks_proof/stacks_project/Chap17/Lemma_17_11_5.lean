import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap18.Lemma_18_23_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.11.5:
- primary domain: finitely presented sheaves of modules on ringed spaces and their behavior under
  the canonical pullback functor;
- inspected owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsFinitePresentation`,
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.RingedSite.pullback_isFinitePresentation`;
- best owner abstraction: the Chapter 18 owner theorem
  `SheafOfModules.RingedSite.pullback_isFinitePresentation`, specialized to the ringed site of
  opens of a ringed space and exposed at the pullback owner
  `AlgebraicGeometry.RingedSpace.Hom.pullback_isFinitePresentation`, with the owner predicate
  `SheafOfModules.IsFinitePresentation` on `Y.Modules`;
- primitive data: a ringed-space morphism `f : X ⟶ Y` and a module sheaf
  `𝒢 : Y.Modules`;
- derived API: the source-facing ringed-space specialization asserting that pullback carries
  finitely presented modules to finitely presented modules.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that pullback along a morphism of ringed spaces preserves
  finite presentation;
- `core/canonical`: `SheafOfModules.RingedSite.pullback_isFinitePresentation`,
  `SheafOfModules.IsFinitePresentation`, and the pullback owner `f^*`;
- `bridge/view`: the specialization along `TopologicalSpace.Opens.map f.hom.base` and
  `RingedSpace.Hom.toRingCatSheafHom f`, exposed at the pullback-owner namespace rather than as a
  separate global compatibility theorem. -/

variable {X Y : RingedSpace.{u}}

namespace RingedSpace.Hom

private theorem pullback_isFinitePresentation_aux
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsFinitePresentation] :
    ((f^*).obj 𝒢).IsFinitePresentation := by
  simpa using
    (SheafOfModules.RingedSite.pullback_isFinitePresentation.{u, u, u, u, u, u, u, u, u, u, u, u, u}
      (TopologicalSpace.Opens.map f.hom.base) (toRingCatSheafHom f) 𝒢)

-- Proof sketch: this is the ringed-space specialization of the Chapter 18 owner theorem on
-- pullback preserving finite presentation for sheaves of modules on ringed sites, applied to the
-- site of opens of `Y` and `X` and the canonical structure-sheaf map `toRingCatSheafHom f`.
/-- Lemma 17.11.5: for a morphism of ringed spaces
`f : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)`, the pullback of an
`\mathcal{O}_Y`-module of finite presentation is an `\mathcal{O}_X`-module of finite
presentation. -/
@[stacks 01BQ]
theorem pullback_isFinitePresentation
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsFinitePresentation] :
    ((f^*).obj 𝒢).IsFinitePresentation :=
  pullback_isFinitePresentation_aux f 𝒢

end RingedSpace.Hom

end AlgebraicGeometry
