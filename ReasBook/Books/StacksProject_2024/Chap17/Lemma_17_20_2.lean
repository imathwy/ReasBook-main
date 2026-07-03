import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {X Y : RingedSpace.{u}}

namespace AlgebraicGeometry.RingedSpace.Hom

/- Domain-style sampling for Lemma 17.20.2:
- primary domain: exactness of inverse-image on module sheaves under a flat morphism of ringed
  spaces;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.Hom.pullback`,
  `RingedSpace.Modules`,
  `SheafOfModules.pullback`,
  `exactFunctor`,
  `RingedSite.Hom.IsFlat.pullback_exact`;
- best owner abstraction: this file is a `bridge/view` item whose primitive hypothesis is still
  the source-facing flatness class `RingedSpace.Hom.IsFlat`, but whose exactness conclusion is
  about the canonical Chapter 6 pullback owner `AlgebraicGeometry.RingedSpace.Hom.pullback`;
  the theorem should therefore be exposed in the `AlgebraicGeometry.RingedSpace.Hom` family,
  while its proof route reuses the site-level exactness owner
  `RingedSite.Hom.IsFlat.pullback_exact`;
- primitive data: a morphism `f : X ⟶ Y` together with `[RingedSpace.Hom.IsFlat f]`;
- derived API: exactness of the canonical pullback functor on the owner categories `Y.Modules` and
  `X.Modules`.

Source/core/bridge triage:
- `source-facing`: flat morphisms of ringed spaces, expressed stalkwise;
- `core/canonical`: `RingedSpace.Modules`, `SheafOfModules.pullback`, and `exactFunctor`;
- `bridge/view`: `AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact`, which upgrades the
  source-facing flatness owner to exactness of the canonical pullback functor.

Primitive-vs-derived decision:
- the module categories should be taken from the existing owner `RingedSpace.Modules`, not rebuilt
  locally as `SheafOfModules (RingedSpace.ringCatSheaf _)`;
- the theorem itself remains necessary as the ringed-space bridge from stalkwise flatness to the
  exactness owner, so the refinement here is to reuse the canonical category owner rather than
  keep a parallel local category spelling.
-/

/-- Lemma 17.20.2: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a flat morphism of ringed
spaces, then the pullback functor `f^* : \mathit{Mod}(\mathcal O_Y) \to \mathit{Mod}(\mathcal O_X)`
is exact. -/
-- Proof sketch: write `f^*` as the composite of the exact inverse-image functor on abelian sheaves
-- with extension of scalars along `f^{-1} \mathcal O_Y ⟶ \mathcal O_X`; stalkwise flatness makes
-- this tensor-extension functor left exact, and pullback is already right exact by adjointness.
theorem IsFlat.pullback_exact
    (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f] :
    exactFunctor Y.Modules X.Modules (f^*) := sorry

end AlgebraicGeometry.RingedSpace.Hom
