import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.14.3:
- primary domain: local freeness of module sheaves on ringed spaces and its stability under
  pullback;
- inspected owner declarations:
  `SheafOfModules.IsLocallyFree`,
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.pullback`,
  `RingedSpace.Hom.toRingCatSheafHom`;
- best owner abstraction: the canonical pullback functor `f^*` on module sheaves together with
  the owner predicate `SheafOfModules.IsLocallyFree`;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y`, a module sheaf `𝒢` on `Y`, and the
  local-freeness structure on `𝒢`;
- derived API: the pullback-stability theorem and instance below. -/

/- Source/core/bridge triage for Lemma 17.14.3:
- `source-facing`: the Stacks assertion that pulling back a locally free module along a morphism of
  ringed spaces again gives a locally free module;
- `core/canonical`: the pullback owner `f^*` and the typeclass owner `SheafOfModules.IsLocallyFree`;
- `bridge/view`: the ringed-space specialization of pullback-stability for the canonical owner.

This file should therefore expose local freeness under pullback in the same theorem-plus-instance
shape as the analogous flatness file, so downstream code can infer local freeness of `((f^*).obj 𝒢)`
from `[𝒢.IsLocallyFree]` without a separate wrapper theorem. -/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

-- Proof sketch: for each `x : X`, pick a neighbourhood of `f x` on which `𝒢` is free. Pull that
-- neighbourhood back along `f`; the restriction of `f^*𝒢` to the preimage is the pullback of a
-- free sheaf, hence free of the same rank, so these pulled-back neighbourhoods witness local
-- freeness of `f^*𝒢`.
/-- Lemma 17.14.3: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a morphism of ringed
spaces and `\mathcal G` is a locally free `\mathcal O_Y`-module, then `f^*\mathcal G` is a
locally free `\mathcal O_X`-module. -/
theorem pullback_isLocallyFree
    (𝒢 : Y.Modules) [𝒢.IsLocallyFree] :
    ((f^*).obj 𝒢).IsLocallyFree := sorry

/-- Pullback along a morphism of ringed spaces preserves locally free module sheaves. -/
instance (𝒢 : Y.Modules) [𝒢.IsLocallyFree] :
    ((f^*).obj 𝒢).IsLocallyFree :=
  pullback_isLocallyFree f 𝒢

end AlgebraicGeometry
