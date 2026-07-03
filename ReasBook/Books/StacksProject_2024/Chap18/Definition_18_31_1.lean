import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

/- Domain-style sampling for Definition 18.31.1:
- primary domain: flat morphisms of ringed sites, expressed by exactness of inverse image on
  module sheaves;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `exactFunctor`;
- best owner abstraction: the source-facing owner should remain `RingedSite.Hom.IsFlat`, while the
  primitive canonical functor is `SheafOfModules.pullback f.structureSheafMap`;
- primitive data: a morphism of ringed sites `f`;
- derived API: the source-facing notation `f^*` and the constructor/reformulation lemmas exposing
  exactness of that canonical pullback functor via the class projection and `@[mk_iff]`.

Source/core/bridge triage:
- `source-facing`: `RingedSite.Hom.IsFlat`;
- `core/canonical`: `SheafOfModules.pullback f.structureSheafMap` with the exactness owner
  `exactFunctor`;
- `bridge/view`: the notation `f^*` for the canonical pullback functor. -/

/-- Pushforward on module sheaves along a morphism of ringed sites is a right adjoint. -/
-- Proof sketch: use the standard pullback-pushforward adjunction attached to the structure-sheaf
-- map; this instance is the minimal bridge needed so the canonical owner
-- `SheafOfModules.pullback f.structureSheafMap` is available in the ringed-site setting.
instance modulePushforward_isRightAdjoint :
    (SheafOfModules.pushforward f.structureSheafMap).IsRightAdjoint := sorry

/-- The inverse-image functor on module sheaves attached to a morphism of ringed sites. -/
noncomputable abbrev modulePullback :
    SheafOfModules.{max u v} Y.structureSheaf ⥤
      SheafOfModules.{max u v} X.structureSheaf :=
  SheafOfModules.pullback f.structureSheafMap

/- Source-facing notation for inverse image of module sheaves on ringed sites. -/
scoped syntax:max term:max "^*" : term

scoped macro_rules
  | `($f^*) => `(RingedSite.Hom.modulePullback $f)

/-- Definition 18.31.1: in the site-presented formalization used here, a morphism of ringed
sites is flat when the inverse-image functor on module sheaves attached to its structure-sheaf
map is exact, formalizing flatness of the ring map `f^\sharp`. -/
@[mk_iff isFlat_iff_pullback_exact]
class IsFlat : Prop where
  /-- Pullback on module sheaves preserves finite limits. -/
  pullback_exact :
    exactFunctor (SheafOfModules.{max u v} Y.structureSheaf)
      (SheafOfModules.{max u v} X.structureSheaf) (f^*)

open scoped RingedSite.Hom

end RingedSite.Hom
