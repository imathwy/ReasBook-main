import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.stacks_project.Chap18.Definition_18_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward f.structureSheafMap.hom).IsRightAdjoint]

/-
Domain-style sampling for Lemma 18.14.3:
- primary domain: pullback/pushforward of sheaves of modules along a morphism of ringed sites or
  ringed topoi, together with the generic exact-functor owners `leftExactFunctor` and
  `rightExactFunctor`;
- sampled owner declarations:
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullback`,
  `RingedSite.Hom.pushforward`,
  `leftExactFunctor`,
  `rightExactFunctor`;
- best owner abstraction: the bundled morphism of ringed sites `f : X ⟶ Y`, with module direct
  and inverse image expressed by the canonical owners
  `SheafOfModules.pushforward.{max u v} f.structureSheafMap` and
  `SheafOfModules.pullback.{max u v} f.structureSheafMap`;
- primitive data: the bundled ringed-site morphism `f`, together with the weak-sheafification and
  local-bijectivity hypotheses on `X.siteTopology` and the presheaf-level right-adjoint owner for
  `PresheafOfModules.pushforward f.structureSheafMap.hom`;
- derived API: the canonical sheaf-level right-adjoint structure on
  `SheafOfModules.pushforward.{max u v} f.structureSheafMap`, the resulting limit/colimit preservation
  instances, and the bundled left/right exactness predicates for the direct and inverse image
  owners.

Source/core/bridge triage:
- `source-facing`: the four clauses asserting that `f_*` preserves limits and is left exact, and
  that `f^*` preserves colimits and is right exact;
- `core/canonical`: `SheafOfModules.pushforward`, `SheafOfModules.pullback`, and the generic
  exactness owners `leftExactFunctor` and `rightExactFunctor`;
- `bridge/view`: the direct `#check` / `#synth` queries below, with no parallel local theorem API.
-/

/- Lemma 18.14.3 (1): the direct-image functor `f_*` on sheaves of modules is left exact. -/
#check
  (leftExactFunctor_iff (SheafOfModules.pushforward.{max u v} f.structureSheafMap)).mpr inferInstance

/- Lemma 18.14.3 (2): in fact, the direct-image functor `f_*` on sheaves of modules commutes with
all limits. -/
#synth PreservesLimits (SheafOfModules.pushforward.{max u v} f.structureSheafMap)

/- Lemma 18.14.3 (3): the inverse-image functor `f^*` on sheaves of modules is right exact. -/
#check
  (rightExactFunctor_iff (SheafOfModules.pullback.{max u v} f.structureSheafMap)).mpr inferInstance

/- Lemma 18.14.3 (4): in fact, the inverse-image functor `f^*` on sheaves of modules commutes
with all colimits. -/
#synth PreservesColimits (SheafOfModules.pullback.{max u v} f.structureSheafMap)

end RingedSite.Hom
