import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap12.Lemma_12_29_1
import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap17.Definition_17_20_1
import stacks_project.Chap17.Lemma_17_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.11.11:
- primary domain: adjunctions, exactness, and injective-object preservation for module-sheaf
  functors on ringed spaces;
- sampled owner declarations:
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `RingedSpace.Hom.IsFlat.pullback_exact`,
  `preservesInjectiveObjects_of_exact_leftAdjoint`,
  `Functor.injective_obj_of_injective`;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical pushforward
  functor `f _*`, derived from the adjunction `f^* ⊣ f _*`;
- primitive data: only the morphism `f : X ⟶ Y` and the flatness hypothesis;
- derived API: preservation of injective objects by `f _*`, and the objectwise injectivity
  consequence for `(f _*).obj ℐ`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a flat direct image sends injective
  `\mathcal O_X`-modules to injective `\mathcal O_Y`-modules;
- `core/canonical`: `Functor.PreservesInjectiveObjects` together with
  `Functor.injective_obj_of_injective`;
- `bridge/view`: this ringed-space specialization built from
  `SheafOfModules.pullbackPushforwardAdjunction` and `RingedSpace.Hom.IsFlat.pullback_exact`.
-/

-- Proof sketch: Lemma `17.20.2` makes `f^*` exact for a flat morphism, and Lemma `12.29.1`
-- upgrades the adjunction `f^* ⊣ f_*` to preservation of injective objects by `f_*`.
/-- For a flat morphism of ringed spaces, direct image on module sheaves preserves injective
objects. -/
instance modulePushforward_preservesInjectiveObjects_of_isFlat
    (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f] :
    (f _*).PreservesInjectiveObjects := by
  sorry

/-- Lemma 20.11.11: for a flat morphism of ringed spaces, the pushforward of an injective
`\mathcal O_X`-module is injective as an `\mathcal O_Y`-module. -/
theorem injective_modulePushforward_of_isFlat
    (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f]
    (ℐ : (RingedSpace.Modules X)) (hℐ : Injective ℐ) :
    Injective ((f _*).obj ℐ) :=
  (f _*).injective_obj_of_injective hℐ

end AlgebraicGeometry.RingedSpace
