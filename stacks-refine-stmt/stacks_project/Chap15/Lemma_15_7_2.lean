import Mathlib
import stacks_project.Chap15.Situation_15_7_1
import stacks_project.Chap15.Lemma_15_6_4

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback.CatCommSqOver

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _
variable (S : Situation)

local notation "baseChangeFunctor" => S.relativeModuleFunctor

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes

/- Domain-style sampling for Lemma 15.7.2:
- primary domain: adjunctions between module-category base change and fibre-product module
  constructions over a commutative tensor square of rings;
- sampled owner declarations:
  `moduleCatBaseChangeSquare`,
  `moduleCatBaseChangeToCategoricalPullback`,
  `FiberProductBaseChangeSituation.relativeModuleFunctor`,
  `module_tensor_pullback_adjunction`,
  `module_tensor_pullback_adjunction_counit_isIso`;
- best owner abstraction: the specialized adjunction
  `module_tensor_pullback_adjunction S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes`;
- primitive data: the fibre-product base-change situation `S`;
- derived API: the specialized base-change functor `S.relativeModuleFunctor`, the specialized
  fibre-product functor `fiberProductFunctor`, their adjunction, and the canonical counit
  isomorphism on the composite back to the relative pullback category.

Source/core/bridge triage:
- `source-facing`: Lemma 15.7.2, asserting that the canonical base-change functor
  `Mod_{D'} → Mod_D ×_[Mod_C] Mod_{C'}` is left adjoint to the canonical fibre-product module
  functor;
- `core/canonical`: `module_tensor_pullback_adjunction`;
- `bridge/view`: the specialization of that owner adjunction to the tensor square attached to `S`.
-/

/- Lemma 15.7.2: in Situation 15.7.1, the canonical base-change functor
`Mod_{D'} → Mod_D ×_[Mod_C] Mod_{C'}`
is left adjoint to the canonical fibre-product module functor
`(N, M', φ) ↦ N ×_φ M'`. This is exactly the specialized owner adjunction from
`module_tensor_pullback_adjunction`. -/
set_option linter.hashCommand false in
#check (module_tensor_pullback_adjunction S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes :
  baseChangeFunctor ⊣ fiberProductFunctor)

/- Lemma 15.7.2: the composite from `Mod_D ×_[Mod_C] Mod_{C'}` back to itself through the
fibre-product module functor and base change is canonically isomorphic to the identity functor.
This is the specialized owner-level counit isomorphism. -/
set_option linter.hashCommand false in
#check (module_tensor_pullback_adjunction_counit_isIso
  S.dprimeToD
  S.dprimeToCPrime
  S.tensor_square_commutes :
    IsIso
      ((module_tensor_pullback_adjunction S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes)
        .counit :
          fiberProductFunctor ⋙ baseChangeFunctor ⟶ 𝟭 S.relativeModuleCategory))

end FiberProductBaseChangeSituation

end
