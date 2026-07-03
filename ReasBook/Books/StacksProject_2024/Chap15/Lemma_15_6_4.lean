import Mathlib
import stacks_project.Chap15.Situation_15_6_1
import stacks_project.Chap15.Lemma_15_5_4

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PullbackModuleCat" =>
  CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)

local notation "baseChangeFunctor" =>
  moduleCatBaseChangeToCategoricalPullback
    S.toA
    S.fromAprime
    S.bprimeToB
    S.bprimeToAprime
    S.comm

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint
    S.bprimeToB
    S.bprimeToAprime
    S.comm

/- Domain-style sampling for Lemma 15.6.4:
- primary domain: adjunctions for module-category base change along a pullback square of
  commutative rings;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation.bprimeToB`,
  `SurjectiveRingPullbackSituation.bprimeToAprime`,
  `moduleCatBaseChangeToCategoricalPullback`,
  `module_tensor_pullback_adjunction`,
  `module_tensor_pullback_adjunction_counit_isIso`;
- best owner abstraction: the specialized adjunction
  `module_tensor_pullback_adjunction S.bprimeToB S.bprimeToAprime S.comm`;
- primitive data: the surjective pullback situation `S`;
- derived API: the left-adjoint instance on the canonical base-change functor and the right-adjoint
  instance on the canonical fibre-product functor, together with the counit isomorphism of the
  composite back to the pullback category.

Source/core/bridge triage:
- `source-facing`: Lemma 15.6.4, asserting that the base-change functor attached to the surjective
  pullback square has the fibre-product module functor as right adjoint;
- `core/canonical`: `module_tensor_pullback_adjunction`;
- `bridge/view`: the specialization of that adjunction to the pullback square built from `S`.
-/

/- Lemma 15.6.4: in a surjective pullback situation, the canonical base-change functor
`Mod_{B'} → Mod_B ×[Mod_A] Mod_{A'}`
is left adjoint to the canonical fibre-product module functor
`(N, M', φ) ↦ N ×_φ M'`. This is exactly the specialized owner adjunction from
`module_tensor_pullback_adjunction`. -/
#check (module_tensor_pullback_adjunction S.bprimeToB S.bprimeToAprime S.comm :
  baseChangeFunctor ⊣ fiberProductFunctor)

/- Lemma 15.6.4: the composite from `Mod_B ×[Mod_A] Mod_{A'}` back to itself through the
fibre-product module functor and base change is canonically isomorphic to the identity functor.
This is the specialized owner-level counit isomorphism. -/
#check (module_tensor_pullback_adjunction_counit_isIso
  S.bprimeToB
  S.bprimeToAprime
  S.comm :
    IsIso
      ((module_tensor_pullback_adjunction S.bprimeToB S.bprimeToAprime S.comm).counit :
        fiberProductFunctor ⋙ baseChangeFunctor ⟶ 𝟭 PullbackModuleCat))

end
