import Mathlib
import stacks_proof.stacks_project.Chap15.Situation_15_7_1

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

/-- Helper for Lemma 15.7.2: the fibre-product module functor on the relative pullback category. -/
noncomputable abbrev relativeFiberProductFunctor
    (S : Situation) :
    S.relativeModuleCategory ⥤ ModuleCat Dp := sorry

local notation "fiberProductFunctor" => relativeFiberProductFunctor S

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

/-- Lemma 15.7.2: in Situation 15.7.1, the canonical base-change functor
`Mod_{D'} → Mod_D ×_[Mod_C] Mod_{C'}`
is left adjoint to the canonical fibre-product module functor
`(N, M', \varphi) ↦ N ×_\varphi M'`. -/
@[stacks 08KM]
noncomputable abbrev relativeModuleFunctor_adjunction
    (S : Situation) :
    S.relativeModuleFunctor ⊣ relativeFiberProductFunctor S := sorry

/-- Helper for Lemma 15.7.2: the intended counit natural transformation from the fibre-product
composite back to the identity on the relative pullback category. -/
noncomputable abbrev relativeModuleFunctor_counit
    (S : Situation) :
    relativeFiberProductFunctor S ⋙ S.relativeModuleFunctor ⟶ 𝟭 S.relativeModuleCategory := sorry

/-- Helper for Lemma 15.7.2: the ambient counit is an isomorphism on the relative pullback
category. -/
noncomputable abbrev relativeModuleFunctor_counit_isIso
    (S : Situation) :
    IsIso
      (FiberProductBaseChangeSituation.relativeModuleFunctor_counit (S := S)) := sorry

/-- Helper for Lemma 15.7.2: the textbook's objectwise identity statement for the counit. -/
noncomputable abbrev relativeModuleFunctor_counitIsoApp
    (S : Situation)
    (X : S.relativeModuleCategory) :
    ((relativeFiberProductFunctor S ⋙ S.relativeModuleFunctor).obj X) ≅ X := sorry

/-- Helper for Lemma 15.7.2: the composite of the fibre-product functor with the relative
base-change functor is naturally isomorphic to the identity. -/
noncomputable abbrev relativeModuleFunctor_counitIso :
    relativeFiberProductFunctor S ⋙ S.relativeModuleFunctor ≅ 𝟭 S.relativeModuleCategory := sorry

end FiberProductBaseChangeSituation

end
