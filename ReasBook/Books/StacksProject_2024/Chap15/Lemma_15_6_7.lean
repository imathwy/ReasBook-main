import Mathlib
import StacksProject_2024.Chap15.Situation_15_6_1
import StacksProject_2024.Chap15.Lemma_15_6_4

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PullbackModuleCat" =>
  CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint S.bprimeToB S.bprimeToAprime S.comm

/- Domain-style sampling for 15.6.7:
- primary domain: finiteness of modules under the canonical fibre-product functor attached to a
  surjective pullback square of commutative rings;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation`,
  `CategoricalPullback`,
  `module_tensor_pullback_right_adjoint`,
  `Module.Finite`;
- best owner abstraction: the source-facing datum is an object
  `X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)`,
  and the fibre-product module is the derived object `fiberProductFunctor.obj X`;
- primitive data: `S` and `X`;
- derived API: the component modules `X.fst`, `X.snd`, and finiteness of the induced fibre-product
  module.

Source/core/bridge triage:
- `source-facing`: `surjectiveRingPullbackModuleFiberProduct_finite`;
- `core/canonical`: the functor
  `module_tensor_pullback_right_adjoint S.bprimeToB S.bprimeToAprime S.comm`;
- `bridge/view`: none; the theorem is stated directly for the canonical owner. -/

-- Proof sketch: choose finitely many generators of `X.fst` over `B` and of `X.snd` over `A'`.
-- Using Lemma `15.6.4`, lift the generators of `X.fst` to the fibre-product module and express
-- generators of `X.snd` via images of further elements of the fibre product. Surjectivity of
-- `B' → B` and the description of its kernel then show these lifted elements generate the whole
-- fibre-product module over `B'`.
/-- Lemma 15.6.7: in a surjective pullback situation, if `N` is finite over `B` and `M'` is
finite over `A'`, then the fibre-product module `N ×_φ M'` is finite over `B'`. -/
theorem surjectiveRingPullbackModuleFiberProduct_finite
    (X : PullbackModuleCat)
    (hfst : Module.Finite B X.fst) (hsnd : Module.Finite A' X.snd) :
    Module.Finite S.Bprime ((fiberProductFunctor).obj X) := sorry

end
