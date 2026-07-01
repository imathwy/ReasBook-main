import Mathlib
import stacks_project.Chap15.Lemma_15_6_4

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PullbackModuleCat" =>
  CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)

/- Domain-style sampling for 15.6.6:
- primary domain: morphisms in the pullback category
  `Mod_B ×[Mod_A] Mod_{A'}`
  attached to Situation `15.6.1`, together with the induced map on the fibre-product module from
  `15.6.4`;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation`,
  `CategoricalPullback`,
  `module_tensor_pullback_right_adjoint`,
  `Functor.map`;
- best owner abstraction: the primitive source-facing data are an object
  `X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)`
  and a morphism `f : X ⟶ Y`; the induced map on fibre-product modules is the derived canonical
  morphism `((module_tensor_pullback_right_adjoint
    S.bprimeToB
    S.bprimeToAprime
    S.comm).map f)`;
- primitive data: `S`, `X`, `Y`, and `f`;
- derived API: the component maps `f.fst`, `f.snd`, and the induced map on the fibre-product
  module.

Source/core/bridge triage:
- `source-facing`: `surjectiveRingPullbackModuleFiberProduct_map_surjective`;
- `core/canonical`: the functor
  `module_tensor_pullback_right_adjoint S.bprimeToB S.bprimeToAprime S.comm`;
- `bridge/view`: none; the theorem reads off surjectivity of the induced map from surjectivity of
  the component morphisms in the pullback category. -/

-- Proof sketch: view `X` and `Y` as triples `(N₁, M'₁, φ₁)` and `(N₂, M'₂, φ₂)` in the canonical
-- pullback category of `15.6.4`. The morphism `f` provides the compatible pair of maps
-- `f.fst : N₁ → N₂` and `f.snd : M'₁ → M'₂`; surjectivity of these components is exactly the
-- hypothesis of the textbook argument, which then gives surjectivity on the induced map between
-- the fibre-product modules.
/-- Lemma 15.6.6: in Situation `15.6.1`, a morphism in
`Mod_B ×[Mod_A] Mod_{A'}`
whose `B`-component and `A'`-component are surjective induces a surjective map on the associated
fibre-product modules over `B' = B ×_A A'`. -/
theorem surjectiveRingPullbackModuleFiberProduct_map_surjective
    {X Y : PullbackModuleCat}
    (f : X ⟶ Y)
    (hfst : Function.Surjective f.fst)
    (hsnd : Function.Surjective f.snd) :
    Function.Surjective
      ((module_tensor_pullback_right_adjoint
        S.bprimeToB
        S.bprimeToAprime
        S.comm).map f) := sorry

end
