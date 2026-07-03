import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_31_1
import StacksProject_2024.Chap18.Lemma_18_20_1
import StacksProject_2024.Chap18.Definition_18_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 18.22.1:
- primary domain: localization of ringed topoi at a sheaf, split into the underlying localized
  geometric morphism of slice topoi and the induced structure-sheaf map on the ringed side;
- sampled owner declarations:
  `CategoryTheory.LeftExactAdjunction.localization`,
  `CategoryTheory.LeftExactAdjunction.localization_inverseImage_obj`,
  `CategoryTheory.LeftExactAdjunction.localization_pushforwardStarIso`;
- sampled bridge declarations in the ringed specialization:
  `RingedSite.Hom.localization`,
  `RingedSite.Hom.localization_base`,
  `SheafOfModules.pushforwardOver`;
- best owner abstraction: the underlying localized geometric morphism is canonically owned by
  `CategoryTheory.LeftExactAdjunction.localization`; the ringed layer is bridge data obtained by
  transporting `f.structureSheafMap` across the localization maps, and in the representable
  specialization this bridge is concretely realized by `RingedSite.Hom.localization`;
- primitive data: the ringed-site morphism `f`, the target sheaf `𝒢`, and the structure-sheaf map
  `f.structureSheafMap`;
- derived API: the localized inverse image and pushforward comparison on underlying topoi, plus the
  representable specialization of the induced structure-sheaf map.

Source/core/bridge triage:
- `source-facing`: the commutative diagram of localized ringed topoi attached to `f` and `𝒢`,
  including the induced structure-sheaf map `(f')^\sharp`;
- `core/canonical`: `CategoryTheory.LeftExactAdjunction.localization` and its companion theorems;
- `bridge/view`: specialization from a ringed-site morphism to `f.toMorphismOfTopoi`, together
  with the representable bridge to `RingedSite.Hom.localization` and `SheafOfModules.pushforwardOver`.

This file is therefore a bridge/view file. It should reuse the Chapter 7 owner for the underlying
localized geometric morphism, but it must still expose the ringed layer through the induced
structure-sheaf map rather than collapsing the lemma to a bare topos-level recall.
-/
recall CategoryTheory.LeftExactAdjunction.localization
recall CategoryTheory.LeftExactAdjunction.localization_inverseImage_obj
recall CategoryTheory.LeftExactAdjunction.localization_pushforwardStarIso

open scoped MorphismOfTopoiIn

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [((f.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology).IsRightAdjoint)]
variable [PreservesFiniteLimits (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology)]
variable (𝒢 : Sheaf Y.siteTopology (Type w))

/- Lemma 18.22.1: for a morphism of ringed topoi
`f : (\mathit{Sh}(\mathcal C), \mathcal O) ⟶ (\mathit{Sh}(\mathcal D), \mathcal O')` and a sheaf
`𝒢` on the target topos, with `𝒡 = f^{-1} 𝒢`, the induced localized morphism on slice topoi is the
canonical slice-topos morphism attached to the adjunction `f^{-1} ⊣ f_*`, namely the Chapter 7
owner specialized to `f.toMorphismOfTopoi`. This is the underlying geometric-morphism part of the
ringed-topos diagram. -/
#check (f.toMorphismOfTopoi.localization 𝒢)

/- Companion specialization: on an object `(ℋ ⟶ 𝒢)`, the localized inverse image applies `f^{-1}`
to the structure map, giving `(f^{-1} ℋ ⟶ f^{-1} 𝒢)`. -/
#check (CategoryTheory.LeftExactAdjunction.localization_inverseImage_obj f.toMorphismOfTopoi 𝒢)

/- Companion specialization: restricting to `f^{-1} 𝒢` and then pushing forward along the
localized morphism is canonically isomorphic to pushing forward along `f` and then restricting to
`𝒢`. This is the topos-level comparison `f'_* j_{f^{-1}\mathcal G}^{-1} \cong
j_{\mathcal G}^{-1} f_*` appearing in the ringed statement. -/
#check (CategoryTheory.LeftExactAdjunction.localization_pushforwardStarIso f.toMorphismOfTopoi 𝒢)

end

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y) (V : Y)

/-- In the representable specialization `\mathcal G = h_V^\#` of Lemma 18.22.1, the ringed
structure-map part `(f')^\sharp` is the localized formula from Lemma 18.20.1: localize
`f^\sharp`, then transport it across the canonical pushforward comparison for the slice square. -/
theorem localization_structureSheafMap_eq :
    (localization f V).structureSheafMap =
      let e :=
        (Over.post f.base).sheafPushforwardContinuousComp (Over.forget (f.base.obj V))
            RingCat.{max u v} (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
            X.siteTopology ≪≫
          eqToIso (by rfl) ≪≫
          ((Over.forget V).sheafPushforwardContinuousComp f.base
            RingCat.{max u v} (Y.siteTopology.over V) Y.siteTopology X.siteTopology).symm
      (Y.siteTopology.overPullback RingCat.{max u v} V).map f.structureSheafMap ≫
        (e.symm.app X.structureSheaf).hom := rfl

end

end RingedSite.Hom
