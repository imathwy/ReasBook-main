import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap07.Lemma_7_31_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_8_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_20_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.LeftExactAdjunction

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 18.22.1:
- primary domain: localization of ringed topoi at a sheaf, split into the underlying localized
  geometric morphism of slice topoi and the induced structure-sheaf map on the ringed side;
- sampled owner declarations:
  `LeftExactAdjunction.localization`,
  `LeftExactAdjunction.localization_inverseImage_obj`,
  `LeftExactAdjunction.localization_pushforwardStarIso`,
  `RingedSite.Hom.structureSheafPushforward_eq`,
  `RingedSite.localizationAtSheafUnderlyingStructureMap`;
- sampled bridge declarations in the ringed specialization:
  `RingedSite.localizationAtSheafStructureMap`,
  `RingedSite.localizationAtSheafUnderlyingStructureMap`,
  `RingedSite.Hom.localizedStructureSheafMap`,
  `RingedSite.Hom.localization_structureSheafMap_eq`;
- best owner abstraction: the underlying localized geometric morphism is canonically owned by
  `LeftExactAdjunction.localization`; the ringed layer is the induced pushforward-form
  structure-sheaf map on the localized slice topoi, obtained by applying `Over.star 𝒢` to the
  forgotten `f.structureSheafMap` and transporting the target through
  `LeftExactAdjunction.localization_pushforwardStarIso`, and it is characterized by its
  compatibility with the general localization owner
  `RingedSite.localizationAtSheafUnderlyingStructureMap`; the representable localization of
  Lemma `18.20.1` is the specialization of this bridge to `𝒢 = h_V^#`;
- primitive data: the ringed-site morphism `f`, the target sheaf `𝒢`, and the structure-sheaf map
  `f.structureSheafMap`;
- derived API: the localized inverse image and pushforward comparison on underlying topoi, plus the
  induced localized structure-sheaf map and its representable specialization.

Source/core/bridge triage:
- `source-facing`: the commutative diagram of localized ringed topoi attached to `f` and `𝒢`,
  including the induced structure-sheaf map `(f')^\sharp`;
- `core/canonical`: `LeftExactAdjunction.localization`,
  `RingedSite.localizationAtSheafStructureMap`, and
  `RingedSite.localizationAtSheafUnderlyingStructureMap`;
- `bridge/view`: specialization from a ringed-site morphism to the canonical Chapter 7 site-to-topos
  bridge `f.toMorphismOfTopoi`, together with the localized pushforward-form structure map
  `RingedSite.Hom.localizedStructureSheafMap` and the representable bridge to
  `RingedSite.Hom.localization`.

This file is therefore a bridge/view file. It should reuse the Chapter 7 owner for the underlying
localized geometric morphism, while still exposing the general ringed layer through the induced
localized structure-sheaf map rather than collapsing the lemma to a bare topos-level recall or to
the representable specialization alone.
-/
recall LeftExactAdjunction.localization
recall LeftExactAdjunction.localization_inverseImage_obj
recall LeftExactAdjunction.localization_pushforwardStarIso

open scoped MorphismOfTopoiIn

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [PreservesFiniteLimits
  (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]
variable (𝒢 : Sheaf Y.siteTopology (Type (max u v)))

/- Lemma 18.22.1: for a morphism of ringed topoi
`f : (\mathit{Sh}(\mathcal C), \mathcal O) ⟶ (\mathit{Sh}(\mathcal D), \mathcal O')` and a sheaf
`𝒢` on the target topos, with `𝒡 = f^{-1} 𝒢`, the induced localized morphism on slice topoi is the
canonical slice-topos morphism attached to the adjunction `f^{-1} ⊣ f_*`, namely the Chapter 7
owner specialized to `f.toMorphismOfTopoi`. This is the underlying geometric-morphism part of the
ringed-topos diagram. -/
#check (f.toMorphismOfTopoi.localization 𝒢)

/- Companion specialization: on an object `(ℋ ⟶ 𝒢)`, the localized inverse image applies `f^{-1}`
to the structure map, giving `(f^{-1} ℋ ⟶ f^{-1} 𝒢)`. -/
#check (LeftExactAdjunction.localization_inverseImage_obj f.toMorphismOfTopoi 𝒢)

/- Companion specialization: restricting to `f^{-1} 𝒢` and then pushing forward along the
localized morphism is canonically isomorphic to pushing forward along `f` and then restricting to
`𝒢`. This is the topos-level comparison `f'_* j_{f^{-1}\mathcal G}^{-1} \cong
j_{\mathcal G}^{-1} f_*` appearing in the ringed statement. -/
#check (LeftExactAdjunction.localization_pushforwardStarIso f.toMorphismOfTopoi 𝒢)

/-- Lemma 18.22.1, ringed layer: the localized morphism
`f' : (\mathit{Sh}(X) / f^{-1} \mathcal G, \mathcal O_{f^{-1}\mathcal G}) \to
(\mathit{Sh}(Y) / \mathcal G, \mathcal O_{\mathcal G})`
has the canonical pushforward-form structure-sheaf map obtained by applying `Over.star 𝒢` to the
forgotten `f^\sharp` and transporting the target across the canonical localized pushforward
comparison. This is the general sheaf-level form of `(f')^\sharp`. -/
abbrev localizedStructureSheafMap :
    (Over.star 𝒢).obj (underlyingStructureSheaf Y) ⟶
      (f.toMorphismOfTopoi.localization 𝒢).pushforward.obj
        ((Over.star ((f.toMorphismOfTopoi)⁻¹.obj 𝒢)).obj (underlyingStructureSheaf X)) :=
  (Over.star 𝒢).map
      ((sheafCompose Y.siteTopology (forget RingCat.{max u v})).map f.structureSheafMap ≫
        eqToHom (structureSheafPushforward_eq f)) ≫
    ((localization_pushforwardStarIso f.toMorphismOfTopoi 𝒢).app
      (underlyingStructureSheaf X)).inv

/- Companion recall: the target and source of `localizedStructureSheafMap` are exactly the
localized structure sheaves on `Sh(Y) / \mathcal G` and `Sh(X) / f^{-1} \mathcal G`. -/
#check localizedStructureSheafMap

/- Companion bridge: the general localization-at-a-sheaf structure-map owner from
Definition `18.21.2` governs the ringed-localization inputs, and the present source-facing map is
the bridge from those localization maps together with `f^\sharp` to the localized morphism of
Lemma `18.22.1`. -/

end

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y) (V : Y)

/- In the representable specialization `\mathcal G = h_V^\#` of Lemma 18.22.1, the ringed
structure-map part `(f')^\sharp` is exactly the owner-level formula already exposed by
`RingedSite.Hom.localization_structureSheafMap_eq` in Lemma 18.20.1. -/
#check (localization_structureSheafMap_eq f V)

/- The representable bridge is supplied by the canonical equivalence and structure-map owners
recalled in Lemma `18.21.3`, together with the localized site-level owner
`localization_structureSheafMap_eq`; no additional wrapper is introduced here. -/

end

end RingedSite.Hom
