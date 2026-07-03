import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_22_1 (from Chap18) -/
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

/-! ### Lemma_18_22_2 (from Chap18) -/
open CategoryTheory

universe u v

noncomputable section

/- Lemma 18.22.2: let
`f : (\mathit{Sh}(\mathcal C), \mathcal O) ⟶ (\mathit{Sh}(\mathcal D), \mathcal O')`
be a morphism of ringed topoi, let `𝒢` be a sheaf on `𝒟`, and set `ℱ = f⁻¹ 𝒢`. If `f` is
presented by a continuous functor `u : 𝒟 ⥤ 𝒞` and `𝒢 = h_V^#`, then via the identifications
of Lemma `18.21.3` the commutative squares of Lemma `18.20.1` and Lemma `18.22.1` are the same.
On underlying topoi this is exactly the canonical slice-topos comparison isomorphism from
Sites, Lemma `7.31.2`. -/
#check
  (fun
    {C : Type u} [Category.{u} C]
    {D : Type u} [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (f : D ⥤ C)
    [f.IsContinuous JD JC]
    (U : D) ↦
      (Over.post f).sheafPushforwardContinuousComp (Over.forget (f.obj U))
          RingCat.{u} (JD.over U) (JC.over (f.obj U)) JC ≪≫
        eqToIso (by rfl) ≪≫
        ((Over.forget U).sheafPushforwardContinuousComp f
          RingCat.{u} (JD.over U) JD JC).symm :
      JC.overPullback RingCat.{u} (f.obj U) ⋙
          (Over.post f).sheafPushforwardContinuous RingCat.{u}
            (JD.over U) (JC.over (f.obj U)) ≅
        f.sheafPushforwardContinuous RingCat.{u} JD JC ⋙
          JD.overPullback RingCat.{u} U)

section

variable {C : Type u} [Category.{v} C] [CategoryTheory.Limits.HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable (𝒪 : Sheaf J RingCat.{max u v}) (U : C)

/- Companion recall: under the representable identifications of Lemma `18.21.3`, the ringed part
of the localization square is the canonical map from the structure sheaf to the pushforward of its
localization on the slice site. This is the `j_U^♯` used in the ringed refinement of the
comparison. -/
#check (SheafOfModules.pushforwardOver (R := 𝒪) U)

end

/-! ### Lemma_18_22_3 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.RingedSite.Hom
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

/- Domain-style sampling for Lemma 18.22.3:
- primary domain: localized morphisms of ringed topoi attached to a map
  `s : ℱ ⟶ f⁻¹ 𝒢`, together with their base-change compatibility;
- sampled owner declarations:
  `CategoryTheory.localization_inverseImage_pullback_base_change_iso`,
  `CategoryTheory.TwoSquare.overPost.rightAdjointIso`,
  `RingedSite.Hom.underlyingInverseImageMap`,
  `Over.starPullbackIsoStar`,
  `RingedSite.Hom.underlyingStructureSheaf`;
- best owner abstraction:
  the underlying inverse-image functor of `f_s` is already the canonical composite
  `((f.toMorphismOfTopoi.localization 𝒢).inverseImage ⋙ Over.pullback s)`, while the ringed layer
  is obtained by
  combining the Chapter 7 comparison owner `TwoSquare.overPost.rightAdjointIso`, the Chapter 18
  owner `RingedSite.Hom.underlyingInverseImageMap`, and the relocalization owner
  `Over.starPullbackIsoStar`;
- primitive data:
  the ringed-site morphism `f`, the sheaves `𝒢`, `𝒢'`, `ℱ`, `ℱ'`, and the maps
  `s : ℱ ⟶ f.toMorphismOfTopoi⁻¹ 𝒢`, `s' : ℱ' ⟶ f.toMorphismOfTopoi⁻¹ 𝒢'`,
  `b : 𝒢' ⟶ 𝒢`, `a : ℱ' ⟶ ℱ`;
- derived API:
  the localized inverse-image functor
  `((f.toMorphismOfTopoi.localization 𝒢).inverseImage ⋙ Over.pullback s)`,
  the inverse-image-form structure-sheaf map `f_s^♯`,
  and the base-change square obtained from
  `localization_inverseImage_pullback_base_change_iso`,
  `Over.starPullbackIsoStar`, and the commutativity hypothesis
  `s' ≫ f.toMorphismOfTopoi⁻¹.map b = a ≫ s`.

Source/core/bridge triage:
- `source-facing`: the localized ringed-topos morphism `(f_s, f_s^♯)` and the base-change square
  of Lemma 18.22.3;
- `core/canonical`: the composite
  `((f.toMorphismOfTopoi.localization 𝒢).inverseImage ⋙ Over.pullback s)` and
  `CategoryTheory.localization_inverseImage_pullback_base_change_iso`,
  `TwoSquare.overPost.rightAdjointIso`, and `Over.starPullbackIsoStar`;
- `bridge/view`: the structure-sheaf map obtained by applying `Over.star` to the canonical
  ringed-site owner `underlyingInverseImageMap f`.

This file therefore stays at the `source-facing` layer for the ringed refinement while reusing the
canonical Chapter 7/mathlib owners for the underlying functorial content. The previous local
wrapper layer is not restored; only the source-facing ringed structure map and its commutative
square are kept.
-/
#check CategoryTheory.localization_inverseImage_pullback_base_change_iso

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [((f.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology).IsRightAdjoint)]
variable [PreservesFiniteLimits (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology)]
variable {𝒢 𝒢' : Sheaf Y.siteTopology (Type w)}
variable {ℱ ℱ' : Sheaf X.siteTopology (Type w)}

/- Lemma 18.22.3 (1), underlying topos level: the inverse-image functor of the localized morphism
`f_s` is the canonical Chapter 7 composite
`((f.toMorphismOfTopoi.localization 𝒢).inverseImage ⋙ Over.pullback s)`. -/
#check
  (fun (s : ℱ ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢) ↦
    (((f.toMorphismOfTopoi).localization 𝒢).inverseImage ⋙ Over.pullback s : Over 𝒢 ⥤ Over ℱ))

/- Companion recall: on underlying topoi, the square associated to
`s' ≫ f.toMorphismOfTopoi⁻¹.map b = a ≫ s` is the canonical base-change isomorphism for
`((f.toMorphismOfTopoi.localization 𝒢).inverseImage ⋙ Over.pullback s)`. -/
#check
  (fun
    (b : 𝒢' ⟶ 𝒢)
    (a : ℱ' ⟶ ℱ)
    (s : ℱ ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢)
    (s' : ℱ' ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢')
    (hs : s' ≫ ((f.toMorphismOfTopoi)⁻¹).map b = a ≫ s) ↦
      show
        Over.pullback b ⋙ ((f.toMorphismOfTopoi).localization 𝒢').inverseImage ⋙
            Over.pullback s' ≅
          ((f.toMorphismOfTopoi).localization 𝒢).inverseImage ⋙ Over.pullback s ⋙
            Over.pullback a from
        localization_inverseImage_pullback_base_change_iso
          f.toMorphismOfTopoi b a s s' hs)

end

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable
  [((f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology).IsRightAdjoint)]
variable
  [PreservesFiniteLimits (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]

/-- The inverse-image-form structure-sheaf map of the localized ringed-topos morphism
`(f_s, f_s^♯)`. Its source is the canonical owner
`((f.toMorphismOfTopoi.localization 𝒢).inverseImage ⋙ Over.pullback s)` applied to the localized
structure sheaf on the `Y`-side; the map itself is the composite of the Chapter 7 `overPost`
comparison, the relocalization comparison along `s`, and the inverse-image form of `f^\sharp`. -/
abbrev localizedPullbackMapStructureSheafSourceIso
    {𝒢 : Sheaf Y.siteTopology (Type (max u v))}
    {ℱ : Sheaf X.siteTopology (Type (max u v))}
    (s : ℱ ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢) :
    (((f.toMorphismOfTopoi).localization 𝒢).inverseImage ⋙ Over.pullback s).obj
        ((Over.star 𝒢).obj (underlyingStructureSheaf Y)) ≅
      (Over.star ((f.toMorphismOfTopoi)⁻¹.obj 𝒢) ⋙ Over.pullback s).obj
        (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y)) :=
  (Functor.isoWhiskerRight
      (TwoSquare.overPost.rightAdjointIso (f.toMorphismOfTopoi⁻¹) 𝒢)
      (Over.pullback s)).app (underlyingStructureSheaf Y)

/-- The inverse-image-form structure-sheaf map of the localized ringed-topos morphism
`(f_s, f_s^♯)`. Its source is the canonical owner
`((f.toMorphismOfTopoi.localization 𝒢).inverseImage ⋙ Over.pullback s)` applied to the localized
structure sheaf on the `Y`-side. -/
abbrev localizedPullbackMapStructureSheafHom
    {𝒢 : Sheaf Y.siteTopology (Type (max u v))}
    {ℱ : Sheaf X.siteTopology (Type (max u v))}
    (s : ℱ ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢) :
    (((f.toMorphismOfTopoi).localization 𝒢).inverseImage ⋙ Over.pullback s).obj
        ((Over.star 𝒢).obj (underlyingStructureSheaf Y)) ⟶
      (Over.star ℱ).obj (underlyingStructureSheaf X) :=
  (localizedPullbackMapStructureSheafSourceIso f s).hom ≫
    ((Over.starPullbackIsoStar s).app
      (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom ≫
    (Over.star ℱ).map (RingedSite.Hom.underlyingInverseImageMap f)

/- Lemma 18.22.3 (1), ringed layer: the structure-sheaf map `f_s^♯` is the composite of the
ringed localized pullback from Lemma 18.22.1 with the relocalization morphism from
Lemma 18.21.4. -/
#check localizedPullbackMapStructureSheafHom

/-- Lemma 18.22.3 (2): if `s' ≫ f.toMorphismOfTopoi⁻¹.map b = a ≫ s`, then the canonical
base-change comparison isomorphism for the localized inverse-image functors is compatible with the
structure-sheaf maps `f_{s'}^♯` and `f_s^♯`. This is the ringed-topos commutative square of the
source, expressed directly in terms of the Chapter 7 owner isomorphism. -/
theorem localizedPullbackMapStructureSheaf_commSq
    {𝒢 𝒢' : Sheaf Y.siteTopology (Type (max u v))}
    {ℱ ℱ' : Sheaf X.siteTopology (Type (max u v))}
    (b : 𝒢' ⟶ 𝒢)
    (a : ℱ' ⟶ ℱ)
    (s : ℱ ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢)
    (s' : ℱ' ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢')
    (hs : s' ≫ ((f.toMorphismOfTopoi)⁻¹).map b = a ≫ s) :
    CommSq
      ((localization_inverseImage_pullback_base_change_iso
          f.toMorphismOfTopoi b a s s' hs).hom.app
        ((Over.star 𝒢).obj (underlyingStructureSheaf Y)))
      ((((f.toMorphismOfTopoi).localization 𝒢').inverseImage ⋙ Over.pullback s').map
          (((Over.starPullbackIsoStar b).app (underlyingStructureSheaf Y)).hom) ≫
        localizedPullbackMapStructureSheafHom f s')
      ((Over.pullback a).map (localizedPullbackMapStructureSheafHom f s) ≫
        ((Over.starPullbackIsoStar a).app (underlyingStructureSheaf X)).hom)
      (𝟙 ((Over.star ℱ').obj (underlyingStructureSheaf X))) := by
  sorry

end

end RingedSite.Hom

/-! ### Lemma_18_22_4 (from Chap18) -/
open CategoryTheory

noncomputable section

/- Lemma 18.22.4: let
`(f, f^\sharp) : (\mathit{Sh}(\mathcal C), \mathcal O) \to (\mathit{Sh}(\mathcal D), \mathcal O')`,
let `s : \mathcal F \to f^{-1}\mathcal G` be as in Lemma 18.22.3, and assume `f` is presented by
a continuous functor `u : \mathcal D \to \mathcal C` with `\mathcal G = h_V^\#`,
`\mathcal F = h_U^\#`, and `s` induced by a morphism `c : U \to u(V)`. Then the commutative
diagrams of Lemma 18.20.2 and Lemma 18.22.3 agree via the identifications of Lemma 18.21.3.
In Lean, the underlying comparison is exactly the representable-localization theorem
`CategoryTheory.representable_localization_comparison_agrees_with_localized_pullback`; the ringed
structure-map identifications are supplied separately by Lemma 18.21.5 and Lemma 18.22.2. -/
recall CategoryTheory.representable_localization_comparison_agrees_with_localized_pullback
