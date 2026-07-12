import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_28_2
import StacksProject_2024.Chap07.Lemma_7_31_3
import StacksProject_2024.Chap18.Definition_18_7_1
import StacksProject_2024.Chap18.Definition_18_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

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
variable [PreservesFiniteLimits
  (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]
variable {𝒢 𝒢' : Sheaf Y.siteTopology (Type (max u v))}
variable {ℱ ℱ' : Sheaf X.siteTopology (Type (max u v))}

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
variable [PreservesFiniteLimits
  (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]

private noncomputable def localizedPullbackMapStructureSheafSourceIso
    {𝒢 : Sheaf Y.siteTopology (Type (max u v))}
    {ℱ : Sheaf X.siteTopology (Type (max u v))}
    (s : ℱ ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢) :
    (((f.toMorphismOfTopoi).localization 𝒢).inverseImage ⋙ Over.pullback s).obj
        ((Over.star 𝒢).obj (underlyingStructureSheaf Y)) ≅
      (Over.star ((f.toMorphismOfTopoi)⁻¹.obj 𝒢) ⋙ Over.pullback s).obj
        (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y)) :=
  (Functor.isoWhiskerRight
      (TwoSquare.overPost.rightAdjointIso (f.toMorphismOfTopoi).inverseImage 𝒢)
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
    (Over.star ℱ).map (underlyingInverseImageMap f)

/-- Helper for Lemma 18.22.3: the final structure-sheaf map `underlyingInverseImageMap f`
commutes with relocalization via naturality of `Over.starPullbackIsoStar`. -/
private theorem starPullbackIsoStar_underlyingInverseImageMap_naturality
    {ℱ ℱ' : Sheaf X.siteTopology (Type (max u v))}
    (a : ℱ' ⟶ ℱ) :
    (Over.pullback a).map ((Over.star ℱ).map (underlyingInverseImageMap f)) ≫
      ((Over.starPullbackIsoStar a).app (underlyingStructureSheaf X)).hom =
    ((Over.starPullbackIsoStar a).app
        (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom ≫
      (Over.star ℱ').map (underlyingInverseImageMap f) := by
  -- Move the inverse-image map across relocalization using naturality of the comparison isomorphism.
  simpa [Functor.comp_obj, Category.assoc] using
    ((Over.starPullbackIsoStar a).hom.naturality (underlyingInverseImageMap f))

/-- Helper for Lemma 18.22.3: the source transport is exactly the `Over.pullback` image of the
Chapter 7 comparison `TwoSquare.overPost.rightAdjointIso`. -/
private theorem localizedPullbackMapStructureSheafSourceIso_hom_eq
    {𝒢 : Sheaf Y.siteTopology (Type (max u v))}
    {ℱ : Sheaf X.siteTopology (Type (max u v))}
    (s : ℱ ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢) :
    (localizedPullbackMapStructureSheafSourceIso f s).hom =
      (Over.pullback s).map
        ((TwoSquare.overPost.rightAdjointIso
            (f.toMorphismOfTopoi).inverseImage 𝒢).hom.app
          (underlyingStructureSheaf Y)) := by
  -- Proof comment: `localizedPullbackMapStructureSheafSourceIso` is just the whiskered component
  -- of `TwoSquare.overPost.rightAdjointIso`, so its `hom` is definitionally the mapped component.
  rfl

/-- Helper for Lemma 18.22.3: the transport prefix in `localizedPullbackMapStructureSheafHom` is
the pulled-back Chapter 7 comparison followed by the relocalization comparison. -/
private theorem localizedPullbackMapStructureSheafTransport_eq
    {𝒢 : Sheaf Y.siteTopology (Type (max u v))}
    {ℱ : Sheaf X.siteTopology (Type (max u v))}
    (s : ℱ ⟶ ((f.toMorphismOfTopoi)⁻¹).obj 𝒢) :
    (localizedPullbackMapStructureSheafSourceIso f s).hom ≫
        ((Over.starPullbackIsoStar s).app
          (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom =
      (Over.pullback s).map
          ((TwoSquare.overPost.rightAdjointIso
              (f.toMorphismOfTopoi).inverseImage 𝒢).hom.app
            (underlyingStructureSheaf Y)) ≫
        ((Over.starPullbackIsoStar s).app
          (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom := by
  -- Proof comment: rewrite the source-side abbreviation once so later proofs can focus on the
  -- remaining base-change compatibility instead of this whiskering transport.
  rw [localizedPullbackMapStructureSheafSourceIso_hom_eq]
  rfl

/-- Helper for Lemma 18.22.3: before applying `underlyingInverseImageMap f`, the Chapter 7
base-change comparison is already compatible with the two transport layers used to define the
localized structure-sheaf maps. -/
private theorem localizedPullbackStructureTransport_commSq
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
        (localizedPullbackMapStructureSheafSourceIso f s').hom ≫
        ((Over.starPullbackIsoStar s').app
          (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom)
      ((Over.pullback a).map ((localizedPullbackMapStructureSheafSourceIso f s).hom) ≫
        (Over.pullback a).map
          (((Over.starPullbackIsoStar s).app
            (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom) ≫
      ((Over.starPullbackIsoStar a).app
          (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom)
      (𝟙 ((Over.star ℱ').obj
        (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y)))) := by
  -- Proof comment: this is the objectwise component of the Chapter 7 base-change isomorphism,
  -- after rewriting the two transport prefixes into the explicit comparison maps used here.
  refine CommSq.mk ?_
  apply Over.OverMorphism.ext
  ext x t
  simp [CategoryTheory.localization_inverseImage_pullback_base_change_iso,
    localizedPullbackMapStructureSheafSourceIso_hom_eq (f := f) (s := s),
    localizedPullbackMapStructureSheafSourceIso_hom_eq (f := f) (s := s'), Category.assoc]
  let rhs :=
    (((((f.toMorphismOfTopoi).localization 𝒢').inverseImage ⋙ Over.pullback s').map
          (((Over.starPullbackIsoStar b).app (underlyingStructureSheaf Y)).hom) ≫
        (localizedPullbackMapStructureSheafSourceIso f s').hom ≫
        ((Over.starPullbackIsoStar s').app
          (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom) ≫
      𝟙 ((Over.star ℱ').obj
        (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y)))).left.hom.app x t
  dsimp [rhs, CategoryTheory.Limits.pullbackProdFstIsoProd]
  rfl

/- Lemma 18.22.3 (1), ringed layer: the structure-sheaf map `f_s^♯` is the composite of the
ringed localized pullback from Lemma 18.22.1 with the relocalization morphism from
Lemma 18.21.4. -/
#check localizedPullbackMapStructureSheafHom

/-- Lemma 18.22.3 (2): if `s' ≫ f.toMorphismOfTopoi⁻¹.map b = a ≫ s`, then the canonical
base-change comparison isomorphism for the localized inverse-image functors is compatible with the
structure-sheaf maps `f_{s'}^♯` and `f_s^♯`. This is the ringed-topos commutative square of the
source, expressed directly in terms of the Chapter 7 owner isomorphism. -/
@[stacks 04J8]
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
  -- Proof comment: first append the final `underlyingInverseImageMap f` to the transport square
  -- that stops just before the last ringed-site structure morphism.
  refine CommSq.mk ?_
  -- Proof comment: the remaining reassociation is exactly the naturality square moving
  -- `underlyingInverseImageMap f` across the relocalization comparison for `a`.
  have htransport := (localizedPullbackStructureTransport_commSq f b a s s' hs).w
  have hnat := starPullbackIsoStar_underlyingInverseImageMap_naturality (f := f) a
  set transportPrefix :=
    (Over.pullback a).map ((localizedPullbackMapStructureSheafSourceIso f s).hom) ≫
      (Over.pullback a).map
        (((Over.starPullbackIsoStar s).app
          (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom)
  have hnat' :
      transportPrefix ≫
          (Over.pullback a).map ((Over.star ℱ).map (underlyingInverseImageMap f)) ≫
          ((Over.starPullbackIsoStar a).app (underlyingStructureSheaf X)).hom =
        transportPrefix ≫
          ((Over.starPullbackIsoStar a).app
            (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom ≫
          (Over.star ℱ').map (underlyingInverseImageMap f) := by
    simpa [transportPrefix, Category.assoc] using
      congrArg
        (fun k ↦ transportPrefix ≫ k)
        hnat
  have htransport' :
      ((localization_inverseImage_pullback_base_change_iso
            f.toMorphismOfTopoi b a s s' hs).hom.app
          ((Over.star 𝒢).obj (underlyingStructureSheaf Y))) ≫
          transportPrefix ≫
          ((Over.starPullbackIsoStar a).app
            (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom ≫
          (Over.star ℱ').map (underlyingInverseImageMap f) =
        ((((f.toMorphismOfTopoi).localization 𝒢').inverseImage ⋙ Over.pullback s').map
            (((Over.starPullbackIsoStar b).app (underlyingStructureSheaf Y)).hom) ≫
          (localizedPullbackMapStructureSheafSourceIso f s').hom ≫
          ((Over.starPullbackIsoStar s').app
            (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom) ≫
          (Over.star ℱ').map (underlyingInverseImageMap f) := by
    simpa [transportPrefix, Category.assoc] using
      congrArg
        (fun k ↦ k ≫ (Over.star ℱ').map (underlyingInverseImageMap f))
        htransport
  calc
    ((localization_inverseImage_pullback_base_change_iso
          f.toMorphismOfTopoi b a s s' hs).hom.app
        ((Over.star 𝒢).obj (underlyingStructureSheaf Y))) ≫
        (Over.pullback a).map (localizedPullbackMapStructureSheafHom f s) ≫
        ((Over.starPullbackIsoStar a).app (underlyingStructureSheaf X)).hom =
      ((localization_inverseImage_pullback_base_change_iso
            f.toMorphismOfTopoi b a s s' hs).hom.app
          ((Over.star 𝒢).obj (underlyingStructureSheaf Y))) ≫
          transportPrefix ≫
          (Over.pullback a).map ((Over.star ℱ).map (underlyingInverseImageMap f)) ≫
          ((Over.starPullbackIsoStar a).app (underlyingStructureSheaf X)).hom := by
      simp [transportPrefix, localizedPullbackMapStructureSheafHom, Functor.map_comp, Category.assoc]
    _ =
      ((localization_inverseImage_pullback_base_change_iso
            f.toMorphismOfTopoi b a s s' hs).hom.app
          ((Over.star 𝒢).obj (underlyingStructureSheaf Y))) ≫
          transportPrefix ≫
          ((Over.starPullbackIsoStar a).app
            (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom ≫
          (Over.star ℱ').map (underlyingInverseImageMap f) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            ((localization_inverseImage_pullback_base_change_iso
                  f.toMorphismOfTopoi b a s s' hs).hom.app
                ((Over.star 𝒢).obj (underlyingStructureSheaf Y))) ≫
              k)
          hnat'
    _ =
      ((((f.toMorphismOfTopoi).localization 𝒢').inverseImage ⋙ Over.pullback s').map
          (((Over.starPullbackIsoStar b).app (underlyingStructureSheaf Y)).hom) ≫
        (localizedPullbackMapStructureSheafSourceIso f s').hom ≫
        ((Over.starPullbackIsoStar s').app
          (((f.toMorphismOfTopoi)⁻¹).obj (underlyingStructureSheaf Y))).hom) ≫
        (Over.star ℱ').map (underlyingInverseImageMap f) := htransport'
    _ = ((((f.toMorphismOfTopoi).localization 𝒢').inverseImage ⋙ Over.pullback s').map
            (((Over.starPullbackIsoStar b).app (underlyingStructureSheaf Y)).hom) ≫
          localizedPullbackMapStructureSheafHom f s') ≫
          𝟙 ((Over.star ℱ').obj (underlyingStructureSheaf X)) := by
      simp [localizedPullbackMapStructureSheafHom, Category.assoc]

end

end RingedSite.Hom
