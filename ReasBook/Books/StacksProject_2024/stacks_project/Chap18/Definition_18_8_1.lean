import Mathlib
import StacksProject_2024.Chap07.Lemma_7_44_2
import StacksProject_2024.Chap18.Definition_18_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

/- Domain-style sampling for Definition 18.8.1:
- primary domain: `2`-morphisms of ringed topoi;
- sampled owner API:
  `RingedSite.Hom`,
  `Functor.sheafPushforwardContinuous`,
  `sheaf_pushforward_forget`,
  `RingedSite.Hom.structureSheafMap`;
- owner abstraction: the natural transformation between the canonical set-valued direct-image
  functors attached to two ringed-site morphisms;
- primitive data: the two ringed-site morphisms together with that direct-image natural
  transformation;
- derived API: the induced component on the underlying set-valued structure sheaf and the
  resulting compatibility triangle, which under the bridge hypotheses of
  `RingedSite.Hom.toMorphismOfTopoi` becomes the underlying `2`-morphism of topoi.

Source/core/bridge triage:
- `source-facing`: a `2`-morphism between ringed-topos morphisms;
- `core/canonical`: the natural transformation between the canonical
  `sheafPushforwardContinuous` functors attached to `f.base` and `g.base`;
- `bridge/view`: passage from a topos `2`-morphism to its component on the underlying sheaf of
  `X.structureSheaf`, via `sheaf_pushforward_forget`.
-/

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}}

instance base_isContinuous (f : X ⟶ Y) : f.base.IsContinuous Y.siteTopology X.siteTopology :=
  f.isMorphismOfSites.toIsContinuous

/-- The underlying set-valued sheaf of the structure sheaf. -/
abbrev underlyingStructureSheaf (X : RingedSite.{u, v}) :
    Sheaf X.siteTopology (Type (max u v)) :=
  (sheafCompose X.siteTopology (forget RingCat.{max u v})).obj X.structureSheaf

/-- The forgotten direct image of `X.structureSheaf` agrees with the direct image of its
underlying sheaf of sets. -/
abbrev structureSheafPushforward_eq
    (f : X ⟶ Y) :
    (sheafCompose Y.siteTopology (forget RingCat.{max u v})).obj
        ((f.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) =
      (f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology).obj
        (underlyingStructureSheaf X) := by
  simpa [Functor.comp_obj, underlyingStructureSheaf] using
    congrArg
      (fun F ↦ F.obj X.structureSheaf)
      (show
        f.base.sheafPushforwardContinuous RingCat.{max u v} Y.siteTopology X.siteTopology ⋙
            sheafCompose Y.siteTopology (forget RingCat.{max u v}) =
          sheafCompose X.siteTopology (forget RingCat.{max u v}) ⋙
            f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology from
        sheaf_pushforward_forget Y.siteTopology X.siteTopology f.base)

/-- The pushforward-form map on underlying structure sheaves attached to a morphism of ringed
sites. -/
abbrev underlyingDirectImageMap
    (f : X ⟶ Y) :
    underlyingStructureSheaf Y ⟶
      (f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology).obj
        (underlyingStructureSheaf X) :=
  (sheafCompose Y.siteTopology (forget RingCat.{max u v})).map f.structureSheafMap ≫
    eqToHom (structureSheafPushforward_eq f)

section

variable (f : X ⟶ Y)
variable [PreservesFiniteLimits
  (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]

/-- The inverse-image-form map on underlying structure sheaves attached to a morphism of ringed
sites. This is the canonical bridge from the bundled owner `RingedSite.Hom` to the underlying
site-presented morphism of topoi `f.toMorphismOfTopoi`. -/
noncomputable abbrev underlyingInverseImageMap :
    (f.toMorphismOfTopoi⁻¹).obj (underlyingStructureSheaf Y) ⟶
      underlyingStructureSheaf X :=
  show
    (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology).obj
        (underlyingStructureSheaf Y) ⟶
      underlyingStructureSheaf X from
    ((f.base.sheafAdjunctionContinuous (Type (max u v)) Y.siteTopology X.siteTopology).homEquiv _ _).symm
      f.underlyingDirectImageMap

end

/-- The structure-sheaf component induced by an underlying topos `2`-morphism. -/
abbrev structureSheafComponent
    {f g : X ⟶ Y}
    (η :
      f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology ⟶
        g.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology) :
    (sheafCompose Y.siteTopology (forget RingCat.{max u v})).obj
        ((f.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) ⟶
      (sheafCompose Y.siteTopology (forget RingCat.{max u v})).obj
        ((g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) :=
  eqToHom (structureSheafPushforward_eq f) ≫
    η.app (underlyingStructureSheaf X) ≫
      eqToHom (structureSheafPushforward_eq g).symm

/-- Definition 18.8.1: a `2`-morphism from `f` to `g` is an underlying `2`-morphism of topoi
together with the compatibility saying that its component on the underlying structure sheaf makes
the usual triangle commute. -/
structure TwoMorphism (f g : X ⟶ Y) where
  /-- The underlying direct-image natural transformation on sheaves of types. -/
  hom :
    f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology ⟶
      g.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology
  /-- The compatibility condition `g^\sharp = t_{\mathcal O_X} \circ f^\sharp` on structure
  sheaves. -/
  comm :
    (sheafCompose Y.siteTopology (forget RingCat.{max u v})).map f.structureSheafMap ≫
      structureSheafComponent hom =
        (sheafCompose Y.siteTopology (forget RingCat.{max u v})).map g.structureSheafMap

/-- The component of a ringed-topos `2`-morphism on the underlying structure sheaf. -/
abbrev TwoMorphism.structureSheafHom
    {f g : X ⟶ Y} (η : TwoMorphism f g) :
    (sheafCompose Y.siteTopology (forget RingCat.{max u v})).obj
        ((f.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) ⟶
      (sheafCompose Y.siteTopology (forget RingCat.{max u v})).obj
        ((g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology X.siteTopology).obj X.structureSheaf) :=
  structureSheafComponent η.hom

/-- A `2`-morphism of ringed-topos data coerces to its underlying `2`-morphism of topoi. -/
instance {f g : X ⟶ Y} :
    CoeTC
      (TwoMorphism f g)
      (f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology ⟶
        g.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology) where
  coe η := η.hom

end RingedSite.Hom

namespace Functor

variable {C₁ C₂ : Type u} [Category.{v} C₁] [Category.{v} C₂]
variable {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}

/-- Forgetting a ring-sheaf transport along a continuous functor gives the corresponding transport
on the underlying set-valued structure sheaves. -/
abbrev pushforwardUnderlyingIso
    (u : C₁ ⥤ C₂) [u.IsContinuous J₁ J₂]
    {𝒪₂ : Sheaf J₂ RingCat.{max u v}} {𝒪₁ : Sheaf J₁ RingCat.{max u v}}
    (e : (u.sheafPushforwardContinuous RingCat.{max u v} J₁ J₂).obj 𝒪₂ ≅ 𝒪₁) :
    (u.sheafPushforwardContinuous (Type (max u v)) J₁ J₂).obj
        (RingedSite.Hom.underlyingStructureSheaf (RingedSite.ofRingSheaf J₂ 𝒪₂)) ≅
      RingedSite.Hom.underlyingStructureSheaf (RingedSite.ofRingSheaf J₁ 𝒪₁) :=
  (eqToIso (by
      simpa [Functor.comp_obj, RingedSite.Hom.underlyingStructureSheaf] using
        congrArg
          (fun F ↦ F.obj 𝒪₂)
          (show
            u.sheafPushforwardContinuous RingCat.{max u v} J₁ J₂ ⋙
                sheafCompose J₁ (forget RingCat.{max u v}) =
              sheafCompose J₂ (forget RingCat.{max u v}) ⋙
                u.sheafPushforwardContinuous (Type (max u v)) J₁ J₂ from
            sheaf_pushforward_forget J₁ J₂ u))).symm ≪≫
    (sheafCompose J₁ (forget RingCat.{max u v})).mapIso e

end Functor
