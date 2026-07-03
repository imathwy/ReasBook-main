import Mathlib
import StacksProject_2024.Chap07.Lemma_7_44_2
import StacksProject_2024.Chap18.Definition_18_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

/- Domain-style sampling for Definition 18.8.1:
- primary domain: `2`-morphisms of ringed topoi;
- sampled owner API:
  `RingedSite.Hom`,
  `Functor.sheafPushforwardContinuous`,
  `sheaf_pushforward_forget`,
  `RingedSite.Hom.ringPushforward`,
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

/-- The underlying set-valued sheaf of the structure sheaf. -/
abbrev underlyingStructureSheaf (X : RingedSite.{u, v}) :
    Sheaf X.siteTopology (Type (max u v)) :=
  (sheafCompose X.siteTopology (forget RingCat.{max u v})).obj X.structureSheaf

/-- The canonical direct-image functor on sheaves of types attached to a morphism of ringed
sites. -/
abbrev toposPushforward (f : X ⟶ Y) :
    Sheaf X.siteTopology (Type (max u v)) ⥤ Sheaf Y.siteTopology (Type (max u v)) :=
  f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology

/-- Forgetting the ring structure commutes with the canonical ring-valued direct image attached to
`f`, after identifying the resulting set-valued direct image with `toposPushforward f`. -/
theorem ringPushforwardCompForget_eq
    (f : X ⟶ Y) :
    f.ringPushforward ⋙ sheafCompose Y.siteTopology (forget RingCat.{max u v}) =
      sheafCompose X.siteTopology (forget RingCat.{max u v}) ⋙ toposPushforward f := by
  simpa [RingedSite.Hom.ringPushforward, toposPushforward] using
    (show
      f.base.sheafPushforwardContinuous RingCat.{max u v} Y.siteTopology X.siteTopology ⋙
          sheafCompose Y.siteTopology (forget RingCat.{max u v}) =
        sheafCompose X.siteTopology (forget RingCat.{max u v}) ⋙
          f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology from
      sheaf_pushforward_forget Y.siteTopology X.siteTopology f.base)

/-- The forgotten direct image of `X.structureSheaf` agrees with the direct image of its
underlying sheaf of sets. -/
abbrev structureSheafPushforward_eq
    (f : X ⟶ Y) :
    (sheafCompose Y.siteTopology (forget RingCat.{max u v})).obj
        (f.ringPushforward.obj X.structureSheaf) =
      (toposPushforward f).obj (underlyingStructureSheaf X) := by
  simpa [Functor.comp_obj, underlyingStructureSheaf] using
    congrArg (fun F ↦ F.obj X.structureSheaf) (ringPushforwardCompForget_eq f)

/-- The structure-sheaf component induced by an underlying topos `2`-morphism. -/
abbrev structureSheafComponent
    {f g : X ⟶ Y} (η : toposPushforward f ⟶ toposPushforward g) :
    (sheafCompose Y.siteTopology (forget RingCat.{max u v})).obj
        (f.ringPushforward.obj X.structureSheaf) ⟶
      (sheafCompose Y.siteTopology (forget RingCat.{max u v})).obj
        (g.ringPushforward.obj X.structureSheaf) :=
  eqToHom (structureSheafPushforward_eq f) ≫
    η.app (underlyingStructureSheaf X) ≫
      eqToHom (structureSheafPushforward_eq g).symm

/-- Definition 18.8.1: a `2`-morphism from `f` to `g` is an underlying `2`-morphism of topoi
together with the compatibility saying that its component on the underlying structure sheaf makes
the usual triangle commute. -/
structure TwoMorphism (f g : X ⟶ Y) where
  /-- The underlying direct-image natural transformation on sheaves of types. -/
  hom : toposPushforward f ⟶ toposPushforward g
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
        (f.ringPushforward.obj X.structureSheaf) ⟶
      (sheafCompose Y.siteTopology (forget RingCat.{max u v})).obj
        (g.ringPushforward.obj X.structureSheaf) :=
  structureSheafComponent η.hom

/-- A `2`-morphism of ringed-topos data coerces to its underlying `2`-morphism of topoi. -/
instance {f g : X ⟶ Y} :
    CoeTC (TwoMorphism f g) (toposPushforward f ⟶ toposPushforward g) where
  coe η := η.hom

end RingedSite.Hom
