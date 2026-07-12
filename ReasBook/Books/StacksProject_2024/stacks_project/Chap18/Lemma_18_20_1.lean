import Mathlib
import StacksProject_2024.Chap07.Lemma_7_28_1
import StacksProject_2024.Chap18.Definition_18_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace RingedSite

namespace Hom

variable {X Y : RingedSite.{u, v}}

/- Domain-style sampling for Lemma 18.20.1:
- primary domain: localization of a morphism of ringed sites to slice ringed sites;
- sampled owner declarations:
  `RingedSite.localization`,
  `CategoryTheory.overPost_isMorphismOfSites`,
  `Functor.sheafPushforwardContinuousComp'`,
  `CategoryTheory.representable_localization_comparison_agrees_with_localized_pullback`;
- best owner abstraction: the source-facing owner is the localized ringed-site morphism
  `RingedSite.Hom.localization`; its primitive data are the slice functor `Over.post f.base` and
  the induced localized structure-sheaf map, while the comparison of underlying topoi is derived
  API from the canonical Chapter 7 owner `Functor.sheafPushforwardContinuousComp'`;
- source/core/bridge triage:
  `source-facing`: the localized ringed-site morphism `RingedSite.Hom.localization`;
  `core/canonical`: `RingedSite.localization`, `CategoryTheory.overPost_isMorphismOfSites`, and
    `Functor.sheafPushforwardContinuousComp'`;
  `bridge/view`: the ringed structure-sheaf map obtained by transporting `f.structureSheafMap`
    across the canonical slice pushforward comparison.
-/

private instance overPost_isContinuous (f : RingedSite.Hom X Y) (V : Y) :
    (Over.post f.base).IsContinuous (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V)) :=
  CategoryTheory.overPost_isContinuous f.base V

private instance overForgetComp_isContinuous (f : RingedSite.Hom X Y) (V : Y) :
    (Over.forget V ⋙ f.base).IsContinuous (Y.siteTopology.over V) X.siteTopology :=
  Functor.isContinuous_comp (Over.forget V) f.base (Y.siteTopology.over V) Y.siteTopology
    X.siteTopology

private instance overPost_isMorphismOfSites (f : RingedSite.Hom X Y) (V : Y) :
    IsMorphismOfSites
      (Y.localization V).siteTopology
      (X.localization (f.base.obj V)).siteTopology
      (Over.post f.base) := by
  simpa [RingedSite.localization] using
    (CategoryTheory.overPost_isMorphismOfSites f.base V)

/-- The structure-sheaf map induced on the localized sites by a morphism of ringed sites. -/
private noncomputable def localizationStructureSheafMap (f : RingedSite.Hom X Y) (V : Y) :
    Y.structureSheaf.over V ⟶
      (((Over.post f.base).sheafPushforwardContinuous RingCat.{max u v}
          (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))).obj
        (X.structureSheaf.over (f.base.obj V))) :=
  let e :=
    Functor.sheafPushforwardContinuousComp'
      (eqToIso (by rfl) : Over.post f.base ⋙ Over.forget (f.base.obj V) ≅ Over.forget V ⋙ f.base)
      RingCat.{max u v} (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
      X.siteTopology
  (Y.siteTopology.overPullback RingCat.{max u v} V).map f.structureSheafMap ≫
    (e.symm.app X.structureSheaf).hom

/-- Lemma 18.20.1: localizing a morphism of ringed sites
`f : (\mathcal C, \mathcal O) \to (\mathcal D, \mathcal O')` at an object `V : \mathcal D`,
with `U = u(V)` for the underlying continuous functor `u`, gives the canonical morphism of
ringed sites `f' : (\mathcal C/U, \mathcal O_U) \to (\mathcal D/V, \mathcal O'_V)`. -/
noncomputable def localization (f : RingedSite.Hom X Y) (V : Y) :
    RingedSite.Hom (X.localization (f.base.obj V)) (Y.localization V) where
  base := Over.post f.base
  isMorphismOfSites := inferInstance
  structureSheafMap := localizationStructureSheafMap f V

instance localization_isContinuous (f : RingedSite.Hom X Y) (V : Y) :
    (localization f V).base.IsContinuous
      (Y.localization V).siteTopology
      (X.localization (f.base.obj V)).siteTopology :=
  (localization f V).isMorphismOfSites.toIsContinuous

instance localization_sheafPullback_preservesFiniteLimits
    (f : RingedSite.Hom X Y) (V : Y)
    [PreservesFiniteLimits
      ((Over.post f.base).sheafPullback
        (Type (max u v))
        (Y.siteTopology.over V)
        (X.siteTopology.over (f.base.obj V)))] :
    PreservesFiniteLimits
      ((localization f V).base.sheafPullback
        (Type (max u v))
        (Y.localization V).siteTopology
        (X.localization (f.base.obj V)).siteTopology) := by
  simpa [localization, RingedSite.localization] using
    (show PreservesFiniteLimits
      ((Over.post f.base).sheafPullback
        (Type (max u v))
        (Y.siteTopology.over V)
        (X.siteTopology.over (f.base.obj V))) from inferInstance)

-- Proof sketch: the localized morphism was defined by giving its `base` field explicitly as
-- `Over.post f.base`, so this is the corresponding definitional identification.
/-- The underlying morphism of sites of the localized morphism is the slice functor
`Over.post f.base`. -/
theorem localization_base (f : RingedSite.Hom X Y) (V : Y) :
    (localization f V).base = Over.post f.base := rfl

-- Proof sketch: this is the defining formula of `localizationStructureSheafMap`, now expressed
-- through the canonical slice pushforward comparison owner `Functor.sheafPushforwardContinuousComp'`.
/-- The structure-sheaf map of the localized morphism is obtained by restricting
`f.structureSheafMap` and transporting it across the canonical slice pushforward comparison. -/
theorem localization_structureSheafMap_eq (f : RingedSite.Hom X Y) (V : Y) :
    (localization f V).structureSheafMap =
      let e :=
        Functor.sheafPushforwardContinuousComp'
          (eqToIso (by rfl) :
            Over.post f.base ⋙ Over.forget (f.base.obj V) ≅ Over.forget V ⋙ f.base)
          RingCat.{max u v} (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
          X.siteTopology
      (Y.siteTopology.overPullback RingCat.{max u v} V).map f.structureSheafMap ≫
        (e.symm.app X.structureSheaf).hom := rfl

/- The underlying localized square of topoi for a morphism of ringed sites is the canonical
comparison isomorphism from Lemma `7.28.1`, expressing `f'_* j_U^{-1} \cong j_V^{-1} f_*`. -/
#check
  (fun (f : RingedSite.Hom X Y) (V : Y) ↦
    show
      X.siteTopology.overPullback (Type (max u v)) (f.base.obj V) ⋙
          (Over.post f.base).sheafPushforwardContinuous
            (Type (max u v)) (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V)) ≅
        f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology ⋙
          Y.siteTopology.overPullback (Type (max u v)) V from
      Functor.sheafPushforwardContinuousComp'
        (eqToIso (by rfl) : Over.post f.base ⋙ Over.forget (f.base.obj V) ≅ Over.forget V ⋙ f.base)
        (Type (max u v)) (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
        X.siteTopology)

end Hom
end RingedSite
