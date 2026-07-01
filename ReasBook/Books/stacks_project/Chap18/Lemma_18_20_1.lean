import Mathlib
import stacks_project.Chap07.Lemma_7_28_1
import stacks_project.Chap18.Definition_18_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace RingedSite

namespace Hom

variable {X Y : RingedSite.{u, v}}

private instance overPost_isContinuous (f : RingedSite.Hom X Y) (V : Y) :
    (Over.post f.base).IsContinuous (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V)) :=
  CategoryTheory.overPost_isContinuous f.base V

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
    (Over.post f.base).sheafPushforwardContinuousComp (Over.forget (f.base.obj V))
        RingCat.{max u v} (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
        X.siteTopology ≪≫
      eqToIso (by rfl) ≪≫
      ((Over.forget V).sheafPushforwardContinuousComp f.base
        RingCat.{max u v} (Y.siteTopology.over V) Y.siteTopology X.siteTopology).symm
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

-- Proof sketch: the localized morphism was defined by giving its `base` field explicitly as
-- `Over.post f.base`, so this is the corresponding definitional identification.
/-- The underlying morphism of sites of the localized morphism is the slice functor
`Over.post f.base`. -/
theorem localization_base (f : RingedSite.Hom X Y) (V : Y) :
    (localization f V).base = Over.post f.base := rfl

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
      (Over.post f.base).sheafPushforwardContinuousComp (Over.forget (f.base.obj V))
          (Type (max u v)) (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
          X.siteTopology ≪≫
        eqToIso (by rfl) ≪≫
        ((Over.forget V).sheafPushforwardContinuousComp f.base
          (Type (max u v)) (Y.siteTopology.over V) Y.siteTopology X.siteTopology).symm)

end Hom
end RingedSite
