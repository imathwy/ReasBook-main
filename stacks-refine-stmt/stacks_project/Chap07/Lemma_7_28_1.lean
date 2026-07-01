import Mathlib
import stacks_project.Chap07.Definition_7_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w u₁ u₂ v₁ v₂ v₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.28.1:
- primary domain: localized morphisms of sites on slice categories and the induced comparison of
  sheaf pushforwards;
- sampled owner API:
  `Over.post`,
  `Functor.IsContinuous`,
  `RepresentablyFlat`,
  `IsMorphismOfSites`,
  `GrothendieckTopology.overPullback`,
  `Functor.sheafPushforwardContinuousComp`,
  `Functor.sheafPushforwardContinuousComp'`;
- source/core/bridge triage:
  `source-facing`: the localized morphism of sites `(D/V, JD.over V) ⟶ (C/u(V), JC.over (u.obj V))`
  induced by `u`, together with the comparison square relating localization and direct image;
  `core/canonical`: the owner classes `Functor.IsContinuous`, `RepresentablyFlat`,
  `IsMorphismOfSites`, and the sheaf pushforward comparison theorems
  `Functor.sheafPushforwardContinuousComp` and
  `Functor.sheafPushforwardContinuousComp'`;
  `bridge/view`: the slice specialization of those owner declarations.

Primitive data are only the functor `u`, the object `V`, and the site structures. The localized
continuity/flatness/site-morphism facts are source-facing bridge statements on the slice sites,
while the sheaf-level square is derived API from the canonical composition owners
`sheafPushforwardContinuousComp`/`sheafPushforwardContinuousComp'`. The file should therefore keep
only the slice bridge instances and express the comparison isomorphism directly in terms of those
owner theorems, rather than assembling a parallel comparison by hand.
-/

-- Proof sketch: a covering sieve on `Over (u.obj V)` is covering exactly when its image in `C`
-- is covering. Pulling such a sieve back along `Over.post u` corresponds to pulling the
-- associated sieve back along `u`, so continuity of `u` transfers directly to the slice site.
/-- The induced slice functor of a continuous site functor is again continuous. -/
instance overPost_isContinuous
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D) :
    (Over.post u).IsContinuous (JD.over V) (JC.over (u.obj V)) := sorry

-- Proof sketch: representable flatness of `u` controls the cofilteredness of structured-arrow
-- categories over objects of `C`. Passing to slices replaces an object of `C/u(V)` by an arrow
-- into `u(V)`, and the relevant structured-arrow category is the localized version of the one for
-- `u`; hence cofilteredness descends to `Over.post u`.
/-- If `u` is representably flat, then the induced slice functor `Over.post u` is representably
flat. -/
instance overPost_representablyFlat
    (u : D ⥤ C) [RepresentablyFlat u] (V : D) :
    RepresentablyFlat (show Over V ⥤ Over (u.obj V) from Over.post u) := sorry

-- Proof sketch: a morphism of sites is, by definition, a continuous functor whose inverse-image
-- functor on sheaves is exact. Localizing at `V` and `u.obj V` preserves this structure, so the
-- induced slice functor again defines a morphism of sites.
/-- The slice functor induced by a morphism of sites is again a morphism of sites on the localized
sites. -/
instance overPost_isMorphismOfSites
    (u : D ⥤ C) [IsMorphismOfSites JD JC u] (V : D) :
    IsMorphismOfSites (JD.over V) (JC.over (u.obj V))
      (show Over V ⥤ Over (u.obj V) from Over.post u) :=
  inferInstance

/- Lemma 7.28.1: for a continuous functor `u`, the localized square of topoi is the direct slice
specialization of the canonical owner theorem `Functor.sheafPushforwardContinuousComp'` applied to
the definitional equality `Over.post u ⋙ Over.forget (u.obj V) = Over.forget V ⋙ u`.
When `u` presents a morphism of sites, this is the library-facing form of the identity
`f'_* j_U^{-1} = j_V^{-1} f_*`. -/
#check
  (fun
    (u : D ⥤ C)
    [u.IsContinuous JD JC]
    (V : D) (A : Type w) [Category.{v₃} A] ↦
      by
        letI : Functor.IsContinuous (Over.forget V ⋙ u) (JD.over V) JC :=
          Functor.isContinuous_comp (Over.forget V) u (JD.over V) JD JC
        exact
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (by rfl) : Over.post u ⋙ Over.forget (u.obj V) ≅ Over.forget V ⋙ u)
            A (JD.over V) (JC.over (u.obj V)) JC :
          JC.overPullback A (u.obj V) ⋙
              (Over.post u).sheafPushforwardContinuous A (JD.over V) (JC.over (u.obj V)) ≅
            u.sheafPushforwardContinuous A JD JC ⋙ JD.overPullback A V))

end CategoryTheory
