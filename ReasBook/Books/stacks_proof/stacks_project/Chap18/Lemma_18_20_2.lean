import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap07.Lemma_7_25_8
import stacks_proof.stacks_project.Chap07.Lemma_7_27_5
import stacks_proof.stacks_project.Chap07.Lemma_7_28_1
import stacks_proof.stacks_project.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace RingedSite
namespace Hom

variable {X Y : RingedSite.{u, v}}

/- Domain-style sampling for Lemma 18.20.2:
- primary domain: localized inverse-image functors on slice sites for a morphism of sites,
  specialized to a morphism of ringed sites through its underlying functor `f.base`;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `CategoryTheory.relocalization_inverse_image_square_iso`,
  `Over.post`,
  `GrothendieckTopology.overMapPullback`;
- best owner abstraction: the Chapter 7 localized slice-site comparison machinery, namely the
  localized square of Lemma `7.28.1` together with the relocalization owners of
  Lemma `7.25.8` and Lemma `7.27.5`, specialized to `f.base`;
- primitive data: the underlying site functor `f.base`, the map `c : U ⟶ f.base.obj V`, and in
  part `(2)` the commutative square `c' ≫ f.base.map b = a ≫ c`;
- derived API: the ringed-site phrasing of Lemma 18.20.2, obtained by specializing those
  site-level owner comparisons to the morphism of sites underlying `f`.

Source/core/bridge triage:
- `source-facing`: the localized factorization and naturality statements for a morphism of ringed
  sites;
- `core/canonical`: the Chapter 7 owner comparisons
  `Functor.sheafPushforwardContinuousComp'`,
  and `CategoryTheory.relocalization_inverse_image_square_iso`;
- `bridge/view`: the specialization from a ringed-site morphism to its underlying site functor
  `f.base`.

This file is therefore a bridge/view file: it should reuse the Chapter 7 owners directly rather
than repackage them as existential comparison morphisms or parallel local comparison isomorphisms.
-/

/- Lemma 18.20.2 is a ringed-site specialization of the Chapter 7 slice-site comparison
machinery. Its public surface should therefore recall those owner declarations directly rather than
introduce new Chapter 18 wrappers. -/
recall Functor.sheafPushforwardContinuousComp'
recall relocalization_inverse_image_square_iso

section

variable (f : RingedSite.Hom X Y)
variable {V : Y} {U : X} (c : U ⟶ f.base.obj V)

/- Lemma 18.20.2 (1): the localized square for `f.base` is the Chapter 7 owner comparison from
Lemma `7.28.1`, specialized to the morphism of sites underlying `f`. -/
#check
  (fun (f : RingedSite.Hom X Y) (V : Y) ↦
    by
      letI :
          Functor.IsContinuous (Over.forget V ⋙ f.base) (Y.siteTopology.over V) X.siteTopology :=
        Functor.isContinuous_comp
          (Over.forget V) f.base (Y.siteTopology.over V) Y.siteTopology X.siteTopology
      exact
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (by rfl) :
            Over.post f.base ⋙ Over.forget (f.base.obj V) ≅ Over.forget V ⋙ f.base)
          (Type (max u v)) (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
          X.siteTopology :
            X.siteTopology.overPullback (Type (max u v)) (f.base.obj V) ⋙
                (Over.post f.base).sheafPushforwardContinuous (Type (max u v))
                  (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V)) ≅
              f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology ⋙
                Y.siteTopology.overPullback (Type (max u v)) V))

/- The relocalization factor `j_{u(V)}^{-1} ⋙ j_c^{-1} ≅ j_U^{-1}` is the direct specialization of
Lemma `7.25.8` to the map `c : U ⟶ f.base.obj V`. -/
#check
  (Functor.sheafPushforwardContinuousComp' (Over.mapForget c)
    (Type (max u v)) (X.siteTopology.over U) (X.siteTopology.over (f.base.obj V))
    X.siteTopology :
      X.siteTopology.overPullback (Type (max u v)) (f.base.obj V) ⋙
          X.siteTopology.overMapPullback (Type (max u v)) c ≅
        X.siteTopology.overPullback (Type (max u v)) U)

end

section

variable (f : RingedSite.Hom X Y)
variable {V V' : Y} {U U' : X} (c : U ⟶ f.base.obj V) (b : V' ⟶ V) (a : U' ⟶ U)
variable (c' : U' ⟶ f.base.obj V') (hcomm : c' ≫ f.base.map b = a ≫ c)

/- Lemma 18.20.2 (2): the relocalization naturality square on the `X`-side is exactly the
canonical Chapter 7 square comparison specialized to
`a : U' ⟶ U`, `c' : U' ⟶ f.base.obj V'`, `c : U ⟶ f.base.obj V`, and `f.base.map b`. -/
#check
  (relocalization_inverse_image_square_iso
    X.siteTopology a c' c (f.base.map b) hcomm.symm :
      X.siteTopology.overMapPullback (Type (max u v)) c ⋙
          X.siteTopology.overMapPullback (Type (max u v)) a ≅
        X.siteTopology.overMapPullback (Type (max u v)) (f.base.map b) ⋙
          X.siteTopology.overMapPullback (Type (max u v)) c')

end

end Hom
end RingedSite
