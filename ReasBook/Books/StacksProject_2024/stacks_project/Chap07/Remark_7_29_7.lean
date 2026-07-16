import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_29_5
import StacksProject_2024.stacks_project.Chap07.Lemma_7_29_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Functor.IsDenseSubsite
open scoped MorphismOfTopoiIn

universe u₁ u₂ u₃ uI uG v₁ v₂ v₃ w

namespace CategoryTheory

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {I : Type uI} {G : Type uG}
variable [HasWeakSheafify J (Type (max u₁ v₁))]
variable [HasWeakSheafify K (Type (max u₂ v₂))]

namespace Functor

variable {C' : Type u₃} [Category.{v₃} C']

/-- The canonical transport of `Type w`-valued sheaves across a dense subsite, obtained by first
raising universes with `sheafCompose J uliftFunctor` and then applying the dense-subsite
equivalence. -/
abbrev denseSubsiteTypeTransport
    (v : C ⥤ C') (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    [v.IsDenseSubsite J J'] :
    Sheaf J (Type w) ⥤ Sheaf J' (Type (max w u₁ u₃ v₁ v₃)) :=
  sheafCompose J uliftFunctor.{max w u₁ u₃ v₁ v₃, w} ⋙
    (sheafEquiv J J' v (Type (max w u₁ u₃ v₁ v₃))).functor

end Functor

/- Domain-style sampling for Remark 7.29.7:
- primary domain: reductions of morphisms of topoi to morphisms of sites after replacing the two
  presenting sites by subcanonical sites with finite limits;
- sampled owner declarations:
  `Functor.IsDenseSubsite`,
  `MorphismOfTopoiIn`,
  `CatCommSq`,
  `Functor.IsDenseSubsite.sheafEquiv`,
  `CategoryTheory.sheafCompose`,
  `Functor.sheafPullback`,
  `Functor.morphismOfTopoiInOfContinuous`;
- best owner abstraction: the replacement-site functors should be recorded through the canonical
  dense-subsite owner `IsDenseSubsite`; the family transport should appear on the public theorem
  surface through the canonical universe-raising transport
  `Functor.denseSubsiteTypeTransport`, whose owner is still the dense-subsite equivalence
  `sheafEquiv`, rather than through extra existentially chosen equivalence data; the lower
  horizontal factorization should first be recorded at the source-facing owner level by a
  morphism of topoi `g : MorphismOfTopoiIn K' J'` together with the explicit relation
  `g _* = u.sheafPushforwardContinuous (Type w) K' J'` saying that `g` is presented by the site
  morphism `u` on direct images, while the stronger identification
  `g = u.morphismOfTopoiInOfContinuous K' J'` belongs only to a companion bridge theorem;
- primitive data: the replacement sites `(C', J')`, `(D', K')`, the dense-subsite functors from
  the original sites, the site morphism `u : D' ⥤ C'`, and the lower morphism of topoi
  `g : MorphismOfTopoiIn K' J'`, its direct-image identification with
  `u.sheafPushforwardContinuous (Type w) K' J'`, and the comparison square `sq : CatCommSq ...`;
- derived API: subcanonicality, finite limits, the canonical family transport given by
  `Functor.denseSubsiteTypeTransport`, and, in the companion theorem only, the canonical lower
  inverse-image owner `u.sheafPullback (Type w) K' J'`, which under the standard realization
  hypotheses is the inverse image of `u.morphismOfTopoiInOfContinuous`;
- ambient construction hypotheses inherited from the owner layer: weak sheafification on the
  original sites `J` and `K`, exactly as required by the replacement-site theorem
  `exists_representable_family_site_presentation` from Lemma `7.29.5`.

Source/core/bridge triage:
- `source-facing`: the existence of replacement sites on which the chosen families become
  representable and the given morphism of topoi factors through a lower morphism of topoi induced
  by a site morphism satisfying the source hypotheses from Proposition `7.14.7`;
- `core/canonical`: `Functor.IsDenseSubsite`, `sheafEquiv`, `IsMorphismOfSites`,
  `MorphismOfTopoiIn`, `CatCommSq`, and `sheafCompose`;
- `bridge/view`: the universe-raising transport functors on sheaf categories, implemented
  canonically by the standard bridge `sheafCompose _ uliftFunctor` followed by `sheafEquiv`,
  together with the weak sheafification and Kan-extension hypotheses used only to identify the
  lower morphism canonically with `u.morphismOfTopoiInOfContinuous`, whose left exactness is
  already derived from `IsMorphismOfSites` through `RepresentablyFlat`.
-/

-- Proof sketch: apply Lemma `7.29.5` separately to the two chosen families to replace both sites
-- by subcanonical sites with finite limits and dense-subsite comparison functors. Apply
-- Lemma `7.29.6` to the transported morphism of topoi between the replacement sites to obtain the
-- site morphism `u : D' ⥤ C'`, the lower morphism of topoi `g : MorphismOfTopoiIn K' J'`, its
-- direct-image identification with `u.sheafPushforwardContinuous (Type w) K' J'`, and the
-- canonical comparison square `sq : CatCommSq ...`. The family transport is recorded on the
-- theorem surface by the canonical dense-subsite transport
-- `Functor.denseSubsiteTypeTransport`, rather than by separate existential equivalence data.
/-- Remark 7.29.7: for a morphism of topoi `f : Sh(J) ⟶ Sh(K)` and chosen families of set-valued
sheaves `ℱ` on `Sh(J)` and `𝒢` on `Sh(K)`, there exist subcanonical replacement sites
`(C', J')` and `(D', K')` with finite limits, dense-subsite comparison functors from the original
sites, such that the canonical dense-subsite transports carry the chosen families to representable
sheaves on the replacement sites, and a site morphism `u : D' ⥤ C'` satisfying the pullback and
terminal-object hypotheses of Proposition `7.14.7`, together with a lower morphism of topoi
`g : Sh(J') ⟶ Sh(K')` whose direct image is the canonical sheaf pushforward induced by `u` and
whose inverse-image functor fits into the canonical factorization square with the two
dense-subsite direct-image functors. -/
theorem exists_topos_morphism_reduction
    (f : MorphismOfTopoiIn K J)
    (ℱ : I → Sheaf J (Type w))
    (𝒢 : G → Sheaf K (Type w)) :
    ∃ (C' : Type u₃) (_ : Category.{v₃} C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J'),
      ∃ (D' : Type u₃) (_ : Category.{v₃} D') (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite K K'),
        ∃ (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D')))
          (g : MorphismOfTopoiIn K' J')
          (_ : g _* = u.sheafPushforwardContinuous (Type w) K' J')
          (sq : CatCommSq
            (targetFunctor.sheafPushforwardContinuous (Type w) K K')
            (g⁻¹)
            (f⁻¹)
            (sourceFunctor.sheafPushforwardContinuous (Type w) J J')),
          (∀ i : I, (((sourceFunctor.denseSubsiteTypeTransport J J').obj (ℱ i)).obj).IsRepresentable) ∧
            ∀ j : G, (((targetFunctor.denseSubsiteTypeTransport K K').obj (𝒢 j)).obj).IsRepresentable := by
  sorry

-- Proof sketch: combine the source-facing theorem above with the canonical-identification bridge
-- from Lemma `7.29.6`, so that the same lower factorization square is realized by
-- the canonical inverse-image owner `u.sheafPullback (Type w) K' J'`; under the standard
-- weak-sheafification and Kan-extension hypotheses this is the inverse image of
-- `u.morphismOfTopoiInOfContinuous K' J'`, and its left exactness remains derived from
-- `IsMorphismOfSites K' J' u` rather than public existential data. The
-- source and target family transport remain recorded through the canonical
-- `Functor.denseSubsiteTypeTransport`, rather than by exposing extra chosen
-- equivalence data.
/-- Canonical-identification companion to Remark 7.29.7: after adding the standard realization
hypotheses needed to form the canonical inverse-image functor attached to the site morphism
`u : D' ⥤ C'`, the lower horizontal edge in the factorization square can be chosen canonically as
`u.sheafPullback (Type w) K' J'`; under the usual realization of a morphism of topoi this is the
inverse-image functor of `u.morphismOfTopoiInOfContinuous K' J'`, and its left exactness remains
derived API of `IsMorphismOfSites K' J' u`. -/
theorem exists_topos_morphism_reduction_canonical
    (f : MorphismOfTopoiIn K J)
    (ℱ : I → Sheaf J (Type w))
    (𝒢 : G → Sheaf K (Type w)) :
    ∃ (C' : Type u₃) (_ : Category.{v₃} C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J'),
      ∃ (D' : Type u₃) (_ : Category.{v₃} D') (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite K K'),
        ∃ (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : HasWeakSheafify J' (Type w))
          (_ : ∀ P : D'ᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P)
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D')))
          (sq : CatCommSq
            (targetFunctor.sheafPushforwardContinuous (Type w) K K')
            (u.sheafPullback (Type w) K' J')
            (f⁻¹)
            (sourceFunctor.sheafPushforwardContinuous (Type w) J J')),
          (∀ i : I, (((sourceFunctor.denseSubsiteTypeTransport J J').obj (ℱ i)).obj).IsRepresentable) ∧
            ∀ j : G, (((targetFunctor.denseSubsiteTypeTransport K K').obj (𝒢 j)).obj).IsRepresentable := by
  sorry

end

end CategoryTheory
