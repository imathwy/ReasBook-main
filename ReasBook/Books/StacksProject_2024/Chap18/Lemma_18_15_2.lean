import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap07.Proposition_7_44_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Lemma 18.15.2:
- primary domain: exactness criteria for direct-image functors on sheaves of abelian groups,
  together with site presentations of morphisms of topoi;
- sampled owner declarations:
  `Functor.sheafPushforwardContinuous`,
  `sheaf_pushforward_forget`,
  `MorphismOfTopoiIn.presentationFunctor_pushforwardIso`,
  `exactFunctor`;
- best owner abstraction:
  the canonical abelian direct-image owner for a presentation is
  `u.sheafPushforwardContinuous AddCommGrpCat J K`;
- primitive-vs-derived split:
  the primitive data are the continuous functor `u : C ⥤ D` and, for the bridge/view layer, a
  comparison isomorphism
  `ePush : u.sheafPushforwardContinuous (Type _) J K ≅ f.pushforward`
  presenting
  the set-valued direct image of a morphism of topoi `f`;
  preservation of epimorphisms, coequalizers, pushouts, and exactness are derived owner-level
  properties of the canonical pushforward functor, while the ambient abelian-sheaf
  infrastructure needed here lives only on the target site `K`;
- source/core/bridge triage:
  `source-facing`: the Stacks exactness criterion for the abelian direct image and its formulation
    for a morphism of topoi presented by a continuous functor;
  `core/canonical`: `exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat J K)`;
  `bridge/view`: the presentation isomorphism `ePush` on underlying sheaves of sets, together
    with the canonical forget-comparison from `sheaf_pushforward_forget`.

The previous public owner `MorphismOfTopoiIn.abelianPushforward` duplicated the existing Chapter 7
presentation machinery. This file now uses the canonical owner
`u.sheafPushforwardContinuous AddCommGrpCat J K` directly and keeps the morphism-of-topoi
formulation only as a bridge/view statement. -/

section ExactnessCriterion

variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]
variable [K.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]

/-- If the underlying set-valued direct image of the continuous presentation `u` preserves
epimorphisms, then the induced direct image on sheaves of abelian groups also preserves
epimorphisms. -/
theorem sheafPushforwardContinuous_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
    (hpush :
      (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K).PreservesEpimorphisms) :
    (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).PreservesEpimorphisms := sorry

/-- If the direct image on sheaves of abelian groups preserves epimorphisms, then it is exact. -/
theorem sheafPushforwardContinuous_exact_of_preservesEpimorphisms
    (hpush :
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).PreservesEpimorphisms) :
    exactFunctor
      (Sheaf K AddCommGrpCat.{max u₁ u₂ v})
      (Sheaf J AddCommGrpCat.{max u₁ u₂ v})
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K) := sorry

/-- Lemma 18.15.2, canonical-owner form: if the direct image on sheaves of abelian groups
preserves epimorphisms, or if its underlying set-valued direct image preserves epimorphisms,
coequalizers, or pushouts, then the abelian direct image is exact. -/
theorem sheafPushforwardContinuous_exact_of_preservesEpimorphisms_or_underlyingPreservesEpimorphisms_or_coequalizers_or_pushouts
    (h :
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).PreservesEpimorphisms ∨
        (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K).PreservesEpimorphisms ∨
          PreservesColimitsOfShape WalkingParallelPair
            (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K) ∨
            PreservesColimitsOfShape WalkingSpan
              (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K)) :
    exactFunctor
      (Sheaf K AddCommGrpCat.{max u₁ u₂ v})
      (Sheaf J AddCommGrpCat.{max u₁ u₂ v})
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K) := sorry

end ExactnessCriterion

section PresentedExactnessCriterion

variable (f : MorphismOfTopoiIn.{u₁, u₂, v, v, max u₁ u₂ v} J K)
variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]
variable [K.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]

-- Bridge/view input: `ePush` presents the underlying set-valued direct image of `f` by the
-- canonical owner `u.sheafPushforwardContinuous (Type _) J K`. Together with the Chapter 7
-- forget-comparison `sheaf_pushforward_forget`, this is the comparison data used to transport the
-- set-valued hypotheses on `f.pushforward` to the abelian pushforward owner.

/-- Lemma 18.15.2, bridge form: if `ePush` presents the underlying set-valued direct image of
`f : Sh(K) ⟶ Sh(J)` by the continuous functor `u`, and if `f _*` preserves epimorphisms,
coequalizers, or pushouts, then the induced direct image on abelian sheaves,
`u.sheafPushforwardContinuous AddCommGrpCat J K`, is exact. -/
theorem presented_sheafPushforwardContinuous_exact_of_pushforwardPreservesEpimorphisms_or_coequalizers_or_pushouts
    (ePush :
      u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K ≅
        f.pushforward)
    (h :
      f.pushforward.PreservesEpimorphisms ∨
        PreservesColimitsOfShape WalkingParallelPair f.pushforward ∨
          PreservesColimitsOfShape WalkingSpan f.pushforward) :
    exactFunctor
      (Sheaf K AddCommGrpCat.{max u₁ u₂ v})
      (Sheaf J AddCommGrpCat.{max u₁ u₂ v})
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K) := sorry

end PresentedExactnessCriterion

end CategoryTheory.Functor
