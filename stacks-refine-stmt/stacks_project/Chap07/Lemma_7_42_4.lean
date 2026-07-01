import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Tactic.Recall
import stacks_project.Chap07.Definition_7_42_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

section

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [u.IsContinuous J K] [u.IsAlmostCocontinuous J K]

/- Domain-style sampling for Lemma 7.42.4:
- primary domain: sheafification comparison for inverse image along continuous, almost
  cocontinuous functors of sites;
- sampled owner declarations:
  `Functor.IsAlmostCocontinuous`,
  `GrothendieckTopology.IsSheafTheoreticallyEmpty`,
  `GrothendieckTopology.sheafTheoreticallyEmpty_iff_forall_unique_sections`,
  `Functor.pushforwardContinuousSheafificationCompatibility_hom_app_hom`;
- best owner abstraction: the canonical comparison morphism
  `sheafifyLift J (whiskerLeft u.op <| toSheafify K G) ...`, determined directly by the weak
  sheafification universal property;
- primitive data: the site functor `u`, the topologies `J` and `K`, weak sheafification on both
  sites, the continuity and almost-cocontinuity hypotheses, the presheaf `G`, and the
  singleton-over-sheaf-theoretically-empty hypothesis on `G`;
- derived API: under the stronger cocontinuity hypothesis, the identification of the source
  comparison morphism with the `hom` of the `G`-component of the canonical mathlib
  compatibility isomorphism.

Source/core/bridge triage:
- `source-facing`: the Stacks Project theorem that the comparison morphism
  `(uᵖ G)^# ⟶ uᵖ (G^#)` is an isomorphism under continuity, almost cocontinuity, and the
  singleton condition on sheaf-theoretically empty objects;
- `core/canonical`: the canonical comparison morphism produced by `sheafifyLift`;
- `bridge/view`: when `u` is cocontinuous, the theorem
  `pushforwardContinuousSheafificationCompatibility_hom_app_hom` identifies that source-facing
  comparison morphism with the component of the canonical mathlib compatibility isomorphism.

The previous refinement failed by replacing the source lemma with a stronger upstream owner. This
file instead keeps the source-facing isomorphism statement as the public entry; the mathlib
compatibility isomorphism appears only as a stronger-assumption bridge below. -/

-- Proof sketch: use almost cocontinuity to pull back a covering of `u(U)` to a covering of `U`
-- whose arrows either land in sheaf-theoretically empty objects or factor through the original
-- cover. The singleton hypothesis on `G` handles the empty-object branch, and the sheaf
-- conditions on `G^#` and `(uᵖ G)^#` then identify matching sections on the pulled-back cover.
-- This gives both injectivity and surjectivity of the canonical comparison morphism, hence it is
-- an isomorphism.
/-- Lemma 7.42.4: if `u : (C, J) ⥤ (D, K)` is continuous and almost cocontinuous, and if the
presheaf `G` is singleton-valued on every sheaf-theoretically empty object of `(D, K)`, then the
canonical comparison morphism `(uᵖ G)^# ⟶ uᵖ (G^#)` is an isomorphism. -/
theorem pushforwardContinuousSheafificationComparison_isIso_of_isAlmostCocontinuous
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    IsIso
      (sheafifyLift J (whiskerLeft u.op <| toSheafify K G)
        ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj G).property) := by
  sorry

section CocontinuousBridge

variable [u.IsCocontinuous J K]

/- Companion bridge: under the stronger cocontinuity hypothesis, the source comparison morphism is
exactly the `hom` of the `G`-component of the canonical mathlib compatibility isomorphism
`u.pushforwardContinuousSheafificationCompatibility (Type w) J K`. -/
recall pushforwardContinuousSheafificationCompatibility_hom_app_hom

end CocontinuousBridge

end

end CategoryTheory.Functor
