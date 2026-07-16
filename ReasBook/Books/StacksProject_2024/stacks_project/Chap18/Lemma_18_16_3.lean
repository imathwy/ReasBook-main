import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.stacks_project.Chap07.Lemma_7_5_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_8_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Lemma 18.16.3:
- primary domain: exactness of the abelian lower-shriek / sheaf-pullback functor attached to a
  continuous functor of sites;
- sampled owner declarations:
  `Functor.sheafPullback`,
  `Functor.sheafAdjunctionContinuous`,
  `CategoryTheory.Functor.sheafPullback_addCommGrp_exact_of_isContinuous_representablyFlat`,
  `CategoryTheory.Limits.hasFiniteConnectedLimits_of_hasEqualizers_and_pullbacks`;
- best owner abstraction: the canonical abelian-sheaf pullback owner
  `u.sheafPullback AddCommGrpCat J K`;
- primitive data: the site functor `u`, continuity, and the source-facing pullback/equalizer
  hypotheses on `C` and `u`; exactness is derived API;
- source/core/bridge triage:
  `source-facing`: the textbook pullback/equalizer criterion ensuring exactness of `g_!`;
  `core/canonical`: `u.sheafPullback AddCommGrpCat J K` and its adjunction/preservation API;
  `bridge/view`: the Chapter 4/18 route from the source pullback/equalizer hypotheses to the
    canonical exactness owner
    `CategoryTheory.Functor.sheafPullback_addCommGrp_exact_of_isContinuous_representablyFlat`.

This item should therefore stay source-facing in its hypothesis block, while its proof should
reuse the owner-level exactness route rather than exposing sheafification/Kan-extension
construction assumptions or introducing any parallel lower-shriek wrapper.
-/

-- Proof sketch: bridge the source pullback/equalizer hypotheses to the canonical Chapter 4/7
-- finite-connected-limit package, then apply the owner theorem
-- `CategoryTheory.Functor.sheafPullback_addCommGrp_exact_of_isContinuous_representablyFlat` for
-- the abelian sheaf pullback `u.sheafPullback AddCommGrpCat J K`.
/-- Lemma 18.16.3: if `u : C ⥤ D` is continuous, `C` has fibre products and equalizers, and `u`
commutes with them, then the lower shriek
`g_! : Ab(\mathcal C) ⥤ Ab(\mathcal D)`, realized in the project API as
`u.sheafPullback AddCommGrpCat J K`, is exact. -/
theorem sheafPullback_addCommGrp_exact_of_continuous_preserves_pullbacks_equalizers
    (u : C ⥤ D)
    [u.IsContinuous J K]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    exactFunctor (Sheaf J AddCommGrpCat.{u}) (Sheaf K AddCommGrpCat.{u})
      (u.sheafPullback AddCommGrpCat.{u} J K) := by
  -- The structured-arrow hypotheses from Lemma 7.5.1 give the exact colimits needed at each
  -- evaluation point of the presheaf left Kan extension.
  let _ :
      ∀ V : Dᵒᵖ, HasExactColimitsOfShape (CostructuredArrow u.op V) AddCommGrpCat.{u} :=
    fun V ↦ by
      obtain ⟨hSpan, hMap⟩ :=
        structuredArrow_op_has_span_cocones_and_postcomposition_equalizers u V.unop
      let _ : HasExactColimitsOfShape ((StructuredArrow V.unop u)ᵒᵖ) AddCommGrpCat.{u} := by
        let _ : HasSpanCocones ((StructuredArrow V.unop u)ᵒᵖ) := hSpan
        exact abelian_group_colimits_exact (I := (StructuredArrow V.unop u)ᵒᵖ) hMap
      exact
        HasExactColimitsOfShape.of_domain_equivalence AddCommGrpCat.{u}
          (structuredArrowOpEquivalence u V.unop)
  -- Route correction: use the objectwise exact-colimit description of `u.op.lan` directly,
  -- rather than detouring through the stronger `RepresentablyFlat u` owner.
  let _ :
      PreservesFiniteLimits
        (u.op.lan :
          (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{u}) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
    intro I _ _
    apply preservesLimitsOfShape_of_evaluation
      (u.op.lan :
        (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{u}) I
    intro V
    exact preservesLimitsOfShape_of_natIso
      (lanEvaluationIsoColim AddCommGrpCat.{u} u.op V).symm
  -- Finite-limit preservation survives sheafification, and the sheaf pullback is a left adjoint,
  -- so exactness follows from the canonical finite-(co)limit characterization.
  let _ : PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{u} J K) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits u AddCommGrpCat.{u} J K
  let _ : (u.sheafPullback AddCommGrpCat.{u} J K).IsLeftAdjoint :=
    (u.sheafAdjunctionContinuous AddCommGrpCat.{u} J K).isLeftAdjoint
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

end CategoryTheory
