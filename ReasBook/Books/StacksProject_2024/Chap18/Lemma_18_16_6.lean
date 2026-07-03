import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap07.Lemma_7_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-
Domain-style sampling for Lemma 18.16.6:
- primary domain: lower shriek / inverse-image / direct-image functors on abelian sheaves under an
  adjunction of site functors;
- sampled owner declarations:
  `Functor.sheafPullback`,
  `Functor.sheafPullbackCocontinuous`,
  `CategoryTheory.sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint`,
  `CategoryTheory.continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- best owner abstractions:
  `u.sheafPullback AddCommGrpCat J K` for the lower shriek attached to the continuous right
  adjoint `u`,
  `w.sheafPullbackCocontinuous AddCommGrpCat K J` for the inverse image attached to the
  cocontinuous left adjoint `w`,
  and `w.sheafPushforwardCocontinuous AddCommGrpCat K J` for the corresponding direct image;
- primitive data: the functors `u`, `w`, the adjunction `w ⊣ u`, and the standard Kan-extension /
  sheafification hypotheses needed to form these owner functors;
- derived API: the Chapter 7 comparison isomorphisms between these owners and the resulting
  exactness statement on abelian sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks comparison of the abelian lower shriek `g_!` with the inverse- and
  direct-image functors attached to the cocontinuous left adjoint `w`, plus exactness of `g_!`;
- `core/canonical`: the Chapter 7 owner functors
  `u.sheafPullback AddCommGrpCat J K`,
  `w.sheafPullbackCocontinuous AddCommGrpCat K J`,
  `u.sheafPushforwardContinuous AddCommGrpCat J K`,
  `w.sheafPushforwardCocontinuous AddCommGrpCat K J`;
- `bridge/view`: the Chapter 7 comparison theorems specialized below to `AddCommGrpCat`.

The previous one-off Chapter 18 wrapper for the cocontinuous inverse image was a duplicate wheel.
The canonical owner now lives upstream in Chapter 7 as
`Functor.sheafPullbackCocontinuous`, so this file reuses that owner directly.
-/

section

variable (u : C ⥤ D) (w : D ⥤ C)
variable [u.IsContinuous J K]
variable (adj : w ⊣ u)

-- Proof sketch: compare `u.sheafPullback AddCommGrpCat J K` with the canonical owner
-- `w.sheafPullbackCocontinuous AddCommGrpCat K J` from Chapter 7, then use the same finite-limit
-- and left-adjoint argument as in the set-valued case.
/-- Lemma 18.16.6 (1): if `u : C ⥤ D` is continuous and has a left adjoint `w`, then the lower
shriek `g_!` on abelian sheaves, realized as `u.sheafPullback AddCommGrpCat J K`, is exact. -/
theorem sheafPullback_addCommGrp_exact_of_leftAdjoint
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}, u.op.HasLeftKanExtension P]
    [HasSheafify K AddCommGrpCat.{max u v}] :
    exactFunctor (Sheaf J AddCommGrpCat.{max u v}) (Sheaf K AddCommGrpCat.{max u v})
      (u.sheafPullback AddCommGrpCat.{max u v} J K) := sorry

section

variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]

/- Lemma 18.16.6 (2): the abelian lower shriek is the inverse-image functor attached to the
cocontinuous left adjoint `w`; this is exactly the `AddCommGrpCat` specialization of the Chapter 7
owner comparison. -/
#check
  (sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint
      u w adj AddCommGrpCat.{max u v} :
    u.sheafPullback AddCommGrpCat.{max u v} J K ≅
      w.sheafPullbackCocontinuous AddCommGrpCat.{max u v} K J)

end

section

variable [w.IsCocontinuous K J]
variable [∀ P : Dᵒᵖ ⥤ AddCommGrpCat.{max u v}, w.op.HasPointwiseRightKanExtension P]

/- Lemma 18.16.6 (3): the inverse image `g⁻¹` attached to `u` is the direct image attached to the
cocontinuous left adjoint `w`; this is the corresponding `AddCommGrpCat` specialization of the
Chapter 7 owner comparison. -/
#check
  (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
      w u AddCommGrpCat.{max u v} adj :
    u.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K ≅
      w.sheafPushforwardCocontinuous AddCommGrpCat.{max u v} K J)

end

end

end CategoryTheory
