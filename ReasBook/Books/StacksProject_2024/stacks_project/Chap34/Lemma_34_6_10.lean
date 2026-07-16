import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_21_6
import StacksProject_2024.stacks_project.Chap07.Lemma_7_22_2
import StacksProject_2024.stacks_project.Chap34.Definition_34_6_8

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S T : Scheme.{u}} (f : T ⟶ S)

local notation "J_T" => bigSyntomicSite T
local notation "J_S" => bigSyntomicSite S

/- Semantic recall / owner check:
- `lean_leansearch` recalled the canonical site-level owners
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPullback`, and
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`.
- `Definition_34_6_8` already owns the source-facing site-level notation `bigSyntomicSite S`;
  this lemma reuses that owner and the canonical adjoint pair `Over.map f` / `Over.pullback f`.
-/

/-- The postcomposition functor along `f` is also continuous for the big syntomic topologies. -/
instance bigSyntomicMapFunctor_isContinuous :
    (Over.map f).IsContinuous J_T J_S := sorry

/-- The inverse-image functor on sheaves induced by `f` on the big syntomic site. -/
abbrev bigSyntomicInverseImage :
    Sheaf J_S (Type (u + 1)) ⥤ Sheaf J_T (Type (u + 1)) :=
  (Over.map f).sheafPushforwardContinuous
    (Type (u + 1)) J_T J_S

/-- The `Over.map f` presentation has the left-Kan-extension hypotheses needed to define the
lower shriek on big syntomic sheaves. -/
local instance bigSyntomicMapFunctor_op_hasLeftKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (Over.map f).op.HasLeftKanExtension P := sorry

/-- The `Over.map f` presentation has the right-Kan-extension hypotheses needed to compare the
continuous and cocontinuous direct images on big syntomic sheaves. -/
local instance bigSyntomicMapFunctor_op_hasPointwiseRightKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (Over.map f).op.HasPointwiseRightKanExtension P := sorry

/-- The lower shriek on big syntomic sheaves induced by `f`. -/
abbrev bigSyntomicLowerShriek
    [HasWeakSheafify J_S (Type (u + 1))] :
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (Over.map f).sheafPullback
    (Type (u + 1)) J_T J_S

/-- Lemma 34.6.10 (1): the postcomposition functor
`(Sch/T)_{syntomic} ⥤ (Sch/S)_{syntomic}` induced by `f` is cocontinuous. -/
@[stacks 04HD]
instance bigSyntomicMapFunctor_isCocontinuous :
    (Over.map f).IsCocontinuous J_T J_S := sorry

/-- Lemma 34.6.10 (2): the pullback functor `Over.pullback f` is right adjoint to
postcomposition `Over.map f`. -/
@[stacks 04HD]
abbrev bigSyntomicMapPullbackAdjunction :
    Over.map f ⊣ Over.pullback f :=
  Over.mapPullbackAdj f

/-- Lemma 34.6.10 (3): the pullback functor `V/S ↦ (V ×[S] T)/T` is continuous for the big
syntomic topologies. -/
@[stacks 04HD]
instance bigSyntomicPullbackFunctor_isContinuous :
    (Over.pullback f).IsContinuous J_S J_T := sorry

/-- The direct-image functor on sheaves induced by `f` on the big syntomic site. -/
abbrev bigSyntomicDirectImage :
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (Over.map f).sheafPushforwardCocontinuous
    (Type (u + 1)) J_T J_S

/-- Lemma 34.6.10 (4): the continuous right-adjoint presentation and the cocontinuous
postcomposition presentation induce the same morphism of topoi; equivalently, their direct-image
functors are canonically isomorphic. -/
@[stacks 04HD]
noncomputable def bigSyntomicDirectImageIsoPullbackPresentation :
    bigSyntomicDirectImage f ≅
      (Over.pullback f).sheafPushforwardContinuous
        (Type (u + 1)) J_S J_T :=
  by
    simpa [bigSyntomicDirectImage] using
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        (Over.map f) (Over.pullback f) (Type (u + 1))
        (bigSyntomicMapPullbackAdjunction f)).symm

/-- Helper for Lemma 34.6.10: the forward comparison morphism in the direct-image comparison is an
isomorphism. -/
theorem bigSyntomicDirectImageIsoPullbackPresentation_hom_isIso :
    IsIso
      ((bigSyntomicDirectImageIsoPullbackPresentation f).hom :
        bigSyntomicDirectImage f ⟶
          (Over.pullback f).sheafPushforwardContinuous
            (Type (u + 1)) J_S J_T) := by
  infer_instance

/-- Lemma 34.6.10 (5): the inverse image of a big syntomic sheaf is computed by evaluation on the
same `T`-scheme, viewed over `S` by postcomposition with `f`. -/
@[stacks 04HD]
noncomputable def bigSyntomicInverseImage_obj_obj_iso
    (𝒢 : Sheaf J_S (Type (u + 1))) (U : Over T) :
    (((bigSyntomicInverseImage f).obj 𝒢).obj.obj (op U)) ≅
      𝒢.obj.obj (op ((Over.map f).obj U)) :=
  (((Over.map f).sheafPushforwardContinuousCompSheafToPresheafIso
      (Type (u + 1)) J_T J_S).app 𝒢).app (op U)

/-- Helper for Lemma 34.6.10: the objectwise inverse-image comparison is an isomorphism. -/
theorem bigSyntomicInverseImage_obj_obj_iso_hom_isIso
    (𝒢 : Sheaf J_S (Type (u + 1))) (U : Over T) :
    IsIso
      ((bigSyntomicInverseImage_obj_obj_iso f 𝒢 U).hom :
        (((bigSyntomicInverseImage f).obj 𝒢).obj.obj (op U)) ⟶
          𝒢.obj.obj (op ((Over.map f).obj U))) := by
  infer_instance

/-- Lemma 34.6.10 (6): the direct image of a big syntomic sheaf is computed by evaluation on the
pullback object `(U ×[S] T)/T`. -/
@[stacks 04HD]
noncomputable def bigSyntomicDirectImage_obj_obj_iso
    (ℱ : Sheaf J_T (Type (u + 1))) (U : Over S) :
    (((bigSyntomicDirectImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((Over.pullback f).obj U)) :=
  let e :
      (((bigSyntomicDirectImage f).obj ℱ).obj) ≅ (Over.pullback f).op ⋙ ℱ.obj :=
    ((Functor.isoWhiskerRight
        (bigSyntomicDirectImageIsoPullbackPresentation f)
        (sheafToPresheaf J_S (Type (u + 1)))).app ℱ) ≪≫
      ((Over.pullback f).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (u + 1)) J_S J_T).app ℱ
  e.app (op U)

/-- Helper for Lemma 34.6.10: the objectwise direct-image comparison is an isomorphism. -/
theorem bigSyntomicDirectImage_obj_obj_iso_hom_isIso
    (ℱ : Sheaf J_T (Type (u + 1))) (U : Over S) :
    IsIso
      ((bigSyntomicDirectImage_obj_obj_iso f ℱ U).hom :
        (((bigSyntomicDirectImage f).obj ℱ).obj.obj (op U)) ⟶
          ℱ.obj.obj (op ((Over.pullback f).obj U))) := by
  infer_instance

section LowerShriek

variable [HasWeakSheafify J_S (Type (u + 1))]

/-- Lemma 34.6.10 (7): the inverse image on big syntomic sheaves has a left adjoint, namely the
lower shriek `f_{big}!`. -/
@[stacks 04HD]
noncomputable abbrev bigSyntomicLowerShriekAdjunction :
    bigSyntomicLowerShriek f ⊣ bigSyntomicInverseImage f :=
  (Over.map f).sheafAdjunctionContinuous
    (Type (u + 1)) J_T J_S

/-- Companion theorem recording that the inverse-image functor has the expected right-adjoint
structure. -/
theorem bigSyntomicInverseImage_isRightAdjoint :
    (bigSyntomicInverseImage f).IsRightAdjoint :=
  (bigSyntomicLowerShriekAdjunction f).isRightAdjoint

/-- Lemma 34.6.10 (8): the lower shriek on big syntomic sheaves commutes with fibre products. -/
@[stacks 04HD]
instance bigSyntomicLowerShriek_preserves_pullbacks :
    PreservesLimitsOfShape WalkingCospan (bigSyntomicLowerShriek f) := sorry

/-- Lemma 34.6.10 (9): the lower shriek on big syntomic sheaves commutes with equalizers. -/
@[stacks 04HD]
instance bigSyntomicLowerShriek_preserves_equalizers :
    PreservesLimitsOfShape WalkingParallelPair (bigSyntomicLowerShriek f) := sorry

end LowerShriek

end

end AlgebraicGeometry
