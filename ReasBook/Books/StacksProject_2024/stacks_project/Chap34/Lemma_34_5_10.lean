import StacksProject_2024.Chap07.Lemma_7_21_6
import StacksProject_2024.Chap07.Lemma_7_21_1
import StacksProject_2024.Chap34.Definition_34_5_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S T : Scheme.{u}} (f : T ⟶ S)

local notation "J_T" => bigSmoothSite T
local notation "J_S" => bigSmoothSite S

/- Semantic recall / owner check:
- `lean_leansearch` recalled the site-level cocontinuous/continuous sheaf functor owners,
  including `Functor.sheafPushforwardContinuous`, which matches the textbook section formulas.
- Local Chapter 7 precedent fixes the relevant categorical owners here: use `Over.map f` and
  `Over.pullback f` for the adjoint pair on slice categories, and package the resulting geometric
  morphism via `Functor.morphismOfTopoiInOfCocontinuous`.
-/

/-- Lemma 34.5.10 (1): the base-change functor
`u : (Sch/T)_{smooth} ⥤ (Sch/S)_{smooth}`, given on objects by `V/T ↦ V/S`, is cocontinuous. -/
@[stacks 021Y]
instance bigSmoothMapFunctor_isCocontinuous :
    (Over.map f).IsCocontinuous J_T J_S := by
  infer_instance

/-- Lemma 34.5.10 (2): the pullback functor
`v : (Sch/S)_{smooth} ⥤ (Sch/T)_{smooth}`, given by `U/S ↦ U ×_S T/T`, is continuous. -/
@[stacks 021Y]
instance bigSmoothPullbackFunctor_isContinuous :
    (Over.pullback f).IsContinuous J_S J_T :=
  (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous J_T J_S

/-- The postcomposition functor along `f` is continuous for the big smooth topologies. -/
instance bigSmoothMapFunctor_isContinuous :
    (Over.map f).IsContinuous J_T J_S := by
  infer_instance

/-- A source-facing presentation of the inverse-image functor `f_big⁻¹` of the big smooth
morphism of topoi, computed by the continuous sheaf functor along `Over.map f`. -/
abbrev bigSmoothInverseImage :
    Sheaf J_S (Type (u + 1)) ⥤ Sheaf J_T (Type (u + 1)) :=
  (Over.map f).sheafPushforwardContinuous (Type (u + 1)) J_T J_S

/-- The `Over.map f` presentation has the left-Kan-extension hypotheses needed to define the
lower shriek on big smooth sheaves. -/
local instance bigSmoothMapFunctor_op_hasLeftKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (Over.map f).op.HasLeftKanExtension P := by
  infer_instance

/-- The `Over.map f` presentation has the right-Kan-extension hypotheses needed to compare the
continuous and cocontinuous direct images on big smooth sheaves. -/
local instance bigSmoothMapFunctor_op_hasPointwiseRightKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (Over.map f).op.HasPointwiseRightKanExtension P := by
  infer_instance

/-- The direct-image functor `f_{big,*}` of the big smooth morphism of topoi, presented by the
cocontinuous pushforward along `Over.map f`. -/
abbrev bigSmoothDirectImage :
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (Over.map f).sheafPushforwardCocontinuous (Type (u + 1)) J_T J_S

/-- Lemma 34.5.10 (3): the cocontinuous base-change functor `Over.map f` determines the big
smooth morphism of topoi `f_big : Sh((Sch/T)_{smooth}) ⟶ Sh((Sch/S)_{smooth})`. -/
@[stacks 021Y]
noncomputable def bigSmoothMorphismOfTopoi :
    MorphismOfTopoiIn J_S J_T where
  inverseImageFunctor :=
    LeftExactFunctor.of (bigSmoothInverseImage f)
  pushforward := bigSmoothDirectImage f
  adjunction := (Over.map f).sheafAdjunctionCocontinuous (Type (u + 1)) J_T J_S

@[simp] theorem bigSmoothMorphismOfTopoi_inverseImage :
    (bigSmoothMorphismOfTopoi f)⁻¹ = bigSmoothInverseImage f :=
  rfl

@[simp] theorem bigSmoothMorphismOfTopoi_pushforward :
    (bigSmoothMorphismOfTopoi f).pushforward = bigSmoothDirectImage f :=
  rfl

/-- Lemma 34.5.10 (3), reformulated: the continuous right-adjoint presentation and the
cocontinuous postcomposition presentation induce the same morphism of topoi; equivalently, their
direct-image functors are canonically isomorphic. -/
@[stacks 021Y]
noncomputable def bigSmoothDirectImageIsoPullbackPresentation :
    bigSmoothDirectImage f ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1)) J_S J_T :=
  by
    simpa [bigSmoothDirectImage] using
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        (Over.map f) (Over.pullback f) (Type (u + 1))
        (Over.mapPullbackAdj f)).symm

/-- The big smooth morphism of topoi has direct image canonically identified with evaluation on
pullbacks via the cocontinuous `Over.map f` presentation and its right adjoint `Over.pullback f`. -/
noncomputable def bigSmoothMorphismOfTopoi_pushforwardIsoPullbackPresentation :
    ((((bigSmoothMorphismOfTopoi f) _*) :
      Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1))) ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1)) J_S J_T :=
  let ePush :
      ((((bigSmoothMorphismOfTopoi f) _*) :
        Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1))) ≅
        ((((Over.map f).morphismOfTopoiInOfCocontinuous J_T J_S) _*) :
          Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)))) :=
    eqToIso <| by
      simpa [bigSmoothMorphismOfTopoi, bigSmoothDirectImage] using
        (Functor.morphismOfTopoiInOfCocontinuous_pushforward
          (u := Over.map f) J_T J_S).symm
  ePush ≪≫ bigSmoothDirectImageIsoPullbackPresentation f

/-- The source-facing presentation `bigSmoothDirectImage` computes sections on `U/S` by
evaluating on the pullback object `U ×_S T/T`. -/
noncomputable def bigSmoothDirectImage_obj_obj_iso
    (ℱ : Sheaf J_T (Type (u + 1))) (U : Over S) :
    (((bigSmoothDirectImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((Over.pullback f).obj U)) :=
  let e :
      ((((bigSmoothDirectImage f).obj ℱ).obj)) ≅ (Over.pullback f).op ⋙ ℱ.obj :=
    ((Functor.isoWhiskerRight
          (bigSmoothDirectImageIsoPullbackPresentation f)
          (sheafToPresheaf J_S (Type (u + 1)))).app ℱ) ≪≫
      ((Over.pullback f).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (u + 1)) J_S J_T).app ℱ
  e.app (op U)

/-- The source-facing presentation `bigSmoothInverseImage` computes sections on `V/T` by
evaluating on the same underlying object viewed over `S`. -/
noncomputable def bigSmoothInverseImage_obj_obj_iso
    (𝒢 : Sheaf J_S (Type (u + 1))) (V : Over T) :
    (((bigSmoothInverseImage f).obj 𝒢).obj.obj (op V)) ≅
      𝒢.obj.obj (op ((Over.map f).obj V)) :=
  (((Over.map f).sheafPushforwardContinuousCompSheafToPresheafIso
    (Type (u + 1)) J_T J_S).app 𝒢).app (op V)

/-- Lemma 34.5.10 (4): for a sheaf `𝒢` on the big smooth site of `S`, the inverse image
`f_big⁻¹ 𝒢` has sections on `V/T` canonically identified with the sections of `𝒢` on the same
underlying object viewed over `S`. -/
@[stacks 021Y]
noncomputable def bigSmoothMorphismOfTopoi_inverseImage_obj_obj_iso
    (𝒢 : Sheaf J_S (Type (u + 1))) (V : Over T) :
    ((((bigSmoothMorphismOfTopoi f)⁻¹).obj 𝒢).obj.obj (op V)) ≅
      𝒢.obj.obj (op ((Over.map f).obj V)) :=
  by
    simpa [bigSmoothMorphismOfTopoi] using
      bigSmoothInverseImage_obj_obj_iso f 𝒢 V

/-- Lemma 34.5.10 (5): for a sheaf `ℱ` on the big smooth site of `T`, the direct image
`f_{big,*} ℱ` has sections on `U/S` canonically identified with the sections of `ℱ` on the
pullback object `U ×_S T/T`. -/
@[stacks 021Y]
noncomputable def bigSmoothMorphismOfTopoi_pushforward_obj_obj_iso
    (ℱ : Sheaf J_T (Type (u + 1))) (U : Over S) :
    ((((bigSmoothMorphismOfTopoi f) _*).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((Over.pullback f).obj U)) :=
  by
    simpa using
      (((Functor.isoWhiskerRight
          (bigSmoothMorphismOfTopoi_pushforwardIsoPullbackPresentation f)
          (sheafToPresheaf J_S (Type (u + 1)))).app ℱ).app (op U)) ≪≫
        (((Over.pullback f).sheafPushforwardContinuousCompSheafToPresheafIso
          (Type (u + 1)) J_S J_T).app ℱ).app (op U)

/-- A source-faithful name for the lower shriek functor `f_{big!}` on sheaves of types over the
big smooth site, realized by the continuous lower-shriek owner attached to `Over.map f`. -/
abbrev bigSmoothLowerShriek :
    [HasWeakSheafify J_S (Type (u + 1))] →
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (Over.map f).sheafPullback (Type (u + 1)) J_T J_S

section LowerShriek

variable [HasWeakSheafify J_S (Type (u + 1))]

/-- Lemma 34.5.10 (6): the lower shriek functor `f_{big!}` is left adjoint to the inverse-image
functor `f_big⁻¹`. -/
@[stacks 021Y]
noncomputable abbrev bigSmoothLowerShriekAdjunction :
    bigSmoothLowerShriek f ⊣ bigSmoothInverseImage f :=
  (Over.map f).sheafAdjunctionContinuous (Type (u + 1)) J_T J_S

/-- Lemma 34.5.10 (6), reformulated: the inverse-image functor `f_big⁻¹` on the big smooth topoi
is a right adjoint. -/
theorem bigSmoothInverseImage_isRightAdjoint :
    (bigSmoothInverseImage f).IsRightAdjoint :=
  (bigSmoothLowerShriekAdjunction f).isRightAdjoint

/-- Lemma 34.5.10 (7): the lower shriek functor `f_{big!}` commutes with fibre products. -/
@[stacks 021Y]
instance bigSmoothLowerShriek_preserves_pullbacks :
    PreservesLimitsOfShape WalkingCospan (bigSmoothLowerShriek f) := by
  simpa using
    (sheafPullback_preserves_pullbacks (Over.map f) :
      PreservesLimitsOfShape WalkingCospan
        ((Over.map f).sheafPullback (Type (u + 1)) J_T J_S))

/-- Lemma 34.5.10 (8): the lower shriek functor `f_{big!}` commutes with equalizers. -/
@[stacks 021Y]
instance bigSmoothLowerShriek_preserves_equalizers :
    PreservesLimitsOfShape WalkingParallelPair (bigSmoothLowerShriek f) := by
  simpa using
    (sheafPullback_preserves_equalizers (Over.map f) :
      PreservesLimitsOfShape WalkingParallelPair
        ((Over.map f).sheafPullback (Type (u + 1)) J_T J_S))

end LowerShriek

end

end AlgebraicGeometry
