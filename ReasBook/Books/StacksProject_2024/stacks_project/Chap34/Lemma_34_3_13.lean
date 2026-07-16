import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_15_1_Topoi
import StacksProject_2024.stacks_project.Chap07.Lemma_7_21_1
import StacksProject_2024.stacks_project.Chap07.Lemma_7_21_5
import StacksProject_2024.stacks_project.Chap07.Lemma_7_21_6
import StacksProject_2024.stacks_project.Chap34.Lemma_34_3_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}} (f : T ⟶ S)

local notation "J_T" => T.smallZariskiTopology
local notation "J_S" => S.bigZariskiTopology

-- Semantic recall: `lean_leansearch` surfaced the canonical site sheaf-functor owners
-- `Functor.sheafPushforwardContinuous`, `Functor.sheafAdjunctionContinuous`, and
-- `Functor.morphismOfTopoiInOfCocontinuous`. Local Chapter 34 precedent in `Lemma_34_4_13`
-- matches the companion-lemma pattern used below.

/-- The relocalization functor from `T_{Zar}` to `(\mathit{Sch}/S)_{Zar}` sending `U/T` to
`U/S`. -/
@[stacks 020Y]
abbrev smallZariskiToBigZariskiFunctor : T.smallZariskiSite ⥤ S.bigZariskiSite :=
  MorphismProperty.Over.forget @IsOpenImmersion ⊤ T ⋙ Over.map f

/-- The small Zariski site has equalizers. -/
instance smallZariski_hasEqualizers : HasEqualizers T.smallZariskiSite := sorry

/-- The relocalization functor from `T_{Zar}` to `(\mathit{Sch}/S)_{Zar}` preserves fibre
products. -/
instance smallZariskiToBigZariskiFunctor_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (smallZariskiToBigZariskiFunctor f) := sorry

/-- The relocalization functor from `T_{Zar}` to `(\mathit{Sch}/S)_{Zar}` preserves equalizers. -/
instance smallZariskiToBigZariskiFunctor_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (smallZariskiToBigZariskiFunctor f) := sorry

/-- The relocalization functor is continuous for the small-to-big Zariski topologies. -/
instance smallZariskiToBigZariskiFunctor_isContinuous :
    Functor.IsContinuous (smallZariskiToBigZariskiFunctor f) J_T J_S := sorry

/-- The relocalization functor has the left-Kan-extension hypotheses needed to define the
source-facing lower shriek on sheaves. -/
instance smallZariskiToBigZariskiFunctor_op_hasLeftKanExtension
    (P : T.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) :
    (smallZariskiToBigZariskiFunctor f).op.HasLeftKanExtension P := sorry

/-- The relocalization functor has the pointwise right-Kan-extension hypotheses needed to define
the cocontinuous morphism of topoi attached to it. -/
instance smallZariskiToBigZariskiFunctor_op_hasPointwiseRightKanExtension
    (P : T.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) :
    (smallZariskiToBigZariskiFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The source-facing inverse-image functor attached to `f`, computed by precomposition with the
relocalization functor on the small Zariski site of `T`. -/
@[stacks 020Y]
abbrev smallZariskiToBigZariskiInverseImage :
    Sheaf J_S (Type (u + 1)) ⥤ Sheaf J_T (Type (u + 1)) :=
  (smallZariskiToBigZariskiFunctor f).sheafPushforwardContinuous
    (Type (u + 1)) J_T J_S

/-- The source-facing lower shriek attached to `f`. -/
@[stacks 020Y]
abbrev smallZariskiToBigZariskiLowerShriek
    [HasWeakSheafify J_S (Type (u + 1))] :
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (smallZariskiToBigZariskiFunctor f).sheafPullback
    (Type (u + 1)) J_T J_S

/-- Lemma 34.3.13 (1): the relocalization functor
`T_{Zar} ⥤ (\mathit{Sch}/S)_{Zar}` sending `U/T` to `U/S` is cocontinuous. -/
@[stacks 020Y]
instance smallZariskiToBigZariskiFunctor_isCocontinuous :
    Functor.IsCocontinuous (smallZariskiToBigZariskiFunctor f) J_T J_S := sorry

/-- Lemma 34.3.13 (2): the relocalization functor induces a morphism of topoi
`i_f : \mathit{Sh}(T_{Zar}) \to \mathit{Sh}((\mathit{Sch}/S)_{Zar})`. -/
@[stacks 020Y]
abbrev smallZariskiToBigZariskiMorphismOfTopoi
    [HasSheafify J_T (Type (u + 1))] :
    MorphismOfTopoiIn J_S J_T :=
  (smallZariskiToBigZariskiFunctor f).morphismOfTopoiInOfCocontinuous J_T J_S

/-- The direct image of `smallZariskiToBigZariskiMorphismOfTopoi` is the cocontinuous sheaf
pushforward attached to the relocalization functor. -/
@[stacks 020Y]
theorem smallZariskiToBigZariskiMorphismOfTopoi_pushforward
    [HasSheafify J_T (Type (u + 1))] :
    (smallZariskiToBigZariskiMorphismOfTopoi f) _* =
      (smallZariskiToBigZariskiFunctor f).sheafPushforwardCocontinuous
        (Type (u + 1)) J_T J_S := sorry

/-- Lemma 34.3.13 (3): for a sheaf `\mathcal{G}` on `(\mathit{Sch}/S)_{Zar}` and an object
`U/T` of `T_{Zar}`, the inverse image `i_f^{-1}\mathcal{G}` is computed by evaluation on the same
scheme viewed over `S`. -/
@[stacks 020Y]
theorem smallZariskiToBigZariskiInverseImage_obj_obj
    (𝒢 : Sheaf J_S (Type (u + 1))) (U : T.smallZariskiSite) :
    ((smallZariskiToBigZariskiInverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((smallZariskiToBigZariskiFunctor f).obj U)) := sorry

/-- Lemma 34.3.13 (4): the source-facing inverse-image functor `i_f^{-1}` has a left adjoint
`i_{f,!}`, realized here by the canonical lower shriek. -/
@[stacks 020Y]
abbrev smallZariskiToBigZariskiLowerShriekAdjunction
    [HasWeakSheafify J_S (Type (u + 1))] :
    smallZariskiToBigZariskiLowerShriek f ⊣ smallZariskiToBigZariskiInverseImage f :=
  (smallZariskiToBigZariskiFunctor f).sheafAdjunctionContinuous
    (Type (u + 1)) J_T J_S

/-- `smallZariskiToBigZariskiLowerShriekAdjunction` is the canonical continuous-site adjunction
attached to the relocalization functor. -/
@[stacks 020Y]
theorem smallZariskiToBigZariskiLowerShriekAdjunction_def
    [HasWeakSheafify J_S (Type (u + 1))] :
    smallZariskiToBigZariskiLowerShriekAdjunction f =
      (smallZariskiToBigZariskiFunctor f).sheafAdjunctionContinuous
        (Type (u + 1)) J_T J_S := sorry

/-- Lemma 34.3.13 (5): the left adjoint `i_{f,!}` commutes with fibre products. -/
@[stacks 020Y]
theorem smallZariskiToBigZariskiLowerShriek_preservesPullbacks
    [HasWeakSheafify J_S (Type (u + 1))] :
    PreservesLimitsOfShape WalkingCospan (smallZariskiToBigZariskiLowerShriek f) := sorry

/-- Lemma 34.3.13 (6): the left adjoint `i_{f,!}` commutes with equalizers. -/
@[stacks 020Y]
theorem smallZariskiToBigZariskiLowerShriek_preservesEqualizers
    [HasWeakSheafify J_S (Type (u + 1))] :
    PreservesLimitsOfShape WalkingParallelPair (smallZariskiToBigZariskiLowerShriek f) := sorry

end AlgebraicGeometry.Scheme
