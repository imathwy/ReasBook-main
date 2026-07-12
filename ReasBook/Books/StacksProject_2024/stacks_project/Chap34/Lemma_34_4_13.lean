import StacksProject_2024.Chap07.Lemma_7_21_1
import StacksProject_2024.Chap34.Lemma_34_4_10

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}} (f : T ⟶ S)

local notation "J_T" => T.smallEtaleTopology
local notation "J_S" => S.overGrothendieckTopology @Etale

-- Semantic recall: `lean_leansearch` surfaced the canonical site sheaf-functor owners
-- `Functor.sheafPushforwardContinuous`, `Functor.sheafAdjunctionContinuous`, and
-- `Functor.morphismOfTopoiInOfCocontinuous`. Local Chapter 34 precedent in
-- `Lemma_34_4_10` fixes the small étale site as `T.Etale` and the big étale site over `S` as
-- `Over S` with topology `S.overGrothendieckTopology @Etale`.

/-- The relocalization functor from `T_{\acute{e}tale}` to `(\mathit{Sch}/S)_{\acute{e}tale}`
sending `U/T` to `U/S`. -/
abbrev smallEtaleToBigEtaleFunctor : T.Etale ⥤ Over S :=
  MorphismProperty.Over.forget @Etale ⊤ T ⋙ Over.map f

/-- The relocalization functor is continuous for the small-to-big étale topologies. -/
instance smallEtaleToBigEtaleFunctor_isContinuous :
    Functor.IsContinuous (smallEtaleToBigEtaleFunctor f) J_T J_S := sorry

/-- The relocalization functor has the left-Kan-extension hypotheses needed to define the
source-facing lower shriek on sheaves. -/
instance smallEtaleToBigEtaleFunctor_op_hasLeftKanExtension
    (P : T.Etaleᵒᵖ ⥤ Type (u + 1)) :
    (smallEtaleToBigEtaleFunctor f).op.HasLeftKanExtension P := sorry

/-- The relocalization functor has the pointwise right-Kan-extension hypotheses needed to define
the cocontinuous morphism of topoi attached to it. -/
instance smallEtaleToBigEtaleFunctor_op_hasPointwiseRightKanExtension
    (P : T.Etaleᵒᵖ ⥤ Type (u + 1)) :
    (smallEtaleToBigEtaleFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The source-facing inverse-image functor attached to `f`, computed by precomposition with the
relocalization functor on the small étale site of `T`. -/
abbrev smallEtaleToBigEtaleInverseImage :
    Sheaf J_S (Type (u + 1)) ⥤ Sheaf J_T (Type (u + 1)) :=
  (smallEtaleToBigEtaleFunctor f).sheafPushforwardContinuous
    (Type (u + 1)) J_T J_S

/-- The source-facing lower shriek attached to `f`. -/
abbrev smallEtaleToBigEtaleLowerShriek
    [HasWeakSheafify J_S (Type (u + 1))] :
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (smallEtaleToBigEtaleFunctor f).sheafPullback
    (Type (u + 1)) J_T J_S

/-- Lemma 34.4.13 (1): the relocalization functor
`T_{\acute{e}tale} ⥤ (\mathit{Sch}/S)_{\acute{e}tale}` sending `U/T` to `U/S` is
cocontinuous. -/
@[stacks 021F]
instance smallEtaleToBigEtaleFunctor_isCocontinuous :
    Functor.IsCocontinuous (smallEtaleToBigEtaleFunctor f) J_T J_S := sorry

/-- Lemma 34.4.13 (2): the relocalization functor induces a morphism of topoi
`i_f : \mathit{Sh}(T_{\acute{e}tale}) \to \mathit{Sh}((\mathit{Sch}/S)_{\acute{e}tale})`. -/
@[stacks 021F]
abbrev smallEtaleToBigEtaleMorphismOfTopoi
    [HasSheafify J_T (Type (u + 1))] :
    MorphismOfTopoiIn J_S J_T :=
  (smallEtaleToBigEtaleFunctor f).morphismOfTopoiInOfCocontinuous J_T J_S

/-- The direct image of `smallEtaleToBigEtaleMorphismOfTopoi` is the cocontinuous sheaf
pushforward attached to the relocalization functor. -/
@[stacks 021F]
theorem smallEtaleToBigEtaleMorphismOfTopoi_pushforward
    [HasSheafify J_T (Type (u + 1))] :
    (smallEtaleToBigEtaleMorphismOfTopoi f) _* =
      (smallEtaleToBigEtaleFunctor f).sheafPushforwardCocontinuous
        (Type (u + 1)) J_T J_S := by
  simpa using
    (Functor.morphismOfTopoiInOfCocontinuous_pushforward
      (smallEtaleToBigEtaleFunctor f) J_T J_S)

/-- Lemma 34.4.13 (3): for a sheaf `𝒢` on `(\mathit{Sch}/S)_{\acute{e}tale}` and an object
`U/T` of `T_{\acute{e}tale}`, the inverse image `i_f^{-1} 𝒢` is computed by evaluation on the
same scheme viewed over `S`. -/
@[stacks 021F]
theorem smallEtaleToBigEtaleInverseImage_obj_obj
    (𝒢 : Sheaf J_S (Type (u + 1))) (U : T.Etale) :
    ((smallEtaleToBigEtaleInverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((smallEtaleToBigEtaleFunctor f).obj U)) := sorry

/-- Lemma 34.4.13 (4): the source-facing inverse-image functor `i_f^{-1}` has a left adjoint
`i_{f,!}`, realized here by the canonical lower shriek. -/
@[stacks 021F]
abbrev smallEtaleToBigEtaleLowerShriekAdjunction
    [HasWeakSheafify J_S (Type (u + 1))] :
    smallEtaleToBigEtaleLowerShriek f ⊣ smallEtaleToBigEtaleInverseImage f :=
  (smallEtaleToBigEtaleFunctor f).sheafAdjunctionContinuous
    (Type (u + 1)) J_T J_S

/-- `smallEtaleToBigEtaleLowerShriekAdjunction` is the canonical continuous-site adjunction
attached to the relocalization functor. -/
@[stacks 021F]
theorem smallEtaleToBigEtaleLowerShriekAdjunction_def
    [HasWeakSheafify J_S (Type (u + 1))] :
    smallEtaleToBigEtaleLowerShriekAdjunction f =
      (smallEtaleToBigEtaleFunctor f).sheafAdjunctionContinuous
        (Type (u + 1)) J_T J_S := by
  rfl

/-- Lemma 34.4.13 (5): the left adjoint `i_{f,!}` commutes with fibre products. -/
@[stacks 021F]
theorem smallEtaleToBigEtaleLowerShriek_preservesPullbacks
    [HasWeakSheafify J_S (Type (u + 1))] :
    PreservesLimitsOfShape WalkingCospan (smallEtaleToBigEtaleLowerShriek f) := sorry

/-- Lemma 34.4.13 (6): the left adjoint `i_{f,!}` commutes with equalizers. -/
@[stacks 021F]
theorem smallEtaleToBigEtaleLowerShriek_preservesEqualizers
    [HasWeakSheafify J_S (Type (u + 1))] :
    PreservesLimitsOfShape WalkingParallelPair (smallEtaleToBigEtaleLowerShriek f) := sorry

end AlgebraicGeometry.Scheme
