import Mathlib
import StacksProject_2024.Chap07.Lemma_7_21_6
import StacksProject_2024.Chap07.Lemma_7_22_2
import StacksProject_2024.Chap34.Definition_34_3_7

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S T : Scheme.{u}} (f : T ⟶ S)

local notation "J_T" => T.bigZariskiTopology
local notation "J_S" => S.bigZariskiTopology

/- Semantic recall / owner check:
- `lean_leansearch` recalled the canonical site-level owners
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPullback`, and
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`.
- Local Chapter 34 precedent in `Lemma_34_4_16` fixes the big-site owner as `Over S` with the
  adjoint pair `Over.map f` and `Over.pullback f`, so this Zariski lemma uses the same surface.
-/

/-- The postcomposition functor on the big Zariski over-categories induced by `f`. -/
abbrev bigZariskiMapFunctor : Over T ⥤ Over S :=
  Over.map f

/-- The pullback functor on the big Zariski over-categories induced by `f`. -/
abbrev bigZariskiPullbackFunctor : Over S ⥤ Over T :=
  Over.pullback f

/-- The postcomposition functor along `f` is also continuous for the big Zariski topologies. -/
instance bigZariskiMapFunctor_isContinuous :
    Functor.IsContinuous (bigZariskiMapFunctor f) J_T J_S := sorry

/-- The inverse-image functor on sheaves induced by `f` on the big Zariski site. -/
abbrev bigZariskiInverseImage :
    Sheaf J_S (Type (u + 1)) ⥤ Sheaf J_T (Type (u + 1)) :=
  (bigZariskiMapFunctor f).sheafPushforwardContinuous
    (Type (u + 1)) J_T J_S

/-- The `Over.map f` presentation has the left-Kan-extension hypotheses needed to define the
lower shriek on big Zariski sheaves. -/
instance bigZariskiMapFunctor_op_hasLeftKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (bigZariskiMapFunctor f).op.HasLeftKanExtension P := sorry

/-- The `Over.map f` presentation has the right-Kan-extension hypotheses needed to compare the
continuous and cocontinuous direct images on big Zariski sheaves. -/
instance bigZariskiMapFunctor_op_hasPointwiseRightKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (bigZariskiMapFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The big Zariski site over `T` has equalizers. -/
instance bigZariskiSite_hasEqualizers :
    HasEqualizers T.bigZariskiSite := sorry

/-- The postcomposition functor along `f` preserves fibre products on big Zariski sites. -/
instance bigZariskiMapFunctor_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (bigZariskiMapFunctor f) := sorry

/-- The postcomposition functor along `f` preserves equalizers on big Zariski sites. -/
instance bigZariskiMapFunctor_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (bigZariskiMapFunctor f) := sorry

/-- The lower shriek on big Zariski sheaves induced by `f`. -/
abbrev bigZariskiLowerShriek
    [HasWeakSheafify J_S (Type (u + 1))] :
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (bigZariskiMapFunctor f).sheafPullback
    (Type (u + 1)) J_T J_S

/-- The direct-image functor on sheaves induced by `f` on the big Zariski site. -/
abbrev bigZariskiDirectImage :
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (bigZariskiPullbackFunctor f).sheafPushforwardContinuous
    (Type (u + 1)) J_S J_T

/-- Lemma 34.3.16 (1): the postcomposition functor
`u : (\mathit{Sch}/T)_{Zar} ⥤ (\mathit{Sch}/S)_{Zar}` induced by `f` is cocontinuous. -/
@[stacks 0210]
instance bigZariskiMapFunctor_isCocontinuous :
    Functor.IsCocontinuous (bigZariskiMapFunctor f) J_T J_S := sorry

/-- Lemma 34.3.16 (2): the pullback functor
`v : (\mathit{Sch}/S)_{Zar} ⥤ (\mathit{Sch}/T)_{Zar}` is right adjoint to the postcomposition
functor `u`. -/
@[stacks 0210]
abbrev bigZariskiMapPullbackAdjunction :
    bigZariskiMapFunctor f ⊣ bigZariskiPullbackFunctor f :=
  Over.mapPullbackAdj f

/-- The map-pullback adjunction is the canonical over-category adjunction. -/
theorem bigZariskiMapPullbackAdjunction_def :
    bigZariskiMapPullbackAdjunction f = Over.mapPullbackAdj f := sorry

/-- Lemma 34.3.16 (3): the pullback functor
`v : (\mathit{Sch}/S)_{Zar} ⥤ (\mathit{Sch}/T)_{Zar}` is continuous. -/
@[stacks 0210]
instance bigZariskiPullbackFunctor_isContinuous :
    Functor.IsContinuous (bigZariskiPullbackFunctor f) J_S J_T := sorry

/-- Lemma 34.3.16 (4): the continuous right-adjoint presentation and the cocontinuous
postcomposition presentation induce the same morphism of topoi; equivalently, their direct-image
functors are canonically isomorphic. -/
@[stacks 0210]
noncomputable def bigZariskiDirectImageIsoCocontinuous :
    bigZariskiDirectImage f ≅
      (bigZariskiMapFunctor f).sheafPushforwardCocontinuous
        (Type (u + 1)) J_T J_S :=
  continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
    (bigZariskiMapFunctor f) (bigZariskiPullbackFunctor f) (Type (u + 1))
    (bigZariskiMapPullbackAdjunction f)

/-- The direct-image comparison is the canonical continuous/cocontinuous pushforward
comparison attached to the map-pullback adjunction. -/
theorem bigZariskiDirectImageIsoCocontinuous_def :
    bigZariskiDirectImageIsoCocontinuous f =
      continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        (bigZariskiMapFunctor f) (bigZariskiPullbackFunctor f) (Type (u + 1))
        (bigZariskiMapPullbackAdjunction f) := sorry

/-- Lemma 34.3.16 (5): the inverse image of a big Zariski sheaf is computed by evaluation on the
same `T`-scheme, viewed over `S` by postcomposition with `f`. -/
@[stacks 0210]
theorem bigZariskiInverseImage_obj_obj
    (𝒢 : Sheaf J_S (Type (u + 1))) (U : Over T) :
    ((bigZariskiInverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((bigZariskiMapFunctor f).obj U)) := sorry

/-- Lemma 34.3.16 (6): the direct image of a big Zariski sheaf is computed by evaluation on the
pullback object `(U \times_S T)/T`. -/
@[stacks 0210]
theorem bigZariskiDirectImage_obj_obj
    (ℱ : Sheaf J_T (Type (u + 1))) (U : Over S) :
    ((bigZariskiDirectImage f).obj ℱ).1.obj (op U) =
      ℱ.1.obj (op ((bigZariskiPullbackFunctor f).obj U)) := sorry

/-- Companion theorem recording that the lower-shriek functor has the expected adjunction API. -/
theorem bigZariskiLowerShriekAdjunction_isLeftAdjoint
    [HasWeakSheafify J_S (Type (u + 1))] :
    (bigZariskiLowerShriek f).IsLeftAdjoint := sorry

section LowerShriek

variable [HasWeakSheafify J_S (Type (u + 1))]

/-- Lemma 34.3.16 (7): the inverse image on big Zariski sheaves has a left adjoint, namely the
lower shriek `f_{big,!}`. -/
@[stacks 0210]
noncomputable def bigZariskiLowerShriekAdjunction :
    bigZariskiLowerShriek f ⊣ bigZariskiInverseImage f :=
  (bigZariskiMapFunctor f).sheafAdjunctionContinuous
    (Type (u + 1)) J_T J_S

/-- Lemma 34.3.16 (8): the lower shriek on big Zariski sheaves commutes with fibre products. -/
@[stacks 0210]
instance bigZariskiLowerShriek_preserves_pullbacks :
    PreservesLimitsOfShape WalkingCospan (bigZariskiLowerShriek f) := sorry

/-- Lemma 34.3.16 (9): the lower shriek on big Zariski sheaves commutes with equalizers. -/
@[stacks 0210]
instance bigZariskiLowerShriek_preserves_equalizers :
    PreservesLimitsOfShape WalkingParallelPair (bigZariskiLowerShriek f) := sorry

end LowerShriek

end

end AlgebraicGeometry
