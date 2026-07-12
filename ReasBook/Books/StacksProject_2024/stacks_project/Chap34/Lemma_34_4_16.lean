import Mathlib
import StacksProject_2024.Chap07.Lemma_7_21_6
import StacksProject_2024.Chap07.Lemma_7_22_2

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S T : Scheme.{u}} (f : T ⟶ S)

local notation "J_T" => T.overGrothendieckTopology @Etale
local notation "J_S" => S.overGrothendieckTopology @Etale

/- Semantic recall / owner check:
- `lean_leansearch` recalled the canonical site-level owners
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPullback`, and
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`.
- Local Chapter 34 precedent then fixed the big site over a scheme `S` as `Over S` with topology
  `S.overGrothendieckTopology @Etale`, and the adjoint pair as `Over.map f` and `Over.pullback f`.
-/

/-- The postcomposition functor on big étale over-categories induced by `f`. -/
abbrev bigEtaleMapFunctor : Over T ⥤ Over S :=
  Over.map f

/-- The pullback functor on big étale over-categories induced by `f`. -/
abbrev bigEtalePullbackFunctor : Over S ⥤ Over T :=
  Over.pullback f

/-- The postcomposition functor along `f` is continuous for the big étale topologies. -/
instance bigEtaleMapFunctor_isContinuous :
    Functor.IsContinuous (bigEtaleMapFunctor f) J_T J_S := sorry

/-- The inverse-image functor on sheaves induced by `f` on the big étale site. -/
abbrev bigEtaleInverseImage :
    Sheaf J_S (Type (u + 1)) ⥤ Sheaf J_T (Type (u + 1)) :=
  (bigEtaleMapFunctor f).sheafPushforwardContinuous
    (Type (u + 1)) J_T J_S

/-- The `Over.map f` presentation has the left-Kan-extension hypotheses needed to define the
lower shriek on big étale sheaves. -/
instance bigEtaleMapFunctor_op_hasLeftKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (bigEtaleMapFunctor f).op.HasLeftKanExtension P := sorry

/-- The `Over.map f` presentation has the right-Kan-extension hypotheses needed to compare the
continuous and cocontinuous direct images on big étale sheaves. -/
instance bigEtaleMapFunctor_op_hasPointwiseRightKanExtension
    (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (bigEtaleMapFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The lower shriek on big étale sheaves induced by `f`. -/
abbrev bigEtaleLowerShriek
    [HasWeakSheafify J_S (Type (u + 1))] :
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (bigEtaleMapFunctor f).sheafPullback
    (Type (u + 1)) J_T J_S

/-- Lemma 34.4.16 (1): the postcomposition functor
`u : (\mathit{Sch}/T)_{\acute{e}tale} ⥤ (\mathit{Sch}/S)_{\acute{e}tale}` induced by `f`
is cocontinuous. -/
@[stacks 021H]
instance bigEtaleMapFunctor_isCocontinuous :
    Functor.IsCocontinuous (bigEtaleMapFunctor f) J_T J_S := sorry

/-- Lemma 34.4.16 (2): the pullback functor
`v : (\mathit{Sch}/S)_{\acute{e}tale} ⥤ (\mathit{Sch}/T)_{\acute{e}tale}` is right adjoint to
the postcomposition functor `u`. -/
@[stacks 021H]
abbrev bigEtaleMapPullbackAdjunction :
    bigEtaleMapFunctor f ⊣ bigEtalePullbackFunctor f :=
  Over.mapPullbackAdj f

/-- Helper for Lemma 34.4.16: the adjunction on big étale over-categories exposes the usual
hom-set equivalence. -/
theorem bigEtaleMapPullbackAdjunction_homEquiv
    (U : Over T) (V : Over S) :
    (bigEtaleMapPullbackAdjunction f).homEquiv U V =
      (Over.mapPullbackAdj f).homEquiv U V := sorry

/-- Lemma 34.4.16 (3): the pullback functor
`v : (\mathit{Sch}/S)_{\acute{e}tale} ⥤ (\mathit{Sch}/T)_{\acute{e}tale}` is continuous. -/
@[stacks 021H]
instance bigEtalePullbackFunctor_isContinuous :
    Functor.IsContinuous (bigEtalePullbackFunctor f) J_S J_T := sorry

/-- The direct-image functor on sheaves induced by `f` on the big étale site. -/
abbrev bigEtaleDirectImage :
    Sheaf J_T (Type (u + 1)) ⥤ Sheaf J_S (Type (u + 1)) :=
  (bigEtalePullbackFunctor f).sheafPushforwardContinuous
    (Type (u + 1)) J_S J_T

/-- Lemma 34.4.16 (4): the continuous right-adjoint presentation and the cocontinuous
postcomposition presentation induce the same morphism of topoi; equivalently, their direct-image
functors are canonically isomorphic. -/
@[stacks 021H]
noncomputable def bigEtaleDirectImageIsoCocontinuous :
    bigEtaleDirectImage f ≅
      (bigEtaleMapFunctor f).sheafPushforwardCocontinuous
        (Type (u + 1)) J_T J_S :=
  continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
    (bigEtaleMapFunctor f) (bigEtalePullbackFunctor f) (Type (u + 1))
    (bigEtaleMapPullbackAdjunction f)

/-- Helper for Lemma 34.4.16: the forward comparison morphism in the direct-image comparison is an
isomorphism. -/
theorem bigEtaleDirectImageIsoCocontinuous_hom_isIso :
    IsIso
      ((bigEtaleDirectImageIsoCocontinuous f).hom :
        bigEtaleDirectImage f ⟶
          (bigEtaleMapFunctor f).sheafPushforwardCocontinuous
            (Type (u + 1)) J_T J_S) := sorry

/-- Lemma 34.4.16 (5): the inverse image of a big étale sheaf is computed by evaluation on the
same `T`-scheme, viewed over `S` by postcomposition with `f`. -/
@[stacks 021H]
theorem bigEtaleInverseImage_obj_obj
    (𝒢 : Sheaf J_S (Type (u + 1))) (U : Over T) :
    ((bigEtaleInverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((bigEtaleMapFunctor f).obj U)) := sorry

/-- Lemma 34.4.16 (6): the direct image of a big étale sheaf is computed by evaluation on the
pullback object `(U ×_S T)/T`. -/
@[stacks 021H]
theorem bigEtaleDirectImage_obj_obj
    (ℱ : Sheaf J_T (Type (u + 1))) (U : Over S) :
    ((bigEtaleDirectImage f).obj ℱ).1.obj (op U) =
      ℱ.1.obj (op ((bigEtalePullbackFunctor f).obj U)) := sorry

/-- Companion theorem recording that the lower-shriek functor has the expected adjunction API. -/
theorem bigEtaleLowerShriekAdjunction_isLeftAdjoint
    [HasWeakSheafify J_S (Type (u + 1))] :
    (bigEtaleLowerShriek f).IsLeftAdjoint := sorry

section LowerShriek

variable [HasWeakSheafify J_S (Type (u + 1))]

/-- Lemma 34.4.16 (7): the inverse image on big étale sheaves has a left adjoint, namely the
lower shriek `f_{big,!}`. -/
@[stacks 021H]
noncomputable def bigEtaleLowerShriekAdjunction :
    bigEtaleLowerShriek f ⊣ bigEtaleInverseImage f :=
  (bigEtaleMapFunctor f).sheafAdjunctionContinuous
    (Type (u + 1)) J_T J_S

/-- Lemma 34.4.16 (8): the lower shriek on big étale sheaves commutes with fibre products. -/
@[stacks 021H]
instance bigEtaleLowerShriek_preserves_pullbacks :
    PreservesLimitsOfShape WalkingCospan (bigEtaleLowerShriek f) := sorry

/-- Lemma 34.4.16 (9): the lower shriek on big étale sheaves commutes with equalizers. -/
@[stacks 021H]
instance bigEtaleLowerShriek_preserves_equalizers :
    PreservesLimitsOfShape WalkingParallelPair (bigEtaleLowerShriek f) := sorry

end LowerShriek

end

end AlgebraicGeometry
