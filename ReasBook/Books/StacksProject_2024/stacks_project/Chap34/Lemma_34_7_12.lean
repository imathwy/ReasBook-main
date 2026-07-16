import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: `lean_leansearch` surfaced the slice-site owners
-- `GrothendieckTopology.overMapPullback`,
-- `Functor.sheafPushforwardContinuous`,
-- and `Functor.morphismOfTopoiInOfCocontinuous`; local project precedent then matched these with
-- `Over.map`, `Over.pullback`, and `Over.mapPullbackAdj`.

variable {S T : Scheme.{u}}

/-- Lemma 34.7.12 (1): the relocalization functor
`(Sch/T)_{fppf} ⥤ (Sch/S)_{fppf}` sending `V/T` to `V/S` is cocontinuous. -/
theorem bigFppfMap_isCocontinuous (f : T ⟶ S) :
    Functor.IsCocontinuous (Over.map f)
      (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S) := sorry

/-- Lemma 34.7.12 (2): the relocalization functor `Over.map f` has right adjoint
`Over.pullback f`. -/
abbrev bigFppfMapPullbackAdjunction (f : T ⟶ S) :
    Over.map f ⊣ Over.pullback f :=
  Over.mapPullbackAdj f

/-- Lemma 34.7.12 (3): the pullback functor
`(Sch/S)_{fppf} ⥤ (Sch/T)_{fppf}` sending `U/S` to `U ×_S T/T` is continuous. -/
theorem bigFppfPullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (Over.pullback f)
      (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over T) := sorry

/-- The inverse-image functor `f_big⁻¹` for the big fppf morphism associated to `f`, realized as
the canonical slice-site pullback `Scheme.fppfTopology.overMapPullback`. -/
abbrev bigFppfInverseImage (f : T ⟶ S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) ⥤
      Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) :=
  Scheme.fppfTopology.overMapPullback (Type (u + 1)) f

/-- Lemma 34.7.12 (4): evaluating `f_big⁻¹ 𝒢` on an object `U/T` is evaluation of `𝒢` on the
same scheme viewed over `S`. -/
theorem bigFppfInverseImage_obj_obj
    (f : T ⟶ S)
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) (U : Over T) :
    (((bigFppfInverseImage f).obj 𝒢).obj.obj (op U)) =
      𝒢.obj.obj (op ((Over.map f).obj U)) := sorry

/-- The direct-image functor `f_big,*` for the big fppf morphism associated to `f`, presented by
the cocontinuous relocalization morphism of topoi attached to `Over.map f`. -/
abbrev bigFppfDirectImage (f : T ⟶ S) :
    Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) ⥤
      Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (Over.map f).sheafPushforwardCocontinuous (Type (u + 1))
    (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)

/-- Lemma 34.7.12 (5): evaluating `f_big,* ℱ` on an object `U/S` is canonically identified with
evaluation of `ℱ` on the pullback object `U ×_S T/T`. -/
noncomputable def bigFppfDirectImage_objObjIso
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))) (U : Over S) :
    (((bigFppfDirectImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((Over.pullback f).obj U)) :=
  let pushforwardIso :
      bigFppfDirectImage f ≅
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over T) :=
    (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
      (Over.map f) (Over.pullback f) (Type (u + 1)) (Over.mapPullbackAdj f)).symm
  let e :
      (((bigFppfDirectImage f).obj ℱ).obj) ≅ (Over.pullback f).op ⋙ ℱ.obj :=
    ((Functor.isoWhiskerRight pushforwardIso
      (sheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1)))).app ℱ) ≪≫
      ((Over.pullback f).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (u + 1)) (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over T)).app ℱ
  e.app (op U)

/-- Helper for Lemma 34.7.12: the comparison morphism computing the direct image on `U/S` is an
isomorphism. -/
theorem bigFppfDirectImage_objObjIso_hom_isIso
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))) (U : Over S) :
    IsIso ((bigFppfDirectImage_objObjIso f ℱ U).hom) := by
  infer_instance

/-- The lower shriek functor `f_big,!`, realized as the canonical left adjoint to
`bigFppfInverseImage f`. -/
abbrev bigFppfLowerShriek (f : T ⟶ S) :
    Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) ⥤
      Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (Over.map f).sheafPullback (Type (u + 1))
    (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)

/-- The canonical adjunction `f_big,! ⊣ f_big⁻¹`. -/
noncomputable def bigFppfLowerShriekAdjunction (f : T ⟶ S) :
    bigFppfLowerShriek f ⊣ bigFppfInverseImage f :=
  (Over.map f).sheafAdjunctionContinuous (Type (u + 1))
    (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)

/-- The inverse-image functor `f_big⁻¹` is a right adjoint. -/
theorem bigFppfInverseImage_isRightAdjoint (f : T ⟶ S) :
    (bigFppfInverseImage f).IsRightAdjoint :=
  (bigFppfLowerShriekAdjunction f).isRightAdjoint

/-- The canonical left adjoint `f_big,!` preserves fibre products. -/
theorem bigFppfLowerShriek_preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (bigFppfLowerShriek f) := sorry

/-- The canonical left adjoint `f_big,!` preserves equalizers. -/
theorem bigFppfLowerShriek_preservesEqualizers (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (bigFppfLowerShriek f) := sorry

/-- Lemma 34.7.12 (6): the inverse-image functor `f_big⁻¹` has a left adjoint which commutes
with fibre products and equalizers. -/
theorem bigFppfInverseImage_hasLeftAdjoint_preserving_pullbacks_equalizers
    (f : T ⟶ S) :
    (bigFppfInverseImage f).IsRightAdjoint ∧
      PreservesLimitsOfShape WalkingCospan (bigFppfLowerShriek f) ∧
        PreservesLimitsOfShape WalkingParallelPair (bigFppfLowerShriek f) := by
  exact ⟨bigFppfInverseImage_isRightAdjoint f,
    bigFppfLowerShriek_preservesPullbacks f,
    bigFppfLowerShriek_preservesEqualizers f⟩

end Scheme
end AlgebraicGeometry
