import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_15_1_Topoi
import StacksProject_2024.stacks_project.Chap07.Lemma_7_21_1
import StacksProject_2024.stacks_project.Chap07.Lemma_7_21_6
import StacksProject_2024.stacks_project.Chap07.Lemma_7_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the site-level sheaf pushforward owners, and nearby
-- Chapter 7 slice-site files verified `Over.map f`, `Over.pullback f`, and `Over.mapPullbackAdj f`
-- as the canonical API for the two site presentations in this lemma.

section

variable (Jph : GrothendieckTopology Scheme.{u})
variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- Lemma 34.8.16 (1): for a chosen big ph topology `Jph` on schemes and a morphism `f : T ⟶ S`,
the associated big ph morphism of topoi
`f_big : Sh((\mathit{Sch}/T)_{ph}) ⟶ Sh((\mathit{Sch}/S)_{ph})` is the morphism of topoi
whose inverse image is the continuous sheaf functor attached to
`Over.map f : Over T ⥤ Over S` and whose direct image is the cocontinuous pushforward along the
same functor. -/
abbrev bigPhMorphismOfTopoi
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [HasSheafify (Jph.over T) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn (Jph.over S) (Jph.over T) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((Over.map f).sheafPushforwardContinuous (Type w) (Jph.over T) (Jph.over S))
  pushforward := (Over.map f).sheafPushforwardCocontinuous (Type w) (Jph.over T) (Jph.over S)
  adjunction := (Over.map f).sheafAdjunctionCocontinuous (Type w) (Jph.over T) (Jph.over S)

@[simp] theorem bigPhMorphismOfTopoi_inverseImage
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [HasSheafify (Jph.over T) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P] :
    (bigPhMorphismOfTopoi Jph f)⁻¹ =
      (Over.map f).sheafPushforwardContinuous (Type w) (Jph.over T) (Jph.over S) :=
  rfl

@[simp] theorem bigPhMorphismOfTopoi_pushforward
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [HasSheafify (Jph.over T) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P] :
    (bigPhMorphismOfTopoi Jph f).pushforward =
      (Over.map f).sheafPushforwardCocontinuous (Type w) (Jph.over T) (Jph.over S) :=
  rfl

/-- Lemma 34.8.16 (2): the direct-image functor of `f_big`, presented cocontinuously by
`Over.map f`, is canonically isomorphic to the continuous direct-image functor attached to the
right adjoint `Over.pullback f : Over S ⥤ Over T`. This is the comparison expressing that the two
site presentations induce the same morphism of topoi. -/
noncomputable def bigPhMorphismOfTopoi_pushforwardIso_pullbackPresentation
    [HasPullbacksAlong f]
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [HasSheafify (Jph.over T) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (Over.pullback f) (Jph.over S) (Jph.over T)] :
    (bigPhMorphismOfTopoi Jph f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type w) (Jph.over S) (Jph.over T) :=
  by
    simpa using
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        (Over.map f) (Over.pullback f) (Type w) (Over.mapPullbackAdj f)).symm

/-- Lemma 34.8.16 (4): for a sheaf `𝒢` on `(\mathit{Sch}/S)_{ph}` and an object `U/T`, the
inverse image `f_big^{-1} 𝒢` has sections on `U/T` canonically identified with the sections of
`𝒢` on the same underlying object viewed over `S`. -/
noncomputable def bigPhMorphismOfTopoi_inverseImage_obj_obj_iso
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [HasSheafify (Jph.over T) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P]
    (𝒢 : Sheaf (Jph.over S) (Type w)) (U : Over T) :
    ((((bigPhMorphismOfTopoi Jph f)⁻¹).obj 𝒢).obj.obj (op U)) ≅
      𝒢.obj.obj (op ((Over.map f).obj U)) :=
  by
    simpa using
      (((Over.map f).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type w) (Jph.over T) (Jph.over S)).app 𝒢).app (op U)

/-- Lemma 34.8.16 (5): for a sheaf `ℱ` on `(\mathit{Sch}/T)_{ph}` and an object `U/S`, the
direct image `f_{big,*} ℱ` has sections on `U/S` canonically identified with the sections of `ℱ`
on the base-change object `(U ×_S T)/T`. -/
noncomputable def bigPhMorphismOfTopoi_pushforward_obj_obj_iso
    [HasPullbacksAlong f]
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [HasSheafify (Jph.over T) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (Over.pullback f) (Jph.over S) (Jph.over T)]
    (ℱ : Sheaf (Jph.over T) (Type w)) (U : Over S) :
    (((bigPhMorphismOfTopoi Jph f).pushforward.obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((Over.pullback f).obj U)) :=
  by
    simpa using
      (((Functor.isoWhiskerRight
          (bigPhMorphismOfTopoi_pushforwardIso_pullbackPresentation Jph f)
          (sheafToPresheaf (Jph.over S) (Type w))).app ℱ).app (op U)) ≪≫
        (((Over.pullback f).sheafPushforwardContinuousCompSheafToPresheafIso
          (Type w) (Jph.over S) (Jph.over T)).app ℱ).app (op U)

/-- A source-faithful name for the lower-shriek functor `f_{big,!}`, realized by the continuous
sheaf pullback functor attached to `Over.map f`. -/
abbrev bigPhLowerShriek
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P] :
    Sheaf (Jph.over T) (Type w) ⥤ Sheaf (Jph.over S) (Type w) :=
  (Over.map f).sheafPullback (Type w) (Jph.over T) (Jph.over S)

/-- Lemma 34.8.16 (7): the lower-shriek functor `f_{big,!}` is left adjoint to the inverse-image
functor `f_big^{-1}`. -/
noncomputable abbrev bigPhLowerShriek_adjunction
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [HasSheafify (Jph.over T) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P] :
    bigPhLowerShriek Jph f ⊣ (bigPhMorphismOfTopoi Jph f)⁻¹ :=
  by
    simpa using
      (Over.map f).sheafAdjunctionContinuous (Type w) (Jph.over T) (Jph.over S)

/-- Lemma 34.8.16 (8): the lower-shriek functor `f_{big,!}` commutes with fibre products. -/
theorem bigPhLowerShriek_preserves_pullbacks
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [HasPullbacks (Over T)] [HasEqualizers (Over T)]
    [PreservesLimitsOfShape WalkingCospan (Over.map f)]
    [PreservesLimitsOfShape WalkingParallelPair (Over.map f)] :
    PreservesLimitsOfShape WalkingCospan (bigPhLowerShriek Jph f) := by
  simpa using
    (sheafPullback_preserves_pullbacks (Over.map f) :
      PreservesLimitsOfShape WalkingCospan
        ((Over.map f).sheafPullback (Type w) (Jph.over T) (Jph.over S)))

/-- Lemma 34.8.16 (9): the lower-shriek functor `f_{big,!}` commutes with equalizers. -/
theorem bigPhLowerShriek_preserves_equalizers
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [HasPullbacks (Over T)] [HasEqualizers (Over T)]
    [PreservesLimitsOfShape WalkingCospan (Over.map f)]
    [PreservesLimitsOfShape WalkingParallelPair (Over.map f)] :
    PreservesLimitsOfShape WalkingParallelPair (bigPhLowerShriek Jph f) := by
  simpa using
    (sheafPullback_preserves_equalizers (Over.map f) :
      PreservesLimitsOfShape WalkingParallelPair
        ((Over.map f).sheafPullback (Type w) (Jph.over T) (Jph.over S)))

end

end AlgebraicGeometry
