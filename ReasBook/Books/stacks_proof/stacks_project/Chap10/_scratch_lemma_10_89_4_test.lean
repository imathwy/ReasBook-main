import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_11_1
import stacks_proof.stacks_project.Chap10.Lemma_10_88_3

universe u v z

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
open ULift

namespace ScratchLemma10894

namespace LinearMap

/-- Scratch helper: `ModuleCat.uliftFunctor` preserves filtered colimits. -/
private noncomputable def uliftFunctorPreservesColimitsOfShape
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{z, v} R) := by
  let e :
      ModuleCat.uliftFunctor.{z, v} R ⋙ forget (ModuleCat.{max v z} R) ≅
        forget (ModuleCat.{v} R) ⋙ CategoryTheory.uliftFunctor.{z} :=
    ModuleCat.uliftFunctorForgetIso (R := R)
  letI : PreservesColimitsOfShape J (forget (ModuleCat.{v} R) ⋙ CategoryTheory.uliftFunctor.{z}) :=
    by infer_instance
  letI : PreservesColimitsOfShape J
      (ModuleCat.uliftFunctor.{z, v} R ⋙ forget (ModuleCat.{max v z} R)) :=
    preservesColimitsOfShape_of_natIso e.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (ModuleCat.uliftFunctor.{z, v} R) (forget (ModuleCat.{max v z} R))

/-- Scratch helper: transporting through `TensorProduct.congr` removes the `ULift` inserted by
`ModuleCat.uliftFunctor.map`. -/
private lemma uliftFunctor_map_lTensor_transport
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type v} [AddCommGroup W] [Module R W]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (f : V →ₗ[R] W) :
    let eV : Q ⊗[R] ULift.{z} V ≃ₗ[R] Q ⊗[R] V :=
      TensorProduct.congr (LinearEquiv.refl R Q)
        (ULift.moduleEquiv : ULift.{z} V ≃ₗ[R] V)
    let eW : Q ⊗[R] ULift.{z} W ≃ₗ[R] Q ⊗[R] W :=
      TensorProduct.congr (LinearEquiv.refl R Q)
        (ULift.moduleEquiv : ULift.{z} W ≃ₗ[R] W)
    eW.toLinearMap.comp
        ((((ModuleCat.uliftFunctor.{z, v} R).map (ModuleCat.ofHom f)).hom).lTensor Q) =
      (f.lTensor Q).comp eV.toLinearMap := by
  ext q v
  rfl

example
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    {M : Type v} [AddCommGroup M] [Module R M]
    {Q : Type z} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of.{v} R M))
    {j : J} {y : Q ⊗[R] pres.diag.obj j}
    (hy : ((pres.ι.app j).hom.lTensor Q) y = 0) :
    ∃ (j' : J) (w : j ⟶ j'), ((pres.diag.map w).hom.lTensor Q) y = 0 := by
  let _ := uliftFunctorPreservesColimitsOfShape (R := R) (J := J) (z := z)
  let presU : ColimitPresentation J (ModuleCat.of.{max v z} R (ULift.{z} M)) :=
    ColimitPresentation.map pres (ModuleCat.uliftFunctor.{z, v} R)
  let eStage : Q ⊗[R] presU.diag.obj j ≃ₗ[R] Q ⊗[R] pres.diag.obj j :=
    TensorProduct.congr (LinearEquiv.refl R Q)
      (ULift.moduleEquiv : ULift.{z} (pres.diag.obj j) ≃ₗ[R] pres.diag.obj j)
  let eTarget : Q ⊗[R] ULift.{z} M ≃ₗ[R] Q ⊗[R] M :=
    TensorProduct.congr (LinearEquiv.refl R Q)
      (ULift.moduleEquiv : ULift.{z} M ≃ₗ[R] M)
  let yU : Q ⊗[R] presU.diag.obj j := eStage.symm y
  have hleg_transport :
      eTarget.toLinearMap.comp ((presU.ι.app j).hom.lTensor Q) =
        ((pres.ι.app j).hom.lTensor Q).comp eStage.toLinearMap := by
    simpa [presU, eStage, eTarget] using
      (uliftFunctor_map_lTensor_transport (R := R) (Q := Q) ((pres.ι.app j).hom))
  have hyU : ((presU.ι.app j).hom.lTensor Q) yU = 0 := by
    apply eTarget.injective
    calc
      eTarget (((presU.ι.app j).hom.lTensor Q) yU)
          = ((pres.ι.app j).hom.lTensor Q) (eStage yU) := by
              simpa [LinearMap.comp_apply] using congrArg (fun k ↦ k yU) hleg_transport
      _ = 0 := by
            simpa [yU] using hy
  obtain ⟨j', w, hwU_zero⟩ :=
    LinearMap.exists_later_stage_lTensor_eq_zero
      (R := R) (J := J) (L := Q) (Q := ULift.{z} M) (pres := presU) (j := j) hyU
  let eLater : Q ⊗[R] presU.diag.obj j' ≃ₗ[R] Q ⊗[R] pres.diag.obj j' :=
    TensorProduct.congr (LinearEquiv.refl R Q)
      (ULift.moduleEquiv : ULift.{z} (pres.diag.obj j') ≃ₗ[R] pres.diag.obj j')
  have hmap_transport :
      eLater.toLinearMap.comp ((presU.diag.map w).hom.lTensor Q) =
        ((pres.diag.map w).hom.lTensor Q).comp eStage.toLinearMap := by
    simpa [presU, eStage, eLater] using
      (uliftFunctor_map_lTensor_transport (R := R) (Q := Q) ((pres.diag.map w).hom))
  refine ⟨j', w, ?_⟩
  calc
    ((pres.diag.map w).hom.lTensor Q) y
        = eLater (((presU.diag.map w).hom.lTensor Q) yU) := by
            symm
            simpa [LinearMap.comp_apply, yU] using congrArg (fun k ↦ k yU) hmap_transport
    _ = 0 := by
          simpa using congrArg (fun t ↦ eLater t) hwU_zero

end LinearMap

end ScratchLemma10894
