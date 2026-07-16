import StacksProject_2024.stacks_project.Chap21.RingedSiteDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory hiding pre
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 21.35.7:
- primary domain: the tensor/internal-Hom comparison in the braided closed monoidal derived
  category `D(𝒪)` of sheaves of modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `DerivedCategory`,
  `MonoidalClosed.curry`,
  `MonoidalClosed.uncurry`,
  `MonoidalClosed.pre`,
  `CommSq`;
- best owner abstraction:
  `source-facing`: the canonical morphism
    `K ⊗^L_𝒪 RHom(M, L) ⟶ RHom(M, K ⊗^L_𝒪 L)`;
  `core/canonical`: `MonoidalClosed.curry` and `MonoidalClosed.uncurry` for the ambient
    tensor/internal-Hom adjunction in the derived category `D`;
  `bridge/view`: this file, which specializes that ambient owner construction to
    `D = RingedSiteDerived J 𝒪`.
- primitive data: the owner category `ringedSiteModuleCategory J 𝒪`, its derived category
  `D = RingedSiteDerived J 𝒪`, the braided closed monoidal structure on `D`, and the objects
  `K`, `L`, `M : D`;
- derived API: the comparison morphism, its uncurried specification, and the naturality square.

This item is therefore source-facing, and its implementation should reuse the ambient
closed-monoidal owner `MonoidalClosed.curry` directly rather than introducing a second
chapter-local wrapper for the transpose in the derived category itself. -/

/-- Lemma 21.35.7: for a ringed site `(𝒞, 𝒪)` and objects `K`, `L`, `M` of `D(𝒪)`, there is a
canonical morphism `K ⊗^L_𝒪 RHom(M, L) ⟶ RHom(M, K ⊗^L_𝒪 L)`.
In the closed monoidal formalization of `D(𝒪)`, `RHom(A, B)` is `(ihom A).obj B`, and this
morphism is the adjoint transpose of the map obtained by braiding `M` past `K` and then
evaluating `RHom(M, L)`. -/
@[stacks 0BYU]
noncomputable def ringedSiteDerivedTensorInternalHomComparison
    (K L M : D) :
    K ⊗ (M ⟹ L) ⟶ (M ⟹ (K ⊗ L)) :=
  curry
    ((α_ M K (M ⟹ L)).inv ≫
      (β_ M K).hom ▷ (M ⟹ L) ≫
      (α_ K M (M ⟹ L)).hom ≫
      K ◁ (ihom.ev M).app L)

/- Uncurrying the canonical tensor/internal-Hom comparison recovers the braiding/evaluation
composite used to define it. -/
@[simp] theorem ringedSiteDerivedTensorInternalHomComparison_uncurry
    (K L M : D) :
    uncurry (ringedSiteDerivedTensorInternalHomComparison K L M) =
      (α_ M K (M ⟹ L)).inv ≫
        (β_ M K).hom ▷ (M ⟹ L) ≫
        (α_ K M (M ⟹ L)).hom ≫
        K ◁ (ihom.ev M).app L := by
  simp [ringedSiteDerivedTensorInternalHomComparison]

/- Uncurrying precomposition by `fM` on the identity map gives the source-side evaluation formula
used in the naturality proofs below. -/
omit [BraidedCategory D] in
theorem ringedSiteDerivedTensorInternalHomComparison_uncurryPreApp
    {L M₁ M₂ : D}
    (fM : M₁ ⟶ M₂) :
    uncurry ((pre fM).app L) =
      fM ▷ (M₂ ⟹ L) ≫ (ihom.ev M₂).app L := by
  simpa using
    (MonoidalClosed.uncurry_pre_app L (𝟙 (M₂ ⟹ L)) fM)

/-- The tensor/internal-Hom comparison is natural in the tensor factor `K`. -/
theorem ringedSiteDerivedTensorInternalHomComparison_natural_tensor
    {K₁ K₂ L M : D}
    (fK : K₁ ⟶ K₂) :
    CommSq
      (fK ⊗ₘ 𝟙 (M ⟹ L))
      (ringedSiteDerivedTensorInternalHomComparison K₁ L M)
      (ringedSiteDerivedTensorInternalHomComparison K₂ L M)
      ((ihom M).map (fK ⊗ₘ 𝟙 L)) := by
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right]
  rw [ringedSiteDerivedTensorInternalHomComparison_uncurry,
    ringedSiteDerivedTensorInternalHomComparison_uncurry]
  simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_id, Category.comp_id]
  calc
    M ◁ fK ▷ (ihom M).obj L ≫
        (α_ M K₂ ((ihom M).obj L)).inv ≫
        (β_ M K₂).hom ▷ (ihom M).obj L ≫
        (α_ K₂ M ((ihom M).obj L)).hom ≫
        K₂ ◁ (ihom.ev M).app L =
      (α_ M K₁ ((ihom M).obj L)).inv ≫
        (M ◁ fK) ▷ (ihom M).obj L ≫
        (β_ M K₂).hom ▷ (ihom M).obj L ≫
        (α_ K₂ M ((ihom M).obj L)).hom ≫
        K₂ ◁ (ihom.ev M).app L := by
          rw [MonoidalCategory.associator_inv_naturality_middle_assoc]
    _ =
      (α_ M K₁ ((ihom M).obj L)).inv ≫
        (β_ M K₁).hom ▷ (ihom M).obj L ≫
        (fK ▷ M) ▷ (ihom M).obj L ≫
        (α_ K₂ M ((ihom M).obj L)).hom ≫
        K₂ ◁ (ihom.ev M).app L := by
          rw [← MonoidalCategory.comp_whiskerRight_assoc]
          rw [BraidedCategory.braiding_naturality_right]
          rw [MonoidalCategory.comp_whiskerRight_assoc]
    _ =
      (α_ M K₁ ((ihom M).obj L)).inv ≫
        (β_ M K₁).hom ▷ (ihom M).obj L ≫
        (α_ K₁ M ((ihom M).obj L)).hom ≫
        fK ▷ (M ⊗ (ihom M).obj L) ≫
        K₂ ◁ (ihom.ev M).app L := by
          rw [MonoidalCategory.associator_naturality_left_assoc]
    _ =
      ((α_ M K₁ ((ihom M).obj L)).inv ≫
          (β_ M K₁).hom ▷ (ihom M).obj L ≫
          (α_ K₁ M ((ihom M).obj L)).hom ≫
          K₁ ◁ (ihom.ev M).app L) ≫
        fK ▷ L := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M K₁ ((ihom M).obj L)).inv ≫
                  (β_ M K₁).hom ▷ (ihom M).obj L ≫
                  (α_ K₁ M ((ihom M).obj L)).hom ≫ k)
              (MonoidalCategory.whisker_exchange fK ((ihom.ev M).app L)).symm

/-- The tensor/internal-Hom comparison is natural in the target object `L`. -/
theorem ringedSiteDerivedTensorInternalHomComparison_natural_target
    (K M : D)
    {L₁ L₂ : D}
    (fL : L₁ ⟶ L₂) :
    CommSq
      (𝟙 K ⊗ₘ (ihom M).map fL)
      (ringedSiteDerivedTensorInternalHomComparison K L₁ M)
      (ringedSiteDerivedTensorInternalHomComparison K L₂ M)
      ((ihom M).map (𝟙 K ⊗ₘ fL)) := by
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right]
  rw [ringedSiteDerivedTensorInternalHomComparison_uncurry,
    ringedSiteDerivedTensorInternalHomComparison_uncurry]
  simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight_assoc]
  calc
    M ◁ K ◁ (ihom M).map fL ≫
        (α_ M K ((ihom M).obj L₂)).inv ≫
        (β_ M K).hom ▷ (ihom M).obj L₂ ≫
        (α_ K M ((ihom M).obj L₂)).hom ≫
        K ◁ (ihom.ev M).app L₂ =
      (α_ M K ((ihom M).obj L₁)).inv ≫
        (M ⊗ K) ◁ (ihom M).map fL ≫
        (β_ M K).hom ▷ (ihom M).obj L₂ ≫
        (α_ K M ((ihom M).obj L₂)).hom ≫
        K ◁ (ihom.ev M).app L₂ := by
          rw [MonoidalCategory.associator_inv_naturality_right_assoc]
    _ =
      (α_ M K ((ihom M).obj L₁)).inv ≫
        (β_ M K).hom ▷ (ihom M).obj L₁ ≫
        (K ⊗ M) ◁ (ihom M).map fL ≫
        (α_ K M ((ihom M).obj L₂)).hom ≫
        K ◁ (ihom.ev M).app L₂ := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M K ((ihom M).obj L₁)).inv ≫ k ≫
                  (α_ K M ((ihom M).obj L₂)).hom ≫
                  K ◁ (ihom.ev M).app L₂)
              (MonoidalCategory.whisker_exchange (β_ M K).hom ((ihom M).map fL))
    _ =
      (α_ M K ((ihom M).obj L₁)).inv ≫
        (β_ M K).hom ▷ (ihom M).obj L₁ ≫
        (α_ K M ((ihom M).obj L₁)).hom ≫
        K ◁ M ◁ (ihom M).map fL ≫
        K ◁ (ihom.ev M).app L₂ := by
          rw [MonoidalCategory.associator_naturality_right_assoc]
    _ =
      ((α_ M K ((ihom M).obj L₁)).inv ≫
          (β_ M K).hom ▷ (ihom M).obj L₁ ≫
          (α_ K M ((ihom M).obj L₁)).hom ≫
          K ◁ (ihom.ev M).app L₁) ≫
        K ◁ fL := by
          have hEv :
              M ◁ (ihom M).map fL ≫ (ihom.ev M).app L₂ =
                (ihom.ev M).app L₁ ≫ fL := by
            simpa using (ihom.ev_naturality M fL)
          simpa [MonoidalCategory.whiskerLeft_comp, Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M K ((ihom M).obj L₁)).inv ≫
                  (β_ M K).hom ▷ (ihom M).obj L₁ ≫
                  (α_ K M ((ihom M).obj L₁)).hom ≫ K ◁ k)
              hEv

/-- The tensor/internal-Hom comparison is contravariantly natural in the source object `M`. -/
theorem ringedSiteDerivedTensorInternalHomComparison_natural_source
    (K L : D)
    {M₁ M₂ : D}
    (fM : M₁ ⟶ M₂) :
    CommSq
      (𝟙 K ⊗ₘ (pre fM).app L)
      (ringedSiteDerivedTensorInternalHomComparison K L M₂)
      (ringedSiteDerivedTensorInternalHomComparison K L M₁)
      ((pre fM).app (K ⊗ L)) := by
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
  rw [ringedSiteDerivedTensorInternalHomComparison_uncurry,
    ringedSiteDerivedTensorInternalHomComparison_uncurry]
  simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight_assoc]
  calc
    M₁ ◁ K ◁ (pre fM).app L ≫
        (α_ M₁ K ((ihom M₁).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₁).obj L ≫
        (α_ K M₁ ((ihom M₁).obj L)).hom ≫
        K ◁ (ihom.ev M₁).app L =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (M₁ ⊗ K) ◁ (pre fM).app L ≫
        (β_ M₁ K).hom ▷ (ihom M₁).obj L ≫
        (α_ K M₁ ((ihom M₁).obj L)).hom ≫
        K ◁ (ihom.ev M₁).app L := by
          rw [MonoidalCategory.associator_inv_naturality_right_assoc]
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
        (K ⊗ M₁) ◁ (pre fM).app L ≫
        (α_ K M₁ ((ihom M₁).obj L)).hom ≫
        K ◁ (ihom.ev M₁).app L := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M₁ K ((ihom M₂).obj L)).inv ≫ k ≫
                  (α_ K M₁ ((ihom M₁).obj L)).hom ≫
                  K ◁ (ihom.ev M₁).app L)
              (MonoidalCategory.whisker_exchange (β_ M₁ K).hom ((pre fM).app L))
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
        (α_ K M₁ ((ihom M₂).obj L)).hom ≫
        K ◁ M₁ ◁ (pre fM).app L ≫
        K ◁ (ihom.ev M₁).app L := by
          rw [MonoidalCategory.associator_naturality_right_assoc]
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
        (α_ K M₁ ((ihom M₂).obj L)).hom ≫
        K ◁ (fM ▷ (ihom M₂).obj L) ≫
        K ◁ (ihom.ev M₂).app L := by
          simpa [MonoidalClosed.uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M₁ K ((ihom M₂).obj L)).inv ≫
                  (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
                  (α_ K M₁ ((ihom M₂).obj L)).hom ≫ K ◁ k)
              (ringedSiteDerivedTensorInternalHomComparison_uncurryPreApp fM)
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
        (K ◁ fM) ▷ (ihom M₂).obj L ≫
        (α_ K M₂ ((ihom M₂).obj L)).hom ≫
        K ◁ (ihom.ev M₂).app L := by
          rw [← MonoidalCategory.associator_naturality_middle_assoc]
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (fM ▷ K) ▷ (ihom M₂).obj L ≫
        (β_ M₂ K).hom ▷ (ihom M₂).obj L ≫
        (α_ K M₂ ((ihom M₂).obj L)).hom ≫
        K ◁ (ihom.ev M₂).app L := by
          rw [← MonoidalCategory.comp_whiskerRight_assoc]
          rw [← BraidedCategory.braiding_naturality_left]
          rw [MonoidalCategory.comp_whiskerRight_assoc]
    _ =
      fM ▷ (K ⊗ (ihom M₂).obj L) ≫
        (α_ M₂ K ((ihom M₂).obj L)).inv ≫
        (β_ M₂ K).hom ▷ (ihom M₂).obj L ≫
        (α_ K M₂ ((ihom M₂).obj L)).hom ≫
        K ◁ (ihom.ev M₂).app L := by
          rw [MonoidalCategory.associator_inv_naturality_left_assoc]

/- The tensor-internal-Hom comparison is functorial in `K` and `L`, and contravariantly
functorial in `M`. -/
theorem ringedSiteDerivedTensorInternalHomComparison_natural
    {K₁ K₂ L₁ L₂ M₁ M₂ : D}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (fK ⊗ₘ ((pre fM).app L₁ ≫ (ihom M₁).map fL))
      (ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₂)
      (ringedSiteDerivedTensorInternalHomComparison K₂ L₂ M₁)
      ((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := by
  let hSource :
      CommSq
        (𝟙 K₁ ⊗ₘ (pre fM).app L₁)
        (ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₂)
        (ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₁)
        ((pre fM).app (K₁ ⊗ L₁)) :=
    ringedSiteDerivedTensorInternalHomComparison_natural_source K₁ L₁ fM
  let hTensor :
      CommSq
        (fK ⊗ₘ 𝟙 (M₁ ⟹ L₁))
        (ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₁)
        (ringedSiteDerivedTensorInternalHomComparison K₂ L₁ M₁)
        ((ihom M₁).map (fK ⊗ₘ 𝟙 L₁)) :=
    ringedSiteDerivedTensorInternalHomComparison_natural_tensor fK
  let hTarget :
      CommSq
        (𝟙 K₂ ⊗ₘ (ihom M₁).map fL)
        (ringedSiteDerivedTensorInternalHomComparison K₂ L₁ M₁)
        (ringedSiteDerivedTensorInternalHomComparison K₂ L₂ M₁)
        ((ihom M₁).map (𝟙 K₂ ⊗ₘ fL)) :=
    ringedSiteDerivedTensorInternalHomComparison_natural_target K₂ M₁ fL
  have hComposite := (CommSq.horiz_comp (CommSq.horiz_comp hSource hTensor) hTarget).w
  have hTop :
      fK ⊗ₘ ((pre fM).app L₁ ≫ (ihom M₁).map fL) =
        ((𝟙 K₁ ⊗ₘ (pre fM).app L₁) ≫ (fK ⊗ₘ 𝟙 ((ihom M₁).obj L₁))) ≫
          (𝟙 K₂ ⊗ₘ (ihom M₁).map fL) := by
        simpa [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp,
          Category.assoc] using
          (MonoidalCategory.whisker_exchange_assoc fK ((pre fM).app L₁)
            (K₂ ◁ (ihom M₁).map fL)).symm
  have hMap :
      (ihom M₁).map (fK ▷ L₁) ≫ (ihom M₁).map (K₂ ◁ fL) =
        (ihom M₁).map (fK ⊗ₘ fL) := by
        simpa [Functor.map_comp, MonoidalCategory.tensorHom_def] using
          congrArg ((ihom M₁).map) (MonoidalCategory.tensorHom_def fK fL).symm
  have hBottom :
      ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₂ ≫
          ((((pre fM).app (K₁ ⊗ L₁)) ≫ (ihom M₁).map (fK ⊗ₘ 𝟙 L₁)) ≫
            (ihom M₁).map (𝟙 K₂ ⊗ₘ fL)) =
        ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₂ ≫
          (((pre fM).app (K₁ ⊗ L₁)) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₂ ≫
                (pre fM).app (K₁ ⊗ L₁) ≫ k)
            hMap
  refine CommSq.mk ?_
  calc
    (fK ⊗ₘ ((pre fM).app L₁ ≫ (ihom M₁).map fL)) ≫
        ringedSiteDerivedTensorInternalHomComparison K₂ L₂ M₁ =
      (((𝟙 K₁ ⊗ₘ (pre fM).app L₁) ≫
            (fK ⊗ₘ 𝟙 ((ihom M₁).obj L₁))) ≫
          (𝟙 K₂ ⊗ₘ (ihom M₁).map fL)) ≫
        ringedSiteDerivedTensorInternalHomComparison K₂ L₂ M₁ := by
          simpa using congrArg
            (fun k ↦ k ≫ ringedSiteDerivedTensorInternalHomComparison K₂ L₂ M₁)
            hTop
    _ =
      ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₂ ≫
        ((((pre fM).app (K₁ ⊗ L₁)) ≫ (ihom M₁).map (fK ⊗ₘ 𝟙 L₁)) ≫
          (ihom M₁).map (𝟙 K₂ ⊗ₘ fL)) := hComposite
    _ =
      ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₂ ≫
        (((pre fM).app (K₁ ⊗ L₁)) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := hBottom

end

end SheafOfModules.RingedSite
