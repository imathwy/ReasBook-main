import StacksProject_2024.stacks_project.Chap21.Lemma_21_34_3_Owner

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [BraidedCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ
set_option quotPrecheck false in
local notation:20 A " ⟶[CpxO] " B:19 => (ihom A).obj B

/- Domain-style sampling for Lemma 21.34.3:
- primary domain: tensor-internal-Hom comparison in the closed braided monoidal category of
  cochain complexes of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleComplexTensorInternalHomComparison`,
  `ringedSiteModuleComplexTensorInternalHomComparison_uncurry`,
  the canonical internal-Hom notation `A ⟶[CpxO] B`;
- best owner abstraction:
  the owner module `Lemma_21_34_3_Owner` provides the source-facing comparison morphism and its
  basic `uncurry` specification on `CpxO`, while this file adds the naturality API needed
  downstream;
- primitive data:
  the complexes `K`, `L`, and `M`;
- derived API:
  the naturality squares for the owner morphism.

Source/core/bridge triage:
- `source-facing`: Lemma 21.34.3;
- `core/canonical`: `ringedSiteModuleComplexTensorInternalHomComparison` together with its
  owner theorem `ringedSiteModuleComplexTensorInternalHomComparison_uncurry`;
- `bridge/view`: the ringed-site specialization of the ambient complex category `CpxO`. -/

/-- Helper for Lemma 21.34.3: the canonical tensor-internal-Hom comparison morphism
`K ⊗ (M ⟶[CpxO] L) ⟶ (M ⟶[CpxO] (K ⊗ L))` on complexes of `𝒪`-modules. -/
@[stacks 0BYT]
noncomputable abbrev tensorInternalHomComparison
    (K L M : CpxO) :
    K ⊗ (M ⟶[CpxO] L) ⟶ (M ⟶[CpxO] (K ⊗ L)) :=
  ringedSiteModuleComplexTensorInternalHomComparison K L M

/- Uncurrying precomposition by `fM` on the identity map gives the source-side evaluation
formula used in the naturality proof below. -/
omit [BraidedCategory CpxO] in
theorem ringedSiteModuleComplexTensorInternalHomComparison_uncurryPreApp
    {L M₁ M₂ : CpxO}
    (fM : M₁ ⟶ M₂) :
    uncurry ((MonoidalClosed.pre fM).app L) =
      fM ▷ (M₂ ⟶[CpxO] L) ≫ (ihom.ev M₂).app L := by
  simpa using
    (MonoidalClosed.uncurry_pre_app L (𝟙 (M₂ ⟶[CpxO] L)) fM)

/-- The tensor-internal-Hom comparison is natural in the tensor factor `K`. -/
theorem ringedSiteModuleComplexTensorInternalHomComparison_natural_tensor
    {K₁ K₂ L M : CpxO}
    (fK : K₁ ⟶ K₂) :
    CommSq
      (fK ⊗ₘ 𝟙 (M ⟶[CpxO] L))
      (ringedSiteModuleComplexTensorInternalHomComparison K₁ L M)
      (ringedSiteModuleComplexTensorInternalHomComparison K₂ L M)
      ((ihom M).map (fK ⊗ₘ 𝟙 L)) := by
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right]
  rw [ringedSiteModuleComplexTensorInternalHomComparison_uncurry,
    ringedSiteModuleComplexTensorInternalHomComparison_uncurry]
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
      (α_ M K₁ ((ihom M).obj L)).inv ≫
        (β_ M K₁).hom ▷ (ihom M).obj L ≫
        (α_ K₁ M ((ihom M).obj L)).hom ≫
        K₁ ◁ (ihom.ev M).app L ≫
        fK ▷ L := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M K₁ ((ihom M).obj L)).inv ≫
                  (β_ M K₁).hom ▷ (ihom M).obj L ≫
                  (α_ K₁ M ((ihom M).obj L)).hom ≫ k)
              (MonoidalCategory.whisker_exchange fK ((ihom.ev M).app L)).symm

/-- The tensor-internal-Hom comparison is natural in the target complex `L`. -/
theorem ringedSiteModuleComplexTensorInternalHomComparison_natural_target
    (K M : CpxO)
    {L₁ L₂ : CpxO}
    (fL : L₁ ⟶ L₂) :
    CommSq
      (𝟙 K ⊗ₘ (ihom M).map fL)
      (ringedSiteModuleComplexTensorInternalHomComparison K L₁ M)
      (ringedSiteModuleComplexTensorInternalHomComparison K L₂ M)
      ((ihom M).map (𝟙 K ⊗ₘ fL)) := by
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right]
  rw [ringedSiteModuleComplexTensorInternalHomComparison_uncurry,
    ringedSiteModuleComplexTensorInternalHomComparison_uncurry]
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
      (α_ M K ((ihom M).obj L₁)).inv ≫
        (β_ M K).hom ▷ (ihom M).obj L₁ ≫
        (α_ K M ((ihom M).obj L₁)).hom ≫
        K ◁ (ihom.ev M).app L₁ ≫
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

/-- The tensor-internal-Hom comparison is contravariantly natural in the source complex `M`. -/
theorem ringedSiteModuleComplexTensorInternalHomComparison_natural_source
    (K L : CpxO)
    {M₁ M₂ : CpxO}
    (fM : M₁ ⟶ M₂) :
    CommSq
      (𝟙 K ⊗ₘ (MonoidalClosed.pre fM).app L)
      (ringedSiteModuleComplexTensorInternalHomComparison K L M₂)
      (ringedSiteModuleComplexTensorInternalHomComparison K L M₁)
      ((MonoidalClosed.pre fM).app (K ⊗ L)) := by
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
  rw [ringedSiteModuleComplexTensorInternalHomComparison_uncurry,
    ringedSiteModuleComplexTensorInternalHomComparison_uncurry]
  simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight_assoc]
  calc
    M₁ ◁ K ◁ (MonoidalClosed.pre fM).app L ≫
        (α_ M₁ K ((ihom M₁).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₁).obj L ≫
        (α_ K M₁ ((ihom M₁).obj L)).hom ≫
        K ◁ (ihom.ev M₁).app L =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (M₁ ⊗ K) ◁ (MonoidalClosed.pre fM).app L ≫
        (β_ M₁ K).hom ▷ (ihom M₁).obj L ≫
        (α_ K M₁ ((ihom M₁).obj L)).hom ≫
        K ◁ (ihom.ev M₁).app L := by
          rw [MonoidalCategory.associator_inv_naturality_right_assoc]
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
        (K ⊗ M₁) ◁ (MonoidalClosed.pre fM).app L ≫
        (α_ K M₁ ((ihom M₁).obj L)).hom ≫
        K ◁ (ihom.ev M₁).app L := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M₁ K ((ihom M₂).obj L)).inv ≫ k ≫
                  (α_ K M₁ ((ihom M₁).obj L)).hom ≫
                  K ◁ (ihom.ev M₁).app L)
              (MonoidalCategory.whisker_exchange (β_ M₁ K).hom
                ((MonoidalClosed.pre fM).app L))
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
        (α_ K M₁ ((ihom M₂).obj L)).hom ≫
        K ◁ M₁ ◁ (MonoidalClosed.pre fM).app L ≫
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
              (ringedSiteModuleComplexTensorInternalHomComparison_uncurryPreApp fM)
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

/-- Lemma 21.34.3: for a ringed site `(𝒞, 𝒪)` and cochain complexes `K`, `L`, `M : CpxO`,
the canonical morphism
`K ⊗ (M ⟶[CpxO] L) ⟶ (M ⟶[CpxO] (K ⊗ L))`
is natural in `K` and `L`, and contravariantly natural in `M`. -/
theorem ringedSiteModuleComplexTensorInternalHomComparison_natural
    {K₁ K₂ L₁ L₂ M₁ M₂ : CpxO}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (fK ⊗ₘ (((MonoidalClosed.pre fM).app L₁) ≫ (ihom M₁).map fL))
      (ringedSiteModuleComplexTensorInternalHomComparison K₁ L₁ M₂)
      (ringedSiteModuleComplexTensorInternalHomComparison K₂ L₂ M₁)
      (((MonoidalClosed.pre fM).app (K₁ ⊗ L₁)) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := by
  let hSource :
      CommSq
        (𝟙 K₁ ⊗ₘ (MonoidalClosed.pre fM).app L₁)
        (ringedSiteModuleComplexTensorInternalHomComparison K₁ L₁ M₂)
        (ringedSiteModuleComplexTensorInternalHomComparison K₁ L₁ M₁)
        ((MonoidalClosed.pre fM).app (K₁ ⊗ L₁)) :=
    ringedSiteModuleComplexTensorInternalHomComparison_natural_source K₁ L₁ fM
  let hTensor :
      CommSq
        (fK ⊗ₘ 𝟙 (M₁ ⟶[CpxO] L₁))
        (ringedSiteModuleComplexTensorInternalHomComparison K₁ L₁ M₁)
        (ringedSiteModuleComplexTensorInternalHomComparison K₂ L₁ M₁)
        ((ihom M₁).map (fK ⊗ₘ 𝟙 L₁)) :=
    ringedSiteModuleComplexTensorInternalHomComparison_natural_tensor fK
  let hTarget :
      CommSq
        (𝟙 K₂ ⊗ₘ (ihom M₁).map fL)
        (ringedSiteModuleComplexTensorInternalHomComparison K₂ L₁ M₁)
        (ringedSiteModuleComplexTensorInternalHomComparison K₂ L₂ M₁)
        ((ihom M₁).map (𝟙 K₂ ⊗ₘ fL)) :=
    ringedSiteModuleComplexTensorInternalHomComparison_natural_target K₂ M₁ fL
  have hComposite :=
    (CommSq.horiz_comp (CommSq.horiz_comp hSource hTensor) hTarget).w
  have hTop :
      fK ⊗ₘ (((MonoidalClosed.pre fM).app L₁) ≫ (ihom M₁).map fL) =
        ((𝟙 K₁ ⊗ₘ (MonoidalClosed.pre fM).app L₁) ≫ (fK ⊗ₘ 𝟙 ((ihom M₁).obj L₁))) ≫
          (𝟙 K₂ ⊗ₘ (ihom M₁).map fL) := by
        simpa [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp,
          Category.assoc] using
          (MonoidalCategory.whisker_exchange_assoc fK ((MonoidalClosed.pre fM).app L₁)
            (K₂ ◁ (ihom M₁).map fL)).symm
  have hMap :
      (ihom M₁).map (fK ▷ L₁) ≫ (ihom M₁).map (K₂ ◁ fL) =
        (ihom M₁).map (fK ⊗ₘ fL) := by
        simpa [Functor.map_comp, MonoidalCategory.tensorHom_def] using
          congrArg ((ihom M₁).map) (MonoidalCategory.tensorHom_def fK fL).symm
  have hBottom :
      ringedSiteModuleComplexTensorInternalHomComparison K₁ L₁ M₂ ≫
          ((((MonoidalClosed.pre fM).app (K₁ ⊗ L₁)) ≫ (ihom M₁).map (fK ⊗ₘ 𝟙 L₁)) ≫
            (ihom M₁).map (𝟙 K₂ ⊗ₘ fL)) =
        ringedSiteModuleComplexTensorInternalHomComparison K₁ L₁ M₂ ≫
          (((MonoidalClosed.pre fM).app (K₁ ⊗ L₁)) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              ringedSiteModuleComplexTensorInternalHomComparison K₁ L₁ M₂ ≫
                (MonoidalClosed.pre fM).app (K₁ ⊗ L₁) ≫ k)
            hMap
  refine CommSq.mk ?_
  calc
    (fK ⊗ₘ (((MonoidalClosed.pre fM).app L₁) ≫ (ihom M₁).map fL)) ≫
        ringedSiteModuleComplexTensorInternalHomComparison K₂ L₂ M₁ =
      (((𝟙 K₁ ⊗ₘ (MonoidalClosed.pre fM).app L₁) ≫
            (fK ⊗ₘ 𝟙 ((ihom M₁).obj L₁))) ≫
          (𝟙 K₂ ⊗ₘ (ihom M₁).map fL)) ≫
        ringedSiteModuleComplexTensorInternalHomComparison K₂ L₂ M₁ := by
          simpa using congrArg
            (fun k ↦ k ≫ ringedSiteModuleComplexTensorInternalHomComparison K₂ L₂ M₁)
            hTop
    _ =
      ringedSiteModuleComplexTensorInternalHomComparison K₁ L₁ M₂ ≫
        ((((MonoidalClosed.pre fM).app (K₁ ⊗ L₁)) ≫ (ihom M₁).map (fK ⊗ₘ 𝟙 L₁)) ≫
          (ihom M₁).map (𝟙 K₂ ⊗ₘ fL)) := hComposite
    _ =
      ringedSiteModuleComplexTensorInternalHomComparison K₁ L₁ M₂ ≫
        (((MonoidalClosed.pre fM).app (K₁ ⊗ L₁)) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := hBottom

end

end SheafOfModules.RingedSite
