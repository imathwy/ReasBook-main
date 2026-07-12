import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex
open MonoidalCategory
open MonoidalClosed
open BraidedCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
  [MonoidalCategory (CochainComplex (ModuleCat R) ℤ)]
  [BraidedCategory (CochainComplex (ModuleCat R) ℤ)]
  [MonoidalClosed (CochainComplex (ModuleCat R) ℤ)]
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for 15.72.4:
- primary domain: tensor-internal-Hom comparison morphisms for cochain complexes of `R`-modules;
- sampled owner declarations:
  `MonoidalClosed.curry`,
  `(ihom.ev M).app L`,
  `MonoidalClosed.pre f`;
- best owner abstraction: the source-facing morphism
  `K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L))` is the curried braiding/evaluation composite in the
  closed monoidal category of cochain complexes, so its canonical owner is `MonoidalClosed.curry`
  rather than a chapter-local reassembly through coevaluation and enriched composition;
- primitive data vs. derived API: the primitive owner data are the braiding and associator
  isomorphisms moving `M` past `K`, together with the evaluation map
  `M ⊗ (M ⟶[CpxR] L) ⟶ L`; the tensor-internal-Hom comparison is the derived curried morphism
  built from those owner maps;
- source/core/bridge triage:
  `source-facing`: the canonical morphism
    `K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L))`
    and its functoriality;
  `core/canonical`: `MonoidalClosed.curry`, `(ihom.ev M).app L`, `MonoidalClosed.pre`,
    `(ihom M).map`, and `⊗ₘ`;
  `bridge/view`: none beyond the source-order presentation of the canonical comparison.
-/

/-- The uncurried braiding/evaluation composite whose transpose is the tensor-Hom comparison. -/
private noncomputable def module_complex_tensor_internal_hom_comparisonTranspose
    (K L M : CpxR) :
    M ⊗ (K ⊗ (M ⟶[CpxR] L)) ⟶ K ⊗ L :=
  (α_ M K (M ⟶[CpxR] L)).inv ≫
    (β_ M K).hom ▷ (M ⟶[CpxR] L) ≫
    (α_ K M (M ⟶[CpxR] L)).hom ≫
    K ◁ (ihom.ev M).app L

/-- Lemma 15.72.4: there is a canonical morphism
`K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L))`
of cochain complexes of `R`-modules. -/
@[stacks 0BYM]
noncomputable def module_complex_tensor_internal_hom_comparison
    (K L M : CpxR) :
    K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L)) :=
  curry (module_complex_tensor_internal_hom_comparisonTranspose K L M)

/-- Uncurrying the canonical tensor-Hom comparison recovers the braiding-evaluation composite used
to define it. -/
theorem module_complex_tensor_internal_hom_comparison_uncurry
    (K L M : CpxR) :
    uncurry (module_complex_tensor_internal_hom_comparison K L M) =
      (α_ M K (M ⟶[CpxR] L)).inv ≫
        (β_ M K).hom ▷ (M ⟶[CpxR] L) ≫
        (α_ K M (M ⟶[CpxR] L)).hom ≫
        K ◁ (ihom.ev M).app L := by
  simp [module_complex_tensor_internal_hom_comparison,
    module_complex_tensor_internal_hom_comparisonTranspose]

/-- Helper for Lemma 15.72.4: uncurrying precomposition by `fM` on the identity map recovers the
source evaluation morphism. -/
theorem uncurry_pre_app_id_eq_source_eval
    {L M₁ M₂ : CpxR}
    (fM : M₁ ⟶ M₂) :
    uncurry ((pre fM).app L) =
      fM ▷ (M₂ ⟶[CpxR] L) ≫ (ihom.ev M₂).app L := by
  -- Apply the owner-level precomposition formula to the identity of the internal-Hom object.
  simpa using
    (MonoidalClosed.uncurry_pre_app (X := L)
      (f := 𝟙 (M₂ ⟶[CpxR] L)) (g := fM))

/-- Helper for Lemma 15.72.4: the tensor-Hom comparison is natural in the tensor factor `K`. -/
theorem module_complex_tensor_internal_hom_comparison_natural_tensor
    {K₁ K₂ L M : CpxR}
    (fK : K₁ ⟶ K₂) :
    CommSq
      (fK ⊗ₘ 𝟙 (M ⟶[CpxR] L))
      (module_complex_tensor_internal_hom_comparison K₁ L M)
      (module_complex_tensor_internal_hom_comparison K₂ L M)
      ((ihom M).map (fK ⊗ₘ 𝟙 L)) := by
  -- Proof comment: pass to the owner-level transpose and compare the two routes by moving `fK`
  -- successively across the associator, the braiding, and the evaluation tail.
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right]
  rw [module_complex_tensor_internal_hom_comparison_uncurry,
    module_complex_tensor_internal_hom_comparison_uncurry]
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
          -- Proof comment: move `fK` past the inverse associator first.
          rw [MonoidalCategory.associator_inv_naturality_middle_assoc]
    _ =
      (α_ M K₁ ((ihom M).obj L)).inv ≫
        (β_ M K₁).hom ▷ (ihom M).obj L ≫
        (fK ▷ M) ▷ (ihom M).obj L ≫
        (α_ K₂ M ((ihom M).obj L)).hom ≫
        K₂ ◁ (ihom.ev M).app L := by
          -- Proof comment: next commute `fK` across the braiding and re-whisker on the right.
          rw [← MonoidalCategory.comp_whiskerRight_assoc]
          rw [BraidedCategory.braiding_naturality_right]
          rw [MonoidalCategory.comp_whiskerRight_assoc]
    _ =
      (α_ M K₁ ((ihom M).obj L)).inv ≫
        (β_ M K₁).hom ▷ (ihom M).obj L ≫
        (α_ K₁ M ((ihom M).obj L)).hom ≫
        fK ▷ (M ⊗ (ihom M).obj L) ≫
        K₂ ◁ (ihom.ev M).app L := by
          -- Proof comment: transport `fK` through the forward associator.
          rw [MonoidalCategory.associator_naturality_left_assoc]
    _ =
      (α_ M K₁ ((ihom M).obj L)).inv ≫
        (β_ M K₁).hom ▷ (ihom M).obj L ≫
        (α_ K₁ M ((ihom M).obj L)).hom ≫
        K₁ ◁ (ihom.ev M).app L ≫
        fK ▷ L := by
          -- Proof comment: the remaining tail is exactly whisker exchange with evaluation.
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M K₁ ((ihom M).obj L)).inv ≫
                  (β_ M K₁).hom ▷ (ihom M).obj L ≫
                  (α_ K₁ M ((ihom M).obj L)).hom ≫ k)
              (MonoidalCategory.whisker_exchange fK ((ihom.ev M).app L)).symm

/-- Helper for Lemma 15.72.4: the tensor-Hom comparison is natural in the target complex `L`. -/
theorem module_complex_tensor_internal_hom_comparison_natural_target
    (K M : CpxR)
    {L₁ L₂ : CpxR}
    (fL : L₁ ⟶ L₂) :
    CommSq
      (𝟙 K ⊗ₘ (ihom M).map fL)
      (module_complex_tensor_internal_hom_comparison K L₁ M)
      (module_complex_tensor_internal_hom_comparison K L₂ M)
      ((ihom M).map (𝟙 K ⊗ₘ fL)) := by
  -- Proof comment: transpose to the owner morphism and transport `(ihom M).map fL` through the
  -- same associator-braiding prefix before using evaluation naturality.
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right]
  rw [module_complex_tensor_internal_hom_comparison_uncurry,
    module_complex_tensor_internal_hom_comparison_uncurry]
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
          -- Proof comment: first move the target map through the inverse associator.
          rw [MonoidalCategory.associator_inv_naturality_right_assoc]
    _ =
      (α_ M K ((ihom M).obj L₁)).inv ≫
        (β_ M K).hom ▷ (ihom M).obj L₁ ≫
        (K ⊗ M) ◁ (ihom M).map fL ≫
        (α_ K M ((ihom M).obj L₂)).hom ≫
        K ◁ (ihom.ev M).app L₂ := by
          -- Proof comment: commute the target map across the braiding by whisker exchange.
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
          -- Proof comment: then move it through the forward associator.
          rw [MonoidalCategory.associator_naturality_right_assoc]
    _ =
      (α_ M K ((ihom M).obj L₁)).inv ≫
        (β_ M K).hom ▷ (ihom M).obj L₁ ≫
        (α_ K M ((ihom M).obj L₁)).hom ≫
        K ◁ (ihom.ev M).app L₁ ≫
        K ◁ fL := by
          -- Proof comment: the tail is just `ihom.ev_naturality`, whiskered by `K`.
          simpa [MonoidalCategory.whiskerLeft_comp, Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M K ((ihom M).obj L₁)).inv ≫
                  (β_ M K).hom ▷ (ihom M).obj L₁ ≫
                  (α_ K M ((ihom M).obj L₁)).hom ≫ K ◁ k)
              (ihom.ev_naturality (A := M) fL)

/-- Helper for Lemma 15.72.4: the tensor-Hom comparison is contravariantly natural in the source
complex `M`. -/
theorem module_complex_tensor_internal_hom_comparison_natural_source
    (K L : CpxR)
    {M₁ M₂ : CpxR}
    (fM : M₁ ⟶ M₂) :
    CommSq
      (𝟙 K ⊗ₘ (pre fM).app L)
      (module_complex_tensor_internal_hom_comparison K L M₂)
      (module_complex_tensor_internal_hom_comparison K L M₁)
      ((pre fM).app (K ⊗ L)) := by
  -- Proof comment: pass to the uncurried owner morphism, rewrite the `pre` tail to a source-side
  -- evaluation map, and then move `fM` across the same associator-braiding prefix.
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
  rw [module_complex_tensor_internal_hom_comparison_uncurry,
    module_complex_tensor_internal_hom_comparison_uncurry]
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
          -- Proof comment: move the precomposition map through the inverse associator.
          rw [MonoidalCategory.associator_inv_naturality_right_assoc]
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
        (K ⊗ M₁) ◁ (pre fM).app L ≫
        (α_ K M₁ ((ihom M₁).obj L)).hom ≫
        K ◁ (ihom.ev M₁).app L := by
          -- Proof comment: commute the internal-Hom map past the braiding.
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
          -- Proof comment: then move it through the forward associator.
          rw [MonoidalCategory.associator_naturality_right_assoc]
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
        (α_ K M₁ ((ihom M₂).obj L)).hom ≫
        K ◁ (fM ▷ (ihom M₂).obj L) ≫
        K ◁ (ihom.ev M₂).app L := by
          -- Proof comment: rewrite the tail using the owner formula for `uncurry ((pre fM).app L)`.
          simpa [MonoidalClosed.uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc] using
            congrArg
              (fun k ↦
                (α_ M₁ K ((ihom M₂).obj L)).inv ≫
                  (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
                  (α_ K M₁ ((ihom M₂).obj L)).hom ≫ K ◁ k)
              (uncurry_pre_app_id_eq_source_eval (L := L) fM)
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (β_ M₁ K).hom ▷ (ihom M₂).obj L ≫
        (K ◁ fM) ▷ (ihom M₂).obj L ≫
        (α_ K M₂ ((ihom M₂).obj L)).hom ≫
        K ◁ (ihom.ev M₂).app L := by
          -- Proof comment: convert the tail into a first-variable transport step.
          rw [← MonoidalCategory.associator_naturality_middle_assoc]
    _ =
      (α_ M₁ K ((ihom M₂).obj L)).inv ≫
        (fM ▷ K) ▷ (ihom M₂).obj L ≫
        (β_ M₂ K).hom ▷ (ihom M₂).obj L ≫
        (α_ K M₂ ((ihom M₂).obj L)).hom ≫
        K ◁ (ihom.ev M₂).app L := by
          -- Proof comment: move `fM` across the braiding on the first tensor factor.
          rw [← MonoidalCategory.comp_whiskerRight_assoc]
          rw [← BraidedCategory.braiding_naturality_left]
          rw [MonoidalCategory.comp_whiskerRight_assoc]
    _ =
      fM ▷ (K ⊗ (ihom M₂).obj L) ≫
        (α_ M₂ K ((ihom M₂).obj L)).inv ≫
        (β_ M₂ K).hom ▷ (ihom M₂).obj L ≫
        (α_ K M₂ ((ihom M₂).obj L)).hom ≫
        K ◁ (ihom.ev M₂).app L := by
          -- Proof comment: the final prefix transport is first-variable associator naturality.
          rw [MonoidalCategory.associator_inv_naturality_left_assoc]

-- Proof sketch: uncurry both sides to the defining braiding/evaluation composite. Naturality then
-- follows from functoriality of `⊗ₘ`, naturality of the associator and braiding, and the
-- owner identities `MonoidalClosed.uncurry_pre_app` and `MonoidalClosed.uncurry_natural_right`.
/-- The tensor-Hom comparison is natural in the tensor factor and in both variables of the
internal-Hom term. -/
theorem module_complex_tensor_internal_hom_comparison_natural
    {K₁ K₂ L₁ L₂ M₁ M₂ : CpxR}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (fK ⊗ₘ ((pre fM).app L₁ ≫ (ihom M₁).map fL))
      (module_complex_tensor_internal_hom_comparison K₁ L₁ M₂)
      (module_complex_tensor_internal_hom_comparison K₂ L₂ M₁)
      ((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := by
  -- Proof comment: compose the source-, tensor-, and target-variable squares in source order, and
  -- then collapse the resulting composites using tensor bifunctoriality and `Functor.map_comp`.
  let hSource :=
    module_complex_tensor_internal_hom_comparison_natural_source (K := K₁) (L := L₁) fM
  let hTensor :=
    module_complex_tensor_internal_hom_comparison_natural_tensor
      (L := L₁) (M := M₁) fK
  let hTarget :=
    module_complex_tensor_internal_hom_comparison_natural_target
      (K := K₂) (M := M₁) fL
  have hComposite :=
    (CommSq.horiz_comp (CommSq.horiz_comp hSource hTensor) hTarget).w
  have hTop :
      fK ⊗ₘ ((pre fM).app L₁ ≫ (ihom M₁).map fL) =
        ((𝟙 K₁ ⊗ₘ (pre fM).app L₁) ≫ (fK ⊗ₘ 𝟙 ((ihom M₁).obj L₁))) ≫
          (𝟙 K₂ ⊗ₘ (ihom M₁).map fL) := by
        -- Proof comment: use whisker exchange to move `fK` past the source-variable map, then
        -- whisker the target-variable map on the right.
        simpa [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp,
          Category.assoc] using
          (MonoidalCategory.whisker_exchange_assoc fK ((pre fM).app L₁)
            (K₂ ◁ (ihom M₁).map fL)).symm
  have hMap :
      (ihom M₁).map (fK ▷ L₁) ≫ (ihom M₁).map (K₂ ◁ fL) =
        (ihom M₁).map (fK ⊗ₘ fL) := by
        -- Proof comment: `ihom.map` preserves composition, and `tensorHom_def` identifies the
        -- composite whiskered arrow with `fK ⊗ₘ fL`.
        simpa [Functor.map_comp, MonoidalCategory.tensorHom_def] using
          congrArg ((ihom M₁).map) (MonoidalCategory.tensorHom_def fK fL).symm
  have hBottom :
      module_complex_tensor_internal_hom_comparison K₁ L₁ M₂ ≫
          (((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ 𝟙 L₁)) ≫
            (ihom M₁).map (𝟙 K₂ ⊗ₘ fL)) =
        module_complex_tensor_internal_hom_comparison K₁ L₁ M₂ ≫
          ((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := by
        -- Proof comment: replace the two successive `ihom.map` terms by the single mapped tensor
        -- product morphism on the bottom edge.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              module_complex_tensor_internal_hom_comparison K₁ L₁ M₂ ≫
                (pre fM).app (K₁ ⊗ L₁) ≫ k)
            hMap
  refine CommSq.mk ?_
  calc
    (fK ⊗ₘ ((pre fM).app L₁ ≫ (ihom M₁).map fL)) ≫
        module_complex_tensor_internal_hom_comparison K₂ L₂ M₁ =
      (((𝟙 K₁ ⊗ₘ (pre fM).app L₁) ≫
            (fK ⊗ₘ 𝟙 ((ihom M₁).obj L₁))) ≫
          (𝟙 K₂ ⊗ₘ (ihom M₁).map fL)) ≫
        module_complex_tensor_internal_hom_comparison K₂ L₂ M₁ := by
          -- Proof comment: expand the top tensor composite in the same order as the horizontally
          -- composed one-variable squares.
          simpa using congrArg
            (fun k ↦ k ≫ module_complex_tensor_internal_hom_comparison K₂ L₂ M₁)
            hTop
    _ =
      module_complex_tensor_internal_hom_comparison K₁ L₁ M₂ ≫
        (((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ 𝟙 L₁)) ≫
          (ihom M₁).map (𝟙 K₂ ⊗ₘ fL)) := hComposite
    _ =
      module_complex_tensor_internal_hom_comparison K₁ L₁ M₂ ≫
        ((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := hBottom

end
