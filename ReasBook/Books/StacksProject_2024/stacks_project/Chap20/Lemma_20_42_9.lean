import StacksProject_2024.Chap20.Lemma_20_42_5
import StacksProject_2024.Chap20.Tensor_internal_hom_to_iterated_internal_hom

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed
noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- This file adds the naturality companions for the source-facing comparison morphism
`tensorInternalHomToIteratedInternalHom`, whose owner declaration now lives in the reusable
support file `Tensor_internal_hom_to_iterated_internal_hom`. -/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DModX" => RingedSpaceDerived X

/-- Helper for Lemma 20.42.9: the uncurried comparison map factors through the chapter
comparison `internalHomComposition K L M`. -/
theorem tensorInternalHomToIteratedInternalHom_uncurry_via_internalHomComposition
    (K L M : DModX) :
    MonoidalClosed.uncurry (tensorInternalHomToIteratedInternalHom K L M) =
      (α_ (K ⟹ L) (L ⟹ M) K).inv ≫
        ((β_ (K ⟹ L) (L ⟹ M)).hom ▷ K) ≫
        (internalHomComposition K L M ▷ K) ≫
        (β_ (K ⟹ M) K).hom ≫
        MonoidalClosed.uncurry (𝟙 (K ⟹ M)) := by
  -- Proof comment: rewrite the owner formula once so later naturality proofs can treat the
  -- middle comparison block as the chapter API `internalHomComposition`.
  simp [tensorInternalHomToIteratedInternalHom_uncurry, internalHomComposition]

omit [BraidedCategory DModX] in
/-- Helper for Lemma 20.42.9: uncurrying a `pre`-map on an outer internal-Hom identity produces
the corresponding source-side evaluation composite. -/
theorem uncurryPreAppIdEqSourceEval
    {A B C : DModX} (f : A ⟶ B) :
    MonoidalClosed.uncurry ((MonoidalClosed.pre f).app C) =
      f ▷ (B ⟹ C) ≫ (ihom.ev B).app C := by
  -- Proof comment: specialize the owner `uncurry_pre_app` formula to the identity of `B ⟹ C`.
  simpa using
    (MonoidalClosed.uncurry_pre_app (X := C) (f := 𝟙 (B ⟹ C)) (g := f))

/-- Helper for Lemma 20.42.9: precomposition on an internal Hom is composition with the
internalized source morphism. -/
private theorem pre_app_eq_leftUnitor_inv_comp
    {K K' L : DModX} (f : K ⟶ K') :
    (MonoidalClosed.pre f).app L =
      (λ_ (K' ⟹ L)).inv ≫
        (MonoidalClosed.curry' f ▷ (K' ⟹ L)) ≫
        comp K K' L := by
  rw [← cancel_mono (λ_ (K' ⟹ L)).hom]
  simpa [Category.assoc] using
    (MonoidalClosed.curry'_whiskerRight_comp (Z := L) f).symm

/-- Helper for Lemma 20.42.9: postcomposition on an internal Hom is composition with the
internalized target morphism. -/
private theorem ihomMap_eq_rightUnitor_inv_comp
    {K L L' : DModX} (g : L ⟶ L') :
    (ihom K).map g =
      (ρ_ (K ⟹ L)).inv ≫
        ((K ⟹ L) ◁ MonoidalClosed.curry' g) ≫
        comp K L L' := by
  rw [← cancel_mono (ρ_ (K ⟹ L)).hom]
  simpa [Category.assoc] using
    (MonoidalClosed.whiskerLeft_curry'_comp (X := K) g).symm

omit [BraidedCategory DModX] in
/-- Helper for Lemma 20.42.9: internal-Hom composition is contravariantly natural in its
source object. -/
private theorem comp_natural_source_assoc
    {K K' L M : DModX} (f : K ⟶ K') :
    (((MonoidalClosed.pre f).app L) ⊗ₘ 𝟙 (L ⟹ M)) ≫ comp K L M =
      comp K' L M ≫ (MonoidalClosed.pre f).app M := by
  -- Proof comment: express both `pre` maps as ordinary enriched composition with `curry' f`,
  -- then use associativity of `comp`.
  rw [pre_app_eq_leftUnitor_inv_comp, pre_app_eq_leftUnitor_inv_comp]
  calc
    (((λ_ (K' ⟹ L)).inv ≫ (MonoidalClosed.curry' f ▷ (K' ⟹ L)) ≫ comp K K' L) ⊗ₘ
          𝟙 (L ⟹ M)) ≫
        comp K L M =
      (λ_ ((K' ⟹ L) ⊗ (L ⟹ M))).inv ≫
        (MonoidalClosed.curry' f ▷ ((K' ⟹ L) ⊗ (L ⟹ M))) ≫
        (α_ (K ⟹ K') (K' ⟹ L) (L ⟹ M)).inv ≫
        (comp K K' L ▷ (L ⟹ M)) ≫
        comp K L M := by
          simp [Category.assoc, MonoidalCategory.tensorHom_def']
    _ =
      (λ_ ((K' ⟹ L) ⊗ (L ⟹ M))).inv ≫
        (MonoidalClosed.curry' f ▷ ((K' ⟹ L) ⊗ (L ⟹ M))) ≫
        ((K ⟹ K') ◁ comp K' L M) ≫
        comp K K' M := by
          rw [MonoidalClosed.assoc]
    _ =
      comp K' L M ≫
        (λ_ (K' ⟹ M)).inv ≫
        (MonoidalClosed.curry' f ▷ (K' ⟹ M)) ≫
        comp K K' M := by
          simpa [Category.assoc, MonoidalCategory.tensorHom_def'] using
            (MonoidalCategory.leftUnitor_inv_comp_tensorHom_assoc
              (f := MonoidalClosed.curry' f) (g := comp K' L M) (h := comp K K' M))
    _ = comp K' L M ≫ (MonoidalClosed.pre f).app M := by
          rw [pre_app_eq_leftUnitor_inv_comp]

omit [BraidedCategory DModX] in
/-- Helper for Lemma 20.42.9: internal-Hom composition is natural in the middle object once the
two variance directions are separated across the two sides of the equality. -/
private theorem comp_natural_middle_assoc
    {K L L' M : DModX} (g : L ⟶ L') :
    (𝟙 (K ⟹ L) ⊗ₘ (MonoidalClosed.pre g).app M) ≫ comp K L M =
      ((ihom K).map g ⊗ₘ 𝟙 (L' ⟹ M)) ≫ comp K L' M := by
  -- Proof comment: uncurry both sides and move the middle-variable map through the second
  -- evaluation, after identifying the first internal-Hom map by `uncurry_ihom_map`.
  -- Route correction: keep the whole proof in the owner `comp` spelling after uncurrying, and
  -- only braid back once the mixed middle-variable transport is already proved.
  have hHead :
      K ◁ (ihom K).map g ≫ (ihom.ev K).app L' =
        (ihom.ev K).app L ≫ g := by
    simpa only [MonoidalClosed.uncurry_eq] using
      (MonoidalClosed.uncurry_ihom_map K g)
  have hTail :
      L ◁ (MonoidalClosed.pre g).app M ≫ (ihom.ev L).app M =
        g ▷ (L' ⟹ M) ≫ (ihom.ev L').app M := by
    simpa only [MonoidalClosed.uncurry_eq] using
      (uncurryPreAppIdEqSourceEval (A := L) (B := L') (C := M) g)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.comp_eq, MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.comp_eq, MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.compTranspose_eq, MonoidalClosed.compTranspose_eq]
  calc
    K ◁ (𝟙 (K ⟹ L) ⊗ₘ (MonoidalClosed.pre g).app M) ≫
        (α_ K (K ⟹ L) (L ⟹ M)).inv ≫
        (ihom.ev K).app L ▷ (L ⟹ M) ≫
        (ihom.ev L).app M =
      (α_ K (K ⟹ L) (L' ⟹ M)).inv ≫
        (K ⊗ (K ⟹ L)) ◁ (MonoidalClosed.pre g).app M ≫
        (ihom.ev K).app L ▷ (L ⟹ M) ≫
        (ihom.ev L).app M := by
          simpa [Category.assoc] using
            (MonoidalCategory.associator_inv_naturality_right_assoc K (K ⟹ L)
              ((MonoidalClosed.pre g).app M)
              ((ihom.ev K).app L ▷ (L ⟹ M) ≫ (ihom.ev L).app M))
    _ =
      (α_ K (K ⟹ L) (L' ⟹ M)).inv ≫
        (ihom.ev K).app L ▷ (L' ⟹ M) ≫
        (L ◁ (MonoidalClosed.pre g).app M) ≫
        (ihom.ev L).app M := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ K (K ⟹ L) (L' ⟹ M)).inv ≫ k)
              (MonoidalCategory.whisker_exchange_assoc ((ihom.ev K).app L)
                ((MonoidalClosed.pre g).app M) ((ihom.ev L).app M))
    _ =
      (α_ K (K ⟹ L) (L' ⟹ M)).inv ≫
        (ihom.ev K).app L ▷ (L' ⟹ M) ≫
        g ▷ (L' ⟹ M) ≫
        (ihom.ev L').app M := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ K (K ⟹ L) (L' ⟹ M)).inv ≫
                  (ihom.ev K).app L ▷ (L' ⟹ M) ≫
                  k)
              hTail
    _ =
      (α_ K (K ⟹ L) (L' ⟹ M)).inv ≫
        (K ◁ (ihom K).map g) ▷ (L' ⟹ M) ≫
        (ihom.ev K).app L' ▷ (L' ⟹ M) ≫
        (ihom.ev L').app M := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (α_ K (K ⟹ L) (L' ⟹ M)).inv ≫
                  k ▷ (L' ⟹ M) ≫
                  (ihom.ev L').app M)
              hHead.symm
    _ =
      K ◁ ((ihom K).map g ⊗ₘ 𝟙 (L' ⟹ M)) ≫
        (α_ K (K ⟹ L') (L' ⟹ M)).inv ≫
        (ihom.ev K).app L' ▷ (L' ⟹ M) ≫
        (ihom.ev L').app M := by
          simpa [Category.assoc] using
            (MonoidalCategory.associator_inv_naturality_middle_assoc K
              ((ihom K).map g) (𝟙 (L' ⟹ M))
              ((ihom.ev K).app L' ▷ (L' ⟹ M) ≫ (ihom.ev L').app M)).symm

/-- Helper for Lemma 20.42.9: `internalHomComposition` is contravariantly natural in its source
object. -/
theorem internalHomComposition_natural_source_assoc
    {K K' L M : DModX} (f : K ⟶ K') :
    (𝟙 (L ⟹ M) ⊗ₘ (MonoidalClosed.pre f).app L) ≫ internalHomComposition K L M =
      internalHomComposition K' L M ≫ (MonoidalClosed.pre f).app M := by
  -- Proof comment: transport the owner-level source naturality lemma across the fixed braiding
  -- that defines `internalHomComposition`.
  calc
    (𝟙 (L ⟹ M) ⊗ₘ (MonoidalClosed.pre f).app L) ≫ internalHomComposition K L M =
      (𝟙 (L ⟹ M) ⊗ₘ (MonoidalClosed.pre f).app L) ≫
        (β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M := by
          rfl
    _ =
      (β_ (L ⟹ M) (K' ⟹ L)).hom ≫
        (((MonoidalClosed.pre f).app L) ⊗ₘ 𝟙 (L ⟹ M)) ≫ comp K L M := by
          simpa [Category.assoc] using
            (BraidedCategory.braiding_naturality_assoc (𝟙 (L ⟹ M))
              ((MonoidalClosed.pre f).app L) (comp K L M))
    _ =
      (β_ (L ⟹ M) (K' ⟹ L)).hom ≫
        (comp K' L M ≫ (MonoidalClosed.pre f).app M) := by
          rw [comp_natural_source_assoc f]
    _ = internalHomComposition K' L M ≫ (MonoidalClosed.pre f).app M := by
          simp [internalHomComposition, Category.assoc]

/-- Helper for Lemma 20.42.9: `internalHomComposition` is natural in the middle object once the
two variance directions are separated across the two sides of the equality. -/
theorem internalHomComposition_natural_middle_assoc
    {K L L' M : DModX} (g : L ⟶ L') :
    (((MonoidalClosed.pre g).app M) ⊗ₘ 𝟙 (K ⟹ L)) ≫ internalHomComposition K L M =
      (𝟙 (L' ⟹ M) ⊗ₘ (ihom K).map g) ≫ internalHomComposition K L' M := by
  -- Proof comment: again braid the source-facing tensor order into the owner `comp` order, use
  -- the owner naturality lemma, and braid back.
  calc
    (((MonoidalClosed.pre g).app M) ⊗ₘ 𝟙 (K ⟹ L)) ≫ internalHomComposition K L M =
      (((MonoidalClosed.pre g).app M) ⊗ₘ 𝟙 (K ⟹ L)) ≫
        (β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M := by
          rfl
    _ =
      (β_ (L' ⟹ M) (K ⟹ L)).hom ≫
        (𝟙 (K ⟹ L) ⊗ₘ (MonoidalClosed.pre g).app M) ≫ comp K L M := by
          simpa [Category.assoc] using
            (BraidedCategory.braiding_naturality_assoc ((MonoidalClosed.pre g).app M)
              (𝟙 (K ⟹ L)) (comp K L M))
    _ =
      (β_ (L' ⟹ M) (K ⟹ L)).hom ≫
        (((ihom K).map g ⊗ₘ 𝟙 (L' ⟹ M)) ≫ comp K L' M) := by
          rw [comp_natural_middle_assoc g]
    _ =
      (𝟙 (L' ⟹ M) ⊗ₘ (ihom K).map g) ≫
        (β_ (L' ⟹ M) (K ⟹ L')).hom ≫ comp K L' M := by
          simpa [Category.assoc] using
            (BraidedCategory.braiding_naturality_assoc (𝟙 (L' ⟹ M))
              ((ihom K).map g) (comp K L' M)).symm
    _ = (𝟙 (L' ⟹ M) ⊗ₘ (ihom K).map g) ≫ internalHomComposition K L' M := by
          simp [internalHomComposition]

-- Proof sketch: use naturality of currying in the tensor factor `K`, together with the
-- contravariant functoriality of the inner internal Hom in its source variable.
/-- The canonical tensor-to-iterated-internal-Hom morphism is natural in the first variable
`K`. -/
theorem tensorInternalHomToIteratedInternalHom_natural_in_first_variable
    {K K' L M : DModX} (f : K ⟶ K') :
    CommSq
      ((𝟙 (L ⟹ M)) ⊗ₘ f)
      (tensorInternalHomToIteratedInternalHom K L M)
      (tensorInternalHomToIteratedInternalHom K' L M)
      ((MonoidalClosed.pre ((MonoidalClosed.pre f).app L)).app M) := by
  -- Route correction: keep the proof in the public uncurried shell and rewrite only the central
  -- `internalHomComposition` block, instead of reopening the owner definition of the comparison.
  refine CommSq.mk ?_
  -- Proof comment: uncurry both routes, normalize to the fixed public shell, and ask Lean to
  -- rewrite only the middle `internalHomComposition` block before simplifying the shell.
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
  rw [tensorInternalHomToIteratedInternalHom_uncurry_via_internalHomComposition,
    tensorInternalHomToIteratedInternalHom_uncurry_via_internalHomComposition]
  rw [MonoidalCategory.tensorHom_def']
  rw [internalHomComposition_natural_source_assoc f]
  simp only [Category.assoc, MonoidalCategory.tensorHom_def']

-- Proof sketch: compare the two transposes obtained from a morphism `L ⟶ L'`; on the source side
-- this acts by precomposition on `RHom(L', M)`, and on the target side by precomposition on the
-- outer internal Hom along `RHom(K, L) ⟶ RHom(K, L')`.
/-- The canonical tensor-to-iterated-internal-Hom morphism is natural in the second variable
`L`. -/
theorem tensorInternalHomToIteratedInternalHom_natural_in_second_variable
    {K L L' M : DModX} (g : L ⟶ L') :
    CommSq
      (((MonoidalClosed.pre g).app M) ⊗ₘ 𝟙 K)
      (tensorInternalHomToIteratedInternalHom K L' M)
      (tensorInternalHomToIteratedInternalHom K L M)
      ((MonoidalClosed.pre ((ihom K).map g)).app M) := by
  -- Route correction: use the same normalized public shell as in the first-variable proof and
  -- change only the central naturality companion and the final `pre`-tail.
  refine CommSq.mk ?_
  -- Proof comment: the middle-variable proof uses the same public shell normalization, with only
  -- the mixed-variance companion for `internalHomComposition` changed in the center.
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
  rw [tensorInternalHomToIteratedInternalHom_uncurry_via_internalHomComposition,
    tensorInternalHomToIteratedInternalHom_uncurry_via_internalHomComposition]
  rw [MonoidalCategory.tensorHom_def']
  rw [internalHomComposition_natural_middle_assoc g]
  simpa only [Category.assoc, MonoidalCategory.tensorHom_def', MonoidalClosed.pre_comm_ihom_map]

-- Proof sketch: use functoriality of both internal-Hom factors in the target object `M` and the
-- naturality of currying in the codomain.
/-- The canonical tensor-to-iterated-internal-Hom morphism is natural in the third variable
`M`. -/
theorem tensorInternalHomToIteratedInternalHom_natural_in_third_variable
    {K L M M' : DModX} (h : M ⟶ M') :
    CommSq
      ((ihom L).map h ⊗ₘ 𝟙 K)
      (tensorInternalHomToIteratedInternalHom K L M)
      (tensorInternalHomToIteratedInternalHom K L M')
      ((ihom (K ⟹ L)).map h) := by
  -- Route correction: mirror the Chapter 15 target-variable proof in the already normalized
  -- public shell, so only the target naturality of `internalHomComposition` and evaluation remain.
  refine CommSq.mk ?_
  -- Proof comment: after uncurrying, the target-variable map stays on the codomain side, so the
  -- only new input relative to the previous proofs is `uncurry_natural_right`.
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right]
  rw [tensorInternalHomToIteratedInternalHom_uncurry_via_internalHomComposition,
    tensorInternalHomToIteratedInternalHom_uncurry_via_internalHomComposition]
  rw [MonoidalCategory.tensorHom_def']
  rw [internalHomComposition_natural_target_assoc K L h]
  simp only [Category.assoc, MonoidalCategory.tensorHom_def']

end

end AlgebraicGeometry.RingedSpace
