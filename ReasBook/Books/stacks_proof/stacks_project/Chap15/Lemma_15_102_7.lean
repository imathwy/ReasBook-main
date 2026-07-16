import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Definition_15_59_13
import stacks_proof.stacks_project.Chap15.«15_74_0_2»
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14
import stacks_proof.stacks_project.Chap15.Lemma_15_80_1
import stacks_proof.stacks_project.Chap15.Lemma_15_95_1
import stacks_proof.stacks_project.Chap15.Lemma_15_102_3
import stacks_proof.stacks_project.Chap15.Lemma_15_102_6
import stacks_proof.stacks_project.Chap15.Lemma_15_102_Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open SequentialProObjectMorphismRep
open scoped DerivedTensorProduct IdealPowerSubmodule

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "singleCpx0" => CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)
private abbrev Q : CpxA ⥤ DMod := DerivedCategory.Q

/-- Helper for Lemma 15.102.7: inside the regular `A`-module, the submodule `I • ⊤` is exactly
`I` itself. -/
private theorem ideal_smul_top_eq_self_submodule (I : Ideal A) :
    ((I • (⊤ : Submodule A A)) : Submodule A A) = (I : Submodule A A) := by
  -- Normalize `I • ⊤` to `Ideal.map` and compare it directly with the ideal viewed as a
  -- submodule of the regular module.
  ext x
  constructor
  · intro hx
    rw [Ideal.smul_top_eq_map] at hx
    simpa using hx
  · intro hx
    rw [Ideal.smul_top_eq_map]
    simpa using hx

/-- Helper for Lemma 15.102.7: the first ideal-power stage of the regular module identifies with
the ideal itself. -/
private noncomputable def ideal_power_first_stage_iso (I : Ideal A) :
    idealPowerStage I 1 (ModuleCat.of A A) ≅ ModuleCat.of A ↥I :=
  eqToIso <| by
    -- Replace the stage `I^[1] A` by `I • ⊤`, then identify that submodule with `I`.
    change ModuleCat.of A ↥((I • (⊤ : Submodule A A)) : Submodule A A) =
      ModuleCat.of A ↥(I : Submodule A A)
    simpa [idealPowerStage, idealPowerSubmodule] using
      congrArg (fun J : Submodule A A ↦ ModuleCat.of A ↥J)
        (ideal_smul_top_eq_self_submodule I)

/-- Helper for Lemma 15.102.7: the stage `m` of the ideal-power complex tower on `M[0]` is the
derived object `(I^(m+1) M)[0]`. -/
private theorem ideal_power_complex_single_eq
    (I : Ideal A) (M : ModuleCat A) (m : ℕ) :
    ((idealPowerSubmoduleFunctor I (m + 1)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (singleCpx0.obj M) =
      singleCpx0.obj (idealPowerStage I (m + 1) M) := by
  -- Applying the ideal-power submodule functor degreewise to a complex concentrated in degree `0`
  -- again gives a complex concentrated in degree `0`.
  rfl

/-- Helper for Lemma 15.102.7: the stage `m` of the ideal-power complex tower on `M[0]` is the
derived object `(I^(m+1) M)[0]`. -/
private noncomputable def single_ideal_power_complex_stage_iso
    (I : Ideal A) (M : ModuleCat A) (m : ℕ) :
    (idealPowerComplexDerivedInverseSystem I (singleCpx0.obj M)).obj (op m) ≅
      (single₀).obj (idealPowerStage I (m + 1) M) :=
  (Q.mapIso (eqToIso (ideal_power_complex_single_eq I M m))) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (idealPowerStage I (m + 1) M)

/-- Helper for Lemma 15.102.7: stage `0` of the derived tensor tower is the tensor product with
the first ideal-power stage `(I^1 A)[0]`, hence with `I[0]`. -/
private noncomputable def ideal_tensor_stage_zero_iso
    (I : Ideal A) (M : ModuleCat A) :
    ((idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct ((single₀).obj M)).obj (op 0)) ≅
      (single₀).obj (ModuleCat.of A ↥I) ⊗[A]^L (single₀).obj M :=
  ((single₀).mapIso (ideal_power_first_stage_iso I)) ⊗ᵢ Iso.refl _

/-- Helper for Lemma 15.102.7: the complex `M[0]` is bounded on both sides and has finite terms.
-/
private theorem single_zero_complex_has_bounded_finite_terms
    (M : ModuleCat A) [Module.Finite A M] :
    (∃ a : ℤ, (singleCpx0.obj M).IsStrictlyGE a) ∧
      (∃ b : ℤ, (singleCpx0.obj M).IsStrictlyLE b) ∧
        ∀ i : ℤ, Module.Finite A ((singleCpx0.obj M).X i) := by
  -- The single complex is supported exactly in degree `0`, so the standard support instances give
  -- both bounds immediately.
  refine ⟨0, inferInstance, 0, inferInstance, ?_⟩
  intro i
  by_cases hi : i = 0
  · -- In degree `0` we recover the original finite module `M`.
    simpa [singleCpx0, hi] using (inferInstance : Module.Finite A M)
  · -- Away from degree `0` the single complex term is zero, hence finite.
    let _ : Subsingleton ((singleCpx0.obj M).X i) :=
      ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M i hi)
    exact Module.Finite.of_surjective (0 : (Fin 0 → A) →ₗ[A] (singleCpx0.obj M).X i) <| by
      intro x
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _

/-- Helper for Lemma 15.102.7: if two representatives into a constant target define the same
pro-object morphism, then after one common source refinement their level-`0` maps agree. -/
private theorem equivalent_constant_target_level_zero_eq
    {X : ℕᵒᵖ ⥤ DMod} {Y : DMod}
    (r₁ r₂ : SequentialProObjectMorphismRep X ((Functor.const ℕᵒᵖ).obj Y))
    (h : r₁.toProObjectHom = r₂.toProObjectHom) :
    ∃ m : ℕ,
      ∃ hm₁ : r₁.reindex 0 ≤ m,
        ∃ hm₂ : r₂.reindex 0 ≤ m,
          X.map (homOfLE hm₁).op ≫ r₁.map 0 =
            X.map (homOfLE hm₂).op ≫ r₂.map 0 := by
  -- Move to the common refinement supplied by `represents_eq_iff_equivalent` and read the
  -- equality directly at target level `0`.
  rcases (represents_eq_iff_equivalent r₁ r₂).1 h with ⟨reindex', h₁, h₂, hmaps⟩
  refine ⟨reindex' 0, h₁ 0, h₂ 0, ?_⟩
  simpa using hmaps 0

/-- Helper for Lemma 15.102.7: a morphism out of a degree-zero object factors through the
previous lower truncation once its degree-zero homology map vanishes. -/
private theorem exists_factor_through_prev_truncLE_of_single0_homologyMap_eq_zero
    {N : ModuleCat A} {Y : DMod}
    (f : (single₀).obj N ⟶ Y)
    (hf : (DerivedCategory.homologyFunctor (ModuleCat A) 0).map f = 0) :
    ∃ φ : (single₀).obj N ⟶ (DerivedCategory.TStructure.t.truncLE (-1)).obj Y,
      φ ≫ (DerivedCategory.TStructure.t.truncLEι (-1)).app Y = f := by
  -- The source proof only needs the `a = 0` case of the Chapter 13 truncation step. Reuse the
  -- owner theorem on one composable arrow instead of rebuilding the truncation triangle locally.
  obtain ⟨φ, hφ⟩ :=
    exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero
      (S := ComposableArrows.mk₁ f)
      (h₀ := inferInstance)
      (fun j hj ↦ by
        have hj0 : j = 0 := by
          omega
        subst hj0
        simpa [ComposableArrows.mk₁, ComposableArrows.Precomp.map_zero_one] using hf)
  simpa using hφ

/-- Helper for Lemma 15.102.7: if the pro-object morphism induced by a natural transformation is
an isomorphism, then the natural transformation admits a representative-level inverse. -/
private theorem compRep_toProObjectHom
    {X Y Z : ℕᵒᵖ ⥤ DMod}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    (compRep r s).toProObjectHom = r.toProObjectHom ≫ s.toProObjectHom := by
  -- Proof comment: both morphisms are represented by the same stagewise composites
  -- `r.map (s.reindex n) ≫ s.map n`, so the canonical pro-object comparison identifies them.
  ext W x
  rfl

/-- Helper for Lemma 15.102.7: if the pro-object morphism induced by a natural transformation is
an isomorphism, then the natural transformation admits a representative-level inverse. -/
private theorem ofNatTrans_isProIsomorphism_of_isIso_toProObjectHom
    {X Y : ℕᵒᵖ ⥤ DMod} (α : X ⟶ Y)
    (hαIso : IsIso (ofNatTrans α).toProObjectHom) :
    (ofNatTrans α).IsProIsomorphism := by
  -- The remaining gap is purely Chapter 4 bookkeeping: choose a representative of the inverse
  -- pro-morphism and compare both composites with the identity representative.
  let η := (ofNatTrans α).toProObjectHom
  rcases exists_representative (inv η) with ⟨s, hs⟩
  refine ⟨s, ?_, ?_⟩
  · -- Proof comment: the chosen representative of `inv η` is a left inverse to `ofNatTrans α`
    -- in the pro-category, hence equivalent to the identity representative on `X`.
    apply (represents_eq_iff_equivalent (compRep (ofNatTrans α) s) (idRep X)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.hom_inv_id η
  · -- Proof comment: the same representative is also a right inverse, so the reverse composite
    -- is equivalent to the identity representative on `Y`.
    apply (represents_eq_iff_equivalent (compRep s (ofNatTrans α)) (idRep Y)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.inv_hom_id η

/-- Helper for Lemma 15.102.7: the stage-`0` comparison from Lemma `15.102.6`, specialized to the
single complex `M[0]`, carries the canonical tensor-to-submodule map to the ordinary inclusion
`I M ↪ M`. -/
private theorem stage_zero_tensor_comparison_comp_subtype_eq
    (I : Ideal A) (M : ModuleCat A) :
    let αNat := idealPowerDerivedTensorToIdealPowerComplexNatTrans I (singleCpx0.obj M)
    αNat.app (op 0) ≫
        (single_ideal_power_complex_stage_iso I M 0).hom ≫
          (single₀).map (ModuleCat.ofHom (idealPowerSubtype I 1 M)) =
      (ideal_tensor_stage_zero_iso I M).hom ≫
        (derivedTensorProduct ((single₀).obj M)).map
          ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
        (singleZeroDerivedTensorIso ((single₀).obj M)).hom := by
  -- Route correction: this is the exact stage-`0` source/target bridge that lets the pro-object
  -- comparison from Lemma `15.102.6` feed the displayed factorization statement here.
  -- Proof comment: at stage `0`, the comparison is the canonical multiplication map
  -- `I ⊗ M → IM`; after identifying the source with `I[0] ⊗^L M[0]` and the target with
  -- `(IM)[0]`, composing with the ambient inclusion gives the standard tensor-unit map.
  simp [idealPowerDerivedTensorToIdealPowerComplexNatTrans, ideal_tensor_stage_zero_iso,
    single_ideal_power_complex_stage_iso, ideal_power_first_stage_iso, Category.assoc]

/-- Helper for Lemma 15.102.7: the transition from stage `m` of the ideal-power tower to stage `0`
followed by the ambient inclusion is the direct inclusion `(I^(m+1)M)[0] → M[0]`. -/
private theorem ideal_power_complex_transition_comp_subtype
    (I : Ideal A) (M : ModuleCat A) (m : ℕ) :
    let Y := idealPowerComplexDerivedInverseSystem I (singleCpx0.obj M)
    Y.transitionMap (Nat.zero_le m) ≫
        (single_ideal_power_complex_stage_iso I M 0).hom ≫
          (single₀).map (ModuleCat.ofHom (idealPowerSubtype I 1 M)) =
      (single_ideal_power_complex_stage_iso I M m).hom ≫
        (single₀).map (ModuleCat.ofHom (idealPowerSubtype I (m + 1) M)) := by
  -- The tower transition is induced by the inclusion `I^(m+1) M ↪ I M`; after identifying both
  -- stages with degree-zero objects, composing with the stage-`1` inclusion recovers the direct
  -- inclusion into `M`.
  simp [SequentialInverseSystem.transitionMap, single_ideal_power_complex_stage_iso,
    idealPowerComplexDerivedInverseSystem, Category.assoc, Functor.ofOpSequence_map_homOfLE_succ]

/- Domain-style sampling for Lemma 15.102.7:
- primary domain: eventual factorization in `D(A)` of the ideal-power inclusion through the first
  stage of the derived ideal-power tensor tower;
- sampled owner declarations:
  `idealPowerStage`,
  `idealPowerSubtype`,
  `derivedTensorProduct`,
  `singleZeroDerivedTensorIso`;
- best owner abstraction: the source-facing factorization should reuse the chapter owner
  `singleZeroDerivedTensorIso` for the canonical tensor-unit identification
  `A[0] \otimes_A^{\mathbf L} M[0] ≅ M[0]`, rather than restating that bridge by an expanded
  whiskered composite;
- primitive data: the ideal `I`, the finite module `M`, and the canonical inclusion
  `idealPowerSubtype I n M`;
- derived API: the existence of a power `n` and a factorization of that inclusion through
  `I[0] \otimes_A^{\mathbf L} M[0]`.

Source/core/bridge triage:
- `source-facing`: the eventual factorization statement below;
- `core/canonical`: `idealPowerStage`, `idealPowerSubtype`, and `derivedTensorProduct`;
- `bridge/view`: `singleZeroDerivedTensorIso`, identifying `A[0] \otimes_A^{\mathbf L} -` with the
  identity on `D(A)`. -/

-- Proof sketch: tensor the distinguished triangle coming from `0 → I → A → A / I → 0` with
-- `M[0]`, so the desired factorization is reduced to killing the composite
-- `I^n M[0] → (A / I)[0] ⊗^L M[0]`. Choose generators of `I`, factor the quotient map
-- `A[0] → (A / I)[0]` through the stage-`0` Koszul object `K(f)`, and then kill the induced map
-- `I^n M[0] → K(f) ⊗ M` by descending through the finite truncation tower. Each obstruction lies
-- in an `Ext` group with finite `I`-annihilated target, so Lemma `15.102.3` kills it after
-- enlarging `n`.
/-- Lemma 15.102.7: if `A` is Noetherian, `I ⊆ A` is an ideal, and `M` is a finite `A`-module,
then for some integer `n > 0` the canonical map `I^n M[0] → M[0]` in `D(A)` factors through the
map induced by `I → A`,
`I[0] \otimes_A^{\mathbf L} M[0] → A[0] \otimes_A^{\mathbf L} M[0]`,
together with the canonical tensor-unit identification
`A[0] \otimes_A^{\mathbf L} M[0] ≅ M[0]`. -/
@[stacks 0928]
theorem exists_idealPower_inclusion_factorization_through_ideal_derivedTensor_map
    (I : Ideal A) (M : ModuleCat A) [Module.Finite A M] :
    ∃ n : ℕ, 0 < n ∧
      ∃ α : (single₀).obj (idealPowerStage I n M) ⟶
          (single₀).obj (ModuleCat.of A ↥I) ⊗[A]^L (single₀).obj M,
        α ≫
            (derivedTensorProduct ((single₀).obj M)).map
              ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
            (singleZeroDerivedTensorIso ((single₀).obj M)).hom =
          (single₀).map (ModuleCat.ofHom (idealPowerSubtype I n M)) :=
  -- Route correction: stop using the pro-object representative comparison from the previous
  -- attempt. The stable imported input is already Lemma `15.102.6`: it identifies the whole
  -- ideal-power tower with the derived tensor tower as sequential pro-objects. Extract the
  -- required stage-`0` factorization from that pro-isomorphism, then rewrite both ends back to
  -- the displayed source and target maps.
  let C := singleCpx0.obj M
  have hbounded : ∃ a : ℤ, C.IsStrictlyGE a := (single_zero_complex_has_bounded_finite_terms M).1
  have hbounded' : ∃ b : ℤ, C.IsStrictlyLE b :=
    (single_zero_complex_has_bounded_finite_terms M).2.1
  have hfinite : ∀ i : ℤ, Module.Finite A (C.X i) :=
    (single_zero_complex_has_bounded_finite_terms M).2.2
  let X := idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct ((single₀).obj M)
  let Y := idealPowerComplexDerivedInverseSystem I C
  let αNat : X ⟶ Y := idealPowerDerivedTensorToIdealPowerComplexNatTrans I C
  have hαIso : IsIso (ofNatTrans αNat).toProObjectHom :=
    idealPowerDerivedTensorToIdealPowerComplex_isIso I C hbounded hbounded' hfinite
  have hαPro : (ofNatTrans αNat).IsProIsomorphism :=
    ofNatTrans_isProIsomorphism_of_isIso_toProObjectHom αNat hαIso
  obtain ⟨m, hm, t, ht⟩ :=
    eventually_factors_target_transition_of_ofNatTrans_isProIsomorphism αNat hαPro 0
  refine ⟨m + 1, Nat.succ_pos _, ?_⟩
  refine ⟨(single_ideal_power_complex_stage_iso I M m).inv ≫
      t ≫ (ideal_tensor_stage_zero_iso I M).hom, ?_⟩
  -- The transition map on the ideal-power tower becomes the direct inclusion
  -- `(I^(m+1) M)[0] → M[0]`, while the stage-`0` comparison identifies the factorization target
  -- with `I[0] ⊗^L M[0]`.
  have ht' :
      (Y.transitionMap hm) ≫
          (single_ideal_power_complex_stage_iso I M 0).hom ≫
            (single₀).map (ModuleCat.ofHom (idealPowerSubtype I 1 M)) =
        t ≫ (ideal_tensor_stage_zero_iso I M).hom ≫
          (derivedTensorProduct ((single₀).obj M)).map
            ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
          (singleZeroDerivedTensorIso ((single₀).obj M)).hom := by
    -- Replace the stage-`0` comparison with the displayed tensor map before comparing with the
    -- ambient inclusion on the ideal-power tower.
    simpa [Category.assoc, stage_zero_tensor_comparison_comp_subtype_eq (I := I) (M := M)] using
      congrArg
        (fun k ↦
          k ≫ (single_ideal_power_complex_stage_iso I M 0).hom ≫
            (single₀).map (ModuleCat.ofHom (idealPowerSubtype I 1 M)))
        ht
  have hleft :
      (single_ideal_power_complex_stage_iso I M m).hom ≫
          (single₀).map (ModuleCat.ofHom (idealPowerSubtype I (m + 1) M)) =
        t ≫ (ideal_tensor_stage_zero_iso I M).hom ≫
          (derivedTensorProduct ((single₀).obj M)).map
            ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
          (singleZeroDerivedTensorIso ((single₀).obj M)).hom := by
    -- The tower transition from stage `m` down to stage `0` is exactly the inclusion
    -- `I^(m+1) M ↪ I M`, and composing further into `M` gives the direct inclusion
    -- `I^(m+1) M ↪ M`.
    simpa [ideal_power_complex_transition_comp_subtype (I := I) (M := M) (m := m)] using ht'
  simpa [Category.assoc] using hleft.symm

end

end CategoryTheory
