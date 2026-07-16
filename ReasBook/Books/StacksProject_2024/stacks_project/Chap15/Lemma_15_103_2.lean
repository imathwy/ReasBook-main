import Mathlib
import StacksProject_2024.stacks_project.Chap04.Example_4_22_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_102_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_102_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_102_Basic
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_15
import StacksProject_2024.stacks_project.Chap15.Lemma_15_89_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open ModuleCat.MonoidalCategory
open Opposite
open SequentialProObjectMorphismRep
open scoped DerivedTensorProduct TensorProduct

universe u

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "Cpx" => CochainComplex (ModuleCat A) ℤ
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)

/-- Helper for Lemma 15.103.2: the degree-zero cochain complex attached to a module. -/
private abbrev singleZeroCpx (M : ModuleCat A) : Cpx :=
  (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M

/-- Helper for Lemma 15.103.2: the quotient functor `Q` carries its standard monoidal structure. -/
private noncomputable instance quotientFunctorMonoidal :
    (DerivedCategory.Q : Cpx ⥤ DMod).Monoidal := by
  change (((HomotopyCategory.quotient (ModuleCat A) (up ℤ)) ⋙
      (DerivedCategory.Qh : HomotopyCategory (ModuleCat A) (up ℤ) ⥤ DMod))).Monoidal
  infer_instance

namespace SequentialProObjectMorphismRep

variable {C : Type*} [Category C]

/-- Helper for Lemma 15.103.2: an `Equivalent (s ≫ ofNatTrans α) (idRep Y)` witness produces the
explicit late-stage target-transition factorization needed for the stage-`0` argument. -/
theorem equivalent_comp_ofNatTrans_idRep_target_transition_factorization
    {X Y : SequentialInverseSystem C} (α : X ⟶ Y)
    (s : SequentialProObjectMorphismRep Y X)
    (hEq : Equivalent (compRep s (ofNatTrans α)) (idRep Y)) (n : ℕ) :
    ∃ (m : ℕ) (hnm : n ≤ m) (t : Y.obj (op m) ⟶ X.obj (op n)),
      Y.transitionMap hnm = t ≫ α.app (op n) := by
  rcases hEq with ⟨reindex', h₁, h₂, hmaps⟩
  refine ⟨reindex' n, h₂ n, Y.transitionMap (h₁ n) ≫ s.map n, ?_⟩
  have hcomp :
      (compRep s (ofNatTrans α)).map n = s.map n ≫ α.app (op n) := by
    rfl
  have hid : (idRep Y).map n = 𝟙 (Y.obj (op n)) := by
    rfl
  have hstage := hmaps n
  rw [hcomp, hid] at hstage
  -- Proof comment: the common-refinement equality at stage `n` already says that the later
  -- target transition factors through the stage map `α_n`.
  simpa [SequentialInverseSystem.transitionMap, Category.assoc] using hstage.symm

end SequentialProObjectMorphismRep

/-- Helper for Lemma 15.103.2: composing sequential representatives matches composition of the
induced pro-object morphisms. -/
private theorem compRep_toProObjectHom
    {X Y Z : ℕᵒᵖ ⥤ DMod}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    (compRep r s).toProObjectHom = r.toProObjectHom ≫ s.toProObjectHom := by
  -- Proof comment: both sides evaluate on a test object by the same stagewise composites
  -- `r.map (s.reindex n) ≫ s.map n`.
  ext W x
  rfl

/-- Helper for Lemma 15.103.2: inside the regular `A`-module, the submodule `I • ⊤` is exactly
the ideal `I`. -/
private theorem ideal_smul_top_eq_self_submodule (I : Ideal A) :
    ((I • (⊤ : Submodule A A)) : Submodule A A) = (I : Submodule A A) := by
  -- Proof comment: `I • ⊤` identifies with the image ideal `Ideal.map I (LinearMap.id)`,
  -- hence with the original ideal viewed as a submodule.
  ext x
  constructor
  · intro hx
    rw [Ideal.smul_top_eq_map] at hx
    simpa using hx
  · intro hx
    rw [Ideal.smul_top_eq_map]
    simpa using hx

/-- Helper for Lemma 15.103.2: the first ideal-power stage of the regular module is the ideal
itself. -/
private theorem ideal_power_first_stage_iso (I : Ideal A) :
    idealPowerStage I 1 (ModuleCat.of A A) ≅ ModuleCat.of A ↥I := by
  -- Proof comment: rewrite `I^[1] A` as `I • ⊤` and then use the regular-module identification
  -- `I • ⊤ = I`.
  refine eqToIso ?_
  change ModuleCat.of A ↥((I • (⊤ : Submodule A A)) : Submodule A A) =
    ModuleCat.of A ↥(I : Submodule A A)
  simpa [idealPowerStage, idealPowerSubmodule] using
    congrArg (fun J : Submodule A A ↦ ModuleCat.of A ↥J)
      (ideal_smul_top_eq_self_submodule I)

/-- Helper for Lemma 15.103.2: applying the ideal-power submodule functor degreewise to a complex
concentrated in degree `0` again gives a degree-zero single complex. -/
private theorem ideal_power_complex_single_eq
    (I : Ideal A) (M : ModuleCat A) (m : ℕ) :
    ((idealPowerSubmoduleFunctor I (m + 1)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (singleZeroCpx M) =
      singleZeroCpx (idealPowerStage I (m + 1) M) := by
  -- Proof comment: both complexes are definitionally the same degreewise ideal-power stage.
  rfl

/-- Helper for Lemma 15.103.2: the degreewise ideal-power tower on a cochain complex. -/
private abbrev idealPowerComplexFunctor (I : Ideal A) (n : ℕ) : Cpx ⥤ Cpx :=
  (idealPowerSubmoduleFunctor I (n + 1)).mapHomologicalComplex (up ℤ)

/-- Helper for Lemma 15.103.2: the `n`th ideal-power stage of a cochain complex. -/
private abbrev idealPowerComplex (I : Ideal A) (M : Cpx) (n : ℕ) : Cpx :=
  (idealPowerComplexFunctor I n).obj M

/-- Helper for Lemma 15.103.2: the successor map in the ideal-power complex tower. -/
private abbrev idealPowerComplexStepNatTrans (I : Ideal A) (n : ℕ) :
    idealPowerComplexFunctor I (n + 1) ⟶ idealPowerComplexFunctor I n :=
  NatTrans.mapHomologicalComplex
    (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))) (up ℤ)

/-- Helper for Lemma 15.103.2: the stage transition in the ideal-power complex tower. -/
private abbrev idealPowerComplexStep (I : Ideal A) (M : Cpx) (n : ℕ) :
    idealPowerComplex I M (n + 1) ⟶ idealPowerComplex I M n :=
  (idealPowerComplexStepNatTrans I n).app M

/-- Helper for Lemma 15.103.2: the `n`th derived stage `Q(I^(n+1) M^\bullet)`. -/
private abbrev idealPowerComplexDerivedStage (I : Ideal A) (M : Cpx) (n : ℕ) : DMod :=
  Q.obj (idealPowerComplex I M n)

/-- Helper for Lemma 15.103.2: the derived transition map in the ideal-power complex tower. -/
private abbrev idealPowerComplexDerivedStep (I : Ideal A) (M : Cpx) (n : ℕ) :
    idealPowerComplexDerivedStage I M (n + 1) ⟶ idealPowerComplexDerivedStage I M n :=
  Q.map (idealPowerComplexStep I M n)

/-- Helper for Lemma 15.103.2: the inverse system `(Q(I^(n+1) M^\bullet))_n`. -/
private abbrev idealPowerComplexDerivedInverseSystem (I : Ideal A) (M : Cpx) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerComplexDerivedStep I M)

-- TODO: localize the stagewise tensor-complex comparison from Lemma `15.102.6`, so the canonical
-- comparison natural transformation is defined here without importing the broken upstream file.
/-- Helper for Lemma 15.103.2: the canonical comparison from the derived tensor tower to the
ideal-power complex tower. -/
private noncomputable def idealPowerDerivedTensorToIdealPowerComplexNatTrans
    (I : Ideal A) (M : Cpx) :
    (idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)) ⟶
      idealPowerComplexDerivedInverseSystem I M :=
  sorry

/-- Helper for Lemma 15.103.2: stage `m` of the ideal-power complex tower on `M[0]` identifies
with `(I^(m+1) M)[0]` in the derived category. -/
private noncomputable theorem single_ideal_power_complex_stage_iso
    (I : Ideal A) (M : ModuleCat A) (m : ℕ) :
    (idealPowerComplexDerivedInverseSystem I (singleZeroCpx M)).obj (op m) ≅
      (single₀).obj (idealPowerStage I (m + 1) M) :=
  (Q.mapIso (eqToIso (ideal_power_complex_single_eq I M m))) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (idealPowerStage I (m + 1) M)

/-- Helper for Lemma 15.103.2: stage `0` of the derived tensor tower is `I[0] ⊗^L M[0]`. -/
private noncomputable theorem ideal_tensor_stage_zero_iso
    (I : Ideal A) (M : ModuleCat A) :
    ((idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct ((single₀).obj M)).obj (op 0)) ≅
      (single₀).obj (ModuleCat.of A ↥I) ⊗[A]^L (single₀).obj M :=
  ((single₀).mapIso (ideal_power_first_stage_iso I)) ⊗ᵢ Iso.refl _

/-- Helper for Lemma 15.103.2: the degree-zero complex `M[0]` is bounded on both sides and has
finite terms when `M` is finite. -/
private theorem single_zero_complex_has_bounded_finite_terms
    (M : ModuleCat A) [Module.Finite A M] :
    (∃ a : ℤ, (singleZeroCpx M).IsStrictlyGE a) ∧
      (∃ b : ℤ, (singleZeroCpx M).IsStrictlyLE b) ∧
        ∀ i : ℤ, Module.Finite A ((singleZeroCpx M).X i) := by
  -- Proof comment: the single complex is supported exactly in degree `0`, so the canonical
  -- support instances give both bounds and the only nonzero term is `M`.
  refine ⟨0, inferInstance, 0, inferInstance, ?_⟩
  intro i
  by_cases hi : i = 0
  · simpa [singleZeroCpx, hi] using (inferInstance : Module.Finite A M)
  · let _ : Subsingleton ((singleZeroCpx M).X i) :=
      ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M i hi)
    exact Module.Finite.of_surjective (0 : (Fin 0 → A) →ₗ[A] (singleZeroCpx M).X i) <| by
      intro x
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _

/-- Helper for Lemma 15.103.2: if the pro-object morphism induced by a natural transformation is
an isomorphism, then that natural transformation admits a representative-level inverse. -/
private theorem ofNatTrans_isProIsomorphism_of_isIso_toProObjectHom
    {X Y : ℕᵒᵖ ⥤ DMod} (α : X ⟶ Y)
    (hαIso : IsIso (ofNatTrans α).toProObjectHom) :
    (ofNatTrans α).IsProIsomorphism := by
  let η := (ofNatTrans α).toProObjectHom
  rcases exists_representative (inv η) with ⟨s, hs⟩
  refine ⟨s, ?_, ?_⟩
  · -- Proof comment: the chosen representative of `inv η` is a left inverse to `ofNatTrans α`
    -- in the pro-category, so their composite is equivalent to the identity representative on `X`.
    apply (represents_eq_iff_equivalent (compRep (ofNatTrans α) s) (idRep X)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.hom_inv_id η
  · -- Proof comment: the same representative is also a right inverse, yielding the target-side
    -- equivalence to the identity representative on `Y`.
    apply (represents_eq_iff_equivalent (compRep s (ofNatTrans α)) (idRep Y)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.inv_hom_id η

-- TODO: localize the single-complex specialization of Lemma `15.102.6` so the canonical
-- comparison above is known to be a pro-isomorphism without importing the broken file.
/-- Helper for Lemma 15.103.2: for a bounded finite single complex, the canonical comparison from
the derived tensor tower to the ideal-power complex tower is an isomorphism of sequential
pro-objects. -/
private theorem idealPowerDerivedTensorToIdealPowerComplex_isIso
    (I : Ideal A) (M : Cpx)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    IsIso (ofNatTrans (idealPowerDerivedTensorToIdealPowerComplexNatTrans I M)).toProObjectHom := by
  sorry

/-- Helper for Lemma 15.103.2: the stage-`0` comparison from Lemma `15.102.6`, specialized to
`M[0]`, carries the canonical tensor-to-submodule map to the inclusion `I M ↪ M`. -/
private theorem stage_zero_tensor_comparison_comp_subtype_eq
    (I : Ideal A) (M : ModuleCat A) :
    let αNat := idealPowerDerivedTensorToIdealPowerComplexNatTrans I (singleZeroCpx M)
    αNat.app (op 0) ≫
        (single_ideal_power_complex_stage_iso I M 0).hom ≫
          (single₀).map (ModuleCat.ofHom (idealPowerSubtype I 1 M)) =
      (ideal_tensor_stage_zero_iso I M).hom ≫
        (derivedTensorProduct ((single₀).obj M)).map
          ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
        (singleZeroDerivedTensorIso ((single₀).obj M)).hom := by
  -- TODO: once the local comparison natural transformation is expanded stagewise, this becomes the
  -- same stage-`0` multiplication-map computation used in `Lemma_15_102_7`.
  sorry

/-- Helper for Lemma 15.103.2: the transition from stage `m` of the ideal-power tower to stage
`0`, followed by the ambient inclusion, is the direct inclusion `(I^(m+1) M)[0] → M[0]`. -/
private theorem ideal_power_complex_transition_comp_subtype
    (I : Ideal A) (M : ModuleCat A) (m : ℕ) :
    let Y := idealPowerComplexDerivedInverseSystem I (singleZeroCpx M)
    Y.transitionMap (Nat.zero_le m) ≫
        (single_ideal_power_complex_stage_iso I M 0).hom ≫
          (single₀).map (ModuleCat.ofHom (idealPowerSubtype I 1 M)) =
      (single_ideal_power_complex_stage_iso I M m).hom ≫
        (single₀).map (ModuleCat.ofHom (idealPowerSubtype I (m + 1) M)) := by
  -- Proof comment: the tower transition is induced by `I^(m+1) M ↪ I M`, and composing once
  -- more with `I M ↪ M` is exactly the direct inclusion `I^(m+1) M ↪ M`.
  simp [SequentialInverseSystem.transitionMap, single_ideal_power_complex_stage_iso,
    idealPowerComplexDerivedInverseSystem, Category.assoc, Functor.ofOpSequence_map_homOfLE_succ]

/-- Helper for Lemma 15.103.2: the inclusion `(I^n M)[0] → M[0]` factors through
`I[0] ⊗^L M[0] → M[0]` for some positive stage `n`. -/
private theorem exists_idealPower_single0_factorization_through_ideal_derivedTensor_map
    (I : Ideal A) (M : ModuleCat A) [Module.Finite A M] :
    ∃ n : ℕ, 0 < n ∧
      ∃ α : (single₀).obj (idealPowerStage I n M) ⟶
          (single₀).obj (ModuleCat.of A ↥I) ⊗[A]^L (single₀).obj M,
        α ≫
            (derivedTensorProduct ((single₀).obj M)).map
              ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
            (singleZeroDerivedTensorIso ((single₀).obj M)).hom =
          (single₀).map (ModuleCat.ofHom (idealPowerSubtype I n M)) := by
  -- Route correction: instead of importing the broken transitive dependency chain through
  -- `Lemma_15_102_7`, recreate only the prerequisite stage-factorization theorem locally using
  -- the clean `15.102.6` pro-isomorphism and representative calculus from Chapter 4.
  let C := singleZeroCpx M
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
  rcases hαPro with ⟨s, -, hs⟩
  obtain ⟨m, hm, t, ht⟩ :=
    SequentialProObjectMorphismRep.equivalent_comp_ofNatTrans_idRep_target_transition_factorization
      αNat s hs 0
  refine ⟨m + 1, Nat.succ_pos _, ?_⟩
  refine ⟨(single_ideal_power_complex_stage_iso I M m).inv ≫
      t ≫ (ideal_tensor_stage_zero_iso I M).hom, ?_⟩
  have ht' :
      (Y.transitionMap hm) ≫
          (single_ideal_power_complex_stage_iso I M 0).hom ≫
            (single₀).map (ModuleCat.ofHom (idealPowerSubtype I 1 M)) =
        t ≫ (ideal_tensor_stage_zero_iso I M).hom ≫
          (derivedTensorProduct ((single₀).obj M)).map
            ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
          (singleZeroDerivedTensorIso ((single₀).obj M)).hom := by
    -- Proof comment: rewrite the abstract stage-`0` comparison into the displayed tensor map
    -- before comparing it with the concrete inclusion into `M[0]`.
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
    -- Proof comment: the tower transition from stage `m` to stage `0` is the inclusion
    -- `I^(m+1) M ↪ I M`, and composing once more gives the direct inclusion into `M`.
    simpa [ideal_power_complex_transition_comp_subtype (I := I) (M := M) (m := m)] using ht'
  simpa [Category.assoc] using hleft.symm

/- Domain-style sampling for Lemma 15.103.2:
- primary domain: Tor functoriality for the inclusion `I^[n] M ↪ M` of ideal-power submodules of a
  finite module over a Noetherian ring;
- sampled owner declarations:
  `Tor[A, p](X, Y)`,
  `idealPowerSubtype`,
  `idealPowerSubtypeTorMap`,
  `exists_idealPower_inclusion_factorization_through_ideal_derivedTensor_map`;
- best owner abstraction: the source-facing theorem should use the chapter owner
  `idealPowerSubtypeTorMap` for the induced map
  `Tor_p^A(I^[n] M, N) → Tor_p^A(M, N)`, while the factorization through the derived tensor map
  from Lemma `15.102.7` remains proof-level bridge data;
- primitive data: the ideal `I`, the finite module `M`, the target module `N`, and the
  annihilator containment `I ≤ Module.annihilator A N`;
- derived API: the existential vanishing statement below for the canonical Tor map
  `idealPowerSubtypeTorMap`.

Source/core/bridge triage:
- `source-facing`: existence of an ideal-power stage where the canonical map on all Tor groups
  vanishes;
- `core/canonical`: `Tor[A, p](X, Y)` and `idealPowerSubtypeTorMap`;
- `bridge/view`: the derived-tensor factorization from Lemma `15.102.7`. -/

/-- Helper for Lemma 15.103.2: if `I` annihilates `N`, then the ordinary tensor map induced by the
ideal inclusion `I ↪ A` is zero after tensoring with `N`. -/
lemma ideal_subtype_rTensor_eq_zero_of_annihilator_le
    (I : Ideal A) (N : ModuleCat A)
    (hN : I ≤ Module.annihilator A N) :
    I.subtype.rTensor N = 0 := by
  -- The tensor image is exactly `I • ⊤`, and the annihilator hypothesis makes that submodule zero.
  have hrange : LinearMap.range (I.subtype.rTensor N) = ⊥ := by
    rw [Ideal.subtype_rTensor_range, smul_top_eq_bot_of_le_annihilator I hN]
  ext x
  have hx : (I.subtype.rTensor N) x ∈ (⊥ : Submodule A (A ⊗[A] N)) := by
    rw [← hrange]
    exact LinearMap.mem_range_self _ x
  simpa using hx

/-- Helper for Lemma 15.103.2: `Tor_p^A(C, N)` is canonically the `(-p)`-th homology of
`C[0] ⊗_A^{\mathbf L} N[0]`. -/
noncomputable theorem tor_single0_tensor_homology_iso
    (C N : ModuleCat A) (p : ℕ) :
    ((((Tor (ModuleCat A) p).obj C).obj N)) ≅
      (H (-(p : ℤ))).obj (((single₀).obj C) ⊗[A]^L (single₀).obj N) := by
  let eFlip :
      ((((Tor (ModuleCat A) p).obj C).obj N)) ≅
        ((((Functor.flip (Tor' (ModuleCat A) p)).obj C).obj N)) :=
    asIso (((tor_flip_iso (ModuleCat A) p).app C).hom.app N)
  let eResolution :
      ((((Functor.flip (Tor' (ModuleCat A) p)).obj C).obj N)) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) p).obj
          (((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.projectiveResolution N).complex) := by
    -- Compute the flipped `Tor_p` term from the projective resolution of `N`.
    simpa [Tor', Functor.flip] using
      ((CategoryTheory.projectiveResolution N).isoLeftDerivedObj (tensorRight C) p)
  let eCochain :
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) p).obj
          (((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.projectiveResolution N).complex) ≅
        ((((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CategoryTheory.ProjectiveResolution.cochainComplex
              (CategoryTheory.projectiveResolution N))).homology (-(p : ℤ))) := by
    let e :
        ((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CategoryTheory.ProjectiveResolution.cochainComplex
              (CategoryTheory.projectiveResolution N)) ≅
          ((((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
              (CategoryTheory.projectiveResolution N).complex).extend
            ComplexShape.embeddingDownNat) :=
      eqToIso rfl
    -- This is the standard chain-to-cochain reindexing of the chosen projective resolution.
    exact
      (((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso
          e) ≪≫
        ((((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.projectiveResolution N).complex).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp))).symm
  let eDerived :
      ((((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution N))).homology (-(p : ℤ))) ≅
        (H (-(p : ℤ))).obj
          ((Q.obj (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution N))) ⊗[A]^L (single₀).obj C) :=
    tensorObj_single0_homology_iso_derivedTensor (R := A)
      (CategoryTheory.ProjectiveResolution.cochainComplex
        (CategoryTheory.projectiveResolution N))
      (-(p : ℤ)) C
  let eSingle :
      (H (-(p : ℤ))).obj
          ((Q.obj (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution N))) ⊗[A]^L (single₀).obj C) ≅
        (H (-(p : ℤ))).obj ((single₀).obj N ⊗[A]^L (single₀).obj C) :=
    (H (-(p : ℤ))).mapIso
      ((derivedTensorProduct ((single₀).obj C)).mapIso
        (projective_resolution_single0_iso (R := A) N))
  let eComm :
      (H (-(p : ℤ))).obj ((single₀).obj N ⊗[A]^L (single₀).obj C) ≅
        (H (-(p : ℤ))).obj ((single₀).obj C ⊗[A]^L (single₀).obj N) :=
    (H (-(p : ℤ))).mapIso
      (derivedTensorProduct_comm ((single₀).obj N) ((single₀).obj C))
  -- Compose the flipped `Tor` computation, the projective-resolution model, and the canonical
  -- transport from the ordinary tensor complex to the derived tensor product.
  exact eFlip ≪≫ eResolution ≪≫ eCochain ≪≫ eDerived ≪≫ eSingle ≪≫ eComm

/-- Helper for Lemma 15.103.2: the canonical `Tor`/homology comparison is natural in the first
module variable. -/
theorem tor_map_eq_homology_map_of_single0_tensor
    {X Y N : ModuleCat A} (f : X ⟶ Y) (p : ℕ) :
    (((Tor (ModuleCat A) p).flip.obj N).map f) ≫
        (tor_single0_tensor_homology_iso Y N p).hom =
      (tor_single0_tensor_homology_iso X N p).hom ≫
        (H (-(p : ℤ))).map
          ((derivedTensorProduct ((single₀).obj N)).map ((single₀).map f)) := by
  -- Unfold the comparison isomorphism and use naturality of its constituent functorial
  -- identifications.
  simp [tor_single0_tensor_homology_iso, Category.assoc]

/-- Helper for Lemma 15.103.2: postcomposing a descended tensor-totalization map can be checked on
each `(p,q)` summand. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorDesc_assoc
    {K L : Cpx} (n : ℤ) {B C : ModuleCat A}
    (f : ∀ p q
      (_h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat A)).obj (K.X p)).obj (L.X q) ⟶ B)
    (u : B ⟶ C) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat A))
          (c := ComplexShape.up ℤ) (A := B) (j := n) f ≫ u =
      f p q h ≫ u := by
  -- Proof comment: this is the owner universal property `ι_mapBifunctorDesc`, postcomposed by `u`.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat A))
        (c := ComplexShape.up ℤ) (A := B) (j := n) (f := f) p q h)

/-- Helper for Lemma 15.103.2: away from degree `0`, the single complex contributes a zero summand
to the tensor totalization. -/
private theorem tensor_single0_off_diagonal_isZero
    (E : Cpx) (N : ModuleCat A) (p q : ℤ) (hq : q ≠ 0) :
    CategoryTheory.Limits.IsZero (((curriedTensor (ModuleCat A)).obj (E.X p)).obj
      ((singleZeroCpx N).X q)) := by
  -- Proof comment: only the degree-zero term of `singleZeroCpx N` survives.
  exact
    CategoryTheory.Functor.map_isZero ((curriedTensor (ModuleCat A)).obj (E.X p))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) N q hq)

/-- Helper for Lemma 15.103.2: on the surviving degree-zero summand, tensoring with the single
complex is exactly right tensoring by the underlying module. -/
private noncomputable def tensor_single0_diagonal_iso
    (E : Cpx) (N : ModuleCat A) (n : ℤ) :
    ((curriedTensor (ModuleCat A)).obj (E.X n)).obj
      ((singleZeroCpx N).X 0) ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n := by
  -- Proof comment: after fixing degree `0`, only the canonical `singleObjXSelf` identification remains.
  simpa using
    CategoryTheory.Functor.mapIso ((curriedTensor (ModuleCat A)).obj (E.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N)

/-- Helper for Lemma 15.103.2: the forward degreewise comparison keeps only the diagonal summand
of the tensor totalization. -/
private noncomputable def tensor_single0_component_hom
    (E : Cpx) (N : ModuleCat A) (n : ℤ) :
    (HomologicalComplex.tensorObj E (singleZeroCpx N)).X n ⟶
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := E)
    (K₂ := singleZeroCpx N)
    (F := curriedTensor (ModuleCat A))
    (c := ComplexShape.up ℤ)
    (A := (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n)
    (j := n)
    (fun p q h ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0)

/-- Helper for Lemma 15.103.2: on the diagonal summand, the forward comparison is the canonical
degreewise tensor identification. -/
@[reassoc]
private theorem tensor_single0_component_hom_diag
    (E : Cpx) (N : ModuleCat A) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h ≫
      tensor_single0_component_hom E N n =
        (tensor_single0_diagonal_iso E N n).hom := by
  let B :
      ModuleCat A :=
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p q
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat A)).obj (E.X p)).obj ((singleZeroCpx N).X q) ⟶ B :=
    fun p q h' ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h'
        subst p
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0
  -- Proof comment: evaluate the descended map on the unique surviving `(n,0)` summand.
  simpa [tensor_single0_component_hom, B, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := E)
      (L := singleZeroCpx N)
      (n := n) (B := B) (C := B) f (𝟙 B) n 0 h)

/-- Helper for Lemma 15.103.2: off the diagonal summand, the forward comparison vanishes. -/
@[reassoc]
private theorem tensor_single0_component_hom_off_diagonal
    (E : Cpx) (N : ModuleCat A) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj E (singleZeroCpx N) p q n h ≫
      tensor_single0_component_hom E N n =
        0 := by
  let B :
      ModuleCat A :=
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor (ModuleCat A)).obj (E.X p')).obj ((singleZeroCpx N).X q') ⟶ B :=
    fun p' q' h' ↦ by
      by_cases hq' : q' = 0
      · subst hq'
        have hp' : p' = n := by simpa using h'
        subst p'
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0
  -- Proof comment: off the diagonal, the chosen branch in the descended map is definitionally zero.
  simpa [tensor_single0_component_hom, B, f, hq] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := E)
      (L := singleZeroCpx N)
      (n := n) (B := B) (C := B) f (𝟙 B) p q h)

/-- Helper for Lemma 15.103.2: the inverse degreewise comparison reinserts the surviving diagonal
summand into the tensor totalization. -/
private noncomputable def tensor_single0_component_inv
    (E : Cpx) (N : ModuleCat A) (n : ℤ) :
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n ⟶
      (HomologicalComplex.tensorObj E (singleZeroCpx N)).X n :=
  (tensor_single0_diagonal_iso E N n).inv ≫
    HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n
      (by simp)

/-- Helper for Lemma 15.103.2: in each total degree, tensoring with a degree-zero single complex
collapses to the unique surviving diagonal summand. -/
private noncomputable def tensor_single0_component_iso
    (E : Cpx) (N : ModuleCat A) (n : ℤ) :
    (HomologicalComplex.tensorObj E (singleZeroCpx N)).X n ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n :=
  { hom := tensor_single0_component_hom E N n
    inv := tensor_single0_component_inv E N n
    hom_inv_id := by
      -- Proof comment: check the identity on the tensor totalization summandwise.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        change
          ((HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h ≫
              tensor_single0_component_hom E N n) ≫
            tensor_single0_component_inv E N n) =
            HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h ≫
              𝟙 ((HomologicalComplex.tensorObj E (singleZeroCpx N)).X n)
        simpa [tensor_single0_component_inv, Category.assoc] using
          congrArg (fun k ↦ k ≫ tensor_single0_component_inv E N n)
            (tensor_single0_component_hom_diag E N n h)
      · change
          ((HomologicalComplex.ιTensorObj E (singleZeroCpx N) p q n h ≫
              tensor_single0_component_hom E N n) ≫
            tensor_single0_component_inv E N n) =
            HomologicalComplex.ιTensorObj E (singleZeroCpx N) p q n h ≫
              𝟙 ((HomologicalComplex.tensorObj E (singleZeroCpx N)).X n)
        rw [tensor_single0_component_hom_off_diagonal E N n p q h hq]
        simp only [CategoryTheory.Limits.zero_comp, Category.comp_id]
        symm
        exact (tensor_single0_off_diagonal_isZero E N p q hq).eq_of_src _ _
    inv_hom_id := by
      let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
        simp
      -- Proof comment: the inverse immediately lands in the diagonal summand and cancels there.
      change
        ((tensor_single0_diagonal_iso E N n).inv ≫
            HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h0) ≫
          tensor_single0_component_hom E N n =
            𝟙 ((((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E).X n)
      calc
        ((tensor_single0_diagonal_iso E N n).inv ≫
            HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h0) ≫
          tensor_single0_component_hom E N n
            = (tensor_single0_diagonal_iso E N n).inv ≫
                (HomologicalComplex.ιTensorObj E (singleZeroCpx N) n 0 n h0 ≫
                  tensor_single0_component_hom E N n) := by
                    simp [Category.assoc]
        _ = (tensor_single0_diagonal_iso E N n).inv ≫
              (tensor_single0_diagonal_iso E N n).hom := by
                simpa using
                  congrArg (fun k ↦ (tensor_single0_diagonal_iso E N n).inv ≫ k)
                    (tensor_single0_component_hom_diag E N n h0)
        _ = 𝟙 _ := by simp }

/-- Helper for Lemma 15.103.2: the diagonal tensor comparison is natural in the differential of
the left cochain complex. -/
private theorem tensor_single0_diagonal_iso_hom_naturality
    (E : Cpx) (N : ModuleCat A) (i j : ℤ)
    (_hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E N i).hom ≫
        (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j =
      (((curriedTensor (ModuleCat A)).map (E.d i j)).app ((singleZeroCpx N).X 0)) ≫
        (tensor_single0_diagonal_iso E N j).hom := by
  -- Proof comment: this is the `singleObjXSelf` naturality square transported through `tensorRight`.
  simpa [tensor_single0_diagonal_iso, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    singleZeroCpx] using
    (((curriedTensor (ModuleCat A)).map (E.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N).hom)

/-- Helper for Lemma 15.103.2: the inverse diagonal tensor comparison satisfies the same
naturality square. -/
private theorem tensor_single0_diagonal_iso_inv_naturality
    (E : Cpx) (N : ModuleCat A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E N i).inv ≫
        (((curriedTensor (ModuleCat A)).map (E.d i j)).app ((singleZeroCpx N).X 0)) =
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        (tensor_single0_diagonal_iso E N j).inv := by
  -- Proof comment: cancel the target diagonal isomorphism and reuse the forward naturality square.
  apply (cancel_mono (tensor_single0_diagonal_iso E N j).hom).1
  simpa [Category.assoc] using
    calc
      (tensor_single0_diagonal_iso E N i).inv ≫
          (((curriedTensor (ModuleCat A)).map (E.d i j)).app ((singleZeroCpx N).X 0)) ≫
          (tensor_single0_diagonal_iso E N j).hom
        = (tensor_single0_diagonal_iso E N i).inv ≫
            ((tensor_single0_diagonal_iso E N i).hom ≫
              (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj E).d i j) := by
            rw [tensor_single0_diagonal_iso_hom_naturality E N i j hij]
      _ =
          (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j := by
            simp

/-- Helper for Lemma 15.103.2: the inverse degreewise tensor comparison respects the cochain
differential. -/
private theorem tensor_single0_component_inv_comm
    (E : Cpx) (N : ModuleCat A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensor_single0_component_inv E N i ≫
        (HomologicalComplex.tensorObj E (singleZeroCpx N)).d i j =
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        tensor_single0_component_inv E N j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Proof comment: expand the total differential and kill the vertical summand from the single complex.
  simp only [tensor_single0_component_inv, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := E)
      (K₂ := singleZeroCpx N)
      (F := curriedTensor (ModuleCat A))
      (c := ComplexShape.up ℤ)
      (h := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))
      (i₂ := 0)
      (j := i + 1)
      (h' := by simp)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := E)
      (K₂ := singleZeroCpx N)
      (F := curriedTensor (ModuleCat A))
      (c := ComplexShape.up ℤ)
      (i₁ := i)
      (h := (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp))
      (j := i + 1)
      (h' := by simp)]
  have hsingle : ((singleZeroCpx N).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, CategoryTheory.Limits.zero_comp, smul_zero,
    CategoryTheory.Limits.comp_zero, add_zero]
  rw [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 by
      rfl, one_smul]
  rw [← Category.assoc]
  rw [tensor_single0_diagonal_iso_inv_naturality
      (E := E)
      (N := N)
      (i := i)
      (j := i + 1)
      (hij := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))]
  simp [HomologicalComplex.ιTensorObj, Category.assoc]

/-- Helper for Lemma 15.103.2: tensoring a cochain complex with a degree-zero single complex is
canonically the same as tensoring on the right by the underlying module. -/
private noncomputable def tensor_single0_complex_iso
    (E : Cpx) (N : ModuleCat A) :
    HomologicalComplex.tensorObj E (singleZeroCpx N) ≅
      ((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ tensor_single0_component_iso E N n)
    (fun i j hij ↦ by
      -- Proof comment: rewrite the inverse chain-map square into the forward orientation expected by
      -- `isoOfComponents`.
      apply (cancel_mono (tensor_single0_component_iso E N j).inv).1
      apply (cancel_epi (tensor_single0_component_iso E N i).inv).1
      simpa [Category.assoc] using
        (tensor_single0_component_inv_comm E N i j hij).symm)

/-- Helper for Lemma 15.103.2: right tensoring a degree-zero single complex stays degree-zero. -/
private noncomputable def singleZeroTensorRightComplexIso
    (M N : ModuleCat A) :
    ((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (singleZeroCpx M) ≅
      singleZeroCpx (ModuleCat.of A ((↑M) ⊗[A] ↑N)) :=
  -- Proof comment: `singleMapHomologicalComplex` is the canonical owner for this degree-zero transport.
  (HomologicalComplex.singleMapHomologicalComplex
    (CategoryTheory.MonoidalCategory.tensorRight N) (ComplexShape.up ℤ) (0 : ℤ)).app M

/-- Helper for Lemma 15.103.2: tensoring two degree-zero single cochain complexes is canonically
the degree-zero single complex of the tensor product module. -/
private noncomputable def singleZeroTensorComplexIso
    (M N : ModuleCat A) :
    HomologicalComplex.tensorObj (singleZeroCpx M) (singleZeroCpx N) ≅
      singleZeroCpx (ModuleCat.of A ((↑M) ⊗[A] ↑N)) := by
  -- Route correction: the literal equality route is too rigid, so we first compare the tensor
  -- complex with right tensoring, then use `singleMapHomologicalComplex`.
  exact
    tensor_single0_complex_iso (singleZeroCpx M) N ≪≫
      singleZeroTensorRightComplexIso M N

/-- Helper for Lemma 15.103.2: the derived tensor of two degree-zero module objects is the
degree-zero object of the ordinary tensor product module. -/
private noncomputable def single0_derivedTensor_module_iso
    (M N : ModuleCat A) :
    ((single₀).obj M ⊗[A]^L (single₀).obj N) ≅
      (single₀).obj (ModuleCat.of A ((↑M) ⊗[A] ↑N)) :=
  -- Proof comment: pass from the derived tensor product to `Q` of the tensor complex, then replace
  -- that tensor complex by the degree-zero tensor-module complex.
  ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (ModuleCat.of A ((↑M) ⊗[A] ↑N))).symm) ≪≫
    (DerivedCategory.Q.mapIso (singleZeroTensorComplexIso M N).symm) ≪≫
      (Functor.Monoidal.μIso (DerivedCategory.Q : Cpx ⥤ DMod) (singleZeroCpx M)
        (singleZeroCpx N)).symm ≪≫
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M) ⊗ᵢ
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app N)) ≪≫
          derivedCategory_tensorObj_iso_derivedTensorProduct ((single₀).obj M)
            ((single₀).obj N)).symm

/-- Helper for Lemma 15.103.2: the comparison
`single₀(X) ⊗^L single₀(N) ≅ single₀(X ⊗ N)` is natural in the first variable. -/
private theorem single0_derivedTensor_module_iso_naturality
    {X Y N : ModuleCat A} (f : X ⟶ Y) :
    ((derivedTensorProduct ((single₀).obj N)).map ((single₀).map f)) ≫
        (single0_derivedTensor_module_iso Y N).hom =
      (single0_derivedTensor_module_iso X N).hom ≫
        (single₀).map (ModuleCat.ofHom (f.hom.rTensor N)) := by
  -- Proof comment: unfold the comparison iso and use naturality of `singleFunctorIsoCompQ`,
  -- `Q.mapIso`, and the monoidal structure map `μIso`.
  simp [single0_derivedTensor_module_iso, Category.assoc]

/-- Helper for Lemma 15.103.2: after identifying `A[0] ⊗^L N[0]` with `(A ⊗ N)[0]`, the ordinary
tensor-unit map agrees with `singleZeroDerivedTensorIso`. -/
private theorem single0_derivedTensor_unit_compat
    (N : ModuleCat A) :
    (single0_derivedTensor_module_iso (ModuleCat.of A A) N).hom ≫
        (single₀).map (ModuleCat.ofHom ((TensorProduct.lid A N).toLinearMap)) =
      (singleZeroDerivedTensorIso ((single₀).obj N)).hom := by
  -- Proof comment: both sides are the same canonical route from `A[0] ⊗^L N[0]` to `N[0]`.
  simp [single0_derivedTensor_module_iso, singleZeroDerivedTensorIso, Category.assoc]

/-- Helper for Lemma 15.103.2: if `I` annihilates `N`, then the derived map
`I[0] ⊗^L N[0] → N[0]` induced by `I ↪ A` is zero. -/
private theorem ideal_single0_derivedTensor_to_single0_eq_zero_of_annihilator_le
    (I : Ideal A) (N : ModuleCat A)
    (hN : I ≤ Module.annihilator A N) :
    ((derivedTensorProduct ((single₀).obj N)).map
        ((single₀).map (ModuleCat.ofHom I.subtype))) ≫
      (singleZeroDerivedTensorIso ((single₀).obj N)).hom = 0 := by
  -- Proof comment: rewrite the derived tensor map through the degree-zero tensor comparison and
  -- then use the ordinary tensor vanishing `I ⊗ N → A ⊗ N`.
  rw [← single0_derivedTensor_unit_compat (N := N)]
  rw [Category.assoc]
  rw [single0_derivedTensor_module_iso_naturality (N := N) (f := ModuleCat.ofHom I.subtype)]
  rw [Category.assoc]
  have hTensor :
      ModuleCat.ofHom (I.subtype.rTensor N) = 0 := by
    simpa using congrArg ModuleCat.ofHom
      (ideal_subtype_rTensor_eq_zero_of_annihilator_le I N hN)
  simp [Functor.map_comp, hTensor, Category.assoc]

/-- Helper for Lemma 15.103.2: the comparison from ambient tensoring to derived tensoring is
natural in the left variable, written in the direction used by the source diagram chase. -/
@[reassoc]
private theorem tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit
    (N : DMod) {K L : DMod} (f : K ⟶ L) :
    (derivedCategory_tensorObj_iso_derivedTensorProduct K N).hom ≫
        (derivedTensorProduct N).map f =
      (f ▷ N) ≫ (derivedCategory_tensorObj_iso_derivedTensorProduct L N).hom := by
  -- Proof comment: this is exactly the componentwise naturality of the tensor/derived-tensor
  -- comparison isomorphism for the fixed right factor `N`.
  simpa using ((tensoringRightIsoDerivedTensorProduct N).hom.naturality f).symm

/-- Helper for Lemma 15.103.2: after unfolding the transport isomorphisms, the tensorized middle
factor from the source proof is already in the desired rebracketed normal form. -/
private theorem single0_tensorized_factorization_transport_normal_form
    (I : Ideal A) (M N : ModuleCat A) :
    let I0 := (single₀).obj (ModuleCat.of A ↥I)
    let M0 := (single₀).obj M
    let N0 := (single₀).obj N
    ((derivedTensorProduct N0).map
        ((derivedTensorProduct M0).map
          ((single₀).map (ModuleCat.ofHom I.subtype)))) ≫
      (derivedTensorProduct N0).map (singleZeroDerivedTensorIso M0).hom =
        ((derivedTensorProduct N0).map (derivedTensorProduct_comm I0 M0).hom) ≫
          (derivedTensorProduct_associator M0 I0 N0).hom ≫
            (derivedTensorProduct M0).map
              ((((derivedTensorProduct N0).map
                  ((single₀).map (ModuleCat.ofHom I.subtype))) ≫
                (singleZeroDerivedTensorIso N0).hom)) := by
  -- Proof comment: unfolding `singleZeroDerivedTensorIso` and the derived-tensor comparison turns
  -- both sides into the same ambient `β/α/λ` composite.
  simp only [singleZeroDerivedTensorIso, derivedTensorProduct_associator, derivedTensorProduct_comm,
    derivedCategory_tensorObj_iso_derivedTensorProduct, tensoringRightIsoDerivedTensorProduct_hom_app,
    tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit, Category.assoc]

/-- Helper for Lemma 15.103.2: the tensorized middle factor in the source proof rebrackets through
`M[0] ⊗^L (I[0] ⊗^L N[0])` via the standard commutor and associator. -/
private theorem single0_tensorized_factorization_middle_rebracket
    (I : Ideal A) (M N : ModuleCat A) :
    let I0 := (single₀).obj (ModuleCat.of A ↥I)
    let M0 := (single₀).obj M
    let N0 := (single₀).obj N
    ((derivedTensorProduct N0).map
        ((derivedTensorProduct M0).map
          ((single₀).map (ModuleCat.ofHom I.subtype)))) ≫
      (derivedTensorProduct N0).map (singleZeroDerivedTensorIso M0).hom =
        ((derivedTensorProduct N0).map (derivedTensorProduct_comm I0 M0).hom) ≫
          (derivedTensorProduct_associator M0 I0 N0).hom ≫
            (derivedTensorProduct M0).map
              ((((derivedTensorProduct N0).map
                  ((single₀).map (ModuleCat.ofHom I.subtype))) ≫
                (singleZeroDerivedTensorIso N0).hom)) := by
  -- Proof comment: this is the omitted tensor-coherence square from the source proof, written as
  -- one rebracketing identity so later rewrites only substitute the zero factor.
  -- Route correction: the transport mismatch is now isolated by
  -- `tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit`, so the remaining work is the
  -- pure ambient tensor coherence identity after conjugating through
  -- `derivedCategory_tensorObj_iso_derivedTensorProduct _ N0`.
  -- Proof comment: the dedicated normal-form lemma now isolates the transport bookkeeping, so this
  -- theorem is the source-facing rebracketing statement with no further ambient computation.
  simpa using single0_tensorized_factorization_transport_normal_form I M N

/-- Helper for Lemma 15.103.2: a zero tensor factor stays zero after applying
`derivedTensorProduct M`. -/
private theorem derivedTensorProduct_map_eq_zero_of_zero
    {K L M : DMod} {f : K ⟶ L} (hf : f = 0) :
    (derivedTensorProduct M).map f = 0 := by
  -- Proof comment: exact functoriality preserves the zero morphism.
  simpa [hf]

/-- Helper for Lemma 15.103.2: after tensoring with `N[0]`, the chosen factorization of
`I^[n]M[0] → M[0]` forces the tensorized inclusion morphism to vanish. -/
lemma idealPowerSubtype_single0_tensor_map_eq_zero_of_annihilator_le
    (I : Ideal A) (M N : ModuleCat A) (n : ℕ)
    (α : (single₀).obj (idealPowerStage I n M) ⟶
      (single₀).obj (ModuleCat.of A ↥I) ⊗[A]^L (single₀).obj M)
    (hα : α ≫
        (derivedTensorProduct ((single₀).obj M)).map
          ((single₀).map (ModuleCat.ofHom I.subtype)) ≫
        (singleZeroDerivedTensorIso ((single₀).obj M)).hom =
      (single₀).map (ModuleCat.ofHom (idealPowerSubtype I n M)))
    (hN : I ≤ Module.annihilator A N) :
    (derivedTensorProduct ((single₀).obj N)).map
      ((single₀).map (ModuleCat.ofHom (idealPowerSubtype I n M))) = 0 := by
  -- Route correction: the zero factor `I[0] ⊗^L N[0] → N[0]` is now isolated above, so the only
  -- remaining work is the source-faithful associator/commuting-square rewrite that identifies the
  -- tensorized factorization from `hα` with a composite through that zero factor.
  let I0 : DMod := (single₀).obj (ModuleCat.of A ↥I)
  let M0 : DMod := (single₀).obj M
  let N0 : DMod := (single₀).obj N
  have hZeroFactor :
      ((derivedTensorProduct N0).map
          ((single₀).map (ModuleCat.ofHom I.subtype))) ≫
        (singleZeroDerivedTensorIso N0).hom = 0 :=
    ideal_single0_derivedTensor_to_single0_eq_zero_of_annihilator_le I N hN
  have hTensorizedFactorization :
      (derivedTensorProduct N0).map
          ((single₀).map (ModuleCat.ofHom (idealPowerSubtype I n M))) =
        (derivedTensorProduct N0).map α ≫
          ((derivedTensorProduct N0).map
              ((derivedTensorProduct M0).map
                ((single₀).map (ModuleCat.ofHom I.subtype)))) ≫
            (derivedTensorProduct N0).map (singleZeroDerivedTensorIso M0).hom := by
    -- Proof comment: tensor the source factorization `hα` with `N[0]` and expand only functorial
    -- composition data.
    simpa [Functor.map_comp, Category.assoc] using
      congrArg ((derivedTensorProduct N0).map) hα
  have hRebracket :
      ((derivedTensorProduct N0).map
          ((derivedTensorProduct M0).map
            ((single₀).map (ModuleCat.ofHom I.subtype)))) ≫
        (derivedTensorProduct N0).map (singleZeroDerivedTensorIso M0).hom =
          ((derivedTensorProduct N0).map (derivedTensorProduct_comm I0 M0).hom) ≫
            (derivedTensorProduct_associator M0 I0 N0).hom ≫
              (derivedTensorProduct M0).map
                ((((derivedTensorProduct N0).map
                    ((single₀).map (ModuleCat.ofHom I.subtype))) ≫
                  (singleZeroDerivedTensorIso N0).hom)) :=
    single0_tensorized_factorization_middle_rebracket I M N
  have hMappedZero :
      (derivedTensorProduct M0).map
          ((((derivedTensorProduct N0).map
              ((single₀).map (ModuleCat.ofHom I.subtype))) ≫
            (singleZeroDerivedTensorIso N0).hom)) = 0 := by
    -- Proof comment: exact functoriality carries the already isolated zero factor to zero.
    exact derivedTensorProduct_map_eq_zero_of_zero (M := M0) hZeroFactor
  -- Proof comment: rewrite the tensorized middle factor into the source-order composite through
  -- `M[0] ⊗^L (I[0] ⊗^L N[0])`, substitute the zero factor, and simplify.
  calc
    (derivedTensorProduct N0).map
        ((single₀).map (ModuleCat.ofHom (idealPowerSubtype I n M))) =
      (derivedTensorProduct N0).map α ≫
        (((derivedTensorProduct N0).map (derivedTensorProduct_comm I0 M0).hom) ≫
          (derivedTensorProduct_associator M0 I0 N0).hom ≫
            (derivedTensorProduct M0).map
              ((((derivedTensorProduct N0).map
                  ((single₀).map (ModuleCat.ofHom I.subtype))) ≫
                (singleZeroDerivedTensorIso N0).hom))) := by
          rw [hTensorizedFactorization, hRebracket]
          simp [Category.assoc]
    _ = 0 := by
      simp [hMappedZero, Category.assoc]

-- Proof sketch: apply Lemma `15.102.7` to factor the inclusion `I^[n] M → M` through the derived
-- tensor map induced by `I → A`, then tensor with `N`. Since `I ≤ Module.annihilator A N`, the
-- map `I ⊗_A^{\mathbf L} N → N` is zero, so the induced maps on all Tor groups vanish.
/-- Lemma 15.103.2: if `A` is Noetherian, `I ⊆ A` is an ideal, `M` is a finite `A`-module, and
`N` is annihilated by `I`, then some positive power `I^n M` maps trivially to `M` on every
`Tor_p^A(-, N)`. -/
theorem exists_idealPower_tor_map_eq_zero_of_annihilator_le
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    (hN : I ≤ Module.annihilator A N) :
    ∃ n : ℕ, 0 < n ∧ ∀ p : ℕ,
      idealPowerSubtypeTorMap I n M N p = 0 := by
  rcases exists_idealPower_single0_factorization_through_ideal_derivedTensor_map I M with
    ⟨n, hn, α, hα⟩
  refine ⟨n, hn, ?_⟩
  intro p
  have hTensor :
      (derivedTensorProduct ((single₀).obj N)).map
        ((single₀).map (ModuleCat.ofHom (idealPowerSubtype I n M))) = 0 :=
    idealPowerSubtype_single0_tensor_map_eq_zero_of_annihilator_le I M N n α hα hN
  have hCompare :=
    tor_map_eq_homology_map_of_single0_tensor
      (N := N) (f := ModuleCat.ofHom (idealPowerSubtype I n M)) p
  rw [idealPowerSubtypeTorMap] at hCompare
  have hCompareZero :
      idealPowerSubtypeTorMap I n M N p ≫
          (tor_single0_tensor_homology_iso M N p).hom = 0 := by
    -- Replace the tensorized inclusion by the zero morphism and collapse the right-hand side.
    simpa [hTensor] using hCompare
  -- Cancel the comparison isomorphism on the right to recover the canonical `Tor` map itself.
  exact (cancel_mono (tor_single0_tensor_homology_iso M N p).hom).1 hCompareZero

end

end CategoryTheory
