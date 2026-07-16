import stacks_proof.stacks_project.Chap10.Lemma_10_128_3.StageRawKernel

universe uR uS uM

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable {f : R →+* S} [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

namespace DirectedLocalEssFinitePresentationModuleApproximation

/-- Helper for Lemma 10.128.3: the canonical map from a stage module to the limit module sends
`m` to the image of `1 ⊗ m` under the final base-change equivalence. -/
noncomputable def stage_module_to_limit_fun
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i).toAlgebra
    A.moduleStage i → M :=
  let _ : Algebra (A.SStage i) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom
      A.toDirectedLocalHomApproximation i).toAlgebra
  fun m ↦ A.finalBaseChange i (1 ⊗ₜ[A.SStage i] m)

/-- Helper for Lemma 10.128.3: the stage-to-limit module map is additive. -/
lemma stage_module_to_limit_fun_map_add
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ)
    (m n : A.moduleStage i) :
    let _ : Algebra (A.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i).toAlgebra
    stage_module_to_limit_fun A i (m + n) =
      stage_module_to_limit_fun A i m + stage_module_to_limit_fun A i n := by
  let _ : Algebra (A.SStage i) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom
      A.toDirectedLocalHomApproximation i).toAlgebra
  -- Proof comment: the final base-change equivalence is linear, so it carries the sum
  -- `1 ⊗ (m + n)` to the sum of the two stage images.
  simp [stage_module_to_limit_fun, TensorProduct.tmul_add]

/-- Helper for Lemma 10.128.3: the stage-to-limit module map is linear over the source-stage ring
when the limit module is viewed through `source_stage_to_limit_hom`. -/
lemma stage_module_to_limit_fun_map_smul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ)
    (r : A.RStage i) (m : A.moduleStage i) :
    let _ : Algebra (A.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i).toAlgebra
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    stage_module_to_limit_fun A i (r • m) = r • stage_module_to_limit_fun A i m := by
  let _ : Algebra (A.SStage i) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom
      A.toDirectedLocalHomApproximation i).toAlgebra
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  -- Proof comment: move the source-stage scalar onto the left tensor factor, then rewrite the
  -- resulting `S`-scalar via the colimit square `R_i → R → S`.
  let s :
      S := DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i (A.stageMap i r)
  have hs :
      s = (f.comp (source_stage_to_limit_hom A i)) r := by
    simpa [s, source_stage_to_target_limit_hom] using
      congrArg (fun g : A.RStage i →+* S ↦ g r)
        (source_stage_to_target_limit_eq (A := A) (i := i))
  calc
    stage_module_to_limit_fun A i (r • m)
        = A.finalBaseChange i (s • (1 ⊗ₜ[A.SStage i] m)) := by
            apply congrArg (A.finalBaseChange i)
            change (1 : S) ⊗ₜ[A.SStage i] ((A.stageMap i r) • m) =
              s • ((1 : S) ⊗ₜ[A.SStage i] m)
            rw [TensorProduct.tmul_smul]
            have hsone : ((A.stageMap i) r : A.SStage i) • (1 : S) = s := by
              change
                ((DirectedLocalHomApproximation.targetStageToLimitHom
                    A.toDirectedLocalHomApproximation i) ((A.stageMap i) r) * 1 : S) = s
              simp [s]
            simpa [hsone, TensorProduct.smul_tmul', Algebra.smul_def]
    _ = s • A.finalBaseChange i (1 ⊗ₜ[A.SStage i] m) := by
          simpa using (A.finalBaseChange i).map_smul s (1 ⊗ₜ[A.SStage i] m)
    _ = (f.comp (source_stage_to_limit_hom A i) r) •
          A.finalBaseChange i (1 ⊗ₜ[A.SStage i] m) := by
          rw [hs]
    _ = r • stage_module_to_limit_fun A i m := by
          rfl

/-- Helper for Lemma 10.128.3: package the stage-to-limit map as a source-stage linear map into
the limit module. -/
noncomputable def stage_module_to_limit
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i).toAlgebra
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    A.moduleStage i →ₗ[A.RStage i] M :=
  let _ : Algebra (A.SStage i) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom
      A.toDirectedLocalHomApproximation i).toAlgebra
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  { toFun := stage_module_to_limit_fun A i
    map_add' := stage_module_to_limit_fun_map_add (A := A) (i := i)
    map_smul' := stage_module_to_limit_fun_map_smul (A := A) (i := i) }

/-- Helper for Lemma 10.128.3: the ambient tensor transport from the raw stage tensor to the
limit-side tensor over `R`, obtained by first sending `M_i` to `M` and then extending the ideal.
-/
noncomputable def raw_kernel_limit_map
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    I ⊗[A.RStage i] A.moduleStage i →ₗ[A.RStage i]
      Ideal.map (source_stage_to_limit_hom A i) I ⊗[R] M :=
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  (mapped_ideal_tensor_map (R := A.RStage i) (R' := R) (N := M) I).comp
    ((stage_module_to_limit A i).lTensor I)

/-- Helper for Lemma 10.128.3: after applying the canonical tensor transport to the limit, the
raw stage multiplication agrees with multiplication in the limit module. -/
lemma raw_kernel_limit_to_module_comp
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    LinearMap.restrictScalars (A.RStage i)
      (TensorProduct.lift
        ((LinearMap.lsmul R M).comp (Ideal.map (source_stage_to_limit_hom A i) I).subtype)) ∘ₗ
      raw_kernel_limit_map A i I =
      stage_module_to_limit A i ∘ₗ
        LinearMap.restrictScalars (A.RStage i) (raw_stage_multiplication A i I) := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  -- Proof comment: the outer comparison is the standard mapped-ideal tensor bridge, and once the
  -- ideal is put on the `R`-side, both composites are determined by the same pure-tensor formula.
  ext a m
  calc
    ((LinearMap.restrictScalars (A.RStage i)
        (TensorProduct.lift
          ((LinearMap.lsmul R M).comp (Ideal.map (source_stage_to_limit_hom A i) I).subtype)) ∘ₗ
        raw_kernel_limit_map A i I)
        (a ⊗ₜ[A.RStage i] m))
        = (TensorProduct.lift ((LinearMap.lsmul (A.RStage i) M).comp I.subtype))
            (((stage_module_to_limit A i).lTensor I) (a ⊗ₜ[A.RStage i] m)) := by
              have hcompare :=
                congrArg
                  (fun g : I ⊗[A.RStage i] M →ₗ[A.RStage i] M ↦
                    g (((stage_module_to_limit A i).lTensor I) (a ⊗ₜ[A.RStage i] m)))
                  (mapped_ideal_tensor_to_module_comp
                    (R := A.RStage i) (R' := R) (N := M) I)
              simpa [raw_kernel_limit_map, LinearMap.comp_apply] using hcompare
    _ = (TensorProduct.lift ((LinearMap.lsmul (A.RStage i) M).comp I.subtype))
          (a ⊗ₜ[A.RStage i] stage_module_to_limit A i m) := by
            simp
    _ = a.1 • stage_module_to_limit A i m := by
          simp
    _ = stage_module_to_limit A i (a.1 • m) := by
          symm
          simpa using stage_module_to_limit_fun_map_smul
            (A := A) (i := i) a.1 m
    _ = ((stage_module_to_limit A i ∘ₗ
          LinearMap.restrictScalars (A.RStage i) (raw_stage_multiplication A i I))
          (a ⊗ₜ[A.RStage i] m)) := by
          simp [raw_stage_multiplication_tmul]

/-- Helper for Lemma 10.128.3: every element of the raw stage kernel has zero image under the
canonical limit-side tensor transport. -/
lemma raw_kernel_limit_zero
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (z : raw_stage_kernel A i I) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    raw_kernel_limit_map A i I z.1 = 0 := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  let μ :
      Ideal.map (source_stage_to_limit_hom A i) I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift
      ((LinearMap.lsmul R M).comp (Ideal.map (source_stage_to_limit_hom A i) I).subtype)
  have hμ_injective : Function.Injective μ := by
    -- Proof comment: flatness of the limit module over `R` gives injectivity of the ideal tensor
    -- multiplication map for every ideal of `R`.
    exact ideal_tensor_to_module_injective_of_flat (A := R) (I := Ideal.map (source_stage_to_limit_hom A i) I) hflat
  apply hμ_injective
  have hz_map := congrArg (fun g ↦ g z.1) (raw_kernel_limit_to_module_comp (A := A) (i := i) (I := I))
  -- Proof comment: the right-hand composite vanishes because `z` belongs to the raw kernel by
  -- definition.
  calc
    μ (raw_kernel_limit_map A i I z.1)
        = stage_module_to_limit A i
            (LinearMap.restrictScalars (A.RStage i) (raw_stage_multiplication A i I) z.1) := by
            simpa [μ, LinearMap.comp_apply] using hz_map
    _ = 0 := by
          have hz : raw_stage_multiplication A i I z.1 = 0 :=
            raw_stage_kernel_multiplication_eq_zero (A := A) (i := i) (I := I) z
          simpa [hz]

/-- Helper for Lemma 10.128.3: the target-side tail direct limit above `i` is `S`, viewed as an
`R_i`-module through the composite map `R_i → S_i → S`. -/
noncomputable def tail_target_limit_linearEquiv
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let tailLimit :=
      Ring.DirectLimit
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ A.targetMap j.1 k.1 h)
    let _ : Algebra (A.RStage i) tailLimit :=
      ((Ring.DirectLimit.toLimitHom
          (fun j : Set.Ici i ↦ A.SStage j.1)
          (fun j k h ↦ A.targetMap j.1 k.1 h)
          (RingEquiv.refl tailLimit) ⟨i, le_rfl⟩).comp (A.stageMap i)).toAlgebra
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    tailLimit ≃ₗ[A.RStage i] S := by
  let tailLimit :=
    Ring.DirectLimit
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ A.targetMap j.1 k.1 h)
  let tailStageToLimit :
      A.SStage i →+* tailLimit :=
    Ring.DirectLimit.toLimitHom
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ A.targetMap j.1 k.1 h)
      (RingEquiv.refl tailLimit) ⟨i, le_rfl⟩
  let _ : Algebra (A.RStage i) tailLimit := (tailStageToLimit.comp (A.stageMap i)).toAlgebra
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  let tailIso :=
    tail_directLimitIso A.SStage (fun i' j h ↦ A.targetMap i' j h) i A.targetColimit
  refine
    { toFun := tailIso
      invFun := tailIso.symm
      left_inv := by
        intro x
        exact tailIso.left_inv x
      right_inv := by
        intro x
        exact tailIso.right_inv x
      map_add' := by
        intro x y
        exact map_add tailIso x y
      map_smul' := by
        intro r x
        -- Proof comment: evaluate the tail/full direct-limit comparison on the source-stage
        -- generator coming from `r`, then multiply in the target ring `S`.
        change
          tailIso (algebraMap (A.RStage i) tailLimit r * x) =
            (source_stage_to_target_limit_hom A i r) *
              tailIso x
        rw [map_mul]
        have hcoeff : tailIso (algebraMap (A.RStage i) tailLimit r) =
            source_stage_to_target_limit_hom A i r := by
          change tailIso
              (Ring.DirectLimit.of
                (fun j : Set.Ici i ↦ A.SStage j.1)
                (fun j k h ↦ A.targetMap j.1 k.1 h) ⟨i, le_rfl⟩ ((A.stageMap i) r)) =
            source_stage_to_target_limit_hom A i r
          simp [tailIso, tailStageToLimit, source_stage_to_target_limit_hom,
            DirectedLocalHomApproximation.targetStageToLimitHom, tail_directLimitIso,
            Ring.DirectLimit.toLimitHom, RingHom.comp_apply]
        simpa [hcoeff] using congrArg (fun s : S ↦ s * tailIso x) hcoeff }

/-- Helper for Lemma 10.128.3: the limit map from a later target stage to `S` is linear over the
fixed source stage `R_i`. -/
lemma source_stage_to_target_limit_isScalarTower
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (j : Set.Ici i) :
    let _ : Algebra (A.RStage i) (A.SStage j.1) :=
      (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage j.1) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation j.1).toAlgebra
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    IsScalarTower (A.RStage i) (A.SStage j.1) S := by
  let _ : Algebra (A.RStage i) (A.SStage j.1) :=
    (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage j.1) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom
      A.toDirectedLocalHomApproximation j.1).toAlgebra
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: the source-stage scalar reaches `S` either directly through
  -- `source_stage_to_target_limit_hom A i` or by first passing through the later target stage and
  -- then taking the direct-limit map, and these two composites agree by the colimit square.
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext r
  -- Proof comment: evaluate both algebra maps on a source-stage scalar and rewrite the target
  -- path using the direct-limit compatibility of the approximation.
  symm
  change
    DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation j.1
        ((source_stage_to_later_target_hom A i j.1 j.2) r) =
      source_stage_to_target_limit_hom A i r
  calc
    DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation j.1
        ((source_stage_to_later_target_hom A i j.1 j.2) r)
        =
      DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation j.1
        (A.targetMap i j.1 j.2 ((A.stageMap i) r)) := by
          rfl
    _ =
      DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation i
        ((A.stageMap i) r) := by
          simpa [RingHom.comp_apply] using congrArg
            (fun g : A.SStage i →+* S ↦ g ((A.stageMap i) r))
            (targetStageToLimitHom_comp_targetMap
              (f := f) A.toDirectedLocalHomApproximation j.2)
    _ = source_stage_to_target_limit_hom A i r := by
          rfl

/-- Helper for Lemma 10.128.3: the tail/full comparison sends a tail-stage coefficient class to
its ambient image in `S`. -/
lemma tail_target_limit_linearEquiv_of
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (j : Set.Ici i) (r : A.SStage j.1) :
    let tailLimit :=
      Ring.DirectLimit
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ A.targetMap j.1 k.1 h)
    tail_target_limit_linearEquiv A i
      (Ring.DirectLimit.of
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ A.targetMap j.1 k.1 h) j r) =
      DirectedLocalHomApproximation.targetStageToLimitHom
        A.toDirectedLocalHomApproximation j.1 r := by
  change
    (tail_directLimitIso A.SStage (fun i' j' h ↦ A.targetMap i' j' h) i A.targetColimit)
      (Ring.DirectLimit.of
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ A.targetMap j.1 k.1 h) j r) =
      A.targetColimit
        (Ring.DirectLimit.of A.SStage (fun i' j' h ↦ A.targetMap i' j' h) j.1 r)
  -- Proof comment: the tail/full direct-limit comparison is literally the forgetful map on stage
  -- representatives, so it sends the tail class of `r` to the ambient class of the same element.
  simp [tail_target_limit_linearEquiv, tail_directLimitIso, tail_directLimit_to_full_of,
    DirectedLocalHomApproximation.targetStageToLimitHom]

/-- Helper for Lemma 10.128.3: the tail/full direct-limit comparison sends the base-stage unit
coefficient to the ambient unit. -/
lemma tail_target_limit_linearEquiv_of_base_one
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) :
    let tailLimit :=
      Ring.DirectLimit
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ A.targetMap j.1 k.1 h)
    tail_target_limit_linearEquiv A i
      (Ring.DirectLimit.of
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ A.targetMap j.1 k.1 h) ⟨i, le_rfl⟩ (1 : A.SStage i)) =
      (1 : S) := by
  -- Proof comment: specialize the stage-representative formula for the tail/full comparison to
  -- the initial tail stage and then use preservation of `1` by the target-stage map.
  simpa using
    tail_target_limit_linearEquiv_of (A := A) (i := i) ⟨i, le_rfl⟩ (1 : A.SStage i)

/-- Helper for Chap10 Lemma 10 128 3: for the owner whose transition maps are
`tail_target_algHom`, the tail/full comparison sends the base-stage scalar class to the
corresponding scalar in the ambient target limit. -/
lemma tail_target_owner_limit_base_scalar
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (r : A.RStage i) :
    let _ : IsDirectedOrder (Set.Ici i) := tail_index_isDirected i
    let _ : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
      fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    let _ : DirectedSystem
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1)) :=
      tail_target_directedSystem A i
    let tailLimit :=
      Ring.DirectLimit
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
    let _ : Algebra (A.RStage i) tailLimit :=
      ((Ring.DirectLimit.toLimitHom
          (fun j : Set.Ici i ↦ A.SStage j.1)
          (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
          (RingEquiv.refl tailLimit) ⟨i, le_rfl⟩).comp
        (source_stage_to_later_target_hom A i i le_rfl)).toAlgebra
    let tailIso := tail_directLimitIso A.SStage (fun i' j h ↦ A.targetMap i' j h)
      i A.targetColimit
    tailIso (algebraMap (A.RStage i) tailLimit r) = source_stage_to_target_limit_hom A i r := by
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected i
  letI : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
    fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
  letI : DirectedSystem
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1)) :=
    tail_target_directedSystem A i
  let tailLimit :=
    Ring.DirectLimit
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
  let _ : Algebra (A.RStage i) tailLimit :=
    ((Ring.DirectLimit.toLimitHom
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
        (RingEquiv.refl tailLimit) ⟨i, le_rfl⟩).comp
      (source_stage_to_later_target_hom A i i le_rfl)).toAlgebra
  let tailIso :=
    tail_directLimitIso A.SStage (fun i' j h ↦ A.targetMap i' j h) i A.targetColimit
  -- Proof comment: unfold only the base-stage class, replace the initial tail source map by
  -- `A.stageMap i`, and use the generic tail-to-full representative formula.
  change tailIso
      (Ring.DirectLimit.of
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
        ⟨i, le_rfl⟩ ((source_stage_to_later_target_hom A i i le_rfl) r)) =
    source_stage_to_target_limit_hom A i r
  rw [source_stage_to_later_target_hom_self]
  have hof :
      (tail_directLimit_to_full A.SStage (fun i' j h ↦ A.targetMap i' j h) i)
        (Ring.DirectLimit.of
          (fun j : Set.Ici i ↦ A.SStage j.1)
          (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
          ⟨i, le_rfl⟩ ((A.stageMap i) r)) =
      (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.targetMap i j h) i) ((A.stageMap i) r) := by
    change (tail_directLimit_to_full A.SStage (fun i' j h ↦ A.targetMap i' j h) i)
        (Ring.DirectLimit.of
          (fun j : Set.Ici i ↦ A.SStage j.1)
          (fun j k h ↦ A.targetMap j.1 k.1 h)
          ⟨i, le_rfl⟩ ((A.stageMap i) r)) =
      (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.targetMap i j h) i) ((A.stageMap i) r)
    exact tail_directLimit_to_full_of
      A.SStage (fun i' j h ↦ A.targetMap i' j h) i ⟨i, le_rfl⟩ ((A.stageMap i) r)
  simpa [tailIso, source_stage_to_target_limit_hom,
    DirectedLocalHomApproximation.targetStageToLimitHom, tail_directLimitIso,
    RingHom.comp_apply] using congrArg A.targetColimit hof

/-- Helper for Chap10 Lemma 10 128 3: the tail/full comparison for the `tail_target_algHom`
owner is linear over the fixed source stage. -/
lemma tail_target_owner_limit_map_smul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (r : A.RStage i) :
    let _ : IsDirectedOrder (Set.Ici i) := tail_index_isDirected i
    let _ : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
      fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    let _ : DirectedSystem
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1)) :=
      tail_target_directedSystem A i
    let tailLimit :=
      Ring.DirectLimit
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
    let _ : Algebra (A.RStage i) tailLimit :=
      ((Ring.DirectLimit.toLimitHom
          (fun j : Set.Ici i ↦ A.SStage j.1)
          (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
          (RingEquiv.refl tailLimit) ⟨i, le_rfl⟩).comp
        (source_stage_to_later_target_hom A i i le_rfl)).toAlgebra
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    let tailIso := tail_directLimitIso A.SStage (fun i' j h ↦ A.targetMap i' j h)
      i A.targetColimit
    ∀ x : tailLimit, tailIso (r • x) = r • tailIso x := by
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected i
  letI : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
    fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
  letI : DirectedSystem
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1)) :=
    tail_target_directedSystem A i
  let tailLimit :=
    Ring.DirectLimit
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
  let _ : Algebra (A.RStage i) tailLimit :=
    ((Ring.DirectLimit.toLimitHom
        (fun j : Set.Ici i ↦ A.SStage j.1)
        (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1))
        (RingEquiv.refl tailLimit) ⟨i, le_rfl⟩).comp
      (source_stage_to_later_target_hom A i i le_rfl)).toAlgebra
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  let tailIso :=
    tail_directLimitIso A.SStage (fun i' j h ↦ A.targetMap i' j h) i A.targetColimit
  change ∀ x : tailLimit,
    tailIso (algebraMap (A.RStage i) tailLimit r * x) =
      (source_stage_to_target_limit_hom A i r) * tailIso x
  intro x
  -- Proof comment: reduce source-stage linearity to the already-normalized image of a base-stage
  -- scalar, then use multiplicativity of the tail/full ring equivalence.
  have hmul :
      tailIso (algebraMap (A.RStage i) tailLimit r * x) =
        tailIso (algebraMap (A.RStage i) tailLimit r) * tailIso x := by
    exact map_mul tailIso (algebraMap (A.RStage i) tailLimit r) x
  rw [hmul]
  have hcoeff :
      tailIso (algebraMap (A.RStage i) tailLimit r) = source_stage_to_target_limit_hom A i r :=
    tail_target_owner_limit_base_scalar (A := A) (i := i) r
  simpa [hcoeff]

end DirectedLocalEssFinitePresentationModuleApproximation

end
