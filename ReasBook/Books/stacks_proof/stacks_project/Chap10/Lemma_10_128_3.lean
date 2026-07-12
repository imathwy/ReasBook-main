import StacksProject_2024.Chap10.Lemma_10_128_3.Index

-- Declarations for this item will be appended below by the statement pipeline.
universe uR uS uM

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable {f : R →+* S} [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

-- Proof sketch: for a fixed stage `λ`, Remark `10.75.9` identifies
-- `Tor₁^{R_λ}(M_λ, R_λ / 𝔪_λ)` with the kernel of `𝔪_λ ⊗[R_λ] M_λ → M_λ`, so this Tor module is
-- finite over `S_λ`. Because `M` is flat over `R`, the corresponding kernel vanishes after
-- passing to the colimit, hence finitely many generators die at some larger stage `λ'`. Applying
-- Lemma `10.99.14` to the local base-change square supplied by the approximation then yields
-- flatness of `M_{λ'}` over `R_{λ'}`.
namespace DirectedLocalEssFinitePresentationModuleApproximation

/-- Helper for the eventual-flatness lemma: the later target stage `A.SStage j` is an
`A.SStage i`-algebra compatible with the source-stage maps out of `A.RStage i`. -/
lemma sourceStageToLaterTarget_isScalarTower
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) :=
      (source_stage_to_later_target_hom A i j hij).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) :=
    (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  -- Proof comment: both routes `R_i → S_i → S_j` and `R_i → S_j` are the same transition map.
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext r
  simpa [RingHom.algebraMap_toAlgebra, source_stage_to_later_target_hom, RingHom.comp_apply] using
    congrArg
      (fun g : A.RStage i →+* A.SStage j ↦ g r)
      (source_stage_to_later_target_eq (A := A) (i := i) (j := j) hij)

/-- Helper for the eventual-flatness lemma: the standard stage module action is the canonical
`R_i-S_i` scalar tower instance. -/
instance stageModuleIsScalarTowerInst
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
  stage_module_isScalarTower A i

/-- Helper for the eventual-flatness lemma: the source-stage and target-stage scalar actions commute on
the stage module. -/
instance stageModuleSmulCommClassInst
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
  stage_module_smulCommClass A i

/-- Helper for the eventual-flatness lemma: the later target stage carries the canonical scalar tower
coming from the approximation transition square. -/
instance sourceStageToLaterTargetIsScalarTowerInst
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) :=
      (source_stage_to_later_target_hom A i j hij).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
  sourceStageToLaterTarget_isScalarTower A i j hij

/-- Helper for the eventual-flatness lemma: the ambient target module `M` is an `R-S` scalar tower
when the `R`-action is obtained by restriction of scalars along `f`. -/
lemma limitModuleTarget_isScalarTower :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra R S := f.toAlgebra
    IsScalarTower R S M := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra R S := f.toAlgebra
  -- Proof comment: the restricted `R`-action is literally scalar multiplication by `f r`.
  refine ⟨?_⟩
  intro r s m
  change ((f r) * s) • m = (f r) • (s • m)
  rw [mul_smul]

/-- Helper for Lemma 10.128.3: transporting the base-stage tail tensor through the
tail/full direct-limit comparison identifies it with the ambient target-limit tensor
`(1 : S) ⊗ x`. -/
lemma tailTargetOwner_stageTensorMap_to_targetLimit
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (x : I ⊗[A.RStage i] A.moduleStage i) :
    let X : Type _ := I ⊗[A.RStage i] A.moduleStage i
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
    let _ : Module (A.RStage i) tailLimit := inferInstance
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    (TensorProduct.congr (tail_target_limit_linearEquiv A i) (LinearEquiv.refl (A.RStage i) X))
      (stageTensorMap
        (A := A.RStage i) (I := Set.Ici i)
        (R := fun j : Set.Ici i ↦ A.SStage j.1)
        (f := fun j k h ↦ tail_target_algHom A i j k h)
        X ⟨i, le_rfl⟩ ((1 : A.SStage i) ⊗ₜ[A.RStage i] x)) =
      (1 : S) ⊗ₜ[A.RStage i] x := by
  let X : Type _ := I ⊗[A.RStage i] A.moduleStage i
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
  let _ : Module (A.RStage i) tailLimit := inferInstance
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: `stageTensorMap` at the initial tail stage is the pure tensor with the base
  -- tail class, and `tail_target_limit_linearEquiv` sends that class to the ambient unit.
  simpa [stageTensorMap] using
    congrArg (fun s : S ↦ s ⊗ₜ[A.RStage i] x)
      (tail_target_limit_linearEquiv_of_base_one (A := A) (i := i))

/-- Helper for Lemma 10.128.3: on pure tensors, the raw-kernel limit transport first
pushes the module factor to the limit and then extends the ideal. -/
lemma raw_kernel_limit_map_tmul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (a : I) (m : A.moduleStage i) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    raw_kernel_limit_map A i I (a ⊗ₜ[A.RStage i] m) =
      (ideal_to_mapped_ideal (R := A.RStage i) (R' := R) I a) ⊗ₜ[R]
        stage_module_to_limit A i m := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  -- Proof comment: unfold the packaged transport once; both factors are then governed by the
  -- defining pure-tensor formulas of `lTensor` and `mapped_ideal_tensor_map`.
  calc
    raw_kernel_limit_map A i I (a ⊗ₜ[A.RStage i] m)
        = mapped_ideal_tensor_map (R := A.RStage i) (R' := R) (N := M) I
            (((stage_module_to_limit A i).lTensor I) (a ⊗ₜ[A.RStage i] m)) := by
              rfl
    _ = mapped_ideal_tensor_map (R := A.RStage i) (R' := R) (N := M) I
          (a ⊗ₜ[A.RStage i] stage_module_to_limit A i m) := by
            simp
    _ =
      (ideal_to_mapped_ideal (R := A.RStage i) (R' := R) I a) ⊗ₜ[R]
        stage_module_to_limit A i m := by
          simp

/-- Helper for Lemma 10.128.3: after extending scalars from `R` to `S`, a vanishing
raw-kernel limit owner still vanishes in the target-limit mapped-ideal tensor owner. -/
lemma raw_kernel_limit_map_target_base_change_zero
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (x : I ⊗[A.RStage i] A.moduleStage i)
    (hzero :
      let _ : Module R M := Module.compHom M f
      let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
      let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
      let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
      raw_kernel_limit_map A i I x = 0) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra R S := f.toAlgebra
    let _ : IsScalarTower R S M := limitModuleTarget_isScalarTower (R := R) (S := S) (f := f)
    (mapped_ideal_tensor_map
      (R := R) (R' := S) (N := M)
      (Ideal.map (source_stage_to_limit_hom A i) I))
      (raw_kernel_limit_map A i I x) = 0 := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  let _ : Algebra R S := f.toAlgebra
  let _ : IsScalarTower R S M := limitModuleTarget_isScalarTower (R := R) (S := S) (f := f)
  -- Proof comment: the remaining transport will compare the ambient target-limit tensor to this
  -- scalar-extended owner, so vanishing can already be pushed across the canonical `R → S`
  -- mapped-ideal tensor map at no additional cost.
  simpa [hzero]

/-- Helper for Chap10 Lemma 10 128 3: the ambient target-limit owner
`S ⊗[A.RStage i] (I ⊗[A.RStage i] A.moduleStage i)` is the standard iterated base-change
owner `((S ⊗[A.RStage i] I) ⊗[S] (S ⊗[A.RStage i] A.moduleStage i))`. -/
noncomputable def targetLimitOwnerDistribBaseChange
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    S ⊗[A.RStage i] (I ⊗[A.RStage i] A.moduleStage i) ≃ₗ[S]
      (S ⊗[A.RStage i] I) ⊗[S] (S ⊗[A.RStage i] A.moduleStage i) :=
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: this is the canonical base-change distribution equivalence; naming it keeps
  -- the remaining transport problem separate from ambient tensor reassociation.
  TensorProduct.AlgebraTensorModule.distribBaseChange
    (A.RStage i) S I (A.moduleStage i)

/-- Helper for Chap10 Lemma 10 128 3: under the distributed base-change owner, the ambient pure
tensor `(1 : S) ⊗ (a ⊗ m)` becomes `((1 : S) ⊗ a) ⊗ ((1 : S) ⊗ m)`. -/
lemma targetLimitOwnerDistribBaseChange_apply_one_tmul_tmul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (a : I) (m : A.moduleStage i) :
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    targetLimitOwnerDistribBaseChange (A := A) i I
        ((1 : S) ⊗ₜ[A.RStage i] (a ⊗ₜ[A.RStage i] m)) =
      (((1 : S) ⊗ₜ[A.RStage i] a) : S ⊗[A.RStage i] I) ⊗ₜ[S]
        (((1 : S) ⊗ₜ[A.RStage i] m) : S ⊗[A.RStage i] A.moduleStage i) := by
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: the named owner equivalence is built from `distribBaseChange`, whose pure
  -- tensor formula already puts the ambient owner into the desired iterated normal form.
  simpa [targetLimitOwnerDistribBaseChange] using
    (TensorProduct.AlgebraTensorModule.distribBaseChange_tmul
      (R := A.RStage i) (A := S) (n := a) (q := m) (a := (1 : S)))

/-- Helper for Chap10 Lemma 10 128 3: tensoring the stage-to-limit map with the ambient target
ring `S` gives the canonical `S`-linear transport from `S ⊗[A.RStage i] A.moduleStage i` to `M`.
-/
noncomputable def targetLimitModuleLift
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    S ⊗[A.RStage i] A.moduleStage i →ₗ[S] M :=
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: this is the ambient `S`-linear lift of the source-stage map `M_i → M`.
  TensorProduct.AlgebraTensorModule.lift (stage_module_to_limit A i)

/-- Helper for Chap10 Lemma 10 128 3: the ambient lifted module map evaluates on
`(1 : S) ⊗ m` by the original stage-to-limit map. -/
lemma targetLimitModuleLift_apply_one_tmul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (m : A.moduleStage i) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    targetLimitModuleLift (A := A) i ((1 : S) ⊗ₜ[A.RStage i] m) =
      stage_module_to_limit A i m := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: `targetLimitModuleLift` is the standard algebra-tensor lift of
  -- `stage_module_to_limit`, so `1 ⊗ m` evaluates by the defining computation rule.
  simp [targetLimitModuleLift]

/-- Helper for the eventual-flatness lemma: tensoring the source-stage raw-kernel transport with the
ambient target ring `S` packages the comparison from the ambient tensor
`S ⊗[A.RStage i] (I ⊗[A.RStage i] A.moduleStage i)` to the scalar-extended raw-kernel owner. -/
noncomputable def targetLimitRawKernelTransport
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    S ⊗[A.RStage i] (I ⊗[A.RStage i] A.moduleStage i) →ₗ[S]
      Ideal.map (source_stage_to_target_limit_hom A i) I ⊗[S] M :=
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  TensorProduct.AlgebraTensorModule.lift
    ((mapped_ideal_tensor_map (R := A.RStage i) (R' := S) (N := M) I).comp
      ((stage_module_to_limit A i).lTensor I))

/-- Helper for the eventual-flatness lemma: the packaged ambient target-limit transport evaluates on
`(1 : S) ⊗ x` by applying the source-stage raw-kernel transport to `x`. -/
lemma targetLimitRawKernelTransport_apply_one_tmul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (x : I ⊗[A.RStage i] A.moduleStage i) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    targetLimitRawKernelTransport (A := A) i I ((1 : S) ⊗ₜ[A.RStage i] x) =
      (mapped_ideal_tensor_map (R := A.RStage i) (R' := S) (N := M) I)
        (((stage_module_to_limit A i).lTensor I) x) := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: the packaged transport is the standard algebra-tensor lift of the raw-kernel
  -- comparison, so `1 ⊗ x` evaluates by the defining computation rule of that lift.
  simp [targetLimitRawKernelTransport]

/-- Helper for the eventual-flatness lemma: on a pure raw tensor `a ⊗ m`, the ambient target-limit
transport sends `(1 : S) ⊗ (a ⊗ m)` to the corresponding mapped-ideal pure tensor over `S`. -/
lemma targetLimitRawKernelTransport_apply_one_tmul_tmul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (a : I) (m : A.moduleStage i) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    targetLimitRawKernelTransport (A := A) i I
        ((1 : S) ⊗ₜ[A.RStage i] (a ⊗ₜ[A.RStage i] m)) =
      (ideal_to_mapped_ideal (R := A.RStage i) (R' := S) I a) ⊗ₜ[S]
        stage_module_to_limit A i m := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: first reduce to the `1 ⊗ x` computation rule, then simplify the source-stage
  -- transport and the mapped-ideal tensor bridge on the pure tensor `a ⊗ m`.
  calc
    targetLimitRawKernelTransport (A := A) i I
        ((1 : S) ⊗ₜ[A.RStage i] (a ⊗ₜ[A.RStage i] m)) =
      (mapped_ideal_tensor_map (R := A.RStage i) (R' := S) (N := M) I)
        (((stage_module_to_limit A i).lTensor I) (a ⊗ₜ[A.RStage i] m)) := by
          simpa using
            targetLimitRawKernelTransport_apply_one_tmul
              (A := A) (i := i) (I := I) (a ⊗ₜ[A.RStage i] m)
    _ =
      (mapped_ideal_tensor_map (R := A.RStage i) (R' := S) (N := M) I)
        (a ⊗ₜ[A.RStage i] stage_module_to_limit A i m) := by
          simp
    _ =
      (ideal_to_mapped_ideal (R := A.RStage i) (R' := S) I a) ⊗ₜ[S]
        stage_module_to_limit A i m := by
          simp

/-- Helper for the eventual-flatness lemma: mapping the source-stage ideal directly to the ambient
target limit agrees with first mapping it to the source limit ring `R` and then extending scalars
along `f : R →+* S`. -/
lemma sourceStageToTargetLimitIdealMap_eq
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    Ideal.map (source_stage_to_target_limit_hom A i) I =
      Ideal.map f (Ideal.map (source_stage_to_limit_hom A i) I) := by
  -- Proof comment: the two ring maps from `A.RStage i` to `S` are equal by the colimit square,
  -- so the induced ideal extensions coincide.
  rw [source_stage_to_target_limit_eq]
  rw [Ideal.map_map]

/-- Helper for the eventual-flatness lemma: on a pure tensor `a ⊗ m`, the direct transport to the
ambient target limit agrees with first moving to the source-limit raw-kernel owner and then
extending scalars from `R` to `S`. -/
lemma targetLimitRawKernelTransport_apply_one_tmul_tmul_eq_iteratedBaseChange
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (a : I) (m : A.moduleStage i) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    targetLimitRawKernelTransport (A := A) i I
        ((1 : S) ⊗ₜ[A.RStage i] (a ⊗ₜ[A.RStage i] m)) =
      (mapped_ideal_tensor_map (R := R) (R' := S) (N := M)
        (Ideal.map (source_stage_to_limit_hom A i) I))
        (raw_kernel_limit_map A i I (a ⊗ₜ[A.RStage i] m)) := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: both routes are pure tensors with the same module factor; after rewriting the
  -- target ideal owner, their left factors are the same element of `S`.
  rw [sourceStageToTargetLimitIdealMap_eq (A := A) (i := i) (I := I)]
  calc
    targetLimitRawKernelTransport (A := A) i I
        ((1 : S) ⊗ₜ[A.RStage i] (a ⊗ₜ[A.RStage i] m)) =
      (ideal_to_mapped_ideal (R := A.RStage i) (R' := S) I a) ⊗ₜ[S]
        stage_module_to_limit A i m := by
          simpa using
            targetLimitRawKernelTransport_apply_one_tmul_tmul
              (A := A) (i := i) (I := I) a m
    _ =
      (ideal_to_mapped_ideal (R := R) (R' := S)
        (Ideal.map (source_stage_to_limit_hom A i) I)
        (ideal_to_mapped_ideal (R := A.RStage i) (R' := R) I a)) ⊗ₜ[S]
          stage_module_to_limit A i m := by
            congr 1
            ext
            change f ((source_stage_to_limit_hom A i) a.1) =
              source_stage_to_target_limit_hom A i a.1
            simpa [RingHom.comp_apply] using
              congrArg (fun g : A.RStage i →+* S ↦ g a.1)
                (source_stage_to_target_limit_eq (A := A) (i := i))
    _ =
      (mapped_ideal_tensor_map (R := R) (R' := S) (N := M)
        (Ideal.map (source_stage_to_limit_hom A i) I))
        (raw_kernel_limit_map A i I (a ⊗ₜ[A.RStage i] m)) := by
          simp [raw_kernel_limit_map_tmul]

/-- Helper for Chap10 Lemma 10 128 3: the ambient target-limit transport on `1 ⊗ x`
agrees with first moving `x` to the limit-side raw-kernel owner over `R` and then extending
scalars along `f : R →+* S`. -/
lemma targetLimitRawKernelTransport_apply_one_tmul_eq_iteratedBaseChange
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (x : I ⊗[A.RStage i] A.moduleStage i) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    targetLimitRawKernelTransport (A := A) i I ((1 : S) ⊗ₜ[A.RStage i] x) =
      (mapped_ideal_tensor_map (R := R) (R' := S) (N := M)
        (Ideal.map (source_stage_to_limit_hom A i) I))
        (raw_kernel_limit_map A i I x) := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: the pure-tensor comparison is already proved, so tensor induction upgrades it
  -- to the full owner `I ⊗[R_i] M_i` without introducing any new transport choices.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [targetLimitRawKernelTransport]
  · intro a m
    simpa using
      targetLimitRawKernelTransport_apply_one_tmul_tmul_eq_iteratedBaseChange
        (A := A) (i := i) (I := I) a m
  · intro x y hx hy
    simp [hx, hy]

/-- Helper for Chap10 Lemma 10 128 3: if the source-limit raw-kernel owner of `x` already
vanishes over `R`, then the packaged ambient target-limit transport of `(1 : S) ⊗ x` vanishes
after extending scalars along `f`. -/
lemma targetLimitRawKernelTransport_zero_of_raw_kernel_limit_zero
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (x : I ⊗[A.RStage i] A.moduleStage i)
    (hzero :
      let _ : Module R M := Module.compHom M f
      let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
      let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
      let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
      raw_kernel_limit_map A i I x = 0) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
    let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
    targetLimitRawKernelTransport (A := A) i I ((1 : S) ⊗ₜ[A.RStage i] x) = 0 := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
  let _ : Algebra (A.RStage i) S := (source_stage_to_target_limit_hom A i).toAlgebra
  -- Proof comment: first rewrite the ambient target-limit transport through the already-proved
  -- iterated `R → S` base-change formula, then use the zero source-limit owner.
  calc
    targetLimitRawKernelTransport (A := A) i I ((1 : S) ⊗ₜ[A.RStage i] x) =
      (mapped_ideal_tensor_map (R := R) (R' := S) (N := M)
        (Ideal.map (source_stage_to_limit_hom A i) I))
        (raw_kernel_limit_map A i I x) := by
          simpa using
            targetLimitRawKernelTransport_apply_one_tmul_eq_iteratedBaseChange
              (A := A) (i := i) (I := I) x
    _ = 0 := by
      simpa using
        raw_kernel_limit_map_target_base_change_zero
          (A := A) (i := i) (I := I) x hzero

/-- Helper for the eventual-flatness lemma: the raw stage kernel at a chosen stage admits a finite
family of generators over `A.SStage i`. -/
lemma existsFiniteRawStageKernelGenerators
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) :
    let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
    ∃ n : ℕ, ∃ ξ : Fin n → raw_stage_kernel A i I,
      Submodule.span (A.SStage i) (Set.range ξ) = ⊤ := by
  let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
  let Kraw := raw_stage_kernel A i I
  have hKraw_finite : Module.Finite (A.SStage i) Kraw := raw_stage_kernel_finite A i
  -- Proof comment: isolate the finite-generation input from Remark `10.75.9` so the main theorem
  -- can focus on descending generator zeroes and the later-stage flatness criterion.
  simpa [I, Kraw] using Module.Finite.exists_fin (R := A.SStage i) (M := Kraw)

/-- Helper for Lemma 10.128.3: canceling the iterated base change of `1 ⊗ z` over an
intermediate algebra `B` recovers the tensor map induced by `B → S`. -/
lemma cancelBaseChange_one_tmul_eq_rTensor_restrictScalars
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {S : Type*} [CommRing S] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    {N : Type*} [AddCommGroup N] [Module A N]
    (z : B ⊗[A] N) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B S S N) ((1 : S) ⊗ₜ[B] z) =
      (LinearMap.rTensor N ((Algebra.linearMap B S).restrictScalars A)) z := by
  -- Proof comment: verify the formula on pure tensors, where both sides are the same scalar
  -- transport, and then extend by tensor induction.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro b n
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simpa [Algebra.smul_def]
  · intro z₁ z₂ hz₁ hz₂
    rw [TensorProduct.tmul_add, map_add,
      (LinearMap.rTensor N ((Algebra.linearMap B S).restrictScalars A)).map_add, hz₁, hz₂]

/-- Helper for Lemma 10.128.3: once a raw-kernel generator vanishes at one later target stage,
it remains zero after passing to any still later stage of the same tail system. -/
lemma rawKernelOwnerZero_mono
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    {j k : A.Λ} (hij : i ≤ j) (hjk : j ≤ k)
    {z : raw_stage_kernel A i I}
    (hz :
      let _ : Algebra (A.RStage i) (A.SStage i) :=
        (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
      let _ : Algebra (A.RStage i) (A.SStage j) :=
        (source_stage_to_later_target_hom A i j hij).toAlgebra
      LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
        ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
          A.SStage i →ₗ[A.RStage i] A.SStage j)
        ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1) = 0) :
    let _ : Algebra (A.RStage i) (A.SStage i) :=
      (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage k) :=
      (source_stage_to_later_target_hom A i k (hij.trans hjk)).toAlgebra
    LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
      ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨k, hij.trans hjk⟩ (hij.trans hjk)).toLinearMap :
        A.SStage i →ₗ[A.RStage i] A.SStage k)
      ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1) = 0 := by
  let _ : Algebra (A.RStage i) (A.SStage i) :=
    (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) :=
    (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage k) :=
    (source_stage_to_later_target_hom A i k (hij.trans hjk)).toAlgebra
  have hcomp :
      ((tail_target_algHom A i ⟨j, hij⟩ ⟨k, hij.trans hjk⟩ hjk).toLinearMap :
          A.SStage j →ₗ[A.RStage i] A.SStage k).comp
        ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
          A.SStage i →ₗ[A.RStage i] A.SStage j) =
      ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨k, hij.trans hjk⟩ (hij.trans hjk)).toLinearMap :
        A.SStage i →ₗ[A.RStage i] A.SStage k) := by
    -- Proof comment: the two tail transitions compose to the direct transition along the directed
    -- target system, so their right-tensor maps may be collapsed to one map from stage `i`.
    ext s
    change A.targetMap j k hjk (A.targetMap i j hij s) = A.targetMap i k (hij.trans hjk) s
    simpa using (DirectedSystem.map_map
      (f := fun a b h ↦ A.targetMap a b h) hij hjk s).symm
  -- Proof comment: apply the later tail transition to the known zero, then rewrite the composed
  -- right-tensor map back to the single transition from the base stage.
  calc
    LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
      ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨k, hij.trans hjk⟩ (hij.trans hjk)).toLinearMap :
        A.SStage i →ₗ[A.RStage i] A.SStage k)
      ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1)
        =
      LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
        (((tail_target_algHom A i ⟨j, hij⟩ ⟨k, hij.trans hjk⟩ hjk).toLinearMap :
            A.SStage j →ₗ[A.RStage i] A.SStage k).comp
          ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
            A.SStage i →ₗ[A.RStage i] A.SStage j))
        ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1) := by
          rw [hcomp]
    _ =
      LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
        ((tail_target_algHom A i ⟨j, hij⟩ ⟨k, hij.trans hjk⟩ hjk).toLinearMap :
          A.SStage j →ₗ[A.RStage i] A.SStage k)
        (LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
          ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
            A.SStage i →ₗ[A.RStage i] A.SStage j)
          ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1)) := by
            symm
            exact LinearMap.rTensor_comp_apply
              (M := I ⊗[A.RStage i] A.moduleStage i)
              (f := ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
                A.SStage i →ₗ[A.RStage i] A.SStage j))
              (g := ((tail_target_algHom A i ⟨j, hij⟩ ⟨k, hij.trans hjk⟩ hjk).toLinearMap :
                A.SStage j →ₗ[A.RStage i] A.SStage k))
              (x := ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1))
    _ = 0 := by
      simp [hz]

/-- Helper for Lemma 10.128.3: after canceling the later-stage base change, tensoring the raw-stage
kernel subtype on the base generator `z` gives the current owner expression. -/
lemma tensorizedRawKernelSubtype_baseGenerator_eq_owner
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    (z : raw_stage_kernel A i I) :
    let _ : Algebra (A.RStage i) (A.SStage i) :=
      (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) :=
      (source_stage_to_later_target_hom A i j hij).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := inferInstance
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := inferInstance
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      inferInstance
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (A.RStage i) (A.SStage i) (A.SStage j) (A.SStage j)
      (I ⊗[A.RStage i] A.moduleStage i))
      ((((raw_stage_kernel A i I).subtype).lTensor (A.SStage j))
        ((1 : A.SStage j) ⊗ₜ[A.SStage i] z)) =
      LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
        ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
          A.SStage i →ₗ[A.RStage i] A.SStage j)
        ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1) := by
  let _ : Algebra (A.RStage i) (A.SStage i) :=
    (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) :=
    (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := inferInstance
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := inferInstance
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    inferInstance
  -- Proof comment: specialize the later family-level computation to the single generator `z`; the
  -- tensorized subtype map on `1 ⊗ z` is exactly the right-tensor owner used downstream.
  simpa [tail_target_algHom_toRingHom] using
    cancelBaseChange_one_tmul_eq_rTensor_restrictScalars
      (A := A.RStage i) (B := A.SStage i) (S := A.SStage j)
      (N := I ⊗[A.RStage i] A.moduleStage i)
      ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1)

/-- Helper for Lemma 10.128.3: once the tensorized raw-kernel subtype kills the base generator at a
later stage, the current owner expression vanishes there as well. -/
lemma tensorizedRawKernelSubtype_zero_to_owner_zero
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    (z : raw_stage_kernel A i I)
    (hz :
      let _ : Algebra (A.RStage i) (A.SStage i) :=
        (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
      let _ : Algebra (A.RStage i) (A.SStage j) :=
        (source_stage_to_later_target_hom A i j hij).toAlgebra
      let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
      let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := inferInstance
      let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
      let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
      let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := inferInstance
      let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
        inferInstance
      (((raw_stage_kernel A i I).subtype).lTensor (A.SStage j))
        ((1 : A.SStage j) ⊗ₜ[A.SStage i] z) = 0) :
    let _ : Algebra (A.RStage i) (A.SStage i) :=
      (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) :=
      (source_stage_to_later_target_hom A i j hij).toAlgebra
    LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
      ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
        A.SStage i →ₗ[A.RStage i] A.SStage j)
      ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1) = 0 := by
  let _ : Algebra (A.RStage i) (A.SStage i) :=
    (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) :=
    (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := inferInstance
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := inferInstance
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    inferInstance
  -- Proof comment: rewrite the current owner as the canceled tensorized subtype value and then
  -- use the assumed vanishing of that later-stage subtype tensor.
  calc
    LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
      ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
        A.SStage i →ₗ[A.RStage i] A.SStage j)
      ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1)
        =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        (A.RStage i) (A.SStage i) (A.SStage j) (A.SStage j)
        (I ⊗[A.RStage i] A.moduleStage i))
        ((((raw_stage_kernel A i I).subtype).lTensor (A.SStage j))
          ((1 : A.SStage j) ⊗ₜ[A.SStage i] z)) := by
            symm
            simpa using
              tensorizedRawKernelSubtype_baseGenerator_eq_owner
                (A := A) (i := i) (j := j) hij (I := I) z
    _ = 0 := by
      simpa [hz]

/-- Helper for Chap10 Lemma 10 128 3: package the image of a raw-kernel generator `z` in the
source-facing later mapped-ideal owner at stage `j`. This is the Stacks-text object whose direct
limit should match `raw_kernel_limit_map A i I z.1`. -/
noncomputable def laterMappedRawKernelOwnerGenerator
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    (z : raw_stage_kernel A i I) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j hij).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) :=
      (source_stage_to_later_target_hom A i j hij).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := inferInstance
    let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
    let _ : Module (A.RStage i) Mj' :=
      Module.compHom Mj' (source_stage_to_later_target_hom A i j hij)
    Ideal.map (A.map i j hij) I ⊗[A.RStage j] Mj' :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j hij).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) :=
    (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := inferInstance
  let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
  let _ : Module (A.RStage i) Mj' :=
    Module.compHom Mj' (source_stage_to_later_target_hom A i j hij)
  -- Proof comment: first rewrite `1 ⊗ z.1` into the source ideal tensor owner over the later
  -- module `Mj'`, then apply the canonical mapped-ideal tensor map along `A.map i j hij`.
  mapped_ideal_tensor_map (R := A.RStage i) (R' := A.RStage j) (N := Mj') I
    ((sourceIdealTensorDomainEquiv (A := A) (i := i) (j := j) hij I).symm
      ((1 : A.SStage j) ⊗ₜ[A.SStage i] z.1))

/-- Helper for Lemma 10.128.3: the only remaining descent step is to force the tensorized raw-stage
kernel generator itself to vanish at a later target stage. -/
lemma existsLaterStageTensorizedRawKernelSubtypeZero
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (z : raw_stage_kernel A i I)
    (hzero :
      let _ : Module R M := Module.compHom M f
      let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
      let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
      let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
      raw_kernel_limit_map A i I z.1 = 0) :
    ∃ j : A.Λ, ∃ hij : i ≤ j,
      let _ : Algebra (A.RStage i) (A.SStage i) :=
        (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
      let _ : Algebra (A.RStage i) (A.SStage j) :=
        (source_stage_to_later_target_hom A i j hij).toAlgebra
      let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
      let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := inferInstance
      let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
      let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
      let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := inferInstance
      let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
        inferInstance
      (((raw_stage_kernel A i I).subtype).lTensor (A.SStage j))
        ((1 : A.SStage j) ⊗ₜ[A.SStage i] z) = 0 := by
  -- Route correction: the old blocker was the wrong normal form. The source proof descends zero in
  -- the later mapped-ideal owner `laterMappedRawKernelOwnerGenerator`, not directly in the
  -- tensorized subtype tail system.
  -- Proof comment: the remaining work is now isolated to one source-facing colimit bridge from the
  -- mapped-owner family to `raw_kernel_limit_map A i I z.1`; once that bridge is proved, the
  -- later mapped-owner zero can be converted back to the current subtype-tensor surface.
  -- TODO: prove that the direct-limit class of
  -- `laterMappedRawKernelOwnerGenerator (A := A) (i := i) (j := i) le_rfl (I := I) z`
  -- is exactly `raw_kernel_limit_map A i I z.1`, then use `Module.DirectLimit.of.zero_exact` to
  -- get a later mapped-owner zero and finish by a dedicated adapter from mapped-owner zero to
  -- tensorized subtype zero.
  sorry

/-- Helper for Lemma 10.128.3: a raw-kernel generator whose limit-side owner vanishes already
dies in one sufficiently large later owner. -/
lemma existsLaterStageRawKernelGeneratorOwnerZero
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (z : raw_stage_kernel A i I)
    (hzero :
      let _ : Module R M := Module.compHom M f
      let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
      let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
      let _ : IsScalarTower (A.RStage i) R M := limit_module_source_stage_isScalarTower A i
      raw_kernel_limit_map A i I z.1 = 0) :
    ∃ j : A.Λ, ∃ hij : i ≤ j,
      let _ : Algebra (A.RStage i) (A.SStage i) :=
        (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
      let _ : Algebra (A.RStage i) (A.SStage j) :=
        (source_stage_to_later_target_hom A i j hij).toAlgebra
      LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
        ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
          A.SStage i →ₗ[A.RStage i] A.SStage j)
        ((1 : A.SStage i) ⊗ₜ[A.RStage i] z.1) = 0 := by
  -- Route correction: the old ambient-target route tried to reflect vanishing from
  -- `targetLimitRawKernelTransport`, but the source argument only needs eventual zero in the later
  -- raw-kernel owner system.
  -- Proof comment: factor the proof through the smaller later-stage statement that the tensorized
  -- raw-kernel subtype on `z` itself vanishes; the final owner equality is a separate adapter.
  obtain ⟨j, hij, hz⟩ :=
    existsLaterStageTensorizedRawKernelSubtypeZero
      (A := A) (i := i) (I := I) z hzero
  refine ⟨j, hij, ?_⟩
  exact tensorizedRawKernelSubtype_zero_to_owner_zero
    (A := A) (i := i) (j := j) hij (I := I) z hz

/-- Helper for Lemma 10.128.3: finitely many raw-kernel generator zeroes in the limit descend to a
single later target stage in the stable owner `S_j ⊗[R_i] (I ⊗[R_i] M_i)`. -/
lemma raw_kernel_zero_descends_on_finset
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    {n : ℕ} (ξ : Fin n → raw_stage_kernel A i I) :
    ∃ j : A.Λ, ∃ hij : i ≤ j,
      let _ : Algebra (A.RStage i) (A.SStage i) :=
        (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
      let _ : Algebra (A.RStage i) (A.SStage j) :=
        (source_stage_to_later_target_hom A i j hij).toAlgebra
      ∀ k,
        LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
          ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
            A.SStage i →ₗ[A.RStage i] A.SStage j)
          ((1 : A.SStage i) ⊗ₜ[A.RStage i] (ξ k).1) = 0 := by
  classical
  let P : Finset (Fin n) → Prop := fun s ↦
    ∃ j : A.Λ, ∃ hij : i ≤ j,
      let _ : Algebra (A.RStage i) (A.SStage i) :=
        (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
      let _ : Algebra (A.RStage i) (A.SStage j) :=
        (source_stage_to_later_target_hom A i j hij).toAlgebra
      ∀ k ∈ s,
        LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
          ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
            A.SStage i →ₗ[A.RStage i] A.SStage j)
          ((1 : A.SStage i) ⊗ₜ[A.RStage i] (ξ k).1) = 0
  have hP : ∀ s : Finset (Fin n), P s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨i, le_rfl, ?_⟩
        intro k hk
        exact False.elim (Finset.notMem_empty k hk)
    | @insert a s ha hs =>
        obtain ⟨j₁, hij₁, hz₁⟩ :=
          existsLaterStageRawKernelGeneratorOwnerZero
            (A := A) (i := i) (I := I) (ξ a)
            (raw_kernel_limit_zero (A := A) hflat i I (ξ a))
        obtain ⟨j₂, hij₂, hz₂⟩ := hs
        obtain ⟨j, hj₁j, hj₂j⟩ := exists_ge_ge j₁ j₂
        refine ⟨j, hij₁.trans hj₁j, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · -- Proof comment: move the singled-out generator zero from its witness stage `j₁` to the
          -- common upper bound `j`.
          exact rawKernelOwnerZero_mono
            (A := A) (i := i) (I := I) hij₁ hj₁j hz₁
        · -- Proof comment: the induction hypothesis gives zeroes on the older finite family at
          -- stage `j₂`, and the monotonicity helper transports them to the common upper bound.
          exact rawKernelOwnerZero_mono
            (A := A) (i := i) (I := I) hij₂ hj₂j (hz₂ k hk)
  obtain ⟨j, hij, hzero⟩ := hP (Finset.univ : Finset (Fin n))
  refine ⟨j, hij, ?_⟩
  intro k
  exact hzero k (by simp)

/-- Helper for Lemma 10.128.3: an `A`-linear map is zero once it vanishes on a family
whose span is all of the source module. -/
lemma linearMap_eq_zero_of_span_range_eq_top
    {A : Type*} [Semiring A]
    {P : Type*} [AddCommMonoid P] [Module A P]
    {Q : Type*} [AddCommMonoid Q] [Module A Q]
    {ι : Type*} (ξ : ι → P)
    (hξspan : Submodule.span A (Set.range ξ) = ⊤)
    (φ : P →ₗ[A] Q)
    (hξzero : ∀ i, φ (ξ i) = 0) :
    φ = 0 := by
  -- Proof comment: every source element lies in the span of the chosen family, so span
  -- induction reduces the map value to the given zero values on generators.
  ext p
  have hp : p ∈ Submodule.span A (Set.range ξ) := by
    rw [hξspan]
    trivial
  refine Submodule.span_induction (p := fun x _ ↦ φ x = 0) hp ?_ ?_ ?_ ?_
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    simpa using hξzero i
  · simp
  · intro x y hx hy
    simp [hx, hy]
  · intro a x hx
    simp [hx]

/-- Helper for Lemma 10.128.3: after base change to the later target stage, the tensors
`(1 : A.SStage j) ⊗ ξ k` still span the whole tensorized raw kernel. -/
lemma laterRawKernelGenerators_span_top
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    {n : ℕ} (ξ : Fin n → raw_stage_kernel A i I)
    (hξspan : Submodule.span (A.SStage i) (Set.range ξ) = ⊤) :
    let _ : Algebra (A.RStage i) (A.SStage i) :=
      (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) :=
      (source_stage_to_later_target_hom A i j hij).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    Submodule.span (A.SStage j)
      (Set.range (fun k : Fin n ↦ (1 : A.SStage j) ⊗ₜ[A.SStage i] ξ k)) = ⊤ := by
  let _ : Algebra (A.RStage i) (A.SStage i) :=
    (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) :=
    (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  have hrange :
      Set.range (fun k : Fin n ↦ (1 : A.SStage j) ⊗ₜ[A.SStage i] ξ k) =
        (TensorProduct.mk (A.SStage i) (A.SStage j) (raw_stage_kernel A i I) 1) ''
          Set.range ξ := by
    ext z
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨ξ k, ⟨k, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
  -- Proof comment: rewrite the later-stage tensorized kernel as the base change of the original
  -- raw kernel, then transport the original spanning hypothesis through `baseChange_span`.
  calc
    Submodule.span (A.SStage j)
        (Set.range (fun k : Fin n ↦ (1 : A.SStage j) ⊗ₜ[A.SStage i] ξ k)) =
      Submodule.span (A.SStage j)
        ((TensorProduct.mk (A.SStage i) (A.SStage j) (raw_stage_kernel A i I) 1) ''
          Set.range ξ) := by
            rw [hrange]
    _ = (Submodule.span (A.SStage i) (Set.range ξ)).baseChange (A.SStage j) := by
          rw [Submodule.baseChange_span]
    _ = (⊤ : Submodule (A.SStage i) (raw_stage_kernel A i I)).baseChange (A.SStage j) := by
          rw [hξspan]
    _ = ⊤ := by
          rw [Submodule.baseChange_top]

/-- Helper for Lemma 10.128.3: after canceling the later-stage base change, the descended
generator owner `hξ_owner_zero` is exactly the tensorized raw-kernel subtype evaluated on
`(1 : A.SStage j) ⊗ ξ k`. -/
lemma tensorizedRawKernelSubtype_generator_eq_owner
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    {n : ℕ} (ξ : Fin n → raw_stage_kernel A i I)
    (k : Fin n) :
    let _ : Algebra (A.RStage i) (A.SStage i) :=
      (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) :=
      (source_stage_to_later_target_hom A i j hij).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := inferInstance
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := inferInstance
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      inferInstance
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (A.RStage i) (A.SStage i) (A.SStage j) (A.SStage j)
      (I ⊗[A.RStage i] A.moduleStage i))
      ((((raw_stage_kernel A i I).subtype).lTensor (A.SStage j))
        ((1 : A.SStage j) ⊗ₜ[A.SStage i] ξ k)) =
      LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
        ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
          A.SStage i →ₗ[A.RStage i] A.SStage j)
        ((1 : A.SStage i) ⊗ₜ[A.RStage i] (ξ k).1) := by
  let _ : Algebra (A.RStage i) (A.SStage i) :=
    (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) :=
    (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) := inferInstance
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) := inferInstance
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := inferInstance
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    inferInstance
  -- Proof comment: simplify the tensorized subtype on the pure generator and then cancel the
  -- later-stage base change using the generic `1 ⊗ z` computation.
  simpa [tail_target_algHom_toRingHom] using
    cancelBaseChange_one_tmul_eq_rTensor_restrictScalars
      (A := A.RStage i) (B := A.SStage i) (S := A.SStage j)
      (N := I ⊗[A.RStage i] A.moduleStage i)
      ((1 : A.SStage i) ⊗ₜ[A.RStage i] (ξ k).1)

/-- Helper for Lemma 10.128.3: commuting the source ideal factor past the later-stage
base change identifies `I ⊗[A.RStage i] (A.SStage j ⊗[A.SStage i] A.moduleStage i)` with the
later-stage tensor owner `A.SStage j ⊗[A.SStage i] (I ⊗[A.RStage i] A.moduleStage i)`. -/
noncomputable def sourceIdealTensorDomainEquiv
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i)) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := (source_stage_to_later_target_hom A i j hij).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
      sourceStageToLaterTarget_isScalarTower (A := A) (i := i) (j := j) hij
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
    let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
    I ⊗[A.RStage i] Mj' ≃ₗ[A.SStage j]
      A.SStage j ⊗[A.SStage i] (I ⊗[A.RStage i] A.moduleStage i) :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) := (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
    sourceStageToLaterTarget_isScalarTower (A := A) (i := i) (j := j) hij
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
  let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
  ((TensorProduct.comm (A.RStage i) I Mj').toAddEquiv.linearEquiv (A.SStage j)).trans
    ((TensorProduct.AlgebraTensorModule.assoc
        (A.RStage i) (A.SStage i) (A.SStage j)
        (A.SStage j) (A.moduleStage i) I).trans
      (LinearEquiv.lTensor (A.SStage j)
        ((TensorProduct.comm (A.RStage i) (A.moduleStage i) I).toAddEquiv.linearEquiv
          (A.SStage i))))

/-- Helper for Lemma 10.128.3: after rewriting the source ideal tensor owner by the
canonical commutativity/associativity equivalence, the later-stage tensor of the raw stage
multiplication becomes the ordinary source multiplication on
`I ⊗[A.RStage i] (A.SStage j ⊗[A.SStage i] A.moduleStage i)`. -/
lemma tensorizedRawStageMultiplication_eq_sourceTensorToModule
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i)) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := (source_stage_to_later_target_hom A i j hij).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
      sourceStageToLaterTarget_isScalarTower (A := A) (i := i) (j := j) hij
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
    let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
    let _ : Module (A.RStage i) Mj' := Module.compHom Mj' (source_stage_to_later_target_hom A i j hij)
    LinearMap.restrictScalars (A.RStage i)
        (((raw_stage_multiplication A i I).lTensor (A.SStage j)) ∘ₗ
          (sourceIdealTensorDomainEquiv (A := A) (i := i) (j := j) hij I).toLinearMap) =
      TensorProduct.lift ((LinearMap.lsmul (A.RStage i) Mj').comp I.subtype) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) := (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
    sourceStageToLaterTarget_isScalarTower (A := A) (i := i) (j := j) hij
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
  let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
  let _ : Module (A.RStage i) Mj' := Module.compHom Mj' (source_stage_to_later_target_hom A i j hij)
  let eDom := sourceIdealTensorDomainEquiv (A := A) (i := i) (j := j) hij I
  -- Proof comment: compare both `A.SStage j`-linear maps on pure tensors `a ⊗ (s ⊗ m)`, where
  -- the commutativity/associativity transport sends them to the same literal tensor formula.
  apply TensorProduct.ext'
  intro a x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp [eDom, sourceIdealTensorDomainEquiv]
  | tmul s m =>
      simp [eDom, sourceIdealTensorDomainEquiv, raw_stage_multiplication_tmul, Algebra.smul_def]
  | add x y hx hy =>
      simp [hx, hy, eDom, sourceIdealTensorDomainEquiv]

/-- Helper for the eventual-flatness lemma: evaluating the tensorized raw multiplication comparison on
an element of the source ideal tensor owner recovers the textbook source multiplication owner. -/
lemma tensorizedRawStageMultiplication_apply_sourceIdealTensorDomainEquiv
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    (x : I ⊗[A.RStage i] (A.SStage j ⊗[A.SStage i] A.moduleStage i)) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := (source_stage_to_later_target_hom A i j hij).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
      sourceStageToLaterTarget_isScalarTower (A := A) (i := i) (j := j) hij
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
    LinearMap.restrictScalars (A.RStage i)
        ((raw_stage_multiplication A i I).lTensor (A.SStage j))
        ((sourceIdealTensorDomainEquiv (A := A) (i := i) (j := j) hij I) x) =
      TensorProduct.lift
        ((LinearMap.lsmul (A.RStage i) (A.SStage j ⊗[A.SStage i] A.moduleStage i)).comp I.subtype) x := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) := (source_stage_to_later_target_hom A i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
    sourceStageToLaterTarget_isScalarTower (A := A) (i := i) (j := j) hij
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
  -- Proof comment: the owner equality is already proved at the level of linear maps, so this
  -- lemma just evaluates it once and packages the result for later injectivity arguments.
  simpa [LinearMap.comp_apply] using congrArg
    (fun f ↦ f x)
    (tensorizedRawStageMultiplication_eq_sourceTensorToModule
      (A := A) (i := i) (j := j) hij I)

/-- Helper for the eventual-flatness lemma: the prime defining the later localization transition lies
over the maximal ideal of the later source stage `A.RStage j`. -/
lemma laterTransitionPrime_comap_eq_maximalIdeal
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (q : Ideal (A.targetStageBaseChange hij)) [q.IsPrime]
    (hqLoc : q.primeCompl.IsLocalizationMap (A.stageBaseChangeMap hij)) :
    Ideal.comap (algebraMap (A.RStage j) (A.targetStageBaseChange hij)) q =
      IsLocalRing.maximalIdeal (A.RStage j) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j hij).toAlgebra
  let _ : Algebra (A.targetStageBaseChange hij) (A.SStage j) := (A.stageBaseChangeMap hij).toAlgebra
  letI : IsLocalization q.primeCompl (A.SStage j) := hqLoc.2
  have hstageComp :
      (A.stageBaseChangeMap hij).comp
          (algebraMap (A.RStage j) (A.targetStageBaseChange hij)) =
        A.stageMap j := by
    ext r
    -- Proof comment: the right tensor-factor algebra map is the pure tensor `1 ⊗ r`, and the
    -- transition base-change map sends that pure tensor to the later stage map.
    simpa using
      (DirectedLocalHomApproximation.stageBaseChangeMap_tmul'
        (A' := A.toDirectedLocalHomApproximation) (h := hij) (s := (1 : A.SStage i)) (r := r))
  letI :
      IsLocalHom
        ((A.stageBaseChangeMap hij).comp
          (algebraMap (A.RStage j) (A.targetStageBaseChange hij))) := by
    simpa [hstageComp] using (show IsLocalHom (A.stageMap j) from inferInstance)
  have hcomap :=
    comap_comap_maximalIdeal_of_local_comparison
      (A := A.RStage j) (B := A.targetStageBaseChange hij) (T := A.SStage j)
      (σ := A.stageBaseChangeMap hij)
  -- Proof comment: replace the contracted maximal ideal of the localization target by the chosen
  -- prime `q`, using the prime-localization witness from the approximation transition.
  simpa [IsLocalization.AtPrime.comap_maximalIdeal (S := A.SStage j) (I := q)] using hcomap

/-- Helper for Lemma 10.128.3: once a finite spanning family of the raw kernel has zero descended
owner images at a later stage, the local flatness criterion can be applied at that later stage. -/
lemma later_mapped_maximalIdeal_ne_top
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    [IsLocalHom (A.map i j hij)]
    (hI : I = IsLocalRing.maximalIdeal (A.RStage i)) :
    Ideal.map (A.map i j hij) I ≠ ⊤ := by
  obtain ⟨q, hqPrime, hqLoc⟩ := A.hasPrimeLocalizationTransitions hij
  letI : q.IsPrime := hqPrime
  have hqcomap :
      Ideal.comap (algebraMap (A.RStage j) (A.targetStageBaseChange hij)) q =
        IsLocalRing.maximalIdeal (A.RStage j) :=
    laterTransitionPrime_comap_eq_maximalIdeal
      (A := A) (i := i) (j := j) hij q hqLoc
  have hsourceComap :
      Ideal.comap (A.map i j hij)
          (Ideal.comap (algebraMap (A.RStage j) (A.targetStageBaseChange hij)) q) = I := by
    -- Proof comment: contract `q` first to the later source stage and then further along the local
    -- transition map `A.map i j hij`; the two comaps collapse to the source maximal ideal.
    rw [hqcomap, hI]
    simpa using (IsLocalRing.maximalIdeal_comap (A.map i j hij))
  have hmap_le_max :
      Ideal.map (A.map i j hij) I ≤ IsLocalRing.maximalIdeal (A.RStage j) := by
    -- Proof comment: convert the source-stage contraction equality into the desired mapped-ideal
    -- containment by `Ideal.map_le_iff_le_comap`, then rewrite the later contraction of `q`.
    refine (Ideal.map_le_iff_le_comap).2 ?_
    rw [← hqcomap]
    simpa [Ideal.comap_comap] using hsourceComap
  -- Proof comment: any ideal contained in the later maximal ideal is proper, so its map cannot be
  -- the top ideal.
  exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (A.RStage j)).ne_top hmap_le_max

/-- Helper for Lemma 10.128.3: if the descended owner images of a spanning family vanish at a
later stage, then the later quotient `Tor₁` owner used by the local flatness criterion is zero. -/
lemma later_tor_one_quotient_isZero_of_zero_generator_images
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    {n : ℕ} (ξ : Fin n → raw_stage_kernel A i I)
    (hξspan : Submodule.span (A.SStage i) (Set.range ξ) = ⊤)
    (hξ_owner_zero :
      let _ : Algebra (A.RStage i) (A.SStage i) :=
        (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) :=
      (source_stage_to_later_target_hom A i j hij).toAlgebra
    ∀ k,
        LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
          ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
            A.SStage i →ₗ[A.RStage i] A.SStage j)
          ((1 : A.SStage i) ⊗ₜ[A.RStage i] (ξ k).1) = 0) :
    let Ij : Ideal (A.RStage j) := Ideal.map (A.map i j hij) I
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
    let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
    let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
    let _ : Module (A.RStage j) Mj' := inferInstance
    CategoryTheory.Limits.IsZero
      ((((CategoryTheory.Tor (ModuleCat.{max uR uS uM} (A.RStage j)) 1).obj
          (ModuleCat.of (R := A.RStage j) Mj')).obj
        (ModuleCat.of (R := A.RStage j) ((A.RStage j) ⧸ Ij)))) := by
  let Ij : Ideal (A.RStage j) := Ideal.map (A.map i j hij) I
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
  let _ : Module (A.RStage j) Mj' := inferInstance
  obtain ⟨q, hqPrime, hqLoc⟩ := A.hasPrimeLocalizationTransitions hij
  letI : q.IsPrime := hqPrime
  letI : IsLocalization q.primeCompl (A.SStage j) := hqLoc.2
  have hSubtypeZeroOnGenerators :
      ∀ k,
        (((raw_stage_kernel A i I).subtype).lTensor (A.SStage j))
          ((1 : A.SStage j) ⊗ₜ[A.SStage i] ξ k) = 0 := by
    intro k
    -- Proof comment: cancel the later-stage base change once so the hypothesis `hξ_owner_zero`
    -- can be consumed without repeated transport rewriting.
    apply
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        (A.RStage i) (A.SStage i) (A.SStage j) (A.SStage j)
        (I ⊗[A.RStage i] A.moduleStage i)).injective
    calc
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        (A.RStage i) (A.SStage i) (A.SStage j) (A.SStage j)
        (I ⊗[A.RStage i] A.moduleStage i))
        ((((raw_stage_kernel A i I).subtype).lTensor (A.SStage j))
          ((1 : A.SStage j) ⊗ₜ[A.SStage i] ξ k))
          =
        LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
          ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
            A.SStage i →ₗ[A.RStage i] A.SStage j)
          ((1 : A.SStage i) ⊗ₜ[A.RStage i] (ξ k).1) := by
            simpa using
              tensorizedRawKernelSubtype_generator_eq_owner
                (A := A) (i := i) (j := j) hij I ξ k
      _ = 0 := hξ_owner_zero k
  have hSubtypeZero :
      ((raw_stage_kernel A i I).subtype).lTensor (A.SStage j) = 0 := by
    -- Proof comment: the later-stage pure tensors `1 ⊗ ξ k` still span the whole tensorized raw
    -- kernel, so vanishing on that family forces the full tensorized subtype map to vanish.
    exact
      linearMap_eq_zero_of_span_range_eq_top
        (ξ := fun k : Fin n ↦ (1 : A.SStage j) ⊗ₜ[A.SStage i] ξ k)
        (laterRawKernelGenerators_span_top
          (A := A) (i := i) (j := j) hij I ξ hξspan)
        (((raw_stage_kernel A i I).subtype).lTensor (A.SStage j))
        hSubtypeZeroOnGenerators
  have hExact :
      Function.Exact
        (((raw_stage_kernel A i I).subtype).lTensor (A.SStage j))
        ((raw_stage_multiplication A i I).lTensor (A.SStage j)) := by
    -- Proof comment: localization flatness of the later target stage preserves the exact kernel
    -- presentation of the raw multiplication map after tensoring.
    exact Module.Flat.rTensor_exact (A.SStage j)
      (LinearMap.exact_subtype_ker_map (raw_stage_multiplication A i I))
  have hkerTensor :
      LinearMap.ker ((raw_stage_multiplication A i I).lTensor (A.SStage j)) = ⊥ := by
    -- Proof comment: exactness identifies the later kernel with the range of the tensorized
    -- subtype, and the previous step already killed that map entirely.
    rw [Function.Exact.linearMap_ker_eq hExact, hSubtypeZero]
    simp
  have hTensorInjective :
      Function.Injective ((raw_stage_multiplication A i I).lTensor (A.SStage j)) :=
    LinearMap.ker_eq_bot.mp hkerTensor
  have hSourceInjective :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul (A.RStage i) Mj').comp I.subtype)) := by
    intro x y hxy
    -- Proof comment: move the source ideal tensor owner to the raw later-stage tensor model,
    -- where injectivity is already available from `hTensorInjective`.
    apply (sourceIdealTensorDomainEquiv (A := A) (i := i) (j := j) hij I).injective
    have hx :=
      tensorizedRawStageMultiplication_apply_sourceIdealTensorDomainEquiv
        (A := A) (i := i) (j := j) hij I x
    have hy :=
      tensorizedRawStageMultiplication_apply_sourceIdealTensorDomainEquiv
        (A := A) (i := i) (j := j) hij I y
    apply hTensorInjective
    exact hx.trans (hxy.trans hy.symm)
  have hMappedInjective :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul (A.RStage j) Mj').comp Ij.subtype)) := by
    -- Proof comment: transport source injectivity from `I` to its mapped ideal `Ij` at the later
    -- source stage.
    simpa [Ij] using
      mapped_ideal_tensor_to_module_injective_of_source_injective
        (A := A.RStage i) (B := A.RStage j) (I := I) (N := Mj') hSourceInjective
  have hkerMapped :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul (A.RStage j) Mj').comp Ij.subtype)) = ⊥ := by
    exact LinearMap.ker_eq_bot.2 hMappedInjective
  -- Proof comment: Remark `10.75.9` identifies the later quotient `Tor₁` owner with this zero
  -- kernel of the mapped ideal multiplication map. Use the dedicated same-universe wrapper here
  -- so the main closing lemma does not have to re-elaborate the full Tor owner inline.
  simpa [Ij, Mj'] using
    tor_one_module_quotient_vanishes_of_ker_eq_bot
      (A := A.RStage j) (I := Ij) (N := Mj') hkerMapped

/-- Helper for Lemma 10.128.3: a zero kernel for the ideal tensor multiplication map
gives the corresponding module-first quotient `Tor₁` vanishing in the same universe. -/
lemma ideal_tensor_lsmul_tor_vanishes_of_ker_eq_bot
    {A : Type uR} [CommRing A] (I : Ideal A)
    {N : Type uR} [AddCommGroup N] [Module A N]
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)) = ⊥) :
    CategoryTheory.Limits.IsZero
      ((((CategoryTheory.Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
      (ModuleCat.of A (A ⧸ I)))) := by
  -- Proof comment: this packages Remark `10.75.9` and the standard zero-kernel criterion into
  -- the exact homological owner used by the later local flatness criterion.
  exact tor_one_module_quotient_vanishes_of_ker_eq_bot (A := A) (I := I) (N := N) hker

/-- Helper for Lemma 10.128.3: vanishing of the later quotient `Tor₁` owner supplies the
final input for the local flatness criterion at stage `j`. -/
lemma later_stage_flat_of_later_tor_one_quotient_isZero
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    (hI : I = IsLocalRing.maximalIdeal (A.RStage i))
    (hTor :
      let Ij : Ideal (A.RStage j) := Ideal.map (A.map i j hij) I
      let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
      let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
      let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
      let _ : Module (A.RStage j) Mj' := inferInstance
      CategoryTheory.Limits.IsZero
        ((((CategoryTheory.Tor (ModuleCat.{max uR uS uM} (A.RStage j)) 1).obj
            (ModuleCat.of (R := A.RStage j) Mj')).obj
          (ModuleCat.of (R := A.RStage j) ((A.RStage j) ⧸ Ij))))) :
    Module.Flat (A.RStage j) (A.moduleStage j) := by
  let Ij : Ideal (A.RStage j) := Ideal.map (A.map i j hij) I
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  let _ : Algebra (A.targetStageBaseChange hij) (A.SStage j) :=
    (A.stageBaseChangeMap hij).toAlgebra
  let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
  let _ : Module (A.RStage j) Mj' := inferInstance
  obtain ⟨q, hqPrime, hqLoc⟩ := A.hasPrimeLocalizationTransitions hij
  letI : q.IsPrime := hqPrime
  letI : IsLocalization q.primeCompl (A.SStage j) := hqLoc.2
  have hIj_ne_top : Ij ≠ ⊤ := by
    -- Proof comment: once the source ideal is the maximal ideal, its image at the later source
    -- stage must stay proper for the local flatness criterion.
    simpa [Ij] using
      later_mapped_maximalIdeal_ne_top
        (A := A) (i := i) (j := j) hij I hI
  have hflatMj' : Module.Flat (A.RStage j) Mj' := by
    -- Proof comment: apply the imported local flatness criterion to the approximation square at
    -- the later stage, using the already-proved quotient-flatness and Tor-vanishing inputs.
    simpa [Ij, Mj'] using
      flat_tensorProduct_of_flat_mod_ideal_and_tor_one_quotient_vanishing_of_isLocalization_tensorProduct
        I hIj_ne_top
        (stage_quotient_flat_over_residueField (A := A) i) hTor
  -- Proof comment: the canonical transition base-change equivalence identifies the flat
  -- base-changed module owner with the actual later stage module.
  exact Module.Flat.of_linearEquiv (A.transitionBaseChange hij).symm

/-- Helper for Lemma 10.128.3: once a finite spanning family of the raw kernel has zero descended
owner images at a later stage, the local flatness criterion can be applied at that later stage. -/
lemma later_stage_flat_of_zero_raw_generators
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j)
    (I : Ideal (A.RStage i))
    {n : ℕ} (ξ : Fin n → raw_stage_kernel A i I)
    (hξspan : Submodule.span (A.SStage i) (Set.range ξ) = ⊤)
    (hξ_owner_zero :
      let _ : Algebra (A.RStage i) (A.SStage i) :=
        (source_stage_to_later_target_hom A i i le_rfl).toAlgebra
      let _ : Algebra (A.RStage i) (A.SStage j) :=
        (source_stage_to_later_target_hom A i j hij).toAlgebra
      ∀ k,
        LinearMap.rTensor (I ⊗[A.RStage i] A.moduleStage i)
          ((tail_target_algHom A i ⟨i, le_rfl⟩ ⟨j, hij⟩ hij).toLinearMap :
            A.SStage i →ₗ[A.RStage i] A.SStage j)
          ((1 : A.SStage i) ⊗ₜ[A.RStage i] (ξ k).1) = 0)
    (hI : I = IsLocalRing.maximalIdeal (A.RStage i)) :
    Module.Flat (A.RStage j) (A.moduleStage j) := by
  -- Proof comment: this is the remaining exactness-and-local-criterion step from the source
  -- proof. First transport the descended owner zeroes to the textbook later raw tensor model,
  -- then kill the later raw multiplication kernel using the spanning family, and finally invoke
  -- Remark `10.75.9` together with Lemma `10.99.14`.
  let Ij : Ideal (A.RStage j) := Ideal.map (A.map i j hij) I
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j hij).toAlgebra
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.targetMap i j hij).toAlgebra
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  let _ : Algebra (A.targetStageBaseChange hij) (A.SStage j) :=
    (A.stageBaseChangeMap hij).toAlgebra
  let Mj' : Type _ := A.SStage j ⊗[A.SStage i] A.moduleStage i
  let _ : Module (A.RStage j) Mj' := inferInstance
  have hTor :
      CategoryTheory.Limits.IsZero
        ((((CategoryTheory.Tor (ModuleCat.{max uR uS uM} (A.RStage j)) 1).obj
            (ModuleCat.of (R := A.RStage j) Mj')).obj
          (ModuleCat.of (R := A.RStage j) ((A.RStage j) ⧸ Ij)))) := by
    -- Proof comment: the source proof only needs later quotient `Tor₁`-vanishing, so normalize
    -- the descended generator data directly to that owner.
    simpa [Ij, Mj'] using
      later_tor_one_quotient_isZero_of_zero_generator_images
        (A := A) (i := i) (j := j) hij I ξ hξspan hξ_owner_zero
  -- Proof comment: once the later quotient `Tor₁` owner is zero, the imported local criterion
  -- applies directly to the named mapped ideal and base-changed module.
  exact later_stage_flat_of_later_tor_one_quotient_isZero
    (A := A) (i := i) (j := j) hij I hI hTor

/-! `Chap10 Lemma 10 128 3` source-facing entry. -/
/-- Chap10 Lemma 10 128 3

Stacks tag `00R6` (`lemma-colimit-eventually-flat`).

Let `R → S`, `M`, `Λ`, `R_λ → S_λ`, and `M_λ` be as in Lemma `10.127.13`.
Assume that `M` is flat over `R`. Then for some `λ ∈ Λ` the module `M_λ`
is flat over `R_λ`. This is the main source-facing declaration. -/
@[stacks 00R6]
theorem exists_flat_stage_of_flat
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ i : A.Λ, Module.Flat (A.RStage i) (A.moduleStage i) := sorry

end DirectedLocalEssFinitePresentationModuleApproximation

end
