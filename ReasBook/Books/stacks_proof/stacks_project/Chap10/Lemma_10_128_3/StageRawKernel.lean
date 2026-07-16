import stacks_proof.stacks_project.Chap10.Lemma_10_127_13.TailApproximation
import stacks_proof.stacks_project.Chap10.Lemma_10_127_5
import stacks_proof.stacks_project.Chap10.Remark_10_75_9
import stacks_proof.stacks_project.Chap10.Lemma_10_99_14
import stacks_proof.stacks_project.Chap10.Lemma_10_100_2
import Mathlib.Tactic.StacksAttribute

universe uR uS uM

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable {f : R →+* S} [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

namespace DirectedLocalEssFinitePresentationModuleApproximation

/-- Helper for Lemma 10.128.3: each source stage ring in the approximation is Noetherian. -/
lemma stage_source_isNoetherianRing
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    IsNoetherianRing (A.RStage i) := by
  have hess : Algebra.EssFiniteType ℤ (A.RStage i) :=
    (RingHom.essFiniteType_algebraMap).1 (A.source_essFiniteType i)
  letI : Algebra.EssFiniteType ℤ (A.RStage i) := hess
  -- Proof comment: the source stage is essentially of finite type over `ℤ`, so it is
  -- Noetherian by the standard localization-stability theorem.
  exact Algebra.EssFiniteType.isNoetherianRing ℤ (A.RStage i)

/-- Helper for Lemma 10.128.3: each target stage ring in the approximation is Noetherian. -/
lemma stage_target_isNoetherianRing
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    IsNoetherianRing (A.SStage i) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  letI : IsNoetherianRing (A.RStage i) := stage_source_isNoetherianRing A i
  have hess : Algebra.EssFiniteType (A.RStage i) (A.SStage i) := by
    exact (RingHom.essFiniteType_algebraMap).1 (by simpa [RingHom.algebraMap_toAlgebra] using A.target_essFiniteType i)
  letI : Algebra.EssFiniteType (A.RStage i) (A.SStage i) := hess
  -- Proof comment: each target stage is essentially of finite type over the already-Noetherian
  -- source stage, so it is Noetherian as well.
  exact Algebra.EssFiniteType.isNoetherianRing (A.RStage i) (A.SStage i)

/-- Helper for Lemma 10.128.3: the maximal ideal of a source stage is finitely generated. -/
lemma stage_maximalIdeal_fg
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    (IsLocalRing.maximalIdeal (A.RStage i)).FG := by
  letI : IsNoetherianRing (A.RStage i) := stage_source_isNoetherianRing A i
  -- Proof comment: ideals in a Noetherian ring are finitely generated.
  exact Ideal.fg_of_isNoetherianRing _

/-- Helper for Lemma 10.128.3: the source-stage scalar action on a stage module factors through
the target-stage scalar action. -/
lemma stage_module_isScalarTower
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  -- Proof comment: the `A.RStage i`-action on `A.moduleStage i` is defined by restricting scalars
  -- along `A.stageMap i`, so associativity of scalar multiplication is exactly `mul_smul`.
  refine ⟨?_⟩
  intro r s m
  change ((A.stageMap i r) * s) • m = (A.stageMap i r) • (s • m)
  rw [mul_smul]

/-- Helper for Lemma 10.128.3: the source and target stage scalar actions commute on a stage
module. -/
lemma stage_module_smulCommClass
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  -- Proof comment: rewrite the restricted `A.RStage i`-action as multiplication by
  -- `A.stageMap i r` on the `A.SStage i`-module and commute the two scalars in the ring
  -- `A.SStage i`.
  refine ⟨?_⟩
  intro r s m
  -- Proof comment: after unfolding the restricted `R_i`-action on both occurrences, both sides
  -- are scalar towers over `S_i`, so `smul_smul` reduces the goal to `mul_comm`.
  have hcomm : (A.stageMap i r) • (s • m) = s • ((A.stageMap i r) • m) := by
    rw [smul_smul, smul_smul, mul_comm]
  simpa using hcomm

/-- Helper for Lemma 10.128.3: the tensor of the stage maximal ideal with the stage module is
finite over the stage target ring. -/
lemma stage_ideal_tensor_finite
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    Module.Finite (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := by
  let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  let _ : Module.Finite (A.RStage i) I := Module.Finite.of_fg (stage_maximalIdeal_fg A i)
  let _ : Module.Finite (A.SStage i) ((A.SStage i ⊗[A.RStage i] I) ⊗[A.SStage i] A.moduleStage i) :=
    by infer_instance
  let eComm :
      (I ⊗[A.RStage i] A.moduleStage i) ≃ₗ[A.SStage i]
        (A.moduleStage i ⊗[A.RStage i] I) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.linearEquiv (A.SStage i)
  let e :
      ((A.SStage i ⊗[A.RStage i] I) ⊗[A.SStage i] A.moduleStage i) ≃ₗ[A.SStage i]
        (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.SStage i) (A.moduleStage i) (A.SStage i ⊗[A.RStage i] I)).symm.trans <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        (A.RStage i) (A.SStage i) (A.SStage i) (A.moduleStage i) I).trans
        eComm.symm
  -- Proof comment: this is the same `comm + cancelBaseChange` comparison used in
  -- Lemma `10.99.7`, now applied stagewise to move finiteness from the obvious base-changed
  -- tensor to the textbook tensor `I ⊗[R_i] M_i`.
  simpa [I] using
    (Module.Finite.equiv e : Module.Finite (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i))

/-- Helper for Lemma 10.128.3: the stage Tor-kernel is finite over the target stage ring once the
canonical multiplication map is viewed as `S_i`-linear. -/
lemma stage_kernel_finite
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    ∃ μi : I ⊗[A.RStage i] A.moduleStage i →ₗ[A.SStage i] A.moduleStage i,
      Module.Finite (A.SStage i) (LinearMap.ker μi) := by
  let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  let μright : A.moduleStage i ⊗[A.RStage i] I →ₗ[A.SStage i] A.moduleStage i :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun m =>
          { toFun := fun x => x.1 • m
            map_add' := by
              intro x y
              exact add_smul x.1 y.1 m
            map_smul' := by
              intro r x
              change ((r • x : I).1 • m = r • (x.1 • m))
              simp [mul_smul] }
        map_add' := by
          intro m n
          ext x
          exact smul_add x.1 m n
        map_smul' := by
          intro s m
          ext x
          -- Proof comment: this is the scalar-commutation input needed to make the multiplication
          -- map linear over `S_i`.
          simpa using (smul_comm x.1 s m) }
  let eComm :
      (I ⊗[A.RStage i] A.moduleStage i) ≃ₗ[A.SStage i]
        (A.moduleStage i ⊗[A.RStage i] I) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.linearEquiv (A.SStage i)
  let μi : I ⊗[A.RStage i] A.moduleStage i →ₗ[A.SStage i] A.moduleStage i :=
    μright.comp eComm.toLinearMap
  let _ : Module.Finite (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    stage_ideal_tensor_finite A i
  let _ : IsNoetherianRing (A.SStage i) := stage_target_isNoetherianRing A i
  let _ : IsNoetherian (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := inferInstance
  let _ : IsNoetherian (A.SStage i) (LinearMap.ker μi) :=
    isNoetherian_of_submodule_of_noetherian
      (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) (LinearMap.ker μi) inferInstance
  -- Proof comment: once the stage multiplication map is promoted to an `S_i`-linear map, its
  -- kernel is just a submodule of a finite module over the Noetherian ring `S_i`.
  exact ⟨μi, Module.IsNoetherian.finite (A.SStage i) (LinearMap.ker μi)⟩

/-- Helper for Lemma 10.128.3: the quotient of a stage module by the maximal-ideal multiple is
flat over the residue field of that stage. -/
lemma stage_quotient_flat_over_residueField
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
    Module.Flat ((A.RStage i) ⧸ I)
      (A.moduleStage i ⧸ (I • (⊤ : Submodule (A.RStage i) (A.moduleStage i)))) := by
  let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
  letI : Field ((A.RStage i) ⧸ I) := Ideal.Quotient.field I
  letI : Module.Free ((A.RStage i) ⧸ I)
      (A.moduleStage i ⧸ (I • (⊤ : Submodule (A.RStage i) (A.moduleStage i)))) :=
    Module.Free.of_divisionRing _ _
  -- Proof comment: over the residue field, every module is free, hence flat.
  exact Module.Flat.of_free

/-- Helper for Lemma 10.128.3: the canonical source-stage map into the limit ring `R`. -/
noncomputable def source_stage_to_limit_hom
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    A.RStage i →+* R :=
  Ring.DirectLimit.toLimitHom A.RStage (fun i j h ↦ A.map i j h) A.colimitIso i

/-- Helper for Lemma 10.128.3: the source-stage action on the limit module `M` factors through the
target-stage map to `S`. -/
noncomputable def source_stage_to_target_limit_hom
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    A.RStage i →+* S :=
  (DirectedLocalHomApproximation.targetStageToLimitHom A.toDirectedLocalHomApproximation i).comp
    (A.stageMap i)

/-- Helper for Lemma 10.128.3: evaluating the colimit square on one source-stage element identifies
the two source-stage maps to the ambient target ring `S`. -/
lemma source_stage_to_target_limit_eq
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    source_stage_to_target_limit_hom A i = f.comp (source_stage_to_limit_hom A i) := by
  ext x
  -- Proof comment: specialize the approximation colimit square to the chosen source-stage
  -- generator.
  have hcolimit := congrArg
    (fun g : Ring.DirectLimit A.RStage (fun i j h ↦ A.map i j h) →+* S ↦
      g (Ring.DirectLimit.of A.RStage (fun i j h ↦ A.map i j h) i x))
    A.colimit_comm
  simpa [source_stage_to_target_limit_hom, source_stage_to_limit_hom,
    DirectedLocalHomApproximation.targetStageToLimitHom, Ring.DirectLimit.toLimitHom,
    RingHom.comp_apply, Ring.DirectLimit.map_apply_of] using hcolimit

/-- Helper for Lemma 10.128.3: the source-stage map to the later target stage is the transition on
the target side after the original stage map. -/
noncomputable def source_stage_to_later_target_hom
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j) :
    A.RStage i →+* A.SStage j :=
  (A.targetMap i j hij).comp (A.stageMap i)

/-- Helper for Lemma 10.128.3: the two obvious source-stage maps into the later target stage
coincide by the approximation compatibility square. -/
lemma source_stage_to_later_target_eq
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i j : A.Λ) (hij : i ≤ j) :
    source_stage_to_later_target_hom A i j hij = (A.stageMap j).comp (A.map i j hij) := by
  -- Proof comment: this is exactly the directed-system compatibility of the approximation.
  simpa [source_stage_to_later_target_hom] using (A.comm hij).symm

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Chap10 Lemma 10 128 3: at the initial tail stage, the source-to-later target map
is the original stage map. -/
lemma source_stage_to_later_target_hom_self
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    source_stage_to_later_target_hom A i i le_rfl = A.stageMap i := by
  -- Proof comment: unfold the source-to-tail map and use the target directed system's identity
  -- transition at stage `i`.
  ext r
  change A.targetMap i i le_rfl ((A.stageMap i) r) = (A.stageMap i) r
  simpa using
    (DirectedSystem.map_self (f := fun a b h ↦ A.targetMap a b h) ((A.stageMap i) r))

/-- Helper for Lemma 10.128.3: on the tail above `i`, each target transition is automatically
linear over the fixed source stage `R_i`. -/
lemma tail_target_algHom_commutes
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (j k : Set.Ici i) (hjk : j ≤ k) (r : A.RStage i) :
    A.targetMap j.1 k.1 hjk ((source_stage_to_later_target_hom A i j.1 j.2) r) =
      (source_stage_to_later_target_hom A i k.1 k.2) r := by
  -- Proof comment: both ways of sending `r` into the later target stage are the same composite
  -- along the directed target system.
  change
    A.targetMap j.1 k.1 hjk (A.targetMap i j.1 j.2 (A.stageMap i r)) =
      A.targetMap i k.1 k.2 (A.stageMap i r)
  simpa using
    (DirectedSystem.map_map
      (f := fun a b h ↦ A.targetMap a b h) j.2 hjk (A.stageMap i r))

/-- Helper for Lemma 10.128.3: on the tail above `i`, each target transition is automatically
linear over the fixed source stage `R_i`. -/
noncomputable def tail_target_algHom
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (j k : Set.Ici i) (hjk : j ≤ k) :
    let _ : Algebra (A.RStage i) (A.SStage j.1) :=
      (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage k.1) :=
      (source_stage_to_later_target_hom A i k.1 k.2).toAlgebra
    A.SStage j.1 →ₐ[A.RStage i] A.SStage k.1 :=
  let _ : Algebra (A.RStage i) (A.SStage j.1) :=
    (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage k.1) :=
    (source_stage_to_later_target_hom A i k.1 k.2).toAlgebra
  { toRingHom := A.targetMap j.1 k.1 hjk
    commutes' := tail_target_algHom_commutes A i j k hjk }

/-- Helper for Chap10 Lemma 10 128 3: the tail target algebra hom has the original target
transition as its underlying ring hom. -/
lemma tail_target_algHom_toRingHom
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (j k : Set.Ici i) (hjk : j ≤ k) :
    (tail_target_algHom A i j k hjk : A.SStage j.1 →+* A.SStage k.1) =
      A.targetMap j.1 k.1 hjk := by
  -- Proof comment: `tail_target_algHom` only packages the target transition with its
  -- source-stage linearity proof; the ring-hom component is unchanged.
  rfl

/-- Helper for Lemma 10.128.3: the tail target algebra maps form a directed system over the fixed
base stage `R_i`. -/
instance tail_target_directedSystem
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) :
    let _ : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
      fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
    DirectedSystem
      (fun j : Set.Ici i ↦ A.SStage j.1)
      (fun j k h ↦ (tail_target_algHom A i j k h : A.SStage j.1 →+* A.SStage k.1)) := by
  letI : ∀ j : Set.Ici i, Algebra (A.RStage i) (A.SStage j.1) :=
    fun j ↦ (source_stage_to_later_target_hom A i j.1 j.2).toAlgebra
  -- Proof comment: after unfolding `tail_target_algHom`, this is exactly the tail directed system
  -- already carried by the approximation's target rings.
  change DirectedSystem
    (fun j : Set.Ici i ↦ A.SStage j.1)
    (fun j k h ↦ A.targetMap j.1 k.1 h)
  infer_instance

/-- Helper for Lemma 10.128.3: for a fixed stage element `m`, multiplication by the ideal factor
is `R_i`-linear in the ideal variable. -/
lemma raw_stage_right_factor_map_add
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (m n : A.moduleStage i) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    (fun x : I ↦ x.1 • (m + n)) = fun x : I ↦ x.1 • m + x.1 • n := by
  -- Proof comment: scalar multiplication distributes over the stage-module sum.
  ext x
  exact smul_add x.1 m n

/-- Helper for Lemma 10.128.3: the fixed-element multiplication map `I → M_i` is `R_i`-linear. -/
lemma raw_stage_right_factor_map_smul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (m : A.moduleStage i) (r : A.RStage i) (x : I) :
    ((r • x : I).1) • m = r • (x.1 • m) := by
  -- Proof comment: the `R_i`-action on `M_i` is the restricted action through `A.stageMap i`.
  change ((r * x.1) • m = r • (x.1 • m))
  simp [mul_smul]

/-- Helper for Lemma 10.128.3: the ideal factor acts linearly on a fixed stage element. -/
noncomputable def raw_stage_right_factor_map
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (m : A.moduleStage i) :
    I →ₗ[A.RStage i] A.moduleStage i :=
  { toFun := fun x ↦ x.1 • m
    map_add' := fun x y ↦ by
      -- Proof comment: additivity is literal additivity of the scalar action.
      exact add_smul x.1 y.1 m
    map_smul' := raw_stage_right_factor_map_smul (A := A) (i := i) (I := I) m }

/-- Helper for Lemma 10.128.3: the family of fixed-element multiplication maps is additive in the
stage-module variable. -/
lemma raw_stage_right_factor_map_map_add
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (m n : A.moduleStage i) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    raw_stage_right_factor_map A i I (m + n) =
      raw_stage_right_factor_map A i I m + raw_stage_right_factor_map A i I n := by
  -- Proof comment: extensionality reduces the equality of linear maps to `smul_add`.
  ext x
  exact smul_add x.1 m n

/-- Helper for Lemma 10.128.3: the family of fixed-element multiplication maps is `S_i`-linear in
the stage-module variable. -/
lemma raw_stage_right_factor_map_map_smul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (s : A.SStage i) (m : A.moduleStage i) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    raw_stage_right_factor_map A i I (s • m) =
      s • raw_stage_right_factor_map A i I m := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  -- Proof comment: commuting the `R_i`-scalar from the ideal with the `S_i`-scalar on `M_i`
  -- is exactly the `SMulCommClass` input proved above.
  ext x
  simpa using (smul_comm x.1 s m)

/-- Helper for Lemma 10.128.3: the raw multiplication map on the right-factor tensor model is
`S_i`-linear. -/
noncomputable def raw_stage_right_multiplication
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
    A.moduleStage i ⊗[A.RStage i] I →ₗ[A.SStage i] A.moduleStage i :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
  TensorProduct.AlgebraTensorModule.lift
    { toFun := raw_stage_right_factor_map A i I
      map_add' := raw_stage_right_factor_map_map_add (A := A) (i := i) (I := I)
      map_smul' := raw_stage_right_factor_map_map_smul (A := A) (i := i) (I := I) }

/-- Helper for Lemma 10.128.3: the raw Tor multiplication map on `I ⊗[R_i] M_i`, promoted to an
`S_i`-linear map by commuting the tensor factors. -/
noncomputable def raw_stage_multiplication
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    I ⊗[A.RStage i] A.moduleStage i →ₗ[A.SStage i] A.moduleStage i :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  let eComm :
      (I ⊗[A.RStage i] A.moduleStage i) ≃ₗ[A.SStage i]
        (A.moduleStage i ⊗[A.RStage i] I) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.linearEquiv (A.SStage i)
  (raw_stage_right_multiplication A i I).comp eComm.toLinearMap

/-- Helper for Lemma 10.128.3: on pure tensors, the named raw stage multiplication map is the
expected literal scalar multiplication map. -/
lemma raw_stage_multiplication_tmul
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (a : I) (m : A.moduleStage i) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    raw_stage_multiplication A i I (a ⊗ₜ[A.RStage i] m) = a.1 • m := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (A.moduleStage i ⊗[A.RStage i] I) := TensorProduct.leftModule
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  -- Proof comment: commute the tensor factors and then evaluate the right-factor multiplication
  -- owner on the pure tensor `m ⊗ a`.
  simp [raw_stage_multiplication, raw_stage_right_multiplication, raw_stage_right_factor_map]

/-- Helper for Lemma 10.128.3: the named `S_i`-linear raw multiplication map restricts to the
literal textbook map `I ⊗[R_i] M_i → M_i`. -/
lemma raw_stage_multiplication_restrictScalars_eq
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    (raw_stage_multiplication A i I).restrictScalars (A.RStage i) =
      TensorProduct.lift ((LinearMap.lsmul (A.RStage i) (A.moduleStage i)).comp I.subtype) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  -- Proof comment: both `R_i`-linear maps agree on pure tensors, and tensor extensionality
  -- upgrades that computation to equality of linear maps.
  ext a m
  simpa using raw_stage_multiplication_tmul (A := A) (i := i) (I := I) a m

/-- Helper for Lemma 10.128.3: the raw Tor kernel at stage `i`, viewed as an `S_i`-submodule of
`I ⊗[R_i] M_i` through the canonical promoted multiplication map. -/
noncomputable def raw_stage_kernel
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i)) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    Submodule (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  LinearMap.ker (raw_stage_multiplication A i I)

/-- Helper for Lemma 10.128.3: membership in the named raw kernel is exactly the textbook
condition `μraw z = 0`. -/
lemma mem_raw_stage_kernel_iff
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (z : I ⊗[A.RStage i] A.moduleStage i) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    z ∈ raw_stage_kernel A i I ↔
      TensorProduct.lift ((LinearMap.lsmul (A.RStage i) (A.moduleStage i)).comp I.subtype) z = 0 := by
  -- Proof comment: the named owner was chosen precisely so that its restricted underlying map is
  -- the raw multiplication map from the textbook.
  change raw_stage_multiplication A i I z = 0 ↔
    TensorProduct.lift ((LinearMap.lsmul (A.RStage i) (A.moduleStage i)).comp I.subtype) z = 0
  have hEval :
      raw_stage_multiplication A i I z =
        TensorProduct.lift ((LinearMap.lsmul (A.RStage i) (A.moduleStage i)).comp I.subtype) z := by
    exact congrArg (fun g : I ⊗[A.RStage i] A.moduleStage i →ₗ[A.RStage i] A.moduleStage i ↦ g z)
      (raw_stage_multiplication_restrictScalars_eq (A := A) (i := i) (I := I))
  constructor <;> intro hz
  · simpa [hEval] using hz
  · simpa [hEval] using hz

/-- Helper for Lemma 10.128.3: an element of the named raw kernel is killed by the named raw
multiplication map. -/
lemma raw_stage_kernel_multiplication_eq_zero
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (i : A.Λ) (I : Ideal (A.RStage i))
    (z : raw_stage_kernel A i I) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    raw_stage_multiplication A i I z.1 = 0 := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  -- Proof comment: membership in the subtype is membership in the kernel of the named raw
  -- multiplication map.
  exact z.2

/-- Helper for Lemma 10.128.3: the source-stage action on the limit module factors through the
source-stage map to `R` and the original `R`-action on `M`. -/
lemma limit_module_source_stage_isScalarTower
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Module R M := Module.compHom M f
    let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
    let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
    IsScalarTower (A.RStage i) R M := by
  let _ : Module R M := Module.compHom M f
  let _ : Algebra (A.RStage i) R := (source_stage_to_limit_hom A i).toAlgebra
  let _ : Module (A.RStage i) M := Module.compHom M (f.comp (source_stage_to_limit_hom A i))
  -- Proof comment: both scalar actions on `M` are defined by the same composite ring map
  -- `R_i → R → S`.
  refine ⟨?_⟩
  intro r x m
  change f ((source_stage_to_limit_hom A i r) * x) • m =
    f (source_stage_to_limit_hom A i r) • (f x • m)
  rw [map_mul, mul_smul]

/-- Helper for Lemma 10.128.3: the named raw stage kernel is finite over `S_i`. -/
lemma raw_stage_kernel_finite
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_isScalarTower A i
    let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
      stage_module_smulCommClass A i
    let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
      (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
    Module.Finite (A.SStage i) (raw_stage_kernel A i I) := by
  let I : Ideal (A.RStage i) := IsLocalRing.maximalIdeal (A.RStage i)
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_isScalarTower A i
  let _ : SMulCommClass (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    stage_module_smulCommClass A i
  let _ : Module (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).toAddEquiv.module (A.SStage i)
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    (TensorProduct.comm (A.RStage i) I (A.moduleStage i)).isScalarTower (A := A.SStage i)
  let _ : Module.Finite (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) :=
    stage_ideal_tensor_finite A i
  let _ : IsNoetherianRing (A.SStage i) := stage_target_isNoetherianRing A i
  let _ : IsNoetherian (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) := inferInstance
  let _ : IsNoetherian (A.SStage i) (raw_stage_kernel A i I) :=
    isNoetherian_of_submodule_of_noetherian
      (A.SStage i) (I ⊗[A.RStage i] A.moduleStage i) (raw_stage_kernel A i I) inferInstance
  -- Proof comment: once the raw kernel has a stable `S_i`-submodule owner, it is a submodule of
  -- a finite module over the Noetherian ring `S_i`, hence finite.
  exact Module.IsNoetherian.finite (A.SStage i) (raw_stage_kernel A i I)

end DirectedLocalEssFinitePresentationModuleApproximation

end
