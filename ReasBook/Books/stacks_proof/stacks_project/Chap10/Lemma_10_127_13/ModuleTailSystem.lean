import StacksProject_2024.Chap10.Lemma_10_127_13.TailApproximation

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w uR uS uM uN

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

/-- Helper for Lemma 10.127.13: after restricting scalars along the target-colimit equivalence, a
finitely presented `S`-module descends to one target stage of the approximation system. -/
theorem descend_module_to_target_stage
    (A : DirectedLocalHomApproximation f) [Module.FinitePresentation S M] :
    let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
    let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
    ∃ (i₀ : A.Λ) (M₀ : Type uS) (_ : AddCommGroup M₀) (_ : Module (A.SStage i₀) M₀)
      (_ : Module.FinitePresentation (A.SStage i₀) M₀),
      Nonempty (D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) := by
  let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
  let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
  let _ : Module.FinitePresentation D M := by
    -- Proof comment: finite presentation transfers from `S` back to the target direct limit
    -- along the colimit ring equivalence.
    simpa [D] using
      (module_finitePresentation_compHom_of_ringEquiv (e := A.targetColimit) (N := M))
  -- Proof comment: once the target system is viewed as a directed system with colimit ring `D`,
  -- the generic descent theorem from Lemma `10.127.6` applies directly.
  simpa [D] using
    (finitelyPresented_module_descends_to_stage
      (R := A.SStage) (f := fun i j h ↦ A.targetMap i j h) (M := M))

/-- Helper for Lemma 10.127.13: target-stage transition maps form a scalar tower along a tail
chain. -/
theorem target_stage_transition_isScalarTower
    (A : DirectedLocalHomApproximation f) (i₀ : A.Λ) (j k : Set.Ici i₀) (hjk : j ≤ k) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.targetMap i₀ k.1 k.2).toAlgebra
    let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.targetMap j.1 k.1 hjk).toAlgebra
    IsScalarTower (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) := by
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.targetMap i₀ k.1 k.2).toAlgebra
  let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.targetMap j.1 k.1 hjk).toAlgebra
  -- Proof comment: the later stage receives scalars from `i₀` either directly or through the
  -- intermediate stage `j`, and the directed-system composition law identifies the two maps.
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext x
  change A.targetMap i₀ k.1 k.2 x = A.targetMap j.1 k.1 hjk (A.targetMap i₀ j.1 j.2 x)
  exact (DirectedSystem.map_map (f := fun a b h ↦ A.targetMap a b h) j.2 hjk x).symm

/-- Helper for Lemma 10.127.13: the limit map from a later stage factors through the earlier tail
stage as a scalar tower. -/
theorem target_stage_limit_isScalarTower
    (A : DirectedLocalHomApproximation f) (i₀ : A.Λ) (j : Set.Ici i₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom A i₀).toAlgebra
    let _ : Algebra (A.SStage j.1) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom A j.1).toAlgebra
    IsScalarTower (A.SStage i₀) (A.SStage j.1) S := by
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom A i₀).toAlgebra
  let _ : Algebra (A.SStage j.1) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom A j.1).toAlgebra
  -- Proof comment: the direct-limit comparison from `j` to `S` already factors through the
  -- transition `i₀ ≤ j`, exactly as `targetStageToLimitHom_comp_targetMap` records.
  refine IsScalarTower.of_algebraMap_eq' ?_
  simpa [RingHom.algebraMap_toAlgebra] using
    (targetStageToLimitHom_comp_targetMap (f := f) A j.2).symm

/-- Helper for Lemma 10.127.13: the tail transition modules are the standard cancel-base-change
modules obtained by extending scalars from the fixed descended stage. -/
noncomputable def tail_module_transition_baseChange
    (A : DirectedLocalHomApproximation f) (i₀ : A.Λ)
    {M₀ : Type uS} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
    let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
    let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.targetMap i₀ k.1 k.2).toAlgebra
    let _ : Module (A.SStage i₀) (A.SStage k.1) := inferInstance
    let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.targetMap j.1 k.1 hjk).toAlgebra
    A.SStage k.1 ⊗[A.SStage j.1] (A.SStage j.1 ⊗[A.SStage i₀] M₀) ≃ₗ[A.SStage k.1]
      A.SStage k.1 ⊗[A.SStage i₀] M₀ :=
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.targetMap i₀ k.1 k.2).toAlgebra
  let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.targetMap j.1 k.1 hjk).toAlgebra
  let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
  let _ : Module (A.SStage i₀) (A.SStage k.1) := inferInstance
  let _ : IsScalarTower (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) :=
    target_stage_transition_isScalarTower (f := f) A i₀ j k hjk
  -- Proof comment: tensoring once from `A.SStage i₀` to `A.SStage j.1` and then again to
  -- `A.SStage k.1` collapses to the single base change to `A.SStage k.1`.
  TensorProduct.AlgebraTensorModule.cancelBaseChange
    (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) (A.SStage k.1) M₀

/-- Helper for Lemma 10.127.13: transport the descended direct-limit module equivalence across
the target-colimit ring equivalence to obtain an `S`-linear equivalence. -/
theorem targetColimit_transport_descended_module_equiv
    (A : DirectedLocalHomApproximation f)
    (i₀ : A.Λ)
    {M₀ : Type uS} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (eM :
      let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
      let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
      D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) :
    let _ : Algebra (A.SStage i₀) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom A i₀).toAlgebra
    Nonempty (S ⊗[A.SStage i₀] M₀ ≃ₗ[S] M) := by
  let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
  let _ : Algebra (A.SStage i₀) D :=
    (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.targetMap i j h) i₀).toAlgebra
  let _ : Algebra (A.SStage i₀) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom A i₀).toAlgebra
  let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
  let _ : Algebra S D := A.targetColimit.symm.toRingHom.toAlgebra
  let _ : IsScalarTower (A.SStage i₀) S D := by
    -- Proof comment: the lifted `S`-algebra on the direct limit is chosen so that composing the
    -- stage map into `S` with `A.targetColimit.symm` recovers the canonical stage map into `D`.
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    simp [DirectedLocalHomApproximation.targetStageToLimitHom, RingHom.algebraMap_toAlgebra]
  let _ : IsScalarTower S D M :=
    { smul_assoc := fun s d m ↦ by
        -- Proof comment: the transported `S`-action on `D` is multiplication by
        -- `A.targetColimit.symm s`, and the `D`-action on `M` is multiplication by
        -- `A.targetColimit d` inside the original `S`-module structure.
        change A.targetColimit ((A.targetColimit.symm s) * d) • m =
          s • (A.targetColimit d • m)
        rw [RingEquiv.map_mul]
        simp [mul_smul] }
  let eDS : D ≃ₐ[S] S :=
    { toRingEquiv := A.targetColimit
      commutes' := by
        intro x
        simp [RingHom.algebraMap_toAlgebra] }
  let eTensor :
      D ⊗[A.SStage i₀] M₀ ≃ₗ[S] S ⊗[A.SStage i₀] M₀ :=
    TensorProduct.AlgebraTensorModule.congr eDS.toLinearEquiv
      (LinearEquiv.refl (A.SStage i₀) M₀)
  -- Proof comment: first rewrite the tensor's left factor from the direct-limit ring `D` to `S`,
  -- then restrict the descended `D`-linear equivalence along the transported scalar tower.
  exact ⟨eTensor.symm.trans (eM.restrictScalars S)⟩

/-- Helper for Lemma 10.127.13: once a stage module has been descended to one target stage of the
ring approximation, the remaining source-faithful step is to restrict to the tail and define each
later stage by scalar extension from that fixed descended module. -/
theorem tail_module_system_from_descended_stage
    (A : DirectedLocalHomApproximation.{uR, uS, max uR uS} f)
    (hA : DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A)
    (i₀ : A.Λ)
    {M₀ : Type uS} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    [Module.FinitePresentation (A.SStage i₀) M₀]
    (eM :
      let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
      let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
      D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) :
    Nonempty
      (DirectedLocalEssFinitePresentationModuleApproximation.{uR, uS, uM, uS, max uR uS} f M) := by
  let B := tail_local_hom_approximation (f := f) A i₀
  have hB :
      DirectedLocalHomApproximation.HasPrimeLocalizationTransitions B :=
    tail_local_hom_approximation_hasPrimeLocalizationTransitions (f := f) A hA i₀
  obtain ⟨finalAtBase⟩ :=
    targetColimit_transport_descended_module_equiv (f := f) (M := M) A i₀ eM
  -- Proof comment: the textbook tail construction keeps the ring approximation and defines each
  -- later stage by extending scalars from the single descended module `M₀` at the base stage `i₀`.
  let C :
      DirectedLocalEssFinitePresentationModuleApproximation.{uR, uS, uM, uS, max uR uS} f M :=
    { toDirectedLocalHomApproximation := B
      hasPrimeLocalizationTransitions := hB
      moduleStage := fun j : B.Λ ↦
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
        A.SStage j.1 ⊗[A.SStage i₀] M₀
      instAddCommGroupModuleStage := fun j ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
        exact show AddCommGroup (A.SStage j.1 ⊗[A.SStage i₀] M₀) from inferInstance
      instModuleModuleStage := fun j ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
        exact show Module (A.SStage j.1) (A.SStage j.1 ⊗[A.SStage i₀] M₀) from inferInstance
      instModuleFiniteModuleStage := fun j ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
        let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
        let _ : Module.Finite (A.SStage i₀) M₀ := inferInstance
        exact show Module.Finite (A.SStage j.1) (A.SStage j.1 ⊗[A.SStage i₀] M₀) from
          inferInstance
      transitionBaseChange := fun {j k : B.Λ} hjk ↦ by
        -- Proof comment: two consecutive scalar extensions from `i₀` through `j` to `k`
        -- collapse to the one-step extension from `i₀` to `k`.
        simpa [tail_local_hom_approximation] using
          tail_module_transition_baseChange (f := f) A i₀ j k hjk
      finalBaseChange := fun j : B.Λ ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
        let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
        let _ : Algebra (A.SStage i₀) S :=
          (DirectedLocalHomApproximation.targetStageToLimitHom A i₀).toAlgebra
        let _ : Algebra (A.SStage j.1) S :=
          (DirectedLocalHomApproximation.targetStageToLimitHom A j.1).toAlgebra
        let _ : IsScalarTower (A.SStage i₀) (A.SStage j.1) S :=
          target_stage_limit_isScalarTower (f := f) A i₀ j
        -- Proof comment: cancel the intermediate base change from `i₀` to `j`, then finish with
        -- the already transported final equivalence at the base stage.
        simpa [tail_local_hom_approximation,
          tail_targetStageToLimitHom_eq (f := f) A i₀ j] using
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            (A.SStage i₀) (A.SStage j.1) S S M₀).trans finalAtBase }
  exact Nonempty.intro C

-- Proof sketch: first approximate the local map `R → S` by a directed system of local maps whose
-- source stages are essentially of finite type over `ℤ` and whose target stages are essentially
-- of finite type over the source stages. Then descend a finite presentation matrix for `M` to a
-- sufficiently large target stage, define the stage modules by cokernels of the descended
-- matrices, and use finite presentation to obtain the base-change isomorphisms between stages and
-- after passage to the colimit.

end
