import stacks_proof.stacks_project.Chap10.Lemma_10_127_17
import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.PolynomialModels
import stacks_proof.stacks_project.Chap10.Lemma_10_127_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w x y

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace DirectedFiniteTypeHomApproximation

variable {f : R →+* S}

/-- The canonical map from a source stage to the limit ring `R`. -/
noncomputable abbrev sourceStageToLimit (A : DirectedFiniteTypeHomApproximation f) (i : A.Λ) :
    A.RStage i →+* R :=
  let ιR := A.colimitSource.toRingHom
  ιR.comp (Ring.DirectLimit.of A.RStage (fun i j h ↦ A.RMap i j h) i)

/-- The canonical map from a target stage to the limit ring `S`. -/
noncomputable abbrev targetStageToLimit (A : DirectedFiniteTypeHomApproximation f) (i : A.Λ) :
    A.SStage i →+* S :=
  let ιS := A.colimitTarget.toRingHom
  ιS.comp (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.SMap i j h) i)

end DirectedFiniteTypeHomApproximation

/-- A directed approximation of a finitely presented `S`-module along a finitely presented ring
map `R → S`, with finite stage modules whose target-side base changes recover the later stages and
the limit module. -/
structure DirectedFinitePresentationModuleApproximation
    (f : R →+* S) (M : Type x) [AddCommGroup M] [Module S M]
    extends DirectedFiniteTypeHomApproximation f where
  hasBijectiveBaseChangeTransitions :
    toDirectedFiniteTypeHomApproximation.HasBijectiveBaseChangeTransitions
  moduleStage : Λ → Type (max v y)
  instAddCommGroupModuleStage : ∀ i, AddCommGroup (moduleStage i)
  instModuleModuleStage : ∀ i, Module (SStage i) (moduleStage i)
  instModuleFiniteModuleStage : ∀ i, Module.Finite (SStage i) (moduleStage i)
  moduleMap :
    ∀ {i j} (h : i ≤ j),
      let _ : Module (SStage i) (moduleStage j) := Module.compHom (moduleStage j) (SMap i j h)
      moduleStage i →ₗ[SStage i] moduleStage j
  moduleMap_id : ∀ i (m : moduleStage i), moduleMap le_rfl m = m
  moduleMap_comp :
    ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (m : moduleStage i),
      moduleMap hjk (moduleMap hij m) = moduleMap (hij.trans hjk) m
  moduleToLimit :
    ∀ i,
      let _ : Module (SStage i) M := Module.compHom M
        (toDirectedFiniteTypeHomApproximation.targetStageToLimit i)
      moduleStage i →ₗ[SStage i] M
  moduleToLimit_comp :
    ∀ {i j} (h : i ≤ j) (m : moduleStage i),
      moduleToLimit j (moduleMap h m) = moduleToLimit i m
  transitionBaseChangeMap_bijective :
    ∀ {i j} (h : i ≤ j),
      let _ : Algebra (SStage i) (SStage j) := (SMap i j h).toAlgebra
      let _ : Module (SStage i) (moduleStage j) := Module.compHom (moduleStage j) (SMap i j h)
      let _ : IsScalarTower (SStage i) (SStage j) (moduleStage j) :=
        RestrictScalars.isScalarTower (SStage i) (SStage j) (moduleStage j)
      Function.Bijective
        (((moduleMap h).liftBaseChange (SStage j)) :
          SStage j ⊗[SStage i] moduleStage i →ₗ[SStage j] moduleStage j)
  finalBaseChangeMap_bijective :
    ∀ i,
      let _ : Algebra (SStage i) S :=
        (toDirectedFiniteTypeHomApproximation.targetStageToLimit i).toAlgebra
      let _ : Module (SStage i) M := Module.compHom M
        (toDirectedFiniteTypeHomApproximation.targetStageToLimit i)
      let _ : IsScalarTower (SStage i) S M :=
        RestrictScalars.isScalarTower (SStage i) S M
      Function.Bijective
        (((moduleToLimit i).liftBaseChange S) :
          S ⊗[SStage i] moduleStage i →ₗ[S] M)

attribute [instance] DirectedFinitePresentationModuleApproximation.instAddCommGroupModuleStage
attribute [instance] DirectedFinitePresentationModuleApproximation.instModuleModuleStage
attribute [instance] DirectedFinitePresentationModuleApproximation.instModuleFiniteModuleStage

namespace DirectedFinitePresentationModuleApproximation

variable {f : R →+* S} {M : Type x} [AddCommGroup M] [Module S M]

/-- The canonical base-change map attached to a transition in the module system. -/
noncomputable def transitionBaseChangeMap
    (A : DirectedFinitePresentationModuleApproximation f M) {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.SMap i j h).toAlgebra
    A.SStage j ⊗[A.SStage i] A.moduleStage i →ₗ[A.SStage j] A.moduleStage j :=
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.SMap i j h).toAlgebra
  let _ : Module (A.SStage i) (A.moduleStage j) :=
    Module.compHom (A.moduleStage j) (A.SMap i j h)
  let _ : IsScalarTower (A.SStage i) (A.SStage j) (A.moduleStage j) :=
    RestrictScalars.isScalarTower (A.SStage i) (A.SStage j) (A.moduleStage j)
  (A.moduleMap h).liftBaseChange (A.SStage j)

/-- The canonical base-change map from a stage module to the limiting module `M`. -/
noncomputable def finalBaseChangeMap
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.SStage i) S := (A.targetStageToLimit i).toAlgebra
    S ⊗[A.SStage i] A.moduleStage i →ₗ[S] M :=
  let ιS : A.SStage i →+* S := A.targetStageToLimit i
  let _ : Algebra (A.SStage i) S := ιS.toAlgebra
  let _ : Module (A.SStage i) M := Module.compHom M ιS
  let _ : IsScalarTower (A.SStage i) S M :=
    RestrictScalars.isScalarTower (A.SStage i) S M
  (A.moduleToLimit i).liftBaseChange S

/-- The canonical transition base-change map is an isomorphism. -/
noncomputable def transitionBaseChange
    (A : DirectedFinitePresentationModuleApproximation f M) {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.SMap i j h).toAlgebra
    A.SStage j ⊗[A.SStage i] A.moduleStage i ≃ₗ[A.SStage j] A.moduleStage j :=
  LinearEquiv.ofBijective (A.transitionBaseChangeMap h) (A.transitionBaseChangeMap_bijective h)

/-- The canonical final base-change map is an isomorphism. -/
noncomputable def finalBaseChange
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.SStage i) S := (A.targetStageToLimit i).toAlgebra
    S ⊗[A.SStage i] A.moduleStage i ≃ₗ[S] M :=
  LinearEquiv.ofBijective (A.finalBaseChangeMap i) (A.finalBaseChangeMap_bijective i)

/-- Helper for Lemma 10.127.18: after transporting the finitely presented `S`-module `M` back to
the target direct-limit ring, it descends to one target stage of the approximation. -/
theorem descend_module_to_target_stage
    (A : DirectedFiniteTypeHomApproximation f)
    {M : Type x} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.SMap i j h)
    let _ : Module D M := Module.compHom M A.colimitTarget.toRingHom
    ∃ (i₀ : A.Λ) (M₀ : Type v) (_ : AddCommGroup M₀) (_ : Module (A.SStage i₀) M₀)
      (_ : Module.FinitePresentation (A.SStage i₀) M₀),
      Nonempty (D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) := by
  let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.SMap i j h)
  let _ : Module D M := Module.compHom M A.colimitTarget.toRingHom
  let _ : Module.FinitePresentation D M := by
    -- Proof comment: finite presentation transfers from `S` to the target direct-limit ring
    -- through the chosen colimit equivalence.
    simpa [D] using
      (module_finitePresentation_compHom_of_ringEquiv (e := A.colimitTarget) (N := M))
  -- Proof comment: after this transport, the generic directed-colimit descent theorem gives
  -- a stage module whose base change to the target colimit recovers `M`.
  simpa [D] using
    (finitelyPresented_module_descends_to_stage
      (R := A.SStage) (f := fun i j h ↦ A.SMap i j h) (M := M))

/-- Helper for Chap10 Lemma 10 127 18: the target-stage-to-limit maps are compatible with target
transition maps. -/
theorem targetStageToLimit_comp_SMap
    (A : DirectedFiniteTypeHomApproximation f) {i j : A.Λ} (h : i ≤ j) :
    (A.targetStageToLimit j).comp (A.SMap i j h) = A.targetStageToLimit i := by
  ext x
  -- Proof comment: both sides are the direct-limit cocone map evaluated on the generator coming
  -- from stage `i`.
  simp [DirectedFiniteTypeHomApproximation.targetStageToLimit, RingHom.comp_apply,
    Ring.DirectLimit.of_f]

/-- Helper for Chap10 Lemma 10 127 18: target transition maps form a scalar tower along any tail
chain. -/
theorem targetStageTransition_isScalarTower
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ) (j k : Set.Ici i₀) (hjk : j ≤ k) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
    let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
    IsScalarTower (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) := by
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
  let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
  -- Proof comment: the direct map `i₀ → k` and the composite `i₀ → j → k` agree by the target
  -- directed-system composition law.
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext x
  change A.SMap i₀ k.1 k.2 x = A.SMap j.1 k.1 hjk (A.SMap i₀ j.1 j.2 x)
  exact (DirectedSystem.map_map (f := fun a b h ↦ A.SMap a b h) j.2 hjk x).symm

/-- Helper for Chap10 Lemma 10 127 18: the target-stage-to-limit map factors through any later
tail stage as a scalar tower. -/
theorem targetStageLimit_isScalarTower
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ) (j : Set.Ici i₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
    let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
    IsScalarTower (A.SStage i₀) (A.SStage j.1) S := by
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
  let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
  -- Proof comment: compatibility of the target direct-limit cocone identifies the two resulting
  -- algebra maps from the base tail stage to `S`.
  refine IsScalarTower.of_algebraMap_eq' ?_
  simpa [RingHom.algebraMap_toAlgebra] using
    (targetStageToLimit_comp_SMap (f := f) A j.2).symm

/-- Helper for Chap10 Lemma 10 127 18: the descended module equivalence over the target direct
limit transports to an `S`-linear equivalence at the base tail stage. -/
theorem targetColimit_transport_descendedModuleEquiv
    (A : DirectedFiniteTypeHomApproximation f)
    (i₀ : A.Λ)
    {M : Type x} [AddCommGroup M] [Module S M]
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (eM :
      let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.SMap i j h)
      let _ : Module D M := Module.compHom M A.colimitTarget.toRingHom
      D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) :
    let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
    Nonempty (S ⊗[A.SStage i₀] M₀ ≃ₗ[S] M) := by
  let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.SMap i j h)
  let _ : Algebra (A.SStage i₀) D :=
    (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.SMap i j h) i₀).toAlgebra
  let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
  let _ : Module D M := Module.compHom M A.colimitTarget.toRingHom
  let _ : Algebra S D := A.colimitTarget.symm.toRingHom.toAlgebra
  let _ : IsScalarTower (A.SStage i₀) S D := by
    -- Proof comment: the transported `S`-algebra on the direct limit is chosen so that the
    -- stage map into `S`, followed by `A.colimitTarget.symm`, is the original stage map into `D`.
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    simp [DirectedFiniteTypeHomApproximation.targetStageToLimit, RingHom.algebraMap_toAlgebra]
  let _ : IsScalarTower S D M :=
    { smul_assoc := fun s d m ↦ by
        -- Proof comment: after transporting the scalar action through the ring equivalence, this
        -- is just associativity of multiplication in `S` followed by the original module action.
        change A.colimitTarget ((A.colimitTarget.symm s) * d) • m =
          s • (A.colimitTarget d • m)
        rw [RingEquiv.map_mul]
        simp [mul_smul] }
  let eDS : D ≃ₐ[S] S :=
    { toRingEquiv := A.colimitTarget
      commutes' := by
        intro x
        simp [RingHom.algebraMap_toAlgebra] }
  let eTensor :
      D ⊗[A.SStage i₀] M₀ ≃ₗ[S] S ⊗[A.SStage i₀] M₀ :=
    TensorProduct.AlgebraTensorModule.congr eDS.toLinearEquiv
      (LinearEquiv.refl (A.SStage i₀) M₀)
  -- Proof comment: rewrite the tensor's left factor from the direct-limit ring to `S`, then
  -- restrict the descended equivalence along the transported scalar tower.
  exact ⟨eTensor.symm.trans (eM.restrictScalars S)⟩

/-- Helper for Chap10 Lemma 10 127 18: restricting a finite-type ring approximation to the tail
above one index preserves the source and target colimit comparison. -/
noncomputable def tailFiniteTypeHomApproximation
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ) :
    DirectedFiniteTypeHomApproximation f where
  Λ := Set.Ici i₀
  instPreorder := inferInstance
  instNonempty := inferInstance
  instDirectedOrder := tail_index_isDirected i₀
  RStage := fun j ↦ A.RStage j.1
  SStage := fun j ↦ A.SStage j.1
  instCommRingRStage := fun _ ↦ inferInstance
  instCommRingSStage := fun _ ↦ inferInstance
  RMap := fun j k h ↦ A.RMap j.1 k.1 h
  SMap := fun j k h ↦ A.SMap j.1 k.1 h
  instDirectedSystemRStage := inferInstance
  instDirectedSystemSStage := inferInstance
  stageMap := fun j ↦ A.stageMap j.1
  comm := fun {j k} h ↦ A.comm h
  source_finiteType := fun j ↦ A.source_finiteType j.1
  target_finiteType := fun j ↦ A.target_finiteType j.1
  colimitSource :=
    tail_directLimitIso A.RStage (fun i j h ↦ A.RMap i j h) i₀ A.colimitSource
  colimitTarget :=
    tail_directLimitIso A.SStage (fun i j h ↦ A.SMap i j h) i₀ A.colimitTarget
  colimit_comm := by
    -- Proof comment: the tail colimit maps are the original colimit maps after forgetting the
    -- lower-bound proof in the tail index, so the original colimit square proves the tail square.
    apply Ring.DirectLimit.hom_ext
    intro j
    ext x
    have hfull :=
      congrArg
        (fun g : Ring.DirectLimit A.RStage (fun i j h ↦ A.RMap i j h) →+* S ↦
          g (Ring.DirectLimit.of A.RStage (fun i j h ↦ A.RMap i j h) j.1 x))
        A.colimit_comm
    simpa [tail_directLimitIso, tail_directLimit_to_full, RingHom.comp_apply,
      Ring.DirectLimit.map_apply_of] using hfull

/-- Helper for Chap10 Lemma 10 127 18: bijective target base-change transitions are inherited by
the tail restriction. -/
theorem tailFiniteTypeHomApproximation_hasBijectiveBaseChangeTransitions
    (A : DirectedFiniteTypeHomApproximation f)
    (hA : A.HasBijectiveBaseChangeTransitions) (i₀ : A.Λ) :
    (tailFiniteTypeHomApproximation (f := f) A i₀).HasBijectiveBaseChangeTransitions := by
  intro j k hjk
  -- Proof comment: a transition in the tail is the same transition in the original directed
  -- system, with the same source and target base-change map.
  simpa [tailFiniteTypeHomApproximation] using hA hjk

/-- Helper for Chap10 Lemma 10 127 18: after passing to the tail, the target-stage-to-limit map
is the original stage-to-limit map at the underlying index. -/
theorem tailTargetStageToLimit_eq
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ) (j : Set.Ici i₀) :
    (tailFiniteTypeHomApproximation (f := f) A i₀).targetStageToLimit j =
      A.targetStageToLimit j.1 := by
  ext x
  -- Proof comment: the tail target colimit is identified with the original target colimit by
  -- forgetting the tail bound; on generators this is the canonical tail map.
  change
    (tail_directLimitIso A.SStage (fun i j h ↦ A.SMap i j h) i₀ A.colimitTarget)
        (Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ A.SStage j.1)
          (fun j k h ↦ A.SMap j.1 k.1 h) j x) =
      A.colimitTarget
        (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.SMap i j h) j.1 x)
  simp [tail_directLimitIso, tail_directLimit_to_full_of]

/-- Helper for Chap10 Lemma 10 127 18: the tail module transition is induced by canceling the
intermediate scalar extension through a later target stage. -/
noncomputable def tailModuleMap
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ)
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
    let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
    (A.SStage j.1 ⊗[A.SStage i₀] M₀) →ₗ[A.SStage j.1]
      (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
  let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
  let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
  let _ : Module (A.SStage i₀) (A.SStage k.1) := inferInstance
  let _ : IsScalarTower (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) :=
    targetStageTransition_isScalarTower (f := f) A i₀ j k hjk
  (LinearMap.liftBaseChangeEquiv (A.SStage k.1)).symm
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) (A.SStage k.1) M₀).toLinearMap

/-- Helper for Chap10 Lemma 10 127 18: the explicit tail module transition sends a pure tensor by
applying the target transition to the left factor. -/
theorem tailModuleMap_tmul
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ)
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    {j k : Set.Ici i₀} (hjk : j ≤ k) (s : A.SStage j.1) (m : M₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
    let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
    tailModuleMap (f := f) A i₀ hjk (s ⊗ₜ[A.SStage i₀] m) =
      A.SMap j.1 k.1 hjk s ⊗ₜ[A.SStage i₀] m := by
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
  let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
  let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
  let _ : Module (A.SStage i₀) (A.SStage k.1) := inferInstance
  let _ : IsScalarTower (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) :=
    targetStageTransition_isScalarTower (f := f) A i₀ j k hjk
  -- Proof comment: `liftBaseChangeEquiv.symm` evaluates the lifted map at `1 ⊗ -`, and the
  -- cancel-base-change equivalence multiplies the two left scalars.
  simp [tailModuleMap, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    Algebra.smul_def, RingHom.algebraMap_toAlgebra]

/-- Helper for Chap10 Lemma 10 127 18: the tail map from a scalar-extended stage module to the
limit module is induced by canceling the intermediate target stage and then applying the descended
final equivalence at the base stage. -/
noncomputable def tailModuleToLimit
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ)
    {M : Type x} [AddCommGroup M] [Module S M]
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (finalAtBase :
      let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
      S ⊗[A.SStage i₀] M₀ ≃ₗ[S] M)
    (j : Set.Ici i₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
    let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
    let _ : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
    (A.SStage j.1 ⊗[A.SStage i₀] M₀) →ₗ[A.SStage j.1] M :=
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
  let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
  let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
  let _ : Module (A.SStage i₀) S := Algebra.toModule
  let _ : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
  let _ : IsScalarTower (A.SStage i₀) (A.SStage j.1) S :=
    targetStageLimit_isScalarTower (f := f) A i₀ j
  let _ : IsScalarTower (A.SStage j.1) S M :=
    RestrictScalars.isScalarTower (A.SStage j.1) S M
  (LinearMap.liftBaseChangeEquiv S).symm
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
      (A.SStage i₀) (A.SStage j.1) S S M₀).trans finalAtBase).toLinearMap

/-- Helper for Chap10 Lemma 10 127 18: the tail map to the limit evaluates on pure tensors by
first sending the target-stage scalar to the limit ring. -/
theorem tailModuleToLimit_tmul
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ)
    {M : Type x} [AddCommGroup M] [Module S M]
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (finalAtBase :
      let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
      S ⊗[A.SStage i₀] M₀ ≃ₗ[S] M)
    (j : Set.Ici i₀) (s : A.SStage j.1) (m : M₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
    let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
    let _ : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
    tailModuleToLimit (f := f) A i₀ finalAtBase j (s ⊗ₜ[A.SStage i₀] m) =
      finalAtBase (A.targetStageToLimit j.1 s ⊗ₜ[A.SStage i₀] m) := by
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
  let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
  let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
  let _ : Module (A.SStage i₀) S := Algebra.toModule
  let _ : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
  let _ : IsScalarTower (A.SStage i₀) (A.SStage j.1) S :=
    targetStageLimit_isScalarTower (f := f) A i₀ j
  let _ : IsScalarTower (A.SStage j.1) S M :=
    RestrictScalars.isScalarTower (A.SStage j.1) S M
  -- Proof comment: the inverse lift-base-change equivalence evaluates at `1 ⊗ -`; after
  -- canceling, this multiplies `1` by the image of the stage scalar in `S`.
  simp [tailModuleToLimit, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    Algebra.smul_def, RingHom.algebraMap_toAlgebra]

/-- Helper for Chap10 Lemma 10 127 18: base-changing the explicit tail transition recovers the
standard tensor-cancellation equivalence. -/
theorem tailModuleMap_liftBaseChange_bijective
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ)
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
    let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
    let _ : Module (A.SStage j.1) (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
      Module.compHom (A.SStage k.1 ⊗[A.SStage i₀] M₀) (A.SMap j.1 k.1 hjk)
    let _ : IsScalarTower (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) :=
      targetStageTransition_isScalarTower (f := f) A i₀ j k hjk
    let _ : IsScalarTower (A.SStage j.1) (A.SStage k.1)
        (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
      RestrictScalars.isScalarTower (A.SStage j.1) (A.SStage k.1)
        (A.SStage k.1 ⊗[A.SStage i₀] M₀)
    Function.Bijective
      (((tailModuleMap (f := f) A i₀ hjk).liftBaseChange (A.SStage k.1)) :
        A.SStage k.1 ⊗[A.SStage j.1] (A.SStage j.1 ⊗[A.SStage i₀] M₀)
          →ₗ[A.SStage k.1] A.SStage k.1 ⊗[A.SStage i₀] M₀) := by
  letI : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  letI : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
  letI : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
  letI : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
  letI : Module (A.SStage i₀) (A.SStage k.1) := inferInstance
  letI : Module (A.SStage j.1) (A.SStage k.1) :=
    Module.compHom (A.SStage k.1) (A.SMap j.1 k.1 hjk)
  letI : Module (A.SStage j.1) (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
    Module.compHom (A.SStage k.1 ⊗[A.SStage i₀] M₀) (A.SMap j.1 k.1 hjk)
  letI : IsScalarTower (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) :=
    targetStageTransition_isScalarTower (f := f) A i₀ j k hjk
  letI : IsScalarTower (A.SStage j.1) (A.SStage k.1)
      (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
    RestrictScalars.isScalarTower (A.SStage j.1) (A.SStage k.1)
      (A.SStage k.1 ⊗[A.SStage i₀] M₀)
  let cancel :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange
      (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) (A.SStage k.1) M₀
  -- Proof comment: tensor induction reduces equality with the cancellation map to pure tensors.
  have hmap :
      (((tailModuleMap (f := f) A i₀ hjk).liftBaseChange (A.SStage k.1)) :
        A.SStage k.1 ⊗[A.SStage j.1] (A.SStage j.1 ⊗[A.SStage i₀] M₀)
          →ₗ[A.SStage k.1] A.SStage k.1 ⊗[A.SStage i₀] M₀) =
        cancel.toLinearMap := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [cancel]
    · intro r z
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp [cancel]
      · intro s m₀
        rw [LinearMap.liftBaseChange_tmul]
        rw [tailModuleMap_tmul (f := f) A i₀ hjk s m₀]
        simp only [LinearEquiv.coe_coe]
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
        change (r * A.SMap j.1 k.1 hjk s) ⊗ₜ[A.SStage i₀] m₀ =
          (A.SMap j.1 k.1 hjk s * r) ⊗ₜ[A.SStage i₀] m₀
        rw [mul_comm]
      · intro x y hx hy
        rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  simpa [hmap] using cancel.bijective

/-- Helper for Chap10 Lemma 10 127 18: base-changing the explicit map to the limit cancels the
intermediate target stage and then applies the base-stage equivalence. -/
theorem tailModuleToLimit_liftBaseChange_bijective
    (A : DirectedFiniteTypeHomApproximation f) (i₀ : A.Λ)
    {M : Type x} [AddCommGroup M] [Module S M]
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (finalAtBase :
      let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
      S ⊗[A.SStage i₀] M₀ ≃ₗ[S] M)
    (j : Set.Ici i₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
    let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
    let _ : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
    let _ : IsScalarTower (A.SStage i₀) (A.SStage j.1) S :=
      targetStageLimit_isScalarTower (f := f) A i₀ j
    let _ : IsScalarTower (A.SStage j.1) S M :=
      RestrictScalars.isScalarTower (A.SStage j.1) S M
    Function.Bijective
      (((tailModuleToLimit (f := f) A i₀ finalAtBase j).liftBaseChange S) :
        S ⊗[A.SStage j.1] (A.SStage j.1 ⊗[A.SStage i₀] M₀) →ₗ[S] M) := by
  letI : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  letI : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
  letI : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
  letI : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
  letI : Module (A.SStage i₀) S := Algebra.toModule
  letI : Module (A.SStage j.1) S := Module.compHom S (A.targetStageToLimit j.1)
  letI : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
  letI : IsScalarTower (A.SStage i₀) (A.SStage j.1) S :=
    targetStageLimit_isScalarTower (f := f) A i₀ j
  letI : IsScalarTower (A.SStage j.1) S M :=
    RestrictScalars.isScalarTower (A.SStage j.1) S M
  let cancel :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (A.SStage i₀) (A.SStage j.1) S S M₀).trans finalAtBase
  -- Proof comment: tensor induction reduces equality with the final cancellation map to pure
  -- tensors, where `finalAtBase` is `S`-linear.
  have hmap :
      (((tailModuleToLimit (f := f) A i₀ finalAtBase j).liftBaseChange S) :
        S ⊗[A.SStage j.1] (A.SStage j.1 ⊗[A.SStage i₀] M₀) →ₗ[S] M) =
        cancel.toLinearMap := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [cancel]
    · intro r z
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp [cancel]
      · intro s m₀
        rw [LinearMap.liftBaseChange_tmul]
        rw [tailModuleToLimit_tmul (f := f) A i₀ finalAtBase j s m₀]
        simp only [LinearEquiv.coe_coe]
        change r • finalAtBase (A.targetStageToLimit j.1 s ⊗ₜ[A.SStage i₀] m₀) =
          finalAtBase
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange
              (A.SStage i₀) (A.SStage j.1) S S M₀)
                (r ⊗ₜ[A.SStage j.1] (s ⊗ₜ[A.SStage i₀] m₀)))
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
        calc
          r • finalAtBase (A.targetStageToLimit j.1 s ⊗ₜ[A.SStage i₀] m₀) =
              finalAtBase (r • (A.targetStageToLimit j.1 s ⊗ₜ[A.SStage i₀] m₀)) := by
            rw [map_smul]
          _ = finalAtBase ((r * A.targetStageToLimit j.1 s) ⊗ₜ[A.SStage i₀] m₀) := by
            rfl
          _ = finalAtBase ((A.targetStageToLimit j.1 s * r) ⊗ₜ[A.SStage i₀] m₀) := by
            rw [mul_comm]
      · intro x y hx hy
        rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  simpa [hmap] using cancel.bijective

/-- Helper for Chap10 Lemma 10 127 18: scalar extension from the descended base module is finite
after wrapping the tensor stage in `ULift`. -/
theorem tailULiftModuleStageFinite
    (A : DirectedFiniteTypeHomApproximation.{u, v, w} f) (i₀ : A.Λ)
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    [Module.FinitePresentation (A.SStage i₀) M₀]
    (j : Set.Ici i₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    Module.Finite (A.SStage j.1)
      (ULift.{y, v} (A.SStage j.1 ⊗[A.SStage i₀] M₀)) := by
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  -- Proof comment: finite presentation gives finite generation, scalar extension preserves it,
  -- and `ULift.moduleEquiv` transports the finite generating set across the universe bridge.
  let hRaw :
      Module.Finite (A.SStage j.1) (A.SStage j.1 ⊗[A.SStage i₀] M₀) :=
    Module.Finite.base_change (A.SStage i₀) (A.SStage j.1) M₀
  exact Module.Finite.equiv
    (ULift.moduleEquiv.symm :
      (A.SStage j.1 ⊗[A.SStage i₀] M₀) ≃ₗ[A.SStage j.1]
        ULift.{y, v} (A.SStage j.1 ⊗[A.SStage i₀] M₀))

/-- Helper for Chap10 Lemma 10 127 18: the public transition map is the raw tensor transition
transported through `ULift.moduleEquiv`. -/
noncomputable def tailULiftModuleMap
    (A : DirectedFiniteTypeHomApproximation.{u, v, w} f) (i₀ : A.Λ)
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
    let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
    let _ : Module (A.SStage j.1) (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
      Module.compHom (A.SStage k.1 ⊗[A.SStage i₀] M₀) (A.SMap j.1 k.1 hjk)
    ULift.{y, v} (A.SStage j.1 ⊗[A.SStage i₀] M₀) →ₗ[A.SStage j.1]
      ULift.{y, v} (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
  let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
  let _ : Module (A.SStage j.1) (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
    Module.compHom (A.SStage k.1 ⊗[A.SStage i₀] M₀) (A.SMap j.1 k.1 hjk)
  (ULift.moduleEquiv.symm :
      (A.SStage k.1 ⊗[A.SStage i₀] M₀) ≃ₗ[A.SStage j.1]
        ULift.{y, v} (A.SStage k.1 ⊗[A.SStage i₀] M₀)).toLinearMap.comp
    ((tailModuleMap (f := f) A i₀ hjk).comp
      (ULift.moduleEquiv :
        ULift.{y, v} (A.SStage j.1 ⊗[A.SStage i₀] M₀) ≃ₗ[A.SStage j.1]
          (A.SStage j.1 ⊗[A.SStage i₀] M₀)).toLinearMap)

/-- Helper for Chap10 Lemma 10 127 18: the transported transition has the same pure tensor
formula as the raw tensor transition, wrapped in `ULift`. -/
theorem tailULiftModuleMap_tmul
    (A : DirectedFiniteTypeHomApproximation.{u, v, w} f) (i₀ : A.Λ)
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    {j k : Set.Ici i₀} (hjk : j ≤ k) (s : A.SStage j.1) (m : M₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
    let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
    let _ : Module (A.SStage j.1) (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
      Module.compHom (A.SStage k.1 ⊗[A.SStage i₀] M₀) (A.SMap j.1 k.1 hjk)
    tailULiftModuleMap (f := f) A i₀ hjk
      (ULift.up (s ⊗ₜ[A.SStage i₀] m)) =
      ULift.up (A.SMap j.1 k.1 hjk s ⊗ₜ[A.SStage i₀] m) := by
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
  let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.SMap j.1 k.1 hjk).toAlgebra
  let _ : Module (A.SStage j.1) (A.SStage k.1 ⊗[A.SStage i₀] M₀) :=
    Module.compHom (A.SStage k.1 ⊗[A.SStage i₀] M₀) (A.SMap j.1 k.1 hjk)
  -- Proof comment: applying `ULift.down` exposes exactly the raw transition formula.
  ext
  simpa [tailULiftModuleMap] using tailModuleMap_tmul (f := f) A i₀ hjk s m

/-- Helper for Chap10 Lemma 10 127 18: the public map to the limit is the raw final map
precomposed with `ULift.moduleEquiv`. -/
noncomputable def tailULiftModuleToLimit
    (A : DirectedFiniteTypeHomApproximation.{u, v, w} f) (i₀ : A.Λ)
    {M : Type x} [AddCommGroup M] [Module S M]
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (finalAtBase :
      let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
      S ⊗[A.SStage i₀] M₀ ≃ₗ[S] M)
    (j : Set.Ici i₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
    let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
    let _ : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
    ULift.{y, v} (A.SStage j.1 ⊗[A.SStage i₀] M₀) →ₗ[A.SStage j.1] M :=
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
  let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
  let _ : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
  (tailModuleToLimit (f := f) A i₀ finalAtBase j).comp
    (ULift.moduleEquiv :
      ULift.{y, v} (A.SStage j.1 ⊗[A.SStage i₀] M₀) ≃ₗ[A.SStage j.1]
        (A.SStage j.1 ⊗[A.SStage i₀] M₀)).toLinearMap

/-- Helper for Chap10 Lemma 10 127 18: the transported final map evaluates on pure tensors by
sending the stage scalar to the limit and then applying the base-stage equivalence. -/
theorem tailULiftModuleToLimit_tmul
    (A : DirectedFiniteTypeHomApproximation.{u, v, w} f) (i₀ : A.Λ)
    {M : Type x} [AddCommGroup M] [Module S M]
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (finalAtBase :
      let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
      S ⊗[A.SStage i₀] M₀ ≃ₗ[S] M)
    (j : Set.Ici i₀) (s : A.SStage j.1) (m : M₀) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
    let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
    let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
    let _ : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
    tailULiftModuleToLimit (f := f) A i₀ finalAtBase j
      (ULift.up (s ⊗ₜ[A.SStage i₀] m)) =
      finalAtBase (A.targetStageToLimit j.1 s ⊗ₜ[A.SStage i₀] m) := by
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
  let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
  let _ : Module (A.SStage j.1) M := Module.compHom M (A.targetStageToLimit j.1)
  -- Proof comment: the `ULift` wrapper disappears under the equivalence, leaving the raw final
  -- map computation.
  simpa [tailULiftModuleToLimit] using tailModuleToLimit_tmul (f := f) A i₀ finalAtBase j s m

/-- Helper for Lemma 10.127.18: once a finitely presented module has descended to one target stage
of the ring approximation, the remaining source-faithful step is to pass to the tail and define
each later stage by scalar extension from that single descended module. -/
theorem tail_module_system_from_descended_stage
    (A : DirectedFiniteTypeHomApproximation.{u, v, w} f)
    (hA : A.HasBijectiveBaseChangeTransitions)
    {M : Type x} [AddCommGroup M] [Module S M]
    (i₀ : A.Λ)
    {M₀ : Type v} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    [Module.FinitePresentation (A.SStage i₀) M₀]
    (eM :
      let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.SMap i j h)
      let _ : Module D M := Module.compHom M A.colimitTarget.toRingHom
      D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) :
    Nonempty (DirectedFinitePresentationModuleApproximation.{u, v, x, v, w} f M) := by
  let B := tailFiniteTypeHomApproximation (f := f) A i₀
  have hB :
      B.HasBijectiveBaseChangeTransitions :=
    tailFiniteTypeHomApproximation_hasBijectiveBaseChangeTransitions (f := f) A hA i₀
  obtain ⟨finalAtBase⟩ :=
    targetColimit_transport_descendedModuleEquiv (f := f) (M := M) A i₀ eM
  -- Proof comment: after restricting to the tail, every module stage is the scalar extension of
  -- the single descended module `M₀` from the base target stage `i₀`.
  let C : DirectedFinitePresentationModuleApproximation.{u, v, x, v, w} f M :=
    { toDirectedFiniteTypeHomApproximation := B
      hasBijectiveBaseChangeTransitions := hB
      moduleStage := fun j : B.Λ ↦
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
        A.SStage j.1 ⊗[A.SStage i₀] M₀
      instAddCommGroupModuleStage := fun j ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
        exact show AddCommGroup (A.SStage j.1 ⊗[A.SStage i₀] M₀) from inferInstance
      instModuleModuleStage := fun j ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
        exact show Module (A.SStage j.1) (A.SStage j.1 ⊗[A.SStage i₀] M₀) from inferInstance
      instModuleFiniteModuleStage := fun j ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
        let _ : Module.Finite (A.SStage i₀) M₀ := inferInstance
        exact show Module.Finite (A.SStage j.1) (A.SStage j.1 ⊗[A.SStage i₀] M₀) from
          Module.Finite.base_change (A.SStage i₀) (A.SStage j.1) M₀
      moduleMap := fun {j k} hjk ↦ by
        simpa [B, tailFiniteTypeHomApproximation] using tailModuleMap (f := f) A i₀ hjk
      moduleMap_id := fun j m ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
        -- Proof comment: on pure tensors the identity transition is the directed-system
        -- identity map, and tensor induction extends this to all elements.
        refine TensorProduct.induction_on m ?_ ?_ ?_
        · simp [B, tailFiniteTypeHomApproximation]
        · intro s m₀
          simpa [B, tailFiniteTypeHomApproximation,
            DirectedSystem.map_self (f := fun a b h ↦ A.SMap a b h) s]
            using tailModuleMap_tmul (f := f) A i₀ (j := j) (k := j) le_rfl s m₀
        · intro x y hx hy
          rw [map_add, hx, hy]
      moduleMap_comp := fun {j k l} hjk hkl m ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
        let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
        let _ : Algebra (A.SStage i₀) (A.SStage l.1) := (A.SMap i₀ l.1 l.2).toAlgebra
        -- Proof comment: compatibility of the module maps is just compatibility of the target
        -- directed-system transition maps on the left tensor factor.
        refine TensorProduct.induction_on m ?_ ?_ ?_
        · simp [B, tailFiniteTypeHomApproximation]
        · intro s m₀
          calc
            (tailModuleMap (f := f) A i₀ hkl)
                ((tailModuleMap (f := f) A i₀ hjk) (s ⊗ₜ[A.SStage i₀] m₀)) =
                (tailModuleMap (f := f) A i₀ hkl)
                  (A.SMap j.1 k.1 hjk s ⊗ₜ[A.SStage i₀] m₀) := by
              rw [tailModuleMap_tmul (f := f) A i₀ hjk s m₀]
            _ = A.SMap k.1 l.1 hkl (A.SMap j.1 k.1 hjk s) ⊗ₜ[A.SStage i₀] m₀ := by
              rw [tailModuleMap_tmul (f := f) A i₀ hkl
                (A.SMap j.1 k.1 hjk s) m₀]
            _ = A.SMap j.1 l.1 (hjk.trans hkl) s ⊗ₜ[A.SStage i₀] m₀ := by
              rw [DirectedSystem.map_map (f := fun a b h ↦ A.SMap a b h) hjk hkl s]
            _ = (tailModuleMap (f := f) A i₀ (hjk.trans hkl))
                (s ⊗ₜ[A.SStage i₀] m₀) := by
              rw [tailModuleMap_tmul (f := f) A i₀ (hjk.trans hkl) s m₀]
        · intro x y hx hy
          rw [map_add, map_add, map_add, hx, hy]
      moduleToLimit := fun j ↦ by
        simpa [B, tailFiniteTypeHomApproximation, tailTargetStageToLimit_eq (f := f) A i₀ j]
          using tailModuleToLimit (f := f) A i₀ finalAtBase j
      moduleToLimit_comp := fun {j k} hjk m ↦ by
        let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.SMap i₀ j.1 j.2).toAlgebra
        let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.SMap i₀ k.1 k.2).toAlgebra
        let _ : Algebra (A.SStage i₀) S := (A.targetStageToLimit i₀).toAlgebra
        let _ : Algebra (A.SStage j.1) S := (A.targetStageToLimit j.1).toAlgebra
        let _ : Algebra (A.SStage k.1) S := (A.targetStageToLimit k.1).toAlgebra
        -- Proof comment: the maps to the limit agree because the target cocone map from `j`
        -- factors through the transition `j ≤ k`.
        refine TensorProduct.induction_on m ?_ ?_ ?_
        · simp [B, tailFiniteTypeHomApproximation]
        · intro s m₀
          have hcompat :
              A.targetStageToLimit k.1 (A.SMap j.1 k.1 hjk s) =
                A.targetStageToLimit j.1 s := by
            exact congrFun (congrArg DFunLike.coe
              (targetStageToLimit_comp_SMap (f := f) A hjk)) s
          calc
            (tailModuleToLimit (f := f) A i₀ finalAtBase k)
                ((tailModuleMap (f := f) A i₀ hjk) (s ⊗ₜ[A.SStage i₀] m₀)) =
                (tailModuleToLimit (f := f) A i₀ finalAtBase k)
                  (A.SMap j.1 k.1 hjk s ⊗ₜ[A.SStage i₀] m₀) := by
              rw [tailModuleMap_tmul (f := f) A i₀ hjk s m₀]
            _ = finalAtBase
                (A.targetStageToLimit k.1 (A.SMap j.1 k.1 hjk s) ⊗ₜ[A.SStage i₀] m₀) := by
              rw [tailModuleToLimit_tmul (f := f) A i₀ finalAtBase k
                (A.SMap j.1 k.1 hjk s) m₀]
            _ = finalAtBase (A.targetStageToLimit j.1 s ⊗ₜ[A.SStage i₀] m₀) := by
              rw [hcompat]
            _ = (tailModuleToLimit (f := f) A i₀ finalAtBase j)
                (s ⊗ₜ[A.SStage i₀] m₀) := by
              rw [tailModuleToLimit_tmul (f := f) A i₀ finalAtBase j s m₀]
        · intro x y hx hy
          rw [map_add, map_add, map_add, hx, hy]
      transitionBaseChangeMap_bijective := fun {j k} hjk ↦ by
        -- Proof comment: the field is the abstract cancellation lemma specialized to the tail.
        simpa [B, tailFiniteTypeHomApproximation] using
          tailModuleMap_liftBaseChange_bijective (f := f) A i₀ (M₀ := M₀) hjk
      finalBaseChangeMap_bijective := fun j ↦ by
        -- Proof comment: the field is the abstract cancellation lemma specialized to the tail.
        simpa [B, tailFiniteTypeHomApproximation, tailTargetStageToLimit_eq (f := f) A i₀ j]
          using tailModuleToLimit_liftBaseChange_bijective (f := f) A i₀
            (M := M) (M₀ := M₀) finalAtBase j }
  exact Nonempty.intro C

/-- Helper for Lemma 10.127.18: a finitely presented ring map admits a directed finite-type
approximation whose stagewise base-change maps are bijective. -/
theorem exists_bijective_finitePresentation_hom_approximation
    (f : R →+* S) (hf : f.FinitePresentation) :
    ∃ A : DirectedFiniteTypeHomApproximation.{u, v, u} f, A.HasBijectiveBaseChangeTransitions := by
  -- Proof comment: the ring-side finite-presentation approximation is the preceding theorem.
  exact _root_.exists_directedFinitePresentationHomApproximation f hf

-- Proof sketch: first apply the finite-presentation approximation of the ring map `R → S` to
-- obtain a directed system `R_λ → S_λ` with finite-type stages and base-change isomorphisms on
-- the ring side. Then choose a finite presentation of `M` as an `S`-module, descend its finitely
-- many generators and relations to a sufficiently large stage, define `M_λ` by the descended
-- presentation, and enlarge stages so that the transition and limit base-change maps become the
-- required isomorphisms.
/-- Chap10 Lemma 10 127 18: if `f : R →+* S` is of finite presentation and `M` is a finitely presented
`S`-module, then there is a directed system of ring maps `R_λ → S_λ` with finite stage modules
`M_λ` such that the ring-map colimit is `f`, the module colimit is `M`, each `R_λ` is of finite
type over `ℤ`, each `S_λ` is of finite type over `R_λ`, each `M_λ` is finite over `S_λ`, the
canonical maps `S_λ ⊗[R_λ] R_μ → S_μ` and `M_λ ⊗[S_λ] S_μ → M_μ` are isomorphisms for `λ ≤ μ`,
and in particular `M ≅ M_λ ⊗[S_λ] S ≅ R ⊗[R_λ] M_λ` for every stage `λ`. -/
@[stacks 00R1]
theorem exists_directedFinitePresentationModuleApproximation
    {M : Type x} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    (hf : f.FinitePresentation) :
    Nonempty (DirectedFinitePresentationModuleApproximation.{u, v, x, v, u} f M) := by
  obtain ⟨A, hA⟩ := exists_bijective_finitePresentation_hom_approximation (f := f) hf
  obtain ⟨i₀, M₀, _, _, _, ⟨eM⟩⟩ :=
    descend_module_to_target_stage (f := f) (A := A) (M := M)
  -- Proof comment: after the ring approximation and module descent are available, the tail
  -- construction packages the descended stage module into the requested approximation.
  exact tail_module_system_from_descended_stage (f := f) (A := A) hA (M := M) i₀ eM

end DirectedFinitePresentationModuleApproximation
