import stacks_project.Chap10.Lemma_10_127_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

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

/-
Domain sampling:
* Primary domain: directed approximation systems for finitely presented commutative ring maps
  together with descended finite stage modules.
* Owner declarations inspected in this domain:
  - `DirectedLocalEssFinitePresentationModuleApproximation`
  - `DirectedFiniteTypeHomApproximation`
  - `DirectedFiniteTypeHomApproximation.HasBijectiveBaseChangeTransitions`
  - `DirectedFinitePresentationModuleApproximation`
* Best owner abstraction: `DirectedFinitePresentationModuleApproximation f M`.
* Layer triage:
  - `source-facing`: `DirectedFinitePresentationModuleApproximation f M`
  - `core/canonical`: the inherited ring-approximation owner
    `DirectedFiniteTypeHomApproximation f` together with the stage-module system
  - `bridge/view`: the canonical transition, final target-side, and final source-side base-change
    equivalences derived from the owner
* Primitive vs. derived:
  - primitive data here: the inherited directed ring approximation, the stage modules, their
    finite `SStage i`-module structures, the transition maps `Mᵢ → Mⱼ`, their cocycle laws, and
    the compatible maps `Mᵢ → M`
  - derived API: the inherited ring-side bijective base-change condition, the canonical tensor
    base-change maps from `LinearMap.liftBaseChange`, the resulting equivalences
    `A.transitionBaseChange h`, `A.finalBaseChange i`, `A.finalBaseChangeSource i`, and the
    `RStage i`-module structure by restriction of scalars
-/

/-- A directed approximation of a finitely presented `S`-module along a finitely presented ring
map `R → S`, with finite stage modules whose target-side base changes recover the later stages and
the limit module. -/
structure DirectedFinitePresentationModuleApproximation
    (f : R →+* S) (M : Type x) [AddCommGroup M] [Module S M]
    extends DirectedFiniteTypeHomApproximation f where
  hasBijectiveBaseChangeTransitions :
    toDirectedFiniteTypeHomApproximation.HasBijectiveBaseChangeTransitions
  moduleStage : Λ → Type y
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

end DirectedFinitePresentationModuleApproximation

namespace DirectedFiniteTypeHomApproximation

variable {f : R →+* S}

/-- The map from a target stage to the limit ring `S` is compatible with the corresponding source
stage map to the limit ring `R`. -/
theorem targetStageToLimit_comp_stageMap (A : DirectedFiniteTypeHomApproximation f) (i : A.Λ) :
    (A.targetStageToLimit i).comp (A.stageMap i) = f.comp (A.sourceStageToLimit i) := by
  simpa [RingHom.comp_assoc] using
    congrArg (fun g ↦ g.comp (Ring.DirectLimit.of A.RStage (fun i j h ↦ A.RMap i j h) i))
      A.colimit_comm

/-- The canonical target-stage map to `S` is an algebra map over the corresponding source stage.
-/
theorem targetStageToLimit_isScalarTower (A : DirectedFiniteTypeHomApproximation f) (i : A.Λ) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.SStage i) S := (A.targetStageToLimit i).toAlgebra
    let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
    IsScalarTower (A.RStage i) (A.SStage i) S := by
  sorry

end DirectedFiniteTypeHomApproximation

namespace DirectedFinitePresentationModuleApproximation

variable {f : R →+* S} {M : Type x} [AddCommGroup M] [Module S M]

/-- Each stage module is naturally a module over the corresponding source stage by restriction of
scalars along the stage map. -/
instance stageModuleSource
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    Module (A.RStage i) (A.moduleStage i) :=
  Module.compHom (A.moduleStage i) (A.stageMap i)

/-- The square obtained from a stage and the limiting ring map `R → S` is a pushout square. -/
theorem finalSquare_isPushout
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.SStage i) S := (A.targetStageToLimit i).toAlgebra
    let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : IsScalarTower (A.RStage i) R S := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.RStage i) (A.SStage i) S := A.targetStageToLimit_isScalarTower i
    Algebra.IsPushout (A.RStage i) R (A.SStage i) S := by
  sorry

/-- The source-side limit base change is derived from the limiting pushout square together with
the target-side base change recovering `M`. -/
noncomputable def finalBaseChangeSource
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Module R M := Module.compHom M f
    let _ : Module (A.RStage i) (A.moduleStage i) := Module.compHom (A.moduleStage i) (A.stageMap i)
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    R ⊗[A.RStage i] A.moduleStage i ≃ₗ[R] M :=
  let _ : Module R M := Module.compHom M f
  let _ : Module (A.RStage i) (A.moduleStage i) := Module.compHom (A.moduleStage i) (A.stageMap i)
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.SStage i) S := (A.targetStageToLimit i).toAlgebra
  let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : IsScalarTower (A.RStage i) R S := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (A.RStage i) (A.SStage i) S := A.targetStageToLimit_isScalarTower i
  let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) := by
    refine ⟨?_⟩
    intro r s m
    simpa [Algebra.smul_def] using mul_smul ((A.stageMap i) r) s m
  let _ : Algebra.IsPushout (A.RStage i) R (A.SStage i) S := A.finalSquare_isPushout i
  let _ : Module R (S ⊗[A.SStage i] A.moduleStage i) :=
    Module.compHom (S ⊗[A.SStage i] A.moduleStage i) f
  let e : S ⊗[A.SStage i] A.moduleStage i ≃ₗ[S] M := A.finalBaseChange i
  let finalBaseChangeR : S ⊗[A.SStage i] A.moduleStage i ≃ₗ[R] M :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        change e ((f r) • x) = (f r) • (e x)
        exact e.toLinearMap.map_smul (f r) x }
  (Algebra.IsPushout.cancelBaseChange
      (A.RStage i) R (A.SStage i) S (A.moduleStage i)).symm.trans
    finalBaseChangeR

end DirectedFinitePresentationModuleApproximation

section

variable (f : R →+* S)

-- Proof sketch: first apply the finite-presentation approximation of the ring map `R → S` to
-- obtain a directed system `R_λ → S_λ` with finite-type stages and base-change isomorphisms on
-- the ring side. Then choose a finite presentation of `M` as an `S`-module, descend its finitely
-- many generators and relations to a sufficiently large stage, define `M_λ` by the descended
-- presentation, and enlarge stages so that the transition and limit base-change maps become the
-- required isomorphisms.
/-- Lemma 10.127.18: if `f : R →+* S` is of finite presentation and `M` is a finitely presented
`S`-module, then there is a directed system of ring maps `R_λ → S_λ` with finite stage modules
`M_λ` such that the ring-map colimit is `f`, the module colimit is `M`, each `R_λ` is of finite
type over `ℤ`, each `S_λ` is of finite type over `R_λ`, each `M_λ` is finite over `S_λ`, the
canonical maps `S_λ ⊗[R_λ] R_μ → S_μ` and `M_λ ⊗[S_λ] S_μ → M_μ` are isomorphisms for `λ ≤ μ`,
and in particular `M ≅ M_λ ⊗[S_λ] S ≅ R ⊗[R_λ] M_λ` for every stage `λ`. -/
theorem exists_directedFinitePresentationModuleApproximation
    {M : Type x} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    (hf : f.FinitePresentation) :
    Nonempty (DirectedFinitePresentationModuleApproximation f M) := sorry

end
