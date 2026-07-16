import stacks_proof.stacks_project.Chap10.Lemma_10_127_8
import stacks_proof.stacks_project.Chap10.Lemma_10_127_18
import stacks_proof.stacks_project.Chap10.Lemma_10_128_3
import stacks_proof.stacks_project.Chap10.Theorem_10_129_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u u₀ v w y z

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

section

variable (f : R →+* S)
variable (M : Type w) [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]

namespace DirectedFinitePresentationModuleApproximation

/-- Helper for Chap10 Lemma 10 168 1: a finite type `ℤ`-algebra can be represented in any
requested universe by `Shrink`. -/
lemma finiteTypeIntCastRingHom_small {A : Type u} [CommRing A]
    (h : (Int.castRingHom A).FiniteType) : Small.{u₀} A := by
  -- Proof comment: a finite type algebra is a quotient of a finite polynomial algebra, hence a
  -- quotient of a type in the requested universe.
  let _ : Algebra.FiniteType ℤ A := RingHom.finiteType_algebraMap.mp h
  obtain ⟨_n, _φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType ℤ A)
  exact small_of_surjective hφ

/-- Helper for Chap10 Lemma 10 168 1: a finite type `ℤ`-algebra map is finitely presented. -/
lemma finiteTypeIntCastRingHom_finitePresentation {A : Type u} [CommRing A]
    (h : (Int.castRingHom A).FiniteType) :
    (Int.castRingHom A).FinitePresentation := by
  -- Proof comment: `ℤ` is Noetherian, so finite type over `ℤ` upgrades to finite presentation.
  exact (RingHom.FinitePresentation.of_finiteType).mp h

/-- Helper for Chap10 Lemma 10 168 1: a stage module over `A.SStage i` is also a module over
`A.RStage i` by restriction along the stage map. -/
instance instSourceModuleStage (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    Module (A.RStage i) (A.moduleStage i) :=
  -- Proof comment: the source action is the canonical pullback of the target-stage action.
  Module.compHom (A.moduleStage i) (A.stageMap i)

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: source stages in the directed approximation are
Noetherian rings. -/
lemma stageSource_isNoetherianRing (A : DirectedFinitePresentationModuleApproximation f M)
    (i : A.Λ) : IsNoetherianRing (A.RStage i) := by
  -- Proof comment: each source stage is finite type over the Noetherian ring `ℤ`.
  let _ : Algebra.FiniteType ℤ (A.RStage i) :=
    RingHom.finiteType_algebraMap.mp (A.source_finiteType i)
  exact Algebra.FiniteType.isNoetherianRing ℤ (A.RStage i)

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: source stages of the approximation are shrinkable to the
base-model universe. -/
lemma stageSource_small (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    Small.{u₀} (A.RStage i) := by
  -- Proof comment: the stored finite-type `ℤ`-algebra structure supplies the quotient
  -- presentation needed by `finiteTypeIntCastRingHom_small`.
  exact finiteTypeIntCastRingHom_small (A.source_finiteType i)

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: a finite module over a small commutative ring is small in
the same universe. -/
lemma finiteModule_small_of_ring_small
    {A : Type v} [CommRing A] {N : Type y} [AddCommGroup N] [Module A N]
    [Small.{w} A] [Module.Finite A N] : Small.{w} N := by
  classical
  -- Proof comment: choose finitely many module generators and use the standard finite-free
  -- parametrization map onto the module.
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := N)
  have hsurj : Function.Surjective (Module.piEquiv (Fin n) A N s) := by
    rw [Module.surjective_piEquiv_apply_iff]
    exact hs
  exact small_of_surjective hsurj

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: target stages of the approximation are small in any
requested universe. -/
lemma stageTarget_small (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    Small.{w} (A.SStage i) := by
  -- Proof comment: finite type over the source stage and finite type of the source over `ℤ`
  -- compose to make the target stage finite type over `ℤ`.
  have hcomp : ((A.stageMap i).comp (Int.castRingHom (A.RStage i))).FiniteType :=
    (A.target_finiteType i).comp (A.source_finiteType i)
  have hcast : (A.stageMap i).comp (Int.castRingHom (A.RStage i)) =
      Int.castRingHom (A.SStage i) := by
    ext n
    simp
  exact finiteTypeIntCastRingHom_small (hcast ▸ hcomp)

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: finite target-stage modules are small in any requested
universe. -/
lemma stageModule_small (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    Small.{w} (A.moduleStage i) := by
  -- Proof comment: the target stage is small and the stored stage module is finite over it.
  letI : Small.{w} (A.SStage i) := stageTarget_small (f := f) (M := M) A i
  exact finiteModule_small_of_ring_small (A := A.SStage i) (N := A.moduleStage i)

/-- Helper for Chap10 Lemma 10 168 1: stage maps and stage modules are finitely presented. -/
lemma stageFinitePresentationData (A : DirectedFinitePresentationModuleApproximation f M)
    (i : A.Λ) :
    (A.stageMap i).FinitePresentation ∧
      Module.FinitePresentation (A.SStage i) (A.moduleStage i) := by
  -- Proof comment: Noetherianity of the source upgrades the finite-type stage map to finite
  -- presentation.
  have hsource : IsNoetherianRing (A.RStage i) := stageSource_isNoetherianRing (f := f) (M := M) A i
  have hstage : (A.stageMap i).FinitePresentation := by
    let _ : IsNoetherianRing (A.RStage i) := hsource
    exact (RingHom.FinitePresentation.of_finiteType).mp (A.target_finiteType i)
  -- Proof comment: the target stage is finite type over a Noetherian source stage, hence
  -- Noetherian; finite modules over it are finitely presented.
  have htarget : IsNoetherianRing (A.SStage i) := by
    let _ : IsNoetherianRing (A.RStage i) := hsource
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra.FiniteType (A.RStage i) (A.SStage i) :=
      RingHom.finiteType_algebraMap.mp (A.target_finiteType i)
    exact Algebra.FiniteType.isNoetherianRing (A.RStage i) (A.SStage i)
  have hmodule : Module.FinitePresentation (A.SStage i) (A.moduleStage i) := by
    let _ : IsNoetherianRing (A.SStage i) := htarget
    exact Module.finitePresentation_of_finite (A.SStage i) (A.moduleStage i)
  exact ⟨hstage, hmodule⟩

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the stage square remains compatible after passing to the
source and target colimits. -/
lemma stageToLimit_comp_stageMap
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    (A.targetStageToLimit i).comp (A.stageMap i) = f.comp (A.sourceStageToLimit i) := by
  ext x
  -- Proof comment: evaluate the stored colimit-commutativity square on the source-stage
  -- generator represented by `x`.
  have h := congrArg
    (fun g : Ring.DirectLimit A.RStage (fun i j h ↦ A.RMap i j h) →+* S =>
      g (Ring.DirectLimit.of A.RStage (fun i j h ↦ A.RMap i j h) i x))
    A.colimit_comm
  simpa [DirectedFiniteTypeHomApproximation.sourceStageToLimit,
    DirectedFiniteTypeHomApproximation.targetStageToLimit, RingHom.comp_apply,
    Ring.DirectLimit.map_apply_of] using h

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the transition base-change equivalence sends a pure tensor
to the scalar multiple of the transition map on the stage module. -/
lemma transitionBaseChange_tmul
    (A : DirectedFinitePresentationModuleApproximation f M) {i j : A.Λ} (hij : i ≤ j)
    (s : A.SStage j) (m : A.moduleStage i) :
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.SMap i j hij).toAlgebra
    A.transitionBaseChange hij (s ⊗ₜ[A.SStage i] m) = s • A.moduleMap hij m := by
  let _ : Algebra (A.SStage i) (A.SStage j) := (A.SMap i j hij).toAlgebra
  -- Proof comment: unfold the equivalence to its bijective linear map and use the standard
  -- pure-tensor computation for `liftBaseChange`.
  simp [transitionBaseChange, transitionBaseChangeMap]

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the final base-change equivalence sends a pure tensor to
the scalar multiple of the map from a stage module to the limiting module. -/
lemma finalBaseChange_tmul
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ)
    (s : S) (m : A.moduleStage i) :
    let _ : Algebra (A.SStage i) S := (A.targetStageToLimit i).toAlgebra
    A.finalBaseChange i (s ⊗ₜ[A.SStage i] m) = s • A.moduleToLimit i m := by
  let _ : Algebra (A.SStage i) S := (A.targetStageToLimit i).toAlgebra
  -- Proof comment: the final equivalence is the bijective lift-base-change map, so its value on
  -- pure tensors is the usual scalar action on the image in the limit module.
  simp [finalBaseChange, finalBaseChangeMap]

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the target-stage map is compatible with the source-stage
algebra structure induced through the limit ring. -/
lemma targetStageToLimitAlgHom_commutes
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) (r : A.RStage i) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
    A.targetStageToLimit i (algebraMap (A.RStage i) (A.SStage i) r) =
      algebraMap (A.RStage i) S r := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
  -- Proof comment: this is exactly the stored compatibility square, evaluated at the chosen
  -- source-stage element.
  exact RingHom.congr_fun (stageToLimit_comp_stageMap (f := f) (M := M) A i) r

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the target-stage-to-limit map as an algebra hom over the
matching source stage. -/
noncomputable def targetStageToLimitAlgHom
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
    A.SStage i →ₐ[A.RStage i] S :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
  { toRingHom := A.targetStageToLimit i
    commutes' := targetStageToLimitAlgHom_commutes (f := f) (M := M) A i }

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the canonical final tensor map
`R ⊗[A.RStage i] A.SStage i → S`. -/
noncomputable def finalRingBaseChangeMap
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    R ⊗[A.RStage i] A.SStage i →ₐ[R] S :=
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
  let _ : IsScalarTower (A.RStage i) R S := IsScalarTower.of_algebraMap_eq' rfl
  Algebra.TensorProduct.lift (Algebra.ofId R S)
    (targetStageToLimitAlgHom (f := f) (M := M) A i)
    fun _ _ ↦ Commute.all _ _

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the canonical final tensor map on pure tensors. -/
lemma finalRingBaseChangeMap_tmul
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ)
    (r : R) (s : A.SStage i) :
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    finalRingBaseChangeMap (f := f) (M := M) A i (r ⊗ₜ[A.RStage i] s) =
      f r * A.targetStageToLimit i s := by
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
  let _ : IsScalarTower (A.RStage i) R S := IsScalarTower.of_algebraMap_eq' rfl
  -- Proof comment: the named final map is a tensor-product lift, so its pure-tensor value is the
  -- product of the two limiting structure maps.
  simp [finalRingBaseChangeMap, targetStageToLimitAlgHom, Algebra.TensorProduct.lift_tmul,
    Algebra.ofId_apply, RingHom.algebraMap_toAlgebra]

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: on the right tensor factor, the canonical final map is the
target-stage-to-limit map. -/
lemma finalRingBaseChangeMap_includeRight
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    RingHom.comp (finalRingBaseChangeMap (f := f) (M := M) A i).toRingHom
        includeRight.toRingHom =
      A.targetStageToLimit i := by
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
  let _ : IsScalarTower (A.RStage i) R S := IsScalarTower.of_algebraMap_eq' rfl
  -- Proof comment: this is the `includeRight` computation for the tensor-product lift, with
  -- scalars restricted back from `R` to the source stage.
  exact congrArg AlgHom.toRingHom
    (Algebra.TensorProduct.lift_comp_includeRight (Algebra.ofId R S)
      (targetStageToLimitAlgHom (f := f) (M := M) A i) (fun _ _ ↦ Commute.all _ _))

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: pushing a source-tail tensor to a later source stage is
compatible with the stage base-change maps. -/
lemma stageBaseChangeMap_tail_compat
    (A : DirectedFinitePresentationModuleApproximation f M) {i j k : A.Λ}
    (hij : i ≤ j) (hjk : j ≤ k)
    (y :
      let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
      let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
      A.SStage i ⊗[A.RStage i] A.RStage j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
    let _ : Algebra (A.RStage i) (A.RStage k) := (A.RMap i k (hij.trans hjk)).toAlgebra
    let _ : Algebra (A.RStage j) (A.RStage k) := (A.RMap j k hjk).toAlgebra
    let _ : ∀ l : M2F1278P23.Up i, Algebra (A.RStage i) (A.RStage l.1) :=
      fun l ↦ (A.RMap i l.1 l.2).toAlgebra
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : M2F1278P23.StagePins A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource i :=
      { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
    A.stageBaseChangeMap (hij.trans hjk)
        (M2F1278P23.pushStage A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
          i (A.SStage i) (j := ⟨j, hij⟩) (k := ⟨k, hij.trans hjk⟩) hjk y) =
      A.SMap j k hjk (A.stageBaseChangeMap hij y) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage k) := (A.RMap i k (hij.trans hjk)).toAlgebra
  let _ : Algebra (A.RStage j) (A.RStage k) := (A.RMap j k hjk).toAlgebra
  let _ : ∀ l : M2F1278P23.Up i, Algebra (A.RStage i) (A.RStage l.1) :=
    fun l ↦ (A.RMap i l.1 l.2).toAlgebra
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : M2F1278P23.StagePins A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource i :=
    { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
  -- Proof comment: tensor induction reduces compatibility to the stored commutative square and
  -- the directed-system composition laws.
  induction y using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul xS yR =>
      change A.stageBaseChangeMap (hij.trans hjk)
          (xS ⊗ₜ[A.RStage i] A.RMap j k hjk yR) =
        A.SMap j k hjk (A.stageBaseChangeMap hij (xS ⊗ₜ[A.RStage i] yR))
      rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
      rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
      rw [map_mul]
      have hS :
          A.SMap j k hjk (A.SMap i j hij xS) =
            A.SMap i k (hij.trans hjk) xS :=
        DirectedSystem.map_map (f := fun a b h ↦ A.SMap a b h) hij hjk xS
      have hR :
          A.SMap j k hjk (A.stageMap j yR) =
            A.stageMap k (A.RMap j k hjk yR) :=
        (RingHom.congr_fun (A.comm hjk) yR).symm
      rw [hS, hR]
  | add y₁ y₂ hy₁ hy₂ =>
      simp [map_add, hy₁, hy₂]

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the canonical final tensor map agrees with the target
colimit map on tensors represented at a finite source-tail stage. -/
lemma finalRingBaseChangeMap_pushHom
    (A : DirectedFinitePresentationModuleApproximation f M) {i j : A.Λ} (hij : i ≤ j)
    (y :
      let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
      let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
      A.SStage i ⊗[A.RStage i] A.RStage j) :
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : ∀ l : M2F1278P23.Up i, Algebra (A.RStage i) (A.RStage l.1) :=
      fun l ↦ (A.RMap i l.1 l.2).toAlgebra
    let _ : M2F1278P23.StagePins A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource i :=
      { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
    finalRingBaseChangeMap (f := f) (M := M) A i
        ((Algebra.TensorProduct.comm (R := A.RStage i) (A := A.SStage i) (B := R))
          (M2F1278P23.pushHom A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
            i (A.SStage i) ⟨j, hij⟩ y)) =
      A.targetStageToLimit j (A.stageBaseChangeMap hij y) := by
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : ∀ l : M2F1278P23.Up i, Algebra (A.RStage i) (A.RStage l.1) :=
    fun l ↦ (A.RMap i l.1 l.2).toAlgebra
  let _ : M2F1278P23.StagePins A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource i :=
    { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
  -- Proof comment: tensor induction reduces the comparison to the pure-tensor formulas for
  -- `pushHom`, `stageBaseChangeMap`, and the final tensor map.
  induction y using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul xS yR =>
      change finalRingBaseChangeMap (f := f) (M := M) A i
          ((Algebra.TensorProduct.comm (R := A.RStage i) (A := A.SStage i) (B := R))
            (xS ⊗ₜ[A.RStage i] A.sourceStageToLimit j yR)) =
        A.targetStageToLimit j (A.stageBaseChangeMap hij (xS ⊗ₜ[A.RStage i] yR))
      rw [Algebra.TensorProduct.comm_tmul]
      rw [finalRingBaseChangeMap_tmul]
      rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
      rw [map_mul]
      have hleft :
          A.targetStageToLimit j (A.SMap i j hij xS) = A.targetStageToLimit i xS := by
        exact RingHom.congr_fun
          (DirectedFinitePresentationModuleApproximation.targetStageToLimit_comp_SMap
            (f := f) A.toDirectedFiniteTypeHomApproximation hij) xS
      have hright :
          A.targetStageToLimit j (A.stageMap j yR) = f (A.sourceStageToLimit j yR) := by
        exact RingHom.congr_fun (stageToLimit_comp_stageMap (f := f) (M := M) A j) yR
      rw [hleft, hright]
      ring
  | add y₁ y₂ hy₁ hy₂ =>
      simp [map_add, hy₁, hy₂]

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the canonical final tensor map is surjective. -/
lemma finalRingBaseChangeMap_surjective
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    Function.Surjective (finalRingBaseChangeMap (f := f) (M := M) A i) := by
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : ∀ l : M2F1278P23.Up i, Algebra (A.RStage i) (A.RStage l.1) :=
    fun l ↦ (A.RMap i l.1 l.2).toAlgebra
  let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
  let _ : M2F1278P23.StagePins A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource i :=
    { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
  change Function.Surjective (finalRingBaseChangeMap (f := f) (M := M) A i)
  intro s
  -- Proof comment: represent `s` at a target stage, then move to a common stage above the fixed
  -- source index `i`.
  obtain ⟨j, t, ht⟩ :=
    Ring.DirectLimit.exists_of
      (G := A.SStage) (f := fun a b h ↦ A.SMap a b h) (A.colimitTarget.symm s)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let _ : Algebra (A.RStage i) (A.RStage k) := (A.RMap i k hik).toAlgebra
  -- Proof comment: the stage base-change bijection lifts the moved target representative to a
  -- tensor over the common source stage.
  obtain ⟨y, hy⟩ :=
    (A.hasBijectiveBaseChangeTransitions hik).2 (A.SMap j k hjk t)
  refine ⟨
    (Algebra.TensorProduct.comm (R := A.RStage i) (A := A.SStage i) (B := R))
      (M2F1278P23.pushHom A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
        i (A.SStage i) ⟨k, hik⟩ y), ?_⟩
  -- Proof comment: the finite-stage bridge rewrites the final tensor map to the target colimit
  -- cocone, where compatibility with the transition from `j` to `k` closes the representative.
  rw [finalRingBaseChangeMap_pushHom (f := f) (M := M) A hik y, hy]
  have hcompat :
      A.targetStageToLimit k (A.SMap j k hjk t) = A.targetStageToLimit j t := by
    exact RingHom.congr_fun
      (DirectedFinitePresentationModuleApproximation.targetStageToLimit_comp_SMap
        (f := f) A.toDirectedFiniteTypeHomApproximation hjk) t
  rw [hcompat]
  simpa [DirectedFiniteTypeHomApproximation.targetStageToLimit, ht]
    using A.colimitTarget.apply_symm_apply s

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the canonical final tensor map is injective. -/
lemma finalRingBaseChangeMap_injective
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    Function.Injective (finalRingBaseChangeMap (f := f) (M := M) A i) := by
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : ∀ l : M2F1278P23.Up i, Algebra (A.RStage i) (A.RStage l.1) :=
    fun l ↦ (A.RMap i l.1 l.2).toAlgebra
  let _ : Algebra (A.RStage i) S := (f.comp (A.sourceStageToLimit i)).toAlgebra
  let _ : M2F1278P23.StagePins A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource i :=
    { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
  change Function.Injective (finalRingBaseChangeMap (f := f) (M := M) A i)
  rw [injective_iff_map_eq_zero]
  intro x hx
  let c : A.SStage i ⊗[A.RStage i] R ≃ₐ[A.RStage i] R ⊗[A.RStage i] A.SStage i :=
    Algebra.TensorProduct.comm (R := A.RStage i) (A := A.SStage i) (B := R)
  -- Proof comment: first represent the swapped tensor at a finite source-tail stage.
  obtain ⟨j, y, hy⟩ :=
    M2F1278P23.exists_pushHom A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
      i (A.SStage i) (c.symm x)
  have hx_rep :
      finalRingBaseChangeMap (f := f) (M := M) A i
          (c (M2F1278P23.pushHom A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
            i (A.SStage i) j y)) = 0 := by
    simpa [c, hy] using hx
  have htarget :
      A.targetStageToLimit j.1 (A.stageBaseChangeMap j.2 y) = 0 := by
    -- Proof comment: the finite-stage bridge translates the final-map zero into a target-colimit
    -- zero for the corresponding stage base-change value.
    exact
      (finalRingBaseChangeMap_pushHom (f := f) (M := M) A j.2 y).symm.trans hx_rep
  have hraw :
      Ring.DirectLimit.of A.SStage (fun a b h ↦ A.SMap a b h) j.1
          (A.stageBaseChangeMap j.2 y) = 0 := by
    apply A.colimitTarget.injective
    simpa [DirectedFiniteTypeHomApproximation.targetStageToLimit] using htarget
  -- Proof comment: direct-limit zero detection gives a later target stage where the represented
  -- stage base-change value is zero.
  obtain ⟨k, hjk, hkzero⟩ := Ring.DirectLimit.of.zero_exact hraw
  let kUp : M2F1278P23.Up i := ⟨k, j.2.trans hjk⟩
  have hbc_zero :
      A.stageBaseChangeMap (j.2.trans hjk)
          (M2F1278P23.pushStage A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
            i (A.SStage i) (j := j) (k := kUp) (show j ≤ kUp from hjk) y) = 0 := by
    rw [stageBaseChangeMap_tail_compat (f := f) (M := M) A j.2 hjk y]
    exact hkzero
  have hpush_zero :
      M2F1278P23.pushStage A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
          i (A.SStage i) (j := j) (k := kUp) (show j ≤ kUp from hjk) y = 0 := by
    -- Proof comment: the stored finite-stage base-change map is injective, so a zero image forces
    -- the source-tail tensor itself to vanish.
    exact (A.hasBijectiveBaseChangeTransitions (j.2.trans hjk)).1 (by simpa using hbc_zero)
  have hpushHom_zero :
      M2F1278P23.pushHom A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
          i (A.SStage i) j y = 0 := by
    have hcomp := AlgHom.congr_fun
      (M2F1278P23.pushHom_comp_pushStage A.RStage (fun a b h ↦ A.RMap a b h)
        A.colimitSource i (A.SStage i) (j := j) (k := kUp) (show j ≤ kUp from hjk)) y
    have hleft :
        ((M2F1278P23.pushHom A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
              i (A.SStage i) kUp).comp
            (M2F1278P23.pushStage A.RStage (fun a b h ↦ A.RMap a b h) A.colimitSource
              i (A.SStage i) (j := j) (k := kUp) (show j ≤ kUp from hjk))) y = 0 := by
      simp only [AlgHom.comp_apply]
      rw [hpush_zero, map_zero]
    exact hcomp.symm.trans hleft
  rw [hy] at hpushHom_zero
  -- Proof comment: applying the tensor-factor commutativity equivalence back to the killed
  -- swapped tensor gives the original tensor zero.
  exact c.symm.injective (by simpa using hpushHom_zero)

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: the ring-side base change from a stage source to the limit
recovers the limiting target ring. -/
lemma finalRingBaseChange (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ) :
    Nonempty
      (let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
       let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
       let _ : Algebra R S := f.toAlgebra
       { ringBaseChange : R ⊗[A.RStage i] A.SStage i ≃ₐ[R] S //
           RingHom.comp ringBaseChange.toRingHom includeRight.toRingHom =
             A.targetStageToLimit i }) := by
  let _ : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let g := finalRingBaseChangeMap (f := f) (M := M) A i
  have hg : Function.Bijective g :=
    ⟨finalRingBaseChangeMap_injective (f := f) (M := M) A i,
      finalRingBaseChangeMap_surjective (f := f) (M := M) A i⟩
  let e : R ⊗[A.RStage i] A.SStage i ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective g.toRingHom hg) (by
      intro r
      -- Proof comment: the ring equivalence is induced by the `R`-algebra hom `g`, so it
      -- preserves the `R`-algebra structure by `g.commutes`.
      exact g.commutes r)
  refine ⟨⟨e, ?_⟩⟩
  -- Proof comment: the subtype condition is precisely the right-factor computation for the
  -- canonical tensor-product lift.
  change RingHom.comp g.toRingHom includeRight.toRingHom = A.targetStageToLimit i
  exact finalRingBaseChangeMap_includeRight (f := f) (M := M) A i

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: shrinking a source stage preserves the finite type
`ℤ`-algebra structure. -/
lemma shrinkSource_finiteType
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ)
    [Small.{u₀} (A.RStage i)] :
    (Int.castRingHom (Shrink.{u₀} (A.RStage i))).FiniteType := by
  -- Proof comment: transport the finite type algebra structure along the canonical shrink
  -- algebra equivalence over `ℤ`.
  letI : Algebra ℤ (A.RStage i) := (Int.castRingHom (A.RStage i)).toAlgebra
  have hR : Algebra.FiniteType ℤ (A.RStage i) :=
    RingHom.finiteType_algebraMap.mp (A.source_finiteType i)
  have hShrink : Algebra.FiniteType ℤ (Shrink.{u₀} (A.RStage i)) :=
    Algebra.FiniteType.equiv hR (Shrink.algEquiv ℤ (A.RStage i)).symm
  exact RingHom.finiteType_algebraMap.mpr hShrink

/-- Helper for Chap10 Lemma 10 168 1: shrinking a source stage preserves finite presentation of
the stage map. -/
lemma shrinkStageMap_finitePresentation
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ)
    [Small.{u₀} (A.RStage i)] :
    ((A.stageMap i).comp (Shrink.ringEquiv (A.RStage i)).toRingHom).FinitePresentation := by
  -- Proof comment: the shrink equivalence is a finitely presented isomorphism, so composition
  -- with the finite-presentation stage map stays finitely presented.
  obtain ⟨hstage, _⟩ := stageFinitePresentationData (f := f) (M := M) A i
  have hshrink : (Shrink.ringEquiv (A.RStage i)).toRingHom.FinitePresentation := by
    refine RingHom.FinitePresentation.of_surjective _
      (Shrink.ringEquiv (A.RStage i)).surjective ?_
    have hker : RingHom.ker ((Shrink.ringEquiv (A.RStage i)).toRingHom) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot
        ((Shrink.ringEquiv (A.RStage i)).toRingHom)).1
          (Shrink.ringEquiv (A.RStage i)).injective
    rw [hker]
    exact Submodule.fg_bot
  exact hstage.comp hshrink

/-- Helper for Chap10 Lemma 10 168 1: shrinking a stage module preserves its finite presentation
over the target stage. -/
lemma shrinkStageModule_finitePresentation
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ)
    [Small.{w} (A.moduleStage i)] :
    Module.FinitePresentation (A.SStage i) (Shrink.{w} (A.moduleStage i)) := by
  -- Proof comment: finite presentation is invariant under the canonical shrink linear
  -- equivalence.
  obtain ⟨_, hmodule⟩ := stageFinitePresentationData (f := f) (M := M) A i
  letI : Module.FinitePresentation (A.SStage i) (A.moduleStage i) := hmodule
  exact Module.FinitePresentation.of_equiv
    (Shrink.linearEquiv (A.SStage i) (A.moduleStage i)).symm

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: flatness of a stage module transports through simultaneous
shrinking of the source ring and module carrier. -/
lemma shrinkStageModule_flat
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ)
    [Small.{u₀} (A.RStage i)] [Small.{w} (A.moduleStage i)]
    (hflat_i : Module.Flat (A.RStage i) (A.moduleStage i)) :
    let stageMap : Shrink.{u₀} (A.RStage i) →+* A.SStage i :=
      (A.stageMap i).comp (Shrink.ringEquiv (A.RStage i)).toRingHom
    let _ : Module (Shrink.{u₀} (A.RStage i)) (Shrink.{w} (A.moduleStage i)) :=
      Module.compHom (Shrink.{w} (A.moduleStage i)) stageMap
    Module.Flat (Shrink.{u₀} (A.RStage i)) (Shrink.{w} (A.moduleStage i)) := by
  let R₀ := Shrink.{u₀} (A.RStage i)
  let M₀ := Shrink.{w} (A.moduleStage i)
  let stageMap : R₀ →+* A.SStage i :=
    (A.stageMap i).comp (Shrink.ringEquiv (A.RStage i)).toRingHom
  letI : Module R₀ M₀ := Module.compHom M₀ stageMap
  letI : Algebra R₀ (A.RStage i) := (Shrink.ringEquiv (A.RStage i)).toRingHom.toAlgebra
  letI : Module R₀ (A.moduleStage i) :=
    Module.compHom (A.moduleStage i) (Shrink.ringEquiv (A.RStage i)).toRingHom
  letI : IsScalarTower R₀ (A.RStage i) (A.moduleStage i) :=
    RestrictScalars.isScalarTower R₀ (A.RStage i) (A.moduleStage i)
  have hflat_base : Module.Flat R₀ (A.RStage i) := by
    -- Proof comment: the shrink ring equivalence identifies the base ring with its source stage.
    exact Module.Flat.of_linearEquiv
      (Module.compHom.toLinearEquiv (Shrink.ringEquiv (A.RStage i))).symm
  have hflat_module : Module.Flat R₀ (A.moduleStage i) := by
    -- Proof comment: compose flatness along the shrink equivalence and the selected stage-flat
    -- module.
    letI : Module.Flat R₀ (A.RStage i) := hflat_base
    letI : Module.Flat (A.RStage i) (A.moduleStage i) := hflat_i
    exact Module.Flat.trans R₀ (A.RStage i) (A.moduleStage i)
  -- Proof comment: transport the resulting flat module across the shrink linear equivalence.
  letI : Module.Flat R₀ (A.moduleStage i) := hflat_module
  exact Module.Flat.of_linearEquiv (Shrink.linearEquiv R₀ (A.moduleStage i))

omit [Module.FinitePresentation S M] in
/-- Helper for Chap10 Lemma 10 168 1: if every prime of the target lies in
`Module.flatOverBaseLocus R S M`, then `M` is flat over the base ring `R`. -/
lemma flat_of_forall_mem_flatOverBaseLocus
    [Algebra R S] [Module R M] [IsScalarTower R S M]
    (h : ∀ q : PrimeSpectrum S, q ∈ Module.flatOverBaseLocus R S M) :
    Module.Flat R M := by
  -- Proof comment: the flat-locus membership supplies flatness after every prime localization of
  -- the target, and the standard maximal-localization criterion recovers global flatness.
  apply Module.flat_of_isLocalized_maximal
    (R := R) (S := S) (M := M)
    (Mₚ := fun P _ ↦ LocalizedModule.AtPrime P M)
    (f := fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M)
  intro P hP
  exact (Module.mem_flatOverBaseLocus R S M ⟨P, hP.isPrime⟩).1 (h ⟨P, hP.isPrime⟩)

/-- Helper for Chap10 Lemma 10 168 1: flatness of the limiting module descends to one stage of a
directed finite-presentation module approximation. -/
lemma exists_flat_stage_of_flat_limit
    (A : DirectedFinitePresentationModuleApproximation f M)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ i : A.Λ, Module.Flat (A.RStage i) (A.moduleStage i) := by
  -- TODO: prove the genuine finite-presentation flatness descent for the pair `(S_i, M_i)`.
  -- Route correction: the previously planned helper claiming that `A.moduleStage i` is finitely
  -- presented as an `A.RStage i`-module is false for polynomial stage algebras; the descent must
  -- use finite presentation of the algebra/module pair, not finite presentation of the restricted
  -- source module.
  sorry

/-- Helper for Chap10 Lemma 10 168 1: a flat approximation stage already gives the finite
presentation model when no source-universe shrink is required. -/
lemma flatFinitePresentationStageData
    (A : DirectedFinitePresentationModuleApproximation.{u, v, w, y, z} f M) (i : A.Λ)
    (hflat_i : Module.Flat (A.RStage i) (A.moduleStage i)) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (r : R₀ →+* R)
      (_ : (Int.castRingHom R₀).FiniteType) (S₀ : Type v) (_ : CommRing S₀)
      (stageMap : R₀ →+* S₀) (M₀ : Type (max v y)) (_ : AddCommGroup M₀)
      (_ : Module S₀ M₀),
      stageMap.FinitePresentation ∧
        Module.FinitePresentation S₀ M₀ ∧
        (let _ : Module R₀ M₀ := Module.compHom M₀ stageMap
         Module.Flat R₀ M₀) ∧
        ∃ targetMap : S₀ →+* S,
          targetMap.comp stageMap = f.comp r ∧
            Nonempty
              (let _ : Algebra R₀ R := r.toAlgebra
               let _ : Algebra R₀ S₀ := stageMap.toAlgebra
               let _ : Algebra R S := f.toAlgebra
               { ringBaseChange : R ⊗[R₀] S₀ ≃ₐ[R] S //
                   RingHom.comp ringBaseChange.toRingHom includeRight.toRingHom = targetMap }) ∧
            Nonempty
              (let _ : Algebra S₀ S := targetMap.toAlgebra
               S ⊗[S₀] M₀ ≃ₗ[S] M) := by
  -- Proof comment: the chosen stage supplies the ring, target algebra, and module; the existing
  -- stage and final-base-change helpers provide the finite-presentation and comparison clauses.
  obtain ⟨hstage, hmodule⟩ := stageFinitePresentationData (f := f) (M := M) A i
  refine ⟨A.RStage i, inferInstance, A.sourceStageToLimit i, A.source_finiteType i,
    A.SStage i, inferInstance, A.stageMap i, A.moduleStage i, inferInstance, inferInstance,
    hstage, hmodule, ?_, A.targetStageToLimit i, ?_, ?_, ?_⟩
  · -- Proof comment: this is exactly the selected stage-flatness hypothesis, with the source
    -- module structure spelled as restriction along the stage map.
    exact hflat_i
  · -- Proof comment: the target map and source map commute with the original map by the stored
    -- colimit square for the approximation.
    exact stageToLimit_comp_stageMap (f := f) (M := M) A i
  · -- Proof comment: the final ring-side base-change bridge was proved once above for every
    -- approximation stage.
    exact finalRingBaseChange (f := f) (M := M) A i
  · -- Proof comment: the module-side base-change bridge is one of the structural equivalences
    -- carried by the directed approximation.
    exact ⟨A.finalBaseChange i⟩

/-- Helper for Chap10 Lemma 10 168 1: a flat approximation stage packages as a finite type
`ℤ`-model in the requested source and module universes. -/
lemma flatFinitePresentationShrinkData
    (A : DirectedFinitePresentationModuleApproximation f M) (i : A.Λ)
    (hflat_i : Module.Flat (A.RStage i) (A.moduleStage i)) :
    ∃ (R₀ : Type u₀) (_ : CommRing R₀) (r : R₀ →+* R)
      (_ : (Int.castRingHom R₀).FiniteType) (S₀ : Type v) (_ : CommRing S₀)
      (stageMap : R₀ →+* S₀) (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module S₀ M₀),
      stageMap.FinitePresentation ∧
        Module.FinitePresentation S₀ M₀ ∧
        (let _ : Module R₀ M₀ := Module.compHom M₀ stageMap
         Module.Flat R₀ M₀) ∧
        ∃ targetMap : S₀ →+* S,
          targetMap.comp stageMap = f.comp r ∧
            Nonempty
              (let _ : Algebra R₀ R := r.toAlgebra
               let _ : Algebra R₀ S₀ := stageMap.toAlgebra
               let _ : Algebra R S := f.toAlgebra
               { ringBaseChange : R ⊗[R₀] S₀ ≃ₐ[R] S //
                   RingHom.comp ringBaseChange.toRingHom includeRight.toRingHom = targetMap }) ∧
            Nonempty
              (let _ : Algebra S₀ S := targetMap.toAlgebra
               S ⊗[S₀] M₀ ≃ₗ[S] M) := by
  classical
  letI : Small.{u₀} (A.RStage i) := stageSource_small (f := f) (M := M) A i
  letI : Small.{w} (A.moduleStage i) := stageModule_small (f := f) (M := M) A i
  let R₀ := Shrink.{u₀} (A.RStage i)
  let M₀ := Shrink.{w} (A.moduleStage i)
  let stageMap : R₀ →+* A.SStage i :=
    (A.stageMap i).comp (Shrink.ringEquiv (A.RStage i)).toRingHom
  let r : R₀ →+* R :=
    (A.sourceStageToLimit i).comp (Shrink.ringEquiv (A.RStage i)).toRingHom
  letI : Module R₀ M₀ := Module.compHom M₀ stageMap
  -- Proof comment: first package the shrunk source ring, original target stage, and shrunk module
  -- using the finite-presentation and flatness transport lemmas proved above.
  refine ⟨R₀, inferInstance, r, ?_, A.SStage i, inferInstance, stageMap, M₀,
    inferInstance, inferInstance, ?_, ?_, ?_, A.targetStageToLimit i, ?_, ?_, ?_⟩
  · exact shrinkSource_finiteType (f := f) (M := M) A i
  · exact shrinkStageMap_finitePresentation (f := f) (M := M) A i
  · exact shrinkStageModule_finitePresentation (f := f) (M := M) A i
  · exact shrinkStageModule_flat (f := f) (M := M) A i hflat_i
  · -- Proof comment: the target-stage square still commutes after precomposing the source map
    -- with the shrink ring equivalence.
    ext x
    exact RingHom.congr_fun (stageToLimit_comp_stageMap (f := f) (M := M) A i)
      (Shrink.ringEquiv (A.RStage i) x)
  · -- Proof comment: compare `R ⊗[Shrink R_i] S_i` with `R ⊗[R_i] S_i` by canceling the
    -- shrink equivalence, then use the already proved final ring base-change equivalence.
    letI : Algebra R₀ R := r.toAlgebra
    letI : Algebra R₀ (A.SStage i) := stageMap.toAlgebra
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R₀ (A.RStage i) := (Shrink.ringEquiv (A.RStage i)).toRingHom.toAlgebra
    letI : Algebra (A.RStage i) R := (A.sourceStageToLimit i).toAlgebra
    letI : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    letI : IsScalarTower R₀ (A.RStage i) R := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower R₀ (A.RStage i) (A.RStage i) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower R₀ (A.RStage i) (A.SStage i) :=
      IsScalarTower.of_algebraMap_eq' rfl
    have eLeft_commutes :
        ∀ x : R₀,
          (Shrink.ringEquiv (A.RStage i)).symm (algebraMap R₀ (A.RStage i) x) =
            algebraMap R₀ R₀ x := by
      intro x
      -- Proof comment: the `R₀`-algebra structure on the original stage is exactly the shrink
      -- ring equivalence.
      simp [RingHom.algebraMap_toAlgebra]
    let eLeft : A.RStage i ≃ₐ[R₀] R₀ :=
      { toRingEquiv := (Shrink.ringEquiv (A.RStage i)).symm
        commutes' := eLeft_commutes }
    let eStageR0 : A.RStage i ⊗[R₀] A.SStage i ≃ₐ[R₀] A.SStage i :=
      (Algebra.TensorProduct.congr eLeft (AlgEquiv.refl : A.SStage i ≃ₐ[R₀] A.SStage i)).trans
        (Algebra.TensorProduct.lid R₀ (A.SStage i))
    have eStage_commutes :
        ∀ x : A.RStage i,
          eStageR0 (algebraMap (A.RStage i) (A.RStage i ⊗[R₀] A.SStage i) x) =
            algebraMap (A.RStage i) (A.SStage i) x := by
      intro x
      -- Proof comment: under the shrink equivalence, the left tensor inclusion becomes the
      -- base-ring tensor inclusion, which `lid` evaluates to the stage algebra map.
      change eStageR0
          ((includeLeft : A.RStage i →ₐ[R₀] A.RStage i ⊗[R₀] A.SStage i) x) =
        A.stageMap i x
      simp [eStageR0, eLeft, stageMap, RingHom.algebraMap_toAlgebra, Algebra.smul_def]
    let eStage : A.RStage i ⊗[R₀] A.SStage i ≃ₐ[A.RStage i] A.SStage i :=
      { toRingEquiv := eStageR0.toRingEquiv
        commutes' := eStage_commutes }
    let eShrink :
        R ⊗[R₀] A.SStage i ≃ₐ[R] R ⊗[A.RStage i] A.SStage i :=
      (Algebra.TensorProduct.cancelBaseChange R₀ (A.RStage i) R R (A.SStage i)).symm.trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) eStage)
    obtain ⟨eFinal, heFinal⟩ := finalRingBaseChange (f := f) (M := M) A i
    refine ⟨⟨eShrink.trans eFinal, ?_⟩⟩
    ext x
    -- Proof comment: on the right tensor factor, the shrink comparison sends `1 ⊗ x` to
    -- `1 ⊗ x`, so the final comparison has the required target-stage computation.
    have hright :
        eShrink ((includeRight : A.SStage i →ₐ[R₀] R ⊗[R₀] A.SStage i) x) =
          (includeRight : A.SStage i →ₐ[A.RStage i] R ⊗[A.RStage i] A.SStage i) x := by
      simp [eShrink, eStage, eStageR0, eLeft, Algebra.TensorProduct.cancelBaseChange_symm_tmul]
      change ((Shrink.ringEquiv (A.RStage i)).symm (1 : A.RStage i)) •
          (1 ⊗ₜ[A.RStage i] x : R ⊗[A.RStage i] A.SStage i) =
        (1 ⊗ₜ[A.RStage i] x : R ⊗[A.RStage i] A.SStage i)
      rw [map_one, one_smul]
    calc
      (eShrink.trans eFinal).toRingHom
          ((includeRight : A.SStage i →ₐ[R₀] R ⊗[R₀] A.SStage i) x) =
          eFinal.toRingHom
            ((includeRight : A.SStage i →ₐ[A.RStage i] R ⊗[A.RStage i] A.SStage i) x) := by
        exact congrArg (fun y ↦ eFinal y) hright
      _ = A.targetStageToLimit i x := by
        exact RingHom.congr_fun heFinal x
  · -- Proof comment: base-change the shrink linear equivalence to `S` and compose with the
    -- structural final module base-change equivalence of the approximation.
    letI : Algebra (A.SStage i) S := (A.targetStageToLimit i).toAlgebra
    exact ⟨((Shrink.linearEquiv (A.SStage i) (A.moduleStage i)).baseChange
      (A.SStage i) S (Shrink.{w} (A.moduleStage i)) (A.moduleStage i)).trans
        (A.finalBaseChange i)⟩

-- Route correction: rather than transporting later-stage flatness through raw tensor
-- representatives, first record that each ring transition square is a pushout and then use the
-- canonical pushout cancellation equivalence for modules.
/-- Helper for Chap10 Lemma 10 168 1: a bijective stage base-change map gives the corresponding
`A.RStage j`-algebra equivalence from `A.RStage j ⊗[A.RStage i] A.SStage i` to `A.SStage j`,
together with its value on the `A.SStage i` generator. -/
lemma stageRingBaseChangeEquiv
    (A : DirectedFinitePresentationModuleApproximation f M) {i j : A.Λ} (hij : i ≤ j) :
    Nonempty
      (let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
       let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
       let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
       { e : A.RStage j ⊗[A.RStage i] A.SStage i ≃ₐ[A.RStage j] A.SStage j //
          ∀ x : A.SStage i, e (1 ⊗ₜ[A.RStage i] x) = A.SMap i j hij x }) := by
  letI : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  letI : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
  letI : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  letI : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j hij)).toAlgebra
  letI : IsScalarTower (A.RStage i) (A.RStage j) (A.SStage j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let c : A.RStage j ⊗[A.RStage i] A.SStage i ≃+*
      A.SStage i ⊗[A.RStage i] A.RStage j :=
    (Algebra.TensorProduct.comm
      (R := A.RStage i) (A := A.RStage j) (B := A.SStage i)).toRingEquiv
  let g : A.RStage j ⊗[A.RStage i] A.SStage i →+* A.SStage j :=
    (A.stageBaseChangeMap hij).comp c.toRingHom
  have hg : Function.Bijective g := by
    -- Proof comment: compose the stored bijection with the tensor-factor commutativity
    -- equivalence.
    exact (A.hasBijectiveBaseChangeTransitions hij).comp c.bijective
  let e : A.RStage j ⊗[A.RStage i] A.SStage i ≃ₐ[A.RStage j] A.SStage j :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective g hg) (by
      intro r
      change (A.stageBaseChangeMap hij) (1 ⊗ₜ[A.RStage i] r) = A.stageMap j r
      -- Proof comment: the pure-tensor formula shows that the transported equivalence is
      -- `A.RStage j`-linear.
      rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
      simp)
  refine ⟨⟨e, ?_⟩⟩
  intro x
  change (A.stageBaseChangeMap hij) (x ⊗ₜ[A.RStage i] 1) = A.SMap i j hij x
  -- Proof comment: on the `A.SStage i` generator, the same pure-tensor formula removes the
  -- final `A.RStage j` scalar.
  rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
  simp

/-- Helper for Chap10 Lemma 10 168 1: the square
`A.RStage i → A.RStage j`, `A.SStage i → A.SStage j` is a pushout square. -/
lemma stageRing_isPushout
    (A : DirectedFinitePresentationModuleApproximation f M) {i j : A.Λ} (hij : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
    let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
    let _ : Algebra (A.SStage i) (A.SStage j) := (A.SMap i j hij).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j hij)).toAlgebra
    let _ : IsScalarTower (A.RStage i) (A.RStage j) (A.SStage j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
      IsScalarTower.of_algebraMap_eq' (by
        simpa [RingHom.algebraMap_toAlgebra] using A.comm hij)
    Algebra.IsPushout (A.RStage i) (A.RStage j) (A.SStage i) (A.SStage j) := by
  letI : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  letI : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
  letI : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  letI : Algebra (A.SStage i) (A.SStage j) := (A.SMap i j hij).toAlgebra
  letI : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j hij)).toAlgebra
  letI : IsScalarTower (A.RStage i) (A.RStage j) (A.SStage j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
    IsScalarTower.of_algebraMap_eq' (by
      simpa [RingHom.algebraMap_toAlgebra] using A.comm hij)
  letI : Algebra (A.SStage i) (A.RStage j ⊗[A.RStage i] A.SStage i) :=
    Algebra.TensorProduct.rightAlgebra
  obtain ⟨e, he⟩ := stageRingBaseChangeEquiv (f := f) (M := M) A hij
  refine Algebra.IsPushout.of_equiv (R := A.RStage i) (R' := A.RStage j)
    (S := A.SStage i) (T := A.SStage j) e ?_
  ext x
  change e (1 ⊗ₜ[A.RStage i] x) = A.SMap i j hij x
  -- Proof comment: the equivalence agrees with the target transition on the `S_i` generator.
  exact he x

/-- Helper for Chap10 Lemma 10 168 1: flatness at one stage persists after any later stage
transition. -/
lemma flat_later_stage_of_flat_stage
    (A : DirectedFinitePresentationModuleApproximation f M) {i j : A.Λ} (hij : i ≤ j)
    (hflat : Module.Flat (A.RStage i) (A.moduleStage i)) :
    Module.Flat (A.RStage j) (A.moduleStage j) := by
  letI : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  letI : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j hij).toAlgebra
  letI : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  letI : Algebra (A.SStage i) (A.SStage j) := (A.SMap i j hij).toAlgebra
  letI : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j hij)).toAlgebra
  letI : IsScalarTower (A.RStage i) (A.RStage j) (A.SStage j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (A.RStage i) (A.SStage i) (A.SStage j) :=
    IsScalarTower.of_algebraMap_eq' (by
      simpa [RingHom.algebraMap_toAlgebra] using A.comm hij)
  letI : Module (A.RStage i) (A.moduleStage i) :=
    Module.compHom (A.moduleStage i) (A.stageMap i)
  letI : IsScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i) :=
    RestrictScalars.isScalarTower (A.RStage i) (A.SStage i) (A.moduleStage i)
  letI : Module (A.RStage j) (A.moduleStage j) :=
    Module.compHom (A.moduleStage j) (A.stageMap j)
  letI : Module (A.RStage j) (A.SStage j ⊗[A.SStage i] A.moduleStage i) :=
    Module.compHom (A.SStage j ⊗[A.SStage i] A.moduleStage i) (A.stageMap j)
  letI : Module.Flat (A.RStage i) (A.moduleStage i) := hflat
  have hbase : Module.Flat (A.RStage j) (A.RStage j ⊗[A.RStage i] A.moduleStage i) := by
    -- Proof comment: flatness survives scalar extension along `A.RStage i → A.RStage j`.
    exact Module.Flat.baseChange (A.RStage i) (A.RStage j) (A.moduleStage i)
  letI : Algebra.IsPushout (A.RStage i) (A.RStage j) (A.SStage i) (A.SStage j) :=
    stageRing_isPushout (f := f) (M := M) A hij
  let ePush : A.SStage j ⊗[A.SStage i] A.moduleStage i ≃ₗ[A.RStage j]
      A.RStage j ⊗[A.RStage i] A.moduleStage i :=
    Algebra.IsPushout.cancelBaseChange (A.RStage i) (A.RStage j) (A.SStage i) (A.SStage j)
      (A.moduleStage i)
  let eS := (A.transitionBaseChange hij).symm
  let eTransition : A.moduleStage j ≃ₗ[A.RStage j]
      A.SStage j ⊗[A.SStage i] A.moduleStage i :=
    { toFun := fun x ↦ eS x
      invFun := fun x ↦ (A.transitionBaseChange hij) x
      left_inv := by intro x; exact eS.left_inv x
      right_inv := by intro x; exact eS.right_inv x
      map_add' := by intro x y; exact eS.map_add x y
      map_smul' := by
        intro r x
        change eS ((A.stageMap j r) • x) = (A.stageMap j r) • eS x
        exact map_smul eS (A.stageMap j r) x }
  -- Proof comment: transport the base-changed flat module across the pushout cancellation and the
  -- stored module transition equivalence.
  exact Module.Flat.of_linearEquiv (eTransition.trans ePush)

end DirectedFinitePresentationModuleApproximation

-- Proof sketch: apply Lemma `10.127.18` to approximate the finitely presented map and module by a
-- directed system of finite-type `ℤ`-models, then use Lemma `10.128.3` to choose a stage whose
-- module is already flat over the corresponding source ring, and record that stage as explicit
-- descended finite-presentation data.
/-- Lemma 10.168.1 (1): if `R → S` is of finite presentation, `M` is a finitely presented
`S`-module, and `M` is flat over `R`, then `(R → S, M)` admits a model over a finite type
`ℤ`-algebra whose descended module is flat over the descended source ring. -/
@[stacks 02JO]
theorem exists_finiteType_flatFinitePresentationModel
    (hf : f.FinitePresentation)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ (R₀ : Type u₀) (_ : CommRing R₀) (r : R₀ →+* R)
      (_ : (Int.castRingHom R₀).FiniteType) (S₀ : Type v) (_ : CommRing S₀)
      (stageMap : R₀ →+* S₀) (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module S₀ M₀),
      stageMap.FinitePresentation ∧
        Module.FinitePresentation S₀ M₀ ∧
        (let _ : Module R₀ M₀ := Module.compHom M₀ stageMap
         Module.Flat R₀ M₀) ∧
        ∃ targetMap : S₀ →+* S,
          targetMap.comp stageMap = f.comp r ∧
            Nonempty
              (let _ : Algebra R₀ R := r.toAlgebra
               let _ : Algebra R₀ S₀ := stageMap.toAlgebra
               let _ : Algebra R S := f.toAlgebra
               { ringBaseChange : R ⊗[R₀] S₀ ≃ₐ[R] S //
                   RingHom.comp ringBaseChange.toRingHom includeRight.toRingHom = targetMap }) ∧
            Nonempty
              (let _ : Algebra S₀ S := targetMap.toAlgebra
               S ⊗[S₀] M₀ ≃ₗ[S] M) := by
  -- Proof comment: choose a finite-presentation directed approximation, descend flatness to one
  -- stage, then delegate the universe-shrink and base-change packaging to the stage adapter.
  obtain ⟨A⟩ :=
    DirectedFinitePresentationModuleApproximation.exists_directedFinitePresentationModuleApproximation
      (f := f) (M := M) hf
  obtain ⟨i, hflat_i⟩ :=
    DirectedFinitePresentationModuleApproximation.exists_flat_stage_of_flat_limit
      (f := f) (M := M) A hflat
  exact DirectedFinitePresentationModuleApproximation.flatFinitePresentationShrinkData
    (f := f) (M := M) A i hflat_i

-- Proof sketch: start from the finite type `ℤ`-data given by part `(1)`. Since the chosen base
-- ring `R₀` is of finite type over `ℤ`, Lemma `10.127.3` factors the map `R₀ → R` through some
-- stage of the directed colimit presentation of `R`; then base change the descended algebra and
-- module to that stage.
/-- Helper for Chap10 Lemma 10 168 1: finite type flat finite-presentation model data descends
to a stage of a directed source-ring colimit. -/
lemma flatFinitePresentationModel_descends_to_directedStage
    {Λ : Type u₀} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)
    (hmodel :
      ∃ (R₀ : Type u₀) (_ : CommRing R₀) (r : R₀ →+* R)
        (_ : (Int.castRingHom R₀).FiniteType) (S₀ : Type v) (_ : CommRing S₀)
        (stageMap : R₀ →+* S₀) (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module S₀ M₀),
        stageMap.FinitePresentation ∧
          Module.FinitePresentation S₀ M₀ ∧
          (let _ : Module R₀ M₀ := Module.compHom M₀ stageMap
           Module.Flat R₀ M₀) ∧
          ∃ targetMap : S₀ →+* S,
            targetMap.comp stageMap = f.comp r ∧
              Nonempty
                (let _ : Algebra R₀ R := r.toAlgebra
                 let _ : Algebra R₀ S₀ := stageMap.toAlgebra
                 let _ : Algebra R S := f.toAlgebra
                 { ringBaseChange : R ⊗[R₀] S₀ ≃ₐ[R] S //
                     RingHom.comp ringBaseChange.toRingHom includeRight.toRingHom = targetMap }) ∧
              Nonempty
                (let _ : Algebra S₀ S := targetMap.toAlgebra
                 S ⊗[S₀] M₀ ≃ₗ[S] M)) :
    ∃ i : Λ,
      let r : RStage i →+* R := Ring.DirectLimit.toLimitHom RStage map colimitIso i
      ∃ (S₀ : Type v) (_ : CommRing S₀) (stageMap : RStage i →+* S₀)
        (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module S₀ M₀),
        stageMap.FinitePresentation ∧
          Module.FinitePresentation S₀ M₀ ∧
          (let _ : Module (RStage i) M₀ := Module.compHom M₀ stageMap
           Module.Flat (RStage i) M₀) ∧
          ∃ targetMap : S₀ →+* S,
            targetMap.comp stageMap = f.comp r ∧
              Nonempty
                (let _ : Algebra (RStage i) R := r.toAlgebra
                 let _ : Algebra (RStage i) S₀ := stageMap.toAlgebra
                 let _ : Algebra R S := f.toAlgebra
                 { ringBaseChange : R ⊗[RStage i] S₀ ≃ₐ[R] S //
                     RingHom.comp ringBaseChange.toRingHom includeRight.toRingHom = targetMap }) ∧
              Nonempty
                (let _ : Algebra S₀ S := targetMap.toAlgebra
                 S ⊗[S₀] M₀ ≃ₗ[S] M) := by
  -- Proof comment: this is the finite-model descent step from the source proof. It should factor
  -- the finite type source model through the directed colimit and then base-change the descended
  -- finite-presentation algebra/module while preserving flatness.
  -- TODO: complete the stage factorization and base-change transport using the finite type and
  -- finite-presentation descent APIs for directed ring colimits.
  sorry

/-- Lemma 10.168.1 (2): for any directed colimit presentation `R = colim_λ R_λ`, the flat finite
presentation data from part `(1)` descends to a single stage `R_λ`. -/
@[stacks 02JO]
theorem exists_stage_flatFinitePresentationModel_of_directedRingColimit
    {Λ : Type u₀} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)
    (hf : f.FinitePresentation)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ i : Λ,
      let r : RStage i →+* R := Ring.DirectLimit.toLimitHom RStage map colimitIso i
      ∃ (S₀ : Type v) (_ : CommRing S₀) (stageMap : RStage i →+* S₀)
        (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module S₀ M₀),
        stageMap.FinitePresentation ∧
          Module.FinitePresentation S₀ M₀ ∧
          (let _ : Module (RStage i) M₀ := Module.compHom M₀ stageMap
           Module.Flat (RStage i) M₀) ∧
          ∃ targetMap : S₀ →+* S,
            targetMap.comp stageMap = f.comp r ∧
              Nonempty
                (let _ : Algebra (RStage i) R := r.toAlgebra
                 let _ : Algebra (RStage i) S₀ := stageMap.toAlgebra
                 let _ : Algebra R S := f.toAlgebra
                 { ringBaseChange : R ⊗[RStage i] S₀ ≃ₐ[R] S //
                     RingHom.comp ringBaseChange.toRingHom includeRight.toRingHom = targetMap }) ∧
              Nonempty
                (let _ : Algebra S₀ S := targetMap.toAlgebra
                 S ⊗[S₀] M₀ ≃ₗ[S] M) := by
  -- Proof comment: first obtain the finite type model from part `(1)`, then apply the dedicated
  -- directed-colimit descent adapter.
  exact flatFinitePresentationModel_descends_to_directedStage
    (f := f) (M := M) RStage map colimitIso
    (exists_finiteType_flatFinitePresentationModel (f := f) (M := M) hf hflat)

-- Proof sketch: choose descended data as in part `(1)`, factor its base ring map through a
-- sufficiently large source stage, descend the ring and module maps to a large stage by finite
-- presentation, and use stabilization of the stagewise base-change isomorphisms to identify the
-- descended data with the given stage data. Flatness then transfers to every later stage.
/-- Lemma 10.168.1 (3): for a directed colimit presentation `(R → S, M) = colim_λ (R_λ → S_λ,
M_λ)` with stage maps of finite presentation and finitely presented stage modules, if `M` is flat
over `R`, then `M_λ` is flat over `R_λ` for all sufficiently large `λ`. -/
@[stacks 02JO]
theorem eventually_flat_stageModules_of_flat_limit
    (A : DirectedFinitePresentationModuleApproximation f M)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ i₀ : A.Λ, ∀ j, i₀ ≤ j → Module.Flat (A.RStage j) (A.moduleStage j) := by
  -- Proof comment: descend flatness to one stage, then transport it through every later
  -- transition in the directed approximation.
  obtain ⟨i₀, hflat_i₀⟩ :=
    DirectedFinitePresentationModuleApproximation.exists_flat_stage_of_flat_limit
      (f := f) (M := M) A hflat
  refine ⟨i₀, fun j hij ↦ ?_⟩
  exact DirectedFinitePresentationModuleApproximation.flat_later_stage_of_flat_stage
    (f := f) (M := M) A hij hflat_i₀

end

end
