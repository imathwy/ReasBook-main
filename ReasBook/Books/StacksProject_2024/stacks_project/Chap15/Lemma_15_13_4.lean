import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap15.Lemma_15_11_3
import StacksProject_2024.Chap15.Lemma_15_13_1
import StacksProject_2024.Chap15.Lemma_15_88_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open CommRingCat
open Opposite
open scoped TensorProduct

noncomputable section

universe u v

section

variable (F : SequentialInverseSystem CommRingCat.{u})

/- Domain-style sampling:
- primary domain: varying-ring sequential module systems over a commutative-ring inverse system
  and their inverse limits over the limit ring;
- sampled owner declarations:
  `SeqRingMod`,
  `sequentialRingedModuleEvaluation`,
  `ringedModuleLimitTower`,
  `ringedModuleInverseLimitFunctor`;
- best owner abstraction: the chapter owner
  `SeqRingMod (fun n ↦ F.obj (op n)) (fun n ↦ (F.stepMap n).hom)` for compatible module systems
  over the varying ring system `F`;
- primitive data: an object `M` of that owner category;
- derived API: its stage modules, successor maps, inverse-limit tower over `A = lim F`, the
  inverse-limit module, and the stagewise base-change comparison maps.

Source/core/bridge triage:
- `source-facing`: Lemma `15.13.4` and its inverse-limit/base-change conclusions;
- `core/canonical`: `SeqRingMod`, `sequentialRingedModuleEvaluation`,
  `ringedModuleLimitTower`, and `ringedModuleInverseLimitFunctor`;
- `bridge/view`: the stagewise and inverse-limit base-change maps induced from the owner-derived
  evaluation and inverse-limit tower.

This refinement therefore deletes the parallel entrywise tower owner from this file. The public
surface is now organized around the intrinsic varying-ring module object, with only thin
source-facing bridge abbreviations for the comparison maps used in the statement. -/

private abbrev stageRing (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) : Type u :=
  (F.obj (op n) : Type u)

private abbrev stageMap (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ) :
    stageRing F (n + 1) →+* stageRing F n :=
  (F.stepMap n).hom

private abbrev ownerSystem : SequentialInverseSystem CommRingCat.{u} :=
  sequentialRingSystem (stageRing F) (stageMap F)

private abbrev inverseLimitRing (F : SequentialInverseSystem CommRingCat.{u}) : Type u :=
  ((limit (ownerSystem F) : CommRingCat.{u}) : Type u)

private abbrev stageModule
    (F : SequentialInverseSystem CommRingCat.{u})
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    ModuleCat (stageRing F n) :=
  (sequentialRingedModuleEvaluation (stageRing F) (stageMap F) n).obj M

local instance instAlgebraInverseLimitStage (n : ℕ) :
    Algebra (inverseLimitRing F) (stageRing F n) :=
  RingHom.toAlgebra (limit.π (ownerSystem F) (op n)).hom

local instance instAlgebraStageSuccStage (n : ℕ) :
    Algebra (stageRing F (n + 1)) (stageRing F n) :=
  RingHom.toAlgebra (stageMap F n)

local instance instModuleInverseLimitRingStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    Module (inverseLimitRing F) (stageModule F M n) :=
  by
    letI : Module ((ownerSystem F).obj (op n)) (stageModule F M n) := by
      simpa [ownerSystem, sequentialRingSystem, stageModule] using
        (stageModule F M n).isModule
    simpa [ownerSystem, sequentialRingSystem, stageModule] using
      Module.compHom (stageModule F M n) (limit.π (ownerSystem F) (op n)).hom

local instance instIsScalarTowerInverseLimitRingStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    IsScalarTower (inverseLimitRing F) (stageRing F n) (stageModule F M n) :=
  by
    letI : Module ((ownerSystem F).obj (op n)) (stageModule F M n) := by
      simpa [ownerSystem, sequentialRingSystem, stageModule] using
        (stageModule F M n).isModule
    simpa [ownerSystem, sequentialRingSystem, stageModule] using
      IsScalarTower.of_compHom (inverseLimitRing F) (stageRing F n) (stageModule F M n)

local instance instModuleStageSuccStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    Module (stageRing F (n + 1)) (stageModule F M n) :=
  Module.compHom (stageModule F M n) (stageMap F n)

local instance instIsScalarTowerStageSuccStageModule
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    IsScalarTower (stageRing F (n + 1)) (stageRing F n) (stageModule F M n) :=
  IsScalarTower.of_compHom (stageRing F (n + 1)) (stageRing F n) (stageModule F M n)

local instance instIsScalarTowerInverseLimitRingStageSucc
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    IsScalarTower (inverseLimitRing F) (stageRing F (n + 1)) (stageModule F M n) :=
  by
    letI : Module ((ownerSystem F).obj (op n)) (stageModule F M n) := by
      simpa [ownerSystem, sequentialRingSystem, stageModule] using
        (stageModule F M n).isModule
    exact IsScalarTower.of_algebraMap_smul fun r m ↦ by
      change
        stageMap F n ((limit.π (ownerSystem F) (op (n + 1))).hom r) • m =
          (limit.π (ownerSystem F) (op n)).hom r • m
      rw [show
          (limit.π (ownerSystem F) (op n)).hom =
            (stageMap F n).comp (limit.π (ownerSystem F) (op (n + 1))).hom from by
        ext x
        simpa using congrArg
          (fun f : limit (ownerSystem F) ⟶ (ownerSystem F).obj (op n) ↦ f x)
          ((limit.w (ownerSystem F) ((homOfLE (Nat.le_succ n)).op)).symm)]
      rfl

local instance instModuleInverseLimitRing
    (M : SeqRingMod (stageRing F) (stageMap F)) :
    Module (inverseLimitRing F)
      ((ringedModuleInverseLimitFunctor (stageRing F) (stageMap F)).obj M) := by
  simpa [inverseLimitRing] using
    ((ringedModuleInverseLimitFunctor (stageRing F) (stageMap F)).obj M).isModule

private abbrev restrictedStageModule
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    ModuleCat (inverseLimitRing F) :=
  (ModuleCat.restrictScalars (limit.π (ownerSystem F) (op n)).hom).obj (stageModule F M n)

local instance instModuleRestrictedStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    Module (stageRing F n) (restrictedStageModule F M n) :=
  (stageModule F M n).isModule

local instance instIsScalarTowerInverseLimitRingRestrictedStage
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    IsScalarTower (inverseLimitRing F) (stageRing F n) (restrictedStageModule F M n) := by
  change IsScalarTower (inverseLimitRing F) (stageRing F n) (stageModule F M n)
  infer_instance

private abbrev stageProjection
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    ((ringedModuleInverseLimitFunctor (stageRing F) (stageMap F)).obj M) ⟶
      restrictedStageModule F M n :=
  by
    simpa [restrictedStageModule, ringedModuleInverseLimitFunctor, stageModule] using
      limit.π (ringedModuleLimitTower (stageRing F) (stageMap F) M) (op n)

private abbrev stageStep
    (M : SeqRingMod (stageRing F) (stageMap F)) (n : ℕ) :
    stageModule F M (n + 1) →ₗ[stageRing F (n + 1)] stageModule F M n :=
  ((sequentialRingedModuleEvaluationStep (stageRing F) (stageMap F) n).app M).hom

/-- The base-change comparison map `A_n ⊗[A_{n + 1}] M_{n + 1} → M_n` induced by the successor
transition map in the owner object `M ∈ SeqRingMod`. -/
abbrev stageBaseChangeComparison
    (M : SeqRingMod (fun n ↦ (F.obj (op n) : Type u)) (fun n ↦ (F.stepMap n).hom)) (n : ℕ) :
    ((F.obj (op n) : Type u) ⊗[(F.obj (op (n + 1)) : Type u)]
        ((sequentialRingedModuleEvaluation
          (fun n ↦ (F.obj (op n) : Type u))
          (fun n ↦ (F.stepMap n).hom) (n + 1)).obj M)) →ₗ[(F.obj (op n) : Type u)]
      ((sequentialRingedModuleEvaluation
        (fun n ↦ (F.obj (op n) : Type u))
        (fun n ↦ (F.stepMap n).hom) n).obj M) :=
  (stageStep F M n).liftBaseChange (stageRing F n)

/-- The base-change comparison map `A_n ⊗[A] M → M_n` from the inverse limit module
`M = lim M_n` to the `n`th stage, where `A = lim A_n`. -/
abbrev inverseLimitBaseChangeComparison
    (M : SeqRingMod (fun n ↦ (F.obj (op n) : Type u)) (fun n ↦ (F.stepMap n).hom)) (n : ℕ) :
    ((F.obj (op n) : Type u) ⊗[
        ((limit
          (sequentialRingSystem
            (fun n ↦ (F.obj (op n) : Type u))
            (fun n ↦ (F.stepMap n).hom)) : CommRingCat.{u}) : Type u)]
        ((ringedModuleInverseLimitFunctor
          (fun n ↦ (F.obj (op n) : Type u))
          (fun n ↦ (F.stepMap n).hom)).obj M)) →ₗ[(F.obj (op n) : Type u)]
      ((sequentialRingedModuleEvaluation
        (fun n ↦ (F.obj (op n) : Type u))
        (fun n ↦ (F.stepMap n).hom) n).obj M) :=
  by
    simpa [restrictedStageModule, stageModule] using
      (stageProjection F M n).hom.liftBaseChange (stageRing F n)

section

variable (M :
  SeqRingMod (fun n ↦ (F.obj (op n) : Type u)) (fun n ↦ (F.stepMap n).hom))
variable [∀ n : ℕ,
  Module.Finite (F.obj (op n))
    ((sequentialRingedModuleEvaluation
      (fun n ↦ (F.obj (op n) : Type u))
      (fun n ↦ (F.stepMap n).hom) n).obj M)]
variable [∀ n : ℕ,
  Module.Flat (F.obj (op (n + 1)))
    ((sequentialRingedModuleEvaluation
      (fun n ↦ (F.obj (op n) : Type u))
      (fun n ↦ (F.stepMap n).hom) (n + 1)).obj M)]
variable [Module.Projective (F.obj (op 0))
  ((sequentialRingedModuleEvaluation
    (fun n ↦ (F.obj (op n) : Type u))
    (fun n ↦ (F.stepMap n).hom) 0).obj M)]

local instance instFlatStage (n : ℕ) : Module.Flat (stageRing F n) (stageModule F M n) := by
  cases n with
  | zero =>
      exact Module.Flat.of_projective
  | succ n =>
      simpa [Nat.succ_eq_add_one] using (inferInstance :
        Module.Flat (stageRing F (n + 1)) (stageModule F M (n + 1)))

/-- Helper for Lemma 15.13.4: surjectivity of the step maps implies surjectivity of every long
transition map. -/
lemma transitionMap_surjective_of_step_surjective
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom) :
    ∀ ⦃i j : ℕ⦄ (hij : i ≤ j), Function.Surjective (F.transitionMap hij).hom := by
  intro i j hij
  induction hij with
  | refl =>
      -- Proof comment: the identity transition is trivially surjective.
      simpa [SequentialInverseSystem.transitionMap]
  | @step j hij ih =>
      -- Proof comment: the long transition factors through the new step map, so surjectivity
      -- composes along the source proof's chain of reductions.
      rw [transitionMap_comp (F := F) hij (Nat.le_succ j)]
      simpa using ih.comp (h_surj j)

/-- Helper for Lemma 15.13.4: if the tensor-level successor comparison is bijective, then the
underlying stage map is already surjective. -/
lemma stageStep_surjective_of_baseChange_bijective
    (n : ℕ)
    (h_step : Function.Surjective (F.stepMap n).hom)
    (h_compare : Function.Bijective (stageBaseChangeComparison F M n)) :
    Function.Surjective (stageStep F M n) := by
  intro y
  rcases h_compare.2 y with ⟨z, hz⟩
  have hz_range :
      ∀ z : (stageRing F n) ⊗[stageRing F (n + 1)] stageModule F M (n + 1),
        ∃ x : stageModule F M (n + 1),
          stageBaseChangeComparison F M n z = stageStep F M n x := by
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · -- Proof comment: the zero tensor comes from the zero vector.
      exact ⟨0, by simp [stageBaseChangeComparison]⟩
    · intro a m
      rcases h_step a with ⟨b, rfl⟩
      refine ⟨b • m, ?_⟩
      -- Proof comment: surjectivity of the ring transition lets us rewrite each pure tensor as the
      -- image of a scalar multiple under the untensored stage map.
      simp [stageBaseChangeComparison, LinearMap.liftBaseChange_tmul, LinearMap.map_smul]
    · intro z₁ z₂ hz₁ hz₂
      rcases hz₁ with ⟨x₁, hx₁⟩
      rcases hz₂ with ⟨x₂, hx₂⟩
      refine ⟨x₁ + x₂, ?_⟩
      -- Proof comment: additivity upgrades the pure-tensor computation to arbitrary tensors.
      simp [hx₁, hx₂, map_add]
  rcases hz_range z with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- Proof comment: the chosen tensor preimage of `y` already lies in the range of the stage map.
  simpa [hz] using hx.symm

/-- Helper for Lemma 15.13.4: the projection from the inverse-limit ring to the initial stage is
surjective when every step transition is surjective. -/
private noncomputable def stage_zero_lift_sequence
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (x : stageRing F 0) : (n : ℕ) → stageRing F n
  | 0 => x
  | n + 1 => Classical.choose (h_surj n (stage_zero_lift_sequence h_surj x n))

/-- Helper for Lemma 15.13.4: the recursively chosen lift sequence maps to the previous stage
under each successor transition. -/
lemma stage_zero_lift_sequence_step
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (x : stageRing F 0) (n : ℕ) :
    (stageMap F n) (stage_zero_lift_sequence (F := F) h_surj x (n + 1)) =
      stage_zero_lift_sequence (F := F) h_surj x n := by
  exact Classical.choose_spec
    (h_surj n (stage_zero_lift_sequence (F := F) h_surj x n))

/-- Helper for Lemma 15.13.4: the recursively chosen lift sequence is compatible with every long
transition map. -/
lemma stage_zero_lift_sequence_transition
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (x : stageRing F 0) :
    ∀ ⦃i j : ℕ⦄ (hij : i ≤ j),
      (F.transitionMap hij).hom (stage_zero_lift_sequence (F := F) h_surj x j) =
        stage_zero_lift_sequence (F := F) h_surj x i := by
  intro i j hij
  induction hij with
  | refl =>
      rfl
  | @step j hij ih =>
      rw [transitionMap_comp (F := F) hij (Nat.le_succ j)]
      change
        (F.transitionMap hij).hom
            ((F.stepMap j).hom (stage_zero_lift_sequence (F := F) h_surj x (j + 1))) =
          stage_zero_lift_sequence (F := F) h_surj x i
      rw [stage_zero_lift_sequence_step (F := F) h_surj x j]
      exact ih

/-- Helper for Lemma 15.13.4: the recursively chosen lifts define a compatible section of the
underlying sequential ring system. -/
lemma stage_zero_lift_section_compatible
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (x : stageRing F 0) :
    ∀ {j k : ℕᵒᵖ} (g : j ⟶ k),
      ((ownerSystem F).map g)
          (stage_zero_lift_sequence (F := F) h_surj x j.unop) =
        stage_zero_lift_sequence (F := F) h_surj x k.unop := by
  intro j k g
  have hkj : k.unop ≤ j.unop := leOfHom g.unop
  have hg : g = (homOfLE hkj).op := by
    subsingleton
  simpa [ownerSystem, sequentialRingSystem, hg] using
    stage_zero_lift_sequence_transition (F := F) h_surj x hkj

/-- Helper for Lemma 15.13.4: the recursively chosen lifts assemble into a section of the
underlying ring-valued inverse system. -/
private noncomputable abbrev stage_zero_lift_section
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (x : stageRing F 0) :
    ((ownerSystem F) ⋙ forget CommRingCat).sections :=
  ⟨fun j ↦ stage_zero_lift_sequence (F := F) h_surj x j.unop,
    stage_zero_lift_section_compatible (F := F) h_surj x⟩

/-- Helper for Lemma 15.13.4: each step map in the owner system is surjective once the original
step maps are surjective. -/
lemma ownerSystem_step_surjective
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom) :
    ∀ n : ℕ, Function.Surjective ((ownerSystem F).stepMap n).hom := by
  intro n
  simpa [ownerSystem, sequentialRingSystem, stageMap] using h_surj n

/-- Helper for Lemma 15.13.4: the locally nilpotent-kernel hypothesis transfers to the owner
system without changing the step ideals. -/
lemma ownerSystem_step_locnil
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1)))) :
    ∀ n : ℕ,
      RingHom.ker ((ownerSystem F).stepMap n).hom ≤
        nilradical ((ownerSystem F).obj (op (n + 1))) := by
  intro n
  simpa [ownerSystem, sequentialRingSystem, stageMap] using h_locnil n

lemma limitProjection_zero_surjective_of_step_surjective
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom) :
    Function.Surjective (limit.π (ownerSystem F) (op 0)).hom := by
  intro x
  refine ⟨limit_of_underlying_sections (F := ownerSystem F)
      (stage_zero_lift_section (F := F) h_surj x), ?_⟩
  -- Proof comment: the section was chosen so that its stage-0 coordinate is exactly the given
  -- element.
  simpa [stage_zero_lift_section, stage_zero_lift_sequence] using
    limit_π_limit_of_underlying_sections (F := ownerSystem F)
      (stage_zero_lift_section (F := F) h_surj x) (op 0)

/-- Helper for Lemma 15.13.4: the quotient of the inverse-limit ring by the kernel of the stage-0
projection is canonically the stage-0 ring. -/
noncomputable abbrev quotient_stage_zero_transport
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom) :
    inverseLimitRing F ⧸ RingHom.ker (limit.π (ownerSystem F) (op 0)).hom ≃+* stageRing F 0 :=
  RingHom.quotientKerEquivOfSurjective
    (f := (limit.π (ownerSystem F) (op 0)).hom)
    (limitProjection_zero_surjective_of_step_surjective (F := F) h_surj)

/-- Helper for Lemma 15.13.4: after transporting scalars across
`A ⧸ ker(A → A₀) ≃ A₀`, the special fiber `M₀` is a finite projective module over the quotient of
the inverse-limit ring. -/
lemma stage_zero_finiteProjective_over_limitQuotient_property
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom) :
    finiteProjectiveModuleProperty
      (inverseLimitRing F ⧸ RingHom.ker (limit.π (ownerSystem F) (op 0)).hom)
      ((ModuleCat.restrictScalars (quotient_stage_zero_transport (F := F) h_surj).symm.toRingHom).obj
        (stageModule F M 0)) := by
  constructor <;> infer_instance

/-- Helper for Lemma 15.13.4: after transporting scalars across
`A ⧸ ker(A → A₀) ≃ A₀`, the special fiber `M₀` is a finite projective module over the quotient of
the inverse-limit ring. -/
noncomputable abbrev stage_zero_finiteProjective_over_limitQuotient
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom) :
    FiniteProjectiveModuleCat
      (inverseLimitRing F ⧸ RingHom.ker (limit.π (ownerSystem F) (op 0)).hom) :=
  ⟨(ModuleCat.restrictScalars (quotient_stage_zero_transport (F := F) h_surj).symm.toRingHom).obj
      (stageModule F M 0),
    stage_zero_finiteProjective_over_limitQuotient_property (F := F) (M := M) h_surj⟩

/-- Helper for Lemma 15.13.4: the transported special fiber lifts to a finite projective module
over the inverse-limit ring because the stage-0 projection kernel is henselian. -/
lemma exists_stage_zero_finiteProjective_lift
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1)))) :
    ∃ P : FiniteProjectiveModuleCat (inverseLimitRing F),
      Nonempty
        ((finiteProjectiveReductionFunctor
            (RingHom.ker (limit.π (ownerSystem F) (op 0)).hom)).obj P ≅
          stage_zero_finiteProjective_over_limitQuotient (F := F) (M := M) h_surj) := by
  letI :
      HenselianRing (inverseLimitRing F)
        (RingHom.ker (limit.π (ownerSystem F) (op 0)).hom) := by
    simpa [inverseLimitRing] using
      (henselianRing_limitProjection_ker_of_surjective_of_isLocallyNilpotent
        (F := ownerSystem F) 0
        (ownerSystem_step_surjective (F := F) h_surj)
        (ownerSystem_step_locnil (F := F) h_locnil))
  -- Proof comment: this is exactly the object-level lifting statement from Lemma `15.13.1`,
  -- applied to the quotient-model version of the special fiber.
  simpa using exists_finiteProjective_lift_of_henselianRing
    (R := inverseLimitRing F)
    (I := RingHom.ker (limit.π (ownerSystem F) (op 0)).hom)
    (stage_zero_finiteProjective_over_limitQuotient (F := F) (M := M) h_surj)

/-- Helper for Lemma 15.13.4: the long kernel `J_n = ker(A_n → A₀)` controlling reduction to the
special fiber. -/
private abbrev stage_zero_kernel (n : ℕ) : Ideal (stageRing F n) :=
  RingHom.ker (F.transitionMap (Nat.zero_le n)).hom

/-- Helper for Lemma 15.13.4: the long kernel `J_n = ker(A_n → A₀)` is locally nilpotent. -/
lemma stage_zero_kernel_isLocallyNilpotent
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1))))
    (n : ℕ) :
    (stage_zero_kernel (F := F) n).IsLocallyNilpotent := by
  -- Proof comment: Lemma `15.11.3` already proves local nilpotence for every long transition
  -- kernel, and `stage_zero_kernel` is exactly the `0 ≤ n` specialization.
  simpa [stage_zero_kernel, stageRing] using
    transitionMap_ker_isLocallyNilpotent (F := F) 0 h_locnil (Nat.zero_le n)

/-- Helper for Lemma 15.13.4: the long kernel `J_n = ker(A_n → A₀)` lies in the Jacobson radical
of `A_n`. -/
lemma stage_zero_kernel_le_jacobson
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1))))
    (n : ℕ) :
    stage_zero_kernel (F := F) n ≤ Ring.jacobson (stageRing F n) := by
  letI :
      HenselianRing (stageRing F n) (stage_zero_kernel (F := F) n) :=
    henselianRing_of_isLocallyNilpotent
      (A := stageRing F n)
      (I := stage_zero_kernel (F := F) n)
      (stage_zero_kernel_isLocallyNilpotent (F := F) h_locnil n)
  -- Proof comment: once `(A_n, J_n)` is henselian, the canonical Jacobson containment is the
  -- exact ring-theoretic input used later by the source proof's comparison lemma.
  exact Ideal.le_ring_jacobson_of_henselianRing
    (A := stageRing F n)
    (I := stage_zero_kernel (F := F) n)

/-- Helper for Lemma 15.13.4: quotienting the stage ring `A_n` by `J_n = ker(A_n → A₀)`
recovers the special-fiber ring `A₀`. -/
noncomputable abbrev stage_zero_quotient_ring_equiv
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (n : ℕ) :
    stageRing F n ⧸ stage_zero_kernel (F := F) n ≃+* stageRing F 0 :=
  RingHom.quotientKerEquivOfSurjective
    (f := (F.transitionMap (Nat.zero_le n)).hom)
    (transitionMap_surjective_of_step_surjective (F := F) h_surj (Nat.zero_le n))

/-- Helper for Lemma 15.13.4: a surjective base-change equivalence transports the standard
tensor/quotient model into a quotient equivalence over the target ring. -/
noncomputable theorem quotient_transport_of_surjective_baseChange_equiv
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    (π : R →+* S)
    {N : Type*} [AddCommGroup N] [Module R N]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (hπ : Function.Surjective π)
    (e : let _ : Algebra R S := π.toAlgebra
      S ⊗[R] N ≃ₗ[S] Q) :
    let _ : Algebra R S := π.toAlgebra
    let eS : R ⧸ RingHom.ker π ≃+* S :=
      RingHom.quotientKerEquivOfSurjective (f := π) hπ
    let _ : Module S (N ⧸ (RingHom.ker π • (⊤ : Submodule R N))) :=
      Module.compHom _ eS.symm.toRingHom
    (N ⧸ (RingHom.ker π • (⊤ : Submodule R N))) ≃ₗ[S] Q := by
  let _ : Algebra R S := π.toAlgebra
  let eS : R ⧸ RingHom.ker π ≃+* S :=
    RingHom.quotientKerEquivOfSurjective (f := π) hπ
  let _ : Module S (N ⧸ (RingHom.ker π • (⊤ : Submodule R N))) :=
    Module.compHom _ eS.symm.toRingHom
  -- Proof comment: first rewrite the quotient via `TensorProduct.quotTensorEquivQuotSMul`, then
  -- transport scalars across `R ⧸ ker(π) ≃ S`, and finally compose with the given base-change
  -- equivalence.
  exact
    ((((TensorProduct.congr eS.symm.toLinearEquiv (LinearEquiv.refl R N)) ≪≫ₗ
        TensorProduct.quotTensorEquivQuotSMul N (RingHom.ker π)).extendScalarsOfSurjective
          hπ).symm).trans e

/-- Helper for Lemma 15.13.4: once the long base change from `A_n` to `A₀` is known, the stage
module quotient by `J_n = ker(A_n → A₀)` is canonically the special fiber `M₀`. -/
noncomputable theorem stage_module_quotient_to_zero_equiv_of_baseChange
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (n : ℕ)
    (e :
      let _ : Algebra (stageRing F n) (stageRing F 0) :=
        RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
      (stageRing F 0) ⊗[stageRing F n] stageModule F M n ≃ₗ[stageRing F 0] stageModule F M 0) :
    let _ : Algebra (stageRing F n) (stageRing F 0) :=
      RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
    let _ :
        Module (stageRing F 0)
          (stageModule F M n ⧸
            (stage_zero_kernel (F := F) n •
              (⊤ : Submodule (stageRing F n) (stageModule F M n)))) :=
      Module.compHom _
        (stage_zero_quotient_ring_equiv (F := F) h_surj n).symm.toRingHom
    (stageModule F M n ⧸
        (stage_zero_kernel (F := F) n •
          (⊤ : Submodule (stageRing F n) (stageModule F M n)))) ≃ₗ[stageRing F 0]
      stageModule F M 0 := by
  let _ : Algebra (stageRing F n) (stageRing F 0) :=
    RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
  -- Proof comment: this is the generic quotient transport specialized to the long transition
  -- map `A_n → A₀`.
  simpa [stage_zero_kernel] using
    (quotient_transport_of_surjective_baseChange_equiv
      (π := (F.transitionMap (Nat.zero_le n)).hom)
      (N := stageModule F M n)
      (Q := stageModule F M 0)
      (hπ := transitionMap_surjective_of_step_surjective (F := F) h_surj (Nat.zero_le n))
      e)

/-- Helper for Lemma 15.13.4: the lifted finite-projective special fiber can be normalized to an
explicit `A₀ ⊗[A] P ≃ M₀` linear equivalence. -/
noncomputable theorem lifted_special_fiber_linear_equiv
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    {P : FiniteProjectiveModuleCat (inverseLimitRing F)}
    (hP :
      Nonempty
        ((finiteProjectiveReductionFunctor
            (RingHom.ker (limit.π (ownerSystem F) (op 0)).hom)).obj P ≅
          stage_zero_finiteProjective_over_limitQuotient (F := F) (M := M) h_surj)) :
    ((stageRing F 0) ⊗[inverseLimitRing F] P.obj) ≃ₗ[stageRing F 0] stageModule F M 0 := by
  rcases hP with ⟨e⟩
  let I : Ideal (inverseLimitRing F) :=
    RingHom.ker (limit.π (ownerSystem F) (op 0)).hom
  have eQuot :
      let _ : Module (inverseLimitRing F ⧸ I) (stageModule F M 0) :=
        Module.compHom _
          (quotient_stage_zero_transport (F := F) h_surj).symm.toRingHom
      ((inverseLimitRing F ⧸ I) ⊗[inverseLimitRing F] P.obj) ≃ₗ[inverseLimitRing F ⧸ I]
        stageModule F M 0 := by
    -- Proof comment: unwrap the reduction functor once and identify reduction with the standard
    -- quotient tensor model.
    simpa [I, stage_zero_finiteProjective_over_limitQuotient] using
      (TensorProduct.quotTensorEquivQuotSMul P.obj I).symm.trans e.toLinearEquiv
  have hsurjTransport :
      Function.Surjective (quotient_stage_zero_transport (F := F) h_surj).toRingHom := by
    intro x
    refine ⟨(quotient_stage_zero_transport (F := F) h_surj).symm x, ?_⟩
    simp
  -- Proof comment: now transport the quotient-ring linear equivalence across the canonical
  -- ring isomorphism `A ⧸ ker(A → A₀) ≃ A₀`.
  simpa [I] using eQuot.extendScalarsOfSurjective hsurjTransport

/-- Helper for Lemma 15.13.4: after first base changing the lifted projective model `P` to the
stage ring `A_n`, one more base change along `A_n → A₀` still recovers the special fiber `M₀`. -/
noncomputable theorem lifted_tensor_baseChange_chain_to_zero
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    {P : FiniteProjectiveModuleCat (inverseLimitRing F)}
    (hP :
      Nonempty
        ((finiteProjectiveReductionFunctor
            (RingHom.ker (limit.π (ownerSystem F) (op 0)).hom)).obj P ≅
          stage_zero_finiteProjective_over_limitQuotient (F := F) (M := M) h_surj)) :
    ∀ n : ℕ,
      let _ : Algebra (stageRing F n) (stageRing F 0) :=
        RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
      (stageRing F 0) ⊗[stageRing F n] ((stageRing F n) ⊗[inverseLimitRing F] P.obj) ≃ₗ
        [stageRing F 0] stageModule F M 0 := by
  intro n
  have hPzero :
      ((stageRing F 0) ⊗[inverseLimitRing F] P.obj) ≃ₗ[stageRing F 0] stageModule F M 0 :=
    lifted_special_fiber_linear_equiv (F := F) (M := M) h_surj hP
  -- Proof comment: reassociate the two successive scalar extensions so that the intermediate
  -- `A_n`-base change collapses to the already normalized special fiber comparison.
  exact
    (TensorProduct.AlgebraTensorModule.assoc
      (inverseLimitRing F)
      (inverseLimitRing F)
      (stageRing F n)
      (stageRing F n)
      (stageRing F 0)
      P.obj).trans hPzero

/-- Helper for Lemma 15.13.4: recursively composing the successor base-change isomorphisms gives
the long base-change equivalence `A₀ ⊗[A_n] M_n ≃ M₀`. -/
noncomputable theorem stage_module_baseChange_chain_to_zero
    (h_baseChange :
      ∀ n : ℕ, Function.Bijective (stageBaseChangeComparison F M n)) :
    ∀ n : ℕ,
      let _ : Algebra (stageRing F n) (stageRing F 0) :=
        RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
      (stageRing F 0) ⊗[stageRing F n] stageModule F M n ≃ₗ[stageRing F 0] stageModule F M 0 := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the stage-`0` tensor collapses by the usual left-unit equivalence.
      simpa using
        (Algebra.TensorProduct.lidOfCompatibleSMul
          (stageRing F 0) (stageRing F 0) (stageModule F M 0)).toLinearEquiv
  | succ n ih =>
      have eStep :
          (stageRing F n) ⊗[stageRing F (n + 1)] stageModule F M (n + 1) ≃ₗ[stageRing F n]
            stageModule F M n :=
        LinearEquiv.ofBijective (stageBaseChangeComparison F M n) (h_baseChange n)
      -- Proof comment: reassociate the long tensor to factor through the already-known successor
      -- base change `A_n ⊗[A_{n+1}] M_{n+1} ≃ M_n`, then apply the induction hypothesis.
      exact
        (TensorProduct.AlgebraTensorModule.assoc
          (stageRing F (n + 1))
          (stageRing F (n + 1))
          (stageRing F 0)
          (stageRing F 0)
          (stageRing F n)
          (stageModule F M (n + 1))).trans <|
          (TensorProduct.congr (LinearEquiv.refl (stageRing F 0) _) eStep).trans ih

/-- Helper for Lemma 15.13.4: quotient reduction commutes with tensoring a linear map by the
quotient ring. -/
private theorem quotientMapByIdeal_lTensor_naturality
    {R : Type*} [CommRing R]
    {N : Type*} [AddCommGroup N] [Module R N]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    {I : Ideal R} (f : N →ₗ[R] Q) :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul N I =
      TensorProduct.quotTensorEquivQuotSMul Q I ∘ₗ f.lTensor (R ⧸ I) := by
  -- Proof comment: both sides agree on pure tensors, so tensor extensionality reduces the claim
  -- to the defining formula for `LinearMap.quotientMapByIdeal`.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 15.13.4: the quotient of the lifted tensor model by the long kernel
`J_n = ker(A_n → A₀)` is canonically the special fiber `M₀`. -/
noncomputable theorem lifted_tensor_quotient_to_zero_equiv
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    {P : FiniteProjectiveModuleCat (inverseLimitRing F)}
    (hP :
      Nonempty
        ((finiteProjectiveReductionFunctor
            (RingHom.ker (limit.π (ownerSystem F) (op 0)).hom)).obj P ≅
          stage_zero_finiteProjective_over_limitQuotient (F := F) (M := M) h_surj)) :
    ∀ n : ℕ,
      let _ : Algebra (stageRing F n) (stageRing F 0) :=
        RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
      let _ :
          Module (stageRing F 0)
            (((stageRing F n) ⊗[inverseLimitRing F] P.obj) ⧸
              (stage_zero_kernel (F := F) n •
                (⊤ :
                  Submodule (stageRing F n)
                    ((stageRing F n) ⊗[inverseLimitRing F] P.obj)))) :=
        Module.compHom _
          (stage_zero_quotient_ring_equiv (F := F) h_surj n).symm.toRingHom
      (((stageRing F n) ⊗[inverseLimitRing F] P.obj) ⧸
          (stage_zero_kernel (F := F) n •
            (⊤ :
              Submodule (stageRing F n)
                ((stageRing F n) ⊗[inverseLimitRing F] P.obj)))) ≃ₗ[stageRing F 0]
        stageModule F M 0 := by
  intro n
  let _ : Algebra (stageRing F n) (stageRing F 0) :=
    RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
  have e :
      (stageRing F 0) ⊗[stageRing F n] ((stageRing F n) ⊗[inverseLimitRing F] P.obj) ≃ₗ
        [stageRing F 0] stageModule F M 0 :=
    lifted_tensor_baseChange_chain_to_zero (F := F) (M := M) h_surj hP n
  -- Proof comment: specialize the generic quotient transport to the long transition
  -- `A_n → A₀` and the already-normalized tensor comparison.
  simpa [stage_zero_kernel] using
    (quotient_transport_of_surjective_baseChange_equiv
      (π := (F.transitionMap (Nat.zero_le n)).hom)
      (N := ((stageRing F n) ⊗[inverseLimitRing F] P.obj))
      (Q := stageModule F M 0)
      (hπ := transitionMap_surjective_of_step_surjective (F := F) h_surj (Nat.zero_le n))
      e)

/-- Helper for Lemma 15.13.4: the lifted special-fiber equivalence gives the stage-`0`
`A`-linear map `P → M₀` by sending `p` to the class of `1 ⊗ p`. -/
noncomputable def lifted_special_fiber_map
    {P : FiniteProjectiveModuleCat (inverseLimitRing F)}
    (hPzero :
      ((stageRing F 0) ⊗[inverseLimitRing F] P.obj) ≃ₗ[stageRing F 0] stageModule F M 0) :
    P.obj →ₗ[inverseLimitRing F] stageModule F M 0 :=
  (hPzero.restrictScalars (inverseLimitRing F)).toLinearMap.comp
    (TensorProduct.mk (inverseLimitRing F) (stageRing F 0) P.obj 1)

/-- Helper for Lemma 15.13.4: once every stage step `M_{n + 1} → M_n` is surjective over `A`,
projectivity of `P` recursively lifts the stage-`0` map to a compatible family `P → M_n`. -/
private noncomputable def projective_stage_lift_sequence
    {P : FiniteProjectiveModuleCat (inverseLimitRing F)}
    (h_step_surj :
      ∀ n : ℕ,
        Function.Surjective
          (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n)))
    (hPzero :
      ((stageRing F 0) ⊗[inverseLimitRing F] P.obj) ≃ₗ[stageRing F 0] stageModule F M 0) :
    (n : ℕ) → P.obj →ₗ[inverseLimitRing F] stageModule F M n
  | 0 => lifted_special_fiber_map (F := F) (M := M) hPzero
  | n + 1 =>
      Classical.choose <|
        Module.projective_lifting_property
          (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n))
          (projective_stage_lift_sequence h_step_surj hPzero n)
          (h_step_surj n)

/-- Helper for Lemma 15.13.4: the recursively chosen lift sequence maps to the previous stage
under the owner step map. -/
lemma projective_stage_lift_sequence_step
    {P : FiniteProjectiveModuleCat (inverseLimitRing F)}
    (h_step_surj :
      ∀ n : ℕ,
        Function.Surjective
          (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n)))
    (hPzero :
      ((stageRing F 0) ⊗[inverseLimitRing F] P.obj) ≃ₗ[stageRing F 0] stageModule F M 0)
    (n : ℕ) :
    (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n)).comp
        (projective_stage_lift_sequence (F := F) (M := M) h_step_surj hPzero (n + 1)) =
      projective_stage_lift_sequence (F := F) (M := M) h_step_surj hPzero n := by
  -- Proof comment: the `n + 1` lift was chosen by projective lifting so that composing with the
  -- surjective step map recovers the previously constructed stage-`n` map.
  exact Classical.choose_spec <|
    Module.projective_lifting_property
      (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n))
      (projective_stage_lift_sequence (F := F) (M := M) h_step_surj hPzero n)
      (h_step_surj n)

/-- Helper for Lemma 15.13.4: package the recursively chosen lifts as the compatible family
`ψ_n : P → M_n` used by the source proof. -/
lemma exists_compatible_projective_stage_lifts
    {P : FiniteProjectiveModuleCat (inverseLimitRing F)}
    (h_step_surj :
      ∀ n : ℕ,
        Function.Surjective
          (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n)))
    (hPzero :
      ((stageRing F 0) ⊗[inverseLimitRing F] P.obj) ≃ₗ[stageRing F 0] stageModule F M 0) :
    ∃ ψ : ∀ n : ℕ, P.obj →ₗ[inverseLimitRing F] stageModule F M n,
      ψ 0 = lifted_special_fiber_map (F := F) (M := M) hPzero ∧
      ∀ n : ℕ,
        (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n)).comp (ψ (n + 1)) =
          ψ n := by
  refine ⟨projective_stage_lift_sequence (F := F) (M := M) h_step_surj hPzero, rfl, ?_⟩
  intro n
  exact projective_stage_lift_sequence_step (F := F) (M := M) h_step_surj hPzero n

/-- Helper for Lemma 15.13.4: after transporting the compatible lifts `ψ_n : P → M_n` all the
way down to the special fiber, the pure tensor `1 ⊗ ψ_n(p)` still agrees with the original
special-fiber comparison `A₀ ⊗[A] P ≃ M₀`. -/
lemma projective_lift_stage_baseChange_to_zero_on_unit_tmul
    (h_baseChange :
      ∀ n : ℕ, Function.Bijective (stageBaseChangeComparison F M n))
    {P : FiniteProjectiveModuleCat (inverseLimitRing F)}
    {ψ : ∀ n : ℕ, P.obj →ₗ[inverseLimitRing F] stageModule F M n}
    (hPzero :
      ((stageRing F 0) ⊗[inverseLimitRing F] P.obj) ≃ₗ[stageRing F 0] stageModule F M 0)
    (hψzero : ψ 0 = lifted_special_fiber_map (F := F) (M := M) hPzero)
    (hψstep :
      ∀ n : ℕ,
        (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n)).comp (ψ (n + 1)) =
          ψ n) :
    ∀ n : ℕ, ∀ p : P.obj,
      let _ : Algebra (stageRing F n) (stageRing F 0) :=
        RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
      stage_module_baseChange_chain_to_zero (F := F) (M := M) h_baseChange n
          ((1 : stageRing F 0) ⊗ₜ[stageRing F n] ψ n p) =
        hPzero ((1 : stageRing F 0) ⊗ₜ[inverseLimitRing F] p) := by
  intro n
  induction n with
  | zero =>
      intro p
      -- Proof comment: at the special fiber, the chosen lift is exactly the normalized stage-`0`
      -- map, so the comparison collapses to the defining formula for `lifted_special_fiber_map`.
      simp [stage_module_baseChange_chain_to_zero, hψzero, lifted_special_fiber_map,
        LinearMap.liftBaseChange_tmul]
  | succ n ih =>
      intro p
      have hstep_apply : stageStep F M n (ψ (n + 1) p) = ψ n p := by
        change
          (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n)) (ψ (n + 1) p) =
            ψ n p
        simpa using LinearMap.congr_fun (hψstep n) p
      -- Proof comment: the recursive definition of the long base-change comparison first inserts
      -- the successor base change `A_n ⊗[A_{n+1}] M_{n+1} → M_n`, and compatibility of the lifts
      -- turns that step into the previous-stage pure tensor handled by the induction hypothesis.
      simpa [stage_module_baseChange_chain_to_zero, stageBaseChangeComparison,
        LinearMap.liftBaseChange_tmul, hstep_apply] using ih p

/-- Helper for Lemma 15.13.4: once the special fiber has been lifted to the inverse-limit ring,
the remaining source-faithful task is to compare that lift with every stage and hence with the
canonical inverse-limit module. -/
lemma exists_projective_inverseLimit_model_with_stagewise_baseChange
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1))))
    (h_baseChange :
      ∀ n : ℕ, Function.Bijective (stageBaseChangeComparison F M n)) :
    ∃ P : FiniteProjectiveModuleCat (inverseLimitRing F),
      Nonempty
        (P.obj ≅
          ((ringedModuleInverseLimitFunctor (stageRing F) (stageMap F)).obj M)) ∧
      ∀ n : ℕ, Function.Bijective (inverseLimitBaseChangeComparison F M n) := by
  -- Route correction: the previous attempt stalled before packaging the quotient transport
  -- `A ⧸ ker(A → A₀) ≃ A₀`. The transport and the henselian lift of the special fiber are now
  -- isolated above, so the remaining blocker is the stagewise comparison with the long kernels.
  obtain ⟨P, hP⟩ :=
    exists_stage_zero_finiteProjective_lift (F := F) (M := M) h_surj h_locnil
  have hJjac :
      ∀ n : ℕ, stage_zero_kernel (F := F) n ≤ Ring.jacobson (stageRing F n) :=
    stage_zero_kernel_le_jacobson (F := F) h_locnil
  have hJquot :
      ∀ n : ℕ, stageRing F n ⧸ stage_zero_kernel (F := F) n ≃+* stageRing F 0 :=
    stage_zero_quotient_ring_equiv (F := F) h_surj
  have hPzero :
      ((stageRing F 0) ⊗[inverseLimitRing F] P.obj) ≃ₗ[stageRing F 0] stageModule F M 0 :=
    lifted_special_fiber_linear_equiv (F := F) (M := M) h_surj hP
  have hPtensorZero :
      ∀ n : ℕ,
        let _ : Algebra (stageRing F n) (stageRing F 0) :=
          RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
        (stageRing F 0) ⊗[stageRing F n] ((stageRing F n) ⊗[inverseLimitRing F] P.obj) ≃ₗ
          [stageRing F 0] stageModule F M 0 :=
    lifted_tensor_baseChange_chain_to_zero (F := F) (M := M) h_surj hP
  have hMzero :
      ∀ n : ℕ,
        let _ : Algebra (stageRing F n) (stageRing F 0) :=
          RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
        (stageRing F 0) ⊗[stageRing F n] stageModule F M n ≃ₗ[stageRing F 0] stageModule F M 0 :=
    stage_module_baseChange_chain_to_zero (F := F) (M := M) h_baseChange
  have hPtensorQuotZero :
      ∀ n : ℕ,
        let _ : Algebra (stageRing F n) (stageRing F 0) :=
          RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
        let _ :
            Module (stageRing F 0)
              (((stageRing F n) ⊗[inverseLimitRing F] P.obj) ⧸
                (stage_zero_kernel (F := F) n •
                  (⊤ :
                    Submodule (stageRing F n)
                      ((stageRing F n) ⊗[inverseLimitRing F] P.obj)))) :=
          Module.compHom _
            (stage_zero_quotient_ring_equiv (F := F) h_surj n).symm.toRingHom
        (((stageRing F n) ⊗[inverseLimitRing F] P.obj) ⧸
            (stage_zero_kernel (F := F) n •
              (⊤ :
                Submodule (stageRing F n)
                  ((stageRing F n) ⊗[inverseLimitRing F] P.obj)))) ≃ₗ[stageRing F 0]
          stageModule F M 0 :=
    lifted_tensor_quotient_to_zero_equiv (F := F) (M := M) h_surj hP
  have hMquotZero :
      ∀ n : ℕ,
        let _ : Algebra (stageRing F n) (stageRing F 0) :=
          RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
        let _ :
            Module (stageRing F 0)
              (stageModule F M n ⧸
                (stage_zero_kernel (F := F) n •
                  (⊤ : Submodule (stageRing F n) (stageModule F M n)))) :=
          Module.compHom _
            (stage_zero_quotient_ring_equiv (F := F) h_surj n).symm.toRingHom
        (stageModule F M n ⧸
            (stage_zero_kernel (F := F) n •
              (⊤ : Submodule (stageRing F n) (stageModule F M n)))) ≃ₗ[stageRing F 0]
          stageModule F M 0 := by
    intro n
    exact
      stage_module_quotient_to_zero_equiv_of_baseChange
        (F := F) (M := M) h_surj n (hMzero n)
  have hStepSurjA :
      ∀ n : ℕ,
        Function.Surjective
          (LinearMap.restrictScalars (inverseLimitRing F) (stageStep F M n)) := by
    intro n
    -- Proof comment: bijectivity of the successor base-change map already forces the untensored
    -- step map to be surjective, and restriction of scalars does not change the underlying
    -- function.
    simpa using
      stageStep_surjective_of_baseChange_bijective (F := F) (M := M) n (h_surj n)
        (h_baseChange n)
  obtain ⟨ψ, hψzero, hψstep⟩ :=
    exists_compatible_projective_stage_lifts
      (F := F) (M := M) (P := P) hStepSurjA hPzero
  have hψzeroFiber :
      ∀ n : ℕ, ∀ p : P.obj,
        let _ : Algebra (stageRing F n) (stageRing F 0) :=
          RingHom.toAlgebra (F.transitionMap (Nat.zero_le n)).hom
        stage_module_baseChange_chain_to_zero (F := F) (M := M) h_baseChange n
            ((1 : stageRing F 0) ⊗ₜ[stageRing F n] ψ n p) =
          hPzero ((1 : stageRing F 0) ⊗ₜ[inverseLimitRing F] p) :=
    projective_lift_stage_baseChange_to_zero_on_unit_tmul
      (F := F) (M := M) h_baseChange hPzero hψzero hψstep
  -- TODO: the quotient-transport step is now isolated in
  -- `stage_module_quotient_to_zero_equiv_of_baseChange` and its tensor analogue, and the new
  -- generator-level lemma `hψzeroFiber` has now verified the pre-quotient special-fiber square on
  -- the canonical tensors `1 ⊗ ψ_n(p)`. To finish the source proof, extend this to a full
  -- tensor-map equality for `φ_n := (ψ n).liftBaseChange (stageRing F n)`, compare the induced
  -- quotient maps modulo `J_n = ker(A_n → A₀)` through `hPtensorQuotZero n` and `hMquotZero n`,
  -- upgrade each `φ_n` to an isomorphism via the Jacobson-radical criterion, and finally package
  -- the stagewise isomorphisms into the inverse-limit comparison `P ≃ lim_n M_n`.
  let _ := P
  let _ := hP
  let _ := hJjac
  let _ := hJquot
  let _ := hPzero
  let _ := hPtensorZero
  let _ := hPtensorQuotZero
  let _ := hMzero
  let _ := hMquotZero
  let _ := ψ
  let _ := hψzero
  let _ := hψstep
  let _ := hψzeroFiber
  sorry

-- Proof sketch: apply Lemma `15.11.3` to the inverse system of rings to see that the pair
-- `(A, ker(A → A₀))` is henselian. Then use Lemma `15.13.1` to lift the finite projective
-- `A₀`-module `M₀` to a finite projective `A`-module, and compare its reductions to the later
-- stages by Lemmas `15.3.4` and `15.3.5`.
/-- Lemma 15.13.4 (1): for a sequential inverse system of rings with surjective, locally
nilpotent transition kernels and compatible finite modules whose positive stages are flat, whose
initial stage is projective, and whose successive base changes are isomorphic, the inverse limit
module `M = lim M_n` is finite over the inverse limit ring `A = lim A_n`. -/
theorem inverseLimitModule_finite_of_surjective_locnil_and_stagewise_flat
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1))))
    (h_baseChange :
      ∀ n : ℕ, Function.Bijective (stageBaseChangeComparison F M n)) :
    Module.Finite
      ((limit
        (sequentialRingSystem
          (fun n ↦ (F.obj (op n) : Type u))
          (fun n ↦ (F.stepMap n).hom)) : CommRingCat.{u}) : Type u)
      ((ringedModuleInverseLimitFunctor
        (fun n ↦ (F.obj (op n) : Type u))
        (fun n ↦ (F.stepMap n).hom)).obj M) :=
  by
    obtain ⟨P, hPiso, _⟩ :=
      exists_projective_inverseLimit_model_with_stagewise_baseChange
        (F := F) (M := M) h_surj h_locnil h_baseChange
    rcases hPiso with ⟨e⟩
    -- Proof comment: finite generation transfers across the identified finite projective model.
    exact Module.Finite.equiv e.toLinearEquiv

-- Proof sketch: the same lifting argument as in part `(1)` produces a finite projective
-- `A`-module lifting `M₀`; the comparison with each stage `M_n` is an isomorphism by Lemmas
-- `15.3.4` and `15.3.5`, so the canonical inverse limit module is projective.
/-- Lemma 15.13.4 (2): under the same hypotheses, the inverse limit module `M = lim M_n` is
projective over the inverse limit ring `A = lim A_n`. -/
theorem inverseLimitModule_projective_of_surjective_locnil_and_stagewise_flat
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1))))
    (h_baseChange :
      ∀ n : ℕ, Function.Bijective (stageBaseChangeComparison F M n)) :
    Module.Projective
      ((limit
        (sequentialRingSystem
          (fun n ↦ (F.obj (op n) : Type u))
          (fun n ↦ (F.stepMap n).hom)) : CommRingCat.{u}) : Type u)
      ((ringedModuleInverseLimitFunctor
        (fun n ↦ (F.obj (op n) : Type u))
        (fun n ↦ (F.stepMap n).hom)).obj M) :=
  by
    obtain ⟨P, hPiso, _⟩ :=
      exists_projective_inverseLimit_model_with_stagewise_baseChange
        (F := F) (M := M) h_surj h_locnil h_baseChange
    rcases hPiso with ⟨e⟩
    -- Proof comment: projectivity likewise transports across the identified projective model.
    exact Module.Projective.of_equiv e.toLinearEquiv

-- Proof sketch: after lifting `M₀` to a finite projective `A`-module, compare that lift with the
-- inverse limit module. The successive base-change isomorphisms `A_n ⊗[A_{n+1}] M_{n+1} ≃ M_n`
-- and Lemma `15.3.5` identify the base change of the inverse limit module with each stage `M_n`.
/-- Lemma 15.13.4 (3): for every stage `n`, base change of the inverse limit module `M = lim M_n`
from `A = lim A_n` to `A_n` recovers the stage module `M_n`. -/
theorem inverseLimitBaseChangeComparison_bijective_of_surjective_locnil_and_stagewise_flat
    (h_surj : ∀ n : ℕ, Function.Surjective (F.stepMap n).hom)
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (F.stepMap n).hom ≤ nilradical (F.obj (op (n + 1))))
    (h_baseChange :
      ∀ n : ℕ, Function.Bijective (stageBaseChangeComparison F M n))
    (n : ℕ) :
    Function.Bijective (inverseLimitBaseChangeComparison F M n) :=
  by
    obtain ⟨_, _, hstage⟩ :=
      exists_projective_inverseLimit_model_with_stagewise_baseChange
        (F := F) (M := M) h_surj h_locnil h_baseChange
    -- Proof comment: the shared comparison model already records the desired stagewise bijection.
    exact hstage n

end

end
