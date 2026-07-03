import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
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
        (fun n ↦ (F.stepMap n).hom)).obj M) := sorry

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
        (fun n ↦ (F.stepMap n).hom)).obj M) := sorry

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
    Function.Bijective (inverseLimitBaseChangeComparison F M n) := sorry

end

end
