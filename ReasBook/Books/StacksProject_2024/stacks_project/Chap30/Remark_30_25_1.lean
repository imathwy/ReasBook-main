import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u v

namespace LinearMap

variable {A : Type u} [CommRing A]
variable {M : Type v} {N : Type v}
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- The map induced by a linear map after quotienting source and target by the multiples of an
ideal. -/
def quotientByIdeal (J : Ideal A) (φ : M →ₗ[A] N) :
    (M ⧸ J • (⊤ : Submodule A M)) →ₗ[A] (N ⧸ J • (⊤ : Submodule A N)) :=
  Submodule.mapQ (J • (⊤ : Submodule A M)) (J • (⊤ : Submodule A N)) φ
    (Submodule.smul_top_le_comap_smul_top J φ)

/-- The quotient map `quotientByIdeal` is the map induced by `φ` on the quotients by `J`. -/
theorem quotientByIdeal_def (J : Ideal A) (φ : M →ₗ[A] N) :
    quotientByIdeal J φ =
      Submodule.mapQ (J • (⊤ : Submodule A M)) (J • (⊤ : Submodule A N)) φ
        (Submodule.smul_top_le_comap_smul_top J φ) := sorry

/-- The map induced by a linear map after quotienting source and target by the `n`-th power of an
ideal. -/
def quotientByIdealPower (I : Ideal A) (φ : M →ₗ[A] N) (n : ℕ+) :
    (M ⧸ I ^ (n : ℕ) • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ (n : ℕ) • (⊤ : Submodule A N)) :=
  quotientByIdeal (I ^ (n : ℕ)) φ

/-- The quotient map by an ideal power is the quotient map for the corresponding powered ideal. -/
theorem quotientByIdealPower_def (I : Ideal A) (φ : M →ₗ[A] N) (n : ℕ+) :
    quotientByIdealPower I φ n = quotientByIdeal (I ^ (n : ℕ)) φ := sorry

/-- A linear map has kernel and cokernel annihilated by a positive power of an ideal. The cokernel
is represented by the quotient of the target by the range. -/
@[stacks 0888]
def HasKernelCokernelAnnihilatedByPower (K : Ideal A) (φ : M →ₗ[A] N) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧
    K ^ t ≤ Module.annihilator A φ.ker ∧
      K ^ t ≤ Module.annihilator A (N ⧸ φ.range)

/-- Unfold the condition that the kernel and cokernel of a linear map are annihilated by a
positive power of an ideal. -/
theorem hasKernelCokernelAnnihilatedByPower_iff (K : Ideal A) (φ : M →ₗ[A] N) :
    HasKernelCokernelAnnihilatedByPower K φ ↔
      ∃ t : ℕ, 1 ≤ t ∧
        K ^ t ≤ Module.annihilator A φ.ker ∧
          K ^ t ≤ Module.annihilator A (N ⧸ φ.range) := sorry

/-- The commutative algebra fact used in the affine proof: if the kernel and cokernel of a map are
killed by `K^t`, then after quotienting source and target by any ideal `J`, the kernel and
cokernel are killed by `K^(2*t)`. -/
@[stacks 0888]
theorem quotientByIdeal_kernel_cokernel_annihilated
    (K J : Ideal A) (φ : M →ₗ[A] N) {t : ℕ} (ht : 1 ≤ t)
    (hker : K ^ t ≤ Module.annihilator A φ.ker)
    (hcoker : K ^ t ≤ Module.annihilator A (N ⧸ φ.range)) :
    K ^ (2 * t) ≤ Module.annihilator A (quotientByIdeal J φ).ker ∧
      K ^ (2 * t) ≤
        Module.annihilator A
          ((N ⧸ J • (⊤ : Submodule A N)) ⧸ (quotientByIdeal J φ).range) := sorry

end LinearMap

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the standard quotient-map API
`Submodule.mapQ`, `Module.annihilator`, and the completion owner `AdicCompletion`. Local Chapter
30 files model `Coh(X, I)` affine-locally via finite modules over completions, so the source-facing
statement below keeps the affine completed modules explicit and uses `X.affineOpens` for the
scheme-local quantifiers. -/

section FormalMapAnnihilationPredicates

variable {X : Scheme.{u}} (I K : X.IdealSheafData)
variable (M N : X.affineOpens → Type v)
variable [(U : X.affineOpens) → AddCommGroup (M U)]
variable [(U : X.affineOpens) → Module (Γ(X, U.1)) (M U)]
variable [(U : X.affineOpens) → Module (AdicCompletion (I.ideal U) (Γ(X, U.1))) (M U)]
variable [(U : X.affineOpens) →
  IsScalarTower (Γ(X, U.1)) (AdicCompletion (I.ideal U) (Γ(X, U.1))) (M U)]
variable [(U : X.affineOpens) → AddCommGroup (N U)]
variable [(U : X.affineOpens) → Module (Γ(X, U.1)) (N U)]
variable [(U : X.affineOpens) → Module (AdicCompletion (I.ideal U) (Γ(X, U.1))) (N U)]
variable [(U : X.affineOpens) →
  IsScalarTower (Γ(X, U.1)) (AdicCompletion (I.ideal U) (Γ(X, U.1))) (N U)]

/-- For a fixed positive power, the kernels of all finite quotient-stage maps are annihilated by
the corresponding affine ideal powers. -/
def formalMapFiniteStageKernelsAnnihilatedByPower
    (α : (U : X.affineOpens) →
      M U →ₗ[AdicCompletion (I.ideal U) (Γ(X, U.1))] N U)
    (t : ℕ+) : Prop :=
  ∀ (U : X.affineOpens) (n : ℕ+),
    K.ideal U ^ (t : ℕ) ≤
      Module.annihilator (Γ(X, U.1))
        (LinearMap.quotientByIdealPower (I.ideal U)
          ((α U).restrictScalars (Γ(X, U.1))) n).ker

/-- Unfold the finite-stage kernel annihilation predicate. -/
theorem formalMapFiniteStageKernelsAnnihilatedByPower_iff
    (α : (U : X.affineOpens) →
      M U →ₗ[AdicCompletion (I.ideal U) (Γ(X, U.1))] N U)
    (t : ℕ+) :
    formalMapFiniteStageKernelsAnnihilatedByPower I K M N α t ↔
      ∀ (U : X.affineOpens) (n : ℕ+),
        K.ideal U ^ (t : ℕ) ≤
          Module.annihilator (Γ(X, U.1))
            (LinearMap.quotientByIdealPower (I.ideal U)
              ((α U).restrictScalars (Γ(X, U.1))) n).ker := sorry

/-- For a fixed positive power, the cokernels of all finite quotient-stage maps are annihilated by
the corresponding affine ideal powers. -/
def formalMapFiniteStageCokernelsAnnihilatedByPower
    (α : (U : X.affineOpens) →
      M U →ₗ[AdicCompletion (I.ideal U) (Γ(X, U.1))] N U)
    (t : ℕ+) : Prop :=
  ∀ (U : X.affineOpens) (n : ℕ+),
    K.ideal U ^ (t : ℕ) ≤
      Module.annihilator (Γ(X, U.1))
        ((N U ⧸ I.ideal U ^ (n : ℕ) • (⊤ : Submodule (Γ(X, U.1)) (N U))) ⧸
          (LinearMap.quotientByIdealPower (I.ideal U)
            ((α U).restrictScalars (Γ(X, U.1))) n).range)

/-- Unfold the finite-stage cokernel annihilation predicate. -/
theorem formalMapFiniteStageCokernelsAnnihilatedByPower_iff
    (α : (U : X.affineOpens) →
      M U →ₗ[AdicCompletion (I.ideal U) (Γ(X, U.1))] N U)
    (t : ℕ+) :
    formalMapFiniteStageCokernelsAnnihilatedByPower I K M N α t ↔
      ∀ (U : X.affineOpens) (n : ℕ+),
        K.ideal U ^ (t : ℕ) ≤
          Module.annihilator (Γ(X, U.1))
            ((N U ⧸ I.ideal U ^ (n : ℕ) • (⊤ : Submodule (Γ(X, U.1)) (N U))) ⧸
              (LinearMap.quotientByIdealPower (I.ideal U)
                ((α U).restrictScalars (Γ(X, U.1))) n).range) := sorry

/-- A single positive power of `K` annihilates both kernels and cokernels at every finite
quotient stage. -/
def formalMapFiniteStagesKernelCokernelAnnihilated
    (α : (U : X.affineOpens) →
      M U →ₗ[AdicCompletion (I.ideal U) (Γ(X, U.1))] N U) : Prop :=
  ∃ t : ℕ+,
    formalMapFiniteStageKernelsAnnihilatedByPower I K M N α t ∧
      formalMapFiniteStageCokernelsAnnihilatedByPower I K M N α t

/-- Unfold the uniform finite-stage kernel-and-cokernel annihilation predicate. -/
theorem formalMapFiniteStagesKernelCokernelAnnihilated_iff
    (α : (U : X.affineOpens) →
      M U →ₗ[AdicCompletion (I.ideal U) (Γ(X, U.1))] N U) :
    formalMapFiniteStagesKernelCokernelAnnihilated I K M N α ↔
      ∃ t : ℕ+,
        formalMapFiniteStageKernelsAnnihilatedByPower I K M N α t ∧
          formalMapFiniteStageCokernelsAnnihilatedByPower I K M N α t := sorry

/-- On a finite affine open cover, each completed affine module map has kernel and cokernel
annihilated by some positive power of the affine ideal. -/
def formalMapFiniteAffineCoverKernelCokernelAnnihilated
    (α : (U : X.affineOpens) →
      M U →ₗ[AdicCompletion (I.ideal U) (Γ(X, U.1))] N U) : Prop :=
  ∃ s : Finset X.affineOpens,
    (∀ x : X, ∃ U ∈ s, x ∈ (U : Set X)) ∧
      ∀ U ∈ s, LinearMap.HasKernelCokernelAnnihilatedByPower (K.ideal U)
        ((α U).restrictScalars (Γ(X, U.1)))

/-- Unfold the finite affine-cover annihilation predicate. -/
theorem formalMapFiniteAffineCoverKernelCokernelAnnihilated_iff
    (α : (U : X.affineOpens) →
      M U →ₗ[AdicCompletion (I.ideal U) (Γ(X, U.1))] N U) :
    formalMapFiniteAffineCoverKernelCokernelAnnihilated I K M N α ↔
      ∃ s : Finset X.affineOpens,
        (∀ x : X, ∃ U ∈ s, x ∈ (U : Set X)) ∧
          ∀ U ∈ s, LinearMap.HasKernelCokernelAnnihilatedByPower (K.ideal U)
            ((α U).restrictScalars (Γ(X, U.1))) := sorry

end FormalMapAnnihilationPredicates

/-- Remark 30.25.1: for a morphism of coherent formal modules, the following are equivalent:
a single power of `K` kills the kernels and cokernels of all finite stages, every affine completed
module map has kernel and cokernel killed by some power of the corresponding ideal, and this
affine condition holds on some finite affine open cover. The affine maps are represented as maps
between finite modules over the adic completions, and the finite stages are represented
affine-locally by quotienting their underlying section-module maps by powers of the ideal defining
the formal completion. -/
@[stacks 0888]
theorem coherentFormalMap_kernelCokernelAnnihilation_tfae
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M N : X.affineOpens → Type v)
    [(U : X.affineOpens) → AddCommGroup (M U)]
    [(U : X.affineOpens) → Module (Γ(X, U.1)) (M U)]
    [(U : X.affineOpens) → Module (AdicCompletion (I.ideal U) (Γ(X, U.1))) (M U)]
    [(U : X.affineOpens) →
      IsScalarTower (Γ(X, U.1)) (AdicCompletion (I.ideal U) (Γ(X, U.1))) (M U)]
    [(U : X.affineOpens) → Module.Finite (AdicCompletion (I.ideal U) (Γ(X, U.1))) (M U)]
    [(U : X.affineOpens) → IsAdicComplete (I.ideal U) (M U)]
    [(U : X.affineOpens) → AddCommGroup (N U)]
    [(U : X.affineOpens) → Module (Γ(X, U.1)) (N U)]
    [(U : X.affineOpens) → Module (AdicCompletion (I.ideal U) (Γ(X, U.1))) (N U)]
    [(U : X.affineOpens) →
      IsScalarTower (Γ(X, U.1)) (AdicCompletion (I.ideal U) (Γ(X, U.1))) (N U)]
    [(U : X.affineOpens) → Module.Finite (AdicCompletion (I.ideal U) (Γ(X, U.1))) (N U)]
    [(U : X.affineOpens) → IsAdicComplete (I.ideal U) (N U)]
    (α : (U : X.affineOpens) →
      M U →ₗ[AdicCompletion (I.ideal U) (Γ(X, U.1))] N U) :
    List.TFAE [
      formalMapFiniteStagesKernelCokernelAnnihilated I K M N α,
      ∀ U : X.affineOpens,
        LinearMap.HasKernelCokernelAnnihilatedByPower (K.ideal U)
          ((α U).restrictScalars (Γ(X, U.1))),
      formalMapFiniteAffineCoverKernelCokernelAnnihilated I K M N α
    ] := sorry

end AlgebraicGeometry
