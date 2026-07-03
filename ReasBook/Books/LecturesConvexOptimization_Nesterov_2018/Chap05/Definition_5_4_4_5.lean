import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_3
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped MatrixOrder RealSymmetricMatrixSpace

/- Definition 5.4.4.5 lies in the positive-definite-matrix / logarithmic-barrier domain.

Sampled owner-style declarations in this domain:
* Chapter 5 `𝕊^n` in `Chap05/Definition_5_4_4_1`, the symmetric-matrix carrier owner;
* `𝕊^n₊` in `Chap05/Definition_5_4_4_3`, the chapter owner for the positive-semidefinite cone;
* `Matrix.PosDef` in `Chap01/Definition_1_4_18`, the canonical owner predicate for positive
  definite matrices;
* `analyticBarrier` in `Chap03/Definition_3_62`, the chapter precedent for keeping a logarithmic
  barrier on its intrinsic strict-domain subtype and any ambient formula only as a bridge;
* `epigraphLogarithmicBarrier` in `Chap05/Definition_5_4_3_5`, the chapter owner style for a
  source-facing barrier together with an ambient view.

Best owner abstraction:
* source-facing: the strict cone notation `𝕊^n₊₊` and the log-determinant barrier
  `logDetBarrier n`;
* core/canonical: `Matrix.PosDef`;
* bridge/view: the interior domain `interior (𝕊^n₊ : Set (𝕊^n))`, together with the ambient
  formula `logDetBarrierAmbient n`.

Primitive data:
* `n : ℕ`.

Derived API:
* the strict cone `𝕊^n₊₊`;
* the owner equality `𝕊^n₊₊ = interior (𝕊^n₊)`;
* the intrinsic bridges `StrictPositiveSemidefiniteCone.inv X` and
  `StrictPositiveSemidefiniteCone.sqrtInv X` back to `𝕊^n`;
* the ambient formula `logDetBarrierAmbient n`;
* the source-facing barrier `logDetBarrier n`.

This file therefore keeps the textbook strict cone `𝕊^n₊₊ = int(𝕊^n₊)` on the Chapter 5
symmetric carrier `𝕊^n`, while retaining `Matrix.PosDef` only as the canonical matrix-level bridge
used by later derivative and volumetric-barrier files.
-/

set_option quotPrecheck false in
scoped[RealSymmetricMatrixSpace] notation:arg "𝕊^" n:arg "₊₊" =>
  (interior (𝕊^n₊ : Set (𝕊^n)))

section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

namespace StrictPositiveSemidefiniteCone

/-- The ambient matrix realization of a strict-cone point. -/
def toMatrix (X : 𝕊^n₊₊) : Mat :=
  ((X : SymmMat) : Mat)

attribute [irreducible] StrictPositiveSemidefiniteCone.toMatrix

@[simp] theorem toMatrix_def (X : 𝕊^n₊₊) :
    toMatrix X = ((X : SymmMat) : Mat) :=
  by
    delta toMatrix
    rfl

end StrictPositiveSemidefiniteCone

/-- The strict cone `𝕊ⁿ₊₊` is definitionally the interior of the positive-semidefinite cone
`𝕊ⁿ₊` in the symmetric carrier `𝕊ⁿ`. -/
@[simp] theorem strictPositiveSemidefiniteCone_eq_interior :
    (𝕊^n₊₊ : Set SymmMat) = interior (𝕊^n₊ : Set SymmMat) :=
  rfl

/-- Membership in `𝕊ⁿ₊₊` is exactly membership in the interior of `𝕊ⁿ₊`. -/
@[simp] theorem mem_strictPositiveSemidefiniteCone_iff
    (X : SymmMat) :
    X ∈ 𝕊^n₊₊ ↔ X ∈ interior (𝕊^n₊ : Set SymmMat) :=
  Iff.rfl

/-- A strict-cone point is symmetric as a matrix. -/
theorem strictPositiveSemidefiniteCone_isSymm
    (X : 𝕊^n₊₊) :
    (((X : SymmMat) : Mat)).IsSymm := by
  simpa using
    (RealSymmetricMatrixSpace.mem_iff_isSymm).mp X.1.2

/-- A strict-cone point is Hermitian as a real matrix. -/
theorem strictPositiveSemidefiniteCone_isHermitian
    (X : 𝕊^n₊₊) :
    (((X : SymmMat) : Mat)).IsHermitian := by
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using strictPositiveSemidefiniteCone_isSymm X

/-- Positive definiteness is the canonical matrix-level view of a strict-cone point. -/
theorem strictPositiveSemidefiniteCone_posDef
    (X : 𝕊^n₊₊) :
    (((X : SymmMat) : Mat)).PosDef := by
  sorry

namespace StrictPositiveSemidefiniteCone

private theorem inv_mem (X : 𝕊^n₊₊) :
    ((((X : SymmMat) : Mat)⁻¹)) ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  exact (strictPositiveSemidefiniteCone_isSymm X).inv

/-- The matrix inverse of a strict-cone point, viewed back in `𝕊^n`. -/
def inv (X : 𝕊^n₊₊) : SymmMat :=
  ⟨(((X : SymmMat) : Mat)⁻¹), inv_mem X⟩

@[simp] theorem coe_inv (X : 𝕊^n₊₊) :
    ((StrictPositiveSemidefiniteCone.inv X : SymmMat) : Mat) =
      (((X : SymmMat) : Mat)⁻¹) :=
  rfl

private theorem sqrtInv_mem (X : 𝕊^n₊₊) :
    CFC.sqrt ((((X : SymmMat) : Mat)⁻¹)) ∈ 𝕊^n := by
  sorry

/-- The inverse square root of a strict-cone point, viewed back in `𝕊^n`. -/
def sqrtInv (X : 𝕊^n₊₊) : SymmMat :=
  ⟨CFC.sqrt ((((X : SymmMat) : Mat)⁻¹)), sqrtInv_mem X⟩

@[simp] theorem coe_sqrtInv (X : 𝕊^n₊₊) :
    ((StrictPositiveSemidefiniteCone.sqrtInv X : SymmMat) : Mat) =
      CFC.sqrt ((((X : SymmMat) : Mat)⁻¹)) :=
  rfl

end StrictPositiveSemidefiniteCone

namespace RealSymmetricMatrixSpace

/-- The intrinsic eigenvalues of a strict-cone point are positive. -/
theorem eigenvalues_pos
    (X : 𝕊^n₊₊) (i : Fin n) :
    0 < eigenvalues (X : SymmMat) i := by
  simpa [eigenvalues] using
    (strictPositiveSemidefiniteCone_posDef X).eigenvalues_pos i

end RealSymmetricMatrixSpace

/-- A positive-definite symmetric matrix lies in the strict cone `𝕊ⁿ₊₊`. -/
theorem mem_strictPositiveSemidefiniteCone_of_posDef
    {X : SymmMat} (hX : (X : Mat).PosDef) :
    X ∈ 𝕊^n₊₊ := by
  sorry

end

section

variable (n : ℕ)

/- Definition 5.4.4.5 uses the strict positive-definite cone `𝕊ⁿ₊₊ = int(𝕊ⁿ₊)` as the
intrinsic domain of the log-determinant barrier. -/
#check (𝕊^n₊₊ : Set (𝕊^n))

end

/-
The SDP strict-feasibility owner extends `SemidefiniteOptimizationProblem` by replacing the weak
cone condition `X ∈ 𝕊ⁿ₊` with the strict cone condition `X ∈ 𝕊ⁿ₊₊` while keeping the equality
constraints unchanged. This matches the chapter LP/QCQP owner style for strict feasible sets.
-/
namespace SemidefiniteOptimizationProblem

variable {m n : ℕ}

local notation "SymmMat" => 𝕊^n

/-- The strict feasible set `{X | X ∈ 𝕊ⁿ₊₊ ∧ ∀ i, ⟪Aᵢ, X⟫_F = bᵢ}` of a semidefinite
optimization problem. The objective matrix does not enter this owner because strict feasibility
depends only on the constraints and strict positive definiteness. -/
def strictFeasibleSet
    (problem : SemidefiniteOptimizationProblem n m) : Set SymmMat :=
  (𝕊^n₊₊ : Set SymmMat) ∩ (problem.affineSlice : Set SymmMat)

/-- Membership in `problem.strictFeasibleSet` means satisfying all Frobenius equality constraints
and lying in the strict positive-semidefinite cone `𝕊ⁿ₊₊`. -/
@[simp] theorem mem_strictFeasibleSet_iff
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.strictFeasibleSet ↔
      X ∈ 𝕊^n₊₊ ∧
        ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i := by
  rw [strictFeasibleSet, Set.mem_inter_iff]
  change X ∈ 𝕊^n₊₊ ∧ X ∈ problem.affineSlice ↔
    X ∈ 𝕊^n₊₊ ∧ ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i
  rw [problem.mem_affineSlice_iff]

/-- The subtype of strict feasible matrices for an SDP. -/
abbrev StrictFeasiblePoint
    (problem : SemidefiniteOptimizationProblem n m) :=
  {X : SymmMat // X ∈ problem.strictFeasibleSet}

end SemidefiniteOptimizationProblem

/-- The ambient formula `X ↦ -log det X` on the intrinsic symmetric-matrix carrier `𝕊ⁿ`. It is
only a bridge view; the source-facing owner barrier is `logDetBarrier n` on `𝕊ⁿ₊₊`. -/
def logDetBarrierAmbient (n : ℕ) :
    𝕊^n → ℝ :=
  fun X ↦ -Real.log ((X : Matrix (Fin n) (Fin n) ℝ)).det

/-- Evaluating the ambient log-determinant formula gives `-log (det X)`. -/
@[simp] theorem logDetBarrierAmbient_apply (n : ℕ)
    (X : 𝕊^n) :
    logDetBarrierAmbient n X = -Real.log ((X : Matrix (Fin n) (Fin n) ℝ)).det :=
  rfl

/-- Definition 5.4.4.5: the log-determinant barrier on `int(𝕊ⁿ₊)`, modeled in Lean by the
strict cone `𝕊ⁿ₊₊`. -/
def logDetBarrier (n : ℕ) :
    𝕊^n₊₊ → ℝ :=
  fun X ↦ logDetBarrierAmbient n X.1

/-- Expanding `logDetBarrier n` recovers the ambient bridge formula restricted to the strict
cone `𝕊ⁿ₊₊`. -/
theorem logDetBarrier_def (n : ℕ) :
    logDetBarrier n = fun X ↦ logDetBarrierAmbient n X.1 :=
  rfl

-- Proof sketch: unfold `logDetBarrier`; the definition is exactly the textbook formula
-- `F(X) = -\ln \det X` evaluated on the canonical Lean domain for `int(𝕊ⁿ₊)`.
/-- Evaluating the log-determinant barrier at a positive-definite matrix returns
`-log (det X)`. -/
@[simp] theorem logDetBarrier_apply (n : ℕ)
    (X : 𝕊^n₊₊) :
    logDetBarrier n X = -Real.log ((X : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ).det :=
  rfl

namespace SemidefiniteOptimizationProblem

variable {m n : ℕ}

local notation "SymmMat" => 𝕊^n

/-- The affine translation from the direction space of the canonical affine constraint slice to
the slice itself, based at a strict feasible point. -/
def affineSliceMap
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint) :
    problem.affineSlice.direction →ᵃ[ℝ] SymmMat :=
  ((Submodule.subtype problem.affineSlice.direction :
      problem.affineSlice.direction →ₗ[ℝ] SymmMat).toAffineMap) +ᵥ
    AffineMap.const ℝ problem.affineSlice.direction (xRef : SymmMat)

/-- The strict pullback of `𝕊ⁿ₊₊` to the direction space of the canonical affine constraint
slice, based at a strict feasible point. -/
def affineSliceStrictDomain
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint) :
    Set problem.affineSlice.direction :=
  problem.affineSliceMap xRef ⁻¹' (𝕊^n₊₊ : Set SymmMat)

/-- The log-determinant barrier pulled back from the affine slice to its direction space via a
strict feasible base point. -/
def affineSliceLogDetBarrier
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint) :
    problem.affineSlice.direction → ℝ :=
  fun Δ ↦ logDetBarrierAmbient n (problem.affineSliceMap xRef Δ)

/-- The orthogonal projection of the SDP cost matrix to the direction space of the canonical
affine constraint slice. -/
def affineSliceProjectedCost
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.affineSlice.direction :=
  problem.affineSlice.direction.orthogonalProjection problem.costMatrix

@[simp] theorem affineSliceMap_apply
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    (Δ : problem.affineSlice.direction) :
    problem.affineSliceMap xRef Δ = (Δ : SymmMat) +ᵥ (xRef : SymmMat) :=
  rfl

@[simp] theorem affineSliceLogDetBarrier_apply
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    (Δ : problem.affineSlice.direction) :
    problem.affineSliceLogDetBarrier xRef Δ =
      logDetBarrierAmbient n (problem.affineSliceMap xRef Δ) :=
  rfl

end SemidefiniteOptimizationProblem

end
