import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_4_4_4 (from Chap05) -/
noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

variable {m n : ℕ}

/- Definition 5.4.4.4 lies in the semidefinite optimization domain.

Sampled owner-style declarations:
* `𝕊^n` in `Chap05/Definition_5_4_4_1`, the chapter owner for real symmetric matrices;
* `RealSymmetricMatrixSpace.frobeniusInner` in `Chap05/Definition_5_4_4_2`, the chapter owner
  for the Frobenius pairing on `𝕊^n`;
* `PrimalEqualityConstrainedProblem` and `PrimalEqualityConstrainedProblem.equalityFeasibleSet`
  in `Chap02/Definition_2_30`, the project owners for linear equality-constrained minimization;
* `realSymmetricMatrixConstraintMap` in `Chap05/Definition_5_4_4_6`, the chapter owner for the
  linear map encoding the SDP Frobenius equality constraints;
* `realSymmetricMatrixAssociatedAffineSubspace` in `Chap05/Definition_5_4_4_6`, the chapter
  owner for the affine slice cut out by the same equality constraints.

Best owner abstraction:
* source-facing: `SemidefiniteOptimizationProblem n m`, which stores exactly the SDP-specific
  primitive data `C ∈ 𝕊^n`, `A₁, …, Aₘ ∈ 𝕊^n`, and `b`;
* core/canonical: `PrimalEqualityConstrainedProblem (𝕊^n) (EuclideanSpace ℝ (Fin m))`;
* bridge/view:
  `toPrimalEqualityConstrainedProblem`, with the Chapter 1 owner recovered as `primalProblem`.

Primitive data:
* `costMatrix : 𝕊^n`;
* `constraintMatrices : Fin m → 𝕊^n`;
* `rhs : EuclideanSpace ℝ (Fin m)`.

Derived API:
* the linear objective `problem.objective`, equivalently the trace pairing with `C`;
* the canonical equality-constrained owner
  `problem.toPrimalEqualityConstrainedProblem`;
* the SDP feasible set `problem.feasibleSet`, canonically identified with
  `problem.toPrimalEqualityConstrainedProblem.equalityFeasibleSet`;
* the affine slice
  `realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`;
* the derived Chapter 1 optimization owner
  `problem.toSetConstrainedMinimizationProblem`;
* coercion of `problem` to its intrinsic objective function on `𝕊^n`.

Source/core/bridge triage:
* source-facing: the SDP data `(C, A, b)`;
* core/canonical:
  `PrimalEqualityConstrainedProblem (𝕊^n) (EuclideanSpace ℝ (Fin m))`;
* bridge/view:
  `toPrimalEqualityConstrainedProblem`, `affineSlice`, and the derived `primalProblem`.

The file therefore keeps the textbook SDP data as the public source-facing owner, but it no
longer carries a parallel coordinate-model owner on `EuclideanSpace ℝ (Fin n × Fin n)`;
its canonical constraint owner is now `toPrimalEqualityConstrainedProblem`, and the Chapter 1
optimization owner is only the derived `primalProblem` view. -/

/-- Definition 5.4.4.4: a semidefinite optimization problem is determined by a cost matrix
`C ∈ 𝕊^n`, a finite family of constraint matrices `A₁, …, Aₘ ∈ 𝕊^n`, and a right-hand side
vector `b`. Its canonical owner bridge is the equality-constrained problem
`toPrimalEqualityConstrainedProblem`, whose `primalProblem` recovers the Chapter 1 set-constrained
optimization view. -/
structure SemidefiniteOptimizationProblem (n m : ℕ) where
  /-- The cost matrix `C ∈ 𝕊^n`. -/
  costMatrix : 𝕊^n
  /-- The family of constraint matrices `A₁, …, Aₘ ∈ 𝕊^n`. -/
  constraintMatrices : Fin m → 𝕊^n
  /-- The right-hand side vector `b ∈ ℝᵐ`. -/
  rhs : EuclideanSpace ℝ (Fin m)

namespace SemidefiniteOptimizationProblem

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/-- The affine slice cut out by the Frobenius equality constraints of an SDP. -/
abbrev affineSlice
    (problem : SemidefiniteOptimizationProblem n m) :
    AffineSubspace ℝ SymmMat :=
  realSymmetricMatrixAssociatedAffineSubspace
    problem.constraintMatrices
    problem.rhs

/-- The objective of a semidefinite optimization problem is the Frobenius pairing with the cost
matrix `C`. For symmetric matrices this is the same as `X ↦ trace (C * X)`. -/
def objective (problem : SemidefiniteOptimizationProblem n m) :
    SymmMat → ℝ :=
  fun X ↦ ⟪problem.costMatrix, X⟫_F

private def ambientProblem
    (problem : SemidefiniteOptimizationProblem n m) :
    SetConstrainedMinimizationProblem SymmMat where
  feasibleSet := (𝕊^n₊ : Set SymmMat)
  objective := problem.objective

/-- The canonical equality-constrained owner attached to an SDP. Its ambient feasible set is the
positive-semidefinite cone `𝕊ⁿ₊`, while the equality data are carried by the Frobenius
constraint map `realSymmetricMatrixConstraintMap problem.constraintMatrices` and the vector
`problem.rhs`. -/
def toPrimalEqualityConstrainedProblem
    (problem : SemidefiniteOptimizationProblem n m) :
    PrimalEqualityConstrainedProblem SymmMat Eₘ :=
  problem.ambientProblem.toPrimalEqualityConstrainedProblem
    (realSymmetricMatrixConstraintMap problem.constraintMatrices)
    problem.rhs

/-- The feasible set of a semidefinite optimization problem is the equality-feasible region of
its canonical equality-constrained owner. -/
def feasibleSet (problem : SemidefiniteOptimizationProblem n m) :
    Set SymmMat :=
  problem.toPrimalEqualityConstrainedProblem.equalityFeasibleSet

/-- The canonical Chapter 1 owner attached to an SDP is the `primalProblem` of its equality owner.
-/
def toSetConstrainedMinimizationProblem
    (problem : SemidefiniteOptimizationProblem n m) :
    SetConstrainedMinimizationProblem SymmMat :=
  problem.toPrimalEqualityConstrainedProblem.primalProblem

/-- The equality-owner bridge preserves the ambient positive-semidefinite cone. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_feasibleSet
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toPrimalEqualityConstrainedProblem.feasibleSet = (𝕊^n₊ : Set SymmMat) :=
  rfl

/-- The equality-owner bridge records the SDP Frobenius constraint map. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_A
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toPrimalEqualityConstrainedProblem.A =
      realSymmetricMatrixConstraintMap problem.constraintMatrices :=
  rfl

/-- The equality-owner bridge records the SDP right-hand side. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_b
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toPrimalEqualityConstrainedProblem.b = problem.rhs :=
  rfl

/-- The equality-owner bridge evaluates to the SDP trace objective. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_apply
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem.toPrimalEqualityConstrainedProblem X = problem.objective X :=
  rfl

/-- The SDP feasible set is definitionally the equality-feasible set of the canonical owner. -/
@[simp] theorem toPrimalEqualityConstrainedProblem_equalityFeasibleSet
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toPrimalEqualityConstrainedProblem.equalityFeasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge preserves the SDP feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge evaluates to the SDP trace objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem.toSetConstrainedMinimizationProblem X = problem.objective X :=
  rfl

/-- A semidefinite optimization problem can be used as its ambient objective function. -/
instance : CoeFun (SemidefiniteOptimizationProblem n m) (fun _ ↦ SymmMat → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Membership in the canonical affine slice is exactly the family of Frobenius equality
constraints. -/
@[simp] theorem mem_affineSlice_iff
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.affineSlice ↔
      ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i := by
  simpa [affineSlice] using
    (mem_realSymmetricMatrixAssociatedAffineSubspace_iff :
      X ∈ realSymmetricMatrixAssociatedAffineSubspace
            problem.constraintMatrices
            problem.rhs ↔
          ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i)

/-- The SDP affine slice is exactly the level set where the canonical equality-constraint map
takes the value `problem.rhs`. -/
@[simp] theorem constraintMap_eq_rhs_iff_mem_affineSlice
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    realSymmetricMatrixConstraintMap problem.constraintMatrices X = problem.rhs ↔
      X ∈ problem.affineSlice := by
  rw [problem.mem_affineSlice_iff]
  constructor
  · intro h i
    simpa using congrArg (fun v : Eₘ ↦ v i) h
  · intro h
    apply PiLp.ext
    intro i
    simpa using h i

/-- Membership in the feasible set is exactly positive semidefiniteness together with membership
in the canonical affine slice defined by the equality constraints. -/
@[simp] theorem mem_feasibleSet_iff_mem_affineSlice
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.feasibleSet ↔
      X ∈ 𝕊^n₊ ∧ X ∈ problem.affineSlice :=
  by
    rw [feasibleSet, PrimalEqualityConstrainedProblem.mem_equalityFeasibleSet_iff,
      problem.toPrimalEqualityConstrainedProblem_feasibleSet,
      problem.toPrimalEqualityConstrainedProblem_A,
      problem.toPrimalEqualityConstrainedProblem_b,
      problem.constraintMap_eq_rhs_iff_mem_affineSlice]

-- Proof sketch: rewrite `problem.feasibleSet` through
-- `problem.toPrimalEqualityConstrainedProblem.equalityFeasibleSet`, then expand the chapter
-- equality-owner membership lemma and the affine-slice characterization.
/-- Membership in the feasible set of a semidefinite optimization problem is exactly
positive-semidefiniteness together with the Frobenius constraints. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.feasibleSet ↔
      X ∈ 𝕊^n₊ ∧
        ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i :=
  by
    rw [mem_feasibleSet_iff_mem_affineSlice, problem.mem_affineSlice_iff]

/-- Expanding feasibility through the chapter cone owner `𝕊ⁿ₊` recovers the canonical matrix
predicate `Matrix.PosSemidef`. -/
theorem mem_feasibleSet_iff_posSemidef
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.feasibleSet ↔
      (X : Mat).PosSemidef ∧
        ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i := by
  rw [mem_feasibleSet_iff, mem_positiveSemidefiniteCone_iff]

-- Proof sketch: unfold `objective`; the value at `X` is definitionally `⟪C, X⟫_F`.
/-- Evaluating the objective of a semidefinite optimization problem returns the Frobenius pairing
with the cost matrix. -/
@[simp] theorem objective_apply
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem.objective X = ⟪problem.costMatrix, X⟫_F :=
  rfl

/-- Evaluating the objective also recovers the textbook trace formula `trace (C * X)`. -/
theorem objective_eq_trace
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem.objective X = trace ((problem.costMatrix : Mat) * (X : Mat)) := by
  have hC : (problem.costMatrix : Mat).IsSymm :=
    RealSymmetricMatrixSpace.isSymm problem.costMatrix
  rw [objective_apply, RealSymmetricMatrixSpace.frobeniusInner_def]
  simp [hC.eq]

/-- Evaluating an SDP as a function returns its trace objective value. -/
@[simp] theorem coe_apply
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    problem X = ⟪problem.costMatrix, X⟫_F :=
  rfl

end SemidefiniteOptimizationProblem

end

/-! ### Definition_5_4_4_5 (from Chap05) -/
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

/-! ### Definition_5_4_4_6 (from Chap05) -/
open Matrix
open scoped RealSymmetricMatrixSpace

noncomputable section

variable {m n : ℕ}

/- Definition 5.4.4.6 lies in the affine linear-constraint domain on the symmetric-matrix
Frobenius space.

Sampled owner-style declarations:
* `AffineSubspace` in mathlib, the canonical owner for affine subsets, including the empty case;
* `AffineSubspace.comap`, the canonical preimage owner under an affine map;
* `AffineSubspace.mk'` and `AffineSubspace.mem_mk'`, the canonical singleton affine-subspace owner
  and its membership bridge;
* `LinearMap.toAffineMap`, the canonical bridge from a linear constraint map to an affine map.

Best owner abstraction:
* source-facing: the associated affine subspace cut out by the Frobenius equations;
* core/canonical: `AffineSubspace ℝ (𝕊^n)`;
* bridge/view: the constraint linear map and the set-style membership theorem.

Primitive data:
* the constraint matrices `A : Fin m → 𝕊^n`;
* the right-hand side `b : EuclideanSpace ℝ (Fin m)`.

Derived API:
* the linear constraint map `realSymmetricMatrixConstraintMap A`;
* the affine subspace `realSymmetricMatrixAssociatedAffineSubspace A b`;
* the membership characterization
  `mem_realSymmetricMatrixAssociatedAffineSubspace_iff`.

Source/core/bridge triage:
* source-facing: `realSymmetricMatrixAssociatedAffineSubspace A b`;
* core/canonical: `AffineSubspace.comap` of the singleton `{b}` under the constraint map;
* bridge/view: the coordinate-free linear map and the pointwise membership lemma.

The refinement therefore keeps the source-facing affine-constraint locus, but upgrades its public
owner from a duplicate bare `Set` to the canonical mathlib affine-subspace owner. -/

/-- The linear map sending `X ∈ 𝕊^n` to the vector of Frobenius constraint values
`(⟪Aᵢ, X⟫_F)_i`. -/
def realSymmetricMatrixConstraintMap
    (A : Fin m → 𝕊^n) : 𝕊^n →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi fun i ↦ innerₛₗ ℝ (A i))

/-- The `i`-th coordinate of the constraint map is the Frobenius pairing with `Aᵢ`. -/
@[simp] theorem realSymmetricMatrixConstraintMap_apply
    (A : Fin m → 𝕊^n) (X : 𝕊^n) (i : Fin m) :
    realSymmetricMatrixConstraintMap A X i = ⟪A i, X⟫_F := by
  simp [realSymmetricMatrixConstraintMap, RealSymmetricMatrixSpace.frobeniusInner]

/-- Definition 5.4.4.6: for symmetric matrices `A₁, …, Aₘ ∈ 𝕊ⁿ` and `b ∈ ℝᵐ`, the associated
affine subspace is the affine subset of `𝕊ⁿ` cut out by the Frobenius inner-product equations
`⟨Aᵢ, X⟩_F = bᵢ` for all `i`. -/
def realSymmetricMatrixAssociatedAffineSubspace
    (A : Fin m → 𝕊^n) (b : EuclideanSpace ℝ (Fin m)) : AffineSubspace ℝ (𝕊^n) :=
  (AffineSubspace.mk' b (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin m)))).comap
    (realSymmetricMatrixConstraintMap A).toAffineMap

/-- Membership in the associated affine subspace means satisfying all Frobenius constraints
`⟨Aᵢ, X⟩_F = bᵢ`. -/
theorem mem_realSymmetricMatrixAssociatedAffineSubspace_iff
    {A : Fin m → 𝕊^n} {b : EuclideanSpace ℝ (Fin m)} {X : 𝕊^n} :
    X ∈ realSymmetricMatrixAssociatedAffineSubspace A b ↔
      ∀ i : Fin m, ⟪A i, X⟫_F = b i := by
  rw [realSymmetricMatrixAssociatedAffineSubspace, AffineSubspace.mem_comap, AffineSubspace.mem_mk',
    Submodule.mem_bot, vsub_eq_sub, sub_eq_zero]
  constructor
  · intro h i
    simpa using congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v i) h
  · intro h
    apply PiLp.ext
    intro i
    simpa using h i

end

/-! ### Definition_5_4_4_7 (from Chap05) -/
open Matrix
open RealSymmetricMatrixSpace
open scoped ConstrainedArgmin RealSymmetricMatrixSpace

noncomputable section

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/-
Definition 5.4.4.7 lies in the semidefinite Newton-direction domain.

Sampled owner-style declarations:
* `𝕊^n₊₊` and `strictPositiveSemidefiniteCone_posDef` in Definition 5.4.4.5, the chapter owner
  for the strict positive-definite cone and its canonical matrix-level bridge;
* `StrictPositiveSemidefiniteCone.inv` and `RealSymmetricMatrixSpace.sandwich`, the intrinsic
  Chapter 5 owners for the symmetric-matrix conjugation `X⁻¹ Δ X⁻¹`;
* `realSymmetricMatrixConstraintMap` and `realSymmetricMatrixAssociatedAffineSubspace` in
  Definition 5.4.4.6, the chapter owners for the tangent constraint kernel and the feasible affine
  slice `𝓛`;
* `constrainedArgmin` / notation `argmin[Q] f` in Chapter 1, the canonical minimizer-set owner on
  a feasible set;
* `mem_constrainedArgmin_iff`, the canonical bridge from `argmin` membership to set membership
  plus `IsMinOn`.

Best owner abstraction:
* source-facing: the Newton-direction set at a feasible strict-cone point `X : 𝕊^n₊₊`;
* core/canonical: tangent directions through `(realSymmetricMatrixConstraintMap A).ker` and
  minimizers through `argmin`;
* bridge/view: feasibility of the base point through
  `realSymmetricMatrixAssociatedAffineSubspace A b`.

Primitive data:
* the constraint matrices `A : Fin m → 𝕊^n`;
* the strict-cone base point `X : 𝕊^n₊₊`;
* the linear term `U : 𝕊^n`.

Derived API:
* the quadratic Newton objective `semidefiniteNewtonDirectionObjective X U`, built from the
  Chapter 5 owners `⟪·, ·⟫_F` and `sandwich (StrictPositiveSemidefiniteCone.inv X)`;
* the Newton-direction set `semidefiniteNewtonDirectionSet A X U`;
* the affine-slice bridge theorem that reintroduces `b` only when one wants the textbook
  feasibility statement.

Source/core/bridge triage:
* source-facing: the Newton directions of the barrier at a strict-cone feasible point;
* core/canonical: the constraint-map kernel and the minimizer owner `argmin`;
* bridge/view: the Frobenius-equation theorems for the base-point feasibility and tangent
  constraints.
-/

/-- The equality-constrained quadratic objective whose minimizers are the Newton directions for
the restriction of the semidefinite log-determinant barrier at the strict-cone point `X`. -/
def semidefiniteNewtonDirectionObjective (X : 𝕊^n₊₊) (U : SymmMat) : SymmMat → ℝ :=
  fun Δ ↦
    ⟪U, Δ⟫_F +
      (1 / 2 : ℝ) *
        ⟪sandwich (StrictPositiveSemidefiniteCone.inv X) Δ, Δ⟫_F

-- Proof sketch: unfold `semidefiniteNewtonDirectionObjective`, then rewrite the intrinsic
-- symmetric-matrix sandwich `sandwich (StrictPositiveSemidefiniteCone.inv X) Δ` and the
-- Frobenius pairing by their ambient matrix formulas.
/-- Evaluating `semidefiniteNewtonDirectionObjective X U` at `Δ` gives the quadratic Newton-model
expression `⟨U, Δ⟩_F + (1 / 2) ⟨X⁻¹ Δ X⁻¹, Δ⟩_F`. -/
theorem semidefiniteNewtonDirectionObjective_apply
    (X : 𝕊^n₊₊) (U Δ : SymmMat) :
    semidefiniteNewtonDirectionObjective X U Δ =
      ⟪U, Δ⟫_F +
        (1 / 2 : ℝ) *
          Matrix.trace
            ((((X : SymmMat) : Mat)⁻¹ * (Δ : Mat) * ((X : SymmMat) : Mat)⁻¹)ᵀ *
              (Δ : Mat)) := by
  calc
    semidefiniteNewtonDirectionObjective X U Δ =
        ⟪U, Δ⟫_F +
          (1 / 2 : ℝ) *
            ⟪sandwich (StrictPositiveSemidefiniteCone.inv X) Δ, Δ⟫_F :=
      rfl
    _ =
        ⟪U, Δ⟫_F +
          (1 / 2 : ℝ) *
            Matrix.trace
              ((((X : SymmMat) : Mat)⁻¹ * (Δ : Mat) * ((X : SymmMat) : Mat)⁻¹)ᵀ *
                (Δ : Mat)) := by
      congr 1
      rw [frobeniusInner_def]
      simp [StrictPositiveSemidefiniteCone.coe_inv]

/-- Definition 5.4.4.7: for a strict-cone base point `X`, the Newton directions are the
minimizers of the quadratic model `⟨U, Δ⟩_F + (1 / 2) ⟨X⁻¹ Δ X⁻¹, Δ⟩_F` on the tangent kernel
`⟨Aᵢ, Δ⟩_F = 0`. When `X` also lies in the affine slice
`realSymmetricMatrixAssociatedAffineSubspace A b`, this is exactly the textbook Newton-direction
set for the barrier restricted to `𝓛`. -/
def semidefiniteNewtonDirectionSet
    (A : Fin m → SymmMat) (X : 𝕊^n₊₊) (U : SymmMat) : Set SymmMat :=
  argmin[(realSymmetricMatrixConstraintMap A).ker]
    (semidefiniteNewtonDirectionObjective X U)

/-- Expanding Newton-direction membership through the `argmin` owner recovers the tangent
Frobenius equations and the minimizing property on the constraint kernel. -/
theorem mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat} :
    Δ ∈ semidefiniteNewtonDirectionSet A X U ↔
      (∀ i : Fin m, ⟪A i, Δ⟫_F = 0) ∧
        IsMinOn (semidefiniteNewtonDirectionObjective X U)
          (realSymmetricMatrixConstraintMap A).ker Δ := by
  rw [semidefiniteNewtonDirectionSet, mem_constrainedArgmin_iff]
  constructor
  · rintro ⟨hΔ, hmin⟩
    change realSymmetricMatrixConstraintMap A Δ = 0 at hΔ
    refine ⟨?_, hmin⟩
    intro i
    simpa [realSymmetricMatrixConstraintMap_apply] using
      congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v i) hΔ
  · rintro ⟨hΔ, hmin⟩
    refine ⟨?_, hmin⟩
    change realSymmetricMatrixConstraintMap A Δ = 0
    apply PiLp.ext
    intro i
    simpa [realSymmetricMatrixConstraintMap_apply] using hΔ i

/-- For a strict-cone point `X` already known to lie in the affine slice `𝓛`, expanding
`semidefiniteNewtonDirectionSet A X U` recovers the textbook Frobenius feasibility equations for
`X` together with the minimizing property on tangent directions. -/
theorem mem_semidefiniteNewtonDirectionSet_iff_feasible_frobenius_isMinOn
    {A : Fin m → SymmMat} {b : EuclideanSpace ℝ (Fin m)} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hX : (X : SymmMat) ∈ realSymmetricMatrixAssociatedAffineSubspace A b) :
    Δ ∈ semidefiniteNewtonDirectionSet A X U ↔
      (∀ i : Fin m, ⟪A i, (X : SymmMat)⟫_F = b i) ∧
        (∀ i : Fin m, ⟪A i, Δ⟫_F = 0) ∧
          IsMinOn (semidefiniteNewtonDirectionObjective X U)
            (realSymmetricMatrixConstraintMap A).ker Δ := by
  rw [mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn]
  constructor
  · intro hΔ
    exact ⟨mem_realSymmetricMatrixAssociatedAffineSubspace_iff.mp hX, hΔ.1, hΔ.2⟩
  · rintro ⟨_, hΔ, hmin⟩
    exact ⟨hΔ, hmin⟩

end

/-! ### Definition_5_4_4_8 (from Chap05) -/
noncomputable section

open Matrix
open scoped MatrixOrder RealSymmetricMatrixSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 5.4.4.8 lies in the semidefinite affine-epigraph / log-determinant barrier domain.

Sampled owner-style declarations:
* Chapter 5 `𝕊^n`, `𝕊^n₊`, and `𝕊^n₊₊`, the intrinsic symmetric-matrix and cone owners;
* Chapter 5 `logDetBarrier n`, the owner barrier on the strict cone subtype;
* `AffineMap.fst`, `LinearMap.snd`, and `Set.preimage`, the canonical affine and pullback owners.

Source/core/bridge triage:
* source-facing: the affine slack map into `𝕊^n`, the semidefinite epigraph, and the strict-domain
  semidefinite affine log-determinant barrier;
* core/canonical: `AffineMap`, `𝕊^n₊`, `𝕊^n₊₊`, and `logDetBarrier n`;
* bridge/view: the ambient matrix formula `t I - 𝓐(x)` and the ambient barrier formula
  `-log det (t I - 𝓐(x))`.

Primitive data:
* an affine map `𝓐 : E →ᵃ[ℝ] SymmMat`.

Derived API:
* the affine slack map `(x, t) ↦ t I - 𝓐(x)` valued in `𝕊^n`;
* the semidefinite epigraph and strict barrier domain as pullbacks of `𝕊^n₊` and `𝕊^n₊₊`;
* the strict-domain barrier on the barrier-point subtype;
* the ambient bridge formula on `E × ℝ`.

This refinement removes the raw matrix-valued duplicate owner and reuses the chapter's intrinsic
symmetric-matrix and cone owners directly. The textbook ambient matrix formula is retained only as
a bridge.
-/

/-- The affine slack map `(x, t) ↦ t I - 𝓐(x)` valued in the symmetric-matrix carrier `𝕊^n`. -/
abbrev semidefiniteAffineSlack
    (𝓐 : E →ᵃ[ℝ] SymmMat) : E × ℝ →ᵃ[ℝ] SymmMat :=
  ((LinearMap.snd ℝ E ℝ).smulRight (1 : SymmMat)).toAffineMap -
    𝓐.comp (AffineMap.fst : E × ℝ →ᵃ[ℝ] E)

/-- Evaluating `semidefiniteAffineSlack` at `(x, t)` gives the source-facing formula
`t I - 𝓐(x)` in `𝕊^n`. -/
@[simp] theorem semidefiniteAffineSlack_apply
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ) :
    semidefiniteAffineSlack 𝓐 (x, t) = t • (1 : SymmMat) - 𝓐 x :=
  rfl

/-- Coercing the affine slack matrix to ambient matrices recovers the textbook formula
`t I - 𝓐(x)`. -/
@[simp] theorem semidefiniteAffineSlack_apply_matrix
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ) :
    ((semidefiniteAffineSlack 𝓐 (x, t) : SymmMat) : Mat) =
      t • (1 : Mat) - (𝓐 x : Mat) :=
  rfl

/-- The semidefinite epigraph `K = {(x, t) | t I - 𝓐(x) ∈ 𝕊ⁿ₊}` attached to the affine
symmetric-matrix map `𝓐`. -/
def semidefiniteAffineEpigraph
    (𝓐 : E →ᵃ[ℝ] SymmMat) : Set (E × ℝ) :=
  semidefiniteAffineSlack 𝓐 ⁻¹' (𝕊^n₊ : Set SymmMat)

/-- Membership in the semidefinite epigraph means that the intrinsic slack matrix lies in
`𝕊ⁿ₊`. -/
@[simp] theorem mem_semidefiniteAffineEpigraph_iff
    (𝓐 : E →ᵃ[ℝ] SymmMat) (xt : E × ℝ) :
    xt ∈ semidefiniteAffineEpigraph 𝓐 ↔
      semidefiniteAffineSlack 𝓐 xt ∈ 𝕊^n₊ :=
  Iff.rfl

/-- In pair coordinates, membership in the semidefinite epigraph means that the textbook slack
matrix `t I - 𝓐(x)` is positive semidefinite. -/
theorem mem_semidefiniteAffineEpigraph_pair_iff
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ) :
    (x, t) ∈ semidefiniteAffineEpigraph 𝓐 ↔
      (t • (1 : Mat) - (𝓐 x : Mat)).PosSemidef := by
  rw [mem_semidefiniteAffineEpigraph_iff, mem_positiveSemidefiniteCone_iff,
    semidefiniteAffineSlack_apply_matrix]

/-- The strict domain on which the semidefinite affine log-determinant barrier is defined. -/
def semidefiniteAffineLogDetBarrierDomain
    (𝓐 : E →ᵃ[ℝ] SymmMat) : Set (E × ℝ) :=
  semidefiniteAffineSlack 𝓐 ⁻¹' (𝕊^n₊₊ : Set SymmMat)

/-- Membership in the strict barrier domain means that the intrinsic slack matrix lies in
`𝕊ⁿ₊₊`. -/
@[simp] theorem mem_semidefiniteAffineLogDetBarrierDomain_iff
    (𝓐 : E →ᵃ[ℝ] SymmMat) (xt : E × ℝ) :
    xt ∈ semidefiniteAffineLogDetBarrierDomain 𝓐 ↔
      semidefiniteAffineSlack 𝓐 xt ∈ 𝕊^n₊₊ :=
  Iff.rfl

/-- In pair coordinates, membership in the strict barrier domain means that the textbook slack
matrix `t I - 𝓐(x)` is positive definite. -/
theorem mem_semidefiniteAffineLogDetBarrierDomain_pair_iff
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ) :
    (x, t) ∈ semidefiniteAffineLogDetBarrierDomain 𝓐 ↔
      (t • (1 : Mat) - (𝓐 x : Mat)).PosDef := by
  rw [mem_semidefiniteAffineLogDetBarrierDomain_iff]
  constructor
  · intro h
    simpa [semidefiniteAffineSlack_apply_matrix] using
      strictPositiveSemidefiniteCone_posDef
        ⟨semidefiniteAffineSlack 𝓐 (x, t), h⟩
  · intro h
    exact mem_strictPositiveSemidefiniteCone_of_posDef <|
      by simpa [semidefiniteAffineSlack_apply_matrix] using h

/-- The subtype of points in the strict semidefinite affine barrier domain. -/
abbrev SemidefiniteAffineBarrierPoint
    (𝓐 : E →ᵃ[ℝ] SymmMat) :=
  {xt : E × ℝ // xt ∈ semidefiniteAffineLogDetBarrierDomain 𝓐}

/-- The ambient formula underlying the semidefinite affine log-determinant barrier. It is only a
bridge view; the owner barrier is `semidefiniteAffineLogDetBarrier 𝓐` on
`SemidefiniteAffineBarrierPoint 𝓐`. -/
def semidefiniteAffineLogDetBarrierAmbient
    (𝓐 : E →ᵃ[ℝ] SymmMat) : E × ℝ → ℝ :=
  fun xt ↦ logDetBarrierAmbient n (semidefiniteAffineSlack 𝓐 xt)

/-- Definition 5.4.4.8: the logarithmic-determinant barrier on the strict domain
`{(x, t) | t I - 𝓐(x) ∈ 𝕊ⁿ₊₊}`. -/
def semidefiniteAffineLogDetBarrier
    (𝓐 : E →ᵃ[ℝ] SymmMat) : SemidefiniteAffineBarrierPoint 𝓐 → ℝ :=
  fun xt ↦ logDetBarrier n ⟨semidefiniteAffineSlack 𝓐 xt.1, xt.2⟩

/-- Evaluating the semidefinite affine log-determinant barrier recovers its ambient bridge
formula. -/
@[simp] theorem semidefiniteAffineLogDetBarrier_apply
    (𝓐 : E →ᵃ[ℝ] SymmMat) (xt : SemidefiniteAffineBarrierPoint 𝓐) :
    semidefiniteAffineLogDetBarrier 𝓐 xt =
      semidefiniteAffineLogDetBarrierAmbient 𝓐 xt :=
  rfl

/-- At a strict-domain pair `(x, t)`, the semidefinite affine log-determinant barrier is the
textbook formula `-log det (t I - 𝓐(x))`. -/
theorem semidefiniteAffineLogDetBarrier_apply_pair
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ)
    (h : (x, t) ∈ semidefiniteAffineLogDetBarrierDomain 𝓐) :
    semidefiniteAffineLogDetBarrier 𝓐 ⟨(x, t), h⟩ =
      -Real.log (t • (1 : Mat) - (𝓐 x : Mat)).det := by
  rw [semidefiniteAffineLogDetBarrier]
  rw [logDetBarrier_apply]
  rw [semidefiniteAffineSlack_apply_matrix]

end

/-! ### Lemma_5_4_4_1 (from Chap05) -/
noncomputable section

open Matrix
open RealSymmetricMatrixSpace StrictPositiveSemidefiniteCone
open scoped Matrix.Norms.Frobenius MatrixOrder RealSymmetricMatrixSpace

/- Lemma 5.4.4.1 lies in the strict positive-definite symmetric-matrix / log-determinant-barrier
domain.

Sampled owner-style declarations:
* `logDetBarrier` and `logDetBarrierAmbient` from `Definition_5_4_4_5`, the source-facing barrier
  and its ambient formula bridge;
* `logDetBarrier_eq_neg_sum_log_eigenvalues` from `Theorem_5_4_4_2`, which already states Chapter 5
  barrier facts on the intrinsic domain `𝕊^n₊₊`;
* `RealSymmetricMatrixSpace.frobeniusInner` from `Definition_5_4_4_2`, the symmetric-space owner
  for the Frobenius pairing on `𝕊^n`, together with the intrinsic bridges `sandwich` and `cube`;
* `StrictPositiveSemidefiniteCone.inv` and `StrictPositiveSemidefiniteCone.sqrtInv` from
  `Definition_5_4_4_5`, the strict-cone bridges returning `X⁻¹` and `X^{-1/2}` to `𝕊^n`;
* `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` from
  `Theorem_5_4_4_3`, which differentiates the ambient extension on the symmetric ambient space.

Source/core/bridge triage:
* source-facing: the barrier `logDetBarrier n : 𝕊^n₊₊ → ℝ` together with the Chapter 5
  directional-derivative owners `lineDeriv`, `secondDirectionalDerivative`, and
  `thirdDirectionalDerivative` for its symmetric-space extension;
* core/canonical: differentiation of the symmetric-space extension `logDetBarrierAmbient n`;
* bridge/view: the ambient trace formula `Matrix.trace (Aᵀ * B)`.

Primitive data:
* `n : ℕ`.

Derived API:
* the Chapter 5 Frobenius owner `RealSymmetricMatrixSpace.frobeniusInner`;
* convexity and `C³` regularity from the upstream barrier owner
  `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone`;
* the directional-derivative formulas stated with the Chapter 5 owners
  `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative`.

This refinement removes the duplicate root-level Frobenius owner and keeps the public derivative
surface on the Chapter 5 directional owners rather than on raw `fderiv` / `iteratedFDeriv`.
The public statements are source-facing in the point `X : 𝕊^n₊₊` and direction `Δ : 𝕊^n`, using
the chapter owner `⟪·, ·⟫_F` on symmetric matrices and ambient trace formulas only as local bridge
syntax where the derivative formulas naturally live in the matrix algebra.
-/

section

variable (n : ℕ)

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n
local notation "logDetBarrierAmbientSymm" => logDetBarrierAmbient n

/-- Lemma 5.4.4.1 (1): at a strict-cone point, the first directional derivative of the
log-determinant barrier in a symmetric direction is the Frobenius pairing with `-X⁻¹`. -/
theorem logDetBarrier_lineDeriv_eq_frobeniusInner
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    lineDeriv ℝ logDetBarrierAmbientSymm X Δ =
      ⟪-inv X, Δ⟫_F := sorry

/-- Lemma 5.4.4.1 (2): the second directional derivative is the Frobenius self-pairing of
`√(X⁻¹) Δ √(X⁻¹)`. -/
theorem logDetBarrier_secondDirectional_eq_frobeniusNormSq
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      ⟪sandwich (sqrtInv X) Δ, sandwich (sqrtInv X) Δ⟫_F :=
  sorry

/-- Lemma 5.4.4.1 (3): the second directional derivative is the Frobenius pairing of `X⁻¹ Δ X⁻¹`
with `Δ`. -/
theorem logDetBarrier_secondDirectional_eq_frobeniusInner
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      ⟪sandwich (inv X) Δ, Δ⟫_F :=
  sorry

/-- Lemma 5.4.4.1 (4): the second directional derivative is the trace of
`(√(X⁻¹) Δ √(X⁻¹))²`. -/
theorem logDetBarrier_secondDirectional_eq_trace_sq
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    secondDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      Matrix.trace (((sandwich (sqrtInv X) Δ : Mat) ^ (2 : ℕ))) := sorry

/-- Lemma 5.4.4.1 (5): the third directional derivative is `-2` times the Frobenius pairing of the
identity with `(√(X⁻¹) Δ √(X⁻¹))³`. -/
theorem logDetBarrier_thirdDirectional_eq_frobeniusInner
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    thirdDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      -2 *
        ⟪(1 : SymmMat), cube (sandwich (sqrtInv X) Δ)⟫_F :=
      sorry

/-- Lemma 5.4.4.1 (6): the third directional derivative is `-2` times the trace of
`(√(X⁻¹) Δ √(X⁻¹))³`. -/
theorem logDetBarrier_thirdDirectional_eq_trace_cube
    (X : 𝕊^n₊₊) (Δ : SymmMat) :
    thirdDirectionalDerivative logDetBarrierAmbientSymm X Δ =
      -2 * Matrix.trace (cube (sandwich (sqrtInv X) Δ) : Mat) := sorry

end

end

/-! ### Lemma_5_4_4_2 (from Chap05) -/
noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

section

variable (n : ℕ)

/- Lemma 5.4.4.2 lies in the Chapter 5 self-concordant-barrier / positive-semidefinite-cone
domain.

Sampled owner-style declarations:
* `𝕊^n₊₊` from `Definition_5_4_4_5`, the source-facing owner for the strict cone
  `int(𝕊ⁿ₊)`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the Chapter 5 owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  from `Theorem_5_4_1_2`, the canonical owner theorem behind this lower bound;
* `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` from
  `Theorem_5_4_4_3`, the chapter barrier instance on the same strict cone.

Best owner abstraction:
* source-facing: the strict cone `𝕊^n₊₊`;
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* bridge/view: `𝕊^n₊₊ = interior (𝕊^n₊)`.

Primitive data:
* `n : ℕ`.

Derived API:
* the barrier-owner hypothesis on `𝕊^n₊₊`;
* the dimension lower bound `(n : ℝ) ≤ (ν : ℝ)`.

This file therefore uses the strict-cone owner already introduced upstream instead of keeping the
raw `interior (𝕊^n₊)` surface in the main statement, and it reuses the Chapter 5 symmetric-space
owner file for the ambient Hilbert-space and completeness structure instead of rebuilding a
parallel local instance tower.
-/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to the cone `𝕊^n₊` in the
-- intrinsic symmetric space `𝕊^n`, with base point the identity matrix,
-- recession directions the rank-one matrices `eᵢ eᵢᵀ`, and coefficients `αᵢ = βᵢ = 1`. Then
-- `I - ∑ i, eᵢ eᵢᵀ = 0` lies in the cone, each backward step `I - eᵢ eᵢᵀ` lies on the boundary
-- rather than in the interior, and the left-hand side becomes `∑ i, 1 = n`.
/-- Lemma 5.4.4.2: every `ν`-self-concordant barrier for the cone `𝕊ⁿ₊` of positive semidefinite
real `n × n` matrices has barrier parameter at least `n`. -/
theorem positiveSemidefiniteCone_barrierParameter_ge_dimension
    {ν : NNReal} {F : 𝕊^n → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (𝕊^n₊₊ : Set (𝕊^n)) ν F) :
    (n : ℝ) ≤ (ν : ℝ) := by
  letI : IsSelfConcordantBarrierOnWith (𝕊^n₊₊ : Set (𝕊^n)) ν F := hF
  sorry

end

end

/-! ### Proposition_5_4_4_1 (from Chap05) -/
open Matrix
open scoped RealSymmetricMatrixSpace

/- Proposition 5.4.4.1 belongs to the chapter's real symmetric-matrix Frobenius domain.

Sampled owner-style declarations:
* `𝕊^n` from Definition 5.4.4.1
* `RealSymmetricMatrixSpace.frobeniusInner`
* `RealSymmetricMatrixSpace.frobeniusInner_def`
* `RealSymmetricMatrixSpace.sandwich`
* `Matrix.trace_mul_cycle'`
* `RealSymmetricMatrixSpace.isSymm`

Best owner abstraction:
* source-facing: the real symmetric-matrix space `𝕊^n` with Frobenius pairing `⟪·, ·⟫_F`;
* core/canonical: the ambient trace formula for the restricted Frobenius pairing;
* bridge/view: the coercion `𝕊^n → Matrix (Fin n) (Fin n) ℝ`.

Primitive data:
* `X Y : 𝕊^n`.

Derived API:
* the intrinsic square `RealSymmetricMatrixSpace.sandwich Y 1 : 𝕊^n`, whose ambient matrix is
  `(Y : Mat)^2`;
* the ambient sandwich product `(Y : Mat) * (X : Mat) * (Y : Mat)`;
* the trace identities obtained from `RealSymmetricMatrixSpace.frobeniusInner_def`,
  cyclicity of trace, and simplification against `(1 : 𝕊^n)`.

This refinement removes the parallel local owner wrappers `square`, `sandwich`, and `identity`,
and returns the proposition to the chapter owners `𝕊^n` and `⟪·, ·⟫_F`, using the canonical
ambient matrix expressions only where multiplication actually lives. -/

section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

open RealSymmetricMatrixSpace

-- `sandwich Y 1` is the intrinsic symmetric-matrix representative of the ambient square `Y²`.
/-- Pairing `X` with the intrinsic square `sandwich Y 1` gives the trace of `YXY`. -/
theorem frobeniusInner_square_eq_trace_sandwich
    (X Y : SymmMat) :
    ⟪X, sandwich Y (1 : SymmMat)⟫_F =
      Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) := by
  calc
    ⟪X, sandwich Y (1 : SymmMat)⟫_F =
        Matrix.trace ((X : Mat)ᵀ * (sandwich Y (1 : SymmMat) : Mat)) := by
          rw [frobeniusInner_def]
    _ = Matrix.trace ((X : Mat) * (Y : Mat) ^ 2) := by
          simp [pow_two, (isSymm X).eq]
    _ = Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) := by
          simpa [pow_two, Matrix.mul_assoc] using
            Matrix.trace_mul_cycle' (X : Mat) (Y : Mat) (Y : Mat)

/-- Pairing the sandwich `YXY` with the identity matrix recovers its trace. -/
theorem frobeniusInner_one_sandwich_eq_trace
    (X Y : SymmMat) :
    ⟪(1 : SymmMat), sandwich Y X⟫_F =
      Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) := by
  rw [frobeniusInner_def]
  simp

/-- Proposition 5.4.4.1: for real symmetric matrices `X` and `Y`, the Frobenius pairing of `X`
with the intrinsic symmetric-carrier square `sandwich Y 1` of `Y²` equals `Trace (YXY)`, and
that trace is the Frobenius pairing of `YXY` with the identity matrix. -/
theorem frobenius_trace_identity_for_real_symmetric_matrices
    (X Y : SymmMat) :
    ⟪X, sandwich Y (1 : SymmMat)⟫_F =
        Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) ∧
      Matrix.trace ((Y : Mat) * (X : Mat) * (Y : Mat)) =
        ⟪(1 : SymmMat), sandwich Y X⟫_F := by
  exact
    ⟨frobeniusInner_square_eq_trace_sandwich X Y,
      (frobeniusInner_one_sandwich_eq_trace X Y).symm⟩

end

/-! ### Proposition_5_4_4_2 (from Chap05) -/
noncomputable section

open scoped BigOperators RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "SymmMat" => 𝕊^n

/-
Proposition 5.4.4.2 lies in the Chapter 5 semidefinite Newton-direction domain.

Sampled owner-style declarations:
* `semidefiniteNewtonDirectionSet` in `Definition_5_4_4_7`, the source-facing Newton-direction
  owner;
* `mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn` in `Definition_5_4_4_7`, the
  tangent-kernel/minimizer bridge for that owner;
* `IsSemidefiniteNewtonDirectionOutput` and `IsSemidefiniteNewtonMultiplier` in `Alg_5_4_4_1`,
  the chapter owners for a Newton-system multiplier solution and its reconstructed direction;
* `semidefiniteNewtonNormalMatrix`, `semidefiniteNewtonNormalRhs`, and
  `semidefiniteNewtonDirectionFromMultiplier` in `Alg_5_4_4_1`, the canonical normal-system data.

Best owner abstraction:
* source-facing: `semidefiniteNewtonDirectionSet A X U`;
* core/canonical: `IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ`;
* bridge/view: the coordinate normal equations obtained by expanding `Matrix.mulVec`.

Primitive data:
* `A : Fin m → 𝕊^n`;
* `X : 𝕊^n₊₊`;
* `U : 𝕊^n`;
* `Δ : 𝕊^n`.

Derived API:
* tangent feasibility `∀ i, ⟪A i, Δ⟫_F = 0`;
* the owner-level Newton-system multiplier/output relation;
* the coordinate normal equations and recovered direction.

This refinement removes the duplicate local KKT/stationarity/primal-step wrappers and reuses the
existing Chapter 5 Newton-system owner from `Alg_5_4_4_1`, keeping coordinate equations only as a
thin companion expansion.
-/

/-- A Newton direction is tangent to the Frobenius constraint kernel. -/
theorem semidefiniteNewtonDirectionSet_feasible
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hΔ : Δ ∈ semidefiniteNewtonDirectionSet A X U) :
    ∀ i : Fin m, ⟪A i, Δ⟫_F = 0 := by
  exact (mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn.mp hΔ).1

/-- Expanding `IsSemidefiniteNewtonDirectionOutput` through `Matrix.mulVec` gives the coordinate
normal equations together with the reconstructed Newton direction. -/
theorem isSemidefiniteNewtonDirectionOutput_iff_coordinate
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat} {multiplier : Fin m → ℝ} :
    IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ ↔
      (∀ i : Fin m,
        ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j =
          semidefiniteNewtonNormalRhs X U A i) ∧
      Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier := by
  rw [isSemidefiniteNewtonDirectionOutput_iff]
  constructor
  · rintro ⟨hmul, rfl⟩
    refine ⟨?_, rfl⟩
    intro i
    simpa [Matrix.mulVec] using congrArg (fun v : Fin m → ℝ ↦ v i) hmul
  · rintro ⟨hcoord, rfl⟩
    refine ⟨?_, rfl⟩
    ext i
    simpa [Matrix.mulVec] using hcoord i

-- Proof sketch: first-order optimality of the quadratic Newton model on the tangent kernel
-- yields exactly the Chapter 5 Newton normal system already packaged by
-- `IsSemidefiniteNewtonDirectionOutput`.
/-- Proposition 5.4.4.2: a Newton direction is an output of the Chapter 5 semidefinite Newton
system. -/
theorem semidefiniteNewtonDirectionSet_output
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hΔ : Δ ∈ semidefiniteNewtonDirectionSet A X U) :
    ∃ multiplier : Fin m → ℝ,
      IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ := by
  sorry

/-- Proposition 5.4.4.2 in coordinate form: a Newton direction admits multipliers solving the
normal equations, and `Δ` is the reconstructed direction attached to those multipliers. -/
theorem semidefiniteNewtonDirectionSet_normal_system
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hΔ : Δ ∈ semidefiniteNewtonDirectionSet A X U) :
    ∃ multiplier : Fin m → ℝ,
      (∀ i : Fin m,
        ∑ j, semidefiniteNewtonNormalMatrix X A i j * multiplier j =
          semidefiniteNewtonNormalRhs X U A i) ∧
      Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier := by
  rcases semidefiniteNewtonDirectionSet_output hΔ with ⟨multiplier, hOutput⟩
  exact ⟨multiplier, isSemidefiniteNewtonDirectionOutput_iff_coordinate.mp hOutput⟩

end

/-! ### Proposition_5_4_4_3 (from Chap05) -/
/- Proposition 5.4.4.3 is a bridge/view item in the chapter's semidefinite Newton-step
arithmetic-cost domain.

Sampled owner-style declarations in the same domain:
* `IsSemidefiniteNewtonDirectionOutput` in `Alg_5_4_4_1`, the Chapter 5 source-facing owner for
  one execution of the Newton-step subroutine;
* `semidefiniteNewtonNormalMatrix` in `Alg_5_4_4_1`, the owner for the dense multiplier system
  `S λ = d`;
* `semidefiniteNewtonDirectionFromMultiplier` in `Alg_5_4_4_1`, the owner for the recovered
  Newton direction `Δ = X (-U + ∑ λ_j A_j) X`;
* `GeneralIterativeScheme.totalArithmeticWork` in `Chap01/Definition_1_2_12`, the broader
  project owner for accumulated arithmetic work across iterations.

Best owner abstraction:
* source-facing: the Chapter 5 Newton-step owner `IsSemidefiniteNewtonDirectionOutput`;
* core/canonical: `ℕ`-valued arithmetic-cost expressions and polynomial inequalities on `(n, m)`;
* bridge/view: the dimension-only dense arithmetic-work model for one execution of that owner.

Primitive data:
* `n`, `m : ℕ`.

Derived API:
* the concrete dense-work expression `semidefiniteNewtonStepDenseArithmeticWorkBound n m`;
* its definitional expansion;
* the regime-specific bound by `n^2 * (m + n) * m`.

Source/core/bridge triage:
* source-facing: `IsSemidefiniteNewtonDirectionOutput`;
* core/canonical: arithmetic work as an `ℕ`-valued expression on primitive dimensions;
* bridge/view: this file's dense one-step arithmetic-cost estimate.

This refinement keeps the source-facing Newton-step owner upstream in `Alg_5_4_4_1` and leaves
this file responsible only for the dimension-level dense arithmetic model and its asymptotic
bound. -/

/- Proposition 5.4.4.3 is the arithmetic-cost companion to the Chapter 5 Newton-step owner. -/
set_option linter.hashCommand false in
#check IsSemidefiniteNewtonDirectionOutput

/-- A parameter-only dense arithmetic upper bound for one execution of the Newton-step subroutine
that computes the matrices `B_j = X * A_j * X`, assembles the dense linear system `S λ = d`,
solves that system, and forms `Δ = X * (-U + ∑ λ_j A_j) * X` using standard dense routines. -/
def semidefiniteNewtonStepDenseArithmeticWorkBound (n m : ℕ) : ℕ :=
  2 * m * n ^ 3 + m ^ 2 * n ^ 2 + m ^ 3 + (m + 1) * n ^ 2 + 2 * n ^ 3

-- Proof sketch: unfold `semidefiniteNewtonStepDenseArithmeticWorkBound`; the right-hand side is
-- exactly the sum of the dense-operation counts assigned to the four steps of the subroutine.
/-- Expanding `semidefiniteNewtonStepDenseArithmeticWorkBound` recovers the stepwise dense
operation count used for the Newton-step subroutine. -/
theorem semidefiniteNewtonStepDenseArithmeticWorkBound_eq (n m : ℕ) :
    semidefiniteNewtonStepDenseArithmeticWorkBound n m =
      2 * m * n ^ 3 + m ^ 2 * n ^ 2 + m ^ 3 + (m + 1) * n ^ 2 + 2 * n ^ 3 :=
  rfl

-- Proof sketch: bound the Step 1 and Step 4 matrix-multiplication terms by multiples of
-- `n^3 * m`, bound the assembly and solve terms by multiples of `n^2 * m^2`, use
-- `m ≤ n (n + 1) / 2` to absorb the `m^3` term into `n^2 * m^2`, and then factor the result as a
-- constant multiple of `n^2 * (m + n) * m`.
/-- Proposition 5.4.4.3: if `1 ≤ m ≤ n(n + 1) / 2`, then one dense execution of the Newton-step
subroutine has arithmetic work bounded by a constant multiple of `n^2 * (m + n) * m`, and hence
has arithmetic complexity `O(n^2 * (m + n) * m)`. -/
theorem semidefiniteNewtonStepDenseArithmeticComplexity_bound
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n * (n + 1) / 2) :
    semidefiniteNewtonStepDenseArithmeticWorkBound n m ≤
      8 * n ^ 2 * (m + n) * m := by
  rw [semidefiniteNewtonStepDenseArithmeticWorkBound_eq]
  have hn : 1 ≤ n := by
    by_cases h0 : n = 0
    · subst h0
      simp at hmn
      omega
    · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
  have hmn_sq : m ≤ n ^ 2 := by
    calc
      m ≤ n * (n + 1) / 2 := hmn
      _ ≤ n * (2 * n) / 2 := by
        have hn_two : n + 1 ≤ 2 * n := by
          nlinarith [hn]
        gcongr
      _ = n ^ 2 := by
        simpa [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          (Nat.mul_div_right (n * n) (show 0 < 2 by decide))
  have hm_two : m + 1 ≤ 2 * m := by
    nlinarith [hm]
  have hmQ : (1 : ℚ) ≤ m := by
    exact_mod_cast hm
  have hnQ : (1 : ℚ) ≤ n := by
    exact_mod_cast hn
  have hmn_sqQ : (m : ℚ) ≤ n ^ 2 := by
    exact_mod_cast hmn_sq
  have hm_twoQ : (m : ℚ) + 1 ≤ 2 * m := by
    exact_mod_cast hm_two
  have hm_sq_geQ : (m : ℚ) ≤ m ^ 2 := by
    nlinarith [hmQ]
  have hn_sq_nonnegQ : 0 ≤ (n : ℚ) ^ 2 := by
    positivity
  have hn_cube_nonnegQ : 0 ≤ (n : ℚ) ^ 3 := by
    positivity
  have hm_cubeQ : (m : ℚ) ^ 3 ≤ m ^ 2 * n ^ 2 := by
    nlinarith [hmn_sqQ]
  have hmn_sq_mulQ : (2 : ℚ) * m * n ^ 2 ≤ 2 * m ^ 2 * n ^ 2 := by
    nlinarith [hm_sq_geQ, hn_sq_nonnegQ]
  have hn_cubeQ : (2 : ℚ) * n ^ 3 ≤ 2 * m * n ^ 3 := by
    nlinarith [hmQ, hn_cube_nonnegQ]
  exact_mod_cast (show
    (2 : ℚ) * m * n ^ 3 + m ^ 2 * n ^ 2 + m ^ 3 + (m + 1) * n ^ 2 + 2 * n ^ 3 ≤
      8 * n ^ 2 * (m + n) * m by
    nlinarith [hm_cubeQ, hmn_sq_mulQ, hn_cubeQ, hm_twoQ])
