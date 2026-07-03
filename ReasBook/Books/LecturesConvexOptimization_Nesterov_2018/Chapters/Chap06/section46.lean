

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_46 (from Chap06) -/
noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

/-
Definition 6.46 lies in the symmetric-matrix / constrained minimization domain.

Sampled owner-style declarations:
- `𝕊^n` and `RealSymmetricMatrixSpace.isSymm` in `Chap05/Definition_5_4_4_2`, the chapter
  owner for real symmetric matrices together with the canonical bridge back to ambient symmetry;
- `RealSymmetricMatrixSpace.eigenvalues` in `Chap05/Definition_5_4_4_1`, the intrinsic spectral
  owner on `𝕊^n`;
- `Matrix.greatestEigenvalue` and the notation `λ_max(H)` in `Chap04/Definition_4_1_6`, the
  project owner for largest real spectral values of square matrices;
- mathlib `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, the canonical bridge from the
  real spectrum of a Hermitian matrix to its ordered eigenvalue list;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in `Chap01/Definition_1_3_7`, the
  canonical constrained optimal-value and `ε`-approximate-minimizer owners.

Best owner abstraction:
- source-facing: `NonsmoothEigenvalueMinimizationProblem m n`, storing the textbook data
  `(Q, C, A₁, …, Aₘ)`;
- core/canonical: `𝕊^n`, `RealSymmetricMatrixSpace.eigenvalues`,
  `λ_max((X : Matrix (Fin n) (Fin n) ℝ))`, and
  `SetConstrainedMinimizationProblem Eₘ` together with its derived `optimalValue` /
  `IsApproximateMinimizer` API for the optimization layer;
- bridge/view: `toSetConstrainedMinimizationProblem`, together with the linear matrix map and the
  objective-evaluation lemmas below.

Primitive data:
- the feasible set `Q ⊆ ℝ^m` with its closedness and convexity hypotheses;
- the constant matrix `C : 𝕊^n`;
- the coefficient matrices `Aᵢ : 𝕊^n`.

Derived API:
- the linear matrix map `linearOperator : Eₘ →ₗ[ℝ] SymmMat`;
- the affine symmetric-matrix evaluation `matrixValue : Eₘ → SymmMat`;
- the real-valued objective `objective : Eₘ → ℝ`, defined through
  `λ_max((problem.matrixValue y : Matrix (Fin n) (Fin n) ℝ))`;
- the canonical optimization-owner bridge `toSetConstrainedMinimizationProblem`;
- the inherited owner specializations
  `problem.toSetConstrainedMinimizationProblem.optimalValue` and
  `problem.toSetConstrainedMinimizationProblem.IsApproximateMinimizer ε yBar`.

This refinement removes the proposition-local maximal-eigenvalue dependency, makes the linear
matrix map land in `𝕊^n` directly, and reuses the existing spectral and constrained-problem owners
instead of keeping parallel local optimal-value or `ε`-solution definitions.
-/

/-- Definition 6.46: a nonsmooth eigenvalue minimization problem is specified by a closed convex
feasible set `Q ⊆ ℝ^m`, a symmetric matrix `C`, and symmetric coefficient matrices
`A₁, …, Aₘ` defining the linear matrix map `A(y) = ∑ᵢ yᵢ Aᵢ`. The ambient optimization owner is
derived canonically through `toSetConstrainedMinimizationProblem`. -/
structure NonsmoothEigenvalueMinimizationProblem (m n : ℕ) where
  /-- The feasible set `Q ⊆ ℝ^m` on which the problem is posed. -/
  feasibleSet : Set (EuclideanSpace ℝ (Fin m))
  /-- The feasible set is closed. -/
  feasibleSet_isClosed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The symmetric matrix `C` in the eigenvalue objective. -/
  constantMatrix : 𝕊^n
  /-- The symmetric coefficient matrices `A₁, …, Aₘ`. -/
  coefficientMatrix : Fin m → 𝕊^n

namespace NonsmoothEigenvalueMinimizationProblem

open RealSymmetricMatrixSpace

/-- The coefficient-weighted matrix operator is additive in the parameter `y`. -/
theorem linearOperator_map_add
    (problem : NonsmoothEigenvalueMinimizationProblem m n)
    (y z : EuclideanSpace ℝ (Fin m)) :
    (∑ i : Fin m, (y + z) i • problem.coefficientMatrix i) =
      (∑ i : Fin m, y i • problem.coefficientMatrix i) +
        ∑ i : Fin m, z i • problem.coefficientMatrix i := sorry

/-- The coefficient-weighted matrix operator is homogeneous in the parameter `y`. -/
theorem linearOperator_map_smul
    (problem : NonsmoothEigenvalueMinimizationProblem m n)
    (a : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    (∑ i : Fin m, (a • y) i • problem.coefficientMatrix i) =
      a • ∑ i : Fin m, y i • problem.coefficientMatrix i := sorry

/-- The linear matrix operator `A(y) = ∑ᵢ yᵢ Aᵢ` attached to the coefficient matrices of the
problem, landing directly in the symmetric-matrix owner `𝕊^n`. -/
def linearOperator (problem : NonsmoothEigenvalueMinimizationProblem m n) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] 𝕊^n where
  toFun y := ∑ i : Fin m, y i • problem.coefficientMatrix i
  map_add' y z := linearOperator_map_add problem y z
  map_smul' a y := linearOperator_map_smul problem a y

/-- Evaluating `linearOperator` gives the coefficient-weighted sum `∑ᵢ yᵢ Aᵢ` in `𝕊^n`. -/
@[simp] theorem linearOperator_apply
    (problem : NonsmoothEigenvalueMinimizationProblem m n)
    (y : EuclideanSpace ℝ (Fin m)) :
    problem.linearOperator y = ∑ i : Fin m, y i • problem.coefficientMatrix i :=
  rfl

/-- The symmetric matrix `C + A(y)` whose maximal eigenvalue defines the objective. -/
def matrixValue (problem : NonsmoothEigenvalueMinimizationProblem m n)
    (y : EuclideanSpace ℝ (Fin m)) : 𝕊^n :=
  problem.constantMatrix + problem.linearOperator y

/-- Evaluating `matrixValue` gives the symmetric-matrix sum `C + A(y)`. -/
@[simp] theorem matrixValue_eq_add
    (problem : NonsmoothEigenvalueMinimizationProblem m n)
    (y : EuclideanSpace ℝ (Fin m)) :
    problem.matrixValue y = problem.constantMatrix + problem.linearOperator y :=
  rfl

/-- The objective `φ(y)` of the nonsmooth eigenvalue minimization problem is the maximal
eigenvalue of `C + A(y)`, expressed intrinsically as the supremum of its real spectrum. -/
def objective (problem : NonsmoothEigenvalueMinimizationProblem m n) :
    EuclideanSpace ℝ (Fin m) → ℝ :=
  fun y ↦ λ_max((problem.matrixValue y : Matrix (Fin n) (Fin n) ℝ))

/-- The objective is the intrinsic real-spectrum supremum composed with the symmetric-matrix
evaluation `y ↦ C + A(y)`. -/
@[simp] theorem objective_eq_comp_matrixValue
    (problem : NonsmoothEigenvalueMinimizationProblem m n) :
    problem.objective =
      fun y ↦ λ_max((problem.matrixValue y : Matrix (Fin n) (Fin n) ℝ)) :=
  rfl

/-- The canonical Chapter 1 optimization owner attached to the nonsmooth eigenvalue minimization
problem. -/
def toSetConstrainedMinimizationProblem
    (problem : NonsmoothEigenvalueMinimizationProblem m n) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin m)) where
  feasibleSet := problem.feasibleSet
  objective := problem.objective

/-- The owner bridge preserves the feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : NonsmoothEigenvalueMinimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge evaluates to the nonsmooth eigenvalue objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : NonsmoothEigenvalueMinimizationProblem m n)
    (y : EuclideanSpace ℝ (Fin m)) :
    problem.toSetConstrainedMinimizationProblem y = problem.objective y :=
  rfl

/-- A nonsmooth eigenvalue minimization problem can be used as its objective function `φ`. -/
instance :
    CoeFun
      (NonsmoothEigenvalueMinimizationProblem m n)
      (fun _ ↦ EuclideanSpace ℝ (Fin m) → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- The objective of the problem is the supremum of the real spectrum of `C + A(y)`. -/
@[simp] theorem objective_apply
    (problem : NonsmoothEigenvalueMinimizationProblem m n)
    (y : EuclideanSpace ℝ (Fin m)) :
    problem.objective y =
      λ_max((problem.matrixValue y : Matrix (Fin n) (Fin n) ℝ)) :=
  rfl

/-- Evaluating a nonsmooth eigenvalue minimization problem as a function returns its objective
value. -/
@[simp] theorem coe_apply
    (problem : NonsmoothEigenvalueMinimizationProblem m n)
    (y : EuclideanSpace ℝ (Fin m)) :
    problem y = problem.objective y :=
  rfl

/-- The canonical constrained optimal value for Definition 6.46 is the inherited Chapter 1 owner
`problem.toSetConstrainedMinimizationProblem.optimalValue`. -/
@[simp] theorem optimalValue_eq
    (problem : NonsmoothEigenvalueMinimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.optimalValue =
      sInf ((fun y ↦ (problem y : EReal)) '' problem.feasibleSet) := by
  simpa using problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

/-- The canonical constrained `ε`-approximate minimizer predicate for Definition 6.46 is the
inherited owner `problem.toSetConstrainedMinimizationProblem.IsApproximateMinimizer ε yBar`. -/
theorem isApproximateMinimizer_iff_problem
    (problem : NonsmoothEigenvalueMinimizationProblem m n)
    (ε : ℝ) (yBar : EuclideanSpace ℝ (Fin m)) :
    problem.toSetConstrainedMinimizationProblem.IsApproximateMinimizer ε yBar ↔
      yBar ∈ problem.feasibleSet ∧
        (problem yBar : EReal) ≤ problem.toSetConstrainedMinimizationProblem.optimalValue + ε := by
  simpa using problem.toSetConstrainedMinimizationProblem.isApproximateMinimizer_iff ε yBar

end NonsmoothEigenvalueMinimizationProblem

end

/-! ### Proposition_6_46 (from Chap06) -/
open scoped Gradient

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-
Proposition 6.46 lies in the chapter's attained affine-minorant / tangent-identity domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the Chapter 6 owner for affine-dual
  supremum objectives;
- `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the canonical feasible-maximizer
  owner for that supremum;
- `smoothedPrimalObjectiveArgmax.value_eq` in `Chap06/Theorem_6_1`, the owner-level attained-value
  theorem;
- `ContinuousLinearMap.flip` together with `InnerProductSpace.toDual`, the canonical transpose /
  Riesz interface for the vector form of `A^* u`.

Best owner abstraction:
- source-facing: Proposition 6.46's affine tangent identity at an attained maximizer;
- core/canonical: `smoothedPrimalObjective A Qd 0 g 0 0` and
  `smoothedPrimalObjectiveArgmax A Qd g 0 0`;
- bridge/view: the zero-smoothing specialization and the vector representative
  `(InnerProductSpace.toDual ℝ E₁).symm (A.flip uBar)` of the transpose field.

Primitive data:
- a continuous linear pairing map `A : E₁ →L[ℝ] StrongDual ℝ E₂`;
- a dual feasible set `Qd : Set E₂`;
- a dual term `g : E₂ → ℝ`;
- a point `xBar : E₁` and an attained maximizer `uBar` in the canonical argmax owner.

Derived API:
- the zero-smoothed value function `smoothedPrimalObjective A Qd 0 g 0 0`;
- the attained value identity at `xBar`, via `smoothedPrimalObjectiveArgmax.value_eq`;
- the affine tangent identity once the gradient is identified with the Riesz representative of
  `A.flip uBar`.

Source/core/bridge triage:
- source-facing: the proposition below;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`, and `A.flip`;
- bridge/view: the specialization `hatf = 0`, `d₂ = 0`, `μ₂ = 0` and the Riesz identification of
  `A^* uBar`.

The previous file introduced a local owner `affineMinorantValueFunction` that was definitionally
the zero-smoothed Chapter 6 owner `smoothedPrimalObjective A Qd 0 g 0 0`, kept a redundant primal
set parameter only through subtype binders, and specialized the ambient spaces to coordinate
Euclidean models. This refinement states the proposition directly on the canonical owner surface,
removes the unused primal-set packaging, and weakens the ambient assumptions to the intrinsic
inner-product / dual-pairing layer actually used by the statement.
-/

-- Proof sketch: use `smoothedPrimalObjectiveArgmax.value_eq` to identify the value at `xBar` with
-- `A xBar uBar - g uBar`, rewrite the gradient term by `hgrad` and the pairing identity
-- `⟪(InnerProductSpace.toDual ℝ E₁).symm (A.flip uBar), x - xBar⟫ = A (x - xBar) uBar`, and then
-- expand the linear term with `A.map_sub`.
/-- Proposition 6.46: if `uBar` attains the supremum defining the zero-smoothed Chapter 6 primal
objective at `xBar` and the gradient at `xBar` is the vector representative of `A^* uBar`, then
for every `x` the affine tangent identity
`f(xBar) + ⟪∇f(xBar), x - xBar⟫ = A x uBar - g uBar` holds for
`f = smoothedPrimalObjective A Qd 0 g 0 0`. -/
theorem affine_minorant_identity
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Qd : Set E₂} {g : E₂ → ℝ}
    {xBar x : E₁} {uBar : E₂}
    (huBar : uBar ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 xBar)
    (hgrad :
      ∇ (smoothedPrimalObjective A Qd 0 g 0 0) xBar =
        (InnerProductSpace.toDual ℝ E₁).symm (A.flip uBar)) :
    smoothedPrimalObjective A Qd 0 g 0 0 xBar +
        inner ℝ (∇ (smoothedPrimalObjective A Qd 0 g 0 0) xBar) (x - xBar) =
      A x uBar - g uBar := by
  have hvalue := smoothedPrimalObjectiveArgmax.value_eq huBar
  have hvalue' :
      smoothedPrimalObjective A Qd 0 g 0 0 xBar = A xBar uBar - g uBar := by
    simpa [smoothedPrimalObjectiveMaximand] using hvalue
  have hpair :
      inner ℝ ((InnerProductSpace.toDual ℝ E₁).symm (A.flip uBar)) (x - xBar) =
        A (x - xBar) uBar := by
    rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.flip_apply]
  rw [hgrad, hpair]
  calc
    smoothedPrimalObjective A Qd 0 g 0 0 xBar + A (x - xBar) uBar
        = (A xBar uBar - g uBar) + A (x - xBar) uBar := by rw [hvalue']
    _ = (A xBar uBar - g uBar) + (A x uBar - A xBar uBar) := by
          simp
    _ = A x uBar - g uBar := by ring

end
