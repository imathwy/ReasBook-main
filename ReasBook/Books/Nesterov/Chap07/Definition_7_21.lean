import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators

variable {p n : ℕ}

local notation "Eₚ" => EuclideanSpace ℝ (Fin p)
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.21 lies in Chapter 7's linear-matrix Gram-operator domain.

Sampled owner-style declarations:
- `LinearMap.adjoint`, the canonical adjoint owner for finite-dimensional inner-product spaces;
- `LinearMap.adjoint_inner_right`, the owner-level evaluation rule for `L†`;
- `Matrix.gram` and `Matrix.gram_apply`, the canonical Gram-matrix owner and its entry formula;
- `LinearMap.toMatrixOrthonormal`, the standard-basis matrix presentation of an endomorphism;
- `Matrix.toEuclideanLin`, the bridge from square matrices to Euclidean endomorphisms.

Best owner abstraction:
- source-facing: the operator on `ℝᵖ` attached to the coefficient map `L(x) = ∑ᵢ xᵢ Aᵢ`;
- core/canonical: the intrinsic Gram operator `L†L`;
- bridge/view: the Frobenius Gram matrix `Matrix.gram ℝ coeffMatrices` and its realization as the
  standard-basis matrix of `L†L`.

Primitive data:
- a family `coeffMatrices : Fin p → Mₙ` of real square matrices.

Derived API:
- the coefficient-sum linear map `linearMatrixCombination`;
- the Gram operator `linearMatrixGramOperator = L†L`;
- the canonical Gram matrix `Matrix.gram ℝ coeffMatrices`;
- the bridge identifying the standard-basis matrix of `linearMatrixGramOperator` with
  `Matrix.gram ℝ coeffMatrices`.

Source/core/bridge triage:
- source-facing: Definition 7.21's operator `G`;
- core/canonical: `(linearMatrixCombination coeffMatrices).adjoint ∘ₗ
  linearMatrixCombination coeffMatrices`;
- bridge/view: the Frobenius-entry formula for `Matrix.gram ℝ coeffMatrices`, the standard-basis
  matrix formula for `G`, and the equality `G = Matrix.toEuclideanLin (Matrix.gram ℝ coeffMatrices)`.

This refinement keeps the source-facing coefficient map and centers the public owner on the
intrinsic operator `L†L`. The matrix presentation `Matrix.gram ℝ coeffMatrices` is retained only
as the canonical bridge/view theorem. -/

private instance ambientMatrixNormedAddCommGroup : NormedAddCommGroup Mₙ :=
  toMatrixNormedAddCommGroup (1 : Mₙ) PosDef.one

private instance ambientMatrixInnerProductSpace : InnerProductSpace ℝ Mₙ :=
  toMatrixInnerProductSpace (1 : Mₙ) PosDef.one.posSemidef

/-- The linear map `x ↦ ∑ᵢ xᵢ Aᵢ` associated with a family of real square matrices. -/
def linearMatrixCombination (coeffMatrices : Fin p → Mₙ) : Eₚ →ₗ[ℝ] Mₙ where
  toFun x := ∑ i : Fin p, x i • coeffMatrices i
  map_add' x y := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp [Finset.smul_sum, smul_smul]

/-- Evaluating `linearMatrixCombination` gives the coefficient-weighted matrix sum
`∑ᵢ xᵢ Aᵢ`. -/
theorem linearMatrixCombination_apply
    (coeffMatrices : Fin p → Mₙ) (x : Eₚ) :
    linearMatrixCombination coeffMatrices x = ∑ i : Fin p, x i • coeffMatrices i := rfl

/-- Definition 7.21 (2): the operator `G : ℝᵖ → ℝᵖ` attached to the matrix family
`A₁, …, Aₚ` is the intrinsic Gram operator `L†L` for
`L(x) = ∑ᵢ xᵢ Aᵢ`, where `L†` is taken with respect to the Frobenius pairing on matrix entries.
Its standard-basis matrix is identified below with the Frobenius Gram matrix
`Matrix.gram ℝ coeffMatrices`. -/
def linearMatrixGramOperator (coeffMatrices : Fin p → Mₙ) : Eₚ →ₗ[ℝ] Eₚ :=
  (linearMatrixCombination coeffMatrices).adjoint ∘ₗ linearMatrixCombination coeffMatrices

section

variable (p n)

/- The bridge/view matrix owner used by Definition 7.21 is `Matrix.gram` on the intrinsic matrix
family. -/
set_option linter.hashCommand false in
#check (Matrix.gram ℝ : (Fin p → Mₙ) → Matrix (Fin p) (Fin p) ℝ)

end

/-- Expanding `Matrix.gram ℝ coeffMatrices` gives the textbook entrywise Frobenius formula. -/
theorem matrix_gram_apply_eq_entrywise_sum
    (coeffMatrices : Fin p → Mₙ) (i j : Fin p) :
    Matrix.gram ℝ coeffMatrices i j =
      ∑ a : Fin n, ∑ b : Fin n, coeffMatrices i a b * coeffMatrices j a b := by
  rw [Matrix.gram_apply]
  change Matrix.trace (coeffMatrices j * 1 * (coeffMatrices i)ᵀ) =
    ∑ a : Fin n, ∑ b : Fin n, coeffMatrices i a b * coeffMatrices j a b
  simp [Matrix.trace, Matrix.mul_apply, mul_comm]

/-- The quadratic form of `linearMatrixGramOperator` is the Frobenius norm square of the
associated matrix combination. -/
theorem linearMatrixGramOperator_quadratic_form
    (coeffMatrices : Fin p → Mₙ) (x : Eₚ) :
    inner ℝ (linearMatrixGramOperator coeffMatrices x) x =
      ∑ i : Fin n, ∑ j : Fin n,
        ((linearMatrixCombination coeffMatrices x) i j) *
          ((linearMatrixCombination coeffMatrices x) i j) := by
  sorry

/-- The matrix of `linearMatrixGramOperator` in the standard orthonormal basis of `ℝᵖ` is the
canonical Gram matrix of the coefficient family. -/
theorem linearMatrixGramOperator_toMatrixOrthonormal
    (coeffMatrices : Fin p → Mₙ) :
    LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p) ℝ)
        (linearMatrixGramOperator coeffMatrices) =
      Matrix.gram ℝ coeffMatrices := by
  ext i j
  rw [LinearMap.toMatrixOrthonormal_apply_apply, linearMatrixGramOperator, LinearMap.comp_apply,
    Matrix.gram_apply]
  simpa [linearMatrixCombination] using
    (LinearMap.adjoint_inner_right (linearMatrixCombination coeffMatrices)
      ((EuclideanSpace.basisFun (Fin p) ℝ) i)
      ((linearMatrixCombination coeffMatrices) ((EuclideanSpace.basisFun (Fin p) ℝ) j)))

/-- The intrinsic Gram operator `linearMatrixGramOperator coeffMatrices = L†L` is represented by
`Matrix.toEuclideanLin (Matrix.gram ℝ coeffMatrices)` in the standard orthonormal basis of
`ℝᵖ`. -/
theorem linearMatrixGramOperator_eq_toEuclideanLin_gram
    (coeffMatrices : Fin p → Mₙ) :
    linearMatrixGramOperator coeffMatrices = Matrix.toEuclideanLin (Matrix.gram ℝ coeffMatrices) := by
  apply (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p) ℝ)).injective
  change LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p) ℝ)
      (linearMatrixGramOperator coeffMatrices) =
    LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p) ℝ)
      (Matrix.toEuclideanLin (Matrix.gram ℝ coeffMatrices))
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
    linearMatrixGramOperator_toMatrixOrthonormal coeffMatrices

end
