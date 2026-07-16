import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Definition 1.4.16 lies in second-order differential calculus on finite-dimensional Euclidean
space.

Relevant owner-style declarations sampled before refining:
* `hessian` in `Nesterov/Chap01/Definition_1_4_16.lean`, the chapter owner for the intrinsic
  Hessian operator `fderiv ℝ (∇ f) x`
* `hessianMatrix` in `Nesterov/Chap01/Definition_1_4_16.lean`, the source-facing matrix view in
  the standard Euclidean basis
* `LinearMap.toMatrixOrthonormal`, the canonical matrix presentation of a Euclidean endomorphism
* `Matrix.toEuclideanLin_eq_toLin_orthonormal`, the inverse bridge back to the intrinsic operator

Best owner abstraction:
* core/canonical owner: `hessian`

Primitive data:
* a real-valued function `f`
* a base point `x`

Derived API:
* the Euclidean matrix view `hessianMatrix f x`
* the notation surface `∇² f x`
* the entrywise coordinate formula `hessianMatrix_apply`
* the second-partial bridge `hessianMatrix_apply_eq_fderiv_gradient_coordinate`
* the reconstruction bridge `hessianMatrix_toEuclideanLin`

Source/core/bridge triage:
* source-facing: the textbook Hessian matrix on `ℝⁿ`
* core/canonical: the intrinsic Hessian operator `hessian f x`
* bridge/view: `hessianMatrix`, `hessianMatrix_apply`,
  `hessianMatrix_apply_eq_fderiv_gradient_coordinate`, and
  `hessianMatrix_toEuclideanLin`

The exact owner and bridge declarations already exist in the chapter file, so this item is
refined to a recall surface instead of reintroducing parallel local Hessian definitions.
-/

/- The intrinsic Hessian operator is the chapter owner for the derivative of the gradient map. -/
recall hessian {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f : X → ℝ) (x : X) : X →L[ℝ] X

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 1.4.16: on `ℝⁿ`, the textbook Hessian matrix is the standard-basis matrix of the
intrinsic Hessian operator. -/
recall hessianMatrix (f : E → ℝ) (x : E) : Matrix (Fin n) (Fin n) ℝ

variable (f : E → ℝ) (x : E)

/- The `Gradient`-scope notation `∇² f x` is the source-facing surface for `hessianMatrix f x`. -/
#check ∇² f x

/- The entries of `∇² f x` are obtained by pairing the intrinsic Hessian operator with the
standard basis vectors. -/
recall hessianMatrix_apply

/- Under first- and second-order differentiability, each matrix entry is the directional
derivative of the corresponding gradient coordinate, i.e. the textbook second partial
derivative. -/
recall hessianMatrix_apply_eq_fderiv_gradient_coordinate

/- Converting the Hessian matrix back to a Euclidean linear map recovers the intrinsic Hessian
operator. -/
recall hessianMatrix_toEuclideanLin

end
