import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

/- Proposition 6.31 lies in the Euclidean linear-algebra / unconstrained argmin domain.

Sampled owner-style declarations:
* `constrainedArgmin` with notation `argmin[Q]` in `Chap01/Definition_1_3_3`, the project owner
  for global minimizers on a set;
* `IsMinOn`, the canonical minimizer predicate underlying `argmin[Q]`;
* `Matrix.toEuclideanLin`, the canonical linear-map owner attached to a real matrix acting on
  Euclidean spaces;
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the mathlib bridge identifying transpose with
  the adjoint on Euclidean spaces.

Best owner abstraction:
* source-facing: the affine-quadratic minimand
  `x ↦ ⟪A x, uHat⟫ + (1 / 2) ‖x‖²` on `ℝⁿ`;
* core/canonical: `Matrix.toEuclideanLin A` together with the project argmin owner
  `argmin[Set.univ]`;
* bridge/view: the Euclidean transpose formula `-Aᵀ uHat` for a chosen minimizer.

Primitive data:
* the matrix `A : ℝ^{m × n}`;
* the dual vector `uHat : ℝ^m`.

Derived API:
* the minimand `euclideanLinearQuadraticMinimand A uHat`;
* the pointwise formula for that minimand;
* the canonical argmin identity `x0 = -Aᵀ uHat` for any chosen minimizer;
* the resulting uniqueness of global minimizers.

No parallel wrapper around matrices, transpose maps, or argmin witnesses is introduced here; the
file stays on the canonical matrix and argmin owners already present in mathlib and the project.
-/

variable {m n : ℕ}

local notation "E₁" => EuclideanSpace ℝ (Fin n)
local notation "E₂" => EuclideanSpace ℝ (Fin m)

/-- The affine-quadratic minimand `x ↦ ⟪A x, uHat⟫ + (1 / 2) ‖x‖²` from Proposition 6.31. -/
def euclideanLinearQuadraticMinimand
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) : E₁ → ℝ :=
  fun x ↦ inner ℝ (A.toEuclideanLin x) uHat + (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)

-- Proof sketch: unfold `euclideanLinearQuadraticMinimand`.
/-- Evaluating `euclideanLinearQuadraticMinimand` recovers the defining expression
`⟪A x, uHat⟫ + (1 / 2) ‖x‖²`. -/
@[simp] theorem euclideanLinearQuadraticMinimand_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) (x : E₁) :
    euclideanLinearQuadraticMinimand A uHat x =
      inner ℝ (A.toEuclideanLin x) uHat + (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := sorry

-- Proof sketch: rewrite the affine term using the Euclidean adjoint of
-- `A.toEuclideanLin`, identify that adjoint with `(Aᵀ).toEuclideanLin`, and apply the
-- first-order condition for a global minimizer of the strongly convex function
-- `x ↦ ⟪A x, uHat⟫ + (1 / 2) ‖x‖²`.
/-- Proposition 6.31 [Chapter6_1.json:100]: if `x0(uHat)` is chosen in
`argmin_x {⟪A x, uHat⟫ + (1 / 2) ‖x‖²}`, then `x0(uHat) = -Aᵀ uHat`. -/
theorem euclideanLinearQuadraticMinimizer_eq_neg_transpose_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) {x0 : E₁}
    (hx0 : x0 ∈ argmin[Set.univ] (euclideanLinearQuadraticMinimand A uHat)) :
    x0 = -(A.transpose.toEuclideanLin uHat) := sorry

-- Proof sketch: apply
-- `euclideanLinearQuadraticMinimizer_eq_neg_transpose_apply` to both minimizers and compare
-- their common value `-Aᵀ uHat`.
/-- Any two global minimizers of `euclideanLinearQuadraticMinimand A uHat` are equal. -/
theorem euclideanLinearQuadraticMinimizer_unique
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) {x y : E₁}
    (hx : x ∈ argmin[Set.univ] (euclideanLinearQuadraticMinimand A uHat))
    (hy : y ∈ argmin[Set.univ] (euclideanLinearQuadraticMinimand A uHat)) :
    x = y := sorry
