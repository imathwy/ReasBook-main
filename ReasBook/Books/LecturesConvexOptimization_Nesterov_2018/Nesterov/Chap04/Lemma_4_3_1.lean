import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_16
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_3_2
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient CoordinateSubspace CoordinateSymmetricMatrixSubspace

variable {n t i : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 4.3.1 lies in the Chapter 4 hard-instance / coordinate-support second-order domain.

Sampled owner-style declarations in this domain:
* `coordinateSubspace` and `mem_coordinateSubspace_iff` in `Chap02/Text_2_13`, the chapter owner
  and coordinatewise view for prefix-supported vectors `ℝ^{i,n}`;
* `coordinateSymmetricMatrixSubspace` and `mem_coordinateSymmetricMatrixSubspace_iff` in
  `Definition_4_3_3`, the chapter owner and entrywise view for the symmetric matrix block support
  condition `𝕊^{i,n}`;
* `hessianMatrix` / `∇²` in `Chap01/Definition_1_4_16`, the canonical matrix owner for second
  derivatives on Euclidean space.

Best owner abstraction:
* source-facing: the textbook claim that the gradient/Hessian data of `f_t` at a point in
  `ℝ^{i,n}` only reveal the first `i + 1` coordinates;
* core/canonical: the two atomic memberships `∇ (fk htn) x ∈ ℝ^{i + 1,n}` and
  `∇² (fk htn) x ∈ 𝕊^{i + 1,n}`;
* bridge/view: the packaged product membership
  `(∇ (fk htn) x, ∇² (fk htn) x) ∈ (ℝ^{i + 1,n}).prod 𝕊^{i + 1,n}`.

Primitive data:
* gradient support in the next coordinate subspace;
* Hessian matrix support in the next symmetric coordinate subspace.

Derived API:
* the product-membership theorem bundling those two owner facts.
-/

-- Proof sketch: expand the gradient plus the Hessian matrix `∇² (fk htn) x`
-- coordinatewise. If `x ∈ ℝ^{i,n}`, then `mem_coordinateSubspace_iff` says that
-- the coordinates of `x` vanish from index `i` onward. For `i < t`, the adjacent-difference terms
-- plus tail terms in Definition 4.3.2 involve only coordinates up to `i + 1`. This places the
-- gradient in `ℝ^{i+1,n}`; the same coordinate inspection places the Hessian matrix in
-- `𝕊^{i+1,n}`.
/-- If `x ∈ ℝ^{i,n}` with `i < t`, then the gradient of the hard-instance objective `f_t`
belongs to the next coordinate subspace `ℝ^{i+1,n}`. -/
theorem fk_gradient_mem_next_coordinateSubspace
    (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) :
    ∇ (fk htn) x ∈ ℝ^{i + 1,n} := sorry

/-- If `x ∈ ℝ^{i,n}` with `i < t`, then the Hessian matrix of the hard-instance objective `f_t`
belongs to the next symmetric coordinate subspace `𝕊^{i+1,n}`. -/
theorem fk_hessian_mem_next_coordinateSymmetricMatrixSubspace
    (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) :
    ∇² (fk htn) x ∈ 𝕊^{i + 1,n} := sorry

/-- Lemma 4.3.1: if `x ∈ ℝ^{i,n}` with `i < t`, then for the hard-instance function `f_t`
formalized by `fk`, the pair formed by the gradient and Hessian matrix at `x` belongs to
`ℝ^{i+1,n} × 𝕊^{i+1,n}`. -/
theorem fk_first_second_order_mem_next_coordinate_subspaces
    (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) :
    (∇ (fk htn) x, ∇² (fk htn) x) ∈
      (ℝ^{i + 1,n}).prod 𝕊^{i + 1,n} := by
  exact ⟨fk_gradient_mem_next_coordinateSubspace htn hx hit,
    fk_hessian_mem_next_coordinateSymmetricMatrixSubspace htn hx hit⟩
