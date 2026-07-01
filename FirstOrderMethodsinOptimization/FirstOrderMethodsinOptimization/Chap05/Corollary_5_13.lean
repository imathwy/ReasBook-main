import FirstOrderMethodsinOptimization.Chap05.Definition_5_1
import FirstOrderMethodsinOptimization.Chap05.Theorem_5_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Corollary 5.13 is a `bridge/view` specialization of the Chapter 5 real-valued smoothness owner
predicate `is_l_smooth_on`, specialized to `Set.univ`, with Theorem 5.12 as its
`core/canonical` Hessian characterization. The source-facing content here is the Euclidean
coordinate realization in terms of the Hessian matrix of `bilinearIteratedFDerivTwo ℝ f x` and its
largest eigenvalue. -/

/-- The Hessian of a twice differentiable function on `ℝ^n`, written as a matrix in the standard
Euclidean basis. -/
def hessian_matrix (f : E → ℝ) (x : E) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix₂ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis) (bilinearIteratedFDerivTwo ℝ f x)

-- Proof sketch: `ContDiff ℝ 2 f` implies that the second derivative of `f` at every point is
-- symmetric via `ContDiffAt.isSymmSndFDerivAt`. Translating the resulting symmetric bilinear form
-- to the standard basis identifies `hessian_matrix f x` as a Hermitian real matrix.
/-- The Hessian matrix of a `C²` real-valued function on `ℝ^n` is Hermitian. -/
theorem hessian_matrix_isHermitian (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    (hessian_matrix f x).IsHermitian := sorry

-- Proof sketch: for `n > 0`, the Hermitian spectrum of `hessian_matrix f x` is canonically sorted
-- in decreasing order, so index `0` selects the largest eigenvalue.
/-- The largest eigenvalue of the Hessian matrix, using the canonical descending ordering of the
Hermitian spectrum. -/
noncomputable def hessian_max_eigenvalue
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (hn : 0 < n) (x : E) : ℝ :=
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  (hessian_matrix_isHermitian f hf x).eigenvalues 0

-- Proof sketch: combine the owner theorem `is_l_smooth_iff_hessian_operator_norm_le`
-- with the fact that convexity makes each Hessian matrix positive semidefinite. For a Hermitian
-- positive semidefinite matrix, the operator norm equals its largest eigenvalue, so the Hessian
-- operator-norm bound is equivalent to the displayed maximal-eigenvalue bound.
/-- Corollary 5.13: a twice continuously differentiable convex function on `ℝ^n` is globally
`L`-smooth with respect to the Euclidean norm if and only if, at every point, the largest
eigenvalue of its Hessian matrix is at most `L`. -/
theorem convex_is_l_smooth_iff_hessian_max_eigenvalue_le
    {f : E → ℝ} {L : NNReal} (hn : 0 < n) (hconvex : ConvexOn ℝ Set.univ f)
    (hf : ContDiff ℝ 2 f) :
    is_l_smooth_on f Set.univ L ↔
      ∀ x : E, hessian_max_eigenvalue f hf hn x ≤ (L : ℝ) := sorry

end
