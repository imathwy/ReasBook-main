import Mathlib.Tactic.Recall
import Nesterov.Chap01.Proposition_1_6_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter HasGeometricRateOfConvergence
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Euclid" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 1.6.13 lies in the finite-dimensional linear-iteration / geometric-convergence
domain.

Relevant owner-style declarations sampled before refining:
* `linear_iteration_contraction_estimate` in `Nesterov/Chap01/Proposition_1_6_13.lean`, the
  chapter owner theorem for norm decay of linear iterations on normed spaces;
* `Matrix.toEuclideanCLM`, the canonical bridge from a matrix to the continuous linear map used by
  that owner theorem;
* `Matrix.l2_opNorm_toEuclideanCLM`, identifying the matrix `L²` operator norm with the norm of
  that bridge;
* `HasGeometricRateOfConvergence.tendsto_zero`, the canonical convergence-to-zero consequence of
  the owner bound.

Best owner abstraction:
* the chapter owner theorem `linear_iteration_contraction_estimate`

Primitive data:
* the matrix sequence `A`
* the trajectory `a`
* the recurrence `a (k + 1) = (A k).toEuclideanLin (a k)`
* the uniform norm bound `‖A k‖ ≤ 1 - q`

Derived API:
* the geometric norm estimate
* the convergence-to-zero consequence for `0 < q < 1`

Source/core/bridge triage:
* source-facing: the matrix recurrence in `ℝⁿ`
* core/canonical: `linear_iteration_contraction_estimate`
* bridge/view: `Matrix.toEuclideanCLM` and `Matrix.l2_opNorm_toEuclideanCLM`

This item therefore reuses the chapter owner theorem directly and keeps only the concrete
matrix-specialized bridge statements, rather than maintaining a parallel local proof of the same
geometric-decay owner result. -/

/- The chapter owner theorem is the canonical normed-space statement behind the matrix
specialization used here. -/
recall linear_iteration_contraction_estimate
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (q : ℝ) (A : ℕ → E →L[𝕜] E) (a : ℕ → E)
    (ha : ∀ k : ℕ, a (k + 1) = A k (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q) :
    HasGeometricRateOfConvergence (fun k : ℕ ↦ ‖a k‖) q ‖a 0‖

/-- The matrix recurrence in Proposition 1.6.13 is the Euclidean-space specialization of the
chapter owner theorem `linear_iteration_contraction_estimate`. -/
theorem norm_linear_iteration_hasGeometricRate
    {q : ℝ}
    (A : ℕ → Mat)
    (a : ℕ → Euclid)
    (ha : ∀ k : ℕ, a (k + 1) = (A k).toEuclideanLin (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q) :
    HasGeometricRateOfConvergence (fun k : ℕ ↦ ‖a k‖) q ‖a 0‖ := by
  let e : Mat ≃⋆ₐ[ℝ] (Euclid →L[ℝ] Euclid) := Matrix.toEuclideanCLM
  let T : ℕ → Euclid →L[ℝ] Euclid := fun k ↦ e (A k)
  have hrec : ∀ k : ℕ, a (k + 1) = T k (a k) := fun k ↦ by
    simpa [T] using ha k
  have hT : ∀ k : ℕ, ‖T k‖ ≤ 1 - q := fun k ↦ by
    simpa [T, Matrix.l2_opNorm_toEuclideanCLM] using hA k
  exact linear_iteration_contraction_estimate q T a hrec hT

/-- Proposition 1.6.13: if a sequence in `ℝⁿ` satisfies the linear recurrence
`a_{k+1} = A_k a_k` and every matrix `A_k` has Euclidean operator norm at most `1 - q`, then the
iterates satisfy the geometric contraction estimate
`‖a_k‖ ≤ (1 - q)^k ‖a_0‖`. -/
theorem norm_linear_iteration_le_geometric_decay
    {q : ℝ}
    (A : ℕ → Mat)
    (a : ℕ → Euclid)
    (ha : ∀ k : ℕ, a (k + 1) = (A k).toEuclideanLin (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q)
    (k : ℕ) :
    ‖a k‖ ≤ (1 - q) ^ k * ‖a 0‖ := by
  simpa [mul_comm] using (norm_linear_iteration_hasGeometricRate A a ha hA) k

/-- The norm sequence of a uniformly contractive linear iteration converges to `0`. -/
theorem norm_linear_iteration_tendsto_zero
    {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (A : ℕ → Mat)
    (a : ℕ → Euclid)
    (ha : ∀ k : ℕ, a (k + 1) = (A k).toEuclideanLin (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q) :
    Tendsto (fun k : ℕ ↦ ‖a k‖) atTop (nhds 0) := by
  have hgeom := norm_linear_iteration_hasGeometricRate A a ha hA
  exact hgeom.tendsto_zero (fun _ ↦ norm_nonneg _) (norm_nonneg _) hq.1 hq.2

end
