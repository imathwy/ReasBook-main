import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Lemma_10_33

-- Declarations for this item will be appended below by the statement pipeline.

/-
Remark 10.35 is `source-facing`: it records that the explicit affine comparison sequence
`t_k = (k + 2) / 2` supplies the scalar comparison facts used in the FISTA `O(1 / k^2)`
estimate.

Domain sampling in the surrounding Chapter 10 API identifies:
- `fista_momentum_update` from Algorithm 10.13 as the `core/canonical` owner of the actual FISTA
  momentum recursion;
- `fista_momentum_sequence_lower_bound` from Lemma 10.33 as the reusable sequence-level lower
  bound owner for genuine FISTA-recursive sequences;
- `fista_t_succ` from Algorithm 10.6 and `is_mfista_trajectory_t_succ` from Algorithm 10.11 as
  downstream sequence-level specializations of that owner.

The present remark is not a second momentum owner. Its first clause is exactly the canonical
sequence-level comparison theorem already provided by Lemma 10.33, while its second clause is the
remaining source-facing scalar inequality for the explicit affine comparison values. -/

/- Remark 10.35 (1): any sequence satisfying the FISTA momentum recursion dominates the affine
comparison profile `k ↦ (k + 2) / 2`. -/
recall fista_momentum_sequence_lower_bound

-- Proof sketch: expand the two displayed affine values and reduce the comparison to elementary
-- real arithmetic.
/-- Remark 10.35 (2): the affine comparison values `t_k = (k + 2) / 2` satisfy the scalar
inequality `t_(k+1)^2 - t_(k+1) ≤ t_k^2` for every `k ≥ 0`. -/
theorem affine_fista_comparison_quadratic_recursion_bound (k : ℕ) :
    (((k : ℝ) + 3) / 2) ^ 2 - ((k : ℝ) + 3) / 2 ≤ (((k : ℝ) + 2) / 2) ^ 2 := by
  nlinarith
