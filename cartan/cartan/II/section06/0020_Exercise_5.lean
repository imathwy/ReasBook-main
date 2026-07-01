import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Metric

/-- Exercise 5: if `f` is continuous on the closed disc `|z| ≤ r` and holomorphic on the open disc
`|z| < r`, then for every `z` with `|z| < r`, the positively oriented circle integral over
`|t| = r` recovers `f z` by the Cauchy integral formula. -/
-- Proof sketch: specialize `DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul` to the
-- disc centered at `0`, rewrite the scalar action as complex multiplication, and commute the
-- resulting equality.
theorem cauchy_integral_formula_closed_disc_zero_center {f : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 r))
    (hz : z ∈ ball 0 r) :
    f z = ((Complex.I * (↑Real.pi * 2)) : ℂ)⁻¹ * ∮ t in C(0, r), f t / (t - z) := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz).symm
