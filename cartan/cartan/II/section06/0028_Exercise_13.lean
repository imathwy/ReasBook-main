import Mathlib

open Filter Metric Complex
open scoped Topology

-- Declarations for this item will be appended below by the statement pipeline.

private theorem diffContOnCl_intermediate_ball
    {f : ℂ → ℂ} {ρ r : ℝ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ)) :
    DiffContOnCl ℂ f (ball (0 : ℂ) ((ρ + r) / 2)) := by
  refine DiffContOnCl.mk_ball ?_ ?_
  · refine hf.mono <| ball_subset_ball ?_
    linarith
  · exact hf.continuousOn.mono <| closedBall_subset_ball <| by linarith

/-- Exercise 13: for a holomorphic function on the open disc `|z| < ρ`, the difference quotients
converge uniformly to `deriv f` on the closed disc `|z| ≤ r` as `h → 0` through the punctured
neighborhood filter `𝓝[≠] (0 : ℂ)`. -/
-- Proof sketch: use the circle-integral identity for the error term on the intermediate circle
-- of radius `(ρ + r) / 2`, then combine the resulting uniform `O(‖h‖)` estimate on the closed
-- ball `closedBall 0 r` with `Metric.tendstoUniformlyOn_iff`; the small-ball restriction on `h`
-- is automatic because `r < ρ`.
theorem difference_quotients_tendsto_uniformly_on_deriv_closed_ball
    {f : ℂ → ℂ} {ρ r : ℝ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ)) :
    TendstoUniformlyOn
      (fun h z ↦ (f (z + h) - f z) / h)
      (deriv f)
      (𝓝[≠] (0 : ℂ))
      (closedBall (0 : ℂ) r) := by
  let hfmid := diffContOnCl_intermediate_ball hrρ hf
  sorry

/-- On the smaller closed disc, the error in the difference quotient admits a Cauchy-integral
representation over the intermediate circle of radius `(ρ + r) / 2`. -/
-- Proof sketch: apply the Cauchy integral formula for `deriv f z` on the circle of radius
-- `(ρ + r) / 2` via `DiffContOnCl.deriv_eq_smul_circleIntegral`, apply
-- `DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul` to `f (· + h) - f`, and simplify
-- the resulting difference into a single integral kernel.
theorem difference_quotient_sub_deriv_eq_circle_integral
    {f : ℂ → ℂ} {ρ r : ℝ} {z h : ℂ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ))
    (hz : z ∈ closedBall (0 : ℂ) r) (hh₀ : h ≠ 0)
    (hh : ‖h‖ < (ρ - r) / 4) :
    (f (z + h) - f z) / h - deriv f z =
      h * ((2 * π * I : ℂ)⁻¹ *
        ∮ t in C(0, (ρ + r) / 2), f t / ((t - z - h) * (t - z) ^ 2)) := by
  let hfmid := diffContOnCl_intermediate_ball hrρ hf
  have hmid₀ : 0 < (ρ + r) / 2 := by
    have hr_nonneg : 0 ≤ r := by
      have hz_norm : ‖z‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      exact le_trans (norm_nonneg z) hz_norm
    linarith
  sorry

/-- Any uniform boundary bound on the intermediate circle gives the linear error estimate for the
difference quotient on the smaller closed disc. -/
-- Proof sketch: take norms in the circle-integral formula for the error term, bound `‖f t‖`
-- on the circle by `M`, estimate the kernel using `‖z‖ ≤ r` and `‖h‖ < (ρ - r) / 4`, and
-- bound the circle integral by the length of the circle times the supremum norm of the integrand,
-- after reducing the Cauchy-integral step to the canonical intermediate-disc owner
-- `diffContOnCl_intermediate_ball hrρ hf`.
theorem norm_difference_quotient_sub_deriv_le_of_boundary_bound
    {f : ℂ → ℂ} {ρ r M : ℝ} {z h : ℂ}
    (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) ρ))
    (hz : z ∈ closedBall (0 : ℂ) r) (hh₀ : h ≠ 0)
    (hh : ‖h‖ < (ρ - r) / 4)
    (hM : ∀ t ∈ sphere (0 : ℂ) ((ρ + r) / 2), ‖f t‖ ≤ M) :
    ‖(f (z + h) - f z) / h - deriv f z‖ ≤
      4 * M * (ρ + r) / (ρ - r) ^ 3 * ‖h‖ := by
  let hfmid := diffContOnCl_intermediate_ball hrρ hf
  sorry
