import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Metric

-- Semantic recall note: no `lean_leansearch` tool was available in this runner, so this item is
-- stated directly using the canonical `DifferentiableOn`, `Metric.ball`, `Metric.closedBall`, and
-- `deriv` interfaces from mathlib.

/-- Lemma V.1-extra-4: if `g` is holomorphic on the open disc of radius `r₀ + ε` centered at `0`
and satisfies `‖g z‖ ≤ M` on the closed disc of radius `r₀`, then `‖deriv g z‖` is bounded by
`M * r₀ / (r₀ - r)^2` at every point of the closed disc of radius `r`, for `r < r₀`. -/
theorem norm_deriv_le_of_holomorphic_on_ball_of_bound
    {g : ℂ → ℂ} {M r r₀ ε : ℝ} (hε : 0 < ε) (hrr₀ : r < r₀)
    (hhol : DifferentiableOn ℂ g (ball (0 : ℂ) (r₀ + ε)))
    (hbound : ∀ z ∈ closedBall (0 : ℂ) r₀, ‖g z‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖deriv g z‖ ≤ M * r₀ / (r₀ - r) ^ 2 := by
  have hrz : ‖z‖ ≤ r := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hr : 0 ≤ r := (norm_nonneg z).trans hrz
  have hR : 0 < r₀ - r := sub_pos.mpr hrr₀
  have hsub : closedBall z (r₀ - r) ⊆ ball (0 : ℂ) (r₀ + ε) := by
    intro w hw
    have hwz : ‖w - z‖ ≤ r₀ - r := by
      simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hw
    have hw0 : ‖w‖ < r₀ + ε := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ (r₀ - r) + r := add_le_add hwz hrz
        _ = r₀ := sub_add_cancel _ _
        _ < r₀ + ε := by simpa using add_lt_add_left hε r₀
    simpa [mem_ball, dist_eq_norm] using hw0
  have hdg : DiffContOnCl ℂ g (ball z (r₀ - r)) :=
    hhol.diffContOnCl_ball hsub
  have hC : ∀ w ∈ sphere z (r₀ - r), ‖g w‖ ≤ M := by
    intro w hw
    apply hbound w
    have hwz : ‖w - z‖ = r₀ - r := by
      simpa [dist_eq_norm, norm_sub_rev] using (mem_sphere_iff_norm.mp hw)
    have hw0 : ‖w‖ ≤ r₀ := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ (r₀ - r) + r := add_le_add (le_of_eq hwz) hrz
        _ = r₀ := sub_add_cancel _ _
    simpa [mem_closedBall, dist_eq_norm] using hw0
  have hderiv : ‖deriv g z‖ ≤ M / (r₀ - r) :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdg hC
  have hM : 0 ≤ M := by
    have hz₀ : z ∈ closedBall (0 : ℂ) r₀ := by
      simpa [mem_closedBall, dist_eq_norm] using hrz.trans hrr₀.le
    exact (norm_nonneg _).trans (hbound z hz₀)
  have hmul : ‖deriv g z‖ * (r₀ - r) ^ 2 ≤ M * r₀ := by
    have hderiv' : ‖deriv g z‖ * (r₀ - r) ≤ M := (le_div_iff₀ hR).mp hderiv
    have hstep : ‖deriv g z‖ * (r₀ - r) ^ 2 ≤ M * (r₀ - r) := by
      have := mul_le_mul_of_nonneg_right hderiv' hR.le
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
    have hr_le : r₀ - r ≤ r₀ := sub_le_self _ hr
    exact hstep.trans <| mul_le_mul_of_nonneg_left hr_le hM
  exact (le_div_iff₀ (sq_pos_of_pos hR)).2 <| by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
