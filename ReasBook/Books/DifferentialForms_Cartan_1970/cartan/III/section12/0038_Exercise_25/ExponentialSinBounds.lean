import DifferentialForms_Cartan_1970.cartan.III.section12.«0038_Exercise_25».SquareBoundaryPiCotBounds

noncomputable section

open scoped Topology unitInterval

/-- Helper for Cartan section12 0038_Exercise_25: the oscillatory exponential factor on the square
contours has norm `exp (-α Im z)`, so only the imaginary coordinate matters in the bounds. -/
lemma exercise25_exp_phase_norm (alpha : ℝ) (z : ℂ) :
    ‖Complex.exp (Complex.I * (alpha : ℂ) * z)‖ = Real.exp (-alpha * z.im) := by
  rcases z with ⟨x, y⟩
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, mul_comm, mul_left_comm]

/-- Helper for Cartan section12 0038_Exercise_25: once `u ≥ π / 2`, the quotient
`exp u / sinh u` is bounded by the same uniform horizontal-side constant used for the cotangent
kernel. -/
lemma exercise25_exp_div_sinh_le_uniform {u : ℝ} (hu : Real.pi / 2 ≤ u) :
    Real.exp u / Real.sinh u ≤ 2 / (1 - Real.exp (-Real.pi)) := by
  have hhalf_pi_pos : 0 < Real.pi / 2 := by positivity
  have hu_pos : 0 < u := lt_of_lt_of_le hhalf_pi_pos hu
  have hsinh_pos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu_pos
  have hexp_lt_one : Real.exp (-Real.pi) < 1 := by
    simpa using (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos))
  have hcoef_pos : 0 < 1 - Real.exp (-Real.pi) := sub_pos.mpr hexp_lt_one
  have hpi_le_two_u : Real.pi ≤ 2 * u := by
    nlinarith [hu]
  have hExpTail :
      Real.exp (-u) ≤ Real.exp (-Real.pi) * Real.exp u := by
    have hle : -u ≤ u - Real.pi := by
      refine (neg_le_sub_iff_le_add).2 ?_
      simpa [two_mul] using hpi_le_two_u
    calc
      Real.exp (-u) ≤ Real.exp (u - Real.pi) := Real.exp_le_exp.mpr hle
      _ = Real.exp (-Real.pi) * Real.exp u := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
  have hsinh_lower :
      (1 - Real.exp (-Real.pi)) * Real.exp u ≤ 2 * Real.sinh u := by
    calc
      (1 - Real.exp (-Real.pi)) * Real.exp u
          = Real.exp u - Real.exp (-Real.pi) * Real.exp u := by ring
      _ ≤ Real.exp u - Real.exp (-u) := by
            exact sub_le_sub_left hExpTail (Real.exp u)
      _ = 2 * Real.sinh u := by
            rw [Real.sinh_eq]
            nlinarith
  exact (div_le_div_iff₀ hsinh_pos hcoef_pos).2 <| by
    simpa [mul_comm] using hsinh_lower
