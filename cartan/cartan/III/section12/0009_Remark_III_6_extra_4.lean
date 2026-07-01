import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this runner, so the statement
-- surface was checked directly against Mathlib's `Complex.norm_exp`, `Complex.sin_mul_I`,
-- `Complex.cos_mul_I`, and `Complex.exp_mul_I`.

private theorem exists_nonneg_real_ge (c M : ℝ) :
    ∃ x : ℝ, c ≤ x ∧ M ≤ x ∧ 0 ≤ x := by
  refine ⟨max (max c M) 0, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left c M) (le_max_left (max c M) 0)
  · exact le_trans (le_max_right c M) (le_max_left (max c M) 0)
  · exact le_max_right (max c M) 0

/-- Remark III.6-extra-4 (1): the oscillatory factor `exp (-I * z)` is bounded by `1` on the
closed lower half-plane, matching the contour-closing direction used for
`∫ x, f x * exp (-I * x)`. -/
theorem exp_neg_I_mul_norm_le_one_of_nonpos_im
    {z : ℂ} (hz : z.im ≤ 0) :
    ‖Complex.exp (-Complex.I * z)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simpa [Complex.mul_re] using hz

/-- Remark III.6-extra-4 (2): more generally, `exp (a * z)` has norm at most `1` exactly on the
half-plane where the real part of `a * z` is nonpositive. -/
theorem exp_mul_norm_le_one_iff
    (a z : ℂ) :
    ‖Complex.exp (a * z)‖ ≤ 1 ↔ (a * z).re ≤ 0 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]

/-- Remark III.6-extra-4 (3): `sin z` is unbounded on every closed upper horizontal half-plane. -/
theorem complex_sin_unbounded_on_closed_upper_half_plane
    (c M : ℝ) :
    ∃ z : ℂ, c ≤ z.im ∧ M ≤ ‖Complex.sin z‖ := by
  obtain ⟨x, hcx, hMx, hx⟩ := exists_nonneg_real_ge c M
  refine ⟨x * Complex.I, ?_, ?_⟩
  · simpa [Complex.mul_im] using hcx
  · calc
      M ≤ x := hMx
      _ ≤ Real.sinh x := Real.self_le_sinh_iff.2 hx
      _ = ‖Complex.sin (x * Complex.I)‖ := by
        rw [Complex.sin_mul_I, ← Complex.ofReal_sinh, Complex.norm_mul, Complex.norm_I, mul_one]
        calc
          Real.sinh x = |Real.sinh x| := by
            rw [abs_of_nonneg (Real.sinh_nonneg_iff.2 hx)]
          _ = ‖(Real.sinh x : ℂ)‖ := by
            symm
            exact RCLike.norm_ofReal (Real.sinh x)

/-- Remark III.6-extra-4 (4): `sin z` is unbounded on every closed lower horizontal half-plane. -/
theorem complex_sin_unbounded_on_closed_lower_half_plane
    (c M : ℝ) :
    ∃ z : ℂ, z.im ≤ c ∧ M ≤ ‖Complex.sin z‖ := by
  obtain ⟨z, hz, hMz⟩ := complex_sin_unbounded_on_closed_upper_half_plane (-c) M
  refine ⟨-z, ?_, ?_⟩
  · simpa using neg_le_neg hz
  · simpa using hMz

/-- Remark III.6-extra-4 (5): `cos z` is unbounded on every closed upper horizontal half-plane. -/
theorem complex_cos_unbounded_on_closed_upper_half_plane
    (c M : ℝ) :
    ∃ z : ℂ, c ≤ z.im ∧ M ≤ ‖Complex.cos z‖ := by
  obtain ⟨x, hcx, hMx, hx⟩ := exists_nonneg_real_ge c M
  refine ⟨x * Complex.I, ?_, ?_⟩
  · simpa [Complex.mul_im] using hcx
  · calc
      M ≤ x := hMx
      _ ≤ Real.sinh x := Real.self_le_sinh_iff.2 hx
      _ ≤ Real.cosh x := (Real.sinh_lt_cosh x).le
      _ = ‖Complex.cos (x * Complex.I)‖ := by
        rw [Complex.cos_mul_I, ← Complex.ofReal_cosh]
        calc
          Real.cosh x = |Real.cosh x| := by
            rw [abs_of_nonneg (Real.cosh_pos x).le]
          _ = ‖(Real.cosh x : ℂ)‖ := by
            symm
            exact RCLike.norm_ofReal (Real.cosh x)

/-- Remark III.6-extra-4 (6): `cos z` is unbounded on every closed lower horizontal half-plane. -/
theorem complex_cos_unbounded_on_closed_lower_half_plane
    (c M : ℝ) :
    ∃ z : ℂ, z.im ≤ c ∧ M ≤ ‖Complex.cos z‖ := by
  obtain ⟨z, hz, hMz⟩ := complex_cos_unbounded_on_closed_upper_half_plane (-c) M
  refine ⟨-z, ?_, ?_⟩
  · simpa using neg_le_neg hz
  · simpa using hMz

-- For later integral calculations with `sin^n x` or `cos^n x`, rewrite the trigonometric factors
-- via complex exponentials before applying the residue method.
