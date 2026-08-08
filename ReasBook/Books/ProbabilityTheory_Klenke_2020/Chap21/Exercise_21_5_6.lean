import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The positive-frequency cosine mode in the half-range Fourier expansion of `1_[0,t]`. -/
def indicator_Icc_zero_t_fourier_cosine_mode (t x : ℝ) (n : ℕ+) : ℝ :=
  (2 * Real.sin ((n : ℝ) * Real.pi * t)) / ((n : ℝ) * Real.pi) *
    Real.cos ((n : ℝ) * Real.pi * x)

/-- The Fourier-cosine term sequence whose sum recovers the indicator of `[0, t]` away from the
jump point. The zeroth term is the constant mode `t`, and the positive terms come from
`indicator_Icc_zero_t_fourier_cosine_mode`. -/
def indicator_Icc_zero_t_fourier_term (t x : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => indicator_Icc_zero_t_fourier_cosine_mode t x ⟨n + 1, Nat.succ_pos _⟩

@[simp] theorem indicator_Icc_zero_t_fourier_term_zero (t x : ℝ) :
    indicator_Icc_zero_t_fourier_term t x 0 = t :=
  rfl

@[simp] theorem indicator_Icc_zero_t_fourier_term_succ_eq_mode (t x : ℝ) (n : ℕ) :
    indicator_Icc_zero_t_fourier_term t x (n + 1) =
      indicator_Icc_zero_t_fourier_cosine_mode t x ⟨n + 1, Nat.succ_pos _⟩ :=
  rfl

-- Proof sketch: unfold the definition of `indicator_Icc_zero_t_fourier_term`; at index `n + 1`
-- it is exactly the positive-mode cosine coefficient from the exercise statement.
/-- The positive Fourier modes of `indicator_Icc_zero_t_fourier_term` are the cosine coefficients
`2 sin((n + 1)π t) / ((n + 1)π)`. -/
theorem indicator_Icc_zero_t_fourier_term_succ (t x : ℝ) (n : ℕ) :
    indicator_Icc_zero_t_fourier_term t x (n + 1) =
      (2 * Real.sin ((n + 1 : ℝ) * Real.pi * t)) / ((n + 1 : ℝ) * Real.pi) *
        Real.cos ((n + 1 : ℝ) * Real.pi * x) := by
  simp [indicator_Icc_zero_t_fourier_cosine_mode]

-- Proof sketch: identify `indicator_Icc_zero_t_fourier_term t x` as the cosine Fourier series of
-- the step function `1_[0,t]`, use the classical pointwise convergence theorem for Fourier series
-- of piecewise smooth functions on `(0,1)`, and evaluate away from the jump point `x = t`.
/-- Exercise 21.5.6: for `t ∈ (0, 1)` and `x ∈ (0, 1) \ {t}`, the Fourier-cosine series with
zeroth term `t` and coefficients `2 sin(nπ t) / (nπ)` sums to the indicator of `[0, t]` at
`x`. -/
theorem indicator_Icc_zero_t_hasSum_fourier_cosine_series {t x : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hx : x ∈ Set.Ioo 0 1) (hxt : x ≠ t) :
    HasSum (indicator_Icc_zero_t_fourier_term t x)
      ((Set.Icc 0 t).indicator (fun _ ↦ (1 : ℝ)) x) := sorry
