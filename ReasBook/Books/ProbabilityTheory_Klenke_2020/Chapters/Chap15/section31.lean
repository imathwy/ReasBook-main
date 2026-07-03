import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_15_31 (from Items/Chap15) -/
open MeasureTheory
open scoped Topology

section

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

-- Proof sketch: pass from the finite law on `ℝ` to the corresponding complex moment-
-- generating function along the imaginary axis, differentiate under the integral sign using the
-- `n`th absolute-moment bound, and then transfer the resulting analyticity back to `charFun`.
/- Theorem 15.31 (1): item (i) is the owner-level differentiability theorem for characteristic
functions with a finite `n`th moment. In mathlib this is already the canonical declaration
`MeasureTheory.contDiff_charFun`. -/
recall MeasureTheory.contDiff_charFun

-- Proof sketch: write the difference quotients as oscillatory integrals, dominate them by the
-- `k`th absolute moment using the remainder estimate from Lemma 15.30, and apply dominated
-- convergence for each `k ≤ n`.
/- Theorem 15.31 (2): item (i) also uses the owner-level derivative formula for characteristic
functions with a finite `n`th moment. In mathlib this is the canonical declaration
`MeasureTheory.iteratedDeriv_charFun`. -/
recall MeasureTheory.iteratedDeriv_charFun

-- Proof sketch: compare `charFun μ (t + h)` with the `n`th partial sum via the remainder term
-- from Lemma 15.30, bound that remainder by `|h|^n E[|X|^n] / n!`, and let `n → ∞`.
/-- Theorem 15.31 (4): Item (iii). If the scaled absolute moments satisfy
`|h|^n E[|X|^n] / n! → 0`, then the characteristic function admits the power-series expansion in
the increment `h`. -/
theorem charFun_eq_tsum_of_moment_growth (t h : ℝ)
    (h_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ)
    (h_growth :
      Filter.Tendsto (fun n : ℕ ↦ |h| ^ n * (∫ x, |x| ^ n ∂μ) / n.factorial) Filter.atTop
        (𝓝 0)) :
    charFun μ (t + h) =
      ∑' k : ℕ,
        (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
          ∫ x, Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k ∂μ := sorry

-- Proof sketch: expand `exp (|h x|)` into its positive power series, use monotone convergence to
-- control the coefficients `|h|^n E[|X|^n] / n!`, verify the growth hypothesis from item (iii),
-- and then apply the preceding power-series theorem.
/-- Theorem 15.31 (5): Item (iii), in particular. If `E[e^{|hX|}] < ∞`, then the same
power-series expansion for `charFun μ (t + h)` holds. -/
theorem charFun_eq_tsum_of_integrable_exp_abs (t h : ℝ)
    (h_exp : Integrable (fun x : ℝ ↦ Real.exp |h * x|) μ) :
    charFun μ (t + h) =
      ∑' k : ℕ,
        (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
          ∫ x, Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k ∂μ := sorry

end

section

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

-- Proof sketch: specialize the derivative formula from item (i) to `k = 1, 2` at `t = 0`, then
-- apply the second-order Taylor expansion with remainder `o(t^2)` encoded by a function
-- `ε(t) → 0`.
/-- Theorem 15.31 (3): Item (ii). A finite second moment yields the quadratic expansion of the
characteristic function at `0` with a remainder `ε(t) t^2` and `ε(t) → 0`. -/
theorem charFun_secondOrderExpansion_at_zero (hμ : MemLp id 2 μ) :
    ∃ ε : ℝ → ℂ,
      Filter.Tendsto ε (𝓝 0) (𝓝 0) ∧
        ∀ t : ℝ,
          charFun μ t =
            1
              + Complex.I * (t : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ)
              - (1 / 2 : ℂ) * (t : ℂ) ^ 2 * ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ)
              + ε t * (t : ℂ) ^ 2 := sorry

end
