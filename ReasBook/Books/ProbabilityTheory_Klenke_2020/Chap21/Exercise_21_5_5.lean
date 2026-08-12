import ProbabilityTheory_Klenke_2020.Chap21.Example_21_29

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The coefficient sequence in the cosine-basis construction of Brownian motion from
Example 21.29: the zeroth coefficient is the constant-mode Gaussian coordinate, and the
positive-frequency coefficients are the cosine coordinates scaled by `1 / (nπ)` after integrating
the basis functions `b₀(x) = 1` and `bₙ(x) = √2 cos(nπx)` from `0` to `t`. -/
def brownianFourierCoefficients (ξ : ℕ → Lp ℝ 2 μ) : ℕ → Ω → ℝ
  | 0 => ξ 0
  | n + 1 => fun ω ↦ ξ (n + 1) ω / (((n + 1 : ℝ) * Real.pi))

@[simp] theorem brownianFourierCoefficients_zero (ξ : ℕ → Lp ℝ 2 μ) :
    brownianFourierCoefficients ξ 0 = ξ 0 :=
  rfl

@[simp] theorem brownianFourierCoefficients_succ (ξ : ℕ → Lp ℝ 2 μ) (n : ℕ) :
    brownianFourierCoefficients ξ (n + 1) =
      fun ω ↦ ξ (n + 1) ω / (((n + 1 : ℝ) * Real.pi)) :=
  rfl

section BrownianFourierCoefficients

variable [IsProbabilityMeasure μ]
variable (ξ : ℕ → Lp ℝ 2 μ)
variable (hξ_gaussian : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)

-- Proof sketch: `brownianFourierCoefficients ξ 0` is just the zeroth Gaussian coordinate, and for
-- `n ≥ 1` the coefficient is `ξₙ / (nπ)`. Hence the second moments are `1` at `n = 0` and
-- `1 / (π² n²)` for positive modes, which is summable. Tonelli or monotone convergence gives
-- integrability of `∑ (Aₙ)²`, forcing almost-sure square summability.
/-- Exercise 21.5.5 (1): the coefficients in the cosine-basis construction of Brownian motion are
almost surely square-summable. -/
theorem brownianFourierCoefficients_sqSummable_ae :
    ∀ᵐ ω ∂μ, Summable (fun n ↦ (brownianFourierCoefficients ξ n ω) ^ (2 : ℕ)) := sorry

variable (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)

-- Proof sketch: the positive-mode coefficients are independent centered Gaussians with standard
-- deviation comparable to `1 / n`. Kolmogorov's three-series theorem applied to
-- `brownianFourierCoefficients ξ` yields almost-sure divergence of the nonnegative series
-- `∑ |Aₙ|`, and adding the zeroth term does not change the divergence conclusion.
/-- Exercise 21.5.5 (2): the series of absolute values of the Brownian Fourier coefficients
diverges to `+∞` almost surely. -/
theorem brownianFourierCoefficients_absPartialSums_tendsto_atTop_ae :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), |brownianFourierCoefficients ξ k ω|)
        atTop atTop := sorry

-- Proof sketch: the coefficients form an independent centered Gaussian sequence with summable
-- variances, namely `1` at index `0` and `1 / (π² n²)` on the positive modes. Kolmogorov's
-- three-series theorem therefore gives almost-sure convergence of the series `∑ Aₙ`.
/-- Exercise 21.5.5 (3): the Brownian Fourier coefficient series itself converges almost surely. -/
theorem brownianFourierCoefficients_summable_ae :
    ∀ᵐ ω ∂μ, Summable (fun n ↦ brownianFourierCoefficients ξ n ω) := sorry

end BrownianFourierCoefficients

end ProbabilityTheory
