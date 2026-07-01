import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The Mellin transform of a measure on `[0, ∞)`. -/
abbrev mellinTransform (μ : Measure NNReal) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ^ s ∂μ

-- Proof sketch: unfold `mellinTransform` for the pushforward law `Measure.map X μ` and rewrite the
-- lower integral using `lintegral_map'`, so the Mellin transform becomes the extended expectation
-- of the canonical `ℝ≥0∞` power of `X`.
/-- The Mellin transform of the law of a nonnegative random variable is the lower integral of
`x ↦ x ^ s` along that variable. -/
theorem mellinTransform_map (μ : Measure Ω) (X : Ω → NNReal) (hX : AEMeasurable X μ) (s : ℝ) :
    mellinTransform (μ.map X) s =
      ∫⁻ ω, (X ω : ℝ≥0∞) ^ s ∂μ := by
  have hpow : AEMeasurable (fun x : NNReal ↦ (x : ℝ≥0∞) ^ s) (μ.map X) :=
    by fun_prop
  simpa [mellinTransform] using
    (lintegral_map' hpow hX)

section

variable {μ ν : Measure NNReal} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε ε₀ : ℝ}

-- Proof sketch: first handle laws with continuous densities on `[0, ∞)` by identifying the
-- Mellin transform with a holomorphic Mellin integral and invoking analytic continuation. Then
-- smooth arbitrary laws by multiplying with an independent `U_[1 - δ, 1]` factor, compare the
-- smoothed Mellin transforms on `[0, ε]`, and let `δ ↓ 0` using convergence in distribution of
-- the smoothed laws.
/-- Exercise 15.1.4: among nonnegative probability laws with some positive finite Mellin moment,
the values of the Mellin transform on any interval `[0, ε]` determine the law. -/
theorem measure_eq_of_mellinTransform_eq_on_Icc_of_exists_lt_top
    (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hμ_moment : mellinTransform μ ε₀ < ∞)
    (h_eq : ∀ s ∈ Set.Icc (0 : ℝ) ε,
      mellinTransform μ s = mellinTransform ν s) :
    μ = ν := sorry

-- Proof sketch: apply the positive-exponent characterization theorem to the pushforwards of `μ`
-- and `ν` under inversion `x ↦ x⁻¹`. The finite negative Mellin moment becomes a positive Mellin
-- moment for the inverted laws, and equality of `m(-s)` on `[0, ε]` becomes equality of the
-- ordinary Mellin transforms of those inverted laws.
/-- The negative-exponent Mellin data `m(-s)` on `[0, ε]` determine a nonnegative probability law
once one negative Mellin moment is finite. -/
theorem measure_eq_of_mellinTransform_neg_eq_on_Icc_of_exists_lt_top
    (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hμ_moment : mellinTransform μ (-ε₀) < ∞)
    (h_eq : ∀ s ∈ Set.Icc (0 : ℝ) ε,
      mellinTransform μ (-s) = mellinTransform ν (-s)) :
    μ = ν := sorry

end
