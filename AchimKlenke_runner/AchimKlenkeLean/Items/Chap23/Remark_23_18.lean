import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- The scaled logarithmic Laplace integral `ε log ∫ exp (φ / ε) dμ_ε` from Varadhan's lemma. -/
def scaled_log_laplace_integral
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (ε : PositiveParameter) : EReal :=
  ((ε : ℝ) : EReal) * ENNReal.log
    (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂ (μ ε : Measure E))

-- Proof sketch: unfold `scaled_log_laplace_integral`.
/-- Expanding `scaled_log_laplace_integral μ φ ε` gives the scaled logarithmic Laplace integral
`ε log ∫ exp (φ / ε) dμ_ε`. -/
theorem scaled_log_laplace_integral_def
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (ε : PositiveParameter) :
    scaled_log_laplace_integral μ φ ε =
      ((ε : ℝ) : EReal) * ENNReal.log
        (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂ (μ ε : Measure E)) := sorry

/-- The scaled logarithmic tail Laplace integral
`ε log ∫ exp (φ / ε) 𝟙_{ {φ ≥ M} } dμ_ε` from the tail condition in Varadhan's lemma. -/
def scaled_log_tail_laplace_integral
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (M : ℝ) (ε : PositiveParameter) : EReal :=
  ((ε : ℝ) : EReal) * ENNReal.log
    (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
      (μ ε : Measure E).restrict {x | M ≤ φ x})

-- Proof sketch: unfold `scaled_log_tail_laplace_integral`.
/-- Expanding `scaled_log_tail_laplace_integral μ φ M ε` gives the scaled logarithmic Laplace
integral restricted to the tail set `{x | M ≤ φ x}`. -/
theorem scaled_log_tail_laplace_integral_def
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (M : ℝ) (ε : PositiveParameter) :
    scaled_log_tail_laplace_integral μ φ M ε =
      ((ε : ℝ) : EReal) * ENNReal.log
        (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
          (μ ε : Measure E).restrict {x | M ≤ φ x}) := sorry

-- Proof sketch: for `x` with `φ x ≥ M`, compare
-- `exp (φ x / ε) = exp (M / ε) * exp ((φ x - M) / ε)` with
-- `exp (M / ε) * exp (α (φ x - M) / ε)` for `α > 1`. This yields
-- `limsup ε log ∫_{φ ≥ M} exp (φ / ε) dμ_ε ≤ -(α - 1) M + C`, where `C` is the bounded limsup
-- from the `α`-moment assumption. Letting `M → ∞` forces the infimum over `M > 0` to be `-∞`.
/-- Remark 23.18: if there exists `α > 1` such that
`limsup_{ε→0+} ε log ∫ exp (α φ / ε) dμ_ε < ∞`, then the tail condition
`inf_{M > 0} limsup_{ε→0+} ε log ∫ exp (φ / ε) 𝟙_{ {φ ≥ M} } dμ_ε = -∞` from Varadhan's lemma
holds. -/
theorem varadhan_tail_condition_of_moment_condition
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ)
    (hmoment :
      ∃ α > 1,
        Filter.limsup
          (fun ε : PositiveParameter ↦ scaled_log_laplace_integral μ (fun x ↦ α * φ x) ε)
          positiveParameterFilter < ⊤) :
    sInf
        ((fun M : ℝ ↦
            Filter.limsup
              (fun ε : PositiveParameter ↦ scaled_log_tail_laplace_integral μ φ M ε)
              positiveParameterFilter) '' Set.Ioi (0 : ℝ)) =
      (⊥ : EReal) := sorry

end ProbabilityTheory
