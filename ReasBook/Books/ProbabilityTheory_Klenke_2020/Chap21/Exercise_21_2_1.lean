import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

local notation "nonnegativeLebesgue" => volume.restrict (Set.Ici (0 : ℝ))

section BrownianMotionExercise

variable [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {B : NNReal → Ω → ℝ}

-- Proof sketch: write the average as a centered Gaussian linear functional of the Brownian path.
-- Fubini and the Brownian covariance kernel `min(s,t)` give expectation `0` and covariance
-- integral `∫₀¹∫₀¹ min(s,t) ds dt = 1/3`; the expectation statement is the first moment
-- computation.
/-- Exercise 21.2.1 (1): item (i), the expectation of the Brownian sample-path average over
`[0,1]` is zero. -/
theorem brownianUnitIntervalAverage_expectation (hB : IsBrownianMotion μ B) :
    ∫ ω, (∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω) ∂μ = 0 := sorry

-- Proof sketch: the same covariance computation as in part (i) shows that
-- `Var[∫₀¹ B_s ds] = ∫₀¹∫₀¹ min(s,t) ds dt = 1/3`.
/-- Exercise 21.2.1 (2): item (i), the variance of the Brownian sample-path average over `[0,1]`
is `1 / 3`. -/
theorem brownianUnitIntervalAverage_variance (hB : IsBrownianMotion μ B) :
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω; μ] = 1 / 3 := sorry

-- Proof sketch: almost every Brownian sample path is continuous, so its zero set is closed. A
-- nontrivial interval of zeros would force a constant segment and hence violate the Gaussian
-- increment law; cover the zero set by intervals on which oscillation is small and conclude it has
-- Lebesgue measure zero.
/-- Exercise 21.2.1 (3): item (ii), almost every Brownian sample path has zero set of Lebesgue
measure zero on `[0, ∞)`, modeled here by Lebesgue measure on `ℝ` restricted to `Set.Ici 0`. -/
theorem brownianZeroSet_volume_eq_zero_ae (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, nonnegativeLebesgue {t : ℝ | B (Real.toNNReal t) ω = 0} = 0 := sorry

-- Proof sketch: expand the square, use linearity of expectation, and evaluate the resulting
-- covariance integrals for `B_t` and the path average. This yields
-- `∫₀¹ E[(B_t - ∫₀¹ B_s ds)^2] dt = 1/6`.
/-- Exercise 21.2.1 (4): item (iii), the expectation of the integrated squared deviation from the
unit-interval Brownian average is `1 / 6`. -/
theorem brownianUnitIntervalCenteredQuadraticDeviation_expectation (hB : IsBrownianMotion μ B) :
    ∫ ω, (∫ t in (0 : ℝ)..1,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2) ∂μ = 1 / 6 := sorry

-- Proof sketch: the centered process `t ↦ B_t - ∫₀¹ B_s ds` is Gaussian with explicit covariance
-- kernel. For a centered Gaussian process, the variance of the integrated square is
-- `2 ∫₀¹∫₀¹ K(s,t)^2 ds dt`, and evaluating this kernel integral gives `1/45`.
/-- Exercise 21.2.1 (5): item (iii), the variance of the integrated squared deviation from the
unit-interval Brownian average is `1 / 45`. -/
theorem brownianUnitIntervalCenteredQuadraticDeviation_variance (hB : IsBrownianMotion μ B) :
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2; μ] = 1 / 45 := sorry

end BrownianMotionExercise

end ProbabilityTheory
