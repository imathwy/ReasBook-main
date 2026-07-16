import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_18

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 21.3.1 concerns the canonical source-facing owner
`IsBrownianMotionStartedAt μ X x`; the translated centered model is only a proof device behind the
reflection argument. The exit time is expressed directly through the canonical hitting-time owner
`hittingAfter` for the Brownian motion started at `x`. -/

section BrownianMotionExercise

variable {μ : Measure Ω}
variable {X : NNReal → Ω → ℝ}

-- Proof sketch: apply the reflection principle to the translated Brownian motion
-- `t ↦ x + B_t`, which starts from `x` and is killed when it reaches `{0, a}`. Iterating the
-- reflections across the endpoints produces the alternating image sum over the strips
-- `[na, (n + 1)a]`.
/-- Exercise 21.3.1 (1): for Brownian motion started at `x ∈ (0, a)`, the probability of staying
inside `(0, a)` up to time `T` is the alternating reflection sum of the terminal interval
probabilities over the strips `[na, (n + 1)a]`. -/
theorem brownianIntervalExitTime_survivalProbability_eq_reflectionSeries
    {a x : ℝ} (hX : IsBrownianMotionStartedAt μ X x) (hx : x ∈ Set.Ioo 0 a) (T : NNReal) :
    μ.real {ω | T < hittingAfter X ({0, a} : Set ℝ) 0 ω} =
      ∑' n : ℤ,
        ((-1 : ℝ) ^ Int.natAbs n) *
          μ.real {ω | X T ω ∈ Set.Icc ((n : ℝ) * a) (((n + 1 : ℤ) : ℝ) * a)} := sorry

end BrownianMotionExercise

-- Proof sketch: periodize the genuine nonnegative density `f`, identify the Fourier coefficients
-- of the periodization by integrating against the complex exponentials, and use the boundedness of
-- `x ↦ x^2 f x` to justify the summation and Fourier-inversion steps. Since mathlib defines
-- `charFun μ t = ∫ exp (t * x * I) dμ`, the Fourier coefficients are sampled at the negative
-- frequencies `-2πk`.
/-- Exercise 21.3.1 (2): if a probability law on `ℝ` has nonnegative density `f`, and if
`x ↦ x^2 f x` is bounded above, then the periodization of `f` is given by the Fourier series built
from the characteristic function `charFun μ`, sampled with the sign convention coming from Lean's
Fourier coefficients. -/
theorem poissonSummationFormula_of_density
    {f : ℝ → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hbound : BddAbove (Set.range fun x ↦ x ^ 2 * f x)) (s : ℝ) :
    ((∑' n : ℤ, f (s + n) : ℝ) : ℂ) =
      ∑' k : ℤ,
        charFun μ (-2 * Real.pi * k) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * s) := sorry

section BrownianMotionExercise

variable {μ : Measure Ω}
variable {X : NNReal → Ω → ℝ}

-- Proof sketch: start from the reflection-series identity in part (1), identify each strip
-- probability with an integral of the Gaussian density of `x + B_T`, apply the Poisson summation
-- formula from part (2) to that nonnegative Gaussian density, and rewrite the resulting odd
-- Fourier modes as the sine series of the killed heat kernel on `(0, a)`.
/-- Exercise 21.3.1 (3): combining the reflection-series formula with Poisson summation yields the
classical Fourier-sine expansion for the probability that Brownian motion started at
`x ∈ (0, a)` stays inside `(0, a)` up to time `T`. -/
theorem brownianIntervalExitTime_survivalProbability_eq_fourierSineSeries
    {a x : ℝ} (hX : IsBrownianMotionStartedAt μ X x) (hx : x ∈ Set.Ioo 0 a) (T : NNReal) :
    μ.real {ω | T < hittingAfter X ({0, a} : Set ℝ) 0 ω} =
      (4 / Real.pi) *
        ∑' k : ℕ,
          (1 / (2 * k + 1 : ℝ)) *
            Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * T / (2 * a ^ 2))) *
              Real.sin (((2 * k + 1 : ℝ) * Real.pi * x) / a) := sorry

end BrownianMotionExercise

end ProbabilityTheory
