import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8
import ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_6
import ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

-- Proof sketch: apply the Kolmogorov extension theorem to the finite-dimensional distributions
-- determined by the convolution semigroup, then identify the coordinate process on the product
-- space as the resulting process with the prescribed increment laws.
/-- Theorem 14.47 (1): every convolution semigroup on `ℝ^d` is realized by the canonical process
on the path space `(ℝ^d)^{ℝ≥0}`, started from the deterministic point `x`, with stationary
independent increments and increment law `ν (t - s)` over every interval `[s,t]`. -/
theorem exists_pathMeasure_of_isConvolutionSemigroup
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) (x : Fin d → ℝ) :
    ∃ P : ProbabilityMeasure (NNReal → Fin d → ℝ),
      HasLaw (Function.eval 0) (Measure.dirac x) (P : Measure (NNReal → Fin d → ℝ)) ∧
        HasStationaryIndependentIncrements Function.eval (P : Measure (NNReal → Fin d → ℝ)) ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw
            (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω s)
            (ν (t - s) : Measure (Fin d → ℝ))
            (P : Measure (NNReal → Fin d → ℝ)) := sorry

-- Proof sketch: unpack the canonical owner `HasStationaryIndependentIncrements` into independent
-- increments and stationary increment laws, identify the law of `X_{s+t} - X_s` with
-- `X_t - X_0`, use independent increments plus `IndepFun.hasLaw_add` to obtain the convolution
-- identity, and read off the time-zero law from the zero increment.
/-- Theorem 14.47 (2): on an arbitrary probability space, the family of laws
`ν_t = law(X_t - X_0)` of a process with stationary independent increments is a convolution
semigroup on `ℝ^d`. -/
theorem incrementLaw_isConvolutionSemigroup
    {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (X : NNReal → Ω → Fin d → ℝ) (hX : IsStochasticProcess X)
    (hX_statIndep : HasStationaryIndependentIncrements X (P : Measure Ω)) :
    IsConvolutionSemigroupWithZero
      (fun t ↦
        ProbabilityMeasure.map P
          ((hX.measurable t).sub (hX.measurable 0)).aemeasurable) := sorry
