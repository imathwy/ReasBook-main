module

public import Mathlib.Probability.Moments.Covariance

public section

universe u v

namespace ProbabilityTheory

/-- The covariance between distinct components of a mutually independent
real-valued family is zero. -/
theorem iIndepFun.covariance_eq_zero
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_memLp : ∀ i, MeasureTheory.MemLp (X i) 2 μ) {i j : ι} (hij : i ≠ j) :
    cov[X i, X j; μ] = 0 :=
  (h_indep.indepFun hij).covariance_eq_zero (h_memLp i) (h_memLp j)

end ProbabilityTheory
