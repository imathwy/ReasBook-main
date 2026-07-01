import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

namespace MeasureTheory

/- Exercise 11.2.1 is `source-facing`: it asserts the existence of a filtered probability space
supporting a martingale with four standard properties. The `core/canonical` owner layer is the
existing martingale API (`Martingale`, pointwise nonnegativity, expectation identities, and
almost-sure convergence), so no extra witness structure is kept here. -/

-- Proof sketch: use a standard non-uniformly-integrable nonnegative martingale, for example a
-- dyadic martingale or an exponential martingale from the earlier chapter, whose expectations stay
-- equal to `1` while the almost-sure limit is `0`.
/-- Exercise 11.2.1: there exists a filtered probability space carrying a nonnegative martingale
with expectation `1` at every time and which converges almost surely to `0`, so the `p = 1`
analogue of Theorem 11.10 can fail. -/
theorem exists_nonnegative_martingale_with_expectation_one_ae_tendsto_zero :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          0 ≤ X ∧
          (∀ n, μ[X n] = 1) ∧
          ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (0 : ℝ)) := sorry

end MeasureTheory
