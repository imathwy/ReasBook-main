import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: this is a source-facing bridge built on the canonical `MemLp`/`lpNorm` API. For
-- the forward implication, combine Hölder's inequality with the fact that a bounded measurable
-- random variable on a probability space belongs to every finite `L^q`; this gives integrability
-- of `X * Y` together with the stated bound. For the reverse implication, test the assumed
-- estimate on bounded truncations of `sgn(X) * |X|^(p - 1)` and pass to the limit.
/-- Exercise 7.2.3: if `p` and `q` are Hölder-conjugate exponents, then a real random variable on
a probability space belongs to `ℒ^p(P)` if and only if every bounded measurable real test random
variable `Y` yields an integrable product `X * Y` whose integral is uniformly controlled by a
constant multiple of the `L^q(P)` norm of `Y`. This avoids the total-expectation convention for
nonintegrable functions and matches the textbook bounded-functional interpretation. -/
theorem memLp_iff_exists_expectation_bound_of_bounded_measurable
    {P : Measure Ω} [IsProbabilityMeasure P] {p q : ℝ} {X : Ω → ℝ}
    (hpq : p.HolderConjugate q) :
    MemLp X (ENNReal.ofReal p) P ↔
      ∃ C : NNReal, ∀ ⦃Y : Ω → ℝ⦄, Measurable Y →
        (∃ M : NNReal, ∀ ω, |Y ω| ≤ M) →
        Integrable (X * Y) P ∧
          |∫ ω, X ω * Y ω ∂P| ≤ (C : ℝ) * lpNorm Y (ENNReal.ofReal q) P := sorry

end MeasureTheory
