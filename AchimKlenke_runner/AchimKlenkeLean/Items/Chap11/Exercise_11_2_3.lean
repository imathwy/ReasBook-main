import Mathlib
import AchimKlenkeLean.Items.Chap07.Definition_7_2
import AchimKlenkeLean.Items.Chap11.Corollary_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace Filter MeasureTheory.Filtration
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

universe u

/- Exercise 11.2.3 is `source-facing`: it asserts the existence of a filtered probability space
carrying a square-integrable martingale that converges almost surely to its canonical limit process
without converging in `L²`. Its `core/canonical` owner layer is the chapter API around
`Martingale`, `Filtration.limitProcess`, and `TendstoInLp`; the `eLpNorm` formulation is only the
derived `bridge/view` from `tendstoInLp_iff_tendsto_eLpNorm`, so the main declaration stays owner-
shaped instead of exposing a parallel bridge-level interface. -/

-- Proof sketch: use a standard square-integrable martingale with almost-sure limit whose second
-- moments are not uniformly bounded, so Corollary 11.11 does not apply; then identify the almost-
-- sure limit with the canonical `limitProcess` and show that the `L²` distance to that limit does
-- not tend to `0`.
/-- Exercise 11.2.3: there exists a square-integrable martingale that converges almost surely to
its canonical limit process but does not converge to that limit in `L²`. -/
theorem exists_square_integrable_martingale_ae_tendsto_limitProcess_not_tendstoInLp_two :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          (∀ n, MemLp (X n) 2 μ) ∧
          (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
          ¬ TendstoInLp 2 μ X (ℱ.limitProcess X μ) := sorry

end MeasureTheory
