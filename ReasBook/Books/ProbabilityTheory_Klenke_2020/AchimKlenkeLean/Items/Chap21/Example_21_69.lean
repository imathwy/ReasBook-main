import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

-- Proof sketch: localize the martingale by the deterministic stopping times `τₙ ≡ n`. Each
-- stopped process is again a martingale and is uniformly integrable because stopping at a bounded
-- deterministic time yields a bounded-time martingale. The localizing sequence increases
-- pointwise to `∞`, so this matches `IsLocalMartingale`.
/-- Example 21.69 (1): every martingale is a local martingale. -/
theorem martingale_isLocalMartingale {μ : Measure Ω} {ℱ : Filtration NNReal mΩ}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ) :
    IsLocalMartingale ℱ μ M := sorry

/- Example 21.69 (2) is `source-facing` existential content. The owner predicates are already
`IsLocalMartingale`, `UniformIntegrable`, and `Martingale`; the ambient filtered probability-space
data are primitive witnesses, not a second packaged owner. -/
-- Proof sketch: take the three-dimensional Brownian-motion example from the text, started away
-- from the origin, and set `M_t = ‖W_t‖⁻¹` up to the first hit of a small ball around `0`. The
-- harmonicity of `y ↦ ‖y‖⁻¹` gives the local-martingale property, while the explicit normal-law
-- computation shows `E[M_t] → 0`, so the process is uniformly integrable but cannot be a
-- martingale.
/-- Example 21.69 (2): there exists a uniformly integrable local martingale on a filtered
probability space which is not a martingale. -/
theorem exists_uniformIntegrable_localMartingale_not_martingale :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω'),
      letI := mΩ'
      ∃ (μ : Measure Ω') (_ : IsProbabilityMeasure μ) (ℱ : Filtration NNReal mΩ')
        (M : NNReal → Ω' → ℝ),
        IsLocalMartingale ℱ μ M ∧
          UniformIntegrable M 1 μ ∧
          ¬ Martingale M ℱ μ := sorry

end ProbabilityTheory
