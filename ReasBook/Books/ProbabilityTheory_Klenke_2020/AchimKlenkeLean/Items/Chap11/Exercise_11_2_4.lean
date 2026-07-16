import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace Filter MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

namespace MeasureTheory

universe u

/- Exercise 11.2.4 is `source-facing`: it gives a counterexample to the converse of
Theorem 11.14. Its `core/canonical` owner layer is the existing martingale API
`Martingale`, `MemLp`, `Filtration.limitProcess`, and the chapter's square-variation owner
`⟨X⟩[ℱ, μ]`. Since Theorem 11.14 is formulated with the owner hypothesis that
`⟨X⟩[ℱ, μ]` is almost surely bounded above along sample paths, the public statement below is kept
in that owner shape rather than via a parallel "finite limit" wrapper. -/

-- Proof sketch: choose a standard square-integrable martingale whose quadratic variation diverges
-- almost surely, for example a partial-sum martingale built from independent centered
-- square-integrable increments with infinite accumulated variance. The martingale convergence still
-- holds almost surely, but the canonical square variation is not almost surely bounded above,
-- equivalently it does not admit an almost surely finite real limit.
/-- Exercise 11.2.4: there exists a filtered probability space carrying a square-integrable
martingale that converges almost surely to its canonical limit process, but whose canonical square
variation `⟨X⟩[ℱ, μ]` is not almost surely bounded above along sample paths; equivalently, it does
not admit an almost surely finite real limit. -/
theorem exists_square_integrable_martingale_ae_tendsto_limitProcess_not_ae_bddAbove_squareVariation :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          (∀ n, MemLp (X n) 2 μ) ∧
          (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
          ¬ ∀ᵐ ω ∂μ, BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω) := sorry

end MeasureTheory
