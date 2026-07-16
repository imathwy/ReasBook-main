import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_30
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_38

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

noncomputable section

/-- In this item, the continuous Brownian path space is equipped with its Borel `σ`-algebra. -/
local instance brownianPathSpaceMeasurableSpace : MeasurableSpace BrownianPathSpace :=
  borel BrownianPathSpace

/-- The Brownian path space carries the canonical Borel-space structure coming from its topology. -/
local instance brownianPathSpaceBorelSpace : BorelSpace BrownianPathSpace :=
  ⟨rfl⟩

-- Proof sketch: this is the source-facing one-way implication extracted from the canonical
-- finite-dimensional-distribution API of Theorem 21.38.
/-- Theorem 21.37: weak convergence of probability laws on `C([0, ∞), ℝ)` implies convergence of
all finite-dimensional marginal laws. -/
theorem brownianPathSpace_tendsto_finiteDimensionalMarginals
    (μs : ℕ → ProbabilityMeasure BrownianPathSpace) (μ : ProbabilityMeasure BrownianPathSpace)
    (hμ : Tendsto μs atTop (𝓝 μ)) (n : ℕ) (times : Fin (n + 1) → NNReal) :
    Tendsto
      (fun m ↦ continuousPathFiniteDimensionalDistribution (μs m) times)
      atTop
      (𝓝 (continuousPathFiniteDimensionalDistribution μ times)) := sorry
