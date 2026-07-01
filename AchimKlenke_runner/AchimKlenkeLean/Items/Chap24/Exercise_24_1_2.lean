import AchimKlenkeLean.Items.Chap24.Definition_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal Topology

universe u

variable {E : Type u} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.SeparableSpace E]

-- Proof sketch: identify `\mathcal M_1(E)` with `ProbabilityMeasure E`, pull back the
-- random-measure sigma-algebra `𝕄` along the canonical inclusion into `BoundedlyFiniteMeasure E`,
-- and compare the resulting generated sigma-algebra with the Borel sigma-algebra of the weak
-- topology on `ProbabilityMeasure E`.
/-- Exercise 24.1.2: the restriction of the random-measure sigma-algebra `𝕄` to the probability
measures `\mathcal M_1(E)` agrees with the Borel sigma-algebra of the weak-convergence topology
on `ProbabilityMeasure E`. -/
theorem randomMeasureMeasurableSpace_comap_probabilityMeasure_eq_borel :
    MeasurableSpace.comap ProbabilityMeasure.toBoundedlyFiniteMeasure
      (randomMeasureMeasurableSpace E) =
        borel (ProbabilityMeasure E) := sorry
