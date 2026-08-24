import ProbabilityTheory_Klenke_2020.Chap24.Definition_24_10

open MeasureTheory ProbabilityTheory

universe u v

namespace ProbabilityTheory

/-- Theorem 24.12: on the chapter ambient locally compact Polish space `E`, every boundedly finite
intensity measure on `E` is the intensity measure of some Poisson point process. -/
theorem exists_poisson_point_process_with_intensity_measure
    {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [LocallyCompactSpace E] [PolishSpace E] (μ : BoundedlyFiniteMeasure E) :
    ∃ (Ω' : Type (max u v)) (_ : MeasurableSpace Ω') (P' : ProbabilityMeasure Ω')
      (X : Ω' → Measure E), IsPoissonPointProcess (μ : Measure E) P' X := by
  sorry

end ProbabilityTheory
