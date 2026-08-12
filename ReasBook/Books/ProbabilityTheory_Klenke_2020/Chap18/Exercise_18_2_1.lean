import ProbabilityTheory_Klenke_2020.Chap17.Example_17_55
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
variable [CompleteSpace E] [SecondCountableTopology E]

-- Proof sketch: apply Strassen's coupling characterization of the Lévy--Prokhorov distance and
-- then use Markov's inequality on the transport-cost random variable under a coupling realizing
-- the Wasserstein infimum. Rearranging the resulting estimate gives the squared form of the
-- textbook square-root bound.
/-- Exercise 18.2.1 (1): for probability measures on a Polish metric space, the
Lévy--Prokhorov distance is bounded above by the square root of the Wasserstein transport cost,
written here in the equivalent squared form over `ℝ≥0∞`. -/
theorem levyProkhorovDist_sq_le_wassersteinDistance
    (P Q : ProbabilityMeasure E) :
    ENNReal.ofReal (levyProkhorovDist (P : Measure E) (Q : Measure E)) ^ (2 : ℕ) ≤
      wassersteinDistance P Q := sorry

variable [BoundedSpace E]

-- Proof sketch: when `E` is bounded, use a coupling with Prohorov error close to
-- `levyProkhorovDist P Q`. The transport cost is controlled by `Metric.diam univ` on the matched
-- part of the coupling and by an additional `1` times the mismatch mass, giving the linear bound.
/-- Exercise 18.2.1 (2): if the metric space `E` has finite diameter, then the Wasserstein
distance is bounded above by `(diam(E) + 1)` times the Lévy--Prokhorov distance, with the
Wasserstein metric written as its defining coupling-cost infimum. -/
theorem wassersteinDistance_le_diam_add_one_mul_levyProkhorovDist
    (P Q : ProbabilityMeasure E) :
    wassersteinDistance P Q ≤
      ENNReal.ofReal
        ((Metric.diam (Set.univ : Set E) + 1) *
          levyProkhorovDist (P : Measure E) (Q : Measure E)) := sorry

end ProbabilityTheory
