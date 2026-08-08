import Mathlib
import ProbabilityTheory_Klenke_2020.Chap09.Example_9_8
import ProbabilityTheory_Klenke_2020.Chap16.Theorem_16_14
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_21
import ProbabilityTheory_Klenke_2020.Chap24.Theorem_24_13

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Lebesgue measure on `[0, ∞)` transported to `NNReal`. -/
def nnrealLebesgue : Measure NNReal :=
  Measure.map Real.toNNReal ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))

/-- The process obtained by summing the `x`-coordinates of all Poisson points whose time
coordinate lies in `(0, t]`. -/
def poissonPointProcessIntegralProcess
    (X : Ω → Measure (NNReal × NNReal)) : NNReal → Ω → NNReal :=
  fun t ω ↦
    (∫⁻ z : NNReal × NNReal,
      (z.1 : ENNReal) *
        Set.indicator (Set.Ioc (0 : NNReal) t) (fun _ ↦ (1 : ENNReal)) z.2 ∂ X ω).toNNReal

-- Proof sketch: apply the Poisson mapping theorem to the restriction of `X` to
-- `NNReal × Set.Ioc s t`, identify the image measure under the first-coordinate map as
-- `((t - s : NNReal) : ENNReal) • ν`, and then read the increment as the associated
-- compound-Poisson or Lévy-Khinchin law with zero drift.
/-- The increments of the Poisson integral process have the subordinator Levy-Khinchin law with
zero drift and Levy measure `((t - s : NNReal) : ENNReal) • ν`. -/
theorem poissonPointProcessIntegralProcess_increment_hasLevyKhinchinRepresentation
    (ν : Measure NNReal) (P : ProbabilityMeasure Ω) (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) {s t : NNReal}
    (hst : s ≤ t) :
    ∃ μst : ProbabilityMeasure NNReal,
      HasLaw
        (fun ω ↦ poissonPointProcessIntegralProcess X t ω - poissonPointProcessIntegralProcess X s ω)
        (μst : Measure NNReal) (P : Measure Ω) ∧
      MeasureTheory.ProbabilityMeasure.HasSubordinatorLevyKhinchinRepresentation μst 0
        (((t - s : NNReal) : ENNReal) • ν) := sorry

-- Proof sketch: for disjoint time intervals, the restrictions of the Poisson point process to the
-- corresponding strips in `NNReal × NNReal` are independent, giving independent increments.
-- The strip `(r, r + s]` has intensity induced by restricting `nnrealLebesgue` to `Set.Ioc r
-- (r + s)`, whose
-- first-coordinate image depends only on `s`, so the increment law is translation invariant.
/-- Example 24.19: the stochastic integral of a Poisson point process on `NNReal × NNReal` with
intensity `ν ⊗ nnrealLebesgue` gives a process with stationary independent increments. -/
theorem poissonPointProcessIntegralProcess_hasStationaryIndependentIncrements
    (ν : Measure NNReal) (P : ProbabilityMeasure Ω) (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) :
    HasStationaryIndependentIncrements (poissonPointProcessIntegralProcess X) (P : Measure Ω) :=
  sorry

-- Proof sketch: for each sample point `ω`, the path is an increasing pure-jump cumulative sum
-- over the strips `NNReal × (0, t]`; such cumulative counting-measure integrals only jump when a
-- new Poisson point enters the strip, so they are right continuous.
/-- The Poisson integral process has right-continuous sample paths. -/
theorem poissonPointProcessIntegralProcess_hasRightContinuousPaths
    (ν : Measure NNReal) (P : ProbabilityMeasure Ω) (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) :
    HasRightContinuousPaths
      (fun t ω ↦ (poissonPointProcessIntegralProcess X t ω : ℝ)) := sorry

-- Proof sketch: if `s ≤ t`, then `Set.Ioc (0 : NNReal) s ⊆ Set.Ioc (0 : NNReal) t`, so the
-- integrand defining the path at time `s` is pointwise bounded by the integrand at time `t`.
-- Monotonicity of the nonnegative counting-measure integral gives the claim.
/-- Each sample path of the Poisson integral process is monotone increasing. -/
theorem poissonPointProcessIntegralProcess_monotone
    (X : Ω → Measure (NNReal × NNReal)) (ω : Ω) :
    Monotone (fun t : NNReal ↦ poissonPointProcessIntegralProcess X t ω) := sorry

end ProbabilityTheory
