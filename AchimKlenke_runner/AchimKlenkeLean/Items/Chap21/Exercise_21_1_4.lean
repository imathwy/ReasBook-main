import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory Topology NNReal ENNReal

noncomputable section

universe u v

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
variable {X : ℝ≥0 → Ω → E}

/-- Exercise 21.1.4 (1): if each time slice `X t` is measurable and every sample path is right
continuous on `[0, ∞)`, then the process is jointly measurable as a map on time and sample space.
-/
-- Proof sketch: approximate each path on `[0, ∞)` by right-step processes built from rational or
-- dyadic times. Each approximant is jointly measurable because it is piecewise constant in time
-- with measurable coefficients `X q`, and the right-continuity of the paths identifies `X` as the
-- pointwise limit of these approximants.
theorem measurable_uncurry_of_measurable_rightContinuous
    (hX_meas : ∀ t, Measurable (X t))
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t) :
    Measurable (Function.uncurry X) := sorry

namespace Adapted

/-- Exercise 21.1.4 (2): an adapted right-continuous process on a Polish state space is
progressively measurable. -/
-- Proof sketch: for each deterministic horizon `t`, restrict the process to `[0, t]`. Adaptedness
-- makes every time section measurable with respect to `ℱ t`, and right-continuity lets one again
-- approximate the restriction by step processes using only times in `[0, t]`, yielding the
-- required measurability on `Set.Iic t × Ω`.
theorem progMeasurable_of_rightContinuous
    {ℱ : Filtration ℝ≥0 inferInstance}
    {X : ℝ≥0 → Ω → E}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t) :
    ProgMeasurable ℱ X := sorry

end Adapted

/-- Exercise 21.1.4 (3): evaluating an adapted right-continuous process at a finite stopping time
is measurable with respect to the stopping-time σ-algebra. -/
-- Proof sketch: part (2) gives progressive measurability. Identify `ω ↦ X (τ ω) ω` with the
-- stopped value of `X` at the finite stopping time `τ`, and then apply the standard theorem that
-- the stopped value of a progressively measurable process is measurable for `𝓕_τ`.
theorem measurable_stoppedValue_of_adapted_rightContinuous
    {ℱ : Filtration ℝ≥0 inferInstance} {τ : Ω → ℝ≥0}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t)
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℝ≥0)) :
    Measurable[hτ.measurableSpace] (fun ω ↦ X (τ ω) ω) := by
  simpa [stoppedValue] using
    measurable_stoppedValue (hX_adapted.progMeasurable_of_rightContinuous hX_right_cont) hτ

end MeasureTheory
