import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_24

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  refine ⟨by
    simpa using
      (AddCircle.measure_univ :
        (volume : Measure UnitAddCircle) Set.univ = ENNReal.ofReal (1 : ℝ))
  ⟩

/-- The quarter-arc of `AddCircle 1` centered at `0`. -/
abbrev addCircleQuarterArc : Set UnitAddCircle :=
  Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ)

-- Proof sketch: `addCircleQuarterArc` is a closed ball in the metric additive circle, hence a
-- Borel set.
/-- The canonical quarter-arc used in the irrational-rotation non-mixing example is measurable. -/
theorem measurableSet_addCircleQuarterArc :
    MeasurableSet addCircleQuarterArc := by
  simpa [addCircleQuarterArc] using
    (measurableSet_closedBall :
      MeasurableSet (Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ)))

/-- Example 20.28: for irrational `r`, the rotation `x ↦ x + r (mod 1)` on the circle fails the
mixing correlation limit for the quarter-arc `addCircleQuarterArc`; in particular, this ergodic
rotation is not mixing. -/
-- Proof sketch: use irrationality to choose a subsequence of the orbit of `0` that lands in the
-- opposite semicircle. Along that subsequence, the translated quarter-arcs are disjoint, so the
-- self-correlation terms are `0` while the product of the marginal measures stays positive.
theorem irrational_addCircle_rotation_quarterArc_selfCorrelation_not_tendsto
    (r : ℝ) (hr : Irrational r) :
    ¬ Tendsto
      (fun n : ℕ ↦
        volume
          (addCircleQuarterArc ∩
            ((fun x : UnitAddCircle ↦ x + (r : UnitAddCircle))^[n]) ⁻¹' addCircleQuarterArc))
      atTop
      (nhds (volume addCircleQuarterArc * volume addCircleQuarterArc)) :=
  sorry

/-- The irrational rotation on `AddCircle 1` is not strongly mixing in the chapter sense. -/
theorem irrational_addCircle_rotation_not_stronglyMixing
    (r : ℝ) (hr : Irrational r) :
    ¬ IsStronglyMixing ((· + (r : UnitAddCircle))) volume := by
  intro hmix
  exact irrational_addCircle_rotation_quarterArc_selfCorrelation_not_tendsto r hr <|
    isStronglyMixing_tendsto_measure_inter_preimage_iterate hmix
      measurableSet_addCircleQuarterArc measurableSet_addCircleQuarterArc
