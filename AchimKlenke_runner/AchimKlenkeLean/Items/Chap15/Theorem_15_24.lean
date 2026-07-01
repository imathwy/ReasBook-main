import AchimKlenkeLean.Items.Chap15.Example_15_15
import AchimKlenkeLean.Items.Chap15.Theorem_15_23

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

-- Proof sketch: approximate `f` on `[0, ∞)` by even convex polygonal interpolants as in
-- `convexPolygonalInterpolant_isCharacteristicFunction`, then apply the owner-level Lévy recovery
-- theorem `exists_probabilityMeasure_of_tendsto_charFun` from Theorem 15.23 to the pointwise
-- limit of the corresponding characteristic functions.
/-- Theorem 15.24: Polya's criterion on `ℝ`: a continuous even function `f : ℝ → ℝ` with values
in `[0,1]`, normalized by `f 0 = 1`, and convex on `[0, ∞)` is the characteristic function of a
probability measure on `ℝ`. -/
theorem exists_probabilityMeasure_charFun_eq_of_continuous_even_convexOn_unitInterval
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_even : Function.Even f) (hf_zero : f 0 = 1)
    (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ t : ℝ, charFun μ t = (f t : ℂ) := sorry
