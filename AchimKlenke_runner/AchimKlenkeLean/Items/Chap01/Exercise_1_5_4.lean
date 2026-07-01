import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityMeasure Set

open scoped Topology

/-- The lower-orthant distribution function of a probability measure on `ℝ × ℝ`, viewed as a
map to `[0,1]`. -/
noncomputable def bivariateMeasureDistributionFunction
    (μ : ProbabilityMeasure (ℝ × ℝ)) : ℝ × ℝ → Icc (0 : ℝ) 1 :=
  fun x ↦ ⟨μ.toMeasure.real (Iic x), measureReal_nonneg, measureReal_le_one⟩

/-- The coercion of the bivariate distribution function back to `ℝ` is the lower-orthant mass
`μ (-∞, x₁] × (-∞, x₂]`. -/
@[simp] theorem bivariateMeasureDistributionFunction_apply
    (μ : ProbabilityMeasure (ℝ × ℝ)) (x : ℝ × ℝ) :
    (bivariateMeasureDistributionFunction μ x : ℝ) = μ (Iic x) := by
  rw [show (bivariateMeasureDistributionFunction μ x : ℝ) = μ.toMeasure.real (Iic x) by rfl]
  exact measureReal_eq_coe_coeFn μ (Iic x)

/-- A bivariate distribution function on `ℝ²` is a `[0,1]`-valued function that is monotone,
right-continuous from the upper-right orthant, has the correct limits at `±∞`, and is
2-increasing on rectangles. -/
class IsBivariateDistributionFunction (F : ℝ × ℝ → Icc (0 : ℝ) 1) : Prop where
  monotone : Monotone F
  right_continuous : ∀ x : ℝ × ℝ, ContinuousWithinAt (fun y ↦ (F y : ℝ)) (Ici x) x
  tendsto_neg_comp_atTop_zero :
    Tendsto (fun x : ℝ × ℝ ↦ (F (-x.1, -x.2) : ℝ)) atTop (𝓝 0)
  tendsto_atTop_one : Tendsto (fun x : ℝ × ℝ ↦ (F x : ℝ)) atTop (𝓝 1)
  rectangle_nonneg : ∀ ⦃x1 y1 x2 y2 : ℝ⦄, x1 ≤ y1 → x2 ≤ y2 →
    0 ≤ (F (y1, y2) : ℝ) - F (y1, x2) - F (x1, y2) + F (x1, x2)

/-- The lower-orthant distribution function of a probability measure on `ℝ × ℝ` satisfies the
standard bivariate distribution-function axioms. -/
instance (μ : ProbabilityMeasure (ℝ × ℝ)) :
    IsBivariateDistributionFunction (bivariateMeasureDistributionFunction μ) := sorry

-- Proof sketch: for the forward implication, use monotonicity and right-continuity of lower-orthant
-- masses and compute rectangle increments by inclusion-exclusion. For the reverse implication,
-- construct the unique Borel probability measure on `ℝ × ℝ` from the 2-increasing,
-- right-continuous lower-orthant function and use `Measure.ext_of_Iic` for uniqueness.
/-- Exercise 1.5.4: a function `F : ℝ² → [0,1]` is the distribution function of a uniquely
determined probability measure on `(ℝ², 𝓑(ℝ²))` if and only if it is monotone increasing and
right-continuous, satisfies `F (-x) → 0` and `F x → 1` as `x → ∞`, and is 2-increasing on
rectangles. -/
theorem existsUnique_probabilityMeasure_with_bivariateDistributionFunction_iff
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) :
    (∃! μ : ProbabilityMeasure (ℝ × ℝ), ∀ x : ℝ × ℝ, (F x : ℝ) = μ (Iic x)) ↔
      IsBivariateDistributionFunction F := sorry
