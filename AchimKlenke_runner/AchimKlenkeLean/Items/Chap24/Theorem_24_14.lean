import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E] [Bornology E]

/-- A nonnegative measurable test function on `E`, modeling the textbook class `B⁺(E)`. -/
structure NonnegativeMeasurableTestFunction (E : Type v) [MeasurableSpace E] where
  /-- The underlying nonnegative measurable function. -/
  toFun : E → ℝ≥0∞
  /-- The underlying function is measurable. -/
  measurable_toFun : Measurable toFun

/-- A bounded measurable real-valued test function on `E`, modeling the textbook class
`B_b^ℝ(E)`. -/
structure RealValuedBoundedMeasurableTestFunction (E : Type v) [MeasurableSpace E] where
  /-- The underlying bounded measurable real-valued function. -/
  toFun : E → ℝ
  /-- The underlying function is measurable. -/
  measurable_toFun : Measurable toFun
  /-- The underlying function has bounded range. -/
  bound' : ∃ C : ℝ, ∀ x, |toFun x| ≤ C

/-- A measure-valued random element has independent increments if its evaluations on every finite
family of pairwise disjoint bounded measurable sets form an independent family. -/
def HasIndependentMeasureIncrements (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  ∀ ⦃ι : Type u⦄ [Fintype ι] [DecidableEq ι] (A : ι → Set E),
    (∀ i, MeasurableSet (A i)) →
    (∀ i, Bornology.IsBounded (A i)) →
    (Set.univ : Set ι).PairwiseDisjoint A →
    iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω)

-- Proof sketch: expand the Laplace and characteristic transforms on simple functions supported on
-- pairwise disjoint bounded measurable sets, use the Poisson marginal law hypothesis for each
-- evaluation `X(A)`, apply the independent-increments hypothesis to factor the expectation, and
-- then pass to the general test functions by monotone-class / approximation arguments.
/-- Theorem 24.14: under the textbook Poisson point process hypotheses of independent increments
and Poisson counting laws on bounded measurable sets with intensity measure `μ`, the Laplace
transform and characteristic function of `X` are given by the usual exponential formulas. -/
theorem poisson_point_process_laplaceTransform_and_characteristicFunction
    (P : ProbabilityMeasure Ω) (μ : Measure E) (X : Ω → Measure E) (hX_meas : Measurable X)
    (hX_indep : HasIndependentMeasureIncrements P X)
    (hX_poisson :
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        HasLaw (fun ω ↦ X ω A)
          (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure ((μ A).toNNReal)))
          (P : Measure Ω)) :
    (∀ f : NonnegativeMeasurableTestFunction E,
      (∫ ω, Real.exp (-((∫⁻ x, f.toFun x ∂ X ω).toReal)) ∂(P : Measure Ω)) =
        Real.exp (∫ x, (Real.exp (-((f.toFun x).toReal)) - 1) ∂ μ)) ∧
    ∀ f : RealValuedBoundedMeasurableTestFunction E,
      (∫ ω, Complex.exp (((∫ x, f.toFun x ∂ X ω : ℝ) : ℂ) * Complex.I) ∂(P : Measure Ω)) =
        Complex.exp (∫ x, (Complex.exp ((f.toFun x : ℂ) * Complex.I) - 1) ∂ μ) := sorry
