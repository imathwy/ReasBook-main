import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_24_7 (from Items/Chap24) -/
noncomputable section

open MeasureTheory
open scoped CompactlySupported NNReal

universe u

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [BorelSpace E] [T2Space E] [LocallyCompactSpace E]

/-- The Laplace transform of a probability law on measures, evaluated at a
nonnegative compactly supported continuous test function. -/
def random_measure_laplace_transform
    (P : ProbabilityMeasure (Measure E))
    (f : C_c(E, ℝ≥0)) : ℝ :=
  ∫ μ, Real.exp (-∫ x, (f x : ℝ) ∂μ) ∂(P : Measure (Measure E))

-- Proof sketch: unfold `random_measure_laplace_transform`; this is exactly the expectation of the
-- textbook test functional `μ ↦ exp (-∫ f dμ)` under the law `P`.
/-- Expanding `random_measure_laplace_transform P f` gives the textbook Laplace-transform formula
for the law `P` of a random measure. -/
theorem random_measure_laplace_transform_def
    (P : ProbabilityMeasure (Measure E))
    (f : C_c(E, ℝ≥0)) :
    random_measure_laplace_transform P f =
      ∫ μ, Real.exp (-∫ x, (f x : ℝ) ∂μ) ∂(P : Measure (Measure E)) :=
  sorry

/-- The characteristic function of a probability law on measures, evaluated at a
real-valued compactly supported continuous test function. -/
def random_measure_characteristic_function
    (P : ProbabilityMeasure (Measure E))
    (f : C_c(E, ℝ)) : ℂ :=
  ∫ μ, Complex.exp ((∫ x, f x ∂μ) * Complex.I) ∂(P : Measure (Measure E))

-- Proof sketch: unfold `random_measure_characteristic_function`; this is exactly the expectation
-- of the Fourier kernel `μ ↦ exp (i ∫ f dμ)` under the law `P`.
/-- Expanding `random_measure_characteristic_function P f` gives the textbook characteristic-
function formula for the law `P` of a random measure. -/
theorem random_measure_characteristic_function_def
    (P : ProbabilityMeasure (Measure E))
    (f : C_c(E, ℝ)) :
    random_measure_characteristic_function P f =
      ∫ μ, Complex.exp ((∫ x, f x ∂μ) * Complex.I) ∂(P : Measure (Measure E)) :=
  sorry

-- Proof sketch: for each nonnegative test function `f`, apply the one-dimensional uniqueness
-- theorem for Laplace transforms to the pushforward laws of `μ ↦ ∫ f dμ`; then invoke
-- `random_measure_law_eq_of_integral_or_disjoint_set_finite_dimensional_distributions`.
/-- Theorem 24.7 (1): the distribution of a random measure is determined by its Laplace transform
`f ↦ random_measure_laplace_transform P f` on `C_c^+(E)`. -/
theorem random_measure_distribution_ext_iff_laplace_transform_eq
    (P Q : ProbabilityMeasure (Measure E)) :
    P = Q ↔
      ∀ f : C_c(E, ℝ≥0),
        random_measure_laplace_transform P f = random_measure_laplace_transform Q f :=
  sorry

-- Proof sketch: for each real-valued test function `f`, apply
-- `MeasureTheory.Measure.ext_of_charFun` to the pushforward laws of `μ ↦ ∫ f dμ`; then use
-- `random_measure_law_eq_of_integral_or_disjoint_set_finite_dimensional_distributions`.
/-- Theorem 24.7 (2): the distribution of a random measure is determined by its characteristic
function `f ↦ random_measure_characteristic_function P f` on `C_c(E)`. -/
theorem random_measure_distribution_ext_iff_characteristic_function_eq
    (P Q : ProbabilityMeasure (Measure E)) :
    P = Q ↔
      ∀ f : C_c(E, ℝ),
        random_measure_characteristic_function P f =
          random_measure_characteristic_function Q f :=
  sorry
