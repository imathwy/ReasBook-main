import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_24_16 (from Items/Chap24) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E]
variable {F : Type w} [MeasurableSpace F] [TopologicalSpace F]

/-- The Laplace functional of a random measure kernel against a nonnegative measurable test
function. -/
def random_measure_laplace_functional
    (P : ProbabilityMeasure Ω) (X : Kernel Ω E) (f : E → ℝ≥0∞) : ℝ :=
  ∫ ω, Real.exp (-(∫⁻ x, f x ∂X ω).toReal) ∂(P : Measure Ω)

/-- The Poisson Laplace functional with intensity measure `μ`. -/
def poisson_laplace_functional (μ : Measure E) (f : E → ℝ≥0∞) : ℝ :=
  Real.exp
    (-(∫⁻ x, (1 - ENNReal.ofReal (Real.exp (-(f x).toReal))) ∂μ).toReal)

/-- A kernel-valued random measure is a Poisson point process with intensity `μ` when `μ` is
locally finite and the Laplace functional has the Poisson form for every nonnegative measurable
test function. -/
def is_poisson_point_process
    (P : ProbabilityMeasure Ω) (X : Kernel Ω E) (μ : Measure E) : Prop :=
  IsLocallyFiniteMeasure μ ∧
    ∀ f : E → ℝ≥0∞, Measurable f →
      random_measure_laplace_functional P X f = poisson_laplace_functional μ f

-- Proof sketch: unfold `is_poisson_point_process`; this is exactly the conjunction of local
-- finiteness of the intensity measure and the Poisson Laplace-functional identity.
/-- Expanding `is_poisson_point_process P X μ` gives the local-finiteness and Laplace-functional
characterization of a Poisson point process with intensity `μ`. -/
theorem is_poisson_point_process_iff
    (P : ProbabilityMeasure Ω) (X : Kernel Ω E) (μ : Measure E) :
    is_poisson_point_process P X μ ↔
      IsLocallyFiniteMeasure μ ∧
        ∀ f : E → ℝ≥0∞, Measurable f →
          random_measure_laplace_functional P X f = poisson_laplace_functional μ f := sorry

-- Proof sketch: use `Kernel.map_apply` and `Measure.map_apply` to rewrite the inner lintegrals,
-- then simplify the composed test function to `f ∘ φ`.
/-- Mapping a random measure kernel along `φ` composes its Laplace functional with `φ`. -/
theorem random_measure_laplace_functional_map
    (P : ProbabilityMeasure Ω) (X : Kernel Ω E) {φ : E → F} (hφ : Measurable φ)
    (f : F → ℝ≥0∞) (hf : Measurable f) :
    random_measure_laplace_functional P (X.map φ) f =
      random_measure_laplace_functional P X (f ∘ φ) := sorry

-- Proof sketch: rewrite the pushforward integral against `μ.map φ` as an integral against `μ`
-- using `lintegral_map`, and then simplify the composed Poisson exponent.
/-- The Poisson Laplace functional for the pushed-forward intensity `μ.map φ` is obtained by
composing the test function with `φ`. -/
theorem poisson_laplace_functional_map
    (μ : Measure E) {φ : E → F} (hφ : Measurable φ) (f : F → ℝ≥0∞) (hf : Measurable f) :
    poisson_laplace_functional (μ.map φ) f = poisson_laplace_functional μ (f ∘ φ) := sorry

-- Proof sketch: equip `μ.map φ` with the assumed local-finiteness, rewrite the Laplace functional
-- of `X.map φ` by `random_measure_laplace_functional_map`, rewrite the Poisson exponent by
-- `poisson_laplace_functional_map`, and apply the defining PPP identity for `X`.
/-- Theorem 24.16: a measurable image of a Poisson point process is again a Poisson point process,
with intensity measure the pushforward `μ.map φ`. -/
theorem poisson_point_process_map
    (P : ProbabilityMeasure Ω) (X : Kernel Ω E) (μ : Measure E)
    (hX : is_poisson_point_process P X μ) {φ : E → F} (hφ : Measurable φ)
    (hμφ : IsLocallyFiniteMeasure (μ.map φ)) :
    is_poisson_point_process P (X.map φ) (μ.map φ) := sorry

end ProbabilityTheory
