import ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

section MeasureAction

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Definition 17.42, measure part: the textbook left action `μ p`, implemented by composing the
initial measure `μ` with the canonical owner kernel `discreteMatrixKernel p`. -/
abbrev measureMatrixAction (μ : Measure E) (p : E → E → ℝ≥0∞) : Measure E :=
  discreteMatrixKernel p ∘ₘ μ

scoped[ProbabilityTheory] infixr:73 " ⋆ₘ " => measureMatrixAction

/-- Expanding the left action `μ ⋆ₘ p` recovers composition with the canonical discrete kernel. -/
@[simp] theorem measureMatrixAction_eq_comp (μ : Measure E) (p : E → E → ℝ≥0∞) :
    μ ⋆ₘ p = discreteMatrixKernel p ∘ₘ μ := rfl

-- Proof sketch: expand the canonical discrete kernel `discreteMatrixKernel p`, rewrite the
-- measure-kernel composition `(μ ⋆ₘ p) {x}` by
-- `Measure.comp_eq_sum_of_countable` on the countable discrete state space, and then evaluate each
-- row measure on the singleton `{x}`.
/-- Definition 17.42, measure part: the textbook entrywise left action
`∑' y, μ {y} * p y x` is exactly the singleton mass at `x` of the source-facing action `μ ⋆ₘ p`
on a countable discrete state space. -/
theorem comp_discreteMatrixKernel_apply_singleton_eq_tsum
    [Countable E] (μ : Measure E) (p : E → E → ℝ≥0∞) (x : E) :
    (μ ⋆ₘ p) {x} = ∑' y : E, μ {y} * p y x := sorry

end MeasureAction

section FunctionAction

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Definition 17.42, function part: the textbook right action `p f`, implemented by integrating
`f` against the canonical owner row measure `discreteMatrixKernel p x`. -/
abbrev matrixFunctionAction (p : E → E → ℝ≥0∞) (f : E → ℝ) : E → ℝ :=
  fun x ↦ ∫ y, f y ∂ discreteMatrixKernel p x

scoped[ProbabilityTheory] infixr:73 " ⋆ᶠ " => matrixFunctionAction

/-- Evaluating the right action `p ⋆ᶠ f` at `x` recovers the kernel integral against the `x`th
row of `discreteMatrixKernel p`. -/
@[simp] theorem matrixFunctionAction_apply (p : E → E → ℝ≥0∞) (f : E → ℝ) (x : E) :
    (p ⋆ᶠ f) x = ∫ y, f y ∂ discreteMatrixKernel p x := rfl

-- Proof sketch: expand `discreteMatrixKernel p x` as the row measure
-- `∑' y, p x y • δ_y`, use `hp` to ensure every row weight is finite, and then evaluate the
-- integral termwise on the Dirac masses.
/-- Definition 17.42, function part: for a stochastic transition matrix `p`, the textbook row
action `(p ⋆ᶠ f) x` agrees with the explicit series `∑' y, (p x y).toReal * f y`. The stochastic
hypothesis is the source-faithful finiteness condition ensuring that `toReal` does not erase
infinite matrix entries. -/
theorem integral_discreteMatrixKernel_eq_tsum
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ) (x : E)
    (hpf : Summable (fun y : E ↦ (p x y).toReal * f y)) :
    (p ⋆ᶠ f) x = ∑' y : E, (p x y).toReal * f y := sorry

end FunctionAction

end ProbabilityTheory
