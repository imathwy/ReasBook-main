import AchimKlenkeLean.Items.Chap08.Example_8_27
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

/- Definition 19.8: reversibility with respect to a measure is the canonical mathlib notion
`ProbabilityTheory.Kernel.IsReversible`. For the textbook's existential "the matrix is
reversible" phrasing, the witness measure must be taken nonzero; `IsReversible κ 0` is otherwise
trivial. On singleton sets this predicate is the detailed balance identity
`p(x,y) π({x}) = p(y,x) π({y})`. -/
recall ProbabilityTheory.Kernel.IsReversible

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- On a discrete state space, reversibility of `discreteMatrixKernel p` with respect to `π` is
equivalent to the singleton detailed balance identities
`p(x,y) π({x}) = p(y,x) π({y})`. -/
theorem isReversible_discreteMatrixKernel_iff
    {p : E → E → ℝ≥0∞} {π : Measure E} :
    IsReversible (discreteMatrixKernel p) π ↔
      ∀ x y : E, p x y * π {x} = p y x * π {y} := sorry

end ProbabilityTheory
