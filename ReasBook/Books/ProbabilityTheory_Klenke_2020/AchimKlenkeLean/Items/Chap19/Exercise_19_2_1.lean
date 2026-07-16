import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_42
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

namespace Kernel

/-- A continuous linear endomorphism of `L²(π)` realizes kernel averaging along `κ` if every
square-integrable representative `φ` is sent to the `L²(π)` class of `x ↦ ∫ y, φ y ∂κ x`.
Because the condition is required for every representative of an `L²` class, it encodes the
descent of kernel averaging to a genuine operator on `L²(π)` rather than depending on a chosen
coercion `L²(π) → E → ℝ`. -/
def IsL2TransitionOperator (κ : Kernel E E) (π : Measure E)
    (T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)) : Prop :=
  ∀ ⦃φ : E → ℝ⦄ (hφ : MemLp φ 2 π), T (hφ.toLp φ) =ᵐ[π] fun x ↦ ∫ y, φ y ∂κ x

end Kernel

-- Proof sketch: for the forward implication, use detailed balance to rewrite
-- `⟪T f, g⟫ = ∫ x ∫ y, f y * g x ∂(discreteMatrixKernel p x) ∂π` symmetrically in `f` and `g`,
-- giving a symmetric operator and hence a self-adjoint one. For the reverse implication, test the
-- symmetry identity on indicator functions of measurable sets to recover the detailed-balance
-- equality in the definition of `Kernel.IsReversible`.
/-- Exercise 19.2.1: a discrete transition matrix `p` is reversible with respect to `π` if and
only if the `L²(π)` Markov operator `f ↦ p f` is self-adjoint. Here the operator is represented by
any continuous linear map on `L²(π)` that realizes one-step averaging against
`discreteMatrixKernel p` on every square-integrable representative. -/
theorem discreteMatrix_isReversible_iff_markovOperator_isSelfAdjoint
    {p : E → E → ℝ≥0∞} {π : Measure E}
    {T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)}
    (hT : (discreteMatrixKernel p).IsL2TransitionOperator π T) :
    IsReversible (discreteMatrixKernel p) π ↔ IsSelfAdjoint T := sorry

end ProbabilityTheory
