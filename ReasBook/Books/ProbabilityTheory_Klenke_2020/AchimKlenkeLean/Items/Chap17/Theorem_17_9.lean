import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {I : Type u} [AddMonoid I] [Preorder I]
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [mE : MeasurableSpace E]

/-- The shifted future path of a process `X` after time `s`, viewed again as an `I`-indexed path.
-/
def futurePath (X : I → Ω → E) (s : I) : Ω → I → E :=
  fun ω t ↦ X (t + s) ω

/-- A path-space kernel `κ` satisfies the future-path conditional-expectation formula when every
bounded measurable functional of the shifted future path has conditional expectation, with respect
to the history up to time `s`, equal to integration against the path law `κ (X s ω)`. -/
def HasFuturePathConditionalExpectationFormula
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E)) : Prop :=
  ∀ ⦃f : (I → E) → ℝ⦄, Measurable f → Bornology.IsBounded (Set.range f) →
    ∀ s x,
      (P x)[fun ω ↦ f (futurePath X s ω) | generatedFiltrationSpace X s] =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ∫ y, f y ∂κ (X s ω)

-- Proof sketch: for the forward direction, first reduce bounded measurable path functionals to
-- cylinder functions depending on finitely many future coordinates; the one-coordinate case is
-- exactly the Markov-property field in Definition 17.3, and the general finite-coordinate case
-- follows by induction and the tower property of conditional expectation. For the reverse
-- direction, specialize the future-path formula to cylinder indicators depending on a single
-- coordinate to recover the state-event Markov property.
/-- Theorem 17.9: under the measurable-process, initial-state, and path-law hypotheses from
Definition 17.3, the time-homogeneous Markov property is equivalent to the bounded measurable
future-path conditional-expectation formula
\[
\mathbf{E}_x\!\left[f\bigl((X_{t+s})_{t \in I}\bigr)\mid \mathcal F_s\right]
= \int_{E^I} f(y)\,\kappa(X_s,dy).
\]
-/
theorem isTimeHomogeneousMarkovProcess_iff_hasFuturePathConditionalExpectationFormula
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hX_meas : ∀ t, Measurable (X t))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun t : I ↦ X t ω)) :
    IsTimeHomogeneousMarkovProcess X P κ ↔
      HasFuturePathConditionalExpectationFormula X P κ := sorry

end ProbabilityTheory
