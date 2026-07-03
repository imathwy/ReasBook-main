import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_17_14 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {I : Type u} [AddCommMonoid I] [PartialOrder I]
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [mE : MeasurableSpace E]

-- Proof sketch: decompose the conditional expectation along the countable partition `{τ = s}`;
-- on each slice apply the deterministic-time Markov property from Theorem 17.9, then sum over
-- the countable time set to recover the kernel expectation evaluated at the stopped state `X τ`.
/-- Theorem 17.14: if the countable time set is closed under addition, then every Markov process
with laws `P x` satisfies the strong Markov property with respect to its natural history
filtration. -/
theorem isTimeHomogeneousMarkovProcess_hasStrongMarkovProperty
    [Countable I]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    [IsTimeHomogeneousMarkovProcess X P κ] :
    HasStrongMarkovProperty P X κ := sorry

end ProbabilityTheory
