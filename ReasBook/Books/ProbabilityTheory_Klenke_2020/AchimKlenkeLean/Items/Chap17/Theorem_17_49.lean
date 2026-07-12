import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable (p : Kernel E E) [IsMarkovKernel p] [Kernel.IsIrreducible (Measure.count : Measure E) p]

-- Proof sketch: irreducibility implies that any invariant measures are unique up to a scalar
-- multiple. Since invariant distributions are probability measures of total mass `1`, that scalar
-- must be `1`, so the set of invariant distributions has at most one element.
/-- Theorem 17.49: if a discrete Markov kernel `p` is irreducible with respect to counting measure,
then `p` has at most one invariant distribution. Equivalently, the set of invariant probability
measures of `p` is subsingleton. -/
theorem invariantDistributions_subsingleton_of_irreducible
    : Set.Subsingleton (invariantDistributions p) := sorry

-- Proof sketch: apply `invariantDistributions_subsingleton_of_irreducible` to the invariant
-- distributions `μ` and `ν`; since both belong to `invariantDistributions p`, subsingularity of
-- that set forces `μ = ν`.
/-- Any two invariant distributions of a discrete irreducible Markov kernel are equal. -/
theorem eq_of_isInvariantDistribution_of_irreducible
    {μ ν : ProbabilityMeasure E}
    (hμ : Kernel.Invariant p (μ : Measure E)) (hν : Kernel.Invariant p (ν : Measure E)) :
    μ = ν := by
  have hsub : Set.Subsingleton (invariantDistributions p) :=
    invariantDistributions_subsingleton_of_irreducible p
  have hμ' : μ ∈ invariantDistributions p := (mem_invariantDistributions_iff p μ).2 hμ
  have hν' : ν ∈ invariantDistributions p := (mem_invariantDistributions_iff p ν).2 hν
  exact hsub hμ' hν'

end ProbabilityTheory
