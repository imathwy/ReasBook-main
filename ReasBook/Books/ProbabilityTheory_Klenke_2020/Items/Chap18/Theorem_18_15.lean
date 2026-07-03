import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_14
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

section Metropolis

variable (π : ProbabilityMeasure E) (q : E → E → ℝ≥0∞)
variable (hq : IsStochasticMatrix q)
variable (hπ_pos : ∀ x : E, 0 < (π : Measure E) ({x} : Set E))
variable (h_support_symm : ∀ x y : E, 0 < q x y ↔ 0 < q y x)
variable [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)]

-- Proof sketch: use the support symmetry hypothesis to show that every positive-probability
-- proposal edge for `q` remains a positive-probability Metropolis edge, because the acceptance
-- factor is strictly positive once the singleton masses of `π` are positive. Any positive
-- counting-measure set reachable from an irreducible proposal kernel is therefore still reachable
-- for the Metropolis kernel.
/-- Theorem 18.15 (1): if the proposal matrix `q` is stochastic and irreducible, the support of
`q` is symmetric, and the target distribution `π` has strictly positive singleton masses, then the
Metropolis kernel built from `q` and `π` is irreducible with respect to counting measure. -/
theorem metropolisKernel_isIrreducible_of_irreducible_proposal :
    Kernel.IsIrreducible (Measure.count : Measure E) (metropolisKernel π q) := sorry

-- Proof sketch: first show that the Metropolis kernel satisfies detailed balance with respect to
-- `π`, hence `π` is invariant. Then combine the irreducibility statement from
-- `metropolisKernel_isIrreducible_of_irreducible_proposal` with uniqueness of invariant
-- distributions for irreducible discrete kernels to identify the invariant-distribution set with
-- the singleton `{π}`.
/-- Theorem 18.15 (2): under the same hypotheses, the invariant distributions of the Metropolis
kernel consist exactly of the target distribution `π`; equivalently, `π` is the unique invariant
distribution of the Metropolis chain. -/
theorem metropolisKernel_invariantDistributions_eq_singleton :
    invariantDistributions (metropolisKernel π q) = {π} := sorry

-- Proof sketch: if the proposal kernel is already aperiodic, then every state has return times of
-- greatest common divisor `1`, and the same positive-support comparison transfers this to the
-- Metropolis kernel. If instead the proposal kernel fails to be reversible with respect to `π`,
-- then the textbook argument shows that the Metropolis acceptance step necessarily inserts
-- self-loops with positive mass somewhere, forcing period `1`.
/-- Theorem 18.15 (3): if, in addition, the proposal kernel is aperiodic or it is not reversible
with respect to `π`, then the Metropolis kernel is aperiodic. -/
theorem metropolisKernel_isAperiodic_of_proposalAperiodic_or_not_reversible
    (haperiodic_or_nonreversible :
      IsAperiodic (discreteMatrixKernel q) ∨
        ¬ Kernel.IsReversible (discreteMatrixKernel q) (π : Measure E)) :
    IsAperiodic (metropolisKernel π q) := sorry

end Metropolis

end ProbabilityTheory
