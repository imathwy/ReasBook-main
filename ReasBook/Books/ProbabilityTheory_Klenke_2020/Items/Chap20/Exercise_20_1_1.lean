import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ProbabilityTheory
open MeasureTheory ProbabilityTheory

universe u v

variable {G : Type u} [Group G] [Fintype G]
variable {Ω : Type v} [MeasurableSpace Ω] [MulAction G Ω] [MeasurableConstSMul G Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] [SMulInvariantMeasure G Ω P]

-- Proof sketch: the finite average `ω ↦ (1 / |G|) ∑ g, X (g • ω)` is invariant under each group
-- element because left multiplication permutes `G`. The owner abstraction
-- `SMulInvariantMeasure G Ω P` yields measure preservation of every map `g • ·`, and the ambient
-- probability measure hypothesis keeps the conditional expectation onto
-- `⨅ g, MeasurableSpace.invariants (g • ·)` in the sigma-finite regime. Hence this average has the
-- same integrals as `X` on every invariant event, and uniqueness of conditional expectation
-- identifies it almost everywhere with `P[X | ...]`.
/-- Exercise 20.1.1: on a probability space with a finite group action by measure-preserving
measurable maps, the conditional expectation of an integrable real-valued function onto the
sigma-algebra of sets invariant under every group element is almost surely its average over the
group orbit. -/
theorem condExp_group_invariants_ae_eq_group_average
    {X : Ω → ℝ} (hX : Integrable X P) :
    P[X | ⨅ g : G, MeasurableSpace.invariants (g • ·)] =ᵐ[P]
      fun ω ↦ ((Fintype.card G : ℝ)⁻¹) * ∑ g : G, X (g • ω) := sorry
