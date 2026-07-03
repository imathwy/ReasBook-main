import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_20_1 (from Items/Chap20) -/
open MeasureTheory ProbabilityTheory

universe u v w

/- Definition 20.1: a stochastic process indexed by a set closed under addition is stationary if
every additive time shift has the same law as the original process; this is the canonical project
notion `IsStationaryProcess`. -/
recall IsStationaryProcess

variable {I : Type u} [AddCommSemigroup I]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {E : Type w} [MeasurableSpace E]

-- Proof sketch: unfold the imported characterization `isStationaryProcess_iff`; the only
-- difference from the textbook formula is the order of the summands, and `add_comm` rewrites
-- `t + s` to `s + t`.
/-- The canonical stationary-process predicate is equivalent to the textbook formulation using the
shifted path `t ↦ X (t + s)`. -/
theorem isStationaryProcess_iff_right_shift (X : I → Ω → E) (μ : Measure Ω := by volume_tac) :
    IsStationaryProcess X μ ↔
      ∀ s : I, IdentDistrib (fun ω t ↦ X (t + s) ω) (fun ω t ↦ X t ω) μ μ := by
  constructor
  · intro h s
    simpa [add_comm] using h.identDistrib s
  · intro h s
    simpa [add_comm] using h s

/-! ### Exercise_20_1_1 (from Items/Chap20) -/
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
