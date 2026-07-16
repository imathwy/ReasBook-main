import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.3.8 lies in the Chapter 5 self-concordant-barrier / local-distance domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the
  canonical pointwise bridge from the barrier parameter inequality to the local
  gradient/local-norm estimate;
* `IsSelfConcordantOnWith.displacement_localNorm_upper_bound` in `Theorem_5_1_5`, the canonical
  Dikin-radius local-norm transport estimate;
* `gradient_difference_inner_ge_hessianLocalNorm_sq_div` in `Theorem_5_1_8`, the canonical
  lower bound for the gradient increment paired with the chord.

Best owner abstraction:
* source-facing: the textbook bound on the local norm of the chord `y - x`;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F` together with `‖y - x‖[F; x]`;
* bridge/view: the owner-level barrier-parameter square estimate at `x`, followed by the standard
  self-concordant local-norm comparison along the segment from `x` to `y`.

Primitive data:
* the barrier owner witness `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* points `x, y ∈ dom`;
* the source-facing nonnegativity hypothesis `0 ≤ ⟪∇ F(x), y - x⟫`.

Derived API:
* the local-distance bound `‖y - x‖[F; x] ≤ ν + 2 √ν`.

This theorem is an owner-level barrier estimate, so its public surface belongs in the barrier
namespace instead of as a parallel top-level theorem with the owner repeated in the binder list.
It uses only the Chapter 5 barrier/local-norm owner layer, so the ambient space assumption stays
at the canonical `[CompleteSpace E]` level rather than introducing a finite-dimensional bridge.
-/

-- Proof sketch: let `r := ‖y - x‖[F; x]`. If `r ≤ Real.sqrt ν`, the claim is immediate.
-- Otherwise choose an intermediate point `z = x + α • (y - x)` on the segment from `x` to `y`
-- with `α = Real.sqrt ν / r`, so the initial subsegment from `x` to `z` has `x`-local norm
-- exactly `√ν`. Since the barrier owner inherits an open convex standard-self-concordant domain,
-- both subsegments stay inside `dom`. Use the chapter's standard self-concordant segment
-- estimates on `x → z` to obtain a lower bound for the gradient increment, and combine that with
-- the barrier-parameter bound at `z` plus local-norm transport on `z → y` to control the
-- remaining pairing. The hypothesis `0 ≤ ⟪∇ F(x), y - x⟫` then lets one rearrange the resulting
-- scalar inequality to obtain `r ≤ ν + 2 * Real.sqrt ν`.
namespace IsSelfConcordantBarrierOnWith

section

variable {dom : Set E} {ν : NNReal} {F : E → ℝ}
variable {x y : E}

/-- Theorem 5.3.8: if `F` is a `ν`-self-concordant barrier on `dom` and the gradient pairing
`⟪∇ F(x), y - x⟫` is nonnegative, then the local norm of the chord `y - x` at `x` is bounded by
`ν + 2 √ν`. -/
theorem hessianLocalNorm_sub_le_barrierParameter_add_two_sqrt_of_gradient_inner_nonneg
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy_nonneg : inner ℝ (∇ F x) (y - x) ≥ 0) :
    ‖y - x‖[F; x] ≤ (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) := by
  sorry

end

end IsSelfConcordantBarrierOnWith

end
