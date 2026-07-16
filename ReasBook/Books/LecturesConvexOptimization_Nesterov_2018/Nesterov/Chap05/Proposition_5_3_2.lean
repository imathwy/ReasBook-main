import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement

noncomputable section

universe u

/- This file lies in the Chapter 5 barrier-parameter / Newton-decrement domain.

Sampled owner declarations in this domain:
* `newtonDecrement` and `newtonDecrement_def` in `Definition_5_0_24`, the pointwise owner for the
  Newton decrement from local Hessian positivity and invertibility data;
* `NewtonDecrement.ofPosDefMem` and `NewtonDecrement.ofPosDefMem_def` in `Definition_5_0_24`, the
  positive-definite-Hessian domain bridge obtained from `x ∈ dom`;
* `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem` and
  `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` in `Definition_5_0_23`, the canonical
  way to derive the local Hessian data from domain hypotheses;
* `barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the local-norm-square
  companion reformulation of the same fixed-point inequality.

Best owner abstraction:
* source-facing: the fixed-point barrier inequality in all directions;
* core/canonical: the Chapter 5 Newton decrement owners `λ[F; x | hPos; hInv]` and `λ[F; x | hx]`;
* bridge/view: `newtonDecrement_def` and `NewtonDecrement.ofPosDefMem_def`, which rewrite those
  owner surfaces as the inverse-Hessian gradient pairing.

Primitive data:
* a function `F`, a point `x`, and a barrier parameter `ν`;
* the pointwise Hessian positivity and invertibility data at `x`.

Derived API:
* the pointwise Newton-decrement bound `λ[F; x | hPos; hInv] ≤ √ν`;
* the inverse-Hessian gradient pairing bound as a companion reformulation;
* the domain-level Newton-decrement bound `λ[F; x | hx] ≤ √ν`.

The public surface therefore states Proposition 5.3.2 first on the Chapter 5 pointwise owner
`λ[F; x | hPos; hInv]`, keeps the inverse-Hessian pairing only as a companion reformulation for
duality arguments, and reserves `λ[F; x | hx]` for the separate positive-definite-domain bridge. -/

section PointwiseOwner

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: complete the square with
-- `u - (hessian F x).inverse (∇ F x)` and then rewrite the maximizing value by
-- `newtonDecrement_def`, identifying it with the pointwise Newton decrement
-- `λ[F; x | hPos; hInv]`.
/-- Proposition 5.3.2, pointwise owner form: if the Hessian at `x` is positive and invertible,
then the barrier inequality from Definition 5.3.2 is equivalent to the Chapter 5 pointwise
Newton-decrement bound `λ[F; x | hPos; hInv] ≤ √ν`. -/
theorem barrier_parameter_bound_iff_newtonDecrement_le_sqrt
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      λ[F; x | hPos; hInv] ≤ Real.sqrt (ν : ℝ) := sorry

end PointwiseOwner

section PointwiseCompanion

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: complete the square with
-- `u - (hessian F x).inverse (∇ F x)` and use the positive / invertible Hessian supplied by the
-- pointwise hypotheses at `x` to identify the supremum of
-- `2 ⟪∇ F(x), u⟫ - ⟪∇² F(x)u, u⟫` with the inverse-Hessian pairing
-- `⟪∇ F(x), (∇² F(x))⁻¹ ∇ F(x)⟫`.
/-- Proposition 5.3.2, companion inverse-Hessian form: if the Hessian at `x` is positive and
invertible, then the barrier inequality from Definition 5.3.2 is equivalent to the
inverse-Hessian pairing bound `⟪∇ F(x), [∇² F(x)]⁻¹ ∇ F(x)⟫ ≤ ν`. -/
theorem barrier_parameter_bound_iff_gradient_inverse_hessian_gradient_le
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) ≤ (ν : ℝ) := sorry

end PointwiseCompanion

section NewtonDecrementBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

-- Proof sketch: apply the pointwise owner theorem
-- `barrier_parameter_bound_iff_newtonDecrement_le_sqrt` to the positive and invertible Hessian
-- witnesses canonically supplied by `HasPositiveDefiniteHessianOn dom F`, then identify the
-- resulting pointwise owner with the domain notation `λ[F; x | hx]`.
/-- Under the positive-definite-Hessian owner hypothesis, the domain-level bridge form of
the fixed-point barrier inequality is equivalently the owner-level Newton-decrement bound
`λ[F; x | hx] ≤ √ν`. -/
theorem barrier_parameter_bound_iff_newtonDecrement_ofPosDefMem_le_sqrt
    {dom : Set E} {F : E → ℝ} {ν : NNReal} [HasPositiveDefiniteHessianOn dom F] {x : E}
    (hx : x ∈ dom) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      λ[F; x | hx] ≤ Real.sqrt (ν : ℝ) := sorry

end NewtonDecrementBridge

end
