import Nesterov.Chap01.Definition_1_3_7
import Nesterov.Chap03.Definition_3_1_7
import Nesterov.Chap07.Definition_7_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

/- Theorem 7.1 lies in the chapter's sublinear / asphericity domain.

Sampled owner-style declarations:
- project `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`
- project `SatisfiesAsphericityCondition` in `Definition_7_7`
- project
  `isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous`
  in `Chap03/Proposition_3_19`
- project `StrongConvexOn.norm_sub_le_two_mul_lipschitzOnWith_div_of_isMinOn_of_mem`
  in `Chap03/Proposition_3_41`

Best owner abstraction:
- source-facing: the consequences of the Chapter 7 asphericity sandwich for a convex positively
  homogeneous function
- core/canonical: `SatisfiesAsphericityCondition`
- bridge/view: the Chapter 3 max formula over `∂f(0)`, the Chapter 3 minimizer-distance owner,
  and, only for the sharper final clause, the explicit pullback of an inner-product norm along a
  linear isomorphism `A : E ≃ₗ[ℝ] F`

Primitive data:
- a real normed space `E`
- a seminorm `p : Seminorm ℝ E`
- a convex function `f : E → ℝ`
- the Chapter 3 positive-homogeneity owner `IsPositivelyHomogeneousOn 1 Set.univ f`
- radii `γ₀ ≤ γ₁` encoded canonically by `SatisfiesAsphericityCondition f p γ₀ γ₁`
- for the optimization companions: a set `Q₁`, a feasible `p`-minimizer `x₀ ∈ Q₁`, and a
  feasible `f`-minimizer `xStar ∈ Q₁`

Derived API:
- the pointwise comparison between `f` and `p`
- the `γ₁`-Lipschitz estimate for `f` with respect to `p`
- the optimal-value chain on `(.mk Q₁ f : SetConstrainedMinimizationProblem E)`, with the
  canonical lower factor `γ₀ / γ₁`
- the distance bounds between a `p`-minimizer and an `f`-minimizer
- the sharper factor-`1` distance estimate obtained separately when `p` is pulled back from an
  actual inner-product norm

Source/core/bridge triage:
- source-facing: the generic consequences of the asphericity sandwich
- core/canonical: `SatisfiesAsphericityCondition`
- bridge/view: the Chapter 3 max formula, the Chapter 3 minimizer-distance owner, and the
  separate inner-product pullback realization used for the sharper last bound

This file keeps the source-facing theorem family on the chapter's canonical asphericity owner.
The pointwise and Lipschitz consequences are organized around the existing Chapter 3
subdifferential/max-formula owner, and the distance estimate is aligned with the existing Chapter 3
minimizer-distance owner rather than introducing a parallel local comparison package. The generic
bounds are stated directly for the source-facing asphericity sandwich on a seminorm, while the
final sharper estimate is stated separately under the explicit inner-product pullback bridge
already exemplified by Lemma 7.1.
-/

section AsphericityConsequences

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} {f : E → ℝ} {γ₀ γ₁ : ℝ}

section

-- Proof sketch: apply the lower and upper dual-ball inclusions from
-- `h_asphericity` to the affine supports of the convex positively homogeneous function `f` at
-- the origin, then evaluate the resulting support inequalities at `x`.
/-- Theorem 7.1 (1): the asphericity sandwich implies the pointwise comparison
`γ₀ * p x ≤ f x ≤ γ₁ * p x`. -/
theorem SatisfiesAsphericityCondition.pointwise_bounds
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x : E) :
    γ₀ * p x ≤ f x ∧ f x ≤ γ₁ * p x := sorry

-- Proof sketch: combine the upper bound from `pointwise_bounds` with convexity and positive
-- homogeneity to control the increment `f x - f y` by the seminorm of `x - y`, then symmetrize.
/-- Theorem 7.1 (2): the asphericity sandwich implies the `γ₁`-Lipschitz estimate for `f` with
respect to `p`. -/
theorem SatisfiesAsphericityCondition.lipschitz
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x y : E) :
    |f x - f y| ≤ γ₁ * p (x - y) := sorry

-- Proof sketch: use the lower pointwise bound from `pointwise_bounds` together with the
-- `p`-minimality of the feasible point `x₀ ∈ Q₁` to compare every `f x` on `Q₁` to `f x₀`, and
-- then pass to the Chapter 1 owner optimal value.
/-- Theorem 7.1 (3): if `x₀` minimizes `p` on `Q₁`, then the asphericity sandwich yields the
lower optimal-value estimate
`((γ₀ / γ₁) * f x₀ : EReal) ≤ (.mk Q₁ f : SetConstrainedMinimizationProblem E).optimalValue`. -/
theorem SatisfiesAsphericityCondition.optimal_value_lower_bound
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ : E} (hx₀ : x₀ ∈ Q₁) (hx₀_min : IsMinOn p Q₁ x₀) :
    ((γ₀ / γ₁) * f x₀ : EReal) ≤ (.mk Q₁ f : SetConstrainedMinimizationProblem E).optimalValue :=
  sorry

/- Theorem 7.1 (4): every feasible point `x₀ ∈ Q₁` gives the standard Chapter 1 upper bound on
the constrained optimal value attached to `f` on `Q₁`; this is exactly
`SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet`. -/
recall SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet

-- Proof sketch: take the upper half of `pointwise_bounds` at the chosen point `x`.
/-- Theorem 7.1 (5): the upper half of the asphericity sandwich gives the pointwise estimate
`f x ≤ γ₁ * p x`, hence in particular at a `p`-minimizer. -/
theorem SatisfiesAsphericityCondition.pointwise_upper_bound
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x : E) :
    f x ≤ γ₁ * p x := sorry

-- Proof sketch: compare the minimizing points `x₀` and `xStar` through the convex positively
-- homogeneous estimates from `pointwise_bounds`, then combine the lower and upper comparisons in
-- the textbook way.
/-- Theorem 7.1 (6): any minimizer `xStar` of `f` on `Q₁` lies within `p`-distance at most
`(2 / γ₀) * f xStar` from a feasible `p`-minimizer `x₀ ∈ Q₁`, and the optimal values satisfy the
correctly oriented comparison `(2 / γ₁) * f x₀ ≤ (2 / γ₀) * f xStar`. -/
theorem SatisfiesAsphericityCondition.optimal_solution_distance
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ xStar : E}
    (hx₀ : x₀ ∈ Q₁) (hx₀_min : IsMinOn p Q₁ x₀)
    (hxStar : xStar ∈ Q₁) (hxStar_min : IsMinOn f Q₁ xStar) :
    p (x₀ - xStar) ≤ (2 / γ₀) * f xStar ∧
      (2 / γ₁) * f x₀ ≤ (2 / γ₀) * f xStar := sorry

end

end AsphericityConsequences

section InnerProductPullback

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} {f : E → ℝ} {γ₀ γ₁ : ℝ}

section

-- Proof sketch: transport the `p`-minimizer `x₀` along the linear isomorphism `A` to a projection
-- point of `0` onto the convex image `A '' Q₁`, apply the Hilbert-space projection geometry from
-- `IsProjectionPointOn.pythagorean_ineq`, and then pull the resulting norm estimate back through
-- `hp_inner`.
/-- Theorem 7.1 (7): when `p` is the pullback of the norm on a real inner-product space along a
linear isomorphism `A`, the distance factor improves from `2` to `1`, and the optimal values
satisfy `(1 / γ₁) * f x₀ ≤ (1 / γ₀) * f xStar`. -/
theorem SatisfiesAsphericityCondition.optimal_solution_distance_of_inner_product
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ xStar : E} {F : Type v}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (hQ₁_convex : Convex ℝ Q₁)
    (hx₀ : x₀ ∈ Q₁) (hx₀_min : IsMinOn p Q₁ x₀)
    (hxStar : xStar ∈ Q₁) (hxStar_min : IsMinOn f Q₁ xStar)
    (A : E ≃ₗ[ℝ] F)
    (hp_inner : ∀ x : E, p x = ‖A x‖) :
    p (x₀ - xStar) ≤ (1 / γ₀) * f xStar ∧
      (1 / γ₁) * f x₀ ≤ (1 / γ₀) * f xStar := sorry

end

end InnerProductPullback

end
