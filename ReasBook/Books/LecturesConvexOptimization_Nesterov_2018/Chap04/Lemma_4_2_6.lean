import LecturesConvexOptimization_Nesterov_2018.Chap02.Definition_2_17
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_2_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {σ2 L τ : ℝ} {f : E → ℝ} {xStar : E}

/- Lemma 4.2.6 lies in the first-order nondegeneracy / strong-convexity-smoothness domain on
real Hilbert spaces.

Sampled owner declarations:
* `IsStrongConvexSmoothObjective` in `Chap02/Definition_2_17`, the chapter owner for positive
  strong convexity together with the `C¹` and Lipschitz-gradient data making `∇ f` genuinely
  first-order;
* `IsStrongConvexSmoothObjective.contDiff`, the canonical source of pointwise
  `HasGradientAt f (∇ f x) x`;
* `IsStrongConvexSmoothObjective.mu_le_L`, the owner comparison theorem showing that on
  nontrivial spaces the smoothness parameter dominates the strong-convexity parameter;
* `firstOrderNondegeneracyCoefficient` in `Definition_4_2_15`, the Chapter 4 owner of the
  normalized gradient/displacement coefficient;
* `IsFirstOrderNondegenerate` in `Definition_4_2_15`, the source-facing owner obtained by
  forgetting the explicit threshold formulas and retaining only the positive lower bound.

Best owner abstraction:
* source-facing: the explicit existence of a scalar `τ` with the displayed threshold and strict
  improvement properties;
* core/canonical: `IsStrongConvexSmoothObjective σ₂ L f`;
* bridge/view: the coefficient `firstOrderNondegeneracyCoefficient f xStar x` and the owner class
  `IsFirstOrderNondegenerate f xStar`.

Primitive data:
* `σ2`, `L`, the objective `f`, and the chosen minimizer `xStar`;
* the source-facing class membership hypothesis `f ∈ 𝓢[σ₂, L]¹¹`;
* the global minimizer witness `IsMinOn f Set.univ xStar`.

Derived API:
* the existence of a positive lower bound `τ`;
* the explicit threshold `2 * sqrt q[σ₂, L] / (1 + q[σ₂, L]) ≤ τ`;
* under the primitive scalar assumptions `0 < σ₂` and `σ₂ < L`, the strict improvement
  `sqrt q[σ₂, L] < τ`;
* the pointwise coefficient bound through `firstOrderNondegeneracyCoefficient`;
* the first-order owner bridge `HasGradientAt f (∇ f x) x` obtained from the smooth owner.

This refinement keeps the lemma source-facing while moving its assumptions to the chapter owner
that already packages the intended first-order meaning of `∇ f`. The coefficient and
nondegeneracy owner remain the downstream bridge/view layer. -/

-- Proof sketch: use the interpolation inequality for a `σ₂`-strongly convex function with
-- `L`-Lipschitz gradient to show that, for every `x ≠ xStar`,
-- `⟪∇ f x, x - xStar⟫` is bounded below by
-- `(2 * sqrt (σ₂ * L) / (σ₂ + L)) * ‖∇ f x‖ * ‖x - xStar‖`. Dividing by the product of the
-- norms gives a uniform lower bound for the coefficient, and the same scalar expression rewrites
-- as `2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])`.
/-- Lemma 4.2.6 (1): if `f` lies in the strong-convex smooth class `𝓢^{1,1}_{σ₂,L}`, then
relative to any chosen global minimizer `xStar` there exists a uniform first-order
nondegeneracy lower bound `τ` whose size is at least the explicit threshold
`2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])`. -/
theorem exists_firstOrderNondegeneracyLowerBound_of_mem_S11
    (hf : f ∈ 𝓢[σ2, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar) :
    ∃ τ : ℝ,
      2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) ≤ τ ∧
        IsFirstOrderNondegeneracyLowerBound f xStar τ := sorry

-- Proof sketch: apply the scalar inequality `2 * sqrt γ / (1 + γ) > sqrt γ` with
-- `γ = q[σ₂, L]`. The primitive scalar assumptions `0 < σ₂` and `σ₂ < L` give
-- `0 < q[σ₂, L] < 1`, so any `τ` above the explicit threshold automatically satisfies
-- `sqrt q[σ₂, L] < τ`.
/-- Lemma 4.2.6 (2): if `0 < σ₂` and `σ₂ < L`, then every lower bound `τ` dominating the explicit
threshold `2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])` automatically satisfies the strict improvement
`sqrt q[σ₂, L] < τ`. -/
theorem sqrt_q_lt_of_firstOrderNondegeneracyThreshold_le
    (hσ2 : 0 < σ2)
    (hσL : σ2 < L)
    (hτ : 2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) ≤ τ) :
    Real.sqrt q[σ2, L] < τ := sorry

/-- A global minimizer of a strongly convex smooth objective is first-order nondegenerate as soon
as Lemma 4.2.6 supplies the explicit positive lower bound on the coefficient. -/
-- Proof sketch: extract `τ` from Lemma 4.2.6 (1), use the `C¹` component of
-- `IsStrongConvexSmoothObjective` to obtain `HasGradientAt f (∇ f x) x` away from `xStar`, and
-- package these data into `IsFirstOrderNondegenerate f xStar`.
theorem isFirstOrderNondegenerate_of_mem_S11
    (hf : f ∈ 𝓢[σ2, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar) :
    IsFirstOrderNondegenerate f xStar := sorry
