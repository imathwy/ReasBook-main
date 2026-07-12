import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_30
import LecturesConvexOptimization_Nesterov_2018.Chap06.Theorem_6_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ConditionalGradientContraction

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Lemma 6.17 lies in the Chapter 6 dual-selection / Hölder-gradient domain.

Sampled owner-style declarations:
- `smoothedPrimalObjectiveMaximand` in `Definition_6_30`, the chapter owner for dual objectives of
  the form `u ↦ (A x) u - g(u) - μ d(u)`;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the chapter owner for feasible
  maximizers of that dual maximand;
- `IsMaxRepresentationWithUniformlyConvexDualTerm` in `Definition_6_63`, the neighboring
  source-facing Chapter 6 owner that already records the same zero-smoothed geometry through
  `smoothedPrimalObjectiveArgmax`;
- `ConditionalGradientContraction.HolderGradientOn` in `Theorem_6_14`, the chapter owner for a
  chosen derivative field that is Hölder continuous on a feasible set.

Best owner abstraction:
- source-facing: Lemma 6.17's Hölder continuity statement for the gradient field attached to a
  maximizing selector `u`;
- core/canonical: the zero-smoothed argmax owner `smoothedPrimalObjectiveArgmax A Set.univ g 0 0`
  together with `ConditionalGradientContraction.HolderGradientOn` for the Hölder derivative
  field;
- bridge/view: the pointwise `fderiv` norm estimate below, recovered from the canonical owner
  using the assumed derivative identification `fderiv ℝ f x = A.flip (u x)`.

Primitive data:
- the dual pairing map `A`, the dual term `g`, the selector `u`, and the parameters `p`, `σg`;
- pointwise argmax membership of `u x` for the zero-smoothed chapter owner;
- differentiability of `g` through `gradg`;
- the `p`-uniform convexity inequality for `gradg`;
- the derivative identification `HasFDerivAt f (A.flip (u x)) x`.

Derived API:
- the canonical Hölder-gradient owner below;
- the source-facing pointwise derivative estimate.
-/

/-- Lemma 6.17 in the canonical Chapter 6 Hölder-gradient owner form: under the argmax-selection
and dual uniform-convexity hypotheses, the chosen derivative field `x ↦ A.flip (u x)`
defines `ConditionalGradientContraction.HolderGradientOn` on `Set.univ` with exponent
`v = 1 / (p - 1)` and constant `Gᵥ = (1 / σ_g)^v ‖A‖^(1 + v)`. -/
theorem holderGradientOn_of_argmax_selection_of_uniformly_convex_derivative
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {f : E₁ → ℝ} {g : E₂ → ℝ}
    {u : E₁ → E₂} {gradg : E₂ → StrongDual ℝ E₂} {p σg : ℝ}
    (hp : 2 ≤ p) (hσg : 0 < σg)
    (hu : ∀ x : E₁, u x ∈ smoothedPrimalObjectiveArgmax A Set.univ g 0 0 x)
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z)
    (huniform :
      ∀ u₁ u₂ : E₂,
        σg * Real.rpow ‖u₁ - u₂‖ p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂))
    (hf : ∀ x : E₁, HasFDerivAt f (A.flip (u x)) x) :
    HolderGradientOn
      (Real.toNNReal (1 / (p - 1)))
      (Real.toNNReal
        (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))))
      Set.univ f (fun x ↦ A.flip (u x)) := by
  sorry

-- Proof sketch: compare the first-order optimality conditions for the maximizers `u x₁` and
-- `u x₂`, use the assumed monotonicity inequality for `gradg` to bound `‖u x₁ - u x₂‖`, then
-- apply the operator-norm estimates for `A` and `A.flip` together with
-- `ContinuousLinearMap.opNorm_flip`, or equivalently reuse the canonical owner theorem above and
-- read off its pointwise Hölder bound.
/-- Lemma 6.17: if `u(x)` lies in the canonical argmax set of `u' ↦ A x u' - g(u')` for every
`x`, `g` has derivative selection `gradg` satisfying the uniform convexity inequality
`σ_g ‖u₁ - u₂‖^p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂)` with `p ≥ 2` and `σ_g > 0`, and `f` has
derivative `A.flip (u x)` at every `x` (the Lean form of `A^* u(x)`), then `∇f` is Hölder
continuous of order `v = 1 / (p - 1)` with constant
`Gᵥ = (1 / σ_g)^v ‖A‖^(1 + v)`. -/
theorem gradient_holder_of_argmax_selection_of_uniformly_convex_derivative
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {f : E₁ → ℝ} {g : E₂ → ℝ}
    {u : E₁ → E₂} {gradg : E₂ → StrongDual ℝ E₂} {p σg : ℝ}
    (hp : 2 ≤ p) (hσg : 0 < σg)
    (hu : ∀ x : E₁, u x ∈ smoothedPrimalObjectiveArgmax A Set.univ g 0 0 x)
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z)
    (huniform :
      ∀ u₁ u₂ : E₂,
        σg * Real.rpow ‖u₁ - u₂‖ p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂))
    (hf : ∀ x : E₁, HasFDerivAt f (A.flip (u x)) x) (x₁ x₂ : E₁) :
    ‖fderiv ℝ f x₁ - fderiv ℝ f x₂‖ ≤
      (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))) *
        Real.rpow ‖x₁ - x₂‖ (1 / (p - 1)) := sorry

end
