import Mathlib
import Nesterov.Chap06.Assumption_6_2_1
import Nesterov.Chap06.Proposition_6_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin ConvexAnalysis Gradient StrongConvex

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Lemma 6.2.5 lies in the chapter's attained dual-objective / constrained-minimization domain.

Mandatory domain-style sampling before refinement:
- `smoothedDualObjectiveMinimand` and `smoothedDualObjective` in `Chap06/Proposition_6_25`, the
  chapter owners for the constrained `EReal` dual value and its primal slice;
- the canonical `argmin[Q₁]` owner surface for pointwise minimizer data;
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the more general
  chapter owner for the same dual-value construction;
- `StructuredObjectiveModel.adjointObjective_eq_of_isMinOn` in
  `Chap06/Text_6_1_2_Adjoint_Problem_Tractability_Caveat`, the attained-infimum bridge from the
  canonical owner to the textbook pointwise formula.

Best owner abstraction:
- source-facing: the unsmoothed dual objective from Lemma 6.2.5 and its selected minimizer
  surface;
- core/canonical: the zero-smoothing specialization
  `smoothedDualObjective A Q₁ hatf hatφ 0 0` together with
  `∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)`;
- bridge/view: the vector-gradient formula obtained from the dual-valued owner through the Hilbert
  space Riesz equivalence.

Primitive data:
- the dual-valued linear map `A : E₁ →L[ℝ] StrongDual ℝ E₂`;
- the feasible set `Q₁`;
- the functions `hatf` and `hatφ`;
- a pointwise minimizer witness in the canonical argmin surface
  `∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)`.

Derived API:
- the zero-smoothing dual owner `smoothedDualObjective A Q₁ hatf hatφ 0 0`;
- its effective-domain and gradient consequences below;
- the source-facing uniqueness, concavity, and Lipschitz-gradient statements of Lemma 6.2.5.

The previous version depended on a broken recall chain through `Definition_6_33` and used a
parallel selector wrapper that is not part of the available chapter API. This refinement keeps
only the actual zero-smoothing owners from `Proposition_6_25` together with the canonical
pointwise `argmin[Q₁]` surface.
-/

section OwnerLayer

/-- The minimizer of the zero-smoothing primal slice is unique when the primal smooth part
satisfies the chapter's source-facing strong-convexity owner `hatf ∈ 𝒮^0_σ(Q₁)`. -/
-- Proof sketch: `hhatf.strongConvexOn` gives the canonical owner `StrongConvexOn Q₁ σ hatf`,
-- which already includes convexity of `Q₁`; adding the affine term `x ↦ A x u` preserves
-- `σ`-strong convexity, and a strongly convex function has at most one minimizer.
theorem dualObjectiveMinimand_minimizer_unique
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    {u : E₂} {x y : E₁}
    (hx : IsMinOn (smoothedDualObjectiveMinimand A hatf 0 0 u) Q₁ x)
    (hy : IsMinOn (smoothedDualObjectiveMinimand A hatf 0 0 u) Q₁ y) :
    x = y := sorry

/- The source text states that `\hat φ` is concave, but with `φ = \tilde φ - \hat φ` and the
claimed concavity of `φ`, the sign-compatible assumption is that `\hat φ` is convex. The
statement skeleton below follows that sign convention. -/

/-- Lemma 6.2.5 (1): in owner form, if `\hat φ` is convex, then the finite real part of the
canonical zero-smoothing `EReal` dual objective is concave on its effective domain. -/
-- Proof sketch: `u ↦ (.mk Q₁ (smoothedDualObjectiveMinimand A hatf 0 0 u)).optimalValue` is the
-- infimum of affine functions of `u`, hence concave on the finite-value domain. The term
-- `-\hat φ` is concave because `\hat φ` is convex, so the sum remains concave.
theorem dualObjective_concave
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    (hhatφ_convex : ConvexOn ℝ Set.univ hatφ) :
    ConcaveOn ℝ (dom (smoothedDualObjective A Q₁ hatf hatφ 0 0))
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) := sorry

/-- The canonical zero-smoothing dual objective is finite everywhere, so its effective domain is
all of `E₂`. -/
-- Proof sketch: `smoothedDualObjective A Q₁ hatf hatφ 0 0` is defined by coercing a real-valued
-- expression into `EReal`, so every point lies in its effective domain.
theorem dualObjective_dom_eq_univ
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} :
    dom (smoothedDualObjective A Q₁ hatf hatφ 0 0) = Set.univ := sorry

end OwnerLayer

section GradientLayer

/-- Lemma 6.2.5 (2): under the same assumptions and differentiability of `\hat φ`, the
zero-smoothing dual objective has gradient
`-\nabla \hat φ(u) + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))` at every `u`, expressed on
the finite real part of the canonical `EReal` owner. -/
-- Proof sketch: `hhatf` supplies the chapter source-facing owner `hatf ∈ 𝒮^0_σ(Q₁)`, hence
-- uniqueness of the pointwise argmin selection, so Danskin's theorem identifies the gradient of
-- `\tilde φ` with the Riesz representative of `A (x₀ u)`. Subtract the gradient of the
-- differentiable term `\hat φ`.
theorem dualObjective_hasGradientAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (u : E₂) :
    HasGradientAt
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
      (-∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))) u := sorry

/-- Lemma 6.2.5 (3): in owner form, if `\hat φ` is differentiable and `∇ \hat φ` is Lipschitz with
constant `L₂(\hat φ)`, then the actual gradient of the finite real part of the canonical
zero-smoothing dual objective is Lipschitz with constant `(1 / σ) ‖A‖² + L₂(\hat φ)`. The
explicit vector-field formula remains the companion bridge theorem
`dualObjective_hasGradientAt`. -/
-- Proof sketch: `hhatφ_diff` supplies the primitive differentiability data needed for
-- `dualObjective_hasGradientAt` to identify the actual gradient field of
-- `extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)` with the explicit source-side
-- formula `u ↦ -∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))`. Then compare the
-- first-order optimality conditions at two dual points, using `hhatf.mu_pos` and
-- `hhatf.strongConvexOn` for the positive modulus and canonical strong-convexity view, to bound
-- the selected dual term, and finally combine that bound with the assumed Lipschitz estimate for
-- `∇ hatφ`.
theorem dualObjective_gradient_lipschitz
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {x₀ : E₂ → E₁}
    {σ : ℝ} {Lhatφ : NNReal}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hhatφ_lipschitz : LipschitzWith Lhatφ (∇ hatφ)) :
    LipschitzWith
      (Lhatφ + Real.toNNReal ((1 / σ) * ‖A‖ ^ (2 : ℕ)))
      (∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))) := sorry

end GradientLayer

end
