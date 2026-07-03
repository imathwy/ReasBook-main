import Mathlib
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_1_5 (from Chap04) -/
open scoped InnerProduct MinimalSingularValue
open scoped ConstrainedArgmin

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

/-
Proposition 4.1.5 lies in nonlinear least squares on real inner-product spaces.

Relevant owner declarations sampled before refinement:
* `GradientDominatedOn` and `GradientDominatedOn.UsesConstant` in `Definition_4_1_9`, the chapter
  owners for gradient domination on a feasible set;
* `gradientWithin` and `UniqueDiffOn`, the canonical constrained first-order owner layer used by
  `GradientDominatedOn`;
* `minimalSingularValue` with source-facing notation `σ_min` in `Definition_4_4_5`, the chapter
  owner for Jacobian nondegeneracy;
* the canonical adjoint-side positivity condition `0 < σ_min((fderivWithin ℝ g 𝓕 x)†)` built from
  the same singular-value owner and the adjoint owner `A†`.

Best owner abstraction:
* source-facing: the half squared-residual objective together with a positive uniform lower bound
  on `J(x) J(x)^*`;
* core/canonical: `GradientDominatedOn 2 𝓕`, `gradientWithin`, and the Jacobian owner
  `σ_min((fderivWithin ℝ g 𝓕 x)†)`;
* bridge/view: the fixed-root witness `xStar` and the textbook constant `(2 * σ)⁻¹`.

Primitive data:
* the residual map `g : E → F`;
* the feasible set `𝓕`;
* a unique-differentiability hypothesis on `𝓕`, making `gradientWithin` intrinsic;
* a root `xStar ∈ 𝓕` of `g`;
* the positive constant `σ`.

Derived API:
* the half squared-residual objective `x ↦ (1 / 2) * ‖g x‖²`;
* the owner witness `GradientDominatedOn 2 𝓕 ...`;
* the source-facing constant witness
  `GradientDominatedOn.UsesConstant 2 𝓕 fLS xStar (1 / (2 * σ))`;
* the companion squared constrained-gradient inequality.
-/

section

variable (g : E → F)

local notation "fLS" =>
  fun x : E ↦ (1 / 2 : ℝ) * ‖g x‖ ^ (2 : ℕ)

local notation "withinJacobianMinSq" =>
  fun (𝓕 : Set E) (x : E) ↦ (σ_min((fderivWithin ℝ g 𝓕 x)†)) ^ (2 : ℕ)

section

variable (𝓕 : Set E) (xStar : E) (σ : ℝ)
variable (h𝓕_unique : UniqueDiffOn ℝ 𝓕)
variable (hg : DifferentiableOn ℝ g 𝓕) (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
variable (hσ_pos : 0 < σ)
variable (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x)

/-- Helper for Proposition 4.1.5: a feasible root of `g` minimizes the half squared residual on
`𝓕`. -/
lemma root_mem_argmin_half_residual_sq
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0) :
    xStar ∈ argmin[𝓕] fLS := by
  rw [mem_constrainedArgmin_iff]
  constructor
  · exact hxStar
  · -- At the root, the objective is zero, and the half squared norm is everywhere nonnegative.
    intro y hy
    have hy_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖g y‖ ^ (2 : ℕ) := by
      positivity
    change (1 / 2 : ℝ) * ‖g xStar‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * ‖g y‖ ^ (2 : ℕ)
    simpa [hgstar] using hy_nonneg

/-- Helper for Proposition 4.1.5: on the feasible set, the constrained gradient of the half
squared residual is the adjoint Jacobian applied to the residual. -/
lemma gradientWithin_half_residual_sq_eq_adjoint_apply
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    {x : E} (hx : x ∈ 𝓕) :
    gradientWithin fLS 𝓕 x =
      (ContinuousLinearMap.adjoint (fderivWithin ℝ g 𝓕 x)) (g x) := by
  -- Differentiate the squared norm and scale by `1 / 2`.
  have hderiv :
      HasFDerivWithinAt fLS
        ((1 / 2 : ℝ) •
          (2 • (innerSL ℝ (g x)).comp (fderivWithin ℝ g 𝓕 x))) 𝓕 x := by
    change HasFDerivWithinAt (fun y : E ↦ (1 / 2 : ℝ) * ‖g y‖ ^ (2 : ℕ))
      ((1 / 2 : ℝ) • (2 • (innerSL ℝ (g x)).comp (fderivWithin ℝ g 𝓕 x))) 𝓕 x
    exact (hg x hx).hasFDerivWithinAt.norm_sq.const_mul (1 / 2 : ℝ)
  have hfderiv :
      fderivWithin ℝ fLS 𝓕 x =
        ((1 / 2 : ℝ) •
          (2 • (innerSL ℝ (g x)).comp (fderivWithin ℝ g 𝓕 x))) := by
    exact hderiv.fderivWithin (h𝓕_unique x hx)
  -- Rewrite the Fréchet derivative through the adjoint and convert it back to a gradient.
  calc
    gradientWithin fLS 𝓕 x
        = (InnerProductSpace.toDual ℝ E).symm
            (((1 / 2 : ℝ) •
              (2 • (innerSL ℝ (g x)).comp (fderivWithin ℝ g 𝓕 x)))) := by
          simpa [gradientWithin] using congrArg ((InnerProductSpace.toDual ℝ E).symm) hfderiv
    _ = (InnerProductSpace.toDual ℝ E).symm
          (InnerProductSpace.toDual ℝ E
            ((ContinuousLinearMap.adjoint (fderivWithin ℝ g 𝓕 x)) (g x))) := by
          apply (InnerProductSpace.toDual ℝ E).injective
          rw [LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.innerSL_apply_comp]
          ext y
          simp [InnerProductSpace.toDual_apply_apply]
    _ = (ContinuousLinearMap.adjoint (fderivWithin ℝ g 𝓕 x)) (g x) := by
          simp

/-- Helper for Proposition 4.1.5: the defining infimum of the least singular value yields the
squared norm lower bound for every vector. -/
lemma minimalSingularValue_sq_mul_norm_sq_le_norm_sq
    (B : F →L[ℝ] E) (y : F) :
    (σ_min(B)) ^ (2 : ℕ) * ‖y‖ ^ (2 : ℕ) ≤ ‖B y‖ ^ (2 : ℕ) := by
  -- First recover the standard unsquared lower bound from the infimum definition.
  have hmul : σ_min(B) * ‖y‖ ≤ ‖B y‖ := by
    by_cases hy : y = 0
    · simp [hy]
    · have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hσy : σ_min(B) ≤ ‖B y‖ / ‖y‖ := by
        rw [minimalSingularValue_def]
        refine csInf_le ?_ ?_
        · refine ⟨0, ?_⟩
          rintro _ ⟨z, rfl⟩
          exact div_nonneg (norm_nonneg _) (norm_nonneg _)
        · exact ⟨⟨y, hy⟩, rfl⟩
      exact (le_div_iff₀ hy_norm).1 hσy
  have hsq : (σ_min(B) * ‖y‖) ^ (2 : ℕ) ≤ ‖B y‖ ^ (2 : ℕ) := by
    have hleft_nonneg : 0 ≤ σ_min(B) * ‖y‖ := by
      exact mul_nonneg (minimalSingularValue_nonneg B) (norm_nonneg _)
    have hright_nonneg : 0 ≤ ‖B y‖ := norm_nonneg _
    nlinarith
  -- Expand the square of the product into the stated form.
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq

/-- Helper for Proposition 4.1.5: the half squared residual satisfies the explicit degree-two
gradient-domination bound at the given root with constant `(2 * σ)⁻¹`. -/
lemma half_residual_sq_usesConstant_at_root
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
    (hσ_pos : 0 < σ)
    (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x) :
    GradientDominatedOn.UsesConstant 2 𝓕 fLS xStar (1 / (2 * σ)) := by
  refine ⟨h𝓕_unique,
    root_mem_argmin_half_residual_sq (g := g) (𝓕 := 𝓕) (xStar := xStar) hxStar hgstar,
    by positivity, ?_⟩
  intro x hx
  have hxStar_zero : fLS xStar = 0 := by
    change (1 / 2 : ℝ) * ‖g xStar‖ ^ (2 : ℕ) = 0
    simp [hgstar]
  have hgrad :
      gradientWithin fLS 𝓕 x =
        (ContinuousLinearMap.adjoint (fderivWithin ℝ g 𝓕 x)) (g x) := by
    simpa using gradientWithin_half_residual_sq_eq_adjoint_apply
      (g := g) (𝓕 := 𝓕) h𝓕_unique hg hx
  have hsq :
      (σ_min((fderivWithin ℝ g 𝓕 x)†)) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) ≤
        ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
    simpa [← hgrad] using
      minimalSingularValue_sq_mul_norm_sq_le_norm_sq
        (B := (fderivWithin ℝ g 𝓕 x)†) (y := g x)
  have hσnorm : σ * ‖g x‖ ^ (2 : ℕ) ≤ ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
    have hnorm_nonneg : 0 ≤ ‖g x‖ ^ (2 : ℕ) := by
      positivity
    nlinarith [hσ hx, hsq]
  have hgap_sq :
      fLS x - fLS xStar ≤ (1 / (2 * σ)) * ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
    -- Rewrite the objective gap as `(1 / (2 * σ)) * (σ * ‖g x‖²)` and use `hσnorm`.
    have hscale : ((1 / (2 * σ) : ℝ) * σ) = 1 / 2 := by
      field_simp [ne_of_gt hσ_pos]
    calc
      fLS x - fLS xStar = (1 / (2 : ℝ)) * ‖g x‖ ^ (2 : ℕ) := by
        rw [hxStar_zero]
        ring
      _ = ((1 / (2 * σ) : ℝ) * σ) * ‖g x‖ ^ (2 : ℕ) := by
        rw [hscale]
      _ = (1 / (2 * σ) : ℝ) * (σ * ‖g x‖ ^ (2 : ℕ)) := by
        ring
      _ ≤ (1 / (2 * σ) : ℝ) * ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hσnorm (by positivity)
  -- Convert the degree-two `Real.rpow` term back to an ordinary square.
  simpa [Real.rpow_natCast] using hgap_sq

/-- Proposition 4.1.5: if `g : E → F` is differentiable on the uniquely differentiable feasible
set `𝓕`, `xStar ∈ 𝓕` is a root of `g`, and `σ > 0` is a uniform lower bound on the least
eigenvalue of `J(x) J(x)^*`, recorded canonically as the inequality
`σ ≤ σ_min((fderivWithin ℝ g 𝓕 x)†)^2` for every `x ∈ 𝓕`, then the nonlinear
least-squares objective `x ↦ (1 / 2) ‖g x‖²` is gradient dominated of degree `2` on `𝓕`. -/
-- Proof sketch: the root hypothesis makes `xStar` a minimizer of the half squared-residual
-- objective. The uniform bound on `σ_min((fderivWithin ℝ g 𝓕 x)†)^2` is the
-- canonical constrained nondegeneracy input controlling the objective gap by `(2 * σ)⁻¹` times
-- the squared
-- constrained-gradient norm, which packages exactly into `GradientDominatedOn 2 𝓕 fLS`.
theorem nonlinearLeastSquares_gradientDominatedOn_two
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
    (hσ_pos : 0 < σ)
    (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x)
    : GradientDominatedOn 2 𝓕 fLS := by
  refine ⟨?_, ?_, ?_⟩
  · -- The objective is a constant multiple of the squared residual norm.
    change DifferentiableOn ℝ (fun x : E ↦ (1 / 2 : ℝ) * ‖g x‖ ^ (2 : ℕ)) 𝓕
    have hnormsq : DifferentiableOn ℝ (fun x : E ↦ ‖g x‖ ^ (2 : ℕ)) 𝓕 := by
      exact DifferentiableOn.norm_sq (𝕜 := ℝ) hg
    exact hnormsq.const_mul (1 / 2 : ℝ)
  · exact ⟨by norm_num, by norm_num⟩
  · -- Package the explicit minimizer and constant from the source proof.
    exact ⟨xStar, 1 / (2 * σ),
      half_residual_sq_usesConstant_at_root
        (g := g) (𝓕 := 𝓕) (xStar := xStar) (σ := σ)
        h𝓕_unique hg hxStar hgstar hσ_pos hσ⟩

/-- The owner from Proposition 4.1.5 is witnessed at the given root by the textbook constant
`(2 * σ)⁻¹`. -/
-- Proof sketch: apply `nonlinearLeastSquares_gradientDominatedOn_two` and use the given root
-- `xStar` as the minimizer witness in the canonical `UsesConstant` package.
theorem nonlinearLeastSquares_gradientDominatedOn_two_usesConstant
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
    (hσ_pos : 0 < σ)
    (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x)
    :
    GradientDominatedOn.UsesConstant 2 𝓕 fLS xStar (1 / (2 * σ)) := by
  -- Reuse the explicit witness constructed from the root and the singular-value bound.
  exact half_residual_sq_usesConstant_at_root
    (g := g) (𝓕 := 𝓕) (xStar := xStar) (σ := σ)
    h𝓕_unique hg hxStar hgstar hσ_pos hσ

/-- Companion squared-norm form of Proposition 4.1.5's constrained gradient-domination
inequality. -/
-- Proof sketch: apply `nonlinearLeastSquares_gradientDominatedOn_two_usesConstant` and rewrite
-- the degree-two `Real.rpow` term as `‖gradientWithin fLS 𝓕 x‖ ^ 2`.
theorem nonlinearLeastSquares_sub_le_inv_two_mul_norm_gradient_sq
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
    (hσ_pos : 0 < σ)
    (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x)
    {x : E} (hx : x ∈ 𝓕) :
    fLS x - fLS xStar ≤ (1 / (2 * σ)) * ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
  -- Apply the packaged degree-two bound and rewrite `Real.rpow` as an ordinary square.
  simpa [Real.rpow_natCast] using
    (nonlinearLeastSquares_gradientDominatedOn_two_usesConstant
      (g := g) (𝓕 := 𝓕) (xStar := xStar) (σ := σ)
      h𝓕_unique hg hxStar hgstar hσ_pos hσ).bound hx

end

end

/-! ### Theorem_4_1_5_1 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open HasGloballyNondegenerateOptimalSet (UsesConstant)

/- Theorem 4.1.5.1 lies in the chapter's star-convex cubic-regularization rate domain.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the source-facing owner of the iterate and
  regularization schedule;
* `StarConvexWithRespectToOn` in `Theorem_4_1_4`, the chapter owner for fixed-center
  star-convexity on a feasible set;
* `HasGloballyNondegenerateOptimalSet.UsesConstant` in `Definition_4_1_8`, the canonical owner
  packaging the chosen minimizer `xStar`, the positive constant `μ`, and the quadratic growth
  bound;
* `starConvex_cubicSegment_gap_le_inverse_square_rate` in `Theorem_4_1_4`, the earlier
  star-convex first-phase rate result on the same fixed-center owner pattern.

Best owner abstraction:
* source-facing: the first-phase decay and termination estimates for a
  `CubicRegularizationMethod`;
* core/canonical: `CubicRegularizationMethod`, `StarConvexWithRespectToOn`, and
  `HasGloballyNondegenerateOptimalSet.UsesConstant`;
* bridge/view: the scalar threshold `starConvexNondegenerateBarOmega`, kept only as a short,
  high-reuse name for the textbook quantity `μ^3 / (8 L^2)`.

Primitive data:
* the objective `f`;
* the cubic-regularization method `method`;
* the fixed star center `xStar`;
* the nondegeneracy constant `μ`;
* the fixed-center star-convex witness `hstar`;
* the canonical witness `hnondegenerate :
  HasGloballyNondegenerateOptimalSet.UsesConstant Set.univ f xStar μ`.

Derived API:
* the threshold `\barω = μ^3 / (8 L^2)`;
* the gap function `Δ k = f (x_k) - f xStar`;
* the first-phase decay theorem and the termination theorem below.

The theorem is kept on the fixed-center owner layer rather than being collapsed to
`StarConvexFunction`, because the source uses the same distinguished minimizer `xStar` both as the
star center and as the minimizer singled out by the nondegeneracy witness. -/

/-- The scale `\barω = μ^3 / (8 L^2)` attached to the global non-degeneracy constant `μ` and the
cubic-regularization parameter bound `L` in the star-convex first-phase estimate. -/
def starConvexNondegenerateBarOmega
    (L μ : ℝ) : ℝ :=
  μ ^ (3 : ℕ) / (8 * L ^ (2 : ℕ))

-- Proof sketch: use the acceptance inequality of the regularized Newton scheme together with the
-- parameter bound `M_k ≤ 2L` to derive the one-step gap recurrence from the cubic model estimate.
-- Apply star-convexity at the optimal point `xStar`, use the global non-degeneracy error bound
-- with parameter `μ` to rewrite the recurrence in terms of
-- `\barω = starConvexNondegenerateBarOmega L μ`, and iterate the scalar first-phase estimate on
-- the regime `f(x_k) - f(xStar) ≥ (4 / 9) \barω`. Since the objective gaps along a
-- `CubicRegularizationMethod` are monotone nonincreasing, any index `k` in that regime
-- automatically forces `Δ 0` into the same regime, so no separate initial-gap hypothesis is
-- primitive. The same scalar recurrence yields an index where the first phase terminates, while
-- the complementary case `Δ 0 ≤ (4 / 9) \barω` terminates immediately at `k₀ = 0`.
namespace CubicRegularizationMethod

section StarConvexCubicRegularizationFirstPhase

variable (f : E → ℝ) {stepMap : ℝ → E → E} {L0 L : ℝ} {x0 : E}
variable (xStar : E) (μ : ℝ)
variable (method : CubicRegularizationMethod f stepMap L0 L x0)
variable
  (hstar : StarConvexWithRespectToOn f xStar Set.univ)
  (hnondegenerate : UsesConstant Set.univ f xStar μ)

local notation "ω̄" => starConvexNondegenerateBarOmega L μ
local notation "Δ" => fun k : ℕ ↦ f (method k) - f xStar

/-- Theorem 4.1.5.1 (1): if `f` is star-convex with center `xStar`, `xStar` is a global
minimizer, the canonical nondegeneracy witness
`HasGloballyNondegenerateOptimalSet.UsesConstant Set.univ f xStar μ` packages the matching
quadratic growth bound, and the iterates are generated by the cubic-regularized Newton scheme
`(4.1.16)`, then every iterate that remains in the first phase satisfies the fourth-root decay
bound with `\barω = μ^3 / (8 L^2)`. -/
theorem starConvex_firstPhase_gap_bound
    (k : ℕ)
    (hk : Δ k ≥ (4 / 9 : ℝ) * ω̄) :
    Δ k ≤
      (Real.rpow (Δ 0) (1 / 4 : ℝ) -
        ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̄ (1 / 4 : ℝ)) ^
        (4 : ℕ) := sorry

-- Proof sketch: if `Δ 0 ≤ (4 / 9) \barω`, take `k₀ = 0`. Otherwise apply the same scalar
-- first-phase recurrence as in `starConvex_firstPhase_gap_bound` to the normalized gaps
-- `Δ_k = (f (x_k) - f xStar) / \barω`. This recurrence cannot stay forever in the regime
-- `Δ_k > 4 / 9`, so some iterate must cross the threshold.
/-- Theorem 4.1.5.1 (2): under the same star-convex cubic-regularization hypotheses, the first
phase ends at some index `k₀` where `f (x_{k₀}) - f(x*) ≤ (4 / 9) \barω`. -/
theorem starConvex_firstPhase_terminates :
    ∃ k0 : ℕ,
      Δ k0 ≤ (4 / 9 : ℝ) * ω̄ := sorry

end StarConvexCubicRegularizationFirstPhase
end CubicRegularizationMethod

/-! ### Theorem_4_1_5_2 (from Chap04) -/
open scoped ConstrainedArgmin

noncomputable section

universe u

/- Theorem 4.1.5.2 lies in the chapter's star-convex cubic-regularization rate domain.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the chapter owner for the iterate sequence
  and regularization schedule;
* `starConvexNondegenerateBarOmega` in `Theorem_4_1_5_1`, the chapter owner for the scale
  `\barω`;
* `CubicRegularizationMethod.starConvex_firstPhase_gap_bound` in `Theorem_4_1_5_1`, the
  preceding first-phase theorem on the same owner data;
* `HasGloballyNondegenerateOptimalSet.UsesConstant` in `Definition_4_1_8`, the chapter owner for
  the chosen minimizer, positive nondegeneracy constant, and quadratic growth bound;
* `nonlinearTransformation_cubicRegularization_secondPhase_gap_le_superlinear` in
  `Theorem_4_1_9`, the parallel second-phase statement in the transformed strongly convex model.

Source/core/bridge triage:
* source-facing: the second-phase superlinear gap estimate after the threshold
  `(4 / 9) * starConvexNondegenerateBarOmega L μ` is reached;
* core/canonical: `CubicRegularizationMethod`, `StarConvexWithRespectToOn`,
  `HasGloballyNondegenerateOptimalSet.UsesConstant`, and `starConvexNondegenerateBarOmega`;
* bridge/view: none beyond the direct use of those owners.

Primitive data:
* an objective `f`;
* a cubic-regularization method `method`;
* a fixed star center `xStar`;
* the non-degeneracy parameter `μ`;
* the canonical witness
  `HasGloballyNondegenerateOptimalSet.UsesConstant Set.univ f xStar μ`;
* the threshold index `k0`.

Derived API:
* the superlinear one-step gap recurrence for all `k ≥ k0`.

The preceding first-phase theorem already lives on the intrinsic complete real inner-product-space
layer, so keeping this second-phase theorem on `EuclideanSpace ℝ (Fin n)` would only duplicate the
same mathematics in a more concrete model. This refinement therefore reuses the existing owner
abstractions directly and removes that unnecessary ambient specialization. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section StarConvexCubicRegularizationSecondPhase

variable (f : E → ℝ)
variable {stepMap : ℝ → E → E} {L0 L : ℝ} {x0 : E}
variable (xStar : E) (μ : ℝ)
variable
  (method :
    CubicRegularizationMethod
      f
      stepMap
      L0 L x0)

local notation "ω̄" => starConvexNondegenerateBarOmega L μ
local notation "Δ" => fun k : ℕ ↦ f (method k) - f xStar

-- Proof sketch: apply the one-step cubic-regularization descent estimate from the first-phase
-- analysis to the normalized gaps
-- `Δ_k = (f (x_k) - f xStar) / starConvexNondegenerateBarOmega L μ`. The canonical witness
-- `HasGloballyNondegenerateOptimalSet.UsesConstant Set.univ f xStar μ` supplies the matching
-- minimizer, positivity, and quadratic growth data, turning the distance term into `Δ_k^(3/2)`,
-- and once
-- `Δ_k ≤ 4 / 9` the minimizer of the scalar upper bound on `[0, 1]` is attained at `α = 1`,
-- yielding `Δ_{k+1} ≤ (1 / 2) Δ_k^(3/2)`. Rewriting this inequality gives the displayed
-- superlinear estimate for every `k ≥ k0`.
/-- Theorem 4.1.5.2: if `f` is star-convex with center `xStar`, the canonical witness
`HasGloballyNondegenerateOptimalSet.UsesConstant Set.univ f xStar μ` packages the matching
global minimizer and quadratic growth bound, and the iterates are generated by the
cubic-regularized Newton scheme `(4.1.16)`, then once
`f (x_{k0}) - f(x*) ≤ (4 / 9) * \barω`, every later iterate satisfies the superlinear estimate
`f (x_{k+1}) - f(x*) ≤ (1 / 2) * (f (x_k) - f(x*)) * sqrt ((f (x_k) - f(x*)) / \barω)`, where
`\barω = μ^3 / (8 L^2)`. -/
theorem starConvex_cubicRegularization_secondPhase_gap_le_superlinear
    (hstar : StarConvexWithRespectToOn f xStar Set.univ)
    (hnondegenerate :
      HasGloballyNondegenerateOptimalSet.UsesConstant Set.univ f xStar μ)
    (k0 : ℕ)
    (hk0 :
      Δ k0 ≤ (4 / 9 : ℝ) * ω̄)
    (k : ℕ)
    (hk : k0 ≤ k) :
    Δ (k + 1) ≤
      (1 / 2 : ℝ) * Δ k * Real.sqrt (Δ k / ω̄) := sorry

end StarConvexCubicRegularizationSecondPhase

/-! ### Definition_4_1_6 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 4.1.6 lies in the cubic-regularization / Hessian-spectrum domain on finite-dimensional
real inner-product spaces.

Sampled owner declarations:
* `hessian` and `hessianMatrix` in `Chap01/Definition_1_4_16`, the intrinsic Hessian owner and
  its Euclidean matrix bridge;
* `spectrum ℝ T`, the canonical spectral owner for a real endomorphism or matrix;
* `ContinuousLinearMap.spectrum_eq` and `Matrix.spectrum_toLpLin`, the canonical bridges between
  the intrinsic Hessian operator and its standard-basis matrix realization.

Best owner abstraction:
* source-facing: the cubic-regularization decrement `δ_k`;
* core/canonical: `‖∇ f x‖` together with `sInf (spectrum ℝ (hessian f x))`;
* bridge/view: the matrix shorthands `λ_min(H)`, `λ_max(H)`, and the Euclidean Hessian-matrix
  spectral formula below.

Primitive data:
* the ambient finite-dimensional real inner-product space `E`;
* an objective `f : E → ℝ`;
* a point `x` or iterate `xk`;
* a scalar `L`.

Derived API:
* the thin matrix-spectrum abbreviations `Matrix.leastEigenvalue` and
  `Matrix.greatestEigenvalue`;
* the intrinsic Hessian least-spectral-value owner `hessianLeastEigenvalue`;
* the source-facing decrement owner `cubicRegularizationDelta`;
* the Euclidean bridge identifying `hessianLeastEigenvalue` with the spectrum of the Hessian
  matrix.

This keeps the source-facing decrement owner from the text, but treats the matrix spectral names as
thin bridge vocabulary over the canonical spectrum owner instead of as an independent second layer
of primitive data. -/

namespace Matrix

/-- The textbook least-eigenvalue quantity of a real square matrix, defined as the infimum of its
real spectrum. For a symmetric real matrix, this is the usual smallest eigenvalue. -/
abbrev leastEigenvalue {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℝ) : ℝ :=
  sInf (spectrum ℝ H)

/-- The textbook greatest-eigenvalue quantity of a real square matrix, defined as the supremum of
its real spectrum. For a symmetric real matrix, this is the usual largest eigenvalue. -/
abbrev greatestEigenvalue {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℝ) : ℝ :=
  sSup (spectrum ℝ H)

end Matrix

notation:max "λ_min(" H:max ")" => Matrix.leastEigenvalue H
notation:max "λ_max(" H:max ")" => Matrix.greatestEigenvalue H

/-- The textbook least-Hessian-eigenvalue quantity at `x`, defined from the real spectrum of the
intrinsic Hessian operator `hessian f x`. On `ℝⁿ`, the standard-basis Hessian matrix formula is a
bridge theorem. When `f` is `C²` at `x`, the Hessian is symmetric, so this is the usual least
eigenvalue of the Hessian matrix. -/
abbrev hessianLeastEigenvalue (f : E → ℝ) (x : E) : ℝ :=
  sInf (spectrum ℝ (hessian f x))

scoped[Gradient] notation:max "λ_min(" "∇²" f:max x:max ")" => hessianLeastEigenvalue f x

/-- Definition 4.1.6: for the textbook cubic-regularization quantity attached to a twice
continuously differentiable real objective `f`, a scalar `L > 0`, and an iterate `x_k`, the
quantity `δ_k` is `L * ‖∇ f(x_k)‖ / λ_min(∇²f(x_k))^2`. -/
def cubicRegularizationDelta (f : E → ℝ) (xk : E) (L : ℝ) : ℝ :=
  L * ‖∇ f xk‖ / (λ_min(∇² f xk)) ^ 2

/-- Unfolding `cubicRegularizationDelta` gives the textbook formula in terms of the intrinsic
gradient norm and least Hessian spectral value. -/
@[simp] theorem cubicRegularizationDelta_def (f : E → ℝ) (xk : E) (L : ℝ) :
    cubicRegularizationDelta f xk L =
      L * ‖∇ f xk‖ / (λ_min(∇² f xk)) ^ 2 :=
  rfl

section

variable {n : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin n)

/-- On `ℝⁿ`, the intrinsic least-Hessian-spectral-value owner agrees with the infimum of the real
spectrum of the standard-basis Hessian matrix. -/
theorem hessianLeastEigenvalue_eq_sInf_spectrum_hessianMatrix (f : F → ℝ) (x : F) :
    λ_min(∇² f x) = sInf (spectrum ℝ (∇² f x)) := by
  unfold hessianLeastEigenvalue
  rw [ContinuousLinearMap.spectrum_eq]
  rw [← Matrix.spectrum_toLpLin 2]
  rw [hessianMatrix_toEuclideanLin]

end

/-! ### Lemma_4_1_6 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

/- Lemma 4.1.6 lies in the Chapter 4 cubic-regularization / local-stationarity domain.

Sampled owner declarations:
* `cubicRegularizationLocalOptimalityMeasure` in `Definition_4_1_4`, the source-facing owner
  `μ[M](x)`;
* `HessianLipschitzOn` in `Definition_4_1_2`, the chapter owner for the local `C²` Hessian-
  Lipschitz hypothesis;
* `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Lemma_4_1_4`, the
  owner-level gradient estimate for a cubic-model minimizer;
* `hessianLeastEigenvalue` and the notation `λ_min(∇² f x)` in `Definition_4_1_6`.

Source/core/bridge triage:
* source-facing: the textbook estimate `μ_M(y) ≤ ‖y - x‖`;
* core/canonical: `cubicRegularizationLocalOptimalityMeasure f L M y`,
  `HessianLipschitzOn L 𝓕 f`, and
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`;
* bridge/view: the gradient bound from `Lemma_4_1_4` together with the assumed least-eigenvalue
  lower bound at `y`.

Primitive data:
* the objective `f : E → ℝ`;
* the regularization parameter `M`;
* the Lipschitz parameter `L`;
* points `x` and `y`;
* the owner hypotheses
  `HessianLipschitzOn L 𝓕 f` and
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`.

Derived API:
* the local-optimality-measure bound `μ[M](y) ≤ ‖y - x‖`.

The previous file kept the concrete model `EuclideanSpace ℝ (Fin n)` even though the owner
measure, the Hessian-Lipschitz owner, and the upstream cubic-minimizer estimate already live on
the intrinsic finite-dimensional real inner-product-space layer. This refinement removes that
extra model specialization instead of keeping a parallel Euclidean-only copy of the same theorem.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → ℝ} {L : NNReal}

local notation:max "μ[" M "](" x ")" =>
  cubicRegularizationLocalOptimalityMeasure f (L : ℝ) M x

-- Proof sketch: apply
-- `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` to control the
-- gradient term in `μ_M(y)`, use the `HessianLipschitzOn` owner from `Definition_4_1_2` for the
-- on-set `C²` and Hessian-Lipschitz data, and control the spectral term by the assumed lower
-- bound on the least eigenvalue of the Hessian at `y`.
/-- Lemma 4.1.6: if `x ∈ 𝓕`, the Hessian of `f` is `L`-Lipschitz on `𝓕`, `y` globally minimizes
the cubic model centered at `x` with parameter `M`, `y ∈ 𝓕`, and the least eigenvalue of
`∇² f(y)` is bounded below by `-((M / 2) + L) ‖y - x‖`, then
`μ_M(y) ≤ ‖y - x‖`. -/
theorem cubicRegularizationLocalOptimalityMeasure_le_norm_sub_of_isMinOn
    {𝓕 : Set E} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hM : 0 < M)
    (hy :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y)
    (hx : x ∈ 𝓕)
    (hy𝓕 : y ∈ 𝓕)
    (hlambdaMin :
      -(((M / 2) + (L : ℝ)) * ‖y - x‖) ≤ λ_min(∇²f y)) :
    μ[M](y) ≤ ‖y - x‖ := by
  rw [cubicRegularizationLocalOptimalityMeasure_eq_max]
  refine max_le ?_ ?_
  · have hgrad :=
      gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation
        hf hM.le hy hx hy𝓕
    have hLM : 0 < (L : ℝ) + M := by
      exact add_pos_of_nonneg_of_pos (show 0 ≤ (L : ℝ) by exact_mod_cast L.2) hM
    have hsq :
        (2 / ((L : ℝ) + M)) * ‖∇ f y‖ ≤ ‖y - x‖ ^ (2 : ℕ) := by
      have hscale : 0 ≤ 2 / ((L : ℝ) + M) := by positivity
      calc
        (2 / ((L : ℝ) + M)) * ‖∇ f y‖
            ≤
              (2 / ((L : ℝ) + M)) *
                ((((L : ℝ) + M) / 2) * ‖y - x‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hgrad hscale
        _ = ‖y - x‖ ^ (2 : ℕ) := by
          field_simp [hLM.ne']
    calc
      Real.sqrt ((2 / ((L : ℝ) + M)) * ‖∇ f y‖)
          ≤ Real.sqrt (‖y - x‖ ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hsq
      _ = ‖y - x‖ := by
        rw [Real.sqrt_sq (norm_nonneg (y - x))]
  · have hLM : 0 < 2 * (L : ℝ) + M := by
      nlinarith [show 0 ≤ (L : ℝ) by exact_mod_cast L.2, hM]
    have hnegLambda : -λ_min(∇²f y) ≤ ((M / 2) + (L : ℝ)) * ‖y - x‖ := by
      linarith
    have hscale : 0 ≤ 2 / (2 * (L : ℝ) + M) := by positivity
    calc
      -(2 / (2 * (L : ℝ) + M)) * λ_min(∇²f y)
          = (2 / (2 * (L : ℝ) + M)) * (-λ_min(∇²f y)) := by ring
      _ ≤ (2 / (2 * (L : ℝ) + M)) * (((M / 2) + (L : ℝ)) * ‖y - x‖) :=
        mul_le_mul_of_nonneg_left hnegLambda hscale
      _ = ‖y - x‖ := by
        field_simp [hLM.ne']
        ring

end

/-! ### Proposition_4_1_6 (from Chap04) -/
noncomputable section

open Matrix

namespace LecturesConvexOptimization_Nesterov_2018.Chap04.Proposition_4_1_6

/-- The higher coordinates of `ℝⁿ⁺¹`, namely all coordinates except the first one. -/
abbrev HigherCoord (n : ℕ) := { i : Fin n.succ // i ≠ 0 }

/-- The standard basis of `ℝⁿ⁺¹` used to read Jacobian matrices entrywise. -/
abbrev standardBasis (n : ℕ) :
    Module.Basis (Fin n.succ) ℝ (EuclideanSpace ℝ (Fin n.succ)) :=
  (EuclideanSpace.basisFun (Fin n.succ) ℝ).toBasis

/-- The continuous linear map extracting the `i`-th coordinate of `ℝⁿ⁺¹`. -/
abbrev coordCLM {n : ℕ} (i : Fin n.succ) :
    EuclideanSpace ℝ (Fin n.succ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp
    (EuclideanSpace.equiv (Fin n.succ) ℝ).toContinuousLinearMap

/-- The continuous linear map keeping only the coordinates strictly before `i`. -/
def previousCoordinatesCLM {n : ℕ} (i : HigherCoord n) :
    EuclideanSpace ℝ (Fin n.succ) →L[ℝ] EuclideanSpace ℝ (Fin i.1) :=
  ((EuclideanSpace.equiv (Fin i.1) ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun j : Fin i.1 ↦
      coordCLM (Fin.castLT j (lt_trans j.2 i.1.2)))

/-- The vector of coordinates of `x` strictly preceding the higher coordinate `i`. -/
def previousCoordinates {n : ℕ} (x : EuclideanSpace ℝ (Fin n.succ)) (i : HigherCoord n) :
    EuclideanSpace ℝ (Fin i.1) :=
  previousCoordinatesCLM i x

/-- Evaluating `previousCoordinates x i` at `j` returns the `j`-th coordinate of `x`. -/
@[simp] theorem previousCoordinates_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n.succ))
    (i : HigherCoord n) (j : Fin i.1) :
    previousCoordinates x i j = x (Fin.castLT j (lt_trans j.2 i.1.2)) := by
  simp [previousCoordinates, previousCoordinatesCLM, coordCLM]

/-- Proposition 4.1.6 is modeled by a triangular transformation on `ℝⁿ⁺¹`. The correction at a
higher coordinate depends only on the strictly earlier coordinates. -/
structure TriangularTransformation (n : ℕ) where
  /-- The correction term attached to the higher coordinate `i`. -/
  correction (i : HigherCoord n) : EuclideanSpace ℝ (Fin i.1) → ℝ
  /-- Each correction term is differentiable on its natural Euclidean domain. -/
  differentiable_correction (i : HigherCoord n) : Differentiable ℝ (correction i)

namespace TriangularTransformation

/-- The coordinate tuple defining the triangular transformation before identifying it with
`EuclideanSpace`. -/
def toCoordinates {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    Fin n.succ → ℝ :=
  Fin.cons (x 0) fun i ↦
    x i.succ +
      u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
        (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩)

/-- The triangular transformation acts by fixing the first coordinate and adding a prefix-dependent
correction to each higher coordinate. -/
def toFun {n : ℕ} (u : TriangularTransformation n) :
    EuclideanSpace ℝ (Fin n.succ) → EuclideanSpace ℝ (Fin n.succ) :=
  fun x ↦ (EuclideanSpace.equiv (Fin n.succ) ℝ).symm (toCoordinates u x)

instance {n : ℕ} : CoeFun (TriangularTransformation n)
    (fun _ ↦ EuclideanSpace ℝ (Fin n.succ) → EuclideanSpace ℝ (Fin n.succ)) where
  coe := toFun

/-- The first coordinate of a triangular transformation is unchanged. -/
@[simp] theorem coe_apply_zero {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    u x 0 = x 0 := by
  simp [TriangularTransformation.toFun, TriangularTransformation.toCoordinates]

/-- A higher coordinate is obtained by adding the corresponding correction term. -/
@[simp] theorem coe_apply_succ {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : Fin n) :
    u x i.succ = x i.succ +
      u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
        (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩) := by
  simp [TriangularTransformation.toFun, TriangularTransformation.toCoordinates]

/-- Helper for Proposition 4.1.6: the triangular transformation is differentiable because each
coordinate is either a coordinate projection or a differentiable correction composed with the
prefix-coordinate map. -/
theorem differentiable {n : ℕ} (u : TriangularTransformation n) :
    Differentiable ℝ u := by
  have hcoords : Differentiable ℝ (u.toCoordinates) := by
    refine (differentiable_pi).2 ?_
    intro i
    cases i using Fin.cases with
    | zero =>
        -- The first coordinate is the identity coordinate map.
        simpa [TriangularTransformation.toCoordinates, coordCLM] using
          (coordCLM (n := n) 0).differentiable
    | succ i =>
        -- Higher coordinates are sums of the identity coordinate and the correction term.
        have hcoord : Differentiable ℝ
            (fun x : EuclideanSpace ℝ (Fin n.succ) ↦ x i.succ) := by
          simpa [coordCLM] using (coordCLM (n := n) i.succ).differentiable
        have hcorr : Differentiable ℝ
            (fun x : EuclideanSpace ℝ (Fin n.succ) ↦
              u.correction ⟨i.succ, Fin.succ_ne_zero i⟩
                (previousCoordinates x ⟨i.succ, Fin.succ_ne_zero i⟩)) := by
          exact (u.differentiable_correction ⟨i.succ, Fin.succ_ne_zero i⟩).comp
            (previousCoordinatesCLM ⟨i.succ, Fin.succ_ne_zero i⟩).differentiable
        simpa [TriangularTransformation.toCoordinates] using hcoord.add hcorr
  -- Transfer differentiability from coordinate tuples back to `EuclideanSpace`.
  simpa [TriangularTransformation.toFun] using
    ((EuclideanSpace.equiv (Fin n.succ) ℝ).symm.differentiable.comp hcoords)

end TriangularTransformation

/-- The Jacobian matrix of `u` in the standard basis. -/
abbrev jacobianMatrix {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    Matrix (Fin n.succ) (Fin n.succ) ℝ :=
  LinearMap.toMatrix (standardBasis n) (standardBasis n) (fderiv ℝ u x).toLinearMap

/-- Helper for Proposition 4.1.6: perturbing `x` in a coordinate `j` which is not strictly earlier
than `i` leaves the prefix coordinates before `i` unchanged. -/
lemma previousCoordinates_add_basis_of_not_lt {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : HigherCoord n)
    (j : Fin n.succ) (t : ℝ) (hji : ¬ j < i.1) :
    previousCoordinates
        (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) i =
      previousCoordinates x i := by
  ext k
  -- The perturbed basis vector has zero contribution on coordinates strictly before `i`.
  have hneq : Fin.castLT k (lt_trans k.2 i.1.2) ≠ j := by
    intro hEq
    apply hji
    have hklt : Fin.castLT k (lt_trans k.2 i.1.2) < i.1 := by
      simpa [Fin.lt_def, Fin.val_castLT] using k.2
    simpa [hEq] using hklt
  simp [previousCoordinates_apply, hneq]

/-- Helper for Proposition 4.1.6: differentiating the `i`-th output coordinate along the `j`-th
standard basis direction reads off the `(i,j)` Jacobian entry. -/
lemma jacobian_entry_hasDerivAt {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i j : Fin n.succ) :
    HasDerivAt
      (fun t : ℝ ↦
        u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) i)
      (jacobianMatrix u x i j) 0 := by
  let e := EuclideanSpace.basisFun (Fin n.succ) ℝ j
  have hu : HasFDerivAt u (fderiv ℝ u x) x := by
    exact (TriangularTransformation.differentiable u x).hasFDerivAt
  have hcoord : HasFDerivAt (fun y ↦ u y i)
      ((coordCLM (n := n) i).comp (fderiv ℝ u x)) x := by
    simpa [coordCLM] using ((coordCLM (n := n) i).hasFDerivAt.comp x hu)
  have hcoord0 : HasFDerivAt (fun y ↦ u y i)
      ((coordCLM (n := n) i).comp (fderiv ℝ u x)) (x + (0 : ℝ) • e) := by
    simpa [e] using hcoord
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • e) e (0 : ℝ) := by
    simpa [e] using (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x)
  -- Compose the derivative of the coordinate function with the basis-direction line.
  have hslice := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hcoord0 hline
  simpa [jacobianMatrix, e, LinearMap.toMatrix_apply] using hslice

/-- Helper for Proposition 4.1.6: Jacobian entries above the diagonal vanish, so the standard
matrix of the derivative is triangular in the `toMatrix` convention. -/
lemma jacobian_matrix_entry_eq_zero_of_later {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) {i j : Fin n.succ} (hij : i < j) :
    jacobianMatrix u x i j = 0 := by
  have hslice := jacobian_entry_hasDerivAt (u := u) (x := x) i j
  cases i using Fin.cases with
  | zero =>
      -- The first coordinate is fixed, so varying any later coordinate leaves it constant.
      have hconst : HasDerivAt
          (fun t : ℝ ↦
            u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) 0)
          0 0 := by
        have hfun :
            (fun t : ℝ ↦
              u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) 0) =
            fun _ : ℝ ↦ x 0 := by
          funext t
          have hne : j ≠ (0 : Fin n.succ) := ne_of_gt hij
          simp [TriangularTransformation.coe_apply_zero, hne]
        rw [hfun]
        simpa using (hasDerivAt_const (0 : ℝ) (x 0))
      exact hslice.unique hconst
  | succ k =>
      -- Later-coordinate perturbations do not affect the correction term at coordinate `k.succ`.
      have hnot : ¬ j < k.succ := not_lt_of_ge (le_of_lt hij)
      have hconst : HasDerivAt
          (fun t : ℝ ↦
            u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) k.succ)
          0 0 := by
        have hfun :
            (fun t : ℝ ↦
              u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) k.succ) =
            fun _ : ℝ ↦ u x k.succ := by
          funext t
          have hprev := previousCoordinates_add_basis_of_not_lt
            (x := x) (i := ⟨k.succ, Fin.succ_ne_zero k⟩) (j := j) (t := t) hnot
          have hcoord :
              (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ j)) k.succ = x k.succ := by
            simp [ne_of_gt hij]
          rw [TriangularTransformation.coe_apply_succ, TriangularTransformation.coe_apply_succ]
          rw [hprev, hcoord]
        rw [hfun]
        simpa using (hasDerivAt_const (0 : ℝ) (u x k.succ))
      exact hslice.unique hconst

/-- Helper for Proposition 4.1.6: each diagonal Jacobian entry equals `1` because the
corresponding output coordinate depends affinely on its own input coordinate with slope `1`. -/
lemma jacobian_matrix_diagonal_eq_one {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) (i : Fin n.succ) :
    jacobianMatrix u x i i = 1 := by
  have hslice := jacobian_entry_hasDerivAt (u := u) (x := x) i i
  cases i using Fin.cases with
  | zero =>
      -- Along the first coordinate, the map is exactly `t ↦ u x 0 + t`.
      have haffine : HasDerivAt
          (fun t : ℝ ↦
            u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ 0)) 0)
          1 0 := by
        have hfun :
            (fun t : ℝ ↦
              u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ 0)) 0) =
            fun t : ℝ ↦ u x 0 + t := by
          funext t
          simp [TriangularTransformation.coe_apply_zero, add_comm]
        rw [hfun]
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (u x 0)
      exact hslice.unique haffine
  | succ k =>
      -- At coordinate `k.succ`, the prefix term is unchanged by perturbing the same coordinate.
      have haffine : HasDerivAt
          (fun t : ℝ ↦
            u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ k.succ)) k.succ)
          1 0 := by
        have hprev := fun t : ℝ ↦ previousCoordinates_add_basis_of_not_lt
          (x := x) (i := ⟨k.succ, Fin.succ_ne_zero k⟩) (j := k.succ) (t := t)
          (by simp)
        have hfun :
            (fun t : ℝ ↦
              u (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ k.succ)) k.succ) =
            fun t : ℝ ↦ u x k.succ + t := by
          funext t
          rw [TriangularTransformation.coe_apply_succ, TriangularTransformation.coe_apply_succ]
          have hcoord :
              (x + t • (EuclideanSpace.basisFun (Fin n.succ) ℝ k.succ)) k.succ =
                x k.succ + t := by
            simp
          rw [hprev t, hcoord]
          ac_rfl
        rw [hfun]
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (u x k.succ)
      exact hslice.unique haffine

/-- Helper for Proposition 4.1.6: in `LinearMap.toMatrix` coordinates, the Jacobian is
lower triangular, i.e. entries with `i < j` vanish. -/
lemma jacobianMatrix_blockTriangular {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    (jacobianMatrix u x).BlockTriangular OrderDual.toDual := by
  intro i j hij
  -- `OrderDual.toDual j < OrderDual.toDual i` is exactly `i < j`.
  exact jacobian_matrix_entry_eq_zero_of_later (u := u) (x := x) (by simpa using hij)

/-- Proposition 4.1.6: for a triangular transformation, the Jacobian matrix has unit diagonal and
triangular zero pattern, so its determinant is `1` at every point. In the `toMatrix` convention
used here, that zero pattern is lower triangular, which is the matrix transpose convention of the
source's upper-triangular statement. -/
theorem triangularTransformation_fderiv_det_eq_one {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    (fderiv ℝ u x).det = 1 := by
  let J := jacobianMatrix u x
  have htri : J.BlockTriangular OrderDual.toDual := by
    simpa [J] using jacobianMatrix_blockTriangular (u := u) (x := x)
  have hdiag : ∀ i : Fin n.succ, J i i = 1 := by
    intro i
    simpa [J] using jacobian_matrix_diagonal_eq_one (u := u) (x := x) i
  -- The entrywise lemmas turn the determinant into the product of the diagonal entries.
  calc
    (fderiv ℝ u x).det = J.det := by
      symm
      simpa [J, jacobianMatrix] using
        (LinearMap.det_toMatrix (standardBasis n) (fderiv ℝ u x).toLinearMap)
    _ = ∏ i, J i i := by
      exact Matrix.det_of_lowerTriangular J htri
    _ = ∏ _ : Fin n.succ, (1 : ℝ) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      simp [hdiag i]
    _ = 1 := by
      simp

/-- Helper for Proposition 4.1.6: determinant `1` implies that the derivative is nonsingular at
every point. -/
theorem triangularTransformation_fderiv_det_ne_zero {n : ℕ} (u : TriangularTransformation n)
    (x : EuclideanSpace ℝ (Fin n.succ)) :
    (fderiv ℝ u x).det ≠ 0 := by
  rw [triangularTransformation_fderiv_det_eq_one (u := u) (x := x)]
  norm_num

end LecturesConvexOptimization_Nesterov_2018.Chap04.Proposition_4_1_6
