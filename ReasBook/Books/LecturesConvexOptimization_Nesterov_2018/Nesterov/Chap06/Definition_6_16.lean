import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_30
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Text_6_1_4_2_Population_Interpretation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v

variable {ι : Type u}

/- Definition 6.16 lies in the continuous-location smoothing domain.

Sampled owner-style declarations:
- `ContinuousLocationWeights`, `continuousLocationDualAdmissibleSet`,
  `continuousLocationDualTupleNorm`, and `continuousLocationDualProxFunction` in
  `Text_6_1_4_2_Population_Interpretation`, the chapter owners of the weights, dual feasible set,
  weighted tuple geometry, and prox-function;
- `smoothedPrimalObjectiveMaximand` and `smoothedPrimalObjective` in `Definition_6_30`, the
  chapter's canonical regularized-max owners;
- `continuousLocationSmoothingMap` in `Proposition_6_17`, the later source-facing bridge that
  rewrites the same tuple geometry through the chapter's smoothing-map owner.

Best owner abstraction:
- source-facing: the continuous-location smoothing specialization and its Huber-sum formula;
- core/canonical: `smoothedPrimalObjectiveMaximand` and `smoothedPrimalObjective`;
- bridge/view: the continuous-location specialization data fed into those owners.

Primitive data:
- the finite population index type `ι`;
- the population weights `weights`;
- the centers `c_j`.

Derived API:
- the dual feasible set `Q₂`;
- the weighted tuple norm and prox-function `d₂`;
- the continuous-location specialization of the regularized maximand and its smoothed supremum;
- the scalar Huber companion description.

Source/core/bridge triage:
- source-facing: `continuousLocationSmoothApproximation` and the Huber-sum companion theorem;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: `continuousLocationSmoothingMap`, together with the internal weighted
  center-penalty term fed to `smoothedPrimalObjective`.

The previous version rebuilt a second public maximand/supremum owner specialized to
`EuclideanSpace ℝ (Fin n)` and `Fin p`. This refinement reuses the chapter's canonical
regularized-max owner directly, keeps the Huber expansion as the real source-facing companion, and
lowers the public ambient data to an arbitrary finite index family in a real inner-product space.
-/

section Geometry

variable {E : Type v} [NormedAddCommGroup E]

-- Proof sketch: unfold `continuousLocationDualAdmissibleSet`; membership is exactly the defining
-- coordinatewise unit-ball condition on the tuple `u`.
/-- A tuple belongs to `Q₂` exactly when each coordinate has norm at most `1`. -/
theorem mem_continuousLocationDualAdmissibleSet_iff (u : ι → E) :
    u ∈ continuousLocationDualAdmissibleSet E ↔ ∀ j, ‖u j‖ ≤ 1 :=
  sorry

variable [Fintype ι]

-- Proof sketch: unfold `continuousLocationDualTupleNorm`.
/-- Evaluating the weighted dual tuple norm expands to the formula
`(∑_j m_j ‖u_j‖²)^(1/2)`. -/
theorem continuousLocationDualTupleNorm_def
    (weights : ContinuousLocationWeights ι) (u : ι → E) :
    continuousLocationDualTupleNorm E weights u =
      Real.sqrt (∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ)) :=
  sorry

-- Proof sketch: unfold `continuousLocationDualProxFunction`; the right-hand side is exactly the
-- defining quadratic expression in `continuousLocationDualTupleNorm`.
/-- Expanding `continuousLocationDualProxFunction` recovers the quadratic formula
`d₂(u) = (1 / 2) ‖u‖²`. -/
theorem continuousLocationDualProxFunction_def
    (weights : ContinuousLocationWeights ι) (u : ι → E) :
    continuousLocationDualProxFunction E weights u =
      (1 / 2 : ℝ) * (continuousLocationDualTupleNorm E weights u) ^ (2 : ℕ) :=
  sorry

end Geometry

section Huber

/-- The scalar Huber regularization term `ψ_μ(τ)` for a positive smoothing parameter `μ`,
defined as the supremum of `γ ↦ γ τ - (μ / 2) γ²` on the interval `[0, 1]`. -/
def continuousLocationHuberLoss (μ : {μ : ℝ // 0 < μ}) : ℝ → ℝ :=
  fun τ ↦
    sSup ((fun γ : ℝ ↦ γ * τ - ((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ)) '' Set.Icc (0 : ℝ) 1)

-- Proof sketch: unfold `continuousLocationHuberLoss`; the displayed supremum over `Set.Icc 0 1`
-- is exactly the defining scalar maximization problem.
/-- Evaluating the scalar Huber loss recovers the regularized maximization over `γ ∈ [0, 1]`. -/
theorem continuousLocationHuberLoss_def
    (μ : {μ : ℝ // 0 < μ}) (τ : ℝ) :
    continuousLocationHuberLoss μ τ =
      sSup ((fun γ : ℝ ↦ γ * τ - (((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ))) '' Set.Icc (0 : ℝ) 1) :=
  sorry

-- Proof sketch: maximize the concave quadratic `γ ↦ γ τ - (μ / 2) γ²` on `[0, 1]`; the critical
-- point is `γ = τ / μ`, which lies in `[0, 1]` exactly when `τ ≤ μ`, yielding the two branches.
/-- For `μ > 0` and `τ ≥ 0`, the scalar Huber loss is the usual quadratic-linear piecewise
function. -/
theorem continuousLocationHuberLoss_eq_piecewise
    (μ : {μ : ℝ // 0 < μ}) {τ : ℝ} (hτ : 0 ≤ τ) :
    continuousLocationHuberLoss μ τ =
      if τ ≤ (μ : ℝ) then τ ^ (2 : ℕ) / (2 * (μ : ℝ)) else τ - (μ : ℝ) / 2 := sorry

end Huber

section Smoothing

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `j`-th coordinate contribution to the continuous-location smoothing operator. -/
private def continuousLocationCoordinateMap (E : Type v) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (j : ι) :
    E →L[ℝ] StrongDual ℝ (ι → E) :=
  ((ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E).precomp ℝ).comp (innerSL ℝ)

/-- The `j`-th coordinate contribution evaluates to the pairing `u ↦ ⟪u_j, x⟫`. -/
-- Proof sketch: unfold `continuousLocationCoordinateMap`; evaluation reduces to the `j`-th
-- projection followed by the real inner-product functional.
private theorem continuousLocationCoordinateMap_apply
    (j : ι) (x : E) (u : ι → E) :
    continuousLocationCoordinateMap E j x u = inner ℝ (u j) x :=
  sorry

variable [Fintype ι]

/-- The continuous-location specialization of the generic smoothing operator
`x ↦ (u ↦ ∑_j m_j ⟪u_j, x⟫)`. -/
def continuousLocationSmoothingMap (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weights : ContinuousLocationWeights ι) :
    E →L[ℝ] StrongDual ℝ (ι → E) :=
  ∑ j, (weights j : ℝ) • continuousLocationCoordinateMap E j

-- Proof sketch: expand the finite weighted sum of the coordinate dual functionals.
/-- The continuous-location smoothing operator acts by the weighted pairing
`u ↦ ∑_j m_j ⟪u_j, x⟫`. -/
theorem continuousLocationSmoothingMap_apply
    (weights : ContinuousLocationWeights ι) (x : E) (u : ι → E) :
    continuousLocationSmoothingMap E weights x u =
      ∑ j, (weights j : ℝ) * inner ℝ (u j) x :=
  sorry

-- Internal helper for the center-dependent dual penalty
-- `u ↦ ∑_j m_j ⟪u_j, c_j⟫` used by the continuous-location specialization.
/-- The weighted center-evaluation term
`u ↦ ∑_j m_j ⟪u_j, c_j⟫` appearing in the continuous-location specialization. -/
private def continuousLocationCenterPenalty
    (weights : ContinuousLocationWeights ι) (centers : ι → E) : (ι → E) → ℝ :=
  fun u ↦ ∑ j, (weights j : ℝ) * inner ℝ (u j) (centers j)

-- Proof sketch: unfold the generic owner, evaluate `continuousLocationSmoothingMap`, and combine
-- the two weighted pairing sums into the pairing with `x - c_j`.
/-- Evaluating the chapter-owner maximand in the continuous-location specialization recovers the
displayed weighted-pairing formula `u ↦ ∑_j m_j ⟪u_j, x - c_j⟫ - μ d₂(u)`. -/
theorem smoothedPrimalObjectiveMaximand_continuousLocation_apply
    (weights : ContinuousLocationWeights ι) (centers : ι → E)
    (μ : {μ : ℝ // 0 < μ}) (x : E) (u : ι → E) :
    smoothedPrimalObjectiveMaximand
        (continuousLocationSmoothingMap E weights)
        (continuousLocationCenterPenalty weights centers)
        (continuousLocationDualProxFunction E weights)
        (μ : ℝ) x u =
      (∑ j, (weights j : ℝ) * inner ℝ (u j) (x - centers j)) -
        (μ : ℝ) * continuousLocationDualProxFunction E weights u :=
  sorry

/-- Definition 6.16 [Chapter6_2.json:42]: the smooth approximation `f_μ` for the continuous
location objective is the continuous-location specialization of the chapter owner
`smoothedPrimalObjective`, with dual feasible set `Q₂`, weighted quadratic prox-function
`d₂(u) = (1 / 2) ‖u‖²`, and center term `u ↦ ∑_j m_j ⟪u_j, c_j⟫`; the accompanying Huber-loss
description is recorded in the companion declarations below. -/
abbrev continuousLocationSmoothApproximation
    (weights : ContinuousLocationWeights ι) (centers : ι → E)
    (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  smoothedPrimalObjective
    (continuousLocationSmoothingMap E weights)
    (continuousLocationDualAdmissibleSet E)
    0
    (continuousLocationCenterPenalty weights centers)
    (continuousLocationDualProxFunction E weights)
    (μ : ℝ)

-- Proof sketch: apply `smoothedPrimalObjective_apply` to the continuous-location specialization of
-- the generic smoothing owner.
/-- Evaluating the smooth approximation recovers the defining supremum over the dual set `Q₂`. -/
theorem continuousLocationSmoothApproximation_apply
    (weights : ContinuousLocationWeights ι) (centers : ι → E)
    (μ : {μ : ℝ // 0 < μ}) (x : E) :
    continuousLocationSmoothApproximation weights centers μ x =
      sSup
        (smoothedPrimalObjectiveMaximand
            (continuousLocationSmoothingMap E weights)
            (continuousLocationCenterPenalty weights centers)
            (continuousLocationDualProxFunction E weights)
            (μ : ℝ) x ''
          continuousLocationDualAdmissibleSet E) :=
  sorry

-- Proof sketch: separate the dual maximization into the independent coordinate problems indexed
-- by `j`, identify each scalar maximization with `continuousLocationHuberLoss μ ‖x - c_j‖`, and
-- sum the resulting contributions with the weights `m_j`.
/-- The smooth approximation splits as the weighted sum of scalar Huber losses evaluated at the
distances `‖x - c_j‖`. -/
theorem continuousLocationSmoothApproximation_eq_sum_huberLoss
    (weights : ContinuousLocationWeights ι) (centers : ι → E)
    (μ : {μ : ℝ // 0 < μ}) (x : E) :
    continuousLocationSmoothApproximation weights centers μ x =
      ∑ j, (weights j : ℝ) * continuousLocationHuberLoss μ ‖x - centers j‖ :=
  sorry

end Smoothing

end
