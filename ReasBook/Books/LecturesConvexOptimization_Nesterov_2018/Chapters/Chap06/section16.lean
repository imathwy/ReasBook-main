

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_16 (from Chap06) -/
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

/-! ### Lemma_6_16 (from Chap06) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 6.16 lies in the Chapter 6 restricted-duality / concavity domain.

Sampled owner declarations:
- `restrictedDualFunction` in `Definition_6_55`, the Chapter 6 owner of the restricted dual
  supremum;
- `scaledRestrictedDualFunction` in `Definition_6_56`, the Chapter 6 owner of the contracted
  restricted dual supremum;
- `AffineMap.lineMap` in mathlib, the canonical affine owner of the contraction
  `y = (1 - τ) • xBar + τ • x` used inside `scaledRestrictedDualFunction`;
- `ConcaveOn` in mathlib, the canonical concavity owner on a feasible set.

Best owner abstraction:
- source-facing: the interval estimate comparing the scaled and unscaled restricted dual
  functions;
- core/canonical: `restrictedDualFunction` and `scaledRestrictedDualFunction`;
- bridge/view: the real-valued specialization `fun x ↦ (F x : WithTop ℝ)`.

Primitive data:
- the feasible set `Q`;
- the real-valued concave function `F`;
- the feasible base point `xBar ∈ Q`;
- the contraction parameter `τ ∈ [0, 1]`;
- the dual vector `s`.

Derived API:
- the canonical restricted dual value
  `restrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ)) ... s`;
- the canonical scaled restricted dual value
  `scaledRestrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ)) ... τ s`;
- the interval comparison below.

The previous file rebuilt local `ℝ`-valued owners for the same restricted-dual suprema already
introduced in `Definition_6_55` and `Definition_6_56`. This refinement removes that duplicate
wheel, keeps the owner layer in the Chapter 6 canonical `WithTop ℝ` form, and presents Lemma 6.16
as the real-valued bridge obtained from the canonical lift `fun x ↦ (F x : WithTop ℝ)`.
-/

/-- Lemma 6.16: for a concave real-valued function `F` on `Q`, the scaled restricted dual
function of the canonical `WithTop` lift of `F` at `(τ, xBar)` lies between `0` and `τ` times the
unscaled restricted dual function. -/
-- Proof sketch: the lower bound comes from the feasible choice `x = xBar`, where the affine gap
-- is `0`. For the upper bound, write `y = (1 - τ) • xBar + τ • x`; concavity keeps `y` in `Q`,
-- and `F y ≥ (1 - τ) * F xBar + τ * F x` gives
-- `s (xBar - y) + F xBar - F y ≤ τ * (s (xBar - x) + F xBar - F x)` pointwise. Taking suprema
-- yields the claimed factor-`τ` estimate.
theorem scaledRestrictedDualFunction_mem_Icc_of_concaveOn
    {Q : Set E} {F : E → ℝ} (hF : ConcaveOn ℝ Q F)
    {xBar : E} (hxBar : xBar ∈ Q) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (s : StrongDual ℝ E) :
    scaledRestrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ))
        ⟨xBar, by simp [hxBar, withTopEffectiveDomain]⟩ τ s ∈
      Set.Icc
        (0 : WithTop ℝ)
        (((τ : WithTop ℝ) *
          restrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ))
            ⟨xBar, by simp [hxBar, withTopEffectiveDomain]⟩ s)) := sorry

end

/-! ### Proposition_6_16 (from Chap06) -/
open scoped BigOperators
open scoped StandardSimplex

noncomputable section

/- Proposition 6.16 lies in the finite simplex / entropy-smoothing domain.

Sampled owner declarations:
* `normalizedEntropyProxFunction` and `normalizedEntropyProxFunction_apply` in
  `Chap06/Definition_6_14`;
* `entropyRegularizedSimplexObjective` and `entropyRegularizedSimplexObjective_apply` in
  `Chap06/Lemma_6_4`;
* `smoothedPrimalObjective` in `Chap06/Definition_6_30`.

Best owner abstraction:
* source-facing: the entropy-smoothed simplex supremum attached to the affine scores
  `j ↦ ⟪a_j, x⟫ + b_j`;
* core/canonical: `normalizedEntropyProxFunction`, with the later chapter owners
  `entropyRegularizedSimplexObjective` and `smoothedPrimalObjective` for the same smoothing
  pattern;
* bridge/view: Proposition 6.16's explicit expansion of the normalized entropy prox term.

Primitive data:
* a real inner-product space `E`;
* the finite affine family `a`, `b`, the linear term `c`, the simplex size `m`, and the
  smoothing parameter `μ`.

Derived API:
* the explicit source-facing entropy expansion of the smoothed simplex supremum.

The previous version introduced a local wrapper `entropySmoothedAffineObjective` whose only role
was to restate the displayed supremum formula. This file now states the proposition directly in the
canonical simplex/entropy language and removes the duplicate owner-shaped definition.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: compare the two `Set.range` supremum sets pointwise, then expand
-- `normalizedEntropyProxFunction m u = Real.log (m : ℝ) + ∑ j, u j * Real.log (u j)` inside the
-- supremum.
/-- Proposition 6.16: the entropy-smoothed approximation of
`x ↦ ⟪c, x⟫ + max_j (⟪a_j, x⟫ + b_j)` is obtained by replacing the entropy prox-function on
`Δ_m` with its explicit formula `log m + ∑_j u_j log u_j`. -/
theorem entropySmoothedAffineSup_eq_entropyExpansion
    (m : ℕ+) (c x : E) (a : Fin (m : ℕ) → E) (b : Fin (m : ℕ) → ℝ) (μ : ℝ) :
    inner ℝ c x +
      sSup
        (Set.range fun u : Δ[m] ↦
          (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
            μ * normalizedEntropyProxFunction m u) =
      inner ℝ c x +
        sSup
          (Set.range fun u : Δ[m] ↦
            (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
              μ * ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
                μ * Real.log (m : ℝ)) := by
  refine congrArg (fun s : Set ℝ ↦ inner ℝ c x + sSup s) ?_
  ext y
  constructor <;> intro hy <;> rcases hy with ⟨u, rfl⟩ <;> refine ⟨u, ?_⟩
  · change
      (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
          μ * ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
            μ * Real.log (m : ℝ) =
        (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
          μ * normalizedEntropyProxFunction m u
    rw [normalizedEntropyProxFunction_apply]
    ring
  · change
      (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
          μ * normalizedEntropyProxFunction m u =
        (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
          μ * ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
            μ * Real.log (m : ℝ)
    rw [normalizedEntropyProxFunction_apply]
    ring

/-! ### Theorem_6_16 (from Chap06) -/
noncomputable section

open scoped BigOperators ConstrainedArgmin Gradient WeightSequenceNotation WithTopConvexAnalysis

universe u

namespace SecondOrderLocalModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 6.16 lies in the Chapter 6 second-order composite trust-region domain.

Mandatory owner-style sampling before refining:
- `CompositeTrustRegionContractionMethod` in `Algorithm_6_6`, the chapter's recursive owner for
  method `(6.4.50)`;
- `secondOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the canonical quadratic Taylor-model
  owner;
- `contractedCompositeSecondOrderModel` in `Algorithm_6_6`, the chapter owner of the contracted
  quadratic composite subproblem;
- `ConditionalGradientContraction.estimatingFunctionalSequence` in `Theorem_6_14`, the chapter
  owner for recursive estimating-function families.

Best owner abstraction:
- source-facing: this theorem's second-order estimating function, error recursion, and
  second-order optimality measure on the finite feasible domain;
- core/canonical: `CompositeTrustRegionContractionMethod`, `secondOrderTaylorModelAt`,
  `contractedCompositeSecondOrderModel`, and
  `ConditionalGradientContraction.estimatingFunctionalSequence`;
- bridge/view: the finite-value representative `withTopRealPart problem.nonsmoothPart` and the
  iterate restriction to `Q ∩ dom Ψ`.

Primitive data:
- the ambient composite problem `problem`;
- the initial feasible point `x0`;
- the recursive method owner `method : CompositeTrustRegionContractionMethod problem x0`.

Derived API:
- the specialized estimating sequence for the initial model
  `f + withTopRealPart Ψ`;
- the recursive second-order error term;
- the source-facing second-order optimality measure on `Q ∩ dom Ψ`. -/

/-- The increment added at step `t + 1` to the second-order error term `\hat C_{ν,t}`. -/
def secondOrderErrorIncrement
    (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) : ℝ :=
  (a (t + 1) * a (t + 1) / A[a]((t + 1))) *
      (Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) +
    (a (t + 1) * a (t + 1) / ((2 : ℝ) * A[a]((t + 1)))) * L * D * D

/-- Expanding `secondOrderErrorIncrement a L Hν D ν t` gives the `H_ν D^{2+ν}` and `L D^2`
contributions added at step `t + 1`, with the canonical Chapter 6 denominator `A[a](t + 1)`. -/
theorem secondOrderErrorIncrement_apply
    (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) :
    secondOrderErrorIncrement a L Hν D ν t =
      (a (t + 1) * a (t + 1) / A[a]((t + 1))) *
          (Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) +
        (a (t + 1) * a (t + 1) / ((2 : ℝ) * A[a]((t + 1)))) * L * D * D :=
  rfl

/-- The recursive error term `\hat C_{ν,t}` for the second-order local-model method, using the
canonical accumulated weights `A[a](t)`. -/
def secondOrderError
    (initialError : ℝ) (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) : ℕ → ℝ
  | 0 => initialError
  | t + 1 => secondOrderError initialError a L Hν D ν t +
      secondOrderErrorIncrement a L Hν D ν t

/-- The second-order error term starts from the prescribed initial gap. -/
theorem secondOrderError_zero
    (initialError : ℝ) (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) :
    secondOrderError initialError a L Hν D ν 0 = initialError :=
  rfl

/-- The recursive step for `\hat C_{ν,t}` adds the increment from
`secondOrderErrorIncrement a L Hν D ν t`. -/
theorem secondOrderError_succ
    (initialError : ℝ) (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) :
    secondOrderError initialError a L Hν D ν (t + 1) =
      secondOrderError initialError a L Hν D ν t +
        secondOrderErrorIncrement a L Hν D ν t :=
  rfl

/-- The second-order optimality measure `θ(x)` is the maximal decrease predicted by the canonical
second-order Taylor model of `f` plus the regularizer gap at a finite feasible point
`x ∈ Q ∩ dom Ψ`, recorded in `EReal` so the owner remains faithful even when the supremum is not
bounded above in `ℝ`. -/
def secondOrderOptimalityMeasure
    (Q : Set E) (f : E → ℝ) (Ψ : E → WithTop ℝ) :
    ↥(Q ∩ dom Ψ) → EReal :=
  fun x ↦
    sSup ((fun y : E ↦
      (((f x + withTopRealPart Ψ x) -
            (secondOrderTaylorModelAt f x y + withTopRealPart Ψ y) : ℝ) : EReal)) ''
      (Q ∩ dom Ψ))

namespace SecondOrderOptimalityMeasureNotation

/- Source-facing Lean notation for the textbook second-order optimality measure `θ(x)` with the
ambient feasible set and composite objective data fixed by the surrounding context. -/
scoped notation:max "θ[" Q ", " f ", " Ψ "](" x:arg ")" =>
  secondOrderOptimalityMeasure Q f Ψ x

end SecondOrderOptimalityMeasureNotation

open scoped SecondOrderOptimalityMeasureNotation

/-- Expanding `θ[Q, f, Ψ](x)` gives the defining `EReal` supremum of the canonical second-order
Taylor-model decrease over the finite feasible domain `Q ∩ dom Ψ`. -/
theorem secondOrderOptimalityMeasure_def
    (Q : Set E) (f : E → ℝ) (Ψ : E → WithTop ℝ) (x : ↥(Q ∩ dom Ψ)) :
    θ[Q, f, Ψ](x) =
      sSup ((fun y : E ↦
        (((f x + withTopRealPart Ψ x) -
              (secondOrderTaylorModelAt f x y + withTopRealPart Ψ y) : ℝ) : EReal)) ''
        (Q ∩ dom Ψ)) :=
  rfl

section Method

variable {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}

/-- Every iterate lies in the finite-value domain `Q ∩ dom Ψ`, because the method stays in `Q`
and `Ψ` is finite on `Q` by the owner hypothesis `ClosedConvexOn Q Ψ`. -/
theorem iterate_mem_optimalityDomain
    (method : CompositeTrustRegionContractionMethod problem x0) (t : ℕ) :
    method t ∈ problem.feasibleSet ∩ dom problem.nonsmoothPart := by
  exact ⟨method.iterates_mem_feasibleSet t,
    problem.nonsmoothPart_closedConvex.subset_withTopEffectiveDomain
      (method.iterates_mem_feasibleSet t)⟩

/-- The estimating sequence `φ_t` attached to Algorithm 6.6, obtained by specializing the
chapter owner `estimatingFunctionalSequence` to the initial model
`f + withTopRealPart Ψ`. -/
def estimatingFunction
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ) :
    ℕ → E → ℝ :=
  ConditionalGradientContraction.estimatingFunctionalSequence
    a
    (fun x ↦ problem.smoothPart x + withTopRealPart problem.nonsmoothPart x)
    problem.smoothPart
    (fun x ↦ InnerProductSpace.toDualMap ℝ E (∇ problem.smoothPart x))
    (withTopRealPart problem.nonsmoothPart)
    method

/-- The estimating sequence starts from `φ₀(x) = a₀ \bar f(x)`. -/
theorem estimatingFunction_zero
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ) :
    estimatingFunction method a 0 =
      fun x ↦ a 0 * (problem.smoothPart x + withTopRealPart problem.nonsmoothPart x) :=
  rfl

/-- The recursive step of the estimating sequence is
`φ_{t+1}(x) = φ_t(x) + a_{t+1} [f(x_t) + ⟪∇ f(x_t), x - x_t⟫ + Ψ(x)]`. -/
theorem estimatingFunction_succ
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ) (t : ℕ) :
    estimatingFunction method a (t + 1) =
      fun x ↦
        estimatingFunction method a t x +
          a (t + 1) *
            (problem.smoothPart (method t) +
              inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
              withTopRealPart problem.nonsmoothPart x) :=
  rfl

/-- The canonical error sequence `\hat C_{ν,t}` anchored at the baseline point `xStar`. -/
def errorTerm
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ)
    (xStar : E) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) : ℕ → ℝ :=
  secondOrderError
    (a 0 *
      ((problem.smoothPart (method 0) + withTopRealPart problem.nonsmoothPart (method 0)) -
        (problem.smoothPart xStar + withTopRealPart problem.nonsmoothPart xStar)))
    a L Hν D ν

/-- Expanding `errorTerm method a xStar L Hν D ν` gives the recursive second-order error term
starting from the weighted initial objective gap at `x₀` relative to `xStar`. -/
theorem errorTerm_def
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ)
    (xStar : E) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) :
    errorTerm method a xStar L Hν D ν =
      secondOrderError
        (a 0 *
          ((problem.smoothPart (method 0) + withTopRealPart problem.nonsmoothPart (method 0)) -
            (problem.smoothPart xStar + withTopRealPart problem.nonsmoothPart xStar)))
        a L Hν D ν :=
  rfl

-- Proof sketch: combine the local quadratic-model minimizing property from
-- `CompositeTrustRegionContractionMethod.iterates_succ_mem_and_isMinOn` with the update formula
-- `x_{t+1} = (1 - τ_t) x_t + τ_t v_t`, use the quadratic upper-model assumption with Hölder
-- remainder and the operator-norm bound on the canonical Hessian to control the estimating-
-- sequence error, and then rewrite the second displayed inequality through the source-facing
-- second-order optimality measure on `Q ∩ dom Ψ`.
/-- Theorem 6.16: if `x_t` is generated by method `(6.4.50)`, then for every `ν ∈ [0, 1]` the
estimating-sequence bound
`A_t \bar f(x_t) ≤ φ_t(x) + \hat C_{ν,t}` holds for all `t ≥ 0` and `x ∈ Q`, and moreover the
one-step decrease satisfies
`\bar f(x_t) - \bar f(x_{t+1}) ≥ τ_t θ(x_t) - (H_ν D^{2+ν} / ((1+ν)(2+ν))) τ_t^{2+ν}`. -/
theorem estimating_function_bound_and_objective_drop
    (method : CompositeTrustRegionContractionMethod problem x0)
    (a : ℕ → ℝ) {L Hν D : ℝ} (xStar : E)
    (ν : Set.Icc (0 : ℝ) 1)
    (hxStar :
      xStar ∈
        argmin[problem.feasibleSet]
          (fun x ↦ problem.smoothPart x + withTopRealPart problem.nonsmoothPart x))
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (h_hessian_bound : ∀ t : ℕ, ‖hessian problem.smoothPart (method t)‖ ≤ L)
    (h_upper_model :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet →
        problem.smoothPart y ≤
          secondOrderTaylorModelAt problem.smoothPart x y +
            Hν * Real.rpow ‖y - x‖ (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) :
    (∀ t : ℕ, ∀ x : E, x ∈ problem.feasibleSet →
      A[a](t) *
          (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) ≤
        estimatingFunction method a t x + errorTerm method a xStar L Hν D ν t) ∧
    (∀ t : ℕ,
      (((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            θ[problem.feasibleSet, problem.smoothPart, problem.nonsmoothPart](
              ⟨method t, iterate_mem_optimalityDomain method t⟩) -
          (((Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
              Real.rpow (method.stepSize t) (2 + (ν : ℝ)) : ℝ) : EReal)) := sorry

end Method

end SecondOrderLocalModel

end
