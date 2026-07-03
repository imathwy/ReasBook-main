import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_14 (from Chap07) -/
noncomputable section

universe u v

section

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {U : Type v} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/- Definition 7.14 lies in the chapter's slice-infimum / constrained-minimization domain.

Sampled owner-style declarations:
- `boundedFeasibleSet` in `Chap07/Definition_7_13`, the chapter owner of the localized set
  `Q₁(ρ)`
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`
- `SetConstrainedMinimizationProblem.optimalValue` and `optimalValue_eq_sInf_image` in
  `Chap01/Definition_1_3_7`
- `supportFunction_toReal_comp_linearMap_dualNorm_bounds` in `Chap07/Lemma_7_2`, the nearby
  intrinsic linear-map formulation of the same `⟪A x, u⟫` pairing pattern

Best owner abstraction:
- source-facing: the relative-scale lower-value function `u ↦ inf_{x ∈ Q₁(\hatρ)} ⟪A x, u⟫`
- core/canonical: for fixed `u`, the constrained minimization owner
  `SetConstrainedMinimizationProblem X`
- bridge/view: the explicit `sInf` image formula for that owner's `optimalValue`

Primitive data:
- the feasible set `Q₁ : Set X`
- the linear map `A : X →ₗ[ℝ] U`
- the objective `f : X → ℝ`
- the base point `x₀ : X`
- the radius parameter `γ₀(F)`

Derived API:
- the localized feasible slice `Q₁(\hatρ)` as `boundedFeasibleSet Q₁ x₀ \hatρ`
- the fixed-`u` constrained linear minimization problem on that slice
- the lower-value function as the owner's canonical `optimalValue : EReal`

Source/core/bridge triage:
- source-facing: the lower-value function from Definition 7.14
- core/canonical: the Chapter 1 constrained minimization owner
- bridge/view: the fixed-`u` problem and its `sInf` presentation

This refinement removes two non-canonical choices from the public core:
- the ad hoc radius-indexed feasible-set family is replaced by the chapter owner
  `boundedFeasibleSet`
- the raw real-valued `sInf` is replaced by the faithful owner value `optimalValue : EReal`

The public surface is also lifted from the coordinate model `Matrix (Fin m) (Fin n) ℝ` on
`EuclideanSpace ℝ (Fin _)` to the intrinsic linear-map formulation `A : X →ₗ[ℝ] U`.
-/

/-- For fixed `u`, the lower-value slice of Definition 7.14 is the constrained linear
minimization problem on the localized feasible set
`Q₁(\hatρ) = boundedFeasibleSet Q₁ x₀ \hatρ`, where `\hatρ = (1 / γ₀(F)) f(x₀)`. -/
def relativeScaleLowerValueProblem
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) : SetConstrainedMinimizationProblem X where
  feasibleSet := boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0)
  objective := fun x ↦ inner ℝ (A x) u

@[simp] theorem relativeScaleLowerValueProblem_feasibleSet
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) :
    (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).feasibleSet =
      boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0) :=
  rfl

@[simp] theorem relativeScaleLowerValueProblem_apply
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) (x : X) :
    relativeScaleLowerValueProblem gamma0F Q1 A f x0 u x =
      inner ℝ (A x) u :=
  rfl

/-- The owner optimal value of the fixed-`u` constrained problem is the extended-real infimum of
the feasible linear values `⟪A x, u⟫` over `Q₁(\hatρ)`. -/
theorem relativeScaleLowerValueProblem_optimalValue_eq_sInf_image
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) :
    (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue =
      sInf ((fun x : X ↦ (inner ℝ (A x) u : EReal)) ''
        boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0)) := by
  simpa [relativeScaleLowerValueProblem] using
    (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue_eq_sInf_image

/-- Definition 7.14: for `\hatρ = (1 / γ₀(F)) f(x₀)`, the lower-value function sends `u` to the
canonical constrained optimal value of `x ↦ ⟪A x, u⟫` on `Q₁(\hatρ)`. Using `optimalValue :
EReal` keeps the source minimum faithful even when the feasible slice is empty or the linear
objective is unbounded below. -/
def relativeScaleLowerValueFunction
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) : U → EReal :=
  fun u ↦ (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue

/-- Evaluating `relativeScaleLowerValueFunction` at `u` gives the defining owner optimal value of
the linear minimization problem on `Q₁(\hatρ)`. -/
@[simp] theorem relativeScaleLowerValueFunction_apply
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) :
    relativeScaleLowerValueFunction gamma0F Q1 A f x0 u =
      (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue :=
  rfl

/-- Expanding `relativeScaleLowerValueFunction` recovers the extended-real infimum of the feasible
linear values over `Q₁(\hatρ)`. -/
theorem relativeScaleLowerValueFunction_eq_sInf_image
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) :
    relativeScaleLowerValueFunction gamma0F Q1 A f x0 u =
      sInf ((fun x : X ↦ (inner ℝ (A x) u : EReal)) ''
        boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0)) := by
  simpa [relativeScaleLowerValueFunction] using
    relativeScaleLowerValueProblem_optimalValue_eq_sInf_image gamma0F Q1 A f x0 u

/-- If the linear objective attains its minimum on the localized feasible slice `Q₁(\hatρ)` at
`xStar`, then the lower-value function equals that attained value. This is the justified
real-minimum reading of Definition 7.14 under an attainment hypothesis. -/
theorem relativeScaleLowerValueFunction_eq_of_isMinOn
    (gamma0F : ℝ) (Q1 : Set X) (A : X →ₗ[ℝ] U)
    (f : X → ℝ) (x0 : X) (u : U) {xStar : X}
    (hxStar :
      xStar ∈ boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0))
    (hmin :
      IsMinOn (fun x : X ↦ inner ℝ (A x) u)
        (boundedFeasibleSet Q1 x0 (aPrioriRadiusEstimate f gamma0F x0)) xStar) :
    relativeScaleLowerValueFunction gamma0F Q1 A f x0 u =
      (inner ℝ (A xStar) u : EReal) := by
  simpa [relativeScaleLowerValueFunction, relativeScaleLowerValueProblem] using
    (relativeScaleLowerValueProblem gamma0F Q1 A f x0 u).optimalValue_eq_of_isMinOn
      hxStar hmin

end

end

/-! ### Lemma_7_14 (from Chap07) -/
noncomputable section

open scoped Gradient WithTopConvexAnalysis

universe u

/- Lemma 7.14 lies in the Chapter 7 logarithmic barrier / concave-subgradient domain.

Mandatory domain-style sampling before refinement:
- `subdifferentialWithin` and the real-valued notation `∂[Q] f(x)` in `Chap03/Theorem_3_44`, the
  canonical constrained lower-support owner for real-valued functions;
- `barrierSubgradientClass` in `Chap07/Definition_7_58`, the chapter owner for the bounded
  constrained-subgradient conclusion;
- `logarithmicTransform` in `Chap07/Definition_7_62`, the chapter owner for `x ↦ log (ψ x)`;
- mathlib `ConcaveOn.comp` together with `strictConcaveOn_log_Ioi`, the canonical concavity API
  for composing a positive concave function with `Real.log`.

Best owner abstraction:
- source-facing: the explicit gradient witness for the constrained subgradient of
  `y ↦ -logarithmicTransform ψ y` on `interior Q`, together with the bounded barrier-subgradient
  class conclusion and concavity of `logarithmicTransform ψ`;
- core/canonical: `∂[interior Q]`, `barrierSubgradientClass`, `Seminorm.dualNorm`,
  `logarithmicTransform`, and `ConcaveOn`;
- bridge/view: the sign flip from the concave logarithmic transform to the convex function
  `y ↦ -logarithmicTransform ψ y`.

Primitive data:
- the set `Q`;
- the point-indexed seminorm family `pointNorm : interior Q → Seminorm ℝ E`;
- the witnesses `hpointNorm`;
- the function `ψ`;
- the gradient existence, positivity, concavity, and canonical dual-norm bound of `ψ` on
  `interior Q`.

Derived API:
- the constrained subgradient statement together with the witness-level dual-norm bound
  `-∇ (logarithmicTransform ψ) x ∈ ∂[interior Q] (-logarithmicTransform ψ) (x)` and
  `‖-∇ (logarithmicTransform ψ) x‖ₓ* ≤ 1`;
- the bounded barrier-subgradient-class statement for `y ↦ -logarithmicTransform ψ y`;
- the concavity of `logarithmicTransform ψ` on `interior Q`.

Source/core/bridge triage:
- source-facing: the explicit logarithmic-gradient witness and the bounded barrier-subgradient
  conclusion below;
- core/canonical: `∂[interior Q]` and `barrierSubgradientClass` applied to the negated
  logarithmic transform;
- bridge/view: the sign-flip passage from the concave logarithmic transform to the constrained
  real-valued subdifferential owner.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

-- Proof sketch: differentiate `x ↦ log (ψ x)` on `interior Q`, use
-- `∇ log(ψ x) = ψ(x)⁻¹ ∇ ψ(x)`, divide the assumed dual-norm bound
-- `‖∇ ψ(x)‖ₓ* ≤ ψ(x)` by the positive value `ψ(x)`, and record the resulting witness-level bound
-- `‖-∇ (logarithmicTransform ψ) x‖ₓ* ≤ 1` for the same constrained subgradient of
-- `y ↦ -logarithmicTransform ψ y`; the barrier-subgradient-class conclusion is then the derived
-- existential corollary. For concavity, compose the concave map `ψ` on
-- `interior Q` with the concave increasing function `log` on `(0, ∞)`.
/-- Lemma 7.14: if `ψ` is concave and strictly positive on `interior Q`, and its gradient has
pointwise `pointNorm`-dual norm at most `ψ x`, then at every `x ∈ interior Q` the gradient of
`x ↦ ln (ψ x)` yields, after the standard sign flip, a constrained subgradient of
`y ↦ - ln (ψ y)` over `interior Q`, written on the chapter notation
`-∇ (logarithmicTransform ψ) x ∈
∂[interior Q] (-logarithmicTransform ψ) (x)`, and this same canonical witness has
`pointNorm`-dual norm at most `1`; equivalently the negated logarithmic transform belongs to the
barrier subgradient class with bound `1`; moreover
`x ↦ ln (ψ x)` is concave on `interior Q`. -/
theorem logarithmicTransform_has_constrained_subgradient_norm_le_one_and_concaveOn
    {Q : Set E} {ψ : E → ℝ} {pointNorm : interior Q → Seminorm ℝ E}
    (hpointNorm : ∀ x : interior Q, Seminorm.IsNorm (pointNorm x))
    (hψ_grad : ∀ x : interior Q, HasGradientAt ψ (∇ ψ x) x)
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hψ_pos : ∀ x : interior Q, 0 < ψ x)
    (hψ_dual_bound : ∀ x : interior Q,
      let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
      (pointNorm x).dualNorm (∇ ψ x) ≤ ψ x) :
    (∀ x : interior Q,
        -∇ (logarithmicTransform ψ) x ∈
          ∂[interior Q] (-logarithmicTransform ψ) (x) ∧
          (let _ : Seminorm.IsNorm (pointNorm x) := hpointNorm x
           (pointNorm x).dualNorm (-∇ (logarithmicTransform ψ) x) ≤ 1)) ∧
      (fun y ↦ -logarithmicTransform ψ y) ∈
        barrierSubgradientClass (interior Q) (interior Q) pointNorm hpointNorm 1 ∧
      ConcaveOn ℝ (interior Q) (logarithmicTransform ψ) := sorry

/-! ### Proposition_7_14 (from Chap07) -/
open scoped BigOperators Gradient

noncomputable section

universe u v

variable {ι : Type u}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 7.14 lies in the chapter's finite max-absolute-linear / symmetric log-sum-exp
smoothing domain.

Sampled owner-style declarations:
- `maxTypeObjective` in `Chap02/Lemma_2_18`, specialized to the finite objective
  `x ↦ max_i |⟪a_i, x⟫|`;
- `gradient` from `Mathlib/Analysis/Calculus/Gradient/Basic`, the canonical first-order owner on
  a real Hilbert space;
- `hessian` in `Chap01/Definition_1_4_16`, the chapter's intrinsic second-order owner.

Best owner abstraction:
- source-facing: the symmetric log-sum-exp smoothing of
  `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`;
- core/canonical: the positive-parameter finite-family smoothing owner
  `absLinearLogSumExp μ a : E → ℝ`;
- bridge/view: the gradient and Hessian formulas below.

Primitive data:
- a finite family `a : ι → E`;
- a positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the symmetric exponential summand `absLinearLogSumExpPairWeight`;
- the normalization factor `absLinearLogSumExpOmega`;
- the coefficient `absLinearLogSumExpLambda`;
- the smoothing owner `absLinearLogSumExp μ a`;
- the smoothness, gradient, and Hessian formulas.

This owner is kept at the finite-family real inner-product-space level. The coordinate model
`Fin m → EuclideanSpace ℝ (Fin n)` is a downstream specialization, not primitive data here. -/

section Definitions

/-- The `i`-th symmetric exponential term
`exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)` used in the smoothing formula. -/
def absLinearLogSumExpPairWeight
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) (x : E) : ℝ :=
  Real.exp (inner ℝ (a i) x / (μ : ℝ)) + Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))

-- Proof sketch: unfold `absLinearLogSumExpPairWeight`.
/-- Expanding `absLinearLogSumExpPairWeight μ a i x` gives the symmetric exponential summand
`exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)`. -/
theorem absLinearLogSumExpPairWeight_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) (x : E) :
    absLinearLogSumExpPairWeight μ a i x =
      Real.exp (inner ℝ (a i) x / (μ : ℝ)) + Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) := rfl

end Definitions

section FiniteFamily

variable [Fintype ι]

/-- The normalization factor
`ω_μ(x) = ∑ᵢ [exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)]`. -/
def absLinearLogSumExpOmega
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x : E) : ℝ :=
  ∑ i, absLinearLogSumExpPairWeight μ a i x

-- Proof sketch: unfold `absLinearLogSumExpOmega`.
/-- Expanding `absLinearLogSumExpOmega μ a x` gives the finite sum of the symmetric exponential
terms. -/
theorem absLinearLogSumExpOmega_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x : E) :
    absLinearLogSumExpOmega μ a x = ∑ i, absLinearLogSumExpPairWeight μ a i x := rfl

/-- The coefficient
`λ_μ⁽ⁱ⁾(x) = (exp (⟪aᵢ, x⟫ / μ) - exp (-⟪aᵢ, x⟫ / μ)) / ω_μ(x)` appearing in the gradient
representation. -/
def absLinearLogSumExpLambda
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) (x : E) : ℝ :=
  (Real.exp (inner ℝ (a i) x / (μ : ℝ)) - Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) /
    absLinearLogSumExpOmega μ a x

-- Proof sketch: unfold `absLinearLogSumExpLambda`.
/-- Expanding `absLinearLogSumExpLambda μ a i x` gives the normalized signed exponential
difference. -/
theorem absLinearLogSumExpLambda_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) (x : E) :
    absLinearLogSumExpLambda μ a i x =
      (Real.exp (inner ℝ (a i) x / (μ : ℝ)) - Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) /
        absLinearLogSumExpOmega μ a x := rfl

/-- The smoothing function
`f_μ(x) = μ log (∑ᵢ [exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)])`
for the maximal absolute value of the linear forms `x ↦ ⟪aᵢ, x⟫`. -/
def absLinearLogSumExp
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) : E → ℝ :=
  fun x ↦ (μ : ℝ) * Real.log (absLinearLogSumExpOmega μ a x)

-- Proof sketch: unfold `absLinearLogSumExp`.
/-- Evaluating `absLinearLogSumExp μ a` at `x` gives
`μ log (absLinearLogSumExpOmega μ a x)`. -/
theorem absLinearLogSumExp_apply
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x : E) :
    absLinearLogSumExp μ a x = (μ : ℝ) * Real.log (absLinearLogSumExpOmega μ a x) := rfl

-- Proof sketch: each summand in `absLinearLogSumExpOmega μ a` is a smooth exponential of a
-- linear functional, so the finite sum is `C^∞`; positivity of `μ` allows composition with
-- `log`, hence `absLinearLogSumExp μ a` is twice continuously differentiable.
/-- Proposition 7.14 (1): for `μ > 0`, the smoothing function
`f_μ(x) = μ log (∑ᵢ [exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)])`
is twice continuously differentiable on a real inner product space. -/
theorem absLinearLogSumExp_contDiff
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) :
    ContDiff ℝ 2 (absLinearLogSumExp μ a) := sorry

section Differential

variable [CompleteSpace E]

-- Proof sketch: differentiate `absLinearLogSumExp μ a x = μ log (ω_μ(x))`; the derivative of
-- `ω_μ` is the sum of the signed exponential coefficients times `aᵢ`, and dividing by `ω_μ(x)`
-- yields the coefficient `absLinearLogSumExpLambda μ a i x` in front of each `aᵢ`.
/-- Proposition 7.14 (2): for `μ > 0`, the gradient of the smoothing function is the weighted sum
`∇ f_μ(x) = ∑ᵢ λ_μ⁽ⁱ⁾(x) aᵢ`, equivalently giving the textbook pairing formula
`⟪∇ f_μ(x), h⟫ = ∑ᵢ λ_μ⁽ⁱ⁾(x) ⟪aᵢ, h⟫`. -/
theorem absLinearLogSumExp_gradient_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x : E) :
    ∇ (absLinearLogSumExp μ a) x =
      ∑ i, absLinearLogSumExpLambda μ a i x • a i := sorry

-- Proof sketch: apply the Hessian identity for `μ log (ω_μ)`:
-- `∇²(μ log ω_μ) = μ (ω_μ⁻¹ ∇²ω_μ - ω_μ⁻² ∇ω_μ ⊗ ∇ω_μ)`. Evaluating the resulting bilinear form
-- on `(h, h)` gives the weighted second-moment term minus the square of the gradient pairing.
/-- Proposition 7.14 (3): for `μ > 0`, the Hessian quadratic form of the smoothing function is
the weighted second-moment term minus the square of the gradient pairing:
`⟪∇² f_μ(x) h, h⟫`
equals the expression displayed in the textbook. -/
theorem absLinearLogSumExp_hessian_quadraticForm_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x h : E) :
    inner ℝ (hessian (absLinearLogSumExp μ a) x h) h =
      (1 / (μ : ℝ)) *
          ∑ i,
            ((inner ℝ (a i) h) ^ (2 : ℕ) / absLinearLogSumExpOmega μ a x) *
              absLinearLogSumExpPairWeight μ a i x -
        (1 / (μ : ℝ)) *
          (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ) := sorry

end Differential

end FiniteFamily

/-! ### Theorem_7_14 (from Chap07) -/
open InnerProductSpace
open scoped BigOperators Gradient HessianDualLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 7.14 lies in the Chapter 7 barrier-subgradient / self-concordant remainder domain.

Mandatory domain-style sampling:
- `HessianDualLocalNorm.ofDetNeZero F x hPos hH g` from `Chap05/Definition_5_0_20`, the owner
  surface for the determinant-based Hessian dual local norm;
- `ω_*` from `Chap05/Definition_5_0_21`, the Chapter 5 owner of the self-concordant upper
  remainder term;
- `IsSelfConcordantBarrierOnWith` from `Chap05/Definition_5_3_2`, the Chapter 5 owner that ties
  the barrier parameter `ν` to the actual barrier term `F`;
- `DualBarrierSubgradientMethod` from `Chap07/Algorithm_7_12`, the Chapter 7 source-facing owner
  of the iterates, step sizes, barrier parameters, and barrier data behind `Uβ`;
- `DualBarrierSubgradientMethod.maximalGap` and `barrierSubgradientWeightSum` from
  `Chap07/Definition_7_57`, the Chapter 7 owners of `ℓ_k⋆` and `S_k`.

Best owner abstraction:
- source-facing: Theorem 7.14's upper bound for the maximal gap of a
  `DualBarrierSubgradientMethod`;
- core/canonical: `method.maximalGap k`, `barrierSubgradientWeightSum`, `ω_*`,
  `IsSelfConcordantBarrierOnWith P ν method.F`, and the determinant-based dual-local-norm bridge;
- bridge/view: the accumulated self-concordant error term `A_k`.

Primitive data:
- the method owner `method : DualBarrierSubgradientMethod P f`;
- the barrier owner `[IsSelfConcordantBarrierOnWith P ν method.F]`, which makes `ν` the actual
  barrier complexity of `method.F`;
- the Hessian nondegeneracy data along the method iterates.

Derived API:
- the maximal gap `ℓ_k⋆` via `method.maximalGap`;
- the step sum `S_k` via `barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ))`;
- the accumulated self-concordant error `A_k` via `method.accumulatedOmegaStarError`.

The previous revision still stated the main theorem over free iterate, step-size, and smoothing
sequences together with a disconnected parameter `x₀`. This refinement keeps the auxiliary error
term, but moves the public theorem surface onto the actual Chapter 7 method owner so the initial
point is the method iterate `method 0` and the maximal gap is the established owner
`method.maximalGap`. The barrier parameter is now also tied to the actual barrier term by the
canonical Chapter 5 owner `[IsSelfConcordantBarrierOnWith P ν method.F]` instead of being a free
scalar.
-/

namespace DualBarrierSubgradientMethod

section

variable {P : Set E} {f : E → ℝ}
variable (method : DualBarrierSubgradientMethod P f)

/-- The barrier owner supplies Hessian positivity at every iterate of the method. -/
theorem iterate_hessian_isPositive
    [IsStandardSelfConcordantOn P method.F] (i : ℕ) :
    (hessian method.F (method i : E)).IsPositive :=
  (inferInstance : IsStandardSelfConcordantOn P method.F).hessian_isPositive (method i).2

/-- The accumulated barrier error term
`A_k = ∑_{i=0}^k β_i ω_* ((λ_i / β_i) ‖g_i‖*_(x_i))` for the actual Chapter 7 method data, where
`g_i` is the chosen subgradient at the iterate `x_i = method i`. The hypothesis `hω` records the
domain condition needed to evaluate `ω_*` at each stage. -/
def accumulatedOmegaStarError
    [IsStandardSelfConcordantOn P method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun i ↦
    let δi :=
      HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
        (method.iterate_hessian_isPositive i) (hH i)
        (method.dualSubgradient (method i))
    let τi : Set.Iio (1 : ℝ) := ⟨
      (method.stepSize i : ℝ) * δi / method.beta i,
      by
        have hlt : (method.stepSize i : ℝ) * δi < (method.beta i : ℝ) := by
          simpa [δi] using hω i
        exact (div_lt_iff₀ (method.beta i).2).2 (by simpa using hlt)⟩
    (method.beta i : ℝ) * ω_* τi

/-- Evaluating `method.accumulatedOmegaStarError hH hω k` gives the finite sum
`∑_{i=0}^k β_i ω_* ((λ_i / β_i) ‖g_i‖*_(x_i))` attached to the actual method data. -/
theorem accumulatedOmegaStarError_def
    [IsStandardSelfConcordantOn P method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (k : ℕ) :
    method.accumulatedOmegaStarError hH hω k =
      Finset.sum (Finset.range (k + 1)) fun i ↦
        let δi :=
          HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
            (method.iterate_hessian_isPositive i) (hH i)
            (method.dualSubgradient (method i))
        let τi : Set.Iio (1 : ℝ) := ⟨
          (method.stepSize i : ℝ) * δi / method.beta i,
          by
            exact
              (div_lt_iff₀ (method.beta i).2).2 (by
                simpa [δi] using hω i)⟩
        (method.beta i : ℝ) * ω_* τi :=
  rfl

-- Proof sketch: sum the one-step upper model for the smoothed support functions along the
-- barrier-subgradient iterates to control the accumulated `ω_*`-error by `A_k`, bound the
-- linearized value at the initial iterate `x₀ = method 0` by
-- `-3 ν S_k ‖g₀‖*_(x₀)`, and insert these estimates into the
-- logarithmic comparison bound coming from inequality `(7.3.12)`.
/-- Theorem 7.14: if the barrier-subgradient iterates `x_k ∈ P` have local ratios
`(λ_k / β_k) ‖g_k‖*_(x_k) < 1` and the smoothing parameters satisfy `β_k ≤ β_{k+1}`, then
for every `k ≥ 0` the maximal-gap owner `method.maximalGap k` is bounded by
`A_k + β_{k+1} ν [1 + 2 log (1 + sqrt (A_k / (β_{k+1} ν)) + 3 (S_k / β_{k+1}) ‖g₀‖*_(x₀))]`,
where `x₀ = method 0`, `g₀` is the chosen subgradient at `x₀`,
`S_k = ∑_{i=0}^k λ_i`, and
`A_k = ∑_{i=0}^k β_i ω_* ((λ_i / β_i) ‖g_i‖*_(x_i))`. -/
theorem maximalGap_upper_bound
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (hβ_mono : ∀ i : ℕ, (method.beta i : ℝ) ≤ method.beta (i + 1))
    (k : ℕ) :
    let A := method.accumulatedOmegaStarError hH hω k;
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k;
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0));
    method.maximalGap k ≤
      A +
        (method.beta (k + 1) : ℝ) * (ν : ℝ) *
          (1 +
            2 * Real.log
              (1 +
                Real.sqrt (A / ((method.beta (k + 1) : ℝ) * (ν : ℝ))) +
                3 * ((S / (method.beta (k + 1) : ℝ)) * δ0))) :=
  sorry

end

end DualBarrierSubgradientMethod

end
