import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

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
