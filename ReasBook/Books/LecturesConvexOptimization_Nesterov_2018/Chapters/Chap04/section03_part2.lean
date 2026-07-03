import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_3_4 (from Chap04) -/
noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 4.3.4 lies in the optimal cubic-Newton estimating-sequence domain on a finite-dimensional
real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod.psi` in `Algorithm_4_3_1`
* `OptimalCubicNewtonMethod.psi_zero` in `Algorithm_4_3_1`
* `OptimalCubicNewtonMethod.psi_succ` in `Algorithm_4_3_1`
* `CubicNewtonStep.residual` in `Definition_4_3_6`
* `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`

Best owner abstraction:
* core/canonical: `OptimalCubicNewtonMethod B Mf f x0 sigma`

Primitive data:
* the method data already stored by `OptimalCubicNewtonMethod`

Derived API:
* the estimating functions `ψ_k`
* the cubic-step residuals `r[(method.step)] (method.y k)`
* the accumulated lower-bound correction term `B_k`
* the convex lower-support inequality from `ConvexOn.lower_tangent_plane`

Source/core/bridge triage:
* source-facing: Lemma 4.3.4's lower bound
  `A_k f(x_k) + B_k ≤ ψ_k(v_k)`
* core/canonical: the owner `OptimalCubicNewtonMethod` with its `psi` recursion
* bridge/view: the scalar correction term `B_k`, derived from the method data rather than stored
  as extra primitive structure
-/

namespace OptimalCubicNewtonMethod

/-- The accumulated cubic correction term `B_k` from the estimating-sequence lower bound. -/
def estimatingLowerBoundCorrection
    {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
    [Fact B.toQuadraticMap.PosDef]
    {x0 : PrimalSpace B} {sigma : ℝ}
    (method : OptimalCubicNewtonMethod B Mf f x0 sigma) :
    ℕ → ℝ :=
  fun k ↦
    (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * ((Mf : ℝ) / sigma)) *
      Finset.sum (Finset.range k) fun i ↦
        method.A (i + 1) * (r[(method.step)] (method.y i)) ^ (3 : ℕ)

/-- The cubic correction term vanishes at the initial stage `k = 0`. -/
@[simp] theorem estimatingLowerBoundCorrection_zero
    {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
    [Fact B.toQuadraticMap.PosDef]
    {x0 : PrimalSpace B} {sigma : ℝ}
    (method : OptimalCubicNewtonMethod B Mf f x0 sigma) :
    method.estimatingLowerBoundCorrection 0 = 0 := by
  sorry

end OptimalCubicNewtonMethod

section

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 : PrimalSpace B} {sigma : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 sigma)

/-- Lemma 4.3.4: if `f` is convex and the algorithmic parameters satisfy
`r_M(y_k) ≤ ρ_k` for every `k`, then `A_k f(x_k) + B_k` is bounded above by
`ψ_k(v_k) = ψ_k^* = min_x ψ_k(x)`, where `B_k` is the accumulated cubic correction term
`((1 - σ^2) / 4) M * ∑_{i=0}^{k-1} A_{i+1} r_M(y_i)^3`. -/
-- Proof sketch: argue by induction on `k`. Use the recursion for `ψ_{k+1}`, the convexity bound
-- comparing `f(x_k)` and the linearization at `x_{k+1}`, minimize the resulting quadratic term at
-- `v_k`, apply `cubicNewtonStep_dualPairing_lower_bound_of_sigma` at `y_k`, and absorb the new
-- cubic contribution into the recursive definition of the correction term.
lemma optimalCubicNewtonMethod_accumulated_value_le_estimating_minimum
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hresidual : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ) :
    method.A k * f (method k) +
        method.estimatingLowerBoundCorrection k ≤
      method.psi k (method.v k) := sorry

end

/-! ### Proposition_4_3_4 (from Chap04) -/
noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.3.4 lies in the optimal cubic-Newton rate / scalar prefactor optimization
domain on a finite-dimensional real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod.gap_le_inverse_seven_halves_rate` in `Theorem_4_3_2`, the chapter
  owner of the inverse-`7/2` objective-gap rate for general `σ ∈ (0, 1)`;
* `OptimalCubicNewtonMethod.accumulated_weight_lower_bound` in `Lemma_4_3_5`, the predecessor
  owner theorem underlying that rate;
* mathlib `IsMinOn`, the canonical owner for the scalar minimization statement on `Set.Ioo 0 1`.

Best owner abstractions:
* core/canonical for the algorithmic estimate: `OptimalCubicNewtonMethod B Mf f x0 sigma`
* core/canonical for the scalar optimization: `IsMinOn`

Primitive data:
* the method data already bundled by `OptimalCubicNewtonMethod`
* the comparison point `xStar` and the residual factor `γ`
* the scalar prefactor `σ ↦ 2 / (σ * sqrt (1 - σ^2))`

Derived API:
* the scalar minimization at `σ = 1 / √2`
* the sharp specialization of the general rate theorem at that parameter value

Source/core/bridge triage:
* source-facing: Proposition 4.3.4's optimal-`σ` claim and the resulting sharp inverse-`7/2` rate
* core/canonical: `OptimalCubicNewtonMethod.gap_le_inverse_seven_halves_rate` and `IsMinOn`
* bridge/view: specialize the owner rate theorem to `σ = 1 / √2` and simplify the coefficient
-/

section

/-- Proposition 4.3.4, scalar part: the prefactor in Theorem 4.3.2 is minimized on `(0, 1)` at
`σ = 1 / √2`. -/
theorem inverse_seven_halves_prefactor_isMinOn :
    IsMinOn
      (fun σ : ℝ ↦
        (2 : ℝ) / (σ * Real.sqrt (1 - σ ^ (2 : ℕ))))
      (Set.Ioo (0 : ℝ) 1)
      ((1 : ℝ) / Real.sqrt 2) := sorry

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 xStar : PrimalSpace B} {γ : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 ((1 : ℝ) / Real.sqrt 2))

namespace OptimalCubicNewtonMethod

-- Proof sketch: the prefactor in Theorem 4.3.2 is the scalar function
-- `σ ↦ 2 / (σ * sqrt (1 - σ^2))` on `(0, 1)`. Differentiate this elementary function or,
-- equivalently, maximize `σ * sqrt (1 - σ^2)` on `(0, 1)` to obtain the optimizer
-- `σ = 1 / sqrt 2`. Then specialize
-- `method.gap_le_inverse_seven_halves_rate` to this value of `σ` and simplify
-- the coefficient
-- `2 / ((1 / sqrt 2) * sqrt (1 - (1 / sqrt 2)^2)) = 4`.
/-- Proposition 4.3.4, rate part: under the convexity assumptions of Theorem 4.3.2, the
right-hand-side
coefficient there is minimized at `σ = 1 / √2`; for an optimal cubic Newton method built with
this parameter, one obtains the sharp specialization
`f(x_k) - f(x^*) ≤ 4 γ^{3/2} M_f ‖x₀ - x^*‖^3 (3 / (2k + 1))^{3.5}` for every `k ≥ 1`. -/
theorem gap_le_inverse_seven_halves_rate_best_sigma
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k))
    {k : ℕ} (hk : 1 ≤ k) :
    let Δ := x0 - xStar
    f (method k) - f xStar ≤
      (((4 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
          ‖Δ‖[B] ^ (3 : ℕ)) *
        Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) := sorry

end OptimalCubicNewtonMethod

end

/-! ### Definition_4_3_5 (from Chap04) -/
noncomputable section

universe u

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm

/- Definition 4.3.5 lies in the bilinear-form / induced-seminorm / Hessian-Lipschitz domain.

Sampled owner-style declarations:
* `LinearMap.BilinForm.PrimalSpace` in `Chap04/Definition_4_2_9`
* `HasLipschitzContinuousHessian` in `Chap04/Definition_4_2_7`
* `HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le` in `Chap04/Definition_4_2_7`
* the norm notation `‖x‖[B]` on `PrimalSpace B` in `Chap04/Definition_4_2_9`

Best owner abstraction:
* source-facing: Definition 4.3.5's Hessian-Lipschitz condition in the `B`-induced geometry
* core/canonical: `HasLipschitzContinuousHessian Mf f` on `LinearMap.BilinForm.PrimalSpace B`
* bridge/view: the `B`-norm notation on `PrimalSpace B`, where the ambient norm is already
  `‖·‖[B]`

Primitive data:
* `B : BilinForm ℝ E`
* the positive-definite quadratic data of `B`
* `Mf : NNReal`
* `f : PrimalSpace B → ℝ`

Derived API:
* the canonical owner `HasLipschitzContinuousHessian Mf f`
* the textbook notation `f ∈ C22[Mf]`
* the inherited `C²` regularity projection

Once Chapter 4 has introduced the intrinsic carrier `PrimalSpace B`, Definition 4.3.5 is no
longer a place to keep a second public owner. The source condition is exactly the existing owner
`HasLipschitzContinuousHessian` on that carrier. -/

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

section

variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef]
variable {Mf : NNReal} {f : PrimalSpace B → ℝ}

/- Definition 4.3.5: on the intrinsic carrier `PrimalSpace B`, the textbook condition that the
Hessian of `f` is globally `M_f`-Lipschitz in the `B`-induced norm is exactly the chapter owner
`HasLipschitzContinuousHessian Mf f`, written on theorem surfaces as `f ∈ C22[Mf]`. -/
recall HasLipschitzContinuousHessian

set_option linter.hashCommand false in
#check (f ∈ C22[Mf])

recall HasLipschitzContinuousHessian.contDiff

end

/-! ### Lemma_4_3_5 (from Chap04) -/
noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 4.3.5 lies in the optimal cubic-Newton estimating-sequence domain on a finite-dimensional
real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod.psi` in `Algorithm_4_3_1`, the owner evaluation of the estimating
  sequence `ψ_k`;
* `OptimalCubicNewtonMethod.estimatingLowerBoundCorrection` in `Lemma_4_3_4`, the derived
  correction term `B_k` attached to a method;
* `optimalCubicNewtonMethod_accumulated_value_le_estimating_minimum` in `Lemma_4_3_4`, the
  predecessor lemma bounding `A_k f(x_k) + B_k` by `ψ_k(v_k)`;
* `CubicNewtonStep.residual` in `Definition_4_3_6`, the owner residual `r_M`.

Best owner abstraction:
* core/canonical: `OptimalCubicNewtonMethod B Mf f x0 sigma`

Primitive data:
* the method data already stored by `OptimalCubicNewtonMethod`
* the comparison point `xStar`
* the scalar sandwich factor `γ`

Derived API:
* the majorization of `ψ_k` at `xStar`
* the residual sandwich `r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)`
* the lower bound on the accumulated weights `A_k`

Source/core/bridge triage:
* source-facing: Lemma 4.3.5's quantitative lower bound on the accumulated weights `A_k`
* core/canonical: the owner `OptimalCubicNewtonMethod` and its derived correction term from
  Lemma 4.3.4
* bridge/view: the passage from the residual sandwich to a bound on the scalar recursion for
  `A_k`
-/

section

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 : PrimalSpace B} {sigma γ : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 sigma) {xStar : PrimalSpace B}

namespace OptimalCubicNewtonMethod

-- Proof sketch: combine Lemma 4.3.4 with the upper majorization of the estimating sequence at the
-- comparison point `xStar` to get the uniform correction bound
-- `method.estimatingLowerBoundCorrection k ≤ (1 / 2) ‖x₀ - xStar‖²`. Then use
-- the residual sandwich `r_M(y_i) ≤ ρ_i ≤ γ r_M(y_i)` to convert the correction bound into a
-- lower bound on `∑ i < k, ρ_i⁻¹ᐟ²`, optimize that sum under the correction constraint as in the
-- textbook Lagrange-multiplier argument, and finally bootstrap the resulting recursion in `A_k`.
/-- Lemma 4.3.5: if `f` is convex, `γ ≥ 1`, the auxiliary parameters of Algorithm 4.3.1 satisfy
`r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)` for every `k`, and the estimating functions are majorized at the
comparison point `xStar` by `A_k f(xStar) + (1 / 2) ‖x₀ - xStar‖²`, then every index `k ≥ 1`
satisfies the denominator-free accumulated-weight lower bound
`(1 / 4) (1 / γ)^(3/2) * sqrt (1 - σ^2) * ((2k + 1) / 3)^(7/2) ≤ M ‖x₀ - xStar‖ A_k`,
with `M = M_f / σ` and the norm induced by `B`. This is the textbook lower bound on `A_k`,
rewritten to avoid the degenerate totalized division artifact when `x₀ = xStar`. -/
theorem accumulated_weight_lower_bound
    (hγ : 1 ≤ γ)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k))
    {k : ℕ} (hk : 1 ≤ k) :
    let Δ := x0 - xStar
    let M : ℝ := (Mf : ℝ) / sigma
    ((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) * Real.sqrt (1 - sigma ^ (2 : ℕ))) *
        Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ) ≤
      M * ‖Δ‖[B] * method.A k := sorry

end OptimalCubicNewtonMethod

end

/-! ### Definition_4_3_6 (from Chap04) -/
open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped Gradient ConstrainedArgmin BInducedNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.3.6 lies in the bilinear-form-induced norm / cubic-Newton-step domain on complete
real inner-product spaces.

Sampled owner-style declarations:
* `LinearMap.BilinForm.primalSeminorm` in `Definition_4_3_4`, the canonical owner of the
  `B`-induced norm `‖·‖[B]`;
* `secondOrderTaylorModelAt` in `Definition_4_1_3`, the canonical owner of the quadratic Taylor
  part of the local model;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the earlier ambient-norm cubic-step owner,
  which becomes the specific comparison owner once the `B`-norm agrees with the ambient norm;
* `IsMinOn` and `argmin[Set.univ]`, the canonical global-minimizer owners on the ambient space.

Best owner abstraction:
* source-facing: the `B`-dependent cubic Newton model and the chosen step map `T_M`;
* core/canonical: `secondOrderTaylorModelAt f x` together with the `B`-induced norm
  `‖·‖[B]`;
* bridge/view: the canonical whole-space argmin membership of the chosen step values, and the
  specialization bridge to `CubicRegularizationMapping` when `B.primalSeminorm = normSeminorm`.

Primitive data:
* the bilinear form `B`;
* the objective `f`;
* the regularization parameter `M`;
* the chosen step map `T_M`.

Derived API:
* the displayed cubic Newton model with cubic term measured in the `B`-norm;
* the whole-space minimizing property of `T_M x`;
* the residual `r_M(x) = ‖T_M(x) - x‖[B]`.

Section 4.3 uses the geometry induced by `B`, so the source-facing owner cannot be collapsed to
the earlier ambient-inner-product owner `CubicRegularizationMapping`. This file therefore keeps
the `B`-dependent step layer as the public owner and derives its API directly from the canonical
Taylor-model and `B`-norm owners, while exposing a thin `toCubicRegularizationMapping` bridge for
the ambient-norm specialization. -/

/-- The cubic Newton model from Definition 4.3.6: the second-order Taylor model of `f` at `x`,
with the constant term `f x` removed and the cubic penalty measured in the `B`-induced norm. -/
def cubicNewtonModel
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → ℝ) (M : ℝ) (x : E) : E → ℝ :=
  fun T ↦ secondOrderTaylorModelAt f x T - f x + (M / 6 : ℝ) * ‖T - x‖[B] ^ (3 : ℕ)

/-- Evaluating `cubicNewtonModel B f M x` recovers the displayed cubic Newton model formula from
Definition 4.3.6. -/
theorem cubicNewtonModel_apply
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → ℝ) (M : ℝ) (x T : E) :
    cubicNewtonModel B f M x T =
      inner ℝ (∇ f x) (T - x) +
        (1 / 2 : ℝ) * inner ℝ (hessian f x (T - x)) (T - x) +
          (M / 6 : ℝ) * ‖T - x‖[B] ^ (3 : ℕ) := by
  simp [cubicNewtonModel, secondOrderTaylorModelAt_apply]
  ring

/-- If the `B`-induced seminorm owner is the ambient norm seminorm, then the `B`-dependent cubic
Newton model is exactly the earlier chapter cubic-regularization model shifted by the harmless
constant `-f x`. -/
theorem cubicNewtonModel_eq_cubicRegularizationQuadraticApproximation_sub
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (hNorm : B.primalSeminorm Fact.out = normSeminorm ℝ E)
    (f : E → ℝ) (M : ℝ) (x : E) :
    cubicNewtonModel B f M x =
      fun y ↦ cubicRegularizationQuadraticApproximation f M x y - f x := by
  funext y
  have hB : ‖y - x‖[B] = ‖y - x‖ := by
    simpa using
      congrArg (fun p : Seminorm ℝ E ↦ p (y - x)) hNorm
  rw [cubicNewtonModel_apply, cubicRegularizationQuadraticApproximation_apply, hB]
  simp [sub_eq_add_neg]
  ring

/-- Under the ambient-norm specialization `B.primalSeminorm = normSeminorm`, minimizing the
`B`-dependent cubic Newton model is equivalent to minimizing the earlier chapter cubic model. -/
theorem isMinOn_cubicNewtonModel_iff
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (hNorm : B.primalSeminorm Fact.out = normSeminorm ℝ E)
    (f : E → ℝ) (M : ℝ) (x y : E) :
    IsMinOn (cubicNewtonModel B f M x) Set.univ y ↔
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y := by
  rw [cubicNewtonModel_eq_cubicRegularizationQuadraticApproximation_sub B hNorm f M x]
  constructor
  · intro hy
    rw [isMinOn_iff] at hy ⊢
    intro z hz
    have hz' := hy z hz
    linarith
  · intro hy
    rw [isMinOn_iff] at hy ⊢
    intro z hz
    have hz' := hy z hz
    linarith

/-- Definition 4.3.6: a cubic Newton step for the `B`-induced geometry is a map `T_M : E → E`
such that, for every base point `x`, the value `T_M x` globally minimizes the `B`-dependent cubic
Newton model centered at `x`. -/
structure CubicNewtonStep
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → ℝ) (M : ℝ) where
  /-- The chosen cubic Newton step map `T_M`. -/
  toFun : E → E
  /-- For each base point `x`, the step `T_M x` globally minimizes the `B`-dependent cubic Newton
  model centered at `x`. -/
  isMinOn (x : E) :
    IsMinOn (cubicNewtonModel B f M x) Set.univ (toFun x)

namespace CubicNewtonStep

variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef] {f : E → ℝ} {M : ℝ}

/-- A cubic Newton step acts on a base point by evaluation of its chosen map `T_M`. -/
instance : CoeFun (CubicNewtonStep B f M) (fun _ ↦ E → E) where
  coe step := step.toFun

/-- Evaluating a cubic Newton step at `x` gives a global minimizer of the `B`-dependent cubic
Newton model centered at `x`. -/
theorem isMinOn_apply
    (step : CubicNewtonStep B f M) (x : E) :
    IsMinOn (cubicNewtonModel B f M x) Set.univ (step x) :=
  step.isMinOn x

/-- Evaluating a cubic Newton step at `x` gives a point of the canonical whole-space argmin set
of the `B`-dependent cubic Newton model centered at `x`. -/
theorem mem_argmin_apply
    (step : CubicNewtonStep B f M) (x : E) :
    step x ∈ argmin[Set.univ] (cubicNewtonModel B f M x) := by
  exact mem_constrainedArgmin_iff.mpr ⟨by simp, step.isMinOn_apply x⟩

/-- The cubic Newton point `T_M(x)` satisfies the canonical first-order optimality condition for
the `B`-dependent cubic Newton model centered at `x`. -/
theorem firstOrderOptimalityCondition
    (step : CubicNewtonStep B f M) (x : E) :
    fderiv ℝ (cubicNewtonModel B f M x) (step x) = 0 := by
  simpa using IsLocalMin.fderiv_eq_zero ((step.isMinOn_apply x).isLocalMin (by simp))

/-- The residual function `r_M(x) = ‖T_M(x) - x‖[B]` attached to a cubic Newton step. -/
def residual (step : CubicNewtonStep B f M) : E → ℝ :=
  fun x ↦ ‖step x - x‖[B]

/-- If the `B`-induced norm agrees with the ambient norm, a cubic Newton step specializes to the
earlier chapter cubic-regularization owner with the same chosen step map. -/
def toCubicRegularizationMapping
    (step : CubicNewtonStep B f M)
    (hNorm : B.primalSeminorm Fact.out = normSeminorm ℝ E) :
    CubicRegularizationMapping f M where
  toFun := step
  isMinOn x := (isMinOn_cubicNewtonModel_iff B hNorm f M x (step x)).1 (step.isMinOn_apply x)

/-- The specialization bridge to `CubicRegularizationMapping` keeps the same step values. -/
@[simp] theorem toCubicRegularizationMapping_apply
    (step : CubicNewtonStep B f M)
    (hNorm : B.primalSeminorm Fact.out = normSeminorm ℝ E)
    (x : E) :
    step.toCubicRegularizationMapping hNorm x = step x :=
  rfl

end CubicNewtonStep

scoped[CubicNewtonStepNotation] notation:max "r[" step:arg "]" =>
  CubicNewtonStep.residual step

scoped[CubicNewtonStepNotation] notation:max "r[" step:arg "](" x:arg ")" =>
  CubicNewtonStep.residual step x

namespace CubicNewtonStep

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef] {f : E → ℝ} {M : ℝ}

open scoped CubicNewtonStepNotation

/-- Evaluating `r[step](x)` recovers the textbook quantity `r_M(x) = ‖T_M(x) - x‖[B]`. -/
@[simp] theorem residual_apply
    (step : CubicNewtonStep B f M) (x : E) :
    r[step](x) = ‖step x - x‖[B] :=
  rfl

end CubicNewtonStep
