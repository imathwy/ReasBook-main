import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_4_2_11 (from Chap04) -/
open scoped Gradient CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u}

/- Text 4.2.11 lies in the whole-space cubic-regularization / strong-convexity quadratic-rate
domain on real Hilbert spaces.

Sampled owner-style declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model minimized by the step;
* `cubicRegularizationQuadraticApproximation_apply` in `Definition_4_1_3`, the owner expansion of
  that cubic model;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the chapter owner for a chosen cubic-step
  map together with its minimizing property;
* `HasLipschitzContinuousHessian` / `f ∈ C22[L3]` in `Definition_4_2_7`, the canonical whole-space
  Hessian-Lipschitz owner;
* `StrongConvexOn.sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn` in `Proposition_4_1_4`, the
  canonical Polyak-type gap bound used in the proof sketch.

Best owner abstraction:
* source-facing: the quadratic-decrease region from Text 4.2.11 and its invariance estimate;
* core/canonical: `CubicRegularizationMapping f (L3 : ℝ)`,
  `cubicRegularizationQuadraticApproximation f (L3 : ℝ) x`,
  `StrongConvexOn Set.univ σ f`, and `f ∈ C22[L3]`;
* bridge/view: the pointwise minimizing relation `step.isMinOn_apply x` for a chosen cubic-step
  owner, or a single trial point `T` satisfying the same owner relation.

Primitive data:
* the objective `f`;
* the strong-convexity modulus `σ`;
* the Hessian-Lipschitz constant `L3`;
* the global minimizer witness `IsMinOn f Set.univ xStar`;
* for the one-step gap lemmas, a cubic-model minimizing witness
  `IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T`;
* for the region invariance theorem, the chosen step owner
  `CubicRegularizationMapping f (L3 : ℝ)`.

Derived API:
* the displayed cubic model itself, reused directly from `Definition_4_1_3`;
* the whole-space `C22[L3]` smoothness owner instead of repeating `ContDiff` and a raw Hessian
  Lipschitz predicate;
* the quadratic-decrease region and its invariance theorem.

This refinement removes the duplicate local wrapper `cubicStepObjective`, rewrites the theorem
surface directly on the chapter owners `m[f; (L3 : ℝ)](x)` and `C22[L3]`, and replaces the raw
pair `(stepMap, hstep)` by the existing owner `CubicRegularizationMapping f (L3 : ℝ)`. The
quadratic-decrease region remains the source-facing declaration owned by this file. -/

section CubicRegularization

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.11 uses the existing Chapter 4 cubic-model owner and its expansion directly; this file
keeps no parallel local copy. -/
recall cubicRegularizationQuadraticApproximation
recall cubicRegularizationQuadraticApproximation_apply

end CubicRegularization

/-- The sublevel set on which the cubic-Newton gap estimate has coefficient at most `1`. It is
written in the multiplication form `2 L₃² (f x - f xStar) ≤ σ³`, which avoids division-by-zero
artifacts when `L₃ = 0`. -/
def cubicNewtonQuadraticDecreaseRegion
    (f : E → ℝ) (xStar : E) (σ : ℝ) (L3 : NNReal) : Set E :=
  {x | (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ ^ (3 : ℕ)}

-- Proof sketch: unfold `cubicNewtonQuadraticDecreaseRegion`.
/-- Membership in `cubicNewtonQuadraticDecreaseRegion f xStar σ L3` is exactly the displayed
sublevel inequality `2 L₃² (f x - f xStar) ≤ σ³`. -/
theorem mem_cubicNewtonQuadraticDecreaseRegion
    {f : E → ℝ} {xStar x : E} {σ : ℝ} {L3 : NNReal} :
    x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3 ↔
      (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ ^ (3 : ℕ) :=
  Iff.rfl

section CubicRegularization

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: combine strong convexity with the Polyak-type estimate
-- `f T - f xStar ≤ (1 / (2 * σ)) ‖∇ f T‖²`, apply Text 4.2.8 (1) with `M = L₃` to bound
-- `‖∇ f T‖` by `L₃ ‖x - T‖²`, and then use Text 4.2.8 (2) with `M = L₃` to convert
-- `‖x - T‖²` into the objective drop `f x - f T`.
/-- For a cubic-step minimizer `T`, the next optimality gap is bounded by the square of the
current one-step objective decrease. -/
theorem cubicStep_gap_le_square_of_objective_drop
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {xStar x T : E} (hxStar : IsMinOn f Set.univ xStar)
    (hT : IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T) :
    f T - f xStar ≤
      ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f T) ^ (2 : ℕ) := sorry

-- Proof sketch: apply `cubicStep_gap_le_square_of_objective_drop`, then use
-- `f xStar ≤ f T` from `hxStar` to get `f x - f T ≤ f x - f xStar`.
/-- For a cubic-step minimizer `T`, the next optimality gap is bounded by a quadratic function of
the current optimality gap. -/
theorem cubicStep_gap_le_square_of_current_gap
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {xStar x T : E} (hxStar : IsMinOn f Set.univ xStar)
    (hT : IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T) :
    f T - f xStar ≤
      ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f xStar) ^ (2 : ℕ) := sorry

-- Proof sketch: for `x` in the displayed set, the defining inequality gives
-- `((2 * L₃²) / σ³) * (f x - f xStar) ≤ 1`. Combine this with
-- `cubicStep_gap_le_square_of_current_gap` to show
-- `f (step x) - f xStar ≤ f x - f xStar`, then rewrite the latter inequality back as
-- membership in `cubicNewtonQuadraticDecreaseRegion f xStar σ L3`.
/-- Text 4.2.11: if `f ∈ C22[L3]` is `σ`-strongly convex and `step` is a cubic regularization
mapping with parameter `L₃`, then
`f (step x) - f xStar ≤ (2 L₃² / σ³) (f x - f (step x))² ≤ (2 L₃² / σ³) (f x - f xStar)²`; in
particular, the sublevel set `{x | 2 L₃² (f x - f xStar) ≤ σ³}` is invariant and is a region of
quadratic decrease for `step`. -/
theorem cubicNewton_quadraticDecreaseRegion
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (step : CubicRegularizationMapping f (L3 : ℝ))
    {x : E} (hx : x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3) :
    step x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3 ∧
      f (step x) - f xStar ≤
        ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f xStar) ^ (2 : ℕ) := sorry

end CubicRegularization

/-! ### Definition_4_2_12 (from Chap04) -/
open scoped Gradient
open scoped ConstrainedArgmin
open scoped CubicRegularizationResidual
open scoped CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.2.12 lies in the cubic-regularization / unconstrained minimizer domain on
complete real inner-product spaces.

Sampled owner-style declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner of the
  cubic model `y ↦ f₂(x; y) + (M / 6) ‖y - x‖³`;
* `IsMinOn` in mathlib, the canonical global-minimizer owner on the ambient space;
* `argmin[Set.univ]` in `Chap01/Definition_1_3_3`, the set-valued constrained-argmin bridge built
  from feasibility and `IsMinOn`;
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator used in the displayed
  stationarity equation;
* `CubicNewtonEstimatingSequence.x_isMin` in `Definition_4_2_14`, a nearby source-facing owner
  that also stores chosen whole-space minimizers through `IsMinOn`.

Source/core/bridge triage:
* source-facing: the cubic regularization mapping `T_M : E → E`;
* core/canonical: the chosen-minimizer owner
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (T_M x)`;
* bridge/view: membership in `argmin[Set.univ] (cubicRegularizationQuadraticApproximation f M x)`
  and the first-order optimality equation for the value `T_M x`.

Primitive data:
* the objective `f`;
* the regularization parameter `M`;
* the chosen map `T_M`.

Derived API:
* the canonical whole-space minimizer relation for `T_M x`;
* membership of `T_M x` in the cubic-model argmin set;
* the stationarity equation under the primitive self-adjointness condition on `hessian f x`,
  and hence under the canonical `C²` bridge
  `hessian_isSelfAdjoint_of_contDiffAt`
  `∇ f(x) + ∇² f(x)(T_M(x) - x) + (M / 2) ‖T_M(x) - x‖ (T_M(x) - x) = 0`.

Positivity of `M` is not primitive data of the owner here: it matters only in separate existence /
coercivity results for the cubic model, not in the definition of a chosen minimizer map once the
argmin property is already supplied.

This file therefore keeps the source-facing owner as a chosen map together with its canonical
whole-space minimizer property, while reusing `argmin[Set.univ]` only as the derived set-valued
bridge exposed elsewhere in the chapter. -/

/- Definition 4.2.12: a cubic regularization mapping for `f` with parameter `M` is a map
`T_M : E → E` such that, for every base point `x`, the value `T_M x` globally minimizes the cubic
model
`cubicRegularizationQuadraticApproximation f M x = (y ↦ f₂(x; y) + (M / 6) ‖y - x‖^3)`. -/
structure CubicRegularizationMapping (f : E → ℝ) (M : ℝ) where
  /-- The cubic regularization map `T_M`. -/
  toFun : E → E
  /-- For each base point `x`, `T_M x` globally minimizes the cubic model centered at `x`. -/
  isMinOn (x : E) :
    IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (toFun x)

namespace CubicRegularizationMapping

variable {f : E → ℝ} {M : ℝ}

/-- A cubic regularization mapping acts on a base point by evaluation of its underlying map. -/
instance : CoeFun (CubicRegularizationMapping f M) (fun _ ↦ E → E) where
  coe T := T.toFun

-- Proof sketch: this is exactly the `isMinOn` field of the structure.
/-- Evaluating a cubic regularization mapping at `x` gives a global minimizer of
`cubicRegularizationQuadraticApproximation f M x`. -/
theorem isMinOn_apply
    (T : CubicRegularizationMapping f M) (x : E) :
    IsMinOn (m[f; M](x)) Set.univ (T x) :=
  T.isMinOn x

-- Proof sketch: combine `isMinOn_apply` with `mem_constrainedArgmin_iff`, using that the feasible
-- set is `Set.univ`.
/-- Evaluating a cubic regularization mapping at `x` gives a point of the canonical whole-space
argmin set of the cubic model centered at `x`. -/
theorem mem_argmin_apply
    (T : CubicRegularizationMapping f M) (x : E) :
    T x ∈ argmin[Set.univ] (m[f; M](x)) := by
  exact mem_constrainedArgmin_iff.mpr ⟨by simp, T.isMinOn_apply x⟩

/-- The residual function `r_M` attached to a cubic regularization mapping. -/
def residual (T : CubicRegularizationMapping f M) : E → ℝ :=
  fun x ↦ r[T x] x

/-- Evaluating `T.residual` recovers the textbook formula `r_M(x) = ‖T_M(x) - x‖`. -/
@[simp] theorem residual_apply
    (T : CubicRegularizationMapping f M) (x : E) :
    T.residual x = ‖T x - x‖ := by
  simp [residual, norm_sub_rev]

end CubicRegularizationMapping

-- Proof sketch: apply the first-order optimality condition for a global minimizer of
-- `cubicRegularizationQuadraticApproximation f M x`; when `hessian f x` is self-adjoint, the
-- derivative of the quadratic term is `hessian f x (y - x)`, while the cubic term contributes
-- `((M / 2) * ‖y - x‖) • (y - x)`.
/-- If `hessian f x` is self-adjoint, then a global minimizer of the cubic model centered at `x`
satisfies the textbook stationarity equation. -/
theorem cubicRegularization_firstOrderOptimalityCondition_of_isMinOn_of_isSelfAdjoint
    {x y : E}
    (hH : IsSelfAdjoint (hessian f x))
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    ∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x) = 0 := sorry

-- Proof sketch: first obtain self-adjointness of `hessian f x` from
-- `hessian_isSelfAdjoint_of_contDiffAt`, then apply the self-adjoint owner theorem above.
/-- If `f` is `C²` at `x`, then a global minimizer of the cubic model centered at `x` satisfies
the textbook stationarity equation. -/
theorem cubicRegularization_firstOrderOptimalityCondition_of_isMinOn
    {x y : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    ∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x) = 0 := by
  exact cubicRegularization_firstOrderOptimalityCondition_of_isMinOn_of_isSelfAdjoint
    (hessian_isSelfAdjoint_of_contDiffAt f x hf) hy

/-- If `f` is `C²` at `x`, then any point of `argmin[Set.univ] (m[f; M](x))` satisfies the
textbook stationarity equation for the cubic model centered at `x`. -/
theorem cubicRegularization_firstOrderOptimalityCondition_of_mem_argmin
    {x y : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hy : y ∈ argmin[Set.univ] (m[f; M](x))) :
    ∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x) = 0 := by
  exact cubicRegularization_firstOrderOptimalityCondition_of_isMinOn
    hf (mem_constrainedArgmin_iff.mp hy).2

namespace CubicRegularizationMapping

-- Proof sketch: combine `T.isMinOn_apply x` with the `C²` stationarity theorem
-- `cubicRegularization_firstOrderOptimalityCondition_of_isMinOn`.
/-- If `f` is `C²` at `x`, then the cubic-regularization point `T x` satisfies the textbook
stationarity equation for the cubic model centered at `x`. -/
theorem firstOrderOptimalityCondition
    (T : CubicRegularizationMapping f M) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    ∇ f x + hessian f x (T x - x) + ((M / 2 : ℝ) * ‖T x - x‖) • (T x - x) = 0 :=
  cubicRegularization_firstOrderOptimalityCondition_of_isMinOn hf (T.isMinOn_apply x)

end CubicRegularizationMapping

/-! ### Text_4_2_12 (from Chap04) -/
open scoped Gradient
open NewtonSystem (AdmissiblePoint step)

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.12 lies in the real-Hilbert-space Newton / Hessian-Lipschitz domain.

Sampled owner declarations:
* `StrongConvexOn` in `Chap03/Definition_3_2_2`, the chapter owner for whole-space strong
  convexity
* `strongConvexOn_iff_hessian_lower_bound` in `Chap02/Definition_2_15`, the chapter bridge from
  the textbook Hessian quadratic-form lower bound to `StrongConvexOn`
* `NewtonSystem.AdmissiblePoint` and `NewtonSystem.step` in `Chap01/Algorithm_1_7_1`, the owner
  Newton domain and update for the stationarity system `∇ f = 0`
* `HasLipschitzContinuousHessian L3 f` and the notation `f ∈ C22[L3]` in `Definition_4_2_7`,
  the chapter owner for `C²` regularity plus global Hessian-Lipschitz control

Source/core/bridge triage:
* source-facing: the quadratic-gradient threshold region and the resulting Newton-step estimate
  from Text 4.2.12
* core/canonical: `StrongConvexOn Set.univ σ2 f`, `NewtonSystem.AdmissiblePoint (∇ f)`,
  `NewtonSystem.step (∇ f)`, and `f ∈ C22[L3]`
* bridge/view: the admissibility bridge from whole-space strong convexity plus `C²` regularity to
  `AdmissiblePoint (∇ f)`, while the quadratic-decrease estimate itself still uses `f ∈ C22[L3]`

Primitive data:
* a modulus `σ2`
* a Hessian-Lipschitz constant `L3`
* a function `f`
* the owner hypotheses `StrongConvexOn Set.univ σ2 f` and `f ∈ C22[L3]`
* for the admissibility bridge only, the weaker `C²` datum supplied by `hf_hessian.contDiff`

Derived API:
* the admissible-point witness for the Newton system `∇ f = 0`, exposed at the weaker
  strong-convexity-plus-`C²` layer
* the canonical Newton update `NewtonSystem.step (∇ f)`
* the quadratic-gradient threshold region and the decrease estimate on that region

The previous file introduced a second public owner for the Hessian lower bound and rebuilt the
Newton step from a local inverse-Hessian equivalence. This refinement keeps the source-facing
threshold region, states the main result directly on the canonical strong-convexity and
Newton-system owners, and keeps the admissibility bridge at the weaker `C²` layer needed for
Hessian nondegeneracy rather than at the full `C22[L3]` layer. -/

/-- The gradient-based threshold region `𝒬_g` from Text 4.2.12, written in multiplication form so
that the degenerate case `L₃ = 0` still gives the intended whole-space threshold. -/
def quadraticGradientRegion
    (f : E → ℝ) (σ2 : ℝ) (L3 : NNReal) : Set E :=
  {x | 4 * (L3 : ℝ) * ‖∇ f x‖ ≤ σ2 ^ (2 : ℕ)}

-- Proof sketch: unfold `quadraticGradientRegion`.
/-- Membership in `quadraticGradientRegion f σ₂ L₃` is exactly the threshold inequality
`4 L₃ ‖∇ f(x)‖ ≤ σ₂²`. -/
theorem mem_quadraticGradientRegion_iff
    {f : E → ℝ} {σ2 : ℝ} {L3 : NNReal} {x : E} :
    x ∈ quadraticGradientRegion f σ2 L3 ↔
      4 * (L3 : ℝ) * ‖∇ f x‖ ≤ σ2 ^ (2 : ℕ) :=
  Iff.rfl

section

variable [FiniteDimensional ℝ E]

namespace StrongConvexOn

private theorem gradient_det_ne_zero
    {σ2 : ℝ} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_C2 : ContDiff ℝ 2 f) (x : E) :
    (fderiv ℝ (∇ f) x).det ≠ 0 := by
  sorry

/-- Whole-space strong convexity and `C²` regularity canonically place every point in the
admissible Newton domain for the stationarity system `∇ f = 0`. -/
abbrev admissiblePoint
    {σ2 : ℝ} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_C2 : ContDiff ℝ 2 f) (x : E) :
    AdmissiblePoint (∇ f) :=
  ⟨x, hf.gradient_det_ne_zero hσ2 hf_C2 x⟩

-- Proof sketch: fix `x` in the threshold region, write the Newton step as
-- `T = NewtonSystem.step (∇ f) x`, use the integral Hessian remainder formula together with the
-- `L₃`-Lipschitz bound on `x ↦ ∇² f(x)` to estimate `‖∇ f(T)‖`, and use strong convexity to
-- control the inverse Hessian norm by `σ₂⁻¹`.
/-- Text 4.2.12: if `f ∈ C22[L₃]` is `σ₂`-strongly convex on `Set.univ`, then every point `x`
in the threshold region `𝒬_g = {x : 4 L₃ ‖∇ f(x)‖ ≤ σ₂²}` satisfies the quadratic gradient
decrease estimate
`‖∇ f(T(x))‖ ≤ (4 L₃ / σ₂²) ‖∇ f(x)‖²`
for the canonical Newton step `T(x) = NewtonSystem.step (∇ f) x` at the admissible point
supplied by `hf.admissiblePoint hσ₂ hf_hessian.contDiff x`. Under `f ∈ C22[L₃]`, this is the
canonical-owner reformulation of the textbook Hessian-lower-bound statement from
Definition 2.15. In this Hilbert-space formalization the textbook dual norm is identified with
the ambient norm. -/
theorem gradient_norm_newton_step_quadratic_decrease_on_region
    {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_hessian : f ∈ C22[L3])
    (x : E) (hx : x ∈ quadraticGradientRegion f σ2 L3) :
    ‖∇ f (step (∇ f) (hf.admissiblePoint hσ2 hf_hessian.contDiff x))‖ ≤
      (4 * (L3 : ℝ) / σ2 ^ (2 : ℕ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  sorry

end StrongConvexOn

end

/-! ### Definition_4_2_13 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped CubicRegularizationModelNotation

/- Definition 4.2.13 lies in the chapter cubic-regularization / model-value domain.

Sampled owner declarations:
* `secondOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the upstream quadratic owner whose
  cubic penalization is already packaged in Chapter 4;
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model, with source-facing notation `m[f; M](x; y)`;
* `cubicRegularizationProblem` in `Definition_4_1_3`, the source-facing whole-space minimization
  problem for the cubic model;
* `Φ[f; M](x)`, the Chapter 4 canonical owner for `Φ_M(x)`;
* `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn` in `Definition_4_1_3`, the
  attained-minimum bridge back to the textbook real value.

Best owner abstraction:
* source-facing: `cubicRegularizationProblem f M x`;
* core/canonical: `Φ[f; M](x)`;
* bridge/view: `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`.

Primitive data:
* `f`
* `M`
* `x`

Derived API:
* the owner optimal value `Φ[f; M](x)`
* realization of its real part at a minimizing trial point via
  `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`

Source/core/bridge triage:
* source-facing: the textbook cubic-regularized proximal value `Φ_M(x)`
* core/canonical: `Φ[f; M](x)`
* bridge/view: `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`

Definition 4.2.13 adds no new owner beyond Definition 4.1.3: the previous local
`cubicRegularizationProximalValue` and `cubicRegularizationProximalValue_eq_of_isMinOn`
duplicated that exact owner interface. This file therefore keeps only the canonical recall/use
surface. -/

section

variable (f : E → ℝ) (M : ℝ) (x T : E)

/- Definition 4.2.13: the cubic-regularized proximal problem at `x` is the source-facing owner
`cubicRegularizationProblem f M x`, and `Φ_M(x)` is its canonical optimal value. -/
recall cubicRegularizationProblem

/- Any global minimizer of the cubic model realizes `Φ_M(x)` through the existing owner theorem
`cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`. -/
recall cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn

set_option linter.hashCommand false in
#check (Φ[f; M](x) : EReal)

set_option linter.hashCommand false in
#check (f̄[f; M](x) : ℝ)

set_option linter.hashCommand false in
#check
  (show
      IsMinOn (m[f; M](x)) Set.univ T →
        f̄[f; M](x) = m[f; M](x; T) from
    cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn)

end

/-! ### Text_4_2_13 (from Chap04) -/
open scoped BigOperators Gradient
open StrongConvexAcceleratedCubicNewton

noncomputable section

universe u

variable {E : Type u}

/- Text 4.2.13 lies in the strongly-convex accelerated cubic-Newton / quadratic-entry domain on
real Hilbert spaces.

Sampled owner declarations:
* `StrongConvexAcceleratedCubicNewton.stageRadius`, `stageLength`, `stageSteps`, and `method` in
  `Algorithm_4_2_4`, the chapter owners for the multistage restart schedule and outer orbit;
* `cubicNewtonQuadraticDecreaseRegion` in `Text_4_2_11`, the nearby source-facing region owner
  for a quadratic regime, written in multiplication form to avoid division-by-zero artifacts;
* `quadraticGradientRegion` in `Text_4_2_12`, the nearby source-facing threshold-region owner for
  Newton dynamics, again written in multiplication form;
* `StrongConvexOn` together with `f ∈ C22[L3]`, the canonical whole-space strong-convexity and
  Hessian-Lipschitz owners used by the surrounding chapter API.

Best owner abstraction:
* source-facing: the quadratic-entry region for the multistage accelerated cubic-Newton orbit and
  the first stage index at which the orbit enters that region;
* core/canonical: `StrongConvexAcceleratedCubicNewton.method` and the region set itself;
* bridge/view: the pointwise membership and least-entry-set expansion.

Primitive data:
* the objective `f`;
* the minimizer `xStar`;
* the strong-convexity modulus `σ₂`;
* the Hessian-Lipschitz constant `L₃`;
* the multistage outer orbit data coming from `StrongConvexAcceleratedCubicNewton.method`.

Derived API:
* the quadratic-entry region inequality, kept in multiplication form
  `8 L₃² (f x - f xStar) ≤ σ₂³`;
* the predicate that stage `k` has entered that region;
* the canonical least-entry witness `IsLeast {k | ...}` and the logarithmic stage bound.

The previous version organized the file around one-off scalar threshold / stage-bound definitions.
This refinement follows the region-style owner pattern already used nearby in Chapter 4: the public
surface is the quadratic-entry region and the corresponding least stage index at which the
multistage orbit enters it, while the displayed scalar inequalities appear only as defining
formulas inside that owner API. -/

/-- The quadratic-entry region for Text 4.2.13, written in multiplication form so that the
degenerate case `L₃ = 0` still gives the intended whole-space threshold region. -/
def strongConvexAcceleratedCubicNewtonQuadraticRegion
    (f : E → ℝ) (xStar : E) (σ2 : ℝ) (L3 : NNReal) : Set E :=
  {x | (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ2 ^ (3 : ℕ)}

-- Proof sketch: unfold `strongConvexAcceleratedCubicNewtonQuadraticRegion`.
/-- Membership in `strongConvexAcceleratedCubicNewtonQuadraticRegion f xStar σ₂ L₃` is exactly
the quadratic-entry inequality `8 L₃² (f x - f xStar) ≤ σ₂³`. -/
theorem mem_strongConvexAcceleratedCubicNewtonQuadraticRegion_iff
    {f : E → ℝ} {xStar x : E} {σ2 : ℝ} {L3 : NNReal} :
    x ∈ strongConvexAcceleratedCubicNewtonQuadraticRegion f xStar σ2 L3 ↔
      (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ2 ^ (3 : ℕ) :=
  Iff.rfl

section

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {L3 : NNReal}

/-- `InStrongConvexAcceleratedCubicNewtonQuadraticRegion xStar innerMethod σ₂ R y₀ k` means that
the `k`th outer-stage iterate of Algorithm 4.2.4 has entered the quadratic region from
Text 4.2.13. -/
def InStrongConvexAcceleratedCubicNewtonQuadraticRegion
    (xStar : E)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) (k : ℕ) : Prop :=
  method innerMethod σ2 R y0 k ∈
    strongConvexAcceleratedCubicNewtonQuadraticRegion f xStar σ2 L3

-- Proof sketch: unfold `InStrongConvexAcceleratedCubicNewtonQuadraticRegion`.
/-- Expanding `InStrongConvexAcceleratedCubicNewtonQuadraticRegion` says exactly that the `k`th
outer iterate satisfies `8 L₃² (f(y_k) - f(x^*)) ≤ σ₂³`. -/
theorem inStrongConvexAcceleratedCubicNewtonQuadraticRegion_iff
    (xStar : E)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) (k : ℕ) :
    InStrongConvexAcceleratedCubicNewtonQuadraticRegion xStar innerMethod σ2 R y0 k ↔
      (8 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) *
          (f (method innerMethod σ2 R y0 k) - f xStar) ≤
        σ2 ^ (3 : ℕ) :=
  Iff.rfl

-- Proof sketch: prove by induction that `‖method innerMethod σ₂ R y₀ k - xStar‖ ≤ R / 2^k`
-- using strong convexity together with
-- `acceleratedCubicRegularization_gap_le_inverse_cubic_rate` applied to the restarted inner owner
-- `innerMethod (method innerMethod σ₂ R y₀ k)` at the scheduled stage length
-- `stageSteps σ₂ L₃ R k`. The owner lower bound `stageLength σ₂ L₃ R k ≤ stageSteps σ₂ L₃ R k`
-- yields the factor `1 / 2`. Then deduce the gap contraction
-- `f (method innerMethod σ₂ R y₀ (k + 1)) - f xStar ≤
--    (1 / 4) * (f (method innerMethod σ₂ R y₀ k) - f xStar)`,
-- iterate this recurrence from the initial cubic upper bound, and solve the threshold inequality
-- `8 L₃² (f (method innerMethod σ₂ R y₀ N) - f xStar) ≤ σ₂³` for `N`. Since the least-entry
-- formulation allows the initial stage `N = 0`, the final real-valued stage bound is
-- clamped below by `0`.
/-- Text 4.2.13 (1): if `f ∈ C22[L₃]` is `σ₂`-strongly convex on `Set.univ`, and the canonical
multistage accelerated cubic-Newton method from Algorithm 4.2.4 started at `y₀` satisfies
`‖y₀ - x^*‖ ≤ R`, then the first stage index `N` whose outer iterate enters the quadratic region
`{x | 8 L₃² (f x - f xStar) ≤ σ₂³}` satisfies
`N ≤ max 0 ((1 / log 4) * log (((8 / 3) * (L₃ R)^3) / σ₂^3))`. The `max 0` is the stage-zero-safe
reformulation of the textbook logarithmic estimate for the natural-number stage indexing used by
`StrongConvexAcceleratedCubicNewton.method`. Under `f ∈ C22[L₃]`, this is the canonical-owner
reformulation of the textbook Hessian-lower-bound hypothesis. -/
theorem strongConvexAcceleratedCubicNewton_firstQuadraticRegionIndex_le_stageBound
    {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ} {xStar y0 : E}
    (hσ2 : 0 < σ2)
    (hf_strong : StrongConvexOn Set.univ σ2 f)
    (hxStar : IsMinOn f Set.univ xStar)
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    {R : ℝ} (hR : 0 ≤ R)
    (hy0 : ‖y0 - xStar‖ ≤ R)
    {N : ℕ}
    (hN :
      IsLeast
        {k : ℕ |
          InStrongConvexAcceleratedCubicNewtonQuadraticRegion
            xStar innerMethod σ2 R y0 k}
        N) :
    (N : ℝ) ≤
      max 0
        (Real.log ((((8 / 3 : ℝ) * (((L3 : ℝ) * R) ^ (3 : ℕ))) / σ2 ^ (3 : ℕ))) /
          Real.log 4) := sorry

private theorem strongConvexAcceleratedCubicNewton_stageLengthRatio_abs_lt_one :
    |((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ)| < 1 := by
  rw [abs_of_pos]
  · have hpow : 1 < Real.rpow (2 : ℝ) (1 / 3 : ℝ) := by
      apply Real.one_lt_rpow
      · norm_num
      · norm_num
    exact inv_lt_one_of_one_lt₀ hpow
  · exact inv_pos.2 (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _)

-- Proof sketch: iterate `stageLength_succ` to express the source schedule
-- `m_k = stageLength σ₂ L₃ R k` as the geometric progression `m_k = m₀ · 2^{-k / 3}`.
/-- For `σ₂ > 0` and `R ≥ 0`, the source stage lengths of Algorithm 4.2.4 form the geometric
progression `m_k = m₀ · 2^{-k / 3}`. -/
theorem strongConvexAcceleratedCubicNewton_stageLength_eq_firstStageLength_mul_ratio_pow
    {σ2 : ℝ} {L3 : NNReal} {R : ℝ}
    (hσ2 : 0 < σ2) (hR : 0 ≤ R) (k : ℕ) :
    stageLength σ2 L3 R k =
      stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k hk =>
      rw [stageLength_succ k hσ2 hR, hk]
      ring_nf

-- Proof sketch: combine the geometric closed form for `stageLength` with the canonical real
-- geometric-series identity `∑' k, ρ^k = (1 - ρ)⁻¹` for `ρ = 2^{-1 / 3}`.
/-- Text 4.2.13 (2): for the source stage schedule `m_k = stageLength σ₂ L₃ R k` of
Algorithm 4.2.4 with `σ₂ > 0` and `R ≥ 0`, the total stage-length budget is summable and equals
`m₀ / (1 - 2^{-1 / 3})`. This is the exact real source-schedule estimate; the discrete Newton
counts used by the algorithm remain `stageSteps σ₂ L₃ R k = ⌈m_k⌉₊`. -/
theorem strongConvexAcceleratedCubicNewton_totalStageLength_eq_geometricFactor_mul_firstStageLength
    {σ2 : ℝ} {L3 : NNReal} {R : ℝ}
    (hσ2 : 0 < σ2) (hR : 0 ≤ R) :
    Summable (stageLength σ2 L3 R) ∧
      ∑' k, stageLength σ2 L3 R k =
        stageLength σ2 L3 R 0 * (1 - (Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹)⁻¹ := by
  have hgeom :
      Summable (fun k : ℕ ↦ ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one
      strongConvexAcceleratedCubicNewton_stageLengthRatio_abs_lt_one
  have hsum :
      Summable
        (fun k : ℕ ↦ stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k) :=
    hgeom.mul_left _
  have hstage :
      stageLength σ2 L3 R =
        fun k : ℕ ↦ stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k := by
    funext k
    exact strongConvexAcceleratedCubicNewton_stageLength_eq_firstStageLength_mul_ratio_pow
      hσ2 hR k
  refine ⟨?_, ?_⟩
  · have h := hsum
    rwa [← hstage] at h
  · have htsum :
        ∑' k, stageLength σ2 L3 R 0 * ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ) ^ k =
          stageLength σ2 L3 R 0 * (1 - ((Real.rpow (2 : ℝ) (1 / 3 : ℝ))⁻¹ : ℝ))⁻¹ := by
        rw [tsum_mul_left,
          tsum_geometric_of_abs_lt_one
            strongConvexAcceleratedCubicNewton_stageLengthRatio_abs_lt_one]
    have h := htsum
    rwa [← hstage] at h

end

end

/-! ### Definition_4_2_14 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 4.2.14 lies in the chapter's cubic-regularized estimating-sequence domain.

Sampled owner-style declarations:
* `IsEstimatingSequence` in `Chap02/Definition_2_21`, the chapter's generic upper-model owner for
  estimating sequences;
* `AcceleratedCubicNewtonMethod` in `Algorithm_4_2_2`, which packages a sequence of estimating
  functions together with minimizing points;
* `OptimalCubicNewtonMethod` in `Algorithm_4_3_1`, the same owner pattern for the optimal cubic
  Newton scheme;
* `sampledAffineMinorant` in `Chap03/Proposition_3_26`, which uses the canonical affine-map owner
  `E →ᵃ[ℝ] ℝ` for affine lower models with constant terms.

Best owner abstraction:
* source-facing: `CubicNewtonEstimatingSequence f x0 L3 C`, because Definition 4.2.14 adds the
  cubic-specific recursion and minimizing data, not just a bare Chapter 2 estimating-sequence
  inequality;
* core/canonical for the noncubic part of `ψ_k`: the affine-map owner `E →ᵃ[ℝ] ℝ`, since the
  chapter's initialization and affine-gradient updates include constant terms;
* bridge/view: `cubicNewtonEstimatingFunction affinePart C x0`, whose pointwise expansion
  recovers the textbook formula.

Primitive data:
* the affine parts `ℓ_k`;
* the points `x_k`;
* the scales `A_k` and increments `a_k`;
* the recursion `A_{k+1} = A_k + a_k`;
* the minimizing property and the two source inequalities.

Derived API:
* the estimating-function family `ψ_k` itself, obtained canonically from `affinePart`, `C`, and
  `x0`;
* pointwise expansion of `ψ_k`;
* convenient theorems phrased with the coercion `sequence k x`.

Refinement outcome:
* keep the source-facing structure;
* widen the noncubic owner from linear maps to the canonical affine-map owner `E →ᵃ[ℝ] ℝ`;
* use `cubicNewtonEstimatingFunction` and the coercion as the public surface.
-/

/-- The cubic estimating functions built from a sequence of affine parts `ℓ_k`, a base point `x0`,
and a cubic regularization parameter `C`. This is the stagewise cubic regularization owner from
Definition 4.2.16 applied to the affine parts `ℓ_k`, with parameter `C / 2` so that the penalty
term is `(C / 6) ‖x - x0‖^3`. -/
abbrev cubicNewtonEstimatingFunction
    (affinePart : ℕ → E →ᵃ[ℝ] ℝ) (C : ℝ) (x0 : E) :
    ℕ → E → ℝ :=
  fun k ↦ cubicallyRegularizedObjective (affinePart k) (C / 2) x0

/-- Evaluating the cubic-Newton estimating function at stage `k` recovers
`ℓ_k(x) + (C / 6) ‖x - x0‖^3`. -/
@[simp] theorem cubicNewtonEstimatingFunction_apply
    (affinePart : ℕ → E →ᵃ[ℝ] ℝ) (C : ℝ) (x0 : E) (k : ℕ) (x : E) :
    cubicNewtonEstimatingFunction affinePart C x0 k x =
      affinePart k x + (C / 6) * ‖x - x0‖ ^ (3 : ℕ) := by
  rw [cubicNewtonEstimatingFunction, cubicallyRegularizedObjective_apply]
  ring

/-- Definition 4.2.14: a cubic-Newton estimating sequence for `f`, centered at `x0` with cubic
parameter `C` and Hessian-Lipschitz constant `L3`, consists of affine parts `ℓ_k`, points `x_k`,
scales `A_k`, and increments `a_k` such that
`ψ_k(x) = ℓ_k(x) + (C / 6) ‖x - x0‖^3`, each `x_k` minimizes `ψ_k`, the scales satisfy
`A_{k+1} = A_k + a_k`, and the recursive relations `𝓡_k^1` and `𝓡_k^2` hold. -/
structure CubicNewtonEstimatingSequence
    (f : E → ℝ) (x0 : E) (L3 C : ℝ) where
  /-- The affine parts `ℓ_k` of the estimating functions `ψ_k`. -/
  affinePart : ℕ → E →ᵃ[ℝ] ℝ
  /-- The minimizing points `x_k`. -/
  x : ℕ → E
  /-- The scaling parameters `A_k`. -/
  A : ℕ → ℝ
  /-- The increments `a_k` in the recursion `A_{k+1} = A_k + a_k`. -/
  a : ℕ → ℝ
  /-- The scaling parameters satisfy `A_{k+1} = A_k + a_k`. -/
  A_succ (k : ℕ) : A (k + 1) = A k + a k
  /-- Each point `x_k` globally minimizes the estimating function `ψ_k`. -/
  x_isMin (k : ℕ) :
    IsMinOn (cubicNewtonEstimatingFunction affinePart C x0 k) Set.univ (x k)
  /-- The recursive relation `𝓡_k^1`, written at the minimizing point `x_k` so that
  `ψ_k(x_k) = ψ_k^*`. -/
  value_lower (k : ℕ) :
    A k * f (x k) ≤ cubicNewtonEstimatingFunction affinePart C x0 k (x k)
  /-- The recursive relation `𝓡_k^2`: every estimating function is bounded above by
  `A_k f(x) + ((2 L₃ + C) / 6) ‖x - x0‖^3`. -/
  upper_bound (k : ℕ) (y : E) :
    cubicNewtonEstimatingFunction affinePart C x0 k y ≤
      A k * f y + ((2 * L3 + C) / 6) * ‖y - x0‖ ^ (3 : ℕ)

namespace CubicNewtonEstimatingSequence

variable {f : E → ℝ} {x0 : E} {L3 C : ℝ}

/-- A cubic-Newton estimating sequence can be used as its sequence of estimating functions
`ψ_k`. -/
instance :
    CoeFun (CubicNewtonEstimatingSequence f x0 L3 C) (fun _ ↦ ℕ → E → ℝ) where
  coe sequence := cubicNewtonEstimatingFunction sequence.affinePart C x0

/-- Evaluating a cubic-Newton estimating sequence at stage `k` recovers the textbook formula for
`ψ_k`. -/
@[simp] theorem apply
    (sequence : CubicNewtonEstimatingSequence f x0 L3 C) (k : ℕ) (y : E) :
    sequence k y =
      sequence.affinePart k y + (C / 6) * ‖y - x0‖ ^ (3 : ℕ) := by
  simpa using cubicNewtonEstimatingFunction_apply sequence.affinePart C x0 k y

/-- The distinguished point `x_k` globally minimizes the estimating function `ψ_k`. -/
theorem isMinOn
    (sequence : CubicNewtonEstimatingSequence f x0 L3 C) (k : ℕ) :
    IsMinOn (sequence k) Set.univ (sequence.x k) := by
  simpa using sequence.x_isMin k

/-- The lower recursive inequality `𝓡_k^1` written on the canonical estimating-function surface.
-/
theorem value_lower_apply
    (sequence : CubicNewtonEstimatingSequence f x0 L3 C) (k : ℕ) :
    sequence.A k * f (sequence.x k) ≤ sequence k (sequence.x k) := by
  simpa using sequence.value_lower k

/-- The upper recursive inequality `𝓡_k^2` written on the canonical estimating-function surface.
-/
theorem upper_bound_apply
    (sequence : CubicNewtonEstimatingSequence f x0 L3 C) (k : ℕ) (y : E) :
    sequence k y ≤
      sequence.A k * f y + ((2 * L3 + C) / 6) * ‖y - x0‖ ^ (3 : ℕ) := by
  simpa using sequence.upper_bound k y

end CubicNewtonEstimatingSequence

end

/-! ### Text_4_2_14 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped ConstrainedArgmin
open ModifiedAcceleratedCubicNewton

/- Text 4.2.14 lies in the Chapter 4 modified accelerated cubic-Newton step domain.

Sampled owner-style declarations:
* `argmin[{xk, step yk}] f` in `Algorithm_4_2_5`, the canonical accepted-point owner for
  `x̂_k`;
* `ModifiedAcceleratedCubicNewton.isMinOn` in `Algorithm_4_2_5`, the canonical source of the
  comparison `f x̂_k ≤ f x_k`;
* `ModifiedAcceleratedCubicNewton.xNext` in `Algorithm_4_2_5`, the owner-derived next
  iterate `x_{k+1}`;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the canonical owner of the cubic trial
  map `T_{2L₃}` used by the modified step.

Best owner abstraction:
* source-facing: the present item is a one-step objective-gap estimate;
* core/canonical: the accepted-point subtype `argmin[{xk, step yk}] f` together with
  `IsMinOn f Set.univ xStar`;
* bridge/view: the cubic decrease and step-length inequalities evaluated at the owner-derived
  points `xHat` and `xNext xHat`.

Primitive data:
* the objective `f`;
* the chapter-standard constant `L3 : NNReal`;
* the cubic step owner `step : CubicRegularizationMapping f (2 * (L3 : ℝ))`;
* the canonical accepted-point owner `xHat : argmin[{xk, step yk}] f`;
* the minimizer `xStar`;
* the strong-convexity scalar `σ₂`;
* the cubic decrease and step-length lower bounds for `xHat` and `xNext xHat`.

Derived API:
* the accepted-point comparison `f xHat ≤ f xk`, obtained canonically from `isMinOn xHat`;
* the first displayed drop comparison;
* the square-root next-gap lower bound.

The previous version duplicated the Chapter 4 owner layer by carrying raw sequences `x` and
`hatX` and by storing `f (x k) ≥ f (hatX k)` as primitive data, even though Algorithm 4.2.5
already records `x̂_k` through the canonical two-point `argmin` owner. This refinement keeps the
source-facing theorem but rewrites it directly on that canonical binder, so the accepted-point
comparison is derived from the owner abstraction instead of repeated as a parallel
hypothesis. It also restores the chapter-standard `L3 : NNReal` surface. -/

-- Proof sketch: apply `ModifiedAcceleratedCubicNewton.isMinOn xHat` to the competitor `xk` to
-- get `f xHat ≤ f xk`, then subtract the common term `f (xNext xHat)`.
/-- The accepted-point owner from Algorithm 4.2.5 immediately gives the comparison
`f x_k - f x_{k+1} ≥ f xHat - f x_{k+1}`. This is the bridge/view part of Text 4.2.14. -/
theorem modified_accelerated_cubic_drop_ge_hat_drop
    (f : E → ℝ) (L3 : NNReal) {xk yk : E}
    (step : CubicRegularizationMapping f (2 * (L3 : ℝ)))
    (xHat : argmin[{xk, step yk}] f) :
    f xk - f (xNext xHat) ≥ f xHat - f (xNext xHat) := by
  have hxHat_le_xk : f xHat ≤ f xk := by
    simpa using
      (ModifiedAcceleratedCubicNewton.isMinOn xHat)
        (by simp : xk ∈ ({xk, step yk} : Set E))
  linarith

-- Proof sketch: combine the assumed cubic decrease estimate with the step-length lower bound and
-- simplify the constants.
/-- Text 4.2.14: let `xHat : argmin[{xk, step yk}] f` be the accepted point `x̂_k` chosen by
Algorithm 4.2.5 for the cubic owner `step : CubicRegularizationMapping f (2 L₃)`, and let
`xNext xHat` be the next iterate `x_{k+1}`. If `xStar` is a global minimizer of `f`,
`σ₂ > 0`, and the step satisfies
`f xHat - f (xNext xHat) ≥ (σ₂ / 6) ‖xNext xHat - xHat‖^3` together with
`‖xNext xHat - xHat‖ ≥
  (sqrt 2 * σ₂^(1/6) / L₃^(1/3))
  (f (xNext xHat) - f xStar)^(1/6)`,
then
`f xHat - f x_{k+1} ≥ (sqrt 2 * σ₂^(3/2) / (3 L₃)) (f x_{k+1} - f xStar)^(1/2)`. -/
theorem modified_accelerated_cubic_hat_drop_ge_sqrt_next_gap
    (f : E → ℝ) (L3 : NNReal) {xk yk : E}
    (step : CubicRegularizationMapping f (2 * (L3 : ℝ)))
    (xHat : argmin[{xk, step yk}] f)
    (xStar : E) (σ₂ : ℝ)
    (hxStar : IsMinOn f Set.univ xStar)
    (hσ₂ : 0 < σ₂)
    (hcubic :
      f xHat - f (xNext xHat) ≥
        (σ₂ / 6 : ℝ) * ‖xNext xHat - xHat‖ ^ (3 : ℕ))
    (hstep :
      ‖xNext xHat - xHat‖ ≥
        ((Real.sqrt 2 * Real.rpow σ₂ (1 / 6 : ℝ)) /
            Real.rpow (L3 : ℝ) (1 / 3 : ℝ)) *
          Real.rpow (f (xNext xHat) - f xStar) (1 / 6 : ℝ)) :
    f xHat - f (xNext xHat) ≥
      ((Real.sqrt 2 * Real.rpow σ₂ (3 / 2 : ℝ)) / (3 * (L3 : ℝ))) *
        Real.sqrt (f (xNext xHat) - f xStar) := sorry

end

/-! ### Definition_4_2_15 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Definition 4.2.15 lies in the unconstrained first-order geometry domain for smooth minimization.

Sampled owner-style declarations:
* mathlib `IsMinOn` and `isMinOn_univ_iff` in `Order/Filter/Extr`, the canonical owner of the
  chosen global-minimizer condition;
* mathlib `HasGradientAt` and `DifferentiableAt.hasGradientAt` in
  `Analysis/Calculus/Gradient/Basic`, the canonical first-order owner and the bridge from
  differentiability to the canonical gradient vector `∇ f x`;
* mathlib `HasGradientAt.gradient` in `Analysis/Calculus/Gradient/Basic`, which identifies the
  totalized gradient with an explicit gradient witness once first-order regularity is known;
* project `Definition_4_2_2`, which already fixes `HasGradientAt` as the chapter owner for
  first-order gradient data.

Best owner abstraction:
* source-facing: `IsFirstOrderNondegenerate f xStar`;
* core/canonical: `IsMinOn f Set.univ xStar` together with `HasGradientAt f (∇ f x) x` away from
  `xStar`;
* bridge/view: the companion theorem `firstOrderNondegeneracyCoefficient_def`.

Primitive data:
* the objective `f`;
* the chosen optimizer `xStar`;
* the global optimality witness `IsMinOn f Set.univ xStar`;
* first-order regularity away from `xStar`, recorded primitively as `DifferentiableAt ℝ f x`;
* a positive scalar `τ` uniformly bounding the coefficient away from `xStar`.

Derived API:
* the explicit textbook formula for the coefficient;
* the canonical gradient witness `HasGradientAt f (∇ f x) x` away from `xStar`;
* the pointwise lower-bound consequences of an admissible coefficient threshold.

This file is therefore an owner file, not a recall file. The refinement target is to keep the
source-facing owner while deleting derived packaging that does not add mathematical content. -/

/-- The cosine-type coefficient comparing the gradient at `x` with the displacement `x - xStar`
toward a chosen optimizer `xStar`. In a Hilbert space, the dual norm of the gradient is
identified with the ordinary norm. -/
def firstOrderNondegeneracyCoefficient
    (f : E → ℝ) (xStar x : E) : ℝ :=
  inner ℝ (∇ f x) (x - xStar) / (‖∇ f x‖ * ‖x - xStar‖)

-- Proof sketch: unfold `firstOrderNondegeneracyCoefficient`.
/-- Expanding `firstOrderNondegeneracyCoefficient f xStar x` recovers the textbook formula for the
coefficient `α(x)`. -/
theorem firstOrderNondegeneracyCoefficient_def
    (f : E → ℝ) (xStar x : E) :
    firstOrderNondegeneracyCoefficient f xStar x =
      inner ℝ (∇ f x) (x - xStar) / (‖∇ f x‖ * ‖x - xStar‖) :=
  rfl

/-- A scalar `τ` is a first-order nondegeneracy lower bound for `f` at `xStar` when it is
positive and uniformly bounds the normalized gradient/displacement coefficient away from the
optimizer. -/
def IsFirstOrderNondegeneracyLowerBound
    (f : E → ℝ) (xStar : E) (τ : ℝ) : Prop :=
  0 < τ ∧
    ∀ ⦃x : E⦄, x ≠ xStar →
      τ ≤ firstOrderNondegeneracyCoefficient f xStar x

namespace IsFirstOrderNondegeneracyLowerBound

variable {f : E → ℝ} {xStar : E} {τ : ℝ}

/-- Every first-order nondegeneracy lower bound is positive. -/
theorem pos (hτ : IsFirstOrderNondegeneracyLowerBound f xStar τ) : 0 < τ :=
  hτ.1

/-- A first-order nondegeneracy lower bound bounds the coefficient at each point away from the
optimizer. -/
theorem le_coefficient
    (hτ : IsFirstOrderNondegeneracyLowerBound f xStar τ) {x : E} (hx : x ≠ xStar) :
    τ ≤ firstOrderNondegeneracyCoefficient f xStar x :=
  hτ.2 hx

end IsFirstOrderNondegeneracyLowerBound

/-- Definition 4.2.15: an unconstrained objective is first-order non-degenerate relative to a
chosen optimal solution `xStar` if `xStar` globally minimizes `f` and the coefficient
`α(x) = ⟪∇ f(x), x - xStar⟫ / (‖∇ f(x)‖ * ‖x - xStar‖)` admits a uniform positive lower bound for
every `x ≠ xStar`. The first-order interpretation of `∇ f(x)` is part of the owner data: away
from `xStar`, `f` is differentiable so the canonical gradient `∇ f x` is the actual gradient. -/
class IsFirstOrderNondegenerate
    (f : E → ℝ) (xStar : E) : Prop where
  /-- The reference point `xStar` is a global minimizer of `f`. -/
  isMinOn : IsMinOn f Set.univ xStar
  /-- Away from the optimizer, `f` is differentiable, hence its canonical gradient is well-defined
  in the first-order sense. -/
  differentiableAt {x : E} (_hx : x ≠ xStar) : DifferentiableAt ℝ f x
  /-- The cosine coefficient has a uniform positive lower bound away from the optimizer. -/
  lowerBound :
    ∃ τ : ℝ, IsFirstOrderNondegeneracyLowerBound f xStar τ

/-- A first-order nondegeneracy hypothesis canonically supplies the global-minimizer fact for the
chosen optimizer `xStar`. -/
instance {f : E → ℝ} {xStar : E} [hf : IsFirstOrderNondegenerate f xStar] :
    Fact (IsMinOn f Set.univ xStar) where
  out := hf.isMinOn

namespace IsFirstOrderNondegenerate

variable {f : E → ℝ} {xStar : E}

/-- Away from the optimizer, the canonical gradient vector `∇ f x` is the actual gradient of
`f` at `x`. -/
theorem hasGradientAt
    (hf : IsFirstOrderNondegenerate f xStar) {x : E} (hx : x ≠ xStar) :
    HasGradientAt f (∇ f x) x :=
  (hf.differentiableAt hx).hasGradientAt

end IsFirstOrderNondegenerate

/-! ### Text_4_2_15 (from Chap04) -/
universe u

/- Text 4.2.15 lies in the chapter's false-acceleration objective-gap transfer domain.

Sampled neighboring declarations:
* `acceleratedCubicRegularization_gap_le_inverse_cubic_rate` in `Theorem_4_2_3`, the chapter's
  owner inverse-cubic objective-gap estimate for accelerated cubic Newton iterates;
* `false_acceleration_gap_ge_gap_to_next_iterate_of_isMinOn` in `Text_4_2_16`, the next scalar
  bridge statement in the same false-acceleration discussion;
* `false_acceleration_gap_le_inverse_eighth_rate` in `Text_4_2_17`, the downstream scalar
  consequence that reuses the chapter-standard nonnegative constants `L3` and `R`.

Best owner abstraction:
* source-facing: the displayed two-thirds-index objective-gap estimate
  `f (x hatK) - f xStar ≤ 3^3 L3 R^3 / N^3`;
* core/canonical: the scalar inverse-cubic gap profile `gap k ≤ (L3 * R^3) / k^3`;
* bridge/view: the companion specialization from the scalar profile to the objective-gap sequence
  `gap k = f (x k) - f xStar`.

Primitive data:
* the displayed indices `N` and `hatK`;
* the chapter-standard nonnegative constants `L3` and `R`.
* the objective `f`, iterate sequence `x`, and comparison point `xStar`.

Derived API:
* the scalar companion theorem obtained by abstracting the objective gaps to a sequence `gap`;
* positivity of the scalar prefactor, inherited from `L3 R : NNReal`.

The previous version made the scalar bridge theorem the main public entry and left the textbook
identification `gap k = f (x k) - f xStar` only in commentary. This refinement restores the
source-facing objective-gap statement as the main theorem and keeps the scalar inverse-cubic
algebra as a reusable companion.
-/

-- Proof sketch: apply the inverse-cubic estimate at the integer index `hatK`. Then use
-- `(hatK : ℝ) = (2 / 3) * N` to rewrite the denominator as `((2 / 3) * N)^3`, simplify this to
-- `(8 / 27) * N^3`, and compare the resulting factor `(27 / 8)` with `27 = 3^3`. The scalar
-- factor is nonnegative because the rate constants live in `NNReal`.
theorem inverse_cubic_gap_at_two_thirds_index_le_three_cubed_bound
    (gap : ℕ → ℝ) (N hatK : ℕ) (L3 R : NNReal)
    (hN : 0 < N)
    (hhatK : (hatK : ℝ) = (2 / 3 : ℝ) * (N : ℝ))
    (hgap :
      ∀ ⦃k : ℕ⦄, 1 ≤ k →
        gap k ≤
          ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (k : ℝ) ^ (3 : ℕ)) :
    gap hatK ≤
      ((3 : ℝ) ^ (3 : ℕ) * ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ))) / (N : ℝ) ^ (3 : ℕ) := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hhatK_pos : 0 < (hatK : ℝ) := by
    rw [hhatK]
    positivity
  have hhatK_nat : 1 ≤ hatK := by
    exact Nat.succ_le_of_lt (by exact_mod_cast hhatK_pos)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_real
  calc
    gap hatK ≤ ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (hatK : ℝ) ^ (3 : ℕ) :=
      hgap hhatK_nat
    _ = (27 / 8 : ℝ) * (((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (N : ℝ) ^ (3 : ℕ)) := by
      rw [hhatK]
      field_simp [hN_ne]
      ring
    _ ≤ (3 : ℝ) ^ (3 : ℕ) * (((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (N : ℝ) ^ (3 : ℕ)) := by
      gcongr
      norm_num
    _ = ((3 : ℝ) ^ (3 : ℕ) * ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ))) / (N : ℝ) ^ (3 : ℕ) := by
      ring

/-- Text 4.2.15: if the objective gaps along an iterate sequence satisfy the inverse-cubic estimate
`gap k ≤ (L3 * R^3) / k^3` for every integer `k ≥ 1`, then at any index `hatK` with
`(hatK : ℝ) = (2 / 3) * N` one has
`f (x hatK) - f xStar ≤ 3^3 * L3 * R^3 / N^3`. -/
theorem false_acceleration_gap_at_two_thirds_index_le_three_cubed_bound
    {E : Type u} (f : E → ℝ) (x : ℕ → E) (xStar : E) (N hatK : ℕ) (L3 R : NNReal)
    (hN : 0 < N)
    (hhatK : (hatK : ℝ) = (2 / 3 : ℝ) * (N : ℝ))
    (hgap :
      ∀ ⦃k : ℕ⦄, 1 ≤ k →
        f (x k) - f xStar ≤
          ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ)) / (k : ℝ) ^ (3 : ℕ)) :
    f (x hatK) - f xStar ≤
      ((3 : ℝ) ^ (3 : ℕ) * ((L3 : ℝ) * (R : ℝ) ^ (3 : ℕ))) / (N : ℝ) ^ (3 : ℕ) := by
  simpa using
    inverse_cubic_gap_at_two_thirds_index_le_three_cubed_bound
      (fun k ↦ f (x k) - f xStar) N hatK L3 R hN hhatK hgap

/-! ### Definition_4_2_16 (from Chap04) -/
noncomputable section

universe u

open scoped LevelSetNotation

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 4.2.16 lies in the normed-space cubic-regularization / sublevel-radius domain.

Sampled owner-style declarations:
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the earlier project owner
  for a regularized objective centered at a base point;
* `𝓛[f](α)` / `mem_levelSet_iff` in `Chap01/Definition_1_4_8`, the project owner for lower level
  sets;
* `NonlinearConvexTransformation.D_isGreatest` in `Chap04/Definition_4_1_10`, the nearby project
  pattern for a textbook radius constant recorded by an attained maximum;
* `IsGreatest` in mathlib, the canonical order-theoretic owner for an attained maximum.

Source/core/bridge triage:
* source-facing: the cubically regularized objective and the textbook radius constant `D` of the
  initial sublevel set;
* core/canonical: `cubicallyRegularizedObjective f δ x₀`, `𝓛[f]((f x₀))`, and `IsGreatest`;
* bridge/view: the initial-sublevel distance set `initialSublevelDistanceSet f x₀`.

Primitive data:
* the objective `f`;
* the base point `x₀`;
* the regularization parameter `δ`.

Derived API:
* evaluation of the cubic regularization owner at a point;
* the bridge set of distances on the canonical initial sublevel set;
* membership in that bridge set from a sublevel inequality;
* the source-facing radius statement `IsGreatest (initialSublevelDistanceSet f x₀) D`.

The cubic perturbation is first introduced here, so it remains the public owner. The sublevel-set
part, however, is already canonical earlier in the chapter, and the textbook radius is an attained
maximum rather than an unconditional supremum. This file therefore keeps the sublevel set itself
canonical, exposes only the distance-image bridge set, and records the radius through
`IsGreatest` instead of a parallel always-defined `ℝ`-valued wrapper. -/

/-- Definition 4.2.16: the cubically regularized objective associated to `f`, the reference point
`x₀`, and the parameter `δ` is the function `x ↦ f x + (δ / 3) ‖x - x₀‖^3`. -/
def cubicallyRegularizedObjective
    (f : E → ℝ) (δ : ℝ) (x0 : E) : E → ℝ :=
  fun x ↦ f x + (δ / 3) * ‖x - x0‖ ^ (3 : ℕ)

/-- Evaluating the cubically regularized objective at `x` gives the defining cubic penalty term
centered at `x₀`. -/
@[simp]
theorem cubicallyRegularizedObjective_apply
    (f : E → ℝ) (δ : ℝ) (x0 x : E) :
    cubicallyRegularizedObjective f δ x0 x =
      f x + (δ / 3) * ‖x - x0‖ ^ (3 : ℕ) :=
  rfl

/-- A nonnegative cubic regularization parameter can only increase the objective value. -/
theorem le_cubicallyRegularizedObjective_of_nonneg
    (f : E → ℝ) (x0 x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    f x ≤ cubicallyRegularizedObjective f δ x0 x := by
  rw [cubicallyRegularizedObjective_apply]
  have hnonneg : 0 ≤ (δ / 3) * ‖x - x0‖ ^ (3 : ℕ) := by
    positivity
  linarith

/-- The set of distances from `x₀` attained on the initial sublevel set `{x | f x ≤ f x₀}`. -/
def initialSublevelDistanceSet (f : E → ℝ) (x0 : E) : Set ℝ :=
  (fun x : E ↦ ‖x - x0‖) '' (𝓛[f]((f x0)) : Set E)

/-- Membership in `initialSublevelDistanceSet f x₀` means that the radius is realized by some
point of the initial sublevel set `{x | f x ≤ f x₀}`. -/
@[simp]
theorem mem_initialSublevelDistanceSet_iff
    {f : E → ℝ} {x0 : E} {r : ℝ} :
    r ∈ initialSublevelDistanceSet f x0 ↔
      ∃ x : E, f x ≤ f x0 ∧ ‖x - x0‖ = r := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by simpa using hx, rfl⟩
  · rintro ⟨x, hx, hnorm⟩
    exact ⟨x, by simpa using hx, hnorm⟩

/-- Any point of the initial sublevel set contributes its distance to `x₀` to the canonical
distance-image bridge set. -/
theorem norm_sub_mem_initialSublevelDistanceSet
    {f : E → ℝ} {x0 x : E} (hx : f x ≤ f x0) :
    ‖x - x0‖ ∈ initialSublevelDistanceSet f x0 :=
  Set.mem_image_of_mem _ (by simpa using hx)

/-- If `D` is an attained maximum of the initial-sublevel distance set, then every point of the
canonical initial level set `𝓛[f]((f x₀))` is at distance at most `D` from `x₀`. -/
theorem norm_sub_le_of_mem_levelSet_of_initialSublevelDistanceSet_isGreatest
    {f : E → ℝ} {x0 x : E} {D : ℝ}
    (hD : IsGreatest (initialSublevelDistanceSet f x0) D)
    (hx : x ∈ (𝓛[f]((f x0)) : Set E)) :
    ‖x - x0‖ ≤ D :=
  hD.2 (Set.mem_image_of_mem _ hx)

/-- If `D` is an attained maximum of the initial-sublevel distance set, then every point in the
initial sublevel set is at distance at most `D` from `x₀`. -/
theorem norm_sub_le_of_le_of_initialSublevelDistanceSet_isGreatest
    {f : E → ℝ} {x0 x : E} {D : ℝ}
    (hD : IsGreatest (initialSublevelDistanceSet f x0) D)
    (hx : f x ≤ f x0) :
    ‖x - x0‖ ≤ D := by
  exact
    norm_sub_le_of_mem_levelSet_of_initialSublevelDistanceSet_isGreatest hD
      (by simpa using hx)

section

variable (f : E → ℝ) (x0 : E) (D : ℝ)

/- Definition 4.2.16: the textbook radius `D` of the initial sublevel set is recorded canonically
as the attained-maximum statement `IsGreatest (initialSublevelDistanceSet f x₀) D`. -/
#check IsGreatest (initialSublevelDistanceSet f x0) D

end

end

/-! ### Text_4_2_16 (from Chap04) -/
universe u

/- Text 4.2.16 lives in the chapter's whole-space minimization domain.

Sampled owner declarations:
* mathlib `IsMinOn`, the canonical owner of whole-space minimality;
* mathlib `isMinOn_univ_iff`, the textbook bridge `IsMinOn f Set.univ xStar ↔ ∀ x, f xStar ≤ f x`;
* Chapter 2 `Definition_2_1`, which already fixes `IsMinOn f Set.univ xStar` as the project's
  source-facing owner for unconstrained minimizers.

Best owner abstraction:
* `IsMinOn f Set.univ xStar`

Primitive data:
* the objective `f`;
* the iterate sequence `x`;
* the minimizer witness `hxStar : IsMinOn f Set.univ xStar`;
* the two indices `hatK` and `N + 1` whose objective values are compared.

Derived API:
* the pointwise inequality `f xStar ≤ f (x (N + 1))`, obtained from the minimizer owner.

Source/core/bridge triage:
* source-facing: the comparison between the gap at the displayed iterate and the gap to `x_{N+1}`;
* core/canonical: `IsMinOn f Set.univ xStar`;
* bridge/view: the textbook pointwise inequality recovered from the owner predicate.

The arithmetic relation identifying `hatK` with the two-thirds index is not used in this
comparison itself, so the refined public statement drops that redundant binder and keeps only the
canonical minimizer data that actually drives the inequality.
-/

-- Proof sketch: use the canonical bridge `isMinOn_univ_iff` at `x (N + 1)` to get
-- `f xStar ≤ f (x (N + 1))`, then apply monotonicity of left subtraction by `f (x hatK)`.
/-- Text 4.2.16: if `xStar` is a global minimizer of `f`, then the objective gap at any iterate
`x_hatK` dominates the gap from the same iterate to the later point `x_{N+1}`. In the textbook
application, `hatK` is the two-thirds index from the preceding step. -/
theorem false_acceleration_gap_ge_gap_to_next_iterate_of_isMinOn
    {E : Type u} (f : E → ℝ) (x : ℕ → E) (xStar : E) (N hatK : ℕ)
    (hxStar : IsMinOn f Set.univ xStar) :
    f (x hatK) - f xStar ≥ f (x hatK) - f (x (N + 1)) := by
  have hxStar_le : f xStar ≤ f (x (N + 1)) := (isMinOn_univ_iff.mp hxStar) (x (N + 1))
  simpa [ge_iff_le] using sub_le_sub_left hxStar_le (f (x hatK))

/-! ### Definition_4_2_17 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped DegreeConditioning

/- Primary domain: higher-order conditioning classes for real-valued objectives on real normed
spaces.

Sampled owner-style declarations:
* `σ[p](f)` and `L[p](f)` from `Definition_4_2_11`
* `HasIteratedFDerivLipschitzConstantOfDegree p f` from `Definition_4_2_11`
* the sibling source-facing class `IsInFunctionClassF2Lip` in `Definition_4_2_18`
* mathlib's `Fact`, whose library note warns against adding global proof-search instances

Best owner abstraction:
* `source-facing`: `IsInFunctionClassF23 f`
* `core/canonical`: the inherited finiteness owner
  `HasIteratedFDerivLipschitzConstantOfDegree 3 f` together with the inherited finite
  uniform-convexity owners `HasUniformConvexityParameterOfDegree 2 f` and
  `HasUniformConvexityParameterOfDegree 3 f`
* `bridge/view`: the textbook surface notation `f ∈ 𝓕₂₃`

Primitive data:
* finite degree-`2` and degree-`3` uniform-convexity parameters, carried by the parent owners
  `HasUniformConvexityParameterOfDegree 2 f` and `HasUniformConvexityParameterOfDegree 3 f`
* finiteness of `L[3](f)`, carried by the parent owner

Derived API:
* the inherited instance `HasIteratedFDerivLipschitzConstantOfDegree 3 f`
* the paired positivity theorem `IsInFunctionClassF23.sigma_pos`, now derived from the parent
  sigma owners
* the source-facing notation `f ∈ 𝓕₂₃`

This file therefore keeps the source-facing class `𝓕_{2,3}` but stores the degree-three
Lipschitz finiteness hypothesis through its canonical upstream owner, and it also stores the
well-definedness of `σ[2](f)` and `σ[3](f)` through their canonical finite-parameter owners
instead of duplicating sigma-positivity as primitive fields. Positivity is then exposed by theorem
rather than a global `Fact` instance. -/

/-- Definition 4.2.17: a function belongs to the class `𝓕_{2,3}` when `σ[2](f)` and `σ[3](f)`
are positive and `L[3](f)` is finite. The finiteness clause is carried by the canonical owner
`HasIteratedFDerivLipschitzConstantOfDegree 3 f`, while the well-definedness of `σ[2](f)` and
`σ[3](f)` is carried by the canonical finite-parameter owners
`HasUniformConvexityParameterOfDegree 2 f` and `HasUniformConvexityParameterOfDegree 3 f`. -/
class IsInFunctionClassF23 (f : E → ℝ) : Prop where
  /-- The degree-two uniform-convexity parameter of `f` is a genuine finite real parameter. -/
  degreeTwo_uniform : HasUniformConvexityParameterOfDegree 2 f
  /-- The degree-three uniform-convexity parameter of `f` is a genuine finite real parameter. -/
  degreeThree_uniform : HasUniformConvexityParameterOfDegree 3 f
  /-- The degree-three Lipschitz constant of `f` is finite. -/
  degreeThree_lipschitz : HasIteratedFDerivLipschitzConstantOfDegree 3 f

attribute [instance] IsInFunctionClassF23.degreeTwo_uniform
attribute [instance] IsInFunctionClassF23.degreeThree_uniform
attribute [instance] IsInFunctionClassF23.degreeThree_lipschitz

scoped[FunctionClasses] notation:50 f:50 " ∈ " "𝓕₂₃" => IsInFunctionClassF23 f

open scoped FunctionClasses

namespace IsInFunctionClassF23

/-- Membership in `𝓕₂₃` records positivity of both source-facing conditioning parameters. -/
theorem sigma_pos {f : E → ℝ} (hf : f ∈ 𝓕₂₃) :
    0 < σ[2](f) ∧ 0 < σ[3](f) := by
  letI : f ∈ 𝓕₂₃ := hf
  exact ⟨HasUniformConvexityParameterOfDegree.uniformConvexityParameterOfDegree_pos,
    HasUniformConvexityParameterOfDegree.uniformConvexityParameterOfDegree_pos⟩

end IsInFunctionClassF23

/-! ### Text_4_2_17 (from Chap04) -/
universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Text 4.2.17 lies in the chapter's scalar inverse-power gap-estimate domain.

Sampled neighboring declarations:
* `false_acceleration_gap_at_two_thirds_index_le_three_cubed_bound` in `Text_4_2_15`, the
  immediate predecessor false-acceleration rate statement, already on the chapter-standard
  constants `L3 R : NNReal`;
* `acceleratedCubicRegularization_gap_le_inverse_cubic_rate` in `Theorem_4_2_3`, the chapter's
  canonical accelerated cubic-Newton inverse-power gap estimate, again using `L3 : NNReal`;
* `cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel` in `Theorem_4_2_2`, the nearby
  cubic-Newton rate theorem written directly with the chapter standard nonnegative constants.

Best owner abstraction:
* source-facing: the displayed inverse-eighth objective-gap estimate at `x_{N+1}`;
* core/canonical: the scalar eighth-power gap upper bound together with the inverse-linear
  distance decay, stated using the chapter-standard nonnegative parameters `L3` and `R`;
* bridge/view: only the ambient coercions `(L3 : ℝ)` and `(R : ℝ)` needed on the real-valued
  theorem surface.

Primitive data:
* the objective `f`, iterate sequence `x`, reference point `xStar`, strong-convexity modulus
  `σ₂`, chapter constants `L3` and `R`, and the index `N`;
* the local eighth-power gap estimate at `x_{N+1}`;
* the inverse-linear distance decay at `x_{N+1}`.

Derived API:
* nonnegativity of the scalar coefficient and right-hand side bound, now inherited from
  `L3 R : NNReal` and `σ₂ > 0`;
* monotonicity of the eighth power applied to the distance estimate.

The previous version carried `L₃` and `R` as raw real parameters even though the surrounding
Chapter 4 rate API already treats them as canonical nonnegative constants. This refinement aligns
the theorem with that owner layer and removes proof scaffolding whose only purpose was to recover
those missing sign facts.
-/

/-- Text 4.2.17 at the source-facing scalar consequence level: once the earlier convexity,
smoothness, and false-acceleration hypotheses have been condensed into the local gap estimate at
`x_{N+1}` and the inverse-linear distance decay `‖x_{N+1} - xStar‖ ≤ 3 R / N`, substituting the
distance bound into the eighth-power estimate yields the inverse-eighth decay of the objective
gap for every positive index `N`. -/
theorem false_acceleration_gap_le_inverse_eighth_rate
    (f : E → ℝ) (x : ℕ → E) (xStar : E) (σ₂ : ℝ) (L3 R : NNReal) (N : ℕ)
    (hσ₂ : 0 < σ₂)
    (hN : 0 < N)
    (hgap_upper :
      f (x (N + 1)) - f xStar ≤
        (((3 : ℝ) ^ (9 : ℕ)) * (L3 : ℝ) ^ (4 : ℕ) / (2 * σ₂ ^ (3 : ℕ))) *
          ‖x (N + 1) - xStar‖ ^ (8 : ℕ))
    (hdistance_decay :
      ‖x (N + 1) - xStar‖ ≤ 3 * (R : ℝ) / (N : ℝ)) :
    f (x (N + 1)) - f xStar ≤
      (((3 : ℝ) ^ (17 : ℕ)) * (L3 : ℝ) ^ (4 : ℕ) * (R : ℝ) ^ (8 : ℕ)) /
        (2 * σ₂ ^ (3 : ℕ) * (N : ℝ) ^ (8 : ℕ)) := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_real
  let coeff : ℝ := (((3 : ℝ) ^ (9 : ℕ)) * (L3 : ℝ) ^ (4 : ℕ) / (2 * σ₂ ^ (3 : ℕ)))
  have hcoeff_nonneg : 0 ≤ coeff := by
    positivity
  have hpow :
      ‖x (N + 1) - xStar‖ ^ (8 : ℕ) ≤ (3 * (R : ℝ) / (N : ℝ)) ^ (8 : ℕ) := by
    gcongr
  calc
    f (x (N + 1)) - f xStar ≤
        coeff *
          ‖x (N + 1) - xStar‖ ^ (8 : ℕ) :=
      hgap_upper
    _ ≤
        coeff *
          (3 * (R : ℝ) / (N : ℝ)) ^ (8 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hpow hcoeff_nonneg
    _ = (((3 : ℝ) ^ (17 : ℕ)) * (L3 : ℝ) ^ (4 : ℕ) * (R : ℝ) ^ (8 : ℕ)) /
          (2 * σ₂ ^ (3 : ℕ) * (N : ℝ) ^ (8 : ℕ)) := by
      dsimp [coeff]
      rw [div_pow, mul_pow]
      field_simp [hN_ne]
