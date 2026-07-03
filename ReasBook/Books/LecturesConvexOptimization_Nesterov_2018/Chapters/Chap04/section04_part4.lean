import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_4_11 (from Chap04) -/
open scoped ConstrainedArgmin

noncomputable section

universe u v

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable {E₂ : Type v} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 4.4.11 lies in the Gauss--Newton local-model / unconstrained minimization domain.

Sampled owner-style declarations:
* `meritFunctionReformulation` in `Definition_4_4_10`, the chapter owner for scalarizing a
  residual map by composing with a merit function;
* `ContinuousLinearMap.toAffineMap` in mathlib, the canonical owner for turning a Jacobian slice
  into the affine map `y ↦ F x + J x (y - x)`;
* `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project
  owner for minimizer sets, specialized here to `Set.univ`;
* `ConvexOn.comp_affineMap` in mathlib, the canonical convexity owner for precomposing `φ` with
  that affine residual model.

Source/core/bridge triage:
* source-facing: the modified Gauss--Newton local model `ψ(x; y)`;
* core/canonical: composition of `φ` with the affine residual linearization determined by a
  Jacobian family `J x : E₁ →L[ℝ] E₂`;
* bridge/view: the pointwise evaluation formula for `ψ(x; y)`.

Primitive data:
* a residual map `F : E₁ → E₂`;
* a Jacobian family `J : E₁ → E₁ →L[ℝ] E₂`;
* a merit function `φ : E₂ → ℝ`.

Derived API:
* pointwise evaluation of the local model;
* convexity in the trial-point variable when `φ` is convex;
* the candidate next-iterate set as the canonical owner `argmin[Set.univ]`.

The public owner therefore takes the Jacobian family as primitive data instead of presenting the
totalized operator `fderiv` as the textbook Jacobian for an arbitrary residual map.
-/

/-- Definition 4.4.11: given a residual map `F`, a Jacobian family `J`, and a merit function
`φ`, the modified Gauss--Newton local model is the two-variable function
`ψ(x; y) = φ (F(x) + J(x)(y - x))`. When `J x = F'(x)`, this is the textbook affine
first-order residual model at the base point `x`. -/
def modifiedGaussNewtonLocalModel
    (F : E₁ → E₂)
    (φ : E₂ → ℝ)
    (J : E₁ → E₁ →L[ℝ] E₂) : E₁ → E₁ → ℝ :=
  fun x ↦ meritFunctionReformulation (fun y ↦ F x + J x (y - x)) φ

/-
Source-facing Lean notation for the textbook local model `ψ(x; y)`, with the ambient residual
map, merit function, and Jacobian family recorded in bracket arguments.
-/
namespace ModifiedGaussNewtonLocalModelNotation

scoped notation:max "ψ[" F:arg "; " φ:arg "; " J:arg "]" =>
  modifiedGaussNewtonLocalModel F φ J

scoped notation:max "ψ[" F:arg "; " φ:arg "; " J:arg "](" x:arg "; " y:arg ")" =>
  modifiedGaussNewtonLocalModel F φ J x y

end ModifiedGaussNewtonLocalModelNotation

open scoped ModifiedGaussNewtonLocalModelNotation

/-- Evaluating the modified Gauss--Newton local model gives the textbook formula
`ψ[F; φ; J](x; y) = φ (F(x) + J(x)(y - x))`. -/
@[simp] theorem modifiedGaussNewtonLocalModel_apply
    (F : E₁ → E₂)
    (φ : E₂ → ℝ)
    (J : E₁ → E₁ →L[ℝ] E₂) (x y : E₁) :
    ψ[F; φ; J](x; y) = φ (F x + J x (y - x)) :=
  rfl

/-- If `φ` is convex, then the modified Gauss--Newton local model is convex in the second
argument `y` for each fixed base point `x`. -/
-- Proof sketch: for fixed `x`, the map `y ↦ F x + J x (y - x)` is affine. The
-- composition of a convex `φ` with this affine map is therefore convex on all of `E₁`.
theorem modifiedGaussNewtonLocalModel_convex
    (F : E₁ → E₂)
    (φ : E₂ → ℝ)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (hφ : ConvexOn ℝ Set.univ φ)
    (x : E₁) :
    ConvexOn ℝ Set.univ (ψ[F; φ; J] x) := by
  let g : E₁ →ᵃ[ℝ] E₂ :=
    (J x).toAffineMap.comp (AffineMap.id ℝ E₁ - AffineMap.const ℝ E₁ x) +
      AffineMap.const ℝ E₁ (F x)
  simpa [g, modifiedGaussNewtonLocalModel, meritFunctionReformulation, Function.comp,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hφ.comp_affineMap g

section ArgminRecall

variable (F : E₁ → E₂) (φ : E₂ → ℝ) (J : E₁ → E₁ →L[ℝ] E₂) (x y : E₁)

/- The candidate next-iterate set for the local model is the canonical minimizer owner
`argmin[Set.univ] (ψ[F; φ; J] x)`. -/
set_option linter.hashCommand false in
#check (argmin[Set.univ] (ψ[F; φ; J] x) : Set E₁)

set_option linter.hashCommand false in
#check
  (show y ∈ argmin[Set.univ] (ψ[F; φ; J] x) ↔
      IsMinOn (ψ[F; φ; J] x) Set.univ y from by
    simp)

end ArgminRecall

end

/-! ### Proposition_4_4_11 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/- This item lies in the modified Gauss--Newton / Newton quadratic-entry domain.

Sampled owner declarations:
* `ModifiedGaussNewtonProblem` in `Definition_4_4_16`, the chapter owner bundling the objective,
  strong-convexity, Hessian-Lipschitz, minimizer, and starting-point data;
* `modifiedNewton_hasQuadraticConvergenceFrom_zero_of_characteristicQuantity_lt_one` and
  `modifiedNewton_firstQuadraticConvergenceIndex_le_sqrt_characteristicQuantity` in
  `Proposition_4_4_10`, the core Chapter 4 owner theorems for the small-characteristic and
  large-characteristic quadratic-entry regimes of the underlying modified Newton orbit;
* `IsLeast {k | HasQuadraticConvergenceFrom method problem.xStar k}` in `Text_4_2_24`, the
  canonical package for the first index from which an orbit converges quadratically;
* `ModifiedGaussNewtonProblem.characteristicQuantity` in `Definition_4_4_16`, the bridge from the
  bundled problem data to the scalar parameter used by the owner theorem.

Source/core/bridge triage:
* source-facing: the modified Gauss--Newton stationarity reformulation attached to
  `problem : ModifiedGaussNewtonProblem E`;
* core/canonical: the modified-Newton owner theorems
  `modifiedNewton_hasQuadraticConvergenceFrom_zero_of_characteristicQuantity_lt_one` and
  `modifiedNewton_firstQuadraticConvergenceIndex_le_sqrt_characteristicQuantity`;
* bridge/view: the coercion from `problem` to its objective together with
  `problem.characteristicQuantity`.

Primitive data:
* the bundled owner object `problem`;
* the Newton orbit `method` of the stationarity reformulation;
* the first quadratic-convergence index witness `hN2`.

Derived API:
* the strong-convexity, Hessian-Lipschitz, and minimizer hypotheses supplied by the fields of
  `problem`;
* the scalar bridge `problem.characteristicQuantity`;
* the Chapter 4 modified-Newton entry-index estimate.

The public surface should therefore be a thin bridge from the bundled modified Gauss--Newton
problem to the Chapter 4 modified-Newton owner theorem, rather than a second theorem specialized
to the concrete model `EuclideanSpace ℝ (Fin n)`.
-/

section

set_option linter.style.longLine false

-- Proof sketch: apply the Chapter 4 modified-Newton owner theorems to the objective carried by
-- `problem`. The bundled owner fields supply the strong-convexity, Hessian-Lipschitz, and
-- minimizer hypotheses, and the textbook parameter `ζ` is exactly
-- `problem.characteristicQuantity`. For `ζ < 1`, reuse the upstream small-characteristic owner
-- theorem to get quadratic convergence from index `0`; for `ζ ≥ 1`, reuse the upstream entry-index
-- estimate and then dominate `6.25 * sqrt ζ` by the textbook scalar surface `1 + 6 ζ²`.
/-- Proposition 4.4.11: if `problem` is a modified Gauss--Newton problem, `method` is the
associated modified Newton orbit started at `problem.x0`, and `N₂` is the first
quadratic-convergence index of `method` toward `problem.xStar`, then `(N₂ : ℝ)` is bounded by
`1 + 6 * problem.characteristicQuantity ^ (2 : ℕ)`. -/
theorem modifiedGaussNewton_scheme_firstQuadraticConvergenceIndex_le_one_add_six_mul_characteristicQuantity_sq
    (problem : ModifiedGaussNewtonProblem E)
    (method : NewtonSystem.Method (∇ problem) problem.x0)
    {N2 : ℕ}
    (hN2 : IsLeast {k : ℕ | HasQuadraticConvergenceFrom method problem.xStar k} N2) :
    (N2 : ℝ) ≤ 1 + 6 * problem.characteristicQuantity ^ (2 : ℕ) := by
  by_cases hξ : problem.characteristicQuantity < 1
  · have hquad0 :
        HasQuadraticConvergenceFrom method problem.xStar 0 :=
      modifiedNewton_hasQuadraticConvergenceFrom_zero_of_characteristicQuantity_lt_one
        problem.sigma_pos
        problem.objective_strongConvex
        problem.objective_mem
        problem.xStar_isMin
        method
        (by simpa using hξ)
    have hN2_zero : N2 = 0 := Nat.eq_zero_of_le_zero (hN2.2 hquad0)
    rw [hN2_zero]
    have hrhs : (0 : ℝ) ≤ 1 + 6 * problem.characteristicQuantity ^ (2 : ℕ) := by
      positivity
    simpa using hrhs
  · have hξ' : 1 ≤ problem.characteristicQuantity := by
      linarith
    have hbound :=
      modifiedNewton_firstQuadraticConvergenceIndex_le_sqrt_characteristicQuantity
        problem.sigma_pos
        problem.objective_strongConvex
        problem.objective_mem
        problem.xStar_isMin
        method
        (by simpa using hξ')
        hN2
    have hscalar :
        (25 / 4 : ℝ) * Real.sqrt problem.characteristicQuantity ≤
          1 + 6 * problem.characteristicQuantity ^ (2 : ℕ) := by
      have hsqrt_le :
          Real.sqrt problem.characteristicQuantity ≤ problem.characteristicQuantity := by
        rw [Real.sqrt_le_iff]
        constructor
        · linarith
        · nlinarith [hξ']
      calc
        (25 / 4 : ℝ) * Real.sqrt problem.characteristicQuantity ≤
            (25 / 4 : ℝ) * problem.characteristicQuantity := by
          gcongr
        _ ≤ 1 + 6 * problem.characteristicQuantity ^ (2 : ℕ) := by
          nlinarith [hξ']
    exact hbound.trans hscalar

end

/-! ### Definition_4_4_12 (from Chap04) -/
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁]

/- Definition 4.4.12 lies in the chapter's quadratic-regularized local-model domain.

Sampled owner-style declarations:
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the project owner for a
  centered quadratic regularization;
* `argmin[Set.univ] ...` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the
  canonical minimizer owner on the ambient space;
* `ModifiedGaussNewtonStep` below, the source-facing choice of a minimizing iterate map;
* `Definition_4_1_3`, the nearby chapter pattern where a source-facing step/value layer is built
  on a pre-existing model owner rather than duplicating the owner itself.

Source/core/bridge triage:
* source-facing: the modified Gauss--Newton step `V_M` on the feasible set and the derived
  quantities `r_M`, `f_M`, and `δ_M`;
* core/canonical: the centered regularized objective
  `quadraticallyRegularizedObjective (ψ x) M x`;
* bridge/view: ambient-point evaluations such as `pointAt`, `residualAt`, `modelValueAt`, and
  `modelGapAt`.

Primitive data:
* the local model family `ψ`;
* the feasible set `𝓕`;
* the regularization parameter `M`;
* the chosen minimizer map `V_M` valued in the canonical argmin owner.

Derived API:
* global minimality of `V_M(x)` for the canonical regularized objective at base point `x`;
* the residual `r_M`, model value `f_M`, and model gap `δ_M`;
* ambient-point views of the same quantities.

The objective owner is already canonical upstream, so this file keeps only the source-facing step
layer and derives its API from `quadraticallyRegularizedObjective (ψ x) M x` directly, without a
parallel ambient-point wrapper layer. -/

/-- Definition 4.4.12: on a feasible set `𝓕`, a modified Gauss--Newton step with parameter `M`
chooses, for each base point `x ∈ 𝓕`, a global minimizer `V_M(x)` of the quadratic-regularized
local model `y ↦ ψ(x; y) + (M / 2) ‖y - x‖²`. The associated quantities `r_M`, `f_M`, and `δ_M`
are defined from this chosen step in the namespace below; later results may impose `0 < M` when
that positivity is mathematically needed. -/
structure ModifiedGaussNewtonStep
    (ψ : E₁ → E₁ → ℝ) (𝓕 : Set E₁) (M : ℝ) where
  /-- The chosen modified Gauss--Newton iterate `V_M(x)` as a point of the canonical whole-space
  argmin set of the quadratic-regularized local model centered at `x`. -/
  minimizer (x : 𝓕) :
    argmin[Set.univ] (quadraticallyRegularizedObjective (ψ x) M x)

namespace ModifiedGaussNewtonStep

variable {ψ : E₁ → E₁ → ℝ} {𝓕 : Set E₁} {M : ℝ}

/-- A modified Gauss--Newton step acts on a base point by evaluation of its chosen iterate map
`V_M`. -/
instance : CoeFun (ModifiedGaussNewtonStep ψ 𝓕 M) (fun _ ↦ 𝓕 → E₁) where
  coe step x := step.minimizer x

/-- At every feasible base point `x`, the iterate `step x` belongs to the canonical whole-space
argmin set of the quadratic-regularized local model centered at `x`. -/
theorem mem_argmin
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    step x ∈ argmin[Set.univ] (quadraticallyRegularizedObjective (ψ x) M x) :=
  (step.minimizer x).2

/-- At every feasible base point `x`, the iterate `step x` globally minimizes the
quadratic-regularized local model centered at `x`. -/
theorem isMinOn_apply
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    IsMinOn (quadraticallyRegularizedObjective (ψ x) M x) Set.univ (step x) :=
  (mem_constrainedArgmin_iff.mp (step.mem_argmin x)).2

/-- The residual function `r_M(x) = ‖V_M(x) - x‖` on feasible base points. -/
def residual (step : ModifiedGaussNewtonStep ψ 𝓕 M) : 𝓕 → ℝ :=
  fun x ↦ ‖step x - x‖

/-- Evaluating `step.residual` recovers the textbook quantity `r_M(x) = ‖V_M(x) - x‖`. -/
@[simp]
theorem residual_apply
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    step.residual x = ‖step x - x‖ :=
  rfl

/-- The quadratic-regularized model value
`f_M(x) = ψ(x; V_M(x)) + (M / 2) r_M(x)^2` on feasible base points. -/
def modelValue (step : ModifiedGaussNewtonStep ψ 𝓕 M) : 𝓕 → ℝ :=
  fun x ↦ quadraticallyRegularizedObjective (ψ x) M x (step x)

/-- Evaluating `step.modelValue` recovers the textbook quantity
`f_M(x) = ψ(x; V_M(x)) + (M / 2) r_M(x)^2`. -/
@[simp]
theorem modelValue_def
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    step.modelValue x =
      ψ x (step x) + (M / 2 : ℝ) * (step.residual x) ^ (2 : ℕ) := by
  simp [modelValue]

/-- The model gap `δ_M(x) = f(x) - f_M(x)` between the merit objective and the
quadratic-regularized model value on feasible base points. -/
def modelGap (step : ModifiedGaussNewtonStep ψ 𝓕 M) (f : E₁ → ℝ) : 𝓕 → ℝ :=
  fun x ↦ f x - step.modelValue x

/-- Evaluating `step.modelGap f` gives the textbook quantity `δ_M(x) = f(x) - f_M(x)`. -/
@[simp]
theorem modelGap_def
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (f : E₁ → ℝ) (x : 𝓕) :
    step.modelGap f x = f x - step.modelValue x :=
  rfl

section WholeSpace

/-- On the whole space, the ambient-point step value at `x` needs no membership proof. -/
abbrev point
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) : E₁ :=
  step ⟨x, Set.mem_univ x⟩

/-- On the whole space, the minimizing-step property at `x` needs no membership proof. -/
theorem isMinOn_point
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    IsMinOn (quadraticallyRegularizedObjective (ψ x) M x) Set.univ (step.point x) := by
  simpa [point] using step.isMinOn_apply ⟨x, Set.mem_univ x⟩

/-- On the whole space, the residual `r_M(x)` needs no membership proof. -/
abbrev residualAtUniv
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) : ℝ :=
  step.residual ⟨x, Set.mem_univ x⟩

namespace ModifiedGaussNewtonStepWholeSpaceNotation

/-- Source-facing notation for the whole-space modified Gauss--Newton residual `r_M(x)` attached
to a chosen step owner. -/
scoped notation:max "r[" step:arg "]" =>
  ModifiedGaussNewtonStep.residualAtUniv step

/-- Pointwise source-facing notation for the whole-space modified Gauss--Newton residual
`r_M(x)`. -/
scoped notation:max "r[" step:arg "](" x:arg ")" =>
  ModifiedGaussNewtonStep.residualAtUniv step x

end ModifiedGaussNewtonStepWholeSpaceNotation

open scoped ModifiedGaussNewtonStepWholeSpaceNotation

/-- Evaluating `r[step](x)` recovers the textbook quantity `r_M(x) = ‖V_M(x) - x‖`. -/
@[simp]
theorem residualAtUniv_def
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    r[step](x) = ‖step.point x - x‖ := by
  rfl

/-- On the whole space, the quadratic-regularized model value `f_M(x)` needs no membership
proof. -/
abbrev modelValueAtUniv
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) : ℝ :=
  step.modelValue ⟨x, Set.mem_univ x⟩

namespace ModifiedGaussNewtonStepWholeSpaceNotation

/-- Source-facing notation for the whole-space modified Gauss--Newton model value `f_M(x)`
attached to a chosen step owner. -/
scoped notation:max "f[" step:arg "]" =>
  ModifiedGaussNewtonStep.modelValueAtUniv step

/-- Pointwise source-facing notation for the whole-space modified Gauss--Newton model value
`f_M(x)`. -/
scoped notation:max "f[" step:arg "](" x:arg ")" =>
  ModifiedGaussNewtonStep.modelValueAtUniv step x

end ModifiedGaussNewtonStepWholeSpaceNotation

open scoped ModifiedGaussNewtonStepWholeSpaceNotation

/-- Evaluating `f[step](x)` recovers the textbook quantity
`f_M(x) = ψ(x; V_M(x)) + (M / 2) r_M(x)^2`. -/
@[simp]
theorem modelValueAtUniv_def
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    f[step](x) =
      ψ x (step.point x) + (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) := by
  simp [modelValueAtUniv, point, residualAtUniv, modelValue]

/-- On the whole space, the model gap `δ_M(x) = f(x) - f_M(x)` needs no membership proof. -/
abbrev modelGapAtUniv
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (f : E₁ → ℝ) (x : E₁) : ℝ :=
  step.modelGap f ⟨x, Set.mem_univ x⟩

namespace ModifiedGaussNewtonStepWholeSpaceNotation

/-- Source-facing notation for the whole-space modified Gauss--Newton model gap `δ_M(x)`
attached to a chosen step owner and merit objective. -/
scoped notation:max "δ[" step:arg "; " f:arg "]" =>
  ModifiedGaussNewtonStep.modelGapAtUniv step f

/-- Pointwise source-facing notation for the whole-space modified Gauss--Newton model gap
`δ_M(x)`. -/
scoped notation:max "δ[" step:arg "; " f:arg "](" x:arg ")" =>
  ModifiedGaussNewtonStep.modelGapAtUniv step f x

end ModifiedGaussNewtonStepWholeSpaceNotation

open scoped ModifiedGaussNewtonStepWholeSpaceNotation

/-- Evaluating `δ[step; f](x)` gives the textbook quantity `δ_M(x) = f(x) - f_M(x)`. -/
@[simp]
theorem modelGapAtUniv_def
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (f : E₁ → ℝ) (x : E₁) :
    δ[step; f](x) = f x - f[step](x) := by
  rfl

end WholeSpace

end ModifiedGaussNewtonStep

end

/-! ### Definition_4_4_13 (from Chap04) -/
noncomputable section

universe u

open scoped ConvexAnalysis

variable {E₁ : Type u} [PseudoMetricSpace E₁]

/- Definition 4.4.13 lies in the local-model constrained-minimization domain on a
pseudo-metric ambient space.

Primary domain:
* local-model decrease quantities on closed trust-region balls
* the closed-ball specialization of the chapter's `EReal`-valued fiberwise-infimum owner

Sampled owner-style declarations:
* `partialInfProjection` in `Chap03/Theorem_3_1_2_3`, the chapter owner for constrained
  `EReal`-valued fiberwise infima
* `partialInfProjection_eq_sInf` in `Chap03/Theorem_3_1_2_3`, the canonical fiber-value
  specification theorem
* `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the chapter bridge from finite
  `EReal` values to real values
* `extendedRealRealPart_partialInfProjection_eq_sInf` in `Chap03/Theorem_3_1_2_3`, the finite
  real-surface bridge for a fiberwise infimum

Best owner abstraction:
* source-facing: the textbook decrease quantity on the finite-value locus of the closed-ball
  infimum
* core/canonical: the closed-ball specialization
  `partialInfProjection (localModelClosedBallRelation r) (Real.toEReal ∘ Function.uncurry ψ)`
* bridge/view: the pointwise real-valued decrease obtained after supplying a finiteness proof for
  the closed-ball partial infimum

Primitive data:
* the local model `ψ`
* the radius `r`
* the ambient pseudo-metric structure needed to form `Metric.closedBall x r`
* the closed-ball fiber relation `{z | z.2 ∈ Metric.closedBall z.1 r}` used to specialize
  `partialInfProjection`

Derived API:
* the finite-value domain of the canonical closed-ball specialization of `partialInfProjection`
* the finite-value domain `localModelFiniteDomain ψ r`
* the source-facing decrease `localModelDecrease f ψ r : localModelFiniteDomain ψ r → ℝ`
* the pointwise bridge `localModelDecreaseAt f ψ r x hx`
* the finite-locus bridge theorems recovering the textbook real infimum formula

Source/core/bridge triage:
* source-facing: `localModelDecrease f ψ r`
* core/canonical:
  `partialInfProjection (localModelClosedBallRelation r) (Real.toEReal ∘ Function.uncurry ψ)`
* bridge/view: `localModelDecreaseAt`,
  `localModelDecreaseAt_eq_sub_sInf`, and `mem_localModelFiniteDomain_of_bddBelow`

This refinement deletes the duplicate closed-ball optimal-value owner, names the Chapter 3
`partialInfProjection` specialization explicitly as the canonical owner, and makes the real-valued
textbook decrease live on the natural finite-value domain rather than totalizing non-finite
infima through `EReal.toReal`.
-/

private def localModelClosedBallRelation (r : NNReal) : Set (E₁ × E₁) :=
  {z | z.2 ∈ Metric.closedBall z.1 r}

/-- The finite-value locus of the closed-ball local-model partial infimum. -/
abbrev localModelFiniteDomain (ψ : E₁ → E₁ → ℝ) (r : NNReal) : Set E₁ :=
  dom (partialInfProjection (localModelClosedBallRelation r) (Real.toEReal ∘ Function.uncurry ψ))

private theorem uncurry_image_localModelClosedBallFiber_eq
    (ψ : E₁ → E₁ → ℝ) (r : NNReal) (x : E₁) :
    Function.uncurry ψ '' {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x} =
      ψ x '' Metric.closedBall x r := by
  ext t
  constructor
  · rintro ⟨⟨x', y⟩, hz, rfl⟩
    rcases hz with ⟨hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(x, y), ⟨hy, rfl⟩, rfl⟩

private theorem partialInfProjection_closedBall_eq_coe_sInf
    (ψ : E₁ → E₁ → ℝ) (r : NNReal) (x : E₁)
    (hψ : BddBelow (ψ x '' Metric.closedBall x r)) :
    partialInfProjection (localModelClosedBallRelation r)
        (Real.toEReal ∘ Function.uncurry ψ) x =
      (sInf (ψ x '' Metric.closedBall x r) : ℝ) := by
  let s : Set ℝ := ψ x '' Metric.closedBall x r
  have hs_nonempty : s.Nonempty := by
    refine ⟨ψ x x, ?_⟩
    exact ⟨x, Metric.mem_closedBall_self r.2, rfl⟩
  have hs_glb : IsGLB s (sInf s) := Real.isGLB_sInf hs_nonempty hψ
  have hs_glb' : IsGLB (((↑) : ℝ → EReal) '' s) ((sInf s : ℝ) : EReal) := by
    refine ⟨?_, ?_⟩
    · rintro z ⟨y, hy, rfl⟩
      exact_mod_cast hs_glb.1 hy
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          rcases hs_nonempty with ⟨y, hy⟩
          have hz_le : z ≤ (y : EReal) := hz ⟨y, hy, rfl⟩
          intro hz_eq_top
          rw [hz_eq_top] at hz_le
          simp at hz_le
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with z
        have hz' : ∀ y ∈ s, z ≤ y := by
          intro y hy
          exact_mod_cast (hz ⟨y, hy, rfl⟩)
        exact_mod_cast hs_glb.2 hz'
  have hs_nonempty' : (((↑) : ℝ → EReal) '' s).Nonempty := hs_nonempty.image _
  change
    partialInfProjection (localModelClosedBallRelation r)
        (Real.toEReal ∘ Function.uncurry ψ) x =
      (sInf (ψ x '' Metric.closedBall x r) : ℝ)
  rw [partialInfProjection_eq_sInf]
  have himage :
      sInf ((Real.toEReal ∘ Function.uncurry ψ) ''
        {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x}) =
        sInf (((↑) : ℝ → EReal) '' s) := by
    congr 1
    calc
      (Real.toEReal ∘ Function.uncurry ψ) ''
          {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x} =
        ((↑) : ℝ → EReal) ''
          (Function.uncurry ψ ''
            {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x}) := by
              ext z
              constructor
              · rintro ⟨p, hp, rfl⟩
                exact ⟨Function.uncurry ψ p, ⟨p, hp, rfl⟩, rfl⟩
              · rintro ⟨t, ⟨p, hp, rfl⟩, rfl⟩
                exact ⟨p, hp, rfl⟩
      _ = ((↑) : ℝ → EReal) '' s := by
        rw [uncurry_image_localModelClosedBallFiber_eq]
  rw [himage]
  exact hs_glb'.csInf_eq hs_nonempty'

/-- A bounded-below local-model image yields a finite value of the canonical Chapter 3 closed-ball
partial infimum at the center point, so the finite-locus bridge applies there. -/
theorem mem_localModelFiniteDomain_of_bddBelow
    (ψ : E₁ → E₁ → ℝ) (r : NNReal) (x : E₁)
    (hψ : BddBelow (ψ x '' Metric.closedBall x r)) :
    x ∈ localModelFiniteDomain ψ r := by
  constructor <;> intro hx
  · change
      partialInfProjection (localModelClosedBallRelation r)
          (Real.toEReal ∘ Function.uncurry ψ) x = ⊤ at hx
    rw [partialInfProjection_closedBall_eq_coe_sInf ψ r x hψ] at hx
    simp at hx
  · change
      partialInfProjection (localModelClosedBallRelation r)
          (Real.toEReal ∘ Function.uncurry ψ) x = ⊥ at hx
    rw [partialInfProjection_closedBall_eq_coe_sInf ψ r x hψ] at hx
    simp at hx

/-- A pointwise nonnegative local model has a closed-ball image that is bounded below by `0`. -/
theorem bddBelow_image_closedBall_of_nonneg
    (ψ : E₁ → E₁ → ℝ) (r : NNReal)
    (hψ : ∀ x y, 0 ≤ ψ x y) (x : E₁) :
    BddBelow (ψ x '' Metric.closedBall x r) := by
  refine ⟨0, ?_⟩
  rintro z ⟨y, -, rfl⟩
  exact hψ x y

/-- Definition 4.4.13: for a radius `r`, `localModelDecrease f ψ r` is the textbook decrease
quantity `Δ_r` on the natural finite-value locus of the closed-ball local-model partial infimum.
At a point `x` together with a proof that the Chapter 3 partial infimum is finite there, the
companion bridge theorem `localModelDecreaseAt_eq_sub_sInf` recovers the textbook formula
`Δ_r(x) = f x - inf_{y ∈ B̄(x,r)} ψ(x;y)`. -/
def localModelDecrease
    (f : E₁ → ℝ) (ψ : E₁ → E₁ → ℝ) (r : NNReal) :
    localModelFiniteDomain ψ r → ℝ :=
  fun x ↦
    f x - extendedRealRealPart
      (partialInfProjection
        (localModelClosedBallRelation r)
        (Real.toEReal ∘ Function.uncurry ψ)) x

/-- Pointwise evaluation of the finite-domain local-model decrease after supplying a finiteness
proof for the canonical closed-ball partial infimum. -/
abbrev localModelDecreaseAt
    (f : E₁ → ℝ) (ψ : E₁ → E₁ → ℝ) (r : NNReal)
    (x : E₁) (hx : x ∈ localModelFiniteDomain ψ r) : ℝ :=
  localModelDecrease f ψ r ⟨x, hx⟩

/-
Source-facing Lean notation for the textbook local-model decrease quantity `Δ_r(x)` after
supplying the required finiteness proof for the canonical closed-ball partial infimum.
-/
namespace LocalModelNotation

scoped notation:max "Δ[" f:arg "; " ψ:arg "; " r:arg "](" x:arg "; " hx:arg ")" =>
  localModelDecreaseAt f ψ r x hx

end LocalModelNotation

open scoped LocalModelNotation

/-- On the finite locus of the canonical Chapter 3 partial infimum, the source-facing quantity
`Δ_r(x)` is exactly `f x` minus the real infimum of the local model over `Metric.closedBall x r`.
-/
theorem localModelDecreaseAt_eq_sub_sInf
    (f : E₁ → ℝ) (ψ : E₁ → E₁ → ℝ) (r : NNReal)
    (x : E₁) (hx : x ∈ localModelFiniteDomain ψ r) :
    Δ[f; ψ; r](x; hx) = f x - sInf (ψ x '' Metric.closedBall x r) := by
  change f x - extendedRealRealPart
      (partialInfProjection
        (localModelClosedBallRelation r)
        (Real.toEReal ∘ Function.uncurry ψ)) x =
    f x - sInf (ψ x '' Metric.closedBall x r)
  congr 1
  calc
    extendedRealRealPart
        (partialInfProjection
          (localModelClosedBallRelation r)
          (Real.toEReal ∘ Function.uncurry ψ)) x =
      sInf (Function.uncurry ψ ''
        {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x}) := by
          simpa using extendedRealRealPart_partialInfProjection_eq_sInf hx
    _ = sInf (ψ x '' Metric.closedBall x r) := by
      rw [uncurry_image_localModelClosedBallFiber_eq]

/-- If the local-model values on the radius-`r` closed ball are bounded below, then evaluating the
source-facing quantity at `x` recovers the textbook real closed-ball infimum formula. -/
theorem localModelDecreaseAt_eq_sub_sInf_of_bddBelow
    (f : E₁ → ℝ) (ψ : E₁ → E₁ → ℝ) (r : NNReal) (x : E₁)
    (hψ : BddBelow (ψ x '' Metric.closedBall x r)) :
    Δ[f; ψ; r](x; (mem_localModelFiniteDomain_of_bddBelow ψ r x hψ)) =
      f x - sInf (ψ x '' Metric.closedBall x r) := by
  simpa using localModelDecreaseAt_eq_sub_sInf f ψ r x
    (mem_localModelFiniteDomain_of_bddBelow ψ r x hψ)

end

/-! ### Definition_4_4_14 (from Chap04) -/
universe u v

open scoped LevelSetNotation

/-
Definition 4.4.14 lies in the order/set-theoretic sublevel-set domain.

Sampled owner-style declarations:
- project `Definition_1_4_8`, which already owns `𝓛[f](τ)`, `mem_levelSet_iff`, and
  `levelSet_eq_setOf`
- project `Definition_4_1_1`, the chapter recall of that same owner surface
- mathlib `Set.Iic`
- mathlib `Set.preimage`

Best owner abstraction:
- source-facing: the recalled level-set notation `𝓛[f](τ)` for a function `f`
- core/canonical: `(f ⁻¹' Set.Iic τ : Set E)`
- bridge/view: `levelSet_eq_setOf`

Primitive data:
- a function `f : E → ℝ`
- a threshold `τ : ℝ`

Derived API:
- `mem_levelSet_iff`
- `levelSet_eq_setOf`

Source/core/bridge triage:
- source-facing: Definition 4.4.14's recalled level-set notation `𝓛[f](τ)`
- core/canonical: the Chapter 1 owner surface imported through `Definition_4_1_1`
- bridge/view: the imported atomic pointwise and set-builder lemmas

This numbered item adds no new owner-layer mathematics. It is a pure recall/use surface for the
existing chapter sublevel-set API, so it reuses the imported notation and companion lemmas
directly instead of defining them again.
-/

section

variable {E : Type u} {α : Type v} [Preorder α]
variable (f : E → α) (τ : α)

/- Definition 4.4.14: the level set `𝓛[f](τ)` is the recalled owner surface for the canonical
sublevel set of `f` at level `τ`. -/
#check (𝓛[f](τ) : Set E)

recall mem_levelSet_iff {f : E → α} {τ : α} {x : E} :
    x ∈ 𝓛[f](τ) ↔ f x ≤ τ

recall levelSet_eq_setOf (f : E → α) (τ : α) :
    (𝓛[f](τ) : Set E) = {x | f x ≤ τ}

end

/-! ### Definition_4_4_15 (from Chap04) -/
universe u v

/- Definition 4.4.15 lies in the nonlinear-equation / distance-to-solution-set domain.

Sampled owner-style declarations:
* `SmoothNonlinearEquationProblem.solutionSet` in `Definition_4_4_8`, the chapter owner for
  exact solutions of a nonlinear system;
* `𝓛[f](τ)` and `mem_levelSet_iff` in `Definition_4_4_14`, the recalled owner for sublevel sets;
* `IsLeast` in mathlib, the canonical order-theoretic owner for an attained minimum;
* `Metric.isGLB_infDist` and `IsClosed.exists_infDist_eq_dist`, the metric bridge lemmas relating
  an attained minimum to the canonical infimum distance.

Best owner abstraction:
* source-facing: the exact-solution sublevel set through `x₀` and the attained-distance set
  attached to an arbitrary residual map;
* core/canonical: `solutionSet`, `𝓛[f](f x₀)`, and `IsLeast`;
* bridge/view: the comparison with `Metric.infDist x₀ (...)`, and the later specialization to
  bundled smooth maps used by the modified Gauss--Newton development.

Primitive data:
* a residual map `problem`;
* a real-valued function `f`;
* a base point `x₀`.

Derived API:
* the set of exact solutions lying in `𝓛[f](f x₀)`;
* the distance image set realized on that solution set;
* the source-facing minimum statement `IsLeast (solutionSublevelDistanceSet problem f x₀) D`;
* companion bridges to `Metric.infDist`.
-/

open SmoothNonlinearEquationProblem
open scoped LevelSetNotation

variable {E₁ : Type u} {E₂ : Type v} [Zero E₂]

/-- The exact solutions of `problem` that lie in the sublevel set `𝓛[f](f x₀)`. -/
def solutionSublevelSet
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) (x0 : E₁) : Set E₁ :=
  𝓛[f]((f x0)) ∩ solutionSet problem

/-- Membership in `solutionSublevelSet problem f x₀` means belonging to `𝓛[f](f x₀)` and solving
the equation `problem x = 0`. -/
@[simp] theorem mem_solutionSublevelSet_iff
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) (x0 x : E₁) :
    x ∈ solutionSublevelSet problem f x0 ↔ x ∈ 𝓛[f]((f x0)) ∧ problem x = 0 := by
  simp [solutionSublevelSet]

/-- For a merit reformulation `x ↦ φ (problem x)`, every exact solution already lies in the
sublevel set through `x₀`, so `solutionSublevelSet` reduces to `solutionSet`. -/
theorem solutionSublevelSet_eq_solutionSet_of_meritFunctionReformulation
    (problem : E₁ → E₂)
    (φ : E₂ → ℝ) [IsMeritFunction φ]
    (x0 : E₁) :
    solutionSublevelSet problem (meritFunctionReformulation problem φ) x0 =
      solutionSet problem := by
  ext x
  constructor
  · intro hx
    have hmem :=
      (mem_solutionSublevelSet_iff problem (meritFunctionReformulation problem φ) x0 x).1 hx
    exact hmem.2
  · intro hx
    refine
      (mem_solutionSublevelSet_iff problem (meritFunctionReformulation problem φ) x0 x).2 ?_
    refine ⟨?_, hx⟩
    rw [mem_levelSet_iff]
    have hxzero : meritFunctionReformulation problem φ x = 0 := by
      simpa [meritFunctionReformulation] using
        (IsMeritFunction.eq_zero_iff (problem x)).2 hx
    exact hxzero.le.trans (IsMeritFunction.nonneg (problem x0))

section

variable [NormedAddCommGroup E₁]

/-- The set of distances from `x₀` attained by exact solutions in the sublevel set
`𝓛[f](f x₀)`. -/
def solutionSublevelDistanceSet
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) (x0 : E₁) : Set ℝ :=
  (fun x : E₁ ↦ ‖x - x0‖) '' solutionSublevelSet problem f x0

/-- Membership in `solutionSublevelDistanceSet problem f x₀` means that the radius is realized by
an exact solution lying in `𝓛[f](f x₀)`. -/
@[simp] theorem mem_solutionSublevelDistanceSet_iff
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) {x0 : E₁} {r : ℝ} :
    r ∈ solutionSublevelDistanceSet problem f x0 ↔
      ∃ x : E₁, x ∈ 𝓛[f]((f x0)) ∧ problem x = 0 ∧ ‖x - x0‖ = r := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (mem_solutionSublevelSet_iff problem f x0 x).1 hx with ⟨hxlevel, hxsol⟩
    exact ⟨x, hxlevel, hxsol, rfl⟩
  · rintro ⟨x, hxlevel, hxsol, hdist⟩
    exact ⟨x, (mem_solutionSublevelSet_iff problem f x0 x).2 ⟨hxlevel, hxsol⟩, hdist⟩

/-- For a merit reformulation, the source-facing attained-distance owner from Definition 4.4.15
agrees with the direct distance image of the exact solution set. -/
theorem solutionSublevelDistanceSet_eq_image_solutionSet_of_meritFunctionReformulation
    (problem : E₁ → E₂)
    (φ : E₂ → ℝ) [IsMeritFunction φ]
    (x0 : E₁) :
    solutionSublevelDistanceSet problem (meritFunctionReformulation problem φ) x0 =
      (fun y : E₁ ↦ ‖y - x0‖) '' solutionSet problem := by
  simp [solutionSublevelDistanceSet,
    solutionSublevelSet_eq_solutionSet_of_meritFunctionReformulation]

/-- An attained minimum distance on `solutionSublevelDistanceSet problem f x₀` agrees with the
canonical infimum distance to `solutionSublevelSet problem f x₀`. -/
theorem infDist_eq_of_isLeast_solutionSublevelDistanceSet
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) {x0 : E₁} {D : ℝ}
    (hD : IsLeast (solutionSublevelDistanceSet problem f x0) D) :
    Metric.infDist x0 (solutionSublevelSet problem f x0) = D := by
  rcases hD.1 with ⟨y, hy, hyD⟩
  have hs : (solutionSublevelSet problem f x0).Nonempty := ⟨y, hy⟩
  have hglb :
      IsGLB ((fun z : E₁ ↦ dist x0 z) '' solutionSublevelSet problem f x0) D := by
    simpa [solutionSublevelDistanceSet, dist_eq_norm, norm_sub_rev] using hD.isGLB
  exact (Metric.isGLB_infDist hs).unique hglb

/-- If the exact-solution sublevel set is closed and nonempty in a proper space, then the metric
infimum distance is attained there, hence it is the least element of
`solutionSublevelDistanceSet problem f x₀`. -/
theorem isLeast_solutionSublevelDistanceSet_infDist
    [ProperSpace E₁]
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) {x0 : E₁}
    (hclosed : IsClosed (solutionSublevelSet problem f x0))
    (hsol : (solutionSublevelSet problem f x0).Nonempty) :
    IsLeast (solutionSublevelDistanceSet problem f x0)
      (Metric.infDist x0 (solutionSublevelSet problem f x0)) := by
  obtain ⟨y, hy, hyD⟩ := hclosed.exists_infDist_eq_dist hsol x0
  refine ⟨?_, ?_⟩
  · refine ⟨y, hy, ?_⟩
    simpa [solutionSublevelDistanceSet, dist_eq_norm, norm_sub_rev] using hyD.symm
  · intro r hr
    rcases hr with ⟨z, hz, rfl⟩
    have hdist : Metric.infDist x0 (solutionSublevelSet problem f x0) ≤ dist x0 z :=
      Metric.infDist_le_dist_of_mem hz
    simpa [solutionSublevelDistanceSet, dist_eq_norm, norm_sub_rev] using
      hdist

section

variable (problem : E₁ → E₂) (f : E₁ → ℝ) (x0 : E₁) (D : ℝ)

/- Definition 4.4.15: the textbook quantity
`min {‖x - x₀‖ : x ∈ 𝓛[f](f x₀), problem x = 0}`
is the attained-minimum statement
`IsLeast (solutionSublevelDistanceSet problem f x₀) D`.
The always-defined metric infimum `Metric.infDist x₀ (solutionSublevelSet problem f x₀)` appears
only as a companion bridge under additional hypotheses. -/
set_option linter.hashCommand false in
#check IsLeast (solutionSublevelDistanceSet problem f x0) D

end

end

/-! ### Definition_4_4_16 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 4.4.16 lies in the unconstrained modified-Newton problem domain.

Primary domain:
* unconstrained strongly convex objectives with globally Lipschitz second derivative on real
  normed spaces

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem.unconstrained`, the chapter owner for a whole-space
  objective viewed as a canonical minimization problem
* `StrongConvexOn Set.univ σ f`, the chapter/mathlib owner for whole-space strong convexity
* `HasLipschitzContinuousHessian L f`, written on theorem surfaces as `f ∈ C22[L]`, the chapter
  owner for global `C²` second-derivative Lipschitz regularity, with the Hilbert Hessian surface
  recovered only in downstream files
* `StrongConvexOn.eq_of_isMinOn` in `Chap03/Corollary_3_2_3`, the chapter owner for uniqueness of
  a minimizer of a positive strongly convex objective
* `modifiedNewtonCharacteristicQuantity` in `Proposition_4_4_10`, the chapter owner for the
  scalar quantity `L ‖x₀ - x*‖ / σ`

Best owner abstraction:
* source-facing: the bundled modified Gauss--Newton problem data in this file
* core/canonical: `SetConstrainedMinimizationProblem.unconstrained problem.objective`,
  `StrongConvexOn Set.univ σ problem.objective`, and `problem.objective ∈ C22[L]`
* bridge/view: `problem.toSetConstrainedMinimizationProblem` and `problem.characteristicQuantity`

Primitive data:
* the objective `f`, strong-convexity modulus `σ`, Hessian-Lipschitz constant `L`, minimizer
  `xStar`, and initial point `x0`
* positive strong convexity, the whole-space strong-convexity owner, the whole-space
  second-derivative Lipschitz owner, and the chosen global minimizer

Derived API:
* the canonical whole-space minimization owner `problem.toSetConstrainedMinimizationProblem`
* coercion to the underlying objective via that owner
* `ContDiff ℝ 2 problem.objective`, supplied directly by `problem.objective_mem.contDiff`
* uniqueness of the chosen minimizer, supplied by `StrongConvexOn.eq_of_isMinOn`
* `initialDistance`
* `characteristicQuantity`, defined by direct reuse of the canonical modified-Newton owner
-/

/- Definition 4.4.16: a modified Gauss--Newton problem consists of a whole-space objective `f`
on a real normed space, a positive strong-convexity modulus `σ`, a global second-derivative
Lipschitz constant `L`, the canonical owner hypotheses `StrongConvexOn Set.univ σ f` and
`f ∈ C22[L]`, a chosen global minimizer `xStar`, and an initial point `x0`. The ambient
whole-space minimization problem is recovered by the bridge
`problem.toSetConstrainedMinimizationProblem`, while convexity, `C²` regularity, and uniqueness
of the minimizer are derived from the owner fields rather than stored as extra primitive data. -/
structure ModifiedGaussNewtonProblem where
  objective : E → ℝ
  σ : ℝ
  L : NNReal
  xStar : E
  x0 : E
  sigma_pos : 0 < σ
  objective_strongConvex : StrongConvexOn Set.univ σ objective
  objective_mem : objective ∈ C22[L]
  xStar_isMin : IsMinOn objective Set.univ xStar

namespace ModifiedGaussNewtonProblem

variable {E}

/-- Forgetting the extra strong-convexity and regularity data gives the canonical whole-space
minimization problem with objective `problem.objective`. -/
abbrev toSetConstrainedMinimizationProblem
    (problem : ModifiedGaussNewtonProblem E) : SetConstrainedMinimizationProblem E :=
  .unconstrained problem.objective

/-- The feasible set of the canonical whole-space bridge is all of `E`. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : ModifiedGaussNewtonProblem E) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = Set.univ :=
  rfl

/-- Evaluating the canonical whole-space bridge recovers the underlying objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : ModifiedGaussNewtonProblem E) (x : E) :
    problem.toSetConstrainedMinimizationProblem x = problem.objective x :=
  rfl

/-- A modified Gauss--Newton problem can be evaluated as its underlying objective function. -/
instance : CoeFun (ModifiedGaussNewtonProblem E) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- The objective of a modified Gauss--Newton problem is `C²`. -/
theorem contDiff (problem : ModifiedGaussNewtonProblem E) :
    ContDiff ℝ 2 problem.objective :=
  problem.objective_mem.contDiff

/-- The chosen minimizer of a modified Gauss--Newton problem is the unique global minimizer. -/
theorem eq_xStar_of_isMinOn
    (problem : ModifiedGaussNewtonProblem E) {y : E} (hy : IsMinOn problem Set.univ y) :
    y = problem.xStar :=
  problem.objective_strongConvex.eq_of_isMinOn
    problem.sigma_pos (by simp) hy (by simp) problem.xStar_isMin

/-- The initial distance `D = ‖x₀ - x*‖` attached to a modified Gauss--Newton problem. -/
def initialDistance (problem : ModifiedGaussNewtonProblem E) : ℝ :=
  ‖problem.x0 - problem.xStar‖

/-- The characteristic quantity `ξ = L D / σ` attached to a modified Gauss--Newton problem. -/
abbrev characteristicQuantity (problem : ModifiedGaussNewtonProblem E) : ℝ :=
  modifiedNewtonCharacteristicQuantity problem.σ problem.L problem.x0 problem.xStar

/-- Expanding `initialDistance` gives the textbook definition `D = ‖x₀ - x*‖`. -/
@[simp] theorem initialDistance_def (problem : ModifiedGaussNewtonProblem E) :
    problem.initialDistance = ‖problem.x0 - problem.xStar‖ :=
  rfl

/-- Expanding `characteristicQuantity` gives the textbook definition `ξ = L D / σ`. -/
@[simp] theorem characteristicQuantity_def (problem : ModifiedGaussNewtonProblem E) :
    problem.characteristicQuantity = (problem.L : ℝ) * problem.initialDistance / problem.σ :=
  rfl

end ModifiedGaussNewtonProblem

/-! ### Definition_4_4_17 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {φ : E → ℝ} {x : E}

/- Definition 4.4.17 lies in the unconstrained smooth minimization / stationarity-reformulation
domain on real Hilbert spaces.

Sampled owner-style declarations:
* `gradient`, recalled in `Chap01/Definition_1_4_7`, the canonical stationarity map `x ↦ ∇ φ x`;
* `fderiv`, recalled in `Chap04/Definition_4_4_7`, the canonical Jacobian owner for a map;
* `hessian` from `Chap01/Definition_1_4_16`, the Jacobian of the gradient map;
* `HasGradientAt.fderiv_apply`, the scalar derivative/gradient bridge used elsewhere in the
  chapter.

Best owner abstraction:
* core/canonical: the gradient map `∇ φ`, with Jacobian `hessian φ x`.

Primitive data:
* a smooth objective `φ`.

Derived API:
* the stationarity equation `∇ φ x = 0`;
* the Jacobian/Hessian operator `hessian φ x = fderiv ℝ (∇ φ) x`.

Source/core/bridge triage:
* source-facing: rewriting unconstrained minimization as the nonlinear equation `∇ φ x = 0`;
* core/canonical: `gradient` and `hessian`;
* bridge/view: the Jacobian description `fderiv ℝ (∇ φ) x`.

This item therefore introduces no parallel Chapter 4 definition of the stationarity map: the
textbook `F` is exactly the existing gradient owner, and its derivative is exactly the existing
Hessian owner. -/

/- Definition 4.4.17: the stationarity map for unconstrained minimization is the canonical
gradient map. -/
#check (∇ φ)

/- Its Jacobian at `x` is the canonical Hessian operator, equivalently `fderiv ℝ (∇ φ) x`. -/
#check (hessian φ x)
#check (fderiv ℝ (∇ φ) x)

end

/-! ### Definition_4_4_18 (from Chap04) -/
noncomputable section

open Metric
open scoped InnerProduct
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

/- Definition 4.4.18 lies in the modified Gauss--Newton optimal-value / strong-dual norm-duality
domain.

Sampled owner-style declarations:
* `modifiedGaussNewtonOptimalValueAt` in `Proposition_4_4_6`, the chapter owner for the
  whole-space quadratic-regularized optimal value;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the chapter owner for the affine
  residual model;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the project owner for the
  centered quadratic penalty inside that optimal-value owner;
* `dual_norm_eq_sSup_closedUnitBall` in `Definition_4_4_4`, the chapter bridge expressing the
  strong-dual norm as a support function of the closed unit ball;
* `ContinuousLinearMap.comp` in mathlib, the canonical owner for precomposing a strong-dual
  functional with a continuous linear map;
* `InnerProductSpace.toDual` in mathlib, the Chapter 4 bridge from Hilbert-space vectors to the
  intrinsic strong dual.

Best owner abstraction:
* core/canonical: `modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x`

Source/core/bridge triage:
* source-facing: the specialized auxiliary value `f_M(x)` for the norm merit and its dual-ball
  formula;
* core/canonical: the Chapter 4 optimal-value owner above;
* bridge/view: the step-variable expansion, the strong-dual closed-ball objective, and the
  Hilbert-space `toDual` specialization.

Primitive data:
* a residual map `F`;
* a Jacobian family `J`;
* a base point `x`.

Derived API:
* the step-variable `sInf` expansion of the canonical owner;
* the positive-parameter dual objective over the closed unit ball in the strong dual;
* the `toDual` specialization recovering the textbook adjoint formula on Hilbert-space vectors.

This refinement deletes the duplicate local `ℝ`-valued infimum owner and reuses the Chapter 4
canonical owner directly. The file now keeps only the norm-specific bridge API. -/

variable {E₁ : Type u} {E₂ : Type v}

section AuxiliaryValue

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

variable (F : E₁ → E₂) (J : E₁ → E₁ →L[ℝ] E₂) (x : E₁)

/- Definition 4.4.18: the specialized auxiliary value `f_M(x)` for the merit `u ↦ ‖u‖` is the
canonical Chapter 4 optimal-value owner specialized to the norm local model. -/
set_option linter.hashCommand false in
#check (modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x : ℝ → EReal)

/-- Unfolding the canonical norm-specialized optimal-value owner recovers the textbook infimum of
the quadratic-regularized linearized residual objective over all steps `h`. -/
theorem modifiedGaussNewtonOptimalValueAt_norm_eq_sInf_range
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x M =
      sInf (Set.range fun h ↦
        (‖F x + J x h‖ + (M / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) : EReal)) := sorry

end AuxiliaryValue

section DualObjective

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The intrinsic strong-dual objective corresponding to the norm auxiliary problem at a positive
regularization parameter `M`. -/
def modifiedGaussNewtonNormDualObjective
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) : StrongDual ℝ E₂ → ℝ :=
  fun s ↦ s (F x) -
    (1 / (2 * (M : ℝ)) : ℝ) * ‖s.comp (J x)‖ ^ (2 : ℕ)

/-- Evaluating the intrinsic strong-dual objective gives the canonical precomposition formula. -/
@[simp] theorem modifiedGaussNewtonNormDualObjective_apply
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) (s : StrongDual ℝ E₂) :
    modifiedGaussNewtonNormDualObjective F J M x s =
      s (F x) -
        (1 / (2 * (M : ℝ)) : ℝ) * ‖s.comp (J x)‖ ^ (2 : ℕ) := by
  rfl

/-- For positive `M`, the canonical norm-specialized auxiliary value equals the supremum of the
intrinsic strong-dual objective over the closed unit ball of the residual strong dual. -/
theorem modifiedGaussNewtonOptimalValueAt_norm_eq_sSup_dualObjective
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x (M : ℝ) =
      sSup ((((↑) : ℝ → EReal) ∘ modifiedGaussNewtonNormDualObjective F J M x) ''
          closedBall (0 : StrongDual ℝ E₂) 1) :=
  sorry

end DualObjective

section DualBridge

variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- Under the Riesz identification, the intrinsic strong-dual objective specializes to the
textbook Hilbert-space formula with the adjoint of `J x`. -/
@[simp] theorem modifiedGaussNewtonNormDualObjective_toDual
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) (s : E₂) :
    modifiedGaussNewtonNormDualObjective F J M x (InnerProductSpace.toDual ℝ E₂ s) =
      inner ℝ s (F x) -
        (1 / (2 * (M : ℝ)) : ℝ) * ‖(J x).adjoint s‖ ^ (2 : ℕ) := by
  simp [modifiedGaussNewtonNormDualObjective,
    show (InnerProductSpace.toDual ℝ E₂ s).comp (J x) =
        InnerProductSpace.toDual ℝ E₁ ((J x).adjoint s) by
    ext y
    simp [ContinuousLinearMap.adjoint_inner_left]]

end DualBridge

end
