import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Assumption_4_4_1 (from Chap04) -/
noncomputable section

universe u

/- Assumption 4.4.1 lies in the local first-order smoothness domain for real-valued functions on
feasible subsets of real normed spaces.

Sampled owner-style declarations:
* mathlib `DifferentiableOn ℝ f 𝓕`
* mathlib `UniqueDiffOn ℝ 𝓕`
* mathlib `LipschitzOnWith L g 𝓕`
* mathlib `contDiffOn_succ_iff_fderivWithin`
* Chapter 1's whole-space owner pair `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` in
  `LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_5_2`

Best owner abstraction:
* source-facing: `HasLipschitzDerivativeOnWith L 𝓕 f`
* core/canonical: the primitive triple `DifferentiableOn ℝ f 𝓕`, `UniqueDiffOn ℝ 𝓕`, and
  `LipschitzOnWith L (fun x ↦ fderivWithin ℝ f 𝓕 x) 𝓕`
* bridge/view: on open sets, the ambient-derivative reformulation through `fderiv`; on
  `Set.univ`,
  the whole-space `ContDiff ℝ 1 f`

Primitive data:
* the feasible set `𝓕`
* the objective `f`
* differentiability of `f` on `𝓕`
* unique differentiability of `𝓕`, making the within derivative intrinsic
* the Lipschitz bound for the derivative map `x ↦ fderivWithin ℝ f 𝓕 x` on `𝓕`

Derived API:
* continuity of the within derivative map on `𝓕`
* `ContDiffOn ℝ 1 f 𝓕` on the feasible set
* on open feasible sets, continuity and Lipschitz control for the ambient derivative map
* the whole-space specialization `ContDiff ℝ 1 f` on `Set.univ`

The source statement is genuinely local and on-set, so it should remain a source-facing owner
instead of being collapsed into the Chapter 1 whole-space Hilbert-space owner pair. The refine
work here is therefore to keep that local owner thin on the canonical within-derivative layer,
with the ambient `fderiv` view only as an open-set bridge, not to introduce a parallel wrapper
around already existing global owners.
-/

/-- Assumption 4.4.1: a real-valued function on a subset `𝓕` of a real normed space has a
Lipschitz-continuous derivative with constant `L` when it is differentiable on the uniquely
differentiable feasible set `𝓕` and its canonical within-derivative map
`x ↦ fderivWithin ℝ f 𝓕 x` is `L`-Lipschitz on `𝓕`. On open feasible sets this agrees with the
ambient derivative formulation. -/
class HasLipschitzDerivativeOnWith (L : NNReal) {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (𝓕 : Set E) (f : E → ℝ) : Prop where
  /-- The function is differentiable on the feasible set. -/
  differentiableOn : DifferentiableOn ℝ f 𝓕
  /-- The feasible set is uniquely differentiable, so the within derivative is intrinsic. -/
  uniqueDiffOn : UniqueDiffOn ℝ 𝓕
  /-- The derivative map is `L`-Lipschitz on the feasible set. -/
  lipschitz : LipschitzOnWith L (fun x ↦ fderivWithin ℝ f 𝓕 x) 𝓕

namespace HasLipschitzDerivativeOnWith

variable {L : NNReal} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝓕 : Set E} {f : E → ℝ}

/-- The canonical within-derivative map in Assumption 4.4.1 is continuous on the feasible set
because every Lipschitz map is continuous on its domain. -/
theorem continuousOn_fderivWithin
    (hf : HasLipschitzDerivativeOnWith L 𝓕 f) :
    ContinuousOn (fderivWithin ℝ f 𝓕) 𝓕 :=
  hf.lipschitz.continuousOn

/-- Assumption 4.4.1 upgrades the objective to a `C¹` function on the feasible set in the
canonical mathlib within-set sense. -/
theorem contDiffOn
    (hf : HasLipschitzDerivativeOnWith L 𝓕 f) :
    ContDiffOn ℝ 1 f 𝓕 := by
  simpa [contDiffOn_zero] using
    (contDiffOn_succ_iff_fderivWithin hf.uniqueDiffOn).2
      ⟨hf.differentiableOn, by simp, contDiffOn_zero.mpr hf.continuousOn_fderivWithin⟩

/-- On an open feasible set, the within-derivative control from Assumption 4.4.1 is exactly the
ambient derivative control. -/
theorem lipschitz_fderiv_of_isOpen
    (hf : HasLipschitzDerivativeOnWith L 𝓕 f) (h𝓕 : IsOpen 𝓕) :
    LipschitzOnWith L (fun x ↦ fderiv ℝ f x) 𝓕 := by
  intro x hx y hy
  simpa [fderivWithin_of_isOpen h𝓕 hx, fderivWithin_of_isOpen h𝓕 hy] using hf.lipschitz hx hy

/-- On an open feasible set, Assumption 4.4.1 also gives continuity of the ambient derivative
map. -/
theorem continuousOn_fderiv_of_isOpen
    (hf : HasLipschitzDerivativeOnWith L 𝓕 f) (h𝓕 : IsOpen 𝓕) :
    ContinuousOn (fderiv ℝ f) 𝓕 :=
  (hf.lipschitz_fderiv_of_isOpen h𝓕).continuousOn

/-- The whole-space specialization of Assumption 4.4.1 yields global `C¹` regularity. -/
theorem contDiff
    (hf : HasLipschitzDerivativeOnWith L Set.univ f) :
    ContDiff ℝ 1 f := by
  simpa [contDiffOn_univ] using hf.contDiffOn

/-- The whole-space specialization of Assumption 4.4.1 yields ordinary differentiability on the
ambient normed space. -/
theorem differentiable
    (hf : HasLipschitzDerivativeOnWith L Set.univ f) :
    Differentiable ℝ f :=
  differentiableOn_univ.mp hf.differentiableOn

end HasLipschitzDerivativeOnWith

/-- Constant real-valued functions have Lipschitz-continuous derivative on any uniquely
differentiable feasible set for every Lipschitz constant. -/
instance {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : NNReal) (𝓕 : Set E) (h𝓕 : UniqueDiffOn ℝ 𝓕) (c : ℝ) :
    HasLipschitzDerivativeOnWith L 𝓕 (fun _ : E ↦ c) where
  differentiableOn := differentiableOn_const c
  uniqueDiffOn := h𝓕
  lipschitz := by
    simpa [fderivWithin_const] using
      (LipschitzWith.const' (0 : E →L[ℝ] ℝ)).lipschitzOnWith

/-! ### Corollary_4_4_1 (from Chap04) -/
noncomputable section

open SetConstrainedMinimizationProblem
open scoped LevelSetNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E]
variable {f : E → ℝ} {ψ : E → E → ℝ}
variable {𝓕 : Set E} {L M : ℝ}

/- Corollary 4.4.1 lies in the modified Gauss--Newton whole-space step / optimal-value bridge
domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet` in
  `Chap01/Definition_1_3_7`, the canonical owner and pointwise upper-bound API for whole-space
  optimal values;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the owner objective whose
  optimal value is `f_M(x)`;
* `modifiedGaussNewtonOptimalValueAt` and `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv`
  in `Proposition_4_4_6`, the chapter owner for the intrinsic quantity `f_M(x)` and its attained
  whole-space bridge;
* `IsMinOn` and `isMinOn_univ_iff` in mathlib, the canonical owner for global minimizers.

Source/core/bridge triage:
* source-facing: the textbook upper bound on the modified Gauss--Newton model value `f_M(x)`;
* core/canonical: `modifiedGaussNewtonOptimalValueAt ψ x M`;
* bridge/view: the whole-space attained-value identity
  `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv`.

Primitive data:
* the model family `ψ`;
* the objective `f`, its global minimizer `xStar`, and a chosen whole-space step `step`;
* the sublevel-set inclusion placing `xStar` in `𝓕`.

Derived API:
* the owner-level comparison
  `modifiedGaussNewtonOptimalValueAt ψ x M ≤ quadraticallyRegularizedObjective (ψ x) M x xStar`
  from `optimalValue_le_of_mem_feasibleSet`;
* the source-facing bridge `modifiedGaussNewtonOptimalValueAt ψ x M = f[step](x)` once a
  whole-space minimizing step is chosen.

This refinement keeps the textbook inequality on the source-facing whole-space step value
`f[step](x)`. The intrinsic owner `modifiedGaussNewtonOptimalValueAt ψ x M` remains in the file
only as the supporting bridge theorem that lets the proof reuse the Chapter 1 optimal-value API
without introducing a parallel local minimization wrapper.
-/

-- Proof sketch: since `xStar` minimizes `f` on `Set.univ`, it belongs to the canonical sublevel
-- set `𝓛[f]((f x))`. The hypothesis `hlevel` therefore gives `xStar ∈ 𝓕`. Apply the quadratic
-- upper-model bound `ψ(x; y) ≤ f(y) + (L / 2) ‖y - x‖²` at `y = xStar`, then compare the
-- intrinsic owner value `modifiedGaussNewtonOptimalValueAt ψ x M` with the quadratic objective at
-- `xStar` using the Chapter 1 optimal-value owner bound.
/-- Internal bridge: the intrinsic owner `modifiedGaussNewtonOptimalValueAt ψ x M` obeys the same
quadratic upper bound at a global minimizer that later yields the textbook `f[step](x)` form of
Corollary 4.4.1. -/
theorem modifiedGaussNewtonOptimalValueAt_le_solutionValue_add_quadratic_error
    (x xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hupper :
      ∀ ⦃y : E⦄, y ∈ 𝓕 →
        ψ x y ≤ f y + (L / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ))
    (hlevel : 𝓛[f]((f x)) ⊆ 𝓕) :
    modifiedGaussNewtonOptimalValueAt ψ x M ≤
      f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
  have hxStar_mem_level : xStar ∈ 𝓛[f]((f x)) := by
    rw [mem_levelSet_iff]
    exact (isMinOn_univ_iff.mp hxStar) x
  have hxStar_mem_𝓕 : xStar ∈ 𝓕 :=
    hlevel hxStar_mem_level
  have hopt :
      modifiedGaussNewtonOptimalValueAt ψ x M ≤
        ψ x xStar + (M / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
    let problem := unconstrained (quadraticallyRegularizedObjective (ψ x) M x)
    have hopt' : problem.optimalValue ≤ (problem xStar : EReal) :=
      problem.optimalValue_le_of_mem_feasibleSet (by simp [problem])
    simpa [problem, modifiedGaussNewtonOptimalValueAt, quadraticallyRegularizedObjective_apply,
      norm_sub_rev]
      using hopt'
  have hupperStar :
      ψ x xStar ≤ f xStar + (L / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [norm_sub_rev] using hupper hxStar_mem_𝓕
  have hsum :
      ψ x xStar + (M / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) ≤
        f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hupperStar]
  exact hopt.trans <| by
    exact_mod_cast hsum

-- Proof sketch: combine the intrinsic owner-level bridge above with the whole-space identity
-- `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv`.
/-- Corollary 4.4.1: if `xStar` globally minimizes `f`, if the sublevel set
`𝓛[f]((f x)) = {y | f y ≤ f x}` is contained in `𝓕`, and if `step` is a whole-space modified
Gauss--Newton minimizer at regularization `M`, then the textbook value `f[step](x)` satisfies
`f[step](x) ≤ f^* + ((L + M) / 2) ‖x - xStar‖²`, where `f^* = f(xStar)`. In the intended
application, `f` is the merit-function reformulation from Definition 4.4.10 and `xStar` is an
exact solution. -/
theorem modifiedGaussNewton_modelValue_le_solutionValue_add_quadratic_error
    (step : ModifiedGaussNewtonStep ψ Set.univ M)
    (x xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hupper :
      ∀ ⦃y : E⦄, y ∈ 𝓕 →
        ψ x y ≤ f y + (L / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ))
    (hlevel : 𝓛[f]((f x)) ⊆ 𝓕) :
    f[step](x) ≤
      f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
  have howner :
      modifiedGaussNewtonOptimalValueAt ψ x M ≤
        f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) :=
    modifiedGaussNewtonOptimalValueAt_le_solutionValue_add_quadratic_error
      x xStar hxStar hupper hlevel
  have hmodel : (f[step](x) : EReal) ≤
      f xStar + ((L + M) / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv step x] using howner
  exact_mod_cast hmodel

/-! ### Definition_4_4_1 (from Chap04) -/
noncomputable section

universe u

variable {R : Type u} [Zero R]
variable {m : ℕ}

/- Definition 4.4.1 lies in the merit-scalarization domain.

Sampled owner-style declarations:
- `norm_eq_zero` in mathlib, the canonical zero-detection theorem for norm-based scalarizers;
- `EuclideanSpace.real_norm_sq_eq` in mathlib, the canonical `ℝ^m` sum-of-squares formula;
- `IsSharpMeritFunction` in `Definition_4_4_9`, the chapter owner extending the same
  merit-function core;
- ordinary function composition for the scalarization `x ↦ φ (F x)`.

Best owner abstractions:
- source-facing: the intrinsic merit-function property of a residual scalarizer `φ : R → ℝ`;
- core/canonical: the reusable owner `IsMeritFunction` on a residual type carrying `0`;
- bridge/view: the Euclidean specialization `u ↦ ‖u‖₂²` on `ℝ^m`, expressed directly by the
  canonical squared norm.

Primitive data:
- a scalarizer `φ : R → ℝ` on a residual type with a distinguished origin.

Derived API:
- the Euclidean model example `u ↦ ‖u‖₂²`;
- downstream residual scalarizations such as `x ↦ φ (F x)`, built by ordinary composition from
  this owner.

This file therefore keeps the public owner intrinsic and lets the finite-coordinate `ℝ^m`
presentation appear only in the Euclidean specialization and downstream composition bridges,
without introducing a second public owner for the squared norm.
-/

/-- Definition 4.4.1: a merit function on a residual type with distinguished origin `0` is a
nonnegative scalarization that vanishes exactly at the origin, so it can be used in merit
reformulations `x ↦ φ (F x)`. -/
class IsMeritFunction (φ : R → ℝ) : Prop where
  /-- A merit function is everywhere nonnegative. -/
  nonneg (u : R) : 0 ≤ φ u
  /-- A merit function vanishes exactly at the origin. -/
  eq_zero_iff (u : R) : φ u = 0 ↔ u = 0

/-- The canonical squared Euclidean norm on `ℝ^m` is a merit function. -/
theorem euclideanNormSq_isMeritFunction (m : ℕ) :
    IsMeritFunction (fun u : EuclideanSpace ℝ (Fin m) ↦ ‖u‖ ^ (2 : ℕ)) := by
  refine
    { nonneg := fun u ↦ by simpa [pow_two] using sq_nonneg ‖u‖
      eq_zero_iff := fun u ↦ by
        exact sq_eq_zero_iff.trans norm_eq_zero }

/-- The canonical squared Euclidean norm provides the textbook merit-function instance on
`ℝ^m`. -/
instance (m : ℕ) : IsMeritFunction (fun u : EuclideanSpace ℝ (Fin m) ↦ ‖u‖ ^ (2 : ℕ)) :=
  euclideanNormSq_isMeritFunction m

end

/-! ### Lemma_4_4_1 (from Chap04) -/
noncomputable section

open scoped Manifold
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Lemma 4.4.1 lies in the merit-scalarization / Gauss--Newton local-model domain.

Sampled owner-style declarations:
* `meritFunctionReformulation` in `Definition_4_4_10`, the source-facing owner for merit
  scalarization by composition;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the source-facing owner for the
  Gauss--Newton local model;
* `jacobian_lipschitz_taylor_remainder_le` in `Proposition_4_4_5`, the owner bridge for the
  residual linearization error under Jacobian Lipschitz control;
* `LipschitzWith.norm_sub_le` in mathlib, the canonical pointwise consequence of a
  `1`-Lipschitz scalarizer.

Best owner abstraction:
* source-facing: the textbook discrepancy bound between the merit reformulation and the
  Gauss--Newton local model;
* core/canonical: the owners `LipschitzWith`, `meritFunctionReformulation`,
  `modifiedGaussNewtonLocalModel`, and `LipschitzOnWith` on the derivative map;
* bridge/view: this lemma, obtained by applying the scalarizer Lipschitz estimate to the
  residual Taylor remainder owner theorem.

Primitive data:
* a bundled smooth residual map `problem`;
* a `1`-Lipschitz scalarizer `φ`;
* a convex feasible set `𝓕`;
* the Jacobian-Lipschitz owner `h_jacobian_lipschitz`.

Derived API:
* the bound on the scalarized discrepancy between `f(y)` and `ψ(x; y)`.

This file therefore keeps only the source-facing discrepancy theorem and reuses the canonical
Taylor remainder owner from `Proposition_4_4_5` instead of carrying a parallel local remainder
API. -/

-- Proof sketch: write the model discrepancy as
-- `|φ (F y) - φ (F x + F'(x) (y - x))|`, use the `1`-Lipschitz property of the scalarizer `φ`
-- to bound it by the norm of the residual linearization error, and then apply the
-- first-order Taylor remainder estimate for `F` on the convex feasible set `𝓕` under the
-- derivative Lipschitz hypothesis.
/-- Lemma 4.4.1: if `𝓕` is convex and `x` and `y` belong to `𝓕`, then the difference between the
merit reformulation `f(y) = φ(F y)` and the modified Gauss--Newton local model
`ψ(x; y) = φ(F(x) + F'(x)(y - x))` is bounded by `((L : ℝ) / 2) * ‖y - x‖²`. -/
theorem abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le
    (problem : C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯)
    (φ : F → ℝ) (hφ : LipschitzWith 1 φ)
    {𝓕 : Set E} {L : NNReal}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    {x y : E} (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    |meritFunctionReformulation problem φ y -
        ψ[problem; φ; (fderiv ℝ problem)](x; y)| ≤
      ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  calc
    |meritFunctionReformulation problem φ y - ψ[problem; φ; (fderiv ℝ problem)](x; y)|
        = ‖φ (problem y) - φ (problem x + fderiv ℝ problem x (y - x))‖ := by
            simp
    _ ≤ ‖problem y - (problem x + fderiv ℝ problem x (y - x))‖ := by
      simpa [dist_eq_norm] using
        hφ.norm_sub_le (problem y)
          (problem x + fderiv ℝ problem x (y - x))
    _ ≤ ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        problem.jacobian_lipschitz_taylor_remainder_le
          h𝓕 h_jacobian_lipschitz x y hx hy

/-! ### Proposition_4_4_1 (from Chap04) -/
noncomputable section

open scoped MinimalSingularValue

universe u v w

variable {𝕜 : Type w} {E₁ : Type u} {E₂ : Type v}
  [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-
Proposition 4.4.1 lies in the normed-space operator / minimal-singular-value domain.

Sampled owner-style declarations:
- `ContinuousLinearMap.minimalSingularValue` with notation `σ_min(A)` in `Definition_4_4_5`, the
  chapter's source-facing owner for the least singular value;
- `minimalSingularValue_def`, the infimum-over-nonzero-vectors bridge for that owner;
- `minimalSingularValue_nonneg`, the canonical positivity API derived from the owner;
- mathlib `ContinuousLinearMap.opNorm` with `ratio_le_opNorm`, the ambient comparison pattern for
  quotient norms of continuous linear maps.

Best owner abstraction:
- source-facing/core: `σ_min(A)` as the chapter owner for the least singular value of a continuous
  linear map;
- bridge/view: `minimalSingularValue_def`, which realizes that owner as the infimum of
  `‖A x‖ / ‖x‖` over nonzero vectors.

Primitive data:
- a continuous linear map `A : E₁ →L[𝕜] E₂`;
- a vector `x : E₁`.

Derived API:
- the pointwise lower bound `σ_min(A) * ‖x‖ ≤ ‖A x‖`.

Source/core/bridge triage:
- source-facing: the textbook lower bound for the image norm in terms of the least singular value;
- core/canonical: the owner `σ_min(A)`;
- bridge/view: evaluate the infimum formula at a fixed nonzero vector.

No extra wrapper is needed here: this proposition is the direct derived inequality attached to the
existing chapter owner. -/

-- Proof sketch: for `x ≠ 0`, the defining infimum of `σ_min(A)` contains the ratio
-- `‖A x‖ / ‖x‖`, so `σ_min(A) ≤ ‖A x‖ / ‖x‖`. Multiplying by `‖x‖` gives the claim.
namespace ContinuousLinearMap

/-- Proposition 4.4.1: the minimal singular value of a continuous linear map gives the lower bound
`σ_min(A) * ‖x‖ ≤ ‖A x‖` for every vector `x`, equivalently `‖A x‖ ≥ σ_min(A) * ‖x‖`. -/
theorem minimalSingularValue_mul_norm_le
    (A : E₁ →L[𝕜] E₂) (x : E₁) :
    σ_min(A) * ‖x‖ ≤ ‖A x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hσx : σ_min(A) ≤ ‖A x‖ / ‖x‖ := by
      rw [minimalSingularValue_def]
      refine csInf_le ?_ ?_
      · refine ⟨0, ?_⟩
        rintro y ⟨v, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact ⟨⟨x, hx⟩, rfl⟩
    exact (le_div_iff₀ hxnorm).1 hσx

end ContinuousLinearMap

/-! ### Theorem_4_4_1 (from Chap04) -/
noncomputable section

open scoped BigOperators LocalModelNotation Manifold
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonLocalDecreaseNotation
open scoped ModifiedGaussNewtonQuadraticChiNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Theorem 4.4.1 lies in the modified Gauss--Newton trajectory / infinite-series domain.

Sampled owner declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate and
  regularization sequences;
* `ModifiedGaussNewtonStep.residualAtUniv` in `Definition_4_4_12`, the canonical whole-space
  residual view attached to a chosen modified Gauss--Newton step;
* `localModelDecreaseAt` in `Definition_4_4_13`, the canonical local-decrease owner specialized
  here through the finite-domain bridge from `Lemma_4_4_3`;
* `χ` in `Lemma_4_4_3`, the source-facing quadratic cutoff entering the textbook lower bounds;
* `cubicRegularization_residual_cube_summable_and_tsum_le` in `Theorem_4_1_1`, the nearby chapter
  pattern for expressing nonnegative infinite-tail bounds via `Summable` together with a `tsum`
  inequality.

Source/core/bridge triage:
* source-facing: Theorem 4.4.1 for the residual-square and chi-weighted tail estimates along a
  modified Gauss--Newton trajectory;
* core/canonical: `ModifiedGaussNewtonMethod` together with the step residual owner
  `ModifiedGaussNewtonStep.residualAtUniv` and the local-decrease owner
  `localModelDecreaseAt`;
* bridge/view: comparison of the varying regularization sequence `M_k` with the fixed parameter
  `2L`, yielding fixed-parameter tail bounds from the trajectory-owned varying tails.

Primitive data:
* a modified Gauss--Newton method `method`;
* a lower bound `fStar ≤ f z` for the merit reformulation;
* a fixed comparison step at regularization `2L`;
* the radius parameter `r` used in the local-decrease lower bound.

Derived API:
* summability of the nonnegative residual-square and chi-weighted tails;
* gap bounds on the corresponding infinite sums;
* summability and comparison bounds for the fixed-parameter tails derived from the varying ones.

The owner abstraction is therefore still the chapter trajectory object `ModifiedGaussNewtonMethod`.
The refinement here is on the derived series API: the nonnegative tails are stated on a
semantics-preserving `Summable` + `tsum` surface instead of as bare real `tsum` inequalities.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable
    (problem : SmoothMap)
    (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (L0 L : ℝ) (x0 : E₁)

local notation "f" => meritFunctionReformulation problem φ
local notation "ψ" => ψ[problem; φ; (fderiv ℝ problem)]

namespace ModifiedGaussNewtonMethod

-- Proof sketch: sum the one-step decrease inequalities
-- `f(x_i) - f(x_{i+1}) ≥ (M_i / 2) r_{M_i}(x_i)^2`, first derived once from
-- `method.step_value_le_modelValue`, `method.step_modelValue_le_merit`, and Lemma 4.4.2, along
-- the tail starting at
-- `k`, telescope the partial sums, and bound the remaining iterate values below by `fStar` via
-- `hf_lower`. Since the residual-square terms are nonnegative, the bounded partial sums give both
-- summability of the tail and the asserted `tsum` bound.
theorem meritFunction_sub_succ_ge_half_mul_residual_sq
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) :
    f (method k) - f (method (k + 1)) ≥
      (method.regularization k / 2 : ℝ) *
        (r[(method.step k)] (method k)) ^ (2 : ℕ) := sorry

/-- Theorem 4.4.1 (1): the residual-square tail starting at `x_k` is summable, and the merit gap
at iterate `x_k` dominates its weighted sum `(L₀ / 2) ∑_{i=k}^∞ r_{Mᵢ}(xᵢ)^2`. -/
theorem gap_ge_residualSqTail
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    {fStar : ℝ}
    (hf_lower : ∀ z : E₁, fStar ≤ f z)
    (k : ℕ) :
    Summable (fun i ↦ (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ)) ∧
      f (method k) - fStar ≥
        (L0 / 2 : ℝ) *
          ∑' i, (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ) := sorry

-- Proof sketch: use `method.regularization (k + i) ≤ 2L` termwise to compare the varying
-- regularization residuals with the fixed-parameter residuals. If the varying tail is summable,
-- termwise comparison yields summability of the fixed-parameter tail together with the tail
-- inequality.
/-- Theorem 4.4.1 (2): if the varying-parameter residual-square tail is summable, then the
comparison tail computed with the fixed parameter `2L` is also summable and is bounded by it. -/
theorem residualSqTail_ge_residualSqTailAt_two_mul_L
    (step2L : ModifiedGaussNewtonStep ψ Set.univ (2 * L))
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ)
    (hvarying :
      Summable (fun i ↦ (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ))) :
    Summable (fun i ↦ (r[step2L] (method (k + i))) ^ (2 : ℕ)) ∧
      (L0 / 2 : ℝ) *
          ∑' i, (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ) ≥
        (L0 / 2 : ℝ) *
          ∑' i, (r[step2L] (method (k + i))) ^ (2 : ℕ) := sorry

-- Proof sketch: sum the one-step decrease inequalities
-- `f(x_i) - f(x_{i+1}) ≥ r^2 M_i χ(Δ[problem; φ; r](x_i) / (M_i r^2))`, first derived once from
-- `method.step_value_le_modelValue`, `method.step_modelValue_le_merit`, and Lemma 4.4.3, along
-- the tail
-- starting at `k`, telescope the partial sums, and bound the remaining limit below by `fStar`
-- via `hf_lower`. The chi-weighted terms are nonnegative, so the same argument yields
-- summability of the tail together with the `tsum` inequality.
theorem meritFunction_sub_succ_ge_chiWeighted
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) (r : NNReal) :
    f (method k) - f (method (k + 1)) ≥
      method.regularization k * (r : ℝ) ^ (2 : ℕ) *
        χ (Δ[problem; φ; r]((method k)) /
          (method.regularization k * (r : ℝ) ^ (2 : ℕ))) := sorry

/-- Theorem 4.4.1 (3): for every radius `r`, the chi-weighted tail
`∑_{i=k}^∞ Mᵢ χ(Δ_r(xᵢ) / (Mᵢ r²))` is summable, and the merit gap at iterate `x_k` dominates the
weighted sum `r² ∑_{i=k}^∞ Mᵢ χ(Δ_r(xᵢ) / (Mᵢ r²))`. -/
theorem gap_ge_chiWeightedTail
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    {fStar : ℝ}
    (hf_lower : ∀ z : E₁, fStar ≤ f z)
    (k : ℕ) (r : NNReal) :
    Summable
        (fun i ↦
          method.regularization (k + i) *
            χ (Δ[problem; φ; r]((method (k + i))) /
              (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))) ∧
      f (method k) - fStar ≥
        (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            (method.regularization (k + i) *
              χ (Δ[problem; φ; r]((method (k + i))) /
                (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))) := sorry

-- Proof sketch: apply the antitonicity of
-- `M ↦ M χ(Δ[problem; φ; r](x_i) / (M r^2))` together with
-- `method.regularization (k + i) ≤ 2L` termwise,
-- then compare the resulting weighted tails. If the varying weighted tail is summable, the same
-- termwise comparison gives summability of the fixed-parameter weighted chi-tail and the asserted
-- bound.
/-- Theorem 4.4.1 (4): if the weighted chi-tail for the varying regularization parameters is
summable, then the comparison weighted chi-tail at the fixed parameter `2L` is summable and is
bounded by the varying-parameter tail. -/
theorem chiWeightedTail_ge_chiWeightedTailAt_two_mul_L
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) (r : NNReal)
    (hvarying :
      Summable
        (fun i ↦
          method.regularization (k + i) *
            χ (Δ[problem; φ; r]((method (k + i))) /
              (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ))))) :
    Summable
        (fun i ↦
          (2 * L) *
            χ (Δ[problem; φ; r]((method (k + i))) /
              ((2 * L) * (r : ℝ) ^ (2 : ℕ)))) ∧
      (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            (method.regularization (k + i) *
              χ (Δ[problem; φ; r]((method (k + i))) /
                (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))) ≥
        (2 * L) * (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            χ (Δ[problem; φ; r]((method (k + i))) /
              ((2 * L) * (r : ℝ) ^ (2 : ℕ))) := sorry

end ModifiedGaussNewtonMethod

end

/-! ### Assumption_4_4_2 (from Chap04) -/
universe u v

open Set
open scoped LevelSetNotation

/-
Assumption 4.4.2 lies in the order/topological sublevel-set domain.

Sampled owner-style declarations:
* `Definition_1_4_8`, which already owns the level-set notation `𝓛[f](τ)` together with the
  atomic companions `mem_levelSet_iff` and `levelSet_eq_setOf`
* `Definition_4_1_1`, the Chapter 4 recall of that same owner surface
* mathlib `Set.Iic`, the canonical lower interval whose preimage defines `𝓛[f](τ)`
* `HasUniformDualNondegeneracyOnInitialSublevelSet` in `Assumption_4_4_3`, the nearby Chapter 4
  source-facing owner that specializes the same sublevel-set surface to the modified
  Gauss--Newton merit function

Best owner abstraction:
* source-facing: `IsSufficientlyLargeFeasibleSetAt f 𝓕 x₀`
* core/canonical: `x₀ ∈ interior 𝓕 ∧ 𝓛[f]((f x₀)) ⊆ 𝓕`
* bridge/view: `levelSet_eq_setOf f (f x₀)`

Primitive data:
* the feasible set `𝓕`
* the base point `x₀`
* the preorder-valued objective `f : E → α`
* the interior condition `x₀ ∈ interior 𝓕`
* containment of the canonical initial sublevel set `𝓛[f]((f x₀))` in `𝓕`

Derived API:
* the interior-membership projection
* the owner-level sublevel-set inclusion
* the whole-space specialization, where the assumption is automatic

There is no upstream owner for the full conjunction in this assumption, so the source-facing
predicate stays. The duplicate wheel was the raw set-builder encoding of the sublevel set, which
is refined here to the existing chapter owner notation.
-/

/-- Assumption 4.4.2: a feasible set `𝓕` is sufficiently large with respect to `x₀` for the
objective `f` when `x₀ ∈ interior 𝓕` and the canonical sublevel set `𝓛[f]((f x₀))` is contained
in `𝓕`. -/
def IsSufficientlyLargeFeasibleSetAt
    {E : Type u} [TopologicalSpace E] {α : Type v} [Preorder α]
    (f : E → α) (𝓕 : Set E) (x0 : E) : Prop :=
  x0 ∈ interior 𝓕 ∧ 𝓛[f]((f x0)) ⊆ 𝓕

namespace IsSufficientlyLargeFeasibleSetAt

variable {E : Type u} [TopologicalSpace E] {α : Type v} [Preorder α]
variable {f : E → α} {𝓕 : Set E} {x0 : E}

/-- In the whole-space case `𝓕 = Set.univ`, Assumption 4.4.2 is automatic. -/
@[simp] theorem univ (f : E → α) (x0 : E) :
    IsSufficientlyLargeFeasibleSetAt f Set.univ x0 := by
  simp [IsSufficientlyLargeFeasibleSetAt]

/-- A sufficiently large feasible set contains the base point `x₀` in its interior. -/
theorem mem_interior
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0) :
    x0 ∈ interior 𝓕 :=
  hlarge.1

/-- A sufficiently large feasible set contains the whole sublevel set `𝓛(f(x₀))`. -/
theorem levelSet_subset
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0) :
    𝓛[f]((f x0)) ⊆ 𝓕 :=
  hlarge.2

/-- A sufficiently large feasible set contains the base point `x₀`. -/
@[simp] theorem mem
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0) :
    x0 ∈ 𝓕 :=
  hlarge.levelSet_subset (by simp)

end IsSufficientlyLargeFeasibleSetAt

/-! ### Corollary_4_4_2 (from Chap04) -/
open Filter
open scoped LevelSetNotation Manifold ModifiedGaussNewtonLocalDecreaseNotation Topology

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {L0 L : ℝ} {x0 : E₁}

/- Corollary 4.4.2 lies in the modified Gauss--Newton trajectory / cluster-point domain.

Sampled owner declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate sequence;
* `ModifiedGaussNewtonMethod.meritFunction_succ_le` in `Proposition_4_4_7`, the owner theorem
  keeping the trajectory inside its initial merit sublevel set;
* `ModifiedGaussNewtonMethod.gap_ge_residualSqTail` and
  `ModifiedGaussNewtonMethod.gap_ge_chiWeightedTail` in `Theorem_4_4_1`, the source-facing
  summability owners behind parts `(1)` and `(2)`;
* `cubicRegularization_limitPoints_isConnected` and
  `cubicRegularization_clusterPoint_value_eq_limit` in `Theorem_4_1_2`, the chapter owners for
  connectedness of cluster-point sets and for passing scalar sequence limits to cluster points;
* `modifiedGaussNewtonLocalDecrease` with notation `Δ[problem; φ; r](x)` in `Lemma_4_4_3`, the
  source-facing local-model decrease `Δ_r`.

Best owner abstraction:
* source-facing: the asymptotic consequences for a `ModifiedGaussNewtonMethod`;
* core/canonical: `ModifiedGaussNewtonMethod`, `MapClusterPt`, the initial sublevel set
  `𝓛[f]((f x0))`, and the generic Chapter 4 cluster-point bridge theorems;
* bridge/view: the local-model decrease `Δ[r](x)` and the initial sublevel set
  `𝓛[f]((f x0))`, used internally to pass from trajectory estimates to cluster-point
  consequences.

Primitive data:
* the trajectory `method`;
* the radius parameter `r`.
* for the connected-cluster-set layer, the bounded initial sublevel set `𝓛[f]((f x0))` in a
  proper ambient space;
* for the cluster-point identity layer, continuity of `Δ[r]` at the chosen cluster point.

Internal proof bridges:
* monotonicity of the merit values, confining the trajectory to `𝓛[f]((f x0))`;
* the generic Chapter 4 connected-cluster-set owner
  `cubicRegularization_limitPoints_isConnected`, used after supplying boundedness of `𝓛[f]((f x0))`;
* the scalar cluster-point bridge `cubicRegularization_clusterPoint_value_eq_limit`, used after
  supplying continuity of `Δ[r]` at the cluster point.

Derived API:
* vanishing successive differences;
* vanishing local-model decrease values along the trajectory;
* connectedness of the cluster-point set `X*` under boundedness of `𝓛[f]((f x0))` in a proper
  ambient space;
* the cluster-point identity `Δ_r(x̄) = 0` under continuity of `Δ[problem; φ; r]` at `x̄`.

This file keeps Corollary 4.4.2 source-facing on the intrinsic normed-space layer already used by
`ModifiedGaussNewtonMethod`, while exposing exactly the extra owner-side data needed by the
canonical Chapter 4 cluster-point bridges: boundedness of the initial merit sublevel set in a
proper ambient space for part `(3)`, and continuity of `Δ[r]` at the chosen cluster point for
part `(4)`.
-/

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

namespace ModifiedGaussNewtonMethod

-- Proof sketch: apply Theorem 4.4.1 with the canonical lower bound `0 ≤ f x` coming from the
-- sharp merit function, identify `x_{k+1} - x_k` with the residual of the chosen step at `x_k`,
-- and use that summable squared residuals force the residuals themselves to converge to `0`.
/-- Corollary 4.4.2 (1): along a modified Gauss--Newton method, the consecutive differences
`‖x_k - x_{k+1}‖` converge to `0`. -/
theorem stepDifferences_tendsto_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    Tendsto (fun k ↦ ‖method k - method (k + 1)‖) atTop (𝓝 0) := sorry

private theorem stepDistances_tendsto_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    Tendsto (fun k ↦ dist (method (k + 1)) (method k)) atTop (𝓝 0) :=
  method.stepDifferences_tendsto_zero

-- Proof sketch: if `r = 0`, then `Metric.closedBall x 0 = {x}` and the source-facing local model
-- decrease collapses to `Δ_0(x) = 0`. For general `r`, use Theorem 4.4.1 to show that the
-- weighted chi-tail built from `Δ[problem; φ; r](method k)` is summable. Since `χ` is
-- nonnegative and
-- vanishes only at `0`, the summability of this tail forces `Δ_r(method k) → 0`.
/-- Corollary 4.4.2 (2): for every radius `r`, the local model decrease `Δ_r(x_k)` tends to `0`
along the modified Gauss--Newton iterates. -/
theorem localModelDecrease_tendsto_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (r : NNReal) :
    Tendsto (fun k ↦ Δ[problem; φ; r]((method k))) atTop (𝓝 0) := sorry

-- Proof sketch: use Proposition 4.4.7 to keep the entire trajectory inside the initial sublevel
-- set `𝓛0`, then apply the chapter owner theorem
-- `cubicRegularization_limitPoints_isConnected` to that bounded set in the proper ambient space,
-- with `stepDistances_tendsto_zero` supplying the canonical metric vanishing-step hypothesis.
/-- Corollary 4.4.2 (3): the set `X*` of limit points of the modified Gauss--Newton trajectory is
connected provided the initial merit sublevel set `𝓛[f]((f x₀))` is bounded in the proper
ambient space. -/
theorem limitPoints_isConnected
    [ProperSpace E₁]
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (hbounded : Bornology.IsBounded 𝓛0) :
    IsConnected {xBar : E₁ | MapClusterPt xBar atTop method} := sorry

-- Proof sketch: if `r = 0`, then `Δ_0 = 0` pointwise by the closed-ball singleton formula.
-- Otherwise apply part `(2)` to get `Δ_r(method k) → 0`, then invoke the chapter owner theorem
-- `cubicRegularization_clusterPoint_value_eq_limit` for the scalar function
-- `fun x ↦ Δ[problem; φ; r](x)`, using the explicit continuity hypothesis at the cluster point.
/-- Corollary 4.4.2 (4): every cluster point `x̄ ∈ X*` of the modified Gauss--Newton trajectory
satisfies `Δ_r(x̄) = 0` for each radius `r`, provided `Δ[problem; φ; r]` is continuous at `x̄`. -/
theorem clusterPoint_localModelDecrease_eq_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (r : NNReal)
    {xBar : E₁} (hxBar : MapClusterPt xBar atTop method)
    (hΔ_cont : ContinuousAt (fun x ↦ Δ[problem; φ; r](x)) xBar) :
    Δ[problem; φ; r](xBar) = 0 := sorry

end ModifiedGaussNewtonMethod

end

/-! ### Definition_4_4_2 (from Chap04) -/
noncomputable section

open scoped ConstrainedArgmin Gradient ModifiedGaussNewtonLocalModelNotation
open ContinuousLinearMap PiLp

universe u v

/- Definition 4.4.2 lies in the constrained Gauss--Newton local-model domain.

Primary domain:
* feasible-step minimization for the affine Gauss--Newton residual model

Sampled owner-style declarations:
* `modifiedGaussNewtonLocalModel` with notation `ψ[F; φ; J]` in `Definition_4_4_11`, the chapter
  owner for affine residual/Jacobian local models
* `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project
  owner for minimizers on a feasible set
* `LagrangianProblem.constraintVector` in `Chap01/Definition_1_10_2`, the upstream owner for
  packaging a finite scalar family into an `ℝ^m`-valued residual map
* `fderiv` / `HasGradientAt.fderiv_apply`, the canonical Jacobian and scalar-gradient bridge in
  mathlib

Best owner abstraction:
* source-facing: feasible step directions `h` with `x + h ∈ D x`
* core/canonical: the affine residual local model `ψ[F; φ; J]` together with `argmin[Q]`
* bridge/view: the step-space specialization `h ↦ ψ[F; φ; J](x; x + h)` and, under
  differentiability hypotheses on coordinate functions, the textbook formula
  `f_i(x) + ⟪∇ f_i(x), h⟫`

Primitive data:
* a residual map `F : E₁ → E₂`
* a Jacobian family `J : E₁ → E₁ →L[ℝ] E₂`
* a merit function `φ : E₂ → ℝ`
* a neighborhood map `D : E₁ → Set E₁`
* a base point `x : E₁`

Derived API:
* the feasible-direction set `{h | x + h ∈ D x}`
* the source-facing search-direction predicate as constrained minimization of the step-space view
  of `ψ[F; φ; J]`
* the coordinate-gradient bridge when `F = (LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector`
  and `J` is its Jacobian

Source/core/bridge triage:
* source-facing: `IsGaussNewtonSearchDirectionAt`
* core/canonical: `modifiedGaussNewtonLocalModel` and `argmin[Q]`
* bridge/view: step-space evaluation at `x + h`, and the coordinate-gradient specialization

This refinement keeps the source-facing feasible-step predicate, but moves its objective to the
chapter's explicit residual/Jacobian owner layer. The coordinate formula with totalized gradients
survives only as a bridge theorem.
-/

section FeasibleDirections

variable {E : Type u} [Add E]

/-- The feasible directions for the local Gauss--Newton subproblem are the steps `h` such that
the trial point `x + h` stays inside the chosen neighborhood `D x`. -/
def gaussNewtonFeasibleDirections
    (D : E → Set E) (x : E) : Set E :=
  {h | x + h ∈ D x}

/-- Membership in the feasible-direction set is exactly the condition `x + h ∈ D x`. -/
@[simp]
theorem mem_gaussNewtonFeasibleDirections_iff
    {D : E → Set E} {x h : E} :
    h ∈ gaussNewtonFeasibleDirections D x ↔ x + h ∈ D x :=
  Iff.rfl

end FeasibleDirections

section StepModelBridge

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Evaluating the chapter Gauss--Newton local model at the trial point `x + h` gives the
step-space affine residual formula `φ (F x + J x h)`. -/
@[simp] theorem modifiedGaussNewtonLocalModel_step_apply
    (F : E₁ → E₂)
    (φ : E₂ → ℝ)
    (J : E₁ → E₁ →L[ℝ] E₂) (x h : E₁) :
    ψ[F; φ; J](x; (x + h)) = φ (F x + J x h) := by
  simp [modifiedGaussNewtonLocalModel]

end StepModelBridge

section CoordinateGradientBridge

variable {m : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "ResidualSpace" => EuclideanSpace ℝ (Fin m)

/-- If each coordinate residual `f_i` has gradient `∇ f_i(x)` at `x`, then the Jacobian of the
packaged residual map `(LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector` has the expected
coordinate formula. -/
theorem fderiv_constraintVector_apply
    (fs : Fin m → E → ℝ) (x h : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) (i : Fin m) :
    fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h i =
      inner ℝ (∇ (fs i) x) h := by
  have hdiff :
      DifferentiableAt ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x := by
    rw [differentiableAt_piLp]
    intro j
    simpa [LagrangianProblem.constraintVector_apply] using (hfs_grad j).differentiableAt
  have hproj :
      HasFDerivAt
        (fun y ↦ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector y).ofLp i)
        ((PiLp.proj 2 (fun _ : Fin m ↦ ℝ) i).comp
          (fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x)) x := by
    exact
      (PiLp.hasFDerivAt_apply
        2
        ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x)
        i).comp x hdiff.hasFDerivAt
  have hcoord :
      fderiv ℝ (fun y ↦ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector y).ofLp i) x h =
        inner ℝ (∇ (fs i) x) h := by
    change fderiv ℝ (fs i) x h = inner ℝ (∇ (fs i) x) h
    exact (hfs_grad i).fderiv_apply
  have hproj_apply := congrArg (fun L : E →L[ℝ] ℝ ↦ L h) hproj.fderiv
  simpa [PiLp.proj_apply] using hproj_apply.symm.trans hcoord

/-- Under the coordinate gradient hypotheses, the affine residual attached to
`(LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector` is exactly the packaged textbook
linearization `(f_i(x) + ⟪∇ f_i(x), h⟫)_i`. -/
@[simp] theorem constraintVector_add_fderiv_eq_linearizedResidual
    (fs : Fin m → E → ℝ) (x h : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    (LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
        fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h =
      (LagrangianProblem.mk
        (fun _ ↦ 0)
        (fun i h' ↦ fs i x + inner ℝ (∇ (fs i) x) h')).constraintVector h := by
  ext i
  simp [fderiv_constraintVector_apply, hfs_grad, LagrangianProblem.constraintVector_apply]

/-- For the packaged residual map `(LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector`, the
step-space local model attached to its canonical Jacobian recovers the textbook
coordinate-gradient formula under the corresponding gradient hypotheses. -/
@[simp] theorem modifiedGaussNewtonLocalModel_step_constraintVector_fderiv_apply
    (φ : ResidualSpace → ℝ)
    (fs : Fin m → E → ℝ) (x h : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    modifiedGaussNewtonLocalModel
        ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector)
        φ
        (fun y ↦ fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) y)
        x
        (x + h) =
      φ
        ((LagrangianProblem.mk
          (fun _ ↦ 0)
          (fun i h' ↦ fs i x + inner ℝ (∇ (fs i) x) h')).constraintVector h) := by
  rw [modifiedGaussNewtonLocalModel_step_apply]
  simp [constraintVector_add_fderiv_eq_linearizedResidual, hfs_grad]

end CoordinateGradientBridge

section Definition_4_4_2

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Definition 4.4.2: a Gauss--Newton search direction at `x` is a feasible step `h` with
`x + h ∈ D x` whose step-space local-model value `ψ[F; φ; J](x; x + h)` is minimal among all
feasible steps for the auxiliary Gauss--Newton subproblem. -/
def IsGaussNewtonSearchDirectionAt
    (φ : E₂ → ℝ)
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (D : E₁ → Set E₁) (x h : E₁) : Prop :=
  h ∈ argmin[gaussNewtonFeasibleDirections D x] (fun h' ↦ ψ[F; φ; J](x; (x + h')))

namespace IsGaussNewtonSearchDirectionAt

/-- Expanding `IsGaussNewtonSearchDirectionAt φ F J D x h` gives feasibility of `h` together with
minimality of the step-space Gauss--Newton local model among all feasible steps. -/
@[simp] theorem iff
    (φ : E₂ → ℝ)
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (D : E₁ → Set E₁) (x h : E₁) :
    IsGaussNewtonSearchDirectionAt φ F J D x h ↔
      x + h ∈ D x ∧
        ∀ h', x + h' ∈ D x →
          ψ[F; φ; J](x; (x + h)) ≤ ψ[F; φ; J](x; (x + h')) := by
  simp [IsGaussNewtonSearchDirectionAt, isMinOn_iff, gaussNewtonFeasibleDirections]

/-- A Gauss--Newton search direction is feasible for the local model constraint set. -/
theorem feasible
    {φ : E₂ → ℝ}
    {F : E₁ → E₂}
    {J : E₁ → E₁ →L[ℝ] E₂}
    {D : E₁ → Set E₁} {x h : E₁}
    (hh : IsGaussNewtonSearchDirectionAt φ F J D x h) :
    x + h ∈ D x :=
  (iff φ F J D x h).1 hh |>.1

/-- A Gauss--Newton search direction minimizes the step-space Gauss--Newton local model over all
feasible directions. -/
theorem isMinOn
    {φ : E₂ → ℝ}
    {F : E₁ → E₂}
    {J : E₁ → E₁ →L[ℝ] E₂}
    {D : E₁ → Set E₁} {x h : E₁}
    (hh : IsGaussNewtonSearchDirectionAt φ F J D x h) :
    IsMinOn
      (fun h' ↦ ψ[F; φ; J](x; (x + h')))
      (gaussNewtonFeasibleDirections D x) h := by
  exact (mem_constrainedArgmin_iff.mp (by simpa [IsGaussNewtonSearchDirectionAt] using hh)).2

end IsGaussNewtonSearchDirectionAt

end Definition_4_4_2

section CoordinateGradientView

variable {m : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "ResidualSpace" => EuclideanSpace ℝ (Fin m)

namespace IsGaussNewtonSearchDirectionAt

/-- When `F = (LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector` and `J` is its Jacobian,
Definition 4.4.2 reduces to the textbook coordinate-gradient formula. This is a bridge theorem,
not the owner declaration. -/
@[simp] theorem iff_constraintVector_fderiv
    (φ : ResidualSpace → ℝ)
    (fs : Fin m → E → ℝ)
    (D : E → Set E) (x h : E)
    (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    IsGaussNewtonSearchDirectionAt
        φ
        ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector)
        (fun y ↦ fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) y)
        D
        x
        h ↔
      x + h ∈ D x ∧
        ∀ h', x + h' ∈ D x →
          φ
              ((LagrangianProblem.mk
                (fun _ ↦ 0)
                (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h) ≤
            φ
              ((LagrangianProblem.mk
                (fun _ ↦ 0)
                (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h') := by
  constructor
  · intro hh
    rcases
        (iff
          φ
          ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector)
          (fun y ↦ fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) y)
          D
          x
          h).1 hh with
      ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    intro h' hh'
    have hAffine :
        φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h) ≤
          φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h') := by
      simpa [modifiedGaussNewtonLocalModel_step_apply] using hmin h' hh'
    calc
      φ
          ((LagrangianProblem.mk
            (fun _ ↦ 0)
            (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h) =
        φ
          ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
            fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h) := by
          symm
          exact congrArg φ (constraintVector_add_fderiv_eq_linearizedResidual fs x h hfs_grad)
      _ ≤ φ
          ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
            fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h') :=
          hAffine
      _ = φ
          ((LagrangianProblem.mk
            (fun _ ↦ 0)
            (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h') := by
          exact congrArg φ (constraintVector_add_fderiv_eq_linearizedResidual fs x h' hfs_grad)
  · rintro ⟨hx, hmin⟩
    refine
      (iff
        φ
        ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector)
        (fun y ↦ fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) y)
        D
        x
        h).2 ?_
    refine ⟨hx, ?_⟩
    intro h' hh'
    have hAffine :
        φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h) ≤
          φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h') := by
      calc
        φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h) =
          φ
            ((LagrangianProblem.mk
              (fun _ ↦ 0)
              (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h) := by
            exact congrArg φ (constraintVector_add_fderiv_eq_linearizedResidual fs x h hfs_grad)
        _ ≤ φ
            ((LagrangianProblem.mk
              (fun _ ↦ 0)
              (fun i h'' ↦ fs i x + inner ℝ (∇ (fs i) x) h'')).constraintVector h') :=
            hmin h' hh'
        _ = φ
            ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector x +
              fderiv ℝ ((LagrangianProblem.mk (fun _ ↦ 0) fs).constraintVector) x h') := by
            symm
            exact congrArg φ
              (constraintVector_add_fderiv_eq_linearizedResidual fs x h' hfs_grad)
    simpa [modifiedGaussNewtonLocalModel_step_apply] using hAffine

end IsGaussNewtonSearchDirectionAt

end CoordinateGradientView

end

/-! ### Lemma_4_4_2 (from Chap04) -/
noncomputable section

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]

open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

/- Lemma 4.4.2 lies in the modified Gauss--Newton quadratic-regularization domain.

Sampled owner-style declarations:
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the canonical owner of the
  centered quadratic penalty model;
* `ModifiedGaussNewtonStep.isMinOn_point` in `Definition_4_4_12`, the minimizing-step owner for
  the regularized local model;
* the whole-space notation/API `δ[step; f](x)` and `r[step](x)` from
  `Definition_4_4_12`, the whole-space source-facing bridge views;
* mathlib `ConvexOn`, the intrinsic convexity owner for the local model slice `ψ x`.

Source/core/bridge triage:
* source-facing: the modified Gauss--Newton model-gap estimate at a base point `x`;
* core/canonical: a convex local model slice `ψ x` together with the minimizer owner
  `step.isMinOn_point x` for the quadratic-regularized objective;
* bridge/view: the whole-space quantities `δ[step; f](x)` and `r[step](x)`.

Primitive data:
* the local model slice `ψ x`;
* its convexity in the trial-point variable;
* the regularization parameter `M`;
* the chosen minimizing step.

Derived API:
* segment comparisons between the minimizer `step.point x` and points on the ray from `x`;
* the source-facing lower bound for the modified Gauss--Newton model gap.

This lower bound does not need a separate strong-convexity wrapper for the quadratic penalty.
Convexity of `ψ x` and the owner minimizer property for the regularized objective already imply the
required estimate on a real normed space. -/

open ModifiedGaussNewtonStep

-- Proof sketch: use convexity of `ψ x` to make the quadratic-regularized local model
-- `quadraticallyRegularizedObjective (ψ x) M x` smaller at its minimizer `step x` than at every
-- segment point `x + t (step x - x)` with `0 ≤ t < 1`. Convexity of `ψ x` bounds the local model
-- at those segment points by a convex combination of `ψ x x` and `ψ x (step x)`, which yields
-- `δ_M(x) ≥ t (M / 2) r_M(x)^2` for every `t < 1`; then let `t` approach `1`.
/-- Lemma 4.4.2: if the local model slice `ψ(x; ·)` is convex on the whole space, then for a
modified Gauss--Newton step on the whole space the model improvement `δ_M(x)` attached to the
diagonal objective `f(x) = ψ(x; x)` satisfies `δ_M(x) ≥ (M / 2) r_M(x)^2`. -/
theorem modifiedGaussNewton_modelGap_ge_half_mul_residual_sq
    {ψ : E₁ → E₁ → ℝ} {M : ℝ}
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁)
    (hconv : ConvexOn ℝ Set.univ (ψ x)) :
    δ[step; fun z ↦ ψ z z](x) ≥
      (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) := by
  let f : E₁ → ℝ := fun z ↦ ψ z z
  let obj : E₁ → ℝ := quadraticallyRegularizedObjective (ψ x) M x
  let y := step.point x
  let c : ℝ := (M / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)
  have hmin : IsMinOn obj Set.univ y := by
    simpa [obj, y] using step.isMinOn_point x
  have hdelta : δ[step; f](x) = ψ x x - ψ x y - c := by
    simp [f, c, y]
    ring
  have hδ0 : 0 ≤ δ[step; f](x) := by
    have hx := (isMinOn_univ_iff.mp hmin) x
    simpa [f, obj, c, y, quadraticallyRegularizedObjective_apply] using hx
  by_cases hc : c ≤ 0
  · have hgoal : (M / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) ≤ 0 := by
      simpa [ModifiedGaussNewtonStep.residualAtUniv_def, y, c] using hc
    linarith
  · have hc_pos : 0 < c := lt_of_not_ge hc
    have hc_le : c ≤ δ[step; f](x) := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      by_cases hε_large : c ≤ ε
      · linarith
      · have hε_lt_c : ε < c := lt_of_not_ge hε_large
        let t : ℝ := 1 - ε / c
        have ht_nonneg : 0 ≤ t := by
          have ht_lt_one' : ε / c < 1 := (div_lt_one hc_pos).2 hε_lt_c
          dsimp [t]
          linarith
        have ht_lt_one : t < 1 := by
          dsimp [t]
          have : 0 < ε / c := by positivity
          linarith
        have hmin_t := (isMinOn_univ_iff.mp hmin) (x + t • (y - x))
        have hconv_t :
            ψ x (x + t • (y - x)) ≤ (1 - t) * ψ x x + t * ψ x y := by
          have hsegment : x + t • (y - x) = AffineMap.lineMap x y t := by
            rw [AffineMap.lineMap_apply_module']
            ac_rfl
          simpa [hsegment, AffineMap.lineMap_apply_module, smul_eq_mul] using
            hconv.2 (by simp) (by simp) (sub_nonneg.mpr ht_lt_one.le) ht_nonneg (by ring)
        have hsub_t : x + t • (y - x) - x = t • (y - x) := by
          abel_nf
        have hnorm_t :
            ‖x + t • (y - x) - x‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * ‖y - x‖ ^ (2 : ℕ) := by
          rw [hsub_t, norm_smul, Real.norm_of_nonneg ht_nonneg, mul_pow]
        have hpenalty_t :
            (M / 2 : ℝ) * ‖x + t • (y - x) - x‖ ^ (2 : ℕ) = c * t ^ (2 : ℕ) := by
          rw [hnorm_t]
          simp [c]
          ring
        have hbound :
            ψ x y + c ≤ (1 - t) * ψ x x + t * ψ x y + c * t ^ (2 : ℕ) := by
          calc
            ψ x y + c = obj y := by
              show ψ x y + c = quadraticallyRegularizedObjective (ψ x) M x y
              simp [c, quadraticallyRegularizedObjective_apply]
            _ ≤ obj (x + t • (y - x)) := hmin_t
            _ = ψ x (x + t • (y - x)) + c * t ^ (2 : ℕ) := by
                  change quadraticallyRegularizedObjective (ψ x) M x (x + t • (y - x)) =
                    ψ x (x + t • (y - x)) + c * t ^ (2 : ℕ)
                  rw [quadraticallyRegularizedObjective_apply, hpenalty_t]
            _ ≤ (1 - t) * ψ x x + t * ψ x y + c * t ^ (2 : ℕ) := by linarith
        have hct : c - ε = c * t := by
          dsimp [t]
          field_simp [hc_pos.ne']
        have hct_le : c * t ≤ δ[step; f](x) := by
          nlinarith [hbound, hdelta]
        linarith
    simpa [ModifiedGaussNewtonStep.residualAtUniv_def, y, c] using hc_le

/-! ### Proposition_4_4_2 (from Chap04) -/
noncomputable section

open scoped MinimalSingularValue

universe u v w

variable {𝕜 : Type w} {E₁ : Type u} {E₂ : Type v}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-
Proposition 4.4.2 stays in the normed-space operator / minimal-singular-value domain.

Sampled owner-style declarations:
- `ContinuousLinearMap.minimalSingularValue` with notation `σ_min(A)` in `Definition_4_4_5`, the
  chapter owner for the least singular value;
- `ContinuousLinearMap.minimalSingularValue_mul_norm_le` in `Proposition_4_4_1`, the owner-derived
  lower-bound theorem attached to `σ_min(A)`;
- mathlib `ContinuousLinearMap.bound_of_antilipschitz`, the canonical inverse-map estimate for a
  continuous linear equivalence;
- mathlib `ContinuousLinearMap.opNorm_le_bound`, the owner for upgrading pointwise estimates to an
  operator-norm bound.

Best owner abstraction:
- source-facing/core: the chapter owner `σ_min(A)`;
- bridge/view: inverse/operator-norm estimates for the continuous linear equivalence `A`.

Primitive data:
- an invertible continuous linear operator `A : E₁ ≃L[𝕜] E₂`.

Derived API:
- the reciprocal formula `σ_min(A) = 1 / ‖A⁻¹‖`.

Source/core/bridge triage:
- source-facing: the textbook reciprocal formula for the least singular value of an invertible
  operator;
- core/canonical: the owner `σ_min(A)`;
- bridge/view: Proposition 4.4.1 and the inverse-map operator-norm estimates from mathlib.

No new owner is needed here: this proposition is the inverse-norm companion of the existing owner
`σ_min(A)`. -/

-- Proof sketch: the lower bound `1 / ‖A.symm‖ ≤ σ_min(A)` comes from the canonical
-- `A.antilipschitz` estimate `‖x‖ ≤ ‖A.symm‖ * ‖A x‖`, so every nonzero vector contributes a
-- ratio `‖A x‖ / ‖x‖` bounded below by `1 / ‖A.symm‖`. For the reverse inequality,
-- Proposition 4.4.1 applied to `A` and `A.symm y` gives
-- `‖A.symm y‖ ≤ (1 / σ_min(A)) * ‖y‖`; taking the operator norm of `A.symm` yields
-- `‖A.symm‖ ≤ 1 / σ_min(A)`, hence `σ_min(A) ≤ 1 / ‖A.symm‖`.
namespace ContinuousLinearEquiv

/-- Proposition 4.4.2: for an invertible continuous linear operator, the minimal singular value
equals the reciprocal operator norm of the inverse. -/
theorem minimalSingularValue_eq_inv_norm_symm
    (A : E₁ ≃L[𝕜] E₂) :
    σ_min(A) = 1 / ‖A.symm‖ := by
  by_cases hE : Subsingleton E₁
  · letI := hE
    letI : Subsingleton E₂ := Function.Surjective.subsingleton A.surjective
    rw [show σ_min(A) = 0 by simpa using minimalSingularValue_eq_zero (A : E₁ →L[𝕜] E₂)]
    have hsymm_zero : (A.symm : E₂ →L[𝕜] E₁) = 0 := by
      ext y
      exact Subsingleton.elim _ _
    have hnorm : ‖A.symm‖ = 0 := by
      change ‖(A.symm : E₂ →L[𝕜] E₁)‖ = 0
      simp [hsymm_zero]
    simp [hnorm]
  · letI : Nontrivial E₁ := not_subsingleton_iff_nontrivial.mp hE
    let B : E₂ →L[𝕜] E₁ := A.symm
    have hB_ne : B ≠ 0 := by
      intro hB
      obtain ⟨x, hx⟩ := exists_ne (0 : E₁)
      apply hx
      calc
        x = B (A x) := by simp [B]
        _ = 0 := by simp [B, hB]
    have hB_pos : 0 < ‖B‖ := norm_pos_iff.mpr hB_ne
    have hlower_map : 1 / ‖B‖ ≤ σ_min(A) := by
      change 1 / ‖B‖ ≤ σ_min((A : E₁ →L[𝕜] E₂))
      rw [minimalSingularValue_def]
      refine le_csInf ?_ ?_
      · obtain ⟨x, hx⟩ := exists_ne (0 : E₁)
        exact ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩
      · intro b hb
        rcases hb with ⟨x, rfl⟩
        have hxbound : ‖x.1‖ ≤ ‖B‖ * ‖A x.1‖ := by
          simpa [B] using
            (A : E₁ →L[𝕜] E₂).bound_of_antilipschitz A.antilipschitz x.1
        have hxnorm : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
        have hdiv : ‖x.1‖ / ‖B‖ ≤ ‖A x.1‖ := by
          exact (div_le_iff₀ hB_pos).2 (by simpa [mul_comm] using hxbound)
        have hmul : (1 / ‖B‖) * ‖x.1‖ ≤ ‖A x.1‖ := by
          simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv
        exact (le_div_iff₀ hxnorm).2 hmul
    have hlower : 1 / ‖B‖ ≤ σ_min(A) := by
      simpa using hlower_map
    have hσ_pos : 0 < σ_min(A) :=
      lt_of_lt_of_le (one_div_pos.mpr hB_pos) hlower
    have hnorm_bound : ‖B‖ ≤ 1 / σ_min(A) := by
      refine B.opNorm_le_bound (by positivity) fun y ↦ ?_
      have hy : σ_min(A) * ‖B y‖ ≤ ‖y‖ := by
        simpa [B] using
          (A : E₁ →L[𝕜] E₂).minimalSingularValue_mul_norm_le (A.symm y)
      have hdiv : ‖B y‖ ≤ ‖y‖ / σ_min(A) := by
        exact (le_div_iff₀ hσ_pos).2 (by simpa [mul_comm] using hy)
      simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
    simpa [B] using le_antisymm ((le_one_div hB_pos hσ_pos).1 hnorm_bound) hlower

end ContinuousLinearEquiv
