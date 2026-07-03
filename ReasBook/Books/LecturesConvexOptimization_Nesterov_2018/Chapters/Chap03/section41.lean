import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_41 (from Chap03) -/
noncomputable section

open scoped BigOperators
open scoped DeltaN

local notation "E" N => EuclideanSpace ℝ (Fin (N + 1))

/-
Definition 3.41 is a recall-only item in the chapter's finite-horizon subgradient-stepsize
domain.

Sampled owner-style declarations:
- `EuclideanSpace.positiveOrthant` in `LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_10_2`, the strict
  orthant owner reused by the same stepsize functional
- `deltaN` in `LecturesConvexOptimization_Nesterov_2018.Chap03.Proposition_3_35`, the chapter owner for the scalar
  `Δ_N(h₀, ..., h_N)`
- `deltaN_apply` in `LecturesConvexOptimization_Nesterov_2018.Chap03.Proposition_3_35`, the pointwise evaluation bridge for
  that owner
- `deltaN_constantChoice_minimizes_positiveOrthant` in
  `LecturesConvexOptimization_Nesterov_2018.Chap03.Proposition_3_35`, the later constant-stepsize optimality theorem for
  the same owner

Best owner abstraction:
- `source-facing`: the textbook scalar `Δ_N` attached to a finite stepsize vector
- `core/canonical`: `deltaN N R h`, with source-facing surface `Δ[N; R] h`
- `bridge/view`: `deltaN_apply`

Primitive data:
- the horizon `N : ℕ`
- the radius `R : ℝ`
- the finite stepsize vector `h : E N`

Derived API:
- the source-facing notation `Δ[N; R] h`
- the defining quotient formula from `deltaN_apply`
- the constant-stepsize minimization theorem from Proposition 3.35

Definition 3.41 adds no new mathematical data beyond this existing owner, so this file keeps only
the direct canonical recall surface and introduces no parallel public alias for `Δ_N`, while
reusing the owner notation from `Proposition_3_35`.
-/

/- Definition 3.41 reuses the chapter owner for the finite stepsize scalar directly. -/
recall deltaN (N : ℕ) (R : ℝ) (h : E N) : ℝ

/- Evaluating the recalled owner `deltaN` gives the textbook quotient
`(R² + ∑_{i=0}^N h_i²) / (2 ∑_{i=0}^N h_i)`. -/
recall deltaN_apply (N : ℕ) (R : ℝ) (h : E N) :
    Δ[N; R] h =
      (R ^ (2 : ℕ) + ∑ i : Fin (N + 1), h i ^ (2 : ℕ)) /
        (2 * ∑ i : Fin (N + 1), h i)

end

/-! ### Proposition_3_41 (from Chap03) -/
universe u

/- Proposition 3.41 lies in the quantitative strong-convexity / Lipschitz radius-bound domain on
real normed spaces.

Mandatory domain-style sampling before refinement:
* `StrongConvexOn.quadratic_growth_of_isMinOn` in `Chap02/Theorem_2_30`, the owner lower-gap
  theorem at a global minimizer;
* mathlib `LipschitzWith.le_add_mul`, the owner one-sided Lipschitz estimate;
* mathlib `LipschitzWith.norm_sub_le`, the owner distance estimate behind the Lipschitz gap bound;
* `sub_sInf_image_closedBall_le_lipschitz_mul_dist_of_isMinOn` in `Theorem_3_54`, a nearby
  chapter bridge with the same upper-gap pattern stated directly relative to
  `sInf (f '' Metric.closedBall xStar R)`.

Best owner abstraction:
* core/canonical: `StrongConvexOn Q μ f`, `LipschitzOnWith M f Q`, and `IsMinOn f Q xStar`;
* bridge/view: the scalar cancellation lemma below and its constrained-owner derivation.

Primitive data:
* the objective `f`, the points `x₀`, `xStar`, and the scalars `μ`, `M`;
* the coefficient signs `0 < μ` and `0 ≤ M`;
* the lower-gap bound `(μ / 2) * ‖x₀ - xStar‖² ≤ f x₀ - f xStar`;
* the upper-gap bound `f x₀ - f xStar ≤ M * ‖x₀ - xStar‖`.

Derived API:
* the owner lower-gap theorem and owner Lipschitz estimate, used only in the companion theorems.

Source/core/bridge triage:
* source-facing: the displayed scalar implication in Proposition 3.41;
* core/canonical: the strong-convexity, Lipschitz, and minimizer owners above;
* bridge/view: the owner-based derivation theorem below.

The previous refinement promoted the numbered proposition to an owner-level theorem on
`StrongConvexOn`, `LipschitzWith`, and `IsMinOn`. This file restores Proposition 3.41 to its
source-facing bridge role: the main public entry keeps only the two gap inequalities used by the
scalar cancellation argument, while the owner-based derivation is factored through the more
canonical constrained owners and the whole-space theorem is a thin specialization.
-/

variable {E : Type u} [NormedAddCommGroup E]

/-- Proposition 3.41: if `μ > 0`, `M ≥ 0`, the quadratic lower-gap bound at `x₀`, and the linear
upper-gap bound at `x₀` all hold relative to `xStar`, then `‖x₀ - xStar‖ ≤ 2 M / μ`. -/
-- Proof sketch: let `d = ‖x₀ - xStar‖`. The two hypotheses give
-- `(μ / 2) * d² ≤ M * d`. If `d = 0` there is nothing to prove. Otherwise cancel the positive
-- factor `d` and rearrange.
theorem norm_sub_le_two_mul_div_of_quadratic_growth_le_lipschitz
    {f : E → ℝ} {μ M : ℝ} {x₀ xStar : E}
    (hμ : 0 < μ)
    (hM : 0 ≤ M)
    (hquad : (μ / 2) * ‖x₀ - xStar‖ ^ (2 : ℕ) ≤ f x₀ - f xStar)
    (hLip : f x₀ - f xStar ≤ M * ‖x₀ - xStar‖) :
    ‖x₀ - xStar‖ ≤ 2 * M / μ := by
  let d : ℝ := ‖x₀ - xStar‖
  change d ≤ 2 * M / μ
  have hbound : (μ / 2) * d ^ (2 : ℕ) ≤ M * d := by
    simpa [d] using hquad.trans hLip
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    exact norm_nonneg _
  by_cases hd : d = 0
  · rw [hd]
    rw [le_div_iff₀ hμ]
    nlinarith
  · have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg (by simpa [eq_comm] using hd)
    have hhalf : (μ / 2) * d ≤ M := by
      have hmul : ((μ / 2) * d) * d ≤ M * d := by
        simpa [pow_two, mul_assoc] using hbound
      exact le_of_mul_le_mul_right hmul hd_pos
    rw [le_div_iff₀ hμ]
    nlinarith

namespace StrongConvexOn

variable [NormedSpace ℝ E]

/-- Constrained-owner derivation of Proposition 3.41 from strong convexity, Lipschitz continuity,
and a minimizer on a common feasible set. -/
-- Proof sketch: obtain the lower-gap bound from
-- `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem`, obtain the upper-gap bound from
-- `LipschitzOnWith.le_add_mul`, and apply
-- `norm_sub_le_two_mul_div_of_quadratic_growth_le_lipschitz`.
theorem norm_sub_le_two_mul_lipschitzOnWith_div_of_isMinOn_of_mem
    {Q : Set E} {f : E → ℝ} {μ : ℝ} {M : NNReal} {x₀ xStar : E}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hLip : LipschitzOnWith M f Q)
    (hxStar_mem : xStar ∈ Q) (hxStar : IsMinOn f Q xStar)
    (hx₀ : x₀ ∈ Q) :
    ‖x₀ - xStar‖ ≤ 2 * (M : ℝ) / μ := by
  have hquad : (μ / 2) * ‖x₀ - xStar‖ ^ (2 : ℕ) ≤ f x₀ - f xStar := by
    have hquad0 : f x₀ ≥ f xStar + (μ / 2) * ‖x₀ - xStar‖ ^ (2 : ℕ) := by
      simpa using hf.quadratic_growth_of_isMinOn_of_mem hxStar_mem hxStar x₀ hx₀
    nlinarith
  have hLip' : f x₀ - f xStar ≤ (M : ℝ) * ‖x₀ - xStar‖ := by
    have hLip0 : f x₀ ≤ f xStar + (M : ℝ) * ‖x₀ - xStar‖ := by
      simpa [dist_eq_norm_sub] using hLip.le_add_mul hx₀ hxStar_mem
    nlinarith
  exact norm_sub_le_two_mul_div_of_quadratic_growth_le_lipschitz hμ M.2 hquad hLip'

/-- Whole-space specialization of the constrained-owner derivation of Proposition 3.41. -/
theorem norm_sub_le_two_mul_lipschitz_div_of_isMinOn
    {f : E → ℝ} {μ : ℝ} {M : NNReal} {xStar : E}
    (hf : StrongConvexOn Set.univ μ f) (hμ : 0 < μ)
    (hLip : LipschitzWith M f) (hxStar : IsMinOn f Set.univ xStar)
    (x₀ : E) :
    ‖x₀ - xStar‖ ≤ 2 * (M : ℝ) / μ :=
  hf.norm_sub_le_two_mul_lipschitzOnWith_div_of_isMinOn_of_mem
    hμ hLip.lipschitzOnWith (by simp) hxStar (by simp)

end StrongConvexOn

/-! ### Theorem_3_41 (from Chap03) -/
noncomputable section

universe u

open scoped DeltaN

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 3.41 lies in the chapter's projected normalized subgradient / constant-stepsize domain.

Sampled owner-style declarations:
- `SimpleSetSubgradientMethod.
    bestFunctionValueUpTo_sub_le_of_projected_normalized_subgradient_method`
  in `Theorem_3_40`, the method-level owner gap estimate;
- `deltaNConstantChoice` in `Proposition_3_35`, the canonical constant stepsize prefix;
- `deltaN_constantChoice` in `Proposition_3_35`, the owner evaluation theorem at that prefix.

Best owner abstraction:
- `source-facing`: the constant-stepsize specialization of the best sampled-value bound for a run
  `method : SimpleSetSubgradientMethod problem`;
- `core/canonical`: the method-level bound from `Theorem_3_40`;
- `bridge/view`: the identification of the method's finite stepsize prefix with
  `deltaNConstantChoice N R`.

Primitive data:
- the owner first-order convex minimization problem `problem`;
- the owner simple-set subgradient run `method`;
- the minimizer `xStar`, radius `R`, Lipschitz constant `M`, and horizon `N`;
- the source-facing constant-stepsize hypothesis on the prefix `0, ..., N`.

Derived API:
- the sampled best value `bestFunctionValueUpTo (fun i ↦ problem (method i)) N`;
- the canonical constant prefix `deltaNConstantChoice N R`;
- the closed form `Δ[N; R] (deltaNConstantChoice N R) = R / √(N + 1)`.

The previous version erased the subgradient-method owner and kept only a generic scalar inequality.
This refinement restores the source-facing semantics by specializing the actual method theorem
`Theorem_3_40` to the constant stepsize prefix.
-/

namespace SimpleSetSubgradientMethod

variable {problem : FirstOrderConvexMinimizationProblem E}

/-- Theorem 3.41: if the first `N + 1` stepsizes of a simple-set subgradient method are chosen
constantly as `h_i = R / √(N + 1)`, then the best sampled objective gap among the first `N + 1`
iterates is bounded by `M R / √(N + 1)`. -/
-- Proof sketch: apply the method-level owner estimate from `Theorem_3_40`, identify the finite
-- stepsize prefix with `deltaNConstantChoice N R`, and simplify with `deltaN_constantChoice`.
theorem bestFunctionValueUpTo_sub_le_of_constant_stepsizes
    (method : SimpleSetSubgradientMethod problem) (xStar : E) (R M : NNReal)
    (hxStar_min : IsMinOn problem problem.feasibleSet xStar)
    (hf_lipschitz : LipschitzOnWith M problem (Metric.closedBall xStar R))
    (hx0_ball : method.x0 ∈ Metric.closedBall xStar R)
    (N : ℕ)
    (h_stepsize :
      ∀ i : Fin (N + 1), method.stepsize i = (R : ℝ) / Real.sqrt (N + 1 : ℝ)) :
    bestFunctionValueUpTo (fun i ↦ problem (method i)) N - problem xStar ≤
      (M : ℝ) * ((R : ℝ) / Real.sqrt (N + 1 : ℝ)) := by
  have hbound :=
    bestFunctionValueUpTo_sub_le_of_projected_normalized_subgradient_method
      method xStar R M hxStar_min hf_lipschitz hx0_ball N
  have hprefix :
      method.stepsizePrefix N = deltaNConstantChoice N R := by
    ext i
    simpa using h_stepsize i
  calc
    bestFunctionValueUpTo (fun i ↦ problem (method i)) N - problem xStar ≤
        (M : ℝ) * Δ[N; (R : ℝ)] (method.stepsizePrefix N) :=
      hbound
    _ = (M : ℝ) * Δ[N; (R : ℝ)] (deltaNConstantChoice N R) := by rw [hprefix]
    _ = (M : ℝ) * ((R : ℝ) / Real.sqrt (N + 1 : ℝ)) := by
      rw [deltaN_constantChoice]

end SimpleSetSubgradientMethod

end
