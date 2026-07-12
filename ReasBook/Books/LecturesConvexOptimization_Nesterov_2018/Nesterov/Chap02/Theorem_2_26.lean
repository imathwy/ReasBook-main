import LecturesConvexOptimization_Nesterov_2018.Chap01.Lemma_1_6_6
import LecturesConvexOptimization_Nesterov_2018.Chap02.Algorithm_2_2
import LecturesConvexOptimization_Nesterov_2018.Chap02.Algorithm_2_3
import LecturesConvexOptimization_Nesterov_2018.Chap02.Definition_2_19
import LecturesConvexOptimization_Nesterov_2018.Chap02.Definition_2_23
import LecturesConvexOptimization_Nesterov_2018.Chap02.Lemma_2_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MinGradientNormAlongIterates SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "p" => normSeminorm ℝ E
local notation "State" => E × E × ℝ

/- Primary domain: smooth-convex accelerated optimal-method recurrences on real Hilbert spaces,
and the monotone type-I variant of method `(2.2.32)`.

Owner-style declarations sampled before refining this file:
* `OptimalMethodRecurrence` in `Algorithm_2_2`, the owner recurrence data
  `(xₖ, yₖ, vₖ, αₖ, γₖ)`;
* `GeneralOptimalMethodScheme` in `Algorithm_2_2`, the owner extension adding the step-`(c)`
  descent inequality;
* `constantStepSchemeIAlphaNext` in `Algorithm_2_3`, the owner scalar update for the
  `μ = 0` optimal-method recurrence used here at `γ₀ = 3L`;
* `minGradientNormAlongIterates` in `Definition_2_23`, the owner finite-window realization of the
  textbook quantity `g_{0,T}`.

Best owner abstraction:
* source-facing: the recursive monotone type-I trajectory `monotoneConstantStepSchemeIA`,
  together with its source-named points `x̂ₖ`, `ŷₖ`;
* core/canonical: `OptimalMethodRecurrence f (L : ℝ) 0 x0 (3 * (L : ℝ))`,
  `GeneralOptimalMethodScheme f (L : ℝ) 0 x0 (3 * (L : ℝ))`, and
  `minGradientNormAlongIterates`;
* bridge/view: `monotoneConstantStepSchemeIAToOptimalMethodRecurrence` and
  `monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme`.

Primitive data:
* the recursive state `(xₖ, vₖ, γₖ)`.

Derived API:
* the source-named sequences `αₖ`, `yₖ`, `x̂ₖ`, `ŷₖ`;
* the comparison lemmas showing `ŷₖ` is chosen between `xₖ` and `x̂ₖ₊₁`;
* the owner bridges recovering the canonical recurrence and descent inequality.

This file therefore keeps the method itself as a recursive source-facing object, not as a public
wrapper structure with primitive comparison fields. The monotonicity data `x̂ₖ`, `ŷₖ` remain
visible as exact recursive declarations, while the owner optimal-method structures are derived
bridge API. -/

private def monotoneConstantStepSchemeIAAlphaState
    (L : NNReal) (state : State) : ℝ :=
  constantStepSchemeIAlphaNext (L : ℝ) 0 state.2.2

private def monotoneConstantStepSchemeIAGammaNextState
    (L : NNReal) (state : State) : ℝ :=
  (L : ℝ) * monotoneConstantStepSchemeIAAlphaState L state ^ (2 : ℕ)

private def monotoneConstantStepSchemeIAYState
    (L : NNReal) (state : State) : E :=
  let xk := state.1
  let vk := state.2.1
  let gammak := state.2.2
  let alphak := monotoneConstantStepSchemeIAAlphaState L state
  let gammaNext := monotoneConstantStepSchemeIAGammaNextState L state
  (1 / gammak) • ((alphak * gammak) • vk + gammaNext • xk)

private def monotoneConstantStepSchemeIAXHatState
    (f : E → ℝ) (L : NNReal) (state : State) : E :=
  let yk := monotoneConstantStepSchemeIAYState L state
  yk - (1 / (L : ℝ)) • ∇ f yk

private def monotoneConstantStepSchemeIAYHatState
    (f : E → ℝ) (L : NNReal) (state : State) : E :=
  let xk := state.1
  let xHatNext := monotoneConstantStepSchemeIAXHatState f L state
  if f xk ≤ f xHatNext then xk else xHatNext

private def monotoneConstantStepSchemeIAXNextState
    (f : E → ℝ) (L : NNReal) (state : State) : E :=
  let yHatk := monotoneConstantStepSchemeIAYHatState f L state
  yHatk - (1 / (L : ℝ)) • ∇ f yHatk

private def monotoneConstantStepSchemeIAVNextState
    (f : E → ℝ) (L : NNReal) (state : State) : E :=
  let vk := state.2.1
  let gammak := state.2.2
  let alphak := monotoneConstantStepSchemeIAAlphaState L state
  let gammaNext := monotoneConstantStepSchemeIAGammaNextState L state
  let yk := monotoneConstantStepSchemeIAYState L state
  (1 / gammaNext) • (((1 - alphak) * gammak) • vk - alphak • ∇ f yk)

/-- Method `(2.2.32)`: the recursive monotone type-I trajectory with state `(xₖ, vₖ, γₖ)`,
started from `(x₀, x₀, 3L)`. The source-named points `yₖ`, `x̂ₖ₊₁`, and `ŷₖ` are derived from the
current state, and the next iterate is the reciprocal-`L` gradient step from `ŷₖ`. -/
noncomputable def monotoneConstantStepSchemeIA
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E × E × ℝ
  | 0 => (x0, x0, 3 * (L : ℝ))
  | k + 1 =>
      let state := monotoneConstantStepSchemeIA f L x0 k
      let xNext := monotoneConstantStepSchemeIAXNextState f L state
      let vNext := monotoneConstantStepSchemeIAVNextState f L state
      let gammaNext := monotoneConstantStepSchemeIAGammaNextState L state
      (xNext, vNext, gammaNext)

/-- The main iterate sequence `xₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAX
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ (monotoneConstantStepSchemeIA f L x0 k).1

/-- The estimating-sequence centers `vₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAV
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ (monotoneConstantStepSchemeIA f L x0 k).2.1

/-- The curvature sequence `γₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAGamma
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → ℝ :=
  fun k ↦ (monotoneConstantStepSchemeIA f L x0 k).2.2

/-- The coefficient sequence `αₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAAlpha
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → ℝ :=
  fun k ↦ monotoneConstantStepSchemeIAAlphaState L (monotoneConstantStepSchemeIA f L x0 k)

/-- The interpolation sequence `yₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAY
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ monotoneConstantStepSchemeIAYState L (monotoneConstantStepSchemeIA f L x0 k)

/-- The trial gradient-step points `x̂ₖ`. We set `x̂₀ = x₀`, while the source recursion uses the
successor values `x̂ₖ₊₁`. -/
noncomputable def monotoneConstantStepSchemeIAXHat
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E
  | 0 => x0
  | k + 1 => monotoneConstantStepSchemeIAXHatState f L (monotoneConstantStepSchemeIA f L x0 k)

/-- The selected comparison points `ŷₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAYHat
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ monotoneConstantStepSchemeIAYHatState f L (monotoneConstantStepSchemeIA f L x0 k)

@[simp] theorem monotoneConstantStepSchemeIA_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIA f L x0 0 = (x0, x0, 3 * (L : ℝ)) :=
  rfl

@[simp] theorem monotoneConstantStepSchemeIA_succ
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIA f L x0 (k + 1) =
      let state := monotoneConstantStepSchemeIA f L x0 k
      let xNext := monotoneConstantStepSchemeIAXNextState f L state
      let vNext := monotoneConstantStepSchemeIAVNextState f L state
      let gammaNext := monotoneConstantStepSchemeIAGammaNextState L state
      (xNext, vNext, gammaNext) :=
  rfl

@[simp] theorem monotoneConstantStepSchemeIAX_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIAX f L x0 0 = x0 :=
  rfl

@[simp] theorem monotoneConstantStepSchemeIAV_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIAV f L x0 0 = x0 :=
  rfl

@[simp] theorem monotoneConstantStepSchemeIAGamma_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIAGamma f L x0 0 = 3 * (L : ℝ) :=
  rfl

@[simp] private theorem monotoneConstantStepSchemeIAAlpha_eq
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAAlpha f L x0 k =
      constantStepSchemeIAlphaNext
        (L : ℝ) 0 (monotoneConstantStepSchemeIAGamma f L x0 k) :=
  rfl

@[simp] private theorem monotoneConstantStepSchemeIAGamma_succ_eq_L_mul_sq
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAGamma f L x0 (k + 1) =
      (L : ℝ) * monotoneConstantStepSchemeIAAlpha f L x0 k ^ (2 : ℕ) :=
  rfl

/-- The interpolation points satisfy the owner optimal-method formula specialized to `μ = 0`. -/
private theorem monotoneConstantStepSchemeIAY_eq
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAY f L x0 k =
      (1 / monotoneConstantStepSchemeIAGamma f L x0 k) •
        ((monotoneConstantStepSchemeIAAlpha f L x0 k *
              monotoneConstantStepSchemeIAGamma f L x0 k) •
            monotoneConstantStepSchemeIAV f L x0 k +
          monotoneConstantStepSchemeIAGamma f L x0 (k + 1) •
            monotoneConstantStepSchemeIAX f L x0 k) := by
  rfl

@[simp] theorem monotoneConstantStepSchemeIAXHat_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIAXHat f L x0 0 = x0 :=
  rfl

/-- The trial points `x̂ₖ₊₁` are the reciprocal-`L` gradient steps from `yₖ`. -/
@[simp] theorem monotoneConstantStepSchemeIAXHat_succ
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAXHat f L x0 (k + 1) =
      monotoneConstantStepSchemeIAY f L x0 k -
        (1 / (L : ℝ)) • ∇ f (monotoneConstantStepSchemeIAY f L x0 k) := by
  rfl

/-- Each comparison point `ŷₖ` is chosen between the current iterate `xₖ` and the trial point
`x̂ₖ₊₁`. -/
@[simp] theorem monotoneConstantStepSchemeIAYHat_eq_if
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAYHat f L x0 k =
      if f (monotoneConstantStepSchemeIAX f L x0 k) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1))
      then monotoneConstantStepSchemeIAX f L x0 k
      else monotoneConstantStepSchemeIAXHat f L x0 (k + 1) := by
  rfl

/-- The selected comparison point has objective value no larger than `x̂ₖ₊₁`. -/
private theorem monotoneConstantStepSchemeIAYHat_objective_le_xHat
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    f (monotoneConstantStepSchemeIAYHat f L x0 k) ≤
      f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1)) := by
  by_cases h :
      f (monotoneConstantStepSchemeIAX f L x0 k) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1))
  · rw [monotoneConstantStepSchemeIAYHat_eq_if, if_pos h]
    exact h
  · rw [monotoneConstantStepSchemeIAYHat_eq_if, if_neg h]

/-- Helper for Theorem 2.26: the selected comparison point has objective value no larger than the
current iterate `xₖ`. -/
private theorem monotoneConstantStepSchemeIAYHat_objective_le_x
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    f (monotoneConstantStepSchemeIAYHat f L x0 k) ≤
      f (monotoneConstantStepSchemeIAX f L x0 k) := by
  -- The `if` defining `ŷₖ` chooses the lower-objective point between `xₖ` and `x̂ₖ₊₁`.
  by_cases h :
      f (monotoneConstantStepSchemeIAX f L x0 k) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1))
  · rw [monotoneConstantStepSchemeIAYHat_eq_if, if_pos h]
  · rw [monotoneConstantStepSchemeIAYHat_eq_if, if_neg h]
    exact le_of_not_ge h

/-- The actual iterates are the reciprocal-`L` gradient steps from the selected comparison
points `ŷₖ`. -/
@[simp] theorem monotoneConstantStepSchemeIAX_succ
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAX f L x0 (k + 1) =
      monotoneConstantStepSchemeIAYHat f L x0 k -
        (1 / (L : ℝ)) • ∇ f (monotoneConstantStepSchemeIAYHat f L x0 k) := by
  rfl

/-- The center update matches the owner optimal-method recurrence specialized to `μ = 0`. -/
private theorem monotoneConstantStepSchemeIAV_succ
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAV f L x0 (k + 1) =
      (1 / monotoneConstantStepSchemeIAGamma f L x0 (k + 1)) •
        (((1 - monotoneConstantStepSchemeIAAlpha f L x0 k) *
              monotoneConstantStepSchemeIAGamma f L x0 k) •
            monotoneConstantStepSchemeIAV f L x0 k -
          monotoneConstantStepSchemeIAAlpha f L x0 k •
            ∇ f (monotoneConstantStepSchemeIAY f L x0 k)) := by
  rfl

/-- The curvature sequence stays positive once `L > 0`. -/
private theorem monotoneConstantStepSchemeIAGamma_pos
    (f : E → ℝ) (L : NNReal) (x0 : E) (hL : 0 < (L : ℝ)) :
    ∀ k : ℕ, 0 < monotoneConstantStepSchemeIAGamma f L x0 k
  | 0 => by
      simpa using show 0 < 3 * (L : ℝ) from by nlinarith
  | k + 1 => by
      have hk : 0 < monotoneConstantStepSchemeIAGamma f L x0 k :=
        monotoneConstantStepSchemeIAGamma_pos f L x0 hL k
      have hα :
          0 <
            constantStepSchemeIAlphaNext
              (L : ℝ) 0 (monotoneConstantStepSchemeIAGamma f L x0 k) :=
        constantStepSchemeIAlphaNext_pos hL hk
      have hsucc :
          0 <
            (L : ℝ) * monotoneConstantStepSchemeIAAlpha f L x0 k ^ (2 : ℕ) := by
        positivity
      simpa [monotoneConstantStepSchemeIAGamma_succ_eq_L_mul_sq] using hsucc

private theorem monotoneConstantStepSchemeIAAlpha_mem_Ioo
    (f : E → ℝ) (L : NNReal) (x0 : E) (hL : 0 < (L : ℝ)) (k : ℕ) :
    monotoneConstantStepSchemeIAAlpha f L x0 k ∈ Set.Ioo (0 : ℝ) 1 := by
  simpa [monotoneConstantStepSchemeIAAlpha_eq] using
    constantStepSchemeIAlphaNext_mem_Ioo hL hL
      (monotoneConstantStepSchemeIAGamma_pos f L x0 hL k)

private theorem monotoneConstantStepSchemeIAAlpha_equation
    (f : E → ℝ) (L : NNReal) (x0 : E) (hL : 0 < (L : ℝ)) (k : ℕ) :
    (L : ℝ) * monotoneConstantStepSchemeIAAlpha f L x0 k ^ (2 : ℕ) =
      (1 - monotoneConstantStepSchemeIAAlpha f L x0 k) *
          monotoneConstantStepSchemeIAGamma f L x0 k +
        monotoneConstantStepSchemeIAAlpha f L x0 k * 0 := by
  have hEq :
      (L : ℝ) * constantStepSchemeIAlphaNext (L : ℝ) 0
          (monotoneConstantStepSchemeIAGamma f L x0 k) ^ (2 : ℕ) =
        (1 - constantStepSchemeIAlphaNext (L : ℝ) 0
            (monotoneConstantStepSchemeIAGamma f L x0 k)) *
            monotoneConstantStepSchemeIAGamma f L x0 k +
          constantStepSchemeIAlphaNext (L : ℝ) 0
            (monotoneConstantStepSchemeIAGamma f L x0 k) * 0 := by
    exact constantStepSchemeIAlphaNext_satisfies_equation hL
      (monotoneConstantStepSchemeIAGamma_pos f L x0 hL k)
  simpa [monotoneConstantStepSchemeIAAlpha_eq] using hEq

/-- The recursive monotone type-I trajectory, viewed through the owner optimal-method recurrence
API. -/
def monotoneConstantStepSchemeIAToOptimalMethodRecurrence
    (f : E → ℝ) (L : NNReal) (x0 : E) (hL : 0 < (L : ℝ)) :
    OptimalMethodRecurrence f (L : ℝ) 0 x0 (3 * (L : ℝ)) where
  L_pos := hL
  mu_nonneg := by positivity
  gamma0_pos := by
    nlinarith
  x := monotoneConstantStepSchemeIAX f L x0
  y := monotoneConstantStepSchemeIAY f L x0
  v := monotoneConstantStepSchemeIAV f L x0
  alpha := monotoneConstantStepSchemeIAAlpha f L x0
  gamma := monotoneConstantStepSchemeIAGamma f L x0
  x_zero := monotoneConstantStepSchemeIAX_zero f L x0
  v_zero := monotoneConstantStepSchemeIAV_zero f L x0
  gamma_zero := monotoneConstantStepSchemeIAGamma_zero f L x0
  alpha_mem_Ioo := monotoneConstantStepSchemeIAAlpha_mem_Ioo f L x0 hL
  alpha_equation := monotoneConstantStepSchemeIAAlpha_equation f L x0 hL
  gamma_succ := by
    intro k
    calc
      monotoneConstantStepSchemeIAGamma f L x0 (k + 1) =
          (L : ℝ) * monotoneConstantStepSchemeIAAlpha f L x0 k ^ (2 : ℕ) := by
            exact monotoneConstantStepSchemeIAGamma_succ_eq_L_mul_sq f L x0 k
      _ =
          (1 - monotoneConstantStepSchemeIAAlpha f L x0 k) *
              monotoneConstantStepSchemeIAGamma f L x0 k +
            monotoneConstantStepSchemeIAAlpha f L x0 k * 0 := by
              exact monotoneConstantStepSchemeIAAlpha_equation f L x0 hL k
  y_eq := by
    intro k
    simpa using monotoneConstantStepSchemeIAY_eq f L x0 k
  v_succ := by
    intro k
    simpa using monotoneConstantStepSchemeIAV_succ f L x0 k

/-- Under the intrinsic reciprocal-`L` gradient-step hypotheses, the monotone type-I trajectory
inherits the descent inequality of the general optimal-method scheme. -/
def monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
    (f : E → ℝ) (L : NNReal) (x0 : E)
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    GeneralOptimalMethodScheme f (L : ℝ) 0 x0 (3 * (L : ℝ)) where
  toOptimalMethodRecurrence :=
    monotoneConstantStepSchemeIAToOptimalMethodRecurrence f L x0 hL
  x_succ_le := by
    intro k
    have hx_le_yHat :
        f (monotoneConstantStepSchemeIAX f L x0 (k + 1)) ≤
          f (monotoneConstantStepSchemeIAYHat f L x0 k) := by
      have hx_desc :
          f (monotoneConstantStepSchemeIAX f L x0 (k + 1)) ≤
            f (monotoneConstantStepSchemeIAYHat f L x0 k) -
              (1 / (2 * (L : ℝ))) *
                ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 k)‖ ^ (2 : ℕ) := by
        simpa [monotoneConstantStepSchemeIAX_succ] using
          gradient_step_value_descent_of_lipschitzGradient
            f hL (fun x ↦ (hgrad x).differentiableAt)
            (by simpa using hgrad_lipschitz)
            (monotoneConstantStepSchemeIAYHat f L x0 k)
      calc
        f (monotoneConstantStepSchemeIAX f L x0 (k + 1)) ≤
            f (monotoneConstantStepSchemeIAYHat f L x0 k) -
              (1 / (2 * (L : ℝ))) *
                ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 k)‖ ^ (2 : ℕ) := hx_desc
        _ ≤ f (monotoneConstantStepSchemeIAYHat f L x0 k) := by
          exact sub_le_self _ (by positivity)
    have hxHat_desc :
        f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1)) ≤
          f (monotoneConstantStepSchemeIAY f L x0 k) -
            (1 / (2 * (L : ℝ))) *
              ‖∇ f (monotoneConstantStepSchemeIAY f L x0 k)‖ ^ (2 : ℕ) := by
      simpa [monotoneConstantStepSchemeIAXHat_succ] using
        gradient_step_value_descent_of_lipschitzGradient
          f hL (fun x ↦ (hgrad x).differentiableAt)
          (by simpa using hgrad_lipschitz)
          (monotoneConstantStepSchemeIAY f L x0 k)
    calc
      f (monotoneConstantStepSchemeIAX f L x0 (k + 1)) ≤
          f (monotoneConstantStepSchemeIAYHat f L x0 k) := hx_le_yHat
      _ ≤ f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1)) :=
          monotoneConstantStepSchemeIAYHat_objective_le_xHat f L x0 k
      _ ≤
          f (monotoneConstantStepSchemeIAY f L x0 k) -
            (1 / (2 * (L : ℝ))) *
              ‖∇ f (monotoneConstantStepSchemeIAY f L x0 k)‖ ^ (2 : ℕ) := hxHat_desc

/-
Theorem 2.26 on the intrinsic real-Hilbert-space owner layer: if `f` is convex on the whole
space, admits the ambient gradient `∇ f` everywhere, that gradient is `L`-Lipschitz in the
ambient norm, and `xStar` is a global minimizer, then the recursive monotone type-I trajectory of
method `(2.2.32)` satisfies the explicit `O(T^{-3/2})` bound on the minimum gradient norm
`g_{0,T}` over the first `T + 1` iterates. The textbook `ℝⁿ` statement is the finite-dimensional
specialization below.
-/

/-- Helper for Theorem 2.26: when `L = 0`, the Lipschitz-gradient hypothesis forces the ambient
gradient to vanish everywhere, so the finite-window minimum gradient norm is exactly zero. -/
private lemma monotoneConstantStepSchemeIA_minGradientNorm_eq_zero_of_L_eq_zero
    {L : NNReal} {f : E → ℝ}
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ}
    (hL0 : (L : ℝ) = 0) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] = 0 := by
  -- A global minimizer is stationary, so the `0`-Lipschitz gradient field is identically zero.
  have hgrad_zero_at_minimizer : ∇ f xStar = 0 :=
    isMinOn_gradient_eq_zero hxStar
  have hgrad_zero : ∀ x : E, ∇ f x = 0 := by
    intro x
    have hdist := hgrad_lipschitz.dist_le_mul x xStar
    have hdist0 : dist (∇ f x) (∇ f xStar) = 0 := by
      apply le_antisymm
      · simpa [hL0] using hdist
      · exact dist_nonneg
    simpa [hgrad_zero_at_minimizer] using eq_of_dist_eq_zero hdist0
  -- The window minimum is attained at some iterate, and that iterate has zero gradient norm.
  rcases minGradientNormAlongIterates.exists_eq
      f (monotoneConstantStepSchemeIAX f L x0) (Nat.zero_le T) with
    ⟨i, -, -, hi⟩
  rw [hi, hgrad_zero, norm_zero]

/-- Helper for Theorem 2.26: the finite-window minimum gradient norm is nonnegative because it is
attained by a gradient norm in the window. -/
private lemma monotoneConstantStepSchemeIA_minGradientNorm_nonneg
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    (T : ℕ) :
    0 ≤ g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] := by
  -- The owner minimum is realized by one iterate in the window.
  rcases minGradientNormAlongIterates.exists_eq
      f (monotoneConstantStepSchemeIAX f L x0) (Nat.zero_le T) with
    ⟨i, -, -, hi⟩
  rw [hi]
  exact norm_nonneg _

/-- Helper for Theorem 2.26: the explicit cubic denominator in the displayed rate is positive for
every admissible horizon `T ≥ 1`. -/
private lemma monotoneConstantStepSchemeIA_explicit_denominator_pos
    {T : ℕ} (hT : 1 ≤ T) :
    0 <
      ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
        (9 / 4 : ℝ) * (T + 2 : ℝ) -
        (9 / 8 : ℝ)) := by
  -- Factor the cubic denominator as `((2x - 3) (4x + 3)^2) / 24` at `x = T + 2`.
  have hT' : (1 : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hT
  have hx : (3 : ℝ) ≤ (T : ℝ) + 2 := by
    nlinarith
  have hfactor_pos : 0 < 2 * ((T : ℝ) + 2) - 3 := by
    nlinarith
  have hsquare_pos : 0 < (4 * ((T : ℝ) + 2) + 3) ^ (2 : ℕ) := by
    positivity
  have hprod_pos :
      0 < (2 * ((T : ℝ) + 2) - 3) * (4 * ((T : ℝ) + 2) + 3) ^ (2 : ℕ) := by
    positivity
  have hrewrite :
      ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
          (9 / 4 : ℝ) * (T + 2 : ℝ) -
          (9 / 8 : ℝ)) =
        ((2 * ((T : ℝ) + 2) - 3) * (4 * ((T : ℝ) + 2) + 3) ^ (2 : ℕ)) / 24 := by
    ring
  rw [hrewrite]
  positivity

/-- Helper for Theorem 2.26: every owner weight stays at most `1`. -/
private theorem optimalMethodRecurrence_weight_le_one
    {f : E → ℝ} {L μ gamma0 : ℝ} {x0 : E}
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (k : ℕ) :
    method.weight k ≤ 1 := by
  -- The owner weight starts at `1` and every update multiplies by a factor from `(0, 1)`.
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [method.weight_succ]
      have hfactor_nonneg : 0 ≤ 1 - method.alpha k := by
        linarith [(method.alpha_mem_Ioo k).2]
      have hfactor_le_one : 1 - method.alpha k ≤ 1 := by
        linarith [(method.alpha_mem_Ioo k).1]
      have hweight_nonneg : 0 ≤ method.weight k := (method.weight_pos k).le
      have hmul_le :
          (1 - method.alpha k) * method.weight k ≤ 1 * method.weight k := by
        exact mul_le_mul_of_nonneg_right hfactor_le_one hweight_nonneg
      have ih' : 1 * method.weight k ≤ 1 := by
        simpa using ih
      exact hmul_le.trans ih'

/-- Helper for Theorem 2.26: every positive-stage owner weight is strictly below `1`. -/
private theorem optimalMethodRecurrence_weight_lt_one_of_one_le
    {f : E → ℝ} {L μ gamma0 : ℝ} {x0 : E}
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    {k : ℕ} (hk : 1 ≤ k) :
    method.weight k < 1 := by
  -- Once `k ≥ 1`, the last recurrence factor is strictly smaller than `1`.
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨j, rfl⟩
  rw [method.weight_succ]
  have hfactor_nonneg : 0 ≤ 1 - method.alpha j := by
    linarith [(method.alpha_mem_Ioo j).2]
  have hfactor_lt_one : 1 - method.alpha j < 1 := by
    linarith [(method.alpha_mem_Ioo j).1]
  have hweight_nonneg : 0 ≤ method.weight j := (method.weight_pos j).le
  have hweight_le_one : method.weight j ≤ 1 :=
    optimalMethodRecurrence_weight_le_one method j
  nlinarith

/-- Helper for Theorem 2.26: the quadratic weight polynomial on `Icc 1 T` has the displayed
closed form. -/
private lemma monotoneConstantStepSchemeIA_quadratic_weight_sum_closed_form
    (T : ℕ) :
    Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) =
      ((T : ℝ) * (2 * (T : ℝ) ^ (2 : ℕ) + 9 * (T : ℝ) + 5)) / 2 := by
  -- Extend the interval sum by one top index and simplify the resulting polynomial recursion.
  induction T with
  | zero =>
      norm_num
  | succ T ih =>
      rw [Finset.sum_Icc_succ_top (show 1 ≤ T + 1 by omega), ih]
      norm_num [pow_two]
      ring_nf

/-- Helper for Theorem 2.26: the owner weight-ratio bound from Theorem 2.22 forces the summed
weight denominator to dominate the displayed cubic polynomial. -/
private lemma monotoneConstantStepSchemeIA_weight_sum_ge_explicit_denominator
    {L : NNReal} {f : E → ℝ} {x0 : E}
    (method : GeneralOptimalMethodScheme f (L : ℝ) 0 x0 (3 * (L : ℝ)))
    {T : ℕ} (hT : 1 ≤ T) :
    ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
        (9 / 4 : ℝ) * (T + 2 : ℝ) -
        (9 / 8 : ℝ)) ≤
      16 * Finset.sum (Finset.Icc 1 T) (fun k ↦
        (1 - method.toOptimalMethodRecurrence.weight k) /
          method.toOptimalMethodRecurrence.weight k) := by
  set weight : ℕ → ℝ := method.toOptimalMethodRecurrence.weight
  have hterm :
      ∀ k ∈ Finset.Icc 1 T,
        (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) ≤ 4 * ((1 - weight k) / weight k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hratio :
        weight k / (1 - weight k) ≤ 4 / (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) :=
      method.toOptimalMethodRecurrence.weight_ratio_le_of_gamma0_eq_three_mul hk1
    have hweight_pos : 0 < weight k := method.toOptimalMethodRecurrence.weight_pos k
    have hweight_lt_one : weight k < 1 :=
      optimalMethodRecurrence_weight_lt_one_of_one_le
        method.toOptimalMethodRecurrence hk1
    have hratio_pos : 0 < weight k / (1 - weight k) := by
      have hden_pos : 0 < 1 - weight k := by
        linarith
      positivity
    have hinv :
        (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) / 4 ≤ (1 - weight k) / weight k := by
      simpa [one_div_div] using one_div_le_one_div_of_le hratio_pos hratio
    nlinarith
  have hsum :
      Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) ≤
        4 * Finset.sum (Finset.Icc 1 T) (fun k ↦ (1 - weight k) / weight k) := by
    calc
      Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4)
          ≤ Finset.sum (Finset.Icc 1 T) (fun k ↦ 4 * ((1 - weight k) / weight k)) := by
            exact Finset.sum_le_sum fun k hk ↦ hterm k hk
      _ = 4 * Finset.sum (Finset.Icc 1 T) (fun k ↦ (1 - weight k) / weight k) := by
            rw [Finset.mul_sum]
  have hT' : (1 : ℝ) ≤ T := by
    exact_mod_cast hT
  have hpoly :
      ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
          (9 / 4 : ℝ) * (T + 2 : ℝ) -
          (9 / 8 : ℝ)) ≤
        4 * Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) := by
    rw [monotoneConstantStepSchemeIA_quadratic_weight_sum_closed_form]
    nlinarith
  have hfour :
      4 * Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) ≤
        16 * Finset.sum (Finset.Icc 1 T) (fun k ↦ (1 - weight k) / weight k) := by
    nlinarith
  exact hpoly.trans hfour

/-- Helper for Theorem 2.26: a global minimizer bounds every objective value below by the local
smooth quadratic gap `‖∇ f x‖² / (2L)`. -/
private lemma monotoneConstantStepSchemeIA_objective_gap_ge_gradient_sq_half_div_L
    {L : NNReal} {f : E → ℝ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    f xStar + (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) ≤ f x := by
  -- A reciprocal-`L` gradient step from `x` decreases the objective by the smooth quadratic
  -- term, and the minimizer sits below that descended value.
  have hdesc :
      f (x - (1 / (L : ℝ)) • ∇ f x) ≤
        f x - (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) := by
    simpa using
      gradient_step_value_descent_of_lipschitzGradient
        f hL (fun z ↦ (hgrad z).differentiableAt) (by simpa using hgrad_lipschitz) x
  have hmin :
      f xStar ≤ f (x - (1 / (L : ℝ)) • ∇ f x) := by
    exact isMinOn_univ_iff.mp hxStar _
  linarith

/-- Helper for Theorem 2.26: the owner interpolation point has the exact smooth-convex source
form `y_k = α_k v_k + (1 - α_k) x_k`. -/
private lemma monotoneConstantStepSchemeIA_y_eq_alpha_smul_v_add_one_sub_smul_x
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {k : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    method.y k = method.alpha k • method.v k + (1 - method.alpha k) • method k := by
  -- Route correction: rewrite the owner `y_k` formula once so the later Lyapunov step can use
  -- the source interpolation identity directly rather than raw `γ` algebra.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hgamma_eq :
      method.gamma k = method.weight k * (3 * (L : ℝ)) := by
    simpa [method] using method.gamma_sub_mu_eq_weight_mul_initial_gap k
  have hgamma_ne : method.gamma k ≠ 0 := by
    rw [hgamma_eq]
    exact mul_ne_zero (method.weight_pos k).ne' (by positivity)
  calc
    method.y k
        = (1 / method.gamma k) •
            ((method.alpha k * method.gamma k) • method.v k +
              method.gamma (k + 1) • method k) := by
            simpa [method] using method.y_eq k
    _ = (1 / method.gamma k) •
          ((method.alpha k * method.gamma k) • method.v k +
            ((1 - method.alpha k) * method.gamma k) • method k) := by
          rw [method.gamma_succ k]
          ring_nf
    _ = method.alpha k • method.v k + (1 - method.alpha k) • method k := by
          have hcoef_v :
              (1 / method.gamma k) * (method.alpha k * method.gamma k) = method.alpha k := by
            field_simp [hgamma_ne]
          have hcoef_x :
              (1 / method.gamma k) * ((1 - method.alpha k) * method.gamma k) =
                1 - method.alpha k := by
            field_simp [hgamma_ne]
          rw [smul_add, smul_smul, smul_smul, hcoef_v, hcoef_x]

/-- Helper for Theorem 2.26: the monotone comparison chain from `y_m` down to the actual iterate
`x_{m+1}` yields three explicit gradient-square terms above the minimizer. -/
private lemma monotoneConstantStepSchemeIA_stage_objective_drop_to_minimizer
    {L : NNReal} {f : E → ℝ}
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    f (method.y m) - f xStar ≥
      (1 / (2 * (L : ℝ))) *
        (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
          ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
          ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
  -- Package the exact source chain
  -- `x_{m+1} ≤ ŷ_m ≤ x̂_{m+1} ≤ y_m`
  -- into one inequality that already ends at the minimizer `xStar`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hx_succ_desc :
      f (method.x (m + 1)) ≤
        f (monotoneConstantStepSchemeIAYHat f L x0 m) -
          (1 / (2 * (L : ℝ))) *
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) := by
    -- Rewrite the owner iterate back to the source successor formula before applying descent.
    change f (monotoneConstantStepSchemeIAX f L x0 (m + 1)) ≤
      f (monotoneConstantStepSchemeIAYHat f L x0 m) -
        (1 / (2 * (L : ℝ))) *
          ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ)
    simpa [monotoneConstantStepSchemeIAX_succ] using
      gradient_step_value_descent_of_lipschitzGradient
        f hL (fun x ↦ (hgrad x).differentiableAt) (by simpa using hgrad_lipschitz)
        (monotoneConstantStepSchemeIAYHat f L x0 m)
  have hyHat_le_xHat :
      f (monotoneConstantStepSchemeIAYHat f L x0 m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) :=
    monotoneConstantStepSchemeIAYHat_objective_le_xHat f L x0 m
  have hxHat_desc :
      f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) ≤
        f (method.y m) -
          (1 / (2 * (L : ℝ))) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    simpa [method, monotoneConstantStepSchemeIAXHat_succ] using
      gradient_step_value_descent_of_lipschitzGradient
        f hL (fun x ↦ (hgrad x).differentiableAt) (by simpa using hgrad_lipschitz)
        (method.y m)
  have hx_gap :
      f xStar +
          (1 / (2 * (L : ℝ))) * ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) ≤
        f (method.x (m + 1)) := by
    -- Insert the actual iterate into the local smooth minimizer gap.
    exact monotoneConstantStepSchemeIA_objective_gap_ge_gradient_sq_half_div_L
      hL hgrad hgrad_lipschitz xStar hxStar (method.x (m + 1))
  linarith

/-- Helper for Theorem 2.26: the bridged owner center update has the smooth-convex source form
`v_{k+1} = v_k - (α_k / γ_{k+1}) ∇ f(y_k)`. -/
private lemma monotoneConstantStepSchemeIA_center_step_eq_sub_weighted_gradient
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {k : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    method.v (k + 1) =
      method.v k - (method.alpha k / method.gamma (k + 1)) • ∇ f (method.y k) := by
  -- Rewrite the owner successor once so the remaining Lyapunov algebra sees a single gradient step.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hgamma_next :
      method.gamma (k + 1) = method.weight (k + 1) * (3 * (L : ℝ)) := by
    simpa [method] using method.gamma_sub_mu_eq_weight_mul_initial_gap (k + 1)
  have hgamma_next_ne : method.gamma (k + 1) ≠ 0 := by
    rw [hgamma_next]
    exact mul_ne_zero (method.weight_pos (k + 1)).ne' (by positivity)
  calc
    method.v (k + 1)
        = (1 / method.gamma (k + 1)) •
            (((1 - method.alpha k) * method.gamma k) • method.v k -
              method.alpha k • ∇ f (method.y k)) := by
            simpa [method] using method.v_succ k
    _ = (1 / method.gamma (k + 1)) •
          (method.gamma (k + 1) • method.v k -
            method.alpha k • ∇ f (method.y k)) := by
          rw [method.gamma_succ k]
          ring_nf
    _ = (1 / method.gamma (k + 1)) • (method.gamma (k + 1) • method.v k) -
          (1 / method.gamma (k + 1)) • (method.alpha k • ∇ f (method.y k)) := by
          rw [smul_sub]
    _ = method.v k - (method.alpha k / method.gamma (k + 1)) • ∇ f (method.y k) := by
          rw [smul_smul, one_div, inv_mul_cancel₀ hgamma_next_ne, one_smul]
          rw [smul_smul]
          congr 1
          field_simp [hgamma_next_ne]

/-- Helper for Theorem 2.26: the `v_m - y_m` part of the mixed inner product is exactly the
source tangent-plane term against the current iterate `x_m`. -/
private lemma monotoneConstantStepSchemeIA_v_minus_y_inner_ge_scaled_objective_drop
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - method.y m) ≥
      (1 - method.alpha m) * (f (method.y m) - f (method m)) := by
  -- Rewrite `y_m = α_m v_m + (1 - α_m) x_m`, then apply the tangent-plane lower bound at `y_m`
  -- to the current iterate `x_m`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hfactor_nonneg : 0 ≤ 1 - method.alpha m := by
    linarith [(method.alpha_mem_Ioo m).2]
  have htangent :
      f (method.y m) + inner ℝ (∇ f (method.y m)) (method m - method.y m) ≤
        f (method m) := by
    have hlower :=
      ConvexOn.lower_tangent_plane_of_hasGradientWithinAt hconvex
        (method.y m) (by simp) (∇ f (method.y m))
        ((hasGradientWithinAt_univ).2 (hgrad (method.y m)))
        (method m) (by simp)
    linarith
  have htangent_scaled :
      (1 - method.alpha m) *
          (f (method.y m) + inner ℝ (∇ f (method.y m)) (method m - method.y m)) ≤
        (1 - method.alpha m) * f (method m) := by
    exact mul_le_mul_of_nonneg_left htangent hfactor_nonneg
  have hcancel_vec :
      (1 - method.alpha m) • (method m - method.y m) +
        method.alpha m • (method.v m - method.y m) = 0 := by
    rw [monotoneConstantStepSchemeIA_y_eq_alpha_smul_v_add_one_sub_smul_x
      (f := f) (L := L) x0 (k := m) hL hgrad hgrad_lipschitz]
    module
  have hcancel_inner :
      (1 - method.alpha m) * inner ℝ (∇ f (method.y m)) (method m - method.y m) +
        method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - method.y m) = 0 := by
    have hinner :=
      congrArg (fun z ↦ inner ℝ (∇ f (method.y m)) z) hcancel_vec
    simpa [inner_add_right, inner_smul_right] using hinner
  have hdom :
      (1 - method.alpha m) * f (method.y m) +
          (1 - method.alpha m) * inner ℝ (∇ f (method.y m)) (method m - method.y m) ≤
        (1 - method.alpha m) * f (method m) := by
    simpa [mul_add] using htangent_scaled
  linarith

/-- Helper for Theorem 2.26: the stage objective gap already carries the exact scalar coefficient
needed downstream once it is expressed against the iterate window minimum `g_{0,T}`. -/
private lemma monotoneConstantStepSchemeIA_stage_scalar_gap_lower_bound
    {L : NNReal} {f : E → ℝ}
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m T : ℕ}
    (hL : 0 < (L : ℝ))
    (hmT : m < T) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) *
        (f (method.y m) -
          ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar)) ≥
      ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
        (3 - method.alpha m ^ (2 : ℕ)) *
          g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) := by
  -- TODO: convert the stage objective chain
  -- `f (method.y m) -> f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))
  -- -> f (monotoneConstantStepSchemeIAYHat f L x0 m) -> f (method.x (m + 1))`
  -- together with the iterate-window bounds at the actual iterates `m` and `m + 1`
  -- into the exact scalar coefficient `3 - method.alpha m ^ 2`.
  have _ :=
    monotoneConstantStepSchemeIA_stage_objective_drop_to_minimizer
      (f := f) (L := L) hgrad hgrad_lipschitz xStar hxStar x0 (m := m) hL
  have _ :
      g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ≤
        ‖∇ f (monotoneConstantStepSchemeIAX f L x0 m)‖ := by
    exact minGradientNormAlongIterates.le
      f (monotoneConstantStepSchemeIAX f L x0) (Nat.zero_le T) (Nat.zero_le m) (Nat.le_of_lt hmT)
  have _ :
      g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ≤
        ‖∇ f (monotoneConstantStepSchemeIAX f L x0 (m + 1))‖ := by
    exact minGradientNormAlongIterates.le
      f (monotoneConstantStepSchemeIAX f L x0) (Nat.zero_le T)
      (Nat.zero_le (m + 1)) hmT
  sorry

/-- Helper for Theorem 2.26: the stage mixed inner product carries the exact textbook scalar
coefficient needed for the Lyapunov norm expansion. -/
private lemma monotoneConstantStepSchemeIA_stage_inner_product_lower_bound
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m T : ℕ}
    (hL : 0 < (L : ℝ))
    (hmT : m < T) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * method.alpha m *
        inner ℝ (∇ f (method.y m)) (method.v m - xStar) ≥
      ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
        (3 - method.alpha m ^ (2 : ℕ)) *
          g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) := by
  -- Route correction: isolate the coefficient-producing scalar estimate first, then use this
  -- lemma only as the mixed-inner-product adapter needed by the Lyapunov norm expansion.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have halpha_nonneg : 0 ≤ method.alpha m := (method.alpha_pos m).le
  have hv_split :
      method.v m - xStar = (method.v m - method.y m) + (method.y m - xStar) := by
    abel
  have hvy :
      method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - method.y m) ≥
        (1 - method.alpha m) * (f (method.y m) - f (method m)) := by
    simpa [method] using
      monotoneConstantStepSchemeIA_v_minus_y_inner_ge_scaled_objective_drop
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz x0 (m := m) hL
  have hyxStar :
      method.alpha m * inner ℝ (∇ f (method.y m)) (method.y m - xStar) ≥
        method.alpha m * (f (method.y m) - f xStar) := by
    -- Apply the lower tangent-plane inequality at `y_m` to the minimizer `xStar`.
    have htangent :
        f (method.y m) + inner ℝ (∇ f (method.y m)) (xStar - method.y m) ≤
          f xStar := by
      exact ConvexOn.lower_tangent_plane_of_hasGradientWithinAt hconvex
        (method.y m) (by simp) (∇ f (method.y m))
        ((hasGradientWithinAt_univ).2 (hgrad (method.y m)))
        xStar (by simp)
    have hinner :
        inner ℝ (∇ f (method.y m)) (method.y m - xStar) ≥ f (method.y m) - f xStar := by
      have htangent' :
          f (method.y m) ≤
            f xStar + inner ℝ (∇ f (method.y m)) (method.y m - xStar) := by
        have hneg :
            inner ℝ (∇ f (method.y m)) (xStar - method.y m) =
              -inner ℝ (∇ f (method.y m)) (method.y m - xStar) := by
          rw [show xStar - method.y m = -(method.y m - xStar) by abel, inner_neg_right]
        rw [hneg] at htangent
        linarith
      linarith
    exact mul_le_mul_of_nonneg_left hinner.le halpha_nonneg
  have hscalar :
      2 * (L : ℝ) *
          (f (method.y m) -
            ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar)) ≥
        ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
          (3 - method.alpha m ^ (2 : ℕ)) *
            g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) := by
    simpa [method] using
      monotoneConstantStepSchemeIA_stage_scalar_gap_lower_bound
        (f := f) (L := L) hgrad hgrad_lipschitz xStar hxStar x0 (m := m) (T := T) hL hmT
  have hsplit :
      method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - xStar) ≥
        f (method.y m) -
          ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar) := by
    -- Decompose `v_m - xStar` into the source pieces `(v_m - y_m)` and `(y_m - xStar)`.
    calc
      method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - xStar)
          =
        method.alpha m *
            inner ℝ (∇ f (method.y m))
              ((method.v m - method.y m) + (method.y m - xStar)) := by
                rw [hv_split]
      _ =
        method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - method.y m) +
          method.alpha m * inner ℝ (∇ f (method.y m)) (method.y m - xStar) := by
            rw [inner_add_right, mul_add]
      _ ≥
        (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          method.alpha m * (f (method.y m) - f xStar) := by
            exact add_le_add hvy hyxStar
      _ =
        f (method.y m) -
          ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar) := by
            ring
  have hscaled :
      2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - xStar) ≥
        2 * (L : ℝ) *
          (f (method.y m) -
            ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar)) := by
    have hscaled' :=
      mul_le_mul_of_nonneg_left hsplit (show 0 ≤ 2 * (L : ℝ) by positivity)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled'
  exact le_trans hscalar hscaled

/-- Helper for Theorem 2.26: the successor weight coefficient is exactly
`(3 - α_m^2) / α_m^2` when `γ₀ = 3L`. -/
private lemma monotoneConstantStepSchemeIA_weight_ratio_eq_alpha_sq
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    ((1 - method.toOptimalMethodRecurrence.weight (m + 1)) /
        method.toOptimalMethodRecurrence.weight (m + 1)) =
      (3 - method.alpha m ^ (2 : ℕ)) / (method.alpha m ^ (2 : ℕ)) := by
  -- Rewrite `λ_{m+1}` from `γ_{m+1} = λ_{m+1} (3L)` and `γ_{m+1} = L α_m^2`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hgamma_weight :
      method.gamma (m + 1) = method.toOptimalMethodRecurrence.weight (m + 1) * (3 * (L : ℝ)) := by
    simpa [method] using method.gamma_sub_mu_eq_weight_mul_initial_gap (m + 1)
  have hgamma_alpha :
      method.gamma (m + 1) = (L : ℝ) * method.alpha m ^ (2 : ℕ) := by
    simpa [method] using method.gamma_succ_eq_L_mul_sq m
  have hweight_eq :
      method.toOptimalMethodRecurrence.weight (m + 1) = method.alpha m ^ (2 : ℕ) / 3 := by
    have hthreeL_ne : (3 * (L : ℝ)) ≠ 0 := by
      exact mul_ne_zero (by norm_num) hL.ne'
    calc
      method.toOptimalMethodRecurrence.weight (m + 1)
          = (method.toOptimalMethodRecurrence.weight (m + 1) * (3 * (L : ℝ))) / (3 * (L : ℝ)) := by
              field_simp [hthreeL_ne]
      _ = ((L : ℝ) * method.alpha m ^ (2 : ℕ)) / (3 * (L : ℝ)) := by
            rw [← hgamma_weight, hgamma_alpha]
      _ = method.alpha m ^ (2 : ℕ) / 3 := by
            field_simp [hL.ne']
  have halpha_sq_ne : method.alpha m ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 (method.alpha_pos m).ne'
  change (1 - ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m)) /
      ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m) =
    (3 - method.alpha m ^ (2 : ℕ)) / (method.alpha m ^ (2 : ℕ))
  rw [← method.toOptimalMethodRecurrence.weight_succ m, hweight_eq]
  field_simp [halpha_sq_ne]

/-- Helper for Theorem 2.26: once the mixed inner product is normalized, the center update yields
the one-step Lyapunov drop with the textbook weight coefficient. -/
private lemma monotoneConstantStepSchemeIA_weighted_descent_potential_step
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m T : ℕ}
    (hL : 0 < (L : ℝ))
    (hmT : m < T) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v (m + 1) - xStar‖ ^ (2 : ℕ) +
        16 * g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) *
          ((1 - method.toOptimalMethodRecurrence.weight (m + 1)) /
            method.toOptimalMethodRecurrence.weight (m + 1)) ≤
      (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v m - xStar‖ ^ (2 : ℕ) := by
  -- Expand the norm square using the source center update, then substitute the normalized
  -- inner-product lower bound and the explicit weight-ratio identity.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
  have hstage :
      2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - xStar) ≥
        ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
          (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) := by
    simpa [g0, method] using
      monotoneConstantStepSchemeIA_stage_inner_product_lower_bound
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar hxStar x0
        (m := m) (T := T) hL hmT
  have hratio :
      ((1 - method.toOptimalMethodRecurrence.weight (m + 1)) /
          method.toOptimalMethodRecurrence.weight (m + 1)) =
        (3 - method.alpha m ^ (2 : ℕ)) / (method.alpha m ^ (2 : ℕ)) := by
    simpa [method] using
      monotoneConstantStepSchemeIA_weight_ratio_eq_alpha_sq
        (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz
  have hcenter :
      method.v (m + 1) =
        method.v m - (method.alpha m / method.gamma (m + 1)) • ∇ f (method.y m) := by
    simpa [method] using
      monotoneConstantStepSchemeIA_center_step_eq_sub_weighted_gradient
        (f := f) (L := L) x0 (k := m) hL hgrad hgrad_lipschitz
  have hgamma_alpha :
      method.gamma (m + 1) = (L : ℝ) * method.alpha m ^ (2 : ℕ) := by
    simpa [method] using method.gamma_succ_eq_L_mul_sq m
  have halpha_ne : method.alpha m ≠ 0 := (method.alpha_pos m).ne'
  have hstep_eq :
      method.v (m + 1) - xStar =
        (method.v m - xStar) -
          ((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m)) := by
    -- Normalize the center step to a single scalar multiple of the current gradient.
    have hcoeff :
        method.alpha m / method.gamma (m + 1) = 1 / ((L : ℝ) * method.alpha m) := by
      rw [hgamma_alpha]
      field_simp [hL.ne', halpha_ne]
    calc
      method.v (m + 1) - xStar
          = (method.v m - (method.alpha m / method.gamma (m + 1)) • ∇ f (method.y m)) - xStar := by
              rw [hcenter]
      _ = (method.v m - xStar) - (method.alpha m / method.gamma (m + 1)) • ∇ f (method.y m) := by
            abel
      _ = (method.v m - xStar) - ((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m)) := by
            rw [hcoeff]
  have hnorm_smul :
      ‖((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m))‖ ^ (2 : ℕ) =
        (1 / ((L : ℝ) * method.alpha m)) ^ (2 : ℕ) *
          ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Compute the square norm through the real inner product to avoid absolute-value clutter.
    calc
      ‖((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m))‖ ^ (2 : ℕ)
          = inner ℝ
              (((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m)))
              (((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m))) := by
                rw [real_inner_self_eq_norm_sq]
      _ =
        (1 / ((L : ℝ) * method.alpha m)) ^ (2 : ℕ) *
          ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
            ring
  have hnorm_expand :
      ‖method.v (m + 1) - xStar‖ ^ (2 : ℕ) =
        ‖method.v m - xStar‖ ^ (2 : ℕ) -
          2 * (1 / ((L : ℝ) * method.alpha m)) *
            inner ℝ (∇ f (method.y m)) (method.v m - xStar) +
          (1 / ((L : ℝ) * method.alpha m)) ^ (2 : ℕ) *
            ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Expand the normalized step with the real Hilbert-space norm-square identity.
    rw [hstep_eq]
    show
      ‖(method.v m - xStar) -
          ((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m))‖ ^ (2 : ℕ) =
        ‖method.v m - xStar‖ ^ (2 : ℕ) -
          2 * (1 / ((L : ℝ) * method.alpha m)) *
            inner ℝ (∇ f (method.y m)) (method.v m - xStar) +
          (1 / ((L : ℝ) * method.alpha m)) ^ (2 : ℕ) *
            ‖∇ f (method.y m)‖ ^ (2 : ℕ)
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm, hnorm_smul]
    ring
  have hratio' :
      ((1 - ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m)) /
          ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m)) =
        (3 - method.alpha m ^ (2 : ℕ)) / (method.alpha m ^ (2 : ℕ)) := by
    simpa [method.toOptimalMethodRecurrence.weight_succ] using hratio
  rw [hratio']
  rw [hnorm_expand]
  set a : ℝ := ‖method.v m - xStar‖ ^ (2 : ℕ)
  set b : ℝ := inner ℝ (∇ f (method.y m)) (method.v m - xStar)
  set c : ℝ := ‖∇ f (method.y m)‖ ^ (2 : ℕ)
  set α : ℝ := method.alpha m
  have hstage' :
      2 * (L : ℝ) * α * b ≥ c + (3 - α ^ (2 : ℕ)) * g0 ^ (2 : ℕ) := by
    simpa [a, b, c, α] using hstage
  have hcoeff_nonneg : 0 ≤ 16 / α ^ (2 : ℕ) := by
    have halpha_pos : 0 < α := by
      simpa [α] using method.alpha_pos m
    positivity
  have hnonpos :
      c + (3 - α ^ (2 : ℕ)) * g0 ^ (2 : ℕ) - 2 * (L : ℝ) * α * b ≤ 0 := by
    linarith
  have hdiff :
      (4 * (L : ℝ)) ^ (2 : ℕ) *
          (a - 2 * (1 / ((L : ℝ) * α)) * b + (1 / ((L : ℝ) * α)) ^ (2 : ℕ) * c) +
        16 * g0 ^ (2 : ℕ) * ((3 - α ^ (2 : ℕ)) / α ^ (2 : ℕ)) -
        (4 * (L : ℝ)) ^ (2 : ℕ) * a =
      (16 / α ^ (2 : ℕ)) *
        (c + (3 - α ^ (2 : ℕ)) * g0 ^ (2 : ℕ) - 2 * (L : ℝ) * α * b) := by
    field_simp [halpha_ne, hL.ne']
    ring
  have hdiff_nonpos :
      (4 * (L : ℝ)) ^ (2 : ℕ) *
          (a - 2 * (1 / ((L : ℝ) * α)) * b + (1 / ((L : ℝ) * α)) ^ (2 : ℕ) * c) +
        16 * g0 ^ (2 : ℕ) * ((3 - α ^ (2 : ℕ)) / α ^ (2 : ℕ)) -
        (4 * (L : ℝ)) ^ (2 : ℕ) * a ≤ 0 := by
    rw [hdiff]
    exact mul_nonpos_of_nonneg_of_nonpos hcoeff_nonneg hnonpos
  exact sub_nonpos.mp hdiff_nonpos

/-- Helper for Theorem 2.26: the remaining positive-`L` step is the source-faithful weighted
descent sum for the monotone type-I trajectory. -/
private lemma monotoneConstantStepSchemeIA_weighted_descent_sum_le_initial_radius_sq
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ} (hL : 0 < (L : ℝ)) (_hT : 1 ≤ T) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) *
        (16 * Finset.sum (Finset.Icc 1 T) (fun k ↦
          (1 -
              (monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
                f L x0 hL hgrad hgrad_lipschitz).toOptimalMethodRecurrence.weight k) /
            (monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
              f L x0 hL hgrad hgrad_lipschitz).toOptimalMethodRecurrence.weight k)) ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
  -- Route correction: once the one-step Lyapunov drop is packaged as a standalone lemma, the
  -- weighted sum is only a telescope plus the nonnegativity of the terminal norm term.
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let ratio : ℕ → ℝ := fun k ↦
    (1 - method.toOptimalMethodRecurrence.weight k) /
      method.toOptimalMethodRecurrence.weight k
  let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
  have htelescoping :
      ∀ n ≤ T,
        (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v n - xStar‖ ^ (2 : ℕ) +
            16 * g0 ^ (2 : ℕ) * Finset.sum (Finset.Icc 1 n) ratio ≤
          (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
    intro n hnT
    induction n with
    | zero =>
        -- The telescope starts from `v₀ = x₀`, and the initial interval sum is empty.
        have hv0 : method.v 0 = x0 := by
          simpa [method] using method.v_zero
        rw [hv0]
        simp [ratio]
        have hsq :
            (4 * (L : ℝ)) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ) =
              (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
          ring
        exact hsq.le
    | succ n ihn =>
        have hn_lt_T : n < T := Nat.lt_of_succ_le hnT
        have hstep :
            (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v (n + 1) - xStar‖ ^ (2 : ℕ) +
                16 * g0 ^ (2 : ℕ) * ratio (n + 1) ≤
              (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v n - xStar‖ ^ (2 : ℕ) := by
          simpa [g0, ratio] using
          monotoneConstantStepSchemeIA_weighted_descent_potential_step
            (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar hxStar x0
            (m := n) (T := T) hL hn_lt_T
        have hprev := ihn (Nat.le_of_lt hn_lt_T)
        rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
        have hstep_added :
            (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v (n + 1) - xStar‖ ^ (2 : ℕ) +
                16 * g0 ^ (2 : ℕ) * ratio (n + 1) +
                16 * g0 ^ (2 : ℕ) * Finset.sum (Finset.Icc 1 n) ratio ≤
              (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v n - xStar‖ ^ (2 : ℕ) +
                16 * g0 ^ (2 : ℕ) * Finset.sum (Finset.Icc 1 n) ratio := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_right hstep (16 * g0 ^ (2 : ℕ) * Finset.sum (Finset.Icc 1 n) ratio)
        calc
          (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v (n + 1) - xStar‖ ^ (2 : ℕ) +
              16 * g0 ^ (2 : ℕ) *
                (Finset.sum (Finset.Icc 1 n) ratio + ratio (n + 1))
              =
            ((4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v (n + 1) - xStar‖ ^ (2 : ℕ) +
                16 * g0 ^ (2 : ℕ) * ratio (n + 1)) +
              16 * g0 ^ (2 : ℕ) * Finset.sum (Finset.Icc 1 n) ratio := by
                ring
          _ ≤ (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v n - xStar‖ ^ (2 : ℕ) +
                16 * g0 ^ (2 : ℕ) * Finset.sum (Finset.Icc 1 n) ratio := by
                exact hstep_added
          _ ≤ (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := hprev
  have hterminal :=
    htelescoping T le_rfl
  have hterm_nonneg :
      0 ≤ (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v T - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hdrop :
      16 * g0 ^ (2 : ℕ) * Finset.sum (Finset.Icc 1 T) ratio ≤
        (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
    calc
      16 * g0 ^ (2 : ℕ) * Finset.sum (Finset.Icc 1 T) ratio
          ≤ (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v T - xStar‖ ^ (2 : ℕ) +
              16 * g0 ^ (2 : ℕ) * Finset.sum (Finset.Icc 1 T) ratio := by
                exact le_add_of_nonneg_left hterm_nonneg
      _ ≤ (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := hterminal
  simpa [g0, ratio, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm,
    add_assoc, add_left_comm, add_comm] using hdrop

/-- Helper for Theorem 2.26: on the positive-`L` branch, the source squared estimate `(2.u398)`
controls the minimum gradient norm over the first `T + 1` iterates. -/
private lemma monotoneConstantStepSchemeIA_sq_minGradientNorm_mul_explicit_denominator_le_of_pos
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ} (hL : 0 < (L : ℝ)) (hT : 1 ≤ T) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) *
        (((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ)) -
          ((9 / 4 : ℝ) * (T + 2 : ℝ)) -
          (9 / 8 : ℝ)) ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
  -- Route correction: separate the positive-`L` proof into the structural weighted-descent sum
  -- and the scalar weight-denominator comparison from Theorem 2.22.
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hweighted :=
    monotoneConstantStepSchemeIA_weighted_descent_sum_le_initial_radius_sq
      hconvex hgrad hgrad_lipschitz xStar hxStar x0 hL hT
  have hscalar :=
    monotoneConstantStepSchemeIA_weight_sum_ge_explicit_denominator (method := method) hT
  have hmul :
      g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) *
          (((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ)) -
            ((9 / 4 : ℝ) * (T + 2 : ℝ)) -
            (9 / 8 : ℝ)) ≤
        g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) *
          (16 * Finset.sum (Finset.Icc 1 T) (fun k ↦
            (1 - method.toOptimalMethodRecurrence.weight k) /
              method.toOptimalMethodRecurrence.weight k)) := by
    exact mul_le_mul_of_nonneg_left hscalar (sq_nonneg _)
  exact hmul.trans (by simpa [method] using hweighted)

-- Proof sketch: on the positive-`L` branch, use
-- `monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz`
-- only as the bridge supplying the owner step-`(c)` descent inequality, then combine that bridge
-- with the source monotone comparison data `x̂ₖ`, `ŷₖ` and the exact update
-- `x_{k+1} = ŷ_k - (1 / L) ∇ f(ŷ_k)` to transfer the resulting function-gap control to the actual
-- iterate gradients `‖∇ f (x_k)‖`. When `L = 0`, the intrinsic gradient hypotheses together with
-- a minimizer forces the gradients to vanish, so the same bound is immediate. After telescoping
-- the tail inequality, identify the textbook `g_{0,T}` with `minGradientNormAlongIterates` and
-- simplify the coefficient sum to the displayed cubic polynomial in `T + 2`.
/-- Theorem 2.26 on the intrinsic real-Hilbert-space owner layer: if `f` is convex on the whole
space, admits the ambient gradient `∇ f` everywhere, that gradient is `L`-Lipschitz in the
ambient norm, and `xStar` is a global minimizer, then the recursive monotone type-I trajectory of
method `(2.2.32)` satisfies the explicit `O(T^{-3/2})` bound on the minimum gradient norm
`g_{0,T}` over the first `T + 1` iterates. The textbook `ℝⁿ` statement is the finite-dimensional
specialization below. -/
theorem monotoneConstantStepSchemeIA_minGradientNormAlongIterates_le_explicit_bound
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ} (hT : 1 ≤ T) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) /
        Real.sqrt
          ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
            (9 / 4 : ℝ) * (T + 2 : ℝ) -
            (9 / 8 : ℝ)) := by
  by_cases hL0 : (L : ℝ) = 0
  · -- In the degenerate case `L = 0`, every gradient vanishes and the right-hand side is zero.
    rw [monotoneConstantStepSchemeIA_minGradientNorm_eq_zero_of_L_eq_zero
      hgrad_lipschitz xStar hxStar x0 hL0]
    simp [hL0]
  · have hL : 0 < (L : ℝ) := by
      exact lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL0)
    have hmin_nonneg :
        0 ≤ g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] :=
      monotoneConstantStepSchemeIA_minGradientNorm_nonneg x0 T
    have hden_pos :
        0 <
          ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
            (9 / 4 : ℝ) * (T + 2 : ℝ) -
            (9 / 8 : ℝ)) :=
      monotoneConstantStepSchemeIA_explicit_denominator_pos hT
    have hsq :=
      monotoneConstantStepSchemeIA_sq_minGradientNorm_mul_explicit_denominator_le_of_pos
        hconvex hgrad hgrad_lipschitz xStar hxStar x0 hL hT
    let denom : ℝ :=
      ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
        (9 / 4 : ℝ) * (T + 2 : ℝ) -
        (9 / 8 : ℝ))
    let rhs : ℝ := (4 * (L : ℝ) * ‖x0 - xStar‖) / Real.sqrt denom
    have hsq_div :
        g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) ≤
          (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) / denom := by
      exact (le_div_iff₀ (by simpa [denom] using hden_pos)).2 (by simpa [denom] using hsq)
    have hrhs_nonneg : 0 ≤ rhs := by
      -- The displayed right-hand side is a nonnegative quotient by a positive square root.
      dsimp [rhs]
      positivity
    have hrhs_sq :
        rhs ^ (2 : ℕ) =
          (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) / denom := by
      -- Squaring removes the square root in the denominator.
      dsimp [rhs]
      rw [div_pow]
      rw [Real.sq_sqrt (by simpa [denom] using hden_pos.le)]
    have hsq_rhs :
        g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) ≤
          rhs ^ (2 : ℕ) := by
      simpa [hrhs_sq] using hsq_div
    simpa [rhs, denom] using (sq_le_sq₀ hmin_nonneg hrhs_nonneg).1 hsq_rhs

/-- Finite-dimensional Chapter 2 bridge form of Theorem 2.26 using the source-facing notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`. -/
theorem monotoneConstantStepSchemeIA_minGradientNormAlongIterates_le_explicit_bound_of_mem_F11
    [FiniteDimensional ℝ E]
    {L : NNReal} {f : E → ℝ}
    (hf : f ∈ 𝓕[L, p]¹¹)
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ} (hT : 1 ≤ T) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) /
        Real.sqrt
          ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
            (9 / 4 : ℝ) * (T + 2 : ℝ) -
            (9 / 8 : ℝ)) :=
  monotoneConstantStepSchemeIA_minGradientNormAlongIterates_le_explicit_bound
    hf.convexOn hf.hasGradientAt hf.gradient_lipschitz xStar hxStar x0 hT
