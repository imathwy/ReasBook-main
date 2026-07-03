import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_1_1
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_1_2
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_1_3
import LecturesConvexOptimization_Nesterov_2018.Chap04.Lemma_4_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped LevelSetNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.1.3 lies in the cubic-regularization / Hessian-Lipschitz descent domain.

Sampled owner declarations:
* `HessianLipschitzOn` in `Definition_4_1_2`
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`
* `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y` in `Definition_4_1_3`
* `regularizedHessian_isPositive_of_isMinOn_cubicRegularizationQuadraticApproximation` in
  `Lemma_4_1_2`
* `𝓛[f](α)` together with `mem_levelSet_iff` in `Definition_4_1_1`

Source/core/bridge triage:
* source-facing: the inner-product inequality `(4.1.9)` and the sharper
  `M > (2 / 3) L` level-set/feasibility conclusion of Lemma 4.1.3
* core/canonical: `HessianLipschitzOn`, `cubicRegularizationQuadraticApproximation`,
  `IsMinOn ... Set.univ ...`, and the chapter sublevel-set owner `𝓛[f]((f x))`
* bridge/view: the passage from sublevel membership to feasibility through the ambient inclusion
  `𝓛[f]((f x)) ⊆ 𝓕`

Primitive data:
* the feasible region `𝓕`
* the Hessian-Lipschitz owner `[HessianLipschitzOn L 𝓕 f]`
* the cubic-model minimizer hypothesis
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint`
* for the inner-product inequality `(4.1.9)`, the base point membership `x ∈ 𝓕`
* the source threshold `((2 / 3 : ℝ) * (L : ℝ) < M)`
* the current-sublevel inclusion `𝓛[f]((f x)) ⊆ 𝓕`, which is the primitive chapter context
  behind the textbook phrase `𝓛(f(x)) ⊂ 𝓕`; this already implies `x ∈ 𝓕` because
  `x ∈ 𝓛[f]((f x))`

Derived API:
* the source inequality `⟪∇ f(x), x - T_M(x)⟫ ≥ 0`
* the source level-set/feasibility conclusion for the cubic trial point

The previous refinement narrowed the main theorem to the stronger owner bound `L ≤ M` and only the
ambient sublevel inequality. This file restores the sharper source-facing threshold
`M > (2 / 3) L` and keeps the level-set/feasibility conclusion as the main public entry, while
still using the chapter’s canonical minimizer and sublevel owners on the theorem surface. -/

section

variable {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x trialPoint : E}

/-- Helper for Lemma 4.1.3: the scalar first-order optimality condition along the segment from
`x` to the minimizing trial point rewrites the gradient pairing as the regularized quadratic
form from the source proof. -/
lemma gradient_pairing_eq_regularized_quadratic_form
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕) :
    inner ℝ (∇ f x) (x - trialPoint) =
      inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
        (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
  -- TODO: recover the textbook stationarity identity by differentiating the cubic model along the
  -- affine line `α ↦ x + α • (trialPoint - x)` at `α = 1`.
  sorry

/-- Helper for Lemma 4.1.3: the missing source inequality
`⟪∇²f(x)(trialPoint - x), trialPoint - x⟫ + (M / 2) ‖trialPoint - x‖^3 ≥ 0` is the scalar
regularized-Hessian positivity input used immediately after the stationarity identity. -/
lemma regularized_quadratic_form_nonneg
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕) :
    0 ≤ inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
      (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
  -- TODO: supply the missing regularized-Hessian positivity route from Lemma 4.1.2, or prove
  -- this scalar inequality directly by a local replacement of the same source step.
  sorry

/-- Lemma 4.1.3, inequality `(4.1.9)`: for a minimizing cubic trial point, the displacement
`x - trialPoint` has nonnegative pairing with the gradient at the base point `x`. Specializing to
`trialPoint = T_M(x)` recovers the textbook formula. -/
theorem inner_gradient_base_sub_cubicTrialPoint_nonneg
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕) :
    0 ≤ inner ℝ (∇ f x) (x - trialPoint) := by
  -- Route correction: first rewrite the pairing by the stationarity identity, then discharge the
  -- resulting scalar form by the regularized-Hessian nonnegativity input.
  have hpair :=
    gradient_pairing_eq_regularized_quadratic_form (L := L) (𝓕 := 𝓕) (f := f)
      (M := M) (x := x) (trialPoint := trialPoint) hstep hx
  simpa [hpair] using
    regularized_quadratic_form_nonneg (L := L) (𝓕 := 𝓕) (f := f)
      (M := M) (x := x) (trialPoint := trialPoint) hstep hx

/-- Helper for Lemma 4.1.3: every feasible point on the segment from `x` to the minimizing trial
point satisfies the source cubic-decrease estimate. -/
lemma segment_objective_drop_of_mem_feasible
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hz : x + α • (trialPoint - x) ∈ 𝓕) :
    f (x + α • (trialPoint - x)) ≤
      f x - α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
  let z : E := x + α • (trialPoint - x)
  have herror :=
    HessianLipschitzOn.secondOrderTaylorModel_error_le
      (hf := (inferInstance : HessianLipschitzOn L 𝓕 f)) x z hx hz
  -- First replace `f z` by the quadratic Taylor model plus the cubic Hessian-Lipschitz error.
  have hupper :
      f z ≤ secondOrderTaylorModelAt f x z + ((L : ℝ) / 6) * ‖z - x‖ ^ (3 : ℕ) := by
    linarith [(abs_le.mp herror).2]
  have hpair :=
    gradient_pairing_eq_regularized_quadratic_form (L := L) (𝓕 := 𝓕) (f := f)
      (M := M) (x := x) (trialPoint := trialPoint) hstep hx
  have hnonneg :=
    inner_gradient_base_sub_cubicTrialPoint_nonneg (L := L) (𝓕 := 𝓕) (f := f)
      (M := M) (x := x) (trialPoint := trialPoint) hstep hx
  have hzsub : z - x = α • (trialPoint - x) := by
    dsimp [z]
    abel_nf
  have hquad_scale :
      inner ℝ (hessian f x (α • (trialPoint - x))) (α • (trialPoint - x)) =
        α ^ (2 : ℕ) * inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) := by
    simp [inner_smul_left, inner_smul_right, pow_two, mul_assoc]
  have hgrad_flip :
      inner ℝ (∇ f x) (x - trialPoint) = - inner ℝ (∇ f x) (trialPoint - x) := by
    rw [show x - trialPoint = -(trialPoint - x) by abel_nf, inner_neg_right]
  have hpair' :
      inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) =
        - inner ℝ (∇ f x) (trialPoint - x) - (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    linarith [hpair, hgrad_flip]
  -- Then rewrite the Taylor model exactly as in the source proof.
  have hmodel :
      secondOrderTaylorModelAt f x z + ((L : ℝ) / 6) * ‖z - x‖ ^ (3 : ℕ) =
        f x + (α - α ^ (2 : ℕ) / 2) * inner ℝ (∇ f x) (trialPoint - x) -
          α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    rw [secondOrderTaylorModelAt_apply, hzsub, inner_smul_right, hquad_scale, hpair', norm_smul,
      Real.norm_of_nonneg hα.1, mul_pow]
    ring
  rw [hmodel] at hupper
  have hcoef : 0 ≤ α - α ^ (2 : ℕ) / 2 := by
    nlinarith [hα.1, hα.2]
  have hgrad_nonpos : inner ℝ (∇ f x) (trialPoint - x) ≤ 0 := by
    have hgrad_neg :
        inner ℝ (∇ f x) (trialPoint - x) = - inner ℝ (∇ f x) (x - trialPoint) := by
      rw [show trialPoint - x = -(x - trialPoint) by abel_nf, inner_neg_right]
    rw [hgrad_neg]
    exact neg_nonpos.mpr hnonneg
  have hdrop_linear :
      (α - α ^ (2 : ℕ) / 2) * inner ℝ (∇ f x) (trialPoint - x) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos hcoef hgrad_nonpos
  linarith

/-- Helper for Lemma 4.1.3: once every feasible point on the segment from `x` to `trialPoint`
falls back into the current sublevel set, the source first-exit argument should force the whole
segment to stay feasible. -/
lemma segment_feasible_of_sublevel_containment
    (hsublevel : 𝓛[f]((f x)) ⊆ 𝓕)
    (hsegment :
      ∀ {α : ℝ}, α ∈ Set.Icc (0 : ℝ) 1 →
        x + α • (trialPoint - x) ∈ 𝓕 →
        x + α • (trialPoint - x) ∈ 𝓛[f]((f x))) :
    trialPoint ∈ 𝓕 := by
  -- Route correction: the remaining gap is not the cubic-model algebra but the interval
  -- first-exit argument that upgrades pointwise feasible-segment sublevel control to endpoint
  -- feasibility.
  -- TODO: package the `Lemma_4_4_4` clopen-on-`Icc` architecture here. The blocker is proving the
  -- relevant segment preimage is closed from the current dependency closure, since the available
  -- `HessianLipschitzOn` hypothesis only gives continuity of `f` on `𝓕`, not on the whole
  -- segment a priori.
  sorry

/-- Lemma 4.1.3: if the current sublevel set `𝓛(f(x))` is contained in `𝓕`,
`f` has `L`-Lipschitz Hessian on `𝓕`, a point `trialPoint` globally minimizes the chapter cubic
model centered at `x`, and `M > (2 / 3) L`, then `trialPoint` belongs to the sublevel set
`𝓛[f]((f x))` and hence is feasible. Specializing to `trialPoint = T_M(x)` recovers the
textbook statement. -/
theorem cubicTrialPoint_mem_sublevel_and_feasible
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hsublevel : 𝓛[f]((f x)) ⊆ 𝓕)
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M) :
    trialPoint ∈ 𝓛[f]((f x)) ∧ trialPoint ∈ 𝓕 := by
  have hx : x ∈ 𝓕 := by
    apply hsublevel
    rw [mem_levelSet_iff]
  -- Every feasible segment point satisfies the source objective decrease, hence lies in the
  -- current sublevel set.
  have hsegment :
      ∀ {α : ℝ}, α ∈ Set.Icc (0 : ℝ) 1 →
        x + α • (trialPoint - x) ∈ 𝓕 →
        x + α • (trialPoint - x) ∈ 𝓛[f]((f x)) := by
    intro α hα hz
    have hdrop :=
      segment_objective_drop_of_mem_feasible (L := L) (𝓕 := 𝓕) (f := f)
        (M := M) (x := x) (trialPoint := trialPoint) hstep hx hα hz
    have hcoef : 0 ≤ M / 4 - α * (L : ℝ) / 6 := by
      nlinarith [hM, hα.1, hα.2]
    have hpow : 0 ≤ ‖trialPoint - x‖ ^ (3 : ℕ) := by
      positivity
    have hαsq : 0 ≤ α ^ (2 : ℕ) := by
      positivity
    have hterm_nonneg :
        0 ≤ α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
      positivity
    rw [mem_levelSet_iff]
    linarith
  -- The only remaining source step is the first-exit argument along the segment.
  have htrial_feasible :
      trialPoint ∈ 𝓕 :=
    segment_feasible_of_sublevel_containment (f := f) (𝓕 := 𝓕)
      (x := x) (trialPoint := trialPoint) hsublevel hsegment
  have htrial_sublevel : trialPoint ∈ 𝓛[f]((f x)) := by
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hfeas1 : x + (1 : ℝ) • (trialPoint - x) ∈ 𝓕 := by
      simpa using htrial_feasible
    simpa using hsegment h1 hfeas1
  exact ⟨htrial_sublevel, htrial_feasible⟩

/-- Companion bridge: the source-facing theorem yields the ambient sublevel inequality
`f trialPoint ≤ f x`. -/
theorem cubicTrialPoint_mem_sublevel
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hsublevel : 𝓛[f]((f x)) ⊆ 𝓕)
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M) :
    trialPoint ∈ 𝓛[f]((f x)) :=
  (cubicTrialPoint_mem_sublevel_and_feasible hstep hsublevel hM).1

end
