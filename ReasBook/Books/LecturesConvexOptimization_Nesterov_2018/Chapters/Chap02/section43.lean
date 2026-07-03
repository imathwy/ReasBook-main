import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_43 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Definition 2.43 is a recall-only item in the epigraph reformulation domain for constrained
quadratically regularized max-type affine minimization on a real Hilbert space.

Primary domain:
* the auxiliary-variable epigraph presentation of the Chapter 2 regularized minimax subproblem on
  `E × ℝ`

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued ambient objective;
* `SetConstrainedMinimizationProblem.coe_apply`, the canonical coercion view of that owner as its
  objective function;
* `maxTypeAffineApproximation` in `Definition_2_39`, the owner affine max-type model at `xBar`;
* `quadraticallyRegularizedObjective` in `Chap01/FirstOrderTaylorModel.lean`, the owner quadratic
  regularization of an objective on `E`.

Best owner abstraction:
* source-facing/core:
  `SetConstrainedMinimizationProblem (E × ℝ)`, built from the epigraph feasible set and its
  auxiliary-variable objective;
* bridge/view:
  the displayed feasible-set and objective expressions, together with the tight-slack
  specialization back to the Chapter 2 owner
  `quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar`.

Primitive data:
* a feasible set `Q : Set E`;
* a nonempty finite component family `fi : ι → E → ℝ`;
* a base point `xBar : E`;
* a regularization parameter `γ : ℝ`.

Derived API:
* the epigraph problem
  `SetConstrainedMinimizationProblem.mk
    {xt : E × ℝ | xt.1 ∈ Q ∧ maxTypeAffineApproximation fi xBar xt.1 ≤ xt.2}
    (fun xt ↦ xt.2 + (γ / 2) * ‖xt.1 - xBar‖ ^ (2 : ℕ))`;
* the coercion of that problem to its objective on `E × ℝ`;
* the constrained minimizer predicate `IsMinOn problem problem.feasibleSet xtStar`;
* the tight-slack specialization `xt.2 = maxTypeAffineApproximation fi xBar xt.1`.

Source/core/bridge triage:
* source-facing: the epigraph minimization problem on `E × ℝ`;
* core/canonical: `SetConstrainedMinimizationProblem (E × ℝ)`;
* bridge/view: the displayed feasible-set and objective formulas for that owner, and the
  projection back to the regularized max-type model on `E`.

This recall file therefore presents the epigraph reformulation through the Chapter 1 owner object,
not as a parallel collection of standalone feasible-set, objective, and minimizer displays.
Downstream Chapter 2 files should package the epigraph problem with
`SetConstrainedMinimizationProblem.mk ...` and use `problem.feasibleSet`, coercion to the
objective, and `IsMinOn problem problem.feasibleSet ...` as the derived API. The textbook states
the item on `ℝⁿ`, but the owner declarations sampled above already live on the canonical abstract
real-Hilbert-space / finite-index layer, so this recall file keeps that generality instead of
re-specializing it to `EuclideanSpace ℝ (Fin n)` and `Fin m`. -/

recall SetConstrainedMinimizationProblem
recall maxTypeAffineApproximation
recall quadraticallyRegularizedObjective
recall IsMinOn

private abbrev epigraphProblem
    (Q : Set E) (fi : ι → E → ℝ) (γ : ℝ) (xBar : E) :
    SetConstrainedMinimizationProblem (E × ℝ) :=
  .mk
    {xt : E × ℝ | xt.1 ∈ Q ∧ maxTypeAffineApproximation fi xBar xt.1 ≤ xt.2}
    (fun xt ↦ xt.2 + (γ / 2) * ‖xt.1 - xBar‖ ^ (2 : ℕ))

section

variable (Q : Set E) (fi : ι → E → ℝ) (γ : ℝ) (xBar : E) (xtStar : E × ℝ)

set_option linter.hashCommand false in
#check
  (show SetConstrainedMinimizationProblem (E × ℝ) from epigraphProblem Q fi γ xBar)

set_option linter.hashCommand false in
#check
  (show
    (epigraphProblem Q fi γ xBar).feasibleSet =
      {xt : E × ℝ | xt.1 ∈ Q ∧ maxTypeAffineApproximation fi xBar xt.1 ≤ xt.2} from
    rfl)

set_option linter.hashCommand false in
#check
  (show
    (epigraphProblem Q fi γ xBar : E × ℝ → ℝ) =
      (fun xt ↦ xt.2 + (γ / 2) * ‖xt.1 - xBar‖ ^ (2 : ℕ)) from
    rfl)

example (x : E) :
    epigraphProblem Q fi γ xBar (x, maxTypeAffineApproximation fi xBar x) =
      quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar x := by
  rfl

#check
  IsMinOn (epigraphProblem Q fi γ xBar) (epigraphProblem Q fi γ xBar).feasibleSet xtStar

end

/-! ### Theorem_2_43 (from Chap02) -/
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 2.43 lies in the whole-space exact-step domain for a single objective
`f ∈ 𝓢[μ, L]¹¹`, with exact step `gradientStep f xBar γ = xBar - (1 / γ) • ∇ f xBar`.

Mandatory domain-style sampling for this refinement:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`, the whole-space owner predicate for
  `𝓢[μ, L]¹¹`;
* `gradientStep` in `Definition_2_35_1`, the canonical owner of the unconstrained exact step;
* `gradientMapping_objective_lower_bound` in `Theorem_2_36`, the source-facing projected-gradient
  inequality whose `Q = Set.univ` specialization yields part `(1)`;
* `gradientMapping_univ_eq_gradient_step` and `reducedGradient_univ_eq_gradient` in
  `Remark_2_35_1`, the canonical bridge from the projected-gradient owner layer back to the
  whole-space `gradientStep` / `∇` surface.

Best owner abstraction:
* source-facing: Theorem 2.43 as a whole-space exact-step result for `x_f(xBar; γ)` and
  `g_f(xBar; γ)`;
* core/canonical: `IsStrongConvexSmoothObjective μ L f`, `gradientStep f xBar γ`, and `∇ f xBar`;
* bridge/view: the `Q = Set.univ` specialization of `gradientMapping_objective_lower_bound`,
  simplified by `gradientMapping_univ_eq_gradient_step` and `reducedGradient_univ_eq_gradient`.

Primitive data:
* the objective hypothesis `hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹`;
* the base point `xBar`, comparison point `x`, and positive inverse-stepsize `γ`;
* for part `(3)`, a minimizer `xStar` of `f` on `Set.univ`.

Derived API:
* the whole-space exact-step lower bound in part `(1)`;
* the value decrease in part `(2)`, obtained by specializing part `(1)` to `x = xBar`;
* the minimizer inequality in part `(3)`, obtained by combining part `(1)` at `x = xStar` with
  the minimizing property of `xStar`.

This file therefore keeps Theorem 2.43 on the chapter's whole-space owner surface and does not
repackage it as a constrained `Q`-problem corollary. -/

section

variable {μ : ℝ} {γ : NNRealˣ} {L : NNReal} {f : E → ℝ}

/-- Theorem 2.43 (1): for a whole-space strongly convex smooth objective, the exact step
`x_f(xBar; γ) = xBar - (1 / γ) • ∇ f xBar` satisfies the standard lower bound, and in the
whole-space setting `g_f(xBar; γ) = ∇ f xBar`. -/
theorem exactStep_objective_lower_bound
    (xBar x : E)
    (hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹)
    (hγ_ge_L : (L : ℝ) ≤ (γ : ℝ)) :
    f x ≥
      f (gradientStep f xBar γ) +
        inner ℝ (∇ f xBar) (x - xBar) +
        (1 / (2 * (γ : ℝ))) * ‖∇ f xBar‖ ^ (2 : ℕ) +
        (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  -- Specialize the projected-gradient lower bound to the whole-space domain `Set.univ`.
  let Q : Set E := Set.univ
  let hQ_nonempty : Q.Nonempty := Set.univ_nonempty
  let hQ_closed : IsClosed Q := isClosed_univ
  let hQ_convex : Convex ℝ Q := convex_univ
  have hbound :=
    gradientMapping_objective_lower_bound
      Q hQ_nonempty hQ_closed hQ_convex xBar hf hγ_ge_L x (by simp [Q])
  -- The whole-space bridge identifies the projected-gradient objects with `gradientStep` and `∇ f`.
  dsimp [Q, hQ_nonempty, hQ_closed, hQ_convex] at hbound
  simpa [gradientMapping_univ_eq_gradient_step, reducedGradient_univ_eq_gradient] using hbound

/-- Theorem 2.43 (2): the whole-space exact step decreases the objective by at least
`(2γ)⁻¹ ‖∇ f xBar‖²`. -/
theorem exactStep_value_le_sub_reducedGradient_sq
    (xBar : E)
    (hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹)
    (hγ_ge_L : (L : ℝ) ≤ (γ : ℝ)) :
    f (gradientStep f xBar γ) ≤
      f xBar - (1 / (2 * (γ : ℝ))) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
  -- Evaluate part (1) at the base point `x = xBar`, where the inner-product term vanishes.
  have hbound :
      f xBar ≥
        f (gradientStep f xBar γ) +
          (1 / (2 * (γ : ℝ))) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
    simpa using exactStep_objective_lower_bound xBar xBar hf hγ_ge_L
  -- Rearrange the scalar inequality into the textbook descent estimate.
  nlinarith

/-- Theorem 2.43 (3): if `xStar` minimizes `f` on the whole space, then the whole-space exact
gradient satisfies
`⟪∇ f xBar, xBar - xStar⟫ ≥ (2γ)⁻¹ ‖∇ f xBar‖² + (μ / 2) ‖xStar - xBar‖²`. -/
theorem reducedGradient_inner_sub_minimizer_ge
    (xBar xStar : E)
    (hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹)
    (hγ_ge_L : (L : ℝ) ≤ (γ : ℝ))
    (hxStar : IsMinOn f Set.univ xStar) :
    inner ℝ (∇ f xBar) (xBar - xStar) ≥
      (1 / (2 * (γ : ℝ))) * ‖∇ f xBar‖ ^ (2 : ℕ) +
        (μ / 2) * ‖xStar - xBar‖ ^ (2 : ℕ) := by
  -- Apply part (1) at the minimizer `xStar` to compare `f xStar` with the exact-step value.
  have hbound := exactStep_objective_lower_bound xBar xStar hf hγ_ge_L
  -- A whole-space minimizer dominates the exact-step point by `isMinOn_univ_iff`.
  have hstep : f (gradientStep f xBar γ) ≥ f xStar := by
    simpa using (isMinOn_univ_iff.mp hxStar) (gradientStep f xBar γ)
  -- Rewrite the inner product with `xStar - xBar` into the negated textbook orientation.
  have hinner :
      inner ℝ (∇ f xBar) (xStar - xBar) =
        -inner ℝ (∇ f xBar) (xBar - xStar) := by
    calc
      inner ℝ (∇ f xBar) (xStar - xBar) =
          inner ℝ (∇ f xBar) xStar - inner ℝ (∇ f xBar) xBar := by
            rw [inner_sub_right]
      _ = -(inner ℝ (∇ f xBar) xBar - inner ℝ (∇ f xBar) xStar) := by ring
      _ = -inner ℝ (∇ f xBar) (xBar - xStar) := by
            rw [inner_sub_right]
  -- Combine the lower bound, the minimizing property, and the sign rewrite.
  nlinarith [hbound, hstep, hinner]

end

end
