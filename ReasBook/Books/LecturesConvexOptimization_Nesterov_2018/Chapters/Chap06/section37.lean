import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_37 (from Chap06) -/
noncomputable section

open scoped Gradient StrongConvex WithTopConvexAnalysis

universe u

/- Definition 6.37 lies in the whole-space strong-convexity / subdifferential domain.

Sampled owner-style declarations:
- `S0On` with the notation `𝒮^0_σ(Q)` in `Chap03/Definition_3_47`, the chapter's source-facing
  owner for positive-parameter strong convexity;
- mathlib `StrongConvexOn`, the canonical whole-space strong-convexity owner;
- `subdifferential` with the notation `∂ f(x)` in `Chap03/Definition_3_1_5`, the chapter owner
  for subgradients of `WithTop ℝ`-valued functions;
- `strongConvexOnWith_normSeminorm_iff` and
  `StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt` in `Chap02/Definition_2_14`, the
  ambient-norm bridge from the core owner to the textbook quadratic lower-tangent inequality.

Best owner abstraction:
- core/canonical: `f ∈ 𝒮^0_σ(Set.univ)`, equivalently `0 < σ ∧ StrongConvexOn Set.univ σ f`;
- bridge/view: the real-valued subgradient membership formula and the differentiable gradient
  specialization.

Primitive data:
- the modulus `σ : ℝ`;
- the real-valued objective `f : E → ℝ`.

Derived API:
- positivity of `σ` and the core owner `StrongConvexOn Set.univ σ f`, via `mem_S0On_iff`;
- the source-facing subgradient characterization below, phrased through the existing owner `∂`;
- the differentiable specialization with `∇ f x`.

Source/core/bridge triage:
- core/canonical main entry: `f ∈ 𝒮^0_σ(Set.univ)`;
- bridge/view: `mem_subdifferential_coe_iff`,
  `mem_S0On_univ_iff_exists_subgradient_lower_tangent_quadratic`, and
  `mem_S0On_univ_iff_gradient_inequality_of_differentiable`.

Definition 6.37 introduces no new owner beyond the earlier chapter surface `𝒮^0_σ(Set.univ)`.
This file therefore recalls that owner directly and keeps the textbook subgradient and gradient
formulas only as bridge theorems, instead of rebuilding parallel local definitions such as
`StrongConvexWithParameter`, `IsSubgradientAt`, or a second real-valued `subdifferential`.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable (σ : ℝ) (f : E → ℝ)

/- Definition 6.37, owner form: positive whole-space strong convexity. -/
#check (f ∈ 𝒮^0_σ(Set.univ))

end

/-- For a real-valued function, membership in the Chapter 3 subdifferential owner is exactly the
usual affine lower-support inequality. -/
theorem mem_subdifferential_coe_iff {f : E → ℝ} {x g : E} :
    g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x) ↔
      ∀ y : E, f y ≥ f x + inner ℝ g (y - x) := by
  constructor
  · intro hg y
    have hy : y ∈ dom (fun z ↦ (f z : WithTop ℝ)) := by
      simp [withTopEffectiveDomain]
    have hineq :
        (((f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      simpa [mem_subdifferential_iff] using (mem_subdifferential_iff.mp hg).2 hy
    exact_mod_cast hineq
  · intro hg
    refine mem_subdifferential_iff.mpr ?_
    refine ⟨by simp [withTopEffectiveDomain], ?_⟩
    intro y hy
    have hineq :
        (((f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      exact_mod_cast hg y
    simpa using hineq

/-- Definition 6.37, source-facing bridge: positive whole-space strong convexity is equivalent to
positivity of `σ` together with the existence, at each base point, of a subgradient supporting the
function with the quadratic term `(σ / 2) * ‖y - x‖²`. -/
theorem mem_S0On_univ_iff_exists_subgradient_lower_tangent_quadratic
    {σ : ℝ} {f : E → ℝ} :
    f ∈ 𝒮^0_σ(Set.univ) ↔
      0 < σ ∧
        ∀ x y : E,
          ∃ g ∈ ∂ (fun z ↦ (f z : WithTop ℝ))(x),
            f y ≥ f x + inner ℝ g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  sorry

/-- For a differentiable function, the source-facing Definition 6.37 bridge reduces to the
gradient lower-support inequality with the same quadratic term. -/
theorem mem_S0On_univ_iff_gradient_inequality_of_differentiable
    [CompleteSpace E] {σ : ℝ} {f : E → ℝ} (hf : Differentiable ℝ f) :
    f ∈ 𝒮^0_σ(Set.univ) ↔
      0 < σ ∧
        ∀ x y : E,
          f y ≥ f x + inner ℝ (∇ f x) (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  sorry

end

/-! ### Proposition_6_37 (from Chap06) -/
universe u

noncomputable section

section

variable {X : Type u}

/-
Proposition 6.37 lies in the constrained minimization / approximate-solution domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  owner for constrained optimal values;
- `SetConstrainedMinimizationProblem.IsApproximateMinimizer` and
  `SetConstrainedMinimizationProblem.isApproximateMinimizer_iff` in
  `Chap01/Definition_1_3_7`, the canonical `ε`-suboptimality owner on a constrained problem;
- `PrimalConvexMinimizationProblem` in `Chap06/Definition_6_4`, which reuses the same owner
  abstraction and derives its optimization API through it.

Best owner abstraction:
- source-facing: Proposition 6.37's smoothing comparison theorem;
- core/canonical: `SetConstrainedMinimizationProblem.mk Q φ` together with its derived
  `optimalValue` and `IsApproximateMinimizer` API;
- bridge/view: the smoothing comparison, with the lower bound used globally on `Q` and the upper
  bound used only at the feasible comparison point `yBar`.

Primitive data:
- the feasible set `Q`;
- the original and smoothed objectives `φ` and `φμ`.
- the global lower smoothing estimate on `Q`;
- the upper smoothing estimate at `yBar`.

Derived API:
- `(SetConstrainedMinimizationProblem.mk Q φ).optimalValue`;
- `(SetConstrainedMinimizationProblem.mk Q φ).IsApproximateMinimizer ε yBar`;
- the corresponding smoothed-problem instances built from `φμ`.

This refinement removes the duplicate local owners `optimalValueOn` and
`IsEpsilonSolutionOn` and states the proposition directly with the Chapter 1 owner API.
-/

-- Proof sketch: use the upper smoothing bound at `yBar` to estimate `φ yBar` by
-- `φμ yBar + μ log n`, use the lower smoothing bound on `Q` to deduce
-- `((SetConstrainedMinimizationProblem.mk Q φμ).optimalValue :
--   EReal) ≤ (SetConstrainedMinimizationProblem.mk Q φ).optimalValue`,
-- and combine these with the assumed `ε / 2` smoothed approximate-minimizer property and the
-- budget bound `μ log n ≤ ε / 2`.
/-- Proposition 6.37: if `φμ` is a smoothing of `φ` on `Q` satisfying
`φμ(y) ≤ φ(y)` for every feasible `y` and `φ(yBar) ≤ φμ(yBar) + μ log n` at the feasible point
`yBar`, then any `ε / 2`-approximate minimizer of the smoothed problem is an `ε`-approximate
minimizer of the original problem whenever `μ log n ≤ ε / 2`. -/
theorem isApproximateMinimizer_of_smoothedObjective_suboptimality
    {Q : Set X} {φ φμ : X → ℝ} {n : ℕ} {μ ε : ℝ} {yBar : X}
    (happrox_lower : ∀ y ∈ Q, φμ y ≤ φ y)
    (happrox_upper : φ yBar ≤ φμ yBar + μ * Real.log (n : ℝ))
    (hsmoothed :
      (SetConstrainedMinimizationProblem.mk Q φμ).IsApproximateMinimizer (ε / 2) yBar)
    (hμ_budget : μ * Real.log (n : ℝ) ≤ ε / 2) :
    (SetConstrainedMinimizationProblem.mk Q φ).IsApproximateMinimizer ε yBar := sorry

-- Proof sketch: under `log n ≠ 0`, the special choice `μ = ε / (2 log n)` gives
-- `μ log n = ε / 2`, so the previous theorem applies directly.
/-- Choosing `μ = ε / (2 log n)` with `log n ≠ 0` forces the smoothing budget to equal `ε / 2`,
so if the lower smoothing estimate holds on `Q` and the upper estimate is available at `yBar`
with that specialized parameter, then an `ε / 2`-approximate minimizer of the smoothed problem is
already an `ε`-approximate minimizer of the original problem. -/
theorem isApproximateMinimizer_of_smoothedObjective_suboptimality_with_canonical_mu
    {Q : Set X} {φ φμ : X → ℝ} {n : ℕ} {ε : ℝ} {yBar : X}
    (hlogn : Real.log (n : ℝ) ≠ 0)
    (happrox_lower : ∀ y ∈ Q, φμ y ≤ φ y)
    (happrox_upper :
      φ yBar ≤ φμ yBar + (ε / (2 * Real.log (n : ℝ))) * Real.log (n : ℝ))
    (hsmoothed :
      (SetConstrainedMinimizationProblem.mk Q φμ).IsApproximateMinimizer (ε / 2) yBar) :
    (SetConstrainedMinimizationProblem.mk Q φ).IsApproximateMinimizer ε yBar := sorry

end
