import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_48 (from Chap03) -/
noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

open scoped StronglyConvexProblemClass

/-
Definition 3.48 is a source-facing recall in the chapter's first-order black-box complexity
domain for strongly convex unconstrained objectives.

Primary domain:
* the strongly convex local-ball problem class `𝒫_s(x₀, μ, M)`

Sampled owner-style declarations:
* `𝒫_s(x₀, μ, M)` / `IsInStronglyConvexProblemClass` in `Theorem_3_47`
* `𝒮^0_μ(Q)` / `mem_S0On_iff` in `Definition_3_47`
* `StrongConvexOnClass`
* `IsMinOn`
* `LipschitzOnWith`
* `IsInLipschitzConvexProblemClass` in `Theorem_3_2_1`

Best owner abstraction:
* source-facing: `𝒫_s(x0, μ, M) f xStar`
* core/canonical:
  `f ∈ 𝒮^0_((μ : ℝ))(Metric.closedBall xStar ‖x0 - xStar‖)`,
  `IsMinOn f Set.univ xStar`, and
  `LipschitzOnWith M f (Metric.closedBall xStar ‖x0 - xStar‖)`
* bridge/view: the stronger whole-space class
  `IsInLipschitzConvexProblemClass x0 ‖x0 - xStar‖₊ M f xStar`, available separately when an
  additional global convexity hypothesis is supplied

Primitive data:
* the objective `f : V → ℝ`
* the chosen minimizer `xStar : V`

Derived API:
* the positivity, strong-convexity, minimizer, and Lipschitz accessors already owned by
  `𝒫_s(x0, μ, M)`
* the stronger whole-space bridge data, kept outside this recall file

Source/core/bridge triage:
* source-facing: `𝒫_s(x0, μ, M) f xStar`
* core/canonical: the component owners `𝒮^0_((μ : ℝ))(Metric.closedBall xStar ‖x0 - xStar‖)`,
  `IsMinOn`, and `LipschitzOnWith`
* bridge/view: the stronger whole-space class `IsInLipschitzConvexProblemClass`

This file therefore recalls the earlier chapter owner through its scoped source notation rather
than recentering the longer raw backing declaration name.
-/

variable (x0 : V) (μ M : NNReal)

/- Definition 3.48 recalls the source-facing strongly convex problem class `𝒫_s(x₀, μ, M)`. -/
#check (𝒫_s(x0, μ, M) : (V → ℝ) → V → Prop)

end

/-! ### Proposition_3_48 (from Chap03) -/
noncomputable section

universe u

variable {X : Type u} [NormedAddCommGroup X]

local notation "Z" => ℝ × X

open scoped ConstrainedArgmin

/- Proposition 3.48 lies in the chapter's constrained minimization / explicit argmin domain.

Relevant owner-style declarations sampled before refinement:
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the chapter
  owner for minimizers of an objective over a feasible set;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the later package owner built
  from a feasible set and an objective;
- `IsMinOn` and `isMinOn_iff` in mathlib, the canonical pointwise minimizer predicate on a set.

Best owner abstraction:
- source-facing: the explicit Kelley complete-data objective `f(y, x) = max {|y|, ‖x‖²}` and
  feasible set `Q = {(y, x) | y² + ‖x‖² ≤ 1}`;
- core/canonical: the minimizer owner `argmin[Q] f`, with `mem_constrainedArgmin_iff` as the
  atomic membership view;
- bridge/view: the later problem package
  `SetConstrainedMinimizationProblem.mk kelleyCompleteFeasibleSet kelleyCompleteObjective`.

Primitive data:
- the explicit objective `kelleyCompleteObjective`;
- the explicit feasible set `kelleyCompleteFeasibleSet`.

Derived API:
- feasibility and objective-value simplification at the origin;
- the argmin set equality and its atomic membership corollary.

This proposition is therefore kept source-facing on the explicit `f` and `Q`, while exposing its
optimality result through the canonical constrained-argmin owner rather than through any extra
wrapper around the same minimizer set.
-/

/-- The objective `f(y, x) = max {|y|, ‖x‖²}` from the complete-data example for Kelley's
method. -/
def kelleyCompleteObjective (z : Z) : ℝ :=
  max |z.1| (‖z.2‖ ^ (2 : ℕ))

/-- The feasible set `Q = {(y, x) | y² + ‖x‖² ≤ 1}` for the complete-data example. -/
def kelleyCompleteFeasibleSet : Set Z :=
  {z | z.1 ^ (2 : ℕ) + ‖z.2‖ ^ (2 : ℕ) ≤ 1}

/-- Membership in `kelleyCompleteFeasibleSet` is exactly the displayed quadratic constraint
defining the unit ball `Q`. -/
@[simp] theorem mem_kelleyCompleteFeasibleSet_iff
    {z : Z} :
    z ∈ kelleyCompleteFeasibleSet ↔
      z.1 ^ (2 : ℕ) + ‖z.2‖ ^ (2 : ℕ) ≤ 1 :=
  Iff.rfl

/-- The Kelley complete-data objective is nonnegative at every point. -/
theorem kelleyCompleteObjective_nonneg (z : Z) :
    0 ≤ kelleyCompleteObjective z := by
  unfold kelleyCompleteObjective
  positivity

/-- The origin is feasible for the Kelley complete-data unit ball constraint. -/
@[simp] theorem zero_mem_kelleyCompleteFeasibleSet :
    (0 : Z) ∈ kelleyCompleteFeasibleSet := by
  simp [kelleyCompleteFeasibleSet]

/-- Evaluating the complete-data Kelley objective at the origin gives the optimal value candidate
`0`. -/
-- Proof sketch: unfold `kelleyCompleteObjective` and simplify `|0|`, `‖0‖`, and the maximum
-- of two zero terms.
@[simp] theorem kelleyCompleteObjective_zero :
    kelleyCompleteObjective (0 : Z) = 0 := by
  simp [kelleyCompleteObjective]

/-- Proposition 3.48: for the problem
`min {f(y, x) | (y, x) ∈ Q}` with
`f(y, x) = max {|y|, ‖x‖²}` and `Q = {(y, x) | y² + ‖x‖² ≤ 1}`,
the unique optimal solution is the origin, i.e. the minimizer set is `{(0, 0)}`. Specializing
`X = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ × ℝⁿ` instance. -/
-- Proof sketch: first show every feasible point has nonnegative objective value, while the origin
-- is feasible and attains value `0`. Hence the origin is a minimizer. If another feasible point
-- were also minimizing, its objective value would be `0`, forcing both `|y| = 0` and `‖x‖² = 0`,
-- so `y = 0` and `x = 0`.
theorem kelleyCompleteArgmin_eq_singleton_origin :
    (argmin[kelleyCompleteFeasibleSet] kelleyCompleteObjective : Set Z) =
      ({(0 : Z)} : Set Z) := by
  ext z
  rw [mem_constrainedArgmin_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz_feasible, hz_min⟩
    rw [isMinOn_iff] at hz_min
    have hz_nonneg : 0 ≤ kelleyCompleteObjective z :=
      kelleyCompleteObjective_nonneg z
    have hzero_feasible : (0 : Z) ∈ kelleyCompleteFeasibleSet := by simp
    have hz_le_zero : kelleyCompleteObjective z ≤ 0 := by
      simpa [kelleyCompleteObjective_zero] using hz_min (0 : Z) hzero_feasible
    have hy_abs_le_zero : |z.1| ≤ 0 := by
      exact (le_max_left |z.1| (‖z.2‖ ^ (2 : ℕ))).trans hz_le_zero
    have hy_zero : z.1 = 0 := by
      exact abs_eq_zero.mp (le_antisymm hy_abs_le_zero (abs_nonneg _))
    have hx_sq_le_zero : ‖z.2‖ ^ (2 : ℕ) ≤ 0 := by
      exact (le_max_right |z.1| (‖z.2‖ ^ (2 : ℕ))).trans hz_le_zero
    have hx_sq_eq_zero : ‖z.2‖ ^ (2 : ℕ) = 0 := by
      exact le_antisymm hx_sq_le_zero <| by positivity
    have hx_zero : z.2 = 0 := by
      apply norm_eq_zero.mp
      exact sq_eq_zero_iff.mp <| by simpa using hx_sq_eq_zero
    exact Prod.ext hy_zero hx_zero
  · intro hz
    subst hz
    refine ⟨?_, ?_⟩
    · simp
    · rw [isMinOn_iff]
      intro w hw
      simpa using kelleyCompleteObjective_nonneg w

/-- Membership in the Kelley complete-data argmin set is exactly the assertion that the point is
the origin. -/
@[simp] theorem mem_kelleyCompleteArgmin_iff
    {z : Z} :
    z ∈ (argmin[kelleyCompleteFeasibleSet] kelleyCompleteObjective : Set Z) ↔ z = 0 := by
  simp [kelleyCompleteArgmin_eq_singleton_origin]

/-! ### Theorem_3_48 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped WithTopConvexAnalysis StronglyConvexProblemClass

/- Theorem 3.48 lies in the chapter's projected subgradient / strongly convex complexity domain on
real inner-product spaces.

Mandatory domain-style sampling before refinement:
- `𝒫_s(x₀, μ, M)` and its owner projections
  `IsInStronglyConvexProblemClass.strongConvexOn_closedBall`,
  `IsInStronglyConvexProblemClass.isMinOn`, and
  `IsInStronglyConvexProblemClass.mu_pos` in `Theorem_3_47`;
- `bestFunctionValueUpTo` in `Definition_3_55`, the chapter owner for sampled-prefix minima;
- `∂[Q] f(x)` in `Theorem_3_44`, the chapter owner surface for real-valued constrained
  subgradients;
- `bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn`
  in `Theorem_3_2_6`, the explicit strong-convexity bridge theorem whose proof interface already
  uses the pointwise projection owner `IsProjectionPointOn Q x (π x)` and the sampled-value owner
  `bestFunctionValueUpTo`.

Best owner abstraction:
- source-facing: Theorem 3.48's logarithmic-budget guarantee for projected subgradient descent on
  the strongly convex class `𝒫_s(x₀, μ, M)`;
- core/canonical: the controlling ball `Q = B₂(x*, ‖x₀ - x*‖)`, the pointwise projection owner
  `IsProjectionPointOn Q x (π x)`, the constrained-subgradient owner `∂[Q] f(x)`, and the
  sampled-value owner `bestFunctionValueUpTo`;
- bridge/view: the explicit strong-convexity bridge theorem
  `bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn`
  from `Theorem_3_2_6`.

Primitive data:
- the objective `f : E → ℝ`, the minimizer `xStar`, and class membership `𝒫_s(x₀, μ, M) f xStar`;
- a chosen projection map on the controlling ball, the iterate sequence `xSeq`, and chosen
  constrained subgradients `g`.

Derived API:
- the strong-convexity and minimizer data on the controlling ball `Q`;
- the sampled-value conclusion on `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N`.

Source/core/bridge triage:
- source-facing: Theorem 3.48 stated on `𝒫_s(x₀, μ, M)`, `bestFunctionValueUpTo`, and
  `∂[Q] f(x)`;
- core/canonical: `IsProjectionPointOn`, `∂[Q] f(x)`, and `bestFunctionValueUpTo`;
- bridge/view: specialization from the `𝒫_s(x₀, μ, M)` owner surface to the explicit
  strong-convexity/minimizer data consumed by `Theorem_3_2_6`.

The previous version collapsed this later source-facing theorem to a direct recall of the earlier
legacy theorem. This file now keeps the public theorem surface on the chapter's current owner
objects and uses the older theorem only as an internal bridge. -/

section StronglyConvexProjectedSubgradient

variable {x0 xStar : E} {μ M : NNReal} {f : E → ℝ}

local notation "Q" => (Metric.closedBall xStar ‖x0 - xStar‖ : Set E)

open IsInStronglyConvexProblemClass
/-- Theorem 3.48: if `f` belongs to the strongly convex class `𝒫_s(x₀, μ, M)` with minimizer
`x*`, `π_Q` is a projection map on the controlling ball `Q = B₂(x*, ‖x₀ - x*‖)`, every selected
subgradient `g_k` lies in `∂[Q] f(x_k)`, satisfies `‖g_k‖ ≤ M`, and the projected subgradient
iteration
`x_{k+1} = π_Q (x_k - (2 ε / ‖g_k‖²) • g_k)`
is run for a budget
`N ≥ (M² / (μ ε)) log (M ‖x₀ - x*‖ / ε)`,
then the sampled best value `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N` is at most
`f x* + ε`. -/
theorem bestFunctionValueUpTo_le_optimalValue_add_eps_of_log_budget_projected_subgradient_method
    (hf : 𝒫_s(x0, μ, M) f xStar)
    {ε : ℝ} (hε : 0 < ε)
    (projQ : E → E)
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x))
    (xSeq g : ℕ → E) (hxSeq_zero : xSeq 0 = x0)
    (hsubgrad : ∀ k : ℕ, g k ∈ ∂[Q] f((xSeq k)))
    (hsubgrad_norm : ∀ k : ℕ, ‖g k‖ ≤ M)
    (hxSeq_succ :
      ∀ k : ℕ,
        xSeq (k + 1) =
          projQ (xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k))
    {N : ℕ}
    (hN :
      (N : ℝ) ≥
        ((M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε) *
          Real.log ((M : ℝ) * ‖x0 - xStar‖ / ε)) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N ≤ f xStar + ε := by
  -- Convert the stored `NNReal` positivity into the real-valued hypothesis expected by the
  -- strong-convexity bridge theorem.
  have hμ : 0 < (μ : ℝ) := by
    exact_mod_cast mu_pos hf
  -- Restrict the global minimizer recorded by the problem class to the controlling closed ball.
  have hQ_subset : Q ⊆ (Set.univ : Set E) := by
    intro y hy
    simp
  have hxStarQ : IsMinOn f Q xStar :=
    (isMinOn hf).on_subset hQ_subset
  -- Rewrite the budget assumption into the canonical `xSeq 0` form used by the imported theorem.
  have hN' :
      (N : ℝ) ≥
        ((M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε) *
          Real.log ((M : ℝ) * ‖xSeq 0 - xStar‖ / ε) := by
    simpa [hxSeq_zero] using hN
  -- Apply the earlier bridge theorem on the controlling ball instead of re-running the
  -- contraction argument in this file.
  exact
    bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn
      projQ hproj hμ hε (strongConvexOn_closedBall hf) hxStarQ
      xSeq g hsubgrad hsubgrad_norm hxSeq_succ hN'

end StronglyConvexProjectedSubgradient

end
