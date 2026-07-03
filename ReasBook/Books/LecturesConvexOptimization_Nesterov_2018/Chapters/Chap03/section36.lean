import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_36 (from Chap03) -/
noncomputable section

universe u

open scoped ConstrainedArgmin

/- Definition 3.36 lies in the constrained convex minimization domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the Chapter 1 owner for the
  feasible-set / objective data of a minimization problem;
* `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  owner of optimal-solution membership on a feasible set;
* `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Chap03/Theorem_3_44`, the
  real-valued feasible-subgradient surface already owned upstream in the chapter;
* `LinearEqualityConstrainedConvexProblem` in `Chap03/Definition_3_27`, the nearby chapter owner
  pattern where the ambient optimization data are inherited from an upstream owner and only the
  genuinely extra convex-program hypotheses remain primitive.

Best owner abstraction:
* source-facing: `ConvexMinimizationProblem X`;
* core/canonical: `SetConstrainedMinimizationProblem X`, `argmin[Q] f`, and the chapter's
  constrained-subdifferential owners;
* bridge/view: `objective_convexOn`.

Primitive data:
* the feasible set `Q` and the real-valued objective `f`, already owned by
  `SetConstrainedMinimizationProblem X`;
* the nonemptiness, closedness, and convexity of `Q`;
* the whole-space convexity witness `ConvexOn ℝ Set.univ f`.

Derived API:
* the coercion back to the inherited Chapter 1 owner;
* the feasible-set convexity owner `problem.objective_convexOn`.

This file therefore keeps the source-facing problem class, but its optimality and subgradient
surfaces are the upstream owners `x ∈ argmin[problem.feasibleSet] problem` and, in downstream
real-valued inner-product settings, `g ∈ ∂[problem.feasibleSet] problem(x)` rather than parallel
local aliases. -/

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Definition 3.36: a convex minimization problem is a set-constrained minimization problem
`min_{x ∈ Q} f(x)` whose feasible set `Q` is nonempty, closed, and convex, and whose objective
`f` is convex on the whole ambient space. -/
structure ConvexMinimizationProblem (X : Type u) [TopologicalSpace X] [AddCommMonoid X]
    [Module ℝ X] extends SetConstrainedMinimizationProblem X where
  /-- The feasible set `Q` is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The objective `f` is convex on the whole ambient space. -/
  objective_convex : ConvexOn ℝ Set.univ objective

namespace ConvexMinimizationProblem

/-- A convex minimization problem can be used as its objective function. -/
instance : CoeFun (ConvexMinimizationProblem X) (fun _ ↦ X → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a convex minimization problem returns its objective value. -/
@[simp] theorem coe_apply (problem : ConvexMinimizationProblem X) (x : X) :
    problem x = problem.objective x :=
  rfl

/-- Restricting the whole-space convex objective to the feasible set yields the canonical
`ConvexOn` owner on that feasible set. -/
theorem objective_convexOn (problem : ConvexMinimizationProblem X) :
    ConvexOn ℝ problem.feasibleSet problem := by
  refine ⟨problem.feasibleSet_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa using problem.objective_convex.2 (by simp) (by simp) ha hb hab

end ConvexMinimizationProblem

end

/-! ### Lemma_3_36 (from Chap03) -/
noncomputable section

universe u v w

open scoped ConstrainedArgmin ConstrainedThreshold

section

variable {Index : Type u} {Param : Type v} {Decision : Type w}
variable (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ)
variable (k : Index) (X : Param)

/-
Lemma 3.36 lies in the chapter's constrained-threshold / feasible-value domain.

Sampled owner-style declarations:
- `constrainedThreshold` in `Lemma_3_3_4`, the chapter owner for the threshold `t_k^*(X)` as the
  `EReal` infimum of the feasible objective values on the slice
  `Q ∩ {x | checkFn k X x ≤ 0}`;
- `constrainedThreshold_eq_minimum_of_feasible_minimizer` in `Lemma_3_3_4`, the source-facing
  attained-minimum form on the feasible slice `Q ∩ {x | checkFn k X x ≤ 0}`;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Chap01/Definition_1_3_7`,
  the Chapter 1 owner bridge from the feasible slice to the corresponding `EReal` `sInf`;
- `IsLeast.csInf_eq` in mathlib, the canonical bridge from an attained least value of a set to the
  corresponding `sInf` identity.

Best owner abstraction:
- `t*[Q; hatFn; checkFn](k, X)`, with owner feasible-value image
  `(fun x ↦ (hatFn k X x : EReal)) '' (Q ∩ {x | checkFn k X x ≤ 0})`.

Primitive data:
- the ambient feasible set `Q`;
- the objective map `hatFn`;
- the constraint map `checkFn`;
- the index `k` and parameter `X`.

Derived API:
- the owner threshold `t*[Q; hatFn; checkFn](k, X)`;
- the real feasible objective-value set `(hatFn k X) '' (Q ∩ {x | checkFn k X x ≤ 0})`;
- the direct `sInf` identification from `IsLeast.csInf_eq`, used only internally after coercing
  that real value set into `EReal`.

Source/core/bridge triage:
- source-facing: Lemma 3.36's statement that the threshold equals the least feasible objective
  value when the real feasible objective-value set has a least element;
- core/canonical: `constrainedThreshold` from `Lemma_3_3_4`;
- bridge/view: `IsLeast.csInf_eq` on the internally coerced owner feasible-value image.

This file therefore keeps no parallel local copies of the feasible set or threshold. It only adds
the source-facing real-minimum consequence, proved by extracting a feasible minimizer and then
reusing the owner attained-minimum theorem from `Lemma_3_3_4`.
-/

/-- Lemma 3.36: if the feasible objective values attain a least element `m`, then `t_k^*(X)`
equals that minimum value. -/
-- Proof sketch: extract a feasible point whose objective value is `m`, show that point belongs to
-- the constrained argmin of the feasible slice, and then apply the owner attained-minimum bridge
-- `constrainedThreshold_eq_minimum_of_feasible_minimizer`.
lemma constrainedThreshold_eq_minimum_of_isLeast
    {m : ℝ}
    (hmin : IsLeast ((hatFn k X) '' (Q ∩ {x | checkFn k X x ≤ 0})) m) :
    t*[Q; hatFn; checkFn](k, X) = (m : EReal) := by
  rcases hmin.1 with ⟨xStar, hxStar, rfl⟩
  have hxStar_argmin : xStar ∈ argmin[Q ∩ {x | checkFn k X x ≤ 0}] (hatFn k X) := by
    rw [mem_constrainedArgmin_iff]
    refine ⟨hxStar, ?_⟩
    rw [isMinOn_iff]
    intro y hy
    exact hmin.2 ⟨y, hy, rfl⟩
  simpa using
    constrainedThreshold_eq_minimum_of_feasible_minimizer
      Q hatFn checkFn k X hxStar_argmin

end

/-! ### Proposition_3_36 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped DeltaN WithTopConvexAnalysis

/- Proposition 3.36 lies in the chapter's unconstrained subgradient-method / finite-prefix
stepsize-bound domain.

Sampled owner-style declarations:
- `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Theorem_3_44`, the chapter
  owner surface for real-valued whole-space subgradients, written here as `∂[Set.univ] f(x)`;
- `bestFunctionValueUpTo` in `Definition_3_55`, the chapter owner for best-so-far sampled values;
- `deltaN` and `deltaN_apply` in `Definition_3_41`, the chapter owner and evaluation bridge for
  the finite-horizon stepsize scalar `Δ_N(h₀, ..., h_N)`;
- `bestFunctionValueGapUpTo_le_lipschitz_mul_stepsize_ratio` in `Theorem_3_2_2`, the chapter's
  owner sampled-gap estimate written on the `bestFunctionValueUpTo` / `deltaN` surface.

Best owner abstraction:
- source-facing: the constant-stepsize sampled-gap bound for the unconstrained subgradient method;
- core/canonical: `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N` together with the finite-prefix
  scalar owner `deltaN N R`;
- bridge/view: the constant stepsize prefix `fun _ ↦ ε / M`.

Primitive data:
- the objective `f`;
- the iterate sequence `xSeq`;
- the chosen whole-space subgradient selection `g`;
- the minimizing point `xStar`;
- the initial radius bound `‖xSeq 0 - xStar‖ ≤ R`;
- the constant stepsize `ε / M`.

Derived API:
- the best sampled value `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N`;
- the finite-prefix constant-stepsize scalar
  `Δ[N; R] ((EuclideanSpace.equiv (Fin (N + 1)) ℝ).symm fun _ ↦ ε / M)`;
- the `ε`-accuracy threshold corollary.

The previous file still hard-coded the scalar quotient with denominator `N`, even though the
chapter owner `bestFunctionValueUpTo ... N` is the infimum over the first `N + 1` samples. This
refinement keeps the source-facing unconstrained subgradient semantics, but rewrites the main
bound on the chapter's canonical `bestFunctionValueUpTo` / `deltaN` surface so the finite-prefix
indexing is coherent. It does not collapse the proposition to
`bestFunctionValueGapUpTo_le_lipschitz_mul_stepsize_ratio`, because that theorem assumes a global
subgradient selector `g : E → E`, while Proposition 3.36 is source-facing on the chosen
whole-space subgradients along one fixed run.
-/

section ConstantStepsize

variable (f : E → ℝ) (xStar : E) (R M ε : ℝ)
variable (xSeq g : ℕ → E)

/-- Proposition 3.36: if `x_{i+1} = x_i - (ε / M) • g_i`, each `g_i` is a subgradient of `f` at
`x_i` with `‖g_i‖ ≤ M`, and a chosen minimizer `xStar` satisfies `‖x₀ - xStar‖ ≤ R`, then the
best sampled objective value
`bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N` among `x₀, …, x_N` is bounded by the chapter owner
`Δ[N; R]` evaluated at the constant prefix `h_i = ε / M`; equivalently, evaluating `deltaN`
gives the textbook formula with denominator `N + 1`. -/
-- Proof sketch: expand `‖xSeq (i + 1) - xStar‖²`, use the subgradient inequality at `xSeq i`
-- with comparison point `xStar`, and bound `‖g i‖²` by `M²`. Summing the one-step recursion over
-- the `N + 1` sampled indices identifies the resulting finite-prefix quotient with the owner
-- `Δ[N; R]` at the constant stepsize prefix.
theorem subgradientMethod_bestObjectiveValue_sub_le_of_constant_stepsize
    (hM : 0 < M) (hε : 0 < ε)
    (hxStar_min : IsMinOn f Set.univ xStar)
    (hxSeq_zero_dist : ‖xSeq 0 - xStar‖ ≤ R)
    (hxSeq_succ : ∀ i, xSeq (i + 1) = xSeq i - (ε / M) • g i)
    (h_subgradient : ∀ i, g i ∈ ∂[Set.univ] f((xSeq i)))
    (h_subgradient_bound : ∀ i, ‖g i‖ ≤ M)
    (N : ℕ) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N - f xStar ≤
      M *
        Δ[N; R] ((EuclideanSpace.equiv (Fin (N + 1)) ℝ).symm fun _ ↦ ε / M) := sorry

/-- If the iteration count is at least `M² R² / ε²`, the constant-step subgradient bound gives an
`ε`-accurate sampled objective value. -/
-- Proof sketch: combine
-- `subgradientMethod_bestObjectiveValue_sub_le_of_constant_stepsize` with the threshold estimate
-- `M * R² / (2 ε (N + 1)) ≤ ε / 2`, obtained from
-- `M² R² / ε² ≤ N + 1`, and simplify the constant-prefix `deltaN` value.
theorem subgradientMethod_bestObjectiveValue_sub_le_eps_of_constant_stepsize_threshold
    (hM : 0 < M) (hε : 0 < ε)
    (hxStar_min : IsMinOn f Set.univ xStar)
    (hxSeq_zero_dist : ‖xSeq 0 - xStar‖ ≤ R)
    (hxSeq_succ : ∀ i, xSeq (i + 1) = xSeq i - (ε / M) • g i)
    (h_subgradient : ∀ i, g i ∈ ∂[Set.univ] f((xSeq i)))
    (h_subgradient_bound : ∀ i, ‖g i‖ ≤ M)
    (N : ℕ)
    (h_threshold : M ^ (2 : ℕ) * R ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ N + 1) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N - f xStar ≤ ε := sorry

end ConstantStepsize

end

/-! ### Theorem_3_36 (from Chap03) -/
noncomputable section

/- Theorem 3.36 lies in the chapter's unrestricted minimax / saddle-value domain.

Primary domain:
- unrestricted minimax for a parametric payoff, already organized in the project around the
  set-based saddle-point and pointwise-supremum owners.

Relevant sampled declarations:
- `minimax_eq_of_unique_slice_argmin_and_attained_dual_max`
- `isSaddlePointOn_of_unique_slice_argmin_and_attained_dual_max`
- `isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max`
- `pointwiseSupremumOn`

Best owner abstraction:
- source-facing: this numbered recall surface;
- core/canonical: the chapter owner
  `minimax_eq_of_unique_slice_argmin_and_attained_dual_max` from
  `Theorem_3_1_29`, phrased through `pointwiseSupremumOn`, `IsSaddlePointOn`, `IsMinOn`, and
  `IsMaxOn`;
- bridge/view: the unrestricted case is the specialization `P = Set.univ`, `S = Set.univ`.

Primitive data:
- none in this file; the owner theorem already carries the full mathematical data.

Derived API:
- the recalled minimax theorem, together with the saddle-point and primal-minimizer companions in
  `Theorem_3_1_29`.

This file no longer introduces a second public lower-envelope theorem or companion bridge lemmas.
The same textbook item is already canonicalized upstream in `Theorem_3_1_29`, so the correct
surface here is direct reuse of that owner rather than a parallel `sInf (Set.range ...)` wrapper.
-/

recall minimax_eq_of_unique_slice_argmin_and_attained_dual_max

end
