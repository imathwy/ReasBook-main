import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_41
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_55
import LecturesConvexOptimization_Nesterov_2018.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

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
