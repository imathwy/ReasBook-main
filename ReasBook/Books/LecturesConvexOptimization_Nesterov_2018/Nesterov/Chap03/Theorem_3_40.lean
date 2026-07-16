import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Algorithm_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_41
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Theorem_3_2_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators DeltaN

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 3.40 lies in the chapter's projected normalized subgradient / finite-horizon stepsize
bound domain.

Sampled owner-style declarations:
- `FirstOrderConvexMinimizationProblem.normalizedSubgradientStep` in `Definition_3_40`, the owner
  projected normalized oracle step;
- `SimpleSetSubgradientMethod.iterates` in `Algorithm_3_2`, the recursive owner iterate sequence;
- `bestFunctionValueUpTo` in `Theorem_3_2_10`, the chapter owner of best sampled objective values;
- `deltaN` and `deltaN_apply` in `Definition_3_41`, the chapter owner and evaluation bridge for
  the finite stepsize scalar `Δ_N`.

Best owner abstraction:
- `source-facing`: the best sampled-value bound for a run
  `method : SimpleSetSubgradientMethod problem`;
- `core/canonical`: the scalar owner `deltaN`, surfaced as `Δ[k; R]`, for the finite
  stepsize prefix;
- `bridge/view`: the finite prefix `method.stepsizePrefix k`.

Primitive data:
- the owner first-order convex minimization problem `problem`;
- the owner simple-set subgradient run `method`;
- the reference minimizer `xStar`, radius `R`, Lipschitz constant `M`, and stage `k`.

Derived API:
- the owner projected normalized step and iterate recursion;
- the iterate sequence `method`;
- the sampled best value `bestFunctionValueUpTo (fun i ↦ problem (method i)) k`;
- the finite stepsize bound expressed canonically as `Δ[k; R]` of the method's prefix.

The previous version exposed a parallel selector-style API through raw parameters
`Q`, `projQ`, `f`, `xSeq`, `g`, and `h`. This refinement keeps the theorem source-facing, but
also removes the redundant nonzero-subgradient hypothesis and rewrites the stepsize ratio through
the chapter owner `deltaN`, leaving only the finite-prefix bridge `method.stepsizePrefix k`.
-/

namespace SimpleSetSubgradientMethod

variable {problem : FirstOrderConvexMinimizationProblem E}

/-- Theorem 3.40: for a simple-set subgradient method on an owner first-order convex minimization
problem, the best objective value among the first `k + 1` iterates satisfies the standard
`M * Δ_k` error bound, written with the chapter owners
`bestFunctionValueUpTo (fun i ↦ problem (method i)) k` for the sampled minimum `f_k^*` and
`Δ[k; R] (method.stepsizePrefix k)` for the finite stepsize prefix. -/
-- Proof sketch: first use nonexpansiveness of the Euclidean projection to derive the one-step
-- distance recursion
-- `‖x_{i+1} - xStar‖² ≤ ‖x_i - xStar‖² - 2 h_i ⟪g_i / ‖g_i‖, x_i - xStar⟫ + h_i²`.
-- Summing this recursion yields an upper bound on the minimum normalized subgradient pairing over
-- `i = 0, …, k`. Then combine the subgradient inequality at the minimizer `xStar` with the
-- Lipschitz bound on the ball `Metric.closedBall xStar R` to estimate each objective gap by
-- `M` times the corresponding normalized pairing, identify the resulting stepsize quotient with
-- `Δ[k; R]` of the finite prefix, and finally take the minimum over the sampled iterates.
theorem bestFunctionValueUpTo_sub_le_of_projected_normalized_subgradient_method
    (method : SimpleSetSubgradientMethod problem) (xStar : E) (R M : NNReal)
    (hxStar_min : IsMinOn problem problem.feasibleSet xStar)
    (hf_lipschitz : LipschitzOnWith M problem (Metric.closedBall xStar R))
    (hx0_ball : method.x0 ∈ Metric.closedBall xStar R)
    (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ problem (method i)) k - problem xStar ≤
      (M : ℝ) * Δ[k; R] (method.stepsizePrefix k) := sorry

end SimpleSetSubgradientMethod

end
