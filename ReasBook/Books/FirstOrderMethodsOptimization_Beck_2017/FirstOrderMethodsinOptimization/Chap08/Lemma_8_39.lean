import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Algorithm_8_13
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_38
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 8.39 is `source-facing`: its mathematical content is the descent estimate for the actual
incremental projected subgradient iterates `x^{k,i}` and `x^k`, not a surrogate wrapper around the
finite-sum problem. The existing owner abstractions already present in the project are the metric
projection `metricProjection`, the aggregate finite-sum objective `finite_sum_objective`, the
standing constrained problem class `IsConstrainedConvexProblem`, and the componentwise
assumption package `IncrementalProjectedSubgradientAssumptions`. Algorithm 8.13 is the canonical
owner of the recursive inner and outer iterate sequences used here. -/

section

variable {m : ℕ}
variable {fi : Fin m → E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem (finite_sum_objective fi) C XStar fOpt)
variable (h_incremental : IncrementalProjectedSubgradientAssumptions fi C)
variable (g : ℕ → C → Fin m → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  incremental_projected_subgradient_method
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex t g x0 k

local notation "x[" k "," i "]" =>
  incremental_projected_subgradient_inner_iterate
    C h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex t g k x[k] i

-- Proof sketch: apply the one-step projected subgradient inequality to each inner update
-- `x[k,i+1] = P_C (x[k,i] - t_k g^{k,i})`, sum over the `m` component steps, rewrite the summed
-- component objectives as the finite-sum objective, and bound the accumulated error terms with the
-- common subgradient norm constant `h_incremental.L` from Assumption 8.38.
/-- Lemma 8.39: under Assumptions 8.7 and 8.38, every outer step of the incremental projected
subgradient method satisfies the fundamental inequality
`‖x^{k+1} - xStar‖^2 ≤ ‖x^k - xStar‖^2 - 2 t_k (f(x^k) - fOpt) + t_k^2 m^2 L^2`
for each optimal point `xStar ∈ XStar`, where `f = ∑ i, f_i` and `L = h_incremental.L`. -/
theorem incremental_projected_subgradient_method_fundamental_inequality
    (h_subgrad :
      ∀ k (i : Fin m),
        toDualMap ℝ E (g k x[k,i] i) ∈ strongDualSubdifferential (fi i) (x[k,i] : E))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖(x[k + 1] : E) - xStar‖ ^ (2 : ℕ) ≤
      ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) -
        2 * t k * (((finite_sum_objective fi) (x[k] : E)).toReal - fOpt) +
          (t k) ^ (2 : ℕ) * (m : ℝ) ^ (2 : ℕ) * h_incremental.L ^ (2 : ℕ) := sorry

end

end
