import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_41
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m : ℕ}
variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {fOpt : ℝ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "q" =>
  fun lam : Λ ↦
    sInf ((fun x : E ↦ ((f x + dotProduct lam (fun i ↦ g i x) : ℝ) : EReal)) '' X)

-- Proof sketch: apply the strong-duality theorem for convex inequality-constrained problems under
-- the Slater-type assumptions packaged by `h_problem`. This identifies the least upper bound of
-- the dual objective values with the primal optimal value.
/-- Theorem 8.20 (1): under Assumption 8.41, if `qOpt` is the optimal value of the dual problem
`max {q(λ) : λ ∈ ℝ_+^m}`, then `qOpt = fOpt`. -/
theorem dual_projected_subgradient_problem_strong_duality
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {qOpt : EReal}
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) qOpt) :
    qOpt = (fOpt : EReal) := sorry

-- Proof sketch: apply the dual-attainment part of the strong-duality theorem for convex
-- inequality-constrained problems under the Slater-type assumptions packaged by `h_problem` to
-- obtain a maximizer of `q` on the nonnegative orthant whose value is `qOpt`.
/-- Theorem 8.20 (2): under Assumption 8.41, the dual problem attains the optimal value `qOpt`
at some nonnegative multiplier. -/
theorem dual_projected_subgradient_problem_dual_attainment
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {qOpt : EReal}
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) qOpt) :
    ∃ lamStar : Λ,
      IsMaxOn q (dual_problem_feasible_set m) lamStar ∧
        q lamStar = qOpt := sorry

end
