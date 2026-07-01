import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m : ℕ}
variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {fOpt : ℝ}

/-- The standing Chapter 8 assumptions for the convex inequality-constrained problem: `X` is
convex, `f` and each `g i` are convex, `XStar` is the nonempty primal solution set with optimal
value `fOpt`, there is a strict feasible point in `X`, and every nonnegative-multiplier
Lagrangian minimization over `X` attains a minimizer. -/
class IsDualProjectedSubgradientProblem
    (X XStar : Set E) (f : E → ℝ) (g : Fin m → E → ℝ) (fOpt : ℝ) : Prop where
  feasible_convex : Convex ℝ X
  objective_convex : ConvexOn ℝ Set.univ f
  constraint_convex (i : Fin m) : ConvexOn ℝ Set.univ (g i)
  optimal_set_eq :
    XStar = {x | IsMinOn f {y | y ∈ X ∧ ∀ i : Fin m, g i y ≤ 0} x}
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB (f '' {x | x ∈ X ∧ ∀ i : Fin m, g i x ≤ 0}) fOpt
  slater_condition_on_X :
    ∃ x ∈ X, ∀ i : Fin m, g i x < 0
  lagrangian_has_minimizer (lam : Fin m → NNReal) :
    ∃ x,
      IsMinOn
        (fun y ↦
          f y +
            dotProduct (fun i : Fin m ↦ (lam i : ℝ)) (fun i ↦ g i y))
        X x

/-- The feasible set of the Chapter 8 dual problem is the nonnegative orthant in multiplier
space. -/
def dual_problem_feasible_set (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {lam | ∀ i : Fin m, 0 ≤ lam i}

-- Proof sketch: unfold `dual_problem_feasible_set`; membership is exactly coordinatewise
-- nonnegativity of the multiplier vector.
/-- Membership in `dual_problem_feasible_set m` means that every multiplier coordinate is
nonnegative. -/
@[simp] theorem mem_dual_problem_feasible_set
    {lam : EuclideanSpace ℝ (Fin m)} :
    lam ∈ dual_problem_feasible_set m ↔ ∀ i : Fin m, 0 ≤ lam i := sorry

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
