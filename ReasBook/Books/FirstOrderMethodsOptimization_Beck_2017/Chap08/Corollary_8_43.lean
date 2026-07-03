import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_41
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp (toLp)

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m : ℕ} [NeZero m]
variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {fOpt : ℝ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/- Corollary 8.43 is `source-facing`: it bounds every optimal dual multiplier for the Chapter 8
dual problem under Assumption 8.41. The natural owner for dual optimality is the canonical
predicate `IsMaxOn` on the nonnegative orthant in `EuclideanSpace ℝ (Fin m)`. The norm estimate
itself is the `μ = fOpt` specialization of the preceding Chapter 8 bound, with strong duality
coming from the standing problem assumptions rather than from a new local wrapper for `Λ*`. -/

-- Proof sketch: use strong duality under `h_problem` to identify the dual optimal value with
-- `fOpt`. Since `lam` maximizes the dual objective on the nonnegative orthant, it belongs to the
-- superlevel set at level `fOpt`. Then apply the Chapter 8 norm bound for dual superlevel sets at
-- the strict feasible point `xBar`.
/-- Corollary 8.43: under Assumption 8.41, every optimal multiplier `λ` of the dual problem
`max {q(λ) : λ ∈ ℝ_+^m}` satisfies the bound
`‖λ‖ ≤ (f(xBar) - fOpt) / min_i {-g_i(xBar)}` for any strict feasible point `xBar ∈ X`. -/
theorem norm_le_div_strict_feasibility_margin_of_dual_optimal_multiplier
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {xBar : E} (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    {lam : Λ}
    (hLam :
      IsMaxOn
        (lagrangian_dual_objective X f (fun x ↦ toLp 2 (fun i : Fin m ↦ g i x)))
        {μ : Λ | ∀ i : Fin m, 0 ≤ μ i} lam) :
    ‖lam‖ ≤
      (f xBar - fOpt) /
        (((Finset.univ).image fun i : Fin m ↦ -g i xBar).min'
          (Finset.univ_nonempty.image fun i : Fin m ↦ -g i xBar)) := sorry

end
