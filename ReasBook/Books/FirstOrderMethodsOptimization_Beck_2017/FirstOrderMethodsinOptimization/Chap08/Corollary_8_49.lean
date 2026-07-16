import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_20
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Theorem_8_42
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Lemma_8_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ} [NeZero m]
variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ}
variable {fOpt qOpt L ε : ℝ}
variable (xSel : (Fin m → NNReal) → {x // x ∈ X}) (lam0 : Fin m → NNReal)
variable {xBar : E}

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "γ" => fun n : ℕ ↦ 1 / Real.sqrt ((n : ℝ) + 1)
local notation "q" => lagrangian_dual_objective X f (dual_constraint_vector g)
local notation "α" => (f xBar - fOpt) / strict_feasibility_margin g xBar
local notation "M" =>
  dual_projected_subgradient_multiplier_norm_bound f fOpt qOpt g xBar L 1 lam0
local notation "C" => 2 * L * ((M + 2 * α) ^ (2 : ℕ) + Real.log 3)
local notation "xSeq" => dual_projected_subgradient_primal_iterate X g xSel γ lam0
local notation "constraintSeq" =>
  fun n ↦ dual_projected_subgradient_constraint_vector g (xSeq n : E)
local notation "partialAvg" =>
  partial_averaging_sequence (fun n ↦ (xSeq n : E)) γ constraintSeq
local notation "violation" =>
  fun x ↦ ‖(WithLp.toLp 2 (fun i ↦ max (g i x) 0) : EuclideanSpace ℝ (Fin m))‖

/- Corollary 8.49 is `source-facing`: it converts the `O(1 / √k)` estimates from Theorem 8.48
into an iteration-complexity threshold of order `O(1 / ε^2)`. The canonical owners are already
present in the Chapter 8 API: the partial averaging iterate from `partial_averaging_sequence`,
the objective-gap estimate from Theorem 8.48, and the Euclidean norm of the coordinatewise
positive part `[(g(x))]_+`. The main labeled entry is therefore a single max-bound packaging the
two source conclusions, with the individual inequalities recovered as companion lemmas. -/

-- Proof sketch: unfold the displayed positive-part Euclidean norm and
-- `dual_projected_subgradient_constraint_vector`; each positive-part coordinate satisfies
-- `max (g_i x) 0 ≤ |g_i x|`, so the Euclidean norm of the positive part is bounded by the
-- Euclidean norm of the full constraint vector.
/-- The Euclidean norm of the coordinatewise positive part `[(g(x))]_+` is bounded by the
Euclidean norm of the full constraint vector `g(x)`. -/
theorem positive_part_constraint_vector_norm_le_dual_projected_subgradient_constraint_vector_norm
    (g : Fin m → E → ℝ) (x : E) :
    ‖(WithLp.toLp 2 (fun i ↦ max (g i x) 0) : EuclideanSpace ℝ (Fin m))‖ ≤
      ‖dual_projected_subgradient_constraint_vector g x‖ := sorry

-- Proof sketch: use the two bounds from Theorem 8.48 for the partial averaging iterate. The
-- complexity hypothesis is exactly the condition ensuring that the common constant
-- `C / √(k + 2)` is at most `ε` and that the constraint estimate
-- `C / (α * √(k + 2))` is also at most `ε`; then bound the positive-part residual by the full
-- constraint norm with
-- `positive_part_constraint_vector_norm_le_dual_projected_subgradient_constraint_vector_norm` and
-- package the two inequalities as a single `max` estimate.
/-- Corollary 8.49: under the hypotheses of Theorem 8.48, if `k ≥ 2` satisfies the displayed
`O(1 / ε^2)` iteration bound, then the partial averaging iterate `x^(k)` has objective gap at
most `ε` and positive-part constraint violation at most `ε`; equivalently, the maximum of these
two errors is bounded by `ε`. -/
theorem dual_projected_subgradient_partial_average_complexity_max_le_epsilon
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    {lamStar : Λ}
    (hLamStar : IsMaxOn q (dual_problem_feasible_set m) lamStar)
    (hqOpt : q lamStar = (qOpt : EReal))
    (hε : 0 < ε)
    (hα : 0 < α)
    {k : ℕ} (hk : 2 ≤ k)
    (hk_complexity :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) - 2 ≤ (k : ℝ)) :
    max (f (partialAvg k) - fOpt) (violation (partialAvg k)) ≤ ε := sorry

-- Proof sketch: apply `le_trans` with `le_max_left _ _` to
-- `dual_projected_subgradient_partial_average_complexity_max_le_epsilon`.
/-- The complexity threshold from Corollary 8.49 implies the objective-gap estimate
`f(x^(k)) - fOpt ≤ ε`. -/
theorem dual_projected_subgradient_partial_average_objective_gap_le_epsilon
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    {lamStar : Λ}
    (hLamStar : IsMaxOn q (dual_problem_feasible_set m) lamStar)
    (hqOpt : q lamStar = (qOpt : EReal))
    (hε : 0 < ε)
    (hα : 0 < α)
    {k : ℕ} (hk : 2 ≤ k)
    (hk_complexity :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) - 2 ≤ (k : ℝ)) :
    f (partialAvg k) - fOpt ≤ ε := sorry

-- Proof sketch: apply `le_trans` with `le_max_right _ _` to
-- `dual_projected_subgradient_partial_average_complexity_max_le_epsilon`.
/-- The complexity threshold from Corollary 8.49 also implies that the positive-part constraint
violation of `x^(k)` is at most `ε`. -/
theorem dual_projected_subgradient_partial_average_positive_constraint_violation_le_epsilon
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    {lamStar : Λ}
    (hLamStar : IsMaxOn q (dual_problem_feasible_set m) lamStar)
    (hqOpt : q lamStar = (qOpt : EReal))
    (hε : 0 < ε)
    (hα : 0 < α)
    {k : ℕ} (hk : 2 ≤ k)
    (hk_complexity :
      C ^ (2 : ℕ) / (min (α ^ (2 : ℕ)) 1 * ε ^ (2 : ℕ)) - 2 ≤ (k : ℝ)) :
    violation (partialAvg k) ≤ ε := sorry

end
