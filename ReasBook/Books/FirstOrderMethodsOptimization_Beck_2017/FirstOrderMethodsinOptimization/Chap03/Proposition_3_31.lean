import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (toLp)

noncomputable section

variable {n : ℕ}

/-
Proposition 3.31 is `source-facing` at the possible-median predicate for an indexed finite sample
and the unit-weight one-dimensional Fermat-Weber objective. The public owner for that objective is
already `fermatWeberObjective` from Definition 3.14, so the textbook sum `x ↦ ∑ i, |x - a i|` and
its `ℓ₁`-norm realization are only `bridge/view` lemmas here rather than a second objective
wrapper. The `core/canonical` owners in this domain are `IsMinOn` for global minimizers and
mathlib's `WithLp 1` norm on the residual vector `i ↦ x - a i`. On the median side, the primitive
counting predicate remains local here, because the earlier chapter owner `median_set` is defined
on `Finset ℝ` and would erase sample multiplicities through `Finset.image`.
-/

recall IsMinOn
recall fermatWeberObjective
recall fermatWeberObjective_one_apply_eq_sum_abs
recall PiLp.norm_eq_of_L1

-- Proof sketch: `PiLp.norm_eq_of_L1` identifies the `WithLp 1` norm with the finite sum of point
-- norms, and on `ℝ` those norms are absolute values. The unit-weight real Fermat-Weber objective
-- is exactly the same finite sum by `fermatWeberObjective_one_apply_eq_sum_abs`.
/-- The unit-weight real Fermat-Weber objective is the `ℓ₁` norm of the residual vector
`i ↦ x - a i`. -/
theorem fermatWeberObjective_one_eq_toLp_norm (a : Fin n → ℝ) (x : ℝ) :
    fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a x = ‖toLp 1 (fun i ↦ x - a i)‖ := by
  calc
    fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a x = ∑ i, |x - a i| :=
      fermatWeberObjective_one_apply_eq_sum_abs a x
    _ = ‖toLp 1 (fun i ↦ x - a i)‖ := by
      simpa using (PiLp.norm_eq_of_L1 (toLp 1 fun i ↦ x - a i)).symm

/-- A real number is a possible median of a finite real sample when at least half of the sample
lies on each side of it, counted with multiplicity. -/
def IsPossibleMedian (a : Fin n → ℝ) (x : ℝ) : Prop :=
  2 * (Finset.univ.filter fun i ↦ a i ≤ x).card ≥ n ∧
    2 * (Finset.univ.filter fun i ↦ x ≤ a i).card ≥ n

/-- The defining inequalities for a possible sample median. -/
@[simp] theorem isPossibleMedian_iff {a : Fin n → ℝ} {x : ℝ} :
    IsPossibleMedian a x ↔
      2 * (Finset.univ.filter fun i ↦ a i ≤ x).card ≥ n ∧
        2 * (Finset.univ.filter fun i ↦ x ≤ a i).card ≥ n :=
  Iff.rfl

-- Proof sketch: order the sample values and analyze the one-dimensional convex objective
-- `fermatWeberObjective (fun _ ↦ 1) a`, equivalently `x ↦ ∑ i, |x - a i|`. Using the
-- subdifferential formula for `|·|` together with the finite sum rule and Fermat's optimality
-- condition, one shows that `x` is a global minimizer exactly when at least half of the sample
-- lies on each side of `x`, which is the defining condition for `IsPossibleMedian a x`.
/-- Proposition 3.31: a real number is a possible median of a finite real sample if and only if it
globally minimizes the unit-weight Fermat-Weber objective, equivalently the absolute-deviation
objective `x ↦ ∑ i, |x - a i|`. -/
theorem isPossibleMedian_iff_isMinOn_fermatWeberObjective_one
    (a : Fin n → ℝ) (x : ℝ) :
    IsPossibleMedian a x ↔
      IsMinOn (fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a) Set.univ x := sorry

/-- Set-valued form of Proposition 3.31. -/
theorem setOf_isPossibleMedian_eq_globalMinimizers_fermatWeberObjective_one (a : Fin n → ℝ) :
    {x : ℝ | IsPossibleMedian a x} =
      {x : ℝ | IsMinOn (fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a) Set.univ x} := by
  ext x
  exact isPossibleMedian_iff_isMinOn_fermatWeberObjective_one a x

end
