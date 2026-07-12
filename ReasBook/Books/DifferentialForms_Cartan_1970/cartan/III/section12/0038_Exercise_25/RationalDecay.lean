import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».ShiftedLogResidueData

noncomputable section

open Filter Bornology

/-- Helper for Exercise 25: the degree-gap hypothesis already forces the denominator polynomial to
be nonzero. -/
lemma exercise25_denominator_ne_zero_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    Q ≠ 0 := by
  exact denominator_ne_zero_of_degree_gap_two P Q hdeg

/-- Helper for Exercise 25: after multiplying the numerator by `X^2`, the corrected numerator
still has nat-degree at most the denominator nat-degree. -/
lemma exercise25_numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (P * Polynomial.X ^ 2).natDegree ≤ Q.natDegree := by
  exact numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two P Q hdeg

/-- Helper for Exercise 25: the corrected numerator `(P * X^2).eval` is `O(Q.eval)` at the
cobounded filter, which is the algebraic form of bounding `z^2 * P(z) / Q(z)` near infinity. -/
lemma exercise25_numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (fun z ↦ (P * Polynomial.X ^ 2).eval z) =O[cobounded ℂ] Q.eval := by
  exact numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two P Q hdeg

/-- Helper for Exercise 25: a norm inequality `‖a‖ ≤ K ‖b‖` turns into a bound on `‖a / b‖`. -/
lemma exercise25_norm_div_le_of_norm_le_mul {a b : ℂ} {K : ℝ}
    (hK : 0 ≤ K) (hab : ‖a‖ ≤ K * ‖b‖) :
    ‖a / b‖ ≤ K := by
  exact norm_div_le_of_norm_le_mul hK hab

/-- Helper for Exercise 25: the corrected rational function `z^2 * P(z) / Q(z)` is uniformly
bounded outside a sufficiently large disk when `deg Q ≥ deg P + 2`. -/
lemma exercise25_rational_mul_sq_eventually_bounded
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖(z ^ 2 : ℂ) * (P.eval z / Q.eval z)‖ ≤ K := by
  simpa [rationalEval] using rationalEval_mul_sq_eventually_bounded P Q hdeg

/-- Helper for Exercise 25: a bound on `‖z^2 w‖` converts to the decay estimate `‖w‖ ≤ K / ‖z‖^2`
once `z` stays away from `0`. -/
lemma exercise25_decay_of_mul_sq_bound {R K : ℝ} {z w : ℂ}
    (hR : 0 < R) (hz : R ≤ ‖z‖) (hbound : ‖(z ^ 2 : ℂ) * w‖ ≤ K) :
    ‖w‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  exact decay_of_mul_sq_bound hR hz hbound
