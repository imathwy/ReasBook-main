module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

public section

namespace FourFoldFanPL

/-- Helper for Exercise 74.4: the determinant of three coordinate vectors in real
three-space. -/
def det3 (u v w : Fin 3 → ℝ) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
    u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0)

/-- Helper for Exercise 74.4: the coordinate formula for the real three-dimensional
determinant. -/
lemma det3_apply (u v w : Fin 3 → ℝ) :
    det3 u v w =
      u 0 * (v 1 * w 2 - v 2 * w 1) -
        u 1 * (v 0 * w 2 - v 2 * w 0) +
          u 2 * (v 0 * w 1 - v 1 * w 0) := by
  -- Expose the coordinate formula through a propositional API for downstream modules.
  rfl

/-- Helper for Exercise 74.4: the signed maximal minors of the matrix with columns
`u`, `w`, `-x`, and `-y`. -/
def correctedCofactors (u w x y : Fin 3 → ℝ) : Fin 4 → ℝ :=
  fun i ↦
    match i.1 with
    | 0 => -det3 w x y
    | 1 => det3 u x y
    | 2 => det3 u w y
    | _ => -det3 u w x

/-- Helper for Exercise 74.4: the first corrected cofactor is the negated complementary
determinant. -/
lemma correctedCofactors_zero (u w x y : Fin 3 → ℝ) :
    correctedCofactors u w x y 0 = -det3 w x y := by
  -- Evaluate the finite cofactor index without exposing its implementation downstream.
  rfl

/-- Helper for Exercise 74.4: the second corrected cofactor is the complementary
determinant with first column `u`. -/
lemma correctedCofactors_one (u w x y : Fin 3 → ℝ) :
    correctedCofactors u w x y 1 = det3 u x y := by
  -- Evaluate the second finite cofactor index.
  rfl

/-- Helper for Exercise 74.4: the third corrected cofactor is the complementary
determinant with columns `u,w,y`. -/
lemma correctedCofactors_two (u w x y : Fin 3 → ℝ) :
    correctedCofactors u w x y 2 = det3 u w y := by
  -- Evaluate the third finite cofactor index.
  rfl

/-- Helper for Exercise 74.4: the last corrected cofactor is the negated complementary
determinant with columns `u,w,x`. -/
lemma correctedCofactors_three (u w x y : Fin 3 → ℝ) :
    correctedCofactors u w x y 3 = -det3 u w x := by
  -- Evaluate the last finite cofactor index.
  rfl

/-- Helper for Exercise 74.4: a linear dependence on `u`, `w`, `-x`, and `-y`
forces the corresponding adjacent coefficient-cofactor ratios to agree. -/
lemma kernelCoefficientRelations (u w x y : Fin 3 → ℝ) (a b c d : ℝ)
    (hlinear : a • u + b • w = c • x + d • y) :
    a * correctedCofactors u w x y 1 = b * correctedCofactors u w x y 0 ∧
      b * correctedCofactors u w x y 2 = c * correctedCofactors u w x y 1 ∧
        d * correctedCofactors u w x y 2 = c * correctedCofactors u w x y 3 := by
  -- Read the vector equality in each of the three ambient coordinates.
  have hzero := congrFun hlinear 0
  have hone := congrFun hlinear 1
  have htwo := congrFun hlinear 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hzero hone htwo
  constructor
  · -- Taking the determinant with `x,y` eliminates the last two coefficients.
    simp [correctedCofactors, det3]
    linear_combination
      (x 1 * y 2 - x 2 * y 1) * hzero -
      (x 0 * y 2 - x 2 * y 0) * hone +
      (x 0 * y 1 - x 1 * y 0) * htwo
  · constructor
    · -- Taking the determinant with `u,y` eliminates `a` and `d`.
      simp [correctedCofactors, det3]
      linear_combination
        (-u 1 * y 2 + u 2 * y 1) * hzero +
        (u 0 * y 2 - u 2 * y 0) * hone +
        (-u 0 * y 1 + u 1 * y 0) * htwo
    · -- Taking the determinant with `u,w` eliminates `a` and `b`.
      simp [correctedCofactors, det3]
      linear_combination
        (-u 1 * w 2 + u 2 * w 1) * hzero +
        (u 0 * w 2 - u 2 * w 0) * hone +
        (-u 0 * w 1 + u 1 * w 0) * htwo

/-- Helper for Exercise 74.4: mixed nonzero cofactors of `[u,w,-x,-y]` exclude a
nonzero intersection of the two positive cones spanned by `u,w` and `x,y`. -/
lemma mixedCofactors_noPositiveConeIntersection (u w x y : Fin 3 → ℝ)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hnonzero : ∀ i, correctedCofactors u w x y i ≠ 0)
    (hnotPositive : ¬ ∀ i, 0 < correctedCofactors u w x y i)
    (hnotNegative : ¬ ∀ i, correctedCofactors u w x y i < 0)
    (hlinear : a • u + b • w = c • x + d • y) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  -- The determinant identities propagate nonzeroness and signs around the four columns.
  obtain ⟨hab, hbc, hdc⟩ := kernelCoefficientRelations u w x y a b c d hlinear
  have haZero : a = 0 := by
    by_contra haNe
    have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm haNe)
    have hbNe : b ≠ 0 := by
      intro hbZero
      rw [hbZero, zero_mul] at hab
      exact (mul_ne_zero haNe (hnonzero 1)) hab
    have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbNe)
    have hcNe : c ≠ 0 := by
      intro hcZero
      rw [hcZero, zero_mul] at hbc
      exact (mul_ne_zero hbNe (hnonzero 2)) hbc
    have hcPos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcNe)
    have hdNe : d ≠ 0 := by
      intro hdZero
      rw [hdZero, zero_mul] at hdc
      exact (mul_ne_zero hcNe (hnonzero 3)) hdc.symm
    have hdPos : 0 < d := lt_of_le_of_ne hd (Ne.symm hdNe)
    rcases lt_or_gt_of_ne (hnonzero 0) with hkZeroNeg | hkZeroPos
    · -- A negative first cofactor forces all four cofactors to be negative.
      apply hnotNegative
      intro i
      fin_cases i
      · exact hkZeroNeg
      · have hprod : a * correctedCofactors u w x y 1 < 0 := by
          rw [hab]
          exact mul_neg_of_pos_of_neg hbPos hkZeroNeg
        exact (mul_neg_iff.mp hprod).resolve_right
          (not_and_of_not_left _ (not_lt_of_ge (le_of_lt haPos))) |>.2
      · have hkOneNeg : correctedCofactors u w x y 1 < 0 := by
          have hprod : a * correctedCofactors u w x y 1 < 0 := by
            rw [hab]
            exact mul_neg_of_pos_of_neg hbPos hkZeroNeg
          exact (mul_neg_iff.mp hprod).resolve_right
            (not_and_of_not_left _ (not_lt_of_ge (le_of_lt haPos))) |>.2
        have hprod : b * correctedCofactors u w x y 2 < 0 := by
          rw [hbc]
          exact mul_neg_of_pos_of_neg hcPos hkOneNeg
        exact (mul_neg_iff.mp hprod).resolve_right
          (not_and_of_not_left _ (not_lt_of_ge (le_of_lt hbPos))) |>.2
      · have hkOneNeg : correctedCofactors u w x y 1 < 0 := by
          have hprod : a * correctedCofactors u w x y 1 < 0 := by
            rw [hab]
            exact mul_neg_of_pos_of_neg hbPos hkZeroNeg
          exact (mul_neg_iff.mp hprod).resolve_right
            (not_and_of_not_left _ (not_lt_of_ge (le_of_lt haPos))) |>.2
        have hkTwoNeg : correctedCofactors u w x y 2 < 0 := by
          have hprod : b * correctedCofactors u w x y 2 < 0 := by
            rw [hbc]
            exact mul_neg_of_pos_of_neg hcPos hkOneNeg
          exact (mul_neg_iff.mp hprod).resolve_right
            (not_and_of_not_left _ (not_lt_of_ge (le_of_lt hbPos))) |>.2
        have hprod : c * correctedCofactors u w x y 3 < 0 := by
          rw [← hdc]
          exact mul_neg_of_pos_of_neg hdPos hkTwoNeg
        exact (mul_neg_iff.mp hprod).resolve_right
          (not_and_of_not_left _ (not_lt_of_ge (le_of_lt hcPos))) |>.2
    · -- A positive first cofactor similarly forces all four cofactors to be positive.
      apply hnotPositive
      intro i
      fin_cases i
      · exact hkZeroPos
      · have hprod : 0 < a * correctedCofactors u w x y 1 := by
          rw [hab]
          exact mul_pos hbPos hkZeroPos
        exact (mul_pos_iff.mp hprod).resolve_right
          (not_and_of_not_left _ (not_lt_of_ge (le_of_lt haPos))) |>.2
      · have hkOnePos : 0 < correctedCofactors u w x y 1 := by
          have hprod : 0 < a * correctedCofactors u w x y 1 := by
            rw [hab]
            exact mul_pos hbPos hkZeroPos
          exact (mul_pos_iff.mp hprod).resolve_right
            (not_and_of_not_left _ (not_lt_of_ge (le_of_lt haPos))) |>.2
        have hprod : 0 < b * correctedCofactors u w x y 2 := by
          rw [hbc]
          exact mul_pos hcPos hkOnePos
        exact (mul_pos_iff.mp hprod).resolve_right
          (not_and_of_not_left _ (not_lt_of_ge (le_of_lt hbPos))) |>.2
      · have hkOnePos : 0 < correctedCofactors u w x y 1 := by
          have hprod : 0 < a * correctedCofactors u w x y 1 := by
            rw [hab]
            exact mul_pos hbPos hkZeroPos
          exact (mul_pos_iff.mp hprod).resolve_right
            (not_and_of_not_left _ (not_lt_of_ge (le_of_lt haPos))) |>.2
        have hkTwoPos : 0 < correctedCofactors u w x y 2 := by
          have hprod : 0 < b * correctedCofactors u w x y 2 := by
            rw [hbc]
            exact mul_pos hcPos hkOnePos
          exact (mul_pos_iff.mp hprod).resolve_right
            (not_and_of_not_left _ (not_lt_of_ge (le_of_lt hbPos))) |>.2
        have hprod : 0 < c * correctedCofactors u w x y 3 := by
          rw [← hdc]
          exact mul_pos hdPos hkTwoPos
        exact (mul_pos_iff.mp hprod).resolve_right
          (not_and_of_not_left _ (not_lt_of_ge (le_of_lt hcPos))) |>.2
  -- Once `a` vanishes, each adjacent ratio and cofactor nonzeroness forces the next
  -- coefficient to vanish in turn.
  have hbZero : b = 0 := by
    rw [haZero, zero_mul] at hab
    exact (mul_eq_zero.mp hab.symm).resolve_right (hnonzero 0)
  have hcZero : c = 0 := by
    rw [hbZero, zero_mul] at hbc
    exact (mul_eq_zero.mp hbc.symm).resolve_right (hnonzero 1)
  have hdZero : d = 0 := by
    rw [hcZero, zero_mul] at hdc
    exact (mul_eq_zero.mp hdc).resolve_right (hnonzero 2)
  exact ⟨haZero, hbZero, hcZero, hdZero⟩

end FourFoldFanPL
