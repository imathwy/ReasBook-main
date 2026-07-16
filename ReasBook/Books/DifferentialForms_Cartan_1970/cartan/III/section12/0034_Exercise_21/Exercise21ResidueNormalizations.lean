import DifferentialForms_Cartan_1970.cartan.III.section12.«0034_Exercise_21».NegativeAxisWedgeAnnulus

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval
/-- Helper for Exercise 21: the positive-imaginary residue coefficient can be rewritten in the
normalized inverse-product form produced by the residue theorem. -/
lemma exercise21_pos_imag_coeff_normalized (a : ℝ) :
    -((Complex.log ((a : ℂ) * Complex.I))⁻¹ * (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹))) =
      1 / ((2 * (a : ℂ) * Complex.I) * Complex.log ((a : ℂ) * Complex.I)) := by
  -- Reverse the inverses in the commutative field `ℂ` and simplify `I⁻¹ = -I`.
  simp [div_eq_mul_inv, mul_left_comm, mul_comm, mul_inv_rev]

/-- Helper for Exercise 21: the negative-imaginary residue coefficient has the analogous
normalized inverse-product form. -/
lemma exercise21_neg_imag_coeff_normalized (a : ℝ) :
    (Complex.log (-((a : ℂ) * Complex.I)))⁻¹ * (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹)) =
      -1 / ((2 * (a : ℂ) * Complex.I) * Complex.log (-((a : ℂ) * Complex.I))) := by
  -- The same inverse-reversal identity applies at the pole `-a i`.
  simp [div_eq_mul_inv, mul_left_comm, mul_comm, mul_inv_rev]

/-- Helper for Exercise 21: summing the residues over the three-pole `Finset` gives the normalized
expression returned by the oriented-boundary residue theorem. -/
lemma exercise21PoleFinset_sum_residue_normalized (a : ℝ) (ha : 0 < a) :
    Finset.sum (exercise21PoleFinset a) (exercise21Residue a) =
      ((1 + (a : ℂ) ^ 2)⁻¹ +
        -((Complex.log ((a : ℂ) * Complex.I))⁻¹ *
            (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹))) +
        (Complex.log (-((a : ℂ) * Complex.I)))⁻¹ *
          (Complex.I * (((a : ℂ)⁻¹) * (2 : ℂ)⁻¹))) := by
  have h_ai_ne_one : (a : ℂ) * Complex.I ≠ (1 : ℂ) := by
    -- The point `a i` has nonzero imaginary part, so it cannot equal `1`.
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_neg_ai_ne_one : -((a : ℂ) * Complex.I) ≠ (1 : ℂ) := by
    -- The point `-a i` also has nonzero imaginary part.
    intro h
    have him := congrArg Complex.im h
    simpa [ha.ne'] using him
  have h_ai_ne_neg_ai : (a : ℂ) * Complex.I ≠ -((a : ℂ) * Complex.I) := by
    -- Equality of the two imaginary poles would force `a = 0`.
    intro h
    have him := congrArg Complex.im h
    have : a = -a := by simpa using him
    linarith
  have h_neg_ai_ne_ai : -((a : ℂ) * Complex.I) ≠ (a : ℂ) * Complex.I := by
    intro h
    exact h_ai_ne_neg_ai h.symm
  rw [exercise21PoleFinset, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · -- Evaluate the residue selector at the three actual poles.
    simp [exercise21Residue, exercise21RealPoleCoeff, exercise21PosImagPoleCoeff,
      exercise21NegImagPoleCoeff, h_ai_ne_one, h_neg_ai_ne_one, h_neg_ai_ne_ai]
    rw [← exercise21_neg_imag_coeff_normalized]
    simp [add_assoc]
  · simp [h_ai_ne_neg_ai]
  · intro h
    simp at h
    rcases h with h | h
    · exact h_ai_ne_one h.symm
    · exact h_neg_ai_ne_one h.symm

