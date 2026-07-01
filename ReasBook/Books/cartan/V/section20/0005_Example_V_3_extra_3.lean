import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this file is source-facing in the complex infinite-product domain.
-- The owner-level mathlib declarations are `Complex.tendsto_euler_sin_prod`,
-- `euler_sineTerm_tprod`, and `multipliable_sineTerm`; the theorems below are bridge statements
-- in the textbook product forms.

open scoped Real

/-- Away from the origin, Euler's sine product takes the textbook quotient form. -/
theorem complex_sin_pi_div_pi_mul_eq_tprod_one_sub_sq_div_nat_sq {z : ℂ} (hz : z ≠ 0) :
    Complex.sin (π * z) / (π * z) =
      ∏' n : ℕ, ((1 : ℂ) - z ^ (2 : ℕ) / ((n : ℂ) + 1) ^ (2 : ℕ)) := by
  by_cases hzintegerComplement : z ∈ Complex.integerComplement
  · have hcanon :
        Complex.sin (((Real.pi : ℝ) : ℂ) * z) / ((((Real.pi : ℝ) : ℂ) * z)) =
          ∏' n : ℕ, ((1 : ℂ) - z ^ (2 : ℕ) / ((n : ℂ) + 1) ^ (2 : ℕ)) := by
        simpa [sineTerm, sub_eq_add_neg, neg_div] using
          (euler_sineTerm_tprod hzintegerComplement).symm
    have hzpi : (π : ℂ) * z = (((Real.pi : ℝ) : ℂ) * z) := rfl
    simpa [hzpi] using hcanon
  · classical
    have hpi : (π : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hzint : ∃ m : ℤ, (m : ℂ) = z := by
      simpa [Complex.mem_integerComplement_iff, eq_comm] using hzintegerComplement
    rcases hzint with ⟨m, rfl⟩
    have hm : m ≠ 0 := by
      norm_num at hz ⊢
      exact hz
    let k : ℕ := Int.natAbs m - 1
    have hk_succ : k + 1 = Int.natAbs m := by
      simpa [k] using Nat.succ_pred_eq_of_pos (Int.natAbs_pos.mpr hm)
    have hk_sq_int : ((Int.natAbs m : ℤ) ^ (2 : ℕ)) = m ^ (2 : ℕ) := by
      exact_mod_cast Int.natAbs_sq m
    have hk_sq_nat : (((k + 1 : ℕ) : ℂ) ^ (2 : ℕ)) = (m : ℂ) ^ (2 : ℕ) := by
      calc
        (((k + 1 : ℕ) : ℂ) ^ (2 : ℕ)) = (((Int.natAbs m : ℤ) : ℂ) ^ (2 : ℕ)) := by
          simp [hk_succ]
        _ = (m : ℂ) ^ (2 : ℕ) := by
          exact_mod_cast hk_sq_int
    have hk_sq : (((k : ℂ) + 1) ^ (2 : ℕ)) = (m : ℂ) ^ (2 : ℕ) := by
      simpa using hk_sq_nat
    have hk_nonzero : ((k : ℂ) + 1) ^ (2 : ℕ) ≠ 0 := by
      have hk1_pos : 0 < k + 1 := by
        rw [hk_succ]
        exact Int.natAbs_pos.mpr hm
      have hk1_nonzero : (k : ℂ) + 1 ≠ 0 := by
        exact_mod_cast hk1_pos.ne'
      exact pow_ne_zero _ hk1_nonzero
    have hk_factor :
        ((1 : ℂ) - (m : ℂ) ^ (2 : ℕ) / ((k : ℂ) + 1) ^ (2 : ℕ)) = 0 := by
      rw [← hk_sq, div_self hk_nonzero, sub_self]
    have hk_factor_owner : (1 : ℂ) + sineTerm (m : ℂ) k = 0 := by
      simpa [sineTerm, sub_eq_add_neg, neg_div] using hk_factor
    have hEventuallyZero :
        (fun n : ℕ ↦ ∏ j ∈ Finset.range n, (1 + sineTerm (m : ℂ) j)) =ᶠ[Filter.atTop]
          fun _ ↦ (0 : ℂ) := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨k + 1, fun n hn ↦ ?_⟩
      refine Finset.prod_eq_zero ?_ hk_factor_owner
      exact Finset.mem_range.mpr <| lt_of_lt_of_le (Nat.lt_succ_self k) hn
    have hzero_prod :
        Filter.Tendsto
          (fun n : ℕ ↦ ∏ j ∈ Finset.range n, (1 + sineTerm (m : ℂ) j))
          Filter.atTop (nhds (0 : ℂ)) := by
      exact Filter.Tendsto.congr' hEventuallyZero.symm tendsto_const_nhds
    have htprod_zero_owner : ∏' n : ℕ, (1 + sineTerm (m : ℂ) n) = 0 :=
      ((multipliable_sineTerm (m : ℂ)).hasProd_iff_tendsto_nat.2 hzero_prod).tprod_eq
    have htprod_zero :
        ∏' n : ℕ, ((1 : ℂ) - (m : ℂ) ^ (2 : ℕ) / ((n : ℂ) + 1) ^ (2 : ℕ)) = 0 := by
      simpa [sineTerm, sub_eq_add_neg, neg_div] using htprod_zero_owner
    have hsin_zero_canon :
        Complex.sin (((Real.pi : ℝ) : ℂ) * (m : ℂ)) / ((((Real.pi : ℝ) : ℂ) * (m : ℂ))) = 0 :=
      by
      have hcanon : Complex.sin ((m : ℂ) * ((Real.pi : ℝ) : ℂ)) = 0 := by
        simpa using Complex.sin_int_mul_pi m
      have : Complex.sin (((Real.pi : ℝ) : ℂ) * (m : ℂ)) = 0 := by
        simpa [mul_comm] using hcanon
      rw [this]
      simp
    have hsin_zero : Complex.sin (π * (m : ℂ)) / (π * (m : ℂ)) = 0 := by
      have hmul : (π : ℂ) * (m : ℂ) = (((Real.pi : ℝ) : ℂ) * (m : ℂ)) := rfl
      simpa [hmul] using hsin_zero_canon
    simpa [htprod_zero] using hsin_zero

/-- Example V.3-extra-3: Euler's infinite product formula for sine, written in the equivalent
product form that is valid at every complex number `z`. -/
theorem complex_sin_eq_pi_mul_tprod_one_sub_sq_div_nat_sq (z : ℂ) :
    Complex.sin (π * z) =
      π * z * ∏' n : ℕ, ((1 : ℂ) - z ^ (2 : ℕ) / ((n : ℂ) + 1) ^ (2 : ℕ)) := by
  by_cases hz : z = 0
  · subst hz
    simp
  · have hq :
        Complex.sin (π * z) / (π * z) =
          ∏' n : ℕ, ((1 : ℂ) - z ^ (2 : ℕ) / ((n : ℂ) + 1) ^ (2 : ℕ)) :=
      complex_sin_pi_div_pi_mul_eq_tprod_one_sub_sq_div_nat_sq hz
    have hpi : (π : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hpiz : π * z ≠ 0 := mul_ne_zero hpi hz
    rw [div_eq_iff hpiz] at hq
    simpa [mul_comm, mul_left_comm, mul_assoc] using hq
