import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex
open Equiv
open scoped Real

local notation "ℂ_ℤ" => integerComplement

/-- The positive-`n` summand in the cotangent partial fraction expansion. -/
noncomputable def cotangent_partial_fraction_term (n : ℕ+) (z : ℂ) : ℂ :=
  (2 * z) / (z ^ (2 : ℕ) - (n : ℂ) ^ (2 : ℕ))

lemma cotangent_partial_fraction_term_eq (n : ℕ+) {z : ℂ}
    (hsub : z - n ≠ 0) (hadd : z + n ≠ 0) :
    cotangent_partial_fraction_term n z = 1 / (z - n) + 1 / (z + n) := by
  rw [cotangent_partial_fraction_term, one_div_add_one_div hsub hadd]
  congr 1 <;> ring

/-- Away from the integers, the positive-index cotangent partial fraction series has the displayed
sum. -/
theorem cotangent_partial_fraction_hasSum {z : ℂ} (hz : z ∈ ℂ_ℤ) :
    HasSum (fun n : ℕ+ ↦ cotangent_partial_fraction_term n z)
      (π / tan (π * z) - 1 / z) := by
  have hsum_pnat :
      HasSum (fun n : ℕ+ ↦ 1 / (z - n) + 1 / (z + n))
        ((Real.pi : ℂ) * cot ((Real.pi : ℂ) * z) - 1 / z) := by
    have hsum_pnat_raw :
        HasSum ((fun n : ℕ+ ↦ 1 / (z - n) + 1 / (z + n)) ∘ pnatEquivNat.symm)
          ((Real.pi : ℂ) * cot ((Real.pi : ℂ) * z) - 1 / z) := by
      refine (Summable.hasSum_iff ?_).2 ?_
      · simpa [cotTerm, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc] using
          summable_cotTerm hz
      · simpa [cotTerm, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc] using
          (cot_series_rep' hz).symm
    rw [pnatEquivNat.symm.hasSum_iff] at hsum_pnat_raw
    exact hsum_pnat_raw
  have hsum_term :
      HasSum (fun n : ℕ+ ↦ cotangent_partial_fraction_term n z)
        ((Real.pi : ℂ) * cot ((Real.pi : ℂ) * z) - 1 / z) := by
    have hterm :
        ∀ n : ℕ+, cotangent_partial_fraction_term n z = 1 / (z - n) + 1 / (z + n) := fun n ↦ by
          refine cotangent_partial_fraction_term_eq n ?_ ?_
          · simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hz (-(n : ℤ))
          · simpa using integerComplement_add_ne_zero hz (n : ℤ)
    simpa [hterm] using hsum_pnat
  have hcot : (Real.pi : ℂ) / tan ((Real.pi : ℂ) * z) =
      (Real.pi : ℂ) * cot ((Real.pi : ℂ) * z) := by
    calc
      (Real.pi : ℂ) / tan ((Real.pi : ℂ) * z) =
          (Real.pi : ℂ) * (tan ((Real.pi : ℂ) * z))⁻¹ := by rw [div_eq_mul_inv]
      _ = (Real.pi : ℂ) * ((cot ((Real.pi : ℂ) * z))⁻¹)⁻¹ := by rw [← cot_inv_eq_tan]
      _ = (Real.pi : ℂ) * cot ((Real.pi : ℂ) * z) := by simp
  have hfinal :
      HasSum (fun n : ℕ+ ↦ cotangent_partial_fraction_term n z)
        ((Real.pi : ℂ) / tan ((Real.pi : ℂ) * z) - 1 / z) := by
    exact hcot ▸ hsum_term
  simpa using hfinal

/-- Example 3: for `z` away from the integers,
`1 / z + ∑_{n ≥ 1} 2z / (z^2 - n^2) = π / tan (π z)`. -/
theorem cotangent_partial_fraction_eq {z : ℂ} (hz : z ∈ ℂ_ℤ) :
    1 / z + (∑' n : ℕ+, cotangent_partial_fraction_term n z) =
      π / tan (π * z) := by
  rw [(cotangent_partial_fraction_hasSum hz).tsum_eq]
  abel
