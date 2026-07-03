import cartan.V.section19.«0006_Example_3»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Complex
open Equiv
open scoped Real

local notation "ℂ_ℤ" => integerComplement

/-- Helper for Exercise 4: the shifted reciprocal difference over the positive naturals is
summable because its terms decay quadratically. -/
lemma summable_reciprocal_shift_difference_nat (u v : ℂ)
    (hu : ∀ n : ℕ, u + (n + 1 : ℂ) ≠ 0)
    (hv : ∀ n : ℕ, v + (n + 1 : ℂ) ≠ 0) :
    Summable (fun n : ℕ ↦ 1 / (u + (n + 1 : ℂ)) - 1 / (v + (n + 1 : ℂ))) := by
  have hsquare :
      Summable (fun n : ℕ ↦ (4 * ‖v - u‖) * (((n + 1 : ℝ) ^ 2)⁻¹)) := by
    -- The comparison series is a shifted `p`-series with exponent `2`.
    have hbase : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) :=
      (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
    have hshift : Summable (fun n : ℕ ↦ (((n + 1 : ℝ) ^ 2)⁻¹)) := by
      simpa using (summable_nat_add_iff 1).2 hbase
    simpa [mul_assoc, mul_left_comm, mul_comm] using hshift.mul_left (4 * ‖v - u‖)
  refine Summable.of_norm_bounded_eventually_nat hsquare ?_
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (2 * max ‖u‖ ‖v‖))] with n hn
  have hlarge : 2 * max ‖u‖ ‖v‖ ≤ (n : ℝ) := by
    exact_mod_cast (Nat.ceil_le.mp hn)
  have hu_half : ‖u‖ ≤ (n + 1 : ℝ) / 2 := by
    have humax : ‖u‖ ≤ max ‖u‖ ‖v‖ := le_max_left _ _
    nlinarith
  have hv_half : ‖v‖ ≤ (n + 1 : ℝ) / 2 := by
    have hvmax : ‖v‖ ≤ max ‖u‖ ‖v‖ := le_max_right _ _
    nlinarith
  have hu_triangle : (n + 1 : ℝ) ≤ ‖u + (n + 1 : ℂ)‖ + ‖u‖ := by
    calc
      (n + 1 : ℝ) = ‖(n + 1 : ℂ)‖ := by simpa using (Complex.norm_natCast (n + 1)).symm
      _ = ‖(u + (n + 1 : ℂ)) + (-u)‖ := by ring_nf
      _ ≤ ‖u + (n + 1 : ℂ)‖ + ‖-u‖ := norm_add_le _ _
      _ = ‖u + (n + 1 : ℂ)‖ + ‖u‖ := by simp
  have hv_triangle : (n + 1 : ℝ) ≤ ‖v + (n + 1 : ℂ)‖ + ‖v‖ := by
    calc
      (n + 1 : ℝ) = ‖(n + 1 : ℂ)‖ := by simpa using (Complex.norm_natCast (n + 1)).symm
      _ = ‖(v + (n + 1 : ℂ)) + (-v)‖ := by ring_nf
      _ ≤ ‖v + (n + 1 : ℂ)‖ + ‖-v‖ := norm_add_le _ _
      _ = ‖v + (n + 1 : ℂ)‖ + ‖v‖ := by simp
  have hu_lower : ((n + 1 : ℝ) / 2) ≤ ‖u + (n + 1 : ℂ)‖ := by
    nlinarith
  have hv_lower : ((n + 1 : ℝ) / 2) ≤ ‖v + (n + 1 : ℂ)‖ := by
    nlinarith
  have hn_half_pos : 0 < (n + 1 : ℝ) / 2 := by
    positivity
  have hu_pos : 0 < ‖u + (n + 1 : ℂ)‖ := lt_of_lt_of_le hn_half_pos hu_lower
  have hv_pos : 0 < ‖v + (n + 1 : ℂ)‖ := lt_of_lt_of_le hn_half_pos hv_lower
  have hu_inv :
      ‖u + (n + 1 : ℂ)‖⁻¹ ≤ (((n + 1 : ℝ) / 2) : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hu_pos hn_half_pos).2 hu_lower
  have hv_inv :
      ‖v + (n + 1 : ℂ)‖⁻¹ ≤ (((n + 1 : ℝ) / 2) : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hv_pos hn_half_pos).2 hv_lower
  have hterm :
      1 / (u + (n + 1 : ℂ)) - 1 / (v + (n + 1 : ℂ)) =
        (v - u) * (((u + (n + 1 : ℂ)) * (v + (n + 1 : ℂ)))⁻¹) := by
    -- Clear the two linear denominators and collect the numerator as `v - u`.
    field_simp [hu n, hv n]
    ring
  calc
    ‖1 / (u + (n + 1 : ℂ)) - 1 / (v + (n + 1 : ℂ))‖
        = ‖v - u‖ * (‖u + (n + 1 : ℂ)‖⁻¹ * ‖v + (n + 1 : ℂ)‖⁻¹) := by
            rw [hterm, norm_mul, norm_inv, norm_mul, mul_inv_rev]
            ring
    _ ≤ ‖v - u‖ * ((((n + 1 : ℝ) / 2) : ℝ)⁻¹ * (((n + 1 : ℝ) / 2) : ℝ)⁻¹) := by
          gcongr
    _ = (4 * ‖v - u‖) * (((n + 1 : ℝ) ^ 2)⁻¹) := by
          have hn1 : ((n + 1 : ℝ)) ≠ 0 := by positivity
          field_simp [pow_two, hn1]
          ring

/-- Helper for Exercise 4: subtracting the two shifted cotangent expansions produces the positive
and negative branches of the target integer series, indexed by `ℕ`. -/
lemma cotangent_shift_pair_difference_hasSum_nat (a : ℝ) (z : ℂ)
    (hz_add : z + a * I ∈ ℂ_ℤ)
    (hz_sub : z - a * I ∈ ℂ_ℤ) :
    HasSum
      (fun n : ℕ ↦
        (1 / (z + (n + 1 : ℂ) - a * I) - 1 / (z + (n + 1 : ℂ) + a * I)) +
          (1 / (z - (n + 1 : ℂ) - a * I) - 1 / (z - (n + 1 : ℂ) + a * I)))
      (π * (cot (π * (z - a * I)) - cot (π * (z + a * I))) -
        (1 / (z - a * I) - 1 / (z + a * I))) := by
  have hsub_pnat :
      HasSum
        (fun n : ℕ+ ↦ 1 / (z - a * I - n) + 1 / (z - a * I + n))
        (π * cot (π * (z - a * I)) - 1 / (z - a * I)) := by
    have hcot (w : ℂ) : π / tan (π * w) = π * cot (π * w) := by
      calc
        π / tan (π * w) = π * (tan (π * w))⁻¹ := by rw [div_eq_mul_inv]
        _ = π * ((cot (π * w))⁻¹)⁻¹ := by rw [← cot_inv_eq_tan]
        _ = π * cot (π * w) := by simp
    have hterm :
        ∀ n : ℕ+, cotangent_partial_fraction_term n (z - a * I) =
          1 / (z - a * I - n) + 1 / (z - a * I + n) := by
      intro n
      refine cotangent_partial_fraction_term_eq n ?_ ?_
      · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          integerComplement_add_ne_zero hz_sub (-(n : ℤ))
      · simpa [add_assoc, add_left_comm, add_comm] using
          integerComplement_add_ne_zero hz_sub (n : ℤ)
    -- Rewrite the cotangent term into the paired simple poles before using Example 3.
    exact hcot (z - a * I) ▸ by
      simpa [hterm] using cotangent_partial_fraction_hasSum hz_sub
  have hadd_pnat :
      HasSum
        (fun n : ℕ+ ↦ 1 / (z + a * I - n) + 1 / (z + a * I + n))
        (π * cot (π * (z + a * I)) - 1 / (z + a * I)) := by
    have hcot (w : ℂ) : π / tan (π * w) = π * cot (π * w) := by
      calc
        π / tan (π * w) = π * (tan (π * w))⁻¹ := by rw [div_eq_mul_inv]
        _ = π * ((cot (π * w))⁻¹)⁻¹ := by rw [← cot_inv_eq_tan]
        _ = π * cot (π * w) := by simp
    have hterm :
        ∀ n : ℕ+, cotangent_partial_fraction_term n (z + a * I) =
          1 / (z + a * I - n) + 1 / (z + a * I + n) := by
      intro n
      refine cotangent_partial_fraction_term_eq n ?_ ?_
      · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          integerComplement_add_ne_zero hz_add (-(n : ℤ))
      · simpa [add_assoc, add_left_comm, add_comm] using
          integerComplement_add_ne_zero hz_add (n : ℤ)
    -- The same simple-pole rewrite applies to the `z + ai` shift.
    exact hcot (z + a * I) ▸ by
      simpa [hterm] using cotangent_partial_fraction_hasSum hz_add
  have hsub_nat :
      HasSum
        (fun n : ℕ ↦ 1 / (z - a * I - (n + 1 : ℂ)) + 1 / (z - a * I + (n + 1 : ℂ)))
        (π * cot (π * (z - a * I)) - 1 / (z - a * I)) := by
    -- Transport the positive-index series from `ℕ+` to `ℕ` exactly once.
    simpa [Function.comp_def, Equiv.pnatEquivNat, add_assoc] using
      (pnatEquivNat.symm.hasSum_iff).2 hsub_pnat
  have hadd_nat :
      HasSum
        (fun n : ℕ ↦ 1 / (z + a * I - (n + 1 : ℂ)) + 1 / (z + a * I + (n + 1 : ℂ)))
        (π * cot (π * (z + a * I)) - 1 / (z + a * I)) := by
    -- Transport the second shifted cotangent series in the same way.
    simpa [Function.comp_def, Equiv.pnatEquivNat, add_assoc] using
      (pnatEquivNat.symm.hasSum_iff).2 hadd_pnat
  have hpair_raw :
      HasSum
        (fun n : ℕ ↦
          (1 / (z - a * I - (n + 1 : ℂ)) + 1 / (z - a * I + (n + 1 : ℂ))) -
            (1 / (z + a * I - (n + 1 : ℂ)) + 1 / (z + a * I + (n + 1 : ℂ))))
        ((π * cot (π * (z - a * I)) - 1 / (z - a * I)) -
          (π * cot (π * (z + a * I)) - 1 / (z + a * I))) := by
    -- Now subtract the two shifted cotangent identities termwise.
    exact hsub_nat.sub hadd_nat
  -- Reorder the four simple-pole terms into the positive and negative branches of the target
  -- integer sum.
  have hvalue :
      ((π * cot (π * (z - a * I)) - 1 / (z - a * I)) -
        (π * cot (π * (z + a * I)) - 1 / (z + a * I))) =
        π * (cot (π * (z - a * I)) - cot (π * (z + a * I))) -
          (1 / (z - a * I) - 1 / (z + a * I)) := by
    ring
  exact hvalue ▸ by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hpair_raw

/-- Helper for Exercise 4: the difference of the two shifted cotangents simplifies to the stated
hyperbolic-sine over sine-product closed form. -/
lemma cotangent_shift_difference_eq_sinh_div_sin_mul_sin (a : ℝ) (z : ℂ)
    (hz_add : z + a * I ∈ ℂ_ℤ)
    (hz_sub : z - a * I ∈ ℂ_ℤ) :
    π * (cot (π * (z - a * I)) - cot (π * (z + a * I))) =
      π * I * sinh (2 * π * a) /
        (sin (π * (z + a * I)) * sin (π * (z - a * I))) := by
  have hsin_add : sin (π * (z + a * I)) ≠ 0 := by
    simpa using sin_pi_mul_ne_zero (x := z + a * I) hz_add
  have hsin_sub : sin (π * (z - a * I)) ≠ 0 := by
    simpa using sin_pi_mul_ne_zero (x := z - a * I) hz_sub
  -- Rewrite the cotangents as `cos / sin`, collapse the numerator to a sine of the difference,
  -- and then use the imaginary-angle sine formula.
  have hnum :
      cos (π * (z - a * I)) * sin (π * (z + a * I)) -
        sin (π * (z - a * I)) * cos (π * (z + a * I)) =
          sin (π * (z + a * I - (z - a * I))) := by
    have harg : π * (z + a * I - (z - a * I)) = π * (z + a * I) - π * (z - a * I) := by
      ring
    rw [harg, Complex.sin_sub]
    ring
  calc
    π * (cot (π * (z - a * I)) - cot (π * (z + a * I)))
        = π * (sin (π * (z + a * I) - π * (z - a * I)) /
            (sin (π * (z + a * I)) * sin (π * (z - a * I)))) := by
              rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin]
              field_simp [hsin_add, hsin_sub]
              exact hnum
    _ = π * (sin (((2 * π * a : ℂ) * I)) /
          (sin (π * (z + a * I)) * sin (π * (z - a * I)))) := by
            congr 1
            ring
    _ = π * (sinh (2 * π * a) * I /
          (sin (π * (z + a * I)) * sin (π * (z - a * I)))) := by
            rw [Complex.sin_mul_I]
    _ = π * I * sinh (2 * π * a) /
          (sin (π * (z + a * I)) * sin (π * (z - a * I))) := by
            ring

/-- Helper for Exercise 4: the reciprocal difference equals the quadratic kernel after clearing the
two linear factors. -/
lemma reciprocal_shift_difference_eq_quadratic_kernel (a : ℝ) (z : ℂ) (n : ℤ)
    (hsub : z + n - a * I ≠ 0)
    (hadd : z + n + a * I ≠ 0) :
    1 / (z + n - a * I) - 1 / (z + n + a * I) =
      (2 * a * I) / ((z + n) ^ 2 + a ^ 2) := by
  -- Use the standard reciprocal-difference formula and then simplify the resulting denominator.
  calc
    1 / (z + n - a * I) - 1 / (z + n + a * I)
        = ((z + n + a * I) - (z + n - a * I)) / ((z + n - a * I) * (z + n + a * I)) := by
            rw [one_div, one_div, inv_sub_inv hsub hadd]
    _ = (2 * a * I) / ((z + n) ^ 2 + a ^ 2) := by
          have hden :
              (z + n - a * I) * (z + n + a * I) = (z + n) ^ 2 + a ^ 2 := by
            calc
              (z + n - a * I) * (z + n + a * I) = (z + n) ^ 2 - (a * I) ^ 2 := by
                ring
              _ = (z + n) ^ 2 + a ^ 2 := by
                have hI : I * ((a : ℂ) * I) = -(a : ℂ) := by
                  calc
                    I * ((a : ℂ) * I) = (a : ℂ) * (I * I) := by ring
                    _ = -(a : ℂ) := by simp
                calc
                  (z + n) ^ 2 - (a * I) ^ 2 = (z + n) ^ 2 - (a : ℂ) * (I * (a * I)) := by
                    ring
                  _ = (z + n) ^ 2 + a ^ 2 := by
                    rw [hI]
                    ring
          rw [hden]
          congr 1
          ring

/-- Helper for Exercise 4: the product `sin (π (z + ai)) sin (π (z - ai))` is the standard
`(cosh - cos)/2` denominator. -/
lemma sin_shift_product_eq_cosh_sub_cos_half (a : ℝ) (z : ℂ) :
    sin (π * (z + a * I)) * sin (π * (z - a * I)) =
      (cosh (2 * π * a) - cos (2 * π * z)) / 2 := by
  have htwo :
      2 * (sin (π * (z + a * I)) * sin (π * (z - a * I))) =
        cos (π * (z + a * I) - π * (z - a * I)) -
          cos (π * (z + a * I) + π * (z - a * I)) := by
    -- This is the complex identity `2 sin u sin v = cos (u - v) - cos (u + v)`.
    rw [Complex.cos_sub, Complex.cos_add]
    ring
  have htwo_ne : (2 : ℂ) ≠ 0 := by
    norm_num
  calc
    sin (π * (z + a * I)) * sin (π * (z - a * I))
        = (cos (π * (z + a * I) - π * (z - a * I)) -
            cos (π * (z + a * I) + π * (z - a * I))) / 2 := by
              refine (eq_div_iff htwo_ne).2 ?_
              simpa [mul_assoc, mul_left_comm, mul_comm] using htwo
    _ = (cos (((2 * π * a : ℂ) * I)) - cos (2 * π * z)) / 2 := by
          congr 1
          ring
    _ = (cosh (2 * π * a) - cos (2 * π * z)) / 2 := by
          rw [Complex.cos_mul_I]

/-- Exercise 4 (1): for a real parameter `a`, the doubly infinite partial-fraction expansion of
`π i sinh (2π a) / (sin (π (z + ai)) sin (π (z - ai)))` over the integer lattice has the stated
sum. -/
theorem exercise_4_partial_fraction_hasSum (a : ℝ) (z : ℂ)
    (hz_add : z + a * I ∈ ℂ_ℤ)
    (hz_sub : z - a * I ∈ ℂ_ℤ) :
    HasSum
      (fun n : ℤ ↦
        1 / (z + n - a * I) - 1 / (z + n + a * I))
      (π * I * sinh (2 * π * a) / (sin (π * (z + a * I)) * sin (π * (z - a * I)))) := by
  let f : ℤ → ℂ := fun n ↦ 1 / (z + n - a * I) - 1 / (z + n + a * I)
  have hpair :
      HasSum (fun n : ℕ ↦ f (n + 1) + f (-(n + 1)))
        (π * (cot (π * (z - a * I)) - cot (π * (z + a * I))) - f 0) := by
    -- The cotangent subtraction already matches the positive and negative branches of the
    -- desired integer series.
    simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      cotangent_shift_pair_difference_hasSum_nat a z hz_add hz_sub
  have hf_pos : Summable (fun n : ℕ ↦ f (n + 1)) := by
    -- The positive branch is the shifted reciprocal-difference series from the structural helper.
    simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      summable_reciprocal_shift_difference_nat (u := z - a * I) (v := z + a * I)
        (hu := by
          intro n
          simpa [add_assoc, add_left_comm, add_comm] using
            integerComplement_add_ne_zero hz_sub ((n : ℤ) + 1))
        (hv := by
          intro n
          simpa [add_assoc, add_left_comm, add_comm] using
            integerComplement_add_ne_zero hz_add ((n : ℤ) + 1))
  have hf_neg : Summable (fun n : ℕ ↦ f (-(n + 1))) := by
    have haux :
        Summable
          (fun n : ℕ ↦
            1 / ((-z + a * I) + (n + 1 : ℂ)) -
              1 / ((-z - a * I) + (n + 1 : ℂ))) := by
      exact summable_reciprocal_shift_difference_nat (u := -z + a * I) (v := -z - a * I)
        (hu := by
          intro n
          have hshift :
              z - a * I - (n + 1 : ℂ) ≠ 0 := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              integerComplement_add_ne_zero hz_sub (-(n + 1 : ℤ))
          intro hz0
          apply hshift
          calc
            z - a * I - (n + 1 : ℂ) = -((-z + a * I) + (n + 1 : ℂ)) := by ring
            _ = 0 := by simp [hz0])
        (hv := by
          intro n
          have hshift :
              z + a * I - (n + 1 : ℂ) ≠ 0 := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              integerComplement_add_ne_zero hz_add (-(n + 1 : ℤ))
          intro hz0
          apply hshift
          calc
            z + a * I - (n + 1 : ℂ) = -((-z - a * I) + (n + 1 : ℂ)) := by ring
            _ = 0 := by simp [hz0])
    -- Negating the auxiliary branch puts it into the exact `f (-(n + 1))` shape.
    have hneg_term :
        (fun n : ℕ ↦
          -(1 / ((-z + a * I) + (n + 1 : ℂ)) -
            1 / ((-z - a * I) + (n + 1 : ℂ)))) =
          (fun n : ℕ ↦ f (-(n + 1))) := by
      funext n
      have hx : -((-z + a * I) + (n + 1 : ℂ)) = z - (n + 1 : ℂ) - a * I := by
        ring
      have hy : -((-z - a * I) + (n + 1 : ℂ)) = z - (n + 1 : ℂ) + a * I := by
        ring
      have hx' : (-z + a * I) + (n + 1 : ℂ) = -(z - (n + 1 : ℂ) - a * I) := by
        ring
      have hy' : (-z - a * I) + (n + 1 : ℂ) = -(z - (n + 1 : ℂ) + a * I) := by
        ring
      calc
        -(1 / ((-z + a * I) + (n + 1 : ℂ)) -
            1 / ((-z - a * I) + (n + 1 : ℂ)))
            = 1 / (z - (n + 1 : ℂ) - a * I) -
                1 / (z - (n + 1 : ℂ) + a * I) := by
                  rw [sub_eq_add_neg, neg_add, neg_neg]
                  rw [hx', hy', one_div, one_div, inv_neg, inv_neg]
                  ring
        _ = f (-(n + 1)) := by
              simp [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    exact hneg_term ▸ haux.neg
  have hpair_tsum :
      (∑' n : ℕ, f (n + 1)) + ∑' n : ℕ, f (-(n + 1)) =
        π * (cot (π * (z - a * I)) - cot (π * (z + a * I))) - f 0 := by
    -- The paired branch sum is uniquely determined by the cotangent subtraction helper.
    exact (hf_pos.hasSum.add hf_neg.hasSum).unique hpair
  have hf : Summable f := Summable.of_add_one_of_neg_add_one hf_pos hf_neg
  -- Reassemble the full `ℤ`-indexed sum from the positive branch, the zero term, and the
  -- negative branch, then replace the cotangent difference by its closed form.
  refine (Summable.hasSum_iff hf).2 ?_
  calc
    ∑' n : ℤ, f n = (∑' n : ℕ, f (n + 1)) + f 0 + ∑' n : ℕ, f (-(n + 1)) := by
      exact tsum_of_add_one_of_neg_add_one hf_pos hf_neg
    _ = ((∑' n : ℕ, f (n + 1)) + ∑' n : ℕ, f (-(n + 1))) + f 0 := by
          ring
    _ = (π * (cot (π * (z - a * I)) - cot (π * (z + a * I))) - f 0) + f 0 := by
          rw [hpair_tsum]
    _ = π * (cot (π * (z - a * I)) - cot (π * (z + a * I))) := by
          ring
    _ = π * I * sinh (2 * π * a) /
          (sin (π * (z + a * I)) * sin (π * (z - a * I))) := by
          exact cotangent_shift_difference_eq_sinh_div_sin_mul_sin a z hz_add hz_sub

/-- Exercise 4 (2): if `a ≠ 0` and `z ± ai` avoid the integers, then the quadratic kernel
`n ↦ 1 / ((z + n)^2 + a^2)` has the stated integer-lattice sum
`(π / a) * sinh (2π a) / (cosh (2π a) - cos (2π z))`. -/
theorem exercise_4_quadratic_kernel_hasSum (a : ℝ) (z : ℂ) (ha : a ≠ 0)
    (hz_add : z + a * I ∈ ℂ_ℤ)
    (hz_sub : z - a * I ∈ ℂ_ℤ) :
    HasSum
      (fun n : ℤ ↦ 1 / ((z + n) ^ 2 + a ^ 2))
      ((π / a) * sinh (2 * π * a) / (cosh (2 * π * a) - cos (2 * π * z))) := by
  let f : ℤ → ℂ := fun n ↦ 1 / (z + n - a * I) - 1 / (z + n + a * I)
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast ha
  have htwo : (2 : ℂ) ≠ 0 := by
    norm_num
  have haI : (2 * a * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero htwo haC) I_ne_zero
  have hpartial := exercise_4_partial_fraction_hasSum a z hz_add hz_sub
  have hscaled := hpartial.mul_left (1 / (2 * a * I : ℂ))
  have hterm :
      (fun n : ℤ ↦ (1 / (2 * a * I : ℂ)) * f n) =
        (fun n : ℤ ↦ 1 / ((z + n) ^ 2 + a ^ 2)) := by
    funext n
    have hsub : z + n - a * I ≠ 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        integerComplement_add_ne_zero hz_sub n
    have hadd : z + n + a * I ≠ 0 := by
      simpa [add_assoc, add_left_comm, add_comm] using
        integerComplement_add_ne_zero hz_add n
    -- Route correction: theorem (2) is obtained by scaling theorem (1) termwise, not by a second
    -- independent convergence argument.
    calc
      (1 / (2 * a * I : ℂ)) * f n
          = (1 / (2 * a * I : ℂ)) *
              ((2 * a * I) / ((z + n) ^ 2 + a ^ 2)) := by
                rw [show f n =
                  1 / (z + n - a * I) - 1 / (z + n + a * I) by rfl]
                rw [reciprocal_shift_difference_eq_quadratic_kernel a z n hsub hadd]
      _ = ((1 / (2 * a * I : ℂ)) * (2 * a * I)) * (((z + n) ^ 2 + a ^ 2)⁻¹) := by
            rw [div_eq_mul_inv]
            ring
      _ = 1 / ((z + n) ^ 2 + a ^ 2) := by
            have hcancel : (1 / (2 * a * I : ℂ)) * (2 * a * I) = 1 := by
              field_simp [haC, I_ne_zero]
            rw [hcancel, one_mul, one_div]
  have hsin_add : sin (π * (z + a * I)) ≠ 0 := by
    simpa using sin_pi_mul_ne_zero (x := z + a * I) hz_add
  have hsin_sub : sin (π * (z - a * I)) ≠ 0 := by
    simpa using sin_pi_mul_ne_zero (x := z - a * I) hz_sub
  have hden : (cosh (2 * π * a) - cos (2 * π * z) : ℂ) ≠ 0 := by
    intro hzero
    have hprod_zero :
        sin (π * (z + a * I)) * sin (π * (z - a * I)) = 0 := by
      rw [sin_shift_product_eq_cosh_sub_cos_half a z, hzero]
      simp
    exact (mul_ne_zero hsin_add hsin_sub) hprod_zero
  have hvalue :
      (1 / (2 * a * I : ℂ)) *
          (π * I * sinh (2 * π * a) /
            (sin (π * (z + a * I)) * sin (π * (z - a * I)))) =
        ((π / a) * sinh (2 * π * a) /
          (cosh (2 * π * a) - cos (2 * π * z))) := by
    -- Replace the sine product by `(cosh - cos) / 2`, then cancel the scalar `2 a i`.
    rw [sin_shift_product_eq_cosh_sub_cos_half a z]
    have haux : (2 * a * I : ℂ) ≠ 0 := haI
    field_simp [haC, hden, I_ne_zero, haux]
  have hscaled_term :
      HasSum (fun n : ℤ ↦ 1 / ((z + n) ^ 2 + a ^ 2))
        ((π / a) * sinh (2 * π * a) / (cosh (2 * π * a) - cos (2 * π * z))) := by
    -- Transport theorem (1) through the termwise quadratic-kernel identity and the closed-form
    -- denominator rewrite.
    exact hvalue ▸ (hscaled.congr_fun (fun n ↦ (congrFun hterm n).symm))
  exact hscaled_term
