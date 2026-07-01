import cartan.V.section19.«0006_Example_3»
import cartan.V.section19.«0007_Example_4»
import cartan.V.section19.«0005_Proposition_2_1»
import cartan.V.section20.«0004_Theorem_2»
import cartan.V.section20.«0005_Example_V_3_extra_3»
import cartan.V.section21.«0013_Exercise_4»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: these are source-facing complex-analysis identities over ordered range partial
-- sums/products, matching the textbook's `n ≥ 1` expansions. Relevant upstream owners in the local
-- project and mathlib are `alternating_cosecant_partial_fraction_hasSum`,
-- `cotangent_partial_fraction_hasSum`, `Real.tendsto_sum_pi_div_four`, and
-- `complex_sin_eq_pi_mul_tprod_one_sub_sq_div_nat_sq`.

open Complex
open Equiv
open scoped Real BigOperators Topology

local notation "ℂ_ℤ" => integerComplement

/-- Helper for Exercise 5: a finite sum of successive differences telescopes to the boundary
terms. -/
lemma sum_range_successive_difference (f : ℕ → ℂ) :
    ∀ N : ℕ, ∑ n ∈ Finset.range N, (f n - f (n + 1)) = f 0 - f N
  | 0 => by
      -- The empty-range boundary identity is immediate.
      simp
  | N + 1 => by
      -- Peel off the last summand and use the induction hypothesis on the initial segment.
      rw [Finset.sum_range_succ, sum_range_successive_difference f N]
      ring

/-- Helper for Exercise 5: the reciprocal of a fixed complex shift of the naturals tends to `0`.
-/
lemma tendsto_reciprocal_add_nat_zero (w : ℂ) :
    Filter.Tendsto (fun N : ℕ ↦ 1 / (w + N)) Filter.atTop (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hnorm_atTop : Filter.Tendsto (fun N : ℕ ↦ ‖w + N‖) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun b ↦ ?_
    have hnat :
        ∀ᶠ N : ℕ in Filter.atTop, b + ‖w‖ ≤ (N : ℝ) := by
      exact (Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop (b + ‖w‖))
    filter_upwards [hnat] with N hN
    have htriangle : (N : ℝ) ≤ ‖w + N‖ + ‖w‖ := by
      calc
        (N : ℝ) = ‖(N : ℂ)‖ := by simpa using (Complex.norm_natCast N).symm
        _ = ‖(w + N) + (-w)‖ := by ring_nf
        _ ≤ ‖w + N‖ + ‖-w‖ := norm_add_le _ _
        _ = ‖w + N‖ + ‖w‖ := by simp
    linarith
  -- After controlling the norm from below by a linear function, inversion sends it to `0`.
  simpa [one_div, norm_inv] using (tendsto_inv_atTop_zero.comp hnorm_atTop)

/-- Helper for Exercise 5: the alternating shifted reciprocal has the same norm tail as the
ordinary shifted reciprocal, hence also tends to `0`. -/
lemma tendsto_alternating_reciprocal_add_nat_zero (w : ℂ) :
    Filter.Tendsto (fun N : ℕ ↦ (-1 : ℂ) ^ N / (w + N)) Filter.atTop (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  -- The alternating sign has unit norm, so only the shifted reciprocal tail matters.
  simpa [norm_div] using
    (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_reciprocal_add_nat_zero w))

/-- Helper for Exercise 5: after the half-integer shift `w = 1 / 2 - z`, the quadratic
denominator factors into the two linear poles used in the source proof. -/
lemma half_shift_denominator_factorization (z : ℂ) (n : ℕ) :
    ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) =
      -(((1 / 2 - z : ℂ) + n) * (((1 / 2 - z : ℂ) - (n + 1)))) := by
  -- This is the basic algebraic bridge from the textbook's half-shift to Lean's kernels.
  ring

/-- Helper for Exercise 5: the quarter-shift cosine kernel has the expected normalized numerator
after clearing the odd square denominator. -/
lemma quarter_shift_kernel_numerator_eq (z : ℂ) (n : ℕ) :
    1 - 4 * ((z + 1) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2 =
      (((4 * n + 1 : ℂ) - z) * ((4 * n + 3 : ℂ) + z)) / (4 * (2 * n + 1 : ℂ) ^ 2) := by
  -- This identifies the paired linear factors with the shifted odd cosine-product kernel.
  have hone : (2 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  field_simp [hone]
  ring_nf

/-- Helper for Exercise 5: the normalizing quarter-shift denominator is the odd-index scalar
factor appearing at `z = 1 / 4`. -/
lemma quarter_shift_kernel_denominator_eq (n : ℕ) :
    1 - 4 * ((1 : ℂ) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2 =
      ((4 * n + 1 : ℂ) * (4 * n + 3 : ℂ)) / (4 * (2 * n + 1 : ℂ) ^ 2) := by
  -- This is the scalar denominator needed to normalize the quarter-shift product pairwise.
  have hone : (2 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  field_simp [hone]
  ring_nf

/-- Helper for Exercise 5: the half-shift cosine summand splits into the transported alternating
cosecant term and a telescoping boundary correction. -/
-- TODO: Rewrite the alternating term as paired simple poles, cancel the shared boundary pole, and
-- finish with `one_div_sub_one_div` plus `half_shift_denominator_factorization`.
lemma pi_div_cos_half_shift_term_eq {z : ℂ} (hz : 1 / 2 - z ∈ ℂ_ℤ) (n : ℕ) :
    ((-1 : ℂ) ^ n * (2 * n + 1 : ℂ)) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) =
      alternating_cosecant_partial_fraction_term n.succPNat (1 / 2 - z) +
        (((-1 : ℂ) ^ n) / ((1 / 2 - z : ℂ) + n) -
          ((-1 : ℂ) ^ (n + 1)) / ((1 / 2 - z : ℂ) + (n + 1))) := by
  let w : ℂ := 1 / 2 - z
  have hsub :
      w - (n.succPNat : ℂ) ≠ 0 := by
    -- The shifted pole `w - (n + 1)` stays off the integers because `w ∈ ℂ_ℤ`.
    simpa [w, Equiv.pnatEquivNat, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      integerComplement_add_ne_zero hz (-(n + 1 : ℤ))
  have hadd :
      w + (n.succPNat : ℂ) ≠ 0 := by
    -- The reflected pole `w + (n + 1)` is excluded for the same reason.
    simpa [w, Equiv.pnatEquivNat, add_assoc, add_left_comm, add_comm] using
      integerComplement_add_ne_zero hz (n + 1 : ℤ)
  have hleft :
      w + n ≠ 0 := by
    -- The boundary pole at `w + n` is the remaining nonzero denominator in the telescoping tail.
    simpa [w, add_assoc, add_left_comm, add_comm] using integerComplement_add_ne_zero hz (n : ℤ)
  have hterm :
      alternating_cosecant_partial_fraction_term n.succPNat w =
        (-1 : ℂ) ^ (n + 1) * (1 / (w - (n + 1 : ℂ)) + 1 / (w + (n + 1 : ℂ))) := by
    -- Expand the imported alternating simple-pole term at the half-shifted point.
    simpa [w, Equiv.pnatEquivNat] using
      alternating_cosecant_partial_fraction_term_eq n.succPNat hsub hadd
  have hpow : (-1 : ℂ) ^ (n + 1) = -((-1 : ℂ) ^ n) := by
    -- The alternating sign is separated so the shared boundary pole cancels explicitly.
    rw [pow_succ]
    ring
  have hw : w = 1 / 2 - z := rfl
  have hcombine :
      ((-1 : ℂ) ^ n * (2 * n + 1 : ℂ)) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) =
        (-1 : ℂ) ^ n * (1 / (w + n) - 1 / (w - (n + 1 : ℂ))) := by
    have hfactor :
        ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) = -((w + n) * (w - (n + 1 : ℂ))) := by
      simpa [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        half_shift_denominator_factorization z n
    -- Clear denominators only after the shared boundary pole has been isolated.
    rw [hfactor]
    field_simp [hleft, hsub]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    let a : ℂ := w - (n + 1 : ℂ)
    have ha : a ≠ 0 := by
      dsimp [a]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have ha_mul : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
    calc
      -((2 * (n : ℂ) + 1) * a⁻¹) = a * a⁻¹ - (w + n) * a⁻¹ := by
        dsimp [a]
        ring
      _ = 1 - (w + n) * a⁻¹ := by rw [ha_mul]
  have hmain :
      ((-1 : ℂ) ^ n * (2 * n + 1 : ℂ)) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) =
        alternating_cosecant_partial_fraction_term n.succPNat w +
          (((-1 : ℂ) ^ n) / (w + n) - ((-1 : ℂ) ^ (n + 1)) / (w + (n + 1 : ℂ))) := by
    calc
      ((-1 : ℂ) ^ n * (2 * n + 1 : ℂ)) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2)
          = (-1 : ℂ) ^ n * (1 / (w + n) - 1 / (w - (n + 1 : ℂ))) := hcombine
      _ = (-1 : ℂ) ^ (n + 1) * (1 / (w - (n + 1 : ℂ)) + 1 / (w + (n + 1 : ℂ))) +
            (((-1 : ℂ) ^ n) / (w + n) - ((-1 : ℂ) ^ (n + 1)) / (w + (n + 1 : ℂ))) := by
              -- After cancelling the common `w + (n + 1)` pole, the remaining terms match exactly.
              rw [hpow]
              ring
      _ = alternating_cosecant_partial_fraction_term n.succPNat w +
            (((-1 : ℂ) ^ n) / (w + n) - ((-1 : ℂ) ^ (n + 1)) / (w + (n + 1 : ℂ))) := by
              rw [hterm]
  simpa [w] using hmain

/-- Helper for Exercise 5: the half-shift tangent summand splits into the transported cotangent
term and a telescoping reciprocal difference. -/
-- TODO: Rewrite the cotangent term as paired simple poles, combine the remaining poles with
-- `one_div_add_one_div`, and then map the denominator through the half-shift factorization.
lemma pi_tan_half_shift_term_eq {z : ℂ} (hz : 1 / 2 - z ∈ ℂ_ℤ) (n : ℕ) :
    (2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) =
      cotangent_partial_fraction_term n.succPNat (1 / 2 - z) +
        (1 / ((1 / 2 - z : ℂ) + n) - 1 / ((1 / 2 - z : ℂ) + (n + 1))) := by
  let w : ℂ := 1 / 2 - z
  have hsub :
      w - (n.succPNat : ℂ) ≠ 0 := by
    -- The half-shifted pole at `w - (n + 1)` is excluded by `w ∈ ℂ_ℤ`.
    simpa [w, Equiv.pnatEquivNat, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      integerComplement_add_ne_zero hz (-(n + 1 : ℤ))
  have hadd :
      w + (n.succPNat : ℂ) ≠ 0 := by
    -- The reflected pole `w + (n + 1)` is excluded as well.
    simpa [w, Equiv.pnatEquivNat, add_assoc, add_left_comm, add_comm] using
      integerComplement_add_ne_zero hz (n + 1 : ℤ)
  have hleft :
      w + n ≠ 0 := by
    -- The boundary pole `w + n` is the only extra denominator after the cancellation step.
    simpa [w, add_assoc, add_left_comm, add_comm] using integerComplement_add_ne_zero hz (n : ℤ)
  have hterm :
      cotangent_partial_fraction_term n.succPNat w =
        1 / (w - (n + 1 : ℂ)) + 1 / (w + (n + 1 : ℂ)) := by
    -- Expand the cotangent summand into its two simple poles.
    simpa [w, Equiv.pnatEquivNat] using cotangent_partial_fraction_term_eq n.succPNat hsub hadd
  have hw : w = 1 / 2 - z := rfl
  have hcombine :
      (2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) =
        1 / (w - (n + 1 : ℂ)) + 1 / (w + n) := by
    have hfactor :
        ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) = -((w + n) * (w - (n + 1 : ℂ))) := by
      simpa [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        half_shift_denominator_factorization z n
    -- Clear denominators after rewriting the quadratic kernel in half-shifted form.
    rw [hfactor]
    field_simp [hsub, hleft]
    have hz_of_w : z = 1 / 2 - w := by
      rw [hw]
      ring
    rw [hz_of_w]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    let a : ℂ := w - (n + 1 : ℂ)
    have ha : a ≠ 0 := by
      dsimp [a]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have ha_mul : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
    calc
      -((2 : ℂ) * (1 / 2 - w) * a⁻¹) = a * a⁻¹ + (w + n) * a⁻¹ := by
        dsimp [a]
        ring
      _ = 1 + (w + n) * a⁻¹ := by rw [ha_mul]
      _ = (w + n) * a⁻¹ + 1 := by ring
  have hmain :
      (2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) =
        cotangent_partial_fraction_term n.succPNat w +
          (1 / (w + n) - 1 / (w + (n + 1 : ℂ))) := by
    calc
      (2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2)
          = 1 / (w - (n + 1 : ℂ)) + 1 / (w + n) := hcombine
      _ = (1 / (w - (n + 1 : ℂ)) + 1 / (w + (n + 1 : ℂ))) +
            (1 / (w + n) - 1 / (w + (n + 1 : ℂ))) := by
              -- Cancel the shared `w + (n + 1)` pole against the boundary correction.
              ring
      _ = cotangent_partial_fraction_term n.succPNat w +
            (1 / (w + n) - 1 / (w + (n + 1 : ℂ))) := by
              rw [hterm]
  simpa [w] using hmain

/-- Exercise 5 (1): the partial-fraction expansion of `π / cos (π z)` away from its poles. -/
theorem pi_div_cos_pi_mul_hasSum
    {z : ℂ}
    (hz : 1 / 2 - z ∈ ℂ_ℤ) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∑ n ∈ Finset.range N,
          ((-1 : ℂ) ^ n * (2 * n + 1 : ℂ)) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2))
      Filter.atTop (𝓝 (π / cos (π * z))) := by
  let w : ℂ := 1 / 2 - z
  have hw : w ∈ ℂ_ℤ := hz
  have hmain :
      HasSum (fun n : ℕ ↦ alternating_cosecant_partial_fraction_term n.succPNat w)
        (π / sin (π * w) - 1 / w) := by
    -- Reindex Example 4 from `ℕ+` to `ℕ` so its partial sums match `Finset.range`.
    simpa [w, Function.comp_def, Equiv.pnatEquivNat] using
      (Equiv.pnatEquivNat.symm.hasSum_iff).2
        (alternating_cosecant_partial_fraction_hasSum hw)
  have hcorr :
      Filter.Tendsto
        (fun N : ℕ ↦
          ∑ n ∈ Finset.range N,
            (((-1 : ℂ) ^ n) / (w + n) - ((-1 : ℂ) ^ (n + 1)) / (w + (n + 1))))
        Filter.atTop (𝓝 (1 / w)) := by
    have hclosed :
        ∀ N : ℕ,
          ∑ n ∈ Finset.range N,
              (((-1 : ℂ) ^ n) / (w + n) - ((-1 : ℂ) ^ (n + 1)) / (w + (n + 1))) =
            1 / w - ((-1 : ℂ) ^ N) / (w + N) := by
      intro N
      -- The correction is a plain telescoping difference for the boundary term `(-1)^n / (w + n)`.
      simpa using
        (sum_range_successive_difference (fun n : ℕ ↦ ((-1 : ℂ) ^ n) / (w + n)) N)
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ (hclosed N).symm) ?_
    simpa using (tendsto_const_nhds.sub (tendsto_alternating_reciprocal_add_nat_zero w))
  have hsplit :
      (fun N : ℕ ↦
        ∑ n ∈ Finset.range N,
          ((-1 : ℂ) ^ n * (2 * n + 1 : ℂ)) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2)) =
        fun N : ℕ ↦
          (∑ n ∈ Finset.range N, alternating_cosecant_partial_fraction_term n.succPNat w) +
            ∑ n ∈ Finset.range N,
              (((-1 : ℂ) ^ n) / (w + n) - ((-1 : ℂ) ^ (n + 1)) / (w + (n + 1))) := by
    funext N
    -- Split each textbook summand into the imported alternating term and the boundary correction.
    simp_rw [w, pi_div_cos_half_shift_term_eq hz]
    rw [Finset.sum_add_distrib]
  have hlimit :
      Filter.Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range N, alternating_cosecant_partial_fraction_term n.succPNat w) +
            ∑ n ∈ Finset.range N,
              (((-1 : ℂ) ^ n) / (w + n) - ((-1 : ℂ) ^ (n + 1)) / (w + (n + 1))))
        Filter.atTop (𝓝 ((π / sin (π * w) - 1 / w) + 1 / w)) :=
    hmain.tendsto_sum_nat.add hcorr
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ (congrFun hsplit N).symm) ?_
  have hsin : sin (π * w) = cos (π * z) := by
    -- The half-period shift turns the sine denominator into the cosine denominator.
    calc
      sin (π * w) = sin (-π * z + π / 2) := by
        simp [w]
        ring_nf
      _ = cos (-π * z) := by rw [Complex.sin_add_pi_div_two]
      _ = cos (π * z) := by simpa using Complex.cos_neg (π * z)
  simpa [h, hsin] using hlimit
where
  h (w : ℂ) : (π / sin (π * w) - 1 / w) + 1 / w = π / sin (π * w) := by
    ring

/-- Exercise 5 (2): the partial-fraction expansion of `π tan (π z)` away from the poles of
`tan (π z)`. -/
theorem pi_tan_pi_mul_hasSum
    {z : ℂ}
    (hz : 1 / 2 - z ∈ ℂ_ℤ) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∑ n ∈ Finset.range N, (2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2))
      Filter.atTop (𝓝 (π * tan (π * z))) := by
  let w : ℂ := 1 / 2 - z
  have hw : w ∈ ℂ_ℤ := hz
  have hmain :
      HasSum (fun n : ℕ ↦ cotangent_partial_fraction_term n.succPNat w)
        (π / tan (π * w) - 1 / w) := by
    -- Reindex Example 3 from `ℕ+` to `ℕ` so its partial sums use `Finset.range`.
    simpa [w, Function.comp_def, Equiv.pnatEquivNat] using
      (Equiv.pnatEquivNat.symm.hasSum_iff).2 (cotangent_partial_fraction_hasSum hw)
  have hcorr :
      Filter.Tendsto
        (fun N : ℕ ↦
          ∑ n ∈ Finset.range N, (1 / (w + n) - 1 / (w + (n + 1))))
        Filter.atTop (𝓝 (1 / w)) := by
    have hclosed :
        ∀ N : ℕ,
          ∑ n ∈ Finset.range N, (1 / (w + n) - 1 / (w + (n + 1))) = 1 / w - 1 / (w + N) := by
      intro N
      -- The cotangent correction telescopes without the alternating sign.
      simpa using (sum_range_successive_difference (fun n : ℕ ↦ 1 / (w + n)) N)
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ (hclosed N).symm) ?_
    simpa using (tendsto_const_nhds.sub (tendsto_reciprocal_add_nat_zero w))
  have hsplit :
      (fun N : ℕ ↦
        ∑ n ∈ Finset.range N, (2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2)) =
        fun N : ℕ ↦
          (∑ n ∈ Finset.range N, cotangent_partial_fraction_term n.succPNat w) +
            ∑ n ∈ Finset.range N, (1 / (w + n) - 1 / (w + (n + 1))) := by
    funext N
    -- Split each textbook summand into the imported cotangent term and the telescoping boundary.
    simp_rw [w, pi_tan_half_shift_term_eq hz]
    rw [Finset.sum_add_distrib]
  have hlimit :
      Filter.Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range N, cotangent_partial_fraction_term n.succPNat w) +
            ∑ n ∈ Finset.range N, (1 / (w + n) - 1 / (w + (n + 1))))
        Filter.atTop (𝓝 ((π / tan (π * w) - 1 / w) + 1 / w)) :=
    hmain.tendsto_sum_nat.add hcorr
  have hsin : sin (π * w) = cos (π * z) := by
    -- The half-period shift swaps the sine and cosine factors.
    calc
      sin (π * w) = sin (-π * z + π / 2) := by
        simp [w]
        ring_nf
      _ = cos (-π * z) := by rw [Complex.sin_add_pi_div_two]
      _ = cos (π * z) := by simpa using Complex.cos_neg (π * z)
  have hcos : cos (π * w) = sin (π * z) := by
    -- The same shift turns the cosine numerator into the sine numerator.
    calc
      cos (π * w) = cos (-π * z + π / 2) := by
        simp [w]
        ring_nf
      _ = -sin (-π * z) := by rw [Complex.cos_add_pi_div_two]
      _ = -(-sin (π * z)) := by simpa using congrArg Neg.neg (Complex.sin_neg (π * z))
      _ = sin (π * z) := by ring
  have hvalue : (π / tan (π * w) - 1 / w) + 1 / w = π * tan (π * z) := by
    have hcot (u : ℂ) : π / tan (π * u) = π * cot (π * u) := by
      calc
        π / tan (π * u) = π * (tan (π * u))⁻¹ := by rw [div_eq_mul_inv]
        _ = π * ((cot (π * u))⁻¹)⁻¹ := by rw [← cot_inv_eq_tan]
        _ = π * cot (π * u) := by simp
    calc
      (π / tan (π * w) - 1 / w) + 1 / w = π / tan (π * w) := by ring
      _ = π * cot (π * w) := hcot w
      _ = π * tan (π * z) := by rw [Complex.cot, Complex.tan, hcos, hsin]
  have hvalue' : π / tan (π * w) = π * tan (π * z) := by
    simpa using hvalue
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ (congrFun hsplit N).symm) ?_
  simpa [hvalue'] using hlimit

/-- Exercise 5 (3): the Leibniz series for `π / 4`. -/
theorem pi_div_four_hasSum_alternating_odd_reciprocals :
    Filter.Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (2 * n + 1))
      Filter.atTop (𝓝 (π / 4)) := by
  -- This is exactly mathlib's Leibniz-series limit for `π / 4`.
  simpa using Real.tendsto_sum_pi_div_four

/-- Helper for Exercise 5: on the half-integer-complement domain, the quadratic odd denominator
never vanishes. -/
lemma half_shift_denominator_ne_zero {z : ℂ} (hz : 1 / 2 - z ∈ ℂ_ℤ) (n : ℕ) :
    ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) ≠ 0 := by
  let w : ℂ := 1 / 2 - z
  have hleft : w + n ≠ 0 := by
    -- The translated half-integer lattice excludes the left linear factor.
    simpa [w, add_assoc, add_left_comm, add_comm] using integerComplement_add_ne_zero hz (n : ℤ)
  have hsub : w - (n + 1 : ℂ) ≠ 0 := by
    -- The same domain exclusion removes the reflected linear factor.
    simpa [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      integerComplement_add_ne_zero hz (-(n + 1 : ℤ))
  have hfactor :
      ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) = -((w + n) * (w - (n + 1 : ℂ))) := by
    -- Route correction: the source proof works through the half-shifted linear factors, so we
    -- keep that factorization explicit instead of unfolding the quadratic kernel repeatedly.
    simpa [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      half_shift_denominator_factorization z n
  rw [hfactor]
  exact neg_ne_zero.mpr (mul_ne_zero hleft hsub)

/-- Helper for Exercise 5: every odd cosine-product factor is nonzero away from the half-integer
lattice. -/
lemma cos_kernel_factor_ne_zero {z : ℂ} (hz : 1 / 2 - z ∈ ℂ_ℤ) (n : ℕ) :
    1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2 ≠ 0 := by
  have hodd : (2 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  have hquad : ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) ≠ 0 := half_shift_denominator_ne_zero hz n
  have hrewrite :
      1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2 =
        (4 : ℂ) * (((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) / (2 * n + 1 : ℂ) ^ 2) := by
    -- Rewrite the odd kernel so its zero set is governed by the same quadratic denominator.
    field_simp [hodd]
    ring
  rw [hrewrite]
  exact mul_ne_zero (by norm_num) (div_ne_zero hquad (pow_ne_zero 2 hodd))

/-- Helper for Exercise 5: on the half-integer-complement domain, the logarithmic derivative of a
single odd cosine kernel is the textbook partial-fraction summand from part (2). -/
lemma logDeriv_cos_kernel_factor {z : ℂ} (hz : 1 / 2 - z ∈ ℂ_ℤ) (n : ℕ) :
    logDeriv (fun w : ℂ ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2) z =
      -(2 * z) / (((n + 1 / 2 : ℂ) ^ 2) - z ^ 2) := by
  have hodd : (2 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  have hkernel : 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2 ≠ 0 := cos_kernel_factor_ne_zero hz n
  have hquad : ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) ≠ 0 := half_shift_denominator_ne_zero hz n
  have hderiv :
      deriv (fun w : ℂ ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2) z =
        -(8 * z) / (2 * n + 1 : ℂ) ^ 2 := by
    -- Differentiate the single factor first; the half-shift algebra is handled afterwards.
    have hderivAt :
        HasDerivAt
          (fun w : ℂ ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2)
          (-(8 * z) / (2 * n + 1 : ℂ) ^ 2) z := by
      convert ((((hasDerivAt_id z).pow 2).const_mul (-(4 : ℂ) / (2 * n + 1 : ℂ) ^ 2)).const_add
        (1 : ℂ)) using 1
      · ext w
        simp only [Pi.pow_apply, id_eq]
        field_simp [hodd]
        ring
      · field_simp [hodd]
        ring_nf
        simp [id_eq]
    simpa using hderivAt.deriv
  rw [logDeriv_apply, hderiv]
  -- Now clear denominators and rewrite to the common quadratic kernel from the source proof.
  field_simp [hodd, hkernel, hquad]
  ring

/-- Helper for Exercise 5: the half-shift telescoping correction from the tangent expansion is
absolutely summable. -/
lemma half_shift_reciprocal_difference_summable {z : ℂ} (hz : 1 / 2 - z ∈ ℂ_ℤ) :
    Summable
      (fun n : ℕ ↦
        1 / ((1 / 2 - z : ℂ) + n) - 1 / ((1 / 2 - z : ℂ) + (n + 1))) := by
  let w : ℂ := 1 / 2 - z
  have hleft : ∀ n : ℕ, (w - 1) + (n + 1 : ℂ) ≠ 0 := by
    intro n
    -- Reindex the earlier reciprocal-difference estimate so the first denominator is `w + n`.
    simpa [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      integerComplement_add_ne_zero hz (n : ℤ)
  have hright : ∀ n : ℕ, w + (n + 1 : ℂ) ≠ 0 := by
    intro n
    -- The second denominator is the next boundary pole in the same half-shifted lattice.
    simpa [w, add_assoc, add_left_comm, add_comm] using
      integerComplement_add_ne_zero hz (n + 1 : ℤ)
  simpa [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    summable_reciprocal_shift_difference_nat (u := w - 1) (v := w) hleft hright

/-- Helper for Exercise 5: the half-shift telescoping reciprocal correction has the expected
boundary sum `1 / (1 / 2 - z)`. -/
lemma half_shift_reciprocal_difference_hasSum {z : ℂ} (hz : 1 / 2 - z ∈ ℂ_ℤ) :
    HasSum
      (fun n : ℕ ↦
        1 / ((1 / 2 - z : ℂ) + n) - 1 / ((1 / 2 - z : ℂ) + (n + 1)))
      (1 / (1 / 2 - z : ℂ)) := by
  let w : ℂ := 1 / 2 - z
  have hsummable :
      Summable (fun n : ℕ ↦ 1 / (w + n) - 1 / (w + (n + 1 : ℂ))) := by
    simpa [w] using half_shift_reciprocal_difference_summable hz
  apply (Summable.hasSum_iff_tendsto_nat hsummable).mpr
  have hclosed :
      ∀ N : ℕ,
        ∑ n ∈ Finset.range N, (1 / (w + n) - 1 / (w + (n + 1 : ℂ))) = 1 / w - 1 / (w + N) := by
    intro N
    -- The correction is the same telescoping boundary term already used in part (2).
    simpa using (sum_range_successive_difference (fun n : ℕ ↦ 1 / (w + n)) N)
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ (hclosed N).symm) ?_
  -- The boundary tail `1 / (w + N)` vanishes, leaving exactly the residue `1 / w`.
  simpa [w] using (tendsto_const_nhds.sub (tendsto_reciprocal_add_nat_zero w))

/-- Helper for Exercise 5: on the half-integer-complement domain, the logarithmic derivatives of
the odd cosine factors sum to the logarithmic derivative of `cos (π z)`. -/
lemma cos_kernel_logDeriv_hasSum_on_half_shift_domain {z : ℂ}
    (hz : 1 / 2 - z ∈ ℂ_ℤ) :
    HasSum
      (fun n : ℕ ↦ logDeriv (fun w : ℂ ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2) z)
      (-(π * tan (π * z))) := by
  let w : ℂ := 1 / 2 - z
  have hcot :
      HasSum (fun n : ℕ ↦ cotangent_partial_fraction_term n.succPNat w)
        (π / tan (π * w) - 1 / w) := by
    -- Reindex Example 3 from `ℕ+` to `ℕ` so the source splitting matches `Finset.range`.
    simpa [w, Function.comp_def, Equiv.pnatEquivNat] using
      (Equiv.pnatEquivNat.symm.hasSum_iff).2 (cotangent_partial_fraction_hasSum hz)
  have hcorr :
      HasSum (fun n : ℕ ↦ 1 / (w + n) - 1 / (w + (n + 1 : ℂ))) (1 / w) := by
    -- Package the telescoping correction in the canonical `HasSum` form.
    simpa [w] using half_shift_reciprocal_difference_hasSum hz
  have hsplit :
      (fun n : ℕ ↦ (2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2)) =
        fun n : ℕ ↦
          cotangent_partial_fraction_term n.succPNat w +
            (1 / (w + n) - 1 / (w + (n + 1 : ℂ))) := by
    funext n
    -- Use the already-verified half-shift decomposition term by term.
    simpa [w] using pi_tan_half_shift_term_eq hz n
  have htangent_raw :
      HasSum
        (fun n : ℕ ↦ (2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2))
        ((π / tan (π * w) - 1 / w) + 1 / w) := by
    -- The textbook tangent series is the cotangent series plus the telescoping correction.
    refine hsplit ▸ hcot.add hcorr
  have hsin : sin (π * w) = cos (π * z) := by
    -- The half-period shift swaps the sine denominator with the cosine denominator.
    calc
      sin (π * w) = sin (-π * z + π / 2) := by
        simp [w]
        ring_nf
      _ = cos (-π * z) := by rw [Complex.sin_add_pi_div_two]
      _ = cos (π * z) := by simpa using Complex.cos_neg (π * z)
  have hcos : cos (π * w) = sin (π * z) := by
    -- The same shift turns the cotangent numerator into the sine numerator.
    calc
      cos (π * w) = cos (-π * z + π / 2) := by
        simp [w]
        ring_nf
      _ = -sin (-π * z) := by rw [Complex.cos_add_pi_div_two]
      _ = -(-sin (π * z)) := by simpa using congrArg Neg.neg (Complex.sin_neg (π * z))
      _ = sin (π * z) := by ring
  have hvalue :
      ((π / tan (π * w) - 1 / w) + 1 / w) = π * tan (π * z) := by
    have hcot_eq (u : ℂ) : π / tan (π * u) = π * cot (π * u) := by
      calc
        π / tan (π * u) = π * (tan (π * u))⁻¹ := by rw [div_eq_mul_inv]
        _ = π * ((cot (π * u))⁻¹)⁻¹ := by rw [← cot_inv_eq_tan]
        _ = π * cot (π * u) := by simp
    calc
      ((π / tan (π * w) - 1 / w) + 1 / w) = π / tan (π * w) := by ring
      _ = π * cot (π * w) := hcot_eq w
      _ = π * tan (π * z) := by rw [Complex.cot, Complex.tan, hcos, hsin]
  have htangent :
      HasSum
        (fun n : ℕ ↦ (2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2))
        (π * tan (π * z)) := by
    exact hvalue ▸ htangent_raw
  have hneg_terms :
      (fun n : ℕ ↦ -((2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2))) =
        (fun n : ℕ ↦ -(2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2)) := by
    funext n
    rw [neg_div]
  -- `logDeriv_cos_kernel_factor` identifies each factor derivative with the negative tangent
  -- summand, so the whole series is the negative of the tangent expansion.
  exact (show
      HasSum
        (fun n : ℕ ↦ logDeriv (fun w : ℂ ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2) z)
        (-(π * tan (π * z))) from by
      rw [show
          (fun n : ℕ ↦ logDeriv (fun w : ℂ ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2) z) =
            (fun n : ℕ ↦ -(2 * z) / ((n + 1 / 2 : ℂ) ^ 2 - z ^ 2) ) by
            funext n
            rw [logDeriv_cos_kernel_factor hz]]
      rw [← hneg_terms]
      exact htangent.neg)

/-- Helper for Exercise 5: the half-integer complement domain is preconnected, just like the
integer complement after the affine shift `z ↦ 1 / 2 - z`. -/
lemma half_shift_integer_complement_isPreconnected :
    IsPreconnected {z : ℂ | 1 / 2 - z ∈ ℂ_ℤ} := by
  have hcount : (Set.range fun n : ℤ ↦ (1 / 2 : ℂ) - n).Countable := Set.countable_range _
  have hpath :
      IsPathConnected (((Set.range fun n : ℤ ↦ (1 / 2 : ℂ) - n)ᶜ : Set ℂ)) :=
    hcount.isPathConnected_compl_of_one_lt_rank (by
      simp only [Complex.rank_real_complex, Nat.one_lt_ofNat])
  have hset :
      {z : ℂ | 1 / 2 - z ∈ ℂ_ℤ} =
        (((Set.range fun n : ℤ ↦ (1 / 2 : ℂ) - n)ᶜ : Set ℂ)) := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, Complex.mem_integerComplement_iff]
    constructor
    · intro hz
      rintro ⟨n, hn⟩
      exact hz ⟨n, by rw [← hn]; ring⟩
    · intro hz
      rintro ⟨n, hn⟩
      exact hz ⟨n, by
        rw [hn]
        ring⟩
  rw [hset]
  exact hpath.isConnected.isPreconnected

/-- Helper for Exercise 5: leaving the shifted integer-complement domain forces `z` to be an odd
half-integer. -/
lemma half_shift_not_mem_integerComplement_iff_exists_half_integer {z : ℂ}
    (hz : ¬ (1 / 2 - z ∈ ℂ_ℤ)) :
    ∃ m : ℤ, z = (((2 * m + 1 : ℤ) : ℂ) / 2) := by
  classical
  rw [Complex.mem_integerComplement_iff] at hz
  push Not at hz
  rcases hz with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  -- Solve the excluded-domain witness `k = 1 / 2 - z` for `z` and package it as an odd
  -- half-integer.
  calc
    z = (1 / 2 : ℂ) - (k : ℂ) := by
      rw [hk]
      ring
    _ = (((2 * (-k) + 1 : ℤ) : ℂ) / 2) := by
      norm_num
      ring

/-- Helper for Exercise 5: outside the shifted integer-complement domain, `z` is a half-integer,
so `cos (π z)` vanishes. -/
lemma cos_pi_mul_eq_zero_of_not_half_shift_domain {z : ℂ}
    (hz : ¬ (1 / 2 - z ∈ ℂ_ℤ)) :
    cos (π * z) = 0 := by
  rcases half_shift_not_mem_integerComplement_iff_exists_half_integer hz with ⟨m, hm⟩
  rw [Complex.cos_eq_zero_iff]
  refine ⟨m, ?_⟩
  -- The half-integer witness is exactly the zero-set parametrization for cosine.
  calc
    π * z = π * ((2 * (m : ℂ) + 1) / 2) := by
      rw [hm]
      norm_num
    _ = (2 * m + 1) * π / 2 := by ring

/-- Helper for Exercise 5: a zero of `cos (π z)` forces `1 / 2 - z` to be an integer, so the
half-shifted point leaves the integer-complement domain. -/
lemma half_shift_cos_zero_forces_not_integer_complement {z : ℂ}
    (hz : cos (π * z) = 0) :
    ¬ (1 / 2 - z ∈ ℂ_ℤ) := by
  rcases Complex.cos_eq_zero_iff.mp hz with ⟨m, hm⟩
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hz_half : z = (((2 * m + 1 : ℤ) : ℂ) / 2) := by
    -- First solve for `2z`, then divide by `2` to recover the half-integer parametrization.
    refine (eq_div_iff (show (2 : ℂ) ≠ 0 by norm_num)).2 ?_
    apply mul_left_cancel₀ hpi
    calc
      π * (z * 2) = (π * z) * 2 := by ring
      _ = ((2 * m + 1) * π / 2) * 2 := by rw [hm]
      _ = (((2 * m + 1 : ℤ) : ℂ) * π) := by
            norm_num
      _ = π * (((2 * m + 1 : ℤ) : ℂ)) := by ring
  rw [Complex.mem_integerComplement_iff]
  push Not
  refine ⟨-m, ?_⟩
  -- The recovered half-integer expression turns `1 / 2 - z` into the integer `-m`.
  calc
    ((-m : ℤ) : ℂ) = (1 / 2 : ℂ) - ((((2 * m + 1 : ℤ) : ℂ) / 2) : ℂ) := by
      norm_num
      ring
    _ = (1 / 2 : ℂ) - z := by rw [hz_half]

/-- Helper for Exercise 5: if `z` lies on the excluded half-integer lattice, one odd cosine
kernel factor is already zero. -/
lemma exists_cos_kernel_zero_of_not_half_shift_domain {z : ℂ}
    (hz : ¬ (1 / 2 - z ∈ ℂ_ℤ)) :
    ∃ n : ℕ, 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2 = 0 := by
  rcases half_shift_not_mem_integerComplement_iff_exists_half_integer hz with ⟨m, hm⟩
  let n : ℕ := Int.natAbs (2 * m + 1) / 2
  have hodd_int : Odd (2 * m + 1 : ℤ) := by
    refine ⟨m, by ring⟩
  have hodd_nat : Odd (Int.natAbs (2 * m + 1)) := hodd_int.natAbs
  have hnodd : 2 * n + 1 = Int.natAbs (2 * m + 1) := by
    dsimp [n]
    exact Nat.two_mul_div_two_add_one_of_odd hodd_nat
  have hsq_int :
      ((Int.natAbs (2 * m + 1) : ℤ) ^ (2 : ℕ)) = (2 * m + 1 : ℤ) ^ (2 : ℕ) := by
    exact_mod_cast Int.natAbs_sq (2 * m + 1)
  have hsq :
      ((2 * n + 1 : ℂ) ^ (2 : ℕ)) = (((2 * m + 1 : ℤ) : ℂ) ^ (2 : ℕ)) := by
    have hnoddC : (2 * n + 1 : ℂ) = Int.natAbs (2 * m + 1) := by
      exact_mod_cast hnodd
    calc
      ((2 * n + 1 : ℂ) ^ (2 : ℕ))
          = ((Int.natAbs (2 * m + 1) : ℂ) ^ (2 : ℕ)) := by rw [hnoddC]
      _ = (((Int.natAbs (2 * m + 1) : ℤ) : ℂ) ^ (2 : ℕ)) := by simp
      _ = (((2 * m + 1 : ℤ) : ℂ) ^ (2 : ℕ)) := by
            exact_mod_cast hsq_int
  have hodd_ne : (2 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  refine ⟨n, ?_⟩
  -- Because the chosen odd denominator matches `|2m + 1|`, the `n`th factor is exactly
  -- `1 - ((2m + 1)^2 / (2n + 1)^2)`.
  rw [hm]
  calc
    1 - 4 * ((((2 * m + 1 : ℤ) : ℂ) / 2) ^ 2) / (2 * n + 1 : ℂ) ^ 2
        = 1 - (((2 * m + 1 : ℤ) : ℂ) ^ (2 : ℕ)) / (2 * n + 1 : ℂ) ^ 2 := by
            ring
    _ = 1 - ((2 * n + 1 : ℂ) ^ (2 : ℕ)) / (2 * n + 1 : ℂ) ^ 2 := by rw [← hsq]
    _ = 0 := by
          rw [div_self (pow_ne_zero 2 hodd_ne), sub_self]

/-- Helper for Exercise 5: on a compact set, the odd cosine-kernel perturbations admit a uniform
quadratic majorant. -/
lemma cos_kernel_compact_square_majorant {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z : ℂ, z ∈ K →
      ‖-4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2‖ ≤ C * (((n + 1 : ℝ) ^ 2)⁻¹) := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  let R : ℝ := max R₀ 0
  have hR : ∀ z, z ∈ K → ‖z‖ ≤ R := by
    intro z hz
    exact le_trans (hR₀ z hz) (le_max_left _ _)
  have hR_nonneg : 0 ≤ R := le_max_right _ _
  refine ⟨4 * R ^ 2, by positivity, ?_⟩
  intro n z hz
  have hzR : ‖z‖ ≤ R := hR z hz
  have hz_sq : ‖z‖ ^ 2 ≤ R ^ 2 := by
    gcongr
  have hodd_sq_pos : 0 < ((2 * n + 1 : ℝ) ^ 2) := by positivity
  have hn_sq_pos : 0 < ((n + 1 : ℝ) ^ 2) := by positivity
  have hn_nonneg : (0 : ℝ) ≤ n := by
    exact_mod_cast Nat.zero_le n
  have hsq_le : ((n + 1 : ℝ) ^ 2) ≤ ((2 * n + 1 : ℝ) ^ 2) := by
    nlinarith
  have hden_inv :
      (((2 * n + 1 : ℝ) ^ 2)⁻¹) ≤ (((n + 1 : ℝ) ^ 2)⁻¹) := by
    exact (inv_le_inv₀ hodd_sq_pos hn_sq_pos).2 hsq_le
  calc
    ‖-4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2‖
        = (4 * ‖z‖ ^ 2) * (((2 * n + 1 : ℝ) ^ 2)⁻¹) := by
            calc
              ‖-4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2‖
                  = ‖(-4 : ℂ)‖ * ‖z ^ 2‖ / ‖((2 * n + 1 : ℂ) ^ 2)‖ := by
                      rw [norm_div, norm_mul]
              _ = 4 * ‖z‖ ^ 2 / ((2 * n + 1 : ℝ) ^ 2) := by
                    have hodd_norm : ‖(2 * n + 1 : ℂ)‖ = (2 * n + 1 : ℝ) := by
                      simpa using Complex.norm_natCast (2 * n + 1)
                    rw [norm_neg, norm_pow, norm_pow, hodd_norm]
                    norm_num
              _ = (4 * ‖z‖ ^ 2) * (((2 * n + 1 : ℝ) ^ 2)⁻¹) := by
                    rw [div_eq_mul_inv]
    _ ≤ (4 * R ^ 2) * (((n + 1 : ℝ) ^ 2)⁻¹) := by
          gcongr

/-- Helper for Exercise 5: the odd cosine-kernel perturbations are normally summable on every
compact set. -/
lemma cos_kernel_perturbation_normallySummableOn {K : Set ℂ} (hK : IsCompact K) :
    NormallySummableOn (fun n z ↦ -4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) K := by
  obtain ⟨C, hC_nonneg, hC⟩ := cos_kernel_compact_square_majorant hK
  refine ⟨fun n ↦ ⟨C * (((n + 1 : ℝ) ^ 2)⁻¹), by positivity⟩, ?_, ?_⟩
  · have hbase : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) :=
      (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
    have hshift : Summable (fun n : ℕ ↦ (((n + 1 : ℝ) ^ 2)⁻¹)) := by
      simpa using (summable_nat_add_iff 1).2 hbase
    simpa [mul_assoc, mul_left_comm, mul_comm] using hshift.mul_left C
  · intro n z hz
    exact hC n z hz

/-- Helper for Exercise 5: on a compact set, a tail of the odd cosine-product factors lies in the
slit plane and its logarithms are normally summable there. -/
lemma cos_kernel_log_tail_on_compact {K : Set ℂ} (hK : IsCompact K) :
    ∃ N : ℕ,
      (∀ n : ℕ, Set.MapsTo
        (fun z ↦ 1 - 4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2) K Complex.slitPlane) ∧
      NormallySummableOn
        (fun (n : ℕ) z ↦ Complex.log (1 - 4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2)) K := by
  obtain ⟨C, hC_nonneg, hbound⟩ := cos_kernel_compact_square_majorant hK
  let N : ℕ := ⌈2 * C⌉₊
  refine ⟨N, ?_, ?_⟩
  · intro n z hz
    have hlarge_nat : 2 * C ≤ (((n + N + 1 : ℕ) : ℝ)) := by
      calc
        2 * C ≤ (N : ℝ) := by
          exact Nat.le_ceil (2 * C)
        _ ≤ n + N := by
          exact_mod_cast Nat.le_add_left N n
        _ ≤ ((n + N + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ (n + N)
    have hbase_sq :
        (((n + N + 1 : ℕ) : ℝ)) ≤ ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
      have hone_le : (1 : ℝ) ≤ (((n + N + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n + N))
      nlinarith
    have hhalf :
        C * ((((n + N + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤ 1 / 2 := by
      have hsq_large : 2 * C ≤ ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
        exact le_trans hlarge_nat hbase_sq
      have haux :
          C ≤ (1 / 2 : ℝ) * ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
        nlinarith
      have hden_pos : (0 : ℝ) < ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
        have hbase_pos : (0 : ℝ) < (((n + N + 1 : ℕ) : ℝ)) := by positivity
        positivity
      have hhalf_div : C / ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) ≤ 1 / 2 :=
        (div_le_iff₀ hden_pos).2 haux
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hhalf_div
    have hfactor_bound :
        ‖-4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2‖ ≤ C * ((((n + N + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hbound (n + N) z hz
    have hlt_one :
        ‖-4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2‖ < 1 := by
      exact lt_of_le_of_lt (hfactor_bound.trans hhalf) (by norm_num)
    -- The tail perturbation lies in the unit ball, so the corresponding factor stays in the slit
    -- plane.
    have hlt_one' : ‖-(4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2)‖ < 1 := by
      simpa [sub_eq_add_neg] using hlt_one
    simpa [sub_eq_add_neg] using
      Complex.mem_slitPlane_of_norm_lt_one
        (z := -(4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2)) hlt_one'
  · refine
      ⟨fun n ↦ ⟨(3 / 2) * C * ((((n + N + 1 : ℕ) : ℝ) ^ 2)⁻¹), by positivity⟩, ?_, ?_⟩
    · have hsummable_inv_sq :
          Summable (fun n : ℕ ↦ ((((n + N + 1 : ℕ) : ℝ) ^ (2 : ℕ))⁻¹)) := by
        simpa [Nat.add_assoc, add_comm, add_left_comm] using
          ((summable_nat_add_iff (N + 1)).2
            (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)))
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        hsummable_inv_sq.mul_left ((3 / 2) * C)
    · intro n z hz
      have hlarge_nat : 2 * C ≤ (((n + N + 1 : ℕ) : ℝ)) := by
        calc
          2 * C ≤ (N : ℝ) := by
            exact Nat.le_ceil (2 * C)
          _ ≤ n + N := by
            exact_mod_cast Nat.le_add_left N n
          _ ≤ ((n + N + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_succ (n + N)
      have hbase_sq :
          (((n + N + 1 : ℕ) : ℝ)) ≤ ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
        have hone_le : (1 : ℝ) ≤ (((n + N + 1 : ℕ) : ℝ)) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n + N))
        nlinarith
      have hhalf :
          C * ((((n + N + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤ 1 / 2 := by
        have hsq_large : 2 * C ≤ ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
          exact le_trans hlarge_nat hbase_sq
        have haux :
            C ≤ (1 / 2 : ℝ) * ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
          nlinarith
        have hden_pos : (0 : ℝ) < ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
          have hbase_pos : (0 : ℝ) < (((n + N + 1 : ℕ) : ℝ)) := by positivity
          positivity
        have hhalf_div : C / ((((n + N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) ≤ 1 / 2 :=
          (div_le_iff₀ hden_pos).2 haux
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hhalf_div
      have hfactor_bound :
          ‖-4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2‖ ≤ C * ((((n + N + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hbound (n + N) z hz
      -- After rewriting the factor as `1 + u`, the half-ball logarithm estimate applies
      -- directly to the compact majorant.
      calc
        ‖Complex.log (1 - 4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2)‖
            = ‖Complex.log (1 + (-4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2))‖ := by
                congr 2
                ring
        _ ≤ (3 / 2 : ℝ) * ‖-4 * z ^ 2 / (2 * (n + N) + 1 : ℂ) ^ 2‖ :=
              Complex.norm_log_one_add_half_le_self (hfactor_bound.trans hhalf)
        _ ≤ (3 / 2 : ℝ) * (C * ((((n + N + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
              gcongr
        _ = (3 / 2) * C * ((((n + N + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
              ring

/-- Helper for Exercise 5: the odd cosine-product factors converge compact-normally on `ℂ`. -/
lemma cos_kernel_normallyMultipliableOnCompacta :
    NormallyMultipliableOnCompacta
      (fun n z ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) Set.univ := by
  -- Package the odd cosine kernel as `1 + u n z` and feed the compact tail from the previous
  -- lemma into the chapter-20 one-add criterion.
  have honeadd :
      NormallyMultipliableOnCompacta
        (fun n z ↦ 1 + (-(4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2))) Set.univ := by
    refine
    (normallyMultipliableOnCompacta_one_add_iff
      (u := fun n z ↦ -(4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2))
      (D := Set.univ)).mpr ?_
    refine ⟨isOpen_univ, ?_, ?_⟩
    · intro n
      fun_prop
    · intro K hK hKD
      let _ := hKD
      simpa [add_assoc, sub_eq_add_neg] using cos_kernel_log_tail_on_compact hK
  simpa [sub_eq_add_neg, add_assoc] using honeadd

/-- Helper for Exercise 5: the logarithmic derivative of `z ↦ cos (π z)` is the transported
trigonometric expression used in the comparison step. -/
lemma logDeriv_cos_pi_mul (z : ℂ) :
    logDeriv (fun w : ℂ ↦ cos (π * w)) z = -(π * tan (π * z)) := by
  -- Compose the upstream cosine logarithmic derivative with the linear map `w ↦ π w`.
  have hcomp :
      logDeriv (fun w : ℂ ↦ cos (π * w)) z =
        logDeriv Complex.cos (π * z) * deriv (fun w : ℂ ↦ π * w) z := by
    exact logDeriv_comp (f := Complex.cos) (g := fun w : ℂ ↦ π * w)
      (by fun_prop) (by fun_prop)
  have hderiv_linear : deriv (fun w : ℂ ↦ π * w) z = π := by
    simpa using (hasDerivAt_const_mul (π : ℂ) z).deriv
  calc
    logDeriv (fun w : ℂ ↦ cos (π * w)) z
        = logDeriv Complex.cos (π * z) * deriv (fun w : ℂ ↦ π * w) z := hcomp
    _ = -tan (π * z) * π := by
          simpa [Complex.logDeriv_cos, hderiv_linear]
    _ = -(π * tan (π * z)) := by
          ring

/-- Helper for Exercise 5: on the half-integer-complement domain, the full odd cosine product is
nonzero because none of its factors vanish there. -/
lemma cos_kernel_tprod_ne_zero_on_half_shift_domain {z : ℂ}
    (hz : 1 / 2 - z ∈ ℂ_ℤ) :
    (∏' n : ℕ, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)) ≠ 0 := by
  have hzero :
      (∏' n : ℕ, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)) = 0 ↔
        ∃ n : ℕ, 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2 = 0 := by
    -- Convert the chapter-20 zero-set theorem into a pointwise statement at the chosen `z`.
    exact Iff.of_eq <| by
      simpa using congrArg (fun s : Set ℂ => z ∈ s)
        (zeroSet_tprod_eq_iUnion_zeroSet_of_normallyMultipliableOnCompacta
          (D := Set.univ)
          (f := fun n w ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2)
          cos_kernel_normallyMultipliableOnCompacta)
  intro hzprod
  rcases hzero.mp hzprod with ⟨n, hn⟩
  exact cos_kernel_factor_ne_zero hz n hn

/-- Helper for Exercise 5: on the half-integer-complement domain, the odd cosine product agrees
with `cos (π z)`. -/
lemma cos_kernel_tprod_eq_cos_pi_mul_on_half_shift_domain :
    Set.EqOn
      (fun z : ℂ ↦ ∏' n : ℕ, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2))
      (fun z ↦ cos (π * z))
      {z : ℂ | 1 / 2 - z ∈ ℂ_ℤ} := by
  let D : Set ℂ := {z : ℂ | 1 / 2 - z ∈ ℂ_ℤ}
  let F : ℂ → ℂ := fun z : ℂ ↦ ∏' n : ℕ, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)
  let G : ℂ → ℂ := fun z : ℂ ↦ cos (π * z)
  have hf :
      ∀ n : ℕ, DifferentiableOn ℂ (fun z : ℂ ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) Set.univ := by
    intro n z hz
    fun_prop
  have hD_open : IsOpen D := by
    -- The half-shift domain is the affine preimage of the integer complement.
    change IsOpen ((fun z : ℂ ↦ (1 / 2 : ℂ) - z) ⁻¹' ℂ_ℤ)
    exact Complex.isOpen_compl_range_intCast.preimage
      (by
        fun_prop :
          Continuous (fun z : ℂ ↦ (1 / 2 : ℂ) - z))
  have hF_diff : DifferentiableOn ℂ F D := by
    -- The odd cosine product is holomorphic on all of `ℂ`, hence also on the comparison domain.
    exact
      (differentiableOn_tprod_of_normallyMultipliableOnCompacta
        (D := Set.univ) isOpen_univ hf cos_kernel_normallyMultipliableOnCompacta).mono
        (by intro z hz; simp)
  have hG_diff : DifferentiableOn ℂ G D := by
    intro z hz
    fun_prop
  have hlogDeriv :
      Set.EqOn (logDeriv F) (logDeriv G) D := by
    intro z hz
    have hfactor_nonzero :
        ∀ n : ℕ, 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2 ≠ 0 := by
      intro n
      exact cos_kernel_factor_ne_zero hz n
    have hF_sum :
        HasSum
          (fun n : ℕ ↦ logDeriv (fun w : ℂ ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2) z)
          (logDeriv F z) := by
      -- The product-side logarithmic derivative is the sum of the factor logarithmic
      -- derivatives at points where no factor vanishes.
      simpa [F] using
        hasSum_logDeriv_tprod_at_nonvanishing_point
          (D := Set.univ)
          (f := fun n w ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2)
          hf
          cos_kernel_normallyMultipliableOnCompacta
          (by simp : z ∈ (Set.univ : Set ℂ)) hfactor_nonzero
    have hG_sum :
        HasSum
          (fun n : ℕ ↦ logDeriv (fun w : ℂ ↦ 1 - 4 * w ^ 2 / (2 * n + 1 : ℂ) ^ 2) z)
          (logDeriv G z) := by
      -- The termwise identity from part (2) matches the cosine logarithmic derivative.
      rw [show logDeriv G z = -(π * tan (π * z)) by simpa [G] using logDeriv_cos_pi_mul z]
      exact cos_kernel_logDeriv_hasSum_on_half_shift_domain hz
    exact hF_sum.unique hG_sum
  have hG_nonzero : ∀ z ∈ D, G z ≠ 0 := by
    intro z hz hzero
    exact half_shift_cos_zero_forces_not_integer_complement hzero hz
  have hF_nonzero : ∀ z ∈ D, F z ≠ 0 := by
    intro z hz
    simpa [F] using cos_kernel_tprod_ne_zero_on_half_shift_domain hz
  obtain ⟨c, hc_ne, hEq⟩ :=
    (logDeriv_eqOn_iff hF_diff hG_diff hD_open half_shift_integer_complement_isPreconnected
      hG_nonzero hF_nonzero).mp hlogDeriv
  have hz0 : (0 : ℂ) ∈ D := by
    -- The base point `0` lies in the half-shift domain because `1 / 2` is not an integer.
    have hhalf : (1 / 2 : ℂ) ∈ ℂ_ℤ := by
      rw [Complex.mem_integerComplement_iff]
      intro hhalf
      rcases hhalf with ⟨n, hn⟩
      have htwo : ((2 * n : ℤ) : ℂ) = 1 := by
        calc
          ((2 * n : ℤ) : ℂ) = (2 : ℂ) * (n : ℂ) := by simp
          _ = (2 : ℂ) * (1 / 2 : ℂ) := by rw [hn]
          _ = 1 := by norm_num
      have htwo_int : (2 * n : ℤ) = 1 := by
        exact_mod_cast htwo
      omega
    simpa [D] using hhalf
  have hF0 : F 0 = 1 := by
    -- At `z = 0` every factor is exactly `1`, so the whole infinite product is `1`.
    simpa [F] using (tprod_one : ∏' n : ℕ, (1 : ℂ) = 1)
  have hG0 : G 0 = 1 := by
    -- The comparison constant is determined by evaluating at the origin.
    simp [G]
  have hc_one : c = 1 := by
    have hpoint : F 0 = c • G 0 := hEq hz0
    have hc_eval : (1 : ℂ) = c := by
      simpa [hF0, hG0] using hpoint
    simpa using hc_eval.symm
  intro z hz
  -- Once the scalar is fixed to `1`, the logarithmic-derivative comparison becomes exact.
  calc
    F z = c • G z := hEq hz
    _ = G z := by simpa [hc_one]
    _ = cos (π * z) := rfl

/-- Helper for Exercise 5: the explicit odd-kernel partial products already match the canonical
`HasProd.tendsto_prod_nat` spelling. -/
lemma cos_kernel_partial_products_eq_explicit_odd_kernel (z : ℂ) :
    (fun N : ℕ ↦ ∏ n ∈ Finset.range N, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)) =
      (fun N : ℕ ↦ (Finset.range N).prod (fun n ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)) := by
  funext N
  rfl

/-- Helper for Exercise 5: a `HasProd` statement for the odd cosine kernel already yields the
canonical `Finset.range` partial-product limit. -/
lemma odd_cosine_kernel_tendsto_of_hasProd {z L : ℂ}
    (h :
      HasProd (fun n : ℕ ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) L) :
    Filter.Tendsto
      (fun N : ℕ ↦
        (Finset.range N).prod (fun n : ℕ ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2))
      Filter.atTop (𝓝 L) := by
  -- This is exactly the canonical `HasProd.tendsto_prod_nat` spelling.
  exact h.tendsto_prod_nat

/-- Helper for Exercise 5: the theorem-side odd-kernel sequence is definitionally the same after
parenthesizing the binder body. -/
lemma odd_cosine_kernel_unparenthesized_eq_parenthesized_sequence (z : ℂ) :
    (fun N : ℕ ↦
      ∏ n ∈ Finset.range N, 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) =
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range N, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)) := by
  -- TODO: The theorem-side unparenthesized binder is still parsed unstably here; transport it
  -- to the parenthesized binder without exposing the leaked free index.
  sorry

/-- Helper for Exercise 5: the theorem-side odd cosine partial products inherit convergence
directly from the canonical `HasProd` spelling. -/
lemma odd_cosine_kernel_theorem_side_tendsto_of_hasProd {z L : ℂ}
    (h :
      HasProd (fun n : ℕ ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) L) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range N, 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)
      Filter.atTop (𝓝 L) := by
  -- TODO: Once the unparenthesized binder bridge is available, this becomes a one-step transport
  -- from `odd_cosine_kernel_parenthesized_tendsto_of_hasProd`.
  sorry

/-- Helper for Exercise 5: the parenthesized odd cosine partial products inherit convergence
directly from the canonical `HasProd` spelling. -/
lemma odd_cosine_kernel_parenthesized_tendsto_of_hasProd {z L : ℂ}
    (h :
      HasProd (fun n : ℕ ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) L) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range N, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2))
      Filter.atTop (𝓝 L) := by
  -- Rewrite the parenthesized binder to the canonical `Finset.range` product once.
  refine Filter.Tendsto.congr'
    (Filter.Eventually.of_forall fun N ↦
      (congrFun (cos_kernel_partial_products_eq_explicit_odd_kernel z) N).symm)
    (odd_cosine_kernel_tendsto_of_hasProd h)

/-- Helper for Exercise 5: once one odd cosine factor vanishes, every later theorem-side partial
product is exactly zero. -/
lemma odd_cosine_kernel_eventually_zero_of_zero_factor {z : ℂ} {n0 : ℕ}
    (hz0 : 1 - 4 * z ^ 2 / (2 * n0 + 1 : ℂ) ^ 2 = 0) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Finset.range N).prod (fun n : ℕ ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) = 0 := by
  let f : ℕ → ℂ := fun n ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2
  refine Filter.eventually_atTop.2 ⟨n0 + 1, ?_⟩
  intro N hN
  have hn_mem : n0 ∈ Finset.range N := by
    simp [Nat.lt_of_lt_of_le (Nat.lt_succ_self n0) hN]
  have hz0' : f n0 = 0 := by
    simpa [f] using hz0
  -- Every sufficiently long partial product contains the zero factor at `n0`.
  simpa [f] using (Finset.prod_eq_zero hn_mem hz0' : (Finset.range N).prod f = 0)

/-- Exercise 5 (4): the Weierstrass product expansion of `cos (π z)`. -/
-- Route correction: the Euler odd/even split is the wrong bottleneck here. The source-faithful
-- route is now through the section-20 logarithmic-derivative product API on the half-integer
-- complement domain, using `logDeriv_cos_kernel_factor` and `pi_tan_pi_mul_hasSum`.
theorem cos_pi_mul_hasProd
    (z : ℂ) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range N, 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)
      Filter.atTop (𝓝 (cos (π * z))) := by
  -- TODO: The analytic proof is complete in `cos_pi_mul_parenthesized_hasProd`; the remaining
  -- work is only the malformed theorem-side transport from the unparenthesized binder surface.
  sorry

/-- Helper for Exercise 5: the parenthesized odd cosine product converges to `cos (π z)` by the
source half-shift domain split. -/
lemma cos_pi_mul_parenthesized_hasProd
    (z : ℂ) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range N, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2))
      Filter.atTop (𝓝 (cos (π * z))) := by
  -- Split exactly as in the source proof: compare with the infinite product on the half-shift
  -- domain, and force eventual zero once a factor vanishes off that domain.
  by_cases hz : 1 / 2 - z ∈ ℂ_ℤ
  · have hprod :
        HasProd (fun n : ℕ ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)
          (∏' n : ℕ, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)) :=
      cos_kernel_normallyMultipliableOnCompacta.hasProd (by simp)
    have hlimit :
        Filter.Tendsto
          (fun N : ℕ ↦
            ∏ n ∈ Finset.range N, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2))
          Filter.atTop
          (𝓝 (∏' n : ℕ, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2))) :=
      odd_cosine_kernel_parenthesized_tendsto_of_hasProd hprod
    have hvalue :
        (∏' n : ℕ, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2)) = cos (π * z) :=
      cos_kernel_tprod_eq_cos_pi_mul_on_half_shift_domain hz
    -- On the nonvanishing domain, the parenthesized partial products converge to the compared
    -- infinite product, which is already identified with `cos (π z)`.
    simpa [hvalue] using hlimit
  · rcases exists_cos_kernel_zero_of_not_half_shift_domain hz with ⟨n0, hn0⟩
    have hzero_canonical :
        ∀ᶠ N : ℕ in Filter.atTop,
          (Finset.range N).prod (fun n : ℕ ↦ 1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) = 0 :=
      odd_cosine_kernel_eventually_zero_of_zero_factor hn0
    have hzero :
        ∀ᶠ N : ℕ in Filter.atTop,
          ∏ n ∈ Finset.range N, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2) = 0 := by
      -- Transport the eventual zero factor only across the parenthesized binder, which is stable.
      filter_upwards [hzero_canonical] with N hN
      exact (congrFun (cos_kernel_partial_products_eq_explicit_odd_kernel z) N).trans hN
    have hlimit_zero :
        Filter.Tendsto
          (fun N : ℕ ↦
            ∏ n ∈ Finset.range N, (1 - 4 * z ^ 2 / (2 * n + 1 : ℂ) ^ 2))
          Filter.atTop (𝓝 (0 : ℂ)) := by
      -- Once the parenthesized partial products are eventually zero, the limit is `0`.
      refine Filter.Tendsto.congr' (hzero.mono fun N hN ↦ hN.symm) ?_
      simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℂ)) Filter.atTop (𝓝 0))
    have hcos : cos (π * z) = 0 := cos_pi_mul_eq_zero_of_not_half_shift_domain hz
    -- The excluded branch ends at the cosine zero forced by the half-integer pole.
    simpa [hcos] using hlimit_zero

/-- Helper for Exercise 5: the quarter-shift denominator factor never vanishes. -/
lemma quarter_shift_denominator_factor_ne_zero (n : ℕ) :
    1 - 4 * ((1 : ℂ) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2 ≠ 0 := by
  have h41 : (4 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (4 * n + 1 : ℕ) ≠ 0 by omega)
  have h43 : (4 * n + 3 : ℂ) ≠ 0 := by
    exact_mod_cast (show (4 * n + 3 : ℕ) ≠ 0 by omega)
  have hodd : (2 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  rw [quarter_shift_kernel_denominator_eq]
  exact div_ne_zero (mul_ne_zero h41 h43) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hodd))

/-- Helper for Exercise 5: clearing the linear denominators turns the quarter-shift factor pair
into the polynomial numerator used by the odd cosine kernel. -/
lemma quarter_shift_factor_pair_eq_ratio_cleared (z : ℂ) (n : ℕ) :
    (1 - z / (4 * n + 1 : ℂ)) * (1 + z / (4 * n + 3 : ℂ)) *
      ((4 * n + 1 : ℂ) * (4 * n + 3 : ℂ)) =
        ((4 * n + 1 : ℂ) - z) * ((4 * n + 3 : ℂ) + z) := by
  have h41 : (4 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (4 * n + 1 : ℕ) ≠ 0 by omega)
  have h43 : (4 * n + 3 : ℂ) ≠ 0 := by
    exact_mod_cast (show (4 * n + 3 : ℕ) ≠ 0 by omega)
  -- Clear only the linear denominators; the remaining odd-kernel normalization is handled
  -- separately by the numerator/denominator rewrite lemmas.
  field_simp [h41, h43]

/-- Helper for Exercise 5: pairing the `2n`-th and `(2n+1)`-st quarter-shift factors gives the
ratio of two odd cosine kernels. -/
lemma quarter_shift_factor_pair_eq_ratio (z : ℂ) (n : ℕ) :
    (1 - z / (4 * n + 1 : ℂ)) * (1 + z / (4 * n + 3 : ℂ)) =
      (1 - 4 * ((z + 1) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2) /
        (1 - 4 * ((1 : ℂ) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2) := by
  have h41 : (4 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (4 * n + 1 : ℕ) ≠ 0 by omega)
  have h43 : (4 * n + 3 : ℂ) ≠ 0 := by
    exact_mod_cast (show (4 * n + 3 : ℕ) ≠ 0 by omega)
  have hodd : (2 * n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  have hscalar : (4 * (2 * n + 1 : ℂ) ^ 2) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hodd)
  have hden : ((4 * n + 1 : ℂ) * (4 * n + 3 : ℂ)) / (4 * (2 * n + 1 : ℂ) ^ 2) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero h41 h43) hscalar
  -- Route correction: rewrite numerator and denominator kernels first, then clear the one common
  -- odd-kernel scalar instead of attacking the raw quotient directly.
  rw [quarter_shift_kernel_numerator_eq, quarter_shift_kernel_denominator_eq]
  apply (eq_div_iff hden).2
  calc
    (1 - z / (4 * n + 1 : ℂ)) * (1 + z / (4 * n + 3 : ℂ)) *
        (((4 * n + 1 : ℂ) * (4 * n + 3 : ℂ)) / (4 * (2 * n + 1 : ℂ) ^ 2))
        =
          ((1 - z / (4 * n + 1 : ℂ)) * (1 + z / (4 * n + 3 : ℂ)) *
            ((4 * n + 1 : ℂ) * (4 * n + 3 : ℂ))) /
            (4 * (2 * n + 1 : ℂ) ^ 2) := by
              rw [div_eq_mul_inv]
              ring
    _ = (((4 * n + 1 : ℂ) - z) * ((4 * n + 3 : ℂ) + z)) / (4 * (2 * n + 1 : ℂ) ^ 2) := by
          rw [quarter_shift_factor_pair_eq_ratio_cleared]

/-- Helper for Exercise 5: the exact terminal pair produced by two `Finset.prod_range_succ`
rewrites matches the normalized odd-kernel ratio. -/
lemma quarter_shift_terminal_pair_eq_ratio_normalized (N : ℕ) (z : ℂ) :
    (1 + (-1 : ℂ) ^ (2 * N + 1) * z / (2 * (2 * N) + 1 : ℂ)) *
      (1 + (-1 : ℂ) ^ (2 * N + 2) * z / (2 * (2 * N + 1) + 1 : ℂ)) =
        (1 - 4 * ((z + 1) / 4) ^ 2 / (2 * N + 1 : ℂ) ^ 2) /
          (1 - 4 * ((1 : ℂ) / 4) ^ 2 / (2 * N + 1 : ℂ) ^ 2) := by
  -- Normalize the alternating signs and odd denominators before applying the paired ratio lemma.
  have hpow1 : (-1 : ℂ) ^ (2 * N + 1) = -1 := by
    rw [show 2 * N + 1 = 2 * N + 1 by omega, pow_add]
    simp
  have hpow2 : (-1 : ℂ) ^ (2 * N + 2) = 1 := by
    rw [show 2 * N + 2 = 2 * (N + 1) by omega]
    simp
  have hden1 : (2 * (2 * N) + 1 : ℂ) = (4 * N + 1 : ℂ) := by
    exact_mod_cast (show 2 * (2 * N) + 1 = 4 * N + 1 by omega)
  have hden2 : (2 * (2 * N + 1) + 1 : ℂ) = (4 * N + 3 : ℂ) := by
    exact_mod_cast (show 2 * (2 * N + 1) + 1 = 4 * N + 3 by omega)
  rw [hpow1, hpow2, hden1, hden2]
  simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc] using quarter_shift_factor_pair_eq_ratio z N

/-- Helper for Exercise 5: the even partial products of the quarter-shift kernel equal the ratio
of the odd cosine partial products at `((z + 1) / 4)` and at `1 / 4`. -/
lemma quarter_shift_even_partial_product_eq_ratio (N : ℕ) (z : ℂ) :
    ∏ n ∈ Finset.range (2 * N), (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ)) =
      (∏ n ∈ Finset.range N, (1 - 4 * ((z + 1) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2)) /
        (∏ n ∈ Finset.range N, (1 - 4 * ((1 : ℂ) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2)) := by
  let q : ℕ → ℂ := fun n ↦ 1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ)
  let a : ℕ → ℂ := fun n ↦ 1 - 4 * ((z + 1) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2
  let b : ℕ → ℂ := fun n ↦ 1 - 4 * ((1 : ℂ) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2
  -- Keep the source induction on the number of paired factors, using the exact terminal-pair
  -- adapter so each step adds one odd-kernel ratio.
  change (∏ n ∈ Finset.range (2 * N), q n) = (∏ n ∈ Finset.range N, a n) / (∏ n ∈ Finset.range N, b n)
  induction N with
  | zero =>
      -- The empty even-stage product is the trivial ratio `1 / 1`.
      simp [q, a, b]
  | succ N ih =>
      have hsplit :
          ∏ n ∈ Finset.range (2 * (N + 1)), q n =
            (∏ n ∈ Finset.range (2 * N), q n) * (q (2 * N) * q (2 * N + 1)) := by
        -- Peel off the two terminal factors so the induction matches the source pairing step.
        calc
          ∏ n ∈ Finset.range (2 * (N + 1)), q n
              = ∏ n ∈ Finset.range (2 * N + 2), q n := by
                  rw [show 2 * (N + 1) = 2 * N + 2 by omega]
          _ = (∏ n ∈ Finset.range (2 * N + 1), q n) * q (2 * N + 1) := by
                rw [Finset.prod_range_succ]
          _ = ((∏ n ∈ Finset.range (2 * N), q n) * q (2 * N)) * q (2 * N + 1) := by
                rw [Finset.prod_range_succ]
          _ = (∏ n ∈ Finset.range (2 * N), q n) * (q (2 * N) * q (2 * N + 1)) := by
                ring
      have hpair : q (2 * N) * q (2 * N + 1) = a N / b N := by
        simpa [q, a, b] using quarter_shift_terminal_pair_eq_ratio_normalized N z
      calc
        ∏ n ∈ Finset.range (2 * (N + 1)), q n
            = (∏ n ∈ Finset.range (2 * N), q n) * (q (2 * N) * q (2 * N + 1)) := hsplit
        _ = ((∏ n ∈ Finset.range N, a n) / (∏ n ∈ Finset.range N, b n)) * (a N / b N) := by
              rw [ih, hpair]
        _ = ((∏ n ∈ Finset.range N, a n) * a N) / ((∏ n ∈ Finset.range N, b n) * b N) := by
              rw [div_mul_div_comm]
        _ = (∏ n ∈ Finset.range (N + 1), a n) / (∏ n ∈ Finset.range (N + 1), b n) := by
              rw [Finset.prod_range_succ, Finset.prod_range_succ]

/-- Helper for Exercise 5: the unique unpaired factor at the even index `2k` is the normalized
odd denominator term from the source parity split. -/
lemma quarter_shift_even_index_factor_eq (z : ℂ) (k : ℕ) :
    1 + (-1 : ℂ) ^ (2 * k + 1) * z / (2 * (2 * k) + 1 : ℂ) =
      1 - z / (4 * k + 1 : ℂ) := by
  -- Normalize the alternating sign and the odd denominator before simplifying the factor.
  have hpow : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    simp [pow_add, pow_mul]
  have hden : (2 * (2 * k) + 1 : ℂ) = (4 * k + 1 : ℂ) := by
    exact_mod_cast (show 2 * (2 * k) + 1 = 4 * k + 1 by omega)
  rw [hpow, hden]
  ring

/-- Helper for Exercise 5: in the odd branch `N = 2k + 1`, the theorem-side transported tail
`if Even N then 1 else 1 - z / (4 * (N / 2) + 1)` is exactly the leftover factor. -/
lemma quarter_shift_odd_tail_transport_eq (z : ℂ) (k : ℕ) :
    (if Even (2 * k + 1) then (1 : ℂ) else 1 - z / (((4 * ((2 * k + 1) / 2) + 1 : ℕ) : ℂ))) =
      1 - z / (4 * k + 1 : ℂ) := by
  have hnot_even : ¬ Even (2 * k + 1) := by
    -- An odd successor cannot lie in the even branch of the parity split.
    intro hEven
    rcases hEven with ⟨m, hm⟩
    omega
  have hdiv : (2 * k + 1) / 2 = k := by
    -- The transported odd tail uses the floor division spelling from the theorem statement.
    omega
  have hden :
      (((4 * ((2 * k + 1) / 2) + 1 : ℕ) : ℂ)) = (4 * k + 1 : ℂ) := by
    exact_mod_cast (show 4 * ((2 * k + 1) / 2) + 1 = 4 * k + 1 by rw [hdiv])
  simp [hnot_even, hden]

/-- Helper for Exercise 5: freezing the quarter-shift body into a local kernel makes the source
parity split binder-stable. -/
lemma quarter_shift_partial_product_eq_even_part_mul_tail_kernel (N : ℕ) (z : ℂ) :
    let q : ℕ → ℂ := fun n ↦ 1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ)
    (∏ n ∈ Finset.range N, q n) =
      (∏ n ∈ Finset.range (2 * (N / 2)), q n) *
        (if Even N then (1 : ℂ) else 1 - z / (((4 * (N / 2) + 1 : ℕ) : ℂ))) := by
  dsimp
  set q : ℕ → ℂ := fun n ↦ 1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ)
  -- Route correction: freeze the product body once, then split only on the parity of `N`.
  rcases Nat.even_or_odd N with hEven | hOdd
  · rcases hEven with ⟨k, rfl⟩
    -- On even stages the paired block already exhausts the whole product.
    have hpair : 2 * ((k + k) / 2) = k + k := by omega
    rw [hpair]
    simp [q]
  · rcases hOdd with ⟨k, rfl⟩
    calc
      ∏ n ∈ Finset.range (2 * k + 1), q n
          = (∏ n ∈ Finset.range (2 * k), q n) * q (2 * k) := by
              -- Peel off the unique unpaired terminal factor in the odd branch.
              rw [Finset.prod_range_succ]
      _ = (∏ n ∈ Finset.range (2 * k), q n) * (1 - z / (4 * k + 1 : ℂ)) := by
            -- The last factor is exactly the odd denominator term from the source split.
            rw [show q (2 * k) = 1 - z / (4 * k + 1 : ℂ) by
              simpa [q] using quarter_shift_even_index_factor_eq z k]
      _ =
          (∏ n ∈ Finset.range (2 * ((2 * k + 1) / 2)), q n) *
            (if Even (2 * k + 1) then (1 : ℂ) else
              1 - z / (((4 * ((2 * k + 1) / 2) + 1 : ℕ) : ℂ))) := by
            -- Transport the tail through the floor-division spelling used by the theorem.
            have hdiv : (2 * k + 1) / 2 = k := by
              omega
            rw [quarter_shift_odd_tail_transport_eq z k]
            simp [hdiv]

/-- Helper for Exercise 5: every quarter-shift partial product is its paired even-stage product,
with only the final odd factor left unpaired. -/
lemma quarter_shift_partial_product_eq_even_part_mul_tail (N : ℕ) (z : ℂ) :
    (∏ n ∈ Finset.range N, (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ))) =
      (∏ n ∈ Finset.range (2 * (N / 2)),
        (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ))) *
        (if Even N then (1 : ℂ) else 1 - z / (((4 * (N / 2) + 1 : ℕ) : ℂ))) := by
  -- Freeze the quarter-shift body before transporting the kernel statement back to the theorem.
  by_cases hN : Even N
  · -- In the even branch the transported tail is `1`, so the kernel statement matches directly.
    rw [if_pos hN]
    simpa [hN] using quarter_shift_partial_product_eq_even_part_mul_tail_kernel N z
  · -- In the odd branch the kernel statement keeps the leftover factor exactly as required.
    rw [if_neg hN]
    simpa [hN] using quarter_shift_partial_product_eq_even_part_mul_tail_kernel N z

/-- Helper for Exercise 5: the paired even quarter-shift block tends to the cosine quotient from
the source ratio argument. -/
lemma quarter_shift_even_block_theorem_side_eq_ratio_sequence (z : ℂ) :
    (fun N : ℕ ↦
      ∏ n ∈ Finset.range (2 * (N / 2)),
        (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ))) =
      (fun N : ℕ ↦
        (∏ n ∈ Finset.range (N / 2), (1 - 4 * ((z + 1) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2)) /
          (∏ n ∈ Finset.range (N / 2), (1 - 4 * ((1 : ℂ) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2))) := by
  funext N
  -- This is the source pairing identity evaluated at the composed stage `N / 2`.
  simpa using quarter_shift_even_partial_product_eq_ratio (N / 2) z

/-- Helper for Exercise 5: the theorem-side paired quarter-shift block is definitionally unchanged
after parenthesizing the binder body. -/
lemma quarter_shift_even_block_unparenthesized_eq_parenthesized_sequence (z : ℂ) :
    (fun N : ℕ ↦
      ∏ n ∈ Finset.range (2 * (N / 2)),
        1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ)) =
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range (2 * (N / 2)),
          (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ))) := by
  -- TODO: The theorem-side unparenthesized paired block still leaks a free index under parsing;
  -- transport it to the parenthesized binder without touching the analytic core.
  sorry

/-- Helper for Exercise 5: the paired even quarter-shift block tends to the cosine quotient from
the source ratio argument. -/
lemma quarter_shift_even_block_tendsto_cosine_ratio (z : ℂ) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range (2 * (N / 2)),
          (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ)))
      Filter.atTop (𝓝 (cos (π * ((z + 1) / 4)) / cos (π / 4))) := by
  have hdiv : Filter.Tendsto (fun N : ℕ ↦ N / 2) Filter.atTop Filter.atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hnum :
      Filter.Tendsto
        (fun N : ℕ ↦
          ∏ n ∈ Finset.range (N / 2), (1 - 4 * ((z + 1) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2))
        Filter.atTop (𝓝 (cos (π * ((z + 1) / 4)))) :=
    -- Compose the parenthesized part-(iii) limit with the floor-division stages from the source.
    (cos_pi_mul_parenthesized_hasProd ((z + 1) / 4)).comp hdiv
  have hcos_quarter :
      cos (π / 4 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    have h : cos (((Real.pi / 4 : ℝ) : ℂ)) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cos, Real.cos_pi_div_four]
    simpa using h
  have hcos_quarter_ne : cos (π / 4 : ℂ) ≠ 0 := by
    rw [hcos_quarter]
    exact_mod_cast (show (Real.sqrt 2 / 2 : ℝ) ≠ 0 by
      exact div_ne_zero
        (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
        (by norm_num))
  have hden :
      Filter.Tendsto
        (fun N : ℕ ↦
          ∏ n ∈ Finset.range (N / 2), (1 - 4 * ((1 : ℂ) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2))
        Filter.atTop (𝓝 (cos (π * ((1 : ℂ) / 4)))) :=
    -- The same parenthesized part-(iii) limit at `z = 1 / 4` supplies the denominator.
    (cos_pi_mul_parenthesized_hasProd ((1 : ℂ) / 4)).comp hdiv
  have hden_ne : cos (π * ((1 : ℂ) / 4)) ≠ 0 := by
    -- Normalize the denominator limit to the nonzero quarter-angle cosine.
    simpa [show π * ((1 : ℂ) / 4) = π / 4 by ring] using hcos_quarter_ne
  have hratio :
      Filter.Tendsto
        (fun N : ℕ ↦
          (∏ n ∈ Finset.range (N / 2), (1 - 4 * ((z + 1) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2)) /
            (∏ n ∈ Finset.range (N / 2), (1 - 4 * ((1 : ℂ) / 4) ^ 2 / (2 * n + 1 : ℂ) ^ 2)))
        Filter.atTop (𝓝 (cos (π * ((z + 1) / 4)) / cos (π / 4))) := by
    -- Division is continuous at the nonzero denominator limit, so the paired ratio inherits the
    -- two odd-kernel limits directly.
    simpa [show π * ((1 : ℂ) / 4) = π / 4 by ring] using hnum.div hden hden_ne
  -- Rewrite the theorem-side paired block to the explicit source ratio sequence.
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ ?_) hratio
  simpa using (congrFun (quarter_shift_even_block_theorem_side_eq_ratio_sequence z).symm N)

/-- Helper for Exercise 5: the leftover odd factor in the quarter-shift product tends to `1`. -/
lemma quarter_shift_odd_factor_tendsto_one (z : ℂ) :
    Filter.Tendsto (fun N : ℕ ↦ 1 - z / (4 * N + 1 : ℂ)) Filter.atTop (𝓝 1) := by
  have hrec :
      Filter.Tendsto (fun N : ℕ ↦ 1 / ((1 / 4 : ℂ) + N)) Filter.atTop (𝓝 0) :=
    tendsto_reciprocal_add_nat_zero (1 / 4 : ℂ)
  have hdiv :
      Filter.Tendsto (fun N : ℕ ↦ z / (4 * N + 1 : ℂ)) Filter.atTop (𝓝 0) := by
    have hmul :
        Filter.Tendsto
          (fun N : ℕ ↦ (z / 4) * (1 / ((1 / 4 : ℂ) + N)))
          Filter.atTop (𝓝 ((z / 4) * 0)) :=
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ z / 4) Filter.atTop (𝓝 (z / 4))).mul hrec
    have hEq :
        (fun N : ℕ ↦ z / (4 * N + 1 : ℂ)) =
          (fun N : ℕ ↦ (z / 4) * (1 / ((1 / 4 : ℂ) + N))) := by
      funext N
      have hfour : (4 : ℂ) ≠ 0 := by norm_num
      have hden : ((1 / 4 : ℂ) + N) ≠ 0 := by
        intro hzero
        have hre : (1 / 4 : ℝ) + N = 0 := by
          simpa using congrArg Complex.re hzero
        nlinarith
      field_simp [hfour, hden]
      ring
    rw [hEq]
    simpa using hmul
  -- Subtract the vanishing correction from the constant `1`.
  simpa using tendsto_const_nhds.sub hdiv

/-- Helper for Exercise 5: the parity-transported quarter-shift tail also tends to `1`. -/
lemma quarter_shift_parity_tail_tendsto_one (z : ℂ) :
    Filter.Tendsto
      (fun N : ℕ ↦ if Even N then (1 : ℂ) else 1 - z / (((4 * (N / 2) + 1 : ℕ) : ℂ)))
      Filter.atTop (𝓝 1) := by
  let g : ℕ → ℂ := fun N ↦ 1 - z / (4 * N + 1 : ℂ)
  have hdiv : Filter.Tendsto (fun N : ℕ ↦ N / 2) Filter.atTop Filter.atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hg : Filter.Tendsto (fun N : ℕ ↦ g (N / 2)) Filter.atTop (𝓝 1) := by
    -- Compose the previously proved odd-tail limit with the floor-division map.
    simpa [g, Function.comp_def] using (quarter_shift_odd_factor_tendsto_one z).comp hdiv
  have hnorm :
      Filter.Tendsto (fun N : ℕ ↦ ‖g (N / 2) - 1‖) Filter.atTop (𝓝 0) := by
    exact tendsto_iff_norm_sub_tendsto_zero.1 hg
  have hbound :
      ∀ N : ℕ,
        ‖(if Even N then (1 : ℂ) else g (N / 2)) - 1‖ ≤ ‖g (N / 2) - 1‖ := by
    intro N
    by_cases hN : Even N
    · simp [hN]
    · simp [hN]
  -- The parity branch either contributes `0` or the already-controlled odd-tail error.
  refine tendsto_iff_norm_sub_tendsto_zero.2 <|
    (by
      simpa [g] using
        squeeze_zero
          (fun N ↦ norm_nonneg ((if Even N then (1 : ℂ) else g (N / 2)) - 1))
          hbound hnorm)

/-- Helper for Exercise 5: freezing the theorem-side quarter-shift sequence turns the source
parity split into a single exact sequence identity. -/
lemma quarter_shift_theorem_side_eq_even_times_tail_sequence (z : ℂ) :
    (fun N : ℕ ↦
      (Finset.range N).prod (fun n : ℕ ↦ 1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ))) =
      (fun N : ℕ ↦
        (∏ n ∈ Finset.range (2 * (N / 2)),
          (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ))) *
          (if Even N then (1 : ℂ) else 1 - z / (((4 * (N / 2) + 1 : ℕ) : ℂ)))) := by
  funext N
  -- This is exactly the parity split already proved pointwise for the theorem-side product.
  simpa using quarter_shift_partial_product_eq_even_part_mul_tail N z

/-- Helper for Exercise 5: the full theorem-side quarter-shift product is definitionally unchanged
after parenthesizing the binder body. -/
lemma quarter_shift_full_product_unparenthesized_eq_parenthesized_sequence (z : ℂ) :
    (fun N : ℕ ↦
      ∏ n ∈ Finset.range N, 1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ)) =
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range N, (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ))) := by
  -- TODO: The full theorem-side unparenthesized product still needs the same parser-stable
  -- transport as the odd-kernel product and the paired block.
  sorry

/-- Helper for Exercise 5: the cosine quotient from the paired product simplifies to the target
trigonometric expression. -/
lemma quarter_shift_cosine_ratio_eq (z : ℂ) :
    cos (π * ((z + 1) / 4)) / cos (π / 4) = cos (π * z / 4) - sin (π * z / 4) := by
  have hcos_quarter :
      cos (π / 4 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    have h : cos (((Real.pi / 4 : ℝ) : ℂ)) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cos, Real.cos_pi_div_four]
    simpa using h
  have hsin_quarter :
      sin (π / 4 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    have h : sin (((Real.pi / 4 : ℝ) : ℂ)) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sin, Real.sin_pi_div_four]
    simpa using h
  have hquarter :
      cos (π / 4 : ℂ) = sin (π / 4 : ℂ) := by
    -- The quarter-angle constants agree, so the cosine addition formula collapses to the target.
    rw [hcos_quarter, hsin_quarter]
  have hcos_ne_value : ((Real.sqrt 2 / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (Real.sqrt 2 / 2 : ℝ) ≠ 0 by
      exact div_ne_zero
        (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
        (by norm_num))
  have hcos_ne : cos (π / 4 : ℂ) ≠ 0 := by
    -- The quarter-angle cosine is the nonzero normalization factor in the source ratio.
    rw [hcos_quarter]
    exact hcos_ne_value
  apply (div_eq_iff hcos_ne).2
  have harg : π * ((z + 1) / 4) = π * z / 4 + π / 4 := by ring
  -- Rewrite the shifted cosine by `cos (u + π / 4)` and then use the equal quarter-angle values.
  rw [harg, Complex.cos_add, hquarter]
  ring

/-- Helper for Exercise 5: the parenthesized quarter-shift product tends to
`cos (π z / 4) - sin (π z / 4)` by the source parity split. -/
lemma cos_pi_quarter_sub_sin_pi_quarter_parenthesized_hasProd
    (z : ℂ) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range N, (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ)))
      Filter.atTop (𝓝 (cos (π * z / 4) - sin (π * z / 4))) := by
  have hsplit :
      Filter.Tendsto
        (fun N : ℕ ↦
          (∏ n ∈ Finset.range (2 * (N / 2)),
            (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ))) *
            (if Even N then (1 : ℂ) else 1 - z / (((4 * (N / 2) + 1 : ℕ) : ℂ))))
        Filter.atTop (𝓝 ((cos (π * ((z + 1) / 4)) / cos (π / 4)) * 1)) := by
    -- The full source decomposition is the product of the paired even block and the odd tail.
    exact (quarter_shift_even_block_tendsto_cosine_ratio z).mul
      (quarter_shift_parity_tail_tendsto_one z)
  have hparenthesized :
      Filter.Tendsto
        (fun N : ℕ ↦
          ∏ n ∈ Finset.range N, (1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ)))
        Filter.atTop (𝓝 ((cos (π * ((z + 1) / 4)) / cos (π / 4)) * 1)) := by
    -- Rewrite the parenthesized full product by the parity split once.
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ ?_) hsplit
    simpa using (congrFun (quarter_shift_theorem_side_eq_even_times_tail_sequence z).symm N)
  -- Collapse the cosine quotient to the target trigonometric expression.
  simpa [quarter_shift_cosine_ratio_eq z] using hparenthesized

/-- Exercise 5 (5): the product expansion of `cos (π z / 4) - sin (π z / 4)`. -/
-- TODO: After Exercise 5 (4), pair consecutive factors and rewrite each pair in terms of the
-- cosine product at `(z + 1) / 4` and at `1 / 4`.
theorem cos_pi_quarter_sub_sin_pi_quarter_hasProd
    (z : ℂ) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∏ n ∈ Finset.range N, 1 + (-1 : ℂ) ^ (n + 1) * z / (2 * n + 1 : ℂ))
      Filter.atTop (𝓝 (cos (π * z / 4) - sin (π * z / 4))) := by
  -- TODO: The analytic source proof is complete in
  -- `cos_pi_quarter_sub_sin_pi_quarter_parenthesized_hasProd`; the remaining blocker is the same
  -- theorem-side transport from the malformed unparenthesized binder surface.
  sorry
