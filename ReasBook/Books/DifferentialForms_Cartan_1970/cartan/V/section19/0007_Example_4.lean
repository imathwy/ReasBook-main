import DifferentialForms_Cartan_1970.cartan.V.section19.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.cartan.V.section19.«0006_Example_3»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Complex
open Equiv
open scoped Real

local notation "ℂ_ℤ" => integerComplement

/-- The `n`-th summand in the alternating integer square-pole series. -/
def alternating_integer_square_pole_series_term (n : ℤ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ n / (z - n) ^ 2

/-- Helper for Example 4: dividing a point of `integerComplement` by `2` stays away from the
integers. -/
lemma half_mem_integerComplement {z : ℂ} (hz : z ∈ ℂ_ℤ) : z / 2 ∈ ℂ_ℤ := by
  -- Halving an integer would force the original point to be an integer as well.
  rw [Complex.mem_integerComplement_iff] at hz ⊢
  intro hhalf
  rcases hhalf with ⟨n, hn⟩
  apply hz
  refine ⟨2 * n, ?_⟩
  calc
    ((2 * n : ℤ) : ℂ) = (2 : ℂ) * n := by norm_num
    _ = (2 : ℂ) * (z / 2) := by rw [hn]
    _ = z := by field_simp

/-- Helper for Example 4: Proposition 2.1 rewritten in `HasSum` form. -/
lemma ordinary_integer_square_pole_hasSum {z : ℂ} (hz : z ∈ ℂ_ℤ) :
    HasSum (fun n : ℤ ↦ integer_square_pole_series_term n z)
      ((π / sin (π * z)) ^ (2 : ℕ)) := by
  -- Recover the series statement from the closed `tsum` identity and the already-proved
  -- summability on `integerComplement`.
  refine (Summable.hasSum_iff ?_).2 ?_
  · exact integer_square_pole_series_summableLocallyUniformlyOn.summable hz
  · simpa [integer_square_pole_series] using integer_square_pole_series_eq_pi_sq_div_sin_sq hz

/-- Helper for Example 4: evaluating the ordinary square-pole term at `z / 2` produces the even
fiber of the `z`-series, scaled by `4`. -/
lemma integer_square_pole_half_arg_term_eq (m : ℤ) (z : ℂ) :
    integer_square_pole_series_term m (z / 2) =
      4 * integer_square_pole_series_term (2 * m) z := by
  -- Rewrite the half-argument denominator as the even-fiber denominator divided by `2`.
  have hrewrite : z / 2 - (m : ℂ) = (z - (2 * m : ℤ)) / 2 := by
    calc
      z / 2 - (m : ℂ) = z / 2 - ((2 : ℂ) * m) / 2 := by norm_num
      _ = (z - ((2 : ℂ) * m)) / 2 := by ring
      _ = (z - (2 * m : ℤ)) / 2 := by norm_num
  rw [integer_square_pole_series_term, integer_square_pole_series_term, hrewrite]
  by_cases hzero : z - (2 * m : ℤ) = 0
  · -- On the pole, both denominators vanish, so both sides are the same singular term.
    have hzero' : z - 2 * (m : ℂ) = 0 := by simpa using hzero
    simp [hzero']
  · -- Away from the pole, clear denominators after the half-argument rewrite.
    field_simp [hzero]
    ring

/-- Helper for Example 4: the parity splitter `Int.divModEquiv 2` sends the even branch to
`2 * m`. -/
lemma int_divModEquiv_two_symm_zero (m : ℤ) :
    (Int.divModEquiv 2).symm (m, (0 : Fin 2)) = 2 * m := by
  simp [Int.divModEquiv]
  ring

/-- Helper for Example 4: the parity splitter `Int.divModEquiv 2` sends the odd branch to
`2 * m + 1`. -/
lemma int_divModEquiv_two_symm_one (m : ℤ) :
    (Int.divModEquiv 2).symm (m, (1 : Fin 2)) = 2 * m + 1 := by
  simp [Int.divModEquiv]
  ring

/-- Helper for Example 4: the even square-pole fiber is the ordinary square-pole identity at
`z / 2`, divided by `4`. -/
lemma even_integer_square_pole_hasSum {z : ℂ} (hz : z ∈ ℂ_ℤ) :
    HasSum (fun m : ℤ ↦ integer_square_pole_series_term (2 * m) z)
      ((1 / 4 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ)) := by
  have hhalf := ordinary_integer_square_pole_hasSum (half_mem_integerComplement hz)
  have hfiber :
      HasSum (fun m : ℤ ↦ 4 * integer_square_pole_series_term (2 * m) z)
        ((π / sin (π * (z / 2))) ^ (2 : ℕ)) := by
    -- Rewrite the ordinary half-argument series termwise as the even fiber at `z`.
    simpa [integer_square_pole_half_arg_term_eq] using hhalf
  -- Scale by `1 / 4` to recover the unweighted even fiber.
  have hscaled := hfiber.mul_left ((1 / 4 : ℂ))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Helper for Example 4: any integer-indexed series can be regrouped into its even and odd
branches. -/
lemma int_hasSum_even_add_odd {f : ℤ → ℂ} {a : ℂ} (hf : HasSum f a) :
    HasSum (fun m : ℤ ↦ f (2 * m) + f (2 * m + 1)) a := by
  -- Reindex by `Int.divModEquiv 2` so each integer is written as an even/odd pair.
  replace hf := ((Int.divModEquiv 2).symm.hasSum_iff).mpr hf
  dsimp [Function.comp_def] at hf
  refine hf.prod_fiberwise fun k => ?_
  dsimp only
  -- Collapse the finite parity fiber to the explicit two-term sum.
  convert! hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two]
  simp [mul_comm]

/-- Helper for Example 4: reindexing the ordinary square-pole series by `Int.divModEquiv 2`
packages it as the sum of its even and odd fibers. -/
lemma integer_square_pole_parity_hasSum {z : ℂ} (hz : z ∈ ℂ_ℤ) :
    HasSum
      (fun m : ℤ ↦ integer_square_pole_series_term (2 * m) z +
        integer_square_pole_series_term (2 * m + 1) z)
      ((π / sin (π * z)) ^ (2 : ℕ)) := by
  -- Apply the generic parity regrouping lemma to the ordinary square-pole series.
  simpa using
    int_hasSum_even_add_odd (f := fun n : ℤ ↦ integer_square_pole_series_term n z)
      (ordinary_integer_square_pole_hasSum hz)

/-- Helper for Example 4: the alternating square-pole series is `2 * (even fiber) - (full series)`
before the final half-angle simplification. -/
lemma alternating_integer_square_pole_series_hasSum_half_sub {z : ℂ} (hz : z ∈ ℂ_ℤ) :
    HasSum (fun n : ℤ ↦ alternating_integer_square_pole_series_term n z)
      ((1 / 2 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ) -
        (π / sin (π * z)) ^ (2 : ℕ)) := by
  -- Route correction: the unstable differentiation route is replaced by the source's direct
  -- half-argument parity decomposition `2 * even - full`.
  let f : ℤ → ℂ := fun n ↦ alternating_integer_square_pole_series_term n z
  have hsummable : Summable f := by
    -- The alternating series has the same termwise norms as the ordinary square-pole series.
    have hord := (ordinary_integer_square_pole_hasSum hz).summable
    refine Summable.of_norm_bounded hord.norm fun n ↦ ?_
    simp [f, alternating_integer_square_pole_series_term, integer_square_pole_series_term]
  have heven_scaled :
      HasSum (fun m : ℤ ↦ 2 * integer_square_pole_series_term (2 * m) z)
        ((1 / 2 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ)) := by
    -- Scale the even-fiber identity so it matches the source formula `2 * even - full`.
    have hscaled := (even_integer_square_pole_hasSum hz).mul_left (2 : ℂ)
    have hconst :
        (2 : ℂ) * ((1 / 4 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ)) =
          ((1 / 2 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ)) := by
      ring
    exact hconst ▸ hscaled
  have hpaired_raw :
      HasSum
        (fun m : ℤ ↦
          2 * integer_square_pole_series_term (2 * m) z -
            (integer_square_pole_series_term (2 * m) z +
              integer_square_pole_series_term (2 * m + 1) z))
        ((1 / 2 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ) -
          (π / sin (π * z)) ^ (2 : ℕ)) := by
    -- Subtract the full even/odd regrouping from twice the even branch.
    simpa using heven_scaled.sub (integer_square_pole_parity_hasSum hz)
  have hpaired :
      HasSum (fun m : ℤ ↦ f (2 * m) + f (2 * m + 1))
        ((1 / 2 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ) -
          (π / sin (π * z)) ^ (2 : ℕ)) := by
    -- Simplify the parity fibers using `(-1)^(2m) = 1` and `(-1)^(2m+1) = -1`.
    have hterm :
        (fun m : ℤ ↦
          2 * integer_square_pole_series_term (2 * m) z -
            (integer_square_pole_series_term (2 * m) z +
              integer_square_pole_series_term (2 * m + 1) z)) =
          (fun m : ℤ ↦ f (2 * m) + f (2 * m + 1)) := by
      funext m
      have hEvenPow : (-1 : ℂ) ^ (2 * m) = 1 := by
        exact Even.neg_one_zpow (show Even (2 * m) by exact ⟨m, by ring_nf⟩)
      have hOddPow : (-1 : ℂ) ^ (2 * m + 1) = -1 := by
        exact Odd.neg_one_zpow (show Odd (2 * m + 1) by exact ⟨m, by ring_nf⟩)
      simp [f, alternating_integer_square_pole_series_term, integer_square_pole_series_term,
        hEvenPow, sub_eq_add_neg]
      rw [hOddPow]
      ring
    exact hterm ▸ hpaired_raw
  have htsum :
      (∑' n : ℤ, f n) =
        ((1 / 2 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ) -
          (π / sin (π * z)) ^ (2 : ℕ)) := by
    -- Regrouping the summable alternating series by parity has the same sum, so uniqueness
    -- identifies the original `ℤ`-series with the paired closed form.
    exact (int_hasSum_even_add_odd hsummable.hasSum).unique hpaired
  exact (Summable.hasSum_iff hsummable).2 htsum

/-- Away from the integers, the alternating integer square-pole series has the displayed sum. -/
theorem alternating_integer_square_pole_series_hasSum {z : ℂ}
    (hz : z ∈ integerComplement) :
    HasSum (fun n : ℤ ↦ alternating_integer_square_pole_series_term n z)
      (π ^ 2 / (sin (π * z) * tan (π * z))) := by
  have hhalf : sin (π * (z / 2)) ≠ 0 := by
    simpa using sin_pi_mul_ne_zero (x := z / 2) (half_mem_integerComplement hz)
  have hsin : sin (π * z) ≠ 0 := by
    simpa using sin_pi_mul_ne_zero (x := z) hz
  have hcos_half : cos (π * (z / 2)) ≠ 0 := by
    -- If the half-angle cosine vanished, the double-angle sine would also vanish, contradicting
    -- `z ∈ integerComplement`.
    intro hcos
    have htwo : π * z = 2 * (π * (z / 2)) := by ring
    have : sin (π * z) = 0 := by
      rw [htwo, Complex.sin_two_mul, hcos]
      ring
    exact hsin this
  have hclosedform :
      ((1 / 2 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ) -
        (π / sin (π * z)) ^ (2 : ℕ)) =
        π ^ 2 / (sin (π * z) * tan (π * z)) := by
    -- Normalize the half-angle expression at `π * (z / 2)` and simplify the resulting rational
    -- identity directly.
    have htwo : π * z = 2 * (π * (z / 2)) := by ring
    have hrewrite :
        π ^ 2 / (sin (π * z) * tan (π * z)) =
          π ^ 2 * cos (π * z) / sin (π * z) ^ (2 : ℕ) := by
      rw [Complex.tan_eq_sin_div_cos, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      rw [pow_two, div_eq_mul_inv]
      field_simp [hsin]
    calc
      ((1 / 2 : ℂ) * (π / sin (π * (z / 2))) ^ (2 : ℕ) -
          (π / sin (π * z)) ^ (2 : ℕ))
        = π ^ 2 * cos (π * z) / sin (π * z) ^ (2 : ℕ) := by
            rw [htwo, Complex.sin_two_mul, Complex.cos_two_mul, pow_two]
            have hhalf' : sin (π * z / 2) ≠ 0 := by
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hhalf
            have hcos_half' : cos (π * z / 2) ≠ 0 := by
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcos_half
            field_simp [hhalf', hcos_half']
      _ = π ^ 2 / (sin (π * z) * tan (π * z)) := hrewrite.symm
  rw [← hclosedform]
  exact alternating_integer_square_pole_series_hasSum_half_sub hz

/-- Example 4 (1): for `z` away from the integers,
`∑ n : ℤ, (-1)^n / (z - n)^2 = π² / (sin (π z) tan (π z))`. -/
theorem alternating_integer_square_pole_series_eq {z : ℂ}
    (hz : z ∈ integerComplement) :
    (∑' n : ℤ, alternating_integer_square_pole_series_term n z) =
      π ^ 2 / (sin (π * z) * tan (π * z)) := by
  -- This is the direct `tsum_eq` wrapper around the main square-pole `HasSum`.
  exact (alternating_integer_square_pole_series_hasSum hz).tsum_eq

/-- The positive-`n` summand `(-1)^n 2z / (z^2 - n^2)` in the alternating partial fraction
expansion of `π / sin (π z)`. -/
def alternating_cosecant_partial_fraction_term (n : ℕ+) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ (n : ℕ) * ((2 * z) / (z ^ (2 : ℕ) - (n : ℂ) ^ (2 : ℕ)))

/-- Helper for Example 4: the alternating partial-fraction term matches the paired simple poles. -/
lemma alternating_cosecant_partial_fraction_term_eq (n : ℕ+) {z : ℂ}
    (hsub : z - n ≠ 0) (hadd : z + n ≠ 0) :
    alternating_cosecant_partial_fraction_term n z =
      (-1 : ℂ) ^ (n : ℕ) * (1 / (z - n) + 1 / (z + n)) := by
  -- This is the same partial-fraction identity as in Example 3, with the alternating sign factored
  -- out so later reindexing can work termwise.
  rw [alternating_cosecant_partial_fraction_term, one_div_add_one_div hsub hadd]
  congr 1
  ring

/-- Helper for Example 4: the half-angle cotangent difference is the cosecant closed form. -/
lemma pi_mul_cot_half_sub_eq_pi_div_sin {z : ℂ} (hz : z ∈ ℂ_ℤ) :
    π * cot (π * (z / 2)) - π * cot (π * z) = π / sin (π * z) := by
  have hhalf : sin (π * (z / 2)) ≠ 0 := by
    simpa using sin_pi_mul_ne_zero (x := z / 2) (half_mem_integerComplement hz)
  have hsin : sin (π * z) ≠ 0 := by
    simpa using sin_pi_mul_ne_zero (x := z) hz
  -- Rewrite the cotangents in terms of `sin` and `cos`, then simplify with the double-angle
  -- formulas at `π * (z / 2)`.
  calc
    π * cot (π * (z / 2)) - π * cot (π * z)
        = π * (cot (π * (z / 2)) - cot (π * z)) := by ring
    _ = π * (cos (π * (z / 2)) / sin (π * (z / 2)) - cos (π * z) / sin (π * z)) := by
        simp [Complex.cot]
    _ = π / sin (π * z) := by
        have htwo : π * z = 2 * (π * (z / 2)) := by ring
        rw [htwo, Complex.sin_two_mul, Complex.cos_two_mul]
        field_simp [hhalf, hsin]
        ring

/-- Helper for Example 4: a nat-indexed series can be regrouped into consecutive even/odd
pairs. -/
lemma nat_hasSum_even_add_odd {f : ℕ → ℂ} {a : ℂ} (hf : HasSum f a) :
    HasSum (fun m : ℕ ↦ f (2 * m) + f (2 * m + 1)) a := by
  -- Reindex by `Nat.divModEquiv 2` so every natural number is written as an even/odd pair.
  replace hf := ((Nat.divModEquiv 2).symm.hasSum_iff).mpr hf
  dsimp [Function.comp_def] at hf
  refine hf.prod_fiberwise fun k => ?_
  dsimp only
  -- Collapse the finite parity fiber to the explicit two-term sum.
  convert! hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two]
  simp [mul_comm]

/-- Helper for Example 4: after transporting to `ℕ`, the half-argument cotangent term picks out
the even positive branch of the original series. -/
lemma cotangent_half_arg_nat_term_eq {z : ℂ} (hz : z ∈ ℂ_ℤ) (m : ℕ) :
    cotangent_partial_fraction_term (pnatEquivNat.symm m) (z / 2) =
      2 * cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z := by
  have hhalf := half_mem_integerComplement hz
  have hsub_left :
      z / 2 - (pnatEquivNat.symm m : ℂ) ≠ 0 := by
    simpa [sub_eq_add_neg] using
      integerComplement_add_ne_zero hhalf (-(pnatEquivNat.symm m : ℤ))
  have hadd_left :
      z / 2 + (pnatEquivNat.symm m : ℂ) ≠ 0 := by
    simpa using integerComplement_add_ne_zero hhalf (pnatEquivNat.symm m : ℤ)
  have hsub_right :
      z - (pnatEquivNat.symm (2 * m + 1) : ℂ) ≠ 0 := by
    simpa [sub_eq_add_neg] using
      integerComplement_add_ne_zero hz (-(pnatEquivNat.symm (2 * m + 1) : ℤ))
  have hadd_right :
      z + (pnatEquivNat.symm (2 * m + 1) : ℂ) ≠ 0 := by
    simpa using integerComplement_add_ne_zero hz (pnatEquivNat.symm (2 * m + 1) : ℤ)
  have hsub_left' : z / 2 - (m + 1 : ℂ) ≠ 0 := by
    simpa [Equiv.pnatEquivNat] using hsub_left
  have hadd_left' : z / 2 + (m + 1 : ℂ) ≠ 0 := by
    simpa [Equiv.pnatEquivNat] using hadd_left
  have hsub_right' : z - (2 * (m + 1) : ℂ) ≠ 0 := by
    intro hzero
    apply hsub_right
    calc
      z - (pnatEquivNat.symm (2 * m + 1) : ℂ) = z - (2 * (m + 1) : ℂ) := by
        simp [Equiv.pnatEquivNat]
        ring
      _ = 0 := hzero
  have hadd_right' : z + (2 * (m + 1) : ℂ) ≠ 0 := by
    intro hzero
    apply hadd_right
    calc
      z + (pnatEquivNat.symm (2 * m + 1) : ℂ) = z + (2 * (m + 1) : ℂ) := by
        simp [Equiv.pnatEquivNat]
        ring
      _ = 0 := hzero
  have hden_left : (z / 2) ^ (2 : ℕ) - (m + 1 : ℂ) ^ (2 : ℕ) ≠ 0 := by
    intro hzero
    apply mul_ne_zero hsub_left' hadd_left'
    calc
      (z / 2 - (m + 1 : ℂ)) * (z / 2 + (m + 1 : ℂ))
          = (z / 2) ^ (2 : ℕ) - (m + 1 : ℂ) ^ (2 : ℕ) := by ring
      _ = 0 := hzero
  have hden_right : z ^ (2 : ℕ) - (2 * (m + 1) : ℂ) ^ (2 : ℕ) ≠ 0 := by
    intro hzero
    apply mul_ne_zero hsub_right' hadd_right'
    calc
      (z - (2 * (m + 1) : ℂ)) * (z + (2 * (m + 1) : ℂ))
          = z ^ (2 : ℕ) - (2 * (m + 1) : ℂ) ^ (2 : ℕ) := by ring
      _ = 0 := hzero
  -- Rewrite the transported indices as `m + 1`, then clear the scaled denominators directly.
  rw [cotangent_partial_fraction_term, cotangent_partial_fraction_term]
  simp [Equiv.pnatEquivNat]
  field_simp [hden_left, hden_right]
  ring

/-- Helper for Example 4: the transported alternating terms collapse to the half-angle branch
minus the full cotangent pair. -/
lemma alternating_cosecant_nat_pair_eq (m : ℕ) (z : ℂ) :
    alternating_cosecant_partial_fraction_term (pnatEquivNat.symm (2 * m)) z +
      alternating_cosecant_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z =
        2 * cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z -
          (cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m)) z +
            cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z) := by
  have hodd : (-1 : ℂ) ^ (2 * m + 1 : ℕ) = -1 := by
    simp [pow_add, pow_mul]
  have heven : (-1 : ℂ) ^ (2 * m + 1 + 1 : ℕ) = 1 := by
    simp [pow_add, pow_mul]
  -- The transported indices are `2m + 1` and `2m + 2`, so the signs are `-1` and `+1`.
  calc
    alternating_cosecant_partial_fraction_term (pnatEquivNat.symm (2 * m)) z +
        alternating_cosecant_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z =
          -cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m)) z +
            cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z := by
              simp [Equiv.pnatEquivNat, alternating_cosecant_partial_fraction_term,
                cotangent_partial_fraction_term, hodd, heven]
    _ =
        2 * cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z -
          (cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m)) z +
            cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z) := by
              ring

/-- Away from the integers, the positive-index alternating partial fraction series has the
displayed sum. -/
theorem alternating_cosecant_partial_fraction_hasSum {z : ℂ}
    (hz : z ∈ integerComplement) :
    HasSum (fun n : ℕ+ ↦ alternating_cosecant_partial_fraction_term n z)
      (π / sin (π * z) - 1 / z) := by
  -- Route correction: do all parity work on the nat-reindexed cotangent series, then transport
  -- the finished alternating identity back to `ℕ+` once.
  let f : ℕ → ℂ := fun m ↦ cotangent_partial_fraction_term (pnatEquivNat.symm m) z
  let h : ℕ → ℂ := fun m ↦ cotangent_partial_fraction_term (pnatEquivNat.symm m) (z / 2)
  let a : ℕ → ℂ := fun m ↦ alternating_cosecant_partial_fraction_term (pnatEquivNat.symm m) z
  have hf :
      HasSum f (π / tan (π * z) - 1 / z) := by
    -- First transport the ordinary cotangent partial fraction identity from `ℕ+` to `ℕ`.
    simpa [f, Function.comp_def] using
      (pnatEquivNat.symm.hasSum_iff).2 (cotangent_partial_fraction_hasSum hz)
  have hh :
      HasSum h (π / tan (π * (z / 2)) - 1 / (z / 2)) := by
    -- The same transport applies to the half-argument cotangent series.
    simpa [h, Function.comp_def] using
      (pnatEquivNat.symm.hasSum_iff).2
        (cotangent_partial_fraction_hasSum (half_mem_integerComplement hz))
  have hpaired_raw :
      HasSum (fun m : ℕ ↦ h m - (f (2 * m) + f (2 * m + 1)))
        ((π / tan (π * (z / 2)) - 1 / (z / 2)) - (π / tan (π * z) - 1 / z)) := by
    -- Subtract the full paired cotangent series from the half-angle cotangent series.
    exact hh.sub (nat_hasSum_even_add_odd hf)
  have hpaired :
      HasSum (fun m : ℕ ↦ a (2 * m) + a (2 * m + 1))
        ((π / tan (π * (z / 2)) - 1 / (z / 2)) - (π / tan (π * z) - 1 / z)) := by
    -- The nat-side helper lemmas isolate both the half-angle rewrite and the alternating sign
    -- algebra, so the paired series can be rewritten termwise.
    have hterm :
        (fun m : ℕ ↦ h m - (f (2 * m) + f (2 * m + 1))) =
          (fun m : ℕ ↦ a (2 * m) + a (2 * m + 1)) := by
      funext m
      have hhalf_term :
          cotangent_partial_fraction_term m.succPNat (z / 2) =
            2 * cotangent_partial_fraction_term (2 * m + 1).succPNat z := by
        simpa [Equiv.pnatEquivNat] using cotangent_half_arg_nat_term_eq hz m
      calc
        h m - (f (2 * m) + f (2 * m + 1)) =
            2 * cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z -
              (cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m)) z +
                cotangent_partial_fraction_term (pnatEquivNat.symm (2 * m + 1)) z) := by
              dsimp [h, f]
              rw [hhalf_term]
        _ = a (2 * m) + a (2 * m + 1) := by
              simpa [a, Equiv.pnatEquivNat] using (alternating_cosecant_nat_pair_eq m z).symm
    exact hterm ▸ hpaired_raw
  have hsummable :
      Summable a := by
    -- The alternating factor has norm `1`, so absolute convergence follows from the ordinary
    -- cotangent series.
    refine Summable.of_norm_bounded hf.summable.norm fun m ↦ ?_
    dsimp [a, f]
    rw [alternating_cosecant_partial_fraction_term, cotangent_partial_fraction_term, norm_mul]
    simp
  have hcot (w : ℂ) : π / tan (π * w) = π * cot (π * w) := by
    calc
      π / tan (π * w) = π * (tan (π * w))⁻¹ := by rw [div_eq_mul_inv]
      _ = π * ((cot (π * w))⁻¹)⁻¹ := by rw [← cot_inv_eq_tan]
      _ = π * cot (π * w) := by simp
  have hz0 : z ≠ 0 := integerComplement.ne_zero hz
  have hvalue :
      ((π / tan (π * (z / 2)) - 1 / (z / 2)) - (π / tan (π * z) - 1 / z)) =
        (π / sin (π * z) - 1 / z) := by
    have hdiv : (1 : ℂ) / (z / 2) = 2 / z := by
      field_simp [hz0]
    -- Rewrite the cotangent values first, then simplify the scalar correction `1 / (z / 2)`.
    calc
      ((π / tan (π * (z / 2)) - 1 / (z / 2)) - (π / tan (π * z) - 1 / z))
          = ((π * cot (π * (z / 2)) - 2 / z) - (π * cot (π * z) - 1 / z)) := by
              rw [hcot (z / 2), hcot z, hdiv]
      _ = (π * cot (π * (z / 2)) - π * cot (π * z)) - 1 / z := by ring
      _ = π / sin (π * z) - 1 / z := by rw [pi_mul_cot_half_sub_eq_pi_div_sin hz]
  have hnat :
      HasSum a (π / sin (π * z) - 1 / z) := by
    -- Regrouping the summable alternating series by parity does not change its sum, so
    -- uniqueness recovers the original nat-indexed series.
    refine (Summable.hasSum_iff hsummable).2 ?_
    exact ((nat_hasSum_even_add_odd hsummable.hasSum).unique hpaired).trans hvalue
  have hpnat :
      HasSum ((fun n : ℕ+ ↦ alternating_cosecant_partial_fraction_term n z) ∘ pnatEquivNat.symm)
        (π / sin (π * z) - 1 / z) := by
    simpa [a, Function.comp_def] using hnat
  simpa using (pnatEquivNat.symm.hasSum_iff).1 hpnat

/-- Example 4 (2): for `z` away from the integers,
`1 / z + ∑_{n ≥ 1} (-1)^n 2z / (z^2 - n^2) = π / sin (π z)`. -/
theorem alternating_cosecant_partial_fraction_eq {z : ℂ}
    (hz : z ∈ integerComplement) :
    1 / z + (∑' n : ℕ+, alternating_cosecant_partial_fraction_term n z) =
      π / sin (π * z) := by
  -- This is the direct `tsum_eq` wrapper around the alternating partial-fraction `HasSum`.
  rw [(alternating_cosecant_partial_fraction_hasSum hz).tsum_eq]
  abel
