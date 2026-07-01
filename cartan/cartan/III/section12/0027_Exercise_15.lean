import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Topology

-- Semantic recall note: a dedicated `lean_leansearch` tool was unavailable in this run, so the
-- owner names here were verified directly against the local mathlib sources.

/-- The meromorphic function `z ↦ 1 / (exp z - 1)` considered in this exercise. -/
def exercise15ExpReciprocal (z : ℂ) : ℂ :=
  1 / (Complex.exp z - 1)

/-- The pole `2 p π i` of `z ↦ 1 / (exp z - 1)`. -/
def exercise15Pole (p : ℤ) : ℂ :=
  (p : ℂ) * (2 * Real.pi * Complex.I)

private def exercise15LaurentCoeffRat : ℤ → ℚ
  | Int.negSucc 0 => 1
  | Int.negSucc (_ + 1) => 0
  | Int.ofNat n => PowerSeries.coeff (n + 1) (bernoulliPowerSeries ℚ)

/-- The Laurent coefficients at `0` of `z ↦ 1 / (exp z - 1)`, obtained by shifting the Bernoulli
generating series `z / (exp z - 1)` by one pole term. -/
def exercise15LaurentCoeff : ℤ → ℂ :=
  fun n ↦ (exercise15LaurentCoeffRat n : ℂ)

private theorem exercise15LaurentCoeffRat_nat_eq_bernoulli (n : ℕ) :
    exercise15LaurentCoeffRat (Int.ofNat n) =
      bernoulli (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℚ) := by
  simp [exercise15LaurentCoeffRat, bernoulliPowerSeries, PowerSeries.coeff_mk]

/-- On nonnegative indices, the Laurent coefficients agree with the Bernoulli generating-series
formula `B_{n + 1} / (n + 1)!`. -/
theorem exercise15LaurentCoeff_nat_eq_bernoulli (n : ℕ) :
    exercise15LaurentCoeff (Int.ofNat n) =
      ((bernoulli (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℚ)) : ℂ) := by
  change ↑(exercise15LaurentCoeffRat (Int.ofNat n)) =
    ((bernoulli (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℚ)) : ℂ)
  exact_mod_cast exercise15LaurentCoeffRat_nat_eq_bernoulli n

/-- The Bernoulli-number normalization `B_n` used in this exercise, recovered from the Laurent
coefficients. -/
def exercise15BernoulliNumber (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | n + 1 =>
      (-1 : ℚ) ^ n * ((Nat.factorial (2 * n + 2) : ℕ) : ℚ) *
        exercise15LaurentCoeffRat (Int.ofNat (2 * n + 1))

/-- The source Bernoulli normalization agrees with the canonical mathlib Bernoulli numbers. -/
theorem exercise15BernoulliNumber_eq_bernoulli (n : ℕ) :
    exercise15BernoulliNumber n = (-1 : ℚ) ^ (n - 1) * bernoulli (2 * n) := by
  cases n with
  | zero =>
      simp [exercise15BernoulliNumber]
  | succ n =>
      rw [exercise15BernoulliNumber, exercise15LaurentCoeffRat_nat_eq_bernoulli]
      field_simp
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul]

/-- The auxiliary kernel `1 / (z^(2 n) (exp z - 1))` from part (ii). -/
def exercise15EvenKernel (n : ℕ) (z : ℂ) : ℂ :=
  1 / (z ^ (2 * n) * (Complex.exp z - 1))

/-- The radius `(2 m + 1) π` of the square contour from part (ii). -/
def exercise15SquareRadius (m : ℕ) : ℝ :=
  ((2 * m + 1 : ℝ) * Real.pi)

/-- The perimeter of the square with vertices `± (2 m + 1) π ± (2 m + 1) π i`. -/
def exercise15SquareBoundary (m : ℕ) : Set ℂ :=
  {z | max |z.re| |z.im| = exercise15SquareRadius m}

/-- Exercise 15 (1): the function `z ↦ 1 / (exp z - 1)` is meromorphic on the whole complex
plane. -/
theorem exercise15_expReciprocal_meromorphic :
    Meromorphic exercise15ExpReciprocal := by
  intro z
  -- The denominator is analytic, hence meromorphic, and inversion preserves meromorphicity.
  unfold exercise15ExpReciprocal
  exact (MeromorphicAt.const 1 z).div ((by
    fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ Complex.exp w - 1) z).meromorphicAt)

/-- Helper for Exercise 15: the denominator `exp z - 1` has a simple zero at each pole
`2 p π i`. -/
theorem exercise15_exp_sub_one_order_one_at_pole (p : ℤ) :
    analyticOrderAt (fun z : ℂ ↦ Complex.exp z - 1) (exercise15Pole p) = 1 := by
  have hanalytic : AnalyticAt ℂ (fun z : ℂ ↦ Complex.exp z - 1) (exercise15Pole p) := by
    -- The denominator is analytic everywhere.
    fun_prop
  have hpole : Complex.exp (exercise15Pole p) - 1 = 0 := by
    -- The chosen points are the `2 π i`-periods of the exponential.
    simp [exercise15Pole, Complex.exp_int_mul_two_pi_mul_I]
  have hderiv : deriv (fun z : ℂ ↦ Complex.exp z - 1) (exercise15Pole p) ≠ 0 := by
    -- The derivative is `exp z`, which is `1` at the period points.
    simp [exercise15Pole, Complex.exp_int_mul_two_pi_mul_I]
  -- Analytic functions with a simple zero have analytic order `1`.
  exact hanalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hpole hderiv

/-- Exercise 15 (2): the points `2 p π i` are simple poles of `z ↦ 1 / (exp z - 1)`. -/
theorem exercise15_expReciprocal_pole_order (p : ℤ) :
    meromorphicOrderAt exercise15ExpReciprocal (exercise15Pole p) = (-1 : ℤ) := by
  -- Rewrite the reciprocal as an inverse so the inverse-order rule applies.
  have hinv :
      meromorphicOrderAt ((fun z : ℂ ↦ Complex.exp z - 1)⁻¹) (exercise15Pole p) = (-1 : ℤ) := by
    rw [meromorphicOrderAt_inv]
    -- The denominator is analytic, so its meromorphic order is its analytic order.
    have hanalytic : AnalyticAt ℂ (fun z : ℂ ↦ Complex.exp z - 1) (exercise15Pole p) := by
      fun_prop
    rw [hanalytic.meromorphicOrderAt_eq, exercise15_exp_sub_one_order_one_at_pole]
    norm_num
  have hrecip : exercise15ExpReciprocal = fun z : ℂ ↦ (Complex.exp z - 1)⁻¹ := by
    funext z
    simp [exercise15ExpReciprocal, one_div]
  rw [hrecip]
  exact hinv

/-- Helper for Exercise 15: shifting by an integral period leaves `1 / (exp z - 1)` unchanged. -/
theorem exercise15_expReciprocal_periodic_shift (p : ℤ) :
    exercise15ExpReciprocal = fun z ↦ exercise15ExpReciprocal (z - exercise15Pole p) := by
  funext z
  -- The exponential is `2 π i`-periodic, so the denominator is unchanged by the shift.
  simp [exercise15ExpReciprocal, exercise15Pole, Complex.exp_sub,
    Complex.exp_int_mul_two_pi_mul_I]

/-- Helper for Exercise 15: the simple pole at `0` has the standard normal form
`z ↦ z⁻¹ * φ z` with `φ` analytic and nonvanishing at the center. -/
theorem exercise15_regular_part_at_zero :
    ∃ c : ℕ → ℂ,
      ∃ φ : ℂ → ℂ,
        HasFPowerSeriesAt φ (.ofScalars ℂ c) 0 ∧
        c 0 ≠ 0 ∧
        exercise15ExpReciprocal =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ z⁻¹ * φ z := by
  -- Rebuild the standard simple-pole normal form directly from the order `-1` at the origin.
  have horder : meromorphicOrderAt exercise15ExpReciprocal 0 = (-1 : ℤ) :=
    by simpa [exercise15Pole] using exercise15_expReciprocal_pole_order 0
  have hne : meromorphicOrderAt exercise15ExpReciprocal 0 ≠ 0 := by
    rw [horder]
    norm_num
  have hmeromorphic : MeromorphicAt exercise15ExpReciprocal 0 := by
    exact meromorphicAt_of_meromorphicOrderAt_ne_zero hne
  obtain ⟨φ, hφ_an, hφ_ne, hφ_eq⟩ :=
    (meromorphicOrderAt_eq_int_iff hmeromorphic).1 horder
  refine ⟨fun n ↦ iteratedDeriv n φ 0 / n.factorial, φ, ?_, ?_, ?_⟩
  · -- Convert the analytic germ into its canonical scalar power series at the origin.
    exact hφ_an.hasFPowerSeriesAt
  · -- The constant coefficient is the center value of the analytic unit, hence is nonzero.
    simpa using hφ_ne
  · -- The order `-1` normal form is exactly the punctured-neighborhood identity `z⁻¹ * φ z`.
    simpa [smul_eq_mul, sub_eq_add_neg] using hφ_eq

/-- Helper for Exercise 15: the regular part `φ` satisfies the source identity
`φ z * (exp z - 1) = z` near the origin. -/
theorem exercise15_regular_part_mul_exp_sub_one_eq_id {c : ℕ → ℂ} {φ : ℂ → ℂ}
    (_hφ_series : HasFPowerSeriesAt φ (.ofScalars ℂ c) 0)
    (hφ_eq : exercise15ExpReciprocal =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ z⁻¹ * φ z) :
    (fun z : ℂ ↦ φ z * (Complex.exp z - 1)) =ᶠ[𝓝 (0 : ℂ)] fun z ↦ z := by
  let p : ℂ → Prop := fun z ↦ exercise15ExpReciprocal z = z⁻¹ * φ z
  have hφ_eq_nhds : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → p z := by
    -- Reinterpret the punctured-neighborhood identity as an implication on the ordinary
    -- neighborhood filter.
    simpa [p, Set.mem_setOf_eq] using (eventually_nhdsWithin_iff.mp hφ_eq)
  have hsmall : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), ‖z‖ < Real.pi := by
    -- Working in a ball of radius `π` excludes every nonzero period `2 π i n`.
    simpa using eventually_norm_sub_lt (0 : ℂ) Real.pi_pos
  filter_upwards [hφ_eq_nhds, hsmall] with z hz_eq hz_small
  by_cases hz : z = 0
  · -- At the center both sides of the product identity are visibly zero.
    simp [hz]
  · have hexp_ne : Complex.exp z - 1 ≠ 0 := by
      -- Any zero of `exp z - 1` is an integral multiple of `2 π i`, hence cannot lie in the
      -- small punctured ball unless it is the origin.
      intro hzero
      have hExp : Complex.exp z = 1 := sub_eq_zero.mp hzero
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hExp
      have hn0 : n ≠ 0 := by
        intro hn_zero
        apply hz
        simpa [hn_zero] using hn
      have him_le : |(n : ℝ)| * (2 * Real.pi) ≤ ‖z‖ := by
        have him :
            z.im = (n : ℝ) * (2 * Real.pi) := by
          rw [hn]
          simp [mul_comm, mul_left_comm]
        have htwo_pi_nonneg : 0 ≤ 2 * Real.pi := by positivity
        simpa [him, abs_mul, abs_of_nonneg htwo_pi_nonneg] using Complex.abs_im_le_norm z
      have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
        exact_mod_cast Int.one_le_abs hn0
      have hpi_le : Real.pi ≤ |(n : ℝ)| * (2 * Real.pi) := by
        nlinarith [Real.pi_pos, hnabs]
      exact (not_le_of_gt hz_small) (hpi_le.trans him_le)
    have hz_eq' : p z := hz_eq hz
    unfold p exercise15ExpReciprocal at hz_eq'
    have hcancel :
        1 = z⁻¹ * φ z * (Complex.exp z - 1) := by
      have hmul := congrArg (fun w : ℂ ↦ w * (Complex.exp z - 1)) hz_eq'
      simpa [one_div, mul_assoc, mul_comm, mul_left_comm, hexp_ne] using hmul
    have hscale := congrArg (fun w : ℂ ↦ z * w) hcancel
    have hscale' :
        z = (z * z⁻¹) * (φ z * (Complex.exp z - 1)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hscale
    -- Multiply first by `exp z - 1` and then by `z` to clear the two inverses separately.
    simpa [mul_assoc, hz] using hscale'.symm

/-- Helper for Exercise 15: the coefficients of `exp z - 1` are `1 / n!` with the constant
term removed. -/
theorem exercise15_exp_sub_one_coeff (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.exp ℂ - 1) =
      (((n.factorial : ℕ) : ℂ)⁻¹ - if n = 0 then 1 else 0) := by
  cases n with
  | zero =>
      -- At degree `0`, subtracting `1` removes the exponential's constant term.
      simp
  | succ n =>
      -- In positive degrees, only the factorial term from the exponential survives.
      simp

/-- Helper for Exercise 15: the Bernoulli generating series satisfies the same coefficient
convolution as the identity `B(X) * (exp X - 1) = X`. -/
theorem exercise15_bernoulli_coeff_convolution_identity (n : ℕ) :
    Finset.sum (Finset.range (n + 1))
        (fun k ↦
        PowerSeries.coeff k (bernoulliPowerSeries ℂ) *
          ((((n - k).factorial : ℕ) : ℂ)⁻¹ - if n - k = 0 then 1 else 0)) =
      if n = 1 then (1 : ℂ) else 0 := by
  have hcoeff :=
    congrArg (PowerSeries.coeff n) (bernoulliPowerSeries_mul_exp_sub_one (A := ℂ))
  rw [PowerSeries.coeff_mul] at hcoeff
  -- First rewrite the coefficients of `exp z - 1` on the antidiagonal product.
  simp only [exercise15_exp_sub_one_coeff, PowerSeries.coeff_X] at hcoeff
  have hreindex :
      (∑ x ∈ Finset.antidiagonal n,
          PowerSeries.coeff x.1 (bernoulliPowerSeries ℂ) *
            ((((x.2).factorial : ℕ) : ℂ)⁻¹ - if x.2 = 0 then 1 else 0)) =
        Finset.sum (Finset.range (n + 1))
          (fun k ↦
            PowerSeries.coeff k (bernoulliPowerSeries ℂ) *
              ((((n - k).factorial : ℕ) : ℂ)⁻¹ - if n - k = 0 then 1 else 0)) := by
    -- This is exactly the standard `antidiagonal`-to-`range` reindexing for Cauchy products.
    simpa using
      (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦
          PowerSeries.coeff i (bernoulliPowerSeries ℂ) *
            ((((j).factorial : ℕ) : ℂ)⁻¹ - if j = 0 then 1 else 0)) n)
  -- Rewrite the source-side antidiagonal convolution into the target `range` form.
  rw [hreindex] at hcoeff
  exact hcoeff

/-- Helper for Exercise 15: the centered bilinear multiplication series gives the analytic
product expansion of the regular part `φ` with `exp z - 1`. -/
theorem exercise15_regular_part_product_hasFPowerSeriesAt_centered
    {c dcoeff : ℕ → ℂ} {φ : ℂ → ℂ}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars ℂ c) 0)
    (hsub : HasFPowerSeriesAt (fun z : ℂ ↦ Complex.exp z - 1)
      (FormalMultilinearSeries.ofScalars ℂ dcoeff) 0) :
    HasFPowerSeriesAt (fun z : ℂ ↦ φ z * (Complex.exp z - 1))
      (((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (c 0, 0)).comp
        ((FormalMultilinearSeries.ofScalars ℂ c).prod
          (FormalMultilinearSeries.ofScalars ℂ dcoeff))) 0 := by
  have hφ0 : φ 0 = c 0 := by
    -- Read off the center value of the analytic regular part from its scalar series.
    have hzero := hφ_series.coeff_zero (fun _ ↦ (0 : ℂ))
    rw [FormalMultilinearSeries.ofScalars_apply_zero] at hzero
    simpa using hzero.symm
  have hprod :
      HasFPowerSeriesAt (fun z : ℂ ↦ (φ z, Complex.exp z - 1))
        ((FormalMultilinearSeries.ofScalars ℂ c).prod
          (FormalMultilinearSeries.ofScalars ℂ dcoeff)) 0 := by
    -- Package the two scalar series into a product-space series before applying bilinear
    -- multiplication.
    exact hφ_series.prod hsub
  have hmul :
      HasFPowerSeriesAt (fun x : ℂ × ℂ ↦ x.1 * x.2)
        ((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (φ 0, Complex.exp 0 - 1))
        (φ 0, Complex.exp 0 - 1) := by
    -- The multiplication map itself has its standard bilinear formal series at the true center.
    exact (ContinuousLinearMap.mul ℂ ℂ).hasFPowerSeriesAt_bilinear (φ 0, Complex.exp 0 - 1)
  have hcomp :
      HasFPowerSeriesAt
        ((fun x : ℂ × ℂ ↦ x.1 * x.2) ∘ fun z : ℂ ↦ (φ z, Complex.exp z - 1))
        (((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (φ 0, Complex.exp 0 - 1)).comp
          ((FormalMultilinearSeries.ofScalars ℂ c).prod
            (FormalMultilinearSeries.ofScalars ℂ dcoeff))) 0 := by
    -- Spell out the inner and outer functions so the composition theorem uses the intended
    -- product-space map.
    exact HasFPowerSeriesAt.comp
      (g := fun x : ℂ × ℂ ↦ x.1 * x.2)
      (f := fun z : ℂ ↦ (φ z, Complex.exp z - 1))
      (x := (0 : ℂ)) hmul hprod
  -- Route correction: compose first at the true product center, then rewrite that center to
  -- `(c 0, 0)` using the known constant terms.
  simpa [Function.comp, hφ0] using hcomp

/-- Helper for Exercise 15: the analytic regular part in the simple-pole decomposition has constant
coefficient `1`. -/
theorem exercise15_regular_part_coeff_zero_eq_one {c : ℕ → ℂ} {φ : ℂ → ℂ}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars ℂ c) 0)
    (hφ_eq : exercise15ExpReciprocal =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ z⁻¹ * φ z) :
    c 0 = 1 := by
  have hmul_id :
      (fun z : ℂ ↦ φ z * (Complex.exp z - 1)) =ᶠ[𝓝 (0 : ℂ)] fun z ↦ z := by
    -- The regular part satisfies the source identity `φ(z) (exp z - 1) = z`.
    exact exercise15_regular_part_mul_exp_sub_one_eq_id hφ_series hφ_eq
  have hderiv_id :
      deriv (fun z : ℂ ↦ φ z * (Complex.exp z - 1)) 0 = 1 := by
    -- Differentiate the eventual identity at the center to read off the first coefficient.
    simpa using (Filter.EventuallyEq.deriv_eq (x := (0 : ℂ)) hmul_id)
  have hφ0 : φ 0 = c 0 := by
    -- The constant coefficient of the scalar power series is exactly the center value.
    have hzero := hφ_series.coeff_zero (fun _ ↦ (0 : ℂ))
    rw [FormalMultilinearSeries.ofScalars_apply_zero] at hzero
    simpa using hzero.symm
  have hφ_diff : DifferentiableAt ℂ φ 0 := hφ_series.analyticAt.differentiableAt
  have hderiv_formula :
      deriv (fun z : ℂ ↦ φ z * (Complex.exp z - 1)) 0 = c 0 := by
    -- The product rule leaves only `φ(0)` because `exp 0 - 1 = 0` and `(exp z - 1)'|₀ = 1`.
    have hsub_diff : DifferentiableAt ℂ (fun z : ℂ ↦ Complex.exp z - 1) 0 := by
      fun_prop
    calc
      deriv (fun z : ℂ ↦ φ z * (Complex.exp z - 1)) 0 =
          deriv φ 0 * (Complex.exp 0 - 1) + φ 0 * deriv (fun z : ℂ ↦ Complex.exp z - 1) 0 := by
            simpa using
              (deriv_fun_mul (𝕜 := ℂ) (x := (0 : ℂ)) (c := φ)
                (d := fun z : ℂ ↦ Complex.exp z - 1) hφ_diff hsub_diff)
      _ = c 0 := by
          simp [hφ0]
  -- Comparing the two derivative computations fixes the constant term to `1`.
  exact hderiv_formula.symm.trans hderiv_id

/-- Helper for Exercise 15: removing the constant term and dividing by `z` shifts a Taylor series
tail by one index at any nonzero point. -/
theorem exercise15_shifted_tail_div_hasSum {bcoeff : ℕ → ℂ} {φz z : ℂ}
    (hφ : HasSum (fun n : ℕ ↦ bcoeff n * z ^ n) φz) (hz : z ≠ 0) :
    HasSum (fun n : ℕ ↦ bcoeff (n + 1) * z ^ n) (z⁻¹ * (φz - bcoeff 0)) := by
  have htail :
      HasSum (fun n : ℕ ↦ bcoeff (n + 1) * z ^ (n + 1)) (φz - bcoeff 0) := by
    -- Shifting the Taylor series by one removes its constant term.
    simpa using (hasSum_nat_add_iff' 1).mpr hφ
  -- Multiplying the shifted tail by `z⁻¹` cancels the extra power of `z`.
  have hscaled := htail.const_smul z⁻¹
  convert hscaled using 1 with n
  simp [smul_eq_mul, mul_assoc, mul_comm, hz, pow_succ]

/-- Helper for Exercise 15: on the punctured neighborhood, dividing an analytic germ by `z`
rewrites its Taylor expansion as a Laurent tail shifted by one degree. -/
theorem exercise15_shifted_tail_div_eventually_eq {bcoeff : ℕ → ℂ} {φ : ℂ → ℂ}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars ℂ bcoeff) 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      z⁻¹ * φ z = z⁻¹ * bcoeff 0 + ∑' n : ℕ, bcoeff (n + 1) * z ^ n := by
  rw [eventually_nhdsWithin_iff]
  have hsum :
      ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ ↦ bcoeff n * z ^ n) (φ z) := by
    -- Evaluate the scalar formal series at `z` to recover the ordinary Taylor sum.
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      hφ_series.eventually_hasSum_sub
  filter_upwards [hsum] with z hz_series hz_ne
  have htail := exercise15_shifted_tail_div_hasSum hz_series hz_ne
  -- Isolate the constant term, then replace the remaining tail by its shifted sum.
  calc
    z⁻¹ * φ z = z⁻¹ * (bcoeff 0 + (φ z - bcoeff 0)) := by simp
    _ = z⁻¹ * bcoeff 0 + z⁻¹ * (φ z - bcoeff 0) := by rw [mul_add]
    _ = z⁻¹ * bcoeff 0 + ∑' n : ℕ, bcoeff (n + 1) * z ^ n := by rw [htail.tsum_eq]

/-- Helper for Exercise 15: at the origin, `1 / (exp z - 1)` has the Bernoulli Laurent
expansion. -/
theorem exercise15_expReciprocal_laurent_at_zero :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      exercise15ExpReciprocal z =
        z⁻¹ + ∑' n : ℕ, exercise15LaurentCoeff (Int.ofNat n) * z ^ n :=
by
  -- Route correction: instead of normalizing the composed formal series term-by-term, extract the
  -- same source convolution from the iterated derivatives of `φ(z) * (exp z - 1) = z`.
  obtain ⟨c, φ, hφ_series, _hc_ne, hφ_eq⟩ := exercise15_regular_part_at_zero
  let dcoeff : ℕ → ℂ := fun n ↦ ((n.factorial : ℕ) : ℂ)⁻¹ - if n = 0 then 1 else 0
  let bcoeff : ℕ → ℂ := fun n ↦ PowerSeries.coeff n (bernoulliPowerSeries ℂ)
  have hmul_id :
      (fun z : ℂ ↦ φ z * (Complex.exp z - 1)) =ᶠ[𝓝 (0 : ℂ)] fun z ↦ z := by
    -- The regular part satisfies the same source product identity as in the textbook.
    exact exercise15_regular_part_mul_exp_sub_one_eq_id hφ_series hφ_eq
  have hc_eq_deriv : ∀ n : ℕ, c n = iteratedDeriv n φ 0 / n.factorial := by
    -- Read the scalar coefficients of `φ` from its analytic expansion via uniqueness.
    intro n
    have hcanonical :
        HasFPowerSeriesAt φ
          (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ iteratedDeriv m φ 0 / m.factorial)) 0 := by
      exact hφ_series.analyticAt.hasFPowerSeriesAt
    have hcoeff :=
      congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q.coeff n)
        (hφ_series.eq_formalMultilinearSeries hcanonical)
    simpa [FormalMultilinearSeries.coeff_ofScalars] using hcoeff
  have hiter_exp_sub_one : ∀ n : ℕ,
      iteratedDeriv n (fun z : ℂ ↦ Complex.exp z - 1) 0 = if n = 0 then 0 else 1 := by
    intro n
    cases n with
    | zero =>
        -- The constant term vanishes because `exp 0 - 1 = 0`.
        simp
    | succ n =>
        -- Every positive derivative agrees with the derivative of `exp`, hence equals `1` at `0`.
        have hconst :
            iteratedDeriv n.succ (fun z : ℂ ↦ Complex.exp z - 1) 0 =
              iteratedDeriv n.succ (fun z : ℂ ↦ Complex.exp z) 0 := by
          simpa [sub_eq_add_neg, add_comm] using
            (iteratedDeriv_const_add (x := (0 : ℂ)) (f := fun z : ℂ ↦ Complex.exp z)
              (n := n.succ) (show 0 < n.succ by simp) (-1 : ℂ))
        have hexp :
            iteratedDeriv n.succ (fun z : ℂ ↦ Complex.exp z) 0 = 1 := by
          simpa [Complex.exp_eq_exp_ℂ, one_mul] using
            congrFun (iteratedDeriv_cexp_const_mul n.succ (1 : ℂ)) 0
        rw [hconst, hexp]
        simp
  have hdcoeff_zero : dcoeff 0 = 0 := by
    -- The constant coefficient of `exp z - 1` vanishes.
    simp [dcoeff]
  have hdcoeff_one : dcoeff 1 = 1 := by
    -- The linear coefficient of `exp z - 1` is `1`.
    simp [dcoeff]
  have hbernoulli_conv :
      ∀ n : ℕ,
        Finset.sum (Finset.range (n + 1)) (fun k ↦ bcoeff k * dcoeff (n - k)) =
          if n = 1 then (1 : ℂ) else 0 := by
    intro n
    -- The Bernoulli power series already satisfies the required coefficient identity.
    simpa [bcoeff, dcoeff] using exercise15_bernoulli_coeff_convolution_identity n
  have hc_zero : c 0 = 1 := by
    -- The regular factor must start with constant term `1`.
    exact exercise15_regular_part_coeff_zero_eq_one hφ_series hφ_eq
  have hshift_regular :
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), z⁻¹ * φ z = z⁻¹ + ∑' n : ℕ, c (n + 1) * z ^ n := by
    -- Divide the regular Taylor series by `z` to expose the Laurent tail.
    filter_upwards [exercise15_shifted_tail_div_eventually_eq hφ_series] with z hz
    simpa [hc_zero] using hz
  have hlaurent_c :
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), exercise15ExpReciprocal z = z⁻¹ + ∑' n : ℕ, c (n + 1) * z ^ n := by
    -- Combine the simple-pole normal form with the shifted Taylor expansion of the regular part.
    filter_upwards [hφ_eq, hshift_regular] with z hz_eq hz_shift
    exact hz_eq.trans hz_shift
  have hiter_exp_sub_one_dcoeff :
      ∀ n : ℕ,
        iteratedDeriv n (fun z : ℂ ↦ Complex.exp z - 1) 0 = (n.factorial : ℂ) * dcoeff n := by
    intro n
    -- Rewrite the exponential derivatives into the normalized scalar coefficients `dcoeff`.
    rw [hiter_exp_sub_one n]
    cases n with
    | zero =>
        simp [dcoeff]
    | succ n =>
        have hfac_ne : (((n + 1).factorial : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (n + 1)
        simp [dcoeff, hfac_ne]
  have hproduct_convolution :
      ∀ n : ℕ,
        Finset.sum (Finset.range (n + 1))
            (fun k ↦ (Nat.choose n k : ℂ) * iteratedDeriv k φ 0 *
              iteratedDeriv (n - k) (fun z : ℂ ↦ Complex.exp z - 1) 0) =
          if n = 1 then (1 : ℂ) else 0 := by
    intro n
    -- Differentiate the source identity `φ(z) * (exp z - 1) = z` and evaluate at `0`.
    calc
      Finset.sum (Finset.range (n + 1))
          (fun k ↦ (Nat.choose n k : ℂ) * iteratedDeriv k φ 0 *
            iteratedDeriv (n - k) (fun z : ℂ ↦ Complex.exp z - 1) 0) =
        iteratedDeriv n (fun z : ℂ ↦ φ z * (Complex.exp z - 1)) 0 := by
          symm
          simpa [Pi.mul_apply] using
            (iteratedDeriv_mul (x := (0 : ℂ)) (n := n)
              (f := φ) (g := fun z : ℂ ↦ Complex.exp z - 1)
              hφ_series.analyticAt.contDiffAt (by fun_prop))
      _ = iteratedDeriv n (fun z : ℂ ↦ z) 0 := by
        rw [Filter.EventuallyEq.iteratedDeriv_eq (n := n) hmul_id]
      _ = if n = 1 then (1 : ℂ) else 0 := by
        simpa using (iteratedDeriv_fun_id_zero (n := n) (𝕜 := ℂ))
  have hpositive_conv :
      ∀ {n : ℕ}, 0 < n →
        Finset.sum (Finset.range (n + 1)) (fun k ↦ c k * dcoeff (n - k)) =
          if n = 1 then (1 : ℂ) else 0 := by
    intro n hn
    have hfactor :
        Finset.sum (Finset.range (n + 1))
            (fun k ↦ (Nat.choose n k : ℂ) * iteratedDeriv k φ 0 *
              iteratedDeriv (n - k) (fun z : ℂ ↦ Complex.exp z - 1) 0) =
          (n.factorial : ℂ) *
            Finset.sum (Finset.range (n + 1)) (fun k ↦ c k * dcoeff (n - k)) := by
      -- Normalize the Leibniz terms by replacing derivatives with factorial-scaled coefficients.
      calc
        Finset.sum (Finset.range (n + 1))
            (fun k ↦ (Nat.choose n k : ℂ) * iteratedDeriv k φ 0 *
              iteratedDeriv (n - k) (fun z : ℂ ↦ Complex.exp z - 1) 0) =
          Finset.sum (Finset.range (n + 1))
            (fun k ↦ (n.factorial : ℂ) * (c k * dcoeff (n - k))) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            have hphi_coeff : iteratedDeriv k φ 0 = (k.factorial : ℂ) * c k := by
              have hkfac_ne : (k.factorial : ℂ) ≠ 0 := by
                exact_mod_cast Nat.factorial_ne_zero k
              calc
                iteratedDeriv k φ 0 =
                    (iteratedDeriv k φ 0 / (k.factorial : ℂ)) * (k.factorial : ℂ) := by
                  field_simp [hkfac_ne]
                _ = c k * (k.factorial : ℂ) := by rw [hc_eq_deriv]
                _ = (k.factorial : ℂ) * c k := by ring
            rw [hphi_coeff, hiter_exp_sub_one_dcoeff]
            calc
              (↑(n.choose k) : ℂ) * ((k.factorial : ℂ) * c k) *
                  ((↑((n - k).factorial) : ℂ) * dcoeff (n - k)) =
                (((n.choose k : ℕ) * k.factorial * (n - k).factorial : ℕ) : ℂ) *
                  (c k * dcoeff (n - k)) := by
                  norm_num [Nat.cast_mul]
                  ring
              _ = (n.factorial : ℂ) * (c k * dcoeff (n - k)) := by
                  norm_num [Nat.choose_mul_factorial_mul_factorial hkn]
        _ = (n.factorial : ℂ) *
            Finset.sum (Finset.range (n + 1)) (fun k ↦ c k * dcoeff (n - k)) := by
            rw [Finset.mul_sum]
    have hfactor_rhs :
        (if n = 1 then (1 : ℂ) else 0) = (n.factorial : ℂ) * (if n = 1 then (1 : ℂ) else 0) := by
      -- For positive `n`, the right-hand side is already scaled by `n!`.
      by_cases h1 : n = 1
      · subst h1
        simp
      · simp [h1]
    have hmain :
        (n.factorial : ℂ) * Finset.sum (Finset.range (n + 1)) (fun k ↦ c k * dcoeff (n - k)) =
          (n.factorial : ℂ) * (if n = 1 then (1 : ℂ) else 0) := by
      rw [← hfactor, hproduct_convolution, ← hfactor_rhs]
    exact (mul_right_inj' (show (n.factorial : ℂ) ≠ 0 by
      exact_mod_cast Nat.factorial_ne_zero n)).1 hmain
  have hc_succ :
      ∀ n : ℕ,
        c (n + 1) = -Finset.sum (Finset.range (n + 1)) (fun k ↦ c k * dcoeff (n + 2 - k)) := by
    intro n
    have hconv : Finset.sum (Finset.range (n + 3)) (fun k ↦ c k * dcoeff (n + 2 - k)) = 0 := by
      simpa using hpositive_conv (n := n + 2) (by omega)
    -- Split off the `dcoeff 0` and `dcoeff 1` terms to isolate the next coefficient.
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hconv
    have hconv' :
        c (n + 1) + Finset.sum (Finset.range (n + 1)) (fun k ↦ c k * dcoeff (n + 2 - k)) = 0 := by
      simpa [hdcoeff_zero, hdcoeff_one, add_comm] using hconv
    exact eq_neg_of_add_eq_zero_left hconv'
  have hb_succ :
      ∀ n : ℕ,
        bcoeff (n + 1) =
          -Finset.sum (Finset.range (n + 1)) (fun k ↦ bcoeff k * dcoeff (n + 2 - k)) := by
    intro n
    have hconv : Finset.sum (Finset.range (n + 3)) (fun k ↦ bcoeff k * dcoeff (n + 2 - k)) = 0 := by
      simpa using hbernoulli_conv (n + 2)
    -- Apply the same two-term split to the Bernoulli coefficient convolution.
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hconv
    have hconv' :
        Finset.sum (Finset.range (n + 1)) (fun k ↦ bcoeff k * dcoeff (n + 2 - k)) +
          bcoeff (n + 1) = 0 := by
      simpa [hdcoeff_zero, hdcoeff_one, add_comm] using hconv
    exact eq_neg_of_add_eq_zero_right hconv'
  have hbcoeff_formula :
      ∀ n : ℕ, bcoeff n = ((bernoulli n / ((Nat.factorial n : ℕ) : ℚ)) : ℂ) := by
    intro n
    -- Unfold the Bernoulli power series coefficient once so later rewriting stays scalar-level.
    simp [bcoeff, bernoulliPowerSeries, PowerSeries.coeff_mk]
  have hcoeff_eq_bernoulli : ∀ n : ℕ, c n = bcoeff n := by
    intro n
    -- The regular-part coefficients and the Bernoulli coefficients satisfy the same recurrence.
    refine Nat.strong_induction_on n ?_
    intro n ih
    cases n with
    | zero =>
        simpa [bcoeff, bernoulliPowerSeries, PowerSeries.coeff_mk] using hc_zero
    | succ n =>
        calc
          c (n + 1) = -Finset.sum (Finset.range (n + 1)) (fun k ↦ c k * dcoeff (n + 2 - k)) :=
            hc_succ n
          _ = -Finset.sum (Finset.range (n + 1)) (fun k ↦ bcoeff k * dcoeff (n + 2 - k)) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hklt : k < n + 1 := Finset.mem_range.mp hk
              rw [ih k hklt]
          _ = bcoeff (n + 1) := (hb_succ n).symm
  have hcoeff_tail :
      ∀ n : ℕ, c (n + 1) = exercise15LaurentCoeff (Int.ofNat n) := by
    intro n
    -- Translate the Bernoulli coefficient at degree `n + 1` into the stored Laurent coefficient.
    calc
      c (n + 1) = bcoeff (n + 1) := hcoeff_eq_bernoulli (n + 1)
      _ = ((bernoulli (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℚ)) : ℂ) := by
            simpa using hbcoeff_formula (n + 1)
      _ = exercise15LaurentCoeff (Int.ofNat n) := by
            symm
            exact exercise15LaurentCoeff_nat_eq_bernoulli n
  filter_upwards [hlaurent_c] with z hz
  -- Replace the tail coefficients `c (n + 1)` by the Laurent coefficients identified above.
  calc
    exercise15ExpReciprocal z = z⁻¹ + ∑' n : ℕ, c (n + 1) * z ^ n := hz
    _ = z⁻¹ + ∑' n : ℕ, exercise15LaurentCoeff (Int.ofNat n) * z ^ n := by
          congr 1
          apply tsum_congr
          intro n
          rw [hcoeff_tail n]

/-- Exercise 15 (3): at each pole `2 p π i`, the Laurent expansion of `z ↦ 1 / (exp z - 1)` has
principal part `(z - 2 p π i)⁻¹` and the same regular coefficients as at `0`. -/
theorem exercise15_expReciprocal_laurent_expansion (p : ℤ) :
    ∀ᶠ z in 𝓝[≠] exercise15Pole p,
      exercise15ExpReciprocal z =
        (z - exercise15Pole p)⁻¹ +
          ∑' n : ℕ, exercise15LaurentCoeff (Int.ofNat n) * (z - exercise15Pole p) ^ n := by
  have hshift :
      exercise15ExpReciprocal =ᶠ[𝓝[≠] exercise15Pole p]
        fun z ↦ exercise15ExpReciprocal (z - exercise15Pole p) := by
    -- The periodicity bridge lets us translate the local problem back to the origin.
    exact Filter.Eventually.of_forall fun z ↦ congrFun (exercise15_expReciprocal_periodic_shift p) z
  have htrans_add :
      Filter.Tendsto (fun z : ℂ ↦ z + -exercise15Pole p)
        (𝓝[≠] exercise15Pole p) (𝓝[≠] (0 : ℂ)) := by
    -- Translation by `-exercise15Pole p` is a homeomorphism of the punctured neighborhood.
    have hmap : Filter.map (fun z : ℂ ↦ z + -exercise15Pole p) (𝓝[≠] exercise15Pole p) =
        𝓝[≠] (0 : ℂ) := by
      rw [show (0 : ℂ) = (Homeomorph.addRight (-exercise15Pole p)) (exercise15Pole p) by simp]
      exact (Homeomorph.addRight (-exercise15Pole p)).map_punctured_nhds_eq (exercise15Pole p)
    change Filter.map (fun z : ℂ ↦ z + -exercise15Pole p) (𝓝[≠] exercise15Pole p) ≤ 𝓝[≠] (0 : ℂ)
    simp [hmap]
  have hzero :
      (fun z : ℂ ↦ exercise15ExpReciprocal (z - exercise15Pole p)) =ᶠ[𝓝[≠] exercise15Pole p]
        fun z ↦
          (z - exercise15Pole p)⁻¹ +
            ∑' n : ℕ, exercise15LaurentCoeff (Int.ofNat n) * (z - exercise15Pole p) ^ n := by
    -- Compose the zero-centered Laurent expansion with the translation map.
    simpa [Function.comp, sub_eq_add_neg] using
      (Filter.EventuallyEq.comp_tendsto exercise15_expReciprocal_laurent_at_zero htrans_add)
  exact hshift.trans hzero

/-- Exercise 15 (4): in the Laurent expansion at `0`, every even coefficient beyond the constant
term vanishes. -/
theorem exercise15_expReciprocal_even_coeff_zero (q : ℕ) (hq : 1 ≤ q) :
    exercise15LaurentCoeff (Int.ofNat (2 * q)) = 0 := by
  have hodd : Odd (2 * q + 1) := ⟨q, by ring⟩
  have hgt : 1 < 2 * q + 1 := by omega
  rw [exercise15LaurentCoeff_nat_eq_bernoulli]
  simp [bernoulli_eq_zero_of_odd hodd hgt]

/-- Helper for Exercise 15: reindexing `Icc 1 n` by `u ↦ u + 1` turns it into `range n`. -/
theorem exercise15_sum_Icc_one_eq_sum_range_succ {α : Type*} [AddCommMonoid α]
    (n : ℕ) (f : ℕ → α) :
    Finset.sum (Finset.Icc 1 n) f = Finset.sum (Finset.range n) (fun u ↦ f (u + 1)) := by
  -- Reindex the closed interval by the successor map.
  symm
  refine Finset.sum_nbij' (i := fun u ↦ u + 1) (j := fun v ↦ v - 1) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_range, Finset.mem_Icc] at hu ⊢
    omega
  · intro v hv
    simp only [Finset.mem_range, Finset.mem_Icc] at hv ⊢
    omega
  · intro u hu
    simp
  · intro v hv
    have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
    simp [hv1]
  · intro u hu
    rfl

/-- Helper for Exercise 15: the even part of the shifted Bernoulli tail reindexes to `Icc 1 n`. -/
theorem exercise15_even_tail_reindex {α : Type*} [AddCommMonoid α]
    (n : ℕ) (f : ℕ → α) :
    Finset.sum ((Finset.range (2 * n - 1)).filter Even) (fun k ↦ f (k + 2)) =
      Finset.sum (Finset.Icc 1 n) (fun v ↦ f (2 * v)) := by
  -- Reindex the even tail by the source substitution `k = 2 v - 2`.
  symm
  refine Finset.sum_nbij' (i := fun v ↦ 2 * v - 2) (j := fun k ↦ k / 2 + 1) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hv ⊢
    constructor
    · omega
    · exact ⟨v - 1, by omega⟩
  · intro k hk
    rcases (Finset.mem_filter.mp hk).2 with ⟨t, rfl⟩
    have ht : t < n := by
      have hlt : t + t < 2 * n - 1 := Finset.mem_range.mp ((Finset.mem_filter.mp hk).1)
      omega
    have hdiv : (2 * t) / 2 = t := by simp
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro v hv
    have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
    have hmul : 2 * v - 2 = 2 * (v - 1) := by omega
    have hdiv : (2 * (v - 1)) / 2 = v - 1 := by simp
    calc
      (2 * v - 2) / 2 + 1 = (2 * (v - 1)) / 2 + 1 := by rw [hmul]
      _ = (v - 1) + 1 := by rw [hdiv]
      _ = v := by omega
  · intro k hk
    rcases (Finset.mem_filter.mp hk).2 with ⟨t, rfl⟩
    simp
    omega
  · intro v hv
    have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
    have harg : 2 * v - 2 + 2 = 2 * v := by omega
    rw [harg]

/-- Helper for Exercise 15: after removing the `k = 0, 1` terms from
`sum_bernoulli (2 * n + 1)`, only the even Bernoulli indices survive. -/
theorem exercise15_sum_bernoulli_odd_split_reindexed (n : ℕ) (hn : 1 ≤ n) :
    1 - ((2 * n + 1 : ℚ) / 2) +
      Finset.sum (Finset.Icc 1 n)
        (fun v ↦ (((2 * n + 1).choose (2 * v) : ℚ) * bernoulli (2 * v))) = 0 := by
  let F : ℕ → ℚ := fun k ↦ (((2 * n + 1).choose k : ℚ) * bernoulli k)
  have hsum : (∑ k ∈ Finset.range (2 * n + 1), F k) = 0 := by
    -- The textbook recurrence starts from the vanishing Bernoulli binomial sum at odd index.
    have hneq : ¬ (2 * n + 1 = 1) := by omega
    have hber := sum_bernoulli (2 * n + 1)
    rw [if_neg hneq] at hber
    simpa [F] using hber
  have htail :
      (∑ k ∈ Finset.range (2 * n - 1), F (k + 2)) =
        Finset.sum (Finset.Icc 1 n) (fun v ↦ F (2 * v)) := by
    -- Split the shifted tail into even and odd parts, then kill the odd part.
    calc
      ∑ k ∈ Finset.range (2 * n - 1), F (k + 2) =
          Finset.sum ((Finset.range (2 * n - 1)).filter Even) (fun k ↦ F (k + 2)) +
            Finset.sum ((Finset.range (2 * n - 1)).filter fun k ↦ ¬ Even k)
              (fun k ↦ F (k + 2)) := by
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * n - 1)) Even]
      _ = Finset.sum ((Finset.range (2 * n - 1)).filter Even) (fun k ↦ F (k + 2)) := by
        have hodd_zero :
            Finset.sum ((Finset.range (2 * n - 1)).filter fun k ↦ ¬ Even k)
              (fun k ↦ F (k + 2)) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro k hk
          have hkodd : Odd k := Nat.not_even_iff_odd.mp ((Finset.mem_filter.mp hk).2)
          have hkodd' : Odd (k + 2) := by
            rcases hkodd with ⟨t, rfl⟩
            exact ⟨t + 1, by ring⟩
          have hkgt : 1 < k + 2 := by omega
          simp [F, bernoulli_eq_zero_of_odd hkodd' hkgt]
        rw [hodd_zero, add_zero]
      _ = Finset.sum (Finset.Icc 1 n) (fun v ↦ F (2 * v)) := exercise15_even_tail_reindex n F
  -- Reassemble the source identity with the surviving even tail.
  rw [Finset.sum_range_eq_add_Ico _ (by omega)] at hsum
  rw [Finset.sum_Ico_eq_sum_range] at hsum
  have h2n : 2 * n + 1 - 1 = (2 * n - 1) + 1 := by omega
  rw [h2n, Finset.sum_range_succ'] at hsum
  have htail' :
      (∑ k ∈ Finset.range (2 * n - 1), F (1 + (k + 1))) =
        Finset.sum (Finset.Icc 1 n) (fun v ↦ F (2 * v)) := by
    simpa [add_assoc, add_left_comm, add_comm] using htail
  rw [htail'] at hsum
  simp [F, bernoulli_zero, bernoulli_one, add_comm] at hsum
  ring_nf at hsum
  have hrewrite :
      1 - ((2 * n + 1 : ℚ) / 2) +
          Finset.sum (Finset.Icc 1 n)
            (fun v ↦ (((2 * n + 1).choose (2 * v) : ℚ) * bernoulli (2 * v))) =
        (1 / 2 : ℚ) - n +
          Finset.sum (Finset.Icc 1 n)
            (fun v ↦ (((2 * n + 1).choose (2 * v) : ℚ) * bernoulli (2 * v))) := by
    ring
  rw [hrewrite]
  simpa [two_mul, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm] using hsum

/-- Helper for Exercise 15: dividing the odd Bernoulli coefficient identity by `(2 n + 1)!`
produces the factorial-normalized recurrence core. -/
theorem exercise15_bernoulli_recurrence_core (n : ℕ) (hn : 1 ≤ n) :
    1 / ((Nat.factorial (2 * n + 1) : ℕ) : ℚ) -
      1 / (2 * ((Nat.factorial (2 * n) : ℕ) : ℚ)) +
      Finset.sum (Finset.Icc 1 n) (fun v ↦
        bernoulli (2 * v) /
          (((Nat.factorial (2 * v) : ℕ) : ℚ) *
            ((Nat.factorial (2 * n - 2 * v + 1) : ℕ) : ℚ))) = 0 := by
  let fact : ℚ := ((Nat.factorial (2 * n + 1) : ℕ) : ℚ)
  have hsplit := exercise15_sum_bernoulli_odd_split_reindexed n hn
  have hdiv :
      (1 - ((2 * n + 1 : ℚ) / 2) +
          Finset.sum (Finset.Icc 1 n)
            (fun v ↦ (((2 * n + 1).choose (2 * v) : ℚ) * bernoulli (2 * v)))) / fact = 0 := by
    rw [hsplit, zero_div]
  -- Divide the whole coefficient identity by `(2 n + 1)!` and simplify each term separately.
  rw [sub_eq_add_neg, add_div, add_div, neg_div, Finset.sum_div] at hdiv
  have hsecond :
      ((2 * n + 1 : ℚ) / 2) / fact = 1 / (2 * ((Nat.factorial (2 * n) : ℕ) : ℚ)) := by
    have hfact :
        fact = (2 * n + 1 : ℚ) * ((Nat.factorial (2 * n) : ℕ) : ℚ) := by
      simp [fact, Nat.factorial_succ, Nat.cast_mul, mul_comm]
    rw [hfact]
    field_simp [fact]
  have hsum :
      Finset.sum (Finset.Icc 1 n)
          (fun v ↦ ((((2 * n + 1).choose (2 * v) : ℚ) * bernoulli (2 * v)) / fact)) =
      Finset.sum (Finset.Icc 1 n) (fun v ↦
        bernoulli (2 * v) /
          (((Nat.factorial (2 * v) : ℕ) : ℚ) *
            ((Nat.factorial (2 * n - 2 * v + 1) : ℕ) : ℚ))) := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    have hvn : v ≤ n := (Finset.mem_Icc.mp hv).2
    have hvle : 2 * v ≤ 2 * n + 1 := by omega
    have hchoose :
        (((2 * n + 1).choose (2 * v) : ℚ) *
            ((Nat.factorial (2 * v) : ℕ) : ℚ) *
            ((Nat.factorial (2 * n - 2 * v + 1) : ℕ) : ℚ)) = fact := by
      have hchoose_nat :
          (2 * n + 1).choose (2 * v) * Nat.factorial (2 * v) *
              Nat.factorial (2 * n - 2 * v + 1) =
            Nat.factorial (2 * n + 1) := by
        have hsub : 2 * n + 1 - 2 * v = 2 * n - 2 * v + 1 := by omega
        simpa [hsub] using (Nat.choose_mul_factorial_mul_factorial hvle)
      have hchoose_rat :
          (((2 * n + 1).choose (2 * v) * Nat.factorial (2 * v) *
              Nat.factorial (2 * n - 2 * v + 1) : ℕ) : ℚ) =
            (((Nat.factorial (2 * n + 1) : ℕ) : ℚ)) := by
        exact_mod_cast hchoose_nat
      simpa [Nat.cast_mul, fact, mul_assoc] using hchoose_rat
    have hchoose_ne : (((2 * n + 1).choose (2 * v) : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hvle
    have hfac_left_ne : (((Nat.factorial (2 * v) : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * v)
    have hfac_right_ne : (((Nat.factorial (2 * n - 2 * v + 1) : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * n - 2 * v + 1)
    rw [← hchoose]
    field_simp [hchoose_ne, hfac_left_ne, hfac_right_ne]
  rw [hsecond, hsum] at hdiv
  simpa [fact, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hdiv

/-- Exercise 15 (5): the Bernoulli numbers `B_n` attached to the Laurent coefficients satisfy the
textbook recurrence relation. -/
theorem exercise15_bernoulli_recurrence (n : ℕ) (hn : 1 ≤ n) :
    1 / ((Nat.factorial (2 * n + 1) : ℕ) : ℚ) -
      1 / (2 * ((Nat.factorial (2 * n) : ℕ) : ℚ)) +
      Finset.sum (Finset.Icc 1 n) (fun v ↦
        (-1 : ℚ) ^ (v - 1) * exercise15BernoulliNumber v /
          (((Nat.factorial (2 * v) : ℕ) : ℚ) *
            ((Nat.factorial (2 * n - 2 * v + 1) : ℕ) : ℚ))) = 0 := by
  -- The source recurrence is the factorial-normalized Bernoulli identity with the textbook sign
  -- convention rewritten through `exercise15BernoulliNumber`.
  have hsum :
      Finset.sum (Finset.Icc 1 n) (fun v ↦
        (-1 : ℚ) ^ (v - 1) * exercise15BernoulliNumber v /
          (((Nat.factorial (2 * v) : ℕ) : ℚ) *
            ((Nat.factorial (2 * n - 2 * v + 1) : ℕ) : ℚ))) =
      Finset.sum (Finset.Icc 1 n) (fun v ↦
        bernoulli (2 * v) /
          (((Nat.factorial (2 * v) : ℕ) : ℚ) *
            ((Nat.factorial (2 * n - 2 * v + 1) : ℕ) : ℚ))) := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    rw [exercise15BernoulliNumber_eq_bernoulli]
    ring_nf
    have hsquare : (-1 : ℚ) ^ ((v - 1) * 2) = 1 := by simp
    rw [hsquare, mul_one]
  rw [hsum]
  exact exercise15_bernoulli_recurrence_core n hn

/-- Helper for Exercise 15: points on the square boundary satisfy `exercise15SquareRadius m ≤ ‖z‖`.
-/
theorem exercise15_squareBoundary_radius_le_norm (m : ℕ) {z : ℂ}
    (hz : z ∈ exercise15SquareBoundary m) :
    exercise15SquareRadius m ≤ ‖z‖ := by
  -- The square boundary fixes the maximum of the real and imaginary absolute values.
  rw [exercise15SquareBoundary] at hz
  calc
    exercise15SquareRadius m = max |z.re| |z.im| := hz.symm
    _ ≤ ‖z‖ := max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)

/-- Helper for Exercise 15: on the square boundary, the denominator `exp z - 1` stays uniformly
away from zero. -/
theorem exercise15_exp_sub_one_lower_bound_on_squareBoundary (m : ℕ) {z : ℂ}
    (hz : z ∈ exercise15SquareBoundary m) :
    (1 / 2 : ℝ) ≤ ‖Complex.exp z - 1‖ := by
  let R : ℝ := exercise15SquareRadius m
  have hRpos : 0 < R := by
    -- The square radius is the positive odd multiple `(2 m + 1) π`.
    dsimp [R, exercise15SquareRadius]
    positivity
  have hRge_one : 1 ≤ R := by
    -- The radius is at least `π`, hence at least `1`.
    dsimp [R, exercise15SquareRadius]
    nlinarith [Real.two_le_pi]
  have hboundary : max |z.re| |z.im| = R := by
    simpa [R, exercise15SquareBoundary] using hz
  by_cases him : |z.im| = R
  · -- On the horizontal edges, `im z = ±(2 m + 1) π`, so the exponential becomes a negative real.
    rcases (abs_eq hRpos.le).mp him with him_pos | him_neg
    · have hexp_neg_real : Complex.exp z = -(Real.exp z.re : ℂ) := by
        have hRsplit : R = (m : ℝ) * (2 * Real.pi) + Real.pi := by
          dsimp [R, exercise15SquareRadius]
          ring
        have hsplit :
            (z.re : ℂ) + (R : ℂ) * Complex.I =
              ((z.re : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I)) + Real.pi * Complex.I := by
          rw [hRsplit]
          push_cast
          ring
        rw [← Complex.re_add_im z, him_pos, hsplit, Complex.exp_add_pi_mul_I, Complex.exp_add,
          Complex.exp_nat_mul_two_pi_mul_I]
        simp
      have hnorm :
          ‖Complex.exp z - 1‖ = Real.exp z.re + 1 := by
        -- The denominator is a negative real number of size `exp (re z) + 1`.
        rw [hexp_neg_real]
        calc
          ‖(-(Real.exp z.re : ℂ) - 1)‖ = ‖((-1 - Real.exp z.re : ℝ) : ℂ)‖ := by
            congr 1
            push_cast
            ring
          _ = Real.exp z.re + 1 := by
            have hexp_nonneg : 0 ≤ Real.exp z.re := (Real.exp_pos z.re).le
            have hnonpos : -1 - Real.exp z.re ≤ 0 := by nlinarith
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hnonpos]
            ring
      nlinarith [Real.exp_pos z.re, hnorm]
    · have hexp_neg_real : Complex.exp z = -(Real.exp z.re : ℂ) := by
        have hRsplit : -R = -((m : ℝ) * (2 * Real.pi)) - Real.pi := by
          dsimp [R, exercise15SquareRadius]
          ring
        have hsplit :
            (z.re : ℂ) + ((-R : ℝ) : ℂ) * Complex.I =
              ((z.re : ℂ) - (m : ℂ) * (2 * Real.pi * Complex.I)) - Real.pi * Complex.I := by
          rw [hRsplit]
          push_cast
          ring
        rw [← Complex.re_add_im z, him_neg, hsplit, Complex.exp_sub_pi_mul_I, Complex.exp_sub,
          Complex.exp_nat_mul_two_pi_mul_I]
        simp
      have hnorm :
          ‖Complex.exp z - 1‖ = Real.exp z.re + 1 := by
        -- The lower horizontal edge gives the same negative-real denominator.
        rw [hexp_neg_real]
        calc
          ‖(-(Real.exp z.re : ℂ) - 1)‖ = ‖((-1 - Real.exp z.re : ℝ) : ℂ)‖ := by
            congr 1
            push_cast
            ring
          _ = Real.exp z.re + 1 := by
            have hexp_nonneg : 0 ≤ Real.exp z.re := (Real.exp_pos z.re).le
            have hnonpos : -1 - Real.exp z.re ≤ 0 := by nlinarith
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hnonpos]
            ring
      nlinarith [Real.exp_pos z.re, hnorm]
  · have hre_abs : |z.re| = R := by
      -- Off the horizontal edges, the boundary condition forces the real part to attain `±R`.
      have hre_le : |z.re| ≤ R := by
        simpa [hboundary] using (le_max_left |z.re| |z.im|)
      have him_le : |z.im| ≤ R := by
        simpa [hboundary] using (le_max_right |z.re| |z.im|)
      by_contra hre_ne
      have hre_lt : |z.re| < R := lt_of_le_of_ne hre_le hre_ne
      have him_lt : |z.im| < R := lt_of_le_of_ne him_le him
      exact (ne_of_lt (max_lt_iff.mpr ⟨hre_lt, him_lt⟩)) hboundary
    rcases (abs_eq hRpos.le).mp hre_abs with hre_pos | hre_neg
    · -- On the right edge, `‖exp z - 1‖` dominates `‖exp z‖ - 1 = exp R - 1`.
      have hnorm_ge : Real.exp R - 1 ≤ ‖Complex.exp z - 1‖ := by
        simpa [Complex.norm_exp, hre_pos] using norm_sub_norm_le (Complex.exp z) (1 : ℂ)
      have hlarge : (1 / 2 : ℝ) ≤ Real.exp R - 1 := by
        have hexp_two : (2 : ℝ) < Real.exp R := by
          exact lt_of_lt_of_le Real.exp_one_gt_two (Real.exp_le_exp.mpr hRge_one)
        linarith
      exact hlarge.trans hnorm_ge
    · -- On the left edge, `‖exp z‖ = exp (-R)` is tiny, so `1 - exp (-R)` is a lower bound.
      have hnorm_ge : 1 - Real.exp (-R) ≤ ‖Complex.exp z - 1‖ := by
        simpa [norm_sub_rev, Complex.norm_exp, hre_neg] using
          norm_sub_norm_le (1 : ℂ) (Complex.exp z)
      have hsmall : Real.exp (-R) < (1 / 2 : ℝ) := by
        have hneg_le : -R ≤ (-1 : ℝ) := by linarith
        exact lt_of_le_of_lt (Real.exp_le_exp.mpr hneg_le) Real.exp_neg_one_lt_half
      linarith

/-- Exercise 15 (6): on the square contour `γ_m`, the kernel
`z ↦ 1 / (z^(2 n) (exp z - 1))` satisfies the stated uniform bound. -/
theorem exercise15_evenKernel_norm_bound_on_squareBoundary (n m : ℕ) (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ exercise15SquareBoundary m) :
    ‖exercise15EvenKernel n z‖ ≤ 2 / (exercise15SquareRadius m) ^ (2 * n) := by
  -- Route correction: prove the contour estimate by separating the denominator lower bound from
  -- the already-established radius lower bound for `‖z‖`.
  have _hn : 0 < n := Nat.succ_le_iff.mp hn
  let R : ℝ := exercise15SquareRadius m
  have hRpos : 0 < R := by
    -- The square radius is a positive odd multiple of `π`.
    dsimp [R, exercise15SquareRadius]
    positivity
  have hRle : R ≤ ‖z‖ := by
    simpa [R] using exercise15_squareBoundary_radius_le_norm m hz
  have hden : (1 / 2 : ℝ) ≤ ‖Complex.exp z - 1‖ :=
    exercise15_exp_sub_one_lower_bound_on_squareBoundary m hz
  have hpow : R ^ (2 * n) ≤ ‖z‖ ^ (2 * n) := by
    exact pow_le_pow_left₀ hRpos.le hRle _
  have hmul :
      R ^ (2 * n) * (1 / 2 : ℝ) ≤ ‖z‖ ^ (2 * n) * ‖Complex.exp z - 1‖ := by
    -- Multiply the `‖z‖` and denominator lower bounds to control the full kernel denominator.
    exact mul_le_mul hpow hden (by positivity) (pow_nonneg (norm_nonneg z) _)
  have hleft_pos : 0 < R ^ (2 * n) * (1 / 2 : ℝ) := by
    exact mul_pos (pow_pos hRpos _) (by norm_num)
  have hrecip :
      1 / (‖z‖ ^ (2 * n) * ‖Complex.exp z - 1‖) ≤ 1 / (R ^ (2 * n) * (1 / 2 : ℝ)) :=
    one_div_le_one_div_of_le hleft_pos hmul
  calc
    ‖exercise15EvenKernel n z‖ = 1 / (‖z‖ ^ (2 * n) * ‖Complex.exp z - 1‖) := by
      -- Taking norms turns the reciprocal kernel into the reciprocal of the product norm.
      rw [exercise15EvenKernel, one_div, norm_inv, norm_mul, norm_pow]
      rw [one_div]
    _ ≤ 1 / (R ^ (2 * n) * (1 / 2 : ℝ)) := hrecip
    _ = 2 / R ^ (2 * n) := by
      field_simp [pow_ne_zero _ hRpos.ne']
    _ = 2 / (exercise15SquareRadius m) ^ (2 * n) := by rfl

/-- Exercise 15 (7): integrating the kernels `z ↦ 1 / (z^(2 n) (exp z - 1))` around the square
contours yields the even zeta-value formula in terms of the source Bernoulli numbers. -/
theorem exercise15_even_zeta_value (n : ℕ) (hn : 1 ≤ n) :
    ∑' p : ℕ, 1 / ((p + 1 : ℝ) ^ (2 * n)) =
      (2 * Real.pi) ^ (2 * n) * (exercise15BernoulliNumber n : ℝ) /
        (2 * ((Nat.factorial (2 * n) : ℕ) : ℝ)) := by
  have h2n : 2 * n ≠ 0 := by omega
  have hshift :
      ∑' p : ℕ, 1 / ((p + 1 : ℝ) ^ (2 * n)) =
        ∑' p : ℕ, 1 / ((p : ℝ) ^ (2 * n)) := by
    have hshift' :
        ∑' p : ℕ, 1 / ((p : ℝ) ^ (2 * n)) =
          0 + ∑' p : ℕ, 1 / ((p + 1 : ℝ) ^ (2 * n)) := by
      simpa [h2n] using (hasSum_zeta_nat (Nat.ne_of_gt hn)).summable.tsum_eq_zero_add
    simpa using hshift'.symm
  have hsign : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n - 1) := by
    have hn' : n + 1 = n - 1 + 2 := by omega
    rw [hn', pow_add, show (-1 : ℝ) ^ 2 = 1 by norm_num, mul_one]
  calc
    ∑' p : ℕ, 1 / ((p + 1 : ℝ) ^ (2 * n))
      = ∑' p : ℕ, 1 / ((p : ℝ) ^ (2 * n)) := hshift
    _ = (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) *
          (bernoulli (2 * n) : ℝ) / (Nat.factorial (2 * n) : ℝ) :=
        (hasSum_zeta_nat (Nat.ne_of_gt hn)).tsum_eq
    _ = (2 * Real.pi) ^ (2 * n) * (exercise15BernoulliNumber n : ℝ) /
          (2 * ((Nat.factorial (2 * n) : ℕ) : ℝ)) := by
        have hB :
            (exercise15BernoulliNumber n : ℝ) =
              (((-1 : ℚ) ^ (n - 1) * bernoulli (2 * n) : ℚ) : ℝ) := by
          exact_mod_cast exercise15BernoulliNumber_eq_bernoulli n
        rw [hB, hsign]
        push_cast
        have htwo : (2 : ℝ) ^ (2 * n - 1) = 2 ^ (2 * n) * (1 / 2 : ℝ) := by
          have hpow : (2 : ℝ) ^ (2 * n) = 2 ^ (2 * n - 1) * 2 := by
            rw [show 2 * n = (2 * n - 1) + 1 by omega, pow_add]
            norm_num
          calc
            (2 : ℝ) ^ (2 * n - 1) = (2 ^ (2 * n - 1) * 2) * (1 / 2 : ℝ) := by ring
            _ = 2 ^ (2 * n) * (1 / 2 : ℝ) := by rw [hpow]
        rw [htwo]
        ring
