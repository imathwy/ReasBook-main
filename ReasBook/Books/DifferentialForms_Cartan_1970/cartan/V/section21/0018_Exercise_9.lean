import Mathlib
import DifferentialForms_Cartan_1970.cartan.V.section19.«0011_Proposition_5_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Topology

namespace PeriodPair

-- Semantic recall note: `lean_leansearch` was unavailable in this session; the source-facing
-- Cartan coefficients below are bridged to mathlib's canonical regular-part owner
-- `PeriodPair.weierstrassPExceptSeries 0 0` together with the lattice invariants `G`, `g₂`, `g₃`.

/-- The coefficient `a_{2n}` in Cartan's Laurent expansion
`℘(z) = z⁻² + a₂ z² + a₄ z⁴ + ···` at the origin. -/
def cartan_weierstrass_even_laurent_coeff (L : PeriodPair) (n : ℕ) : ℂ :=
  (L.weierstrassPExceptSeries 0 0).coeff (2 * n)

@[inherit_doc PeriodPair.cartan_weierstrass_even_laurent_coeff]
scoped[CartanWeierstrass] notation "a_[" L "](" n ")" =>
  PeriodPair.cartan_weierstrass_even_laurent_coeff L n

open scoped CartanWeierstrass

/-- Cartan's coefficient `a_{2n}` is the even-index coefficient of the canonical regular-part
power series of `℘` at the lattice point `0`. -/
theorem cartan_weierstrass_even_laurent_coeff_eq_G (L : PeriodPair) (n : ℕ) (hn : n ≠ 0) :
    a_[L](n) = (2 * n + 1 : ℂ) * L.G (2 * n + 2) := by
  simp [cartan_weierstrass_even_laurent_coeff, weierstrassPExceptSeries, sumInvPow_zero, hn]

/-- The coefficient `a₂` in Cartan's Laurent expansion is `g₂ / 20`. -/
theorem cartan_weierstrass_even_laurent_coeff_one (L : PeriodPair) :
    a_[L](1) = L.cartan_a₂ := by
  rw [L.cartan_weierstrass_even_laurent_coeff_eq_G 1 (by norm_num)]
  rw [cartan_a₂, g₂]
  field_simp
  ring

/-- The coefficient `a₄` in Cartan's Laurent expansion is `g₃ / 28`. -/
theorem cartan_weierstrass_even_laurent_coeff_two (L : PeriodPair) :
    a_[L](2) = L.cartan_a₄ := by
  rw [L.cartan_weierstrass_even_laurent_coeff_eq_G 2 (by norm_num)]
  rw [cartan_a₄, g₃]
  field_simp
  ring

/-- Helper for Exercise 9: the Laurent expansion of `℘` has no constant term in its regular part
at the origin. -/
lemma cartan_weierstrass_even_laurent_coeff_zero (L : PeriodPair) :
    a_[L](0) = 0 := by
  -- The degree-zero coefficient is the value of the regularized function `℘[L - 0]` at `0`.
  simp [cartan_weierstrass_even_laurent_coeff, weierstrassPExceptSeries]

/-- Helper for Exercise 9: after multiplying Cartan's cubic differential equation by `z^6`, the
regularized identity extends holomorphically across the pole at the origin. -/
lemma cartan_regularized_weierstrass_relation_eventually_zero (L : PeriodPair) :
    (fun z : ℂ ↦
      (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2 -
        4 * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3 +
        20 * L.cartan_a₂ * z ^ 4 * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) +
        28 * L.cartan_a₄ * z ^ 6) =ᶠ[𝓝 (0 : ℂ)] 0 := by
  -- Route correction: normalize the regularized expression to `z^6` times the cubic relation
  -- before using the differential equation for `(℘, ℘')` away from the lattice.
  filter_upwards [L.compl_lattice_diff_singleton_mem_nhds (0 : ℂ)] with z hz
  by_cases hz0 : z = 0
  · simp [hz0]
    ring_nf
  have hzL : z ∉ L.lattice := by
    simpa [hz0] using hz
  have hcubic :
      ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃ = 0 := by
    rw [L.derivWeierstrassP_sq z hzL]
    ring
  -- Rewrite the regularized terms to the cubic relation multiplied by `z^6`.
  rw [show
      (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2 -
          4 * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3 +
          20 * L.cartan_a₂ * z ^ 4 * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) +
          28 * L.cartan_a₄ * z ^ 6 =
        z ^ 6 * (℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃) by
      rw [L.twenty_mul_cartan_a₂, L.twenty_eight_mul_cartan_a₄]
      simp only [L.derivWeierstrassPExcept_def, L.weierstrassPExcept_def,
        ← ZeroMemClass.coe_zero L.lattice]
      simp [hz0]
      field_simp
      ring]
  simpa [hcubic]

/-- Helper for Exercise 9: the regularized function `z ↦ ℘[L - 0] z * z^2 + 1` takes the value
`1` at the origin. -/
lemma cartan_regularized_weierstrass_value (L : PeriodPair) :
    (℘[L - (0 : ℂ)] (0 : ℂ) * (0 : ℂ) ^ 2 + 1) = 1 := by
  -- The quadratic factor kills the constant term of the regularized `℘` germ.
  simp

/-- Helper for Exercise 9: the normalized even derivatives of the regularized `℘` germ recover
Cartan's Laurent coefficients directly. -/
lemma cartan_regularized_weierstrass_normalized_coeff (L : PeriodPair) (k : ℕ) :
    iteratedDeriv (2 * k) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 / (2 * k).factorial = a_[L](k) := by
  cases k with
  | zero =>
      -- The zero-th derivative is just the regularized value at `0`, which is the vanishing
      -- constant term of the regular part.
      simp [L.cartan_weierstrass_even_laurent_coeff_zero]
  | succ k =>
      -- For positive index, the analytic derivative formula is already a factorial multiple of
      -- the Eisenstein series term defining Cartan's coefficient.
      have hpos : 2 * Nat.succ k ≠ 0 := by omega
      have hfac : (((2 * Nat.succ k).factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (2 * Nat.succ k)
      rw [L.iteratedDeriv_weierstrassPExcept_self (l := (0 : ℂ)) (n := 2 * Nat.succ k)]
      rw [if_neg hpos, div_eq_iff hfac]
      rw [L.cartan_weierstrass_even_laurent_coeff_eq_G (Nat.succ k) (Nat.succ_ne_zero _)]
      simp [L.sumInvPow_zero, Nat.factorial_succ, Nat.cast_mul, mul_assoc]
      left
      ring

/-- Helper for Exercise 9: the normalized odd derivatives of the regularized `℘'` germ recover
the shifted Cartan coefficients. -/
lemma cartan_regularized_deriv_normalized_coeff_shift (L : PeriodPair) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 / (2 * k + 1).factorial =
      (2 * k + 2 : ℂ) * a_[L](k + 1) := by
  -- Rewrite the odd derivative explicitly, then identify the resulting `G`-term with
  -- Cartan's shifted Laurent coefficient.
  have hfac : (((2 * k + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
  rw [L.iteratedDeriv_derivWeierstrassPExcept_self (l := (0 : ℂ)) (n := 2 * k + 1)]
  rw [div_eq_iff hfac]
  rw [L.cartan_weierstrass_even_laurent_coeff_eq_G (k + 1) (Nat.succ_ne_zero _)]
  simp [L.sumInvPow_zero, Nat.factorial_succ, Nat.cast_mul, mul_assoc]
  ring

/-- Helper for Exercise 9: normalized iterated derivatives at `0` turn a product into the
antidiagonal convolution of normalized derivatives. -/
lemma cartan_iteratedDeriv_mul_factorial_at_zero {f g : ℂ → ℂ} {m : ℕ}
    (hf : ContDiffAt ℂ m f 0) (hg : ContDiffAt ℂ m g 0) :
    iteratedDeriv m (fun z ↦ f z * g z) 0 / m.factorial =
      Finset.sum (Finset.antidiagonal m) fun p ↦
        (iteratedDeriv p.1 f 0 / p.1.factorial) *
          (iteratedDeriv p.2 g 0 / p.2.factorial) := by
  -- Expand Leibniz first, then normalize each summand with the casted binomial/factorial identity.
  change iteratedDeriv m (f * g) 0 / m.factorial =
    Finset.sum (Finset.antidiagonal m) fun p ↦
      (iteratedDeriv p.1 f 0 / p.1.factorial) *
        (iteratedDeriv p.2 g 0 / p.2.factorial)
  rw [iteratedDeriv_mul hf hg, Finset.sum_div]
  calc
    ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (m - i) g 0) / m.factorial
        =
          ∑ i ∈ Finset.range (m + 1),
            (iteratedDeriv i f 0 / i.factorial) *
              (iteratedDeriv (m - i) g 0 / (m - i).factorial) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                rw [Nat.cast_choose ℂ hi']
                have hm : ((m.factorial : ℕ) : ℂ) ≠ 0 := by
                  exact_mod_cast Nat.factorial_ne_zero m
                field_simp [hm]
    _ =
          Finset.sum (Finset.antidiagonal m) fun p ↦
            (iteratedDeriv p.1 f 0 / p.1.factorial) *
              (iteratedDeriv p.2 g 0 / p.2.factorial) := by
                rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦
                  (iteratedDeriv i f 0 / i.factorial) *
                    (iteratedDeriv j g 0 / j.factorial))]

/-- Helper for Exercise 9: the even positive iterated derivatives of the regularized `℘` germ
recover Cartan's coefficients `a_[L](k)`. -/
lemma cartan_normalized_antidiagonal_pow_two_collapse (L : PeriodPair) (k : ℕ) :
    Finset.sum (Finset.antidiagonal (2 * k + 2)) (fun p ↦
      (iteratedDeriv p.1 (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 / p.1.factorial) *
        (iteratedDeriv p.2 (fun z : ℂ ↦ z ^ 2) 0 / p.2.factorial)) =
      a_[L](k) := by
  -- Collapse the antidiagonal to the unique index where the `z^2` derivative survives.
  rw [Finset.sum_eq_single (2 * k, 2)]
  · -- At the surviving boundary point, the `z^2` factor contributes exactly `1`.
    have hpow :
        iteratedDeriv 2 (fun z : ℂ ↦ z ^ 2) 0 / (2 : ℕ).factorial = 1 := by
      rw [iteratedDeriv_fun_pow_zero]
      norm_num
    calc
      (iteratedDeriv (2 * k) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 / (2 * k).factorial) *
          (iteratedDeriv 2 (fun z : ℂ ↦ z ^ 2) 0 / (2 : ℕ).factorial) =
        (iteratedDeriv (2 * k) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 / (2 * k).factorial) * 1 := by
          rw [hpow]
      _ = a_[L](k) := by
          simpa using L.cartan_regularized_weierstrass_normalized_coeff k
  · intro p hp hne
    -- Any other antidiagonal pair has `p.2 ≠ 2`, so the normalized `z^2` derivative vanishes.
    have hp_sum : p.1 + p.2 = 2 * k + 2 := by
      simpa using Finset.mem_antidiagonal.mp hp
    have hp2_ne : p.2 ≠ 2 := by
      intro hp2
      apply hne
      apply Prod.ext
      · omega
      · simpa [hp2]
    have hpow :
        iteratedDeriv p.2 (fun z : ℂ ↦ z ^ 2) 0 / p.2.factorial = 0 := by
      rw [iteratedDeriv_fun_pow_zero]
      simp [hp2_ne]
    rw [hpow, mul_zero]
  · intro hmem
    exfalso
    apply hmem
    simp

/-- Helper for Exercise 9: the even positive iterated derivatives of the regularized `℘` germ
recover Cartan's coefficients `a_[L](k)`. -/
lemma cartan_regularized_weierstrass_iteratedDeriv_even (L : PeriodPair) (k : ℕ) :
    iteratedDeriv (2 * k + 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ 2 + 1) 0 =
      (2 * k + 2).factorial * a_[L](k) :=
by
  have hfac : (((2 * k + 2).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k + 2)
  have hf : ContDiffAt ℂ (2 * k + 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 := by
    simpa using (L.analyticAt_weierstrassPExcept (0 : ℂ)).contDiffAt
  have hg : ContDiffAt ℂ (2 * k + 2) (fun z : ℂ ↦ z ^ 2) 0 := by
    fun_prop
  have hprod :
      iteratedDeriv (2 * k + 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ 2) 0 /
          (2 * k + 2).factorial =
        a_[L](k) := by
    -- Normalize the Leibniz expansion first, then collapse the antidiagonal to the unique
    -- `z^2` boundary term.
    calc
      iteratedDeriv (2 * k + 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ 2) 0 /
          (2 * k + 2).factorial =
          Finset.sum (Finset.antidiagonal (2 * k + 2)) (fun p ↦
            (iteratedDeriv p.1 (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 / p.1.factorial) *
              (iteratedDeriv p.2 (fun z : ℂ ↦ z ^ 2) 0 / p.2.factorial)) := by
            exact cartan_iteratedDeriv_mul_factorial_at_zero hf hg
      _ = a_[L](k) := L.cartan_normalized_antidiagonal_pow_two_collapse k
  -- Positive-order derivatives ignore the constant `1`, so the normalized product identity
  -- already gives the desired factorial form.
  rw [show
      iteratedDeriv (2 * k + 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ 2 + 1) 0 =
        iteratedDeriv (2 * k + 2) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ 2) 0 by
      simpa [add_comm] using
        (iteratedDeriv_const_add (f := fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ 2)
          (x := (0 : ℂ)) (n := 2 * k + 2) (c := (1 : ℂ)) (by positivity))]
  simpa [mul_comm] using (div_eq_iff hfac).mp hprod

/-- Helper for Exercise 9: the odd iterated derivatives of the regularized `℘` germ vanish at the
origin. -/
lemma cartan_regularized_weierstrass_iteratedDeriv_odd (L : PeriodPair) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ 2 + 1) 0 = 0 :=
by
  let f : ℂ → ℂ := fun z ↦ ℘[L - (0 : ℂ)] z * z ^ 2 + 1
  have hsymm : (fun z : ℂ ↦ f (-z)) = f := by
    -- The regularized `℘` germ is even, and the extra `z^2` factor preserves evenness.
    funext z
    calc
      f (-z) = ℘[L - (0 : ℂ)] z * (-z) ^ 2 + 1 := by
        simp [f, L.weierstrassPExcept_neg]
      _ = f z := by
        ring
  have hnegpow : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  -- Compare the odd derivative with itself after precomposing by `z ↦ -z`.
  have hcomp := iteratedDeriv_comp_neg (2 * k + 1) f 0
  rw [hsymm] at hcomp
  simpa [f, smul_eq_mul, hnegpow, ← CharZero.eq_neg_self_iff] using hcomp

/-- Helper for Exercise 9: the regularized derivative germ `z ↦ ℘'[L - 0] z * z^3 - 2` takes the
value `-2` at the origin. -/
lemma cartan_regularized_deriv_value (L : PeriodPair) :
    (℘'[L - (0 : ℂ)] (0 : ℂ) * (0 : ℂ) ^ 3 - 2) = -2 := by
  -- The cubic factor kills the analytic germ of `℘'[L - 0]` at the origin.
  simp

/-- Helper for Exercise 9: the even positive iterated derivatives of the regularized `℘'` germ are
factorial multiples of `(2 * k) * a_[L](k)`. -/
lemma cartan_normalized_antidiagonal_pow_three_collapse (L : PeriodPair) (k : ℕ) :
    Finset.sum (Finset.antidiagonal (2 * k + 4)) (fun p ↦
      (iteratedDeriv p.1 (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 / p.1.factorial) *
        (iteratedDeriv p.2 (fun z : ℂ ↦ z ^ 3) 0 / p.2.factorial)) =
      (2 * k + 2 : ℂ) * a_[L](k + 1) := by
  -- Collapse the shifted antidiagonal to the unique index where the `z^3` derivative survives.
  rw [Finset.sum_eq_single (2 * k + 1, 3)]
  · -- At the surviving boundary point, the `z^3` factor contributes exactly `1`.
    have hpow :
        iteratedDeriv 3 (fun z : ℂ ↦ z ^ 3) 0 / (3 : ℕ).factorial = 1 := by
      rw [iteratedDeriv_fun_pow_zero]
      norm_num
    calc
      (iteratedDeriv (2 * k + 1) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 / (2 * k + 1).factorial) *
          (iteratedDeriv 3 (fun z : ℂ ↦ z ^ 3) 0 / (3 : ℕ).factorial) =
        (iteratedDeriv (2 * k + 1) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 / (2 * k + 1).factorial) *
          1 := by
          rw [hpow]
      _ = (2 * k + 2 : ℂ) * a_[L](k + 1) := by
          simpa using L.cartan_regularized_deriv_normalized_coeff_shift k
  · intro p hp hne
    -- Any other antidiagonal pair has `p.2 ≠ 3`, so the normalized `z^3` derivative vanishes.
    have hp_sum : p.1 + p.2 = 2 * k + 4 := by
      simpa using Finset.mem_antidiagonal.mp hp
    have hp2_ne : p.2 ≠ 3 := by
      intro hp2
      apply hne
      apply Prod.ext
      · omega
      · simpa [hp2]
    have hpow :
        iteratedDeriv p.2 (fun z : ℂ ↦ z ^ 3) 0 / p.2.factorial = 0 := by
      rw [iteratedDeriv_fun_pow_zero]
      simp [hp2_ne]
    rw [hpow, mul_zero]
  · intro hmem
    exfalso
    apply hmem
    simp

/-- Helper for Exercise 9: the even positive iterated derivatives of the regularized `℘'` germ are
factorial multiples of `(2 * k) * a_[L](k)`. -/
lemma cartan_regularized_deriv_iteratedDeriv_even (L : PeriodPair) (k : ℕ) :
    iteratedDeriv (2 * k + 2) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3 - 2) 0 =
      (2 * k + 2).factorial * ((2 * k : ℂ) * a_[L](k)) :=
by
  cases k with
  | zero =>
      have hfac : (((2 : ℕ).factorial : ℕ) : ℂ) ≠ 0 := by norm_num
      have hf : ContDiffAt ℂ 2 (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 := by
        simpa using (L.analyticAt_derivWeierstrassPExcept (0 : ℂ)).contDiffAt
      have hg : ContDiffAt ℂ 2 (fun z : ℂ ↦ z ^ 3) 0 := by
        fun_prop
      have hprod :
          iteratedDeriv 2 (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3) 0 / (2 : ℕ).factorial = 0 := by
        -- At order `2`, every antidiagonal pair differentiates `z^3` too few or too many times.
        calc
          iteratedDeriv 2 (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3) 0 / (2 : ℕ).factorial =
              Finset.sum (Finset.antidiagonal 2) (fun p ↦
                (iteratedDeriv p.1 (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 / p.1.factorial) *
                  (iteratedDeriv p.2 (fun z : ℂ ↦ z ^ 3) 0 / p.2.factorial)) := by
                exact cartan_iteratedDeriv_mul_factorial_at_zero hf hg
          _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro p hp
            have hp_sum : p.1 + p.2 = 2 := by
              simpa using Finset.mem_antidiagonal.mp hp
            have hp2_ne : p.2 ≠ 3 := by omega
            have hpow :
                iteratedDeriv p.2 (fun z : ℂ ↦ z ^ 3) 0 / p.2.factorial = 0 := by
              rw [iteratedDeriv_fun_pow_zero]
              simp [hp2_ne]
            rw [hpow, mul_zero]
      have hprod_zero :
          iteratedDeriv 2 (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3) 0 = 0 := by
        rw [div_eq_iff hfac] at hprod
        simpa using hprod
      -- Positive-order derivatives kill the constant `-2`, so only the product term remains.
      rw [show
          iteratedDeriv 2 (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3 - 2) 0 =
            iteratedDeriv 2 (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3) 0 by
          simpa [sub_eq_add_neg, add_comm] using
            (iteratedDeriv_const_add
              (f := fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3)
              (x := (0 : ℂ)) (n := 2) (c := (-2 : ℂ)) (by norm_num))]
      simpa using hprod_zero
  | succ k =>
      have hidx : 2 * Nat.succ k + 2 = 2 * k + 4 := by
        omega
      have hfac : ((((2 * Nat.succ k + 2).factorial : ℕ)) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (2 * Nat.succ k + 2)
      have hf : ContDiffAt ℂ (2 * Nat.succ k + 2) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 := by
        simpa using (L.analyticAt_derivWeierstrassPExcept (0 : ℂ)).contDiffAt
      have hg : ContDiffAt ℂ (2 * Nat.succ k + 2) (fun z : ℂ ↦ z ^ 3) 0 := by
        fun_prop
      have hprod :
          iteratedDeriv (2 * Nat.succ k + 2) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3) 0 /
              (2 * Nat.succ k + 2).factorial =
            (2 * k + 2 : ℂ) * a_[L](k + 1) := by
        -- Route correction: use the shifted `z^3` antidiagonal collapse directly at order
        -- `2 * k + 4`, rather than trying to force the unshifted statement through `k = 0`.
        rw [hidx]
        calc
          iteratedDeriv (2 * k + 4) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3) 0 /
              (2 * k + 4).factorial =
            Finset.sum (Finset.antidiagonal (2 * k + 4)) (fun p ↦
              (iteratedDeriv p.1 (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 / p.1.factorial) *
                (iteratedDeriv p.2 (fun z : ℂ ↦ z ^ 3) 0 / p.2.factorial)) := by
              exact cartan_iteratedDeriv_mul_factorial_at_zero hf hg
          _ = (2 * k + 2 : ℂ) * a_[L](k + 1) := by
            exact L.cartan_normalized_antidiagonal_pow_three_collapse k
      -- Positive-order derivatives kill the constant `-2`, so we can clear the factorial.
      rw [show
          iteratedDeriv (2 * Nat.succ k + 2) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3 - 2) 0 =
            iteratedDeriv (2 * Nat.succ k + 2) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3) 0 by
          simpa [sub_eq_add_neg, add_comm] using
            (iteratedDeriv_const_add
              (f := fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3)
              (x := (0 : ℂ)) (n := 2 * Nat.succ k + 2) (c := (-2 : ℂ)) (by positivity))]
      rw [hidx]
      have hprod_zeroed := (div_eq_iff hfac).mp hprod
      have hprod_zeroed' :
          iteratedDeriv (2 * k + 4) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3) 0 =
            (2 * k + 2 : ℂ) * a_[L](k + 1) * (2 * k + 4).factorial := by
        convert hprod_zeroed using 1
      have hsucc_coeff : (2 * k + 2 : ℂ) = (2 * Nat.succ k : ℂ) := by
        simp [Nat.succ_eq_add_one]
        ring
      calc
        iteratedDeriv (2 * k + 4) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3) 0 =
            ((2 * k + 2 : ℂ) * a_[L](k + 1)) * (2 * k + 4).factorial := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hprod_zeroed'
        _ = (2 * k + 4).factorial * ((2 * k + 2 : ℂ) * a_[L](k + 1)) := by
              ring
        _ = (2 * k + 4).factorial * ((2 * Nat.succ k : ℂ) * a_[L](Nat.succ k)) := by
              rw [hsucc_coeff]

/-- Helper for Exercise 9: the odd iterated derivatives of the regularized `℘'` germ vanish at
the origin. -/
lemma cartan_regularized_deriv_iteratedDeriv_odd (L : PeriodPair) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ 3 - 2) 0 = 0 :=
by
  let f : ℂ → ℂ := fun z ↦ ℘'[L - (0 : ℂ)] z * z ^ 3 - 2
  have hsymm : (fun z : ℂ ↦ f (-z)) = f := by
    -- The regularized derivative germ is odd, so multiplying by `z^3` makes it even.
    funext z
    calc
      f (-z) = (-℘'[L - (0 : ℂ)] z) * (-z) ^ 3 - 2 := by
        simp [f, L.derivWeierstrassPExcept_neg]
      _ = f z := by
        ring
  have hnegpow : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  -- Compare the odd derivative with itself after precomposing by `z ↦ -z`.
  have hcomp := iteratedDeriv_comp_neg (2 * k + 1) f 0
  rw [hsymm] at hcomp
  simpa [f, smul_eq_mul, hnegpow, ← CharZero.eq_neg_self_iff] using hcomp

/-- Helper for Exercise 9: the cubic coefficient reindexing through `piAntidiag` matches
`Nat.antidiagonalTuple`. -/
lemma cartan_cube_piAntidiag_eq_antidiagonalTuple (L : PeriodPair) (n : ℕ) :
    Finset.sum (Finset.piAntidiag (Finset.univ : Finset (Fin 3)) n) (fun q ↦
      a_[L](q 0) * a_[L](q 1) * a_[L](q 2)) =
      Finset.sum (Finset.Nat.antidiagonalTuple 3 n) (fun q ↦
        a_[L](q 0) * a_[L](q 1) * a_[L](q 2)) := by
  -- Route correction: use the canonical `piAntidiag`-to-`antidiagonalTuple` identification
  -- instead of normalizing the cubic index set by hand.
  rw [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple]

/-- Helper for Exercise 9: the normalized coefficient of the square of the regularized
Weierstrass germ splits into the two boundary terms and the interior antidiagonal convolution. -/
lemma cartan_regularized_square_support_decomposition (L : PeriodPair) (r : ℕ) :
    Finset.sum (Finset.antidiagonal (2 * r + 4)) (fun p ↦
        (iteratedDeriv p.1 (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ) : ℂ)) 0 /
          ((p.1.factorial : ℕ) : ℂ)) *
          (iteratedDeriv p.2 (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ) : ℂ)) 0 /
            ((p.2.factorial : ℕ) : ℂ))) =
      2 * a_[L](r + 1) + Finset.sum (Finset.antidiagonal r) (fun p ↦ a_[L](p.1) * a_[L](p.2)) := by
  let B : ℂ → ℂ := fun z ↦ ℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ)
  let F : ℕ × ℕ → ℂ := fun p ↦
    (iteratedDeriv p.1 B 0 / ((p.1.factorial : ℕ) : ℂ)) *
      (iteratedDeriv p.2 B 0 / ((p.2.factorial : ℕ) : ℂ))
  have hnorm_zero : iteratedDeriv 0 B 0 / (((0 : ℕ).factorial : ℕ) : ℂ) = 1 := by
    -- The zero-th normalized derivative is just the value of the regularized germ at `0`.
    simpa [B] using L.cartan_regularized_weierstrass_value
  have hnorm_even (k : ℕ) :
      iteratedDeriv (2 * k + 2) B 0 / (((2 * k + 2).factorial : ℕ) : ℂ) = a_[L](k) := by
    have hfac : ((((2 * k + 2).factorial : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * k + 2)
    -- Normalize the positive even derivative using the previously proved factorial formula.
    refine (div_eq_iff hfac).2 ?_
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using
      L.cartan_regularized_weierstrass_iteratedDeriv_even k
  have hnorm_odd (k : ℕ) :
      iteratedDeriv (2 * k + 1) B 0 / (((2 * k + 1).factorial : ℕ) : ℂ) = 0 := by
    have hfac : ((((2 * k + 1).factorial : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
    -- Odd normalized derivatives vanish because the regularized germ is even.
    refine (div_eq_iff hfac).2 ?_
    simpa [B] using L.cartan_regularized_weierstrass_iteratedDeriv_odd k
  have hboundary_split :
      Finset.sum (Finset.antidiagonal (2 * r + 4)) F =
        Finset.sum
            ((Finset.antidiagonal (2 * r + 4)).filter (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0)) F +
          Finset.sum
            ((Finset.antidiagonal (2 * r + 4)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))) F := by
    -- First separate the two boundary pairs from the positive-support interior.
    simpa [Finset.sum_filter] using
      (Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal (2 * r + 4))
        (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0) F).symm
  have hboundary_set :
      (Finset.antidiagonal (2 * r + 4)).filter (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0) =
        {(0, 2 * r + 4), (2 * r + 4, 0)} := by
    -- On the fixed antidiagonal, having one coordinate equal to zero forces one of the two ends.
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpAnti, hpZero⟩
      have hpSum : p.1 + p.2 = 2 * r + 4 := by
        simpa using Finset.mem_antidiagonal.mp hpAnti
      rcases hpZero with hp1 | hp2
      · simp [hp1]
        left
        apply Prod.ext <;> omega
      · simp [hp2]
        right
        apply Prod.ext <;> omega
    · intro hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · simp [Finset.mem_antidiagonal]
      · have hp' : p = (2 * r + 4, 0) := by simpa using hp
        rw [hp']
        simp [Finset.mem_antidiagonal]
  have htop : iteratedDeriv (2 * r + 4) B 0 / ((((2 * r + 4).factorial : ℕ) : ℂ)) = a_[L](r + 1) := by
    -- The top even derivative is the `k = r + 1` case of the normalized even formula.
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnorm_even (r + 1)
  have hboundary :
      Finset.sum
          ((Finset.antidiagonal (2 * r + 4)).filter (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0)) F =
        2 * a_[L](r + 1) := by
    -- Evaluate the two boundary pairs `(0, 2r + 4)` and `(2r + 4, 0)` explicitly.
    rw [hboundary_set]
    simp [F, hnorm_zero, htop]
    ring
  have hinterior_split :
      Finset.sum
          ((Finset.antidiagonal (2 * r + 4)).filter
            (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))) F =
        Finset.sum
            (((Finset.antidiagonal (2 * r + 4)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) F +
          Finset.sum
            (((Finset.antidiagonal (2 * r + 4)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ ¬ Even p.1) F := by
    -- Next separate the interior into even-even support and odd-odd support.
    simpa [Finset.sum_filter] using
      (Finset.sum_filter_add_sum_filter_not
        ((Finset.antidiagonal (2 * r + 4)).filter (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0)))
        (fun p : ℕ × ℕ ↦ Even p.1) F).symm
  have hodd_support_zero :
      Finset.sum
          (((Finset.antidiagonal (2 * r + 4)).filter
            (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ ¬ Even p.1) F = 0 := by
    -- If the first coordinate is odd, its normalized derivative vanishes and kills the product.
    refine Finset.sum_eq_zero ?_
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpInterior, hpOdd⟩
    have hp_mem : p ∈ Finset.antidiagonal (2 * r + 4) := (Finset.mem_filter.mp hpInterior).1
    obtain hpEven | hpOdd' := p.1.even_or_odd
    · exact (hpOdd hpEven).elim
    · rcases hpOdd'.exists_bit1 with ⟨k, hk⟩
      simp [F, hk, hnorm_odd k]
  let e : ℕ × ℕ ↪ ℕ × ℕ :=
    ⟨fun q : ℕ × ℕ ↦ (2 * q.1 + 2, 2 * q.2 + 2), by
      intro q q' hqq'
      have h1 : 2 * q.1 + 2 = 2 * q'.1 + 2 := by
        simpa using congrArg Prod.fst hqq'
      have h2 : 2 * q.2 + 2 = 2 * q'.2 + 2 := by
        simpa using congrArg Prod.snd hqq'
      apply Prod.ext <;> omega⟩
  have hinterior_set :
      ((Finset.antidiagonal (2 * r + 4)).filter
        (fun p : ℕ × ℕ ↦ p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ Even p.1)) =
        (Finset.antidiagonal r).map e := by
    -- Positive even-even interior pairs are exactly `(2q₁ + 2, 2q₂ + 2)` with `q₁ + q₂ = r`.
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpAnti, hpPos⟩
      rcases hpPos with ⟨hp1, hpPos⟩
      rcases hpPos with ⟨hp2, hpEven⟩
      have hpSum : p.1 + p.2 = 2 * r + 4 := by
        simpa using Finset.mem_antidiagonal.mp hpAnti
      rcases hpEven with ⟨k, hk⟩
      have hkPos : 1 ≤ k := by
        omega
      let q : ℕ × ℕ := (k - 1, r + 1 - k)
      have hqMem : q ∈ Finset.antidiagonal r := by
        simp [q, Finset.mem_antidiagonal]
        omega
      refine Finset.mem_map.mpr ?_
      refine ⟨q, hqMem, ?_⟩
      ext <;> simp [e, q]
      · omega
      · omega
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨q, hqMem, hpEq⟩
      have hqSum : q.1 + q.2 = r := by
        simpa using Finset.mem_antidiagonal.mp hqMem
      have hpEq' : p = (2 * q.1 + 2, 2 * q.2 + 2) := by
        simpa [e] using hpEq.symm
      rw [hpEq']
      refine Finset.mem_filter.mpr ?_
      constructor
      · simp [Finset.mem_antidiagonal]
        omega
      · constructor
        · omega
        · constructor
          · omega
          · exact ⟨q.1 + 1, by omega⟩
  have hinterior_rewrite :
      (((Finset.antidiagonal (2 * r + 4)).filter
        (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) =
        ((Finset.antidiagonal (2 * r + 4)).filter
          (fun p : ℕ × ℕ ↦ p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ Even p.1)) := by
    -- Rewrite the nested filter into the single positive even-support predicate used above.
    ext p
    simp [and_assoc]
  have hinterior :
      Finset.sum
          (((Finset.antidiagonal (2 * r + 4)).filter
            (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) F =
        Finset.sum (Finset.antidiagonal r) (fun p ↦ a_[L](p.1) * a_[L](p.2)) := by
    -- Reindex the surviving interior support by the smaller antidiagonal `p.1 + p.2 = r`.
    rw [hinterior_rewrite, hinterior_set, Finset.sum_map]
    refine Finset.sum_congr rfl ?_
    intro q hq
    simp [F, e, hnorm_even q.1, hnorm_even q.2]
  -- Combine the boundary package, the odd-support vanishing, and the interior reindexing.
  calc
    Finset.sum (Finset.antidiagonal (2 * r + 4)) F =
        Finset.sum
            ((Finset.antidiagonal (2 * r + 4)).filter (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0)) F +
          Finset.sum
            ((Finset.antidiagonal (2 * r + 4)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))) F := hboundary_split
    _ =
        2 * a_[L](r + 1) +
          Finset.sum
            ((Finset.antidiagonal (2 * r + 4)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))) F := by
          rw [hboundary]
    _ =
        2 * a_[L](r + 1) +
          (Finset.sum
              (((Finset.antidiagonal (2 * r + 4)).filter
                (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) F +
            Finset.sum
              (((Finset.antidiagonal (2 * r + 4)).filter
                (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ ¬ Even p.1) F) := by
          rw [hinterior_split]
    _ =
        2 * a_[L](r + 1) +
          Finset.sum
            (((Finset.antidiagonal (2 * r + 4)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) F := by
          rw [hodd_support_zero, add_zero]
    _ = 2 * a_[L](r + 1) + Finset.sum (Finset.antidiagonal r) (fun p ↦ a_[L](p.1) * a_[L](p.2)) := by
          rw [hinterior]

/-- Helper for Exercise 9: the normalized coefficient of the square of the regularized
Weierstrass germ is the boundary contribution plus the interior antidiagonal convolution. -/
lemma cartan_regularized_square_normalized_coeff (L : PeriodPair) (r : ℕ) :
    iteratedDeriv (2 * r + 4) (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 2) 0 /
        (2 * r + 4).factorial =
      2 * a_[L](r + 1) + ∑ p ∈ Finset.antidiagonal r, a_[L](p.1) * a_[L](p.2) := by
  let B : ℂ → ℂ := fun z ↦ ℘[L - (0 : ℂ)] z * z ^ 2 + 1
  have hB : ContDiffAt ℂ (2 * r + 4) B 0 := by
    have hweier : ContDiffAt ℂ (2 * r + 4) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 := by
      simpa using (L.analyticAt_weierstrassPExcept (0 : ℂ)).contDiffAt
    have hzsq : ContDiffAt ℂ (2 * r + 4) (fun z : ℂ ↦ z ^ 2) 0 := by
      fun_prop
    have hprod : ContDiffAt ℂ (2 * r + 4) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ 2) 0 := by
      exact hweier.mul hzsq
    have hconst : ContDiffAt ℂ (2 * r + 4) (fun _ : ℂ ↦ (1 : ℂ)) 0 := by
      fun_prop
    -- The regularized germ `B` is holomorphic at the origin, so Leibniz applies directly.
    simpa [B] using hprod.add hconst
  -- Rewrite the square as `B * B`, apply normalized Leibniz, and then use the support
  -- decomposition proved just above.
  calc
    iteratedDeriv (2 * r + 4) (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 2) 0 /
        (2 * r + 4).factorial =
      ∑ p ∈ Finset.antidiagonal (2 * r + 4),
        (iteratedDeriv p.1 B 0 / p.1.factorial) * (iteratedDeriv p.2 B 0 / p.2.factorial) := by
          simpa [B, pow_two] using cartan_iteratedDeriv_mul_factorial_at_zero (f := B) (g := B) hB hB
    _ = 2 * a_[L](r + 1) + ∑ p ∈ Finset.antidiagonal r, a_[L](p.1) * a_[L](p.2) := by
          simpa [B] using cartan_regularized_square_support_decomposition L r

/-- Helper for Exercise 9: the normalized second derivative of the square of the regularized
Weierstrass germ vanishes. -/
lemma cartan_regularized_square_second_normalized_coeff (L : PeriodPair) :
    iteratedDeriv 2 (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 2) 0 /
        (2 : ℕ).factorial = (0 : ℂ) := by
  let B : ℂ → ℂ := fun z ↦ ℘[L - (0 : ℂ)] z * z ^ 2 + 1
  have hB : ContDiffAt ℂ 2 B 0 := by
    have hweier : ContDiffAt ℂ 2 (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 := by
      simpa using (L.analyticAt_weierstrassPExcept (0 : ℂ)).contDiffAt
    have hzsq : ContDiffAt ℂ 2 (fun z : ℂ ↦ z ^ 2) 0 := by
      fun_prop
    have hprod : ContDiffAt ℂ 2 (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ 2) 0 := by
      exact hweier.mul hzsq
    have hconst : ContDiffAt ℂ 2 (fun _ : ℂ ↦ (1 : ℂ)) 0 := by
      fun_prop
    -- The regularized germ is holomorphic at the origin, so its square is covered by Leibniz.
    simpa [B] using hprod.add hconst
  have hnorm_zero : iteratedDeriv 0 B 0 / (((0 : ℕ).factorial : ℕ) : ℂ) = 1 := by
    -- The zero-th normalized derivative is just the value of the regularized germ at `0`.
    simpa [B] using L.cartan_regularized_weierstrass_value
  have hnorm_one : iteratedDeriv 1 B 0 / (((1 : ℕ).factorial : ℕ) : ℂ) = 0 := by
    -- The odd derivative vanishes because the regularized germ is even.
    simp [B, L.cartan_regularized_weierstrass_iteratedDeriv_odd 0]
  have hnorm_two : iteratedDeriv 2 B 0 / (((2 : ℕ).factorial : ℕ) : ℂ) = 0 := by
    have hfac : ((((2 : ℕ).factorial : ℕ) : ℂ)) ≠ 0 := by
      norm_num
    -- The first positive even normalized derivative is `a_[L](0)`, which is zero.
    refine (div_eq_iff hfac).2 ?_
    simpa [B, L.cartan_weierstrass_even_laurent_coeff_zero, mul_comm, mul_left_comm, mul_assoc] using
      L.cartan_regularized_weierstrass_iteratedDeriv_even 0
  have hanti : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    native_decide
  have hvalue : B 0 = 1 := by
    -- Evaluate the regularized germ itself at the origin.
    simpa [B] using L.cartan_regularized_weierstrass_value
  have hderiv : deriv B 0 = 0 := by
    -- The first derivative is the odd case of the even regularized germ.
    simpa [B, iteratedDeriv_one] using L.cartan_regularized_weierstrass_iteratedDeriv_odd 0
  have hsecond : iteratedDeriv 2 B 0 / (2 : ℂ) = 0 := by
    -- The second normalized derivative is exactly the `a_[L](0)` term, which vanishes.
    simpa using hnorm_two
  -- Route correction: keep the source-faithful Leibniz expansion and kill the three low-order
  -- antidiagonal terms directly, rather than reopening the full square-support analysis.
  calc
    iteratedDeriv 2 (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 2) 0 / (2 : ℕ).factorial =
      ∑ p ∈ Finset.antidiagonal 2,
        (iteratedDeriv p.1 B 0 / p.1.factorial) *
          (iteratedDeriv p.2 B 0 / p.2.factorial) := by
            simpa [B, pow_two] using
              cartan_iteratedDeriv_mul_factorial_at_zero (f := B) (g := B) hB hB
    _ = 0 := by
      rw [hanti]
      simp [hvalue, hderiv, hsecond]

/-- Helper for Exercise 9: shifting the second coordinate of the antidiagonal convolution is the
same as summing over the next antidiagonal, because the omitted boundary term has `a_[L](0) = 0`.
-/
lemma cartan_shifted_antidiagonal_convolution (L : PeriodPair) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, a_[L](p.1) * a_[L](p.2 + 1) =
      ∑ q ∈ Finset.antidiagonal (n + 1), a_[L](q.1) * a_[L](q.2) := by
  -- Route correction: rewrite the larger antidiagonal by `antidiagonal_succ'`, so the shifted
  -- second coordinate is produced by the canonical `Nat.succ` map.
  rw [Finset.Nat.antidiagonal_succ']
  -- The only extra term is `(n + 1, 0)`, and it vanishes because Cartan's regular part has no
  -- constant term.
  simp [Nat.succ_eq_add_one, L.cartan_weierstrass_even_laurent_coeff_zero]

/-- Helper for Exercise 9: the nested cubic antidiagonal sum is the same as the canonical
three-index antidiagonal tuple sum. -/
lemma cartan_cube_nested_antidiagonal_reindex (L : PeriodPair) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, a_[L](p.1) *
        (∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2)) =
      ∑ q ∈ Finset.Nat.antidiagonalTuple 3 n, a_[L](q 0) * a_[L](q 1) * a_[L](q 2) := by
  calc
    ∑ p ∈ Finset.antidiagonal n, a_[L](p.1) *
        (∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2)) =
      ∑ p ∈ Finset.antidiagonal n,
        ∑ r ∈ Finset.antidiagonal p.2, a_[L](p.1) * a_[L](r.1) * a_[L](r.2) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro r hr
          ring
    _ =
      ∑ x ∈ (Finset.antidiagonal n).sigma (fun p ↦ Finset.antidiagonal p.2),
        a_[L](x.1.1) * a_[L](x.2.1) * a_[L](x.2.2) := by
          rw [Finset.sum_sigma']
    _ =
      ∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 3)) n,
        a_[L](q 0) * a_[L](q 1) * a_[L](q 2) := by
          refine Finset.sum_bij
            (fun x _ ↦ ![x.1.1, x.2.1, x.2.2]) ?_ ?_ ?_ ?_
          · intro x hx
            rcases Finset.mem_sigma.mp hx with ⟨hp, hr⟩
            have hp_sum : x.1.1 + x.1.2 = n := by
              simpa using Finset.mem_antidiagonal.mp hp
            have hr_sum : x.2.1 + x.2.2 = x.1.2 := by
              simpa using Finset.mem_antidiagonal.mp hr
            refine Finset.mem_piAntidiag.mpr ?_
            constructor
            · simp [Fin.sum_univ_succ, hp_sum, hr_sum, add_assoc]
            · intro i hi
              simp
          · intro x hx y hy hxy
            rcases x with ⟨p, r⟩
            rcases y with ⟨p', r'⟩
            rcases Finset.mem_sigma.mp hx with ⟨hp, hr⟩
            rcases Finset.mem_sigma.mp hy with ⟨hp', hr'⟩
            have hp₁ : p.1 = p'.1 := by
              simpa using congr_fun hxy 0
            have hr₁ : r.1 = r'.1 := by
              simpa using congr_fun hxy 1
            have hr₂ : r.2 = r'.2 := by
              simpa using congr_fun hxy 2
            have hp₂ : p.2 = p'.2 := by
              have hr_sum : r.1 + r.2 = p.2 := by
                simpa using Finset.mem_antidiagonal.mp hr
              have hr'_sum : r'.1 + r'.2 = p'.2 := by
                simpa using Finset.mem_antidiagonal.mp hr'
              omega
            have hp_eq : p = p' := Prod.ext hp₁ hp₂
            subst hp_eq
            congr
            exact Prod.ext hr₁ hr₂
          · intro q hq
            have hq_sum : q 0 + (q 1 + q 2) = n := by
              simpa [Fin.sum_univ_succ, add_assoc] using (Finset.mem_piAntidiag.mp hq).1
            refine ⟨⟨(q 0, q 1 + q 2), (q 1, q 2)⟩, ?_, ?_⟩
            · refine Finset.mem_sigma.mpr ?_
              constructor
              · simpa [Finset.mem_antidiagonal] using hq_sum
              · simp [Finset.mem_antidiagonal]
            · ext i
              fin_cases i <;> simp
          · intro x hx
            simp
    _ =
      ∑ q ∈ Finset.Nat.antidiagonalTuple 3 n, a_[L](q 0) * a_[L](q 1) * a_[L](q 2) := by
          simpa using L.cartan_cube_piAntidiag_eq_antidiagonalTuple n

/-- Helper for Exercise 9: the normalized coefficient of the cube of the regularized
Weierstrass germ splits into the two boundary packages and the interior convolution term. -/
lemma cartan_regularized_cube_support_decomposition (L : PeriodPair) (n : ℕ) :
    iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3) 0 /
        (2 * n + 6).factorial =
      a_[L](n + 2) +
        (2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
        ∑ p ∈ Finset.antidiagonal n,
          a_[L](p.1) *
            (2 * a_[L](p.2 + 1) + ∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2)) :=
by
  let B : ℂ → ℂ := fun z ↦ ℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ)
  let C : ℂ → ℂ := fun z ↦ B z ^ (2 : ℕ)
  let F : ℕ × ℕ → ℂ := fun p ↦
    (iteratedDeriv p.1 B 0 / ((p.1.factorial : ℕ) : ℂ)) *
      (iteratedDeriv p.2 C 0 / ((p.2.factorial : ℕ) : ℂ))
  have hB : ContDiffAt ℂ (2 * n + 6) B 0 := by
    have hweier : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 := by
      simpa using (L.analyticAt_weierstrassPExcept (0 : ℂ)).contDiffAt
    have hzsq : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ z ^ (2 : ℕ)) 0 := by
      fun_prop
    have hprod : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ (2 : ℕ)) 0 := by
      exact hweier.mul hzsq
    have hconst : ContDiffAt ℂ (2 * n + 6) (fun _ : ℂ ↦ (1 : ℂ)) 0 := by
      fun_prop
    -- The regularized Weierstrass germ is holomorphic at `0`.
    simpa [B] using hprod.add hconst
  have hC : ContDiffAt ℂ (2 * n + 6) C 0 := by
    -- The square term inherits the same differentiability at the origin.
    simpa [C] using hB.pow 2
  have hnormB_zero : iteratedDeriv 0 B 0 / (((0 : ℕ).factorial : ℕ) : ℂ) = 1 := by
    -- The zero-th normalized derivative is just the value `B(0) = 1`.
    simpa [B] using L.cartan_regularized_weierstrass_value
  have hnormB_even (k : ℕ) :
      iteratedDeriv (2 * k + 2) B 0 / (((2 * k + 2).factorial : ℕ) : ℂ) = a_[L](k) := by
    have hfac : ((((2 * k + 2).factorial : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * k + 2)
    -- Positive even derivatives of `B` recover the Laurent coefficients.
    refine (div_eq_iff hfac).2 ?_
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using
      L.cartan_regularized_weierstrass_iteratedDeriv_even k
  have hnormB_odd (k : ℕ) :
      iteratedDeriv (2 * k + 1) B 0 / (((2 * k + 1).factorial : ℕ) : ℂ) = 0 := by
    have hfac : ((((2 * k + 1).factorial : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
    -- Odd derivatives vanish because `B` is even.
    refine (div_eq_iff hfac).2 ?_
    simpa [B] using L.cartan_regularized_weierstrass_iteratedDeriv_odd k
  have hnormC_zero : iteratedDeriv 0 C 0 / (((0 : ℕ).factorial : ℕ) : ℂ) = 1 := by
    -- The square still takes the value `1` at the origin.
    simp [C, B, L.cartan_regularized_weierstrass_value]
  have hnormC_two : iteratedDeriv 2 C 0 / (((2 : ℕ).factorial : ℕ) : ℂ) = 0 := by
    -- The order-two normalized coefficient of `B^2` vanishes.
    simpa [C, B] using L.cartan_regularized_square_second_normalized_coeff
  have hB_zero : B 0 = 1 := by
    -- Evaluating `B` at the origin recovers the normalized regularized value.
    simpa [B] using L.cartan_regularized_weierstrass_value
  have hC_zero : C 0 = 1 := by
    -- Squaring the origin value still gives `1`.
    simp [C, hB_zero]
  have hC_two_zero : iteratedDeriv 2 C 0 = 0 := by
    have hfac2 : ((((2 : ℕ).factorial : ℕ) : ℂ)) ≠ 0 := by
      norm_num
    -- Clear the factorial from the normalized order-two vanishing statement.
    simpa using (div_eq_iff hfac2).mp hnormC_two
  have hnormC_even (k : ℕ) :
      iteratedDeriv (2 * k + 4) C 0 / (((2 * k + 4).factorial : ℕ) : ℂ) =
        2 * a_[L](k + 1) + ∑ p ∈ Finset.antidiagonal k, a_[L](p.1) * a_[L](p.2) := by
    -- Positive even derivatives of `B^2` are already packaged by the square lemma.
    simpa [C, B] using L.cartan_regularized_square_normalized_coeff k
  have hboundary_zero_split :
      Finset.sum (Finset.antidiagonal (2 * n + 6)) F =
        Finset.sum ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 = 0)) F +
          Finset.sum ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)) F := by
    -- First isolate the bottom boundary point where the square factor contributes its value.
    simpa [Finset.sum_filter] using
      (Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal (2 * n + 6))
        (fun p : ℕ × ℕ ↦ p.2 = 0) F).symm
  have hboundary_zero_set :
      (Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 = 0) =
        {(2 * n + 6, 0)} := by
    -- On the fixed antidiagonal, `p.2 = 0` forces the unique lower boundary point.
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpAnti, hpZero⟩
      have hpSum : p.1 + p.2 = 2 * n + 6 := by
        simpa using Finset.mem_antidiagonal.mp hpAnti
      simp [hpZero]
      apply Prod.ext <;> omega
    · intro hp
      rw [Finset.mem_singleton.mp hp]
      simp [Finset.mem_antidiagonal]
  have hbottom :
      Finset.sum ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 = 0)) F =
        a_[L](n + 2) := by
    have htopB :
        iteratedDeriv (2 * n + 6) B 0 / ((((2 * n + 6).factorial : ℕ) : ℂ)) = a_[L](n + 2) := by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnormB_even (n + 2)
    -- Evaluate the lower boundary point `(2 * n + 6, 0)` directly.
    rw [hboundary_zero_set]
    simp [F, htopB, hC_zero]
  have hboundary_top_split :
      Finset.sum ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)) F =
        Finset.sum
            (((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 = 0)) F +
          Finset.sum
            (((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 ≠ 0)) F := by
    -- Next isolate the top boundary point where the first factor contributes its value.
    simpa [Finset.sum_filter] using
      (Finset.sum_filter_add_sum_filter_not
        ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0))
        (fun p : ℕ × ℕ ↦ p.1 = 0) F).symm
  have hboundary_top_set :
      (((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
        (fun p : ℕ × ℕ ↦ p.1 = 0)) = {(0, 2 * n + 6)} := by
    -- With `p.2 ≠ 0`, the condition `p.1 = 0` forces the unique top boundary point.
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpNe, hpOne⟩
      have hpAnti : p ∈ Finset.antidiagonal (2 * n + 6) := (Finset.mem_filter.mp hpNe).1
      have hpSum : p.1 + p.2 = 2 * n + 6 := by
        simpa using Finset.mem_antidiagonal.mp hpAnti
      simp [hpOne]
      apply Prod.ext <;> omega
    · intro hp
      rw [Finset.mem_singleton.mp hp]
      simp [Finset.mem_antidiagonal]
  have htop :
      Finset.sum
          (((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
            (fun p : ℕ × ℕ ↦ p.1 = 0)) F =
        2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2) := by
    have htopC :
        iteratedDeriv (2 * n + 6) C 0 / ((((2 * n + 6).factorial : ℕ) : ℂ)) =
          2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2) := by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnormC_even (n + 1)
    -- Evaluate the top boundary point `(0, 2 * n + 6)` directly.
    rw [hboundary_top_set]
    simp [F, hB_zero, htopC]
  have hexception_split :
      Finset.sum
          (((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
            (fun p : ℕ × ℕ ↦ p.1 ≠ 0)) F =
        Finset.sum
            ((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 = 2)) F +
          Finset.sum
            ((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)) F := by
    -- Split off the exceptional `p.2 = 2` term before the interior reindexing.
    simpa [Finset.sum_filter] using
      (Finset.sum_filter_add_sum_filter_not
        (((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
          (fun p : ℕ × ℕ ↦ p.1 ≠ 0))
        (fun p : ℕ × ℕ ↦ p.2 = 2) F).symm
  have hexception_set :
      ((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
        (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 = 2)) = {(2 * n + 4, 2)} := by
    -- On the fixed antidiagonal, the exceptional order `p.2 = 2` is a single point.
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpPos, hpTwo⟩
      have hpAnti : p ∈ Finset.antidiagonal (2 * n + 6) := (Finset.mem_filter.mp (Finset.mem_filter.mp hpPos).1).1
      have hpSum : p.1 + p.2 = 2 * n + 6 := by
        simpa using Finset.mem_antidiagonal.mp hpAnti
      simp [hpTwo]
      apply Prod.ext <;> omega
    · intro hp
      rw [Finset.mem_singleton.mp hp]
      simp [Finset.mem_antidiagonal]
  have hexception :
      Finset.sum
          ((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
            (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 = 2)) F = 0 := by
    have htopB :
        iteratedDeriv (2 * n + 4) B 0 / ((((2 * n + 4).factorial : ℕ) : ℂ)) = a_[L](n + 1) := by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnormB_even (n + 1)
    -- The exceptional square term vanishes by the order-two square lemma.
    rw [hexception_set]
    simp [F, htopB, hC_two_zero]
  have hinterior_split :
      Finset.sum
          ((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
            (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)) F =
        Finset.sum
            (((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)).filter
              (fun p : ℕ × ℕ ↦ Even p.1)) F +
          Finset.sum
            (((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)).filter
              (fun p : ℕ × ℕ ↦ ¬ Even p.1)) F := by
    -- Route correction: split the cube support before any large simp, so the interior is handled
    -- by one clean reindexing instead of a brittle filtered antidiagonal normalization.
    simpa [Finset.sum_filter] using
      (Finset.sum_filter_add_sum_filter_not
        ((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
          (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2))
        (fun p : ℕ × ℕ ↦ Even p.1) F).symm
  have hodd_support_zero :
      Finset.sum
          (((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
            (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)).filter
            (fun p : ℕ × ℕ ↦ ¬ Even p.1)) F = 0 := by
    -- Odd first coordinates force the normalized derivative of `B` to vanish.
    refine Finset.sum_eq_zero ?_
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpRest, hpOdd⟩
    obtain hpEven | hpOdd' := p.1.even_or_odd
    · exact (hpOdd hpEven).elim
    · rcases hpOdd'.exists_bit1 with ⟨k, hk⟩
      simp [F, hk, hnormB_odd k]
  have hinterior_rewrite :
      (((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
        (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)).filter
        (fun p : ℕ × ℕ ↦ Even p.1)) =
        ((Finset.antidiagonal (2 * n + 6)).filter
          (fun p : ℕ × ℕ ↦ p.2 ≠ 0 ∧ p.1 ≠ 0 ∧ p.2 ≠ 2 ∧ Even p.1)) := by
    -- Rewrite the nested filters into a single support predicate for the final reindexing.
    ext p
    simp [and_assoc, and_left_comm, and_comm]
  let e : ℕ × ℕ ↪ ℕ × ℕ :=
    ⟨fun q : ℕ × ℕ ↦ (2 * q.1 + 2, 2 * q.2 + 4), by
      intro q q' hqq'
      have h1 : 2 * q.1 + 2 = 2 * q'.1 + 2 := by
        simpa using congrArg Prod.fst hqq'
      have h2 : 2 * q.2 + 4 = 2 * q'.2 + 4 := by
        simpa using congrArg Prod.snd hqq'
      apply Prod.ext <;> omega⟩
  have hinterior_set :
      ((Finset.antidiagonal (2 * n + 6)).filter
        (fun p : ℕ × ℕ ↦ p.2 ≠ 0 ∧ p.1 ≠ 0 ∧ p.2 ≠ 2 ∧ Even p.1)) =
        (Finset.antidiagonal n).map e := by
    -- The surviving interior is exactly `(2 * i + 2, 2 * j + 4)` with `i + j = n`.
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpAnti, hpData⟩
      rcases hpData with ⟨hp2, hp1, hp2two, hpEven⟩
      have hpSum : p.1 + p.2 = 2 * n + 6 := by
        simpa using Finset.mem_antidiagonal.mp hpAnti
      rcases hpEven with ⟨k, hk⟩
      have hk_pos : 1 ≤ k := by
        omega
      have hk_le : k ≤ n + 1 := by
        omega
      let q : ℕ × ℕ := (k - 1, n + 1 - k)
      have hqMem : q ∈ Finset.antidiagonal n := by
        simp [q, Finset.mem_antidiagonal]
        omega
      refine Finset.mem_map.mpr ?_
      refine ⟨q, hqMem, ?_⟩
      ext <;> simp [e, q, hk]
      · omega
      · omega
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨q, hqMem, hpEq⟩
      have hqSum : q.1 + q.2 = n := by
        simpa using Finset.mem_antidiagonal.mp hqMem
      have hpEq' : p = (2 * q.1 + 2, 2 * q.2 + 4) := by
        simpa [e] using hpEq.symm
      rw [hpEq']
      refine Finset.mem_filter.mpr ?_
      constructor
      · simp [Finset.mem_antidiagonal]
        omega
      · constructor
        · omega
        · constructor
          · omega
          · constructor
            · omega
            · exact ⟨q.1 + 1, by omega⟩
  have hinterior :
      Finset.sum
          (((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
            (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)).filter
            (fun p : ℕ × ℕ ↦ Even p.1)) F =
        ∑ p ∈ Finset.antidiagonal n,
          a_[L](p.1) *
            (2 * a_[L](p.2 + 1) + ∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2)) := by
    -- Reindex the interior support by the smaller antidiagonal after the even shifts.
    rw [hinterior_rewrite, hinterior_set, Finset.sum_map]
    refine Finset.sum_congr rfl ?_
    intro q hq
    simp [F, e, hnormB_even q.1, hnormC_even q.2]
  -- Combine the lower boundary, upper boundary, exceptional vanishing term, and interior reindex.
  calc
    iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3) 0 /
        (2 * n + 6).factorial =
      ∑ p ∈ Finset.antidiagonal (2 * n + 6),
        (iteratedDeriv p.1 B 0 / p.1.factorial) *
          (iteratedDeriv p.2 C 0 / p.2.factorial) := by
            simpa [B, C, pow_succ, pow_one, mul_assoc] using
              cartan_iteratedDeriv_mul_factorial_at_zero (f := B) (g := C) hB hC
    _ =
      Finset.sum ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 = 0)) F +
        Finset.sum ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)) F := by
          rw [hboundary_zero_split]
    _ =
      a_[L](n + 2) +
        Finset.sum ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)) F := by
          rw [hbottom]
    _ =
      a_[L](n + 2) +
        (Finset.sum
            (((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 = 0)) F +
          Finset.sum
            (((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 ≠ 0)) F) := by
          rw [hboundary_top_split]
    _ =
      a_[L](n + 2) +
        ((2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
          Finset.sum
            (((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 ≠ 0)) F) := by
          rw [htop]
    _ =
      a_[L](n + 2) +
        ((2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
          (Finset.sum
              ((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
                (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 = 2)) F +
            Finset.sum
              ((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
                (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)) F)) := by
          rw [hexception_split]
    _ =
      a_[L](n + 2) +
        ((2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
          (0 +
            Finset.sum
              ((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
                (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)) F)) := by
          rw [hexception]
    _ =
      a_[L](n + 2) +
        ((2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
          (Finset.sum
              (((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
                (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)).filter
                (fun p : ℕ × ℕ ↦ Even p.1)) F +
            Finset.sum
              (((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
                (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)).filter
                (fun p : ℕ × ℕ ↦ ¬ Even p.1)) F)) := by
          rw [zero_add, hinterior_split]
    _ =
      a_[L](n + 2) +
        ((2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
          Finset.sum
            (((((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 0)).filter
              (fun p : ℕ × ℕ ↦ p.1 ≠ 0)).filter (fun p : ℕ × ℕ ↦ p.2 ≠ 2)).filter
              (fun p : ℕ × ℕ ↦ Even p.1)) F) := by
          rw [hodd_support_zero, add_zero]
    _ =
      a_[L](n + 2) +
        ((2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
          ∑ p ∈ Finset.antidiagonal n,
            a_[L](p.1) *
              (2 * a_[L](p.2 + 1) + ∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2))) := by
          rw [hinterior]
    _ =
      a_[L](n + 2) +
        (2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
        ∑ p ∈ Finset.antidiagonal n,
          a_[L](p.1) *
            (2 * a_[L](p.2 + 1) + ∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2)) := by
          ring

/-- Helper for Exercise 9: the normalized coefficient of the cube of the regularized Weierstrass
germ is the top coefficient, three copies of the quadratic convolution, and the cubic
antidiagonal sum. -/
lemma cartan_regularized_cube_normalized_coeff (L : PeriodPair) (n : ℕ) :
    iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3) 0 /
        (2 * n + 6).factorial =
      3 * a_[L](n + 2) +
        3 * (∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
        ∑ q ∈ Finset.Nat.antidiagonalTuple 3 n, a_[L](q 0) * a_[L](q 1) * a_[L](q 2) :=
by
  -- Collapse the structural cube package into Cartan's quadratic and cubic convolutions.
  calc
    iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3) 0 /
        (2 * n + 6).factorial =
      a_[L](n + 2) +
        (2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
        ∑ p ∈ Finset.antidiagonal n,
          a_[L](p.1) *
            (2 * a_[L](p.2 + 1) + ∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2)) := by
          exact L.cartan_regularized_cube_support_decomposition n
    _ =
      a_[L](n + 2) +
        (2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
        (2 * (∑ p ∈ Finset.antidiagonal n, a_[L](p.1) * a_[L](p.2 + 1)) +
          ∑ p ∈ Finset.antidiagonal n,
            a_[L](p.1) * (∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2))) := by
          have hinterior_split :
              ∑ p ∈ Finset.antidiagonal n,
                  a_[L](p.1) *
                    (2 * a_[L](p.2 + 1) + ∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2)) =
                Finset.sum (Finset.antidiagonal n) (fun p ↦ a_[L](p.1) * (2 * a_[L](p.2 + 1))) +
                  Finset.sum (Finset.antidiagonal n)
                    (fun p ↦ a_[L](p.1) * (∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2))) := by
            calc
              ∑ p ∈ Finset.antidiagonal n,
                  a_[L](p.1) *
                    (2 * a_[L](p.2 + 1) + ∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2)) =
                Finset.sum (Finset.antidiagonal n) (fun p ↦
                  (a_[L](p.1) * (2 * a_[L](p.2 + 1))) +
                    (a_[L](p.1) * (∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2)))) := by
                      refine Finset.sum_congr rfl ?_
                      intro p hp
                      ring
              _ =
                Finset.sum (Finset.antidiagonal n) (fun p ↦ a_[L](p.1) * (2 * a_[L](p.2 + 1))) +
                  Finset.sum (Finset.antidiagonal n)
                    (fun p ↦ a_[L](p.1) * (∑ r ∈ Finset.antidiagonal p.2, a_[L](r.1) * a_[L](r.2))) := by
                      rw [Finset.sum_add_distrib]
          have hlinear :
              (∑ p ∈ Finset.antidiagonal n, a_[L](p.1) * (2 * a_[L](p.2 + 1))) =
                2 * (∑ p ∈ Finset.antidiagonal n, a_[L](p.1) * a_[L](p.2 + 1)) := by
            calc
              (∑ p ∈ Finset.antidiagonal n, a_[L](p.1) * (2 * a_[L](p.2 + 1))) =
                ∑ p ∈ Finset.antidiagonal n, 2 * (a_[L](p.1) * a_[L](p.2 + 1)) := by
                  refine Finset.sum_congr rfl ?_
                  intro p hp
                  ring
              _ = 2 * (∑ p ∈ Finset.antidiagonal n, a_[L](p.1) * a_[L](p.2 + 1)) := by
                  rw [← Finset.mul_sum]
          simpa [hinterior_split, hlinear]
    _ =
      a_[L](n + 2) +
        (2 * a_[L](n + 2) + ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
        (2 * (∑ q ∈ Finset.antidiagonal (n + 1), a_[L](q.1) * a_[L](q.2)) +
          ∑ q ∈ Finset.Nat.antidiagonalTuple 3 n, a_[L](q 0) * a_[L](q 1) * a_[L](q 2)) := by
          rw [L.cartan_shifted_antidiagonal_convolution, L.cartan_cube_nested_antidiagonal_reindex]
    _ =
      3 * a_[L](n + 2) +
        3 * (∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) +
        ∑ q ∈ Finset.Nat.antidiagonalTuple 3 n, a_[L](q 0) * a_[L](q 1) * a_[L](q 2) := by
          ring

/-- Helper for Exercise 9: the normalized coefficient of the square of the regularized derivative
germ is the boundary contribution plus the even-even antidiagonal convolution. -/
lemma cartan_regularized_deriv_square_normalized_coeff (L : PeriodPair) (n : ℕ) :
    iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2) 0 /
        (2 * n + 6).factorial =
      (-8 * (n + 2 : ℂ)) * a_[L](n + 2) +
        4 * ∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2) :=
by
  let A : ℂ → ℂ := fun z ↦ ℘'[L - (0 : ℂ)] z * z ^ (3 : ℕ) - (2 : ℂ)
  let F : ℕ × ℕ → ℂ := fun p ↦
    (iteratedDeriv p.1 A 0 / ((p.1.factorial : ℕ) : ℂ)) *
      (iteratedDeriv p.2 A 0 / ((p.2.factorial : ℕ) : ℂ))
  have hA : ContDiffAt ℂ (2 * n + 6) A 0 := by
    have hderiv : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 := by
      simpa using (L.analyticAt_derivWeierstrassPExcept (0 : ℂ)).contDiffAt
    have hzcube : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ z ^ (3 : ℕ)) 0 := by
      fun_prop
    have hprod : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ (3 : ℕ)) 0 := by
      exact hderiv.mul hzcube
    have hconst : ContDiffAt ℂ (2 * n + 6) (fun _ : ℂ ↦ (2 : ℂ)) 0 := by
      fun_prop
    -- The regularized derivative germ is holomorphic at the origin.
    simpa [A] using hprod.sub hconst
  have hnorm_zero : iteratedDeriv 0 A 0 / (((0 : ℕ).factorial : ℕ) : ℂ) = -2 := by
    -- The zero-th normalized derivative is the value `A(0) = -2`.
    simpa [A] using L.cartan_regularized_deriv_value
  have hnorm_even (k : ℕ) :
      iteratedDeriv (2 * k + 2) A 0 / (((2 * k + 2).factorial : ℕ) : ℂ) =
        (2 * k : ℂ) * a_[L](k) := by
    have hfac : ((((2 * k + 2).factorial : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * k + 2)
    -- Positive even derivatives of `A` are already packaged by the derivative lemma.
    refine (div_eq_iff hfac).2 ?_
    simpa [A, mul_comm, mul_left_comm, mul_assoc] using
      L.cartan_regularized_deriv_iteratedDeriv_even k
  have hnorm_odd (k : ℕ) :
      iteratedDeriv (2 * k + 1) A 0 / (((2 * k + 1).factorial : ℕ) : ℂ) = 0 := by
    have hfac : ((((2 * k + 1).factorial : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
    -- Odd derivatives vanish because `A` is even.
    refine (div_eq_iff hfac).2 ?_
    simpa [A] using L.cartan_regularized_deriv_iteratedDeriv_odd k
  have hboundary_split :
      Finset.sum (Finset.antidiagonal (2 * n + 6)) F =
        Finset.sum
            ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0)) F +
          Finset.sum
            ((Finset.antidiagonal (2 * n + 6)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))) F := by
    -- First separate the two boundary terms from the positive-support interior.
    simpa [Finset.sum_filter] using
      (Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal (2 * n + 6))
        (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0) F).symm
  have hboundary_set :
      (Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0) =
        {(0, 2 * n + 6), (2 * n + 6, 0)} := by
    -- On this antidiagonal, a vanishing coordinate forces one of the two endpoints.
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpAnti, hpZero⟩
      have hpSum : p.1 + p.2 = 2 * n + 6 := by
        simpa using Finset.mem_antidiagonal.mp hpAnti
      rcases hpZero with hp1 | hp2
      · simp [hp1]
        left
        apply Prod.ext <;> omega
      · simp [hp2]
        right
        apply Prod.ext <;> omega
    · intro hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · simp [Finset.mem_antidiagonal]
      · have hp' : p = (2 * n + 6, 0) := by simpa using hp
        rw [hp']
        simp [Finset.mem_antidiagonal]
  have htop :
      iteratedDeriv (2 * n + 6) A 0 / ((((2 * n + 6).factorial : ℕ) : ℂ)) =
        (2 * (n + 2) : ℂ) * a_[L](n + 2) := by
    -- The top positive even derivative is the `k = n + 2` case of the derivative package.
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnorm_even (n + 2)
  have hboundary :
      Finset.sum
          ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0)) F =
        (-8 * (n + 2 : ℂ)) * a_[L](n + 2) := by
    -- Evaluate the two boundary terms `(0, 2 * n + 6)` and `(2 * n + 6, 0)` explicitly.
    rw [hboundary_set]
    simp [F, hnorm_zero, htop]
    ring
  have hinterior_split :
      Finset.sum
          ((Finset.antidiagonal (2 * n + 6)).filter
            (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))) F =
        Finset.sum
            (((Finset.antidiagonal (2 * n + 6)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) F +
          Finset.sum
            (((Finset.antidiagonal (2 * n + 6)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ ¬ Even p.1) F := by
    -- Then split the interior by the parity of the first index.
    simpa [Finset.sum_filter] using
      (Finset.sum_filter_add_sum_filter_not
        ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0)))
        (fun p : ℕ × ℕ ↦ Even p.1) F).symm
  have hodd_support_zero :
      Finset.sum
          (((Finset.antidiagonal (2 * n + 6)).filter
            (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ ¬ Even p.1) F = 0 := by
    -- Odd first coordinates force the first normalized derivative factor to vanish.
    refine Finset.sum_eq_zero ?_
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpInterior, hpOdd⟩
    obtain hpEven | hpOdd' := p.1.even_or_odd
    · exact (hpOdd hpEven).elim
    · rcases hpOdd'.exists_bit1 with ⟨k, hk⟩
      simp [F, hk, hnorm_odd k]
  let e : ℕ × ℕ ↪ ℕ × ℕ :=
    ⟨fun q : ℕ × ℕ ↦ (2 * q.1 + 2, 2 * q.2 + 2), by
      intro q q' hqq'
      have h1 : 2 * q.1 + 2 = 2 * q'.1 + 2 := by
        simpa using congrArg Prod.fst hqq'
      have h2 : 2 * q.2 + 2 = 2 * q'.2 + 2 := by
        simpa using congrArg Prod.snd hqq'
      apply Prod.ext <;> omega⟩
  have hinterior_set :
      ((Finset.antidiagonal (2 * n + 6)).filter
        (fun p : ℕ × ℕ ↦ p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ Even p.1)) =
        (Finset.antidiagonal (n + 1)).map e := by
    -- Positive even-even support is exactly `(2 * i + 2, 2 * j + 2)` with `i + j = n + 1`.
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpAnti, hpData⟩
      rcases hpData with ⟨hp1, hp2, hpEven⟩
      have hpSum : p.1 + p.2 = 2 * n + 6 := by
        simpa using Finset.mem_antidiagonal.mp hpAnti
      rcases hpEven with ⟨k, hk⟩
      have hkPos : 1 ≤ k := by
        omega
      let q : ℕ × ℕ := (k - 1, n + 2 - k)
      have hqMem : q ∈ Finset.antidiagonal (n + 1) := by
        simp [q, Finset.mem_antidiagonal]
        omega
      refine Finset.mem_map.mpr ?_
      refine ⟨q, hqMem, ?_⟩
      ext <;> simp [e, q, hk]
      · omega
      · omega
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨q, hqMem, hpEq⟩
      have hqSum : q.1 + q.2 = n + 1 := by
        simpa using Finset.mem_antidiagonal.mp hqMem
      have hpEq' : p = (2 * q.1 + 2, 2 * q.2 + 2) := by
        simpa [e] using hpEq.symm
      rw [hpEq']
      refine Finset.mem_filter.mpr ?_
      constructor
      · simp [Finset.mem_antidiagonal]
        omega
      · constructor
        · omega
        · constructor
          · omega
          · exact ⟨q.1 + 1, by omega⟩
  have hinterior_rewrite :
      (((Finset.antidiagonal (2 * n + 6)).filter
        (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) =
        ((Finset.antidiagonal (2 * n + 6)).filter
          (fun p : ℕ × ℕ ↦ p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ Even p.1)) := by
    -- Rewrite the nested filter into the single positive even-support predicate above.
    ext p
    simp [and_assoc]
  have hinterior :
      Finset.sum
          (((Finset.antidiagonal (2 * n + 6)).filter
            (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) F =
        4 * ∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2) := by
    -- Reindex the surviving support and simplify each normalized derivative factor.
    rw [hinterior_rewrite, hinterior_set, Finset.sum_map]
    calc
      ∑ q ∈ Finset.antidiagonal (n + 1),
          (iteratedDeriv (2 * q.1 + 2) A 0 / ((2 * q.1 + 2).factorial : ℂ)) *
            (iteratedDeriv (2 * q.2 + 2) A 0 / ((2 * q.2 + 2).factorial : ℂ)) =
        ∑ q ∈ Finset.antidiagonal (n + 1),
          (((2 * q.1 : ℂ) * a_[L](q.1)) * (((2 * q.2 : ℂ) * a_[L](q.2)))) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            simp [F, e, hnorm_even q.1, hnorm_even q.2]
      _ =
        ∑ q ∈ Finset.antidiagonal (n + 1),
          4 * ((q.1 * q.2 : ℂ) * a_[L](q.1) * a_[L](q.2)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            ring
      _ =
        4 * ∑ q ∈ Finset.antidiagonal (n + 1), (q.1 * q.2 : ℂ) * a_[L](q.1) * a_[L](q.2) := by
            rw [← Finset.mul_sum]
  -- Combine the boundary package with the reindexed interior contribution.
  calc
    iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2) 0 /
        (2 * n + 6).factorial =
      ∑ p ∈ Finset.antidiagonal (2 * n + 6),
        (iteratedDeriv p.1 A 0 / p.1.factorial) *
          (iteratedDeriv p.2 A 0 / p.2.factorial) := by
            simpa [A, pow_two] using
              cartan_iteratedDeriv_mul_factorial_at_zero (f := A) (g := A) hA hA
    _ =
      Finset.sum
          ((Finset.antidiagonal (2 * n + 6)).filter (fun p : ℕ × ℕ ↦ p.1 = 0 ∨ p.2 = 0)) F +
        Finset.sum
          ((Finset.antidiagonal (2 * n + 6)).filter
            (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))) F := by
          rw [hboundary_split]
    _ =
      (-8 * (n + 2 : ℂ)) * a_[L](n + 2) +
        Finset.sum
          ((Finset.antidiagonal (2 * n + 6)).filter
            (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))) F := by
          rw [hboundary]
    _ =
      (-8 * (n + 2 : ℂ)) * a_[L](n + 2) +
        (Finset.sum
            (((Finset.antidiagonal (2 * n + 6)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) F +
          Finset.sum
            (((Finset.antidiagonal (2 * n + 6)).filter
              (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ ¬ Even p.1) F) := by
          rw [hinterior_split]
    _ =
      (-8 * (n + 2 : ℂ)) * a_[L](n + 2) +
        Finset.sum
          (((Finset.antidiagonal (2 * n + 6)).filter
            (fun p : ℕ × ℕ ↦ ¬ (p.1 = 0 ∨ p.2 = 0))).filter fun p : ℕ × ℕ ↦ Even p.1) F := by
          rw [hodd_support_zero, add_zero]
    _ =
      (-8 * (n + 2 : ℂ)) * a_[L](n + 2) +
        4 * ∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2) := by
          rw [hinterior]

/-- Helper for Exercise 9: in the normalized `2 * n + 6`-th derivative of `z^4` times the
regularized Weierstrass germ, only the `(4, 2 * n + 2)` Leibniz term survives. -/
lemma cartan_regularized_zpow_four_mul_weierstrass_normalized_coeff (L : PeriodPair) (n : ℕ) :
    iteratedDeriv (2 * n + 6)
        (fun z : ℂ ↦ z ^ (4 : ℕ) * (℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ))) 0 /
        (2 * n + 6).factorial =
      a_[L](n) :=
by
  let B : ℂ → ℂ := fun z ↦ ℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ)
  have hzpow : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ z ^ (4 : ℕ)) 0 := by
    fun_prop
  have hB : ContDiffAt ℂ (2 * n + 6) B 0 := by
    have hweier : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 := by
      simpa using (L.analyticAt_weierstrassPExcept (0 : ℂ)).contDiffAt
    have hzsq : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ z ^ (2 : ℕ)) 0 := by
      fun_prop
    have hprod : ContDiffAt ℂ (2 * n + 6) (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ (2 : ℕ)) 0 := by
      exact hweier.mul hzsq
    have hconst : ContDiffAt ℂ (2 * n + 6) (fun _ : ℂ ↦ (1 : ℂ)) 0 := by
      fun_prop
    -- The regularized germ is holomorphic, so Leibniz applies to `z^4 * B`.
    simpa [B] using hprod.add hconst
  -- Collapse the antidiagonal to the unique surviving pair `(4, 2 * n + 2)`.
  calc
    iteratedDeriv (2 * n + 6)
        (fun z : ℂ ↦ z ^ (4 : ℕ) * (℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ))) 0 /
        (2 * n + 6).factorial =
      ∑ p ∈ Finset.antidiagonal (2 * n + 6),
        (iteratedDeriv p.1 (fun z : ℂ ↦ z ^ (4 : ℕ)) 0 / p.1.factorial) *
          (iteratedDeriv p.2 B 0 / p.2.factorial) := by
            simpa [B] using
              cartan_iteratedDeriv_mul_factorial_at_zero (f := fun z : ℂ ↦ z ^ (4 : ℕ)) (g := B)
                hzpow hB
    _ = a_[L](n) := by
      rw [Finset.sum_eq_single (4, 2 * n + 2)]
      · have hpow :
            iteratedDeriv 4 (fun z : ℂ ↦ z ^ (4 : ℕ)) 0 / (4 : ℕ).factorial = 1 := by
          rw [iteratedDeriv_fun_pow_zero]
          norm_num
        calc
          (iteratedDeriv 4 (fun z : ℂ ↦ z ^ (4 : ℕ)) 0 / (4 : ℕ).factorial) *
              (iteratedDeriv (2 * n + 2) B 0 / (2 * n + 2).factorial) =
            1 * (iteratedDeriv (2 * n + 2) B 0 / (2 * n + 2).factorial) := by
              rw [hpow]
          _ = a_[L](n) := by
              simpa [B] using
                show iteratedDeriv (2 * n + 2) B 0 / ((((2 * n + 2).factorial : ℕ) : ℂ)) = a_[L](n) from by
                  have hfac : ((((2 * n + 2).factorial : ℕ) : ℂ)) ≠ 0 := by
                    exact_mod_cast Nat.factorial_ne_zero (2 * n + 2)
                  refine (div_eq_iff hfac).2 ?_
                  simpa [B, mul_comm, mul_left_comm, mul_assoc] using
                    L.cartan_regularized_weierstrass_iteratedDeriv_even n
      · intro p hp hne
        have hpSum : p.1 + p.2 = 2 * n + 6 := by
          simpa using Finset.mem_antidiagonal.mp hp
        have hp1_ne : p.1 ≠ 4 := by
          intro hp1
          apply hne
          apply Prod.ext
          · simpa [hp1]
          · omega
        have hpow :
            iteratedDeriv p.1 (fun z : ℂ ↦ z ^ (4 : ℕ)) 0 / p.1.factorial = 0 := by
          rw [iteratedDeriv_fun_pow_zero]
          simp [hp1_ne]
        rw [hpow, zero_mul]
      · intro hmem
        exfalso
        apply hmem
        exact Finset.mem_antidiagonal.mpr (by omega)

/-- Helper for Exercise 9: differentiating the regularized cubic relation at order `2 * n + 6`
still gives zero at the origin. -/
lemma cartan_regularized_relation_iteratedDeriv_zero (L : PeriodPair) (n : ℕ) :
    iteratedDeriv (2 * n + 6)
        (fun z : ℂ ↦
          (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2 -
            4 * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3 +
            20 * L.cartan_a₂ * z ^ 4 * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) +
            28 * L.cartan_a₄ * z ^ 6) 0 = 0 := by
  let R : ℂ → ℂ := fun z ↦
    (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2 -
      4 * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3 +
      20 * L.cartan_a₂ * z ^ 4 * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) +
      28 * L.cartan_a₄ * z ^ 6
  -- Differentiate the neighborhood identity directly instead of reopening the pole cancellation.
  simpa [R] using
    (Filter.EventuallyEq.iteratedDeriv_eq (n := 2 * n + 6)
      L.cartan_regularized_weierstrass_relation_eventually_zero)

/-- Helper for Exercise 9: the normalized `2 * n + 6` coefficient of the residual `z^6` term
vanishes once `n ≥ 1`. -/
lemma cartan_regularized_zpow_six_normalized_coeff_vanish (L : PeriodPair) {n : ℕ}
    (hn : 1 ≤ n) :
    iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ 28 * L.cartan_a₄ * z ^ (6 : ℕ)) 0 /
        (2 * n + 6).factorial = 0 := by
  have hneq6 : 2 * n + 6 ≠ 6 := by
    omega
  have hraw :
      iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ z ^ (6 : ℕ)) 0 = 0 := by
    rw [iteratedDeriv_fun_pow_zero, if_neg hneq6]
    norm_num
  -- The only nonzero derivative of `z^6` occurs in order `6`, which is excluded by `hn`.
  calc
    iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ 28 * L.cartan_a₄ * z ^ (6 : ℕ)) 0 /
        (2 * n + 6).factorial =
      ((28 * L.cartan_a₄) * iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ z ^ (6 : ℕ)) 0) /
          (2 * n + 6).factorial := by
            rw [iteratedDeriv_const_mul_field (n := 2 * n + 6) (x := (0 : ℂ))
              (c := 28 * L.cartan_a₄) (f := fun z : ℂ ↦ z ^ (6 : ℕ))]
    _ = 0 := by
      rw [hraw]
      simp

/-- Helper for Exercise 9: differentiating the regularized cubic relation and expanding by
linearity isolates the four termwise derivatives at order `2 * n + 6`. -/
lemma cartan_regularized_relation_iteratedDeriv_additive_expansion (L : PeriodPair) (n : ℕ) :
    iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2) 0 -
        4 * iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3) 0 +
        20 * L.cartan_a₂ *
          iteratedDeriv (2 * n + 6)
            (fun z : ℂ ↦ z ^ (4 : ℕ) * (℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ))) 0 +
        iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ 28 * L.cartan_a₄ * z ^ (6 : ℕ)) 0 = 0 := by
  let m : ℕ := 2 * n + 6
  let A₀ : ℂ → ℂ := fun z ↦ ℘'[L - (0 : ℂ)] z * z ^ (3 : ℕ) - (2 : ℂ)
  let B₀ : ℂ → ℂ := fun z ↦ ℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ)
  let A : ℂ → ℂ := fun z ↦ A₀ z ^ (2 : ℕ)
  let B : ℂ → ℂ := fun z ↦ B₀ z ^ (3 : ℕ)
  let C : ℂ → ℂ := fun z ↦ z ^ (4 : ℕ) * B₀ z
  let D : ℂ → ℂ := fun z ↦ 28 * L.cartan_a₄ * z ^ (6 : ℕ)
  have hA₀ : ContDiffAt ℂ m A₀ 0 := by
    have hderiv : ContDiffAt ℂ m (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z) 0 := by
      simpa using (L.analyticAt_derivWeierstrassPExcept (0 : ℂ)).contDiffAt
    have hzcube : ContDiffAt ℂ m (fun z : ℂ ↦ z ^ (3 : ℕ)) 0 := by
      fun_prop
    have hprod : ContDiffAt ℂ m (fun z : ℂ ↦ ℘'[L - (0 : ℂ)] z * z ^ (3 : ℕ)) 0 := by
      exact hderiv.mul hzcube
    have hconst : ContDiffAt ℂ m (fun _ : ℂ ↦ (2 : ℂ)) 0 := by
      fun_prop
    -- The regularized derivative germ is holomorphic at the origin.
    simpa [A₀] using hprod.sub hconst
  have hB₀ : ContDiffAt ℂ m B₀ 0 := by
    have hweier : ContDiffAt ℂ m (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z) 0 := by
      simpa using (L.analyticAt_weierstrassPExcept (0 : ℂ)).contDiffAt
    have hzsq : ContDiffAt ℂ m (fun z : ℂ ↦ z ^ (2 : ℕ)) 0 := by
      fun_prop
    have hprod : ContDiffAt ℂ m (fun z : ℂ ↦ ℘[L - (0 : ℂ)] z * z ^ (2 : ℕ)) 0 := by
      exact hweier.mul hzsq
    have hconst : ContDiffAt ℂ m (fun _ : ℂ ↦ (1 : ℂ)) 0 := by
      fun_prop
    -- The regularized Weierstrass germ is holomorphic at the origin.
    simpa [B₀] using hprod.add hconst
  have hA : ContDiffAt ℂ m A 0 := by
    -- The square term inherits differentiability from the regularized derivative germ.
    simpa [A] using hA₀.pow 2
  have hB : ContDiffAt ℂ m B 0 := by
    -- The cube term inherits differentiability from the regularized Weierstrass germ.
    simpa [B] using hB₀.pow 3
  have hC : ContDiffAt ℂ m C 0 := by
    have hzfour : ContDiffAt ℂ m (fun z : ℂ ↦ z ^ (4 : ℕ)) 0 := by
      fun_prop
    -- The mixed `z^4 * B₀` term is still holomorphic at the origin.
    simpa [C] using hzfour.mul hB₀
  have hD : ContDiffAt ℂ m D 0 := by
    -- The residual term is a polynomial.
    simpa [D] using (show ContDiffAt ℂ m (fun z : ℂ ↦ 28 * L.cartan_a₄ * z ^ (6 : ℕ)) 0 by
      fun_prop)
  have hFourB : ContDiffAt ℂ m (fun z : ℂ ↦ (4 : ℂ) * B z) 0 := by
    -- Scalar multiplication preserves differentiability.
    have hconst : ContDiffAt ℂ m (fun _ : ℂ ↦ (4 : ℂ)) 0 := by
      fun_prop
    simpa using hconst.mul hB
  have hTwentyC : ContDiffAt ℂ m (fun z : ℂ ↦ (20 * L.cartan_a₂ : ℂ) * C z) 0 := by
    -- Scalar multiplication preserves differentiability here as well.
    have hconst : ContDiffAt ℂ m (fun _ : ℂ ↦ (20 * L.cartan_a₂ : ℂ)) 0 := by
      fun_prop
    simpa using hconst.mul hC
  have hRight : ContDiffAt ℂ m (fun z : ℂ ↦ 20 * L.cartan_a₂ * C z + D z) 0 := by
    -- Group the last two summands before expanding by linearity.
    simpa using hTwentyC.add hD
  have hexpand :
      iteratedDeriv m (fun z : ℂ ↦ A z - 4 * B z + 20 * L.cartan_a₂ * C z + D z) 0 =
        iteratedDeriv m A 0 - 4 * iteratedDeriv m B 0 +
          20 * L.cartan_a₂ * iteratedDeriv m C 0 + iteratedDeriv m D 0 := by
    -- Route correction: split the differentiated relation into additive and scalar pieces before
    -- normalizing by factorials, so Lean never has to elaborate the full monolithic term at once.
    calc
      iteratedDeriv m (fun z : ℂ ↦ A z - 4 * B z + 20 * L.cartan_a₂ * C z + D z) 0 =
          iteratedDeriv m (fun z : ℂ ↦ A z - 4 * B z) 0 +
            iteratedDeriv m (fun z : ℂ ↦ 20 * L.cartan_a₂ * C z + D z) 0 := by
              simpa [add_assoc] using
                (iteratedDeriv_add (f := fun z : ℂ ↦ A z - 4 * B z)
                  (g := fun z : ℂ ↦ 20 * L.cartan_a₂ * C z + D z) (hA.sub hFourB) hRight)
      _ =
          iteratedDeriv m (fun z : ℂ ↦ A z - 4 * B z) 0 +
              (iteratedDeriv m (fun z : ℂ ↦ 20 * L.cartan_a₂ * C z) 0 + iteratedDeriv m D 0) := by
              simpa [add_assoc] using
                congrArg (fun z : ℂ ↦ iteratedDeriv m (fun z : ℂ ↦ A z - 4 * B z) 0 + z)
                  (iteratedDeriv_add (f := fun z : ℂ ↦ 20 * L.cartan_a₂ * C z)
                    (g := D) hTwentyC hD)
      _ =
          (iteratedDeriv m A 0 - iteratedDeriv m (fun z : ℂ ↦ 4 * B z) 0) +
              iteratedDeriv m (fun z : ℂ ↦ 20 * L.cartan_a₂ * C z) 0 +
            iteratedDeriv m D 0 := by
              simpa [add_assoc] using
                congrArg
                  (fun z : ℂ ↦ z + iteratedDeriv m (fun z : ℂ ↦ 20 * L.cartan_a₂ * C z) 0 +
                    iteratedDeriv m D 0)
                  (iteratedDeriv_sub (f := A) (g := fun z : ℂ ↦ 4 * B z) hA hFourB)
      _ =
          (iteratedDeriv m A 0 - 4 * iteratedDeriv m B 0) +
              20 * L.cartan_a₂ * iteratedDeriv m C 0 +
            iteratedDeriv m D 0 := by
              rw [iteratedDeriv_const_mul_field (n := m) (x := (0 : ℂ)) (c := (4 : ℂ))
                    (f := B)]
              rw [iteratedDeriv_const_mul_field (n := m) (x := (0 : ℂ))
                    (c := (20 * L.cartan_a₂ : ℂ)) (f := C)]
      _ =
          iteratedDeriv m A 0 - 4 * iteratedDeriv m B 0 +
            20 * L.cartan_a₂ * iteratedDeriv m C 0 + iteratedDeriv m D 0 := by
              ring
  -- Rewrite the differentiated regularized relation through the local abbreviations.
  calc
    iteratedDeriv m A 0 - 4 * iteratedDeriv m B 0 +
        20 * L.cartan_a₂ * iteratedDeriv m C 0 + iteratedDeriv m D 0 =
      iteratedDeriv m (fun z : ℂ ↦ A z - 4 * B z + 20 * L.cartan_a₂ * C z + D z) 0 := by
        symm
        exact hexpand
    _ = 0 := by
      simpa [m, A, B, C, D, A₀, B₀, mul_assoc] using
        L.cartan_regularized_relation_iteratedDeriv_zero n

/-- Helper for Exercise 9: dividing the expanded differentiated relation by `(2 * n + 6)!`
and substituting the prepackaged normalized coefficient identities leaves only the residual
`z^6` contribution. -/
lemma cartan_regularized_relation_normalized_coeff_core (L : PeriodPair) (n : ℕ) :
    ((-8 * (n + 2 : ℂ)) * a_[L](n + 2) +
        4 * ∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2)) -
      4 * (3 * a_[L](n + 2) +
        3 * ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2) +
        ∑ q ∈ Finset.Nat.antidiagonalTuple 3 n, a_[L](q 0) * a_[L](q 1) * a_[L](q 2)) +
      20 * L.cartan_a₂ * a_[L](n) +
      iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ 28 * L.cartan_a₄ * z ^ (6 : ℕ)) 0 /
        (2 * n + 6).factorial = 0 := by
  let m : ℕ := 2 * n + 6
  let a2 : ℂ := L.cartan_a₂
  let X : ℂ := iteratedDeriv m (fun z : ℂ ↦ (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) ^ 2) 0
  let Y : ℂ := iteratedDeriv m (fun z : ℂ ↦ (℘[L - (0 : ℂ)] z * z ^ 2 + 1) ^ 3) 0
  let Z : ℂ := iteratedDeriv m
    (fun z : ℂ ↦ z ^ (4 : ℕ) * (℘[L - (0 : ℂ)] z * z ^ (2 : ℕ) + (1 : ℂ))) 0
  let W : ℂ := iteratedDeriv m (fun z : ℂ ↦ 28 * L.cartan_a₄ * z ^ (6 : ℕ)) 0
  have hraw : X - 4 * Y + 20 * a2 * Z + W = 0 := by
    -- First express the additive expansion using atomized scalar names.
    simpa [m, a2, X, Y, Z, W] using L.cartan_regularized_relation_iteratedDeriv_additive_expansion n
  have hnorm :
      X / m.factorial - 4 * (Y / m.factorial) + 20 * a2 * (Z / m.factorial) +
        W / m.factorial = 0 := by
    -- Now divide the scalar relation by the common factorial denominator.
    have := congrArg (fun z : ℂ ↦ z / (((m.factorial : ℕ) : ℂ))) hraw
    ring_nf at this
    simpa [div_eq_mul_inv, m, mul_assoc, mul_left_comm, mul_comm] using this
  -- Rewrite the three main normalized terms using the already proved coefficient packages.
  calc
    ((-8 * (n + 2 : ℂ)) * a_[L](n + 2) +
        4 * ∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2)) -
      4 * (3 * a_[L](n + 2) +
        3 * ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2) +
        ∑ q ∈ Finset.Nat.antidiagonalTuple 3 n, a_[L](q 0) * a_[L](q 1) * a_[L](q 2)) +
      20 * L.cartan_a₂ * a_[L](n) +
      iteratedDeriv (2 * n + 6) (fun z : ℂ ↦ 28 * L.cartan_a₄ * z ^ (6 : ℕ)) 0 /
        (2 * n + 6).factorial =
      X / m.factorial - 4 * (Y / m.factorial) + 20 * a2 * (Z / m.factorial) +
        W / m.factorial := by
          rw [L.cartan_regularized_deriv_square_normalized_coeff n,
            L.cartan_regularized_cube_normalized_coeff n,
            L.cartan_regularized_zpow_four_mul_weierstrass_normalized_coeff n]
    _ = 0 := by
      exact hnorm

/-- Helper for Exercise 9: the raw quadratic and constant antidiagonal sums recombine into the
single weighted antidiagonal sum appearing in the recurrence. -/
lemma cartan_weighted_antidiagonal_sum_rewrite (L : PeriodPair) (n : ℕ) :
    4 * ∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2) -
      12 * ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2) =
        4 * ∑ p ∈ Finset.antidiagonal (n + 1),
          (((p.1 * p.2 : ℂ) - 3) * a_[L](p.1) * a_[L](p.2)) := by
  -- Factor out the common `4`, then combine the two antidiagonal sums termwise.
  calc
    4 * ∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2) -
        12 * ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2) =
      4 *
        ((∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2)) -
          3 * ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)) := by
            ring
    _ =
      4 * ∑ p ∈ Finset.antidiagonal (n + 1),
        (((p.1 * p.2 : ℂ) - 3) * a_[L](p.1) * a_[L](p.2)) := by
          congr 1
          calc
            (∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2)) -
                3 * ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2) =
              (∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2)) -
                  ∑ p ∈ Finset.antidiagonal (n + 1), 3 * (a_[L](p.1) * a_[L](p.2)) := by
                    rw [← Finset.mul_sum]
            _ =
              ∑ p ∈ Finset.antidiagonal (n + 1),
                ((p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2) - 3 * (a_[L](p.1) * a_[L](p.2))) := by
                  rw [Finset.sum_sub_distrib]
            _ =
              ∑ p ∈ Finset.antidiagonal (n + 1),
                (((p.1 * p.2 : ℂ) - 3) * a_[L](p.1) * a_[L](p.2)) := by
                  refine Finset.sum_congr rfl ?_
                  intro p hp
                  ring

/-- Helper for Exercise 9: after normalizing the differentiated regularized relation, the three
prepackaged coefficient identities combine into the single scalar relation used in the recurrence. -/
lemma cartan_regularized_relation_normalized_coeff (L : PeriodPair) {n : ℕ} (hn : 1 ≤ n) :
    ((-8 * (n + 2 : ℂ)) * a_[L](n + 2) +
        4 * ∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2)) -
      4 * (3 * a_[L](n + 2) +
        3 * ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2) +
        ∑ q ∈ Finset.Nat.antidiagonalTuple 3 n, a_[L](q 0) * a_[L](q 1) * a_[L](q 2)) +
      20 * L.cartan_a₂ * a_[L](n) = 0 := by
  have hcore := L.cartan_regularized_relation_normalized_coeff_core n
  -- The only residual normalized term is the `z^6` contribution, which vanishes for `n ≥ 1`.
  rw [L.cartan_regularized_zpow_six_normalized_coeff_vanish hn] at hcore
  simpa using hcore

/-- Exercise 9 (1): the differential equation
`℘'(z)^2 = 4 ℘(z)^3 - 20 a₂ ℘(z) - 28 a₄` yields an induction recurrence for the even
Laurent coefficients of `℘` at the origin. -/
theorem cartan_weierstrass_even_laurent_coeff_recurrence
    (L : PeriodPair) {n : ℕ} (hn : 1 ≤ n) :
    (2 * n + 7 : ℂ) * a_[L](n + 2) =
      (Finset.sum (Finset.antidiagonal (n + 1)) fun p ↦
          ((p.1 * p.2 : ℂ) - 3) * a_[L](p.1) * a_[L](p.2)) -
      (Finset.sum (Finset.Nat.antidiagonalTuple 3 n) fun q ↦
          a_[L](q 0) * a_[L](q 1) * a_[L](q 2)) +
      5 * L.cartan_a₂ * a_[L](n) :=
by
  let a2 : ℂ := L.cartan_a₂
  let A : ℂ := a_[L](n + 2)
  let Q : ℂ :=
    ∑ p ∈ Finset.antidiagonal (n + 1), (p.1 * p.2 : ℂ) * a_[L](p.1) * a_[L](p.2)
  let S : ℂ :=
    ∑ p ∈ Finset.antidiagonal (n + 1), a_[L](p.1) * a_[L](p.2)
  let T : ℂ :=
    ∑ q ∈ Finset.Nat.antidiagonalTuple 3 n, a_[L](q 0) * a_[L](q 1) * a_[L](q 2)
  let W : ℂ :=
    ∑ p ∈ Finset.antidiagonal (n + 1), (((p.1 * p.2 : ℂ) - 3) * a_[L](p.1) * a_[L](p.2))
  have hrewrite : Q * 4 - S * 12 = 4 * W := by
    -- Package the quadratic and constant antidiagonal sums into Cartan's weighted form.
    have hsum : 4 * Q - 12 * S = 4 * W := by
      simpa [Q, S, W] using L.cartan_weighted_antidiagonal_sum_rewrite n
    ring_nf at hsum
    simpa [mul_comm] using hsum
  have hnorm :
      ((-8 * (n + 2 : ℂ)) * A + 4 * Q) - 4 * (3 * A + 3 * S + T) + 20 * a2 * a_[L](n) = 0 := by
    simpa [A, Q, S, T, a2] using L.cartan_regularized_relation_normalized_coeff hn
  -- Rewrite the normalized coefficient identity into the weighted antidiagonal form.
  ring_nf at hnorm
  have hnorm' : -(↑n * A * 8) - A * 28 + 4 * W - T * 4 + a2 * a_[L](n) * 20 = 0 := by
    calc
      -(↑n * A * 8) - A * 28 + 4 * W - T * 4 + a2 * a_[L](n) * 20 =
        -(↑n * A * 8) - A * 28 + (Q * 4 - S * 12) - T * 4 + a2 * a_[L](n) * 20 := by
          rw [hrewrite]
      _ = -(↑n * A * 8) - A * 28 + Q * 4 - S * 12 - T * 4 + a2 * a_[L](n) * 20 := by
          ring
      _ = 0 := by
          exact hnorm
  have hdiv := congrArg (fun z : ℂ ↦ z / 4) hnorm'
  -- Divide by `4` and normalize the scalar algebra to isolate `a_[L](n + 2)`.
  ring_nf at hdiv
  let R : ℂ := W - T + 5 * a2 * a_[L](n)
  have hfinal : -((2 * n + 7 : ℂ) * A) + R = 0 := by
    calc
      -((2 * n + 7 : ℂ) * A) + R = -(↑n * (2 * A)) + (-(7 * A) + R) := by
        ring
      _ = 0 := by
        simpa [R, A, W, T, a2, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hsub : R - (2 * n + 7 : ℂ) * A = 0 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfinal
  have hgoal : R = (2 * n + 7 : ℂ) * A := by
    exact sub_eq_zero.mp hsub
  simpa [R, A, W, T, a2, mul_comm, mul_left_comm, mul_assoc] using hgoal.symm

/-- Exercise 9 (2): the Laurent coefficient `a₆` is `a₂² / 3`. -/
theorem cartan_weierstrass_a6 (L : PeriodPair) :
    a_[L](3) = L.cartan_a₂ ^ 2 / 3 := by
  -- Specialize the general recurrence to `n = 1`, where only the `(1, 1)` square term survives.
  have hrec := L.cartan_weierstrass_even_laurent_coeff_recurrence (n := 1) (by norm_num)
  have hanti :
      Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    native_decide
  have htuple :
      Finset.Nat.antidiagonalTuple 3 1 = {![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} := by
    native_decide
  rw [hanti, htuple] at hrec
  simp [L.cartan_weierstrass_even_laurent_coeff_zero, L.cartan_weierstrass_even_laurent_coeff_one,
    L.cartan_weierstrass_even_laurent_coeff_two] at hrec
  have hrec' := hrec
  ring_nf at hrec'
  apply (eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).2
  have hdiv := congrArg (fun z : ℂ => z / 3) hrec'
  ring_nf at hdiv
  convert hdiv using 1 <;> ring_nf

/-- Exercise 9 (3): the Laurent coefficient `a₈` is `3 a₂ a₄ / 11`. -/
theorem cartan_weierstrass_a8 (L : PeriodPair) :
    a_[L](4) = 3 * L.cartan_a₂ * L.cartan_a₄ / 11 := by
  -- Specialize the general recurrence to `n = 2`, where the cubic sum still vanishes because
  -- every triple has a zero entry.
  have hrec := L.cartan_weierstrass_even_laurent_coeff_recurrence (n := 2) (by norm_num)
  have hanti :
      Finset.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by
    native_decide
  have htuple :
      Finset.Nat.antidiagonalTuple 3 2 =
        {![2, 0, 0], ![1, 1, 0], ![1, 0, 1], ![0, 2, 0], ![0, 1, 1], ![0, 0, 2]} := by
    native_decide
  rw [hanti, htuple] at hrec
  simp [L.cartan_weierstrass_even_laurent_coeff_zero, L.cartan_weierstrass_even_laurent_coeff_one,
    L.cartan_weierstrass_even_laurent_coeff_two, L.cartan_weierstrass_a6] at hrec
  have hrec' := hrec
  ring_nf at hrec'
  apply (eq_div_iff (by norm_num : (11 : ℂ) ≠ 0)).2
  have hdiv := congrArg (fun z : ℂ => z / 11) hrec'
  ring_nf at hdiv
  have hmul := congrArg (fun z : ℂ => z * 11) hdiv
  ring_nf at hmul
  convert hmul using 1 <;> ring_nf

end PeriodPair
