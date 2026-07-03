import Mathlib
import DifferentialForms_Cartan_1970.I.section04.«0012_Definition_I_4_extra_4»
import DifferentialForms_Cartan_1970.III.section11.«0008_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section11.«0012_Corollary_III_5_extra_8»
import DifferentialForms_Cartan_1970.V.section20.«0002_Definition_V_3_extra_2»
import DifferentialForms_Cartan_1970.V.section20.«0003_Theorem_1»
import DifferentialForms_Cartan_1970.V.section21.«0012_Exercise_3»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped JacobiTheta
open MeromorphicOn

/-- Helper for Exercise II: `θ₀` inherits the period `1` from `jacobiTheta₂` after the
half-translation in its definition. -/
theorem jacobi_theta_zero_add_one (τ u : ℂ) :
    (θ₀[τ]) (u + 1) = (θ₀[τ]) u := by
  -- The half-translation defining `θ₀` preserves the `+1` periodicity of `jacobiTheta₂`.
  simpa [jacobi_theta_zero_apply, add_assoc, add_left_comm, add_comm] using
    jacobiTheta₂_add_left (u + (1 / 2 : ℂ)) τ

/-- Helper for Exercise II: the scalar from `jacobiTheta₂_add_left'` is exactly the textbook
quasi-periodicity factor for `θ₀`. -/
theorem jacobi_theta_zero_add_tau_scalar (τ u : ℂ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ)))) =
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) := by
  -- Split the exponent into its `τ`, `u`, and half-period contributions, then simplify each
  -- contribution separately.
  calc
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ))))
        =
          Complex.exp (-(Real.pi : ℂ) * Complex.I * τ) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
            Complex.exp (-(Real.pi : ℂ) * Complex.I) := by
              rw [show (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ)))) =
                  (-(Real.pi : ℂ) * Complex.I * τ) +
                    (-(2 * Real.pi : ℂ) * Complex.I * u) +
                    (-(Real.pi : ℂ) * Complex.I) by ring]
              rw [Complex.exp_add, Complex.exp_add]
    _ = (jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) * (-1) := by
          rw [show (-(Real.pi : ℂ) * Complex.I * τ) = -((Real.pi : ℂ) * Complex.I * τ) by ring]
          rw [Complex.exp_neg, jacobi_q_eq_exp]
          rw [show (-(Real.pi : ℂ) * Complex.I) = -((Real.pi : ℂ) * Complex.I) by ring]
          rw [Complex.exp_neg]
          simp [Complex.exp_pi_mul_I]
    _ = -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) := by
          ring

/-- Helper for Exercise II: translating `θ₀` by `τ` multiplies it by Cartan's standard
quasi-periodicity factor. -/
theorem jacobi_theta_zero_add_tau (τ u : ℂ) :
    (θ₀[τ]) (u + τ) =
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) * (θ₀[τ]) u := by
  -- Rewrite `θ₀` through `jacobiTheta₂`, apply the `+τ` law there, and then normalize the scalar.
  rw [jacobi_theta_zero_apply, jacobi_theta_zero_apply]
  calc
    jacobiTheta₂ (u + τ + (1 / 2 : ℂ)) τ
        =
          Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ)))) *
            jacobiTheta₂ (u + (1 / 2 : ℂ)) τ := by
              convert jacobiTheta₂_add_left' (u + (1 / 2 : ℂ)) τ using 1 <;> ring
    _ =
        (-(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
          jacobiTheta₂ (u + (1 / 2 : ℂ)) τ := by
            rw [jacobi_theta_zero_add_tau_scalar]
    _ = -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          jacobiTheta₂ (u + (1 / 2 : ℂ)) τ := by
            ring

/-- The infinite product appearing in the exercise. -/
def jacobi_theta_zero_product (τ : ℂ) : ℂ → ℂ :=
  fun u ↦
    ∏' n : ℕ+,
      (1 - (jacobi_q τ) ^ (2 * (n : ℕ) - 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
        (1 -
          (jacobi_q τ) ^ (2 * (n : ℕ) - 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u))

/-- Evaluation formula for `jacobi_theta_zero_product`. -/
theorem jacobi_theta_zero_product_apply (τ u : ℂ) :
    jacobi_theta_zero_product τ u =
      ∏' n : ℕ+,
        (1 -
            (jacobi_q τ) ^ (2 * (n : ℕ) - 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
          (1 -
            (jacobi_q τ) ^ (2 * (n : ℕ) - 1) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) := rfl

/-- Helper for Exercise II: translating the product by the integer period `1` leaves each
exponential factor unchanged, so the whole infinite product is `1`-periodic. -/
theorem jacobi_theta_zero_product_add_one (τ u : ℂ) :
    jacobi_theta_zero_product τ (u + 1) = jacobi_theta_zero_product τ u := by
  -- Each factor picks up the multiplier `exp (2π I) = 1`, so the defining `tprod` is unchanged.
  have hpos :
      Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (u + 1)) =
        Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) := by
    calc
      Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (u + 1))
          = Complex.exp (((2 * Real.pi : ℂ) * Complex.I * u) + ((2 * Real.pi : ℂ) * Complex.I)) := by
              ring_nf
      _ = Complex.exp (((2 * Real.pi : ℂ) * Complex.I * u)) *
            Complex.exp ((2 * Real.pi : ℂ) * Complex.I) := by
              rw [Complex.exp_add]
      _ = Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) := by
            simp [Complex.exp_two_pi_mul_I]
  have hneg :
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (u + 1)) =
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) := by
    have htwopi : Complex.exp (-(2 * Real.pi : ℂ) * Complex.I) = 1 := by
      rw [show (-(2 * Real.pi : ℂ) * Complex.I) = -((2 * Real.pi : ℂ) * Complex.I) by ring]
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    calc
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (u + 1))
          = Complex.exp ((-(2 * Real.pi : ℂ) * Complex.I * u) + (-(2 * Real.pi : ℂ) * Complex.I)) := by
              ring_nf
      _ = Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I) := by
              rw [Complex.exp_add]
      _ = Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) := by
            rw [htwopi, mul_one]
  refine tprod_congr fun n ↦ ?_
  rw [hpos, hneg]

/-- Helper for Exercise II: the `n`th factor of the theta-zero product, indexed by `ℕ` so that the
Chapter V normal-product API applies directly. -/
def theta_zero_product_factor (τ : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun u ↦
    (1 - (jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
      (1 -
        (jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u))

/-- Helper for Exercise II: the product factors are a `1 + uₙ` perturbation family. -/
def theta_zero_product_perturbation (τ : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun u ↦ theta_zero_product_factor τ n u - 1

/-- Evaluation formula for `theta_zero_product_factor`. -/
theorem theta_zero_product_factor_apply (τ : ℂ) (n : ℕ) (u : ℂ) :
    theta_zero_product_factor τ n u =
      (1 - (jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
        (1 -
          (jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) := rfl

/-- Evaluation formula for `theta_zero_product_perturbation`. -/
theorem theta_zero_product_perturbation_apply (τ : ℂ) (n : ℕ) (u : ℂ) :
    theta_zero_product_perturbation τ n u = theta_zero_product_factor τ n u - 1 := rfl

/-- Helper for Exercise II: rewriting the `ℕ+`-indexed source product as an `ℕ`-indexed product
produces the same function. -/
theorem jacobi_theta_zero_product_eq_tprod_nat (τ u : ℂ) :
    jacobi_theta_zero_product τ u = ∏' n : ℕ, theta_zero_product_factor τ n u := by
  -- Reindex the positive naturals by `n ↦ n + 1` so the odd exponents become `2 n + 1`.
  have ht :
      ∏' n : ℕ+,
        (1 - (jacobi_q τ) ^ (2 * (n : ℕ) - 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
          (1 -
            (jacobi_q τ) ^ (2 * (n : ℕ) - 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) =
        ∏' n : ℕ,
          (1 - (jacobi_q τ) ^ (2 * (n + 1) - 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
            (1 -
              (jacobi_q τ) ^ (2 * (n + 1) - 1) *
                Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) := by
    simpa using
      (tprod_pnat_eq_tprod_succ (f := fun m : ℕ ↦
        (1 - (jacobi_q τ) ^ (2 * m - 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
          (1 -
            (jacobi_q τ) ^ (2 * m - 1) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u))))
  rw [jacobi_theta_zero_product_apply, ht]
  refine tprod_congr fun n ↦ ?_
  have hpow : 2 * (n + 1) - 1 = 2 * n + 1 := by
    omega
  simp [theta_zero_product_factor, hpow]

/-- Helper for Exercise II: each single product factor is entire. -/
theorem theta_zero_product_factor_differentiable (τ : ℂ) (n : ℕ) :
    Differentiable ℂ (theta_zero_product_factor τ n) := by
  intro u
  -- Each factor is `1` minus a scalar multiple of an exponential, so the product is entire.
  change DifferentiableAt ℂ
    (fun z ↦
      (1 - (jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * z)) *
        (1 -
          (jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z))) u
  fun_prop

/-- Helper for Exercise II: each product factor is holomorphic on the whole plane. -/
theorem theta_zero_product_factor_differentiableOn (τ : ℂ) (n : ℕ) :
    DifferentiableOn ℂ (theta_zero_product_factor τ n) Set.univ := by
  intro u _hu
  exact (theta_zero_product_factor_differentiable τ n u).differentiableWithinAt

/-- Helper for Exercise II: when `Im τ > 0`, the Jacobi parameter `q` has norm strictly less than
`1`. -/
theorem jacobi_q_norm_lt_one (τ : ℂ) (hτ : 0 < τ.im) :
    ‖jacobi_q τ‖ < 1 := by
  -- The real part of `π I τ` is `-π Im τ`, so the exponential norm decays exponentially.
  rw [jacobi_q_eq_exp, Complex.norm_exp]
  have hre : (Real.pi * Complex.I * τ).re = -Real.pi * τ.im := by
    rw [show (Real.pi * Complex.I * τ : ℂ) = (Real.pi : ℝ) * (τ * Complex.I) by ring]
    rw [Complex.re_ofReal_mul, Complex.mul_I_re]
    ring
  rw [hre]
  exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hτ])

/-- Helper for Exercise II: the odd powers of `q` are exactly the exponential factors attached to
the half-shifted lattice points. -/
theorem jacobi_q_pow_two_mul_add_one_eq_exp (τ : ℂ) (n : ℕ) :
    (jacobi_q τ) ^ (2 * n + 1) =
      Complex.exp
        ((2 * Real.pi : ℂ) * Complex.I * (((n : ℂ) + (1 / 2 : ℂ)) * τ)) := by
  -- Rewrite the odd power as an exponential of `(2 n + 1) π I τ = 2 π I ((n + 1 / 2) τ)`.
  calc
    (jacobi_q τ) ^ (2 * n + 1)
        = Complex.exp (((2 * n + 1 : ℕ) : ℂ) * (Real.pi * Complex.I * τ)) := by
            rw [jacobi_q_eq_exp, ← Complex.exp_nat_mul]
    _ = Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (((n : ℂ) + (1 / 2 : ℂ)) * τ)) := by
          congr 1
          calc
            (((2 * n + 1 : ℕ) : ℂ) * (Real.pi * Complex.I * τ))
                = (((2 : ℂ) * ((n : ℂ) + (1 / 2 : ℂ))) * (Real.pi * Complex.I * τ)) := by
                    congr 1
                    norm_num
                    ring
            _ = (2 * Real.pi : ℂ) * Complex.I * (((n : ℂ) + (1 / 2 : ℂ)) * τ) := by
                  ring

/-- Helper for Exercise II: expanding the `1 + uₙ` perturbation isolates the two linear
exponential terms and the quadratic correction term. -/
theorem theta_zero_product_perturbation_expanded (τ : ℂ) (n : ℕ) (u : ℂ) :
    theta_zero_product_perturbation τ n u =
      -((jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) -
        ((jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) +
        (jacobi_q τ) ^ (4 * n + 2) := by
  -- Expand `(1 - a)(1 - b) - 1 = -a - b + ab`, then collapse the exponential pair to `1`.
  let a :=
    (jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)
  let b :=
    (jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)
  have hab :
      a * b = (jacobi_q τ) ^ (4 * n + 2) := by
    -- The two exponentials are inverse to each other, so only the `q`-power remains.
    calc
      a * b
          = ((jacobi_q τ) ^ (2 * n + 1) * (jacobi_q τ) ^ (2 * n + 1)) *
              (Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) *
                Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) := by
                dsimp [a, b]
                ring
      _ = ((jacobi_q τ) ^ (2 * n + 1) * (jacobi_q τ) ^ (2 * n + 1)) * 1 := by
            congr 1
            calc
              Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) *
                  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)
                = Complex.exp (((2 * Real.pi : ℂ) * Complex.I * u) +
                    (-(2 * Real.pi : ℂ) * Complex.I * u)) := by
                      rw [← Complex.exp_add]
              _ = 1 := by simp
      _ = (jacobi_q τ) ^ (4 * n + 2) := by
            rw [mul_one, ← pow_add]
            congr 1
            omega
  rw [theta_zero_product_perturbation_apply, theta_zero_product_factor_apply]
  calc
    (1 - a) * (1 - b) - 1 = -a - b + a * b := by ring
    _ = -a - b + (jacobi_q τ) ^ (4 * n + 2) := by rw [hab]
    _ = -((jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) -
          ((jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) +
          (jacobi_q τ) ^ (4 * n + 2) := by
            rfl

/-- Helper for Exercise II: on a compact set, the perturbations of the product factors admit a
uniform geometric majorant in the ratio `‖jacobi_q τ‖²`. -/
theorem theta_zero_product_compact_exponential_majorant
    (τ : ℂ) (hτ : 0 < τ.im) {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n z, z ∈ K →
      ‖theta_zero_product_perturbation τ n z‖ ≤ C * (‖jacobi_q τ‖ ^ 2) ^ n := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  let R : ℝ := max R₀ 0
  have hR : ∀ z, z ∈ K → ‖z‖ ≤ R := by
    intro z hz
    exact le_trans (hR₀ z hz) (le_max_left _ _)
  have hR_nonneg : 0 ≤ R := le_max_right _ _
  let E : ℝ := Real.exp (2 * Real.pi * R)
  let q : ℝ := ‖jacobi_q τ‖
  have hq_lt_one : q < 1 := jacobi_q_norm_lt_one τ hτ
  have hq_nonneg : 0 ≤ q := norm_nonneg _
  have hq_le_one : q ≤ 1 := hq_lt_one.le
  let C : ℝ := 2 * E * q + q ^ (2 : ℕ)
  refine ⟨C, by positivity, ?_⟩
  intro n z hz
  have hzR : ‖z‖ ≤ R := hR z hz
  have hpos_re :
      (((2 * Real.pi : ℂ) * Complex.I * z).re) ≤ 2 * Real.pi * R := by
    have him_le : |z.im| ≤ R := le_trans (Complex.abs_im_le_norm z) hzR
    have him_lower : -R ≤ z.im := (abs_le.mp him_le).1
    have hre :
        (((2 * Real.pi : ℂ) * Complex.I * z).re) = -(2 * Real.pi) * z.im := by
      simpa [Complex.mul_re, Complex.mul_im]
    rw [hre]
    nlinarith [Real.pi_pos, him_lower]
  have hneg_re :
      ((-(2 * Real.pi : ℂ) * Complex.I * z).re) ≤ 2 * Real.pi * R := by
    have him_le : |z.im| ≤ R := le_trans (Complex.abs_im_le_norm z) hzR
    have him_upper : z.im ≤ R := (abs_le.mp him_le).2
    have hre :
        ((-(2 * Real.pi : ℂ) * Complex.I * z).re) = (2 * Real.pi) * z.im := by
      simpa [Complex.mul_re, Complex.mul_im]
    rw [hre]
    nlinarith [Real.pi_pos, him_upper]
  have hpos_exp :
      ‖Complex.exp ((2 * Real.pi : ℂ) * Complex.I * z)‖ ≤ E := by
    -- The compact bound on `|Im z|` gives a uniform bound for the positive exponential branch.
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hpos_re)
  have hneg_exp :
      ‖Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z)‖ ≤ E := by
    -- The negative branch is bounded by the same compact exponential constant.
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hneg_re)
  have hq_pow_odd :
      q ^ (2 * n + 1) = q * (q ^ 2) ^ n := by
    calc
      q ^ (2 * n + 1) = q ^ (1 + 2 * n) := by congr 1; omega
      _ = q ^ (1 : ℕ) * q ^ (2 * n) := by rw [pow_add]
      _ = q * (q ^ 2) ^ n := by
            rw [pow_one, pow_mul]
  have hq_pow_even :
      q ^ (2 * n + 2) = q ^ (2 : ℕ) * (q ^ 2) ^ n := by
    calc
      q ^ (2 * n + 2) = q ^ (2 + 2 * n) := by congr 1; omega
      _ = q ^ (2 : ℕ) * q ^ (2 * n) := by rw [pow_add]
      _ = q ^ (2 : ℕ) * (q ^ 2) ^ n := by rw [pow_mul]
  have hq_pow_quad_le :
      q ^ (4 * n + 2) ≤ q ^ (2 : ℕ) * (q ^ 2) ^ n := by
    have hpow_le_one : q ^ (2 * n) ≤ 1 := pow_le_one₀ hq_nonneg hq_le_one
    calc
      q ^ (4 * n + 2) = q ^ (2 * n + 2) * q ^ (2 * n) := by
        rw [show 4 * n + 2 = (2 * n + 2) + 2 * n by omega, pow_add]
      _ ≤ q ^ (2 * n + 2) * 1 := by
            gcongr
      _ = q ^ (2 : ℕ) * (q ^ 2) ^ n := by simpa [hq_pow_even]
  let A :=
    (jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * z)
  let B :=
    (jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z)
  let D := (jacobi_q τ) ^ (4 * n + 2)
  have hA :
      ‖A‖ ≤ E * q * (q ^ 2) ^ n := by
    -- The odd `q`-power contributes one extra `q`, and the compact exponential bound absorbs
    -- the remaining oscillatory factor.
    calc
      ‖A‖ = q ^ (2 * n + 1) * ‖Complex.exp ((2 * Real.pi : ℂ) * Complex.I * z)‖ := by
              simp [A, q, norm_mul, norm_pow]
      _ ≤ q ^ (2 * n + 1) * E := by
            gcongr
      _ = E * q * (q ^ 2) ^ n := by rw [hq_pow_odd]; ring
  have hB :
      ‖B‖ ≤ E * q * (q ^ 2) ^ n := by
    -- The same argument controls the negative exponential branch.
    calc
      ‖B‖ = q ^ (2 * n + 1) * ‖Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z)‖ := by
              simp [B, q, norm_mul, norm_pow]
      _ ≤ q ^ (2 * n + 1) * E := by
            gcongr
      _ = E * q * (q ^ 2) ^ n := by rw [hq_pow_odd]; ring
  have hD :
      ‖D‖ ≤ q ^ (2 : ℕ) * (q ^ 2) ^ n := by
    -- The quadratic correction has an even higher `q`-power, so it is dominated by the same
    -- geometric ratio.
    calc
      ‖D‖ = q ^ (4 * n + 2) := by simp [D, q, norm_pow]
      _ ≤ q ^ (2 : ℕ) * (q ^ 2) ^ n := hq_pow_quad_le
  have htriangle :
      ‖-A - B + D‖ ≤ ‖A‖ + ‖B‖ + ‖D‖ := by
    calc
      ‖-A - B + D‖ = ‖(-A - B) + D‖ := by ring_nf
      _ ≤ ‖-A - B‖ + ‖D‖ := norm_add_le _ _
      _ ≤ (‖-A‖ + ‖B‖) + ‖D‖ := by
            simpa [sub_eq_add_neg] using add_le_add_right (norm_add_le (-A) (-B)) ‖D‖
      _ = ‖A‖ + ‖B‖ + ‖D‖ := by simp [add_assoc]
  have hsum_bound :
      ‖A‖ + ‖B‖ + ‖D‖ ≤ C * (q ^ 2) ^ n := by
    calc
      ‖A‖ + ‖B‖ + ‖D‖
          ≤ E * q * (q ^ 2) ^ n + (E * q * (q ^ 2) ^ n + q ^ (2 : ℕ) * (q ^ 2) ^ n) := by
              nlinarith [hA, hB, hD]
      _ = C * (q ^ 2) ^ n := by
            dsimp [C]
            ring
  calc
    ‖theta_zero_product_perturbation τ n z‖ = ‖-A - B + D‖ := by
          simp [A, B, D, theta_zero_product_perturbation_expanded]
    _ ≤ ‖A‖ + ‖B‖ + ‖D‖ := htriangle
    _ ≤ C * (q ^ 2) ^ n := hsum_bound
    _ = C * (‖jacobi_q τ‖ ^ 2) ^ n := by simp [q]

/-- Helper for Exercise II: on a compact set, the perturbations of the product factors admit a
uniform geometric majorant. -/
theorem theta_zero_product_perturbation_normallySummableOn
    (τ : ℂ) (hτ : 0 < τ.im) {K : Set ℂ} (hK : IsCompact K) :
    NormallySummableOn (theta_zero_product_perturbation τ) K := by
  -- Package the compact majorant as the `NNReal` summable sequence required by
  -- `NormallySummableOn`.
  obtain ⟨C, hC_nonneg, hC⟩ :=
    theta_zero_product_compact_exponential_majorant τ hτ hK
  refine ⟨fun n ↦ ⟨C * (‖jacobi_q τ‖ ^ 2) ^ n, by positivity⟩, ?_, ?_⟩
  · have hq2_lt_one : ‖jacobi_q τ‖ ^ (2 : ℕ) < 1 := by
      have hq := jacobi_q_norm_lt_one τ hτ
      nlinarith [hq, norm_nonneg (jacobi_q τ)]
    have hgeom : Summable (fun n : ℕ ↦ (‖jacobi_q τ‖ ^ (2 : ℕ)) ^ n) :=
      summable_geometric_of_lt_one (show 0 ≤ ‖jacobi_q τ‖ ^ (2 : ℕ) by positivity) hq2_lt_one
    -- The geometric majorant is summable because `‖q‖² < 1`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgeom.mul_left C
  · intro n z hz
    exact hC n z hz

/-- Helper for Exercise II: the source product converges compact-normally on `ℂ`. -/
theorem jacobi_theta_zero_product_normallyMultipliableOnCompacta
    (τ : ℂ) (hτ : 0 < τ.im) :
    NormallyMultipliableOnCompacta (theta_zero_product_factor τ) Set.univ := by
  -- Route correction: once the perturbation family is normally summable on every compact set, the
  -- remaining task is exactly the standard `1 + uₙ` slit/log packaging from the chapter API.
  have honeadd :
      NormallyMultipliableOnCompacta
        (fun n z ↦ 1 + theta_zero_product_perturbation τ n z) Set.univ := by
    refine
      (normallyMultipliableOnCompacta_one_add_iff
        (u := theta_zero_product_perturbation τ) (D := Set.univ)).mpr ?_
    refine ⟨isOpen_univ, ?_, ?_⟩
    · intro n
      -- Each perturbation is entire because the underlying factor is entire.
      exact (theta_zero_product_factor_differentiableOn τ n).continuousOn.sub continuousOn_const
    · intro K hK _hK_univ
      have hsum : NormallySummableOn (theta_zero_product_perturbation τ) K :=
        theta_zero_product_perturbation_normallySummableOn τ hτ hK
      have hzero :
          TendstoUniformlyOn
            (theta_zero_product_perturbation τ) (fun _ ↦ (0 : ℂ)) Filter.atTop K :=
        hsum.tendstoUniformlyOn_zero
      rw [Metric.tendstoUniformlyOn_iff] at hzero
      have hhalf := hzero (1 / 2) (by norm_num)
      rw [Filter.eventually_atTop] at hhalf
      rcases hhalf with ⟨N, hN⟩
      have hsum_tail :
          NormallySummableOn (fun n z ↦ theta_zero_product_perturbation τ (n + N) z) K :=
        hsum.nat_add N
      rcases hsum_tail with ⟨a, ha, hbound⟩
      refine ⟨N, ?_, ?_⟩
      · intro n z hz
        have hhalf_n : ‖theta_zero_product_perturbation τ (n + N) z‖ ≤ 1 / 2 := by
          simpa [dist_eq_norm] using (hN (n + N) (by omega) z hz).le
        -- Once the perturbation lies in the half-ball, `1 + uₙ(z)` stays in the slit plane.
        simpa [theta_zero_product_perturbation] using
          Complex.mem_slitPlane_of_norm_lt_one
            (z := theta_zero_product_perturbation τ (n + N) z)
            (lt_of_le_of_lt hhalf_n (by norm_num))
      · refine ⟨fun n ↦ ⟨(3 / 2 : ℝ) * a n, by positivity⟩, ?_, ?_⟩
        · -- The logarithmic tail is dominated termwise by the shifted perturbation series.
          simpa [mul_assoc, mul_left_comm, mul_comm] using ha.mul_left (3 / 2 : ℝ)
        · intro n z hz
          have hhalf_n : ‖theta_zero_product_perturbation τ (n + N) z‖ ≤ 1 / 2 := by
            simpa [dist_eq_norm] using (hN (n + N) (by omega) z hz).le
          calc
            ‖Complex.log (1 + theta_zero_product_perturbation τ (n + N) z)‖
                ≤ (3 / 2 : ℝ) * ‖theta_zero_product_perturbation τ (n + N) z‖ :=
                  Complex.norm_log_one_add_half_le_self hhalf_n
            _ ≤ (3 / 2 : ℝ) * a n := by
                  gcongr
                  exact hbound n z hz
  have hfactor_eq :
      (fun n z ↦ 1 + theta_zero_product_perturbation τ n z) = theta_zero_product_factor τ := by
    funext n z
    simp [theta_zero_product_perturbation]
  exact hfactor_eq ▸ honeadd

/-- Helper for Exercise II: a single factor vanishes exactly when `u` lies on one of the two
half-shifted translates determined by its odd exponent. -/
theorem theta_zero_product_factor_zero_iff (τ u : ℂ) (n : ℕ) :
    theta_zero_product_factor τ n u = 0 ↔
      ∃ m : ℤ,
        u = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ ∨
        u = m - ((n : ℂ) + (1 / 2 : ℂ)) * τ := by
  let shift : ℂ := ((n : ℂ) + (1 / 2 : ℂ)) * τ
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    simp [c, Real.pi_ne_zero]
  have hq : (jacobi_q τ) ^ (2 * n + 1) = Complex.exp (c * shift) := by
    -- Rewrite the odd power of `q` into the exponential attached to the half-shifted lattice.
    simpa [c, shift] using jacobi_q_pow_two_mul_add_one_eq_exp τ n
  rw [theta_zero_product_factor_apply]
  constructor
  · intro hzero
    -- Split the factorization into the two scalar exponential equations.
    rcases mul_eq_zero.mp hzero with hpos | hneg
    · have hone :
        (jacobi_q τ) ^ (2 * n + 1) * Complex.exp (c * u) = 1 := by
        exact eq_comm.mp (sub_eq_zero.mp hpos)
      have hexp : Complex.exp (c * (shift + u)) = 1 := by
        calc
          Complex.exp (c * (shift + u))
              = Complex.exp (c * shift + c * u) := by
                  congr 1
                  ring
          _ = Complex.exp (c * shift) * Complex.exp (c * u) := by
                rw [Complex.exp_add]
          _ = 1 := by
                rw [← hq, hone]
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
      have hsum : shift + u = (m : ℂ) := by
        -- Cancel the nonzero scalar `2 π I` to recover the affine lattice equation for `u`.
        have hm' : c * (shift + u) = c * (m : ℂ) := by
          calc
            c * (shift + u) = (m : ℂ) * c := hm
            _ = c * (m : ℂ) := by ring
        exact mul_left_cancel₀ hc hm'
      refine ⟨m, Or.inr ?_⟩
      calc
        u = (shift + u) - shift := by ring
        _ = (m : ℂ) - shift := by rw [hsum]
        _ = (m : ℂ) - ((n : ℂ) + (1 / 2 : ℂ)) * τ := by rfl
    · have hone :
        (jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) = 1 := by
        exact eq_comm.mp (sub_eq_zero.mp hneg)
      have hexp : Complex.exp (c * (shift - u)) = 1 := by
        calc
          Complex.exp (c * (shift - u))
              = Complex.exp (c * shift + (-(2 * Real.pi : ℂ) * Complex.I * u)) := by
                  congr 1
                  ring
          _ = Complex.exp (c * shift) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) := by
                rw [Complex.exp_add]
          _ = 1 := by
                rw [← hq, hone]
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
      have hdiff : shift - u = (m : ℂ) := by
        -- The second linear factor gives the opposite sign in the shifted-lattice equation.
        have hm' : c * (shift - u) = c * (m : ℂ) := by
          calc
            c * (shift - u) = (m : ℂ) * c := hm
            _ = c * (m : ℂ) := by ring
        exact mul_left_cancel₀ hc hm'
      refine ⟨-m, Or.inl ?_⟩
      calc
        u = shift - (m : ℂ) := by
              calc
                u = shift - (shift - u) := by ring
                _ = shift - (m : ℂ) := by rw [hdiff]
        _ = ((-m : ℤ) : ℂ) + shift := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        _ = ((-m : ℤ) : ℂ) + (((n : ℂ) + (1 / 2 : ℂ)) * τ) := by rfl
  · rintro ⟨m, hm | hm⟩
    · -- A point on the positive branch kills the second linear factor.
      apply mul_eq_zero.mpr
      right
      apply sub_eq_zero.mpr
      have hbranch :
          Complex.exp (c * shift) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) = 1 := by
        have hshift_sub : shift - u = ((-m : ℤ) : ℂ) := by
          rw [hm]
          calc
            shift - ((m : ℂ) + shift) = -(m : ℂ) := by ring
            _ = ((-m : ℤ) : ℂ) := by simp
        calc
          Complex.exp (c * shift) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)
              = Complex.exp (c * (shift - u)) := by
                  rw [← Complex.exp_add]
                  congr 1
                  ring
          _ = Complex.exp (((-m : ℤ) : ℂ) * c) := by
                rw [hshift_sub]
                ring
          _ = 1 := by
                simpa [c, mul_comm] using (Complex.exp_eq_one_iff.mpr ⟨-m, rfl⟩)
      simpa [hq] using hbranch.symm
    · -- A point on the negative branch kills the first linear factor.
      apply mul_eq_zero.mpr
      left
      apply sub_eq_zero.mpr
      have hbranch :
          Complex.exp (c * shift) * Complex.exp (c * u) = 1 := by
        calc
          Complex.exp (c * shift) * Complex.exp (c * u)
              = Complex.exp (c * (shift + u)) := by
                  rw [← Complex.exp_add]
                  congr 1
                  ring
          _ = Complex.exp ((m : ℂ) * c) := by
                congr 1
                rw [hm]
                ring
          _ = 1 := by
                simpa [c, mul_comm] using (Complex.exp_eq_one_iff.mpr ⟨m, rfl⟩)
      simpa [hq] using hbranch.symm

/-- Helper for Exercise II: the nat-indexed `±` shifted lattice produced by the factor zeros is
exactly the textbook integer-indexed shifted lattice. -/
theorem theta_zero_product_shifted_lattice_nat_sign_iff_int (τ u : ℂ) :
    (∃ n : ℕ,
      ∃ m : ℤ,
        u = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ ∨
        u = m - ((n : ℂ) + (1 / 2 : ℂ)) * τ) ↔
      ∃ m n : ℤ, u = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ := by
  constructor
  · rintro ⟨n, m, hm | hm⟩
    · -- The positive branch is already in the target normal form.
      exact ⟨m, (n : ℤ), by simpa using hm⟩
    · -- The negative branch corresponds to the integer index `-(n + 1)`.
      refine ⟨m, Int.negSucc n, ?_⟩
      calc
        u = m - ((n : ℂ) + (1 / 2 : ℂ)) * τ := hm
        _ = m + ((((Int.negSucc n : ℤ) : ℂ) + (1 / 2 : ℂ)) * τ) := by
              simp [Int.negSucc_eq, sub_eq_add_neg]
              ring
  · rintro ⟨m, k, hk⟩
    cases k with
    | ofNat n =>
        -- Nonnegative indices stay on the positive branch of the factor-zero classification.
        exact ⟨n, m, Or.inl hk⟩
    | negSucc n =>
        -- Negative indices are exactly the negative branch with nat parameter `n`.
        refine ⟨n, m, Or.inr ?_⟩
        calc
          u = m + ((((Int.negSucc n : ℤ) : ℂ) + (1 / 2 : ℂ)) * τ) := hk
          _ = m - ((n : ℂ) + (1 / 2 : ℂ)) * τ := by
                simp [Int.negSucc_eq, sub_eq_add_neg]
                ring

/-- Exercise II (1): when `Im τ > 0`, the source infinite product defines an entire function of
`u`. -/
theorem exercise_ii_jacobi_theta_zero_product_differentiable
    (τ : ℂ) (hτ : 0 < τ.im) :
    Differentiable ℂ (jacobi_theta_zero_product τ) := by
  intro u
  -- Reindex the product to `ℕ`, then apply the Chapter V holomorphy theorem on `Set.univ`.
  have hdiff :
      DifferentiableOn ℂ (fun z ↦ ∏' n : ℕ, theta_zero_product_factor τ n z) Set.univ :=
    differentiableOn_tprod_of_normallyMultipliableOnCompacta isOpen_univ
      (fun n ↦ theta_zero_product_factor_differentiableOn τ n)
      (jacobi_theta_zero_product_normallyMultipliableOnCompacta τ hτ)
  have hdiffAt : DifferentiableAt ℂ (fun z ↦ ∏' n : ℕ, theta_zero_product_factor τ n z) u := by
    simpa [differentiableWithinAt_univ] using hdiff u (by simp)
  have hprod_eq :
      jacobi_theta_zero_product τ = fun z ↦ ∏' n : ℕ, theta_zero_product_factor τ n z := by
    funext z
    exact jacobi_theta_zero_product_eq_tprod_nat τ z
  simpa [hprod_eq] using hdiffAt

/-- Exercise II (2): when `Im τ > 0`, the zeros of the source infinite product are exactly the
shifted lattice points `m + (n + 1 / 2)τ`. -/
theorem exercise_ii_jacobi_theta_zero_product_zero_iff
    (τ u : ℂ) (hτ : 0 < τ.im) :
    jacobi_theta_zero_product τ u = 0 ↔
      ∃ m n : ℤ, u = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ := by
  -- Route correction: first translate the global zero-set theorem into an `ℕ`-indexed factor
  -- statement, then use the explicit factor-zero classification to recover the textbook lattice.
  rw [jacobi_theta_zero_product_eq_tprod_nat]
  have hzero :
      (∏' n : ℕ, theta_zero_product_factor τ n u) = 0 ↔
        ∃ n : ℕ, theta_zero_product_factor τ n u = 0 := by
    exact Iff.of_eq <| by
      simpa using congrArg (fun s : Set ℂ => u ∈ s)
        (zeroSet_tprod_eq_iUnion_zeroSet_of_normallyMultipliableOnCompacta
          (D := Set.univ) (f := theta_zero_product_factor τ)
          (jacobi_theta_zero_product_normallyMultipliableOnCompacta τ hτ))
  calc
    (∏' n : ℕ, theta_zero_product_factor τ n u) = 0
        ↔ ∃ n : ℕ, theta_zero_product_factor τ n u = 0 := hzero
    _ ↔
        ∃ n : ℕ,
          ∃ m : ℤ,
            u = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ ∨
            u = m - ((n : ℂ) + (1 / 2 : ℂ)) * τ := by
          simp [theta_zero_product_factor_zero_iff]
    _ ↔ ∃ m n : ℤ, u = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ :=
          theta_zero_product_shifted_lattice_nat_sign_iff_int τ u

/-- Helper for Exercise II: if `‖q‖ < 1`, then the odd-indexed factors `1 - q^(2n+1) * z`
form a convergent infinite product. -/
lemma odd_theta_factors_multipliable {q z : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun n : ℕ ↦ 1 - q ^ (2 * n + 1) * z) := by
  -- Rewrite the odd powers as a fixed scalar times a geometric progression in `q²`.
  have hq2_lt_one : ‖q ^ (2 : ℕ)‖ < 1 := by
    simpa [norm_pow] using pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hgeom : Summable (fun n : ℕ ↦ (q ^ (2 : ℕ)) ^ n) :=
    summable_geometric_of_norm_lt_one hq2_lt_one
  have hsummable :
      Summable (fun n : ℕ ↦ -(q ^ (2 * n + 1) * z)) := by
    have hscaled : Summable (fun n : ℕ ↦ (-q * z) * (q ^ (2 : ℕ)) ^ n) :=
      hgeom.mul_left (-q * z)
    refine hscaled.congr ?_
    intro n
    have hpow : q ^ (2 * n + 1) = q * (q ^ (2 : ℕ)) ^ n := by
      rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add, pow_one, pow_mul]
    rw [hpow]
    ring
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hsummable

/-- Helper for Exercise II: `q²` is the exponential multiplier acquired by shifting `u` by `τ`
inside the Jacobi product factors. -/
lemma jacobi_q_sq_eq_exp_two_pi_I_mul (τ : ℂ) :
    (jacobi_q τ) ^ (2 : ℕ) = Complex.exp ((2 * Real.pi : ℂ) * Complex.I * τ) := by
  -- Expand `q = exp (π I τ)` and absorb the factor `2` into the exponent.
  calc
    (jacobi_q τ) ^ (2 : ℕ) = Complex.exp (((2 : ℕ) : ℂ) * (Real.pi * Complex.I * τ)) := by
      rw [jacobi_q_eq_exp, ← Complex.exp_nat_mul]
    _ = Complex.exp ((2 * Real.pi : ℂ) * Complex.I * τ) := by
      congr 1
      ring

/-- Helper for Exercise II: the positive odd-exponential branch of the source product. -/
def theta_zero_positive_branch (τ : ℂ) (u : ℂ) (n : ℕ) : ℂ :=
  1 - (jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)

/-- Helper for Exercise II: the negative odd-exponential branch of the source product. -/
def theta_zero_negative_branch (τ : ℂ) (u : ℂ) (n : ℕ) : ℂ :=
  1 - (jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)

/-- Helper for Exercise II: shifting the positive exponential branch by `τ` just reindexes the odd
`q`-powers from `2 n + 1` to `2 (n + 1) + 1`. -/
lemma theta_zero_positive_branch_add_tau_reindex (τ u : ℂ) :
    ∏' n : ℕ,
      (1 - (jacobi_q τ) ^ (2 * n + 1) *
        Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (u + τ))) =
      ∏' n : ℕ,
        (1 - (jacobi_q τ) ^ (2 * (n + 1) + 1) *
          Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) := by
  -- Rewrite the shifted exponential as `exp (2π I u) * q²`, then absorb `q²` into the odd power.
  refine tprod_congr fun n ↦ ?_
  have hexp :
      Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (u + τ)) =
        Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) * (jacobi_q τ) ^ (2 : ℕ) := by
    calc
      Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (u + τ))
          = Complex.exp
              (((2 * Real.pi : ℂ) * Complex.I * u) +
                ((2 * Real.pi : ℂ) * Complex.I * τ)) := by
                congr 1
                ring
      _ = Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) *
            Complex.exp ((2 * Real.pi : ℂ) * Complex.I * τ) := by
              rw [Complex.exp_add]
      _ = Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) * (jacobi_q τ) ^ (2 : ℕ) := by
            rw [← jacobi_q_sq_eq_exp_two_pi_I_mul τ]
  rw [hexp]
  calc
    1 -
        (jacobi_q τ) ^ (2 * n + 1) *
          (Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) * (jacobi_q τ) ^ (2 : ℕ))
      =
        1 -
          (((jacobi_q τ) ^ (2 * n + 1) * (jacobi_q τ) ^ (2 : ℕ)) *
            Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) := by
              congr 1
              ring
    _ =
        1 -
          ((jacobi_q τ) ^ (2 * (n + 1) + 1) *
            Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) := by
              have hpow :
                  (jacobi_q τ) ^ (2 * n + 1) * (jacobi_q τ) ^ (2 : ℕ) =
                    (jacobi_q τ) ^ (2 * (n + 1) + 1) := by
                have hpow' :
                    (jacobi_q τ) ^ (2 * n + 1) * (jacobi_q τ) ^ (2 : ℕ) =
                      (jacobi_q τ) ^ ((2 * n + 1) + 2) := by
                  rw [← pow_add]
                have hidx : (2 * n + 1) + 2 = 2 * (n + 1) + 1 := by
                  omega
                simpa [hidx] using hpow'
              rw [hpow]

/-- Helper for Exercise II: the positive odd branch is pointwise multipliable because it is the
standard odd-indexed geometric perturbation family. -/
lemma theta_zero_positive_branch_multipliable (τ u : ℂ) (hτ : 0 < τ.im) :
    Multipliable (theta_zero_positive_branch τ u) := by
  -- Keep the branch opaque until the final line so the pointwise odd-product theorem applies
  -- without reopening the expanded family inside later split lemmas.
  change Multipliable (fun n : ℕ ↦
    1 - (jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))
  exact
    odd_theta_factors_multipliable
      (q := jacobi_q τ)
      (z := Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))
      (jacobi_q_norm_lt_one τ hτ)

/-- Helper for Exercise II: the positive odd branch splits into its `n = 0` head factor and the
remaining tail, written explicitly so the standard head-tail theorem applies before any branch
abbreviation unfolds. -/
lemma theta_zero_positive_branch_head_split (τ u : ℂ) (hτ : 0 < τ.im) :
    (∏' n : ℕ, theta_zero_positive_branch τ u n) =
      theta_zero_positive_branch τ u 0 *
        ∏' n : ℕ, theta_zero_positive_branch τ u (n + 1) := by
  -- Keep the branch opaque and apply the dedicated nat-indexed head-tail theorem directly.
  let f : ℕ → ℂ := theta_zero_positive_branch τ u
  have htail : Multipliable (fun n : ℕ ↦ f (n + 1)) := by
    let g : ℕ → ℂ := fun n ↦
      1 -
        (jacobi_q τ) ^ (2 * n + 1) *
          (Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) * (jacobi_q τ) ^ (2 : ℕ))
    have hg : Multipliable g := by
      exact
        odd_theta_factors_multipliable
          (q := jacobi_q τ)
          (z := Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) * (jacobi_q τ) ^ (2 : ℕ))
          (jacobi_q_norm_lt_one τ hτ)
    refine hg.congr ?_
    intro n
    dsimp [g, f, theta_zero_positive_branch]
    have hidx : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
    rw [hidx, pow_add, pow_two]
    ring
  simpa [f] using tprod_eq_zero_mul' (f := f) htail

/-- Helper for Exercise II: shifting the negative exponential branch by `τ` contributes one extra
head factor and otherwise recovers the original odd branch. -/
lemma theta_zero_negative_branch_add_tau_split (τ u : ℂ) (hτ : 0 < τ.im) :
    ∏' n : ℕ,
      (1 - (jacobi_q τ) ^ (2 * n + 1) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (u + τ))) =
      (1 - (jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
        ∏' n : ℕ,
          (1 - (jacobi_q τ) ^ (2 * n + 1) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) := by
  let q : ℂ := jacobi_q τ
  let e : ℂ := Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)
  let shifted : ℕ → ℂ := fun n ↦
    1 - q ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (u + τ))
  let split : ℕ → ℂ
    | 0 => 1 - q⁻¹ * e
    | n + 1 => 1 - q ^ (2 * n + 1) * e
  have hq_ne : q ≠ 0 := by
    simpa [q, jacobi_q_eq_exp] using Complex.exp_ne_zero (Real.pi * Complex.I * τ)
  have htail :
      Multipliable (fun n : ℕ ↦ 1 - q ^ (2 * n + 1) * e) := by
    -- The unshifted negative branch is an odd-indexed geometric perturbation.
    simpa [q, e] using
      (odd_theta_factors_multipliable
        (q := jacobi_q τ) (z := Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u))
        (jacobi_q_norm_lt_one τ hτ))
  have hshifted_eq :
      ∏' n : ℕ, shifted n = ∏' n : ℕ, split n := by
    -- After expanding `exp (-(2π I) (u + τ))`, the `n = 0` term becomes the extra head factor and
    -- the tail matches the original branch.
    have hexp :
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (u + τ)) = e * q⁻¹ * q⁻¹ := by
      calc
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (u + τ))
            = Complex.exp
                ((-(2 * Real.pi : ℂ) * Complex.I * u) +
                  (-(2 * Real.pi : ℂ) * Complex.I * τ)) := by
                    congr 1
                    ring
        _ = Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * τ) := by
                rw [Complex.exp_add]
        _ = e * Complex.exp (-((2 * Real.pi : ℂ) * Complex.I * τ)) := by
              rw [show (-(2 * Real.pi : ℂ) * Complex.I * τ) =
                  -((2 * Real.pi : ℂ) * Complex.I * τ) by ring]
        _ = e * (Complex.exp ((2 * Real.pi : ℂ) * Complex.I * τ))⁻¹ := by
              rw [Complex.exp_neg]
        _ = e * ((q ^ (2 : ℕ))⁻¹) := by
              rw [← jacobi_q_sq_eq_exp_two_pi_I_mul τ]
        _ = e * q⁻¹ * q⁻¹ := by
              simp [pow_two, mul_inv_rev, mul_assoc]
    refine tprod_congr fun n ↦ ?_
    cases n with
    | zero =>
        dsimp [shifted, split]
        rw [hexp]
        congr 1
        calc
          q ^ (2 * 0 + 1) * (e * q⁻¹ * q⁻¹)
              = e * (q * q⁻¹) * q⁻¹ := by
                  simp
                  ring
          _ = q⁻¹ * e := by
                simp [hq_ne]
                ring
    | succ n =>
        dsimp [shifted, split]
        rw [hexp]
        congr 1
        have hcancel :
            (q * q) * (q⁻¹ * q⁻¹) = 1 := by
          calc
            (q * q) * (q⁻¹ * q⁻¹) = (q * q⁻¹) * (q * q⁻¹) := by ring
            _ = 1 := by simp [hq_ne]
        calc
          q ^ (2 * Nat.succ n + 1) * (e * q⁻¹ * q⁻¹)
              = q ^ (2 * n + 1) * (q * q) * (e * q⁻¹ * q⁻¹) := by
                  rw [show 2 * Nat.succ n + 1 = (2 * n + 1) + 2 by omega, pow_add, pow_two]
          _ = q ^ (2 * n + 1) * e * ((q * q) * (q⁻¹ * q⁻¹)) := by ring
          _ = q ^ (2 * n + 1) * e := by rw [hcancel]; ring
  have hsplit :
      ∏' n : ℕ, split n = (1 - q⁻¹ * e) * ∏' n : ℕ, (1 - q ^ (2 * n + 1) * e) := by
    -- Peel off the `n = 0` head term from the split branch.
    simpa [split] using
      (tprod_eq_zero_mul'
        (f := split)
        (by
          simpa [split] using htail))
  simpa [shifted, q, e] using hshifted_eq.trans hsplit

/-- Helper for Exercise II: the odd theta-zero product splits into independent positive and
negative exponential branches. -/
lemma theta_zero_product_explicit_branch_split (τ u : ℂ) (hτ : 0 < τ.im) :
    jacobi_theta_zero_product τ u =
      (∏' n : ℕ, theta_zero_positive_branch τ u n) *
        ∏' n : ℕ, theta_zero_negative_branch τ u n := by
  have hpos : Multipliable (theta_zero_positive_branch τ u) := by
    -- The positive branch is the standard odd geometric perturbation family.
    change Multipliable (fun n : ℕ ↦
      1 - (jacobi_q τ) ^ (2 * n + 1) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))
    exact
      (odd_theta_factors_multipliable
        (q := jacobi_q τ)
        (z := Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))
        (jacobi_q_norm_lt_one τ hτ))
  have hneg : Multipliable (theta_zero_negative_branch τ u) := by
    -- The negative branch is the same family with the opposite exponential parameter.
    change Multipliable (fun n : ℕ ↦
      1 - (jacobi_q τ) ^ (2 * n + 1) * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u))
    exact
      (odd_theta_factors_multipliable
        (q := jacobi_q τ)
        (z := Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u))
        (jacobi_q_norm_lt_one τ hτ))
  -- Freeze the full factor as `pos n * neg n`, then apply the stable `tprod_mul` theorem once.
  rw [jacobi_theta_zero_product_eq_tprod_nat]
  calc
    ∏' n : ℕ, theta_zero_product_factor τ n u =
        ∏' n : ℕ, theta_zero_positive_branch τ u n * theta_zero_negative_branch τ u n := by
      refine tprod_congr fun n ↦ ?_
      simp [theta_zero_positive_branch, theta_zero_negative_branch, theta_zero_product_factor]
    _ = (∏' n : ℕ, theta_zero_positive_branch τ u n) * ∏' n : ℕ, theta_zero_negative_branch τ u n := by
      simpa using hpos.tprod_mul hneg

/-- Helper for Exercise II: after shifting by `τ`, the source product factors as the extra
negative head term times the common positive tail and negative branch. -/
lemma theta_zero_product_shifted_split (τ u : ℂ) (hτ : 0 < τ.im) :
    jacobi_theta_zero_product τ (u + τ) =
      (1 - (jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
        ((∏' n : ℕ,
            (1 - (jacobi_q τ) ^ (2 * (n + 1) + 1) *
              Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))) *
          ∏' n : ℕ,
            (1 - (jacobi_q τ) ^ (2 * n + 1) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u))) := by
  -- Route correction: first freeze the full product as branchwise `tprod`s, then substitute the
  -- already-proved shifted branch identities without reopening the expanded factor family.
  rw [theta_zero_product_explicit_branch_split τ (u + τ) hτ]
  rw [show ∏' n : ℕ, theta_zero_positive_branch τ (u + τ) n =
      ∏' n : ℕ, theta_zero_positive_branch τ u (n + 1) by
        simpa [theta_zero_positive_branch] using theta_zero_positive_branch_add_tau_reindex τ u]
  rw [show ∏' n : ℕ, theta_zero_negative_branch τ (u + τ) n =
      (1 - (jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
        ∏' n : ℕ, theta_zero_negative_branch τ u n by
        simpa [theta_zero_negative_branch] using theta_zero_negative_branch_add_tau_split τ u hτ]
  change
    (∏' n : ℕ, theta_zero_positive_branch τ u (n + 1)) *
        ((1 - (jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
          ∏' n : ℕ, theta_zero_negative_branch τ u n) =
      (1 - (jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
        ((∏' n : ℕ, theta_zero_positive_branch τ u (n + 1)) *
          ∏' n : ℕ, theta_zero_negative_branch τ u n)
  ac_rfl

/-- Helper for Exercise II: before shifting by `τ`, the source product factors as the positive head
term times the same common positive tail and negative branch. -/
lemma theta_zero_product_unshifted_split (τ u : ℂ) (hτ : 0 < τ.im) :
    jacobi_theta_zero_product τ u =
      (1 - jacobi_q τ * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
        ((∏' n : ℕ,
            (1 - (jacobi_q τ) ^ (2 * (n + 1) + 1) *
              Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))) *
          ∏' n : ℕ,
            (1 - (jacobi_q τ) ^ (2 * n + 1) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u))) := by
  -- Route correction: split the positive branch on the opaque family first, and only then unfold
  -- the `n = 0` head factor into Cartan's common-tail normal form.
  rw [theta_zero_product_explicit_branch_split τ u hτ]
  rw [show ∏' n : ℕ, theta_zero_positive_branch τ u n =
      (1 - jacobi_q τ * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
        ∏' n : ℕ,
          (1 - (jacobi_q τ) ^ (2 * (n + 1) + 1) *
            Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) by
        simpa [theta_zero_positive_branch] using theta_zero_positive_branch_head_split τ u hτ]
  -- Now every factor is in the common positive-tail/negative-branch shape from the source proof.
  change
    ((1 - jacobi_q τ * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
        ∏' n : ℕ,
          (1 - (jacobi_q τ) ^ (2 * (n + 1) + 1) *
            Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))) *
        ∏' n : ℕ, theta_zero_negative_branch τ u n =
      (1 - jacobi_q τ * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) *
        ((∏' n : ℕ,
            (1 - (jacobi_q τ) ^ (2 * (n + 1) + 1) *
              Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))) *
          ∏' n : ℕ,
            (1 - (jacobi_q τ) ^ (2 * n + 1) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)))
  simp [theta_zero_negative_branch]
  ac_rfl

/-- Helper for Exercise II: translating the source infinite product by `τ` multiplies it by the
same quasi-periodicity scalar as `θ₀`. -/
theorem jacobi_theta_zero_product_add_tau (τ u : ℂ) (hτ : 0 < τ.im) :
    jacobi_theta_zero_product τ (u + τ) =
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
        jacobi_theta_zero_product τ u := by
  -- Compare the shifted and unshifted common-tail factorizations, then simplify only the scalar
  -- head factor by cancelling `q⁻¹ q` and `exp (-2π I u) * exp (2π I u)`.
  rw [theta_zero_product_shifted_split τ u hτ, theta_zero_product_unshifted_split τ u hτ]
  have hq_ne : jacobi_q τ ≠ 0 := by
    simpa [jacobi_q_eq_exp] using Complex.exp_ne_zero (Real.pi * Complex.I * τ)
  have hexp :
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
        Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u) = 1 := by
    calc
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)
        = Complex.exp
            ((-(2 * Real.pi : ℂ) * Complex.I * u) +
              ((2 * Real.pi : ℂ) * Complex.I * u)) := by
                rw [← Complex.exp_add]
      _ = 1 := by simp
  have hhead :
      1 - (jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) =
        (-(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
          (1 - jacobi_q τ * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u)) := by
    symm
    calc
      (-(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
          (1 - jacobi_q τ * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))
        =
          (-(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) -
            ((-(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
              (jacobi_q τ * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))) := by
                ring
      _ =
          (-(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) - (-1) := by
            congr 1
            calc
              (-(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
                  (jacobi_q τ * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))
                = -(((jacobi_q τ)⁻¹ * jacobi_q τ) *
                    (Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
                      Complex.exp ((2 * Real.pi : ℂ) * Complex.I * u))) := by
                        ring
              _ = -1 := by
                    rw [inv_mul_cancel₀ hq_ne, hexp]
                    norm_num
      _ = 1 - (jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) := by
            ring
  rw [hhead]
  ac_rfl

/-- Helper for Exercise II: the source proof's period pair is the lattice generated by `1` and
`τ`. -/
def theta_zero_period_pair (τ : ℂ) (hτ : 0 < τ.im) : PeriodPair :=
  ⟨1, τ, linear_independent_one_tau_of_im_pos τ hτ⟩

/-- Helper for Exercise II: the zeros of Cartan's `θ₀` are exactly the shifted lattice points
already identified in Exercise 3. -/
theorem jacobi_theta_zero_zero_iff
    (τ u : ℂ) (hτ : 0 < τ.im) :
    (θ₀[τ]) u = 0 ↔
      ∃ m n : ℤ, u = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ := by
  -- Reuse the earlier zero-locus theorem so the numerator and denominator zeros are now matched by
  -- the same lattice description.
  simpa using exercise_3_theta_zero_zero_iff τ u hτ

/-- Helper for Exercise II: the auxiliary theta function `θ₁` has a simple zero at the origin. -/
-- TODO: prove this by importing the Exercise 3 divisor package into this file's local API: show the
-- chosen boundary-regular period cell has total divisor mass `1`, then identify the unique support
-- point as the origin and read the divisor value back as analytic order.
theorem jacobi_theta_one_analyticOrderAt_zero_eq_one
    (τ : ℂ) (hτ : 0 < τ.im) :
    analyticOrderAt (θ₁[τ]) 0 = 1 := by
  classical
  let L : PeriodPair := theta_one_period_pair τ hτ
  obtain ⟨t, ht0, ht1, hzero_mem, hboundary, hlattice⟩ :=
    exists_theta_one_boundary_regular_slanted_periodParallelogram τ hτ
  let z₀ : ℂ := -(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ
  let P : Set ℂ := L.periodParallelogram z₀
  let d : ℂ → ℤ := MeromorphicOn.divisor (θ₁[τ]) P
  let s : Finset ℂ :=
    (divisor_support_finite_of_isCompact (K := P) (g := θ₁[τ])
      (by simpa [L, P, z₀] using L.isCompact_periodParallelogram z₀)).toFinset
  have hsum :
      Finset.sum s (fun z ↦ (d z : ℂ)) = 1 := by
    -- The source contour count gives total divisor mass `1` on the chosen boundary-regular cell.
    simpa [L, z₀, P, d, s] using
      theta_one_zero_mass_in_boundary_regular_periodParallelogram_eq_one τ hτ z₀
        (by simpa [L, z₀, P] using hboundary)
  have hzero_div_pos : 0 < d 0 := by
    -- The origin is a zero inside the cell, so its divisor contribution is positive.
    simpa [d, P] using
      (theta_one_divisor_pos_iff_eq_zero_on_set τ hτ (P := P)
        (by simpa [L, P, z₀] using hzero_mem)).2 (jacobi_theta_one_zero_at_zero τ)
  have hzero_mem_s : 0 ∈ s := by
    -- Positive divisor mass puts the origin into the finite divisor support.
    have hzero_ne : d 0 ≠ 0 := ne_of_gt hzero_div_pos
    simpa [s, d, Function.mem_support] using hzero_ne
  have hzero_unique :
      ∀ z ∈ P, (θ₁[τ]) z = 0 → z = 0 := by
    intro z hzP hz
    -- The boundary-regular slanted cell contains no zero of `θ₁` other than the origin.
    exact theta_one_zero_eq_zero_of_mem_boundary_regular_slanted_cell τ hτ
      (t := t)
      hzero_mem
      hboundary
      (by simpa [L, z₀, P] using hzP)
      hz
  have hother_zero :
      ∀ z ∈ s.erase 0, d z = 0 := by
    intro z hz
    have hzP : z ∈ P := by
      have hzsupport : z ∈ (MeromorphicOn.divisor (θ₁[τ]) P).support := by
        simpa [s, d] using Finset.mem_of_mem_erase hz
      exact (MeromorphicOn.divisor (θ₁[τ]) P).supportWithinDomain hzsupport
    by_cases hzzero : (θ₁[τ]) z = 0
    · have hz0 : z = 0 := hzero_unique z hzP hzzero
      exact False.elim ((Finset.mem_erase.mp hz).1 hz0)
    · have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
        -- Entire holomorphy of `θ₁` restricts to the cell owner `P`.
        exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
      have hanalyticP : AnalyticOnNhd ℂ (θ₁[τ]) P := by
        exact hanalytic_univ.mono (by intro w hw; simp)
      simpa [d] using divisor_eq_zero_of_analyticOnNhd_nonvanishing hanalyticP hzP hzzero
  have hsum_single : Finset.sum s (fun z ↦ (d z : ℂ)) = d 0 := by
    -- Every divisor term away from `0` vanishes, so the total mass is concentrated at the origin.
    have herase_zero : ∑ x ∈ s.erase 0, (d x : ℂ) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      exact_mod_cast hother_zero x hx
    rw [← Finset.sum_erase_add _ _ hzero_mem_s, herase_zero]
    simp
  have hdiv0_complex : (d 0 : ℂ) = 1 := by
    rw [← hsum_single]
    exact hsum
  have hdiv0 : d 0 = 1 := by
    exact_mod_cast hdiv0_complex
  have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
    -- The entire theta function is analytic at the origin.
    exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
  have hanalyticP : AnalyticOnNhd ℂ (θ₁[τ]) P := by
    exact hanalytic_univ.mono (by intro w hw; simp)
  have hanalytic0 : AnalyticAt ℂ (θ₁[τ]) 0 := hanalytic_univ 0 (by simp)
  have hmer_not_top : meromorphicOrderAt (θ₁[τ]) 0 ≠ ⊤ := by
    -- Finite analytic order rules out an infinite meromorphic order at the origin.
    rw [hanalytic0.meromorphicOrderAt_eq]
    simpa using theta_one_analyticOrderAt_ne_top τ 0 hτ
  have hmer_eq_one : meromorphicOrderAt (θ₁[τ]) 0 = (1 : WithTop ℤ) := by
    -- Read the divisor value back as the finite meromorphic order at the origin.
    calc
      meromorphicOrderAt (θ₁[τ]) 0
          = ↑((meromorphicOrderAt (θ₁[τ]) 0).untop₀) := by
              exact (WithTop.coe_untop₀_of_ne_top hmer_not_top).symm
      _ = (1 : WithTop ℤ) := by
            congr 1
            rw [← hanalyticP.meromorphicOn.divisor_apply (by simpa [P, L, z₀] using hzero_mem)]
            simpa [d] using hdiv0
  -- Compatibility of analytic and meromorphic order identifies the origin as a simple zero.
  rw [hanalytic0.meromorphicOrderAt_eq] at hmer_eq_one
  cases horder : analyticOrderAt (θ₁[τ]) 0 with
  | top =>
      exact (theta_one_analyticOrderAt_ne_top τ 0 hτ horder).elim
  | coe n =>
      have hn : (n : WithTop ℤ) = (1 : WithTop ℤ) := by
        simpa [horder] using hmer_eq_one
      exact_mod_cast hn

/-- Helper for Exercise II: the base zero of `θ₁` is simple, so its first derivative at the origin
is nonzero. -/
-- TODO: once the previous analytic-order lemma is proved, close this with the standard
-- simple-zero criterion `analyticOrderAt = 1 ↔ f = 0 ∧ deriv ≠ 0`.
theorem jacobi_theta_one_deriv_ne_zero_at_zero
    (τ : ℂ) (hτ : 0 < τ.im) :
    deriv (θ₁[τ]) 0 ≠ 0 := by
  have hanalytic0 : AnalyticAt ℂ (θ₁[τ]) 0 := by
    -- Entire differentiability of `θ₁` gives the analytic germ needed for the simple-zero test.
    exact ((exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
      0 (by simp)
  exact
    (AnalyticAt.analyticOrderAt_eq_one_iff_zero_and_deriv_ne_zero hanalytic0).1
      (jacobi_theta_one_analyticOrderAt_zero_eq_one τ hτ) |>.2

/-- Helper for Exercise II: transporting the simple zero of `θ₁` through the half-`τ` shift
formula shows that `θ₀` has nonvanishing derivative at `τ / 2`. -/
-- TODO: differentiate the half-`τ` shift identity `θ₀(u + τ / 2) = s(u) * θ₁(u)` at `u = 0`; the
-- product rule collapses because `θ₁(0) = 0`, leaving a nonzero scalar times `θ₁'(0)`.
theorem jacobi_theta_zero_deriv_ne_zero_at_half_tau
    (τ : ℂ) (hτ : 0 < τ.im) :
    deriv (θ₀[τ]) (τ / 2) ≠ 0 := by
  let a : ℂ → ℂ :=
    fun u ↦ Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u + τ / 4))
  have hshift :
      deriv (fun u ↦ (θ₀[τ]) (u + τ / 2)) 0 =
        Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ / 4)) *
          deriv (θ₁[τ]) 0 := by
    -- Differentiate the half-`τ` shift identity; the extra product-rule term vanishes at `0`
    -- because `θ₁(0) = 0`.
    rw [show (fun u ↦ (θ₀[τ]) (u + τ / 2)) =
        fun u ↦
          Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
            (θ₁[τ]) u by
          funext u
          exact exercise_3_theta_zero_add_half_tau τ u]
    change deriv (fun u ↦ a u * (θ₁[τ]) u) 0 =
      Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ / 4)) * deriv (θ₁[τ]) 0
    have hderiv_mul :
        deriv (fun u ↦ a u * (θ₁[τ]) u) 0 =
          deriv a 0 * (θ₁[τ]) 0 + a 0 * deriv (θ₁[τ]) 0 := by
      simpa using
        (deriv_mul
          (c := a)
          (d := θ₁[τ])
          (by
            change DifferentiableAt ℂ a 0
            dsimp [a]
            fun_prop)
          ((exercise_3_theta_one_differentiable τ hτ) 0))
    calc
      deriv (fun u ↦ a u * (θ₁[τ]) u) 0
          = deriv a 0 * (θ₁[τ]) 0 + a 0 * deriv (θ₁[τ]) 0 := hderiv_mul
      _ = a 0 * deriv (θ₁[τ]) 0 := by simp [jacobi_theta_one_zero_at_zero]
      _ = Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ / 4)) * deriv (θ₁[τ]) 0 := by
            simp [a]
  have hleft :
      deriv (fun u ↦ (θ₀[τ]) (u + τ / 2)) 0 = deriv (θ₀[τ]) (τ / 2) := by
    -- Translation in the source variable does not change derivatives.
    simpa using deriv_comp_add_const (f := θ₀[τ]) (a := τ / 2) (x := 0)
  have hscalar_ne :
      Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ / 4)) ≠ 0 := by
    -- The half-shift scalar is nonzero.
    exact mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _)
  -- A nonzero scalar times the already nonzero derivative of `θ₁` stays nonzero.
  rw [← hleft, hshift]
  exact mul_ne_zero hscalar_ne (jacobi_theta_one_deriv_ne_zero_at_zero τ hτ)

/-- Helper for Exercise II: because `θ₀` itself is `1`-periodic, its derivative is also
`1`-periodic. -/
theorem jacobi_theta_zero_deriv_add_one (τ u : ℂ) :
    deriv (θ₀[τ]) (u + 1) = deriv (θ₀[τ]) u := by
  have hcomp :
      deriv (fun z ↦ (θ₀[τ]) (z + 1)) u = deriv (θ₀[τ]) (u + 1) := by
    simpa using deriv_comp_add_const (f := θ₀[τ]) (a := 1) (x := u)
  have hperiod :
      (fun z ↦ (θ₀[τ]) (z + 1)) = θ₀[τ] := by
    -- Rewrite the translated germ by the already-proved period-`1` identity.
    funext z
    simpa using jacobi_theta_zero_add_one τ z
  -- Differentiate the translated function and then collapse it back to the original germ.
  calc
    deriv (θ₀[τ]) (u + 1) = deriv (fun z ↦ (θ₀[τ]) (z + 1)) u := by
      exact hcomp.symm
    _ = deriv (θ₀[τ]) u := by rw [hperiod]

/-- Helper for Exercise II: at a zero of `θ₀`, differentiating the `+τ` quasi-periodicity law
transports the derivative by the same nonzero scalar. -/
theorem jacobi_theta_zero_deriv_add_tau_of_zero
    (τ u : ℂ) (hτ : 0 < τ.im) (hu : (θ₀[τ]) u = 0) :
    deriv (θ₀[τ]) (u + τ) =
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
        deriv (θ₀[τ]) u := by
  let s : ℂ → ℂ := fun z ↦
    -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z)
  have hcomp :
      deriv (fun z ↦ (θ₀[τ]) (z + τ)) u = deriv (θ₀[τ]) (u + τ) := by
    simpa using deriv_comp_add_const (f := θ₀[τ]) (a := τ) (x := u)
  have hshift :
      (fun z ↦ (θ₀[τ]) (z + τ)) = fun z ↦ s z * (θ₀[τ]) z := by
    -- Freeze the scalar factor so the product rule sees a stable `s * θ₀` shape.
    funext z
    dsimp [s]
    simpa using jacobi_theta_zero_add_tau τ z
  have hderiv_mul :
      deriv (fun z ↦ s z * (θ₀[τ]) z) u =
        deriv s u * (θ₀[τ]) u + s u * deriv (θ₀[τ]) u := by
    -- Differentiate the product at `u`; the first summand will disappear because `θ₀ u = 0`.
    simpa using
      (deriv_mul
        (c := s)
        (d := θ₀[τ])
        (by
          change DifferentiableAt ℂ s u
          dsimp [s]
          fun_prop)
        ((exercise_3_theta_zero_differentiable τ hτ) u))
  calc
    deriv (θ₀[τ]) (u + τ) = deriv (fun z ↦ (θ₀[τ]) (z + τ)) u := by
      exact hcomp.symm
    _ = deriv (fun z ↦ s z * (θ₀[τ]) z) u := by rw [hshift]
    _ = deriv s u * (θ₀[τ]) u + s u * deriv (θ₀[τ]) u := hderiv_mul
    _ = s u * deriv (θ₀[τ]) u := by simp [hu]
    _ =
        -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          deriv (θ₀[τ]) u := by
            rfl

/-- Helper for Exercise II: the derivative of `θ₀` is unchanged by integer translation. -/
theorem jacobi_theta_zero_deriv_add_int
    (τ u : ℂ) :
    ∀ m : ℤ, deriv (θ₀[τ]) (u + m) = deriv (θ₀[τ]) u := by
  intro m
  refine Int.induction_on m ?_ ?_ ?_
  · simp
  · intro k hk
    calc
      deriv (θ₀[τ]) (u + ((k + 1 : ℤ) : ℂ))
          = deriv (θ₀[τ]) ((u + (k : ℤ)) + 1) := by
              simp [Int.cast_add, add_assoc, add_left_comm, add_comm]
      _ = deriv (θ₀[τ]) (u + (k : ℤ)) := jacobi_theta_zero_deriv_add_one τ (u + (k : ℤ))
      _ = deriv (θ₀[τ]) u := hk
  · intro k hk
    have hstep :
        deriv (θ₀[τ]) ((u + (((-((k : ℤ)) - 1 : ℤ) : ℂ))) + 1) =
          deriv (θ₀[τ]) (u + (((-((k : ℤ)) - 1 : ℤ) : ℂ))) :=
      jacobi_theta_zero_deriv_add_one τ (u + (((-((k : ℤ)) - 1 : ℤ) : ℂ)))
    calc
      deriv (θ₀[τ]) (u + (((-((k : ℤ)) - 1 : ℤ) : ℂ)))
          = deriv (θ₀[τ]) ((u + (((-((k : ℤ)) - 1 : ℤ) : ℂ))) + 1) := by
              exact hstep.symm
      _ = deriv (θ₀[τ]) u := by
            simpa [Int.cast_neg, Int.cast_natCast, Int.cast_sub, sub_eq_add_neg, add_assoc,
              add_left_comm, add_comm] using hk

/-- Helper for Exercise II: starting from the base point `τ / 2`, the derivative of `θ₀` stays
nonzero on every vertical translate `τ / 2 + nτ` of the zero lattice. -/
theorem jacobi_theta_zero_deriv_ne_zero_on_half_tau_vertical_lattice
    (τ : ℂ) (hτ : 0 < τ.im) :
    ∀ n : ℤ, deriv (θ₀[τ]) (τ / 2 + (n : ℂ) * τ) ≠ 0 := by
  intro n
  refine Int.induction_on n ?_ ?_ ?_
  · simpa [zero_mul, add_comm] using jacobi_theta_zero_deriv_ne_zero_at_half_tau τ hτ
  · intro j hj
    have hzero :
        (θ₀[τ]) (τ / 2 + ((j : ℤ) : ℂ) * τ) = 0 := by
      -- Every point on the vertical half-shift lattice is already in the known zero set of `θ₀`.
      exact
        (jacobi_theta_zero_zero_iff τ (τ / 2 + ((j : ℤ) : ℂ) * τ) hτ).2
          ⟨0, (j : ℤ), by ring⟩
    have hstep :=
      jacobi_theta_zero_deriv_add_tau_of_zero τ (τ / 2 + ((j : ℤ) : ℂ) * τ) hτ hzero
    have hscalar_ne :
        -(jacobi_q τ)⁻¹ *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (τ / 2 + ((j : ℤ) : ℂ) * τ)) ≠
          0 := by
      exact mul_ne_zero
        (neg_ne_zero.mpr (inv_ne_zero (by
          simpa [jacobi_q_eq_exp] using Complex.exp_ne_zero (Real.pi * Complex.I * τ)))
        )
        (Complex.exp_ne_zero _)
    have hrewrite :
        τ / 2 + ((j + 1 : ℤ) : ℂ) * τ = (τ / 2 + ((j : ℤ) : ℂ) * τ) + τ := by
      rw [Int.cast_add, add_mul, Int.cast_natCast, Int.cast_one]
      ring
    rw [hrewrite, hstep]
    exact mul_ne_zero hscalar_ne hj
  · intro j hj
    let u : ℂ := τ / 2 + (((-((j : ℤ)) - 1 : ℤ) : ℂ) * τ)
    have hzero : (θ₀[τ]) u = 0 := by
      -- The predecessor point on the same lattice is also a zero of `θ₀`.
      exact (jacobi_theta_zero_zero_iff τ u hτ).2 ⟨0, -((j : ℤ)) - 1, by
        dsimp [u]
        ring⟩
    have hstep := jacobi_theta_zero_deriv_add_tau_of_zero τ u hτ hzero
    have hnext_ne : deriv (θ₀[τ]) (u + τ) ≠ 0 := by
      -- Rewrite the translated predecessor point as the already-known induction point.
      simpa [u, Int.cast_neg, Int.cast_natCast, Int.cast_sub, sub_eq_add_neg, add_mul, add_assoc,
        add_left_comm, add_comm, one_mul] using hj
    -- If the predecessor derivative vanished, the translated derivative would vanish as well,
    -- contradicting the induction hypothesis.
    intro hderiv_zero
    apply hnext_ne
    rw [hstep, hderiv_zero]
    simp

/-- Helper for Exercise II: every zero of `θ₀` is simple, so its derivative never vanishes on the
zero lattice. -/
theorem jacobi_theta_zero_deriv_ne_zero_of_zero
    (τ u : ℂ) (hτ : 0 < τ.im) (hu : (θ₀[τ]) u = 0) :
    deriv (θ₀[τ]) u ≠ 0 := by
  rcases (jacobi_theta_zero_zero_iff τ u hτ).1 hu with ⟨m, n, rfl⟩
  have hvør :
      deriv (θ₀[τ]) ((((n : ℂ) + (1 / 2 : ℂ)) * τ)) ≠ 0 := by
    -- First remove the integer translation and reduce to the vertical half-shift lattice.
    simpa [div_eq_mul_inv, one_div, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm] using
      jacobi_theta_zero_deriv_ne_zero_on_half_tau_vertical_lattice τ hτ n
  have hperiod :
      deriv (θ₀[τ]) ((m : ℂ) + (((n : ℂ) + (1 / 2 : ℂ)) * τ)) =
        deriv (θ₀[τ]) ((((n : ℂ) + (1 / 2 : ℂ)) * τ)) := by
    -- The derivative is unchanged by the horizontal integer-period translation.
    simpa [add_assoc, add_left_comm, add_comm] using
      jacobi_theta_zero_deriv_add_int τ ((((n : ℂ) + (1 / 2 : ℂ)) * τ)) m
  rw [hperiod]
  exact hvør

/-- Helper for Exercise II: the raw quotient whose removable singularities must be resolved in the
final source-faithful argument. -/
def theta_zero_raw_quotient (τ : ℂ) : ℂ → ℂ :=
  fun u ↦ jacobi_theta_zero_product τ u / (θ₀[τ]) u

/-- Helper for Exercise II: every zero of `θ₀` is already a zero of the source product because the
two zero loci were identified earlier in the file. -/
theorem jacobi_theta_zero_product_zero_of_theta_zero_zero
    (τ u : ℂ) (hτ : 0 < τ.im) (hu : (θ₀[τ]) u = 0) :
    jacobi_theta_zero_product τ u = 0 := by
  -- Translate the denominator zero through the common shifted-lattice description.
  exact
    (exercise_ii_jacobi_theta_zero_product_zero_iff τ u hτ).2
      ((jacobi_theta_zero_zero_iff τ u hτ).1 hu)

/-- Helper for Exercise II: because the source product itself is `1`-periodic, its derivative is
also invariant under integer translation by `1`. -/
theorem jacobi_theta_zero_product_deriv_add_one (τ u : ℂ) :
    deriv (jacobi_theta_zero_product τ) (u + 1) =
      deriv (jacobi_theta_zero_product τ) u := by
  have hcomp :
      deriv (fun z ↦ jacobi_theta_zero_product τ (z + 1)) u =
        deriv (jacobi_theta_zero_product τ) (u + 1) := by
    simpa using deriv_comp_add_const (f := jacobi_theta_zero_product τ) (a := 1) (x := u)
  have hperiod : (fun z ↦ jacobi_theta_zero_product τ (z + 1)) = jacobi_theta_zero_product τ := by
    -- Rewrite the translated germ by the already-proved period-`1` law.
    funext z
    simpa using jacobi_theta_zero_product_add_one τ z
  -- Differentiate the translated function and collapse it back to the original germ.
  calc
    deriv (jacobi_theta_zero_product τ) (u + 1) =
        deriv (fun z ↦ jacobi_theta_zero_product τ (z + 1)) u := by
          exact hcomp.symm
    _ = deriv (jacobi_theta_zero_product τ) u := by rw [hperiod]

/-- Helper for Exercise II: at a zero of the source product, differentiating the `+τ`
quasi-periodicity law transports the derivative by the same nonzero scalar as for `θ₀`. -/
theorem jacobi_theta_zero_product_deriv_add_tau_of_zero
    (τ u : ℂ) (hτ : 0 < τ.im) (hu : jacobi_theta_zero_product τ u = 0) :
    deriv (jacobi_theta_zero_product τ) (u + τ) =
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
        deriv (jacobi_theta_zero_product τ) u := by
  let s : ℂ → ℂ := fun z ↦
    -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z)
  have hcomp :
      deriv (fun z ↦ jacobi_theta_zero_product τ (z + τ)) u =
        deriv (jacobi_theta_zero_product τ) (u + τ) := by
    simpa using deriv_comp_add_const (f := jacobi_theta_zero_product τ) (a := τ) (x := u)
  have hshift :
      (fun z ↦ jacobi_theta_zero_product τ (z + τ)) =
        fun z ↦ s z * jacobi_theta_zero_product τ z := by
    -- Freeze the common quasi-periodicity scalar before differentiating.
    funext z
    dsimp [s]
    simpa using jacobi_theta_zero_product_add_tau τ z hτ
  have hderiv_mul :
      deriv (fun z ↦ s z * jacobi_theta_zero_product τ z) u =
        deriv s u * jacobi_theta_zero_product τ u +
          s u * deriv (jacobi_theta_zero_product τ) u := by
    -- Differentiate the product; the first summand vanishes because the source product is zero at
    -- the center.
    simpa using
      (deriv_mul
        (c := s)
        (d := jacobi_theta_zero_product τ)
        (by
          change DifferentiableAt ℂ s u
          dsimp [s]
          fun_prop)
        ((exercise_ii_jacobi_theta_zero_product_differentiable τ hτ) u))
  calc
    deriv (jacobi_theta_zero_product τ) (u + τ) =
        deriv (fun z ↦ jacobi_theta_zero_product τ (z + τ)) u := by
          exact hcomp.symm
    _ = deriv (fun z ↦ s z * jacobi_theta_zero_product τ z) u := by rw [hshift]
    _ =
        deriv s u * jacobi_theta_zero_product τ u +
          s u * deriv (jacobi_theta_zero_product τ) u := hderiv_mul
    _ = s u * deriv (jacobi_theta_zero_product τ) u := by simp [hu]
    _ =
        -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          deriv (jacobi_theta_zero_product τ) u := by
            rfl

/-- Helper for Exercise II: away from a zero `u₀` of `θ₀`, the raw quotient can be rewritten as a
quotient of regularized divided differences based at `u₀`. -/
theorem theta_zero_raw_quotient_eventuallyEq_dslope_div
    (τ u₀ : ℂ) (hτ : 0 < τ.im) (hu₀ : (θ₀[τ]) u₀ = 0) :
    theta_zero_raw_quotient τ =ᶠ[nhdsWithin u₀ ({u₀}ᶜ)]
      fun z ↦ dslope (jacobi_theta_zero_product τ) u₀ z / dslope (θ₀[τ]) u₀ z := by
  have hnum₀ : jacobi_theta_zero_product τ u₀ = 0 :=
    jacobi_theta_zero_product_zero_of_theta_zero_zero τ u₀ hτ hu₀
  have hden_punct : ∀ᶠ z in nhdsWithin u₀ ({u₀}ᶜ), (θ₀[τ]) z ≠ 0 := by
    have hanalytic : AnalyticAt ℂ (θ₀[τ]) u₀ := by
      exact
        ((exercise_3_theta_zero_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          u₀ (by simp)
    rcases hanalytic.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
    · have hderiv_zero : deriv (θ₀[τ]) u₀ = 0 := by
        rw [Filter.EventuallyEq.deriv_eq hzero, deriv_const]
      exact False.elim ((jacobi_theta_zero_deriv_ne_zero_of_zero τ u₀ hτ hu₀) hderiv_zero)
    · exact hnonzero
  -- On the punctured neighborhood, isolate the common factor `z - u₀` in numerator and
  -- denominator and cancel it.
  filter_upwards [hden_punct, self_mem_nhdsWithin] with z hzden hz_ne
  have hz_ne' : z ≠ u₀ := by simpa using hz_ne
  have hnum :
      jacobi_theta_zero_product τ z =
        (z - u₀) * dslope (jacobi_theta_zero_product τ) u₀ z := by
    simpa [smul_eq_mul] using
      (sub_smul_dslope_of_zero (f := jacobi_theta_zero_product τ) hnum₀ z).symm
  have hden :
      (θ₀[τ]) z = (z - u₀) * dslope (θ₀[τ]) u₀ z := by
    simpa [smul_eq_mul] using
      (sub_smul_dslope_of_zero (f := θ₀[τ]) hu₀ z).symm
  calc
    theta_zero_raw_quotient τ z =
        ((z - u₀) * dslope (jacobi_theta_zero_product τ) u₀ z) /
          ((z - u₀) * dslope (θ₀[τ]) u₀ z) := by
            simp [theta_zero_raw_quotient, hnum, hden]
    _ = dslope (jacobi_theta_zero_product τ) u₀ z / dslope (θ₀[τ]) u₀ z := by
          field_simp [hzden, sub_ne_zero.mpr hz_ne']

/-- Helper for Exercise II: the globally defined removable extension of the raw quotient uses the
derivative ratio exactly at the zero lattice of `θ₀`. -/
def theta_zero_extended_quotient (τ : ℂ) : ℂ → ℂ :=
  fun u ↦
    if hu : (θ₀[τ]) u = 0 then
      deriv (jacobi_theta_zero_product τ) u / deriv (θ₀[τ]) u
    else
      theta_zero_raw_quotient τ u

/-- Helper for Exercise II: at a zero `u₀` of `θ₀`, the global extension agrees on a full
neighborhood with the quotient of the two `dslope` functions based at `u₀`. -/
theorem theta_zero_extended_quotient_eventuallyEq_dslope_div
    (τ u₀ : ℂ) (hτ : 0 < τ.im) (hu₀ : (θ₀[τ]) u₀ = 0) :
    theta_zero_extended_quotient τ =ᶠ[nhds u₀]
      fun z ↦ dslope (jacobi_theta_zero_product τ) u₀ z / dslope (θ₀[τ]) u₀ z := by
  have hraw :
      theta_zero_raw_quotient τ =ᶠ[nhdsWithin u₀ ({u₀}ᶜ)]
        fun z ↦ dslope (jacobi_theta_zero_product τ) u₀ z / dslope (θ₀[τ]) u₀ z :=
    theta_zero_raw_quotient_eventuallyEq_dslope_div τ u₀ hτ hu₀
  have hden_punct : ∀ᶠ z in nhdsWithin u₀ ({u₀}ᶜ), (θ₀[τ]) z ≠ 0 := by
    have hanalytic : AnalyticAt ℂ (θ₀[τ]) u₀ := by
      exact
        ((exercise_3_theta_zero_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
          u₀ (by simp)
    rcases hanalytic.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
    · have hderiv_zero : deriv (θ₀[τ]) u₀ = 0 := by
        rw [Filter.EventuallyEq.deriv_eq hzero, deriv_const]
      exact False.elim ((jacobi_theta_zero_deriv_ne_zero_of_zero τ u₀ hτ hu₀) hderiv_zero)
    · exact hnonzero
  have hdslope_den_nonzero : ∀ᶠ z in nhds u₀, dslope (θ₀[τ]) u₀ z ≠ 0 := by
    have hcont : ContinuousAt (dslope (θ₀[τ]) u₀) u₀ :=
      (continuousAt_dslope_same).2 ((exercise_3_theta_zero_differentiable τ hτ) u₀)
    have hcenter : dslope (θ₀[τ]) u₀ u₀ ≠ 0 := by
      simpa [dslope_same] using jacobi_theta_zero_deriv_ne_zero_of_zero τ u₀ hτ hu₀
    exact hcont (isOpen_ne.mem_nhds hcenter)
  rcases Metric.mem_nhds_iff.mp hdslope_den_nonzero with ⟨δ₁, hδ₁_pos, hδ₁⟩
  rcases Metric.mem_nhdsWithin_iff.mp hden_punct with ⟨δ₂, hδ₂_pos, hδ₂⟩
  rcases Metric.mem_nhdsWithin_iff.mp hraw with ⟨δ₃, hδ₃_pos, hδ₃⟩
  let δ : ℝ := min δ₁ (min δ₂ δ₃)
  have hδ_pos : 0 < δ := by
    refine lt_min hδ₁_pos ?_
    exact lt_min hδ₂_pos hδ₃_pos
  refine Filter.mem_of_superset (Metric.ball_mem_nhds u₀ hδ_pos) ?_
  intro z hz
  by_cases hz₀ : z = u₀
  · -- At the center, the extension was defined to be the derivative ratio, which is exactly the
    -- `dslope` quotient by `dslope_same`.
    subst hz₀
    simp [theta_zero_extended_quotient, hu₀, dslope_same]
  · have hz₁ : z ∈ Metric.ball u₀ δ₁ :=
      (Metric.ball_subset_ball (min_le_left _ _)) hz
    have hz₂ : z ∈ Metric.ball u₀ δ₂ :=
      (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _))) hz
    have hz₃ : z ∈ Metric.ball u₀ δ₃ :=
      (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))) hz
    have hdenz : (θ₀[τ]) z ≠ 0 := hδ₂ ⟨hz₂, hz₀⟩
    have hrawz :
        theta_zero_raw_quotient τ z =
          dslope (jacobi_theta_zero_product τ) u₀ z / dslope (θ₀[τ]) u₀ z := hδ₃ ⟨hz₃, hz₀⟩
    -- Away from the center, the punctured-neighborhood identity applies and the extension chooses
    -- the raw quotient branch because the denominator is already nonzero there.
    simp [theta_zero_extended_quotient, hdenz, hrawz]

/-- Helper for Exercise II: off the zero lattice of `θ₀`, the global extension agrees locally with
the raw quotient. -/
theorem theta_zero_extended_quotient_eventuallyEq_raw_of_nonzero
    (τ u : ℂ) (hτ : 0 < τ.im) (hu : (θ₀[τ]) u ≠ 0) :
    theta_zero_extended_quotient τ =ᶠ[nhds u] theta_zero_raw_quotient τ := by
  have hcont : ContinuousAt (θ₀[τ]) u := ((exercise_3_theta_zero_differentiable τ hτ) u).continuousAt
  have hnonzero : ∀ᶠ z in nhds u, (θ₀[τ]) z ≠ 0 := hcont (isOpen_ne.mem_nhds hu)
  -- On a neighborhood where the denominator never vanishes, the extension picks the raw quotient
  -- branch by definition.
  filter_upwards [hnonzero] with z hz
  simp [theta_zero_extended_quotient, hz]

/-- Helper for Exercise II: before resolving the common zeros, the raw quotient is already
`1`-periodic. -/
theorem theta_zero_raw_quotient_add_one (τ u : ℂ) :
    theta_zero_raw_quotient τ (u + 1) = theta_zero_raw_quotient τ u := by
  -- Both the numerator and denominator are `1`-periodic, so the pointwise quotient is unchanged.
  simp [theta_zero_raw_quotient, jacobi_theta_zero_product_add_one, jacobi_theta_zero_add_one]

/-- Helper for Exercise II: the numerator and denominator acquire the same scalar under `u ↦ u + τ`,
so their quotient is already `τ`-periodic before removable singularities are resolved. -/
theorem theta_zero_raw_quotient_add_tau (τ u : ℂ) (hτ : 0 < τ.im) :
    theta_zero_raw_quotient τ (u + τ) = theta_zero_raw_quotient τ u := by
  let s : ℂ := -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)
  have hs_ne : s ≠ 0 := by
    -- The common quasi-periodicity scalar never vanishes.
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    exact neg_ne_zero.mpr (inv_ne_zero (by simpa [jacobi_q_eq_exp] using Complex.exp_ne_zero (Real.pi * Complex.I * τ)))
  -- Rewrite both numerator and denominator by their `+τ` laws, then cancel the shared scalar.
  rw [theta_zero_raw_quotient, theta_zero_raw_quotient,
    jacobi_theta_zero_product_add_tau τ u hτ, jacobi_theta_zero_add_tau τ u]
  simpa [s, mul_assoc, mul_left_comm, mul_comm] using
    (mul_div_mul_left (jacobi_theta_zero_product τ u) ((θ₀[τ]) u) hs_ne)

/-- Helper for Exercise II: after matching the `+1` and `+τ` quasi-periodicity factors of the
numerator and denominator, the raw quotient is periodic for the full lattice generated by `1`
and `τ`. -/
theorem theta_zero_raw_quotient_has_period_lattice (τ : ℂ) (hτ : 0 < τ.im) :
    HasPeriodLattice (theta_zero_period_pair τ hτ) (theta_zero_raw_quotient τ) := by
  -- Package the verified `+1` and `+τ` periodicities through the canonical period-pair API.
  rw [hasPeriodLattice_iff_periodic_generators]
  constructor
  · intro u
    simpa [theta_zero_period_pair] using theta_zero_raw_quotient_add_one τ u
  · intro u
    simpa [theta_zero_period_pair] using theta_zero_raw_quotient_add_tau τ u hτ

/-- Helper for Exercise II: the removable extension is holomorphic at every point of the plane. -/
theorem theta_zero_extended_quotient_differentiable
    (τ : ℂ) (hτ : 0 < τ.im) :
    Differentiable ℂ (theta_zero_extended_quotient τ) := by
  intro u
  by_cases hu : (θ₀[τ]) u = 0
  · let g : ℂ → ℂ := fun z ↦
      dslope (jacobi_theta_zero_product τ) u z / dslope (θ₀[τ]) u z
    have hnum_ds :
        DifferentiableAt ℂ (dslope (jacobi_theta_zero_product τ) u) u := by
      have hdiffOn :
          DifferentiableOn ℂ (dslope (jacobi_theta_zero_product τ) u) Set.univ := by
        simpa using
          (Complex.differentiableOn_dslope (s := Set.univ) (c := u) (by simp)).2
            (exercise_ii_jacobi_theta_zero_product_differentiable τ hτ).differentiableOn
      simpa [differentiableWithinAt_univ] using hdiffOn u (by simp)
    have hden_ds :
        DifferentiableAt ℂ (dslope (θ₀[τ]) u) u := by
      have hdiffOn :
          DifferentiableOn ℂ (dslope (θ₀[τ]) u) Set.univ := by
        simpa using
          (Complex.differentiableOn_dslope (s := Set.univ) (c := u) (by simp)).2
            (exercise_3_theta_zero_differentiable τ hτ).differentiableOn
      simpa [differentiableWithinAt_univ] using hdiffOn u (by simp)
    have hden_ne :
        dslope (θ₀[τ]) u u ≠ 0 := by
      simpa [dslope_same] using jacobi_theta_zero_deriv_ne_zero_of_zero τ u hτ hu
    have hg : DifferentiableAt ℂ g u := by
      dsimp [g]
      exact hnum_ds.div hden_ds hden_ne
    -- At a zero, the extension agrees near the center with the regular `dslope` quotient model.
    exact
      hg.congr_of_eventuallyEq
        (theta_zero_extended_quotient_eventuallyEq_dslope_div τ u hτ hu)
  · have hraw : DifferentiableAt ℂ (theta_zero_raw_quotient τ) u := by
      simpa [theta_zero_raw_quotient] using
        (((exercise_ii_jacobi_theta_zero_product_differentiable τ hτ) u).div
          ((exercise_3_theta_zero_differentiable τ hτ) u)
          hu)
    -- Away from the zero lattice, the extension is locally just the ordinary quotient.
    exact
      hraw.congr_of_eventuallyEq
        (theta_zero_extended_quotient_eventuallyEq_raw_of_nonzero τ u hτ hu)

/-- Helper for Exercise II: the removable extension inherits the integer period `1`. -/
theorem theta_zero_extended_quotient_add_one (τ u : ℂ) :
    theta_zero_extended_quotient τ (u + 1) = theta_zero_extended_quotient τ u := by
  by_cases hu : (θ₀[τ]) u = 0
  · have hu₁ : (θ₀[τ]) (u + 1) = 0 := by
      simpa [jacobi_theta_zero_add_one τ u] using hu
    -- On the zero lattice, both numerator and denominator derivatives are `1`-periodic.
    simp [theta_zero_extended_quotient, hu, hu₁, jacobi_theta_zero_product_deriv_add_one,
      jacobi_theta_zero_deriv_add_one]
  · have hu₁ : (θ₀[τ]) (u + 1) ≠ 0 := by
      intro h
      exact hu (by simpa [jacobi_theta_zero_add_one τ u] using h)
    -- Off the zero lattice, the extension reduces to the already-periodic raw quotient.
    simp [theta_zero_extended_quotient, hu, hu₁, theta_zero_raw_quotient_add_one]

/-- Helper for Exercise II: the removable extension inherits the second generator `τ` of the
period lattice. -/
theorem theta_zero_extended_quotient_add_tau (τ u : ℂ) (hτ : 0 < τ.im) :
    theta_zero_extended_quotient τ (u + τ) = theta_zero_extended_quotient τ u := by
  let s : ℂ := -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)
  have hs_ne : s ≠ 0 := by
    -- The common quasi-periodicity scalar never vanishes.
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    exact
      neg_ne_zero.mpr <|
        inv_ne_zero (by simpa [jacobi_q_eq_exp] using Complex.exp_ne_zero (Real.pi * Complex.I * τ))
  by_cases hu : (θ₀[τ]) u = 0
  · have huτ : (θ₀[τ]) (u + τ) = 0 := by
      simpa [s, hu] using jacobi_theta_zero_add_tau τ u
    have hnum : jacobi_theta_zero_product τ u = 0 :=
      jacobi_theta_zero_product_zero_of_theta_zero_zero τ u hτ hu
    -- On the zero lattice, both derivative ratios pick up the same nonzero scalar under `+τ`.
    rw [theta_zero_extended_quotient, theta_zero_extended_quotient, huτ, hu,
      jacobi_theta_zero_product_deriv_add_tau_of_zero τ u hτ hnum,
      jacobi_theta_zero_deriv_add_tau_of_zero τ u hτ hu]
    simpa [s] using
      (mul_div_mul_left
        (deriv (jacobi_theta_zero_product τ) u)
        (deriv (θ₀[τ]) u)
        hs_ne)
  · have huτ : (θ₀[τ]) (u + τ) ≠ 0 := by
      intro hzero
      have hmul : s * (θ₀[τ]) u = 0 := by
        simpa [s, hzero] using jacobi_theta_zero_add_tau τ u
      exact hu ((mul_eq_zero.mp hmul).resolve_left hs_ne)
    -- Off the zero lattice, the raw quotient already has the required `+τ` period.
    simp [theta_zero_extended_quotient, hu, huτ, theta_zero_raw_quotient_add_tau, hτ]

/-- Helper for Exercise II: the removable extension is periodic for the full lattice generated by
`1` and `τ`. -/
theorem theta_zero_extended_quotient_has_period_lattice
    (τ : ℂ) (hτ : 0 < τ.im) :
    HasPeriodLattice (theta_zero_period_pair τ hτ) (theta_zero_extended_quotient τ) := by
  -- Package the two generator periodicities through the period-pair API.
  rw [hasPeriodLattice_iff_periodic_generators]
  constructor
  · intro u
    simpa [theta_zero_period_pair] using theta_zero_extended_quotient_add_one τ u
  · intro u
    simpa [theta_zero_period_pair] using theta_zero_extended_quotient_add_tau τ u hτ

/-- Exercise II (3): when `Im τ > 0`, the source infinite product is a constant multiple of the
canonical Jacobi theta function evaluated at the half-shifted variable `u + 1 / 2`, i.e. of
Cartan's `θ₀`. -/
theorem exercise_ii_jacobi_theta_zero_product_eq_const_mul_jacobiTheta₂_shift
    (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ c : ℂ, ∀ u : ℂ,
      jacobi_theta_zero_product τ u = c * jacobiTheta₂ (u + (1 / 2 : ℂ)) τ := by
  -- Route correction: apply the period-lattice constancy corollary to the holomorphic removable
  -- extension of the source quotient, then split on whether `θ₀` vanishes at the evaluation
  -- point.
  obtain ⟨c, hc⟩ :=
    differentiable_eq_const_of_has_period_lattice
      (theta_zero_period_pair τ hτ)
      (theta_zero_extended_quotient_differentiable τ hτ)
      (theta_zero_extended_quotient_has_period_lattice τ hτ)
  refine ⟨c, ?_⟩
  intro u
  by_cases hu : (θ₀[τ]) u = 0
  · have hnum : jacobi_theta_zero_product τ u = 0 :=
      jacobi_theta_zero_product_zero_of_theta_zero_zero τ u hτ hu
    have htheta : jacobiTheta₂ (u + (1 / 2 : ℂ)) τ = 0 := by
      simpa [jacobi_theta_zero_apply] using hu
    -- At zeros of `θ₀`, both sides vanish.
    rw [hnum, htheta]
    simp
  · have hquot :
      jacobi_theta_zero_product τ u / (θ₀[τ]) u = c := by
      simpa [theta_zero_extended_quotient, hu, theta_zero_raw_quotient] using hc u
    have hprod :
        jacobi_theta_zero_product τ u = c * (θ₀[τ]) u := (div_eq_iff hu).1 hquot
    -- Away from the zero lattice, multiply the constant quotient identity back by `θ₀`.
    simpa [jacobi_theta_zero_apply] using hprod

/-- Exercise II (3), restated in Cartan's `θ₀` notation via the half-shift bridge. -/
theorem exercise_ii_jacobi_theta_zero_product_eq_const_mul_theta_zero
    (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ c : ℂ, ∀ u : ℂ, jacobi_theta_zero_product τ u = c * (θ₀[τ]) u := by
  -- Rewrite the already-established shifted-`jacobiTheta₂` formula through Cartan's `θ₀` bridge.
  rcases exercise_ii_jacobi_theta_zero_product_eq_const_mul_jacobiTheta₂_shift τ hτ with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro u
  rw [hc u, jacobi_theta_zero_apply]
