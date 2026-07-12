import Mathlib
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import DifferentialForms_Cartan_1970.III.section11.«0008_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section12.«0008_Example_III_6_extra_3»
import DifferentialForms_Cartan_1970.III.section12.«0033_Exercise_20».Index

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool `lean_leansearch` was unavailable in this environment.
-- The notation in this file was verified locally by `lake lean`.

open MeasureTheory
open InnerProductSpace
open Filter
open FourierTransform
open scoped Real Topology

noncomputable section

/-- Exercise 20 (1): for `a, b > 0` and `n ≥ 1`,
evaluate `∫_0^∞ (a + b x^2)^{-n} dx` by residues. -/
theorem integral_inv_quadratic_pow
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) :
    ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
      = Real.pi * (Nat.centralBinom (n - 1) : ℝ) /
          ((2 : ℝ) ^ (2 * n - 1) * a ^ (n - 1) * Real.sqrt (a * b)) := by
  have hscale := exercise20_integral_inv_quadratic_pow_scaling a b n ha hb
  let m : ℕ := n - 1
  have hm : n = m + 1 := by
    -- Since `n > 0`, writing `n = (n - 1) + 1` keeps the final coefficient stable.
    omega
  have hsqrt_div : Real.sqrt (a / b) = Real.sqrt a / Real.sqrt b := by
    rw [Real.sqrt_div ha.le b]
  have hsqrt_mul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul ha.le b]
  have hsqrta_sq : Real.sqrt a * Real.sqrt a = a := by
    nlinarith [Real.sq_sqrt ha.le]
  have hsqrta_ne : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.2 ha
  have hsqrtb_ne : Real.sqrt b ≠ 0 := Real.sqrt_ne_zero'.2 hb
  have hcoeff :
      Real.sqrt (a / b) / a ^ n = 1 / (a ^ (n - 1) * Real.sqrt (a * b)) := by
    -- The outer scaling coefficient matches the target denominator after one square-root rewrite.
    rw [hsqrt_div, hsqrt_mul, hm, pow_succ]
    field_simp [hsqrta_ne, hsqrtb_ne, hsqrta_sq]
    simp [pow_two, hsqrta_sq, mul_comm]
  -- Route correction: the remaining blocker is now exactly the normalized integral
  -- `∫_0^∞ (1 + y²)^(-n) dy`; the scaling and prefactor simplification are complete.
  have hnorm :
      ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume
        = Real.pi * (Nat.centralBinom (n - 1) : ℝ) / (2 : ℝ) ^ (2 * n - 1) := by
    -- Close the normalized kernel by the tangent substitution and the even-power cosine integral.
    rw [exercise20_integral_inv_one_add_sq_pow_eq_cos_even_power n hn]
    have hexp : 2 * (n - 1) + 1 = 2 * n - 1 := by
      omega
    rw [← hexp]
    exact exercise20_integral_cos_even_power_centralBinom (n - 1)
  calc
    ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
        = (Real.sqrt (a / b) / a ^ n) *
            ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume := hscale
    _ = (Real.sqrt (a / b) / a ^ n) *
          (Real.pi * (Nat.centralBinom (n - 1) : ℝ) / (2 : ℝ) ^ (2 * n - 1)) := by
            rw [hnorm]
    _ = (1 / (a ^ (n - 1) * Real.sqrt (a * b))) *
          (Real.pi * (Nat.centralBinom (n - 1) : ℝ) / (2 : ℝ) ^ (2 * n - 1)) := by
            rw [hcoeff]
    _ = Real.pi * (Nat.centralBinom (n - 1) : ℝ) /
          ((2 : ℝ) ^ (2 * n - 1) * a ^ (n - 1) * Real.sqrt (a * b)) := by
            rw [hsqrt_mul]
            field_simp [ha.ne', hsqrta_ne, hsqrtb_ne]

/-- Exercise 20 (2): for real `a` and `b`,
evaluate `∫_0^∞ (cos (2 a x) - cos (2 b x)) / x^2 dx` by residues. -/
theorem integral_cos_sub_cos_div_sq
    (a b : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), (Real.cos (2 * a * x) - Real.cos (2 * b * x)) / x ^ 2 ∂volume
      = Real.pi * (|b| - |a|) := by
  have hrewrite :
      ∫ x in Set.Ioi (0 : ℝ), (Real.cos (2 * a * x) - Real.cos (2 * b * x)) / x ^ 2 ∂volume
        =
          ∫ x in Set.Ioi (0 : ℝ),
            ((1 - Real.cos (2 * b * x)) - (1 - Real.cos (2 * a * x))) / x ^ 2 ∂volume := by
    -- This isolates the common kernel `J c = ∫ (1 - cos (2 c x)) / x²`.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact exercise20_cos_sub_cos_div_sq_eq_kernel_difference a b x
  rw [hrewrite]
  have hsplit :
      ∫ x in Set.Ioi (0 : ℝ),
          ((1 - Real.cos (2 * b * x)) - (1 - Real.cos (2 * a * x))) / x ^ 2 ∂volume
        =
          ∫ x in Set.Ioi (0 : ℝ),
            (1 - Real.cos (2 * b * x)) / x ^ 2 - (1 - Real.cos (2 * a * x)) / x ^ 2 ∂volume := by
    -- Split the common denominator before using the two kernel evaluations.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp [hx0]
  rw [hsplit]
  -- Evaluate the rewritten difference as `J b - J a` using the shared kernel theorem.
  rw [integral_sub (exercise20_integrable_one_sub_cos_two_mul_div_sq b)
    (exercise20_integrable_one_sub_cos_two_mul_div_sq a)]
  rw [exercise20_integral_one_sub_cos_two_mul_div_sq,
    exercise20_integral_one_sub_cos_two_mul_div_sq]
  ring

/-- Helper for Cartan section12 0033_Exercise_20: the Fourier transform of
`x ↦ exp (-(2 π a) |x|)` is the rational kernel `a / (π (a² + w²))`. -/
lemma exercise20_fourierExpAbsKernel
    (a w : ℝ) (ha : 0 < a) :
    𝓕 (fun x : ℝ ↦ Complex.exp (-((2 * Real.pi * a : ℝ) : ℂ) * |x|)) w =
      (a / (Real.pi * (a ^ 2 + w ^ 2)) : ℂ) := by
  let U : ℂ := ((2 * Real.pi * a : ℝ) : ℂ)
  let V : ℂ := ((2 * Real.pi * w : ℝ) : ℂ)
  let integrand : ℝ → ℂ := fun x : ℝ ↦
    Complex.exp (↑(-2 * Real.pi * x * w) * Complex.I) *
      Complex.exp (-U * |x|)
  have hleftPoint :
      Set.EqOn integrand (fun x : ℝ ↦ Complex.exp ((U - V * Complex.I) * x)) (Set.Iic 0) := by
    intro x hx
    dsimp [integrand, U, V]
    have hx' : |x| = -x := by
      exact abs_of_nonpos (by simpa using hx)
    rw [hx', neg_mul, ← Complex.exp_add]
    apply congrArg Complex.exp
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp
      ring_nf
  have hrightPoint :
      Set.EqOn integrand (fun x : ℝ ↦ Complex.exp (-(U + V * Complex.I) * x)) (Set.Ioi 0) := by
    intro x hx
    dsimp [integrand, U, V]
    have hx' : |x| = x := by
      exact abs_of_pos (by simpa using hx)
    rw [hx', ← Complex.exp_add]
    apply congrArg Complex.exp
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp
      ring_nf
  have hleftRe : 0 < (U - V * Complex.I).re := by
    have h : 0 < 2 * Real.pi * a := by
      positivity
    simpa [U, V] using h
  have hrightRe : (-(U + V * Complex.I)).re < 0 := by
    have h : -(2 * Real.pi * a) < 0 := by
      nlinarith [Real.pi_pos, ha]
    simpa [U, V] using h
  have hleftInt : IntegrableOn integrand (Set.Iic 0) := by
    exact (integrableOn_congr_fun hleftPoint measurableSet_Iic).2
      (integrableOn_exp_mul_complex_Iic (a := U - V * Complex.I) hleftRe 0)
  have hrightInt : IntegrableOn integrand (Set.Ioi 0) := by
    exact (integrableOn_congr_fun hrightPoint measurableSet_Ioi).2
      (integrableOn_exp_mul_complex_Ioi (a := -(U + V * Complex.I)) hrightRe 0)
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_Iic_add_Ioi hleftInt hrightInt]
  have hleftEq :
      ∫ x : ℝ in Set.Iic 0, integrand x ∂volume = 1 / (U - V * Complex.I) := by
    calc
      ∫ x : ℝ in Set.Iic 0, integrand x ∂volume
          = ∫ x : ℝ in Set.Iic 0, Complex.exp ((U - V * Complex.I) * x) ∂volume := by
              exact setIntegral_congr_fun measurableSet_Iic hleftPoint
      _ = 1 / (U - V * Complex.I) := by
            simpa [div_eq_mul_inv] using
              integral_exp_mul_complex_Iic (a := U - V * Complex.I) hleftRe 0
  have hrightEq :
      ∫ x : ℝ in Set.Ioi 0, integrand x ∂volume = 1 / (U + V * Complex.I) := by
    calc
      ∫ x : ℝ in Set.Ioi 0, integrand x ∂volume
          = ∫ x : ℝ in Set.Ioi 0, Complex.exp (-(U + V * Complex.I) * x) ∂volume := by
              exact setIntegral_congr_fun measurableSet_Ioi hrightPoint
      _ = -(1 / (-(U + V * Complex.I))) := by
            simpa [div_eq_mul_inv] using
              integral_exp_mul_complex_Ioi (a := -(U + V * Complex.I)) hrightRe 0
      _ = 1 / (U + V * Complex.I) := by
            field_simp
  rw [hleftEq, hrightEq]
  have hleft_ne : U - V * Complex.I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp [U, V, ha.ne'] at hre
  have hright_ne : U + V * Complex.I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp [U, V, ha.ne'] at hre
  have hsum :
      1 / (U - V * Complex.I) + 1 / (U + V * Complex.I) =
        (2 * U) / (U ^ 2 + V ^ 2) := by
    calc
      1 / (U - V * Complex.I) + 1 / (U + V * Complex.I)
          = ((U + V * Complex.I) + (U - V * Complex.I)) /
              ((U - V * Complex.I) * (U + V * Complex.I)) := by
                field_simp [hleft_ne, hright_ne]
      _ = (2 * U) / ((U - V * Complex.I) * (U + V * Complex.I)) := by
            ring
      _ = (2 * U) / (U ^ 2 + V ^ 2) := by
            congr 1
            ring_nf
            simp [Complex.I_sq]
  rw [hsum]
  have hUV : U ^ 2 + V ^ 2 = ((4 * Real.pi ^ 2 * (a ^ 2 + w ^ 2) : ℝ) : ℂ) := by
    simp [U, V, pow_two]
    ring
  rw [hUV]
  have hreal :
    (4 * Real.pi * a) / (4 * Real.pi ^ 2 * (a ^ 2 + w ^ 2)) =
        a / (Real.pi * (a ^ 2 + w ^ 2)) := by
    field_simp [Real.pi_ne_zero]
  calc
    (2 * U) / (((4 * Real.pi ^ 2 * (a ^ 2 + w ^ 2) : ℝ) : ℂ))
        = ((4 * Real.pi * a) / (4 * Real.pi ^ 2 * (a ^ 2 + w ^ 2)) : ℂ) := by
            apply Complex.ext
            · simp [U]
              ring_nf
            · simp [U]
              ring_nf
    _ = (a / (Real.pi * (a ^ 2 + w ^ 2)) : ℂ) := by
          exact_mod_cast hreal

/-- Helper for Cartan section12 0033_Exercise_20: Fourier inversion converts the rational kernel
`(x² + a²)⁻¹` into the exponential profile `exp (-a |s|)`. -/
lemma exercise20_integral_univ_exp_mul_inv_quadratic_abs_freq
    (a s : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x)) =
      (Real.pi * Real.exp (-a * |s|) / a : ℂ) := by
  let g : ℝ → ℂ := fun x : ℝ ↦ Complex.exp (-((2 * Real.pi * a : ℝ) : ℂ) * |x|)
  have hg_cont : Continuous g := by
    dsimp [g]
    fun_prop
  have hg_iic : IntegrableOn g (Set.Iic 0) := by
    have hEq :
        Set.EqOn g (fun x : ℝ ↦ Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * x)) (Set.Iic 0) := by
      intro x hx
      dsimp [g]
      have hx' : |x| = -x := by
        exact abs_of_nonpos (by simpa using hx)
      simp [hx']
    exact (integrableOn_congr_fun hEq measurableSet_Iic).2
      (integrableOn_exp_mul_complex_Iic (a := ((2 * Real.pi * a : ℝ) : ℂ))
        (by
          have h : 0 < 2 * Real.pi * a := by
            positivity
          simpa using h) 0)
  have hg_ioi : IntegrableOn g (Set.Ioi 0) := by
    have hEq :
        Set.EqOn g (fun x : ℝ ↦ Complex.exp (-(((2 * Real.pi * a : ℝ) : ℂ)) * x)) (Set.Ioi 0) := by
      intro x hx
      dsimp [g]
      have hx' : |x| = x := by
        exact abs_of_pos (by simpa using hx)
      simp [hx']
    have hneg : (-(((2 * Real.pi * a : ℝ) : ℂ))).re < 0 := by
      have h : -(2 * Real.pi * a) < 0 := by
        nlinarith [Real.pi_pos, ha]
      simpa using h
    exact (integrableOn_congr_fun hEq measurableSet_Ioi).2
      (integrableOn_exp_mul_complex_Ioi (a := -(((2 * Real.pi * a : ℝ) : ℂ))) hneg 0)
  have hg_int : Integrable g := by
    rw [← integrableOn_univ]
    convert hg_iic.union hg_ioi using 1
    ext x
    simp
  have hbaseC : Integrable (fun x : ℝ ↦ (((x ^ 2 + a ^ 2)⁻¹ : ℝ) : ℂ)) := by
    refine Integrable.congr (exercise20_integrable_inv_quadratic_univ a ha).ofReal ?_
    filter_upwards with x
    simp
  have hkernel_int :
      Integrable (fun x : ℝ ↦ (a / (Real.pi * (a ^ 2 + x ^ 2)) : ℂ)) := by
    refine Integrable.congr (hbaseC.const_mul (((a / Real.pi : ℝ) : ℂ))) ?_
    filter_upwards with x
    simp [div_eq_mul_inv, mul_assoc, mul_comm, add_comm]
  have hfourier_int : Integrable (𝓕 g) := by
    refine Integrable.congr hkernel_int ?_
    filter_upwards with x
    simpa [g] using (exercise20_fourierExpAbsKernel a x ha).symm
  have hFg : 𝓕 g = fun x : ℝ ↦ (a / (Real.pi * (a ^ 2 + x ^ 2)) : ℂ) := by
    funext x
    simpa [g] using exercise20_fourierExpAbsKernel a x ha
  have hpoint :=
    congrFun (Continuous.fourierInv_fourier_eq hg_cont hg_int hfourier_int) (s / (2 * Real.pi))
  rw [hFg, Real.fourierInv_eq'] at hpoint
  simp only [smul_eq_mul] at hpoint
  have hcalc :
      ∫ v : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ v (s / (2 * Real.pi))) * Complex.I) *
          (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)
        =
          (((a / Real.pi : ℝ) : ℂ) *
            ∫ x : ℝ, ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x))) := by
    calc
      ∫ v : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ v (s / (2 * Real.pi))) * Complex.I) *
          (a / (Real.pi * (a ^ 2 + v ^ 2)) : ℂ)
          =
            ∫ v : ℝ, (((a / Real.pi : ℝ) : ℂ) *
              (((((v ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * v)))) := by
                apply integral_congr_ae
                filter_upwards with v
                have hsimp : 2 * Real.pi * inner ℝ v (s / (2 * Real.pi)) = s * v := by
                  simp
                  field_simp [Real.pi_ne_zero]
                rw [hsimp]
                simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_comm]
      _ = (((a / Real.pi : ℝ) : ℂ) *
            ∫ x : ℝ, ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x))) := by
              rw [integral_const_mul]
  rw [hcalc] at hpoint
  have hconst_ne : (((a / Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast div_ne_zero ha.ne' Real.pi_ne_zero
  have hpoint' :
      ∫ x : ℝ, ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x)) =
        (((a / Real.pi : ℝ) : ℂ))⁻¹ * g (s / (2 * Real.pi)) := by
    exact (eq_inv_mul_iff_mul_eq₀ hconst_ne).2 hpoint
  have habs_div : |s / (2 * Real.pi)| = |s| / (2 * Real.pi) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hexp :
      Complex.exp (-((2 * Real.pi * a : ℝ) : ℂ) * |s / (2 * Real.pi)|) =
        (Real.exp (-a * |s|) : ℂ) := by
    rw [habs_div]
    have hargReal :
        -(2 * Real.pi * a) * (|s| / (2 * Real.pi)) = -a * |s| := by
      field_simp [Real.pi_ne_zero]
    have harg :
        -((2 * Real.pi * a : ℝ) : ℂ) * ((|s| / (2 * Real.pi) : ℝ) : ℂ) =
          ((-a * |s| : ℝ) : ℂ) := by
      exact_mod_cast hargReal
    change Complex.exp (-((2 * Real.pi * a : ℝ) : ℂ) * ((|s| / (2 * Real.pi) : ℝ) : ℂ)) =
      (Real.exp (-a * |s|) : ℂ)
    rw [harg, Complex.ofReal_exp]
  calc
    ∫ x : ℝ, ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x))
        = (((a / Real.pi : ℝ) : ℂ))⁻¹ * g (s / (2 * Real.pi)) := hpoint'
    _ = (((Real.pi / a : ℝ) : ℂ) *
          Complex.exp (-((2 * Real.pi * a : ℝ) : ℂ) * |s / (2 * Real.pi)|)) := by
            simp [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = (((Real.pi / a : ℝ) : ℂ) * (Real.exp (-a * |s|) : ℂ)) := by
          rw [hexp]
    _ = (Real.pi * Real.exp (-a * |s|) / a : ℂ) := by
          have hreal :
              (Real.pi / a) * Real.exp (-a * |s|) = Real.pi * Real.exp (-a * |s|) / a := by
            field_simp [ha.ne']
          exact_mod_cast hreal

/-- Helper for Exercise 20: the remaining source-faithful contour step is the whole-line unit
frequency kernel from Proposition 3.1. -/
lemma exercise20_integral_univ_exp_mul_inv_quadratic_unit_freq
    (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * x) =
      (Real.pi * Real.exp (-a) / a : ℂ) := by
  simpa using exercise20_integral_univ_exp_mul_inv_quadratic_abs_freq a 1 ha

/-- Helper for Exercise 20: once the unit-frequency contour kernel is known, a positive dilation
transfers it to all `s > 0` on the whole line. -/
lemma exercise20_integral_univ_exp_mul_inv_quadratic_pos_freq
    (a s : ℝ) (ha : 0 < a) (hs : 0 < s) :
    ∫ x : ℝ, ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x)) =
      (Real.pi * Real.exp (-a * s) / a : ℂ) := by
  simpa [abs_of_pos hs] using exercise20_integral_univ_exp_mul_inv_quadratic_abs_freq a s ha

/-- Helper for Exercise 20: the oscillatory quadratic kernel is integrable on the whole line, so
`Complex.re` may be commuted through its integral. -/
lemma exercise20_integrable_exp_mul_inv_quadratic_univ
    (a s : ℝ) (ha : 0 < a) :
    Integrable
      (fun x : ℝ ↦
        ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x))) := by
  have hbase :
      Integrable (fun x : ℝ ↦ ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹)) := by
    -- The real quadratic majorant is already integrable, and complexification preserves that.
    refine Integrable.congr (exercise20_integrable_inv_quadratic_univ a ha).ofReal ?_
    filter_upwards with x
    simp
  have hcont : Continuous fun x : ℝ ↦ Complex.exp (Complex.I * (s * x)) := by
    -- The oscillatory factor is continuous on the whole real line.
    fun_prop
  -- The exponential factor has constant norm `1`, so the quadratic kernel still dominates.
  refine hbase.mul_bdd (c := 1) hcont.aestronglyMeasurable ?_
  filter_upwards with x
  have hnorm : ‖Complex.exp (Complex.I * (s * x))‖ = 1 := by
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (s * x)
  exact le_of_eq hnorm

/-- Helper for Exercise 20: after the whole-line residue computation, taking real parts and using
evenness halves the cosine kernel to the positive half-line. -/
lemma exercise20_integral_cos_mul_inv_quadratic_positive_freq
    (a s : ℝ) (ha : 0 < a) (hs : 0 < s) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (s * x) / (x ^ 2 + a ^ 2) ∂volume
      = Real.pi * Real.exp (-a * s) / (2 * a) := by
  let f : ℝ → ℝ := fun x ↦ Real.cos (s * x) / (x ^ 2 + a ^ 2)
  have hcomplexIntegrable := exercise20_integrable_exp_mul_inv_quadratic_univ a s ha
  have hrealPart :
      ∀ x : ℝ,
        Complex.re
          (((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x))) = f x := by
    intro x
    dsimp [f]
    have hmul : Complex.I * (s * x) = ((s * x : ℝ) : ℂ) * Complex.I := by
      simp [mul_comm]
    rw [mul_comm, ← Complex.ofReal_inv, Complex.re_mul_ofReal, hmul, Complex.exp_ofReal_mul_I_re]
    ring
  have hfIntegrable : Integrable f := by
    refine Integrable.congr hcomplexIntegrable.re ?_
    filter_upwards with x
    exact hrealPart x
  have hwhole :
      ∫ x : ℝ, f x = Real.pi * Real.exp (-a * s) / a := by
    have hwholec :=
      congrArg Complex.re
        (exercise20_integral_univ_exp_mul_inv_quadratic_pos_freq a s ha hs)
    have hexp_real : (Complex.exp (-(↑a * ↑s))).re = Real.exp (-a * s) := by
      simpa using Complex.exp_ofReal_re (-(a * s))
    calc
      ∫ x : ℝ, f x
          = Complex.re
              (∫ x : ℝ,
                ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) * Complex.exp (Complex.I * (s * x))) := by
                  calc
                    ∫ x : ℝ, f x
                        = ∫ x : ℝ,
                            Complex.re
                              (((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) *
                                Complex.exp (Complex.I * (s * x))) := by
                                  refine integral_congr_ae ?_
                                  filter_upwards with x
                                  simpa using (hrealPart x).symm
                    _ = Complex.re
                          (∫ x : ℝ,
                            ((((x ^ 2 + a ^ 2) : ℝ) : ℂ)⁻¹) *
                              Complex.exp (Complex.I * (s * x))) := by
                                exact integral_re hcomplexIntegrable
      _ = Real.pi * (Complex.exp (-(↑a * ↑s))).re / a := by
            simpa using hwholec
      _ = Real.pi * Real.exp (-a * s) / a := by
            rw [hexp_real]
  have hleft_eq_right :
      ∫ x in Set.Iic (0 : ℝ), f x ∂volume = ∫ x in Set.Ioi (0 : ℝ), f x ∂volume := by
    calc
      ∫ x in Set.Iic (0 : ℝ), f x ∂volume
          = ∫ x in Set.Iic (0 : ℝ), f (-x) ∂volume := by
              refine integral_congr_ae ?_
              filter_upwards with x
              dsimp [f]
              simp [Real.cos_neg]
      _ = ∫ x in Set.Ioi (0 : ℝ), f x ∂volume := by
            simpa [f] using integral_comp_neg_Iic (0 : ℝ) f
  have hsplit :
      ∫ x in Set.Iic (0 : ℝ), f x ∂volume + ∫ x in Set.Ioi (0 : ℝ), f x ∂volume = ∫ x : ℝ, f x := by
    -- Reassemble the two half-line integrals into the full-line integral.
    exact
      intervalIntegral.integral_Iic_add_Ioi
        (μ := volume) (f := f) (b := 0) hfIntegrable.integrableOn hfIntegrable.integrableOn
  have hdouble :
      (2 : ℝ) * ∫ x in Set.Ioi (0 : ℝ), f x ∂volume = Real.pi * Real.exp (-a * s) / a := by
    calc
      (2 : ℝ) * ∫ x in Set.Ioi (0 : ℝ), f x ∂volume
          = ∫ x in Set.Ioi (0 : ℝ), f x ∂volume +
              ∫ x in Set.Ioi (0 : ℝ), f x ∂volume := by
                ring
      _ = ∫ x in Set.Iic (0 : ℝ), f x ∂volume +
            ∫ x in Set.Ioi (0 : ℝ), f x ∂volume := by
              rw [hleft_eq_right]
      _ = ∫ x : ℝ, f x := hsplit
      _ = Real.pi * Real.exp (-a * s) / a := hwhole
  have hhalf :
      ∫ x in Set.Ioi (0 : ℝ), f x ∂volume = (Real.pi * Real.exp (-a * s) / a) / 2 := by
    have hdouble' :
        (∫ x in Set.Ioi (0 : ℝ), f x ∂volume) * 2 = Real.pi * Real.exp (-a * s) / a := by
      simpa [mul_comm] using hdouble
    exact (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2 hdouble' 
  calc
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (s * x) / (x ^ 2 + a ^ 2) ∂volume
        = ∫ x in Set.Ioi (0 : ℝ), f x ∂volume := by
            rfl
    _ = (Real.pi * Real.exp (-a * s) / a) / 2 := hhalf
    _ = Real.pi * Real.exp (-a * s) / (2 * a) := by
          field_simp [ha.ne']

/-- Helper for Exercise 20: the zero-frequency cosine kernel already follows from part (1), so the
remaining contour work is only the positive-frequency residue computation. -/
lemma exercise20_integral_cos_mul_inv_quadratic_nonneg_freq
    (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (s * x) / (x ^ 2 + a ^ 2) ∂volume
      = Real.pi * Real.exp (-a * s) / (2 * a) := by
  by_cases hs0 : s = 0
  · -- At frequency `0`, the cosine kernel is exactly the `n = 1` quadratic integral from part (1).
    subst hs0
    calc
      ∫ x in Set.Ioi (0 : ℝ), Real.cos ((0 : ℝ) * x) / (x ^ 2 + a ^ 2) ∂volume
          = ∫ x in Set.Ioi (0 : ℝ), (a ^ 2 + 1 * x ^ 2)⁻¹ ^ 1 ∂volume := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x hx
              simp [pow_one, add_comm]
      _ = Real.pi * (Nat.centralBinom (1 - 1) : ℝ) /
            ((2 : ℝ) ^ (2 * 1 - 1) * (a ^ 2) ^ (1 - 1) * Real.sqrt (a ^ 2 * 1)) := by
            simpa using
              (integral_inv_quadratic_pow (a := a ^ 2) (b := 1) (n := 1)
                (by positivity) (by positivity) (by norm_num : 0 < (1 : ℕ)))
      _ = Real.pi * Real.exp (-a * (0 : ℝ)) / (2 * a) := by
            simp [Real.sqrt_sq_eq_abs, abs_of_pos ha]
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (by simpa [eq_comm] using hs0)
    -- Route correction: the remaining contour work has been isolated in the unit-frequency kernel,
    -- and the `s > 0` branch is now only the already-packaged scaling plus evenness adapter.
    exact exercise20_integral_cos_mul_inv_quadratic_positive_freq a s ha hs_pos

/-- Helper for Exercise 20: the source correction term is the set integral behind the improper
limit. -/
lemma exercise20_integral_sinc_over_quadratic
    (a : ℝ) (ha : 0 < a) :
    ∫ x in Set.Ioi (0 : ℝ), Real.sinc x / (x ^ 2 + a ^ 2) ∂volume
      = Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2) := by
  -- Route correction: the source-faithful Fubini reduction is now complete, so the target depends
  -- only on the narrower cosine-kernel residue theorem above.
  refine exercise20_integral_sinc_over_quadratic_of_cos_kernel a ha ?_
  intro s hs
  have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le zero_le_one] using hs
  exact exercise20_integral_cos_mul_inv_quadratic_nonneg_freq a s ha hs'.1

/-- Helper for Exercise 20: once the set-integral correction term is evaluated, the improper
interval limit follows from the standard `Ioi`-integral convergence theorem. -/
lemma exercise20_tendsto_intervalIntegral_sinc_over_quadratic
    (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun R : ℝ ↦
        ∫ x in (0 : ℝ)..R, Real.sinc x / (x ^ 2 + a ^ 2))
      atTop
      (𝓝 (Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2))) := by
  have hfi := exercise20_integrable_sinc_over_quadratic a ha
  have hlimit :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := volume) (f := fun x : ℝ ↦ Real.sinc x / (x ^ 2 + a ^ 2))
      (a := (0 : ℝ)) (b := fun R : ℝ ↦ R) hfi tendsto_id
  -- Route correction: the improper-limit adapter is no longer the blocker; only the exact set
  -- integral `exercise20_integral_sinc_over_quadratic` remains.
  simpa [exercise20_integral_sinc_over_quadratic a ha] using hlimit

/-- Cartan section12 0033_Exercise_20: Exercise 20 (3) evaluates the conditionally convergent
improper integral `∫_0^∞ ((x^2 - a^2) / (x^2 + a^2)) (sin x / x) dx` for `a > 0` by residues. The
source integral is stated as an interval-integral limit rather than a Lebesgue integral over
`Set.Ioi`, since the integrand is not absolutely integrable. -/
theorem integral_quadratic_ratio_mul_sin_div
    (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun R : ℝ ↦
        ∫ x in (0 : ℝ)..R,
          ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * (Real.sin x / x))
      atTop
      (𝓝 (Real.pi * Real.exp (-a) - Real.pi / 2)) := by
  have ha2_ne : a ^ 2 ≠ 0 := by exact pow_ne_zero 2 ha.ne'
  have hsinc_limit :
      Tendsto (fun R : ℝ ↦ ∫ x in (0 : ℝ)..R, Real.sinc x) atTop (𝓝 (Real.pi / 2)) := by
    have hEq :
        (fun R : ℝ ↦ ∫ x in (0 : ℝ)..R, Real.sin x / x) =ᶠ[atTop]
          fun R : ℝ ↦ ∫ x in (0 : ℝ)..R, Real.sinc x := by
      -- On the eventual positive tail, the imported `sin x / x = sinc x` interval identity
      -- rewrites the Dirichlet term to the continuous model.
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact intervalIntegral_sin_div_eq_intervalIntegral_sinc hR
    exact Tendsto.congr' hEq tendsto_intervalIntegral_sin_div_eq_pi_half
  have hsplit_limit :
      Tendsto
        (fun R : ℝ ↦
          ∫ x in (0 : ℝ)..R,
            Real.sinc x - (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2)))
        atTop
        (𝓝 (Real.pi * Real.exp (-a) - Real.pi / 2)) := by
    have hcorr :=
      exercise20_tendsto_intervalIntegral_sinc_over_quadratic a ha
    have hsub :
        Tendsto
          (fun R : ℝ ↦
            (∫ x in (0 : ℝ)..R, Real.sinc x) -
              (2 * a ^ 2) * (∫ x in (0 : ℝ)..R, Real.sinc x / (x ^ 2 + a ^ 2)))
          atTop
          (𝓝 ((Real.pi / 2) -
            (2 * a ^ 2) * (Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2)))) :=
      hsinc_limit.sub ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (2 * a ^ 2)) atTop
        (𝓝 (2 * a ^ 2))).mul hcorr)
    have hcont_corr :
        Continuous fun x : ℝ ↦ Real.sinc x / (x ^ 2 + a ^ 2) := by
      -- The `sinc` model is continuous, and the quadratic denominator stays positive for `a > 0`.
      refine Real.continuous_sinc.div ?_ ?_
      · continuity
      · intro x
        have hpos : 0 < x ^ 2 + a ^ 2 := by positivity
        exact hpos.ne'
    have hinterval_eq :
        (fun R : ℝ ↦
          ∫ x in (0 : ℝ)..R,
            Real.sinc x - (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2))) =
          fun R : ℝ ↦
            (∫ x in (0 : ℝ)..R, Real.sinc x) -
              (2 * a ^ 2) * (∫ x in (0 : ℝ)..R, Real.sinc x / (x ^ 2 + a ^ 2)) := by
      -- Split the interval integral once the two summands are known to be interval integrable.
      funext R
      have hsinc_int : IntervalIntegrable Real.sinc volume (0 : ℝ) R :=
        Real.continuous_sinc.intervalIntegrable _ _
      have hscaled_int :
          IntervalIntegrable
            (fun x : ℝ ↦ (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2)))
            volume (0 : ℝ) R :=
        (continuous_const.mul hcont_corr).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hsinc_int hscaled_int, intervalIntegral.integral_const_mul]
    have hconst :
        (Real.pi / 2) - (2 * a ^ 2) * (Real.pi * (1 - Real.exp (-a)) / (2 * a ^ 2)) =
          Real.pi * Real.exp (-a) - Real.pi / 2 := by
      field_simp [ha2_ne]
      ring
    -- Combine the Dirichlet limit with the correction-kernel limit, then normalize the constant.
    simpa [hinterval_eq, hconst] using hsub
  have hraw_eq :
      (fun R : ℝ ↦
        ∫ x in (0 : ℝ)..R,
          ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * (Real.sin x / x)) =ᶠ[atTop]
        fun R : ℝ ↦
          ∫ x in (0 : ℝ)..R,
            Real.sinc x - (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hto_sinc :
        ∫ x in (0 : ℝ)..R,
          ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * (Real.sin x / x)
          =
            ∫ x in (0 : ℝ)..R,
              ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * Real.sinc x := by
      -- For `R > 0`, the unordered interval is `Ioc 0 R`, so it excludes `0`; there the raw
      -- quotient and `sinc` agree pointwise.
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall <| fun x hx ↦ by
        rw [Set.uIoc_of_le hR.le, Set.mem_Ioc] at hx
        have hx0 : x ≠ 0 := by linarith
        rw [Real.sinc_of_ne_zero hx0]
    have hsinc_split :
        ∫ x in (0 : ℝ)..R,
          ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * Real.sinc x
          =
            ∫ x in (0 : ℝ)..R,
              Real.sinc x - (2 * a ^ 2) * (Real.sinc x / (x ^ 2 + a ^ 2)) := by
      -- With `sinc`, the algebraic split holds pointwise on the whole interval, including `0`.
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall <| fun x hx ↦ by
        have hden : x ^ 2 + a ^ 2 ≠ 0 := by
          have hpos : 0 < x ^ 2 + a ^ 2 := by positivity
          exact hpos.ne'
        exact exercise20_quadratic_ratio_mul_sinc_split a x hden
    exact hto_sinc.trans hsinc_split
  -- Route correction: the main theorem is now reduced to the single source-faithful blocker
  -- `exercise20_tendsto_intervalIntegral_sinc_over_quadratic`.
  exact Tendsto.congr' hraw_eq.symm hsplit_limit

/-- Exercise 20 (4): if `|a| < 1`, then
`∫_0^π cos (n t) / (1 - 2 a cos t + a^2) dt = π a^n / (1 - a^2)`. -/
theorem integral_cos_nat_mul_div_poisson_kernel_lt_one
    (a : ℝ) (n : ℕ) (ha : |a| < 1) :
    ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2)
      = Real.pi * a ^ n / (1 - a ^ 2) := by
  have hne : |a| ≠ 1 := ne_of_lt ha
  have hden : 1 - a ^ 2 ≠ 0 := by
    intro hzero
    have hsquare : a ^ 2 = 1 := by linarith
    have habs_sq : |a| ^ 2 = 1 := by simpa [sq_abs] using hsquare
    have habs : |a| = 1 := by
      have habs_nonneg : 0 ≤ |a| := abs_nonneg a
      nlinarith
    exact hne habs
  have havg := exercise20_poisson_average_fourier_mode (a := a) (n := n) ha
  -- The Poisson average is already the desired scalar multiple of the cosine integral.
  rw [exercise20_poisson_circleAverage_eq_intervalIntegral (a := a) (n := n) hne] at havg
  apply (eq_div_iff hden).2
  have hmul := congrArg (fun x : ℝ ↦ Real.pi * x) havg
  field_simp [hden, Real.pi_ne_zero] at hmul ⊢
  linarith

/-- Exercise 20 (5): if `1 < |a|`, then
`∫_0^π cos (n t) / (1 - 2 a cos t + a^2) dt = π / (a^n (a^2 - 1))`. -/
theorem integral_cos_nat_mul_div_poisson_kernel_gt_one
    (a : ℝ) (n : ℕ) (ha : 1 < |a|) :
    ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2)
      = Real.pi / (a ^ n * (a ^ 2 - 1)) := by
  have ha0 : a ≠ 0 := by
    intro hzero
    have : (1 : ℝ) < 0 := by simpa [hzero] using ha
    linarith
  have hainv : |a⁻¹| < 1 := by
    simpa [abs_inv] using (inv_lt_one_of_one_lt₀ ha)
  have hrewrite :
      ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2)
        = (a ^ 2)⁻¹ *
            ∫ t in (0 : ℝ)..Real.pi,
              Real.cos (n * t) / (1 - 2 * a⁻¹ * Real.cos t + (a ^ 2)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
    field_simp [ha0, ha2]
    ring
  -- Reduce to the `|a| < 1` case by factoring out `a²` from the denominator.
  rw [hrewrite]
  have hsq : (a ^ 2)⁻¹ = a⁻¹ ^ 2 := by
    field_simp [ha0]
  rw [hsq, integral_cos_nat_mul_div_poisson_kernel_lt_one (a := a⁻¹) (n := n) hainv]
  field_simp [ha0]
  have hpowcancel : (1 / a) ^ n * a ^ n = 1 := by
    simp [ha0]
  rw [hpowcancel, one_div]

/-- Helper for Cartan section12 0033_Exercise_20: package the explicit formulas proved above into
one conjunction for the item-per-file pipeline. -/
theorem exercise20_residue_integral_evaluations :
    (∀ a b : ℝ, ∀ n : ℕ, 0 < a → 0 < b → 0 < n →
      ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
        = Real.pi * (Nat.centralBinom (n - 1) : ℝ) /
            ((2 : ℝ) ^ (2 * n - 1) * a ^ (n - 1) * Real.sqrt (a * b))) ∧
    (∀ a b : ℝ,
      ∫ x in Set.Ioi (0 : ℝ), (Real.cos (2 * a * x) - Real.cos (2 * b * x)) / x ^ 2 ∂volume
        = Real.pi * (|b| - |a|)) ∧
    (∀ a : ℝ, 0 < a →
      Tendsto
        (fun R : ℝ ↦
          ∫ x in (0 : ℝ)..R,
            ((x ^ 2 - a ^ 2) / (x ^ 2 + a ^ 2)) * (Real.sin x / x))
        atTop
        (𝓝 (Real.pi * Real.exp (-a) - Real.pi / 2))) ∧
    (∀ a : ℝ, ∀ n : ℕ, |a| < 1 →
      ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2)
        = Real.pi * a ^ n / (1 - a ^ 2)) ∧
    (∀ a : ℝ, ∀ n : ℕ, 1 < |a| →
      ∫ t in (0 : ℝ)..Real.pi, Real.cos (n * t) / (1 - 2 * a * Real.cos t + a ^ 2)
        = Real.pi / (a ^ n * (a ^ 2 - 1))) := by
  -- Package the five proved formulas under the raw item label so the item-per-file pipeline can
  -- recover the textbook entry from this target file.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b n ha hb hn
    exact integral_inv_quadratic_pow a b n ha hb hn
  · intro a b
    exact integral_cos_sub_cos_div_sq a b
  · intro a ha
    exact integral_quadratic_ratio_mul_sin_div a ha
  · intro a n ha
    exact integral_cos_nat_mul_div_poisson_kernel_lt_one a n ha
  · intro a n ha
    exact integral_cos_nat_mul_div_poisson_kernel_gt_one a n ha
