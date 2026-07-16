import Mathlib
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import DifferentialForms_Cartan_1970.cartan.III.section12.«0008_Example_III_6_extra_3»

open MeasureTheory
open InnerProductSpace
open Filter
open scoped Real Topology

noncomputable section

/-- Helper for Exercise 20: the substitution `x = sqrt (a / b) * y` reduces the quadratic kernel
to the normalized kernel `1 + y²`. -/
lemma exercise20_integral_inv_quadratic_pow_scaling
    (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
      = (Real.sqrt (a / b) / a ^ n) *
          ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume := by
  let c : ℝ := Real.sqrt (a / b)
  have hc : 0 < c := by
    -- The scaling factor is positive because `a / b > 0`.
    dsimp [c]
    exact Real.sqrt_pos.mpr (div_pos ha hb)
  have hscale :
      ∫ y in Set.Ioi (0 : ℝ), (a + b * (c * y) ^ 2)⁻¹ ^ n ∂volume =
        c⁻¹ * ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume := by
    simpa [c, smul_eq_mul] using
      (integral_comp_mul_left_Ioi (g := fun t : ℝ ↦ (a + b * t ^ 2)⁻¹ ^ n) (a := (0 : ℝ)) hc)
  have hc_sq : c ^ 2 = a / b := by
    -- Squaring the chosen scale recovers the ratio `a / b`.
    dsimp [c]
    simpa [pow_two] using Real.sq_sqrt (show 0 ≤ a / b by exact (div_nonneg ha.le hb.le))
  have hpoint :
      ∀ y : ℝ,
        (a + b * (c * y) ^ 2)⁻¹ ^ n =
          (a⁻¹ ^ n) * (1 + y ^ 2)⁻¹ ^ n := by
    intro y
    have hrewrite : a + b * (c * y) ^ 2 = a * (1 + y ^ 2) := by
      -- After the scaling, the quadratic denominator factors as `a (1 + y²)`.
      calc
        a + b * (c * y) ^ 2 = a + b * (c ^ 2 * y ^ 2) := by ring
        _ = a + a * y ^ 2 := by
              rw [hc_sq]
              field_simp [hb.ne']
        _ = a * (1 + y ^ 2) := by ring
    -- Separate the constant factor `a` from the normalized kernel.
    rw [hrewrite, mul_inv_rev, mul_pow]
    ring
  -- Route correction: the outer scaling is now isolated, so the remaining blocker is only the
  -- normalized integral `∫_0^∞ (1 + y²)^(-n) dy`.
  calc
    ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
        = c * ∫ y in Set.Ioi (0 : ℝ), (a + b * (c * y) ^ 2)⁻¹ ^ n ∂volume := by
            calc
              ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume
                  = c * (c⁻¹ * ∫ x in Set.Ioi (0 : ℝ), (a + b * x ^ 2)⁻¹ ^ n ∂volume) := by
                      field_simp [hc.ne']
                _ = c * ∫ y in Set.Ioi (0 : ℝ), (a + b * (c * y) ^ 2)⁻¹ ^ n ∂volume := by
                      rw [hscale]
    _ = c * ∫ y in Set.Ioi (0 : ℝ), (a⁻¹ ^ n) * (1 + y ^ 2)⁻¹ ^ n ∂volume := by
          congr 1
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y hy
          exact hpoint y
    _ = (c * a⁻¹ ^ n) * ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume := by
          rw [integral_const_mul]
          ring
    _ = (Real.sqrt (a / b) / a ^ n) * ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume := by
          simp [c, div_eq_mul_inv, inv_pow]

/-- Helper for Exercise 20: the tangent substitution on `(0, π / 2)` rewrites the normalized
quadratic kernel as an even cosine-power integral. -/
lemma exercise20_integral_inv_one_add_sq_pow_eq_cos_even_power
    (n : ℕ) (hn : 0 < n) :
    ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ ^ (2 * (n - 1)) := by
  let s : Set ℝ := Set.Ioo (0 : ℝ) (Real.pi / 2)
  have hs_image : Real.tan '' s = Set.Ioi (0 : ℝ) := by
    ext y
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      exact Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
    · intro hy
      refine ⟨Real.arctan y, ⟨Real.arctan_pos.mpr hy, Real.arctan_lt_pi_div_two y⟩, ?_⟩
      rw [Real.tan_arctan]
  have hderiv :
      ∀ θ ∈ s, HasDerivWithinAt Real.tan (1 / Real.cos θ ^ 2) s θ := by
    intro θ hθ
    -- Differentiate `tan` on the open interval where `cos θ > 0`.
    exact
      (Real.hasDerivAt_tan_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).hasDerivWithinAt
  have hinj : Set.InjOn Real.tan s := by
    intro x hx y hy hxy
    exact
      Real.injOn_tan
        ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
        ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩
        hxy
  have hchange :
      ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume
        =
          ∫ θ in s,
            |(fun t : ℝ ↦ 1 / Real.cos t ^ 2) θ| • ((1 + Real.tan θ ^ 2)⁻¹ ^ n) ∂volume := by
    rw [← hs_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  have hpoint :
      ∀ θ ∈ s, |1 / Real.cos θ ^ 2| • ((1 + Real.tan θ ^ 2)⁻¹ ^ n)
          = Real.cos θ ^ (2 * (n - 1)) := by
    intro θ hθ
    have hcos_pos : 0 < Real.cos θ := by
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have hcos_ne : Real.cos θ ≠ 0 := hcos_pos.ne'
    have habs :
        |1 / Real.cos θ ^ 2| = 1 / Real.cos θ ^ 2 := by
      rw [abs_of_pos]
      positivity
    have hkernel : (1 + Real.tan θ ^ 2)⁻¹ = Real.cos θ ^ 2 := by
      simpa using Real.inv_one_add_tan_sq hcos_ne
    have hstep :
        (1 / Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ n = (Real.cos θ ^ 2) ^ (n - 1) := by
      have hn' : n = Nat.succ (n - 1) := by
        omega
      have hmul :
          (Real.cos θ ^ 2) ^ n = Real.cos θ ^ 2 * (Real.cos θ ^ 2) ^ (n - 1) := by
        rw [hn', pow_succ']
        simp
      rw [hmul]
      field_simp [pow_ne_zero 2 hcos_ne]
    -- After the Jacobian factor, only the even cosine power remains.
    calc
      |1 / Real.cos θ ^ 2| • ((1 + Real.tan θ ^ 2)⁻¹ ^ n)
          = (1 / Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ n := by
              rw [habs, hkernel, smul_eq_mul]
      _ = (Real.cos θ ^ 2) ^ (n - 1) := hstep
      _ = Real.cos θ ^ (2 * (n - 1)) := by
            rw [pow_mul]
  -- Rewrite the image integral pointwise, then convert the open set integral to the interval form.
  calc
    ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ ^ n ∂volume
        =
          ∫ θ in s,
            |(fun t : ℝ ↦ 1 / Real.cos t ^ 2) θ| • ((1 + Real.tan θ ^ 2)⁻¹ ^ n) ∂volume := hchange
    _ = ∫ θ in s, Real.cos θ ^ (2 * (n - 1)) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          exact hpoint θ hθ
    _ = ∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), Real.cos θ ^ (2 * (n - 1)) ∂volume := by
          rw [integral_Ioc_eq_integral_Ioo]
    _ = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ ^ (2 * (n - 1)) := by
          rw [intervalIntegral.integral_of_le]
          positivity

/-- Helper for Exercise 20: the even cosine-power integral on `[0, π / 2]` has the standard
central-binomial closed form. -/
lemma exercise20_integral_cos_even_power_centralBinom
    (m : ℕ) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ ^ (2 * m)
      = Real.pi * (Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m + 1) := by
  have hprod :
      ∏ i ∈ Finset.range m, (2 * (i : ℝ) + 1) / (2 * i + 2)
        = (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m := by
    induction m with
    | zero =>
        simp
    | succ m hm =>
        rw [Finset.prod_range_succ, hm]
        have hcentral :
            ((m + 1 : ℝ) * (Nat.centralBinom (m + 1) : ℝ))
              = 2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
          exact_mod_cast Nat.succ_mul_centralBinom_succ m
        rw [pow_succ]
        field_simp
        nlinarith [hcentral]
  have hpow : (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * m) := by
    calc
      (4 : ℝ) ^ m = ((2 : ℝ) ^ 2) ^ m := by norm_num
      _ = (2 : ℝ) ^ (2 * m) := by rw [pow_mul]
  -- Use the standard sine-power evaluation, then rewrite the Wallis product as a central binomial.
  calc
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ ^ (2 * m)
        = (1 / 2 : ℝ) * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ (2 * m) := by
            rw [EulerSine.integral_cos_pow_eq]
    _ = (1 / 2 : ℝ) *
          (Real.pi * ∏ i ∈ Finset.range m, (2 * (i : ℝ) + 1) / (2 * i + 2)) := by
            rw [integral_sin_pow_even]
    _ = (1 / 2 : ℝ) * (Real.pi * ((Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m)) := by
          rw [hprod]
    _ = (1 / 2 : ℝ) * (Real.pi * ((Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m))) := by
          rw [hpow]
    _ = Real.pi * (Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m + 1) := by
          field_simp
          ring
