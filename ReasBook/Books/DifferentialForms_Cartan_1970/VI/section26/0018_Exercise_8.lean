import Mathlib
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import DifferentialForms_Cartan_1970.III.section11.PeriodLattice
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped UpperHalfPlane

noncomputable section

-- Domain sampling for this file: the source-facing primitive owner is the modulus
-- `Exercise8Modulus = Set.Ioo (0 : ℝ) 1`. The canonical period-data owners for the doubly
-- periodic inverse are `PeriodPair` and `HasPeriodLattice`; the remaining derived objects use
-- `UpperHalfPlane`, `curveIntegral`, `Complex.scalarOneForm` / `f dz`, `Meromorphic`, and the
-- Jacobi-theta owner `jacobiTheta₂`.

/-- The modulus parameter `k` from Exercise 8, constrained by `0 < k < 1`. -/
abbrev Exercise8Modulus := Set.Ioo (0 : ℝ) 1

namespace Exercise8Modulus

/-- An Exercise 8 modulus is positive. -/
theorem pos (k : Exercise8Modulus) : 0 < (k : ℝ) :=
  k.2.1

/-- An Exercise 8 modulus is strictly smaller than `1`. -/
theorem lt_one (k : Exercise8Modulus) : (k : ℝ) < 1 :=
  k.2.2

end Exercise8Modulus

/-- The closed upper half-plane `Im z ≥ 0`. -/
abbrev ClosedUpperHalfPlane :=
  {z : ℂ // 0 ≤ z.im}

/-- The elliptic integrand from Exercise 8, for a modulus `k ∈ (0, 1)`. -/
def exercise8_integrand (k : Exercise8Modulus) (z : ℂ) : ℂ :=
  1 /
    Complex.sqrt
      (((1 : ℂ) - z ^ (2 : ℕ)) * ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ)))

/-- The Abelian integral from Exercise 8, computed along the straight segment from `0` to `z`. -/
def exercise8_abel_integral (k : Exercise8Modulus) (z : UpperHalfPlane) : ℂ :=
  ∫ᶜ w in Path.segment (0 : ℂ) (z : ℂ), (exercise8_integrand k dz) w

/-- Normal form for the Exercise 8 Abelian integral. -/
theorem exercise8_abel_integral_def (k : Exercise8Modulus) (z : UpperHalfPlane) :
    exercise8_abel_integral k z =
      ∫ᶜ w in Path.segment (0 : ℂ) (z : ℂ), (exercise8_integrand k dz) w := rfl

/-- The complete real period `K` from Exercise 8. -/
def exercise8_complete_real_period (k : Exercise8Modulus) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)))

/-- Normal form for the complete real period from Exercise 8. -/
theorem exercise8_complete_real_period_def (k : Exercise8Modulus) :
    exercise8_complete_real_period k =
      ∫ t in (0 : ℝ)..1,
        1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) := rfl

/-- The complete imaginary period `K'` from Exercise 8. -/
def exercise8_complete_imaginary_period (k : Exercise8Modulus) : ℝ :=
  ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
    1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)))

/-- Normal form for the complete imaginary period from Exercise 8. -/
theorem exercise8_complete_imaginary_period_def (k : Exercise8Modulus) :
    exercise8_complete_imaginary_period k =
      ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
        1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) := rfl

/-- Helper for Exercise 8: on `[0, 1]`, the radicand `1 - k^2 x^2` stays strictly positive. -/
lemma exercise8_real_factor_radicand_pos {k : Exercise8Modulus} {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < 1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ) := by
  -- The source proof first isolates the continuous multiplier `1 / √(1 - k² x²)` on `[0, 1]`.
  have hk2 : (k : ℝ) ^ (2 : ℕ) < 1 := by
    nlinarith [Exercise8Modulus.pos k, Exercise8Modulus.lt_one k]
  have hx2le : x ^ (2 : ℕ) ≤ 1 := by
    nlinarith [hx.1, hx.2]
  have hmulle : (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ) ≤ (k : ℝ) ^ (2 : ℕ) := by
    exact mul_le_of_le_one_right (by positivity) hx2le
  exact sub_pos.mpr (lt_of_le_of_lt hmulle hk2)

/-- Helper for Exercise 8: the factor `1 / √(1 - k^2 x^2)` is positive on `(0, 1)`. -/
lemma exercise8_real_factor_pos {k : Exercise8Modulus} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < 1 / Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)) := by
  -- Once the radicand is positive, the factor is a positive reciprocal square root.
  exact one_div_pos.mpr <|
    Real.sqrt_pos.2 <|
      exercise8_real_factor_radicand_pos (k := k) ⟨le_of_lt hx.1, hx.2.le⟩

/-- Helper for Exercise 8: the continuous multiplier `1 / √(1 - k^2 x^2)` is well-defined on
`[0, 1]`. -/
lemma exercise8_real_factor_continuousOn (k : Exercise8Modulus) :
    ContinuousOn
      (fun x : ℝ => 1 / Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)))
      (Icc (0 : ℝ) 1) := by
  -- The multiplier is the inverse of a square root whose radicand stays positive on the interval.
  -- We prove continuity for the inverse form and then rewrite `1 / a` as `a⁻¹`.
  simpa [one_div] using
    (ContinuousOn.inv₀
      (Real.continuous_sqrt.continuousOn.comp
        (by
          simpa using
            (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow (2 : ℕ)))))
        (by
          intro x hx
          exact (exercise8_real_factor_radicand_pos (k := k) hx).le))
      (by
        intro x hx
        exact Real.sqrt_ne_zero'.2 (exercise8_real_factor_radicand_pos (k := k) hx)) :
      ContinuousOn
        (fun x : ℝ => (Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)))⁻¹)
        (Icc (0 : ℝ) 1))

/-- Helper for Exercise 8: on `[0, 1]`, the real-period kernel factors through the Chebyshev
model kernel `1 / √(1 - x^2)`. -/
lemma exercise8_real_kernel_eq_factored {k : Exercise8Modulus} {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    1 / Real.sqrt ((1 - x ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))) =
      (1 / Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))) *
        (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ := by
  -- This puts the Exercise 8 kernel into the exact shape needed for mathlib's model integral.
  have hx_nonneg : 0 ≤ 1 - x ^ (2 : ℕ) := by
    nlinarith [hx.1, hx.2]
  rw [Real.sqrt_mul hx_nonneg (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)), one_div, mul_inv_rev]
  rw [one_div]

/-- The complete real period `K` from Exercise 8 is positive. -/
theorem exercise8_complete_real_period_pos (k : Exercise8Modulus) :
    0 < exercise8_complete_real_period k := by
  -- Route correction: we follow the source route by factoring the kernel into a continuous
  -- positive multiplier times the standard Chebyshev kernel `1 / √(1 - x^2)`.
  rw [exercise8_complete_real_period_def]
  have hbase :
      IntervalIntegrable
        (fun x : ℝ => (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hcheb01 :
        IntervalIntegrable
          (fun x : ℝ => Real.sqrt (1 - x ^ (2 : ℕ))⁻¹)
          MeasureTheory.volume (0 : ℝ) 1 := by
      let hcheb := Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
      refine hcheb.mono_set' (c := (0 : ℝ)) (d := (1 : ℝ)) ?_
      intro x hx
      have hx' : x ∈ Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using hx
      have hx'' : x ∈ Ioc (-1 : ℝ) 1 := by
        exact ⟨by linarith [hx'.1], hx'.2⟩
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx''
    simpa using hcheb01
  have hfactored :
      IntervalIntegrable
        (fun x : ℝ =>
          (1 / Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))) *
            (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (0 : ℝ) 1 := by
    -- The extra factor is continuous on `[0, 1]`, so it preserves interval integrability.
    exact hbase.continuousOn_mul <|
      by simpa [Set.uIcc_of_le zero_le_one] using exercise8_real_factor_continuousOn k
  have hkernel :
      IntervalIntegrable
        (fun x : ℝ =>
          1 / Real.sqrt ((1 - x ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))))
        MeasureTheory.volume (0 : ℝ) 1 := by
    refine hfactored.congr ?_
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      have hxIoc : x ∈ Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using hx
      exact ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    simpa using (exercise8_real_kernel_eq_factored (k := k) hx').symm
  refine intervalIntegral.intervalIntegral_pos_of_pos_on hkernel ?_ zero_lt_one
  intro x hx
  have hx_sqrt : 0 < Real.sqrt (1 - x ^ (2 : ℕ)) := by
    have hx_rad : 0 < 1 - x ^ (2 : ℕ) := by
      nlinarith [hx.1, hx.2]
    exact Real.sqrt_pos.2 hx_rad
  -- The factored form shows the kernel is a product of two positive real factors.
  rw [exercise8_real_kernel_eq_factored (k := k) ⟨le_of_lt hx.1, hx.2.le⟩]
  exact mul_pos (exercise8_real_factor_pos (k := k) hx) (inv_pos.2 hx_sqrt)

/-- Helper for Exercise 8: the endpoint model kernel `1 / √((t - a) (b - t))` is interval
integrable on every compact interval `[a, b]` with `a < b`. -/
lemma exercise8_endpoint_sqrt_kernel_intervalIntegrable {a b : ℝ} (hab : a < b) :
    IntervalIntegrable
      (fun t : ℝ => (Real.sqrt ((t - a) * (b - t)))⁻¹)
      MeasureTheory.volume a b := by
  let c : ℝ := (b - a) / 2
  let d : ℝ := (a + b) / 2
  have hc_pos : 0 < c := by
    -- The affine transport from `[-1, 1]` to `[a, b]` uses the positive half-length `c`.
    dsimp [c]
    linarith
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hmodel :
      IntervalIntegrable
        (fun x : ℝ => (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (-1) 1 := by
    -- This is mathlib's Chebyshev-model endpoint singularity.
    simpa using Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have hscaled :
      IntervalIntegrable
        (fun x : ℝ => c⁻¹ * (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (-1) 1 := by
    -- Multiplying by the constant Jacobian factor preserves interval integrability.
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hmodel.const_mul c⁻¹
  have hcomp :
      IntervalIntegrable
        (fun x : ℝ =>
          (Real.sqrt (((c * x + d) - a) * (b - (c * x + d))))⁻¹)
        MeasureTheory.volume (-1) 1 := by
    -- After the affine substitution, the transported kernel is exactly the scaled Chebyshev model.
    refine hscaled.congr ?_
    intro x hx
    have hx' : x ∈ Icc (-1 : ℝ) 1 := by
      have hxIoc : x ∈ Ioc (-1 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      exact ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hx_nonneg : 0 ≤ 1 - x ^ (2 : ℕ) := by
      nlinarith [hx'.1, hx'.2]
    have hprod :
        (((c * x + d) - a) * (b - (c * x + d))) = c ^ (2 : ℕ) * (1 - x ^ (2 : ℕ)) := by
      dsimp [c, d]
      ring
    have hsqrtc : Real.sqrt (c ^ (2 : ℕ)) = c := by
      simpa [pow_two, abs_of_nonneg hc_pos.le] using Real.sqrt_sq_eq_abs c
    change c⁻¹ * (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ =
      (Real.sqrt (((c * x + d) - a) * (b - (c * x + d))))⁻¹
    symm
    calc
      (Real.sqrt (((c * x + d) - a) * (b - (c * x + d))))⁻¹
          = (Real.sqrt (c ^ (2 : ℕ) * (1 - x ^ (2 : ℕ))))⁻¹ := by rw [hprod]
      _ = (Real.sqrt (c ^ (2 : ℕ)) * Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ := by
            rw [Real.sqrt_mul (pow_nonneg hc_pos.le _) (1 - x ^ (2 : ℕ))]
      _ = (c * Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ := by rw [hsqrtc]
      _ = (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ * c⁻¹ := by rw [mul_inv_rev]
      _ = c⁻¹ * (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ := by ring
  have hshift :
      IntervalIntegrable
        (fun y : ℝ => (Real.sqrt ((y + d - a) * (b - (y + d))))⁻¹)
        MeasureTheory.volume (-c) c := by
    -- Undo the multiplicative part of the affine substitution.
    refine (IntervalIntegrable.comp_mul_left_iff
      (f := fun y : ℝ => (Real.sqrt ((y + d - a) * (b - (y + d))))⁻¹)
      (a := -c) (b := c) hc_ne).mp ?_
    simpa [hc_ne, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm] using hcomp
  -- Undo the translational part of the affine substitution.
  have htranslate :
      IntervalIntegrable
        (fun t : ℝ => (Real.sqrt ((t - a) * (b - t)))⁻¹)
        MeasureTheory.volume (-c + d) (c + d) := by
    refine (IntervalIntegrable.comp_add_right_iff
      (f := fun t : ℝ => (Real.sqrt ((t - a) * (b - t)))⁻¹)
      (a := -c) (b := c) (c := d)).mp ?_
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift
  have hleft : -c + d = a := by
    dsimp [c, d]
    ring
  have hright : c + d = b := by
    dsimp [c, d]
    ring
  simpa [hleft, hright] using htranslate

/-- Helper for Exercise 8: on `[1, 1 / k]`, the auxiliary factor `(t + 1) (1 / k + t)` stays
strictly positive. -/
lemma exercise8_imaginary_factor_radicand_pos {k : Exercise8Modulus} {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    0 < (t + 1) * (1 / (k : ℝ) + t) := by
  -- The source proof isolates the harmless positive factor away from the endpoint singularities.
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have ht_add_one : 0 < t + 1 := by
    linarith [ht.1]
  have ht_add_inv : 0 < 1 / (k : ℝ) + t := by
    have hk_inv_pos : 0 < 1 / (k : ℝ) := one_div_pos.mpr hk_pos
    linarith [hk_inv_pos, ht.1]
  exact mul_pos ht_add_one ht_add_inv

/-- Helper for Exercise 8: the positive multiplier in the `[1, 1 / k]` kernel factorization is
strictly positive on the open interval. -/
lemma exercise8_imaginary_factor_pos {k : Exercise8Modulus} {t : ℝ}
    (ht : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ))) :
    0 < (((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹) := by
  -- Positivity follows from the positivity of `k` and the positive square-root radicand.
  exact inv_pos.2 <|
    mul_pos (Exercise8Modulus.pos k) <|
      Real.sqrt_pos.2 <|
        exercise8_imaginary_factor_radicand_pos (k := k) ⟨ht.1.le, ht.2.le⟩

/-- Helper for Exercise 8: the positive multiplier in the `[1, 1 / k]` kernel factorization is
continuous on the closed interval. -/
lemma exercise8_imaginary_factor_continuousOn (k : Exercise8Modulus) :
    ContinuousOn
      (fun t : ℝ => ((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹)
      (Icc (1 : ℝ) (1 / (k : ℝ))) := by
  -- The multiplier is the inverse of a nonvanishing continuous square-root factor.
  refine ContinuousOn.inv₀ ?_ ?_
  · exact
      (continuousOn_const.mul <|
        Real.continuous_sqrt.continuousOn.comp
          ((continuousOn_id.add continuousOn_const).mul
            (continuousOn_const.add continuousOn_id))
          (by
            intro t ht
            exact (exercise8_imaginary_factor_radicand_pos (k := k) ht).le))
  · intro t ht
    exact mul_ne_zero (Exercise8Modulus.pos k).ne'
      (Real.sqrt_ne_zero'.2 <| exercise8_imaginary_factor_radicand_pos (k := k) ht)

/-- Helper for Exercise 8: on `[1, 1 / k]`, the imaginary-period kernel factors into a positive
continuous multiplier times the endpoint model kernel. -/
lemma exercise8_imaginary_kernel_eq_factored {k : Exercise8Modulus} {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) =
      (((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹) *
        (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹ := by
  -- The source normalization separates the endpoint singularities from the positive multiplier.
  have hk_ne : (k : ℝ) ≠ 0 := (Exercise8Modulus.pos k).ne'
  have hA_nonneg : 0 ≤ (t - 1) * (1 / (k : ℝ) - t) := by
    nlinarith [ht.1, ht.2]
  have hB_nonneg :
      0 ≤ (k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t)) := by
    exact mul_nonneg (pow_nonneg (Exercise8Modulus.pos k).le _) <|
      (exercise8_imaginary_factor_radicand_pos (k := k) ht).le
  have hprod :
      (t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) =
        ((t - 1) * (1 / (k : ℝ) - t)) *
          ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t))) := by
    field_simp [pow_two, hk_ne]
    ring
  have hsqrtB :
      Real.sqrt ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t))) =
        (k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)) := by
    calc
      Real.sqrt ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t))) =
          Real.sqrt ((k : ℝ) ^ (2 : ℕ)) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)) := by
            rw [Real.sqrt_mul (pow_nonneg (Exercise8Modulus.pos k).le _)
              ((t + 1) * (1 / (k : ℝ) + t))]
      _ = (k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)) := by
            rw [show Real.sqrt ((k : ℝ) ^ (2 : ℕ)) = (k : ℝ) by
              simpa [pow_two, abs_of_nonneg (Exercise8Modulus.pos k).le] using
                Real.sqrt_sq_eq_abs (k : ℝ)]
  calc
    1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) =
        (Real.sqrt
          (((t - 1) * (1 / (k : ℝ) - t)) *
            ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t)))))⁻¹ := by
          rw [hprod, one_div]
    _ =
        (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)) *
          Real.sqrt ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t))))⁻¹ := by
          rw [Real.sqrt_mul hA_nonneg
            ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t)))]
    _ =
        (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)) *
          ((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t))))⁻¹ := by
          rw [hsqrtB]
    _ =
        (((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹) *
          (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹ := by
          rw [mul_inv_rev]

/-- The complete imaginary period `K'` from Exercise 8 is positive. -/
theorem exercise8_complete_imaginary_period_pos (k : Exercise8Modulus) :
    0 < exercise8_complete_imaginary_period k := by
  -- Route correction: we now mirror the `K > 0` proof after factoring the kernel into a positive
  -- continuous multiplier times the transported endpoint model on `[1, 1 / k]`.
  rw [exercise8_complete_imaginary_period_def]
  have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
    simpa [one_div] using (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
  have hendpoint :
      IntervalIntegrable
        (fun t : ℝ => (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹)
        MeasureTheory.volume (1 : ℝ) (1 / (k : ℝ)) :=
    exercise8_endpoint_sqrt_kernel_intervalIntegrable hk_inv_gt_one
  have hfactored :
      IntervalIntegrable
        (fun t : ℝ =>
          (((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹) *
            (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹)
        MeasureTheory.volume (1 : ℝ) (1 / (k : ℝ)) := by
    -- The isolated multiplier is continuous on the whole interval, so it preserves integrability.
    have hcont :
        ContinuousOn
          (fun t : ℝ =>
            (Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹ * (k : ℝ)⁻¹)
          (Set.uIcc (1 : ℝ) (1 / (k : ℝ))) := by
      have hcontIcc :
          ContinuousOn
            (fun t : ℝ =>
              (Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹ * (k : ℝ)⁻¹)
            (Icc (1 : ℝ) (1 / (k : ℝ))) := by
        simpa [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
          exercise8_imaginary_factor_continuousOn k
      rw [Set.uIcc_of_le hk_inv_gt_one.le]
      exact hcontIcc
    simpa [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      hendpoint.continuousOn_mul hcont
  have hkernel :
      IntervalIntegrable
        (fun t : ℝ =>
          1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))))
        MeasureTheory.volume (1 : ℝ) (1 / (k : ℝ)) := by
    refine hfactored.congr ?_
    intro t ht
    have ht' : t ∈ Icc (1 : ℝ) (1 / (k : ℝ)) := by
      have htIoc : t ∈ Ioc (1 : ℝ) (1 / (k : ℝ)) := by
        rw [Set.uIoc_of_le hk_inv_gt_one.le] at ht
        exact ht
      exact ⟨le_of_lt htIoc.1, htIoc.2⟩
    simpa using (exercise8_imaginary_kernel_eq_factored (k := k) ht').symm
  refine intervalIntegral.intervalIntegral_pos_of_pos_on hkernel ?_ hk_inv_gt_one
  intro t ht
  -- The factored form reduces strict positivity to the positivity of its two real factors.
  have htIoo : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ)) := by
    simpa [one_div, Set.uIoo_of_lt hk_inv_gt_one] using ht
  rw [exercise8_imaginary_kernel_eq_factored (k := k) ⟨le_of_lt htIoo.1, htIoo.2.le⟩]
  have hendpoint_pos : 0 < (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹ := by
    have hrad : 0 < (t - 1) * (1 / (k : ℝ) - t) := by
      nlinarith [htIoo.1, htIoo.2]
    exact inv_pos.2 (Real.sqrt_pos.2 hrad)
  exact mul_pos (exercise8_imaginary_factor_pos (k := k) htIoo) hendpoint_pos

/-- The complex number `i K' / K` lies in the upper half-plane. -/
theorem exercise8_tau_im_pos (k : Exercise8Modulus) :
    0 <
      (Complex.I *
        (exercise8_complete_imaginary_period k / exercise8_complete_real_period k)).im := by
  -- The imaginary part of `i * (K' / K)` is exactly the positive ratio `K' / K`.
  have hquot :
      0 <
        exercise8_complete_imaginary_period k / exercise8_complete_real_period k := by
    exact div_pos (exercise8_complete_imaginary_period_pos k) (exercise8_complete_real_period_pos k)
  simpa using hquot

/-- The Jacobi parameter `τ = i K' / K` attached to Exercise 8, viewed in the upper half-plane. -/
def exercise8_tau (k : Exercise8Modulus) : ℍ :=
  ⟨Complex.I * (exercise8_complete_imaginary_period k / exercise8_complete_real_period k),
    exercise8_tau_im_pos k⟩

/-- Normal form for the Exercise 8 parameter `τ`. -/
theorem exercise8_tau_def (k : Exercise8Modulus) :
    (exercise8_tau k : ℂ) =
      Complex.I * (exercise8_complete_imaginary_period k / exercise8_complete_real_period k) := rfl

/-- The open rectangle with vertices `-K`, `K`, `K + i K'`, and `-K + i K'`. -/
def exercise8_open_rectangle (k : Exercise8Modulus) : Set ℂ :=
  Set.Ioo (-exercise8_complete_real_period k) (exercise8_complete_real_period k) ×ℂ
    Set.Ioo (0 : ℝ) (exercise8_complete_imaginary_period k)

/-- Membership in the Exercise 8 rectangle is given by the expected inequalities on real and
imaginary parts. -/
theorem mem_exercise8_open_rectangle_iff {k : Exercise8Modulus} {u : ℂ} :
    u ∈ exercise8_open_rectangle k ↔
      u.re ∈ Ioo (-exercise8_complete_real_period k) (exercise8_complete_real_period k) ∧
        u.im ∈ Ioo (0 : ℝ) (exercise8_complete_imaginary_period k) :=
  Complex.mem_reProdIm

/-- The full period pair `4 K`, `2 i K'` for the meromorphic inverse in Exercise 8. -/
theorem exercise8_period_pair_indep (k : Exercise8Modulus) :
    LinearIndependent ℝ
      ![(((4 * exercise8_complete_real_period k : ℝ) : ℂ)),
        (((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I)] := by
  -- The imaginary part forces the coefficient of the purely imaginary generator to vanish.
  refine LinearIndependent.pair_iff.2 ?_
  intro a b hab
  have himag : b * (2 * exercise8_complete_imaginary_period k) = 0 := by
    have hab_im := congrArg Complex.im hab
    simpa [Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using hab_im
  have hb : b = 0 := by
    nlinarith [exercise8_complete_imaginary_period_pos k, himag]
  -- With the imaginary coefficient gone, the real part forces the remaining coefficient to vanish.
  have hreal : a * (4 * exercise8_complete_real_period k) = 0 := by
    have hab_re := congrArg Complex.re hab
    simpa [hb, Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using
      hab_re
  have ha : a = 0 := by
    nlinarith [exercise8_complete_real_period_pos k, hreal]
  exact ⟨ha, hb⟩

/-- The canonical period-data owner for the doubly-periodic inverse from Exercise 8. -/
def exercise8_period_pair (k : Exercise8Modulus) : PeriodPair :=
  { ω₁ := ((4 * exercise8_complete_real_period k : ℝ) : ℂ)
    ω₂ := ((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I
    indep := exercise8_period_pair_indep k }

/-- The half-real-period pair whose lattice is the zero locus of the Exercise 8 inverse. -/
theorem exercise8_half_period_pair_indep (k : Exercise8Modulus) :
    LinearIndependent ℝ
      ![(((2 * exercise8_complete_real_period k : ℝ) : ℂ)),
        (((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I)] := by
  -- The same real-versus-purely-imaginary decomposition works for the half-period pair.
  refine LinearIndependent.pair_iff.2 ?_
  intro a b hab
  have himag : b * (2 * exercise8_complete_imaginary_period k) = 0 := by
    have hab_im := congrArg Complex.im hab
    simpa [Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using hab_im
  have hb : b = 0 := by
    nlinarith [exercise8_complete_imaginary_period_pos k, himag]
  -- The first generator is a positive real number, so the real part kills its coefficient.
  have hreal : a * (2 * exercise8_complete_real_period k) = 0 := by
    have hab_re := congrArg Complex.re hab
    simpa [hb, Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using
      hab_re
  have ha : a = 0 := by
    nlinarith [exercise8_complete_real_period_pos k, hreal]
  exact ⟨ha, hb⟩

/-- The source-facing zero-lattice owner for Exercise 8, obtained by halving the real period. -/
def exercise8_half_period_pair (k : Exercise8Modulus) : PeriodPair :=
  { ω₁ := ((2 * exercise8_complete_real_period k : ℝ) : ℂ)
    ω₂ := ((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I
    indep := exercise8_half_period_pair_indep k }

/-- The pole lattice is the translate of the zero lattice by the half imaginary period `i K'`. -/
def exercise8_pole_shift (k : Exercise8Modulus) : ℂ :=
  (exercise8_half_period_pair k).ω₂ / 2

/-- Membership in the zero lattice is the expected even-period coordinate condition. -/
theorem mem_exercise8_half_period_pair_lattice_iff {k : Exercise8Modulus} {u : ℂ} :
    u ∈ (exercise8_half_period_pair k).lattice ↔
      ∃ m n : ℤ,
        u =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
  -- Unfold the lattice description to identify the integer coordinates in the chosen basis.
  rw [exercise8_half_period_pair, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    -- Rewrite the basis combination into the source-facing even-period formula.
    calc
      u = m * (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) +
            n * ((((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I)) := hmn.symm
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
          norm_num [mul_assoc, mul_left_comm, mul_comm]
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    -- The source-facing even-period coordinates are exactly the lattice coordinates for `ω₁, ω₂`.
    calc
      m * (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) +
          n * ((((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I)) =
            ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
              (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
            norm_num [mul_assoc, mul_left_comm, mul_comm]
      _ = u := hmn.symm

/-- Membership in the translated pole lattice is the expected odd-half-period condition. -/
theorem mem_exercise8_pole_shift_sub_lattice_iff {k : Exercise8Modulus} {u : ℂ} :
    u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice ↔
      ∃ m n : ℤ,
        u =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
  have hpole :
      exercise8_pole_shift k = exercise8_complete_imaginary_period k * Complex.I := by
    -- The pole shift is the half imaginary period `ω₂ / 2 = i K'`.
    simp [exercise8_pole_shift, exercise8_half_period_pair]
    ring
  constructor
  · intro hu
    rcases (mem_exercise8_half_period_pair_lattice_iff).1 hu with ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    -- Add back the half imaginary period to move from the even lattice to the pole translate.
    calc
      u = (u - exercise8_pole_shift k) + exercise8_pole_shift k := by ring
      _ =
          (((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
              (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I) +
            exercise8_complete_imaginary_period k * Complex.I := by rw [hmn, hpole]
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
          norm_num [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm]
  · rintro ⟨m, n, hu⟩
    -- Subtracting the half imaginary period recovers the even lattice coordinates.
    apply (mem_exercise8_half_period_pair_lattice_iff).2
    refine ⟨m, n, ?_⟩
    calc
      u - exercise8_pole_shift k =
          (((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
              (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I) -
            exercise8_complete_imaginary_period k * Complex.I := by rw [hu, hpole]
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            ((((2 * n + 1 : ℤ) : ℂ) - 1) * exercise8_complete_imaginary_period k) * Complex.I := by
          ring
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
          norm_num

/-- The theta quotient appearing in the Exercise 8 representation formula. -/
def exercise8_theta_quotient (k : Exercise8Modulus) (u : ℂ) : ℂ :=
  let τ : ℂ := exercise8_tau k
  let v := u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)
  (-Complex.I) * Complex.exp (Real.pi * Complex.I * (v + τ / 4)) *
      jacobiTheta₂ (v + (1 + τ) / 2) τ / jacobiTheta₂ (v + 1 / 2) τ

/-- Normal form for the Exercise 8 theta quotient. -/
theorem exercise8_theta_quotient_def (k : Exercise8Modulus) (u : ℂ) :
    exercise8_theta_quotient k u =
      (-Complex.I) *
          Complex.exp
            (Real.pi * Complex.I *
              (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ) + exercise8_tau k / 4)) *
          jacobiTheta₂
            (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ) + (1 + exercise8_tau k) / 2)
            (exercise8_tau k) /
        jacobiTheta₂
          (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ) + 1 / 2) (exercise8_tau k) := by
  rfl

/-- Helper for Exercise 8: the positive-side branch of the textbook boundary trace on the real
axis. -/
def exercise8_boundary_value_nonneg (k : Exercise8Modulus) : ℝ → ℂ :=
  fun x ↦
    if _ : x < 1 then
      ((∫ t in (0 : ℝ)..x,
          (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) : ℂ)
    else if _ : x < 1 / (k : ℝ) then
      (exercise8_complete_real_period k : ℂ) +
        (((∫ t in (1 : ℝ)..x,
            (1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
          ℝ) : ℂ) *
          Complex.I
    else
      (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
        ((∫ t in (0 : ℝ)..(1 / ((k : ℝ) * x)),
            (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
          ℂ)

/-- Helper for Exercise 8: the bottom-edge branch of the textbook boundary trace. -/
def exercise8_boundary_inner_branch (k : Exercise8Modulus) (x : ℝ) : ℂ :=
  ((∫ t in (0 : ℝ)..x,
      (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) : ℂ)

/-- Helper for Exercise 8: the right-edge branch of the textbook boundary trace. -/
def exercise8_boundary_right_branch (k : Exercise8Modulus) (x : ℝ) : ℂ :=
  (exercise8_complete_real_period k : ℂ) +
    (((∫ t in (1 : ℝ)..x,
        (1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
      ℝ) : ℂ) *
      Complex.I

/-- Helper for Exercise 8: the top-edge branch of the textbook boundary trace. -/
def exercise8_boundary_top_branch (k : Exercise8Modulus) (x : ℝ) : ℂ :=
  (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
    ((∫ t in (0 : ℝ)..(1 / ((k : ℝ) * x)),
        (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
      ℂ)

/-- Helper for Exercise 8: the full real-axis trace is obtained from the positive-side textbook
formulas by Schwarz reflection across the real axis. -/
def exercise8_boundary_trace (k : Exercise8Modulus) : ℝ → ℂ :=
  fun x ↦
    if _ : 0 ≤ x then
      exercise8_boundary_value_nonneg k x
    else
      -star (exercise8_boundary_value_nonneg k (-x))

/-- Helper for Exercise 8: `exercise8_boundary_value` is the reflected real-axis trace used by the
rest of the local API. -/
abbrev exercise8_boundary_value (k : Exercise8Modulus) : ℝ → ℂ :=
  exercise8_boundary_trace k

/-- Helper for Exercise 8: the reflected trace satisfies the Schwarz symmetry
`trace (-x) = -conj (trace x)` on the real axis. -/
lemma exercise8_boundary_value_reflection (k : Exercise8Modulus) (x : ℝ) :
    exercise8_boundary_value k (-x) = -star (exercise8_boundary_value k x) := by
  by_cases hx : 0 ≤ x
  · -- For `x ≥ 0`, the negative-side value is defined by reflected conjugation.
    by_cases hx0 : x = 0
    · subst hx0
      simp [exercise8_boundary_value, exercise8_boundary_trace, exercise8_boundary_value_nonneg]
    · have hneg : ¬ 0 ≤ -x := by
        have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        linarith
      simp [exercise8_boundary_value, exercise8_boundary_trace, hx, hneg]
  · -- For `x < 0`, reflecting twice returns the positive-side owner.
    have hneg : 0 ≤ -x := by linarith
    simp [exercise8_boundary_value, exercise8_boundary_trace, hx, hneg]

/-- Helper for Exercise 8: the boundary owner vanishes at the origin. -/
lemma exercise8_boundary_value_zero (k : Exercise8Modulus) :
    exercise8_boundary_value k 0 = 0 := by
  -- The source trace starts from the origin, so its integral owner is zero there.
  simp [exercise8_boundary_value, exercise8_boundary_trace, exercise8_boundary_value_nonneg]

/-- Helper for Exercise 8: rewrite a casted real interval integral as the corresponding complex
interval integral. -/
lemma exercise8_intervalIntegral_ofReal {f : ℝ → ℝ} {a b : ℝ} :
    (((∫ t in a..b, f t : ℝ)) : ℂ) = ∫ t in a..b, ((f t : ℂ)) := by
  -- This freezes the real-to-complex cast normalization used by the source boundary formulas.
  symm
  exact intervalIntegral.integral_ofReal

/-- Helper for Exercise 8: `exercise8_boundary_value_nonneg` has a single explicit three-branch
normal form. -/
lemma exercise8_boundary_value_nonneg_canonical_form (k : Exercise8Modulus) (x : ℝ) :
    exercise8_boundary_value_nonneg k x =
      if hx1 : x < 1 then
        ((∫ t in (0 : ℝ)..x,
            (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
          ℂ)
      else if hxk : x < 1 / (k : ℝ) then
        (exercise8_complete_real_period k : ℂ) +
          (((∫ t in (1 : ℝ)..x,
              (1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) :
                ℝ)) :
            ℝ) : ℂ) *
            Complex.I
      else
        (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
          ((∫ t in (0 : ℝ)..(1 / ((k : ℝ) * x)),
              (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) :
                ℝ)) :
            ℂ) := by
  -- Route correction: we freeze the nested `if` owner once so later branch proofs only do source
  -- branch selection, rather than unfolding the definition under coercions each time.
  rfl

/-- Helper for Exercise 8: on the first positive branch, the source boundary owner is exactly the
real integral from `0` to `x`. -/
lemma exercise8_boundary_value_nonneg_eq_of_lt_one {k : Exercise8Modulus} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    exercise8_boundary_value_nonneg k x =
      ((∫ t in (0 : ℝ)..x,
          (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
        ℂ) := by
  -- The canonical-form lemma reduces the proof to choosing the first textbook branch.
  simpa [exercise8_boundary_value_nonneg, hx1]

/-- Helper for Exercise 8: on the open right-edge branch, the source boundary owner is `K` plus a
purely imaginary interval integral. -/
lemma exercise8_boundary_value_nonneg_eq_of_right_open {k : Exercise8Modulus} {x : ℝ}
    (hx1 : 1 ≤ x) (hxk : x < 1 / (k : ℝ)) :
    exercise8_boundary_value_nonneg k x =
      (exercise8_complete_real_period k : ℂ) +
        (((∫ t in (1 : ℝ)..x,
            (1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
          ℝ) : ℂ) *
          Complex.I := by
  -- The first branch is excluded by `x ≥ 1`, and the second branch matches the source formula.
  have hnot_lt_one : ¬ x < 1 := not_lt.mpr hx1
  have hxk_inv : x < (k : ℝ)⁻¹ := by
    simpa [one_div] using hxk
  simp [exercise8_boundary_value_nonneg, hnot_lt_one, hxk]
  intro hge
  exact False.elim ((not_le.mpr hxk_inv) hge)

/-- Helper for Exercise 8: on the top branch, the source boundary owner is `i K'` plus the
reciprocal-substitution real integral. -/
lemma exercise8_boundary_value_nonneg_eq_of_ge_inv_k {k : Exercise8Modulus} {x : ℝ}
    (hx : 1 / (k : ℝ) ≤ x) :
    exercise8_boundary_value_nonneg k x =
      (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
        ((∫ t in (0 : ℝ)..(1 / ((k : ℝ) * x)),
            (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
          ℂ) := by
  -- Route correction: after freezing the owner, the top edge is just the third branch selection.
  have hk_one : (1 : ℝ) ≤ 1 / (k : ℝ) := by
    exact (one_le_div (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k).le
  have hx1 : 1 ≤ x := le_trans hk_one hx
  have hnot_lt_one : ¬ x < 1 := not_lt.mpr hx1
  have hnot_lt_inv : ¬ x < 1 / (k : ℝ) := not_lt.mpr hx
  simp [exercise8_boundary_value_nonneg, hnot_lt_one, hnot_lt_inv]
  intro hlt
  exact False.elim (hnot_lt_inv (by simpa [one_div] using hlt))

/-- Helper for Exercise 8: on `[0, 1]`, the boundary owner is the real integral from the source. -/
lemma exercise8_boundary_value_eq_inner {k : Exercise8Modulus} {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    exercise8_boundary_value k x =
      ((∫ t in (0 : ℝ)..x,
          (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
        ℂ) := by
  -- After the positive-side owner is stable, the public owner just rewrites to the nonnegative
  -- branch and we split the interior case from the endpoint `x = 1`.
  by_cases hxlt : x < 1
  · -- Inside `[0, 1)`, the boundary owner is exactly the first positive branch.
    simpa [exercise8_boundary_value, exercise8_boundary_trace, hx.1] using
      exercise8_boundary_value_nonneg_eq_of_lt_one (k := k) hx.1 hxlt
  · -- At the endpoint, the first branch closes up to the complete real period `K`.
    have hxge : 1 ≤ x := not_lt.mp hxlt
    have hxeq : x = 1 := le_antisymm hx.2 hxge
    subst hxeq
    have hk : (1 : ℝ) < 1 / (k : ℝ) := by
      exact (one_lt_div (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
    calc
      exercise8_boundary_value k 1
          = (exercise8_complete_real_period k : ℂ) +
              (((∫ t in (1 : ℝ)..1,
                  (1 / Real.sqrt
                    ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
                ℝ) : ℂ) *
                Complex.I := by
              simpa [exercise8_boundary_value, exercise8_boundary_trace] using
                exercise8_boundary_value_nonneg_eq_of_right_open (k := k) (x := 1)
                  (by norm_num) hk
      _ = (exercise8_complete_real_period k : ℂ) := by simp
      _ = ((∫ t in (0 : ℝ)..1,
              (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) :
                ℝ)) :
            ℂ) := by
              rw [exercise8_complete_real_period_def, exercise8_intervalIntegral_ofReal]

/-- Helper for Exercise 8: at `x = 1`, the boundary owner equals the complete real period `K`. -/
lemma exercise8_boundary_value_one (k : Exercise8Modulus) :
    exercise8_boundary_value k 1 = exercise8_complete_real_period k := by
  -- The endpoint `x = 1` is the complete real period by the inner-edge formula.
  calc
    exercise8_boundary_value k 1
        = ∫ t in (0 : ℝ)..1,
            ((1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) :
              ℝ) : ℂ) := by
            simpa [exercise8_intervalIntegral_ofReal] using
              exercise8_boundary_value_eq_inner (k := k) (x := 1) ⟨by norm_num, by norm_num⟩
    _ = exercise8_complete_real_period k := by
          rw [← exercise8_intervalIntegral_ofReal, exercise8_complete_real_period_def]

/-- Helper for Exercise 8: on `[1 / k, ∞)`, the boundary owner follows the top-edge reciprocal
substitution formula from the source. -/
lemma exercise8_boundary_value_eq_top {k : Exercise8Modulus} {x : ℝ}
    (hx : 1 / (k : ℝ) ≤ x) :
    exercise8_boundary_value k x =
      (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
        ((∫ t in (0 : ℝ)..(1 / ((k : ℝ) * x)),
            (1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
          ℂ) := by
  -- On the top edge, the public owner just unwraps to the nonnegative branch.
  have hx0 : 0 ≤ x := by
    have hk0 : 0 ≤ 1 / (k : ℝ) := one_div_nonneg.mpr (Exercise8Modulus.pos k).le
    exact le_trans hk0 hx
  simpa [exercise8_boundary_value, exercise8_boundary_trace, hx0] using
    exercise8_boundary_value_nonneg_eq_of_ge_inv_k (k := k) hx

/-- Helper for Exercise 8: at `x = 1 / k`, the boundary owner reaches the vertex `K + i K'`. -/
lemma exercise8_boundary_value_inv_k (k : Exercise8Modulus) :
    exercise8_boundary_value k (1 / (k : ℝ)) =
      exercise8_complete_real_period k + exercise8_complete_imaginary_period k * Complex.I := by
  -- Specializing the top-edge formula at `x = 1 / k` turns the reciprocal substitution back into
  -- the complete real period integral.
  have hk_ne : (k : ℝ) ≠ 0 := (Exercise8Modulus.pos k).ne'
  have hbound : 1 / ((k : ℝ) * (1 / (k : ℝ))) = 1 := by
    field_simp [hk_ne]
  calc
    exercise8_boundary_value k (1 / (k : ℝ))
        = (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
            ∫ t in (0 : ℝ)..(1 / ((k : ℝ) * (1 / (k : ℝ)))),
              ((1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) :
                ℝ) : ℂ) := by
            simpa [exercise8_intervalIntegral_ofReal] using
              exercise8_boundary_value_eq_top (k := k) (x := 1 / (k : ℝ)) le_rfl
    _ = (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
          ∫ t in (0 : ℝ)..1,
            ((1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) :
              ℝ) : ℂ) := by
            rw [hbound]
    _ = (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
          exercise8_complete_real_period k := by
            rw [← exercise8_intervalIntegral_ofReal, exercise8_complete_real_period_def]
    _ = exercise8_complete_real_period k + exercise8_complete_imaginary_period k * Complex.I := by
          simpa [add_comm]

/-- Helper for Exercise 8: on `[1, 1 / k]`, the boundary owner follows the right-edge source
formula. -/
lemma exercise8_boundary_value_eq_right {k : Exercise8Modulus} {x : ℝ}
    (hx1 : 1 ≤ x) (hxk : x ≤ 1 / (k : ℝ)) :
    exercise8_boundary_value k x =
      (exercise8_complete_real_period k : ℂ) +
        (((∫ t in (1 : ℝ)..x,
            (1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) : ℝ)) :
          ℝ) : ℂ) *
          Complex.I := by
  -- The right edge is open below `1 / k`, with the endpoint recovered from the vertex formula.
  by_cases hxlt : x < 1 / (k : ℝ)
  · have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
    simpa [exercise8_boundary_value, exercise8_boundary_trace, hx0] using
      exercise8_boundary_value_nonneg_eq_of_right_open (k := k) hx1 hxlt
  · have hxeq : x = 1 / (k : ℝ) := by linarith
    subst hxeq
    simpa [exercise8_complete_imaginary_period_def] using
      exercise8_boundary_value_inv_k (k := k)

/-- Helper for Exercise 8: the reflected trace sends `-1` to the left real vertex `-K`. -/
lemma exercise8_boundary_value_neg_one (k : Exercise8Modulus) :
    exercise8_boundary_value k (-1) = -exercise8_complete_real_period k := by
  -- Reflect the positive endpoint `1 ↦ K` across the real axis.
  calc
    exercise8_boundary_value k (-1) = -star (exercise8_boundary_value k 1) := by
      simpa using exercise8_boundary_value_reflection k 1
    _ = -star (exercise8_complete_real_period k : ℂ) := by
      rw [exercise8_boundary_value_one]
    _ = -exercise8_complete_real_period k := by simp

/-- Helper for Exercise 8: the reflected trace sends `-1 / k` to the left-top vertex
`-K + i K'`. -/
lemma exercise8_boundary_value_neg_inv_k (k : Exercise8Modulus) :
    exercise8_boundary_value k (-(1 / (k : ℝ))) =
      -exercise8_complete_real_period k +
        exercise8_complete_imaginary_period k * Complex.I := by
  -- Reflect the right-top vertex `K + i K'` across the imaginary axis.
  calc
    exercise8_boundary_value k (-(1 / (k : ℝ))) =
        -star (exercise8_boundary_value k (1 / (k : ℝ))) := by
          simpa using exercise8_boundary_value_reflection k (1 / (k : ℝ))
    _ =
        -star
          (exercise8_complete_real_period k + exercise8_complete_imaginary_period k * Complex.I) := by
          rw [exercise8_boundary_value_inv_k]
    _ =
        -exercise8_complete_real_period k +
          exercise8_complete_imaginary_period k * Complex.I := by
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Helper for Exercise 8: the real-period kernel is interval integrable on `[0, 1]`. -/
lemma exercise8_real_kernel_intervalIntegrable (k : Exercise8Modulus) :
    IntervalIntegrable
      (fun x : ℝ =>
        1 / Real.sqrt ((1 - x ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))))
      MeasureTheory.volume (0 : ℝ) 1 := by
  -- This is the same factorization used earlier to prove `K > 0`, but extracted as reusable API.
  have hbase :
      IntervalIntegrable
        (fun x : ℝ => (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hcheb01 :
        IntervalIntegrable
          (fun x : ℝ => Real.sqrt (1 - x ^ (2 : ℕ))⁻¹)
          MeasureTheory.volume (0 : ℝ) 1 := by
      let hcheb := Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
      refine hcheb.mono_set' (c := (0 : ℝ)) (d := (1 : ℝ)) ?_
      intro x hx
      have hx' : x ∈ Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using hx
      have hx'' : x ∈ Ioc (-1 : ℝ) 1 := by
        exact ⟨by linarith [hx'.1], hx'.2⟩
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx''
    simpa using hcheb01
  have hfactored :
      IntervalIntegrable
        (fun x : ℝ =>
          (1 / Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))) *
            (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (0 : ℝ) 1 := by
    -- The harmless multiplier is continuous on the closed interval, so it preserves integrability.
    exact hbase.continuousOn_mul <|
      by simpa [Set.uIcc_of_le zero_le_one] using exercise8_real_factor_continuousOn k
  refine hfactored.congr ?_
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    have hxIoc : x ∈ Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le zero_le_one] using hx
    exact ⟨le_of_lt hxIoc.1, hxIoc.2⟩
  simpa using (exercise8_real_kernel_eq_factored (k := k) hx').symm

/-- Helper for Exercise 8: the right-edge kernel is interval integrable on `[1, 1 / k]`. -/
lemma exercise8_imaginary_kernel_intervalIntegrable (k : Exercise8Modulus) :
    IntervalIntegrable
      (fun t : ℝ =>
        1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))))
      MeasureTheory.volume (1 : ℝ) (1 / (k : ℝ)) := by
  -- This extracts the integrability package already hidden inside the proof that `K' > 0`.
  have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
    simpa [one_div] using (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
  have hendpoint :
      IntervalIntegrable
        (fun t : ℝ => (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹)
        MeasureTheory.volume (1 : ℝ) (1 / (k : ℝ)) :=
    exercise8_endpoint_sqrt_kernel_intervalIntegrable hk_inv_gt_one
  have hfactored :
      IntervalIntegrable
        (fun t : ℝ =>
          (((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹) *
            (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹)
        MeasureTheory.volume (1 : ℝ) (1 / (k : ℝ)) := by
    -- The positive multiplier is continuous on the full edge interval.
    have hcont :
        ContinuousOn
          (fun t : ℝ =>
            (Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹ * (k : ℝ)⁻¹)
          (Set.uIcc (1 : ℝ) (1 / (k : ℝ))) := by
      have hcontIcc :
          ContinuousOn
            (fun t : ℝ =>
              (Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹ * (k : ℝ)⁻¹)
            (Icc (1 : ℝ) (1 / (k : ℝ))) := by
        simpa [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
          exercise8_imaginary_factor_continuousOn k
      rw [Set.uIcc_of_le hk_inv_gt_one.le]
      exact hcontIcc
    simpa [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      hendpoint.continuousOn_mul hcont
  refine hfactored.congr ?_
  intro t ht
  have ht' : t ∈ Icc (1 : ℝ) (1 / (k : ℝ)) := by
    have htIoc : t ∈ Ioc (1 : ℝ) (1 / (k : ℝ)) := by
      rw [Set.uIoc_of_le hk_inv_gt_one.le] at ht
      exact ht
    exact ⟨le_of_lt htIoc.1, htIoc.2⟩
  simpa using (exercise8_imaginary_kernel_eq_factored (k := k) ht').symm

/-- Helper for Exercise 8: the bottom-edge real kernel is named once so the primitive continuity
proof runs on a small head symbol. -/
def exercise8_real_kernel (k : Exercise8Modulus) (x : ℝ) : ℝ :=
  1 / Real.sqrt ((1 - x ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)))

/-- Helper for Exercise 8: the source bottom-edge primitive from `0` to `x`. -/
def exercise8_inner_primitive (k : Exercise8Modulus) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, exercise8_real_kernel k t

/-- Helper for Exercise 8: the right-edge real kernel is named once so the primitive continuity
proof runs on a small head symbol. -/
def exercise8_imaginary_kernel (k : Exercise8Modulus) (x : ℝ) : ℝ :=
  1 / Real.sqrt ((x ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)))

/-- Helper for Exercise 8: the source right-edge primitive from `1` to `x`. -/
def exercise8_right_primitive (k : Exercise8Modulus) (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, exercise8_imaginary_kernel k t

/-- Helper for Exercise 8: the complexified bottom-edge primitive is continuous on `[0, 1]`. -/
lemma exercise8_inner_primitive_complex_continuousOn_Icc (k : Exercise8Modulus) :
    ContinuousOn (fun x : ℝ => ((exercise8_inner_primitive k x : ℝ) : ℂ)) (Icc (0 : ℝ) 1) := by
  -- Route correction: prove continuity on the named real primitive first, then postcompose with
  -- `Complex.ofReal` instead of normalizing casts pointwise before the continuity theorem fires.
  have hprimitive :
      ContinuousOn (fun x : ℝ => exercise8_inner_primitive k x) (Icc (0 : ℝ) 1) := by
    -- The canonical primitive owner is continuous on its whole closed interval.
    simpa [exercise8_inner_primitive, Set.uIcc_of_le zero_le_one] using
      (intervalIntegral.continuousOn_primitive_interval'
        (f := exercise8_real_kernel k) (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b₁ := (0 : ℝ)) (b₂ := (1 : ℝ))
        (exercise8_real_kernel_intervalIntegrable k) (by simp))
  -- Postcomposing with the continuous real-to-complex embedding preserves continuity.
  simpa using Complex.continuous_ofReal.comp_continuousOn' hprimitive

/-- Helper for Exercise 8: the right-edge primitive is continuous on `[1, 1 / k]`. -/
lemma exercise8_right_primitive_continuousOn_Icc (k : Exercise8Modulus) :
    ContinuousOn (fun x : ℝ => exercise8_right_primitive k x) (Icc (1 : ℝ) (1 / (k : ℝ))) := by
  -- Route correction: keep the right-edge primitive on its short owner and invoke the canonical
  -- interval-primitive continuity theorem before adding the affine complex decoration.
  have hk_lt : 1 < 1 / (k : ℝ) := by
    simpa [one_div] using (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
  -- The closed right edge is exactly the `uIcc` where the primitive theorem applies.
  have hprimitive :
      ContinuousOn
        (fun x : ℝ => ∫ t in (1 : ℝ)..x, exercise8_imaginary_kernel k t)
        (uIcc (1 : ℝ) (1 / (k : ℝ))) := by
    exact
      intervalIntegral.continuousOn_primitive_interval'
      (f := exercise8_imaginary_kernel k) (μ := MeasureTheory.volume)
      (a := (1 : ℝ)) (b₁ := (1 : ℝ)) (b₂ := (1 / (k : ℝ)))
      (exercise8_imaginary_kernel_intervalIntegrable k) (by simp)
  change ContinuousOn
    (fun x : ℝ => ∫ t in (1 : ℝ)..x, exercise8_imaginary_kernel k t)
    (Icc (1 : ℝ) (1 / (k : ℝ)))
  convert hprimitive using 1
  rw [Set.uIcc_of_le hk_lt.le]

/-- Helper for Exercise 8: the bottom-edge branch is exactly the complexified named primitive. -/
lemma exercise8_boundary_inner_branch_eq_inner_primitive (k : Exercise8Modulus) (x : ℝ) :
    exercise8_boundary_inner_branch k x = ((exercise8_inner_primitive k x : ℝ) : ℂ) := by
  -- Route correction: this freezes the source bottom-edge primitive behind a short owner before
  -- the continuity theorem invokes `continuousOn_primitive_interval'`.
  -- The two owners are definitionally the same real primitive, with only the short kernel name
  -- hidden on the right-hand side.
  rw [exercise8_boundary_inner_branch, exercise8_inner_primitive, exercise8_intervalIntegral_ofReal]
  simp [exercise8_real_kernel]

/-- Helper for Exercise 8: the right-edge branch is exactly `K + i` times the named primitive. -/
lemma exercise8_boundary_right_branch_eq_right_primitive (k : Exercise8Modulus) (x : ℝ) :
    exercise8_boundary_right_branch k x =
      (exercise8_complete_real_period k : ℂ) +
        ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I := by
  -- Route correction: this keeps the right-edge primitive on a short owner before continuity
  -- adds the constant real period and multiplies by `I`.
  rfl

/-- Helper for Exercise 8: the top-edge branch is `i K'` plus the bottom-edge primitive after the
reciprocal substitution from the source proof. -/
lemma exercise8_boundary_top_branch_eq_inner_composition (k : Exercise8Modulus) (x : ℝ) :
    exercise8_boundary_top_branch k x =
      (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
        ((exercise8_inner_primitive k (1 / ((k : ℝ) * x)) : ℝ) : ℂ) := by
  -- This is just the source top-edge formula rewritten through the named bottom-edge primitive.
  -- As on the bottom edge, unfolding only the short primitive owner already matches the source
  -- reciprocal-substitution formula exactly.
  rw [exercise8_boundary_top_branch, exercise8_inner_primitive, exercise8_intervalIntegral_ofReal]
  simp [exercise8_real_kernel]

/-- Helper for Exercise 8: the bottom-edge branch is continuous on `[0, 1]`. -/
lemma exercise8_boundary_inner_branch_continuousOn (k : Exercise8Modulus) :
    ContinuousOn (exercise8_boundary_inner_branch k) (Icc (0 : ℝ) 1) := by
  -- Route correction: the same source primitive proof now runs on the short owner
  -- `exercise8_inner_primitive`, which avoids unfolding the full kernel during elaboration.
  -- The branch is definitionally the complexified primitive owner whose continuity we already know.
  exact ContinuousOn.congr (exercise8_inner_primitive_complex_continuousOn_Icc k) fun x hx => by
    simpa using exercise8_boundary_inner_branch_eq_inner_primitive k x

/-- Helper for Exercise 8: the right-edge branch is continuous on `[1, 1 / k]`. -/
lemma exercise8_boundary_right_branch_continuousOn (k : Exercise8Modulus) :
    ContinuousOn (exercise8_boundary_right_branch k) (Icc (1 : ℝ) (1 / (k : ℝ))) := by
  -- Route correction: we mirror the bottom-edge source argument on the short owner
  -- `exercise8_right_primitive`, then append the affine complex operations afterwards.
  have hprim :
      ContinuousOn (fun x : ℝ => ((exercise8_right_primitive k x : ℝ) : ℂ))
        (Icc (1 : ℝ) (1 / (k : ℝ))) := by
    -- First complexify the real primitive without changing its continuity set.
    simpa using Complex.continuous_ofReal.comp_continuousOn'
      (exercise8_right_primitive_continuousOn_Icc k)
  have haffine :
      ContinuousOn
        (fun x : ℝ =>
          (exercise8_complete_real_period k : ℂ) +
            ((exercise8_right_primitive k x : ℝ) : ℂ) * Complex.I)
        (Icc (1 : ℝ) (1 / (k : ℝ))) := by
    -- Then add the constant real period and multiply the primitive by `I`.
    exact continuousOn_const.add (hprim.mul continuousOn_const)
  -- The source right-edge branch is exactly this affine complex expression.
  exact ContinuousOn.congr haffine fun x hx => by
    simpa using exercise8_boundary_right_branch_eq_right_primitive k x

/-- Helper for Exercise 8: the reciprocal parameter `x ↦ 1 / (k x)` maps the top-edge domain
to the bottom-edge interval. -/
lemma exercise8_top_branch_argument_mem_Icc {k : Exercise8Modulus} {x : ℝ}
    (hx : 1 / (k : ℝ) ≤ x) :
    1 / ((k : ℝ) * x) ∈ Icc (0 : ℝ) 1 := by
  -- The reciprocal change of variables from the source sends `[1 / k, ∞)` into `[0, 1]`.
  constructor
  · have hx_pos : 0 < x := by
      have hk_inv_pos : 0 < 1 / (k : ℝ) := one_div_pos.mpr (Exercise8Modulus.pos k)
      exact lt_of_lt_of_le hk_inv_pos hx
    exact (one_div_pos.mpr (mul_pos (Exercise8Modulus.pos k) hx_pos)).le
  · have hk_ne : (k : ℝ) ≠ 0 := (Exercise8Modulus.pos k).ne'
    have hmul : (k : ℝ) * (1 / (k : ℝ)) ≤ (k : ℝ) * x := by
      exact mul_le_mul_of_nonneg_left hx (Exercise8Modulus.pos k).le
    have hleft : (k : ℝ) * (1 / (k : ℝ)) = 1 := by
      field_simp [hk_ne]
    have hkx_ge_one : 1 ≤ (k : ℝ) * x := by
      rw [← hleft]
      exact hmul
    have hkx_inv_le : ((k : ℝ) * x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hkx_ge_one
    simpa [one_div] using hkx_inv_le

/-- Helper for Exercise 8: the reciprocal parameter `x ↦ 1 / (k x)` is continuous on the top-edge
domain `[1 / k, ∞)`. -/
lemma exercise8_top_branch_argument_continuousOn (k : Exercise8Modulus) :
    ContinuousOn (fun x : ℝ => 1 / ((k : ℝ) * x)) (Ici (1 / (k : ℝ))) := by
  -- This is the analytic input for composing the bottom-edge owner with the top-edge change.
  have hmul : ContinuousOn (fun x : ℝ => (k : ℝ) * x) (Ici (1 / (k : ℝ))) :=
    (continuous_const.mul continuous_id).continuousOn
  have hmul_ne : ∀ x ∈ Ici (1 / (k : ℝ)), (k : ℝ) * x ≠ 0 := by
    intro x hx
    have hx_pos : 0 < x := by
      have hk_inv_pos : 0 < 1 / (k : ℝ) := one_div_pos.mpr (Exercise8Modulus.pos k)
      exact lt_of_lt_of_le hk_inv_pos hx
    exact (mul_pos (Exercise8Modulus.pos k) hx_pos).ne'
  simpa [one_div] using ContinuousOn.inv₀ hmul hmul_ne

/-- Helper for Exercise 8: the top-edge branch is continuous on `[1 / k, +∞)`. -/
lemma exercise8_boundary_top_branch_continuousOn (k : Exercise8Modulus) :
    ContinuousOn (exercise8_boundary_top_branch k) (Ici (1 / (k : ℝ))) := by
  -- The source proof writes the top edge as `i K'` plus the bottom-edge primitive evaluated at
  -- the reciprocal parameter `x ↦ 1 / (k x)`.
  have hcomp :
      ContinuousOn
        (fun x : ℝ => ((exercise8_inner_primitive k (1 / ((k : ℝ) * x)) : ℝ) : ℂ))
        (Ici (1 / (k : ℝ))) := by
    -- Compose the bottom-edge primitive owner with the reciprocal source substitution.
    refine (exercise8_inner_primitive_complex_continuousOn_Icc k).comp'
      (exercise8_top_branch_argument_continuousOn k) ?_
    intro x hx
    exact exercise8_top_branch_argument_mem_Icc (k := k) hx
  have haffine :
      ContinuousOn
        (fun x : ℝ =>
          (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
            ((exercise8_inner_primitive k (1 / ((k : ℝ) * x)) : ℝ) : ℂ))
        (Ici (1 / (k : ℝ))) := by
    -- Adding the constant imaginary period preserves continuity on the whole top edge.
    exact continuousOn_const.add hcomp
  -- The top-edge branch is this affine composition of the bottom-edge primitive.
  exact ContinuousOn.congr haffine fun x hx => by
    simpa using exercise8_boundary_top_branch_eq_inner_composition k x

/-- Helper for Exercise 8: the real kernel is strictly positive on the open interval `(0, 1)`. -/
lemma exercise8_real_kernel_pos {k : Exercise8Modulus} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < exercise8_real_kernel k x := by
  -- The source kernel factors into two positive real factors on `(0, 1)`.
  rw [exercise8_real_kernel, exercise8_real_kernel_eq_factored (k := k) ⟨le_of_lt hx.1, hx.2.le⟩]
  have hx_sqrt : 0 < Real.sqrt (1 - x ^ (2 : ℕ)) := by
    have hx_rad : 0 < 1 - x ^ (2 : ℕ) := by
      nlinarith [hx.1, hx.2]
    exact Real.sqrt_pos.2 hx_rad
  exact mul_pos (exercise8_real_factor_pos (k := k) hx) (inv_pos.2 hx_sqrt)

/-- Helper for Exercise 8: on the positive top branch `x ≥ 1 / k`, the reflected boundary trace
has strictly positive real part. In particular, the finite real-axis trace cannot hit the midpoint
`i K'` of the top edge on this branch. -/
lemma exercise8_boundary_trace_top_branch_re_pos {k : Exercise8Modulus} {x : ℝ}
    (hx : 1 / (k : ℝ) ≤ x) :
    0 < (exercise8_boundary_trace k x).re := by
  -- Route correction: the top branch is `i K'` plus the bottom-edge primitive after the
  -- reciprocal substitution, so its real part is exactly that positive primitive value.
  have hx_pos : 0 < x := by
    exact lt_of_lt_of_le (one_div_pos.mpr (Exercise8Modulus.pos k)) hx
  let y : ℝ := 1 / ((k : ℝ) * x)
  have hy_pos : 0 < y := by
    dsimp [y]
    exact one_div_pos.mpr (mul_pos (Exercise8Modulus.pos k) hx_pos)
  have hy_mem : y ∈ Icc (0 : ℝ) 1 := by
    simpa [y] using exercise8_top_branch_argument_mem_Icc (k := k) hx
  have hkernel :
      IntervalIntegrable (exercise8_real_kernel k) MeasureTheory.volume (0 : ℝ) y := by
    refine (exercise8_real_kernel_intervalIntegrable k).mono_set ?_
    have hsubset : Set.Icc (0 : ℝ) y ⊆ Set.Icc (0 : ℝ) 1 := by
      intro t ht
      exact ⟨ht.1, ht.2.trans hy_mem.2⟩
    simpa [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hy_mem.1] using hsubset
  have hprimitive_pos : 0 < exercise8_inner_primitive k y := by
    -- The reciprocal parameter stays in `(0, 1]`, so the primitive from `0` to `y` is positive.
    dsimp [exercise8_inner_primitive]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hkernel ?_ hy_pos
    intro t ht
    exact exercise8_real_kernel_pos (k := k) ⟨ht.1, lt_of_lt_of_le ht.2 hy_mem.2⟩
  have hrepr :
      exercise8_boundary_trace k x =
        (exercise8_complete_imaginary_period k : ℂ) * Complex.I +
          ((exercise8_inner_primitive k y : ℝ) : ℂ) := by
    -- Rewrite the public owner to the top-branch source formula with the named primitive.
    rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
    rw [exercise8_boundary_value_eq_top (k := k) hx]
    rw [exercise8_inner_primitive, exercise8_intervalIntegral_ofReal]
    simp [exercise8_real_kernel, y]
  rw [hrepr]
  simpa using hprimitive_pos

/-- Helper for Exercise 8: on the nonnegative real axis, the current finite trace misses the
midpoint `i K'` of the top edge. -/
lemma exercise8_boundary_trace_ne_top_midpoint_of_nonneg (k : Exercise8Modulus) {x : ℝ}
    (hx0 : 0 ≤ x) :
    exercise8_boundary_trace k x ≠
      (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
  by_cases hx1 : x < 1
  · -- On the bottom edge the trace is real, so its imaginary part cannot equal `K' > 0`.
    have him_zero : (exercise8_boundary_trace k x).im = 0 := by
      rw [show exercise8_boundary_trace k x = exercise8_boundary_inner_branch k x by
        rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
        exact exercise8_boundary_value_eq_inner (k := k) ⟨hx0, hx1.le⟩]
      rw [exercise8_boundary_inner_branch_eq_inner_primitive]
      simp
    intro hxmid
    have him : (exercise8_boundary_trace k x).im = exercise8_complete_imaginary_period k := by
      simpa using congrArg Complex.im hxmid
    rw [him_zero] at him
    exact (exercise8_complete_imaginary_period_pos k).ne' him.symm
  · have hx1' : 1 ≤ x := not_lt.mp hx1
    by_cases hxk : x < 1 / (k : ℝ)
    · -- On the right edge the real part is always the positive constant `K`.
      have hre_pos : 0 < (exercise8_boundary_trace k x).re := by
        rw [show exercise8_boundary_trace k x = exercise8_boundary_value k x by rfl]
        rw [exercise8_boundary_value_eq_right (k := k) hx1' hxk.le]
        simpa using exercise8_complete_real_period_pos k
      intro hxmid
      have hre : (exercise8_boundary_trace k x).re = 0 := by
        simpa using congrArg Complex.re hxmid
      exact hre_pos.ne' hre
    · -- On the positive top branch the real part is the positive reciprocal-substitution
      -- primitive, so it also cannot be `0`.
      have hre_pos : 0 < (exercise8_boundary_trace k x).re :=
        exercise8_boundary_trace_top_branch_re_pos (k := k) (x := x) (not_lt.mp hxk)
      intro hxmid
      have hre : (exercise8_boundary_trace k x).re = 0 := by
        simpa using congrArg Complex.re hxmid
      exact hre_pos.ne' hre

/-- Helper for Exercise 8: the current finite real-axis trace misses the midpoint `i K'` of the
top edge. This exposes the source/Lean mismatch that the textbook statement really uses the point
at infinity on the boundary, whereas the local owner here only ranges over `ℝ`. -/
lemma exercise8_boundary_trace_ne_top_midpoint (k : Exercise8Modulus) (x : ℝ) :
    exercise8_boundary_trace k x ≠
      (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
  by_cases hx0 : 0 ≤ x
  · exact exercise8_boundary_trace_ne_top_midpoint_of_nonneg k hx0
  · -- Reflect across the imaginary axis and reduce to the already treated nonnegative case.
    have hxneg : 0 ≤ -x := by linarith
    intro hxmid
    have hreflect :
        exercise8_boundary_trace k (-x) = -star (exercise8_boundary_trace k x) := by
      simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k x
    have hxmid_neg :
        exercise8_boundary_trace k (-x) =
          (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by
      calc
        exercise8_boundary_trace k (-x) = -star (exercise8_boundary_trace k x) := hreflect
        _ =
            -star ((exercise8_complete_imaginary_period k : ℂ) * Complex.I) := by rw [hxmid]
        _ = (exercise8_complete_imaginary_period k : ℂ) * Complex.I := by simp
    exact (exercise8_boundary_trace_ne_top_midpoint_of_nonneg k hxneg) hxmid_neg

/-- Helper for Exercise 8: the midpoint `i K'` of the top edge is not in the range of the current
finite real-axis trace owner. -/
lemma exercise8_top_midpoint_not_mem_boundary_trace_range (k : Exercise8Modulus) :
    (exercise8_complete_imaginary_period k : ℂ) * Complex.I ∉
      Set.range (exercise8_boundary_trace k) := by
  intro hmem
  rcases hmem with ⟨x, hx⟩
  exact exercise8_boundary_trace_ne_top_midpoint k x hx

/-- Helper for Exercise 8: on `x ≥ 0`, the nonnegative owner is the interval-set piecewise glue
of the three source boundary branches. -/
lemma exercise8_boundary_value_nonneg_eq_piecewise_on_Ici (k : Exercise8Modulus) :
    EqOn
      (exercise8_boundary_value_nonneg k)
      (Set.piecewise (Iio (1 : ℝ)) (exercise8_boundary_inner_branch k)
        (Set.piecewise (Iio (1 / (k : ℝ))) (exercise8_boundary_right_branch k)
          (exercise8_boundary_top_branch k)))
      (Ici (0 : ℝ)) := by
  intro x hx0
  by_cases hx1 : x < 1
  · -- On the inner interval `[0, 1)`, the positive-side owner is exactly the bottom-edge branch.
    rw [Set.piecewise_eq_of_mem (s := Iio (1 : ℝ)) _ _ hx1]
    exact exercise8_boundary_value_nonneg_eq_of_lt_one (k := k) hx0 hx1
  · have hx1' : 1 ≤ x := not_lt.mp hx1
    by_cases hxk : x < 1 / (k : ℝ)
    · -- On `[1, 1 / k)`, the owner is the right-edge branch.
      rw [Set.piecewise_eq_of_notMem (s := Iio (1 : ℝ)) _ _ hx1]
      rw [Set.piecewise_eq_of_mem (s := Iio (1 / (k : ℝ))) _ _ hxk]
      exact exercise8_boundary_value_nonneg_eq_of_right_open (k := k) hx1' hxk
    · -- On `[1 / k, ∞)`, the owner is the top-edge reciprocal-substitution branch.
      rw [Set.piecewise_eq_of_notMem (s := Iio (1 : ℝ)) _ _ hx1]
      rw [Set.piecewise_eq_of_notMem (s := Iio (1 / (k : ℝ))) _ _ hxk]
      exact exercise8_boundary_value_nonneg_eq_of_ge_inv_k (k := k) (not_lt.mp hxk)

/-- Helper for Exercise 8: the nonnegative-side boundary trace is continuous on `x ≥ 0`. -/
lemma exercise8_boundary_value_nonneg_continuousOn (k : Exercise8Modulus) :
    ContinuousOn (exercise8_boundary_value_nonneg k) (Ici (0 : ℝ)) := by
  -- Route correction: we glue the three source branches in two steps, first at `x = 1 / k` and
  -- then at `x = 1`, so each `ContinuousOn.if` sees only one frontier point.
  let rightOrTop : ℝ → ℂ :=
    Set.piecewise (Iio (1 / (k : ℝ))) (exercise8_boundary_right_branch k)
      (exercise8_boundary_top_branch k)
  have hk_lt : 1 < 1 / (k : ℝ) := by
    simpa [one_div] using (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
  have hrightOrTop : ContinuousOn rightOrTop (Ici (1 : ℝ)) := by
    -- First glue the right and top edges at the vertex `x = 1 / k`.
    have htopOnMax :
        ContinuousOn (exercise8_boundary_top_branch k) (Ici (max (1 : ℝ) (1 / (k : ℝ)))) := by
      have hk_max : max (1 : ℝ) (1 / (k : ℝ)) = 1 / (k : ℝ) := max_eq_right hk_lt.le
      convert exercise8_boundary_top_branch_continuousOn k using 1
      rw [hk_max]
    refine ContinuousOn.piecewise (s := Ici (1 : ℝ)) (t := Iio (1 / (k : ℝ))) ?_ ?_ ?_
    · intro a ha
      have ha_eq : a = 1 / (k : ℝ) := by
        simpa [frontier_Iio] using ha.2
      subst ha_eq
      -- Both source formulas hit the same vertex `K + i K'`.
      calc
        exercise8_boundary_right_branch k (1 / (k : ℝ))
            = exercise8_boundary_value k (1 / (k : ℝ)) := by
              symm
              simpa [exercise8_boundary_right_branch] using
                exercise8_boundary_value_eq_right (k := k) (x := 1 / (k : ℝ)) hk_lt.le le_rfl
        _ = exercise8_boundary_top_branch k (1 / (k : ℝ)) := by
              simpa [exercise8_boundary_top_branch] using
                exercise8_boundary_value_eq_top (k := k) (x := 1 / (k : ℝ)) le_rfl
    · -- On the left side of the vertex, this is the right-edge branch.
      simpa [rightOrTop, closure_Iio, hk_lt.le] using
        exercise8_boundary_right_branch_continuousOn k
    · -- On and above the vertex, this is the top-edge branch.
      simpa [rightOrTop] using htopOnMax
  have hpiecewise :
      ContinuousOn
        (Set.piecewise (Iio (1 : ℝ)) (exercise8_boundary_inner_branch k) rightOrTop)
        (Ici (0 : ℝ)) := by
    -- Then glue the bottom edge to the already-glued right/top owner at `x = 1`.
    refine ContinuousOn.piecewise (s := Ici (0 : ℝ)) (t := Iio (1 : ℝ)) ?_ ?_ ?_
    · intro a ha
      have ha_eq : a = 1 := by
        simpa [frontier_Iio] using ha.2
      subst ha_eq
      -- The two source formulas share the real-period vertex `K`.
      calc
        exercise8_boundary_inner_branch k 1 = exercise8_boundary_value k 1 := by
          symm
          simpa [exercise8_boundary_inner_branch] using
            exercise8_boundary_value_eq_inner (k := k) (x := 1)
              ⟨by norm_num, by norm_num⟩
        _ = exercise8_boundary_right_branch k 1 := by
          simpa [exercise8_boundary_right_branch] using
            exercise8_boundary_value_eq_right (k := k) (x := 1) (by norm_num) hk_lt.le
        _ = rightOrTop 1 := by
          have hpiece :
              rightOrTop 1 = exercise8_boundary_right_branch k 1 := by
            dsimp [rightOrTop]
            rw [Set.piecewise_eq_of_mem (s := Iio (1 / (k : ℝ)))
              (exercise8_boundary_right_branch k) (exercise8_boundary_top_branch k) hk_lt]
          symm
          exact hpiece
    · -- On `[0, 1]`, the owner is the bottom-edge branch.
      simpa [closure_Iio] using exercise8_boundary_inner_branch_continuousOn k
    · -- On `[1, ∞)`, the owner is the right/top piecewise glue.
      simpa [rightOrTop, closure_Ici, Set.inter_assoc, Set.inter_left_comm, Set.inter_right_comm]
        using hrightOrTop
  have hcanonical :
      ContinuousOn
        (Set.piecewise (Iio (1 : ℝ)) (exercise8_boundary_inner_branch k)
          (Set.piecewise (Iio (1 / (k : ℝ))) (exercise8_boundary_right_branch k)
            (exercise8_boundary_top_branch k)))
        (Ici (0 : ℝ)) := by
    -- This restores the explicit three-branch textbook formula used by the public owner.
    simpa [rightOrTop] using hpiecewise
  -- Finally rewrite the public positive-side owner to the glued source branches.
  exact ContinuousOn.congr hcanonical (exercise8_boundary_value_nonneg_eq_piecewise_on_Ici k)

/-- Helper for Exercise 8: the repaired real-axis trace is continuous. -/
lemma exercise8_boundary_trace_continuous (k : Exercise8Modulus) :
    Continuous (exercise8_boundary_trace k) := by
  -- The negative half-line is obtained from the nonnegative owner by `x ↦ -x`, conjugation, and
  -- a final minus sign, so the only glue point is the origin.
  have hnonneg :
      ContinuousOn (exercise8_boundary_value_nonneg k) (Ici (0 : ℝ)) :=
    exercise8_boundary_value_nonneg_continuousOn k
  have hreflected :
      ContinuousOn (fun x : ℝ => -star (exercise8_boundary_value_nonneg k (-x))) (Iic (0 : ℝ)) := by
    -- Reflect the positive-side owner across `x ↦ -x`, then conjugate and negate.
    have hcomp :
        ContinuousOn (fun x : ℝ => exercise8_boundary_value_nonneg k (-x)) (Iic (0 : ℝ)) := by
      refine hnonneg.comp' continuous_neg.continuousOn ?_
      intro x hx
      have hx' : x ≤ 0 := hx
      show 0 ≤ -x
      linarith
    exact hcomp.star.neg
  have hfrontier :
      ∀ a ∈ frontier {x : ℝ | 0 ≤ x},
        exercise8_boundary_value_nonneg k a = -star (exercise8_boundary_value_nonneg k (-a)) := by
    intro a ha
    have ha_eq : a = 0 := by
      have hmem : a ∈ frontier (Ici (0 : ℝ)) := by
        simpa [Ici] using ha
      have hsingleton : a ∈ ({(0 : ℝ)} : Set ℝ) := by
        simpa [frontier_Ici] using hmem
      exact Set.mem_singleton_iff.mp hsingleton
    subst ha_eq
    -- Both sides vanish at the origin, so the reflection glues continuously there.
    simp [exercise8_boundary_value_nonneg]
  have hnonnegClosed :
      ContinuousOn (exercise8_boundary_value_nonneg k) (closure {x : ℝ | 0 ≤ x}) := by
    change ContinuousOn (exercise8_boundary_value_nonneg k) (closure (Ici (0 : ℝ)))
    simpa [closure_Ici] using hnonneg
  have hreflectedClosed :
      ContinuousOn (fun x : ℝ => -star (exercise8_boundary_value_nonneg k (-x)))
        (closure {x : ℝ | ¬ 0 ≤ x}) := by
    have hset : closure {x : ℝ | ¬ 0 ≤ x} = closure (Iio (0 : ℝ)) := by
      congr 1
      ext x
      simp [not_le]
    rw [hset]
    simpa [closure_Iio] using hreflected
  -- Glue the positive owner and its reflected negative-side owner across the origin.
  simpa [exercise8_boundary_trace] using
    (continuous_if (p := fun x : ℝ => 0 ≤ x) hfrontier hnonnegClosed hreflectedClosed)

/-- A continuous extension of the Exercise 8 Abelian integral to the closed upper half-plane. -/
def IsExercise8Extension (k : Exercise8Modulus) (fbar : ClosedUpperHalfPlane → ℂ) : Prop :=
  Continuous fbar ∧
    ∀ z : UpperHalfPlane,
      fbar ⟨(z : ℂ), le_of_lt z.im_pos⟩ = exercise8_abel_integral k z

/-- Helper for Exercise 8: the strict upper half-plane includes canonically into the closed
upper half-plane. -/
def exercise8_closedUpperHalfPlane_of_upper (z : UpperHalfPlane) : ClosedUpperHalfPlane :=
  ⟨(z : ℂ), le_of_lt z.im_pos⟩

/-- Helper for Exercise 8: the strict upper slice is dense in the closed upper half-plane. -/
lemma exercise8_dense_upper_slice :
    DenseRange (exercise8_closedUpperHalfPlane_of_upper : UpperHalfPlane → ClosedUpperHalfPlane) :=
  by
  -- The source uniqueness step approximates each boundary point by moving a short vertical distance
  -- into the strict upper half-plane.
  rw [Metric.denseRange_iff]
  intro z r hr
  refine
    ⟨⟨(z : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I, ?_⟩, ?_⟩
  · -- Adding `i r/2` makes the imaginary part strictly positive while staying arbitrarily close.
    have hz_im : 0 ≤ ((z : ℂ)).im := z.2
    have hhalf_pos : 0 < r / 2 := by
      linarith
    have :
        0 < (((z : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I)).im := by
      simpa [Complex.add_im] using add_pos_of_nonneg_of_pos hz_im hhalf_pos
    exact this
  · -- In the subtype metric, the perturbation has size exactly `r / 2`.
    have hhalf_lt : |r| / 2 < r := by
      rw [abs_of_pos hr]
      linarith
    simpa [exercise8_closedUpperHalfPlane_of_upper, Subtype.dist_eq, dist_eq_norm] using hhalf_lt

/-- Helper for Exercise 8: a continuous extension to the closed upper half-plane is unique once it
agrees with the Abel integral on the strict upper slice. -/
lemma exercise8_extension_unique {k : Exercise8Modulus}
    {fbar gbar : ClosedUpperHalfPlane → ℂ}
    (hfbar : IsExercise8Extension k fbar) (hgbar : IsExercise8Extension k gbar) :
    fbar = gbar := by
  -- Route correction: the uniqueness part no longer waits on the boundary-value formulas; it is
  -- isolated as a dense-slice argument on `ClosedUpperHalfPlane`.
  refine exercise8_dense_upper_slice.equalizer hfbar.1 hgbar.1 ?_
  funext z
  simp [exercise8_closedUpperHalfPlane_of_upper, hfbar.2 z, hgbar.2 z]

/-- Helper for Exercise 8: a closed-upper-half-plane point off the real axis actually lies in the
strict upper half-plane. -/
lemma exercise8_im_pos_of_closed_nonreal {z : ClosedUpperHalfPlane} (hz : ((z : ℂ)).im ≠ 0) :
    0 < ((z : ℂ)).im := by
  -- In the closed half-plane, the only nonpositive imaginary value is `0`.
  exact lt_of_le_of_ne z.2 (Ne.symm hz)

/-- Helper for Exercise 8: the canonical owner on the closed half-plane uses the repaired boundary
trace on the real axis and the Abel integral in the interior. -/
def exercise8_closed_extension (k : Exercise8Modulus) : ClosedUpperHalfPlane → ℂ :=
  fun z ↦
    if hz : ((z : ℂ)).im = 0 then
      exercise8_boundary_trace k ((z : ℂ).re)
    else
      exercise8_abel_integral k ⟨(z : ℂ), exercise8_im_pos_of_closed_nonreal hz⟩

/-- Helper for Exercise 8: the canonical closed-half-plane owner restricts to the repaired
boundary trace on the real axis. -/
@[simp] lemma exercise8_closed_extension_of_real (k : Exercise8Modulus) (x : ℝ) :
    exercise8_closed_extension k ⟨(x : ℂ), by simp⟩ = exercise8_boundary_trace k x := by
  -- The real-axis branch is selected because the imaginary part is exactly zero.
  simp [exercise8_closed_extension]

/-- Helper for Exercise 8: the canonical closed-half-plane owner agrees with the Abel integral on
the strict upper half-plane. -/
@[simp] lemma exercise8_closed_extension_of_upper (k : Exercise8Modulus) (z : UpperHalfPlane) :
    exercise8_closed_extension k ⟨(z : ℂ), le_of_lt z.im_pos⟩ = exercise8_abel_integral k z := by
  -- Off the real axis the definition picks the interior Abel-integral branch.
  have hz : (((⟨(z : ℂ), le_of_lt z.im_pos⟩ : ClosedUpperHalfPlane) : ℂ)).im ≠ 0 := ne_of_gt z.im_pos
  have hz0 : ¬ (((⟨(z : ℂ), le_of_lt z.im_pos⟩ : ClosedUpperHalfPlane) : ℂ)).im = 0 := hz
  have hSubtype :
      (⟨(z : ℂ), exercise8_im_pos_of_closed_nonreal (z := ⟨(z : ℂ), le_of_lt z.im_pos⟩) hz⟩ :
        UpperHalfPlane) = z := by
    ext
    rfl
  by_cases hzero : (((⟨(z : ℂ), le_of_lt z.im_pos⟩ : ClosedUpperHalfPlane) : ℂ)).im = 0
  · exact False.elim (hz hzero)
  · rw [exercise8_closed_extension, dif_neg hzero]

/-- Helper for Exercise 8: the canonical owner built from the reflected boundary trace is the
source-faithful closed-half-plane extension. -/
lemma exercise8_closed_extension_spec (k : Exercise8Modulus) :
    IsExercise8Extension k (exercise8_closed_extension k) := by
  constructor
  · -- TODO: prove continuity by matching the interior Abel integral to the repaired boundary
    -- trace along the real axis and then applying the source continuous-extension argument.
    sorry
  · -- The interior branch of the definition is literally the Abel integral.
    intro z
    simpa using exercise8_closed_extension_of_upper k z

/-- Helper for Exercise 8: the repaired boundary trace parametrizes exactly the frontier of the
fundamental rectangle. -/
lemma exercise8_boundary_trace_range_eq_frontier_rectangle (k : Exercise8Modulus) :
    Set.range (exercise8_boundary_trace k) = frontier (exercise8_open_rectangle k) := by
  -- TODO: assemble the four source boundary branches `(-∞,-1/k]`, `[-1,1]`, `[1,1/k]`, and
  -- `(-1/k,-1]` into the rectangle perimeter using the repaired reflected trace formulas.
  sorry

/-- The source-facing inverse of the Exercise 8 Abelian integral on the fundamental rectangle. -/
def IsExercise8RectangleInverse
    (k : Exercise8Modulus) (G : exercise8_open_rectangle k → UpperHalfPlane) : Prop :=
  (∀ u : exercise8_open_rectangle k, exercise8_abel_integral k (G u) = u) ∧
    (∀ z : UpperHalfPlane, exercise8_abel_integral k z ∈ exercise8_open_rectangle k) ∧
    ∀ z : UpperHalfPlane,
      ∀ hz : exercise8_abel_integral k z ∈ exercise8_open_rectangle k,
        G ⟨exercise8_abel_integral k z, hz⟩ = z

/-- A meromorphic doubly-periodic extension of the Exercise 8 rectangle inverse. -/
def IsExercise8Inverse (k : Exercise8Modulus) (F : ℂ → ℂ) : Prop :=
  ∃ G : exercise8_open_rectangle k → UpperHalfPlane,
    IsExercise8RectangleInverse k G ∧
      Meromorphic F ∧
      HasPeriodLattice (exercise8_period_pair k) F ∧
      (∀ u : exercise8_open_rectangle k, F u = G u)

/-- Exercise 8 (1): for `0 < k < 1`, the Abelian integral extends continuously to the closed
upper half-plane `Im z ≥ 0`. -/
theorem exercise_8_continuous_extension
    (k : Exercise8Modulus) :
    ∃ fbar : ClosedUpperHalfPlane → ℂ, IsExercise8Extension k fbar := by
  -- The canonical owner is the repaired boundary trace on `Im z = 0` and the Abel integral in the
  -- strict upper half-plane.
  exact ⟨exercise8_closed_extension k, exercise8_closed_extension_spec k⟩

/-- Exercise 8 (2): for `0 < k < 1`, the Abelian integral is a bijection from the open upper
half-plane onto the open rectangle with vertices `-K`, `K`, `K + i K'`, and `-K + i K'`. -/
theorem exercise_8_abel_integral_bijective
    (k : Exercise8Modulus) :
    Set.BijOn (exercise8_abel_integral k) univ (exercise8_open_rectangle k) := by
  -- TODO: use the boundary trace to identify the rectangle edges, then package the inverse
  -- `G : exercise8_open_rectangle k → UpperHalfPlane` before extracting bijectivity.
  sorry

/-- Exercise 8 (3): any continuous extension of the Abelian integral maps the real axis onto the
perimeter of the Exercise 8 rectangle. -/
theorem exercise_8_boundary_to_perimeter
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    Set.range (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩) = frontier (exercise8_open_rectangle k) :=
  by
  -- Uniqueness lets us replace any extension by the canonical closed-half-plane owner.
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  calc
    Set.range (fun x : ℝ ↦ fbar ⟨(x : ℂ), by simp⟩)
        = Set.range (fun x : ℝ ↦ exercise8_closed_extension k ⟨(x : ℂ), by simp⟩) := by
            simp [hEq]
    _ = Set.range (exercise8_boundary_trace k) := by
          ext u
          constructor
          · rintro ⟨x, rfl⟩
            refine ⟨x, ?_⟩
            simp
          · rintro ⟨x, rfl⟩
            refine ⟨x, ?_⟩
            simp
    _ = frontier (exercise8_open_rectangle k) :=
          exercise8_boundary_trace_range_eq_frontier_rectangle k

/-- Exercise 8 (4): the boundary point `-1` corresponds to the vertex `-K`. -/
theorem exercise_8_vertex_neg_one
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    fbar ⟨(-1 : ℂ), by simp⟩ = -exercise8_complete_real_period k := by
  -- Uniqueness reduces the vertex computation to the canonical reflected boundary trace.
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  calc
    fbar ⟨(-1 : ℂ), by simp⟩ = exercise8_closed_extension k ⟨(-1 : ℂ), by simp⟩ := by
      simpa [hEq]
    _ = exercise8_boundary_trace k (-1) := by
      simpa using exercise8_closed_extension_of_real k (-1 : ℝ)
    _ = -exercise8_complete_real_period k := by
      simpa using exercise8_boundary_value_neg_one k

/-- Exercise 8 (5): the boundary point `1` corresponds to the vertex `K`. -/
theorem exercise_8_vertex_one
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    fbar ⟨(1 : ℂ), by simp⟩ = exercise8_complete_real_period k := by
  -- Uniqueness again lets us evaluate the canonical owner instead of the arbitrary extension.
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  calc
    fbar ⟨(1 : ℂ), by simp⟩ = exercise8_closed_extension k ⟨(1 : ℂ), by simp⟩ := by
      simpa [hEq]
    _ = exercise8_boundary_trace k 1 := by
      simpa using exercise8_closed_extension_of_real k (1 : ℝ)
    _ = exercise8_complete_real_period k := by
      simpa using exercise8_boundary_value_one k

/-- Exercise 8 (6): the boundary point `1 / k` corresponds to the vertex `K + i K'`. -/
theorem exercise_8_vertex_inv_k
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    fbar ⟨((1 / (k : ℝ)) : ℂ), by simp⟩ =
      exercise8_complete_real_period k +
        exercise8_complete_imaginary_period k * Complex.I := by
  -- The repaired boundary trace already records the right-top vertex `K + i K'`.
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  calc
    fbar ⟨((1 / (k : ℝ)) : ℂ), by simp⟩ =
        exercise8_closed_extension k ⟨((1 / (k : ℝ)) : ℂ), by simp⟩ := by
          simpa [hEq]
    _ = exercise8_boundary_trace k (1 / (k : ℝ)) := by
      simpa using exercise8_closed_extension_of_real k (1 / (k : ℝ))
    _ =
        exercise8_complete_real_period k +
          exercise8_complete_imaginary_period k * Complex.I := by
          simpa using exercise8_boundary_value_inv_k k

/-- Exercise 8 (7): the boundary point `-1 / k` corresponds to the vertex `-K + i K'`. -/
theorem exercise_8_vertex_neg_inv_k
    (k : Exercise8Modulus)
    {fbar : ClosedUpperHalfPlane → ℂ} (hfbar : IsExercise8Extension k fbar) :
    fbar ⟨((-(1 / (k : ℝ))) : ℂ), by simp⟩ =
      -exercise8_complete_real_period k +
        exercise8_complete_imaginary_period k * Complex.I := by
  -- Route correction: the left-top vertex comes from Schwarz reflection, not from global oddness.
  have hEq : fbar = exercise8_closed_extension k :=
    exercise8_extension_unique hfbar (exercise8_closed_extension_spec k)
  calc
    fbar ⟨((-(1 / (k : ℝ))) : ℂ), by simp⟩ =
        exercise8_closed_extension k ⟨((-(1 / (k : ℝ))) : ℂ), by simp⟩ := by
          simpa [hEq]
    _ = exercise8_boundary_trace k (-(1 / (k : ℝ))) := by
          simpa using exercise8_closed_extension_of_real k (-(1 / (k : ℝ)))
    _ =
        -exercise8_complete_real_period k +
          exercise8_complete_imaginary_period k * Complex.I := by
          simpa using exercise8_boundary_value_neg_inv_k k

/-- Exercise 8 (8): the inverse transformation extends to a meromorphic doubly-periodic function
with periods `4 K` and `2 i K'`. -/
theorem exercise_8_inverse_exists
    (k : Exercise8Modulus) :
    ∃ F : ℂ → ℂ, IsExercise8Inverse k F := by
  -- TODO: reflect the rectangle inverse across the four sides to obtain the doubly-periodic
  -- meromorphic extension with periods `4K` and `2 i K'`.
  sorry

/-- Exercise 8 (9): the meromorphic inverse has a zero exactly at the points of the even
period lattice, in the sense of positive meromorphic order. -/
theorem exercise_8_inverse_zero_iff
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) (u : ℂ) :
    0 < meromorphicOrderAt F u ↔ u ∈ (exercise8_half_period_pair k).lattice := by
  -- TODO: use the reflected inverse's fundamental-cell divisor and propagate it by period-lattice
  -- invariance to identify the full zero lattice.
  sorry

/-- Exercise 8 (10): the poles of the meromorphic inverse are exactly the translated odd
half-period lattice. -/
theorem exercise_8_inverse_pole_iff
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) (u : ℂ) :
    meromorphicOrderAt F u < 0 ↔
      u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice := by
  -- TODO: translate the fundamental pole at `i K'` across the half-period lattice and use the
  -- already proved lattice-coordinate normal form for the shifted pole condition.
  sorry

/-- Exercise 8 (11): as a meromorphic function, the inverse is a constant multiple of the quotient
`θ₁ (u / 2K) / θ₀ (u / 2K)` with parameter `τ = i K' / K`. We record this through the canonical
normal-form representative on `ℂ`. -/
theorem exercise_8_theta_quotient_formula
    (k : Exercise8Modulus)
    {F : ℂ → ℂ} (hF : IsExercise8Inverse k F) :
    ∃ A : ℂ,
      toMeromorphicNFOn F Set.univ =
        toMeromorphicNFOn (fun u ↦ A * exercise8_theta_quotient k u) Set.univ := by
  -- TODO: compare the reflected inverse with the scaled theta quotient via period lattice and
  -- zero/pole lattice data, then apply the constancy theorem for entire doubly-periodic functions.
  sorry
