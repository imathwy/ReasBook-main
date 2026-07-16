import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».PeriodData

open Set
open scoped UpperHalfPlane

noncomputable section

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

/-- Helper for Exercise 8: the bottom-edge primitive stays between `0` and the complete real
period `K` on `[0, 1]`. -/
lemma exercise8_inner_primitive_mem_Icc {k : Exercise8Modulus} {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    exercise8_inner_primitive k x ∈ Icc (0 : ℝ) (exercise8_complete_real_period k) := by
  constructor
  · -- The bottom-edge kernel is pointwise nonnegative, so every partial primitive is nonnegative.
    dsimp [exercise8_inner_primitive]
    refine intervalIntegral.integral_nonneg hx.1 ?_
    intro t ht
    dsimp [exercise8_real_kernel]
    exact one_div_nonneg.mpr (Real.sqrt_nonneg _)
  · -- Integrating the same nonnegative kernel over `[0, x]` is bounded by the full integral `K`.
    dsimp [exercise8_inner_primitive, exercise8_complete_real_period]
    have hnonneg :
        0 ≤ᵐ[MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)] exercise8_real_kernel k := by
      exact Filter.Eventually.of_forall fun t => by
        dsimp [exercise8_real_kernel]
        exact one_div_nonneg.mpr (Real.sqrt_nonneg _)
    exact intervalIntegral.integral_mono_interval
      (μ := MeasureTheory.volume) (f := exercise8_real_kernel k)
      (c := (0 : ℝ)) (d := (1 : ℝ)) (a := (0 : ℝ)) (b := x)
      le_rfl hx.1 hx.2 hnonneg (exercise8_real_kernel_intervalIntegrable k)

/-- Helper for Exercise 8: the right-edge primitive stays between `0` and the complete imaginary
period `K'` on `[1, 1 / k]`. -/
lemma exercise8_right_primitive_mem_Icc {k : Exercise8Modulus} {x : ℝ}
    (hx : x ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    exercise8_right_primitive k x ∈ Icc (0 : ℝ) (exercise8_complete_imaginary_period k) := by
  constructor
  · -- The right-edge kernel is pointwise nonnegative, so its primitive starts at `0`.
    dsimp [exercise8_right_primitive]
    refine intervalIntegral.integral_nonneg hx.1 ?_
    intro t ht
    dsimp [exercise8_imaginary_kernel]
    exact one_div_nonneg.mpr (Real.sqrt_nonneg _)
  · -- The same interval-monotonicity argument bounds the primitive by the full edge integral `K'`.
    dsimp [exercise8_right_primitive, exercise8_complete_imaginary_period]
    have hnonneg :
        0 ≤ᵐ[MeasureTheory.volume.restrict (Ioc (1 : ℝ) (1 / (k : ℝ)))]
          exercise8_imaginary_kernel k := by
      exact Filter.Eventually.of_forall fun t => by
        dsimp [exercise8_imaginary_kernel]
        exact one_div_nonneg.mpr (Real.sqrt_nonneg _)
    exact intervalIntegral.integral_mono_interval
      (μ := MeasureTheory.volume) (f := exercise8_imaginary_kernel k)
      (c := (1 : ℝ)) (d := (1 / (k : ℝ))) (a := (1 : ℝ)) (b := x)
      le_rfl hx.1 hx.2 hnonneg (exercise8_imaginary_kernel_intervalIntegrable k)

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
