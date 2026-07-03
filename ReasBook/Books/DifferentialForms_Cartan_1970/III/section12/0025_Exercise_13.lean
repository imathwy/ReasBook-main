import Mathlib
import DifferentialForms_Cartan_1970.III.section11.«0007_Remark_III_5_extra_6»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool is unavailable in this runner, so
-- the statement shape was checked directly against the local owner
-- `logDeriv_eventuallyEq_order_principalPart_add_analytic` and mathlib's
-- `HasFPowerSeriesAt` / `FormalMultilinearSeries.ofScalars` API for scalar analytic expansions.

open scoped Topology BigOperators

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]

/-- Helper for Exercise 13: a meromorphic function of order `-1` at `0` is `z⁻¹` times an
analytic germ with nonzero constant term. -/
lemma simple_pole_normal_form_at_zero {f : 𝕜 → 𝕜}
    (horder : meromorphicOrderAt f 0 = (-1 : ℤ)) :
    ∃ a : ℕ → 𝕜,
      ∃ φ : 𝕜 → 𝕜,
        HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0 ∧
        a 0 ≠ 0 ∧
        f =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * φ z := by
  -- First remove the meromorphic wrapper and recover the analytic unit in the standard order
  -- normal form.
  have hne : meromorphicOrderAt f 0 ≠ 0 := by
    rw [horder]
    norm_num
  have hf : MeromorphicAt f 0 := by
    exact meromorphicAt_of_meromorphicOrderAt_ne_zero hne
  obtain ⟨φ, hφ_an, hφ_ne, hφ_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 horder
  refine ⟨fun n ↦ iteratedDeriv n φ 0 / n.factorial, φ, ?_, ?_, ?_⟩
  · -- Convert the analytic germ into the scalar power-series expansion centered at `0`.
    exact hφ_an.hasFPowerSeriesAt
  · -- The constant coefficient is the value at `0`, hence is nonzero.
    simpa using hφ_ne
  · -- At `0` the textbook normal form `f = z⁻¹ φ` is exactly the `n = -1` owner lemma.
    simpa [smul_eq_mul, sub_eq_add_neg] using hφ_eq

/-- Helper for Exercise 13: punctured-neighborhood equality propagates to the logarithmic
derivative. -/
lemma logDeriv_congr_nhdsNE {f₁ f₂ : 𝕜 → 𝕜} (h : f₁ =ᶠ[𝓝[≠] (0 : 𝕜)] f₂) :
    logDeriv f₁ =ᶠ[𝓝[≠] (0 : 𝕜)] logDeriv f₂ := by
  -- Rewrite `logDeriv` as `deriv / value` and transport both factors through the eventual
  -- equality on the punctured neighborhood.
  filter_upwards [h, h.nhdsNE_deriv] with z hz hderiv
  simp [logDeriv_apply, hz, hderiv]

/-- Helper for Exercise 13: subtracting a constant does not change the simple-pole order at `0`. -/
lemma simple_pole_sub_const_order {f : 𝕜 → 𝕜}
    (horder : meromorphicOrderAt f 0 = (-1 : ℤ)) (x : 𝕜) :
    meromorphicOrderAt (fun z ↦ f z - x) 0 = (-1 : ℤ) := by
  classical
  by_cases hx : x = 0
  · -- The zero constant does nothing, so this is exactly the original order statement.
    simpa [hx] using horder
  · -- A simple pole has strictly smaller order than any nonzero constant term.
    have hconst : meromorphicOrderAt (fun _ : 𝕜 ↦ -x) 0 = (0 : WithTop ℤ) := by
      rw [meromorphicOrderAt_const]
      simp [hx]
    have hlt : meromorphicOrderAt f 0 < meromorphicOrderAt (fun _ : 𝕜 ↦ -x) 0 := by
      rw [horder, hconst]
      exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)
    have hadd :
        meromorphicOrderAt (f + fun _ : 𝕜 ↦ -x) 0 = meromorphicOrderAt f 0 :=
      meromorphicOrderAt_add_eq_left_of_lt
        (f₁ := f) (f₂ := fun _ : 𝕜 ↦ -x) (x := (0 : 𝕜)) (by fun_prop) hlt
    simpa [horder, sub_eq_add_neg] using hadd

/-- Helper for Exercise 13: after subtracting a constant from a simple pole, the logarithmic
derivative is `-1 / z` plus an analytic germ. -/
lemma simple_pole_logDeriv_sub_eventuallyEq_principalPart_add_analytic {f : 𝕜 → 𝕜}
    (horder : meromorphicOrderAt f 0 = (-1 : ℤ)) (x : 𝕜) :
    ∃ g : 𝕜 → 𝕜,
      AnalyticAt 𝕜 g 0 ∧
      logDeriv (fun z ↦ f z - x) =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ -1 / z + g z := by
  -- The local logarithmic-derivative owner theorem applies once the order of `f - x` is known.
  have hf : MeromorphicAt (fun z ↦ f z - x) 0 := by
    have hne : meromorphicOrderAt f 0 ≠ 0 := by
      rw [horder]
      norm_num
    have hf0 : MeromorphicAt f 0 := by
      exact meromorphicAt_of_meromorphicOrderAt_ne_zero hne
    simpa using hf0.sub (MeromorphicAt.const x 0)
  have hsuborder : meromorphicOrderAt (fun z ↦ f z - x) 0 = (-1 : ℤ) :=
    simple_pole_sub_const_order horder x
  simpa [sub_zero] using
    logDeriv_eventuallyEq_order_principalPart_add_analytic hf hsuborder

/-- Helper for Exercise 13: for each `x`, the regular part of `logDeriv (fun z ↦ f z - x)` admits
a scalar power series at `0`. -/
lemma simple_pole_logDeriv_sub_has_scalar_power_series {f : 𝕜 → 𝕜}
    (horder : meromorphicOrderAt f 0 = (-1 : ℤ)) (x : 𝕜) :
    ∃ c : ℕ → 𝕜,
      ∃ g : 𝕜 → 𝕜,
        HasFPowerSeriesAt g (.ofScalars 𝕜 c) 0 ∧
        logDeriv (fun z ↦ f z - x) =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ -1 / z + g z := by
  -- Package the analytic remainder from the previous lemma into its canonical scalar series.
  obtain ⟨g, hg_an, hg_eq⟩ :=
    simple_pole_logDeriv_sub_eventuallyEq_principalPart_add_analytic horder x
  refine ⟨fun n ↦ iteratedDeriv n g 0 / n.factorial, g, ?_, hg_eq⟩
  exact hg_an.hasFPowerSeriesAt

/-- Helper for Exercise 13: after the simple-pole normal form `f(z) = z⁻¹ φ(z)`, subtracting a
constant rewrites the logarithmic derivative into the explicit analytic quotient
`(deriv φ z - x) / (φ z - x * z)`. -/
lemma simple_pole_logDeriv_sub_explicit_regular_part {a : ℕ → 𝕜} {φ f : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (ha0 : a 0 ≠ 0)
    (hφ_eq : f =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * φ z)
    (x : 𝕜) :
    AnalyticAt 𝕜 (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 ∧
      logDeriv (fun z ↦ f z - x) =ᶠ[𝓝[≠] (0 : 𝕜)]
        fun z ↦ -1 / z + ((deriv φ z - x) / (φ z - x * z)) := by
  have hφ_an : AnalyticAt 𝕜 φ 0 := hφ_series.analyticAt
  have hφ0 : φ 0 = a 0 := by
    -- Read the constant term of the analytic expansion as the value at the center.
    simpa [FormalMultilinearSeries.ofScalars_apply_eq] using
      (hφ_series.coeff_zero (fun _ ↦ (0 : 𝕜))).symm
  have hshift_an : AnalyticAt 𝕜 (fun z ↦ φ z - x * z) 0 := by
    -- The shifted denominator stays analytic because we only subtract the linear term `x * z`.
    simpa using hφ_an.sub (analyticAt_const.mul analyticAt_id)
  have hshift0 : φ 0 - x * 0 ≠ 0 := by
    simpa [hφ0] using ha0
  have hquot_an : AnalyticAt 𝕜 (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 := by
    -- The quotient is analytic at `0` because the denominator keeps its nonzero constant term.
    exact (hφ_an.deriv.sub analyticAt_const).div hshift_an hshift0
  have hmodel_eq :
      (fun z ↦ f z - x) =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * (φ z - x * z) := by
    -- Rewrite `f(z) - x` into the normal form with a single analytic denominator factor.
    filter_upwards [self_mem_nhdsWithin, hφ_eq] with z hzmem hz
    have hz0 : z ≠ 0 := by simpa using hzmem
    have hxz : z⁻¹ * (x * z) = x := by
      calc
        z⁻¹ * (x * z) = x * (z⁻¹ * z) := by ring
        _ = x := by simp [hz0]
    calc
      f z - x = z⁻¹ * φ z - x := by rw [hz]
      _ = z⁻¹ * φ z - z⁻¹ * (x * z) := by rw [hxz]
      _ = z⁻¹ * (φ z - x * z) := by ring
  have hmodel_log :
      logDeriv (fun z ↦ z⁻¹ * (φ z - x * z)) =ᶠ[𝓝[≠] (0 : 𝕜)]
        fun z ↦ (-1 : 𝕜) / z + logDeriv (fun z ↦ φ z - x * z) z := by
    -- Compute the logarithmic derivative of the model product directly on the punctured
    -- neighborhood where both factors are nonzero and differentiable.
    have hshift_nonzero : ∀ᶠ z in 𝓝[≠] (0 : 𝕜), φ z - x * z ≠ 0 := by
      exact (hshift_an.continuousAt.eventually_ne hshift0).filter_mono nhdsWithin_le_nhds
    have hφ_ev : ∀ᶠ z in 𝓝[≠] (0 : 𝕜), AnalyticAt 𝕜 φ z := by
      exact hφ_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hshift_nonzero, hφ_ev] with z hzmem hz hφz
    have hz0 : z ≠ 0 := by simpa using hzmem
    have hlinear_diff : DifferentiableAt 𝕜 (fun w : 𝕜 ↦ x * w) z := by
      fun_prop
    have hshift_diff : DifferentiableAt 𝕜 (fun w ↦ φ w - x * w) z := by
      exact hφz.differentiableAt.sub hlinear_diff
    have hshiftz : logDeriv (fun w ↦ w⁻¹ * (φ w - x * w)) z =
        logDeriv (fun w ↦ w⁻¹) z + logDeriv (fun w ↦ φ w - x * w) z := by
      simpa using
        (logDeriv_mul z (inv_ne_zero hz0) hz
          (differentiableAt_inv hz0) hshift_diff)
    calc
      logDeriv (fun z ↦ z⁻¹ * (φ z - x * z)) z
          = logDeriv (fun w ↦ w⁻¹) z + logDeriv (fun w ↦ φ w - x * w) z := hshiftz
      _ = (-1 : 𝕜) / z + logDeriv (fun w ↦ φ w - x * w) z := by rw [logDeriv_inv]
  have hshift_nonzero : ∀ᶠ z in 𝓝[≠] (0 : 𝕜), φ z - x * z ≠ 0 := by
    -- The denominator remains nonzero on a small punctured neighborhood because its value at `0`
    -- is already nonzero.
    exact (hshift_an.continuousAt.eventually_ne hshift0).filter_mono nhdsWithin_le_nhds
  have hφ_ev : ∀ᶠ z in 𝓝[≠] (0 : 𝕜), AnalyticAt 𝕜 φ z := by
    -- Analyticity propagates to nearby points of the punctured neighborhood.
    exact hφ_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hshift_log :
      logDeriv (fun z ↦ φ z - x * z) =ᶠ[𝓝[≠] (0 : 𝕜)]
        fun z ↦ (deriv φ z - x) / (φ z - x * z) := by
    -- Once the denominator is nonzero, `logDeriv` is the ordinary quotient `f' / f`.
    filter_upwards [hshift_nonzero, hφ_ev] with z hz hφz
    have hlinear_diff : DifferentiableAt 𝕜 (fun w : 𝕜 ↦ x * w) z := by
      fun_prop
    have hderiv_shift : deriv (fun w ↦ φ w - x * w) z = deriv φ z - x := by
      have hderiv_linear : deriv (fun w : 𝕜 ↦ x * w) z = x := by
        simpa using deriv_const_mul_field x z
      have hderiv_sub :
          deriv (fun w ↦ φ w - x * w) z = deriv φ z - deriv (fun w : 𝕜 ↦ x * w) z := by
        simpa using deriv_sub hφz.differentiableAt hlinear_diff
      rw [hderiv_linear] at hderiv_sub
      exact hderiv_sub
    -- Evaluate the logarithmic derivative using the explicit derivative of the shifted factor.
    calc
      logDeriv (fun z ↦ φ z - x * z) z = deriv (fun w ↦ φ w - x * w) z / (φ z - x * z) := by
        rfl
      _ = (deriv φ z - x) / (φ z - x * z) := by rw [hderiv_shift]
  have hrewrite :
      (fun z ↦ (-1 : 𝕜) / z + logDeriv (fun z ↦ φ z - x * z) z) =ᶠ[𝓝[≠] (0 : 𝕜)]
        fun z ↦ -1 / z + ((deriv φ z - x) / (φ z - x * z)) := by
    -- Only the analytic quotient changes in the final rewrite.
    filter_upwards [hshift_log] with z hz
    simpa using congrArg (fun t : 𝕜 ↦ (-1 : 𝕜) / z + t) hz
  exact ⟨hquot_an, (logDeriv_congr_nhdsNE hmodel_eq).trans <| hmodel_log.trans hrewrite⟩

/-- Helper for Exercise 13: the stored scalar coefficients of the analytic unit `φ` agree with the
iterated derivatives at `0` after multiplying by the factorial. -/
lemma simple_pole_normal_form_iteratedDeriv_coeff {a : ℕ → 𝕜} {φ : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0) (n : ℕ) :
    iteratedDeriv n φ 0 = n.factorial * a n := by
  -- Compare the given scalar series with the canonical analytic series built from iterated
  -- derivatives, then read off the `n`-th scalar coefficient.
  have hcanonical := hφ_series.analyticAt.hasFPowerSeriesAt
  have hcoeff_series :
      (FormalMultilinearSeries.ofScalars 𝕜 a).coeff n =
        (FormalMultilinearSeries.ofScalars 𝕜
          (fun m ↦ iteratedDeriv m φ 0 / m.factorial)).coeff n := by
    exact congrArg (fun p : FormalMultilinearSeries 𝕜 𝕜 𝕜 ↦ p.coeff n)
      (hφ_series.eq_formalMultilinearSeries hcanonical)
  have hcoeff :
      a n = iteratedDeriv n φ 0 / n.factorial := by
    simpa [FormalMultilinearSeries.coeff_ofScalars] using hcoeff_series
  have hfact : (n.factorial : 𝕜) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  -- Clear the factorial denominator to recover the coefficient formula in the textbook form.
  have hmul := congrArg (fun t : 𝕜 ↦ t * n.factorial) hcoeff
  calc
    iteratedDeriv n φ 0 = (iteratedDeriv n φ 0 / n.factorial) * n.factorial := by
      field_simp [hfact]
    _ = a n * n.factorial := by simpa using hmul.symm
    _ = n.factorial * a n := by ring

/-- Helper for Exercise 13: the analytic quotient
`qₓ(z) = (deriv φ z - x) / (φ z - x * z)` has its canonical scalar power series at `0`, and the
shifted denominator multiplies `qₓ` back to `deriv φ - x` near `0`. -/
lemma shifted_regular_part_series_and_product {a : ℕ → 𝕜} {φ f : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (ha0 : a 0 ≠ 0)
    (hφ_eq : f =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * φ z)
    (x : 𝕜) :
    HasFPowerSeriesAt
        (fun z ↦ (deriv φ z - x) / (φ z - x * z))
        (.ofScalars 𝕜
          fun n ↦ iteratedDeriv n (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 / n.factorial)
        0 ∧
      (fun z ↦ (φ z - x * z) * ((deriv φ z - x) / (φ z - x * z))) =ᶠ[𝓝 (0 : 𝕜)]
        fun z ↦ deriv φ z - x := by
  obtain ⟨hquot_an, _⟩ :=
    simple_pole_logDeriv_sub_explicit_regular_part hφ_series ha0 hφ_eq x
  have hquot_series :
      HasFPowerSeriesAt
        (fun z ↦ (deriv φ z - x) / (φ z - x * z))
        (.ofScalars 𝕜
          fun n ↦ iteratedDeriv n (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 / n.factorial)
        0 :=
    hquot_an.hasFPowerSeriesAt
  have hφ0 : φ 0 = a 0 := by
    -- Read the constant coefficient of `φ` from its scalar power series.
    simpa using simple_pole_normal_form_iteratedDeriv_coeff hφ_series 0
  have hshift_an : AnalyticAt 𝕜 (fun z ↦ φ z - x * z) 0 := by
    -- The denominator remains analytic after subtracting the linear term `x * z`.
    simpa using hφ_series.analyticAt.sub (analyticAt_const.mul analyticAt_id)
  have hshift0 : φ 0 - x * 0 ≠ 0 := by
    -- Its value at `0` is still the nonzero constant term `a 0`.
    simpa [hφ0] using ha0
  have hshift_nonzero : ∀ᶠ z in 𝓝 (0 : 𝕜), φ z - x * z ≠ 0 := by
    -- Continuity turns the nonzero value at `0` into eventual nonvanishing.
    exact hshift_an.continuousAt.eventually_ne hshift0
  refine ⟨hquot_series, ?_⟩
  -- On the neighborhood where the denominator is nonzero, multiplication cancels the quotient.
  filter_upwards [hshift_nonzero] with z hz
  field_simp [hz]

/-- Helper for Exercise 13: the shifted denominator `z ↦ φ z - x * z` has the expected values of
its iterated derivatives at `0`. -/
lemma shifted_denominator_iteratedDeriv_at_zero {a : ℕ → 𝕜} {φ : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (x : 𝕜) :
    (fun z ↦ φ z - x * z) 0 = a 0 ∧
      iteratedDeriv 1 (fun z ↦ φ z - x * z) 0 = a 1 - x ∧
      ∀ n : ℕ,
        iteratedDeriv (n + 2) (fun z ↦ φ z - x * z) 0 = (n + 2).factorial * a (n + 2) := by
  have hφ_cont :
      ∀ n : ℕ, ContDiffAt 𝕜 n φ 0 := fun n ↦ hφ_series.analyticAt.contDiffAt
  have hlinear_cont :
      ∀ n : ℕ, ContDiffAt 𝕜 n (fun z : 𝕜 ↦ x * z) 0 := by
    intro n
    simpa using (contDiffAt_const.mul contDiffAt_id : ContDiffAt 𝕜 n (fun z : 𝕜 ↦ x * z) 0)
  have hφ0 : φ 0 = a 0 := by
    -- The zeroth iterated derivative recovers the constant coefficient.
    simpa using simple_pole_normal_form_iteratedDeriv_coeff hφ_series 0
  have hφ1 : iteratedDeriv 1 φ 0 = a 1 := by
    -- The first iterated derivative is the first scalar coefficient because `1! = 1`.
    simpa using simple_pole_normal_form_iteratedDeriv_coeff hφ_series 1
  have hlinear1 : iteratedDeriv 1 (fun z : 𝕜 ↦ x * z) 0 = x := by
    -- The linear correction contributes exactly `x` to the first derivative.
    calc
      iteratedDeriv 1 (fun z : 𝕜 ↦ x * z) 0
          = x * iteratedDeriv 1 (fun z : 𝕜 ↦ z) 0 := by
              simpa using
                (iteratedDeriv_const_mul_field (n := 1) (x := (0 : 𝕜))
                  (c := x) (f := fun z : 𝕜 ↦ z))
      _ = x := by simp [iteratedDeriv_fun_id_zero]
  refine ⟨?_, ?_, ?_⟩
  · -- Evaluating the shifted denominator at `0` removes the linear term `x * z`.
    calc
      (fun z ↦ φ z - x * z) 0 = φ 0 := by simp
      _ = a 0 := hφ0
  · -- The first derivative is the derivative of `φ` minus the slope `x`.
    calc
      iteratedDeriv 1 (fun z ↦ φ z - x * z) 0
          = iteratedDeriv 1 φ 0 - iteratedDeriv 1 (fun z : 𝕜 ↦ x * z) 0 := by
              simpa using
                (iteratedDeriv_sub (n := 1) (x := (0 : 𝕜)) (hf := hφ_cont 1)
                  (hg := hlinear_cont 1))
      _ = a 1 - x := by rw [hφ1, hlinear1]
  · intro n
    have hlinear_high : iteratedDeriv (n + 2) (fun z : 𝕜 ↦ x * z) 0 = 0 := by
      -- Every higher derivative of the linear correction vanishes at `0`.
      calc
        iteratedDeriv (n + 2) (fun z : 𝕜 ↦ x * z) 0
            = x * iteratedDeriv (n + 2) (fun z : 𝕜 ↦ z) 0 := by
                simpa using
                  (iteratedDeriv_const_mul_field (n := n + 2) (x := (0 : 𝕜))
                    (c := x) (f := fun z : 𝕜 ↦ z))
        _ = 0 := by
          have hneq : n + 2 ≠ 1 := by omega
          simp [iteratedDeriv_fun_id_zero, hneq]
    -- Route correction: the `x * z` term contributes only in derivative order `1`, so every
    -- higher derivative comes entirely from `φ`.
    calc
      iteratedDeriv (n + 2) (fun z ↦ φ z - x * z) 0
          = iteratedDeriv (n + 2) φ 0 - iteratedDeriv (n + 2) (fun z : 𝕜 ↦ x * z) 0 := by
              simpa using
                (iteratedDeriv_sub (n := n + 2) (x := (0 : 𝕜)) (hf := hφ_cont (n + 2))
                  (hg := hlinear_cont (n + 2)))
      _ = iteratedDeriv (n + 2) φ 0 := by rw [hlinear_high, sub_zero]
      _ = (n + 2).factorial * a (n + 2) :=
        simple_pole_normal_form_iteratedDeriv_coeff hφ_series (n + 2)

/-- Helper for Exercise 13: evaluating the shifted product identity at `0` gives the base
coefficient recurrence for the regular part. -/
lemma shifted_logderiv_base_identity {a : ℕ → 𝕜} {φ f : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (ha0 : a 0 ≠ 0)
    (hφ_eq : f =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * φ z)
    (x : 𝕜) :
    a 0 *
      (iteratedDeriv 0 (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 / (0 : ℕ).factorial) =
      a 1 - x := by
  obtain ⟨_, hprod⟩ := shifted_regular_part_series_and_product hφ_series ha0 hφ_eq x
  have hprod0 : (φ 0 - x * 0) * (((deriv φ 0 - x) / (φ 0 - x * 0))) = deriv φ 0 - x := by
    -- Evaluate the neighborhood identity exactly at the center.
    simpa using Filter.EventuallyEq.eq_of_nhds hprod
  have hφ0 : φ 0 = a 0 := by
    -- The constant coefficient of `φ` is its value at `0`.
    simpa using simple_pole_normal_form_iteratedDeriv_coeff hφ_series 0
  have hφ1 : deriv φ 0 = a 1 := by
    -- The first scalar coefficient is the first derivative at the center.
    simpa [iteratedDeriv_succ'] using simple_pole_normal_form_iteratedDeriv_coeff hφ_series 1
  -- After rewriting the zeroth coefficient as the value at `0`, the evaluated product identity
  -- is exactly the base recurrence.
  simpa [iteratedDeriv_zero, hφ0, hφ1] using hprod0

/-- Helper for Exercise 13: differentiating the shifted product identity `n + 1` times and
evaluating at `0` gives the raw Leibniz sum used in the coefficient recurrence. -/
lemma shifted_logderiv_product_iteratedDeriv_at_zero {a : ℕ → 𝕜} {φ f : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (ha0 : a 0 ≠ 0)
    (hφ_eq : f =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * φ z)
    (x : 𝕜) (n : ℕ) :
    Finset.sum (Finset.range (n + 2)) (fun i ↦
        (Nat.choose (n + 1) i : 𝕜) *
          iteratedDeriv i (fun z ↦ φ z - x * z) 0 *
          iteratedDeriv (n + 1 - i) (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0) =
      iteratedDeriv (n + 1) (fun z ↦ deriv φ z - x) 0 := by
  obtain ⟨hq_series, hprod⟩ := shifted_regular_part_series_and_product hφ_series ha0 hφ_eq x
  have hA_cont : ContDiffAt 𝕜 (n + 1) (fun z ↦ φ z - x * z) 0 := by
    -- The shifted denominator is analytic, so every iterated derivative needed by Leibniz exists.
    simpa using (hφ_series.analyticAt.sub (analyticAt_const.mul analyticAt_id)).contDiffAt
  have hq_cont :
      ContDiffAt 𝕜 (n + 1) (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 := by
    -- The regular part is analytic at `0`, so the product formula applies without transport.
    exact hq_series.analyticAt.contDiffAt
  have hmul :
      iteratedDeriv (n + 1)
          ((fun z ↦ φ z - x * z) * fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 =
        Finset.sum (Finset.range (n + 2)) (fun i ↦
          (Nat.choose (n + 1) i : 𝕜) *
            iteratedDeriv i (fun z ↦ φ z - x * z) 0 *
            iteratedDeriv (n + 1 - i) (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0) := by
    -- This is the raw Leibniz expansion before any factorial normalization.
    simpa [Nat.add_assoc] using
      (iteratedDeriv_mul (n := n + 1) (x := (0 : 𝕜))
        (f := fun z ↦ φ z - x * z)
        (g := fun z ↦ (deriv φ z - x) / (φ z - x * z))
        hA_cont hq_cont)
  have hiter :
      iteratedDeriv (n + 1)
          ((fun z ↦ φ z - x * z) * fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 =
        iteratedDeriv (n + 1) (fun z ↦ deriv φ z - x) 0 := by
    -- Differentiate the neighborhood identity instead of unfolding the quotient directly.
    exact Filter.EventuallyEq.iteratedDeriv_eq (n + 1) hprod
  calc
    Finset.sum (Finset.range (n + 2)) (fun i ↦
        (Nat.choose (n + 1) i : 𝕜) *
          iteratedDeriv i (fun z ↦ φ z - x * z) 0 *
          iteratedDeriv (n + 1 - i) (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0) =
        iteratedDeriv (n + 1)
          ((fun z ↦ φ z - x * z) * fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 := by
            exact hmul.symm
    _ = iteratedDeriv (n + 1) (fun z ↦ deriv φ z - x) 0 := hiter

/-- Helper for Exercise 13: the right-hand side of the raw differentiated product identity is the
stored coefficient `(n + 2)! • a (n + 2)` of the analytic unit `φ`. -/
lemma shifted_logderiv_numerator_iteratedDeriv_at_zero {a : ℕ → 𝕜} {φ : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (x : 𝕜) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z ↦ deriv φ z - x) 0 = (n + 2).factorial * a (n + 2) := by
  have hderiv_cont : ContDiffAt 𝕜 (n + 1) (fun z ↦ deriv φ z) 0 := by
    -- The numerator remains analytic because it is the derivative of the analytic unit `φ`.
    exact hφ_series.analyticAt.deriv.contDiffAt
  have hconst_cont : ContDiffAt 𝕜 (n + 1) (fun _ : 𝕜 ↦ x) 0 := by
    -- The constant subtraction term contributes no higher iterated derivatives.
    simpa using (contDiffAt_const : ContDiffAt 𝕜 (n + 1) (fun _ : 𝕜 ↦ x) 0)
  calc
    iteratedDeriv (n + 1) (fun z ↦ deriv φ z - x) 0
        = iteratedDeriv (n + 1) (fun z ↦ deriv φ z) 0 -
            iteratedDeriv (n + 1) (fun _ : 𝕜 ↦ x) 0 := by
              simpa using
                (iteratedDeriv_sub (n := n + 1) (x := (0 : 𝕜))
                  (hf := hderiv_cont) (hg := hconst_cont))
    _ = iteratedDeriv (n + 1) (fun z ↦ deriv φ z) 0 := by simp [iteratedDeriv_const]
    _ = iteratedDeriv (n + 2) φ 0 := by
      -- Rewrite the numerator as one more iterated derivative of `φ`.
      simpa [Nat.add_assoc] using congrFun (iteratedDeriv_succ' (n := n + 1) (f := φ)).symm 0
    _ = (n + 2).factorial * a (n + 2) :=
      simple_pole_normal_form_iteratedDeriv_coeff hφ_series (n + 2)

/-- Helper for Exercise 13: the normalized Taylor coefficients of the explicit shifted regular
part `z ↦ (deriv φ z - x) / (φ z - x * z)`. -/
noncomputable def shifted_regular_coeff (φ : 𝕜 → 𝕜) (x : 𝕜) (n : ℕ) : 𝕜 :=
  iteratedDeriv n (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 / n.factorial

/-- Helper for Exercise 13: multiplying the normalized shifted regular coefficient by `n!`
recovers the corresponding iterated derivative at `0`. -/
lemma shifted_regular_coeff_factorial_mul {φ : 𝕜 → 𝕜} (x : 𝕜) (n : ℕ) :
    iteratedDeriv n (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 =
      n.factorial * shifted_regular_coeff φ x n := by
  -- Expand the definition and clear the factorial denominator by a single field calculation.
  have hfact : (n.factorial : 𝕜) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  calc
    iteratedDeriv n (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0
        = (iteratedDeriv n (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0 / n.factorial) *
            n.factorial := by
              field_simp [hfact]
    _ = n.factorial * shifted_regular_coeff φ x n := by
          rw [mul_comm, shifted_regular_coeff]

/-- Helper for Exercise 13: the zeroth normalized coefficient of the explicit regular part is the
expected quotient `(a 0)⁻¹ (a 1 - x)`. -/
lemma shifted_regular_coeff_zero {a : ℕ → 𝕜} {φ f : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (ha0 : a 0 ≠ 0)
    (hφ_eq : f =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * φ z)
    (x : 𝕜) :
    shifted_regular_coeff φ x 0 = (a 0)⁻¹ * (a 1 - x) := by
  have hbase := shifted_logderiv_base_identity hφ_series ha0 hφ_eq x
  have hbase' : a 0 * shifted_regular_coeff φ x 0 = a 1 - x := by
    simpa [shifted_regular_coeff] using hbase
  -- Multiply the base identity by `(a 0)⁻¹` to solve for the normalized zeroth coefficient.
  calc
    shifted_regular_coeff φ x 0 = (a 0)⁻¹ * (a 0 * shifted_regular_coeff φ x 0) := by
      rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    _ = (a 0)⁻¹ * (a 1 - x) := by rw [hbase']

/-- Helper for Exercise 13: the normalized shifted coefficients satisfy the scalar recurrence
coming from the product identity `(φ z - x * z) * qₓ z = deriv φ z - x`. -/
lemma shifted_logderiv_product_iteratedDeriv_split {a : ℕ → 𝕜} {φ f : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (ha0 : a 0 ≠ 0)
    (hφ_eq : f =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * φ z)
    (x : 𝕜) (n : ℕ) :
    a 0 * shifted_regular_coeff φ x (n + 1) +
      (a 1 - x) * shifted_regular_coeff φ x n +
      Finset.sum (Finset.Icc 2 (n + 1))
        (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i)) =
      (n + 2 : 𝕜) * a (n + 2) := by
  have hraw := shifted_logderiv_product_iteratedDeriv_at_zero hφ_series ha0 hφ_eq x n
  rcases shifted_denominator_iteratedDeriv_at_zero hφ_series x with ⟨hden0, hden1, hdenhigh⟩
  let term : ℕ → 𝕜 := fun i ↦
    (Nat.choose (n + 1) i : 𝕜) *
      iteratedDeriv i (fun z ↦ φ z - x * z) 0 *
      iteratedDeriv (n + 1 - i) (fun z ↦ (deriv φ z - x) / (φ z - x * z)) 0
  let fact : 𝕜 := (n + 1).factorial
  have hfact : fact ≠ 0 := by
    dsimp [fact]
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  have hsplit :
      Finset.sum (Finset.range (n + 2)) term =
        term 0 + term 1 + Finset.sum (Finset.Icc 2 (n + 1)) term := by
    -- Split the raw Leibniz sum into the `i = 0`, `i = 1`, and `i ≥ 2` pieces used by the
    -- textbook coefficient comparison.
    calc
      Finset.sum (Finset.range (n + 2)) term = Finset.sum (Finset.Icc 0 (n + 1)) term := by
        rw [Nat.range_succ_eq_Icc_zero]
      _ = term 0 + Finset.sum (Finset.Icc 1 (n + 1)) term := by
        rw [show Finset.Icc 0 (n + 1) = insert 0 (Finset.Icc 1 (n + 1)) by
              simpa using
                (Finset.insert_Icc_add_one_left_eq_Icc (a := 0) (b := n + 1)
                  (Nat.zero_le _)).symm]
        rw [Finset.sum_insert]
        simp
      _ = term 0 + (term 1 + Finset.sum (Finset.Icc 2 (n + 1)) term) := by
        rw [show Finset.Icc 1 (n + 1) = insert 1 (Finset.Icc 2 (n + 1)) by
              simpa using
                (Finset.insert_Icc_add_one_left_eq_Icc (a := 1) (b := n + 1)
                  (Nat.succ_le_succ (Nat.zero_le n))).symm]
        rw [Finset.sum_insert]
        simp
      _ = term 0 + term 1 + Finset.sum (Finset.Icc 2 (n + 1)) term := by ring
  have hterm0 :
      term 0 = (a 0 * shifted_regular_coeff φ x (n + 1)) * fact := by
    -- The `i = 0` summand contributes the leading denominator coefficient `a 0`.
    have hφ0 : φ 0 = a 0 := by
      simpa using hden0
    dsimp [term, fact]
    rw [iteratedDeriv_zero, shifted_regular_coeff_factorial_mul]
    rw [hφ0]
    simp [Nat.choose_zero_right]
    ring
  have hterm1 :
      term 1 = ((a 1 - x) * shifted_regular_coeff φ x n) * fact := by
    -- The `i = 1` summand contributes the shifted linear coefficient `a 1 - x`.
    dsimp [term, fact]
    rw [hden1, shifted_regular_coeff_factorial_mul, Nat.choose_one_right, Nat.factorial_succ,
      Nat.cast_mul]
    ring_nf
  have htail_term :
      ∀ i ∈ Finset.Icc 2 (n + 1),
        term i = (a i * shifted_regular_coeff φ x (n + 1 - i)) * fact := by
    intro i hi
    have hi_two : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi_le : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
    have hderiv_i :
        iteratedDeriv i (fun z ↦ φ z - x * z) 0 = (i.factorial : 𝕜) * a i := by
      rw [show i = i - 2 + 2 by omega]
      simpa using hdenhigh (i - 2)
    have hchoose :
        ((Nat.choose (n + 1) i : 𝕜) * (i.factorial : 𝕜) * ((n + 1 - i).factorial : 𝕜)) =
          fact := by
      dsimp [fact]
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (n := n + 1) (k := i) hi_le
    -- Route correction: normalize the factorial/binomial factor once here, instead of repeating
    -- this algebra inside the scalar recurrence or the eval bridge.
    dsimp [term]
    rw [hderiv_i, shifted_regular_coeff_factorial_mul]
    calc
      (Nat.choose (n + 1) i : 𝕜) * ((i.factorial : 𝕜) * a i) *
          (((n + 1 - i).factorial : 𝕜) * shifted_regular_coeff φ x (n + 1 - i))
          = ((Nat.choose (n + 1) i : 𝕜) * (i.factorial : 𝕜) *
              ((n + 1 - i).factorial : 𝕜)) *
              (a i * shifted_regular_coeff φ x (n + 1 - i)) := by
              ring
      _ = fact * (a i * shifted_regular_coeff φ x (n + 1 - i)) := by rw [hchoose]
      _ = (a i * shifted_regular_coeff φ x (n + 1 - i)) * fact := by ring
  have htail :
      Finset.sum (Finset.Icc 2 (n + 1)) term =
        (Finset.sum (Finset.Icc 2 (n + 1))
          (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i))) * fact := by
    -- After the normalization, every tail summand carries the same factorial factor.
    calc
      Finset.sum (Finset.Icc 2 (n + 1)) term =
          Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ (a i * shifted_regular_coeff φ x (n + 1 - i)) * fact) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact htail_term i hi
      _ =
          (Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i))) * fact := by
              rw [Finset.sum_mul]
  have hnormalized :
      (a 0 * shifted_regular_coeff φ x (n + 1) +
          (a 1 - x) * shifted_regular_coeff φ x n +
          Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i))) * fact =
        ((n + 2 : 𝕜) * a (n + 2)) * fact := by
    have hfactorial_succ_cast :
        ((((n + 2).factorial : ℕ) : 𝕜)) = (n + 2 : 𝕜) * fact := by
      -- Rewrite the numerator factorial once before reattaching the coefficient `a (n + 2)`.
      dsimp [fact]
      rw [Nat.factorial_succ, Nat.cast_mul]
      congr 1
      have hone : (1 : 𝕜) + 1 = 2 := by norm_num
      simpa [add_assoc, hone]
    -- Compare the split-and-normalized Leibniz sum with the normalized numerator coefficient.
    calc
      (a 0 * shifted_regular_coeff φ x (n + 1) +
          (a 1 - x) * shifted_regular_coeff φ x n +
          Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i))) * fact
          = term 0 + term 1 + Finset.sum (Finset.Icc 2 (n + 1)) term := by
              rw [hterm0, hterm1, htail]
              ring
      _ = Finset.sum (Finset.range (n + 2)) term := by rw [hsplit]
      _ = iteratedDeriv (n + 1) (fun z ↦ deriv φ z - x) 0 := hraw
      _ = (((n + 2).factorial : ℕ) : 𝕜) * a (n + 2) := by
            rw [shifted_logderiv_numerator_iteratedDeriv_at_zero hφ_series x n]
      _ = ((n + 2 : 𝕜) * fact) * a (n + 2) := by
            rw [hfactorial_succ_cast]
      _ = ((n + 2 : 𝕜) * a (n + 2)) * fact := by ring
  exact mul_right_cancel₀ hfact hnormalized

/-- Helper for Exercise 13: the normalized shifted coefficients satisfy the scalar recurrence
coming from the product identity `(φ z - x * z) * qₓ z = deriv φ z - x`. -/
lemma shifted_regular_coeff_succ {a : ℕ → 𝕜} {φ f : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (ha0 : a 0 ≠ 0)
    (hφ_eq : f =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * φ z)
    (x : 𝕜) (n : ℕ) :
    shifted_regular_coeff φ x (n + 1) =
      (a 0)⁻¹ *
        ((n + 2 : 𝕜) * a (n + 2) -
          (a 1 - x) * shifted_regular_coeff φ x n -
          Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i))) := by
  have hsplit := shifted_logderiv_product_iteratedDeriv_split hφ_series ha0 hφ_eq x n
  have hsolve :
      a 0 * shifted_regular_coeff φ x (n + 1) =
        (n + 2 : 𝕜) * a (n + 2) -
          (a 1 - x) * shifted_regular_coeff φ x n -
          Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i)) := by
    -- Move the lower-order terms to the right-hand side before dividing by `a 0`.
    calc
      a 0 * shifted_regular_coeff φ x (n + 1)
          = (a 0 * shifted_regular_coeff φ x (n + 1) +
              (a 1 - x) * shifted_regular_coeff φ x n +
              Finset.sum (Finset.Icc 2 (n + 1))
                (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i))) -
              ((a 1 - x) * shifted_regular_coeff φ x n +
                Finset.sum (Finset.Icc 2 (n + 1))
                  (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i))) := by
              ring
      _ = (n + 2 : 𝕜) * a (n + 2) -
            ((a 1 - x) * shifted_regular_coeff φ x n +
              Finset.sum (Finset.Icc 2 (n + 1))
                (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i))) := by
              rw [hsplit]
      _ = (n + 2 : 𝕜) * a (n + 2) -
            (a 1 - x) * shifted_regular_coeff φ x n -
            Finset.sum (Finset.Icc 2 (n + 1))
              (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i)) := by
              ring
  -- Multiply by `(a 0)⁻¹` to solve for the new coefficient.
  calc
    shifted_regular_coeff φ x (n + 1)
        = (a 0)⁻¹ * (a 0 * shifted_regular_coeff φ x (n + 1)) := by
            rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    _ = (a 0)⁻¹ *
          ((n + 2 : 𝕜) * a (n + 2) -
            (a 1 - x) * shifted_regular_coeff φ x n -
            Finset.sum (Finset.Icc 2 (n + 1))
              (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i))) := by
            rw [hsolve]

/-- Helper for Exercise 13: every tail index appearing in the coefficient recurrence is strictly
smaller than the current stage. -/
lemma shifted_regular_coeff_tail_lt_of_mem {n i : ℕ} (hi : i ∈ Finset.Icc 2 (n + 1)) :
    n + 1 - i < n + 1 := by
  -- Membership in `Icc 2 (n + 1)` gives the upper bound needed for the recursive call.
  have hi_two : 2 ≤ i := (Finset.mem_Icc.mp hi).1
  have hi_le : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
  omega

/-- Helper for Exercise 13: the attached tail indices in the strong-recursive polynomial family are
strictly smaller than the current stage. -/
lemma shifted_regular_coeff_tail_lt {n : ℕ}
    (i : {i // i ∈ Finset.Icc 2 (n + 1)}) :
    n + 1 - (i : ℕ) < n + 1 := by
  -- This is the subtype-packaged version used inside the proof-free recursive definition.
  exact shifted_regular_coeff_tail_lt_of_mem i.property

/-- Helper for Exercise 13: the universal polynomial family satisfying the same recurrence as the
normalized shifted regular coefficients. -/
noncomputable def shifted_regular_coeff_polynomial (a : ℕ → 𝕜) : ℕ → Polynomial 𝕜 :=
  fun n ↦
    Nat.strongRecOn' n fun n U ↦
      match n with
      | 0 =>
          Polynomial.C ((a 0)⁻¹) * (Polynomial.C (a 1) - Polynomial.X)
      | n + 1 =>
          Polynomial.C ((a 0)⁻¹) *
            (Polynomial.C ((n + 2 : 𝕜) * a (n + 2)) -
              (Polynomial.C (a 1) - Polynomial.X) * U n (Nat.lt_succ_self n) -
              Finset.sum ((Finset.Icc 2 (n + 1)).attach)
                (fun i ↦
                  Polynomial.C (a i) *
                    U (n + 1 - i) (shifted_regular_coeff_tail_lt (n := n) i)))

/-- Helper for Exercise 13: the strong-recursive polynomial family starts with the expected linear
polynomial. -/
lemma shifted_regular_coeff_polynomial_zero (a : ℕ → 𝕜) :
    shifted_regular_coeff_polynomial a 0 =
      Polynomial.C ((a 0)⁻¹) * (Polynomial.C (a 1) - Polynomial.X) := by
  -- Evaluate the strong recursion at the initial stage.
  rw [shifted_regular_coeff_polynomial, Nat.strongRecOn'_beta]

/-- Helper for Exercise 13: removing the attached tail index from the recursive polynomial sum
produces the ordinary `Finset.Icc` tail used in the textbook recurrence. -/
lemma shifted_regular_coeff_polynomial_tail_sum (a : ℕ → 𝕜) (n : ℕ) :
    Finset.sum ((Finset.Icc 2 (n + 1)).attach)
      (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i)) =
    Finset.sum (Finset.Icc 2 (n + 1))
      (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i)) := by
  -- Strip off the subtype wrapper once so every downstream proof can work with ordinary indices.
  simpa using
    (Finset.Icc 2 (n + 1)).sum_attach
      (fun j ↦ Polynomial.C (a j) * shifted_regular_coeff_polynomial a (n + 1 - j))

/-- Helper for Exercise 13: the strong-recursive polynomial family satisfies the coefficient
recurrence at stage `n + 1`. -/
lemma shifted_regular_coeff_polynomial_succ (a : ℕ → 𝕜) (n : ℕ) :
    shifted_regular_coeff_polynomial a (n + 1) =
      Polynomial.C ((a 0)⁻¹) *
        (Polynomial.C ((n + 2 : 𝕜) * a (n + 2)) -
          (Polynomial.C (a 1) - Polynomial.X) * shifted_regular_coeff_polynomial a n -
          Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i))) := by
  -- Unfold the strong recursion exactly once, then rewrite the attached tail through the clean
  -- polynomial family wrapper.
  calc
    shifted_regular_coeff_polynomial a (n + 1)
        =
          Polynomial.C ((a 0)⁻¹) *
            (Polynomial.C ((n + 2 : 𝕜) * a (n + 2)) -
              (Polynomial.C (a 1) - Polynomial.X) * shifted_regular_coeff_polynomial a n -
              Finset.sum ((Finset.Icc 2 (n + 1)).attach)
                (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i))) := by
          rw [shifted_regular_coeff_polynomial, Nat.strongRecOn'_beta]
          rfl
    _ = Polynomial.C ((a 0)⁻¹) *
          (Polynomial.C ((n + 2 : 𝕜) * a (n + 2)) -
            (Polynomial.C (a 1) - Polynomial.X) * shifted_regular_coeff_polynomial a n -
            Finset.sum (Finset.Icc 2 (n + 1))
              (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i))) := by
          rw [shifted_regular_coeff_polynomial_tail_sum]

/-- Helper for Exercise 13: the linear polynomial `C c - X` has degree at most `1`. -/
lemma natDegree_C_sub_X_le (c : 𝕜) :
    (Polynomial.C c - Polynomial.X).natDegree ≤ 1 := by
  -- Rewrite to the standard owner lemma for `X - C c`; negation does not change the degree.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (Polynomial.natDegree_X_sub_C_le c :
      (Polynomial.X - Polynomial.C c).natDegree ≤ 1)

/-- Helper for Exercise 13: evaluating the universal polynomial recurrence at `x` reproduces the
normalized Taylor coefficients of the explicit shifted regular part. -/
lemma shifted_regular_coeff_polynomial_eval_tail_sum {a : ℕ → 𝕜} (x : 𝕜) (n : ℕ) :
    Polynomial.eval x
      (Finset.sum (Finset.Icc 2 (n + 1))
        (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i))) =
      Finset.sum (Finset.Icc 2 (n + 1))
        (fun i ↦ a i * Polynomial.eval x (shifted_regular_coeff_polynomial a (n + 1 - i))) := by
  -- Push `Polynomial.eval` through the tail sum so the induction hypotheses can be applied
  -- termwise.
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Polynomial.eval_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 13: evaluating the universal polynomial recurrence at `x` reproduces the
normalized Taylor coefficients of the explicit shifted regular part. -/
lemma shifted_regular_coeff_polynomial_eval {a : ℕ → 𝕜} {φ f : 𝕜 → 𝕜}
    (hφ_series : HasFPowerSeriesAt φ (.ofScalars 𝕜 a) 0)
    (ha0 : a 0 ≠ 0)
    (hφ_eq : f =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ z⁻¹ * φ z)
    (x : 𝕜) (n : ℕ) :
    Polynomial.eval x (shifted_regular_coeff_polynomial a n) = shifted_regular_coeff φ x n := by
  refine Nat.strongRecOn' n ?_
  intro n ih
  cases n with
  | zero =>
      -- The base polynomial evaluates to the zeroth scalar coefficient directly.
      rw [shifted_regular_coeff_polynomial_zero, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_C, Polynomial.eval_X]
      simpa using (shifted_regular_coeff_zero hφ_series ha0 hφ_eq x).symm
  | succ n =>
      -- Route correction: evaluate the clean polynomial recurrence and match it against the clean
      -- scalar recurrence, rather than reopening the raw Leibniz identity.
      rw [shifted_regular_coeff_polynomial_succ, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_C, Polynomial.eval_X,
        shifted_regular_coeff_polynomial_eval_tail_sum]
      have hrec :
          Polynomial.eval x (shifted_regular_coeff_polynomial a n) =
            shifted_regular_coeff φ x n :=
        ih n (Nat.lt_succ_self n)
      have htail :
          Finset.sum (Finset.Icc 2 (n + 1))
              (fun i ↦ a i * Polynomial.eval x (shifted_regular_coeff_polynomial a (n + 1 - i))) =
            Finset.sum (Finset.Icc 2 (n + 1))
              (fun i ↦ a i * shifted_regular_coeff φ x (n + 1 - i)) := by
        -- Every tail index is strictly smaller, so the strong induction hypothesis applies.
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [ih (n + 1 - i) (shifted_regular_coeff_tail_lt_of_mem hi)]
      simpa [hrec, htail] using (shifted_regular_coeff_succ hφ_series ha0 hφ_eq x n).symm

/-- Helper for Exercise 13: every stage of the universal polynomial recurrence has degree at most
`n + 1`. -/
lemma shifted_regular_coeff_polynomial_natDegree_le {a : ℕ → 𝕜} :
    ∀ n : ℕ, (shifted_regular_coeff_polynomial a n).natDegree ≤ n + 1 := by
  intro n
  refine Nat.strongRecOn' n ?_
  intro n ih
  cases n with
  | zero =>
      -- The initial polynomial is linear, so its degree is at most `1`.
      simpa [shifted_regular_coeff_polynomial_zero] using
        (Polynomial.natDegree_C_mul_le ((a 0)⁻¹) (Polynomial.C (a 1) - Polynomial.X)).trans
          (natDegree_C_sub_X_le (a 1))
  | succ n =>
      -- Route correction: after the cleaned successor recurrence, the degree bound is a direct
      -- induction using one product bound and one tail-sum bound.
      rw [shifted_regular_coeff_polynomial_succ]
      have hconst :
          (Polynomial.C ((n + 2 : 𝕜) * a (n + 2))).natDegree ≤ n + 2 := by
        rw [Polynomial.natDegree_C]
        omega
      have hprod :
          ((Polynomial.C (a 1) - Polynomial.X) * shifted_regular_coeff_polynomial a n).natDegree ≤
            n + 2 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Polynomial.natDegree_mul_le_of_le (m := 1) (n := n + 1)
            (natDegree_C_sub_X_le (a 1)) (ih n (Nat.lt_succ_self n)))
      have htail :
          (Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i))).natDegree
            ≤ n + 2 := by
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
        intro i hi
        have hrec := ih (n + 1 - i) (shifted_regular_coeff_tail_lt_of_mem hi)
        exact (Polynomial.natDegree_C_mul_le (a i)
          (shifted_regular_coeff_polynomial a (n + 1 - i))).trans <| by
            omega
      have hsub :
          (Polynomial.C ((n + 2 : 𝕜) * a (n + 2)) -
              (Polynomial.C (a 1) - Polynomial.X) * shifted_regular_coeff_polynomial a n).natDegree
            ≤ n + 2 :=
        by
          simpa using
            (Polynomial.natDegree_sub_le_of_le (m := n + 2) (n := n + 2) hconst hprod)
      exact (Polynomial.natDegree_C_mul_le ((a 0)⁻¹) _).trans
        (by
          simpa using
            (Polynomial.natDegree_sub_le_of_le (m := n + 2) (n := n + 2) hsub htail))

/-- Helper for Exercise 13: the coefficient of `X^(n + 1)` in the universal recurrence is exactly
`-((a 0)⁻¹)^(n + 1)`. -/
lemma shifted_regular_coeff_polynomial_top_coeff {a : ℕ → 𝕜} :
    ∀ n : ℕ,
      (shifted_regular_coeff_polynomial a n).coeff (n + 1) = -((a 0)⁻¹) ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
      -- Read the coefficient of `X` directly from the initial linear polynomial.
      rw [shifted_regular_coeff_polynomial_zero, Polynomial.coeff_C_mul]
      simp [pow_one, mul_comm]
  | succ n ih =>
      -- In the successor recurrence, only the `X * Uₙ` term can contribute to degree `n + 2`.
      rw [shifted_regular_coeff_polynomial_succ, Polynomial.coeff_C_mul]
      have hhigh :
          (shifted_regular_coeff_polynomial a n).coeff (n + 2) = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt <|
          (shifted_regular_coeff_polynomial_natDegree_le (a := a) n).trans_lt (by omega)
      have htail_degree :
          (Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i))).natDegree
            ≤ n := by
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
        intro i hi
        have hi_two : 2 ≤ i := (Finset.mem_Icc.mp hi).1
        have hi_le : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
        have hrec := shifted_regular_coeff_polynomial_natDegree_le (a := a) (n + 1 - i)
        exact (Polynomial.natDegree_C_mul_le (a i)
          (shifted_regular_coeff_polynomial a (n + 1 - i))).trans <|
          hrec.trans <| by
            omega
      have htail :
          (Finset.sum (Finset.Icc 2 (n + 1))
            (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i))).coeff
            (n + 2) = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt <| htail_degree.trans_lt (by omega)
      have hprod :
          (((Polynomial.C (a 1) - Polynomial.X) * shifted_regular_coeff_polynomial a n).coeff
            (n + 2)) =
            -((shifted_regular_coeff_polynomial a n).coeff (n + 1)) := by
        -- The `C (a 1)` piece is too small in degree, so only the `-X` shift survives.
        rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
        rw [hhigh]
        ring
      have hinner :
          (Polynomial.C ((n + 2 : 𝕜) * a (n + 2)) -
              (Polynomial.C (a 1) - Polynomial.X) * shifted_regular_coeff_polynomial a n -
              Finset.sum (Finset.Icc 2 (n + 1))
                (fun i ↦ Polynomial.C (a i) * shifted_regular_coeff_polynomial a (n + 1 - i))).coeff
              (n + 2) =
            (shifted_regular_coeff_polynomial a n).coeff (n + 1) := by
        -- The constant term and the whole tail vanish in degree `n + 2`.
        rw [Polynomial.coeff_sub, Polynomial.coeff_sub, htail]
        simp [hprod]
      rw [hinner, ih]
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 13: the universal recurrence polynomial at stage `n` has exact degree
`n + 1` as soon as the constant denominator coefficient `a 0` is nonzero. -/
lemma shifted_regular_coeff_polynomial_natDegree {a : ℕ → 𝕜} (ha0 : a 0 ≠ 0) :
    ∀ n : ℕ, (shifted_regular_coeff_polynomial a n).natDegree = n + 1 := by
  intro n
  -- Exact degree follows once the top coefficient is known to be nonzero.
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (shifted_regular_coeff_polynomial_natDegree_le (a := a) n) ?_
  rw [shifted_regular_coeff_polynomial_top_coeff]
  exact neg_ne_zero.mpr <| pow_ne_zero _ (inv_ne_zero ha0)

/-- Exercise 13: if `f` has a simple pole at the origin, then the Laurent expansion of
`logDeriv (fun z ↦ f z - x)` (equivalently, `f' / (f - x)`) has principal part `-1 / z`, and the
coefficient of `z^n` in the regular part is the evaluation at `x` of a polynomial of degree
`n + 1`; equivalently, the regular part is a scalar power series whose coefficients are polynomial
in `x`. -/
theorem simple_pole_logDeriv_sub_laurent_polynomial_coeffs
    {f : 𝕜 → 𝕜} (horder : meromorphicOrderAt f 0 = (-1 : ℤ)) :
    ∃ U : ℕ → Polynomial 𝕜,
      (∀ n : ℕ, (U n).natDegree = n + 1) ∧
      ∀ x : 𝕜,
        ∃ g : 𝕜 → 𝕜,
          HasFPowerSeriesAt g
            (.ofScalars 𝕜 fun n ↦ Polynomial.eval x (U n))
            0 ∧
          logDeriv (fun z ↦ f z - x) =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ -1 / z + g z := by
  -- Follow the source proof up to the analytic normal form `f(z) = z⁻¹ φ(z)`.
  obtain ⟨a, φ, hφ_series, ha0, hφ_eq⟩ := simple_pole_normal_form_at_zero horder
  -- Route correction: keep the textbook quotient
  -- `qₓ(z) = (deriv φ z - x) / (φ z - x * z)` and transfer its normalized coefficient recurrence
  -- directly into `Polynomial 𝕜`.
  refine ⟨shifted_regular_coeff_polynomial a, shifted_regular_coeff_polynomial_natDegree ha0, ?_⟩
  intro x
  let g : 𝕜 → 𝕜 := fun z ↦ (deriv φ z - x) / (φ z - x * z)
  have hseries :
      HasFPowerSeriesAt g (.ofScalars 𝕜 fun n ↦ shifted_regular_coeff φ x n) 0 := by
    -- The regular part already has its analytic scalar power series at `0`.
    simpa [g, shifted_regular_coeff] using
      (shifted_regular_part_series_and_product hφ_series ha0 hφ_eq x).1
  have hcoeff_eq :
      (fun n ↦ shifted_regular_coeff φ x n) =
        fun n ↦ Polynomial.eval x (shifted_regular_coeff_polynomial a n) := by
    -- The universal polynomial recurrence evaluates to the actual scalar coefficient sequence.
    funext n
    symm
    exact shifted_regular_coeff_polynomial_eval hφ_series ha0 hφ_eq x n
  have hlog :
      logDeriv (fun z ↦ f z - x) =ᶠ[𝓝[≠] (0 : 𝕜)] fun z ↦ -1 / z + g z := by
    -- The punctured-neighborhood identity was already established for the same explicit quotient.
    simpa [g] using (simple_pole_logDeriv_sub_explicit_regular_part hφ_series ha0 hφ_eq x).2
  refine ⟨g, ?_, hlog⟩
  -- Reindex the already-known scalar series by the evaluated polynomial coefficient family.
  simpa [hcoeff_eq] using hseries

end
