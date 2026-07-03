import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped ENNReal NNReal

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Helper for Exercise 6: evaluating the derivative series of a scalar power series at `1`
recovers the usual derived scalar coefficient sequence. -/
theorem apply_one_comp_derivSeries_ofScalars (a : ℕ → 𝕂) :
    (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries
        ((ofScalars 𝕂 a).derivSeries) =
      ofScalars 𝕂 (fun n ↦ (n.succ : 𝕂) * a n.succ) := by
  -- The derivative-series coefficient is the multilinear coefficient evaluated on `1`.
  ext n
  simp [coeff_ofScalars, derivSeries_coeff_one, smul_eq_mul]

/-- Helper for Exercise 6: summing the evaluated derivative series yields the scalar derived
series. -/
theorem derivSeries_sum_apply_one_ofScalars (a : ℕ → 𝕂) {z : 𝕂}
    (hz : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕂 a).derivSeries.radius) :
    (ofScalars 𝕂 a).derivSeries.sum z 1 =
      ofScalarsSum (fun n ↦ (n.succ : 𝕂) * a n.succ) z := by
  -- First package the derivative series as a summable family and apply the map `f ↦ f 1`.
  have hsummable : Summable (fun n : ℕ ↦ (ofScalars 𝕂 a).derivSeries n fun _ ↦ z) := by
    apply FormalMultilinearSeries.summable
    simpa [Metric.mem_eball, edist_zero_right] using hz
  have hmap := hsummable.hasSum.mapL (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂))
  have hsum :
      (((ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries
          ((ofScalars 𝕂 a).derivSeries)).sum z) =
        (ofScalars 𝕂 a).derivSeries.sum z 1 := by
    simpa [FormalMultilinearSeries.sum, ContinuousLinearMap.compFormalMultilinearSeries_apply] using
      hmap.tsum_eq
  -- Then identify the mapped series coefficientwise with the usual scalar derivative series.
  calc
    (ofScalars 𝕂 a).derivSeries.sum z 1 =
        (((ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries
            ((ofScalars 𝕂 a).derivSeries)).sum z) := hsum.symm
    _ = ofScalarsSum (fun n ↦ (n.succ : 𝕂) * a n.succ) z := by
      simpa [ofScalarsSum] using
        congrArg (fun p : FormalMultilinearSeries 𝕂 𝕂 𝕂 ↦ p.sum z)
          (apply_one_comp_derivSeries_ofScalars a)

/-- Helper for Exercise 6: inside the disk of convergence, the derivative of the scalar power
series `ofScalarsSum a` is obtained by termwise differentiation. -/
theorem hasDerivAt_ofScalarsSum_of_mem_radius (a : ℕ → 𝕂) {z : 𝕂}
    (hz : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕂 a).radius) :
    HasDerivAt (ofScalarsSum a) (ofScalarsSum (fun n ↦ (n.succ : 𝕂) * a n.succ) z) z := by
  let p : FormalMultilinearSeries 𝕂 𝕂 𝕂 := ofScalars 𝕂 a
  have hzp : (‖z‖₊ : ℝ≥0∞) < p.radius := by
    simpa [p] using hz
  have hp0 : 0 < p.radius := lt_of_le_of_lt (by simp) hzp
  have hp : HasFPowerSeriesOnBall (ofScalarsSum a) p 0 p.radius := p.hasFPowerSeriesOnBall hp0
  have hf : HasFDerivAt (ofScalarsSum a)
      (continuousMultilinearCurryFin1 𝕂 𝕂 𝕂 (p.changeOrigin z 1)) z := by
    -- The analytic expansion on the convergence disk provides the Fréchet derivative at `z`.
    simpa [p] using hp.hasFDerivAt hzp
  have hs :
      fderiv 𝕂 (ofScalarsSum a) z = p.derivSeries.sum z := by
    -- The derivative power series at `z` is the sum of the derived formal series.
    simpa [p] using hp.fderiv.sum (by simpa [Metric.mem_eball, edist_zero_right] using hzp)
  have hs' :
      continuousMultilinearCurryFin1 𝕂 𝕂 𝕂 (p.changeOrigin z 1) 1 =
        ofScalarsSum (fun n ↦ (n.succ : 𝕂) * a n.succ) z := by
    -- Evaluate the Fréchet derivative at `1` to recover the scalar derivative coefficient sum.
    calc
      continuousMultilinearCurryFin1 𝕂 𝕂 𝕂 (p.changeOrigin z 1) 1 = p.derivSeries.sum z 1 := by
        rw [← hs]
        exact (congrArg (fun f ↦ f 1) hf.fderiv).symm
      _ = ofScalarsSum (fun n ↦ (n.succ : 𝕂) * a n.succ) z := by
        apply derivSeries_sum_apply_one_ofScalars
        simpa [p] using hz.trans_le p.radius_le_radius_derivSeries
  -- Convert the Fréchet derivative statement into the scalar derivative statement.
  simpa using hf.hasDerivAt.congr_deriv hs'

/-- Helper for Exercise 6: if `c` is not a nonpositive integer, then the ordinary hypergeometric
series has positive radius of convergence. -/
theorem ordinary_hypergeometric_radius_pos_of_c_not_neg_nat (a b c : 𝕂)
    (hc : ∀ n : ℕ, c ≠ -(n : 𝕂)) :
    0 < (ordinaryHypergeometricSeries 𝕂 a b c).radius := by
  -- The terminating cases reduce to the already proved infinite-radius theorem.
  by_cases hab : ∃ n : ℕ, a = -(n : 𝕂) ∨ b = -(n : 𝕂)
  · obtain ⟨n, hna | hnb⟩ := hab
    · rw [hna]
      have hr :
          (ordinaryHypergeometricSeries 𝕂 (-(n : 𝕂)) b c).radius = ⊤ := by
        simpa using
          (ordinaryHypergeometric_radius_top_of_neg_nat₁ 𝕂 b c :
            (ordinaryHypergeometricSeries 𝕂 (-(n : 𝕂)) b c).radius = ⊤)
      rw [hr]
      simp
    · rw [hnb]
      have hr :
          (ordinaryHypergeometricSeries 𝕂 a (-(n : 𝕂)) c).radius = ⊤ := by
        simpa using
          (ordinaryHypergeometric_radius_top_of_neg_nat₂ 𝕂 a c :
            (ordinaryHypergeometricSeries 𝕂 a (-(n : 𝕂)) c).radius = ⊤)
      rw [hr]
      simp
  -- Otherwise the series is genuinely infinite and mathlib identifies the radius as `1`.
  · have habc : ∀ n : ℕ, (n : 𝕂) ≠ -a ∧ (n : 𝕂) ≠ -b ∧ (n : 𝕂) ≠ -c := by
      intro n
      refine ⟨?_, ?_, ?_⟩
      · intro hna
        have hna' : a = -(n : 𝕂) := by
          have hneg := congrArg Neg.neg hna
          simpa using hneg.symm
        apply hab
        exact ⟨n, Or.inl hna'⟩
      · intro hnb
        have hnb' : b = -(n : 𝕂) := by
          have hneg := congrArg Neg.neg hnb
          simpa using hneg.symm
        apply hab
        exact ⟨n, Or.inr hnb'⟩
      · intro hnc
        apply hc n
        have hneg := congrArg Neg.neg hnc
        simpa using hneg.symm
    rw [ordinaryHypergeometricSeries_radius_eq_one 𝕂 a b c habc]
    simp

/-- Helper for Exercise 6: the hypergeometric coefficient sequence satisfies the standard
first-order recurrence. -/
theorem ordinary_hypergeometric_coefficient_recurrence (a b c : 𝕂)
    (hc : ∀ n : ℕ, c ≠ -(n : 𝕂)) (n : ℕ) :
    ((n + 1 : 𝕂) * (c + n)) * ordinaryHypergeometricCoefficient a b c (n + 1) =
      (a + n) * (b + n) * ordinaryHypergeometricCoefficient a b c n := by
  -- The denominator factors are nonzero because the `c`-parameter avoids nonpositive integers.
  have hc_add_ne_zero : c + n ≠ 0 := by
    intro hzero
    exact hc n (eq_neg_of_add_eq_zero_left hzero)
  have hc_poch_ne_zero : (ascPochhammer 𝕂 n).eval c ≠ 0 := by
    intro hzero
    rcases (ascPochhammer_eval_eq_zero_iff n c).1 hzero with ⟨k, hk, hkc⟩
    apply hc k
    have hneg := congrArg Neg.neg hkc
    simpa using hneg.symm
  have hfac_ne_zero : ((n.factorial : ℕ) : 𝕂) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hsuc_ne_zero : (n + 1 : 𝕂) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  -- After expanding the coefficient formula, the recurrence is a direct field-algebra identity.
  rw [ordinaryHypergeometricCoefficient, ordinaryHypergeometricCoefficient, Nat.factorial_succ,
    ascPochhammer_succ_eval, ascPochhammer_succ_eval, ascPochhammer_succ_eval]
  field_simp [hc_add_ne_zero, hc_poch_ne_zero, hfac_ne_zero, hsuc_ne_zero]
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring_nf

/-- Helper for Exercise 6: the `n`-th coefficient of the twice-derived scalar power series is the
expected second derived coefficient. -/
theorem derivSeries_derivSeries_apply_apply_one_one_ofScalars (a : ℕ → 𝕂) (n : ℕ) (z : 𝕂) :
    (((ofScalars 𝕂 a).derivSeries).derivSeries n fun _ ↦ z) 1 1 =
      (((n.succ : 𝕂) * (n.succ.succ : 𝕂)) * a n.succ.succ) * z ^ n := by
  -- Evaluating the two derivative series at `(1,1)` just reads off the second scalar derivative.
  cases n <;> simp [coeff_ofScalars, derivSeries_coeff_one, smul_eq_mul, mul_assoc, mul_comm]
  ring

/-- Helper for Exercise 6: evaluating the twice-derived scalar power series at `(1, 1)` gives the
usual second derived coefficient sequence. -/
theorem derivSeries_derivSeries_sum_apply_one_apply_one_ofScalars (a : ℕ → 𝕂) {z : 𝕂}
    (hz : (‖z‖₊ : ℝ≥0∞) < ((ofScalars 𝕂 a).derivSeries).derivSeries.radius) :
    (((ofScalars 𝕂 a).derivSeries).derivSeries.sum z) 1 1 =
      ofScalarsSum (fun n ↦ ((n.succ : 𝕂) * (n.succ.succ : 𝕂)) * a n.succ.succ) z := by
  -- Map the second derivative series first by evaluation at `1`, then once more at `1`.
  have hsummable :
      Summable (fun n : ℕ ↦ ((ofScalars 𝕂 a).derivSeries).derivSeries n fun _ ↦ z) := by
    apply FormalMultilinearSeries.summable
    simpa [Metric.mem_eball, edist_zero_right] using hz
  have hmap₁ := hsummable.hasSum.mapL (ContinuousLinearMap.apply 𝕂 (𝕂 →L[𝕂] 𝕂) (1 : 𝕂))
  have hmap₂ := hmap₁.mapL (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂))
  have hsum :
      (((ofScalars 𝕂 a).derivSeries).derivSeries.sum z) 1 1 =
        ∑' n : ℕ, (((ofScalars 𝕂 a).derivSeries).derivSeries n fun _ ↦ z) 1 1 := by
    exact hmap₂.tsum_eq.symm
  -- The coefficientwise evaluation simplifies to the expected factor `(n+1)(n+2)`.
  calc
    (((ofScalars 𝕂 a).derivSeries).derivSeries.sum z) 1 1 =
        ∑' n : ℕ, (((ofScalars 𝕂 a).derivSeries).derivSeries n fun _ ↦ z) 1 1 := hsum
    _ = ∑' n : ℕ, (((n.succ : 𝕂) * (n.succ.succ : 𝕂)) * a n.succ.succ) * z ^ n := by
      refine tsum_congr fun n ↦ derivSeries_derivSeries_apply_apply_one_one_ofScalars a n z
    _ = ofScalarsSum (fun n ↦ ((n.succ : 𝕂) * (n.succ.succ : 𝕂)) * a n.succ.succ) z := by
      rw [ofScalars_sum_eq]
      simp [smul_eq_mul]

/-- Helper for Exercise 6: on the convergence disk, the derivative of `₂F₁ a b c` is the termwise
derived scalar series. -/
theorem ordinary_hypergeometric_deriv_eq_tsum (a b c z : 𝕂)
    (hc : ∀ n : ℕ, c ≠ -(n : 𝕂))
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    deriv (₂F₁ a b c) z =
      ∑' n : ℕ, ((n + 1 : 𝕂) * ordinaryHypergeometricCoefficient a b c (n + 1)) * z ^ n := by
  let A : ℕ → 𝕂 := ordinaryHypergeometricCoefficient a b c
  have hz' : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕂 A).radius := by
    simpa [A, ordinaryHypergeometricSeries, Metric.mem_eball, edist_zero_right] using hz
  have hderiv :
      HasDerivAt (ofScalarsSum A) (ofScalarsSum (fun n ↦ (n.succ : 𝕂) * A n.succ) z) z :=
    hasDerivAt_ofScalarsSum_of_mem_radius A hz'
  -- Rewrite the hypergeometric sum as the scalar `ofScalarsSum` and read off its derivative.
  calc
    deriv (₂F₁ a b c) z =
        ofScalarsSum (fun n ↦ (n.succ : 𝕂) * A n.succ) z := by
      simpa [A, ordinaryHypergeometric, ordinaryHypergeometricSeries] using hderiv.deriv
    _ = ∑' n : ℕ, ((n + 1 : 𝕂) * ordinaryHypergeometricCoefficient a b c (n + 1)) * z ^ n := by
      simpa [A, ofScalars_sum_eq, smul_eq_mul]

/-- Helper for Exercise 6: on the convergence disk, the second derivative of `₂F₁ a b c` is the
twice-termwise-derived scalar series. -/
theorem ordinary_hypergeometric_second_deriv_eq_tsum (a b c z : 𝕂)
    (hc : ∀ n : ℕ, c ≠ -(n : 𝕂))
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    iteratedDeriv 2 (₂F₁ a b c) z =
      ∑' n : ℕ,
        (((n + 1 : 𝕂) * (n + 2 : 𝕂)) * ordinaryHypergeometricCoefficient a b c (n + 2)) * z ^ n := by
  let A : ℕ → 𝕂 := ordinaryHypergeometricCoefficient a b c
  let A₁ : ℕ → 𝕂 := fun n ↦ (n.succ : 𝕂) * A n.succ
  let A₂ : ℕ → 𝕂 := fun n ↦ ((n.succ : 𝕂) * (n.succ.succ : 𝕂)) * A n.succ.succ
  have hz' : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕂 A).radius := by
    simpa [A, ordinaryHypergeometricSeries, Metric.mem_eball, edist_zero_right] using hz
  have hA₁radius :
      (ofScalars 𝕂 A).radius ≤ (ofScalars 𝕂 A₁).radius := by
    calc
      (ofScalars 𝕂 A).radius ≤ ((ofScalars 𝕂 A).derivSeries).radius :=
        (ofScalars 𝕂 A).radius_le_radius_derivSeries
      _ ≤
          ((ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries
            ((ofScalars 𝕂 A).derivSeries)).radius :=
        radius_le_radius_continuousLinearMap_comp _ _
      _ = (ofScalars 𝕂 A₁).radius := by
        simpa [A₁] using
          congrArg FormalMultilinearSeries.radius (apply_one_comp_derivSeries_ofScalars (𝕂 := 𝕂) A)
  have hz₁ : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕂 A₁).radius :=
    hz'.trans_le hA₁radius
  have hderiv₂ :
      HasDerivAt (ofScalarsSum A₁) (ofScalarsSum A₂ z) z :=
    by
      -- The second scalar derivative is the derivative of the already differentiated coefficient sequence.
      simpa [A₁, A₂, ofScalars_sum_eq, smul_eq_mul, mul_assoc, mul_comm] using
        (hasDerivAt_ofScalarsSum_of_mem_radius A₁ hz₁)
  have hderiv_eventually :
      (fun w ↦ deriv (₂F₁ a b c) w) =ᶠ[nhds z] fun w ↦ ofScalarsSum A₁ w := by
    filter_upwards [Metric.isOpen_eball.mem_nhds hz] with w hw
    simpa [A, A₁, ofScalars_sum_eq, smul_eq_mul] using
      ordinary_hypergeometric_deriv_eq_tsum a b c w hc hw
  have hsecond :
      HasDerivAt (fun w ↦ deriv (₂F₁ a b c) w) (ofScalarsSum A₂ z) z :=
    hderiv₂.congr_of_eventuallyEq hderiv_eventually
  -- Differentiate the first-derivative function on a neighborhood where it matches the derived scalar series.
  calc
    iteratedDeriv 2 (₂F₁ a b c) z = deriv (fun w ↦ deriv (₂F₁ a b c) w) z := by
      simp [iteratedDeriv_succ]
    _ = ofScalarsSum A₂ z := hsecond.deriv
    _ = ∑' n : ℕ,
          (((n + 1 : 𝕂) * (n + 2 : 𝕂)) * ordinaryHypergeometricCoefficient a b c (n + 2)) * z ^ n := by
      simpa [A, A₂, ofScalars_sum_eq, smul_eq_mul]

-- Proof sketch: if `a = -n` or `b = -n` for some `n`, then one numerator Pochhammer factor
-- vanishes from that point on, so the hypergeometric series is a polynomial and therefore has
-- infinite radius.
/-- Exercise 6 (1): the ordinary hypergeometric series has infinite radius when it terminates
because `a` or `b` is a nonpositive integer. -/
theorem ordinary_hypergeometric_radius_eq_top_of_terminating (a b c : 𝕂)
    (hab : ∃ n : ℕ, a = -(n : 𝕂) ∨ b = -(n : 𝕂)) :
    (ordinaryHypergeometricSeries 𝕂 a b c).radius = ⊤ := by
  obtain ⟨n, rfl | rfl⟩ := hab
  · simpa using
      (ordinaryHypergeometric_radius_top_of_neg_nat₁ 𝕂 b c :
        (ordinaryHypergeometricSeries 𝕂 (-(n : 𝕂)) b c).radius = ⊤)
  · simpa using
      (ordinaryHypergeometric_radius_top_of_neg_nat₂ 𝕂 a c :
        (ordinaryHypergeometricSeries 𝕂 a (-(n : 𝕂)) c).radius = ⊤)

/- Exercise 6 (2): this is exactly the canonical owner theorem
`ordinaryHypergeometricSeries_radius_eq_one`, specialized to the scalar target algebra. -/
recall ordinaryHypergeometricSeries_radius_eq_one

-- Proof sketch: work inside the open disk of convergence, differentiate the hypergeometric power
-- series termwise twice, and use the Pochhammer recursion on coefficients to identify the resulting
-- combination with the zero power series.
/-- Exercise 6 (3): for `c` not a nonpositive integer, the sum `₂F₁ a b c` of the hypergeometric
series satisfies Gauss's differential equation on its open disk of convergence. -/
theorem ordinary_hypergeometric_differential_equation (a b c z : 𝕂)
    (hc : ∀ n : ℕ, c ≠ -(n : 𝕂))
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z +
        (c - (a + b + 1) * z) * deriv (₂F₁ a b c) z -
        (a * b) * (₂F₁ a b c z) = 0 := by
  -- Route correction: the source-faithful route is coefficient comparison after two termwise
  -- differentiations, so the main theorem is reduced to the analytic bridge lemmas above.
  -- TODO: rewrite `z * S'` and `z * S''` by the standard nat-index shift identities for `tsum`,
  -- then collect the coefficient of `z^n` as
  -- `((n + 1 : 𝕂) * (c + n)) * A (n + 1) - (a + n) * (b + n) * A n`
  -- and finish by `ordinary_hypergeometric_coefficient_recurrence`.
  sorry
