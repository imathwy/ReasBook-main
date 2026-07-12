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
    (_hc : ∀ n : ℕ, c ≠ -(n : 𝕂))
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
      simp [A, ofScalars_sum_eq, smul_eq_mul]

/-- Helper for Exercise 6: on the convergence disk, the second derivative of `₂F₁ a b c` is the
twice-termwise-derived scalar series. -/
theorem ordinary_hypergeometric_second_deriv_eq_tsum (a b c z : 𝕂)
    (hc : ∀ n : ℕ, c ≠ -(n : 𝕂))
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    iteratedDeriv 2 (₂F₁ a b c) z =
      ∑' n : ℕ,
        (((n + 1 : 𝕂) * (n + 2 : 𝕂)) *
            ordinaryHypergeometricCoefficient a b c (n + 2)) *
          z ^ n := by
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
      -- The second scalar derivative is the derivative of the already differentiated
      -- coefficient sequence.
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
  -- Differentiate the first-derivative function on a neighborhood where it matches
  -- the derived scalar series.
  calc
    iteratedDeriv 2 (₂F₁ a b c) z = deriv (fun w ↦ deriv (₂F₁ a b c) w) z := by
      simp [iteratedDeriv_succ]
    _ = ofScalarsSum A₂ z := hsecond.deriv
    _ = ∑' n : ℕ,
          (((n + 1 : 𝕂) * (n + 2 : 𝕂)) *
              ordinaryHypergeometricCoefficient a b c (n + 2)) *
            z ^ n := by
      -- Rewrite the scalar series termwise to normalize `n.succ.succ` as `n + 2`.
      rw [ofScalars_sum_eq]
      refine tsum_congr fun n ↦ ?_
      dsimp [A₂, A]
      rw [show n + 1 + 1 = n + 2 by omega]
      simp

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

/-- Helper for Cartan section04 frozen_0021_Exercise_6: if a scalar series has vanishing initial
term, shifting by one preserves its sum. -/
theorem hasSum_nat_add_one_of_zero
    {f : ℕ → 𝕂} {s : 𝕂}
    (hshift : HasSum (fun n : ℕ ↦ f (n + 1)) s)
    (h0 : f 0 = 0) :
    HasSum f s := by
  -- Recover the unshifted series by adding back the vanishing initial coefficient.
  have hf : Summable f := (summable_nat_add_iff 1).1 hshift.summable
  have htsum : ∑' n : ℕ, f n = s := by
    calc
      ∑' n : ℕ, f n = f 0 + ∑' n : ℕ, f (n + 1) := hf.tsum_eq_zero_add
      _ = s := by simp [h0, hshift.tsum_eq]
  rw [← htsum]
  exact hf.hasSum

/-- Helper for Cartan section04 frozen_0021_Exercise_6: if the first two coefficients vanish,
shifting by two preserves the sum. -/
theorem hasSum_nat_add_two_of_zero
    {f : ℕ → 𝕂} {s : 𝕂}
    (hshift : HasSum (fun n : ℕ ↦ f (n + 2)) s)
    (h0 : f 0 = 0)
    (h1 : f 1 = 0) :
    HasSum f s := by
  -- Recover the full series from the tail by adding back the two vanishing coefficients.
  have hf : Summable f := (summable_nat_add_iff 2).1 hshift.summable
  have hsum0 : ∑ i ∈ Finset.range 2, f i = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [h0, h1]
  have htsum : ∑' n : ℕ, f n = s := by
    calc
      ∑' n : ℕ, f n = (∑ i ∈ Finset.range 2, f i) + ∑' n : ℕ, f (n + 2) := by
        symm
        exact hf.sum_add_tsum_nat_add 2
      _ = s := by simp [hsum0, hshift.tsum_eq]
  rw [← htsum]
  exact hf.hasSum

/-- Helper for Cartan section04 frozen_0021_Exercise_6: composing the Fréchet derivative power
series with evaluation at `1` returns the scalar derivative power series. -/
theorem scalar_deriv_hasFPowerSeriesOnBall_apply_one
    {f : 𝕂 → 𝕂} {p : FormalMultilinearSeries 𝕂 𝕂 𝕂} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f p 0 r) :
    HasFPowerSeriesOnBall (deriv f)
      ((ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries p.derivSeries) 0 r := by
  -- Evaluate the Fréchet derivative at `1` to move back to scalar derivatives.
  simpa only [Function.comp_apply, fderiv_apply_one_eq_deriv] using
    (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).comp_hasFPowerSeriesOnBall h.fderiv

/-- Helper for Cartan section04 frozen_0021_Exercise_6: the coefficients of the scalarized
derivative power series are the usual scalar derivative coefficients. -/
theorem scalar_apply_one_derivSeries_coeff
    (p : FormalMultilinearSeries 𝕂 𝕂 𝕂) (n : ℕ) :
    ((ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries p.derivSeries).coeff n =
      ((n + 1 : 𝕂) * p.coeff (n + 1)) := by
  -- Unfold the coefficient and evaluate the derivative multilinear map on the diagonal vector `1`.
  rw [FormalMultilinearSeries.coeff,
    ContinuousLinearMap.compFormalMultilinearSeries_apply']
  simp [FormalMultilinearSeries.derivSeries_coeff_one]

/-- Helper for Cartan section04 frozen_0021_Exercise_6: inside the convergence disk, the
hypergeometric series has the expected scalar `HasSum` expansion. -/
theorem ordinary_hypergeometric_hasSum
    (a b c : 𝕂) {z : 𝕂}
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    HasSum (fun n : ℕ ↦ ordinaryHypergeometricCoefficient a b c n * z ^ n) (₂F₁ a b c z) := by
  let p : FormalMultilinearSeries 𝕂 𝕂 𝕂 := ordinaryHypergeometricSeries 𝕂 a b c
  have hz' : (‖z‖₊ : ℝ≥0∞) < p.radius := by
    simpa [p, ordinaryHypergeometricSeries, Metric.mem_eball, edist_zero_right] using hz
  have hp0 : 0 < p.radius := lt_of_le_of_lt (by simp) hz'
  have hp : HasFPowerSeriesOnBall (₂F₁ a b c) p 0 p.radius := p.hasFPowerSeriesOnBall hp0
  have hsum : HasSum (fun n : ℕ ↦ z ^ n • p.coeff n) (₂F₁ a b c z) := by
    -- Read the scalar series via diagonal evaluation of the formal power series.
    simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff] using hp.hasSum hz
  simpa [p, ordinaryHypergeometricSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Helper for Cartan section04 frozen_0021_Exercise_6: inside the convergence disk, the first
derivative has the expected scalar `HasSum` expansion. -/
theorem ordinary_hypergeometric_deriv_hasSum
    (a b c : 𝕂) {z : 𝕂}
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    HasSum
      (fun n : ℕ ↦ ((n + 1 : 𝕂) * ordinaryHypergeometricCoefficient a b c (n + 1)) * z ^ n)
      (deriv (₂F₁ a b c) z) := by
  let p : FormalMultilinearSeries 𝕂 𝕂 𝕂 := ordinaryHypergeometricSeries 𝕂 a b c
  have hz' : (‖z‖₊ : ℝ≥0∞) < p.radius := by
    simpa [p, ordinaryHypergeometricSeries, Metric.mem_eball, edist_zero_right] using hz
  have hp0 : 0 < p.radius := lt_of_le_of_lt (by simp) hz'
  have hp : HasFPowerSeriesOnBall (₂F₁ a b c) p 0 p.radius := p.hasFPowerSeriesOnBall hp0
  have hpow :
      HasFPowerSeriesOnBall (deriv (₂F₁ a b c))
        ((ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries p.derivSeries)
        0 p.radius :=
    scalar_deriv_hasFPowerSeriesOnBall_apply_one hp
  -- Rewrite the scalarized derivative series coefficientwise.
  convert hpow.hasSum hz using 1
  · funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, scalar_apply_one_derivSeries_coeff]
    simp [p, ordinaryHypergeometricSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      mul_comm, mul_assoc]
  · simp

/-- Helper for Cartan section04 frozen_0021_Exercise_6: inside the convergence disk, the second
derivative has the expected scalar `HasSum` expansion. -/
theorem ordinary_hypergeometric_second_deriv_hasSum
    (a b c : 𝕂) {z : 𝕂}
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    HasSum
      (fun n : ℕ ↦
        (((n + 1 : 𝕂) * (n + 2 : 𝕂)) * ordinaryHypergeometricCoefficient a b c (n + 2)) *
          z ^ n)
      (iteratedDeriv 2 (₂F₁ a b c) z) := by
  let p : FormalMultilinearSeries 𝕂 𝕂 𝕂 := ordinaryHypergeometricSeries 𝕂 a b c
  let p₁ : FormalMultilinearSeries 𝕂 𝕂 𝕂 :=
    (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries p.derivSeries
  have hz' : (‖z‖₊ : ℝ≥0∞) < p.radius := by
    simpa [p, ordinaryHypergeometricSeries, Metric.mem_eball, edist_zero_right] using hz
  have hp0 : 0 < p.radius := lt_of_le_of_lt (by simp) hz'
  have hp : HasFPowerSeriesOnBall (₂F₁ a b c) p 0 p.radius := p.hasFPowerSeriesOnBall hp0
  have hpow₁ : HasFPowerSeriesOnBall (deriv (₂F₁ a b c)) p₁ 0 p.radius :=
    scalar_deriv_hasFPowerSeriesOnBall_apply_one hp
  have hpow₂ :
      HasFPowerSeriesOnBall (deriv (deriv (₂F₁ a b c)))
        ((ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries p₁.derivSeries)
        0 p.radius :=
    scalar_deriv_hasFPowerSeriesOnBall_apply_one hpow₁
  -- Route correction: rewrite the twice-scalarized derivative series coefficientwise.
  convert hpow₂.hasSum hz using 1
  · funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, scalar_apply_one_derivSeries_coeff,
      scalar_apply_one_derivSeries_coeff]
    rw [show n + (1 + 1) = n + 2 by omega, show n + 1 + 1 = n + 2 by omega]
    simp only [p, ordinaryHypergeometricSeries, FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, mul_comm, mul_assoc]
    have hcast : ((n + 1 : 𝕂) + 1) = (n + 2 : 𝕂) := by ring
    simp [hcast]
  · simp [iteratedDeriv_succ]

-- Proof sketch: work inside the open disk of convergence, differentiate the hypergeometric power
-- series termwise twice, and use the Pochhammer recursion on coefficients to identify the resulting
-- combination with the zero power series.
/-- Cartan section04 frozen_0021_Exercise_6: for `c` not a nonpositive integer, the sum
`₂F₁ a b c` of the hypergeometric series satisfies Gauss's differential equation on its open
disk of convergence. -/
theorem ordinary_hypergeometric_differential_equation (a b c z : 𝕂)
    (hc : ∀ n : ℕ, c ≠ -(n : 𝕂))
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z +
        (c - (a + b + 1) * z) * deriv (₂F₁ a b c) z -
        (a * b) * (₂F₁ a b c z) = 0 := by
  -- Route correction: the source-faithful route is coefficient comparison after two termwise
  -- differentiations, so the main theorem is reduced to coefficientwise vanishing.
  let u : ℕ → 𝕂 := ordinaryHypergeometricCoefficient a b c
  let f : ℕ → 𝕂 := fun n ↦ u n * z ^ n
  let f' : ℕ → 𝕂 := fun n ↦ ((n + 1 : 𝕂) * u (n + 1)) * z ^ n
  let f'' : ℕ → 𝕂 := fun n ↦ (((n + 1 : 𝕂) * (n + 2 : 𝕂)) * u (n + 2)) * z ^ n
  let z_f' : ℕ → 𝕂 := fun n ↦ ((n : 𝕂) * u n) * z ^ n
  let z_f'' : ℕ → 𝕂 := fun n ↦ ((n : 𝕂) * (n + 1 : 𝕂) * u (n + 1)) * z ^ n
  let z2_f'' : ℕ → 𝕂 := fun n ↦ ((n : 𝕂) * ((n : 𝕂) - 1) * u n) * z ^ n
  let odeCoeff : ℕ → 𝕂 := fun n ↦
    z_f'' n - z2_f'' n + c * f' n - (a + b + 1) * z_f' n - a * b * f n
  have hS : HasSum f (₂F₁ a b c z) := ordinary_hypergeometric_hasSum a b c hz
  have hS' : HasSum f' (deriv (₂F₁ a b c) z) :=
    ordinary_hypergeometric_deriv_hasSum a b c hz
  have hS'' : HasSum f'' (iteratedDeriv 2 (₂F₁ a b c) z) :=
    ordinary_hypergeometric_second_deriv_hasSum a b c hz
  have hzS' : HasSum z_f' (z * deriv (₂F₁ a b c) z) := by
    have hshift : HasSum (fun n : ℕ ↦ z_f' (n + 1)) (z * deriv (₂F₁ a b c) z) := by
      -- Multiplying the first-derivative series by `z` shifts the coefficients by one.
      simpa [z_f', f', pow_succ', mul_assoc, mul_comm] using HasSum.mul_left z hS'
    have h0 : z_f' 0 = 0 := by
      simp [z_f']
    exact hasSum_nat_add_one_of_zero hshift h0
  have hzS'' : HasSum z_f'' (z * iteratedDeriv 2 (₂F₁ a b c) z) := by
    have hshift : HasSum (fun n : ℕ ↦ z_f'' (n + 1)) (z * iteratedDeriv 2 (₂F₁ a b c) z) := by
      -- Multiplying the second-derivative series by `z` shifts the coefficients by one.
      convert HasSum.mul_left z hS'' using 1
      · funext n
        dsimp [z_f'', f'']
        rw [pow_succ']
        rw [show n + 1 + 1 = n + 2 by omega]
        have hpoly :
            ((n + 1 : 𝕂) + (n + 1 : 𝕂) ^ 2) =
              (2 : 𝕂) + (n : 𝕂) * 3 + (n : 𝕂) ^ 2 := by
          ring
        calc
          ↑(n + 1) * (↑(n + 1) + 1) * u (n + 2) * (z * z ^ n) =
              (↑(n + 1) * u (n + 2) * (z * z ^ n)) +
                (↑(n + 1) ^ 2 * u (n + 2) * (z * z ^ n)) := by
                  ring
          _ =
              (((n + 1 : 𝕂) + (n + 1 : 𝕂) ^ 2) * (u (n + 2) * (z * z ^ n))) := by
                simpa [mul_assoc] using
                  (add_mul (n + 1 : 𝕂) ((n + 1 : 𝕂) ^ 2) (u (n + 2) * (z * z ^ n))).symm
          _ = (((2 : 𝕂) + (n : 𝕂) * 3 + (n : 𝕂) ^ 2) * (u (n + 2) * (z * z ^ n))) := by
                rw [hpoly]
          _ = z * ((↑n + 1) * (↑n + 2) * u (n + 2) * z ^ n) := by
                ring
    have h0 : z_f'' 0 = 0 := by
      simp [z_f'']
    exact hasSum_nat_add_one_of_zero hshift h0
  have hz2S'' : HasSum z2_f'' (z ^ 2 * iteratedDeriv 2 (₂F₁ a b c) z) := by
    have hshift :
        HasSum (fun n : ℕ ↦ z2_f'' (n + 2)) (z ^ 2 * iteratedDeriv 2 (₂F₁ a b c) z) := by
      -- Multiplying the second-derivative series by `z^2` shifts the coefficients by two.
      convert HasSum.mul_left (z ^ 2) hS'' using 1
      · funext n
        dsimp [z2_f'', f'']
        rw [pow_add, pow_two]
        have hcast : ((n + 2 : 𝕂) - 1) = (n + 1 : 𝕂) := by ring
        simp [hcast, mul_assoc, mul_comm]
    have h0 : z2_f'' 0 = 0 := by
      simp [z2_f'']
    have h1 : z2_f'' 1 = 0 := by
      simp [z2_f'']
    exact hasSum_nat_add_two_of_zero hshift h0 h1
  have h_ode_series :
      HasSum odeCoeff
        (z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z +
          (c - (a + b + 1) * z) * deriv (₂F₁ a b c) z -
          a * b * (₂F₁ a b c z)) := by
    have hterm₁ :
        HasSum (fun n : ℕ ↦ z_f'' n - z2_f'' n) (z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z) := by
      -- The `z (1 - z) S''` term is the difference of the once-shifted and twice-shifted series.
      convert hzS''.sub hz2S'' using 1
      ring
    have hterm₂ :
        HasSum (fun n : ℕ ↦ c * f' n - (a + b + 1) * z_f' n)
          ((c - (a + b + 1) * z) * deriv (₂F₁ a b c) z) := by
      -- The `S'` term splits into the unshifted and shifted derivative series.
      convert (HasSum.mul_left c hS').sub (HasSum.mul_left (a + b + 1) hzS') using 1
      ring
    have hterm₃ : HasSum (fun n : ℕ ↦ a * b * f n) (a * b * (₂F₁ a b c z)) := by
      -- The original series contributes with the scalar factor `ab`.
      exact HasSum.mul_left (a * b) hS
    convert hterm₁.add hterm₂ |>.sub hterm₃ using 1
    · ext n
      simp [odeCoeff]
      ring
  have hcoeff_zero : ∀ n : ℕ, odeCoeff n = 0 := by
    intro n
    -- The coefficient vanishes by the standard hypergeometric recurrence.
    calc
      odeCoeff n =
          ((((n + 1 : 𝕂) * (c + n)) * u (n + 1) - ((a + n) * (b + n)) * u n) * z ^ n) := by
            simp [odeCoeff, u, f, f', z_f', z_f'', z2_f'']
            ring
      _ = 0 := by
        rw [ordinary_hypergeometric_coefficient_recurrence a b c hc n]
        ring
  calc
    z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z +
        (c - (a + b + 1) * z) * deriv (₂F₁ a b c) z -
        (a * b) * (₂F₁ a b c z) =
      ∑' n : ℕ, odeCoeff n := h_ode_series.tsum_eq.symm
    _ = 0 := by
      simp [hcoeff_zero]
