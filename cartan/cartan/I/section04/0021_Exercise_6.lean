import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the canonical
-- owner/API choice was checked against Mathlib's
-- `Analysis.SpecialFunctions.OrdinaryHypergeometric` interface.

open scoped Topology ENNReal NNReal

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Exercise 6 (1): if one of the upper parameters is a nonpositive integer, then the Gaussian
hypergeometric series terminates and its radius of convergence is `⊤`. -/
theorem ordinaryHypergeometricSeries_radius_eq_top_of_neg_nat
    (a b c : 𝕂)
    (hab : ∃ k : ℕ, a = -(k : 𝕂) ∨ b = -(k : 𝕂)) :
    (ordinaryHypergeometricSeries 𝕂 a b c).radius = ⊤ := by
  obtain ⟨k, rfl | rfl⟩ := hab
  · simpa using
      (ordinaryHypergeometric_radius_top_of_neg_nat₁ 𝕂 b c :
        (ordinaryHypergeometricSeries 𝕂 (-(k : 𝕂)) b c).radius = ⊤)
  · simpa using
      (ordinaryHypergeometric_radius_top_of_neg_nat₂ 𝕂 a c :
        (ordinaryHypergeometricSeries 𝕂 a (-(k : 𝕂)) c).radius = ⊤)

/- Exercise 6 (2): this is exactly the canonical owner theorem
`ordinaryHypergeometricSeries_radius_eq_one`. -/
recall ordinaryHypergeometricSeries_radius_eq_one

/-- Helper for Exercise 6: the ordinary hypergeometric coefficients satisfy the standard
first-order recurrence. -/
lemma ordinaryHypergeometricCoefficient_succ_relation
    (a b c : 𝕂)
    (hc : ∀ k : ℕ, c ≠ -(k : 𝕂))
    (n : ℕ) :
    ((n + 1 : 𝕂) * (c + n)) * ordinaryHypergeometricCoefficient a b c (n + 1) =
      ((a + n) * (b + n)) * ordinaryHypergeometricCoefficient a b c n := by
  -- Cancel the successor step in the factorial and ascending Pochhammer factors.
  have hc_ne : c + n ≠ 0 := by
    intro h
    exact hc n (eq_neg_of_add_eq_zero_left h)
  have hpoch_c_ne : (ascPochhammer 𝕂 n).eval c ≠ 0 := by
    intro h
    obtain ⟨k, hk, hk_eq⟩ := (ascPochhammer_eval_eq_zero_iff n c).1 h
    have : c = -(k : 𝕂) := by
      simpa [hk_eq] using (neg_neg c).symm
    exact hc k this
  simp only [ordinaryHypergeometricCoefficient, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, ascPochhammer_succ_eval]
  field_simp [hc_ne, hpoch_c_ne]

/-- Helper for Exercise 6: if a summable scalar series has vanishing initial term, shifting by one
does not change its sum. -/
lemma hasSum_nat_add_one_of_zero
    {f : ℕ → 𝕂}
    {s : 𝕂}
    (hshift : HasSum (fun n : ℕ ↦ f (n + 1)) s)
    (h0 : f 0 = 0) :
    HasSum f s := by
  -- Recover the unshifted series by adding back the vanishing initial term.
  have hf : Summable f := (summable_nat_add_iff 1).1 hshift.summable
  have htsum : ∑' n : ℕ, f n = s := by
    calc
      ∑' n : ℕ, f n = f 0 + ∑' n : ℕ, f (n + 1) := hf.tsum_eq_zero_add
      _ = s := by simp [h0, hshift.tsum_eq]
  rw [← htsum]
  exact hf.hasSum

/-- Helper for Exercise 6: if the first two terms vanish, shifting by two does not change the sum. -/
lemma hasSum_nat_add_two_of_zero
    {f : ℕ → 𝕂}
    {s : 𝕂}
    (hshift : HasSum (fun n : ℕ ↦ f (n + 2)) s)
    (h0 : f 0 = 0)
    (h1 : f 1 = 0) :
    HasSum f s := by
  -- Recover the full series from the tail by adding back the two vanishing terms.
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

/-- Helper for Exercise 6: composing the Fréchet derivative power series with evaluation at `1`
returns a scalar power series for the usual derivative. -/
lemma scalar_deriv_hasFPowerSeriesOnBall_apply_one
    {f : 𝕂 → 𝕂}
    {p : FormalMultilinearSeries 𝕂 𝕂 𝕂}
    {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f p 0 r) :
    HasFPowerSeriesOnBall (deriv f)
      ((ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries p.derivSeries) 0 r := by
  -- Compose the derivative series with evaluation at `1` to move back to scalar derivatives.
  simpa only [Function.comp_apply, fderiv_apply_one_eq_deriv] using
    (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).comp_hasFPowerSeriesOnBall h.fderiv

/-- Helper for Exercise 6: the coefficients of the evaluated derivative series are the usual
scalar derivative coefficients. -/
lemma scalar_apply_one_derivSeries_coeff
    (p : FormalMultilinearSeries 𝕂 𝕂 𝕂)
    (n : ℕ) :
    ((ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).compFormalMultilinearSeries p.derivSeries).coeff n =
      ((n + 1 : 𝕂) * p.coeff (n + 1)) := by
  -- Unfold the coefficient and evaluate the derivative multilinear map on the diagonal vector `1`.
  rw [FormalMultilinearSeries.coeff, ContinuousLinearMap.compFormalMultilinearSeries_apply']
  simpa [FormalMultilinearSeries.derivSeries_coeff_one, smul_eq_mul]

/-- Helper for Exercise 6: inside the disk of convergence, the defining hypergeometric power series
has the expected scalar `HasSum` expansion. -/
lemma ordinaryHypergeometric_hasSum
    (a b c : 𝕂)
    {z : 𝕂}
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    HasSum
      (fun n : ℕ ↦ ordinaryHypergeometricCoefficient a b c n * z ^ n)
      (₂F₁ a b c z) := by
  let p : FormalMultilinearSeries 𝕂 𝕂 𝕂 := ordinaryHypergeometricSeries 𝕂 a b c
  have hz' : (‖z‖₊ : ℝ≥0∞) < p.radius := by
    simpa [p, ordinaryHypergeometricSeries, Metric.mem_eball, edist_zero_right] using hz
  have hp0 : 0 < p.radius := lt_of_le_of_lt (by simp) hz'
  have hp : HasFPowerSeriesOnBall (₂F₁ a b c) p 0 p.radius := p.hasFPowerSeriesOnBall hp0
  have hsum : HasSum (fun n : ℕ ↦ z ^ n • p.coeff n) (₂F₁ a b c z) := by
    -- Read the scalar series through the diagonal evaluation formula for formal power series.
    simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff] using hp.hasSum hz
  simpa [p, ordinaryHypergeometricSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Helper for Exercise 6: inside the disk of convergence, the first derivative has the expected
scalar `HasSum` expansion. -/
lemma ordinaryHypergeometric_deriv_hasSum
    (a b c : 𝕂)
    {z : 𝕂}
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
  -- Rewrite the scalarized derivative series coefficientwise instead of unfolding the whole `HasSum`.
  convert hpow.hasSum hz using 1
  · funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, scalar_apply_one_derivSeries_coeff]
    simp [p, ordinaryHypergeometricSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc]
  · simp

/-- Helper for Exercise 6: inside the disk of convergence, the second derivative has the expected
scalar `HasSum` expansion. -/
lemma ordinaryHypergeometric_iteratedDeriv_two_hasSum
    (a b c : 𝕂)
    {z : 𝕂}
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
  -- Route correction: rewrite the twice-scalarized derivative series term by term.
  convert hpow₂.hasSum hz using 1
  · funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, scalar_apply_one_derivSeries_coeff,
      scalar_apply_one_derivSeries_coeff]
    rw [show n + (1 + 1) = n + 2 by omega, show n + 1 + 1 = n + 2 by omega]
    simp only [p, p₁, ordinaryHypergeometricSeries, FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    have hcast : ((n + 1 : 𝕂) + 1) = (n + 2 : 𝕂) := by ring
    simpa [hcast]
  · simp [iteratedDeriv_succ]

/-- Helper for Exercise 6: inside the disk of convergence, the first derivative is obtained by
termwise differentiation of the hypergeometric power series. -/
lemma ordinaryHypergeometric_deriv_eq_tsum
    (a b c : 𝕂)
    {z : 𝕂}
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    deriv (₂F₁ a b c) z =
      ∑' n : ℕ, ((n + 1 : 𝕂) * ordinaryHypergeometricCoefficient a b c (n + 1)) * z ^ n := by
  -- Read the scalar derivative expansion from the corresponding `HasSum` statement.
  exact (ordinaryHypergeometric_deriv_hasSum a b c hz).tsum_eq.symm

/-- Helper for Exercise 6: inside the disk of convergence, the second derivative is obtained by
termwise differentiation twice. -/
lemma ordinaryHypergeometric_iteratedDeriv_two_eq_tsum
    (a b c : 𝕂)
    {z : 𝕂}
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    iteratedDeriv 2 (₂F₁ a b c) z =
      ∑' n : ℕ,
        (((n + 1 : 𝕂) * (n + 2 : 𝕂)) * ordinaryHypergeometricCoefficient a b c (n + 2)) *
          z ^ n := by
  -- Read the twice-differentiated scalar expansion from the corresponding `HasSum` statement.
  exact (ordinaryHypergeometric_iteratedDeriv_two_hasSum a b c hz).tsum_eq.symm

/-- Exercise 6 (3): on the open disk of convergence, the sum of the Gaussian hypergeometric series
with parameters `a`, `b`, `c : 𝕂` satisfies the differential equation
`z (1 - z) S''(z) + (c - (a + b + 1) z) S'(z) - ab S(z) = 0`. -/
theorem ordinaryHypergeometric_differential_equation
    (a b c : 𝕂)
    (hc : ∀ k : ℕ, c ≠ -(k : 𝕂))
    (z : 𝕂)
    (hz : z ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z +
        (c - (a + b + 1) * z) * deriv (₂F₁ a b c) z -
        a * b * (₂F₁ a b c z) =
      0 := by
  let u : ℕ → 𝕂 := ordinaryHypergeometricCoefficient a b c
  let f : ℕ → 𝕂 := fun n ↦ u n * z ^ n
  let f' : ℕ → 𝕂 := fun n ↦ ((n + 1 : 𝕂) * u (n + 1)) * z ^ n
  let f'' : ℕ → 𝕂 := fun n ↦ (((n + 1 : 𝕂) * (n + 2 : 𝕂)) * u (n + 2)) * z ^ n
  let z_f' : ℕ → 𝕂 := fun n ↦ ((n : 𝕂) * u n) * z ^ n
  let z_f'' : ℕ → 𝕂 := fun n ↦ ((n : 𝕂) * (n + 1 : 𝕂) * u (n + 1)) * z ^ n
  let z2_f'' : ℕ → 𝕂 := fun n ↦ ((n : 𝕂) * ((n : 𝕂) - 1) * u n) * z ^ n
  let odeCoeff : ℕ → 𝕂 := fun n ↦
    z_f'' n - z2_f'' n + c * f' n - (a + b + 1) * z_f' n - a * b * f n
  have hS : HasSum f (₂F₁ a b c z) := ordinaryHypergeometric_hasSum a b c hz
  have hS' : HasSum f' (deriv (₂F₁ a b c) z) := ordinaryHypergeometric_deriv_hasSum a b c hz
  have hS'' : HasSum f'' (iteratedDeriv 2 (₂F₁ a b c) z) :=
    ordinaryHypergeometric_iteratedDeriv_two_hasSum a b c hz
  have hzS' : HasSum z_f' (z * deriv (₂F₁ a b c) z) := by
    have hshift : HasSum (fun n : ℕ ↦ z_f' (n + 1)) (z * deriv (₂F₁ a b c) z) := by
      -- Multiplying the derivative series by `z` shifts the coefficient index by one.
      simpa [z_f', f', pow_succ', mul_assoc, mul_comm] using HasSum.mul_left z hS'
    have h0 : z_f' 0 = 0 := by
      simp [z_f']
    exact hasSum_nat_add_one_of_zero hshift h0
  have hzS'' : HasSum z_f'' (z * iteratedDeriv 2 (₂F₁ a b c) z) := by
    have hshift : HasSum (fun n : ℕ ↦ z_f'' (n + 1)) (z * iteratedDeriv 2 (₂F₁ a b c) z) := by
      -- Multiplying the second-derivative series by `z` shifts the coefficient index by one.
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
    have hshift : HasSum (fun n : ℕ ↦ z2_f'' (n + 2)) (z ^ 2 * iteratedDeriv 2 (₂F₁ a b c) z) := by
      -- Multiplying the second-derivative series by `z^2` shifts the coefficient index by two.
      convert HasSum.mul_left (z ^ 2) hS'' using 1
      · funext n
        dsimp [z2_f'', f'']
        rw [pow_add, pow_two]
        have hcast : ((n + 2 : 𝕂) - 1) = (n + 1 : 𝕂) := by ring
        simpa [hcast, mul_assoc, mul_left_comm, mul_comm]
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
    have hterm₁ : HasSum (fun n : ℕ ↦ z_f'' n - z2_f'' n)
        (z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z) := by
      -- The `z (1 - z) S''` term is the difference of the once-shifted and twice-shifted series.
      convert hzS''.sub hz2S'' using 1
      ring
    have hterm₂ : HasSum (fun n : ℕ ↦ c * f' n - (a + b + 1) * z_f' n)
        ((c - (a + b + 1) * z) * deriv (₂F₁ a b c) z) := by
      -- The `S'` contribution splits into the unshifted and shifted first-derivative series.
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
    -- The recurrence for the hypergeometric coefficients cancels the coefficient of each `z^n`.
    calc
      odeCoeff n =
          ((((n + 1 : 𝕂) * (c + n)) * u (n + 1) - ((a + n) * (b + n)) * u n) * z ^ n) := by
            simp [odeCoeff, u, f, f', f'', z_f', z_f'', z2_f'']
            ring
      _ = 0 := by
        rw [ordinaryHypergeometricCoefficient_succ_relation a b c hc n]
        ring
  calc
    z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z +
        (c - (a + b + 1) * z) * deriv (₂F₁ a b c) z -
        a * b * (₂F₁ a b c z) =
      ∑' n : ℕ, odeCoeff n := h_ode_series.tsum_eq.symm
    _ = 0 := by
      simp [hcoeff_zero]
