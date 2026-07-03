import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_6_29 (from Items/Chap06) -/
open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Topology ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: for every `λ ≥ 0`, the integrand `ω ↦ exp (-(λ * X ω))` is bounded by `1` on the
-- almost-everywhere set where `0 ≤ X ω`, hence it is integrable on a probability space. This gives
-- `Ici 0 ⊆ integrableExpSet (-X) P`, so every `λ > 0` belongs to the interior.
/-- A nonnegative random variable has Laplace transform defined on the open right half-line. -/
theorem Ioi_subset_interior_integrableExpSet_neg_of_nonneg
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) :
    Ioi (0 : ℝ) ⊆ interior (integrableExpSet (-X) P) := by
  have h_nonneg_mem : Ici (0 : ℝ) ⊆ integrableExpSet (-X) P := by
    intro s hs
    refine Integrable.mono'
      (integrable_const (1 : ℝ))
      ((hX_meas.neg.const_mul s).exp.aestronglyMeasurable) ?_
    filter_upwards [hX_nonneg] with ω hω
    have hsX : 0 ≤ s * X ω := mul_nonneg hs hω
    have hle : Real.exp (-(s * X ω)) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr (by linarith : -(s * X ω) ≤ 0)
    simpa [Pi.neg_apply, neg_mul, mul_comm, mul_left_comm, mul_assoc,
      abs_of_nonneg (Real.exp_pos _).le] using hle
  intro t ht
  exact (interior_mono h_nonneg_mem) (by simpa [interior_Ici] using ht)

-- Proof sketch: rewrite the Laplace transform as the moment-generating function `mgf (-X) P`,
-- place `λ` in `interior (integrableExpSet (-X) P)` using the preceding lemma, and then apply the
-- canonical identity `ProbabilityTheory.iteratedDeriv_mgf`.
/-- Example 6.29: for a nonnegative random variable `X`, the Laplace transform
`λ ↦ P[fun ω ↦ exp (-(λ * X ω))] = mgf (-X) P λ` has `n`th derivative
`P[fun ω ↦ (-(X ω)) ^ n * exp (-(λ * X ω))]` for every `λ > 0`. -/
theorem iteratedDeriv_laplaceTransform_eq
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n (mgf (-X) P) t =
      P[fun ω ↦ (-(X ω)) ^ n * Real.exp (-(t * X ω))] := by
  have ht_mem : t ∈ interior (integrableExpSet (-X) P) :=
    Ioi_subset_interior_integrableExpSet_neg_of_nonneg hX_meas hX_nonneg ht
  simpa [Pi.neg_apply, neg_mul, mul_comm, mul_left_comm, mul_assoc] using
    iteratedDeriv_mgf ht_mem n

-- Proof sketch: once `λ > 0` is known to lie in the interior of `integrableExpSet (-X) P`, the
-- Laplace transform is analytic there by `ProbabilityTheory.analyticOn_mgf`; analyticity on an
-- open neighborhood implies `C^∞` regularity on `Set.Ioi 0`.
/-- The Laplace transform of a nonnegative random variable is infinitely differentiable on
`(0, ∞)`. -/
theorem laplaceTransform_contDiffOn
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) :
    ContDiffOn ℝ ⊤ (mgf (-X) P) (Ioi (0 : ℝ)) := by
  refine (analyticOn_mgf.mono ?_).contDiffOn_of_completeSpace
  exact Ioi_subset_interior_integrableExpSet_neg_of_nonneg hX_meas hX_nonneg

-- Proof sketch: specialize the preceding `n`th-derivative formula to `n = 1` and factor the minus
-- sign outside the expectation.
/-- The first derivative of the Laplace transform is `-P[X * exp (-λ X)]`. -/
theorem deriv_laplaceTransform_eq
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    deriv (mgf (-X) P) t =
      -(P[fun ω ↦ X ω * Real.exp (-(t * X ω))]) := by
  have ht_mem : t ∈ interior (integrableExpSet (-X) P) :=
    Ioi_subset_interior_integrableExpSet_neg_of_nonneg hX_meas hX_nonneg ht
  simpa [Pi.neg_apply, neg_mul, mul_comm, mul_left_comm, mul_assoc, integral_neg] using
    deriv_mgf ht_mem

-- Proof sketch: specialize the general `n`th-derivative formula to `n = 2` and use
-- `(-(X ω)) ^ 2 = (X ω) ^ 2`.
/-- The second derivative of the Laplace transform is `P[X^2 * exp (-λ X)]`. -/
theorem second_iteratedDeriv_laplaceTransform_eq
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (mgf (-X) P) t =
      P[fun ω ↦ (X ω) ^ 2 * Real.exp (-(t * X ω))] := by
  have ht_mem : t ∈ interior (integrableExpSet (-X) P) :=
    Ioi_subset_interior_integrableExpSet_neg_of_nonneg hX_meas hX_nonneg ht
  simpa [Pi.neg_apply, neg_mul, mul_comm, mul_left_comm, mul_assoc] using
    iteratedDeriv_mgf ht_mem 2

-- Proof sketch: rewrite `(-1)^n * F^(n)(λ)` using the derivative formula above as the truncated
-- moment `∫ X^n exp (-λX) dP`, then apply monotone convergence as `λ ↓ 0`.
/-- The right limit of the signed `n`th derivative of the Laplace transform recovers the `n`th
nonnegative moment in `ENNReal`. -/
theorem tendsto_ofReal_signed_iteratedDeriv_laplaceTransform_right_zero
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_meas : Measurable X) (hX_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω) (n : ℕ) :
    Tendsto
      (fun t : ℝ ↦ ENNReal.ofReal (((-1 : ℝ) ^ n) * iteratedDeriv n (mgf (-X) P) t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫⁻ ω, ENNReal.ofReal ((X ω) ^ n) ∂P)) := sorry
