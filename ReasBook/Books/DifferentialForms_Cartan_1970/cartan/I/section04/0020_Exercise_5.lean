import DifferentialForms_Cartan_1970.cartan.I.section02.«0006_Proposition_I_2_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open Filter
open scoped NNReal ENNReal

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- Helper for Exercise 5: the root-growth term of the coefficientwise power series is the
corresponding natural power of the original root-growth term. -/
lemma coeffwise_pow_root_term (a : ℕ → 𝕜) (p n : ℕ) :
    ((‖(a ^ p) n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞) =
      (((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞) ^ p) := by
  have hn : 0 ≤ (1 / (n : ℝ)) := by positivity
  -- Rewrite the `n`th powered coefficient to the scalar identity `‖a n ^ p‖ = ‖a n‖ ^ p`.
  calc
    ((‖(a ^ p) n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)
        = (((‖a n‖₊ ^ p : ℝ≥0) ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞) := by
            simp [Pi.pow_apply, nnnorm_pow]
    _ = ((((‖a n‖₊ ^ p : ℝ≥0) : ℝ≥0∞) ^ (1 / (n : ℝ)))) := by
          rw [ENNReal.coe_rpow_of_nonneg _ hn]
    _ = ((((‖a n‖₊ : ℝ≥0∞) ^ p) ^ (1 / (n : ℝ)))) := by
          rw [ENNReal.coe_pow]
    _ = ((‖a n‖₊ : ℝ≥0∞) ^ ((p : ℝ) * (1 / (n : ℝ)))) := by
          rw [← ENNReal.rpow_natCast_mul]
    _ = ((‖a n‖₊ : ℝ≥0∞) ^ ((1 / (n : ℝ)) * p)) := by
          rw [mul_comm]
    _ = (((‖a n‖₊ : ℝ≥0∞) ^ (1 / (n : ℝ))) ^ p) := by
          rw [ENNReal.rpow_mul_natCast]
    _ = ((((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞) ^ p)) := by
          rw [← ENNReal.coe_rpow_of_nonneg _ hn]

/-- Helper for Exercise 5: taking a natural power commutes with `limsup` for sequences in
`ℝ≥0∞` along `atTop`. -/
lemma limsup_pow_atTop (u : ℕ → ℝ≥0∞) (p : ℕ) :
    limsup (fun n ↦ u n ^ p) (atTop : Filter ℕ) = (limsup u (atTop : Filter ℕ)) ^ p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · apply le_antisymm
    · -- Push the strict upper bound through a `p`-th root, then bound the sequence eventually.
      rw [Filter.limsup_le_iff']
      intro y hy
      have hy_root : limsup u (atTop : Filter ℕ) < y ^ ((p : ℝ)⁻¹) := by
        apply (ENNReal.pow_lt_pow_left_iff hp).mp
        calc
          (limsup u (atTop : Filter ℕ)) ^ p < y := hy
          _ = (y ^ ((p : ℝ)⁻¹)) ^ p := (ENNReal.rpow_inv_natCast_pow hp y).symm
      obtain ⟨z, hz_left, hz_right⟩ := exists_between hy_root
      have hu : ∀ᶠ n in (atTop : Filter ℕ), u n ≤ z :=
        (Filter.limsup_le_iff').mp le_rfl z hz_left
      have hzpow : z ^ p < y := by
        calc
          z ^ p < (y ^ ((p : ℝ)⁻¹)) ^ p := (ENNReal.pow_lt_pow_left_iff hp).2 hz_right
          _ = y := ENNReal.rpow_inv_natCast_pow hp y
      filter_upwards [hu] with n hn
      exact (ENNReal.pow_le_pow_left hn).trans (le_of_lt hzpow)
    · -- Likewise, pull a strict lower bound back through a `p`-th root and use frequent values.
      rw [Filter.le_limsup_iff']
      intro y hy
      have hy_root : y ^ ((p : ℝ)⁻¹) < limsup u (atTop : Filter ℕ) := by
        apply (ENNReal.pow_lt_pow_left_iff hp).mp
        calc
          (y ^ ((p : ℝ)⁻¹)) ^ p = y := ENNReal.rpow_inv_natCast_pow hp y
          _ < (limsup u (atTop : Filter ℕ)) ^ p := hy
      obtain ⟨z, hz_left, hz_right⟩ := exists_between hy_root
      have hu : ∃ᶠ n in (atTop : Filter ℕ), z ≤ u n :=
        (Filter.le_limsup_iff').mp le_rfl z hz_right
      have hzpow : y < z ^ p := by
        calc
          y = (y ^ ((p : ℝ)⁻¹)) ^ p := (ENNReal.rpow_inv_natCast_pow hp y).symm
          _ < z ^ p := (ENNReal.pow_lt_pow_left_iff hp).2 hz_left
      exact hu.mono fun n hn ↦ (le_of_lt hzpow).trans (ENNReal.pow_le_pow_left hn)

/-- Helper for Exercise 5: coefficientwise division cancels against coefficientwise multiplication
when the denominator coefficients are nonzero. -/
lemma coeffwise_div_mul_cancel (a b : ℕ → 𝕜) (hb : ∀ n, b n ≠ 0) :
    (a / b) * b = a := by
  -- Reduce the statement to the pointwise field identity `(a_n / b_n) * b_n = a_n`.
  funext n
  simp [Pi.div_apply, Pi.mul_apply, hb n]

-- Core owner: `FormalMultilinearSeries.ofScalars` for the scalar series, together with the
-- chapter bridge `ofScalars_radius_inv_eq_limsup`. The exercise remains source-facing: it records
-- how coefficientwise algebra on the scalar sequence changes the radius.
--
-- Proof sketch: rewrite both sides through `ofScalars_radius_inv_eq_limsup`, then use
-- `‖a n ^ p‖ = ‖a n‖ ^ p` to compare the root-growth terms.
/-- Exercise 5 (1): the radius of convergence of the coefficientwise `p`-th power series
`U(X) = ∑ (a_n)^p X^n` is the `p`-th power of the radius of `S(X) = ∑ a_n X^n`. -/
theorem ofScalars_radius_eq_pow_of_coeffwisePow
    (a : ℕ → 𝕜) (p : ℕ) :
    (ofScalars 𝕜 (a ^ p)).radius = (ofScalars 𝕜 a).radius ^ p := by
  -- Compare inverse radii through Hadamard's root formula.
  rw [← inv_inj]
  rw [ENNReal.inv_pow, ofScalars_radius_inv_eq_limsup, ofScalars_radius_inv_eq_limsup]
  -- Rewrite the powered coefficients pointwise, then commute the natural power with `limsup`.
  simp_rw [coeffwise_pow_root_term]
  simpa using
    limsup_pow_atTop
      (fun n ↦ ((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) p

-- Proof sketch: apply `ofScalars_radius_inv_eq_limsup` to both scalar series and compare the
-- coefficient growth of `a n * b n` with the product of the growth controls for `a n` and `b n`.
/-- Exercise 5 (2): the radius of convergence of the Hadamard product
`V(X) = ∑ (a_n b_n) X^n` is at least the product of the radii of `S` and `T`. -/
theorem ofScalars_radius_hadamardMul_ge
    (a b : ℕ → 𝕜) :
    (ofScalars 𝕜 a).radius * (ofScalars 𝕜 b).radius ≤
      (ofScalars 𝕜 (a * b)).radius := by
  let ra : ℝ≥0∞ := (ofScalars 𝕜 a).radius
  let rb : ℝ≥0∞ := (ofScalars 𝕜 b).radius
  let rab : ℝ≥0∞ := (ofScalars 𝕜 (a * b)).radius
  by_cases hra0 : ra = 0
  · simp [ra, hra0]
  by_cases hrb0 : rb = 0
  · simp [rb, hrb0]
  -- Reduce the target to bounding every finite radius strictly below `ρ(S) * ρ(T)`.
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hr_ne_top : (r : ℝ≥0∞) ≠ ⊤ := by
    simp
  -- Choose `s < ρ(S)` so that `r / ρ(T) < s`.
  have hrs : (r : ℝ≥0∞) / rb < ra := by
    exact
      (ENNReal.div_lt_iff (a := ra) (b := rb) (c := (r : ℝ≥0∞))
        (Or.inl hrb0) (Or.inr hr_ne_top)).2 hr
  obtain ⟨s, hs_left, hs_right⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hrs
  have hs0 : (s : ℝ≥0∞) ≠ 0 := by
    intro hs_zero
    have hzero : ((r : ℝ≥0∞) / rb) < 0 := by
      simpa [hs_zero] using hs_left
    simpa using hzero
  have hs_ne_top : (s : ℝ≥0∞) ≠ ⊤ := by
    simp
  -- Choose `t < ρ(T)` so that `r / s < t`.
  have hrt : (r : ℝ≥0∞) / s < rb := by
    apply
      (ENNReal.div_lt_iff (a := rb) (b := (s : ℝ≥0∞)) (c := (r : ℝ≥0∞))
        (Or.inl hs0) (Or.inl hs_ne_top)).2
    have hmul : (r : ℝ≥0∞) < (s : ℝ≥0∞) * rb := by
      exact
        (ENNReal.div_lt_iff (a := (s : ℝ≥0∞)) (b := rb) (c := (r : ℝ≥0∞))
          (Or.inl hrb0) (Or.inr hr_ne_top)).1 hs_left
    simpa [mul_comm] using hmul
  obtain ⟨t, ht_left, ht_right⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hrt
  have ht_ne_top : (t : ℝ≥0∞) ≠ ⊤ := by
    simp
  have hst : (r : ℝ≥0∞) < (s : ℝ≥0∞) * t := by
    have hmul : (r : ℝ≥0∞) < (t : ℝ≥0∞) * s := by
      exact
        (ENNReal.div_lt_iff (a := (t : ℝ≥0∞)) (b := (s : ℝ≥0∞)) (c := (r : ℝ≥0∞))
          (Or.inl hs0) (Or.inl hs_ne_top)).1 ht_left
    simpa [mul_comm] using hmul
  -- Bound the weighted coefficient sequences for `a` and `b` separately below their radii.
  obtain ⟨Ca, hCa_pos, hCa⟩ : ∃ Ca > 0, ∀ n, ‖ofScalars 𝕜 a n‖₊ * s ^ n ≤ Ca := by
    simpa [ra] using (ofScalars 𝕜 a).nnnorm_mul_pow_le_of_lt_radius hs_right
  obtain ⟨Cb, hCb_pos, hCb⟩ : ∃ Cb > 0, ∀ n, ‖ofScalars 𝕜 b n‖₊ * t ^ n ≤ Cb := by
    simpa [rb] using (ofScalars 𝕜 b).nnnorm_mul_pow_le_of_lt_radius ht_right
  -- Multiply the two bounds to control the Hadamard coefficients at radius `s * t`.
  have hbound : ∀ n, ‖ofScalars 𝕜 (a * b) n‖₊ * (s * t) ^ n ≤ Ca * Cb := by
    intro n
    have hna : ‖ofScalars 𝕜 a n‖₊ = ‖a n‖₊ := Subtype.ext (ofScalars_norm 𝕜 a n)
    have hnb : ‖ofScalars 𝕜 b n‖₊ = ‖b n‖₊ := Subtype.ext (ofScalars_norm 𝕜 b n)
    have hnm0 : ‖ofScalars 𝕜 (a * b) n‖₊ = ‖(a * b) n‖₊ := Subtype.ext (ofScalars_norm 𝕜 (a * b) n)
    have hnm : ‖ofScalars 𝕜 (a * b) n‖₊ = ‖a n‖₊ * ‖b n‖₊ := by
      rw [hnm0, Pi.mul_apply, nnnorm_mul]
    have hm := mul_le_mul' (hCa n) (hCb n)
    simpa [hna, hnb, hnm, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hm
  have hrad : (((s * t : NNReal) : ℝ≥0∞)) ≤ rab := by
    simpa [rab] using (ofScalars 𝕜 (a * b)).le_radius_of_bound_nnreal (Ca * Cb) hbound
  exact (le_of_lt hst).trans hrad

-- Proof sketch: rewrite the quotient series through `ofScalars_radius_inv_eq_limsup`, use
-- `‖a n / b n‖ = ‖a n‖ / ‖b n‖`, and compare the resulting root-test expressions. The
-- coefficientwise nonzero assumption keeps the quotient coefficients faithful to the source.
-- In `ℝ≥0∞`, the textbook quotient assertion also needs the denominator radius to be finite:
-- otherwise `⊤ / ⊤ = 0`, producing a false formal statement.
/-- Exercise 5 (3): if every coefficient `b_n` is nonzero and `T` has nonzero radius of
convergence with finite radius, then the radius of convergence of
`W(X) = ∑ (a_n / b_n) X^n` is at most `ρ(S) / ρ(T)`. -/
theorem ofScalars_radius_coeffwiseDiv_le
    (a b : ℕ → 𝕜) (hb : ∀ n, b n ≠ 0)
    (hρT_pos : (ofScalars 𝕜 b).radius ≠ 0)
    (hρT_finite : (ofScalars 𝕜 b).radius ≠ ⊤) :
    (ofScalars 𝕜 (a / b)).radius ≤ (ofScalars 𝕜 a).radius / (ofScalars 𝕜 b).radius :=
  by
  -- Route correction: the source includes `ρ(T) ≠ 0`; the ENNReal formalization also needs
  -- finiteness of `ρ(T)` to avoid the `⊤ / ⊤ = 0` edge case.
  -- Move the quotient target back to the product inequality supplied by the Hadamard bound.
  rw [ENNReal.le_div_iff_mul_le (Or.inl hρT_pos) (Or.inl hρT_finite)]
  -- The coefficientwise product `((a / b) * b)` simplifies to `a` because each `b n` is nonzero.
  simpa [coeffwise_div_mul_cancel a b hb] using
    ofScalars_radius_hadamardMul_ge (𝕜 := 𝕜) (a / b) b
