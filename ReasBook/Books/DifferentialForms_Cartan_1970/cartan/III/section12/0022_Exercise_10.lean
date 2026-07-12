import Mathlib

-- Domain sampling note: this item lives in one-variable complex analysis on the unit disc.
-- The source-facing declaration below is a rigidity theorem for holomorphic self-maps of the disc.
-- The canonical owner abstractions upstream are Mathlib's fixed-point predicate
-- `Function.IsFixedPt` and the Schwarz-lemma equality API in
-- `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`, so the theorem keeps only the primitive
-- disc data (`DifferentiableOn`, `MapsTo`) and uses the owner fixed-point predicate for the two
-- distinguished points instead of parallel raw equality hypotheses.

-- Declarations for this item will be appended below by the statement pipeline.

open Function Metric Set
open scoped ComplexConjugate

/-- Helper for Exercise 10: the standard unit-disc automorphism sending `a` to the origin. -/
noncomputable def discCenter (a z : ℂ) : ℂ :=
  (z - a) / (1 - conj a * z)

/-- Helper for Exercise 10: the inverse unit-disc automorphism sending the origin to `a`. -/
noncomputable def discUncenter (a z : ℂ) : ℂ :=
  discCenter (-a) z

/-- Helper for Exercise 10: the key norm-squared identity for the centered disc automorphism. -/
lemma disc_center_normSq_gap (a z : ℂ) :
    Complex.normSq (1 - conj a * z) - Complex.normSq (z - a) =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  -- Expand both norm squares so the mixed real-part terms cancel.
  rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul,
    Complex.normSq_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h_re : Complex.re (a * conj z) = Complex.re (z * conj a) := by
    calc
      Complex.re (a * conj z) = Complex.re (conj (a * conj z)) := by
        simp
      _ = Complex.re (z * conj a) := by
        simp [mul_comm]
  have h_cross : (1 * conj (conj a * z)).re = Complex.re (z * conj a) := by
    calc
      (1 * conj (conj a * z)).re = Complex.re (conj (conj a * z)) := by
        simp
      _ = Complex.re (a * conj z) := by
        simp [mul_comm]
      _ = Complex.re (z * conj a) := h_re
  rw [h_cross]
  ring

/-- Helper for Exercise 10: the denominator of `discCenter a` does not vanish on the unit disc. -/
lemma disc_center_denom_ne_zero {a z : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    1 - conj a * z ≠ 0 := by
  have ha_lt : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hz_lt : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hgap_pos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    have ha_sq : 0 < 1 - ‖a‖ ^ 2 := by
      nlinarith [norm_nonneg a, ha_lt]
    have hz_sq : 0 < 1 - ‖z‖ ^ 2 := by
      nlinarith [norm_nonneg z, hz_lt]
    exact mul_pos ha_sq hz_sq
  have hgap := disc_center_normSq_gap a z
  have hden_pos : 0 < Complex.normSq (1 - conj a * z) := by
    -- The gap identity makes the denominator norm strictly positive.
    have hnum_nonneg : 0 ≤ Complex.normSq (z - a) := Complex.normSq_nonneg _
    nlinarith [hgap, hnum_nonneg, hgap_pos]
  exact Complex.normSq_pos.1 hden_pos

/-- Helper for Exercise 10: the centered Möbius map preserves the open unit disc. -/
lemma disc_center_mapsTo_unit_ball {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    MapsTo (discCenter a) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro z hz
  have ha_lt : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hz_lt : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hgap : Complex.normSq (1 - conj a * z) - Complex.normSq (z - a) =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := disc_center_normSq_gap a z
  have hgap_pos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    have ha_sq : 0 < 1 - ‖a‖ ^ 2 := by
      nlinarith [norm_nonneg a, ha_lt]
    have hz_sq : 0 < 1 - ‖z‖ ^ 2 := by
      nlinarith [norm_nonneg z, hz_lt]
    exact mul_pos ha_sq hz_sq
  have hden_pos : 0 < Complex.normSq (1 - conj a * z) := by
    -- The same gap identity shows the denominator norm is strictly positive.
    have hnum_nonneg : 0 ≤ Complex.normSq (z - a) := Complex.normSq_nonneg _
    nlinarith [hgap, hnum_nonneg, hgap_pos]
  have hnum_lt : Complex.normSq (z - a) < Complex.normSq (1 - conj a * z) := by
    nlinarith [hgap, hgap_pos]
  have hnormSq_lt : Complex.normSq (discCenter a z) < 1 := by
    rw [discCenter, Complex.normSq_div]
    exact (div_lt_one hden_pos).2 hnum_lt
  have hsq_lt : ‖discCenter a z‖ ^ 2 < 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hnormSq_lt
  have hnorm_lt : ‖discCenter a z‖ < 1 := by
    nlinarith [norm_nonneg (discCenter a z), hsq_lt]
  exact mem_ball_zero_iff.2 hnorm_lt

/-- Helper for Exercise 10: the inverse centered Möbius map also preserves the unit disc. -/
lemma disc_uncenter_mapsTo_unit_ball {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    MapsTo (discUncenter a) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  have hneg : -a ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, norm_neg] using ha
  -- `discUncenter a` is `discCenter (-a)`.
  simpa [discUncenter] using (disc_center_mapsTo_unit_ball hneg)

/-- Helper for Exercise 10: the disc automorphism centered at `a`
is holomorphic on the unit disc. -/
lemma disc_center_differentiableOn {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (discCenter a) (ball (0 : ℂ) 1) := by
  intro z hz
  -- Differentiate numerator and denominator separately; the denominator never vanishes on the disc.
  have hden_diff : DifferentiableAt ℂ (fun w : ℂ ↦ 1 - conj a * w) z := by
    fun_prop
  exact ((differentiableAt_id.sub_const a).div hden_diff
    (disc_center_denom_ne_zero ha hz)).differentiableWithinAt

/-- Helper for Exercise 10: the inverse disc automorphism is holomorphic on the unit disc. -/
lemma disc_uncenter_differentiableOn {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (discUncenter a) (ball (0 : ℂ) 1) := by
  have hneg : -a ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, norm_neg] using ha
  -- Reduce to the centered map at `-a`.
  simpa [discUncenter] using (disc_center_differentiableOn hneg)

/-- Helper for Exercise 10: the centered and uncentered Möbius maps are inverse on the unit disc. -/
lemma disc_uncenter_leftInvOn_disc_center {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    Set.LeftInvOn (discUncenter a) (discCenter a) (ball (0 : ℂ) 1) := by
  intro z hz
  have hden_center : 1 - conj a * z ≠ 0 := disc_center_denom_ne_zero ha hz
  have ha_sq_ne : ((1 : ℂ) - ‖a‖ ^ 2) ≠ 0 := by
    have ha_lt : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
    have ha_sq_pos : 0 < (1 : ℝ) - ‖a‖ ^ 2 := by
      nlinarith [norm_nonneg a, ha_lt]
    exact_mod_cast ha_sq_pos.ne'
  have hden_formula :
      1 + conj a * discCenter a z = ((1 : ℂ) - ‖a‖ ^ 2) / (1 - conj a * z) := by
    -- Normalize the denominator appearing in the inverse map.
    unfold discCenter
    have hsplit :
        1 + conj a * ((z - a) / (1 - conj a * z)) =
          (1 - conj a * z + conj a * (z - a)) / (1 - conj a * z) := by
      field_simp [hden_center]
    rw [hsplit]
    have hnumerator : 1 - conj a * z + conj a * (z - a) = (1 : ℂ) - ‖a‖ ^ 2 := by
      calc
        1 - conj a * z + conj a * (z - a) = 1 - conj a * z + conj a * z - conj a * a := by
          ring
        _ = (1 : ℂ) - conj a * a := by
          ring
        _ = (1 : ℂ) - ‖a‖ ^ 2 := by
          rw [Complex.conj_mul']
    rw [hnumerator]
  have hnum_formula :
      discCenter a z + a = z * (((1 : ℂ) - ‖a‖ ^ 2) / (1 - conj a * z)) := by
    -- Put the numerator over the same common denominator.
    unfold discCenter
    have hsplit :
        (z - a) / (1 - conj a * z) + a =
          ((z - a) + a * (1 - conj a * z)) / (1 - conj a * z) := by
      have hden_center' : 1 - z * conj a ≠ 0 := by
        simpa [mul_comm] using hden_center
      field_simp [hden_center, hden_center']
    rw [hsplit]
    have hnumerator : (z - a) + a * (1 - conj a * z) = z * ((1 : ℂ) - ‖a‖ ^ 2) := by
      calc
        (z - a) + a * (1 - conj a * z) = z - a + a - a * (conj a * z) := by
          ring
        _ = z - z * (a * conj a) := by
          ring
        _ = z - z * ‖a‖ ^ 2 := by
          rw [Complex.mul_conj']
        _ = z * ((1 : ℂ) - ‖a‖ ^ 2) := by
          ring
    rw [hnumerator, mul_div_assoc]
  have hfrac_ne : (((1 : ℂ) - ‖a‖ ^ 2) / (1 - conj a * z)) ≠ 0 := by
    exact div_ne_zero ha_sq_ne hden_center
  -- Rewrite both pieces of the inverse map using the same fraction, then cancel it.
  calc
    discUncenter a (discCenter a z) = (discCenter a z + a) / (1 + conj a * discCenter a z) := by
      simp [discUncenter, discCenter]
    _ = (z * (((1 : ℂ) - ‖a‖ ^ 2) / (1 - conj a * z))) /
          (((1 : ℂ) - ‖a‖ ^ 2) / (1 - conj a * z)) := by
      rw [hnum_formula, hden_formula]
    _ = z := by
      calc
        (z * (((1 : ℂ) - ‖a‖ ^ 2) / (1 - conj a * z))) /
            (((1 : ℂ) - ‖a‖ ^ 2) / (1 - conj a * z)) =
            z * ((((1 : ℂ) - ‖a‖ ^ 2) / (1 - conj a * z)) /
              (((1 : ℂ) - ‖a‖ ^ 2) / (1 - conj a * z))) := by
          rw [mul_div_assoc]
        _ = z := by
          rw [div_self hfrac_ne, mul_one]

/-- Helper for Exercise 10: the centered automorphism fixes its center. -/
@[simp] lemma disc_center_self (a : ℂ) : discCenter a a = 0 := by
  -- The numerator vanishes at the center.
  simp [discCenter]

/-- Helper for Exercise 10: the uncentered automorphism sends the origin back to `a`. -/
@[simp] lemma disc_uncenter_zero (a : ℂ) : discUncenter a 0 = a := by
  -- This is the explicit formula at the origin.
  simp [discUncenter, discCenter]

/-- Exercise 10: if `f` is holomorphic on the open unit disc, maps the disc to itself, and fixes
two distinct points of the disc, then `f` is the identity on that disc. -/
theorem eqOn_id_on_unit_disc_of_two_fixed_points
    {f : ℂ → ℂ} {a b : ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (h_maps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (ha : a ∈ ball (0 : ℂ) 1)
    (hb : b ∈ ball (0 : ℂ) 1)
    (hab : a ≠ b)
    (hfa : f.IsFixedPt a)
    (hfb : f.IsFixedPt b) :
    EqOn f id (ball (0 : ℂ) 1) := by
  let g : ℂ → ℂ := discCenter a ∘ f ∘ discUncenter a
  let z₀ : ℂ := discCenter a b
  have h_uncenter_maps : MapsTo (discUncenter a) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    disc_uncenter_mapsTo_unit_ball ha
  have h_center_maps : MapsTo (discCenter a) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    disc_center_mapsTo_unit_ball ha
  have hleft : Set.LeftInvOn (discUncenter a) (discCenter a) (ball (0 : ℂ) 1) :=
    disc_uncenter_leftInvOn_disc_center ha
  have h_center_diff : DifferentiableOn ℂ (discCenter a) (ball (0 : ℂ) 1) :=
    disc_center_differentiableOn ha
  have h_uncenter_diff : DifferentiableOn ℂ (discUncenter a) (ball (0 : ℂ) 1) :=
    disc_uncenter_differentiableOn ha
  have hg_diff : DifferentiableOn ℂ g (ball (0 : ℂ) 1) := by
    -- Differentiate the conjugated map one composition at a time.
    let h : ℂ → ℂ := f ∘ discUncenter a
    have hh_diff : DifferentiableOn ℂ h (ball (0 : ℂ) 1) := by
      simpa [h] using hf.comp h_uncenter_diff h_uncenter_maps
    have hh_maps : MapsTo h (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
      intro z hz
      exact h_maps (h_uncenter_maps hz)
    simpa [g, h] using h_center_diff.comp hh_diff hh_maps
  have hg_maps_ball : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    -- Conjugation keeps the image inside the unit disc.
    exact h_center_maps (h_maps (h_uncenter_maps hz))
  have hg0 : g.IsFixedPt 0 := by
    -- The conjugated map fixes the origin because `f` fixes `a`.
    change discCenter a (f (discUncenter a 0)) = 0
    rw [disc_uncenter_zero, hfa.eq, disc_center_self]
  have hz₀_mem : z₀ ∈ ball (0 : ℂ) 1 := by
    -- Transport the second fixed point into the centered disc.
    exact h_center_maps hb
  have hz₀_fixed : g.IsFixedPt z₀ := by
    -- The second fixed point remains fixed after conjugation.
    change discCenter a (f (discUncenter a (discCenter a b))) = discCenter a b
    rw [hleft hb, hfb.eq]
  have hz₀_ne : z₀ ≠ 0 := by
    -- Distinctness survives because `discCenter a` is injective on the unit disc.
    have h_inj : InjOn (discCenter a) (ball (0 : ℂ) 1) := hleft.injOn
    intro hz
    have hba : b = a := h_inj hb ha (by simpa [z₀, disc_center_self] using hz)
    exact hab hba.symm
  have hdslope : dslope g 0 z₀ = 1 := by
    -- At the nonzero fixed point, the difference quotient is exactly `1`.
    rw [dslope_of_ne _ hz₀_ne, slope_def_module, sub_zero, hg0.eq, hz₀_fixed.eq, sub_zero,
      smul_eq_mul]
    exact inv_mul_cancel₀ hz₀_ne
  have hnorm_dslope : ‖dslope g 0 z₀‖ = 1 / 1 := by
    -- The Schwarz equality hypothesis is now immediate.
    simp [hdslope]
  have hg_maps_closed : MapsTo g (ball (0 : ℂ) 1) (closedBall (g 0) 1) := by
    intro z hz
    -- The open-disc image lies in the closed ball of the same radius.
    simpa [hg0.eq] using ball_subset_closedBall (hg_maps_ball hz)
  have hg_eq : EqOn g id (ball (0 : ℂ) 1) := by
    -- Apply the equality case of Schwarz's lemma to the centered map.
    have h_affine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
      hg_diff hg_maps_closed hz₀_mem hnorm_dslope
    intro z hz
    simpa [hg0.eq, hdslope] using h_affine hz
  intro z hz
  have hz_center : discCenter a z ∈ ball (0 : ℂ) 1 := h_center_maps hz
  have h_centered : g (discCenter a z) = discCenter a z := hg_eq hz_center
  have h_pullback : discUncenter a (discCenter a z) = z := hleft hz
  have h_center_eq : discCenter a (f z) = discCenter a z := by
    -- Evaluate the centered identity at `discCenter a z` and undo the conjugation.
    simpa [g, h_pullback] using h_centered
  have h_inj : InjOn (discCenter a) (ball (0 : ℂ) 1) := hleft.injOn
  -- Cancel the centered automorphism to recover `f z = z`.
  exact h_inj (h_maps hz) hz h_center_eq
