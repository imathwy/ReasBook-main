import SmoothManifolds_Lee_2012.Chap02.Sec02_10.Lemma_2_20

-- Declarations for this item will be appended below by the statement pipeline.

open Real
open scoped ContDiff

/-- Helper for Lemma 2.21: the normalized cutoff built from the two complementary distances to
`r₁` and `r₂`. -/
private noncomputable def one_zero_cutoff (r₁ r₂ : ℝ) : ℝ → ℝ :=
  fun t ↦ expNegInvGlue (r₂ - t) / (expNegInvGlue (r₂ - t) + expNegInvGlue (t - r₁))

/-- Helper for Lemma 2.21: the denominator in the normalized cutoff is everywhere positive. -/
private lemma cutoff_denominator_pos {r₁ r₂ : ℝ} (hr : r₁ < r₂) (t : ℝ) :
    0 < expNegInvGlue (r₂ - t) + expNegInvGlue (t - r₁) := by
  -- One translated argument is positive on each side of the split at `r₂`.
  rcases lt_or_ge t r₂ with ht | ht
  · exact add_pos_of_pos_of_nonneg
      (expNegInvGlue.pos_of_pos (sub_pos.2 ht))
      (expNegInvGlue.nonneg _)
  · exact add_pos_of_nonneg_of_pos
      (expNegInvGlue.nonneg _)
      (expNegInvGlue.pos_of_pos (sub_pos.2 (lt_of_lt_of_le hr ht)))

/-- Helper for Lemma 2.21: the normalized cutoff is smooth because it is a quotient of smooth
affine reparameterizations of `expNegInvGlue` with nowhere-vanishing denominator. -/
private lemma one_zero_cutoff_contDiff {r₁ r₂ : ℝ} (hr : r₁ < r₂) :
    ContDiff ℝ ∞ (one_zero_cutoff r₁ r₂) := by
  -- Compose the smooth building block with the two affine maps in the numerator and denominator.
  have h_left : ContDiff ℝ ∞ (fun t : ℝ ↦ expNegInvGlue (r₂ - t)) := by
    simpa using expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have h_right : ContDiff ℝ ∞ (fun t : ℝ ↦ expNegInvGlue (t - r₁)) := by
    simpa using expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)
  -- Divide by the denominator once the global positivity invariant is available.
  simpa [one_zero_cutoff] using
    h_left.div (h_left.add h_right) (fun t ↦ (cutoff_denominator_pos hr t).ne')

/-- Helper for Lemma 2.21: on the left of `r₁`, the normalized cutoff is identically `1`. -/
private lemma one_zero_cutoff_eq_one_of_le {r₁ r₂ : ℝ} (hr : r₁ < r₂) {t : ℝ}
    (ht : t ≤ r₁) : one_zero_cutoff r₁ r₂ t = 1 := by
  have h_left_pos : 0 < expNegInvGlue (r₂ - t) := by
    exact expNegInvGlue.pos_of_pos (sub_pos.2 (lt_of_le_of_lt ht hr))
  have h_right_zero : expNegInvGlue (t - r₁) = 0 := by
    exact expNegInvGlue.zero_of_nonpos (sub_nonpos.2 ht)
  -- The denominator collapses to the numerator, so the quotient is `1`.
  rw [one_zero_cutoff, h_right_zero, add_zero, div_self h_left_pos.ne']

/-- Helper for Lemma 2.21: between `r₁` and `r₂`, the normalized cutoff lies strictly between
`0` and `1`. -/
private lemma one_zero_cutoff_pos_lt_one_of_between {r₁ r₂ : ℝ} (hr : r₁ < r₂) {t : ℝ}
    (ht₁ : r₁ < t) (ht₂ : t < r₂) :
    0 < one_zero_cutoff r₁ r₂ t ∧ one_zero_cutoff r₁ r₂ t < 1 := by
  have h_num : 0 < expNegInvGlue (r₂ - t) := by
    exact expNegInvGlue.pos_of_pos (sub_pos.2 ht₂)
  have h_other : 0 < expNegInvGlue (t - r₁) := by
    exact expNegInvGlue.pos_of_pos (sub_pos.2 ht₁)
  have h_den : 0 < expNegInvGlue (r₂ - t) + expNegInvGlue (t - r₁) := by
    exact cutoff_denominator_pos hr t
  refine ⟨?_, ?_⟩
  · -- Positivity comes from positivity of both the numerator and denominator.
    simpa [one_zero_cutoff] using div_pos h_num h_den
  · -- The denominator is the numerator plus an additional positive summand.
    simpa [one_zero_cutoff] using
      (div_lt_one h_den).2 (lt_add_of_pos_right (expNegInvGlue (r₂ - t)) h_other)

/-- Helper for Lemma 2.21: on the right of `r₂`, the normalized cutoff is identically `0`. -/
private lemma one_zero_cutoff_eq_zero_of_ge {r₁ r₂ : ℝ} (_hr : r₁ < r₂) {t : ℝ}
    (ht : r₂ ≤ t) : one_zero_cutoff r₁ r₂ t = 0 := by
  have h_left_zero : expNegInvGlue (r₂ - t) = 0 := by
    exact expNegInvGlue.zero_of_nonpos (sub_nonpos.2 ht)
  -- The numerator vanishes on the right-hand region.
  rw [one_zero_cutoff, h_left_zero, zero_div]

/-- Lemma 2.21: given real numbers `r₁ < r₂`, there exists a smooth function `h : ℝ → ℝ` such
that `h t = 1` for `t ≤ r₁`, `0 < h t ∧ h t < 1` for `r₁ < t < r₂`, and `h t = 0` for
`t ≥ r₂`. -/
theorem exists_one_zero_smooth_cutoff {r₁ r₂ : ℝ} (hr : r₁ < r₂) :
    ∃ h : ℝ → ℝ,
      ContDiff ℝ ∞ h ∧
      (∀ ⦃t : ℝ⦄, t ≤ r₁ → h t = 1) ∧
      (∀ ⦃t : ℝ⦄, r₁ < t → t < r₂ → 0 < h t ∧ h t < 1) ∧
      ∀ ⦃t : ℝ⦄, r₂ ≤ t → h t = 0 := by
  -- Route correction: use Lee's normalized `expNegInvGlue` quotient directly.
  refine ⟨one_zero_cutoff r₁ r₂, ?_, ?_, ?_, ?_⟩
  · -- Smoothness is the quotient smoothness packaged in the helper lemma.
    exact one_zero_cutoff_contDiff hr
  · intro t ht
    -- On the left, the second translated cutoff has already vanished.
    exact one_zero_cutoff_eq_one_of_le hr ht
  · intro t ht₁ ht₂
    -- In the open interval, both translated cutoffs are positive.
    exact one_zero_cutoff_pos_lt_one_of_between hr ht₁ ht₂
  · intro t ht
    -- On the right, the numerator has already vanished.
    exact one_zero_cutoff_eq_zero_of_ge hr ht
