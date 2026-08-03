import BauschkeLean.Chap12.ProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ERealFunction

-- Semantic search note: `lean_leansearch` only surfaced unrelated complex-analysis proximity
-- lemmas, so this item follows the established Chapter 24 pattern: an explicit `]-∞,+∞]` owner
-- together with the general Chapter 12 `HasUniqueProxPoint`/`proximityOperator` surface.

variable (ωLower : Set.Iio (0 : ℝ)) (ωUpper : Set.Ioi (0 : ℝ))

/-- The split logarithmic barrier on `]ωLower, 0] ∪ ]0, ωUpper[` with value
`-log (ξ - ωLower) + log (-ωLower)` on the nonpositive side, value
`-log (ωUpper - ξ) + log ωUpper` on the positive side, and `+∞` outside `]ωLower, ωUpper[`. -/
def splitLogBarrier (ωLower : Set.Iio (0 : ℝ)) (ωUpper : Set.Ioi (0 : ℝ)) :
    ℝ → Set.Ioi (⊥ : EReal) :=
  ι[Set.Ioo (ωLower : ℝ) (ωUpper : ℝ)] +
    (fun ξ : ℝ ↦
      if ξ ≤ 0 then
        -Real.log (ξ - (ωLower : ℝ)) + Real.log (-(ωLower : ℝ))
      else
        -Real.log ((ωUpper : ℝ) - ξ) + Real.log (ωUpper : ℝ)).toEReal

variable {ωLower ωUpper}

@[simp] theorem splitLogBarrier_apply_of_mem_Ioo_nonpos {ξ : ℝ}
    (hξ : ξ ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ)) (hξ_nonpos : ξ ≤ 0) :
    (splitLogBarrier ωLower ωUpper ξ : EReal) =
      ((-Real.log (ξ - (ωLower : ℝ)) + Real.log (-(ωLower : ℝ)) : ℝ) : EReal) := by
  simp [splitLogBarrier, hξ, hξ_nonpos]

@[simp] theorem splitLogBarrier_apply_of_mem_Ioo_pos {ξ : ℝ}
    (hξ : ξ ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ)) (hξ_pos : 0 < ξ) :
    (splitLogBarrier ωLower ωUpper ξ : EReal) =
      ((-Real.log ((ωUpper : ℝ) - ξ) + Real.log (ωUpper : ℝ) : ℝ) : EReal) := by
  simp [splitLogBarrier, hξ, not_le_of_gt hξ_pos]

@[simp] theorem splitLogBarrier_apply_of_not_mem_Ioo {ξ : ℝ}
    (hξ : ξ ∉ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ)) :
    (splitLogBarrier ωLower ωUpper ξ : EReal) = ⊤ := by
  simpa [splitLogBarrier, indicator_apply, hξ] using
    (EReal.top_add_coe
      (if ξ ≤ 0 then
        -Real.log (ξ - (ωLower : ℝ)) + Real.log (-(ωLower : ℝ))
      else
        -Real.log ((ωUpper : ℝ) - ξ) + Real.log (ωUpper : ℝ)))

@[simp] theorem effectiveDomain_splitLogBarrier :
    effectiveDomain (splitLogBarrier ωLower ωUpper) = Set.Ioo (ωLower : ℝ) (ωUpper : ℝ) := by
  ext ξ
  constructor
  · intro hξ
    by_contra hnot
    rw [mem_effectiveDomain_iff, splitLogBarrier_apply_of_not_mem_Ioo hnot] at hξ
    exact lt_irrefl _ hξ
  · intro hξ
    rw [mem_effectiveDomain_iff]
    by_cases hξ_nonpos : ξ ≤ 0
    · rw [splitLogBarrier_apply_of_mem_Ioo_nonpos hξ hξ_nonpos]
      simpa using
        (EReal.coe_lt_top (-Real.log (ξ - (ωLower : ℝ)) + Real.log (-(ωLower : ℝ))))
    · have hξ_pos : 0 < ξ := lt_of_not_ge hξ_nonpos
      rw [splitLogBarrier_apply_of_mem_Ioo_pos hξ hξ_pos]
      simpa using
        (EReal.coe_lt_top (-Real.log ((ωUpper : ℝ) - ξ) + Real.log (ωUpper : ℝ)))

/-- Helper for Example 24.41: the nonpositive branch of the proximal objective, written as a
real-valued seed function. -/
private def leftProxSeed (ωLower : Set.Iio (0 : ℝ)) (ξ y : ℝ) : ℝ :=
  -Real.log (y - (ωLower : ℝ)) + Real.log (-(ωLower : ℝ)) +
    (1 / 2 : ℝ) * y ^ (2 : ℕ) - ξ * y + (1 / 2 : ℝ) * ξ ^ (2 : ℕ)

/-- Helper for Example 24.41: the positive branch of the proximal objective, written as a
real-valued seed function. -/
private def rightProxSeed (ωUpper : Set.Ioi (0 : ℝ)) (ξ y : ℝ) : ℝ :=
  -Real.log ((ωUpper : ℝ) - y) + Real.log (ωUpper : ℝ) +
    (1 / 2 : ℝ) * y ^ (2 : ℕ) - ξ * y + (1 / 2 : ℝ) * ξ ^ (2 : ℕ)

/-- Helper for Example 24.41: the left quadratic-root candidate from formula `(24.76)`. -/
private def leftCandidate (ωLower : Set.Iio (0 : ℝ)) (ξ : ℝ) : ℝ :=
  (ξ + (ωLower : ℝ) + Real.sqrt (|ξ - (ωLower : ℝ)| ^ (2 : ℕ) + 4)) / 2

/-- Helper for Example 24.41: the right quadratic-root candidate from formula `(24.76)`. -/
private def rightCandidate (ωUpper : Set.Ioi (0 : ℝ)) (ξ : ℝ) : ℝ :=
  (ξ + (ωUpper : ℝ) - Real.sqrt (|ξ - (ωUpper : ℝ)| ^ (2 : ℕ) + 4)) / 2

/-- Helper for Example 24.41: on the nonpositive branch, the seed is exactly the proximal
objective. -/
private theorem leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos (ξ y : ℝ)
    (hy : y ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ)) (hy_nonpos : y ≤ 0) :
    (leftProxSeed ωLower ξ y : EReal) =
      proximalObjective (splitLogBarrier ωLower ωUpper) ξ y := by
  -- Rewrite the barrier to its active finite branch and expand the quadratic term.
  rw [proximalObjective, splitLogBarrier_apply_of_mem_Ioo_nonpos hy hy_nonpos,
    Real.norm_eq_abs, sq_abs]
  congr 1
  dsimp [leftProxSeed]
  ring

/-- Helper for Example 24.41: on the positive branch, the seed is exactly the proximal
objective. -/
private theorem rightProxSeed_eq_proximalObjective_of_mem_Ioo_pos (ξ y : ℝ)
    (hy : y ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ)) (hy_pos : 0 < y) :
    (rightProxSeed ωUpper ξ y : EReal) =
      proximalObjective (splitLogBarrier ωLower ωUpper) ξ y := by
  -- Rewrite the barrier to its active finite branch and expand the quadratic term.
  rw [proximalObjective, splitLogBarrier_apply_of_mem_Ioo_pos hy hy_pos,
    Real.norm_eq_abs, sq_abs]
  congr 1
  dsimp [rightProxSeed]
  ring

/-- Helper for Example 24.41: both branch seeds agree at the common boundary point `0`. -/
@[simp] private theorem branchSeeds_zero_eq (ξ : ℝ) :
    leftProxSeed ωLower ξ 0 = rightProxSeed ωUpper ξ 0 := by
  -- The logarithmic terms cancel at `0`, leaving the same quadratic value on both sides.
  simp [leftProxSeed, rightProxSeed]

/-- Helper for Example 24.41: the derivative of the nonpositive seed is
`y - ξ - 1 / (y - ωLower)`. -/
private theorem leftProxSeed_hasDerivAt (ξ y : ℝ) (hy : (ωLower : ℝ) < y) :
    HasDerivAt (leftProxSeed ωLower ξ) (y - ξ - 1 / (y - (ωLower : ℝ))) y := by
  have hy_pos : 0 < y - (ωLower : ℝ) := sub_pos.mpr hy
  have hlog :
      HasDerivAt (fun t : ℝ ↦ -Real.log (t - (ωLower : ℝ)))
        (-(1 / (y - (ωLower : ℝ)))) y := by
    have hsub : HasDerivAt (fun t : ℝ ↦ t - (ωLower : ℝ)) 1 y := by
      simpa [sub_eq_add_neg] using (hasDerivAt_id y).sub_const (ωLower : ℝ)
    simpa [one_div, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
      ((Real.hasDerivAt_log hy_pos.ne').comp y hsub).neg
  have hsq :
      HasDerivAt (fun t : ℝ ↦ (1 / 2 : ℝ) * t ^ (2 : ℕ)) y y := by
    simpa [pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id y).pow 2).const_mul (1 / 2 : ℝ)
  have hlin :
      HasDerivAt (fun t : ℝ ↦ -ξ * t) (-ξ) y := by
    simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_id y).const_mul (-ξ)
  -- Differentiate each seed summand separately and simplify the resulting slope.
  convert
      hlog.add
        ((hasDerivAt_const y (Real.log (-(ωLower : ℝ)))).add
          (hsq.add (hlin.add (hasDerivAt_const y ((1 / 2 : ℝ) * ξ ^ (2 : ℕ)))))) using 1
  · ext t
    simp [leftProxSeed, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · ring

/-- Helper for Example 24.41: the derivative of the positive seed is
`y - ξ + 1 / (ωUpper - y)`. -/
private theorem rightProxSeed_hasDerivAt (ξ y : ℝ) (hy : y < (ωUpper : ℝ)) :
    HasDerivAt (rightProxSeed ωUpper ξ) (y - ξ + 1 / ((ωUpper : ℝ) - y)) y := by
  have hy_pos : 0 < (ωUpper : ℝ) - y := sub_pos.mpr hy
  have hlog :
      HasDerivAt (fun t : ℝ ↦ -Real.log ((ωUpper : ℝ) - t))
        (1 / ((ωUpper : ℝ) - y)) y := by
    have hneg : HasDerivAt (fun t : ℝ ↦ -t) (-1) y := by
      simpa using (hasDerivAt_id y).neg
    have hsub : HasDerivAt (fun t : ℝ ↦ (ωUpper : ℝ) - t) (-1) y := by
      simpa [sub_eq_add_neg, add_comm] using hneg.const_add (ωUpper : ℝ)
    simpa [one_div, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
      ((Real.hasDerivAt_log hy_pos.ne').comp y hsub).neg
  have hsq :
      HasDerivAt (fun t : ℝ ↦ (1 / 2 : ℝ) * t ^ (2 : ℕ)) y y := by
    simpa [pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id y).pow 2).const_mul (1 / 2 : ℝ)
  have hlin :
      HasDerivAt (fun t : ℝ ↦ -ξ * t) (-ξ) y := by
    simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_id y).const_mul (-ξ)
  -- Differentiate each seed summand separately and simplify the resulting slope.
  convert
      hlog.add
        ((hasDerivAt_const y (Real.log (ωUpper : ℝ))).add
          (hsq.add (hlin.add (hasDerivAt_const y ((1 / 2 : ℝ) * ξ ^ (2 : ℕ)))))) using 1
  · ext t
    simp [rightProxSeed, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · ring

/-- Helper for Example 24.41: the left-branch derivative
`z ↦ z - ξ - 1 / (z - ωLower)` is strictly increasing on `]ωLower, +∞[`. -/
private theorem leftSeedSlope_strictMono (ξ : ℝ) :
    StrictMonoOn (fun z : ℝ ↦ z - ξ - 1 / (z - (ωLower : ℝ))) (Set.Ioi (ωLower : ℝ)) := by
  intro z hz p hp hzp
  have hzne : z - (ωLower : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hz)
  have hpne : p - (ωLower : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp)
  have hzw_pos : 0 < z - (ωLower : ℝ) := sub_pos.mpr hz
  have hpw_pos : 0 < p - (ωLower : ℝ) := sub_pos.mpr hp
  have hfactor_pos : 0 <
      1 + 1 / ((z - (ωLower : ℝ)) * (p - (ωLower : ℝ))) := by
    positivity
  have hdiff :
      (z - ξ - 1 / (z - (ωLower : ℝ))) - (p - ξ - 1 / (p - (ωLower : ℝ))) =
        (z - p) * (1 + 1 / ((z - (ωLower : ℝ)) * (p - (ωLower : ℝ)))) := by
    field_simp [hzne, hpne]
    ring
  -- The explicit difference formula makes the derivative monotonicity transparent.
  have hneg :
      (z - p) * (1 + 1 / ((z - (ωLower : ℝ)) * (p - (ωLower : ℝ)))) < 0 := by
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hzp) hfactor_pos
  have hdiff_neg :
      (z - ξ - 1 / (z - (ωLower : ℝ))) - (p - ξ - 1 / (p - (ωLower : ℝ))) < 0 := by
    rwa [hdiff]
  linarith

/-- Helper for Example 24.41: the right-branch derivative
`z ↦ z - ξ + 1 / (ωUpper - z)` is strictly increasing on `]-∞, ωUpper[`. -/
private theorem rightSeedSlope_strictMono (ξ : ℝ) :
    StrictMonoOn (fun z : ℝ ↦ z - ξ + 1 / ((ωUpper : ℝ) - z)) (Set.Iio (ωUpper : ℝ)) := by
  intro z hz p hp hzp
  have hzne : (ωUpper : ℝ) - z ≠ 0 := sub_ne_zero.mpr (ne_of_gt hz)
  have hpne : (ωUpper : ℝ) - p ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp)
  have huz_pos : 0 < (ωUpper : ℝ) - z := sub_pos.mpr hz
  have hup_pos : 0 < (ωUpper : ℝ) - p := sub_pos.mpr hp
  have hfactor_pos : 0 <
      1 + 1 / (((ωUpper : ℝ) - z) * ((ωUpper : ℝ) - p)) := by
    positivity
  have hdiff :
      (z - ξ + 1 / ((ωUpper : ℝ) - z)) - (p - ξ + 1 / ((ωUpper : ℝ) - p)) =
        (z - p) * (1 + 1 / (((ωUpper : ℝ) - z) * ((ωUpper : ℝ) - p))) := by
    field_simp [hzne, hpne]
    ring
  -- The same rational identity shows that the right-branch derivative is strictly increasing.
  have hneg :
      (z - p) * (1 + 1 / (((ωUpper : ℝ) - z) * ((ωUpper : ℝ) - p))) < 0 := by
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hzp) hfactor_pos
  have hdiff_neg :
      (z - ξ + 1 / ((ωUpper : ℝ) - z)) - (p - ξ + 1 / ((ωUpper : ℝ) - p)) < 0 := by
    rwa [hdiff]
  linarith

/-- Helper for Example 24.41: the left branch seed is minimized at `0` whenever
`(ωLower : ℝ)⁻¹ ≤ ξ`. -/
private theorem leftSeed_zero_le_of_inv_lower_le (ξ y : ℝ)
    (hξ : (ωLower : ℝ)⁻¹ ≤ ξ) (hy : y ∈ Set.Ioc (ωLower : ℝ) 0) :
    leftProxSeed ωLower ξ 0 ≤ leftProxSeed ωLower ξ y := by
  by_cases hy_zero : y = 0
  · -- The endpoint case is immediate.
    simpa [hy_zero]
  · have hy_lt_zero : y < 0 := lt_of_le_of_ne hy.2 hy_zero
    have hcont : ContinuousOn (leftProxSeed ωLower ξ) (Set.Icc y 0) := by
      intro z hz
      have hzw : (ωLower : ℝ) < z := lt_of_lt_of_le hy.1 hz.1
      exact (leftProxSeed_hasDerivAt (ωLower := ωLower) ξ z hzw).continuousAt.continuousWithinAt
    have hderiv :
        ∀ z ∈ Set.Ioo y 0, HasDerivAt (leftProxSeed ωLower ξ)
          (z - ξ - 1 / (z - (ωLower : ℝ))) z := by
      intro z hz
      exact leftProxSeed_hasDerivAt (ωLower := ωLower) ξ z (lt_trans hy.1 hz.1)
    -- Apply the mean value theorem and compare the intermediate slope with the slope at `0`.
    rcases
        exists_hasDerivAt_eq_slope
          (f := leftProxSeed ωLower ξ)
          (f' := fun z ↦ z - ξ - 1 / (z - (ωLower : ℝ)))
          hy_lt_zero hcont hderiv with
      ⟨c, hc, hcSlope⟩
    have hmono := leftSeedSlope_strictMono (ωLower := ωLower) ξ
    have hcSlope_lt_zeroSlope :
        c - ξ - 1 / (c - (ωLower : ℝ)) < 0 - ξ - 1 / (0 - (ωLower : ℝ)) := by
      exact hmono (lt_trans hy.1 hc.1) ωLower.2 hc.2
    have hw_ne : (ωLower : ℝ) ≠ 0 := ne_of_lt ωLower.2
    have hzeroSlope_nonpos : 0 - ξ - 1 / (0 - (ωLower : ℝ)) ≤ 0 := by
      have hrewrite :
          0 - ξ - 1 / (0 - (ωLower : ℝ)) = (ωLower : ℝ)⁻¹ - ξ := by
        field_simp [hw_ne]
        ring
      rw [hrewrite]
      linarith
    have hslope_neg :
        (leftProxSeed ωLower ξ 0 - leftProxSeed ωLower ξ y) / (0 - y) < 0 := by
      rw [← hcSlope]
      linarith
    have hden_pos : 0 < 0 - y := sub_pos.mpr hy_lt_zero
    have hdiff_neg : leftProxSeed ωLower ξ 0 - leftProxSeed ωLower ξ y < 0 := by
      by_contra hnonneg
      have hnonneg' : 0 ≤ leftProxSeed ωLower ξ 0 - leftProxSeed ωLower ξ y :=
        le_of_not_gt hnonneg
      have hquot_nonneg :
          0 ≤ (leftProxSeed ωLower ξ 0 - leftProxSeed ωLower ξ y) / (0 - y) := by
        exact div_nonneg hnonneg' hden_pos.le
      linarith
    linarith

/-- Helper for Example 24.41: the positive branch seed is minimized at `0` whenever
`ξ ≤ (ωUpper : ℝ)⁻¹`. -/
private theorem rightSeed_zero_le_of_le_inv_upper (ξ y : ℝ)
    (hξ : ξ ≤ (ωUpper : ℝ)⁻¹) (hy : y ∈ Set.Ico (0 : ℝ) (ωUpper : ℝ)) :
    rightProxSeed ωUpper ξ 0 ≤ rightProxSeed ωUpper ξ y := by
  by_cases hy_zero : y = 0
  · -- The endpoint case is immediate.
    simpa [hy_zero]
  · have hy_pos : 0 < y := lt_of_le_of_ne hy.1 (by simpa [eq_comm] using hy_zero)
    have hcont : ContinuousOn (rightProxSeed ωUpper ξ) (Set.Icc 0 y) := by
      intro z hz
      have hzu : z < (ωUpper : ℝ) := lt_of_le_of_lt hz.2 hy.2
      exact (rightProxSeed_hasDerivAt (ωUpper := ωUpper) ξ z hzu).continuousAt.continuousWithinAt
    have hderiv :
        ∀ z ∈ Set.Ioo 0 y, HasDerivAt (rightProxSeed ωUpper ξ)
          (z - ξ + 1 / ((ωUpper : ℝ) - z)) z := by
      intro z hz
      exact rightProxSeed_hasDerivAt (ωUpper := ωUpper) ξ z (lt_trans hz.2 hy.2)
    -- Apply the mean value theorem and compare the intermediate slope with the slope at `0`.
    rcases
        exists_hasDerivAt_eq_slope
          (f := rightProxSeed ωUpper ξ)
          (f' := fun z ↦ z - ξ + 1 / ((ωUpper : ℝ) - z))
          hy_pos hcont hderiv with
      ⟨c, hc, hcSlope⟩
    have hmono := rightSeedSlope_strictMono (ωUpper := ωUpper) ξ
    have hzeroSlope_lt_cSlope :
        0 - ξ + 1 / ((ωUpper : ℝ) - 0) < c - ξ + 1 / ((ωUpper : ℝ) - c) := by
      exact hmono ωUpper.2 (lt_trans hc.2 hy.2) hc.1
    have hu_ne : (ωUpper : ℝ) ≠ 0 := ne_of_gt ωUpper.2
    have hzeroSlope_nonneg : 0 ≤ 0 - ξ + 1 / ((ωUpper : ℝ) - 0) := by
      have hrewrite :
          0 - ξ + 1 / ((ωUpper : ℝ) - 0) = (ωUpper : ℝ)⁻¹ - ξ := by
        field_simp [hu_ne]
        ring
      rw [hrewrite]
      linarith
    have hslope_pos :
        0 < (rightProxSeed ωUpper ξ y - rightProxSeed ωUpper ξ 0) / (y - 0) := by
      rw [← hcSlope]
      linarith
    have hden_pos : 0 < y - 0 := by simpa using hy_pos
    have hdiff_pos : 0 < rightProxSeed ωUpper ξ y - rightProxSeed ωUpper ξ 0 := by
      by_contra hnonpos
      have hnonpos' : rightProxSeed ωUpper ξ y - rightProxSeed ωUpper ξ 0 ≤ 0 :=
        le_of_not_gt hnonpos
      have hquot_nonpos :
          (rightProxSeed ωUpper ξ y - rightProxSeed ωUpper ξ 0) / (y - 0) ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg hnonpos' hden_pos.le
      linarith
    linarith

/-- Helper for Example 24.41: the right quadratic candidate lies in `(0, ωUpper)` and solves
the positive stationary equation. -/
private theorem rightCandidate_mem_Ioo_and_stationary (ξ : ℝ)
    (hξ : (ωUpper : ℝ)⁻¹ < ξ) :
    rightCandidate ωUpper ξ ∈ Set.Ioo (0 : ℝ) (ωUpper : ℝ) ∧
      rightCandidate ωUpper ξ + 1 / ((ωUpper : ℝ) - rightCandidate ωUpper ξ) = ξ := by
  let Δ : ℝ := Real.sqrt (|ξ - (ωUpper : ℝ)| ^ (2 : ℕ) + 4)
  have hΔ_nonneg : 0 ≤ Δ := by
    simp [Δ]
  have hΔ_sq : Δ ^ (2 : ℕ) = (ξ - (ωUpper : ℝ)) ^ (2 : ℕ) + 4 := by
    have hrad_nonneg : 0 ≤ |ξ - (ωUpper : ℝ)| ^ (2 : ℕ) + 4 := by
      positivity
    simpa [Δ, sq_abs] using Real.sq_sqrt hrad_nonneg
  have hu_pos : 0 < (ωUpper : ℝ) := ωUpper.2
  have hu_ne : (ωUpper : ℝ) ≠ 0 := ne_of_gt hu_pos
  have hξ_pos : 0 < ξ := by
    have hu_inv_pos : 0 < (ωUpper : ℝ)⁻¹ := inv_pos.mpr hu_pos
    exact lt_trans hu_inv_pos hξ
  have hmul_gt : 1 < ξ * (ωUpper : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hξ hu_pos
    simpa [hu_ne, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hsum_pos : 0 < ξ + (ωUpper : ℝ) := by
    linarith
  have hΔ_lt_sum : Δ < ξ + (ωUpper : ℝ) := by
    have hsq_lt : Δ ^ (2 : ℕ) < (ξ + (ωUpper : ℝ)) ^ (2 : ℕ) := by
      nlinarith [hΔ_sq, hmul_gt]
    by_contra hnot
    have hsq_ge : (ξ + (ωUpper : ℝ)) ^ (2 : ℕ) ≤ Δ ^ (2 : ℕ) := by
      nlinarith [le_of_not_gt hnot, hsum_pos, hΔ_nonneg]
    linarith
  have habs_lt_Δ : |ξ - (ωUpper : ℝ)| < Δ := by
    by_contra hnot
    have hsq_ge : Δ ^ (2 : ℕ) ≤ |ξ - (ωUpper : ℝ)| ^ (2 : ℕ) := by
      nlinarith [le_of_not_gt hnot, abs_nonneg (ξ - (ωUpper : ℝ)), hΔ_nonneg]
    rw [sq_abs] at hsq_ge
    nlinarith [hΔ_sq]
  have hdiff_lt_Δ : ξ - (ωUpper : ℝ) < Δ := by
    exact lt_of_le_of_lt (le_abs_self (ξ - (ωUpper : ℝ))) habs_lt_Δ
  have hcand : rightCandidate ωUpper ξ = (ξ + (ωUpper : ℝ) - Δ) / 2 := by
    simp [rightCandidate, Δ, sq_abs]
  have hp_pos : 0 < rightCandidate ωUpper ξ := by
    -- The threshold `ξ > ωUpper⁻¹` gives `Δ < ξ + ωUpper`, hence the printed root is positive.
    rw [hcand]
    nlinarith
  have hp_lt_upper : rightCandidate ωUpper ξ < (ωUpper : ℝ) := by
    -- The square root dominates `ξ - ωUpper`, so the printed root stays below `ωUpper`.
    rw [hcand]
    nlinarith
  have hgap_pos : 0 < (ωUpper : ℝ) - rightCandidate ωUpper ξ := sub_pos.mpr hp_lt_upper
  have hproduct :
      (ξ - rightCandidate ωUpper ξ) * ((ωUpper : ℝ) - rightCandidate ωUpper ξ) = 1 := by
    -- Expanding the printed formula reduces the stationarity identity to the square-root equation.
    rw [hcand]
    field_simp
    nlinarith [hΔ_sq]
  have hrecip : 1 / ((ωUpper : ℝ) - rightCandidate ωUpper ξ) = ξ - rightCandidate ωUpper ξ := by
    have hgap_ne : (ωUpper : ℝ) - rightCandidate ωUpper ξ ≠ 0 := ne_of_gt hgap_pos
    apply mul_right_cancel₀ hgap_ne
    calc
      (1 / ((ωUpper : ℝ) - rightCandidate ωUpper ξ)) * ((ωUpper : ℝ) - rightCandidate ωUpper ξ)
          = 1 := by field_simp [hgap_ne]
      _ = (ξ - rightCandidate ωUpper ξ) * ((ωUpper : ℝ) - rightCandidate ωUpper ξ) := by
            simpa using hproduct.symm
  refine ⟨⟨hp_pos, hp_lt_upper⟩, ?_⟩
  -- Substitute the product identity in reciprocal form to recover the stationary equation.
  calc
    rightCandidate ωUpper ξ + 1 / ((ωUpper : ℝ) - rightCandidate ωUpper ξ)
        = rightCandidate ωUpper ξ + (ξ - rightCandidate ωUpper ξ) := by rw [hrecip]
    _ = ξ := by ring

/-- Helper for Example 24.41: the left quadratic candidate lies in `(ωLower, 0)` and solves the
negative stationary equation. -/
private theorem leftCandidate_mem_Ioo_and_stationary (ξ : ℝ)
    (hξ : ξ < (ωLower : ℝ)⁻¹) :
    leftCandidate ωLower ξ ∈ Set.Ioo (ωLower : ℝ) (0 : ℝ) ∧
      leftCandidate ωLower ξ - 1 / (leftCandidate ωLower ξ - (ωLower : ℝ)) = ξ := by
  let Δ : ℝ := Real.sqrt (|ξ - (ωLower : ℝ)| ^ (2 : ℕ) + 4)
  have hΔ_nonneg : 0 ≤ Δ := by
    simp [Δ]
  have hΔ_sq : Δ ^ (2 : ℕ) = (ξ - (ωLower : ℝ)) ^ (2 : ℕ) + 4 := by
    have hrad_nonneg : 0 ≤ |ξ - (ωLower : ℝ)| ^ (2 : ℕ) + 4 := by
      positivity
    simpa [Δ, sq_abs] using Real.sq_sqrt hrad_nonneg
  have hw_neg : (ωLower : ℝ) < 0 := ωLower.2
  have hw_ne : (ωLower : ℝ) ≠ 0 := ne_of_lt hw_neg
  have hw_inv_neg : (ωLower : ℝ)⁻¹ < 0 := by
    have hneg_pos : 0 < -((ωLower : ℝ)) := by
      linarith
    have hpos : 0 < (-(ωLower : ℝ))⁻¹ := inv_pos.mpr hneg_pos
    simpa [inv_neg] using hpos
  have hξ_neg : ξ < 0 := lt_trans hξ hw_inv_neg
  have hmul_gt : 1 < ξ * (ωLower : ℝ) := by
    have hmul := mul_lt_mul_of_neg_right hξ hw_neg
    simpa [hw_ne, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hsum_neg : ξ + (ωLower : ℝ) < 0 := by
    linarith
  have hΔ_lt_neg_sum : Δ < -(ξ + (ωLower : ℝ)) := by
    have hsq_lt : Δ ^ (2 : ℕ) < (-(ξ + (ωLower : ℝ))) ^ (2 : ℕ) := by
      nlinarith [hΔ_sq, hmul_gt]
    by_contra hnot
    have hsq_ge : (-(ξ + (ωLower : ℝ))) ^ (2 : ℕ) ≤ Δ ^ (2 : ℕ) := by
      nlinarith [le_of_not_gt hnot, hΔ_nonneg]
    linarith
  have habs_lt_Δ : |ξ - (ωLower : ℝ)| < Δ := by
    by_contra hnot
    have hsq_ge : Δ ^ (2 : ℕ) ≤ |ξ - (ωLower : ℝ)| ^ (2 : ℕ) := by
      nlinarith [le_of_not_gt hnot, abs_nonneg (ξ - (ωLower : ℝ)), hΔ_nonneg]
    rw [sq_abs] at hsq_ge
    nlinarith [hΔ_sq]
  have hneg_diff_lt_Δ : -((ξ - (ωLower : ℝ))) < Δ := by
    exact lt_of_le_of_lt (neg_le_abs (ξ - (ωLower : ℝ))) habs_lt_Δ
  have hcand : leftCandidate ωLower ξ = (ξ + (ωLower : ℝ) + Δ) / 2 := by
    simp [leftCandidate, Δ, sq_abs]
  have hlower_lt_p : (ωLower : ℝ) < leftCandidate ωLower ξ := by
    -- The square root dominates `ωLower - ξ`, so the printed root stays above `ωLower`.
    rw [hcand]
    nlinarith
  have hp_neg : leftCandidate ωLower ξ < 0 := by
    -- The threshold `ξ < ωLower⁻¹` gives `Δ < -(ξ + ωLower)`, hence the printed root is negative.
    rw [hcand]
    nlinarith
  have hgap_pos : 0 < leftCandidate ωLower ξ - (ωLower : ℝ) := sub_pos.mpr hlower_lt_p
  have hproduct :
      (leftCandidate ωLower ξ - ξ) * (leftCandidate ωLower ξ - (ωLower : ℝ)) = 1 := by
    -- Expanding the printed formula reduces the stationarity identity to the square-root equation.
    rw [hcand]
    field_simp
    nlinarith [hΔ_sq]
  have hrecip :
      1 / (leftCandidate ωLower ξ - (ωLower : ℝ)) = leftCandidate ωLower ξ - ξ := by
    have hgap_ne : leftCandidate ωLower ξ - (ωLower : ℝ) ≠ 0 := ne_of_gt hgap_pos
    apply mul_right_cancel₀ hgap_ne
    calc
      (1 / (leftCandidate ωLower ξ - (ωLower : ℝ))) *
          (leftCandidate ωLower ξ - (ωLower : ℝ))
          = 1 := by field_simp [hgap_ne]
      _ = (leftCandidate ωLower ξ - ξ) * (leftCandidate ωLower ξ - (ωLower : ℝ)) := by
            simpa using hproduct.symm
  refine ⟨⟨hlower_lt_p, hp_neg⟩, ?_⟩
  -- Substitute the reciprocal form of the product identity to recover the stationary equation.
  calc
    leftCandidate ωLower ξ - 1 / (leftCandidate ωLower ξ - (ωLower : ℝ))
        = leftCandidate ωLower ξ - (leftCandidate ωLower ξ - ξ) := by rw [hrecip]
    _ = ξ := by ring

/-- Helper for Example 24.41: on `[0, ωUpper)`, the right candidate minimizes the positive
branch seed in the upper regime. -/
private theorem rightCandidate_le_rightSeed_of_inv_upper_lt (ξ y : ℝ)
    (hξ : (ωUpper : ℝ)⁻¹ < ξ) (hy : y ∈ Set.Ico (0 : ℝ) (ωUpper : ℝ)) :
    rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ) ≤ rightProxSeed ωUpper ξ y := by
  rcases rightCandidate_mem_Ioo_and_stationary (ωUpper := ωUpper) ξ hξ with ⟨hp, hp_stationary⟩
  by_cases hpy : y = rightCandidate ωUpper ξ
  · -- Equal points give equality of seed values.
    simpa [hpy]
  · by_cases hlt : rightCandidate ωUpper ξ < y
    · have hcont : ContinuousOn (rightProxSeed ωUpper ξ) (Set.Icc (rightCandidate ωUpper ξ) y) := by
        intro z hz
        have hderivAt :
            HasDerivAt (rightProxSeed ωUpper ξ) (z - ξ + 1 / ((ωUpper : ℝ) - z)) z :=
          rightProxSeed_hasDerivAt (ωUpper := ωUpper) ξ z (lt_of_le_of_lt hz.2 hy.2)
        exact hderivAt.continuousAt.continuousWithinAt
      have hderiv :
          ∀ z ∈ Set.Ioo (rightCandidate ωUpper ξ) y, HasDerivAt (rightProxSeed ωUpper ξ)
            (z - ξ + 1 / ((ωUpper : ℝ) - z)) z := by
        intro z hz
        exact rightProxSeed_hasDerivAt (ωUpper := ωUpper) ξ z (lt_trans hz.2 hy.2)
      -- On the interval to the right of the stationary point, the derivative is positive.
      rcases
          exists_hasDerivAt_eq_slope
            (f := rightProxSeed ωUpper ξ)
            (f' := fun z ↦ z - ξ + 1 / ((ωUpper : ℝ) - z))
            hlt hcont hderiv with
        ⟨c, hc, hcSlope⟩
      have hmono := rightSeedSlope_strictMono (ωUpper := ωUpper) ξ
      have hcSlope_pos : 0 < c - ξ + 1 / ((ωUpper : ℝ) - c) := by
        have hcmp :
            rightCandidate ωUpper ξ - ξ + 1 / ((ωUpper : ℝ) - rightCandidate ωUpper ξ) <
              c - ξ + 1 / ((ωUpper : ℝ) - c) := by
          exact hmono hp.2 (lt_trans hc.2 hy.2) hc.1
        linarith
      have hslope_pos :
          0 <
            (rightProxSeed ωUpper ξ y - rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ)) /
              (y - rightCandidate ωUpper ξ) := by
        rw [← hcSlope]
        exact hcSlope_pos
      have hden_pos : 0 < y - rightCandidate ωUpper ξ := sub_pos.mpr hlt
      have hdiff_pos :
          0 < rightProxSeed ωUpper ξ y - rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ) := by
        by_contra hnonpos
        have hnonpos' :
            rightProxSeed ωUpper ξ y - rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ) ≤ 0 :=
          le_of_not_gt hnonpos
        have hquot_nonpos :
            (rightProxSeed ωUpper ξ y - rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ)) /
                (y - rightCandidate ωUpper ξ) ≤
              0 := by
          exact div_nonpos_of_nonpos_of_nonneg hnonpos' hden_pos.le
        linarith
      linarith
    · have hy_lt_p : y < rightCandidate ωUpper ξ := lt_of_le_of_ne (le_of_not_gt hlt) hpy
      have hcont : ContinuousOn (rightProxSeed ωUpper ξ) (Set.Icc y (rightCandidate ωUpper ξ)) := by
        intro z hz
        have hderivAt :
            HasDerivAt (rightProxSeed ωUpper ξ) (z - ξ + 1 / ((ωUpper : ℝ) - z)) z :=
          rightProxSeed_hasDerivAt (ωUpper := ωUpper) ξ z (lt_of_le_of_lt hz.2 hp.2)
        exact hderivAt.continuousAt.continuousWithinAt
      have hderiv :
          ∀ z ∈ Set.Ioo y (rightCandidate ωUpper ξ), HasDerivAt (rightProxSeed ωUpper ξ)
            (z - ξ + 1 / ((ωUpper : ℝ) - z)) z := by
        intro z hz
        exact rightProxSeed_hasDerivAt (ωUpper := ωUpper) ξ z (lt_trans hz.2 hp.2)
      -- On the interval to the left of the stationary point, the derivative is negative.
      rcases
          exists_hasDerivAt_eq_slope
            (f := rightProxSeed ωUpper ξ)
            (f' := fun z ↦ z - ξ + 1 / ((ωUpper : ℝ) - z))
            hy_lt_p hcont hderiv with
        ⟨c, hc, hcSlope⟩
      have hmono := rightSeedSlope_strictMono (ωUpper := ωUpper) ξ
      have hcSlope_neg : c - ξ + 1 / ((ωUpper : ℝ) - c) < 0 := by
        have hcmp :
            c - ξ + 1 / ((ωUpper : ℝ) - c) <
              rightCandidate ωUpper ξ - ξ + 1 / ((ωUpper : ℝ) - rightCandidate ωUpper ξ) := by
          exact hmono (lt_trans hc.2 hp.2) hp.2 hc.2
        linarith
      have hslope_neg :
          (rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ) - rightProxSeed ωUpper ξ y) /
              (rightCandidate ωUpper ξ - y) <
            0 := by
        rw [← hcSlope]
        exact hcSlope_neg
      have hden_pos : 0 < rightCandidate ωUpper ξ - y := sub_pos.mpr hy_lt_p
      have hdiff_neg :
          rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ) - rightProxSeed ωUpper ξ y < 0 := by
        by_contra hnonneg
        have hnonneg' :
            0 ≤ rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ) - rightProxSeed ωUpper ξ y :=
          le_of_not_gt hnonneg
        have hquot_nonneg :
            0 ≤
              (rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ) - rightProxSeed ωUpper ξ y) /
                (rightCandidate ωUpper ξ - y) := by
          exact div_nonneg hnonneg' hden_pos.le
        linarith
      linarith

/-- Helper for Example 24.41: on `(ωLower, 0]`, the left candidate minimizes the nonpositive
branch seed in the lower regime. -/
private theorem leftCandidate_le_leftSeed_of_lt_inv_lower (ξ y : ℝ)
    (hξ : ξ < (ωLower : ℝ)⁻¹) (hy : y ∈ Set.Ioc (ωLower : ℝ) (0 : ℝ)) :
    leftProxSeed ωLower ξ (leftCandidate ωLower ξ) ≤ leftProxSeed ωLower ξ y := by
  rcases leftCandidate_mem_Ioo_and_stationary (ωLower := ωLower) ξ hξ with ⟨hp, hp_stationary⟩
  by_cases hpy : y = leftCandidate ωLower ξ
  · -- Equal points give equality of seed values.
    simpa [hpy]
  · by_cases hlt : leftCandidate ωLower ξ < y
    · have hcont :
          ContinuousOn (leftProxSeed ωLower ξ) (Set.Icc (leftCandidate ωLower ξ) y) := by
        intro z hz
        have hderivAt :
            HasDerivAt (leftProxSeed ωLower ξ) (z - ξ - 1 / (z - (ωLower : ℝ))) z :=
          leftProxSeed_hasDerivAt (ωLower := ωLower) ξ z (lt_of_lt_of_le hp.1 hz.1)
        exact hderivAt.continuousAt.continuousWithinAt
      have hderiv :
          ∀ z ∈ Set.Ioo (leftCandidate ωLower ξ) y, HasDerivAt (leftProxSeed ωLower ξ)
            (z - ξ - 1 / (z - (ωLower : ℝ))) z := by
        intro z hz
        exact leftProxSeed_hasDerivAt (ωLower := ωLower) ξ z (lt_trans hp.1 hz.1)
      -- To the right of the stationary point, the derivative is positive.
      rcases
          exists_hasDerivAt_eq_slope
            (f := leftProxSeed ωLower ξ)
            (f' := fun z ↦ z - ξ - 1 / (z - (ωLower : ℝ)))
            hlt hcont hderiv with
        ⟨c, hc, hcSlope⟩
      have hmono := leftSeedSlope_strictMono (ωLower := ωLower) ξ
      have hcSlope_pos : 0 < c - ξ - 1 / (c - (ωLower : ℝ)) := by
        have hcmp :
            leftCandidate ωLower ξ - ξ - 1 / (leftCandidate ωLower ξ - (ωLower : ℝ)) <
              c - ξ - 1 / (c - (ωLower : ℝ)) := by
          exact hmono hp.1 (lt_trans hp.1 hc.1) hc.1
        linarith
      have hslope_pos :
          0 <
            (leftProxSeed ωLower ξ y - leftProxSeed ωLower ξ (leftCandidate ωLower ξ)) /
              (y - leftCandidate ωLower ξ) := by
        rw [← hcSlope]
        exact hcSlope_pos
      have hden_pos : 0 < y - leftCandidate ωLower ξ := sub_pos.mpr hlt
      have hdiff_pos :
          0 < leftProxSeed ωLower ξ y - leftProxSeed ωLower ξ (leftCandidate ωLower ξ) := by
        by_contra hnonpos
        have hnonpos' :
            leftProxSeed ωLower ξ y - leftProxSeed ωLower ξ (leftCandidate ωLower ξ) ≤ 0 :=
          le_of_not_gt hnonpos
        have hquot_nonpos :
            (leftProxSeed ωLower ξ y - leftProxSeed ωLower ξ (leftCandidate ωLower ξ)) /
                (y - leftCandidate ωLower ξ) ≤
              0 := by
          exact div_nonpos_of_nonpos_of_nonneg hnonpos' hden_pos.le
        linarith
      linarith
    · have hy_lt_p : y < leftCandidate ωLower ξ := lt_of_le_of_ne (le_of_not_gt hlt) hpy
      have hcont :
          ContinuousOn (leftProxSeed ωLower ξ) (Set.Icc y (leftCandidate ωLower ξ)) := by
        intro z hz
        have hderivAt :
            HasDerivAt (leftProxSeed ωLower ξ) (z - ξ - 1 / (z - (ωLower : ℝ))) z :=
          leftProxSeed_hasDerivAt (ωLower := ωLower) ξ z (lt_of_lt_of_le hy.1 hz.1)
        exact hderivAt.continuousAt.continuousWithinAt
      have hderiv :
          ∀ z ∈ Set.Ioo y (leftCandidate ωLower ξ), HasDerivAt (leftProxSeed ωLower ξ)
            (z - ξ - 1 / (z - (ωLower : ℝ))) z := by
        intro z hz
        exact leftProxSeed_hasDerivAt (ωLower := ωLower) ξ z (lt_trans hy.1 hz.1)
      -- To the left of the stationary point, the derivative is negative.
      rcases
          exists_hasDerivAt_eq_slope
            (f := leftProxSeed ωLower ξ)
            (f' := fun z ↦ z - ξ - 1 / (z - (ωLower : ℝ)))
            hy_lt_p hcont hderiv with
        ⟨c, hc, hcSlope⟩
      have hmono := leftSeedSlope_strictMono (ωLower := ωLower) ξ
      have hcSlope_neg : c - ξ - 1 / (c - (ωLower : ℝ)) < 0 := by
        have hcmp :
            c - ξ - 1 / (c - (ωLower : ℝ)) <
              leftCandidate ωLower ξ - ξ - 1 / (leftCandidate ωLower ξ - (ωLower : ℝ)) := by
          exact hmono (lt_trans hy.1 hc.1) hp.1 hc.2
        linarith
      have hslope_neg :
          (leftProxSeed ωLower ξ (leftCandidate ωLower ξ) - leftProxSeed ωLower ξ y) /
              (leftCandidate ωLower ξ - y) <
            0 := by
        rw [← hcSlope]
        exact hcSlope_neg
      have hden_pos : 0 < leftCandidate ωLower ξ - y := sub_pos.mpr hy_lt_p
      have hdiff_neg :
          leftProxSeed ωLower ξ (leftCandidate ωLower ξ) - leftProxSeed ωLower ξ y < 0 := by
        by_contra hnonneg
        have hnonneg' :
            0 ≤ leftProxSeed ωLower ξ (leftCandidate ωLower ξ) - leftProxSeed ωLower ξ y :=
          le_of_not_gt hnonneg
        have hquot_nonneg :
            0 ≤
              (leftProxSeed ωLower ξ (leftCandidate ωLower ξ) - leftProxSeed ωLower ξ y) /
                (leftCandidate ωLower ξ - y) := by
          exact div_nonneg hnonneg' hden_pos.le
        linarith
      linarith

/-- Helper for Example 24.41: `0` is a proximal point in the middle regime
`(ωLower : ℝ)⁻¹ ≤ ξ ≤ (ωUpper : ℝ)⁻¹`. -/
private theorem zero_isProxPoint_splitLogBarrier_of_inv_bounds (ξ : ℝ)
    (hξ_lower : (ωLower : ℝ)⁻¹ ≤ ξ) (hξ_upper : ξ ≤ (ωUpper : ℝ)⁻¹) :
    IsProxPoint (splitLogBarrier ωLower ωUpper) ξ 0 := by
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ) := ⟨ωLower.2, ωUpper.2⟩
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff]
  intro y
  by_cases hy : y ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ)
  · by_cases hy_nonpos : y ≤ 0
    · -- On the nonpositive branch, the left seed is minimized at `0`.
      rw [← leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ 0 hzero_mem le_rfl,
        ← leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ y hy hy_nonpos]
      exact_mod_cast
        leftSeed_zero_le_of_inv_lower_le (ωLower := ωLower) ξ y hξ_lower ⟨hy.1, hy_nonpos⟩
    · have hy_pos : 0 < y := lt_of_not_ge hy_nonpos
      rw [← leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ 0 hzero_mem le_rfl,
        ← rightProxSeed_eq_proximalObjective_of_mem_Ioo_pos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ y hy hy_pos]
      exact_mod_cast (by
        calc
          leftProxSeed ωLower ξ 0 = rightProxSeed ωUpper ξ 0 := by
            rw [branchSeeds_zero_eq (ωLower := ωLower) (ωUpper := ωUpper) ξ]
          _ ≤ rightProxSeed ωUpper ξ y :=
            rightSeed_zero_le_of_le_inv_upper (ωUpper := ωUpper) ξ y hξ_upper ⟨hy_pos.le, hy.2⟩)
  · -- Outside the effective domain, the regularized objective is `⊤`.
    have htop : proximalObjective (splitLogBarrier ωLower ωUpper) ξ y = ⊤ := by
      rw [proximalObjective, splitLogBarrier_apply_of_not_mem_Ioo hy, EReal.top_add_coe]
    rw [← leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos
        (ωLower := ωLower) (ωUpper := ωUpper) ξ 0 hzero_mem le_rfl, htop]
    exact le_top

/-- Helper for Example 24.41: the right quadratic candidate is a proximal point in the upper
regime `((ωUpper : ℝ)⁻¹ < ξ)`. -/
private theorem rightCandidate_isProxPoint_of_inv_upper_lt (ξ : ℝ)
    (hξ : (ωUpper : ℝ)⁻¹ < ξ) :
    IsProxPoint (splitLogBarrier ωLower ωUpper) ξ (rightCandidate ωUpper ξ) := by
  rcases rightCandidate_mem_Ioo_and_stationary (ωUpper := ωUpper) ξ hξ with ⟨hp, hp_stationary⟩
  have hp_mem : rightCandidate ωUpper ξ ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ) := by
    exact ⟨lt_trans ωLower.2 hp.1, hp.2⟩
  have hw_inv_neg : (ωLower : ℝ)⁻¹ < 0 := by
    have hw_lt_zero : (ωLower : ℝ) < 0 := by
      exact ωLower.2
    have hneg_pos : 0 < -((ωLower : ℝ)) := by
      simpa using neg_pos.mpr hw_lt_zero
    have hpos : 0 < (-(ωLower : ℝ))⁻¹ := inv_pos.mpr hneg_pos
    simpa [inv_neg] using hpos
  have hu_inv_pos : 0 < (ωUpper : ℝ)⁻¹ := inv_pos.mpr ωUpper.2
  have hξ_pos : 0 < ξ := lt_trans hu_inv_pos hξ
  have hξ_lower : (ωLower : ℝ)⁻¹ ≤ ξ := by
    linarith
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff]
  intro y
  by_cases hy : y ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ)
  · by_cases hy_nonpos : y ≤ 0
    · rw [← rightProxSeed_eq_proximalObjective_of_mem_Ioo_pos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ (rightCandidate ωUpper ξ) hp_mem hp.1,
        ← leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ y hy hy_nonpos]
      exact_mod_cast (by
        calc
          rightProxSeed ωUpper ξ (rightCandidate ωUpper ξ) ≤ rightProxSeed ωUpper ξ 0 :=
            rightCandidate_le_rightSeed_of_inv_upper_lt
              (ωUpper := ωUpper) ξ 0 hξ ⟨le_rfl, ωUpper.2⟩
          _ = leftProxSeed ωLower ξ 0 := by
            rw [← branchSeeds_zero_eq (ωLower := ωLower) (ωUpper := ωUpper) ξ]
          _ ≤ leftProxSeed ωLower ξ y :=
            leftSeed_zero_le_of_inv_lower_le (ωLower := ωLower) ξ y hξ_lower ⟨hy.1, hy_nonpos⟩)
    · have hy_pos : 0 < y := lt_of_not_ge hy_nonpos
      rw [← rightProxSeed_eq_proximalObjective_of_mem_Ioo_pos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ (rightCandidate ωUpper ξ) hp_mem hp.1,
        ← rightProxSeed_eq_proximalObjective_of_mem_Ioo_pos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ y hy hy_pos]
      exact_mod_cast
        rightCandidate_le_rightSeed_of_inv_upper_lt (ωUpper := ωUpper) ξ y hξ ⟨hy_pos.le, hy.2⟩
  · have htop :
        proximalObjective (splitLogBarrier ωLower ωUpper) ξ y = ⊤ := by
      rw [proximalObjective, splitLogBarrier_apply_of_not_mem_Ioo hy, EReal.top_add_coe]
    rw [← rightProxSeed_eq_proximalObjective_of_mem_Ioo_pos
      (ωLower := ωLower) (ωUpper := ωUpper) ξ (rightCandidate ωUpper ξ) hp_mem hp.1, htop]
    exact le_top

/-- Helper for Example 24.41: the left quadratic candidate is a proximal point in the lower
regime `(ξ < (ωLower : ℝ)⁻¹)`. -/
private theorem leftCandidate_isProxPoint_of_lt_inv_lower (ξ : ℝ)
    (hξ : ξ < (ωLower : ℝ)⁻¹) :
    IsProxPoint (splitLogBarrier ωLower ωUpper) ξ (leftCandidate ωLower ξ) := by
  rcases leftCandidate_mem_Ioo_and_stationary (ωLower := ωLower) ξ hξ with ⟨hp, hp_stationary⟩
  have hp_mem : leftCandidate ωLower ξ ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ) := by
    exact ⟨hp.1, lt_trans hp.2 ωUpper.2⟩
  have hw_inv_neg : (ωLower : ℝ)⁻¹ < 0 := by
    have hw_lt_zero : (ωLower : ℝ) < 0 := by
      exact ωLower.2
    have hneg_pos : 0 < -((ωLower : ℝ)) := by
      simpa using neg_pos.mpr hw_lt_zero
    have hpos : 0 < (-(ωLower : ℝ))⁻¹ := inv_pos.mpr hneg_pos
    simpa [inv_neg] using hpos
  have hu_inv_pos : 0 < (ωUpper : ℝ)⁻¹ := inv_pos.mpr ωUpper.2
  have hξ_neg : ξ < 0 := lt_trans hξ hw_inv_neg
  have hξ_upper : ξ ≤ (ωUpper : ℝ)⁻¹ := by
    linarith
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff]
  intro y
  by_cases hy : y ∈ Set.Ioo (ωLower : ℝ) (ωUpper : ℝ)
  · by_cases hy_nonpos : y ≤ 0
    · rw [← leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ (leftCandidate ωLower ξ) hp_mem hp.2.le,
        ← leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ y hy hy_nonpos]
      exact_mod_cast
        leftCandidate_le_leftSeed_of_lt_inv_lower (ωLower := ωLower) ξ y hξ ⟨hy.1, hy_nonpos⟩
    · have hy_pos : 0 < y := lt_of_not_ge hy_nonpos
      rw [← leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ (leftCandidate ωLower ξ) hp_mem hp.2.le,
        ← rightProxSeed_eq_proximalObjective_of_mem_Ioo_pos
          (ωLower := ωLower) (ωUpper := ωUpper) ξ y hy hy_pos]
      exact_mod_cast (by
        calc
          leftProxSeed ωLower ξ (leftCandidate ωLower ξ) ≤ leftProxSeed ωLower ξ 0 :=
            leftCandidate_le_leftSeed_of_lt_inv_lower
              (ωLower := ωLower) ξ 0 hξ ⟨ωLower.2, le_rfl⟩
          _ = rightProxSeed ωUpper ξ 0 := by
            rw [branchSeeds_zero_eq (ωLower := ωLower) (ωUpper := ωUpper) ξ]
          _ ≤ rightProxSeed ωUpper ξ y :=
            rightSeed_zero_le_of_le_inv_upper (ωUpper := ωUpper) ξ y hξ_upper ⟨hy_pos.le, hy.2⟩)
  · rw [← leftProxSeed_eq_proximalObjective_of_mem_Ioo_nonpos
      (ωLower := ωLower) (ωUpper := ωUpper) ξ (leftCandidate ωLower ξ) hp_mem hp.2.le]
    have htop :
        proximalObjective (splitLogBarrier ωLower ωUpper) ξ y = ⊤ := by
      rw [proximalObjective, splitLogBarrier_apply_of_not_mem_Ioo hy, EReal.top_add_coe]
    rw [htop]
    exact le_top

/-- Example 24.41: if `ωLower ∈ ℝ_{--}` and `ωUpper ∈ ℝ_{++}`, then any chosen proximity operator
of the split logarithmic barrier is given by the textbook piecewise formula. -/
theorem prox_splitLogBarrier_eq_piecewise
    (hprox : HasUniqueProxPoint (splitLogBarrier ωLower ωUpper)) :
    proximityOperator (splitLogBarrier ωLower ωUpper) hprox =
      fun ξ : ℝ ↦
        if ξ < (ωLower : ℝ)⁻¹ then
          (ξ + (ωLower : ℝ) +
            Real.sqrt (|ξ - (ωLower : ℝ)| ^ (2 : ℕ) + 4)) / 2
        else if (ωUpper : ℝ)⁻¹ < ξ then
          (ξ + (ωUpper : ℝ) -
            Real.sqrt (|ξ - (ωUpper : ℝ)| ^ (2 : ℕ) + 4)) / 2
        else
          0 := by
  funext ξ
  by_cases hleft : ξ < (ωLower : ℝ)⁻¹
  · -- The left quadratic root is a proximal point in the lower regime.
    have hproxPoint :
        IsProxPoint (splitLogBarrier ωLower ωUpper) ξ (leftCandidate ωLower ξ) :=
      leftCandidate_isProxPoint_of_lt_inv_lower (ωLower := ωLower) (ωUpper := ωUpper) ξ hleft
    have hEq :=
      eq_proximityOperator_of_isProxPoint
        (splitLogBarrier ωLower ωUpper) hprox hproxPoint
    simp [leftCandidate, hleft, hEq.symm]
  · by_cases hright : (ωUpper : ℝ)⁻¹ < ξ
    · -- The right quadratic root is a proximal point in the upper regime.
      have hproxPoint :
          IsProxPoint (splitLogBarrier ωLower ωUpper) ξ (rightCandidate ωUpper ξ) :=
        rightCandidate_isProxPoint_of_inv_upper_lt
          (ωLower := ωLower) (ωUpper := ωUpper) ξ hright
      have hEq :=
        eq_proximityOperator_of_isProxPoint
          (splitLogBarrier ωLower ωUpper) hprox hproxPoint
      simp [rightCandidate, hleft, hright, hEq.symm]
    · -- In the middle regime, `0` is a proximal point, so uniqueness picks it.
      have hmiddleLower : (ωLower : ℝ)⁻¹ ≤ ξ := le_of_not_gt hleft
      have hmiddleUpper : ξ ≤ (ωUpper : ℝ)⁻¹ := le_of_not_gt hright
      have hproxPoint :
          IsProxPoint (splitLogBarrier ωLower ωUpper) ξ 0 :=
        zero_isProxPoint_splitLogBarrier_of_inv_bounds
          (ωLower := ωLower) (ωUpper := ωUpper) ξ hmiddleLower hmiddleUpper
      have hEq :=
        eq_proximityOperator_of_isProxPoint
          (splitLogBarrier ωLower ωUpper) hprox hproxPoint
      simp [hleft, hright, hEq.symm]

end ERealFunction
