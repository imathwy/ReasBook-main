import Mathlib

-- Domain sampling note: this item lives in one-variable complex analysis. The canonical owner
-- abstractions already present in the chapter/project are the Rouché theorem
-- `rouche_theorem_on_oriented_boundary`, together with Mathlib's `MeromorphicOn.divisor` API and
-- its basic divisor owners such as `divisor_pow` and `divisor_sub_const_self`. The source-facing
-- statement below therefore stays a direct divisor count, without introducing any parallel local
-- zero-count wrapper.

-- Declarations for this item will be appended below by the statement pipeline.

open MeromorphicOn Metric
open scoped BigOperators

noncomputable section

/-- Helper for Example III.6-extra-8: Rouché on the closed unit disc identifies the divisor sums
of `z^n - f z` and `z^n` under the strict unit-circle domination hypothesis. -/
lemma rouche_on_closed_unit_disc
    {f : ℂ → ℂ} {n : ℕ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ < 1) :
    ∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n - f z) (closedBall (0 : ℂ) 1) z =
      ∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n) (closedBall (0 : ℂ) 1) z := by
  have hpow :
      AnalyticOnNhd ℂ (fun z : ℂ ↦ z ^ n) (closedBall (0 : ℂ) 1) :=
    analyticOnNhd_id.pow n
  have hneg :
      AnalyticOnNhd ℂ (fun z : ℂ ↦ -f z) (closedBall (0 : ℂ) 1) :=
    hf.neg
  have hboundary_frontier :
      ∀ z ∈ frontier (closedBall (0 : ℂ) 1), ‖(-f z)‖ < ‖z ^ n‖ := by
    intro z hz
    -- On the frontier of the unit closed disc, the boundary hypothesis is exactly the unit-circle
    -- estimate, and `‖z ^ n‖ = 1`.
    have hz_sphere : z ∈ sphere (0 : ℂ) 1 := by
      simpa [frontier_closedBall (0 : ℂ) one_ne_zero] using hz
    have hnorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz_sphere
    calc
      ‖(-f z)‖ = ‖f z‖ := by simp
      _ < 1 := hboundary z hz_sphere
      _ = ‖z‖ ^ n := by rw [hnorm, one_pow]
      _ = ‖z ^ n‖ := by rw [norm_pow]
  have hrouche :
      ∑ᶠ z,
          divisor ((fun z : ℂ ↦ z ^ n) + (fun z : ℂ ↦ -f z))
            (closedBall (0 : ℂ) 1) z =
        ∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n) (closedBall (0 : ℂ) 1) z := by
    -- TODO: apply the missing importable theorem
    -- `rouche_theorem_on_oriented_boundary` to the singleton family
    -- `fun _ : Unit ↦ (standardCirclePath (1 : NNReal)).toClosedPath`. The remaining blocker is
    -- structural: this item cannot import `III/section12/0031_Exercise_19.lean`, and no exposed
    -- earlier theorem currently provides either that Rouché statement or the canonical witness
    -- `IsOrientedBoundaryOf (closedBall (0 : ℂ) 1) ...` for the standard unit circle.
    sorry
  -- The remaining step is only the algebraic rewrite from `f₀ + g₀` back to `z^n - f z`.
  simpa [sub_eq_add_neg] using hrouche

/-- Helper for Example III.6-extra-8: a point on the unit circle has `n`th power of norm `1`. -/
lemma unit_circle_pow_norm_eq_one {z : ℂ} {n : ℕ}
    (hz : z ∈ sphere (0 : ℂ) 1) :
    ‖z ^ n‖ = 1 := by
  -- On the unit circle, multiplicativity of the norm reduces the power to `1 ^ n`.
  have hnorm : ‖z‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  rw [norm_pow, hnorm, one_pow]

/-- Helper for Example III.6-extra-8: a point on the unit circle has nonzero `n`th power. -/
lemma unit_circle_pow_ne_zero {z : ℂ} {n : ℕ}
    (hz : z ∈ sphere (0 : ℂ) 1) :
    z ^ n ≠ 0 := by
  -- The previous norm computation excludes vanishing on the boundary.
  intro hzero
  have hnorm : (1 : ℝ) = 0 := by
    simpa [hzero] using unit_circle_pow_norm_eq_one (n := n) hz
  norm_num at hnorm

/-- Helper for Example III.6-extra-8: on the unit circle the function `z^n - f z` does not
vanish under the strict boundary estimate `‖f z‖ < 1`. -/
lemma boundary_pow_sub_ne_zero
    {f : ℂ → ℂ} {n : ℕ}
    (hboundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ < 1)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    z ^ n - f z ≠ 0 := by
  -- A boundary zero would force `‖f z‖ = ‖z^n‖ = 1`, contradicting the hypothesis.
  intro hzero
  have hEq : f z = z ^ n := by
    exact sub_eq_zero.mp hzero |>.symm
  have hlt : ‖f z‖ < 1 := hboundary z hz
  have hnorm : ‖f z‖ = 1 := by
    calc
      ‖f z‖ = ‖z ^ n‖ := by rw [hEq]
      _ = 1 := unit_circle_pow_norm_eq_one (n := n) hz
  rw [hnorm] at hlt
  exact lt_irrefl _ hlt

/-- Helper for Example III.6-extra-8: on the unit circle the function `f z - z^n` does not
vanish under the same strict boundary estimate. -/
lemma boundary_sub_pow_ne_zero
    {f : ℂ → ℂ} {n : ℕ}
    (hboundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ < 1)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    f z - z ^ n ≠ 0 := by
  -- Rewrite as the negative of `z^n - f z`, which has already been shown nonvanishing.
  have hne : z ^ n - f z ≠ 0 := boundary_pow_sub_ne_zero (n := n) hboundary hz
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using neg_ne_zero.mpr hne

/-- Helper for Example III.6-extra-8: negating a meromorphic function does not change its divisor. -/
lemma divisor_neg_eq {U : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicOn g U) :
    divisor (fun z ↦ -g z) U = divisor g U := by
  -- Compare the two divisors pointwise via the equality of meromorphic orders under negation.
  ext z
  by_cases hz : z ∈ U
  · have hleft :
        divisor (fun z ↦ -g z) U z = (meromorphicOrderAt (fun z ↦ -g z) z).untop₀ := by
        simpa using
          (MeromorphicOn.divisor_apply (f := fun z ↦ -g z) (U := U) (z := z) hg.neg hz)
    have hright :
        divisor g U z = (meromorphicOrderAt g z).untop₀ := by
        simpa using (MeromorphicOn.divisor_apply (f := g) (U := U) (z := z) hg hz)
    rw [hleft, hright]
    exact congrArg WithTop.untop₀ (meromorphicOrderAt_fun_neg (f := g) (x := z)).symm
  · simp [hz]

/-- Helper for Example III.6-extra-8: an analytic function on the closed unit disc whose boundary
values are nonzero has the same divisor on the closed and open unit discs. -/
lemma divisor_closedBall_eq_ball_of_boundary_nonzero
    {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) 1))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) 1, g z ≠ 0) :
    ∀ z : ℂ,
      divisor g (closedBall (0 : ℂ) 1) z = divisor g (ball (0 : ℂ) 1) z := by
  intro z
  by_cases hz_ball : z ∈ ball (0 : ℂ) 1
  · -- Inside the open disc, the divisor is exactly the restriction of the closed-disc divisor.
    have hrestrict :=
      congrArg (fun D : Function.locallyFinsuppWithin (ball (0 : ℂ) 1) ℤ ↦ D z)
        (MeromorphicOn.divisor_restrict
          (U := closedBall (0 : ℂ) 1) (V := ball (0 : ℂ) 1) hg.meromorphicOn
          (by
            intro w hw
            exact Metric.ball_subset_closedBall hw))
    simpa [Function.locallyFinsuppWithin.restrict_apply, hz_ball] using hrestrict
  · by_cases hz_closed : z ∈ closedBall (0 : ℂ) 1
    · -- On the boundary sphere, the closed-disc divisor vanishes because the function is nonzero.
      have hz_sphere : z ∈ sphere (0 : ℂ) 1 := by
        have hle : ‖z‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz_closed
        have hge : 1 ≤ ‖z‖ := by
          have hnotlt : ¬ ‖z‖ < 1 := by
            simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
          exact le_of_not_gt hnotlt
        simpa [Metric.mem_sphere, dist_eq_norm] using le_antisymm hle hge
      have hdiv_closed : divisor g (closedBall (0 : ℂ) 1) z = 0 := by
        -- Analyticity turns the divisor into the analytic order, which is zero at nonvanishing points.
        rw [hg.divisor_apply hz_closed, (hg z hz_closed).analyticOrderAt_eq_zero.mpr (hboundary z hz_sphere)]
        simp
      have hdiv_ball : divisor g (ball (0 : ℂ) 1) z = 0 := by
        exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz_ball
      rw [hdiv_closed, hdiv_ball]
    · -- Outside the closed disc, both divisors vanish because their domains no longer contain `z`.
      have hz_ball' : z ∉ ball (0 : ℂ) 1 := by
        intro hz
        exact hz_closed (Metric.ball_subset_closedBall hz)
      simp [hz_closed, hz_ball']

/-- Helper for Example III.6-extra-8: the divisor of `f z - z^n` is unchanged when the unit-disc
domain is enlarged from the open to the closed disc. -/
lemma divisor_sub_pow_closedBall_eq_ball
    {f : ℂ → ℂ} {n : ℕ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ < 1) :
    ∀ z : ℂ,
      divisor (fun z : ℂ ↦ f z - z ^ n) (closedBall (0 : ℂ) 1) z =
        divisor (fun z : ℂ ↦ f z - z ^ n) (ball (0 : ℂ) 1) z := by
  -- The general closedBall-to-ball bridge applies because `f z - z^n` stays nonzero on the boundary.
  have hsub :
      AnalyticOnNhd ℂ (fun z : ℂ ↦ f z - z ^ n) (closedBall (0 : ℂ) 1) :=
    hf.sub (analyticOnNhd_id.pow n)
  exact divisor_closedBall_eq_ball_of_boundary_nonzero hsub
    (fun z hz ↦ boundary_sub_pow_ne_zero (n := n) hboundary hz)

/-- Helper for Example III.6-extra-8: the divisor of `z^n` is unchanged when the unit-disc domain
is enlarged from the open to the closed disc. -/
lemma divisor_pow_closedBall_eq_ball
    {n : ℕ} :
    ∀ z : ℂ,
      divisor (fun z : ℂ ↦ z ^ n) (closedBall (0 : ℂ) 1) z =
        divisor (fun z : ℂ ↦ z ^ n) (ball (0 : ℂ) 1) z := by
  -- Boundary points never annihilate `z^n`, so the same bridge applies to the model function.
  exact divisor_closedBall_eq_ball_of_boundary_nonzero
    (analyticOnNhd_id.pow n)
    (fun z hz ↦ unit_circle_pow_ne_zero (n := n) hz)

/-- Helper for Example III.6-extra-8: the model equation `z^n = 0` contributes total divisor sum
`n` on the open unit disc. -/
lemma pow_divisor_sum_unit_ball
    (n : ℕ) :
    ∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n) (ball (0 : ℂ) 1) z = (n : ℤ) := by
  -- Rewrite the divisor of `z^n` as the `n`-fold scalar multiple of the divisor of `z`.
  have hpow :
      divisor (fun z : ℂ ↦ z ^ n) (ball (0 : ℂ) 1) =
        n • divisor (fun z : ℂ ↦ z) (ball (0 : ℂ) 1) := by
    simpa using
      (MeromorphicOn.divisor_fun_pow
        (U := ball (0 : ℂ) 1) (f := fun z : ℂ ↦ z) analyticOnNhd_id.meromorphicOn n)
  rw [show (∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n) (ball (0 : ℂ) 1) z) =
      ∑ᶠ z, (n • divisor (fun z : ℂ ↦ z) (ball (0 : ℂ) 1) z) by
      simpa [hpow]]
  -- Only the origin contributes, with multiplicity `1` for `z` and hence `n` for `z^n`.
  rw [finsum_eq_single (fun z : ℂ ↦ n • divisor (fun z : ℂ ↦ z) (ball (0 : ℂ) 1) z) 0]
  · have hzero_mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_eq_norm]
    have hdiv_zero : divisor (fun z : ℂ ↦ z) (ball (0 : ℂ) 1) 0 = 1 := by
      simpa using
        (MeromorphicOn.divisor_sub_const_self
          (U := ball (0 : ℂ) 1) (z₀ := (0 : ℂ)) hzero_mem)
    rw [hdiv_zero]
    norm_num
  · intro z hz
    have hdiv_ne : divisor (fun z : ℂ ↦ z) (ball (0 : ℂ) 1) z = 0 := by
      simpa using
        (MeromorphicOn.divisor_sub_const_of_ne
          (U := ball (0 : ℂ) 1) (z₀ := (0 : ℂ)) (x := z) hz)
    rw [hdiv_ne]
    simp

/-- Example III.6-extra-8: if `f` is analytic on a neighborhood of the closed unit disc and
`‖f z‖ < 1` on the unit circle, then the equation `f z = z ^ n` has total multiplicity `n` in the
open unit disc. -/
theorem unit_disc_eq_pow_divisor_sum
    {f : ℂ → ℂ} {n : ℕ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ < 1) :
    ∑ᶠ z, divisor (fun z : ℂ ↦ f z - z ^ n) (ball (0 : ℂ) 1) z = (n : ℤ) := by
  -- Route correction: run Rouché on `z^n - f z` over the closed disc, then transfer the divisor
  -- count to `f z - z^n` and finally restrict from `closedBall` to `ball`.
  have hpow_sub :
      AnalyticOnNhd ℂ (fun z : ℂ ↦ z ^ n - f z) (closedBall (0 : ℂ) 1) :=
    (analyticOnNhd_id.pow n).sub hf
  have hrouche_closed :
      ∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n - f z) (closedBall (0 : ℂ) 1) z =
        ∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n) (closedBall (0 : ℂ) 1) z :=
    rouche_on_closed_unit_disc hf hboundary
  have hneg_closed :
      divisor (fun z : ℂ ↦ f z - z ^ n) (closedBall (0 : ℂ) 1) =
        divisor (fun z : ℂ ↦ z ^ n - f z) (closedBall (0 : ℂ) 1) := by
    -- Negation does not change the divisor, and `f z - z^n` is the negative of `z^n - f z`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (divisor_neg_eq (U := closedBall (0 : ℂ) 1) hpow_sub.meromorphicOn)
  have hsub_ball :
      (fun z : ℂ ↦ divisor (fun z : ℂ ↦ f z - z ^ n) (closedBall (0 : ℂ) 1) z) =
        fun z : ℂ ↦ divisor (fun z : ℂ ↦ f z - z ^ n) (ball (0 : ℂ) 1) z :=
    funext (divisor_sub_pow_closedBall_eq_ball hf hboundary)
  have hpow_ball :
      (fun z : ℂ ↦ divisor (fun z : ℂ ↦ z ^ n) (closedBall (0 : ℂ) 1) z) =
        fun z : ℂ ↦ divisor (fun z : ℂ ↦ z ^ n) (ball (0 : ℂ) 1) z :=
    funext (divisor_pow_closedBall_eq_ball (n := n))
  -- Assemble the closed-disc Rouché count with the two restriction bridges and the model sum.
  calc
    ∑ᶠ z, divisor (fun z : ℂ ↦ f z - z ^ n) (ball (0 : ℂ) 1) z
        = ∑ᶠ z, divisor (fun z : ℂ ↦ f z - z ^ n) (closedBall (0 : ℂ) 1) z := by
            simpa using congrArg (fun D : ℂ → ℤ ↦ ∑ᶠ z, D z) hsub_ball.symm
    _ = ∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n - f z) (closedBall (0 : ℂ) 1) z := by
          simpa using congrArg (fun D : Function.locallyFinsuppWithin (closedBall (0 : ℂ) 1) ℤ ↦
            ∑ᶠ z, D z) hneg_closed
    _ = ∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n) (closedBall (0 : ℂ) 1) z := hrouche_closed
    _ = ∑ᶠ z, divisor (fun z : ℂ ↦ z ^ n) (ball (0 : ℂ) 1) z := by
          simpa using congrArg (fun D : ℂ → ℤ ↦ ∑ᶠ z, D z) hpow_ball
    _ = (n : ℤ) := pow_divisor_sum_unit_ball n
