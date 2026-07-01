import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this item lives in the locally uniform convergence API for complex function
-- series on an open set. The owner abstractions are `SummableLocallyUniformlyOn`,
-- `SummableUniformlyOn`, and `HasSumUniformlyOn`. The primitive source-facing datum is the series
-- `n ↦ fun z ↦ f (z ^ (n + 1))` on the open unit disc; compact-uniform convergence and the chosen
-- tsum target are derived API.

open Metric

/-- Helper for Exercise 1: a compact subset of the unit disc is contained in a strictly smaller
closed disc centered at the origin. -/
private theorem compact_subset_closedBall_radius_lt_one {K : Set ℂ}
    (hK : IsCompact K) (hK_unit : K ⊆ ball (0 : ℂ) 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ K ⊆ closedBall (0 : ℂ) ρ := by
  rcases Set.eq_empty_or_nonempty K with rfl | hK_nonempty
  · -- The empty compact set is contained in every closed disc, so radius `0` is enough.
    exact ⟨0, le_rfl, zero_lt_one, Set.empty_subset _⟩
  · -- On a nonempty compact set, the norm attains a maximum; that maximum is still `< 1`.
    obtain ⟨w, hwK, hwmax⟩ := hK.exists_isMaxOn hK_nonempty continuous_norm.continuousOn
    refine ⟨‖w‖, norm_nonneg _, mem_ball_zero_iff.mp (hK_unit hwK), ?_⟩
    intro z hz
    rw [mem_closedBall_zero_iff]
    exact (isMaxOn_iff.mp hwmax) z hz

/-- Helper for Exercise 1: if `‖z‖ ≤ ρ < 1`, then every positive power of `z` stays in any larger
disc of radius `r > ρ`. -/
private theorem pow_succ_mem_ball_of_mem_closedBall_lt_one {ρ r : ℝ} {z : ℂ} {n : ℕ}
    (hz : z ∈ closedBall (0 : ℂ) ρ) (_hρ_nonneg : 0 ≤ ρ) (hρ_lt_one : ρ < 1) (hρ_lt_r : ρ < r) :
    z ^ (n + 1) ∈ ball (0 : ℂ) r := by
  -- Powers cannot increase the norm once the base lies in the closed unit disc.
  rw [mem_ball_zero_iff]
  have hzρ : ‖z‖ ≤ ρ := by
    simpa [mem_closedBall_zero_iff] using hz
  have hz_le_one : ‖z‖ ≤ 1 := hzρ.trans hρ_lt_one.le
  calc
    ‖z ^ (n + 1)‖ = ‖z‖ ^ (n + 1) := by rw [norm_pow]
    _ ≤ ‖z‖ ^ (1 : ℕ) := by
      exact pow_le_pow_of_le_one (norm_nonneg _) hz_le_one (Nat.succ_le_succ (Nat.zero_le n))
    _ = ‖z‖ := by simp
    _ ≤ ρ := hzρ
    _ < r := hρ_lt_r

/-- Helper for Exercise 1: Schwarz's lemma on a slightly larger disc yields a geometric majorant for
the terms `f (z^(n+1))` on the closed disc of radius `ρ < 1`. -/
private theorem exists_geometric_majorant_for_iterated_powers {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hf0 : f 0 = 0) {ρ : ℝ} (hρ_nonneg : 0 ≤ ρ) (hρ_lt_one : ρ < 1) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n z, z ∈ closedBall (0 : ℂ) ρ → ‖f (z ^ (n + 1))‖ ≤ u n := by
  let r : ℝ := (ρ + 1) / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    nlinarith
  have hρ_lt_r : ρ < r := by
    dsimp [r]
    nlinarith
  have hr_lt_one : r < 1 := by
    dsimp [r]
    nlinarith
  -- First bound `f` on the closed ball of radius `r`.
  have hcont : ContinuousOn f (closedBall (0 : ℂ) r) := by
    exact hf.continuousOn.mono (closedBall_subset_ball hr_lt_one)
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn (f := f) hcont
  let C : ℝ := max M 0
  have hC_nonneg : 0 ≤ C := le_max_right _ _
  have hC_bound : ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ C := by
    intro z hz
    exact (hM z hz).trans (le_max_left _ _)
  -- Then Schwarz on `ball 0 r` turns that uniform bound into a linear estimate.
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) r) := by
    exact hf.differentiableOn.mono (ball_subset_ball hr_lt_one.le)
  have hmaps : Set.MapsTo f (ball (0 : ℂ) r) (closedBall (f 0) C) := by
    intro z hz
    rw [hf0, mem_closedBall_zero_iff]
    exact hC_bound z (ball_subset_closedBall hz)
  have hschwarz : ∀ w, w ∈ ball (0 : ℂ) r → ‖f w‖ ≤ (C / r) * ‖w‖ := by
    intro w hw
    simpa [hf0, dist_eq_norm] using
      Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps hw
  -- Finally, evaluate the linear bound at `z^(n+1)` and dominate it by a geometric series.
  have hgeom : Summable (fun n : ℕ ↦ (((C / r) * ρ) * ρ ^ n)) := by
    exact (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left ((C / r) * ρ)
  refine ⟨fun n ↦ ((C / r) * ρ) * ρ ^ n, hgeom, ?_⟩
  intro n z hz
  have hzpow_mem : z ^ (n + 1) ∈ ball (0 : ℂ) r := by
    exact pow_succ_mem_ball_of_mem_closedBall_lt_one hz hρ_nonneg hρ_lt_one hρ_lt_r
  have hzρ : ‖z‖ ≤ ρ := by
    simpa [mem_closedBall_zero_iff] using hz
  have hpow : ‖z ^ (n + 1)‖ ≤ ρ ^ (n + 1) := by
    calc
      ‖z ^ (n + 1)‖ = ‖z‖ ^ (n + 1) := by rw [norm_pow]
      _ ≤ ρ ^ (n + 1) := by
        exact pow_le_pow_left₀ (norm_nonneg _) hzρ _
  have hCr_nonneg : 0 ≤ C / r := div_nonneg hC_nonneg hr_pos.le
  calc
    ‖f (z ^ (n + 1))‖ ≤ (C / r) * ‖z ^ (n + 1)‖ := hschwarz _ hzpow_mem
    _ ≤ (C / r) * (ρ ^ (n + 1)) := mul_le_mul_of_nonneg_left hpow hCr_nonneg
    _ = ((C / r) * ρ) * ρ ^ n := by
      rw [pow_succ]
      ring

/-- Exercise 1: if `f` is holomorphic on the unit disc and `f 0 = 0`, then the series
`∑_{n ≥ 1} f (z^n)` converges locally uniformly on the unit disc, i.e. uniformly on every compact
subset of that disc. -/
theorem exercise_1_summableLocallyUniformlyOn_unitDisc
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hf0 : f 0 = 0) :
    SummableLocallyUniformlyOn
      (fun n z ↦ f (z ^ (n + 1)))
      (ball (0 : ℂ) 1) := by
  -- Apply the local M-test on each compact subset of the unit disc.
  apply SummableLocallyUniformlyOn_of_locally_bounded Metric.isOpen_ball
  intro K hK_unit hK
  -- Compactness lets us shrink from the open unit disc to a closed disc of radius `ρ < 1`.
  obtain ⟨ρ, hρ_nonneg, hρ_lt_one, hKρ⟩ := compact_subset_closedBall_radius_lt_one hK hK_unit
  -- Schwarz on a slightly larger disc produces the geometric majorant needed for summability.
  obtain ⟨u, hu, hubound⟩ :=
    exists_geometric_majorant_for_iterated_powers hf hf0 hρ_nonneg hρ_lt_one
  refine ⟨u, hu, ?_⟩
  intro n z hz
  exact hubound n z (hKρ hz)

/-- Exercise 1: on every compact subset of the unit disc, the series `∑_{n ≥ 1} f (z^n)`
converges uniformly. -/
theorem exercise_1_summableUniformlyOn_compact_unitDisc
    {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hf0 : f 0 = 0)
    (hK : IsCompact K)
    (hK_unit : K ⊆ ball (0 : ℂ) 1) :
    SummableUniformlyOn
      (fun n z ↦ f (z ^ (n + 1)))
      K := by
  let hlocalK :
      SummableLocallyUniformlyOn (fun n z ↦ f (z ^ (n + 1))) K :=
    (exercise_1_summableLocallyUniformlyOn_unitDisc hf hf0).mono hK_unit
  have hhasLocal :
      HasSumLocallyUniformlyOn
        (fun n z ↦ f (z ^ (n + 1)))
        (fun z ↦ ∑' n : ℕ, f (z ^ (n + 1)))
        K :=
    hlocalK.hasSumLocallyUniformlyOn
  have hhas :
      HasSumUniformlyOn
        (fun n z ↦ f (z ^ (n + 1)))
        (fun z ↦ ∑' n : ℕ, f (z ^ (n + 1)))
        K := by
    rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
    rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hhasLocal
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp hhasLocal
  exact hhas.summableUniformlyOn

/-- Exercise 1: on every compact subset of the unit disc, the series `∑_{n ≥ 1} f (z^n)`
has the canonical uniform sum `z ↦ ∑' n, f (z ^ (n + 1))`. -/
theorem exercise_1_hasSumUniformlyOn_compact_unitDisc
    {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hf0 : f 0 = 0)
    (hK : IsCompact K)
    (hK_unit : K ⊆ ball (0 : ℂ) 1) :
    HasSumUniformlyOn
      (fun n z ↦ f (z ^ (n + 1)))
      (fun z ↦ ∑' n : ℕ, f (z ^ (n + 1)))
      K := by
  exact (exercise_1_summableUniformlyOn_compact_unitDisc hf hf0 hK hK_unit).hasSumUniformlyOn
