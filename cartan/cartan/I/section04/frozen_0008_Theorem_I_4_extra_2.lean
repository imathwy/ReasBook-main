import Mathlib
import cartan.I.section04.«0004_Proposition_2_2»
import cartan.I.section04.«frozen_0006_Remark_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal NNReal
open Filter

variable {D : Set ℝ} {f : ℝ → ℝ}

/-- Helper for Theorem I.4-extra-2: on the unordered interval `uIcc x₀ x`, the Taylor polynomial
centered at `x₀` rewrites using the ordinary iterated derivatives at `x₀`. -/
lemma taylorWithinEval_uIcc_eq_finset_sum_iteratedDeriv
    {x₀ x : ℝ} (hfx₀ : ContDiffAt ℝ ⊤ f x₀) (n : ℕ) :
    taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
      ∑ k ∈ Finset.range (n + 1),
        (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k := by
  by_cases hxx₀ : x = x₀
  · -- At the center, the Taylor polynomial collapses to the constant term.
    subst hxx₀
    rw [taylorWithinEval_self]
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp
  · -- Away from the center, the unordered interval is a genuine interval.
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hu : UniqueDiffOn ℝ (Set.uIcc x₀ x) := by
      by_cases hlt : x₀ < x
      · simpa [Set.uIcc, min_eq_left hlt.le, max_eq_right hlt.le] using uniqueDiffOn_Icc hlt
      · have hgt : x < x₀ := by
          refine lt_of_not_ge ?_
          intro hx₀x
          exact hxx₀ (le_antisymm (not_lt.mp hlt) hx₀x)
        simpa [Set.uIcc, min_eq_right hgt.le, max_eq_left hgt.le] using uniqueDiffOn_Icc hgt
    have hwithin :
        iteratedDerivWithin k f (Set.uIcc x₀ x) x₀ = iteratedDeriv k f x₀ := by
      simpa using iteratedDerivWithin_eq_iteratedDeriv hu (hfx₀.of_le (by simp))
    -- The remaining step is scalar-algebra normalization.
    rw [hwithin]
    ring_nf

/-- Helper for Theorem I.4-extra-2: a local geometric derivative bound should control the
Lagrange remainder of the Taylor polynomial. -/
lemma lagrange_remainder_le_geometric_pow
    {x₀ r M t : ℝ} (hr : 0 < r) (hM : 0 < M) (ht : 0 < t)
    (hball : Metric.ball x₀ r ⊆ D) (hf : ContDiffOn ℝ ⊤ f D)
    (hbound :
      ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
        |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρr : ρ < r) :
    ∀ {x : ℝ}, x ∈ Metric.ball x₀ ρ → ∀ n : ℕ,
      |f x - ∑ k ∈ Finset.range (n + 1),
          (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k|
        ≤ M * (t * |x - x₀|) ^ (n + 1) := by
  intro x hx n
  by_cases hxx₀ : x = x₀
  · -- At the center, the Taylor remainder vanishes term-by-term.
    subst hxx₀
    have hx_nhds : D ∈ nhds x := by
      refine mem_of_superset (Metric.ball_mem_nhds _ hr) ?_
      intro y hy
      exact hball hy
    have hfx : ContDiffAt ℝ ⊤ f x := (hf.of_le le_top).contDiffAt hx_nhds
    have hsum :
        ∑ k ∈ Finset.range (n + 1),
          (iteratedDeriv k f x / (k.factorial : ℝ)) * (x - x) ^ k = f x := by
      simpa [taylorWithinEval_self] using
        (taylorWithinEval_uIcc_eq_finset_sum_iteratedDeriv (x₀ := x) (x := x) hfx n).symm
    rw [hsum]
    simp [hM.le]
  · have hx_abs : |x - x₀| < ρ := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hinterval_subset_D : Set.uIcc x₀ x ⊆ D := by
      intro y hy
      have hy_dist : dist y x₀ ≤ dist x x₀ := by
        simpa [dist_comm] using (Real.dist_left_le_of_mem_uIcc hy)
      have hy_ball : y ∈ Metric.ball x₀ r := by
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt hy_dist (lt_of_lt_of_le hx (le_of_lt hρr))
      exact hball hy_ball
    have hcont_interval : ContDiffOn ℝ (n + 1) f (Set.uIcc x₀ x) := by
      exact (hf.of_le (by simp)).mono hinterval_subset_D
    have hx₀x : x₀ ≠ x := fun hx' ↦ hxx₀ hx'.symm
    obtain ⟨x', hx', hTaylor⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (x := x) (x₀ := x₀) hx₀x hcont_interval
    have hx'_ball : x' ∈ Metric.ball x₀ r := by
      have hx'_dist : dist x' x₀ ≤ dist x x₀ := by
        simpa [dist_comm] using
          (Real.dist_left_le_of_mem_uIcc (Set.uIoo_subset_uIcc_self hx'))
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt hx'_dist (lt_of_lt_of_le hx (le_of_lt hρr))
    have hderiv_bound := hbound x' hx'_ball (n + 1)
    have hfactorial_rewrite :
        iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / ((n + 1).factorial : ℝ) =
          (iteratedDeriv (n + 1) f x' / ((n + 1).factorial : ℝ)) * (x - x₀) ^ (n + 1) := by
      field_simp
    have hx₀_nhds : D ∈ nhds x₀ := by
      refine mem_of_superset (Metric.ball_mem_nhds _ hr) ?_
      intro y hy
      exact hball hy
    have hfx₀ : ContDiffAt ℝ ⊤ f x₀ := (hf.of_le le_top).contDiffAt hx₀_nhds
    have hTaylorPoly :
        ∑ k ∈ Finset.range (n + 1),
          (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k =
            taylorWithinEval f n (Set.uIcc x₀ x) x₀ x := by
      symm
      exact taylorWithinEval_uIcc_eq_finset_sum_iteratedDeriv hfx₀ n
    -- Rewrite the remainder into the normalized derivative times the geometric factor.
    calc
      |f x - ∑ k ∈ Finset.range (n + 1),
          (iteratedDeriv k f x₀ / (k.factorial : ℝ)) * (x - x₀) ^ k|
          = |f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x| := by
              rw [hTaylorPoly]
      _ = |iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / ((n + 1).factorial : ℝ)| := by
            rw [hTaylor]
      _ = |iteratedDeriv (n + 1) f x' / ((n + 1).factorial : ℝ)| * |x - x₀| ^ (n + 1) := by
            rw [hfactorial_rewrite, abs_mul, abs_pow]
      _ ≤ (M * t ^ (n + 1)) * |x - x₀| ^ (n + 1) := by
            gcongr
      _ = M * (t * |x - x₀|) ^ (n + 1) := by
            rw [mul_assoc, ← mul_pow]

/-- Helper for Theorem I.4-extra-2: analyticity at `x₀` should imply a uniform local geometric
bound for the normalized iterated derivatives. -/
lemma analyticAt_has_local_uniform_geometric_iteratedDeriv_bound
    (hD : IsOpen D) (hf : ContDiffOn ℝ ⊤ f D) {x₀ : ℝ} (hx₀ : x₀ ∈ D)
    (ha : AnalyticAt ℝ f x₀) :
    ∃ r > 0, Metric.ball x₀ r ⊆ D ∧ ∃ M > 0, ∃ t > 0,
      ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
        |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p := by
  -- TODO: follow the source-faithful change-of-origin route. Shift `f` to `g z = f (z + x₀)`,
  -- extract a scalar power-series ball from `ha.hasFPowerSeriesAt.comp_sub (-x₀)`, then apply
  -- `norm_changeOrigin_coeff_le_powerSeriesAbsSum` together with
  -- `scalar_changeOrigin_coeff_eq_iteratedDeriv_div_factorial` and rewrite back using
  -- `iteratedDeriv_comp_add_const`.
  sorry

/-- Helper for Theorem I.4-extra-2: a local geometric bound on the normalized iterated
derivatives should force analyticity at the center. -/
lemma analyticAt_of_locally_geometric_factorial_iteratedDeriv_bound
    (hD : IsOpen D) (hf : ContDiffOn ℝ ⊤ f D) {x₀ : ℝ} (hx₀ : x₀ ∈ D) :
    (∃ r > 0, Metric.ball x₀ r ⊆ D ∧ ∃ M > 0, ∃ t > 0,
      ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
        |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p) →
    AnalyticAt ℝ f x₀ := by
  intro h
  -- TODO: keep the textbook Taylor-Lagrange route. Define the canonical scalar series
  -- `a n = iteratedDeriv n f x₀ / n!`, deduce a positive convergence radius from the bound at
  -- `x₀` via `FormalMultilinearSeries.le_radius_of_bound`, and then compare its partial sums with
  -- `f` on a smaller ball using `lagrange_remainder_le_geometric_pow`.
  sorry

/-- Pointwise form of Theorem I.4-extra-2 in the ambient open set `D`: at `x₀ ∈ D`, analyticity is
equivalent to the existence of a ball contained in `D` and positive constants `M` and `t` such that
`|iteratedDeriv p f x / p!| ≤ M * t ^ p` throughout that ball. -/
theorem analyticAt_iff_locally_geometric_factorial_iteratedDeriv_bound
    (hD : IsOpen D) (hf : ContDiffOn ℝ ⊤ f D) {x₀ : ℝ} (hx₀ : x₀ ∈ D) :
    AnalyticAt ℝ f x₀ ↔
      ∃ r > 0, Metric.ball x₀ r ⊆ D ∧ ∃ M > 0, ∃ t > 0,
        ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
          |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p := by
  constructor
  · intro ha
    -- This is the coefficient-estimate half of the textbook argument.
    exact analyticAt_has_local_uniform_geometric_iteratedDeriv_bound hD hf hx₀ ha
  · intro hbound
    -- This is the Taylor-Lagrange half of the textbook argument.
    exact analyticAt_of_locally_geometric_factorial_iteratedDeriv_bound hD hf hx₀ hbound

/-- Theorem I.4-extra-2: for a smooth real function on an open set, analyticity is equivalent to
the local existence of a ball contained in the domain and positive constants `M` and `t` such that
`|iteratedDeriv p f x / p!| ≤ M * t ^ p` throughout that ball. -/
theorem analyticOnNhd_iff_locally_geometric_factorial_iteratedDeriv_bound
    (hD : IsOpen D) (hf : ContDiffOn ℝ ⊤ f D) :
    AnalyticOnNhd ℝ f D ↔
      ∀ x₀ ∈ D, ∃ r > 0, Metric.ball x₀ r ⊆ D ∧ ∃ M > 0, ∃ t > 0,
        ∀ x ∈ Metric.ball x₀ r, ∀ p : ℕ,
          |iteratedDeriv p f x / (p.factorial : ℝ)| ≤ M * t ^ p := by
  constructor
  · intro h x₀ hx₀
    exact
      (analyticAt_iff_locally_geometric_factorial_iteratedDeriv_bound hD hf hx₀).1 (h x₀ hx₀)
  · intro h x₀ hx₀
    exact
      (analyticAt_iff_locally_geometric_factorial_iteratedDeriv_bound hD hf hx₀).2 (h x₀ hx₀)
