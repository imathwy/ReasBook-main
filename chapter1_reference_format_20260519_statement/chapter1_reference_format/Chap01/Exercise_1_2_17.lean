import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped NNReal
open scoped Topology

universe u

section UltrametricCriterion

variable {α : Type u} [PseudoMetricSpace α] [IsUltrametricDist α]

/-- Helper for Exercise 1.2.17: if all successive distances in a tail are `< ε`, then every later
term stays within `ε` of the base point of that tail. -/
lemma tail_dist_lt_of_small_steps (x : ℕ → α) {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hstep : ∀ k, dist (x (N + k + 1)) (x (N + k)) < ε) :
    ∀ k, dist (x (N + k)) (x N) < ε := by
  intro k
  induction k with
  | zero =>
      -- The base point is trivially within every positive radius of itself.
      simpa using hε
  | succ k ih =>
      -- One more step stays inside the same `ε`-ball by the ultrametric inequality.
      have hchain := IsUltrametricDist.dist_triangle_max (x (N + k + 1)) (x (N + k)) (x N)
      exact hchain.trans_lt (max_lt (hstep k) ih)

/-- Exercise 1.2.17 (1): in an ultrametric space, hence in particular in an ultrametric normed
field, a sequence is Cauchy exactly when the distances between successive terms tend to zero. -/
-- Proof sketch: the forward implication is immediate from the usual metric characterization of
-- Cauchy sequences. For the reverse implication, use the ultrametric inequality to bound every
-- tail distance `dist (x m) (x n)` by the maximum of the successive distances between consecutive
-- terms along the segment from `n` to `m`, and then use the assumption that these successive
-- distances tend to `0`.
theorem cauchySeq_iff_tendsto_dist_succ_zero (x : ℕ → α) :
    CauchySeq x ↔ Tendsto (fun n ↦ dist (x n.succ) (x n)) atTop (𝓝 0) := by
  constructor
  · intro hx
    rw [Metric.tendsto_nhds]
    intro ε hε
    -- A Cauchy tail controls all pairs in that tail, hence successive pairs in particular.
    rcases Metric.cauchySeq_iff.1 hx ε hε with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using
      hN n.succ (le_trans hn (Nat.le_succ _)) n hn
  · intro hx
    refine Metric.cauchySeq_iff'.2 ?_
    intro ε hε
    -- Convert the limit assumption into a uniform bound on all successive tail steps.
    rcases Filter.eventually_atTop.1 ((Metric.tendsto_nhds.1 hx) ε hε) with ⟨N, hN⟩
    have hstep : ∀ k, dist (x (N + k + 1)) (x (N + k)) < ε := by
      intro k
      simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using
        hN (N + k) (Nat.le_add_right N k)
    -- The ultrametric tail lemma then collapses every later point into the same `ε`-ball.
    refine ⟨N, fun n hn => ?_⟩
    rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
    exact tail_dist_lt_of_small_steps x hε (N := N) hstep k

end UltrametricCriterion

section RealCounterexample

/-- Helper for Exercise 1.2.17: the harmonic partial sums are unbounded above in `ℝ`. -/
lemma harmonic_unbounded_above (R : ℝ) : ∃ n : ℕ, R < (harmonic n : ℝ) := by
  have hshift : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))) atTop atTop := by
    exact ((tendsto_natCast_atTop_atTop (R := ℝ))).comp (Filter.tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (↑(n + 1) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hshift
  -- Since `log (n + 1)` tends to `+∞`, eventually it lies above the prescribed bound `R`.
  rcases Filter.eventually_atTop.1 (hlog.eventually_gt_atTop R) with ⟨n, hn⟩
  exact ⟨n, lt_of_lt_of_le (hn n le_rfl) (log_add_one_le_harmonic n)⟩

/-- Helper for Exercise 1.2.17: consecutive harmonic partial sums differ by the next reciprocal. -/
lemma dist_harmonic_succ_eq_inv (n : ℕ) :
    dist (harmonic n.succ : ℝ) (harmonic n) = ((n + 1 : ℝ)⁻¹) := by
  rw [Real.dist_eq, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
  have hnonneg : 0 ≤ ((n + 1 : ℝ)⁻¹) := by positivity
  -- The harmonic increments are positive, so the distance is just the increment itself.
  simp [abs_of_nonneg hnonneg]

/-- Exercise 1.2.17 (2): the real harmonic partial sums give an explicit sequence in `ℝ` that is
not Cauchy. -/
-- Proof sketch: if the harmonic partial sums were Cauchy, then `Metric.cauchySeq_bdd` would make
-- them bounded. This contradicts the lower bound `Real.log (n + 1) ≤ harmonic n`, since
-- `Real.log (n + 1)` is unbounded along `atTop`.
theorem real_harmonic_sequence_not_cauchy :
    ¬ CauchySeq (fun n ↦ (harmonic n : ℝ)) := by
  intro hc
  rcases cauchySeq_bdd hc with ⟨R, _, hR⟩
  rcases harmonic_unbounded_above R with ⟨n, hn⟩
  have hbounded : (harmonic n : ℝ) < R := by
    -- A Cauchy sequence in a metric space is bounded, so each harmonic partial sum stays below `R`.
    have habs : |(harmonic n : ℝ)| < R := by
      simpa [Real.dist_eq, harmonic_zero] using hR n 0
    exact lt_of_le_of_lt (le_abs_self _) habs
  exact not_lt_of_ge hbounded.le hn

/-- Exercise 1.2.17 (3): for the real harmonic partial sums, the distances between consecutive
terms tend to zero. -/
-- Proof sketch: rewrite `harmonic (n + 1) - harmonic n` using `harmonic_succ`; the successive
-- distance is then `|(n + 1 : ℝ)⁻¹|`, and this tends to `0` by
-- `tendsto_inv_atTop_nhds_zero_nat`.
theorem tendsto_dist_succ_real_harmonic_sequence :
    Tendsto (fun n ↦ dist (harmonic n.succ : ℝ) (harmonic n)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((((n + 1 : ℕ) : ℝ))⁻¹)) atTop (𝓝 0) := by
    exact ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))).comp (Filter.tendsto_add_atTop_nat 1)
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Rewrite the successive distances as reciprocals and use the standard inverse-limit theorem.
  filter_upwards [Metric.tendsto_nhds.1 hinv ε hε] with n hn
  have hnonneg : 0 ≤ ((n + 1 : ℝ)⁻¹) := by positivity
  simpa [dist_harmonic_succ_eq_inv, Real.dist_eq, abs_of_nonneg hnonneg] using hn

end RealCounterexample

section NormEquivalence

variable (K : Type u) [Semiring K]

/- Exercise 1.2.17 (4): by Definition 1.2.12, equivalence of norms is the canonical relation
`AbsoluteValue.IsEquiv`; mathlib already packages this relation as the setoid on
`AbsoluteValue K ℝ≥0`, so it is an equivalence relation. -/
#check (inferInstance : Setoid (AbsoluteValue K ℝ≥0))

end NormEquivalence
