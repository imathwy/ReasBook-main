import Mathlib
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22»
import DifferentialForms_Cartan_1970.IV.section16.«0002_Theorem_IV_4_extra_2»
import DifferentialForms_Cartan_1970.IV.section17.«0012_Exercise_4».SubharmonicCore

open Filter InnerProductSpace Laplacian Metric Real Set Topology
open scoped BigOperators InnerProductSpace
/-- Helper for Exercise 4: a continuous function that is nonzero at an interior point stays
nonzero on some closed ball around that point. -/
lemma exists_zero_free_closedBall_of_mem_open_of_ne_zero {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hf : ContinuousOn f D) {a : ℂ} (ha : a ∈ D) (hfa : f a ≠ 0) :
    ∃ R > 0, Metric.closedBall a R ⊆ D ∧ ∀ z ∈ Metric.closedBall a R, f z ≠ 0 := by
  have hfa_norm : 0 < ‖f a‖ := norm_pos_iff.mpr hfa
  rcases Metric.isOpen_iff.mp hD a ha with ⟨R₁, hR₁_pos, hR₁⟩
  rcases (Metric.continuousOn_iff.mp hf) a ha ‖f a‖ hfa_norm with ⟨R₂, hR₂_pos, hR₂⟩
  let R := min (R₁ / 2) (R₂ / 2)
  have hR_pos : 0 < R := by
    dsimp [R]
    positivity
  have hR_lt_R₁ : R < R₁ := by
    dsimp [R]
    have hhalf : R₁ / 2 < R₁ := by linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hR_lt_R₂ : R < R₂ := by
    dsimp [R]
    have hhalf : R₂ / 2 < R₂ := by linarith
    exact lt_of_le_of_lt (min_le_right _ _) hhalf
  refine ⟨R, hR_pos, ?_⟩
  have hclosed_subset : Metric.closedBall a R ⊆ D :=
    (Metric.closedBall_subset_ball hR_lt_R₁).trans hR₁
  refine ⟨hclosed_subset, ?_⟩
  intro z hz
  have hzD : z ∈ D := hclosed_subset hz
  have hz_dist_lt : dist z a < R₂ := by
    have hz_dist_le : dist z a ≤ R := by
      simpa [Metric.mem_closedBall] using hz
    exact lt_of_le_of_lt hz_dist_le hR_lt_R₂
  have hdist : dist (f z) (f a) < ‖f a‖ := hR₂ z hzD hz_dist_lt
  -- Any point in the ball stays closer to `f a` than the distance from `f a` to `0`.
  intro hfz
  have : False := by
    have hdist' := hdist
    simp [dist_eq_norm, hfz] at hdist'
  exact this.elim

/-- Helper for Exercise 4: on a zero-free analytic closed disc, Jensen's logarithmic mean identity
can be scaled by the nonnegative exponent `p`. -/
lemma circleAverage_scaled_log_norm_eq_scaled_log_center {g : ℂ → ℂ} {c : ℂ} {R p : ℝ}
    (hR : 0 < R) (h₁g : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (h₂g : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) :
    Real.circleAverage (fun z ↦ p * Real.log ‖g z‖) c R = p * Real.log ‖g c‖ := by
  have h₁g' : AnalyticOnNhd ℂ g (Metric.closedBall c |R|) := by
    simpa [abs_of_pos hR] using h₁g
  have h₂g' : ∀ z ∈ Metric.closedBall c |R|, g z ≠ 0 := by
    simpa [abs_of_pos hR] using h₂g
  -- Push the scalar `p` through the circle average, then invoke the zero-free logarithmic mean
  -- identity coming from Jensen's formula.
  calc
    Real.circleAverage (fun z ↦ p * Real.log ‖g z‖) c R
        = p * Real.circleAverage (fun z ↦ Real.log ‖g z‖) c R := by
          simpa [smul_eq_mul] using
            (Real.circleAverage_fun_smul (a := p) (f := fun z ↦ Real.log ‖g z‖) (c := c)
              (R := R))
    _ = p * Real.log ‖g c‖ := by
          rw [h₁g'.circleAverage_log_norm_of_ne_zero h₂g']

/-- Helper for Exercise 4: Jensen's inequality for `exp` on the circle parameter turns the
logarithmic mean into a mean inequality for exponentials. -/
lemma circleAverage_exp_scaled_log_le {g : ℂ → ℂ} {c : ℂ} {R p : ℝ} (hp : 0 ≤ p) (hR : 0 < R)
    (h₁g : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (h₂g : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) :
    Real.exp (Real.circleAverage (fun z ↦ p * Real.log ‖g z‖) c R) ≤
      Real.circleAverage (fun z ↦ Real.exp (p * Real.log ‖g z‖)) c R := by
  have hlog_circle : CircleIntegrable (fun z ↦ Real.log ‖g z‖) c R := by
    exact
      (h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm_of_nonneg hR.le
  have hscaled_log_circle : CircleIntegrable (fun z ↦ p * Real.log ‖g z‖) c R := by
    -- Scalar multiples preserve circle integrability of the logarithmic boundary data.
    simpa [smul_eq_mul] using hlog_circle.const_fun_smul (a := p)
  have hg_contOn : ContinuousOn (fun θ : ℝ ↦ g (circleMap c R θ)) Set.univ := by
    exact h₁g.continuousOn.comp (t := Metric.closedBall c R) (continuous_circleMap c R).continuousOn
      (fun θ _ ↦ circleMap_mem_closedBall c hR.le θ)
  have hg_cont : Continuous (fun θ : ℝ ↦ g (circleMap c R θ)) := by
    simpa [continuousOn_univ] using hg_contOn
  have hrpow_cont : Continuous (fun θ : ℝ ↦ Real.rpow ‖g (circleMap c R θ)‖ p) := by
    exact hg_cont.norm.rpow_const (fun _ ↦ Or.inr hp)
  have hlogexp_eq :
      ∀ θ : ℝ,
        Real.exp (p * Real.log ‖g (circleMap c R θ)‖) =
          Real.rpow ‖g (circleMap c R θ)‖ p := by
    intro θ
    have hθ_nonzero : g (circleMap c R θ) ≠ 0 :=
      h₂g (circleMap c R θ) (circleMap_mem_closedBall c hR.le θ)
    have hθ_pos : 0 < ‖g (circleMap c R θ)‖ := norm_pos_iff.mpr hθ_nonzero
    -- On the zero-free circle, `exp (p * log ‖g‖)` is exactly `‖g‖^p`.
    simpa [mul_comm] using (Real.rpow_def_of_pos hθ_pos p).symm
  have : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    rw [Set.uIoc_of_le (by positivity : 0 ≤ 2 * Real.pi)]
    infer_instance
  have : NeZero (MeasureTheory.volume (Set.uIoc 0 (2 * Real.pi))) := ⟨by simp⟩
  -- Route correction: isolate Jensen on the interval-average surface before rewriting back to
  -- `Real.circleAverage`.
  rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
  have hJensen :
      Real.exp (⨍ θ in 0..(2 * Real.pi), p * Real.log ‖g (circleMap c R θ)‖) ≤
        ⨍ θ in 0..(2 * Real.pi), Real.exp (p * Real.log ‖g (circleMap c R θ)‖) := by
    -- Apply Jensen's inequality for the convex function `exp` on the parameter interval.
    refine convexOn_exp.map_average_le continuousOn_exp isClosed_univ (by simp) ?_ ?_
    · rw [Set.uIoc_of_le (by positivity : 0 ≤ 2 * Real.pi)]
      exact hscaled_log_circle.1
    · exact (MeasureTheory.integrable_congr (Filter.Eventually.of_forall hlogexp_eq)).mpr
        hrpow_cont.integrableOn_uIoc
  simpa only [MeasureTheory.average_congr (Filter.Eventually.of_forall hlogexp_eq)] using hJensen

/-- Helper for Exercise 4: Jensen's formula on a zero-free analytic closed disc gives the
sub-mean inequality for `‖g‖^p`. -/
lemma circleAverage_norm_rpow_ge_center_of_analytic_nonvanishing {g : ℂ → ℂ} {c : ℂ} {R p : ℝ}
    (hp : 0 ≤ p) (hR : 0 < R) (h₁g : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (h₂g : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) :
    Real.rpow ‖g c‖ p ≤ Real.circleAverage (fun z ↦ Real.rpow ‖g z‖ p) c R := by
  have hc_nonzero : g c ≠ 0 := h₂g c (Metric.mem_closedBall_self hR.le)
  have hc_pos : 0 < ‖g c‖ := norm_pos_iff.mpr hc_nonzero
  -- First rewrite the center term as an exponential of the logarithmic mean, then invoke the
  -- interval-parameter Jensen inequality and convert the boundary exponential back to `Real.rpow`.
  calc
    Real.rpow ‖g c‖ p = Real.exp (p * Real.log ‖g c‖) := by
      simpa [mul_comm] using (Real.rpow_def_of_pos hc_pos p)
    _ = Real.exp (Real.circleAverage (fun z ↦ p * Real.log ‖g z‖) c R) := by
      rw [circleAverage_scaled_log_norm_eq_scaled_log_center hR h₁g h₂g]
    _ ≤ Real.circleAverage (fun z ↦ Real.exp (p * Real.log ‖g z‖)) c R := by
      exact circleAverage_exp_scaled_log_le hp hR h₁g h₂g
    _ = Real.circleAverage (fun z ↦ Real.rpow ‖g z‖ p) c R := by
      rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
      refine MeasureTheory.average_congr ?_
      filter_upwards with θ
      have hθ_nonzero : g (circleMap c R θ) ≠ 0 :=
        h₂g (circleMap c R θ) (circleMap_mem_closedBall c hR.le θ)
      have hθ_pos : 0 < ‖g (circleMap c R θ)‖ := norm_pos_iff.mpr hθ_nonzero
      -- The zero-free boundary again lets us rewrite the exponential expression as `‖g‖^p`.
      simpa [mul_comm] using (Real.rpow_def_of_pos hθ_pos p).symm
