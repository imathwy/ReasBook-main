module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Topology.UniformSpace.UniformConvergence

public section

namespace UnitIntervalPower

/-- The sequence of power functions on the closed unit interval. -/
@[expose] def sequence (n : ℕ) (x : Set.Icc (0 : ℝ) 1) : ℝ :=
  (x : ℝ) ^ n

/-- The power sequence evaluates by taking the corresponding natural power. -/
@[simp] theorem sequence_apply (n : ℕ) (x : Set.Icc (0 : ℝ) 1) :
    sequence n x = (x : ℝ) ^ n := rfl

/-- The pointwise limit of the power functions on the closed unit interval. -/
@[expose] noncomputable def limit (x : Set.Icc (0 : ℝ) 1) : ℝ :=
  if (x : ℝ) = 1 then 1 else 0

/-- The pointwise limit is `1` at the right endpoint and `0` elsewhere. -/
@[simp] theorem limit_apply (x : Set.Icc (0 : ℝ) 1) :
    limit x = if (x : ℝ) = 1 then 1 else 0 := rfl

/-- Helper for Exercise 21.6: the power sequence converges at each point of the closed unit
interval. -/
theorem limit_at (x : Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto (fun n ↦ sequence n x) Filter.atTop (nhds (limit x)) := by
  by_cases hx : (x : ℝ) = 1
  · -- At the right endpoint, both the sequence and its limit are constantly one.
    simpa only [sequence_apply, limit_apply, hx, if_pos, one_pow] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 1))
  · -- At every other point, the base lies in `[0,1)`, so its powers tend to zero.
    have hx_lt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 hx
    simpa [sequence_apply, limit_apply, hx] using
      tendsto_pow_atTop_nhds_zero_of_lt_one x.property.1 hx_lt

/-- The power sequence converges to `limit` in the product topology on the function space. -/
theorem tendsto_limit :
    Filter.Tendsto sequence Filter.atTop (nhds limit) :=
  tendsto_pi_nhds.mpr limit_at

/-- Helper for Exercise 21.6: a canonical sequence of real points approaching `1` from below. -/
noncomputable def approachOnePoint (n : ℕ) : ℝ :=
  1 - 1 / (2 * (n + 1 : ℝ))

/-- Helper for Exercise 21.6: `approachOnePoint n` belongs to the half-open unit interval. -/
lemma approachOnePoint_mem_Ico (n : ℕ) :
    approachOnePoint n ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · -- The subtracted fraction is at most `1 / 2`, leaving a nonnegative point.
    unfold approachOnePoint
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : (2 : ℝ) ≤ 2 * (n + 1 : ℝ) := by
      nlinarith
    have hfrac : 1 / (2 * (n + 1 : ℝ)) ≤ (1 : ℝ) / 2 := by
      exact one_div_le_one_div_of_le (by norm_num) hden
    nlinarith
  · -- The subtracted fraction is positive, so the point is strictly below `1`.
    unfold approachOnePoint
    have hden : 0 < (2 : ℝ) * (n + 1 : ℝ) := by
      positivity
    have hfrac : 0 < 1 / ((2 : ℝ) * (n + 1 : ℝ)) := one_div_pos.mpr hden
    linarith

/-- Helper for Exercise 21.6: the chosen points have powers uniformly bounded below by `1 / 2`. -/
lemma half_le_approachOnePoint_pow (n : ℕ) :
    (1 / 2 : ℝ) ≤ approachOnePoint n ^ n := by
  have hmem := approachOnePoint_mem_Ico n
  -- Bernoulli's inequality reduces the power estimate to a rational inequality.
  have hbernoulli :
      1 + n * (approachOnePoint n - 1) ≤ approachOnePoint n ^ n :=
    one_add_mul_sub_le_pow (by linarith [hmem.1]) n
  have hden : 0 < (n + 1 : ℝ) := by
    positivity
  have hnfrac : (n : ℝ) / (n + 1 : ℝ) ≤ 1 := by
    rw [div_le_one hden]
    norm_num
  have hlower : (1 / 2 : ℝ) ≤ 1 + n * (approachOnePoint n - 1) := by
    unfold approachOnePoint
    field_simp
    nlinarith
  exact hlower.trans hbernoulli

/-- Helper for Exercise 21.6: a uniform limit of `sequence` equals its pointwise limit. -/
lemma eq_limit_of_tendstoUniformly (g : Set.Icc (0 : ℝ) 1 → ℝ)
    (hg : TendstoUniformly sequence g Filter.atTop) :
    g = limit := by
  funext x
  -- Uniform convergence gives a pointwise limit, which is unique in `ℝ`.
  exact tendsto_nhds_unique (hg.tendsto_at x) (limit_at x)

/-- Exercise 21.6: The power sequence converges pointwise on the closed unit interval but does not
converge uniformly to any real-valued function. -/
theorem not_tendstoUniformly :
    ¬ ∃ g : Set.Icc (0 : ℝ) 1 → ℝ,
      TendstoUniformly sequence g Filter.atTop := by
  rintro ⟨g, hg⟩
  -- Replace the proposed uniform limit by the already established pointwise limit.
  have hg_eq := eq_limit_of_tendstoUniformly g hg
  rw [hg_eq] at hg
  have hquarter : (0 : ℝ) < 1 / 4 := by
    norm_num
  have heventually := (Metric.tendstoUniformly_iff.mp hg) (1 / 4) hquarter
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  have hmemIco := approachOnePoint_mem_Ico N
  have hmemIcc : approachOnePoint N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hmemIco.1, hmemIco.2.le⟩
  let x : Set.Icc (0 : ℝ) 1 := ⟨approachOnePoint N, hmemIcc⟩
  -- Evaluate the uniform estimate at the matching near-endpoint witness.
  have hdist := hN N le_rfl x
  have hx_ne : (x : ℝ) ≠ 1 := ne_of_lt hmemIco.2
  have hdist_eq : dist (limit x) (sequence N x) = approachOnePoint N ^ N := by
    simp [limit_apply, sequence_apply, hx_ne, x, Real.dist_eq,
      abs_of_nonneg (pow_nonneg hmemIco.1 N)]
  rw [hdist_eq] at hdist
  -- The witness power is at least `1 / 2`, contradicting the uniform `1 / 4` bound.
  linarith [half_le_approachOnePoint_pow N]

end UnitIntervalPower
