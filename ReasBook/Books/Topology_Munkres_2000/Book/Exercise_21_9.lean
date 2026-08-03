module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Filter.AtTopBot.Ring
public import Mathlib.Topology.UniformSpace.UniformConvergence

public section

namespace MovingSpike

/-- The moving-spike sequence, where Lean index `n` represents textbook index `n + 1`. -/
@[expose] noncomputable def sequence (n : ℕ) (x : ℝ) : ℝ :=
  1 / (((n + 1 : ℕ) : ℝ) ^ 3 * (x - 1 / ((n + 1 : ℕ) : ℝ)) ^ 2 + 1)

/-- The moving-spike sequence evaluates by the formula from Exercise 21.9. -/
@[simp] theorem sequence_apply (n : ℕ) (x : ℝ) :
    sequence n x = 1 / (((n + 1 : ℕ) : ℝ) ^ 3 * (x - 1 / ((n + 1 : ℕ) : ℝ)) ^ 2 + 1) := rfl

/-- Every function in the moving-spike sequence is continuous. -/
theorem continuous (n : ℕ) : Continuous (sequence n) := by
  unfold sequence
  apply Continuous.div continuous_const
  · fun_prop
  · intro x
    positivity

/-- Helper for Exercise 21.9: the shifted real-valued index tends to positive infinity. -/
private lemma shiftedIndex_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
  -- Casting preserves the divergence of the shifted natural-number index.
  exact tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)

/-- Helper for Exercise 21.9: the moving spike at zero has a linear denominator. -/
private lemma sequence_zero_apply (n : ℕ) :
    sequence n 0 = 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
  -- Clear the nonzero shifted index and normalize the resulting polynomial identity.
  rw [sequence_apply]
  have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  field_simp
  ring

/-- Helper for Exercise 21.9: away from zero, the sequence denominator tends to infinity. -/
private lemma denominator_tendsto_atTop_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ 3 *
      (x - 1 / ((n + 1 : ℕ) : ℝ)) ^ 2 + 1) Filter.atTop Filter.atTop := by
  -- The cubic factor diverges, while the squared factor tends to the positive value `x ^ 2`.
  have hcubic : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ 3)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (α := ℝ) (by norm_num)).comp shiftedIndex_tendsto_atTop
  have hinv : Filter.Tendsto ((fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    shiftedIndex_tendsto_atTop.inv_tendsto_atTop
  have hsquare : Filter.Tendsto (fun n : ℕ ↦
      (x - 1 / ((n + 1 : ℕ) : ℝ)) ^ 2) Filter.atTop (nhds (x ^ 2)) := by
    simpa only [Pi.inv_apply, one_div, sub_zero] using (tendsto_const_nhds.sub hinv).pow 2
  have hproduct : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ 3 *
      (x - 1 / ((n + 1 : ℕ) : ℝ)) ^ 2) Filter.atTop Filter.atTop :=
    hcubic.atTop_mul_pos (sq_pos_of_ne_zero hx) hsquare
  -- Adding the nonnegative constant term preserves divergence to positive infinity.
  exact Filter.tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one) hproduct

/-- Exercise 21.9 (a): The moving-spike sequence converges pointwise to zero. -/
theorem tendsto_at (x : ℝ) :
    Filter.Tendsto (fun n ↦ sequence n x) Filter.atTop (nhds 0) := by
  -- At zero the denominator is linear; elsewhere its cubic factor dominates.
  by_cases hx : x = 0
  · subst x
    have hdenominator : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) + 1)
        Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one)
        shiftedIndex_tendsto_atTop
    have hinverse := hdenominator.inv_tendsto_atTop
    have hinversePointwise : Filter.Tendsto (fun n : ℕ ↦
        (((n + 1 : ℕ) : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
      hinverse.congr (fun n ↦ Pi.inv_apply _ n)
    simpa only [sequence_zero_apply, one_div] using hinversePointwise
  · have hdenominator := denominator_tendsto_atTop_of_ne_zero x hx
    have hinverse := hdenominator.inv_tendsto_atTop
    have hinversePointwise : Filter.Tendsto (fun n : ℕ ↦
        (((n + 1 : ℕ) : ℝ) ^ 3 * (x - 1 / ((n + 1 : ℕ) : ℝ)) ^ 2 + 1)⁻¹)
        Filter.atTop (nhds 0) :=
      hinverse.congr (fun n ↦ Pi.inv_apply _ n)
    simpa only [sequence_apply, one_div] using hinversePointwise

/-- The moving-spike sequence converges to zero in the product topology on the function space. -/
theorem tendsto_zero :
    Filter.Tendsto sequence Filter.atTop (nhds (fun _ : ℝ ↦ 0)) :=
  tendsto_pi_nhds.mpr tendsto_at

/-- The `n`-th moving spike has value `1` at its center `1 / (n + 1)`. -/
@[simp] theorem sequence_center (n : ℕ) :
    sequence n (1 / ((n + 1 : ℕ) : ℝ)) = 1 := by
  simp [sequence]

/-- Exercise 21.9 (b): The moving-spike sequence does not converge uniformly to zero. -/
theorem not_tendstoUniformly :
    ¬ TendstoUniformly sequence (fun _ : ℝ ↦ 0) Filter.atTop := by
  -- A uniform error bound of `1 / 2` would also hold at every moving center.
  intro huniform
  have heventually := (Metric.tendstoUniformly_iff.mp huniform) (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  have hcenter := hN N le_rfl (1 / ((N + 1 : ℕ) : ℝ))
  -- The value at that center is always one, contradicting the strict error bound.
  rw [sequence_center] at hcenter
  norm_num [Real.dist_eq] at hcenter

end MovingSpike
