module

public import Topology_Munkres_2000.Book.Exercise_21_9.MovingSpike
public import Mathlib.Topology.UniformSpace.CompactConvergence

public section

open Filter

/-- The scaled-identity sequence, where Lean index `n` represents textbook index `n + 1`. -/
@[expose] noncomputable def scaledIdentitySequence (n : ℕ) (x : ℝ) : ℝ :=
  x / ((n + 1 : ℕ) : ℝ)

/-- The scaled-identity sequence evaluates by the formula from Exercise 46.4. -/
@[simp] theorem scaledIdentitySequence_apply (n : ℕ) (x : ℝ) :
    scaledIdentitySequence n x = x / ((n + 1 : ℕ) : ℝ) := rfl

/-- Every function in `scaledIdentitySequence` is continuous. -/
theorem continuous_scaledIdentitySequence (n : ℕ) :
    Continuous (scaledIdentitySequence n) := by
  -- Division by the fixed shifted index preserves continuity in `x`.
  unfold scaledIdentitySequence
  fun_prop

/-- Companion result for Exercise 46.4 (1): The scaled-identity sequence converges to zero
in the topology of pointwise convergence. -/
theorem tendsto_scaledIdentitySequence_pointwise :
    Tendsto scaledIdentitySequence atTop (nhds (fun _ : ℝ ↦ 0)) := by
  -- Reduce product-topology convergence to the scalar limit at each point.
  rw [tendsto_pi_nhds]
  intro x
  have hlimit : Tendsto (fun n : ℕ ↦ x / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat (f := fun n : ℕ ↦ x / (n : ℝ)) 1).mpr
        (tendsto_const_div_atTop_nhds_zero_nat x)
  simpa only [scaledIdentitySequence_apply] using hlimit

/-- Helper for Exercise 46.4: on every bounded set, the scaled identities converge uniformly
to zero. -/
private lemma tendstoUniformlyOn_scaledIdentitySequence_of_isBounded (K : Set ℝ)
    (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn scaledIdentitySequence (fun _ : ℝ ↦ 0) atTop K := by
  -- Bound all numerators by one constant and let the shifted denominator tend to infinity.
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨C, hC_pos, hC⟩ := hK.exists_pos_norm_le
  have hlimit : Tendsto (fun n : ℕ ↦ C / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat (f := fun n : ℕ ↦ C / (n : ℝ)) 1).mpr
        (tendsto_const_div_atTop_nhds_zero_nat C)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlimit ε hε
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn x hx
  have hden_pos : 0 < ((n + 1 : ℕ) : ℝ) := by
    positivity
  have hC_div : C / ((n + 1 : ℕ) : ℝ) < ε := by
    have hdist := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hC_pos hden_pos)] at hdist
    exact hdist
  -- The pointwise error is at most the common scalar bound.
  calc
    dist 0 (scaledIdentitySequence n x) = ‖x‖ / ((n + 1 : ℕ) : ℝ) := by
      rw [scaledIdentitySequence_apply, Real.dist_eq, zero_sub, abs_neg, abs_div,
        Real.norm_eq_abs, abs_of_pos hden_pos]
    _ ≤ C / ((n + 1 : ℕ) : ℝ) := (div_le_div_iff_of_pos_right hden_pos).mpr (hC x hx)
    _ < ε := hC_div

/-- Exercise 46.4 (2): The scaled-identity sequence converges to zero in the topology
of compact convergence. -/
theorem tendsto_scaledIdentitySequence_compactConvergence :
    Tendsto
      (fun n ↦ UniformOnFun.ofFun {K : Set ℝ | IsCompact K} (scaledIdentitySequence n))
      atTop
      (nhds (UniformOnFun.ofFun {K : Set ℝ | IsCompact K} (fun _ : ℝ ↦ 0))) := by
  -- Compact subsets are bounded, so the preceding uniform estimate applies to each one.
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  intro K hK
  simpa only [Function.comp_apply, UniformOnFun.toFun_ofFun,
    tendstoUniformlyOn_iff_restrict] using
    tendstoUniformlyOn_scaledIdentitySequence_of_isBounded K hK.isBounded

/-- Companion result for Exercise 46.4 (3): The scaled-identity sequence does not converge
uniformly to zero on `ℝ`. -/
theorem not_tendsto_scaledIdentitySequence_uniform :
    ¬ TendstoUniformly scaledIdentitySequence (fun _ : ℝ ↦ 0) atTop := by
  -- A uniform half-unit error bound fails at the point equal to the current denominator.
  intro huniform
  have hhalf : (0 : ℝ) < 1 / 2 := by
    norm_num
  have heventually := (Metric.tendstoUniformly_iff.mp huniform) (1 / 2) hhalf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  have hpoint := hN N le_rfl ((N + 1 : ℕ) : ℝ)
  have hden_ne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  rw [scaledIdentitySequence_apply, div_self hden_ne] at hpoint
  norm_num [Real.dist_eq] at hpoint

/-- Companion result for Exercise 46.4 (4): The moving-spike sequence converges to zero
in the topology of pointwise convergence. -/
theorem tendsto_movingSpike_pointwise :
    Tendsto MovingSpike.sequence atTop (nhds (fun _ : ℝ ↦ 0)) :=
  MovingSpike.tendsto_zero

/-- Helper for Exercise 46.4: the moving-spike centers together with their limit point. -/
private def movingSpikeCenters : Set ℝ :=
  Set.insert 0 (Set.range (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)))

/-- Helper for Exercise 46.4: the set of moving-spike centers and its limit point is compact. -/
private lemma isCompact_movingSpikeCenters : IsCompact movingSpikeCenters := by
  -- The centers converge to zero, so their range with the limit point adjoined is compact.
  have hlimit : Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  unfold movingSpikeCenters
  exact hlimit.isCompact_insert_range

/-- Helper for Exercise 46.4: the moving spikes do not converge uniformly on their compact
set of centers. -/
private lemma not_tendstoUniformlyOn_movingSpikeCenters :
    ¬ TendstoUniformlyOn MovingSpike.sequence (fun _ : ℝ ↦ 0) atTop movingSpikeCenters := by
  -- At the `N`-th center, the `N`-th spike still has value one.
  intro huniform
  have hhalf : (0 : ℝ) < 1 / 2 := by
    norm_num
  have heventually := (Metric.tendstoUniformlyOn_iff.mp huniform) (1 / 2) hhalf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  have hcenter_mem : 1 / ((N + 1 : ℕ) : ℝ) ∈ movingSpikeCenters := by
    rw [movingSpikeCenters]
    exact Set.mem_insert_iff.mpr (Or.inr ⟨N, rfl⟩)
  have hcenter := hN N le_rfl (1 / ((N + 1 : ℕ) : ℝ)) hcenter_mem
  rw [MovingSpike.sequence_center] at hcenter
  norm_num [Real.dist_eq] at hcenter

/-- Companion result for Exercise 46.4 (5): The moving-spike sequence does not converge to zero
in the topology of compact convergence. -/
theorem not_tendsto_movingSpike_compactConvergence :
    ¬ Tendsto
      (fun n ↦ UniformOnFun.ofFun {K : Set ℝ | IsCompact K} (MovingSpike.sequence n))
      atTop
      (nhds (UniformOnFun.ofFun {K : Set ℝ | IsCompact K} (fun _ : ℝ ↦ 0))) := by
  -- Compact convergence would force uniform convergence on the compact center set.
  intro hcompact
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hcompact
  have hcenters := hcompact movingSpikeCenters isCompact_movingSpikeCenters
  have huniform :
      TendstoUniformlyOn MovingSpike.sequence (fun _ : ℝ ↦ 0) atTop movingSpikeCenters := by
    simpa only [Function.comp_apply, UniformOnFun.toFun_ofFun,
      tendstoUniformlyOn_iff_restrict] using hcenters
  exact not_tendstoUniformlyOn_movingSpikeCenters huniform

/-- Companion result for Exercise 46.4 (6): The moving-spike sequence does not converge uniformly
to zero on `ℝ`. -/
theorem not_tendsto_movingSpike_uniform :
    ¬ TendstoUniformly MovingSpike.sequence (fun _ : ℝ ↦ 0) atTop :=
  MovingSpike.not_tendstoUniformly
