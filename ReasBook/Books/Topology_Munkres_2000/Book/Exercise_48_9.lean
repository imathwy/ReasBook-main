module

public import Topology_Munkres_2000.Book.Exercise_48_9.Approximation

import Mathlib.Topology.Instances.Irrational

public section

open Filter

/-- Helper for Exercise 48.9: every rational input is an enumerated spike point. -/
private lemma rationalSpikeFunction_eq_one_div_of_not_irrational (g : ℕ+ ≃ ℚ) {x : ℝ}
    (hx : ¬ Irrational x) :
    ∃ n : ℕ+, x = (g n : ℝ) ∧ rationalSpikeFunction g x = 1 / (n : ℝ) := by
  -- Represent `x` by a rational, then pull that rational back through the enumeration.
  obtain ⟨q, rfl⟩ := exists_rat_of_not_irrational hx
  refine ⟨g.symm q, ?_, ?_⟩
  · simp
  · simpa using rationalSpikeFunction_apply g (g.symm q)

/-- Helper for Exercise 48.9: every positive-height superlevel set of the spike
function is finite. -/
private lemma finite_setOf_rationalSpikeFunction_abs_ge (g : ℕ+ ≃ ℚ) {ε : ℝ}
    (hε : 0 < ε) : Set.Finite {x : ℝ | ε ≤ |rationalSpikeFunction g x|} := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  let exceptional : Finset ℝ :=
    (Finset.range (N + 1)).image (fun k ↦ (g k.succPNat : ℝ))
  -- A spike of height at least `ε` must occur among the finite initial segment.
  refine exceptional.finite_toSet.subset ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_cases hxi : Irrational x
  · rw [rationalSpikeFunction_eq_zero_of_irrational g hxi, abs_zero] at hx
    exact ((not_lt_of_ge hx) hε).elim
  · obtain ⟨n, hxn, hvalue⟩ :=
      rationalSpikeFunction_eq_one_div_of_not_irrational g hxi
    have hnPos : 0 < (n : ℝ) := by
      exact_mod_cast n.property
    have habs : |rationalSpikeFunction g x| = 1 / (n : ℝ) := by
      rw [hvalue, abs_of_pos (one_div_pos.mpr hnPos)]
    have hnRange : n.natPred < N + 1 := by
      by_contra hn
      have hle : N + 1 ≤ n.natPred := Nat.le_of_not_gt hn
      have hnat : N + 1 < (n : ℕ) := by
        rw [← PNat.natPred_add_one n]
        exact Nat.lt_succ_of_le hle
      have hreal : (N + 1 : ℝ) < (n : ℝ) := by
        exact_mod_cast hnat
      have hNpos : (0 : ℝ) < N + 1 := by
        positivity
      have hsmall : 1 / (n : ℝ) < ε :=
        (one_div_lt_one_div_of_lt hNpos hreal).trans hN
      exact (not_lt_of_ge hx) (habs.trans_lt hsmall)
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨n.natPred, Finset.mem_range.mpr hnRange, ?_⟩
    simpa using hxn.symm

/-- Helper for Exercise 48.9: the rational spike function is continuous wherever
its value is zero. -/
private lemma continuousAt_rationalSpikeFunction_of_eq_zero (g : ℕ+ ≃ ℚ) {x : ℝ}
    (hx : rationalSpikeFunction g x = 0) : ContinuousAt (rationalSpikeFunction g) x := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hfinite := finite_setOf_rationalSpikeFunction_abs_ge g hε
  have hxOutside : x ∉ {y : ℝ | ε ≤ |rationalSpikeFunction g y|} := by
    rw [Set.mem_setOf_eq, hx, abs_zero]
    exact not_le_of_gt hε
  -- Outside the closed finite superlevel set, every spike has height below `ε`.
  filter_upwards [hfinite.isClosed.compl_mem_nhds hxOutside] with y hy
  have hylt : |rationalSpikeFunction g y| < ε := not_le.mp hy
  simpa [Real.dist_eq, hx] using hylt

/-- Helper for Exercise 48.9: continuity forces the rational spike function to
vanish at the point. -/
private lemma rationalSpikeFunction_eq_zero_of_continuousAt (g : ℕ+ ≃ ℚ) {x : ℝ}
    (h : ContinuousAt (rationalSpikeFunction g) x) : rationalSpikeFunction g x = 0 := by
  have hvanish : ∀ y ∈ {y : ℝ | Irrational y}, rationalSpikeFunction g y = 0 := by
    intro y hy
    exact rationalSpikeFunction_eq_zero_of_irrational g hy
  -- Extend the zero value from the dense irrational subset by continuity.
  exact h.continuousWithinAt.eq_const_of_mem_closure (dense_irrational x) hvanish

/-- Exercise 48.9 (1): `rationalSpikeFunction g` is continuous exactly at the
irrational points. -/
theorem continuousAt_rationalSpikeFunction_iff (g : ℕ+ ≃ ℚ) (x : ℝ) :
    ContinuousAt (rationalSpikeFunction g) x ↔ Irrational x := by
  constructor
  · intro h
    -- At a rational spike, continuity would force its positive height to vanish.
    by_contra hx
    obtain ⟨n, _, hvalue⟩ :=
      rationalSpikeFunction_eq_one_div_of_not_irrational g hx
    have hzero := rationalSpikeFunction_eq_zero_of_continuousAt g h
    have hnNe : (n : ℝ) ≠ 0 := by
      exact_mod_cast n.ne_zero
    exact (one_div_ne_zero hnNe) (hvalue.symm.trans hzero)
  · intro hx
    -- Irrational inputs lie in the zero locus, where the finite-superlevel estimate applies.
    exact continuousAt_rationalSpikeFunction_of_eq_zero g
      (rationalSpikeFunction_eq_zero_of_irrational g hx)

/-- Exercise 48.9 (2): `rationalSpikeFunction g` is a pointwise limit of continuous
real-valued functions. -/
theorem exists_continuous_tendsto_rationalSpikeFunction (g : ℕ+ ≃ ℚ) :
    ∃ F : ℕ → ℝ → ℝ, (∀ n, Continuous (F n)) ∧
      ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (rationalSpikeFunction g x)) :=
  ⟨rationalSpikeApproximation g, continuous_rationalSpikeApproximation g,
    tendsto_rationalSpikeApproximation g⟩

end
