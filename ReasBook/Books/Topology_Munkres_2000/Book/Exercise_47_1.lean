module

public import Topology_Munkres_2000.Book.Definition_45_3.PointwiseBounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.MetricSpace.Equicontinuity

public section

/-- The family `fₙ(x) = x + sin (n x)` from part (a). -/
noncomputable def linearPlusSine (n : ℕ+) : C(ℝ, ℝ) where
  toFun x := x + Real.sin ((n : ℝ) * x)
  continuous_toFun := by fun_prop

/-- The family `gₙ(x) = n + sin x` from part (b). -/
noncomputable def translatedSine (n : ℕ+) : C(ℝ, ℝ) where
  toFun x := (n : ℝ) + Real.sin x
  continuous_toFun := by fun_prop

/-- The family `hₙ(x) = |x| ^ (1 / n)` from part (c), using real exponentiation. -/
noncomputable def rootFamily (n : ℕ+) : C(ℝ, ℝ) where
  toFun x := |x| ^ (1 / (n : ℝ))
  continuous_toFun := by
    apply (Real.continuous_rpow_const ?_).comp continuous_abs
    positivity

/-- The family `kₙ(x) = n * sin (x / n)` from part (d). -/
noncomputable def scaledSine (n : ℕ+) : C(ℝ, ℝ) where
  toFun x := (n : ℝ) * Real.sin (x / (n : ℝ))
  continuous_toFun := by fun_prop

/-- Helper for Exercise 47.1: a uniformly norm-bounded real family has bounded range. -/
lemma isBounded_range_of_norm_le {ι : Type*} (u : ι → ℝ) (C : ℝ)
    (hu : ∀ i, ‖u i‖ ≤ C) : Bornology.IsBounded (Set.range u) := by
  -- Use the common norm bound after replacing an arbitrary range element by its index.
  rw [isBounded_iff_forall_norm_le]
  exact ⟨C, Set.forall_mem_range.mpr hu⟩

/-- Helper for Exercise 47.1: the root family is bounded by `max 1 |x|`. -/
lemma rootFamily_abs_le_max (n : ℕ+) (x : ℝ) : |rootFamily n x| ≤ max 1 |x| := by
  -- The exponent `1 / n` lies in `[0, 1]`, so split according to whether `|x| ≤ 1`.
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.property
  have hexp_nonneg : 0 ≤ 1 / (n : ℝ) := by positivity
  have hexp_le : 1 / (n : ℝ) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hn
  rw [rootFamily]
  simp only [ContinuousMap.coe_mk]
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  by_cases hx : |x| ≤ 1
  · exact (Real.rpow_le_one (abs_nonneg x) hx hexp_nonneg).trans (le_max_left _ _)
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hx) hexp_le).trans (le_max_right _ _)

/-- Helper for Exercise 47.1: every scaled sine map is `1`-Lipschitz. -/
lemma scaledSine_dist_le (n : ℕ+) (x y : ℝ) :
    dist (scaledSine n x) (scaledSine n y) ≤ dist x y := by
  -- Factor out the positive scale and apply the standard sine difference estimate.
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast n.property
  have hsin := Real.abs_sin_sub_sin_le (x / (n : ℝ)) (y / (n : ℝ))
  rw [scaledSine, Real.dist_eq]
  simp only [ContinuousMap.coe_mk]
  calc
    |(n : ℝ) * Real.sin (x / (n : ℝ)) - (n : ℝ) * Real.sin (y / (n : ℝ))| =
        (n : ℝ) * |Real.sin (x / (n : ℝ)) - Real.sin (y / (n : ℝ))| := by
          rw [← mul_sub, abs_mul, abs_of_pos hn_pos]
    _ ≤ (n : ℝ) * |x / (n : ℝ) - y / (n : ℝ)| :=
      mul_le_mul_of_nonneg_left hsin hn_pos.le
    _ = |x - y| := by
      rw [← sub_div, abs_div, abs_of_pos hn_pos]
      field_simp

/-- Helper for Exercise 47.1: the linear-plus-sine family separates nearby points at zero. -/
lemma linearPlusSine_separated_near_zero {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ+, ∃ x : ℝ, dist x 0 < δ ∧
      1 ≤ dist (linearPlusSine n 0) (linearPlusSine n x) := by
  -- Choose `n` so large that `x = π / (2n)` lies inside the prescribed ball.
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.pi / (2 * δ))
  have hratio_pos : 0 < Real.pi / (2 * δ) := by positivity
  have hm_real_pos : (0 : ℝ) < m := lt_trans hratio_pos hm
  have hm_pos : 0 < m := by exact_mod_cast hm_real_pos
  let n : ℕ+ := ⟨m, hm_pos⟩
  let x : ℝ := Real.pi / (2 * (m : ℝ))
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hx_lt : x < δ := by
    dsimp [x]
    have hm_real : Real.pi / (2 * δ) < (m : ℝ) := by exact_mod_cast hm
    have hpi : Real.pi < (m : ℝ) * (2 * δ) :=
      (div_lt_iff₀ (show 0 < 2 * δ by positivity)).1 hm_real
    apply (div_lt_iff₀ (show 0 < 2 * (m : ℝ) by positivity)).2
    nlinarith [hpi]
  have hangle : (n : ℝ) * x = Real.pi / 2 := by
    dsimp [n, x]
    field_simp
  refine ⟨n, x, ?_, ?_⟩
  · simpa only [Real.dist_eq, sub_zero, abs_of_pos hx_pos] using hx_lt
  · rw [Real.dist_eq]
    simp only [linearPlusSine, ContinuousMap.coe_mk, mul_zero, Real.sin_zero, add_zero,
      zero_sub, abs_neg, hangle, Real.sin_pi_div_two]
    rw [abs_of_pos]
    · linarith
    · linarith

/-- Helper for Exercise 47.1: the root family sends arbitrarily small points to `1 / 2`. -/
lemma rootFamily_separated_near_zero {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ+, ∃ x : ℝ, dist x 0 < δ ∧
      dist (rootFamily n 0) (rootFamily n x) = 1 / 2 := by
  -- Use a geometric-power input whose matching root is exactly `1 / 2`.
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 < 1 by norm_num)
  have hevent : ∀ᶠ m : ℕ in Filter.atTop, (1 / 2 : ℝ) ^ m < δ :=
    hlim (Iio_mem_nhds hδ)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  let m := M + 1
  have hm_pos : 0 < m := by
    dsimp [m]
    omega
  have hm_ne : m ≠ 0 := Nat.ne_of_gt hm_pos
  have hpow_lt : (1 / 2 : ℝ) ^ m < δ := hM m (by omega)
  let n : ℕ+ := ⟨m, hm_pos⟩
  let x : ℝ := (1 / 2 : ℝ) ^ m
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hroot : rootFamily n x = 1 / 2 := by
    rw [rootFamily]
    simp only [ContinuousMap.coe_mk, abs_of_pos hx_pos]
    dsimp [n, x]
    simpa only [one_div] using
      Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ 1 / 2 by norm_num) hm_ne
  refine ⟨n, x, ?_, ?_⟩
  · simpa only [Real.dist_eq, sub_zero, abs_of_pos hx_pos, x] using hpow_lt
  · rw [hroot, rootFamily, Real.dist_eq]
    simp only [ContinuousMap.coe_mk, abs_zero, one_div]
    norm_num

/-- Companion to Exercise 47.1 (1). The family in part (a) is pointwise bounded. -/
theorem linearPlusSine_pointwiseBounded : PointwiseBounded (fun n ↦ linearPlusSine n) := by
  -- At each fixed point, the sine term adds at most one to the absolute value.
  rw [pointwiseBounded_iff]
  intro x
  refine isBounded_range_of_norm_le (fun n ↦ linearPlusSine n x) (|x| + 1) ?_
  intro n
  rw [linearPlusSine, Real.norm_eq_abs]
  simp only [ContinuousMap.coe_mk]
  calc
    |x + Real.sin ((n : ℝ) * x)| ≤ |x| + |Real.sin ((n : ℝ) * x)| := abs_add_le _ _
    _ ≤ |x| + 1 := add_le_add_right (Real.abs_sin_le_one _) |x|

/-- Companion to Exercise 47.1 (2). The family in part (a) is not equicontinuous. -/
theorem linearPlusSine_not_equicontinuous : ¬ Equicontinuous (fun n ↦ linearPlusSine n) := by
  -- Equicontinuity at zero with epsilon one contradicts the separation helper.
  intro h
  have hzero := (Metric.equicontinuousAt_iff.mp (h 0)) 1 zero_lt_one
  obtain ⟨δ, hδ, hmod⟩ := hzero
  obtain ⟨n, x, hx, hsep⟩ := linearPlusSine_separated_near_zero hδ
  have hlt := hmod x hx n
  linarith

/-- Companion to Exercise 47.1 (3). The family in part (b) is not pointwise bounded. -/
theorem translatedSine_not_pointwiseBounded :
    ¬ PointwiseBounded (fun n ↦ translatedSine n) := by
  -- A bound at zero would bound all positive natural indices, which is impossible.
  intro h
  have hzero := pointwiseBounded_iff.mp h 0
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hzero
  obtain ⟨m, hm⟩ := exists_nat_gt (max C 0)
  have hm_real_pos : (0 : ℝ) < m := lt_of_le_of_lt (le_max_right C 0) hm
  have hm_pos : 0 < m := by exact_mod_cast hm_real_pos
  let n : ℕ+ := ⟨m, hm_pos⟩
  have hn_mem : translatedSine n 0 ∈ Set.range (fun k : ℕ+ ↦ translatedSine k 0) :=
    Set.mem_range_self n
  have hn_bound := hC _ hn_mem
  rw [translatedSine, Real.norm_eq_abs] at hn_bound
  simp only [ContinuousMap.coe_mk, Real.sin_zero, add_zero, n] at hn_bound
  have hn_abs : |(n : ℝ)| = (m : ℝ) := by
    rw [abs_of_pos]
    · rfl
    · exact_mod_cast n.property
  have hn_bound' : (m : ℝ) ≤ C := by
    calc
      (m : ℝ) = |(n : ℝ)| := hn_abs.symm
      _ ≤ C := hn_bound
  have hCm : C < (m : ℝ) := lt_of_le_of_lt (le_max_left C 0) hm
  linarith

/-- Companion to Exercise 47.1 (4). The family in part (b) is equicontinuous. -/
theorem translatedSine_equicontinuous : Equicontinuous (fun n ↦ translatedSine n) := by
  -- Translation cancels in differences, leaving the common `1`-Lipschitz sine estimate.
  refine Metric.equicontinuous_of_continuity_modulus id (continuousAt_id.tendsto)
    (fun n ↦ translatedSine n) ?_
  intro x y n
  rw [translatedSine, Real.dist_eq]
  simp only [ContinuousMap.coe_mk, id_eq]
  simpa only [add_sub_add_left_eq_sub, Real.dist_eq] using Real.abs_sin_sub_sin_le x y

/-- Companion to Exercise 47.1 (5). The family in part (c) is pointwise bounded. -/
theorem rootFamily_pointwiseBounded : PointwiseBounded (fun n ↦ rootFamily n) := by
  -- The root estimate supplies one bound depending only on the evaluation point.
  rw [pointwiseBounded_iff]
  intro x
  refine isBounded_range_of_norm_le (fun n ↦ rootFamily n x) (max 1 |x|) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact rootFamily_abs_le_max n x

/-- Companion to Exercise 47.1 (6). The family in part (c) is not equicontinuous. -/
theorem rootFamily_not_equicontinuous : ¬ Equicontinuous (fun n ↦ rootFamily n) := by
  -- Equicontinuity at zero with epsilon `1 / 4` contradicts the exact root separation.
  intro h
  have hzero := (Metric.equicontinuousAt_iff.mp (h 0)) (1 / 4 : ℝ) (by norm_num)
  obtain ⟨δ, hδ, hmod⟩ := hzero
  obtain ⟨n, x, hx, hsep⟩ := rootFamily_separated_near_zero hδ
  have hlt := hmod x hx n
  rw [hsep] at hlt
  norm_num at hlt

/-- Companion to Exercise 47.1 (7). The family in part (d) is pointwise bounded. -/
theorem scaledSine_pointwiseBounded : PointwiseBounded (fun n ↦ scaledSine n) := by
  -- Specialize the common Lipschitz estimate at zero to bound every value by `|x|`.
  rw [pointwiseBounded_iff]
  intro x
  refine isBounded_range_of_norm_le (fun n ↦ scaledSine n x) |x| ?_
  intro n
  have h := scaledSine_dist_le n x 0
  rw [scaledSine, Real.dist_eq] at h
  rw [Real.norm_eq_abs, scaledSine]
  simpa only [ContinuousMap.coe_mk, zero_div, Real.sin_zero, mul_zero, sub_zero,
    Real.dist_eq] using h

/-- Companion to Exercise 47.1 (8). The family in part (d) is equicontinuous. -/
theorem scaledSine_equicontinuous : Equicontinuous (fun n ↦ scaledSine n) := by
  -- The identity modulus works uniformly by the common Lipschitz estimate.
  refine Metric.equicontinuous_of_continuity_modulus id (continuousAt_id.tendsto)
    (fun n ↦ scaledSine n) ?_
  intro x y n
  simpa only [id_eq] using scaledSine_dist_le n x y

/-- Exercise 47.1 theorem suite: the pointwise-boundedness and equicontinuity
classifications for all four families. -/
theorem Exercise_47_1 :
    PointwiseBounded (fun n ↦ linearPlusSine n) ∧
      ¬ Equicontinuous (fun n ↦ linearPlusSine n) ∧
      ¬ PointwiseBounded (fun n ↦ translatedSine n) ∧
      Equicontinuous (fun n ↦ translatedSine n) ∧
      PointwiseBounded (fun n ↦ rootFamily n) ∧
      ¬ Equicontinuous (fun n ↦ rootFamily n) ∧
      PointwiseBounded (fun n ↦ scaledSine n) ∧
      Equicontinuous (fun n ↦ scaledSine n) := by
  -- Package the eight classifications established by the companion theorems.
  exact ⟨linearPlusSine_pointwiseBounded, linearPlusSine_not_equicontinuous,
    translatedSine_not_pointwiseBounded, translatedSine_equicontinuous,
    rootFamily_pointwiseBounded, rootFamily_not_equicontinuous,
    scaledSine_pointwiseBounded, scaledSine_equicontinuous⟩
