module

public import Topology_Munkres_2000.Book.Theorem_46_2
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed

public section

open Filter Set

/-- The partial sums of the weighted geometric series on `(-1, 1)`. -/
def weightedGeometricPartialSum : ℕ → Set.Ioo (-1 : ℝ) 1 → ℝ :=
  Nat.rec (fun _ ↦ 0) fun n partialSum x ↦
    partialSum x + (n + 1 : ℕ) * (x : ℝ) ^ (n + 1)

/-- Helper for Exercise 46.5: the recursive partial sum equals the corresponding finite sum. -/
lemma weightedGeometricPartialSum_eq_sum_range (n : ℕ) (x : Set.Ioo (-1 : ℝ) 1) :
    weightedGeometricPartialSum n x =
      ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) * (x : ℝ) ^ (k + 1) := by
  -- Induction exposes exactly the new weighted-geometric summand.
  induction n with
  | zero =>
      simp [weightedGeometricPartialSum]
  | succ n inductionHypothesis =>
      change weightedGeometricPartialSum n x +
        ((n + 1 : ℕ) : ℝ) * (x : ℝ) ^ (n + 1) = _
      rw [inductionHypothesis, Finset.sum_range_succ]

/-- Helper for Exercise 46.5: consecutive partial sums differ by one summand. -/
lemma weightedGeometricPartialSum_succ_sub (n : ℕ) (x : Set.Ioo (-1 : ℝ) 1) :
    weightedGeometricPartialSum (n + 1) x - weightedGeometricPartialSum n x =
      ((n + 1 : ℕ) : ℝ) * (x : ℝ) ^ (n + 1) := by
  -- Unfold one recursion step and cancel the preceding partial sum.
  simp [weightedGeometricPartialSum]

/-- Every weighted geometric partial sum is continuous on `(-1, 1)`. -/
theorem continuous_weightedGeometricPartialSum (n : ℕ) :
    Continuous (weightedGeometricPartialSum n) := by
  -- Rewrite to a finite sum of continuous polynomial terms.
  have hfinite : weightedGeometricPartialSum n = fun x : Set.Ioo (-1 : ℝ) 1 ↦
      ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) * (x : ℝ) ^ (k + 1) := by
    funext x
    exact weightedGeometricPartialSum_eq_sum_range n x
  rw [hfinite]
  fun_prop

/-- The function represented on `(-1, 1)` by the weighted geometric series. -/
noncomputable def weightedGeometricLimit (x : Set.Ioo (-1 : ℝ) 1) : ℝ :=
  (x : ℝ) / (1 - (x : ℝ)) ^ 2

/-- Helper for Exercise 46.5: the shifted weighted geometric series has its standard sum. -/
lemma hasSum_shiftedWeightedGeometric {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n ↦ ((n + 1 : ℕ) : ℝ) * x ^ (n + 1)) (x / (1 - x) ^ 2) := by
  -- Multiply the standard `(n + 1) * x^n` series by `x`.
  have hnorm : ‖x‖ < 1 := by
    simpa only [Real.norm_eq_abs] using hx
  have hseries :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 1 hnorm).mul_left x
  have hterms :
      (fun n ↦ ((n + 1 : ℕ) : ℝ) * x ^ (n + 1)) =
        fun n ↦ x * (((n + 1).choose 1 : ℕ) * x ^ n : ℝ) := by
    funext n
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  have hsum : x / (1 - x) ^ 2 = x * (1 / (1 - x) ^ (1 + 1)) := by
    ring
  rw [hterms, hsum]
  exact hseries

/-- Helper for Exercise 46.5: absolute values on a compact subset stay uniformly below `1`. -/
lemma exists_compact_abs_bound_lt_one {K : Set (Set.Ioo (-1 : ℝ) 1)}
    (hK : IsCompact K) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ x ∈ K, |(x : ℝ)| ≤ r := by
  classical
  -- The empty set has the trivial bound; otherwise maximize the absolute value.
  by_cases hKnonempty : K.Nonempty
  · obtain ⟨y, hyK, hyMax⟩ :=
      hK.exists_isMaxOn hKnonempty (continuous_abs.comp continuous_subtype_val).continuousOn
    refine ⟨|(y : ℝ)|, abs_nonneg _, ?_, ?_⟩
    · exact abs_lt.mpr y.property
    · intro x hxK
      exact hyMax hxK
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro x hxK
    exact (hKnonempty ⟨x, hxK⟩).elim

/-- Exercise 46.5 (1): The weighted geometric partial sums converge to
`weightedGeometricLimit` in the topology of compact convergence on `(-1, 1)`. -/
theorem tendsto_weightedGeometricPartialSum_compactConvergence :
    Tendsto
      (fun n ↦ UniformOnFun.ofFun {K : Set (Set.Ioo (-1 : ℝ) 1) | IsCompact K}
        (weightedGeometricPartialSum n)) atTop
      (nhds (UniformOnFun.ofFun {K : Set (Set.Ioo (-1 : ℝ) 1) | IsCompact K}
        weightedGeometricLimit)) := by
  -- On each compact set, a radius below one gives a summable uniform majorant.
  rw [tendsto_compactConvergence_iff]
  intro K hK
  obtain ⟨r, hr0, hr1, hrK⟩ := exists_compact_abs_bound_lt_one hK
  have hrAbs : |r| < 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  have hmajorant : Summable (fun n ↦ ((n + 1 : ℕ) : ℝ) * r ^ (n + 1)) :=
    (hasSum_shiftedWeightedGeometric hrAbs).summable
  have hbound : ∀ n (x : K),
      ‖((n + 1 : ℕ) : ℝ) * (x : Set.Ioo (-1 : ℝ) 1) ^ (n + 1)‖ ≤
        ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) := by
    intro n x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hrK x x.property) _) (Nat.cast_nonneg _)
  have huniform := tendstoUniformly_tsum_nat hmajorant hbound
  have hpartial :
      (fun n ↦ K.restrict (weightedGeometricPartialSum n)) =
        fun n (x : K) ↦ ∑ k ∈ Finset.range n,
          ((k + 1 : ℕ) : ℝ) * (x : Set.Ioo (-1 : ℝ) 1) ^ (k + 1) := by
    funext n x
    exact weightedGeometricPartialSum_eq_sum_range n x
  have hlimit :
      K.restrict weightedGeometricLimit = fun x : K ↦
        ∑' n, ((n + 1 : ℕ) : ℝ) * (x : Set.Ioo (-1 : ℝ) 1) ^ (n + 1) := by
    funext x
    exact (hasSum_shiftedWeightedGeometric (abs_lt.mpr x.val.property)).tsum_eq.symm
  rw [hpartial, hlimit]
  exact huniform

/-- Exercise 46.5 (2): The limit of the weighted geometric partial sums is continuous. -/
theorem continuous_weightedGeometricLimit : Continuous weightedGeometricLimit := by
  -- The denominator never vanishes because every point of the subtype is below `1`.
  unfold weightedGeometricLimit
  apply Continuous.div
  · exact continuous_subtype_val
  · exact (continuous_const.sub continuous_subtype_val).pow 2
  · intro x hzero
    have hbase : 1 - (x : ℝ) = 0 := by
      nlinarith
    have hone : (x : ℝ) = 1 := by
      linarith
    exact (ne_of_lt x.property.2) hone

/-- Helper for Exercise 46.5: every increment is at least `1 / 2` somewhere near `1`. -/
lemma exists_weightedGeometricTerm_ge_half (n : ℕ) :
    ∃ x : Set.Ioo (-1 : ℝ) 1,
      (1 / 2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (x : ℝ) ^ (n + 1) := by
  -- Choose a point whose distance from `1` is quadratic in the index.
  let a : ℝ := (n + 1 : ℕ)
  have ha : 1 ≤ a := by
    simp [a]
  let x : ℝ := 1 - 1 / (2 * a ^ 2)
  have hdenom : 0 < 2 * a ^ 2 := by positivity
  have hxLower : (-1 : ℝ) < x := by
    dsimp [x]
    have hfrac : 1 / (2 * a ^ 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · norm_num
      · nlinarith [sq_nonneg a]
    nlinarith
  have hxUpper : x < 1 := by
    dsimp [x]
    have hfracPos : 0 < 1 / (2 * a ^ 2) := one_div_pos.mpr hdenom
    linarith
  refine ⟨⟨x, hxLower, hxUpper⟩, ?_⟩
  have hxMinus : x - 1 = -(1 / (2 * a ^ 2)) := by
    dsimp [x]
    ring
  have hxNegOne : (-1 : ℝ) ≤ x := hxLower.le
  have hpow := one_add_mul_sub_le_pow hxNegOne (n + 1)
  have hlinear : (1 / 2 : ℝ) ≤ a * (1 + (n + 1 : ℕ) * (x - 1)) := by
    rw [hxMinus]
    have haEq : ((n + 1 : ℕ) : ℝ) = a := rfl
    rw [haEq]
    have haPos : 0 < a := lt_of_lt_of_le zero_lt_one ha
    field_simp
    nlinarith [sq_nonneg (a - 1)]
  exact hlinear.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))

/-- Exercise 46.5 (3): The weighted geometric partial sums do not converge in the
uniform topology on the entire interval `(-1, 1)`. -/
theorem not_tendsto_weightedGeometricPartialSum_uniform :
    ¬ ∃ g : Set.Ioo (-1 : ℝ) 1 → ℝ,
      TendstoUniformly weightedGeometricPartialSum g atTop := by
  -- Uniform convergence would force consecutive partial sums uniformly close.
  rintro ⟨g, hg⟩
  have hCauchy : UniformCauchySeqOn weightedGeometricPartialSum atTop Set.univ :=
    hg.tendstoUniformlyOn.uniformCauchySeqOn
  have hhalfPos : (0 : ℝ) < 1 / 2 := by
    norm_num
  obtain ⟨N, hN⟩ :=
    (Metric.uniformCauchySeqOn_iff.mp hCauchy) (1 / 2) hhalfPos
  obtain ⟨x, hx⟩ := exists_weightedGeometricTerm_ge_half N
  have hdist := hN (N + 1) (Nat.le_add_right N 1) N le_rfl x (Set.mem_univ x)
  have hincrement :
      weightedGeometricPartialSum (N + 1) x - weightedGeometricPartialSum N x =
        ((N + 1 : ℕ) : ℝ) * (x : ℝ) ^ (N + 1) :=
    weightedGeometricPartialSum_succ_sub N x
  have hhalfNonneg : (0 : ℝ) ≤ 1 / 2 := by
    norm_num
  rw [Real.dist_eq, hincrement, abs_of_nonneg (hhalfNonneg.trans hx)] at hdist
  exact (not_lt_of_ge hx) hdist
